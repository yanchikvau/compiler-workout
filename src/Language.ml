(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let conv_BoolToInt value = 
      match value with
      | true -> 1
      | false -> 0
    
    let conv_IntToBool value = 
      match value with
      | 0 -> false
      | _ -> true
 
 
    let rec eval state expr = 
      let eval_state = eval state in
        match expr with
        | Const literal -> literal
        | Var var -> state var
        | Binop (oper, expr_lt, expr_rt) ->
            let expr_lt = eval_state expr_lt in
            let expr_rt = eval_state expr_rt in
            match oper with
            | "+"   -> expr_lt + expr_rt
            | "-"   -> expr_lt - expr_rt
            | "*"   -> expr_lt * expr_rt
            | "/"   -> expr_lt / expr_rt
            | "%"   -> expr_lt mod expr_rt
            | "<" -> conv_BoolToInt (expr_lt < expr_rt)
            | "<="  -> conv_BoolToInt (expr_lt <= expr_rt)
            | ">" -> conv_BoolToInt (expr_lt > expr_rt)
            | ">="  -> conv_BoolToInt (expr_lt >= expr_rt)
            | "=="  -> conv_BoolToInt (expr_lt == expr_rt)
            | "!="  -> conv_BoolToInt (expr_lt != expr_rt)  
            | "&&"  -> conv_BoolToInt (conv_IntToBool expr_lt && conv_IntToBool expr_rt)
            | "!!"  -> conv_BoolToInt (conv_IntToBool expr_lt || conv_IntToBool expr_rt)
            | _ -> failwith("Error: undefined operation !")

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
let elemop oper = ostap($(oper)), fun expr_lt expr_rt -> Binop (oper, expr_lt, expr_rt)
    ostap (
        parse: 
              !(Ostap.Util.expr
                      (fun x -> x)
                      [|
                                `Lefta, [elemop "!!"];
                                `Lefta, [elemop "&&"];
                                `Nona,  [
                      elemop "==";
                      elemop "!=";
                      elemop ">=";
                      elemop ">";
                      elemop "<=";
                      elemop "<";
                    ];
                                 `Lefta, [
                      elemop "+";
                      elemop "-";
                    ];
                                `Lefta, [
                      elemop "*";
                      elemop "/";
                      elemop "%";
                    ];
                      |] 
                      primary
                  );
      primary: var:IDENT {Var var} 
             | literal:DECIMAL {Const literal} 
              | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t   with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output) stmt = 
      match stmt with
      |Assign(x, expr) -> (Expr.update x (Expr.eval state expr) state, input, output)
      |Read x -> (Expr.update x (List.hd input) state, List.tl input, output)
      |Write expr -> (state, input, output @ [Expr.eval state expr])
      |Seq (st_1, st_2) -> (eval (eval (state, input, output) st_1) st_2)
      |Skip -> (state, input, output)
            |If (expr, st_1, st_2) -> if Expr.eval state expr != 0 then eval (state, input, output) st_1 else eval (state, input, output) st_2
      |While  (expr, st) -> if Expr.eval state expr != 0 then eval (eval (state, input, output) st) stmt else (state, input, output)
      |Repeat (expr, st) -> 
        let (state', input', output') = eval (state, input, output) st in
        if Expr.eval state' expr == 0 then eval (state', input', output') stmt else (state', input', output')
      | _ -> failwith "Error: undefined statement !"
                               
    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      stmt: read | write | assign | if_ | while_ | for_ | repeat_ | skip;
      read: "read" -"(" x:IDENT -")" { Read x };
      write: "write" -"(" e:!(Expr.parse) -")" { Write e };
      assign: x:IDENT -":=" e:!(Expr.parse) { Assign (x, e) };
      if_: "if" e:!(Expr.parse) "then" s:parse "fi" {If (e, s, Skip)} 
         | "if" e:!(Expr.parse) "then" s1:parse else_elif:else_or_elif "fi" {If (e, s1, else_elif)};
      else_or_elif: else_ | elif_;
      else_: "else" s:parse {s};
      elif_: "elif" e:!(Expr.parse) "then" s1:parse s2:else_or_elif {If (e, s1, s2)};
      while_: "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)};
      for_: "for" init:parse "," e:!(Expr.parse) "," s1:parse "do" s2:parse "od" {Seq (init, While (e, Seq(s2, s1)))};
      repeat_: "repeat" s:parse "until" e:!(Expr.parse) {Repeat (e, s)};
      skip: "skip" {Skip};
      seq: left_st:stmt -";" right_st:parse { Seq (left_st, right_st) }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
