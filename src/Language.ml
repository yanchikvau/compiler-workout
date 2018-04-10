(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty_info x = failwith (Printf.sprintf "Undefined variable %s" x)
    (* Empty state *)
    let empty = { g = empty_info; l = empty_info; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
     let update x v s =
      let update' f y = if x = y then v else f y in 
      if List.mem x s.scope then { s with l = update' s.l } else { s with g = update' s.g }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = empty_info; scope = xs }

    (* Drops a scope *)
    let leave st st' = { g = st'.g; l = st.l; scope = st.scope }

  end
    
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
     | Var var -> State.eval state var
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
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env (state, input, output) stmt = 
            match stmt with
                |Assign(x, expr) -> (State.update x (Expr.eval state expr) state, input, output)
                |Read x -> (State.update x (List.hd input) state, List.tl input, output)
                |Write expr -> (state, input, output @ [Expr.eval state expr])
                |Seq (st_1, st_2) -> (eval env(eval env(state, input, output) st_1) st_2)
                |Skip -> (state, input, output)
                |If (expr, st_1, st_2) -> if Expr.eval state expr != 0 then eval env (state, input, output) st_1 else eval env (state, input, output) st_2
                |While  (expr, st) -> if Expr.eval state expr != 0 then eval env (eval env (state, input, output) st) stmt else (state, input, output)
                |Repeat (expr, st) -> 
                        let (state', input', output') = eval env (state, input, output) st in
                        if Expr.eval state' expr == 0 then eval env (state', input', output') stmt else (state', input', output')
                |Call (f, params)    ->
           let (args, vars, body) = env#definition f in
           let evaled_params = List.map (Expr.eval state) params in
           let enter_state = State.enter state (args @ vars) in
           let update_function = (fun st param value -> State.update param value st) in
           let (res_state, res_input, res_output) = eval env ((List.fold_left2 update_function enter_state args evaled_params), input, output) body in 
                    (State.leave res_state state, res_input, res_output)
                | _ -> failwith "Error: undefined statement !"
                                
    (* Statement parser *)
    ostap (
            parse: seq | stmt;
            stmt: read | write | assign | if_ | while_ | for_ | repeat_ | skip | call;
            read: "read" "(" x:IDENT ")" { Read x };
            write: "write" "(" e:!(Expr.parse) ")" { Write e };
            assign: x:IDENT ":=" e:!(Expr.parse) { Assign (x, e) };
            if_: "if" e:!(Expr.parse) "then" s:parse "fi" {If (e, s, Skip)} 
                  | "if" e:!(Expr.parse) "then" s1:parse else_elif:else_or_elif "fi" {If (e, s1, else_elif)};
            else_or_elif: else_ | elif_;
            else_: "else" s:parse {s};
            elif_: "elif" e:!(Expr.parse) "then" s1:parse s2:else_or_elif {If (e, s1, s2)};
            while_: "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)};
            for_: "for" init:parse "," e:!(Expr.parse) "," s1:parse "do" s2:parse "od" {Seq (init, While (e, Seq(s2, s1)))};
            repeat_: "repeat" s:parse "until" e:!(Expr.parse) {Repeat (e, s)};
            skip: "skip" {Skip};
            call: x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)};
            seq: left_st:stmt -";" right_st:parse { Seq (left_st, right_st) }
          )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      argument: IDENT;
      parse:
        "fun" fname:IDENT "(" args: !(Util.list0 argument) ")"
        locals: (%"local" !(Util.list argument))?
        "{" body: !(Stmt.parse) "}" { (fname, (args, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = let module DefMap = Map.Make (String) in
  let definitionsMap = List.fold_left (fun m ((name, _) as definitions) -> DefMap.add name definitions m) DefMap.empty defs in
  let env = (object method definition name = snd (DefMap.find name definitionsMap) end) in
  let _, _, output = Stmt.eval env (State.empty, i, []) body
  in output
                                   
(* Top-level parser *)
let parse = ostap (
  defs:!(Definition.parse) * body:!(Stmt.parse) {
    (defs, body) 
  }
)
