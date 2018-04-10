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
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let int_to_bool value = 
          if value == 0 then false else true
    let bool_to_int value = 
          if value then 1 else 0

    let binop operation left_operand right_operand = 
            match operation with
            | "+"   -> left_operand + right_operand
            | "-"   -> left_operand - right_operand
            | "*"   -> left_operand * right_operand
            | "/"   -> left_operand / right_operand
            | "%"   -> left_operand mod right_operand
            | "&&"  -> bool_to_int (int_to_bool left_operand && int_to_bool right_operand)
            | "!!"  -> bool_to_int (int_to_bool left_operand || int_to_bool right_operand)
            | "<" -> bool_to_int (left_operand < right_operand)
            | "<="  -> bool_to_int (left_operand <= right_operand)
            | ">" -> bool_to_int (left_operand > right_operand)
            | ">="  -> bool_to_int (left_operand >= right_operand)
            | "=="  -> bool_to_int (left_operand == right_operand)
            | "!="  -> bool_to_int (left_operand != right_operand)
            | _ -> failwith("Undefined operator!")

    let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
              | Const const -> (st, i, o, Some const)
              | Var variable -> 
                      let value = State.eval st variable in
                      (st, i, o, Some value)
              | Binop (operation, left, right) ->
                let (st', i', o', Some l) as conf' = eval env conf left in
                let (st', i', o', Some r) = eval env conf' right in
                let value = binop operation l r in 
                (st', i', o', Some value)
              | Call (name, args) ->
                      let rec evalArgs env conf args =
                              match args with
                              | expr::args' ->
                                      let (st', i', o', Some eval_arg) as conf' = eval env conf expr in
                                      let eval_args', conf' = evalArgs env conf' args' in 
                                      eval_arg::eval_args', conf'
                              |[] -> [], conf  
                      in
                      let eval_args, conf' = evalArgs env conf args in
                      env#definition env name eval_args conf'
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let mapoperation operations = List.map (fun operation -> ostap($(operation)), (fun left right -> Binop (operation, left, right))) operations
    ostap (                                      
      parse: 
              !(Ostap.Util.expr
                      (fun x -> x)
                      [|
                              `Lefta, mapoperation ["!!"];
                              `Lefta, mapoperation ["&&"];
                              `Nona,  mapoperation ["=="; "!=";">="; ">"; "<="; "<"];
                              `Lefta, mapoperation ["+"; "-"];
                              `Lefta, mapoperation ["*"; "/"; "%"];
                      |]
                      primary
              );
      primary: 
              x:IDENT "(" args:!(Util.list0)[parse] ")" {Call (x, args)}
            | variable:IDENT {Var variable} 
            | const:DECIMAL {Const const} 
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env conf k stmt =
      let romb stmt k =
              if k = Skip then stmt
              else Seq (stmt, k) in
      match conf, stmt with
      | (st, input, output, r) , Assign (variable, expr) -> 
              let (st', i', o', Some value) = Expr.eval env conf expr in
              eval env (State.update variable value st', i', o', r) Skip k
      | (st, z::input, output, r), Read variable ->
              eval env (State.update variable z st, input, output, r) Skip k
      | (st, input, output, r), Write expr ->
              let (st', i', o', Some value) = Expr.eval env conf expr in
              eval env (st', i', o' @ [value], r) Skip k
      | conf, Seq (left_stmt, right_stmt) ->
              eval env conf (romb right_stmt k) left_stmt
      | conf, Skip -> 
              if k = Skip then conf
              else eval env conf Skip k
      | (st, input, output, r), If (expr, th, el) ->
              let (st', i', o', Some value) as conf' = Expr.eval env conf expr in
              let if_answer value = if value == 0 then el else th in
              eval env conf' k (if_answer value)
      | conf, While (expr, while_stmt) ->
              let (st', i', o', Some value) as conf' = Expr.eval env conf expr in
              if value == 0 then eval env conf' Skip k
              else eval env conf' (romb stmt k) while_stmt
      | conf, Repeat (expr, repeat_stmt) ->
              eval env conf (romb (While(Expr.Binop("==",expr, Expr.Const 0), repeat_stmt)) k) repeat_stmt
      | (st, input, output, r), Call (name, args) ->
                      let rec evalArgs env conf args =
                              match args with
                              | expr::args' ->
                                      let (st', i', o', Some eval_arg) = Expr.eval env conf expr in
                                      let eval_args', conf' = evalArgs env (st', i', o', Some eval_arg) args' in 
                                      eval_arg::eval_args', conf'
                              |[] -> [], conf  in
                      let eval_args, conf' = evalArgs env conf args in
                      let conf'' = env#definition env name eval_args conf' in
                      eval env conf'' Skip k
      | (st, input, output, r), Return expr -> (
                    match expr with
                    | None -> (st, input, output, None)
                    | Some expr -> Expr.eval env conf expr
              )
      | _, _ -> failwith("Undefined statement!")
         
    (* Statement parser *)
    ostap (
      parse: 
                      seq | stmt;
  
        stmt:
            read | write | assign | skip | repeat_stmt | while_stmt | if_stmt | for_stmt | call | ret;

      assign: 
                    variable:IDENT -":=" expr:!(Expr.parse) {Assign (variable, expr)};
            read: 
                    %"read" -"(" variable:IDENT -")" {Read variable};
            write: 
                    %"write" -"(" expr:!(Expr.parse) -")" {Write expr};
            skip: 
                    %"skip" {Skip};
            if_stmt: 
                    %"if" expr:!(Expr.parse) %"then"
                    if_true:parse 
                    if_false:else_stmt %"fi" {If (expr, if_true, if_false)};
            else_stmt:  
                    %"else" if_false:parse {if_false} 
                    | %"elif" expr:!(Expr.parse) %"then"
                    if_true:parse 
                    if_false:else_stmt {If (expr, if_true, if_false)}
            | "" {Skip};
            while_stmt:
                    %"while" expr:!(Expr.parse) %"do"
                    while_body:parse
                    %"od" {While (expr, while_body)};
            repeat_stmt:
                    %"repeat" 
                    repeat_body:parse 
                    %"until" expr:!(Expr.parse) {Repeat (expr, repeat_body)};
            for_stmt:
                    %"for" init:parse -"," expr:!(Expr.parse) -"," loop:parse %"do"
                    for_body:parse
                    %"od" { Seq (init, While(expr, Seq (for_body, loop))) };
            call: x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)};
            ret: %"return" expr:!(Expr.parse)? { Return expr};
            seq: 
                    left_stmt:stmt -";" right_stmt:parse {Seq (left_stmt, right_stmt)} 
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
