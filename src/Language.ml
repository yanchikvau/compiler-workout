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

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       
    let int2bool x = x !=0
    let bool2int x = if x then 1 else 0

    let binop operation left_op right_op =
  match operation with
        | "+" -> left_op + right_op
        | "-" -> left_op - right_op
        | "*" -> left_op * right_op
        | "/" -> left_op / right_op
        | "%" -> left_op mod right_op
        | "<" -> bool2int (left_op < right_op)
        | ">" -> bool2int (left_op > right_op)
        | "<=" -> bool2int (left_op <= right_op)
        | ">=" -> bool2int (left_op >= right_op)
        | "==" -> bool2int (left_op == right_op)
        | "!=" -> bool2int (left_op != right_op)
        | "&&" -> bool2int (int2bool left_op && int2bool right_op)
        | "!!" -> bool2int (int2bool left_op || int2bool right_op)
        | _ -> failwith "Not implemented yet"
  

    let rec eval env ((st, i, o, r) as conf) expr = 
        match expr with
        | Const c -> (st, i, o, Some c)
        | Var v -> (st, i, o, Some (State.eval st v))
        | Binop (operation, left_expr, right_expr) ->
          let (st', i', o', Some left_op) = eval env conf left_expr in
          let (st'', i'', o'', Some right_op) = eval env (st', i', o', Some left_op) right_expr in
          (st'', i'', o'', Some (binop operation left_op right_op))  
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

  let binop_transforming binoplist = List.map (fun op -> ostap($(op)), (fun left_op right_op -> Binop (op, left_op, right_op))) binoplist 
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
    !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, binop_transforming ["!!"];
            `Lefta, binop_transforming ["&&"];
            `Nona,  binop_transforming [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, binop_transforming ["+"; "-"];
            `Lefta, binop_transforming ["*"; "/"; "%"]
          |]
  
  primary
  );
        primary: x:IDENT {Var x} | c:DECIMAL {Const c} | -"(" parse -")" 
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
            let pleas first scnd =
                (match scnd with
                | Skip -> first
                | _ -> Seq(first, scnd)) in
        match stmt with
        | Assign (x, expr) -> 
          let (st', i', o', Some v) = Expr.eval env conf expr in
          eval env (State.update x v st', i', o', r) Skip k
        | Read (x) -> eval env (State.update x (List.hd i) st, List.tl i, o, r) Skip k
        | Write (expr) -> 
          let (st', i', o', Some v) = Expr.eval env conf expr in
          eval env (st', i', o @ [v], r) Skip k
        | Seq (frts_stmt, scnd_stmt) -> eval env conf (pleas scnd_stmt k) frts_stmt
        | Skip -> 
          (match k with
          | Skip -> conf
          | _ -> eval env conf Skip k)
        | If (expr, frts_stmt, scnd_stmt) -> 
          let (st', i', o', Some v) = Expr.eval env conf expr in
          eval env conf k (if v <> 0 then frts_stmt else scnd_stmt)
        | While (expr, st) -> eval env conf k (If (expr, Seq (st, While (expr, st)), Skip))
        | Repeat (st, expr) -> eval env conf k (Seq (st, If (expr, Skip, Repeat (st, expr))))
        | Return expr ->
          (match expr with
          | None -> conf
          | Some expr -> Expr.eval env conf expr)
        | Call (f, expr) -> eval env (Expr.eval env conf (Expr.Call (f, expr))) Skip k;;   
         
    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      stmt: assign | read | write | if_ | while_ | for_ | repeat_ | skip | call;
      assign: x:IDENT -":=" expr:!(Expr.parse) {Assign (x, expr)};
      read: -"read" -"(" x:IDENT -")" {Read x};
      write: -"write" -"("expr:!(Expr.parse) -")" {Write expr};
      if_: "if" expr:!(Expr.parse) "then" st:parse "fi" {If (expr, st, Skip)} 
         | "if" expr:!(Expr.parse) "then" frts_stmt:parse else_elif:else_or_elif "fi" {If (expr, frts_stmt, else_elif)}; else_or_elif: else_ | elif_;
      else_: "else" st:parse {st};
      elif_: "elif" expr:!(Expr.parse) "then" frts_stmt:parse scnd_stmt:else_or_elif {If (expr, frts_stmt, scnd_stmt)};
      while_: "while" expr:!(Expr.parse) "do" st:parse "od" {While (expr, st)};
      for_: "for" init:parse "," expr:!(Expr.parse) "," frts_stmt:parse "do" scnd_stmt:parse "od" {Seq (init, While (expr, Seq(scnd_stmt, frts_stmt)))};
      repeat_: "repeat" st:parse "until" expr:!(Expr.parse) {Repeat (st, expr)};
      skip: "skip" {Skip};
      call: x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)};
      seq: frts_stmt:stmt -";" scnd_stmt:parse {Seq (frts_stmt, scnd_stmt)}
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
           let xs, locs, s      =  snd @@ M.find f m in
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
