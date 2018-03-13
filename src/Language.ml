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
  

    let rec eval state expr = 
        match expr with
        | Const c -> c
        | Var v -> state v
        | Binop (operation, left_expr, right_expr) ->
        let left_op = eval state left_expr in
        let right_op = eval state right_expr in
        binop operation left_op right_op

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    let binop_transforming binoplist = List.map (fun op -> ostap($(op)), (fun left_op right_op -> Binop (op, left_op, right_op))) binoplist
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output) stmt = 
        match stmt with
        | Assign (x, expr) -> (Expr.update x (Expr.eval state expr) state, input, output)
        | Read (x) -> 
                (match input with
                | z::tail -> (Expr.update x z state, tail, output)
                | [] -> failwith "Empty input stream")
        | Write (expr) -> (state, input, output @ [(Expr.eval state expr)])
        | Seq (frts_stmt, scnd_stmt) -> (eval (eval (state, input, output) frts_stmt ) scnd_stmt)
                                
    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      stmt: assign | read | write;
      assign: x:IDENT -":=" expr:!(Expr.parse) {Assign (x, expr)};
      read: -"read" -"(" x:IDENT -")" {Read x};
      write: -"write" -"("expr:!(Expr.parse) -")" {Write expr};
      seq: frts_stmt:stmt -";" scnd_stmt:parse {Seq (frts_stmt, scnd_stmt)} 
              
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
