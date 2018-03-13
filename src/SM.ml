open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval conf prog =
        match prog with
        | [] -> conf
        |inst::tail -> (
                match conf, inst with
                | (y::x::stack, tm_conf), BINOP operation -> 
                        let value = Language.Expr.binop operation x y in
                        eval (value::stack, tm_conf) tail
                | (stack, tm_conf), CONST value ->
                        eval (value::stack, tm_conf) tail
                | (stack, (st, z::input, output)), READ -> 
                        eval (z::stack, (st, input, output)) tail
                | (z::stack, (st, input, output)), WRITE -> 
                        eval (stack, (st, input, output @ [z])) tail
                | (stack, (st, input, output)), LD x -> 
                        let value = st x in
                        eval (value::stack, (st, input, output)) tail
                        | (z::stack, (st, input, output)), ST x -> 
                        let stt = Language.Expr.update x z st in
                        eval (stack, (stt, input, output)) tail
                )


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileExpr expr = 
        match expr with
        | Language.Expr.Const c -> [CONST c]
        | Language.Expr.Var x -> [LD x]
        | Language.Expr.Binop (operation, left_op, right_op) -> compileExpr left_op @ compileExpr right_op @ [BINOP operation]


let rec compile st = 
        match st with
        | Language.Stmt.Assign (x, expr) -> compileExpr expr @ [ST x]
        | Language.Stmt.Read x -> [READ; ST x]
        | Language.Stmt.Write expr -> compileExpr expr @ [WRITE]
        | Language.Stmt.Seq (frts_stmt, scnd_stmt) -> compile frts_stmt @ compile scnd_stmt