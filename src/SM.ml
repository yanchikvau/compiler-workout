open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (stack,(state,input,output)) smProgram = 
        match smProgram with
        | [] -> (stack,(state,input,output))
        | intstr :: smProg_tl -> 
                  match intstr with
                  | CONST var -> eval env (var :: stack, (state,input,output)) smProg_tl
                  | READ -> eval env (List.hd input :: stack, (state, List.tl input, output)) smProg_tl
                  | WRITE -> eval env (List.tl stack, (state, input, output @ [List.hd stack])) smProg_tl
                  | LD x -> eval env (state x :: stack, (state,input,output)) smProg_tl
                  | ST x -> eval env (List.tl stack, ((Expr.update x (List.hd stack) state), input, output)) smProg_tl
                  | BINOP oper -> 
                          let y :: x :: stack_tl = stack in
                          let value = Expr.eval state (Expr.Binop (oper, Expr.Const x, Expr.Const y)) in
                          eval env (value :: stack_tl, (state, input, output)) smProg_tl
                  | LABEL _ -> eval env (stack,(state,input,output)) smProg_tl
                  | JMP label -> eval env (stack,(state,input,output)) (env#labeled label)
                  | CJMP (cond, label)  -> 
                    let (s::stack_tail) = stack in
                    let x = match cond with
                    | "nz" -> s <> 0
                    | "z" -> s = 0 
                    in eval env (List.tl stack, (state,input,output)) (if (x) then (env#labeled label) else smProg_tl)


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
 let env = object 
    val mutable id = 0
    method next_label = 
      id <- (id + 1);
      "L" ^ string_of_int id
  end
  
let rec compileExpression expr = 
      match expr with
      | Expr.Const var -> [CONST var]
      | Expr.Var var -> [LD var]
      | Expr.Binop (oper, lt, rt) -> (compileExpression lt) @ (compileExpression rt) @ [BINOP oper]

 
let rec compile stmt = 
        match stmt with
        | Stmt.Assign (x, expr) -> (compileExpression expr) @ [ST x]
        | Stmt.Read x -> [READ; ST x]
        | Stmt.Write expr -> (compileExpression expr) @ [WRITE]
        | Stmt.Seq (st_1, st_2) -> (compile st_1) @ (compile st_2)
        | Stmt.Skip -> []
        | Stmt.If (expr, st_1, st_2) ->
               let else_label = env#next_label in
               let end_label = env#next_label in
               let current_case = compile st_1 in
               let last_case = compile st_2 in
               (compileExpression expr @ [CJMP ("z", else_label)] @ current_case @ [JMP end_label] @ [LABEL else_label] @ last_case @ [LABEL end_label])
        | Stmt.While (expr, st) ->
               let end_label = env#next_label in
               let loop_label = env#next_label in
               let body = compile st in
               ([JMP end_label] @ [LABEL loop_label] @ body @ [LABEL end_label] @ compileExpression expr @ [CJMP ("nz", loop_label)])
        | Stmt.Repeat (expr, st) ->
               let loop_label = env#next_label in
               let body = compile st in
               ([LABEL loop_label] @ body @ compileExpression expr @ [CJMP ("z", loop_label)])
