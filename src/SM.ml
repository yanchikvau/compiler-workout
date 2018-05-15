open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n


  let rec eval env cnfg prog = 
  match prog with
  | [] -> cnfg
  | instr::p -> 
    match cnfg, instr with
    | (cstack, y::x::stack, c), BINOP (operation)  -> eval env (cstack, (Value.of_int (Expr.binop operation (Value.to_int x) (Value.to_int y)))::stack, c) p
    | (cstack, stack, c), CONST (value) -> eval env (cstack, (Value.of_int value)::stack, c) p
    | (cstack, stack, c), STRING (str) -> eval env (cstack, (Value.of_string str)::stack, c) p
    | (cstack, stack, (s, i, o)), LD (variable) -> eval env (cstack, (State.eval s variable)::stack, (s, i, o)) p
    | (cstack, z::stack, (s, i, o)), ST (variable) -> eval env (cstack, stack, ((State.update variable z s), i, o)) p
    | (cstack, stack, (s, i, o)), STA (variable, n) -> 
      let v::ind, stack' = split (n + 1) stack in 
      eval env (cstack, stack', (Language.Stmt.update s variable v (List.rev ind), i, o)) p  
    | cnfg, LABEL (label) -> eval env cnfg p
    | cnfg, JMP (label) -> eval env cnfg (env#labeled label)
    | (cstack, z::stack, c), CJMP (suf, label) -> 
      (
        match suf with
      | "z" -> if (Value.to_int z)==0 then eval env (cstack, stack, c) (env#labeled label) else eval env (cstack, stack, c) p
      | "nz"-> if (Value.to_int z)<>0 then eval env (cstack, stack, c) (env#labeled label) else eval env (cstack, stack, c) p
      ) 
    | (cstack, stack, (s, i, o)), CALL (name, n, isFunc) -> 
      if env#is_label name then eval env ((p, s)::cstack, stack,(s, i, o)) (env#labeled name)
      else eval env (env#builtin cnfg name n isFunc) p
    | (cstack, stack, (s, i, o)), BEGIN (_, args, locals) ->
      let rec combine s args stack = 
        match args, stack with
        | name_arg::args', z::stack' -> 
          let s', stack'' = combine s args' stack' in
          (State.update name_arg z s', stack'')
        | [], stack' -> (s, stack') in
      let s', stack' = combine (State.enter s (args @ locals)) args stack in
      eval env (cstack, stack',(s',i, o)) p
    | (cstack, stack, (s, i, o)), END | (cstack, stack, (s, i, o)), RET _ -> 
    (
      match cstack with
      | (p', s')::cstack' -> eval env (cstack', stack, (State.leave s s', i, o)) p'
      | [] -> cnfg
    )      

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileEx stmt =
  match stmt with
  | Expr.Const (value) -> [CONST value]
  | Expr.Var (variable) -> [LD variable]
  | Expr.Binop (op, left, right) -> compileEx left @ compileEx right @ [BINOP op]
  | Expr.Call (name, args) -> List.concat (List.map compileEx (List.rev args)) @ [CALL ("L" ^ name, List.length args, false)]
  | Expr.String (str) -> [STRING str]
  | Expr.Array (elems) -> List.flatten (List.map compileEx elems) @ [CALL ("$array", List.length elems, false)]
  | Expr.Elem (a, indx) ->  compileEx a @ compileEx indx @ [CALL ("$elem", 2, false)]
  | Expr.Length (a) -> compileEx a @ [CALL ("$length", 1, false)]


let rec compile_label env stmt  = 
  match stmt with
  | Stmt.Assign (variable, indexes, expr) -> 
    (
      match indexes with
    | [] -> compileEx expr @ [ST variable], env 
    | indexes -> List.flatten (List.map compileEx (indexes @ [expr])) @ [STA (variable, List.length indexes)], env
    )
  | Stmt.Seq (left, right) -> 
      let left_path, env = compile_label env left  in
      let right_path, env = compile_label env right in
      left_path @ right_path, env
  | Stmt.Skip -> [], env
  | Stmt.If (expr, at, aels) ->
    let lelse, env = env#newL in 
    let lfi, env = env#newL in
    let atc, env = compile_label env at  in
    let aelsc, env = compile_label env aels in
    compileEx expr @ [CJMP ("z", lelse)] @ atc @ [JMP lfi; LABEL lelse] @ aelsc @ [LABEL lfi], env
  | Stmt.While (expr, body) ->
    let lcheck, env = env#newL in
    let lloop, env = env#newL in
    let wbody, env = compile_label env body in
    [JMP lcheck; LABEL lloop] @ wbody @ [LABEL lcheck] @ compileEx expr @ [CJMP ("nz", lloop)], env
  | Stmt.DoWhile (expr, body) ->(
    let lloop, env = env#newL in
    let dwbody, env = compile_label env body in
   [LABEL lloop] @ dwbody @ compileEx expr @ [CJMP ("z", lloop)]), env
  | Stmt.Call (name, args) ->
    List.concat (List.map compileEx (List.rev args)) @ [CALL ("L" ^ name, List.length args, true)], env
  | Stmt.Return (expr) -> 
    (
    match expr with
    | None -> [RET false], env
    | Some expr -> compileEx expr @ [RET true], env
    )

let rec compile_funcs env defs =
    match defs with
     | (name, (args, locals, body))::defs' ->
        let body_f, env = compile_funcs env defs' in
        let compile_body, env = compile_label env body in 
        [LABEL ("L" ^ name); BEGIN ("L" ^ name, args, locals)] @ compile_body @ [END] @ body_f, env
     | [] -> [], env

let compile (defs, stmt) =
  let env = object
    val count_label = 0
    method newL = "L" ^ string_of_int count_label, {< count_label = count_label + 1 >}
  end in
  let prg, env = compile_label env stmt in
 let compileFunc, _  = compile_funcs env defs in prg @ [END] @ compileFunc
