open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
    | (cstack, stack, c), SEXP (tag, elems) -> 
          let exprs, stack' = split elems stack in 
          eval env (cstack, (Value.sexp tag (List.rev exprs)) :: stack', c) p
    | (cstack, stack, (s, i, o)), LD (variable) -> eval env (cstack, (State.eval s variable)::stack, (s, i, o)) p
    | (cstack, z::stack, (s, i, o)), ST (variable) -> eval env (cstack, stack, ((State.update variable z s), i, o)) p
    | (cstack, stack, (s, i, o)), STA (variable, n) -> 
      let v::ind, stack' = split (n + 1) stack in 
      eval env (cstack, stack', (Language.Stmt.update s variable v ind, i, o)) p  
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
      let s', stack' = combine (State.enter s (args @ locals)) (List.rev args) stack in
      eval env (cstack, stack',(s',i, o)) p
    | (cstack, stack, (s, i, o)), END | (cstack, stack, (s, i, o)), RET _ -> 
    (
      match cstack with
      | (p', s')::cstack' -> eval env (cstack', stack, (State.leave s s', i, o)) p'
      | [] -> cnfg
    )
    | (cstack, z::stack, c), DROP -> eval env (cstack, stack, c) p   
    | (cstack, z::stack, c), DUP -> eval env (cstack, z::z::stack, c) p 
    | (cstack, x::y::stack, c), SWAP -> eval env (cstack, y::x::stack, c) p  
    | (cstack, sexp::stack, c), TAG s -> 
          let res = if s = Value.tag_of sexp then 1 else 0 in 
          eval env (cstack, (Value.of_int res)::stack, c) p
    | (cstack, stack, (s, i, o)), ENTER elems -> 
        let vals, rest = split (List.length elems) stack in
        let s' = List.fold_left2 (fun ast e var -> State.bind var e ast) State.undefined vals elems in 
            eval env (cstack, rest, (State.push s s' elems, i, o)) p   
    | (cstack, stack, (s, i, o)), LEAVE -> eval env (cstack, stack, (State.drop s, i, o)) p           

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern p lfalse =
  (let rec comp pat = 
    (match pat with
      Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident x -> [DROP]
    | Stmt.Pattern.Sexp (tag, ps) -> 
      let res, _ = (List.fold_left (fun (acc, pos) pat -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp pat)), pos + 1) ([], 0) ps) in
      [DUP; TAG tag; CJMP ("z", lfalse)] @ res) in
  comp p)
  and bindings p =
  let rec bind cp = 
    (match cp with
      Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident x -> [SWAP]
    | Stmt.Pattern.Sexp (_, xs) -> 
      let res, _ = List.fold_left (fun (acc, pos) curp -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)) ([], 0) xs in res @ [DROP]) in
  bind p @ [ENTER (Stmt.Pattern.vars p)]
  and expr e = 
    match e with
    | Expr.Const (value) -> [CONST value]
    | Expr.Var (variable) -> [LD variable]
    | Expr.Binop (op, left, right) -> expr left @ expr right @ [BINOP op]
    | Expr.Call (name, args) -> call (label name) args false
    | Expr.String (str) -> [STRING str]
    | Expr.Array (elems) -> call ".array" elems false
    | Expr.Elem (a, indx) ->  call ".elem" [a; indx] false
    | Expr.Length (a) -> call ".length" [a] false
    | Expr.Sexp (tag, elems) -> let args = List.fold_left (fun acc indx -> acc @ (expr indx)) [] elems in args @ [SEXP (tag, List.length elems)] in
  let rec compile_stmt l env stmt =  
    match stmt with
    | Stmt.Assign (variable, indexes, exp) -> 
      (
        match indexes with
      | [] -> env, false, expr exp @ [ST variable]
      | indexes -> let indexes = List.fold_left (fun acc index -> acc @ (expr index)) [] indexes in 
      env, false, (List.rev indexes @ expr exp @ [STA (variable, List.length indexes)])
      )
    | Stmt.Seq (left, right) -> 
        let env, _, left_path = compile_stmt l env left  in
        let env, _, right_path = compile_stmt l env right in
        env, false, left_path @ right_path
    | Stmt.Skip -> env, false, []
    | Stmt.If (exp, at, aels) ->
      let lelse, env = env#get_label in 
      let lfi, env = env#get_label in
      let env, _, atc = compile_stmt l env at  in
      let env, _, aelsc = compile_stmt l env aels in
      env, false, expr exp @ [CJMP ("z", lelse)] @ atc @ [JMP lfi; LABEL lelse] @ aelsc @ [LABEL lfi]
    | Stmt.While (exp, body) ->
      let lcheck, env = env#get_label in
      let lloop, env = env#get_label in
      let env, _, wbody = compile_stmt l env body in
      env, false, [JMP lcheck; LABEL lloop] @ wbody @ [LABEL lcheck] @ expr exp @ [CJMP ("nz", lloop)]
    | Stmt.DoWhile (exp, body) ->(
      let lloop, env = env#get_label in
      let env, _, dwbody = compile_stmt l env body in
     env, false, [LABEL lloop] @ dwbody @ expr exp @ [CJMP ("z", lloop)])
    | Stmt.Call (name, args) ->
      env, false, List.concat (List.map expr (List.rev args)) @ [CALL ("L" ^ name, List.length args, true)]
    | Stmt.Return (exp) -> 
      (
      match exp with
      | None -> env, false, [RET false]
      | Some exp -> env, false, expr exp @ [RET true]
      ) 
    | Stmt.Leave -> env, false, [LEAVE]
    | Stmt.Case (exp, patt) ->
      let rec comp_pat ps env lbl isFirst lend = 
        (match ps with
          [] -> env, []
        | (p, act)::tl -> 
          let env, _, body = compile_stmt l env act in 
          let lfalse, env = env#get_label
          and start = if isFirst then [] else [LABEL lbl] in
          let env, code = comp_pat tl env lfalse false lend in
          env, 
          start @ (pattern p lfalse) @ bindings p @ body @ [LEAVE; JMP lend] @ code) in
      let lend, env = env#get_label in
      let env, code = comp_pat patt env "" true lend in
      env, false, expr exp @ code @ [LABEL lend] in

  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
(if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)