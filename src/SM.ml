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
          
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
    match insn with
    | BINOP op     -> let y::x::stack' = stack in eval env (cstack, Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c) prg'
    | CONST i      -> eval env (cstack, (Value.of_int i)::stack, c) prg'
    | STRING s     -> eval env (cstack, (Value.of_string s)::stack, c) prg'
    | SEXP (tag, len) -> (
      let es, stack' = split len stack in
      eval env (cstack, (Value.sexp tag (List.rev es)) :: stack', c) prg'
    )
    | LD x         -> eval env (cstack, State.eval st x :: stack, c) prg'
    | ST x         -> let v::stack' = stack in eval env (cstack, stack', (State.update x v st, i, o)) prg'
    | STA (x, len) -> (
      let v::indexes, stack' = split (len + 1) stack in
      eval env (cstack, stack', (Language.Stmt.update st x v (List.rev indexes), i, o)) prg'
    )
    | LABEL _      -> eval env conf prg'
    | JMP l        -> eval env conf (env#labeled l)
    | CJMP (s, l)  ->
      let x::stack' = stack in
      let prg'' =
        if (Value.to_int x = 0 && s = "z") || (Value.to_int x != 0 && s = "nz")
        then env#labeled l
        else prg'
      in
      eval env (cstack, stack', c) prg''
    | CALL (fun_name, args_length, is_procedure) -> (
      if env#is_label fun_name
      then let cstack' = ((prg', st)::cstack) in eval env (cstack', stack, c) (env#labeled fun_name)
      else eval env (env#builtin conf fun_name args_length is_procedure) prg'
    )
    | BEGIN (_, args, locals) -> (
      let bind ((v :: stack), state) x = (stack, State.update x v state) in
      let (stack', st') = List.fold_left bind (stack, State.enter st (args @ locals)) args in
      eval env (cstack, stack', (st', i, o)) prg'
    )
    | END | RET _ -> (
      match cstack with
      | [] -> conf
      | (p, s)::cstack' -> eval env (cstack', stack, (Language.State.leave st s, i, o)) p
    )
    | DROP -> eval env (cstack, List.tl stack, c) prg'
    | DUP -> let v::_ = stack in eval env (cstack, v::stack, c) prg'
    | SWAP -> let x::y::stack' = stack in eval env (cstack, y::x::stack', c) prg'
    | TAG s -> (
      let sexp::stack' = stack in
      let v = if s = Value.tag_of sexp then 1 else 0 in
      eval env (cstack, Value.of_int v :: stack', c) prg'
    )
    | ENTER names -> (
      let values, stack' = split (List.length names) stack in
      let new_scope = List.fold_left2 (fun st x v -> State.bind x v st) State.undefined names values in
      eval env (cstack, stack', (State.push st new_scope names, i, o)) prg'
    )
    | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) prg'
    | _ -> failwith "Undefined behavior"

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
  and pattern env lfalse is_last_pattern x =
    let rec pattern' env lfalse inner level = function
      | Stmt.Pattern.Wildcard -> env, (if inner then [DROP] else [])
      | Stmt.Pattern.Ident _ -> env, (if inner then [DROP] else [])
      | Stmt.Pattern.Sexp (tag_name, xs) -> (
        let ok, env = env#get_label in
        let (env, _, acc) =
          List.fold_left (fun (env, i, acc) x ->
                            let env, rest_patterns = pattern' env lfalse true (level + 1) x in
                            env, (i + 1), acc @ [DUP; CONST i; CALL (".elem", 2, false)] @ rest_patterns)
                         (env, 0, []) xs
        in
        env, [DUP; TAG tag_name; CJMP ("nz", ok)] @ (Language.list_init (if is_last_pattern then level + 1 else level) (fun _ -> DROP)) @ [JMP lfalse; LABEL ok] @ acc @ (if inner then [DROP] else [])
      )
      | _ -> env, [JMP lfalse]
    in
    pattern' env lfalse false 0 x
  and bindings p =
    let rec bind inner acc = function
      | Stmt.Pattern.Wildcard -> acc @ (if inner then [DROP] else [])
      | Stmt.Pattern.Ident x -> acc @ (if inner then [SWAP] else [DUP])
      | Stmt.Pattern.Sexp (_, xs) ->
        let lift i x =
          let code = (if inner then [] else [DUP]) @ [CONST i; CALL (".elem", 2, false)] in
          bind true (acc @ code) x
        in
        List.concat (List.mapi lift xs)
    in
    bind false [] p @ [DROP; ENTER (Stmt.Pattern.vars p)]
  and expr e =
    match e with
    | Expr.Const n -> [CONST n]
    | Expr.Array es -> call ".array" es false
    | Expr.String s -> [STRING s]
    | Expr.Sexp (tag, es) -> (List.concat (List.map expr es)) @ [SEXP (tag, List.length es)]
    | Expr.Var x -> [LD x]
    | Expr.Binop (op, e1, e2) -> expr e1 @ expr e2 @ [BINOP op]
    | Expr.Elem (xs_e, index_e) -> call ".elem" [xs_e; index_e] false
    | Expr.Length xs_e -> call ".length" [xs_e] false
    | Expr.Call (fun_name, args) -> call (label fun_name) (List.rev args) false
  in
  let rec compile_stmt l env stmt =
    match stmt with
    | Stmt.Assign (x, [], e) -> env, false, expr e @ [ST x]
    | Stmt.Assign (x, indexes, e) -> (
      let code = List.concat (List.map expr (indexes @ [e])) @ [STA (x, List.length indexes)] in
      env, false, code
    )
    | Stmt.Seq (st1, st2) -> (
      let env, _, code1 = compile_stmt l env st1 in
      let env, _, code2 = compile_stmt l env st2 in
      env, false, code1 @ code2
    )
    | Stmt.Skip -> env, false, []
    | Stmt.If (e, t, f) -> (
      let else_label, env = env#get_label in
      let fi_label, env = env#get_label in
      let env, _, t_compiled = compile_stmt l env t in
      let env, _, f_compiled = compile_stmt l env f in
      env, false, expr e @ [CJMP ("z", else_label)] @ t_compiled @ [JMP fi_label] @ [LABEL else_label] @ f_compiled @ [LABEL fi_label]
    )
    | Stmt.While (e, s) -> (
      let cond_label, env = env#get_label in
      let loop_label, env = env#get_label in
      let env, _, body = compile_stmt l env s in
      env, false, [JMP cond_label] @ [LABEL loop_label] @ body @ [LABEL cond_label] @ expr e @ [CJMP ("nz", loop_label)]
    )
    | Stmt.Repeat (s, e) -> (
      let loop_label, env = env#get_label in
      let env, _, body = compile_stmt l env s in
      env, false, [LABEL loop_label] @ body @ expr e @ [CJMP ("z", loop_label)]
    )
    | Stmt.Call (fun_name, args) -> env, false, call (label fun_name) (List.rev args) true
    | Stmt.Case (e, bs) -> (
      let lend, env = env#get_label in
      let rec traverse branches env lbl n =
        match branches with
        | [] -> env, []
        | (pat, body)::branches' -> (
          let env, _, body_compiled = compile_stmt l env body in
          let lfalse, env = if n = 0 then lend, env else env#get_label in
          let env, code = traverse branches' env (Some lfalse) (n - 1) in
          let env, pattern_code = pattern env lfalse (n = 0) pat in
          env, (match lbl with None -> [] | Some l -> [LABEL l]) @ pattern_code @ bindings pat @ body_compiled @ [LEAVE] @ (if n = 0 then [] else [JMP lend]) @ code
        )
      in
      let env, code = traverse bs env None (List.length bs - 1) in
      env, false, expr e @ code @ [LABEL lend]
    )
    | Stmt.Return e -> (
      match e with
      | None -> env, false, [RET false]
      | Some e' -> env, false, expr e' @ [RET true]
    )
    | Stmt.Leave -> env, false, [LEAVE]
    | _ -> failwith "Undefined Behavior"
  in
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