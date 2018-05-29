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
let print_instr i = Printf.printf "%s\n" (show(insn) i);
                            
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
          
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg =
  match prg with
  | [] -> conf
  | inst :: tail -> 
    (* print_instr inst; *)
    let cfg, next = 
     (match inst with      
      | BINOP binop -> 
        (match stack with 
            y :: x :: st_end -> (cstack, Value.of_int (Expr.calc binop (Value.to_int x) (Value.to_int y)) :: st_end, c), tail
          | _ -> failwith "Not enough arguments for binary operation")
      | CONST n -> (cstack, (Value.of_int n) :: stack, c), tail
      | STRING s -> (cstack, (Value.of_string s) :: stack, c), tail
      | SEXP (s, vals) -> let exprs, rest = split vals stack in (cstack, (Value.sexp s (List.rev exprs)) :: rest, c), tail
      | LD x -> (cstack, (State.eval st x) :: stack, c), tail
      | ST x -> let num = List.hd stack in (cstack, List.tl stack, (State.update x num st, i, o)), tail
      | STA (x, count) -> let value::taken, rest = split (count + 1) stack in
                (cstack, rest, (Stmt.update st x value taken, i, o)), tail
      | LABEL _ -> conf, tail
      | JMP l -> conf, (env#labeled l)
      | CJMP (op, l) ->
        let cmp = Value.to_int (List.hd stack) in
        let ret = if (op = "z" && cmp = 0) || (op = "nz" && cmp <> 0) then (env#labeled l) else tail in
        (cstack, List.tl stack, c), ret
      | BEGIN (_, params, locals) ->
        let new_st = State.enter st (params @ locals) in
        let args, rest = split (List.length params) stack in
        let st' = List.fold_left2 (fun ast p v -> State.update p v ast) new_st params (List.rev args) in
        (cstack, rest, (st', i, o)), tail
      | END | RET _ -> 
         (match cstack with
        | [] -> conf, []
        | (prg', st') :: rest -> 
          let new_st = State.leave st st' in
          (rest, stack, (new_st, i, o)), prg')
      | CALL (proc, argCount, isProc) -> if env#is_label proc then ((tail, st) :: cstack, stack, c), (env#labeled proc) 
                       else (env#builtin conf proc argCount isProc), tail
      | DROP -> (cstack, List.tl stack, c), tail
      | DUP -> let hd::_ = stack in (cstack, hd::stack, c), tail
      | SWAP -> let x::y::rest = stack in (cstack, y::x::rest, c), tail
      | TAG s -> let sexp::tl = stack in let res = if s = Value.tag_of sexp then 1 else 0 in (cstack, (Value.of_int res)::tl, c), tail
      | ENTER es -> 
        let vals, rest = split (List.length es) stack in
        let st' = List.fold_left2 (fun ast e var -> State.bind var e ast) State.undefined vals es in 
            (cstack, rest, (State.push st st' es, i, o)), tail
      | LEAVE -> (cstack, stack, (State.drop st, i, o)), tail) in
    eval env cfg next;;

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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
  and pattern env p lfalse =
  (match p with
  | Stmt.Pattern.Wildcard -> env, [DROP]
  | Stmt.Pattern.Ident x -> env, [DROP]
  | Stmt.Pattern.Sexp (tag, ps) ->
    let faillbl, env = env#get_label in
    let oklbl, env = env#get_label in
    let env, res, _ = List.fold_left
            (fun (env', acc, pos) pat -> 
              let env'', newpat = pattern env' pat faillbl in
              env'', (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ newpat), pos + 1) 
           (env, [], 0) ps in
    env, [DUP; TAG tag; CJMP ("nz", oklbl); LABEL faillbl; DROP; JMP lfalse; LABEL oklbl] @ res @ [DROP])
  and bindings p = 
  let rec bind cp cur =   
    (match cp with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident _ -> cur @ [SWAP]
    | Stmt.Pattern.Sexp (_, xs) ->
      fst @@ (List.fold_left (fun (acc, pos) x ->  (acc @ bind x (cur @ [CONST pos; CALL (".elem", 2, false)]), pos + 1)) ([], 0) xs)) in
  let code = 
  (match p with
  | Stmt.Pattern.Wildcard -> []
  | Stmt.Pattern.Ident _ -> [DUP; SWAP]
  | Stmt.Pattern.Sexp (_, xs) -> 
    (fst @@ (List.fold_left (fun (acc, pos) x -> (acc @ bind x [DUP; CONST pos; CALL (".elem", 2, false)]), pos + 1) ([], 0) xs))) in
  code @ [DROP; ENTER (Stmt.Pattern.vars p)]
  and expr e =
  (match e with
    | Expr.Const n -> [CONST n]
    | Expr.Array a -> call ".array" a false 
    | Expr.Sexp (s, exprs) -> let args = List.fold_left (fun acc index -> acc @ (expr index)) [] exprs in args @ [SEXP (s, List.length exprs)]
    | Expr.String s -> [STRING s]
    | Expr.Var x -> [LD x]
    | Expr.Binop (binop, x, y) -> expr x @ expr y @ [BINOP binop]
    | Expr.Elem (v, e) -> call ".elem" [v; e] false
    | Expr.Length l -> call ".length" [l] false
    | Expr.Call (proc, args) -> call (label proc) args false) in
  let rec compile_stmt l env stmt =
  (match stmt with
      Stmt.Assign (x, args, e) -> 
      (match args with
        [] -> env, false, expr e @ [ST x]
      | args -> let indexes = List.fold_left (fun acc index -> acc @ (expr index)) [] args in 
            env, false, (List.rev indexes @ expr e @ [STA (x, List.length args)]))
    | Stmt.Seq (stmt_left, stmt_right) ->
      let env, _, left = compile_stmt l env stmt_left in
      let env, _, right = compile_stmt l env stmt_right in
      env, false, left @ right
    | Stmt.Skip -> env, false, []
    | Stmt.If (cond, t, f) ->
      let flbl, env = env#get_label in
      let endlbl, env = env#get_label in
      let env, _, ift = compile_stmt l env t in
      let env, _, iff = compile_stmt l env f in
      let instr = 
        match f with
        | Skip -> [LABEL flbl]
        | _ -> [JMP endlbl; LABEL flbl] @ iff @ [LABEL endlbl] in
      env, false, (expr cond) @ [CJMP ("z", flbl)] @ ift @ instr
    | Stmt.While (cond, st) ->
      let initlbl, env = env#get_label in
      let endlbl, env = env#get_label in
      let env, _, body = compile_stmt l env st in
      env, false, [JMP endlbl; LABEL initlbl] @ body @ [LABEL endlbl] @ (expr cond) @ [CJMP ("nz", initlbl)]
    | Stmt.Repeat (st, cond) ->
      let initlbl, env = env#get_label in
      let env, _, body = compile_stmt l env st in
      env, false, [LABEL initlbl] @ body @ (expr cond) @ [CJMP ("z", initlbl)]
    | Stmt.Case (e, patterns) ->
      let rec comp_pat ps env lbl isFirst lend = 
        (match ps with
          [] -> env, []
        | (p, act)::tl -> 
          let env, _, body = compile_stmt l env act in 
          let lfalse, env = if List.length tl = 0 then lend, env else env#get_label
          and start = if isFirst then [] else [LABEL lbl] in
          let env, code = comp_pat tl env lfalse false lend in
          let env, code_pat = pattern env p lfalse in
          env, start @ [DUP] @ code_pat @ bindings p @ body @ [JMP lend] @ code) in
      let lend, env = env#get_label in
      let env, code = comp_pat patterns env "" true lend in
      env, false, (expr e) @ code @ [LABEL lend]
    | Stmt.Return e -> 
      let ret, isFunc =
      (match e with
      | None -> [], false
      | Some p -> (expr p), true) in
      env, false, ret @ [RET isFunc]
    | Stmt.Call (proc, args) -> env, false, call (label proc) args true
    | Stmt.Leave -> env, false, [LEAVE]) in
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