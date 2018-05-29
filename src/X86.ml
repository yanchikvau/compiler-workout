open GT
       
(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4;;

(* We need to distinguish the following operand types: *)
@type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)
with show

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator
     compile : env -> prg -> env * instr list
   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env code =
  let make_mov x y =
    (match x, y with 
    | M _, S _ | S _, S _ | S _, M _ -> [Mov (x, edx); Mov (edx, y)]
    | _, _ -> [Mov (x, y)]) in
  let call env f n p = 
    let f =
      match f.[0] with '.' -> "B" ^ String.sub f 1 (String.length f - 1) | _ -> f in
    let push_reg = List.map (fun x -> Push x) (env#live_registers n)
    and pop_reg = List.rev (List.map (fun x -> Pop x) (env#live_registers n)) in 
    let rec compile_args env' = function
      | 0 -> env', []
      | n -> (let res, env'' = env'#pop in 
          let env'', st = compile_args env'' (n - 1) in 
          env'', st @ [Push res]) in
    let env', args = compile_args env n in
    let env', func_add = 
       (if p then env', []
        else let e, env'' = env'#allocate in env'', make_mov eax e) in
    let args, n = 
      (match f with
      | "Barray" -> [Push (L n)] @ args, n + 1
      | "Bsta" -> 
        let (x::v::indexes) = List.rev args in
        [Push (L (n - 2))] @ [v; x] @ indexes, n + 1
      | "Bsexp" ->
        let (tag::indexes) = List.rev args in
        [Push (L n)] @ (List.rev indexes) @ [tag], n + 1
      | _ -> args, n) in
    env', push_reg @ (List.rev args) @ [Call f; Binop ("+", L (word_size * n), esp)] @ pop_reg @ func_add in
  let rec create_binop op x y = 
    let logic_op op x y = [Mov (y, edx); Binop (op, x, edx)] in
    (match op with
    | "+" -> [Mov (x, eax); Binop ("+", y, eax)], eax
    | "-" -> [Mov (x, eax); Binop ("-", y, eax)], eax
    | "*" -> [Mov (x, eax); Binop ("*", y, eax)], eax
    | "/" -> [Mov (x, eax); Cltd; IDiv y], eax
    | "%" -> [Mov (x, eax); Cltd; IDiv y], edx
    | ">" -> (logic_op "cmp" y x) @ [Mov (L 0, eax); Set ("g", "%al")], eax
    | "<" -> (logic_op "cmp" x y) @ [Mov (L 0, eax); Set ("g", "%al")], eax
    | ">=" -> (logic_op "cmp" y x) @ [Mov (L 0, eax); Set ("ge", "%al")], eax
    | "<=" -> (logic_op "cmp" x y) @ [Mov (L 0, eax); Set ("ge", "%al")], eax
    | "==" -> (logic_op "cmp" x y) @ [Mov (L 0, eax); Set ("e", "%al")], eax
    | "!=" -> (logic_op "cmp" x y) @ [Mov (L 0, eax); Set ("ne", "%al")], eax
    | "&&" -> 
      let x_conv, reg_x = create_binop "!=" x (L 0)
      and y_conv, reg_y = create_binop "!=" y (L 0) in
      x_conv @ [Mov (reg_x, x)] @ y_conv @ [Mov (reg_y, y)] @ (logic_op "&&" x y) @ [Mov (L 0, eax); Set ("nz", "%al")], eax
    | "!!" -> (logic_op "!!" x y) @ [Mov (L 0, eax); Set ("nz", "%al")], eax
    | _ -> failwith "Not implemented binary operator %s\n" @@ op) in
  match code with
  | [] -> (env, [])
  | instr::rest ->
    (* Printf.printf "%s\n" env#show_stack; *)
    (* SM.print_instr instr; *)
    let env', ops = 
      (match instr with
      | BINOP op -> 
        let y, x, env = env#pop2 in
        let e, env = env#allocate
        and new_ops, acc = create_binop op x y in
        (env, new_ops @ (make_mov acc e))
      | CONST n ->
        let x, env = env#allocate in
        (env, make_mov (L n) x)
      | STRING s -> 
        let s, env = env#string s in
        let x, env = env#allocate in
        let env, c = call env ".string" 1 false in
        env, (make_mov (M ("$" ^ s)) x) @ c
      | SEXP (tag, indNum) ->
        let e, env = env#allocate in
        let env, c = call env ".sexp" (indNum + 1) false in
        env, (make_mov (L (env#hash tag)) e) @ c
      | LD x ->
        let e, env = env#allocate in
        (env, make_mov (env#loc x) e)
      | ST x -> 
        let e, env = (env#global x)#pop in
        (env, make_mov e (env#loc x))
      | STA (x, indNum) -> 
        let e, env = (env#global x)#allocate in
        let env, code = call env ".sta" (indNum + 2) true in
        env, (make_mov (env#loc x) e) @ code
      | LABEL l ->
        let env' = if env#is_barrier then (env#drop_barrier)#retrieve_stack l else env in
        (env', [Label l])
      | JMP l -> 
        let env' = (env#set_stack l)#set_barrier in
        (env', [Jmp l])
      | CJMP (op, l) -> 
        let e, env = env#pop in
        let env' = (env#set_stack l) in
        (env', [Binop ("cmp", L 0, e); CJmp (op, l)])
      | BEGIN (name, args, locals) -> 
        let env' = env#enter name args locals in
        env', [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ (env'#lsize)), esp)]
      | END -> env, [Label (env#epilogue); Mov (ebp, esp); Pop ebp; Ret; Meta (Printf.sprintf "\t.set\t%s,\t%d" env#lsize (env#allocated * word_size))]
      | CALL (name, argnum, isProc) -> call env name argnum isProc
      | RET isFunc ->
        if isFunc then let ret, env' = env#pop in env', (make_mov ret eax) @ [Jmp env'#epilogue]
        else env, [Jmp env#epilogue]
      | DROP -> 
        let _, env' = env#pop in env', []
      | DUP -> 
        let peek = env#peek in
        let x, env = env#allocate in
        env, make_mov peek x
      | SWAP ->
        let x, y = env#peek2 in
        env, [Push ebp; Mov (x, ebp)] @ (make_mov y x) @ [Mov (ebp, y); Pop ebp]
      | TAG s ->
        let htag = env#hash s in
        let e, env = env#allocate in
        let env, code = call env ".tag" 2 false in
        env, (make_mov (L htag) e) @ code
      | ENTER xs -> 
        let env, c = List.fold_left
          (fun (env', acc) _ -> let e, env'' = env'#pop in env'', acc @ [e]) (env, []) xs in
        let env = env#scope xs in
        let code = List.fold_left2 (fun acc s x -> acc @ (make_mov s (env#loc x))) [] c xs in
        env, code
      | LEAVE -> env#unscope, []) in
    let newenv, op_list = compile env' rest in
    (newenv, ops @ op_list);;

(* A set of strings *)           
module S = Set.Make (String) 

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let list_init len = function func -> 
  let rec init' cur = if cur >= len then [] else [func cur] @ (init' (cur + 1)) in
  init' 0 in 
  let make_assoc l i = List.combine l (list_init (List.length l) (fun x -> x + i)) in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)
                        
    method show_stack =
      GT.show(list) (GT.show(opnd)) stack
             
    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}
                            
    (* associates a stack to a label *)
    method set_stack l = {< stackmap = M.add l stack stackmap >}
                               
    (* retrieves a stack for a label *)
    method retrieve_stack l =
      try {< stack = M.find l stackmap >} with Not_found -> self
                               
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
  let rec allocate' = function
  | []                            -> ebx          , 0
  | (S n)::_                      -> S (n+1)      , n+2
  | (R n)::_ when n < num_of_regs -> R (n+1)      , stack_slots
  | _                             -> S static_size, static_size+1
  in
  allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
             
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

    (* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}
        
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  (* SM.print_prg f; *)
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)