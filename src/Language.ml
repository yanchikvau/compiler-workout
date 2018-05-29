(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
  let list_init len = function func -> 
    let rec init' cur = if cur >= len then [] else [func cur] @ (init' (cur + 1)) in
    init' 0
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
          (* Printf.printf "%s\n" (show(Value.t) b); *)
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator
          val eval : env -> config -> t -> int * config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let calc binop x y = 
    let val_to_bool x = x <> 0
    and logic_calc logic_op x y = if logic_op x y then 1 else 0 in
      match binop with
      | "+" -> x + y
      | "-" -> x - y
      | "*" -> x * y
      | "/" -> x / y
      | "%" -> x mod y
      | "<" -> logic_calc (<) x y
      | ">" -> logic_calc (>) x y
      | "<=" -> logic_calc (<=) x y
      | ">=" -> logic_calc (>=) x y
      | "==" -> logic_calc (=) x y
      | "!=" -> logic_calc (<>) x y
      | "&&" -> logic_calc (&&) (val_to_bool x) (val_to_bool y)
      | "!!" -> logic_calc (||) (val_to_bool x) (val_to_bool y)
      | _ -> failwith "No such binary operator";;  
    
    let rec eval env ((st, i, o, r) as conf) expr =
    (match expr with
      | Const value -> (st, i, o, Some (Value.of_int value))
      | Array a ->
        let (st', i', o', exprs) = eval_list env conf a in 
        (st', i', o', Some (Value.of_array exprs))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Sexp (str, l) ->
        let (st', i', o', exprs) = eval_list env conf l in
        (st', i', o', Some (Value.sexp str exprs))
      | Var x -> (st, i, o, Some (State.eval st x))
      | Binop (binop, x, y) -> 
        let (_, _, _, Some cx) as conf = eval env conf x in
        let (st'', i'', o'', Some cy) as conf = eval env conf y in
        (st'', i'', o'', Some (Value.of_int (calc binop (Value.to_int cx) (Value.to_int cy))))
      | Elem (e, index) -> 
        let (_, _, _, Some ce) as conf = eval env conf e in
        let (_, _, _, Some cx) as conf = eval env conf index in 
        env#definition env ".elem" [ce; cx] conf
      | Length l -> 
        let (_, _, _, Some cl) as conf = eval env conf l in 
        env#definition env ".length" [cl] conf
      | Call (proc, args) -> 
        let (c'', params) = List.fold_left (fun (c', vals) p -> let (st', i', o', Some r') = eval env c' p in ((st', i', o', Some r'), [r'] @ vals)) (conf, []) args in
        env#definition env proc (List.rev params) c'')
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse: expr;
    expr: 
    !(Ostap.Util.expr
      (fun x -> x)
      (Array.map (fun (pr, ops) -> pr, List.map (fun op -> ostap(- $(op)), (fun x y -> Binop (op, x, y))) ops)
      [|
        `Lefta, ["!!"]; 
        `Lefta, ["&&"]; 
        `Nona, ["<="; ">="; "<"; ">"; "=="; "!="];
        `Lefta, ["+"; "-"]; 
        `Lefta, ["*"; "/"; "%"]; 
      |])
      simple_elem
    );
    simple_elem: s:!(atom) e:(elem_get | len)* {List.fold_left (fun acc cur -> match cur with Some x -> Elem (acc, x) | None -> Length acc) s e}; 
    atom: fun_call | sexp | num:DECIMAL {Const num} | s:STRING {String (String.sub s 1 ((String.length s) - 2))} | x:IDENT {Var x} | c:CHAR {Const Char.code c} | arr | -"(" parse -")";
    elem_get: "[" e:!(parse) "]" {Some e};
    len: %".length" {None};
    arr: "[" elems:!(Ostap.Util.listBy)[ostap (",")][parse]? "]" {Array (match elems with Some e -> e | None -> [])};
    fun_call: x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][parse]? ")" {Call (x, match params with Some s -> s | None -> [])};
    sexp: "`" x:IDENT params:(-"(" !(Ostap.Util.listBy)[ostap (",")][parse] -")")? {Sexp (x, match params with Some s -> s | None -> [])}
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:
        "_" {Wildcard}
      | "`" x:IDENT params:(-"(" !(Ostap.Util.listBy)[ostap (",")][parse] -")")? {Sexp (x, match params with Some s -> s | None -> [])}
      | x:IDENT {Ident x}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt =
    let merge stmt1 stmt2 = 
      (match stmt2 with
      | Skip -> stmt1
      | _ -> Seq(stmt1, stmt2)) in
    match stmt with
    | Assign (x, args, expr) -> 
      let (_, _, _, evals) = Expr.eval_list env conf args in
      let (st', i', o', Some v) = Expr.eval env conf expr in
      eval env ((update st' x v evals), i', o', r) Skip k
    | Seq (stmt_left, stmt_right) -> 
      eval env conf (merge stmt_right k) stmt_left
    | Skip -> 
      (match k with
      | Skip -> conf
      | _ -> eval env conf Skip k)
    | If (cond, t, f) ->
      let (st', i', o', Some v) = Expr.eval env conf cond in
      eval env conf k (if (Value.to_int v) <> 0 then t else f)
    | While (cond, stmt) -> eval env conf k (If (cond, Seq (stmt, While (cond, stmt)), Skip))
    | Repeat (stmt, cond) -> eval env conf k (Seq (stmt, If (cond, Skip, Repeat (stmt, cond))))
    | Case (expr, pats) ->
      let (st', i', o', Some v) as conf = Expr.eval env conf expr in 
      let rec match_pat (p : Pattern.t) (value : Value.t) state = 
        (match p, value with
          Wildcard, _ -> Some state
        | Ident x, value -> Some (State.bind x value state)
        | Sexp (t, ep), Sexp (t', ev) when ((t = t') && (List.length ep = List.length ev)) -> 
          (List.fold_left2 (fun acc curp curs -> match acc with (Some s) -> (match_pat curp curs s) | None -> None) (Some state) ep ev)
        | _, _ -> None) in
      let rec check_pat ps = 
        (match ps with
          [] -> eval env conf Skip k
        | (p, act)::tl -> 
          let match_res = match_pat p v State.undefined in
          (match match_res with
            None -> check_pat tl
          | Some s -> 
            let st'' = State.push st' s (Pattern.vars p) in
            eval env (st'', i', o', None) k (Seq (act, Leave)))) in
      check_pat pats
    | Return expr -> 
      (match expr with
      | None -> conf
      | Some e -> Expr.eval env conf e)
    | Call (proc, args) -> eval env (Expr.eval env conf (Expr.Call (proc, args))) Skip k
    | Leave -> eval env (State.drop st, i, o, r) Skip k;;
                                                        
    (* Statement parser *)
    ostap (
      parse: full_stmt;
    full_stmt: <s::xs> :!(Ostap.Util.listBy)[ostap (";")][stmt] {List.fold_left (fun acc y -> Seq (acc, y)) s xs};
    stmt: 
      x:IDENT a:!(args)* ":=" e:!(Expr.parse) {Assign (x, a, e)}
    | %"skip" {Skip}
    | cond:!(if_cond) {cond}
    | %"case" e:!(Expr.parse) %"of" patterns:!(Ostap.Util.listBy)[ostap ("|")][pat] %"esac" {Case (e, patterns)}
    | %"while" cond:!(Expr.parse) %"do" st:!(parse) %"od" {While (cond, st)}
    | %"repeat" st:!(parse) %"until" cond:!(Expr.parse) {Repeat (st, cond)}
    | %"for" init:!(stmt) "," cond:!(Expr.parse) "," step:!(stmt) %"do" st:!(parse) %"od" {Seq(init, While (cond, Seq(st, step)))}
    | x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][Expr.parse]? ")" {Call (x, match params with Some s -> s | None -> [])}
    | %"return" expr:!(Expr.parse)? {Return expr};
    args: "[" e:!(Expr.parse) "]" {e};
    pat: p:!(Pattern.parse) "->" exprs:!(parse) {p, exprs};
    if_cond:
      %"if" cond:!(Expr.parse) %"then" st:!(parse) el:!(else_block)? %"fi" {If (cond, st, match el with Some s -> s | None -> Skip)};
    else_block:
      %"elif" cond:!(Expr.parse) %"then" st:!(parse) next:!(else_block)? {If (cond, st, match next with Some s -> s | None -> Skip)}
    | %"else" st:!(parse) {st}
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))