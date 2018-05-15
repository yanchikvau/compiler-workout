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
    let rec enum i count func =
    if i < count then (func i) :: (enum (i + 1) count func)
    else []
    let update_array  a i x = enum 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

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
    let convert_to_bool value =
      if value == 0 then false else true

    let convert_to_int value =
      if value then 1 else 0

    let binop op left_path right_path = 
    match op with
        | "+"   -> left_path + right_path
        | "-"   -> left_path - right_path
        | "*"   -> left_path * right_path
        | "/"   -> left_path / right_path
        | "%"   -> left_path mod right_path
        | "&&"  -> convert_to_int (convert_to_bool left_path && convert_to_bool right_path)
        | "!!"  -> convert_to_int (convert_to_bool left_path || convert_to_bool right_path)
        | "<"   -> convert_to_int (left_path < right_path)
        | "<="  -> convert_to_int (left_path <= right_path)
        | ">"   -> convert_to_int (left_path > right_path)
        | ">="  -> convert_to_int (left_path >= right_path)
        | "=="  -> convert_to_int (left_path == right_path)
        | "!="  -> convert_to_int (left_path != right_path)
        | _ -> failwith "Unknown operator"
        

    let rec eval env ((status, i, o, r) as conf) expr = 
      match expr with
      | Const (const) -> (status, i, o, Some (Value.of_int const)) 
      | Array (elems) -> let (status, i, o, ret_values) = eval_list env conf elems in env#definition env ".array" ret_values (status, i, o, None)
      | String (str) -> (status, i, o, Some (Value.of_string str))
      | Var (variable) -> (status, i, o, Some (State.eval status variable))
      | Binop (op, left, right) -> 
        let (_, _, _, Some left_path) as conf' = eval env conf left in
        let (status', i', o', Some right_path) = eval env conf' right in
        (status', i', o', Some (Value.of_int (binop op (Value.to_int left_path) (Value.to_int right_path))))
      | Elem (a, indx) -> 
        let (_, _, _, Some value_a) as conf = eval env conf a in 
        let (_, _, _, Some value_indx) as conf = eval env conf indx in 
        env#definition env ".elem" [value_a; value_indx] conf
      | Length a -> 
        let (status, i, o, Some value_a) as conf = eval env conf a in 
        env#definition env ".length" [value_a] conf  
      | Sexp (tag, elems) ->
        let (status, i, o, vs) = eval_list env conf elems in 
        (status, i, o, Some (Value.sexp tag vs)) 
      | Call (name, args) ->  
        let (conf', st_args) = List.fold_left 
                  (fun (conf, res_list) expr -> let (_, _, _, Some value) as conf' = eval env conf expr in (conf', res_list @ [value]))
                  (conf, [])
                  args in
        env#definition env name st_args conf' 
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
    let listop ops =
      List.map (fun op -> ostap($(op)), fun left right -> Binop (op, left, right)) ops

    ostap (
      parse: 
        !(Util.expr
          (fun x -> x)
          [|
            `Lefta, listop ["!!"];
            `Lefta, listop ["&&"];
            `Nona,  listop ["=="; "!=";">="; ">"; "<="; "<"];
            `Lefta, listop ["+"; "-"];
            `Lefta, listop ["*"; "/"; "%"];
          |]
          primary
        );
      primary: 
        e:expr action:(
        -"[" i:parse -"]" {`Elem i} 
        | -"." %"length" {`Len}
      ) * {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) e action};  
      expr:
        name : IDENT "(" args:!(Util.list0)[parse] ")" {Call (name, args)}
        | variable: IDENT {Var (variable)}
        | const: DECIMAL {Const (const)}
        | str:STRING {String (String.sub str 1 (String.length str - 2))}
        | ch:CHAR {Const (Char.code ch)}
        | -"`" tag:IDENT elems:(-"(" !(Util.list)[parse] -")")? {Sexp (tag, match elems with None -> [] | Some elems -> elems)}
        | -"[" elements:!(Util.list0)[parse] -"]" {Array elements}
        | -"(" parse -")"
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
            | "`" tag:IDENT elems:(-"(" !(Ostap.Util.list)[parse] -")")? {Sexp (tag, match elems with None -> [] | Some elems -> elems)}
            | name:IDENT {Ident name}
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
    (* loop with a post-condition       *) | DoWhile of Expr.t * t 
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

    let sequence first second =
    match second with
    | Skip -> first
    | second -> Seq (first, second)

    let rec eval env cnfg k stmt = 
    match cnfg, stmt with
    | (s, i, o, r), Assign (variable, indexes, expr) -> 
      let (s', i', o', indx) = Expr.eval_list env cnfg indexes in
      let (s', i', o', Some value) = Expr.eval env (s', i', o', None) expr in
      eval env (update s' variable value indx, i', o', None) Skip k
    | cnfg, Seq (left, right) -> eval env cnfg (sequence right k) left
    | cnfg, Skip -> 
      (match k with
      | Skip -> cnfg
      | k -> eval env cnfg Skip k
      )
    | (s, i, o, r), If (expr, at, aels) -> 
      let (s',i',o', Some value) as cnfg' = Expr.eval env cnfg expr in
      if Value.to_int value == 0 then eval env cnfg' k aels
      else eval env cnfg' k at
    | (s, i, o, r), While (expr, body) -> 
      let (s',i',o', Some value) as cnfg' = Expr.eval env cnfg expr in
      if Value.to_int value == 0 then eval env cnfg' Skip k
      else eval env cnfg' (sequence stmt k) body
    | (s, i, o, r), DoWhile (expr, body) -> eval env cnfg (sequence (While (Expr.Binop("==", expr, Expr.Const 0), body)) k) body
    | cnfg, Call (name, args) ->
      let (cnfg', st_args) = List.fold_left 
                  (fun (cnfg, res_list) expr -> let (_, _, _, Some value) as cnfg' = Expr.eval env cnfg expr in (cnfg', res_list @ [value]))
                  (cnfg, [])
                  args in
      let cnfg'' = env#definition env name st_args cnfg' in eval env cnfg'' Skip k
    | (s, i, o, r), Return (expr) -> 
      (
      match expr with
      | None -> (s, i, o, None)
      | Some expr -> Expr.eval env cnfg expr
      )
    | (s, i, o, r), Case (expr, patts) ->
     let (s', i', o', Some v) as cnfg = Expr.eval env cnfg expr in 
     let rec patt_val (patt: Pattern.t) (value : Value.t) st = 
       (match patt, value with
       | Wildcard, _ -> Some st
       | Ident x, value -> Some (State.bind x value st)
       | Sexp (tag1, elem1), Sexp (tag2, elem2) when ((tag1 = tag2) && (List.length elem1 = List.length elem2)) -> 
         (List.fold_left2 (fun acc curp curs -> match acc with (Some s) -> (patt_val curp curs s) | None -> None) (Some st) elem1 elem2)
       | _, _ -> None) in
     let rec find_patt ps = 
       (match ps with
         [] -> eval env cnfg Skip k
       | (p, action)::tl -> 
         let match_res = patt_val p v State.undefined in
         (match match_res with
           None -> find_patt tl
         | Some s -> 
           let s'' = State.push s' s (Pattern.vars p) in
           eval env (s'', i', o', None) k (Seq (action, Leave)))) in
     find_patt patts
    | (s, i, o, r), Leave -> eval env (State.drop s, i, o, r) Skip k
    | _, _ -> failwith("Unknown operator")
                                                        
    (* Statement parser *)
    ostap (
      parse: 
        left_stmt:stmt -";" right_stmt:parse {Seq (left_stmt, right_stmt)} | stmt;
      stmt: 
        variable:IDENT indx:(-"[" !(Expr.parse) -"]") * -":=" expr:!(Expr.parse) {Assign (variable, indx, expr)}
        | %"skip" {Skip}
        | %"while" expr:!(Expr.parse) %"do" body:parse %"od" {While (expr, body)}
        | %"repeat" body:parse %"until" expr:!(Expr.parse) {DoWhile (expr, body)}
        | %"for" init:parse -"," expr:!(Expr.parse) -"," loopexpr:parse %"do" body:parse %"od" {Seq (init, While (expr, Seq (body, loopexpr)))}
        | %"if" expr:!(Expr.parse) %"then" at:parse aels:else_body %"fi" {If (expr, at, aels)}
        | name : IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (name, args)}
        | %"return" expr:!(Expr.parse)? {Return (expr)} 
        | %"case" expr:!(Expr.parse) %"of" patterns:!(Ostap.Util.listBy)[ostap ("|")][pattern] %"esac" {Case (expr, patterns)};
      pattern: 
        p:!(Pattern.parse) "->" action:!(parse) {p, action};
      else_body:
        %"else" aels:parse {aels}
        | %"elif" expr:!(Expr.parse) %"then" at:parse aels:else_body {If (expr, at, aels)}
        | "" {Skip}

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