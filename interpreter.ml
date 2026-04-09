(* ── Utilities ──────────────────────────────────────────────────────────── *)
let is_bool w = w = ":true:" || w = ":false:"
(* Drop a trailing '\r' from a string, if present *)
let trim_crlf str =
  let size = String.length str in
  if size > 0 && str.[size - 1] = '\r' then String.sub str 0 (size - 1)
  else str

let is_integer tok =
  try ignore (int_of_string tok); true
  with Failure _ -> false 

let looks_like_int tok = is_integer tok

let is_name w =
  let n = String.length w in
  n > 0
  && (w.[0] = '_' || (w.[0] >= 'a' && w.[0] <= 'z') || (w.[0] >= 'A' && w.[0] <= 'Z'))
  && String.for_all (fun c ->
       c = '_'
       || (c >= 'a' && c <= 'z')
       || (c >= 'A' && c <= 'Z')
       || (c >= '0' && c <= '9')
     ) w 

(* Anything that is not a plain string value *)
let is_non_string w =
  is_integer w || is_bool w || w = ":error:" || w = ":unit:"

type env = (string * string) list list 

let empty_env : env = [[]]

(* Look up a name, searching from the innermost scope outward *)
let rec lookup name = function
  | []           -> None
  | scope :: rest ->
    (match List.assoc_opt name scope with
     | Some v -> Some v
     | None   -> lookup name rest)

     
(* Bind a name in the current (innermost) scope *)
let bind name value = function
  | []           -> [(name, value)] :: []   (* should not happen *)
  | scope :: rest -> ((name, value) :: List.remove_assoc name scope) :: rest 

let push_scope env = [] :: env

let pop_scope = function
  | []           -> ([], [])
  | scope :: rest -> (scope, rest)
 
(* Resolve a token: if it is a bound name return its value, else return as-is.
   Returns None if the name exists but is unbound. *)
let resolve tok env =
  if is_name tok then lookup tok env
  else Some tok
 

(* ── Stack operations ───────────────────────────────────────────────────── *)

(* Push a single token onto the stack, handling quoted strings and "-0" *)
let push_token word stack =
  let size = String.length word in
  if size >= 2 && word.[0] = '"' && word.[size - 1] = '"' then
    String.sub word 1 (size - 2) :: stack          (* strip surrounding quotes *)
  else if size >= 2 && word.[0] = '-' && word.[1] = '0' then
    "0" :: stack                                    (* normalise negative zero  *)
  else
    word :: stack

(* Remove the top of the stack; push :error: if it is empty *)
let drop_top stack = match stack with
  | []           -> ":error:" :: stack
  | _ :: beneath -> beneath


let int_binop op guard_zero env stack = match stack with 
  | []               -> ":error:" :: []
  | only :: []       -> ":error:" :: only :: []
  | rhs :: lhs :: tl -> 
    let lhs' = resolve lhs env in 
    let rhs' = resolve rhs env in 
    (match lhs', rhs' with
    | Some lv, Some rv when is_integer lv && is_integer rv -> 
      if guard_zero && rv = "0" then ":error:" :: rhs ::lhs :: tl 
      else string_of_int(op(int_of_string lv ) (int_of_string rv)) :: tl
    |_ -> ":error:" :: rhs :: lhs :: tl)

(* Generic integer binary operation.
   [div_guard] enables the division-by-zero safety check. *)
let arith_binop op div_guard stack = match stack with
  | []               -> ":error:" :: []
  | only :: []       -> ":error:" :: only :: []
  | rhs :: lhs :: tl ->
    if not (looks_like_int lhs) || not (looks_like_int rhs) then
      ":error:" :: rhs :: lhs :: tl
    else if div_guard && rhs = "0" then
      ":error:" :: rhs :: lhs :: tl
    else
      string_of_int (op (int_of_string lhs) (int_of_string rhs)) :: tl

let run_add stack = arith_binop ( + )   false stack
let run_sub stack = arith_binop ( - )   false stack
let run_mul stack = arith_binop ( * )   false stack
let run_div stack = arith_binop ( / )   true  stack
let run_rem stack = arith_binop ( mod ) true  stack

(* Negate the top integer; push :error: when empty or non-integer *)
let run_neg env stack = match stack with
  | []              -> ":error:" :: []
  | head :: beneath ->
    (match resolve head env with 
    | Some v when is_integer v -> string_of_int (-(int_of_string v)) :: beneath 
    | _ -> ":error:" :: head :: beneath) 

(* Swap the top two elements; push :error: when fewer than two exist *)
let run_swap stack = match stack with
  | []               -> ":error:" :: []
  | top :: []        -> ":error:" :: top :: []
  | top :: nxt :: tl -> nxt :: top :: tl

(* Convert top of stack to string representation (values are already
   stored as strings, so this is a no-op unless the stack is empty) *)
let run_to_string stack = match stack with
  | [] -> ":error:" :: []
  | _  -> stack

(* Print and discard the top element via [write]; push :error: if empty *)
let run_println write stack = match stack with
  | []              -> ":error:" :: []
  | head :: beneath -> write head; beneath


let run_cat stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: []
  | top :: next :: tl -> 
    if is_non_string top || is_non_string next then 
      ":error:" :: top :: next :: tl
    else 
      (next ^ top) :: tl 

let run_and env stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    let top' = resolve top env in 
    let nxt' = resolve nxt env in 
    (match top', nxt' with 
    | Some tv, Some nv when is_bool tv && is_bool nv -> 
      (if tv = ":true:" && nv = ":true:" then ":true:" else ":false:") :: tl
    |_-> ":error:" :: top :: nxt :: tl)

let run_or env stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    let top' = resolve top env in 
    let nxt' = resolve nxt env in 
    (match top', nxt' with 
    | Some tv, Some nv when is_bool tv && is_bool nv -> 
      (if tv = ":true:" || nv = ":true:" then ":true:" else ":false:") :: tl
    |_-> ":error:" :: top :: nxt :: tl)

let run_not env stack = match stack with
  | []              -> ":error:" :: []
  | top :: tl      ->
    (match resolve top env with 
    | Some v when is_bool v -> 
      (if v = ":true:" then ":false:" else ":true:") :: tl
    | _ -> ":error:" :: top :: tl) 
let run_equal env stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    let top' = resolve top env in 
    let nxt' = resolve nxt env in  
    (match top', nxt' with 
    | Some tv, Some nv when is_integer tv && is_integer nv -> (if tv = nv then ":true:" else ":false:") :: tl
    |_  -> ":error:" :: top :: nxt :: tl)

let run_lessThan env stack = match stack with
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: []
  | top :: nxt :: tl -> 
    let top' = resolve top env in 
    let nxt' = resolve nxt env in  
    (match top', nxt' with 
    | Some tv, Some nv when is_integer tv && is_integer nv -> (if int_of_string nv < int_of_string tv then ":true:" else ":false:") :: tl
    |_ -> ":error:" :: top :: nxt :: tl)

(* Bind: pop value then name, store in env, push :unit: *)
let run_bind env stack = match stack with 
  | []        -> (":error:" :: [], env)
  | v :: [] -> (":error:" :: v :: [], env)
  | v :: name :: tl ->    
    if not(is_name name) then 
      (":error:" :: v :: name :: tl, env)
    else 
      let resolved = if is_name v then lookup v env else Some v in 
      (match resolved with 
      | None -> (":error:" :: v :: name :: tl, env)
      | Some actual -> 
        if actual = ":error:" then 
          (":error:" :: v :: name :: tl, env)
        else  
          (":unit:" :: tl, bind name actual env))

let run_if stack = match stack with
  | []                    -> ":error:" :: []
  | x :: []               -> ":error:" :: x :: []
  | x :: y :: []          -> ":error:" :: x :: y :: []
  | x :: y :: z :: tl     ->
    if not (is_bool z) then ":error:" :: x :: y :: z :: tl
    else if z = ":true:"  then x :: tl
    else y :: tl
(* ── IO helpers ─────────────────────────────────────────────────────────── *)

(* Collect every line from [chan] into a list *)
let load_lines chan =
  let rec collect acc =
    match (try Some (input_line chan) with End_of_file -> None) with
    | None     -> List.rev acc
    | Some raw -> collect (trim_crlf raw :: acc)
  in
  collect []

(* When a push line contains a quoted string we must bypass the normal
   whitespace tokeniser to preserve spaces inside the quotes.
   Returns [Some contents] when the line is a quoted push, else [None]. *)
let quoted_push_arg raw_line =
  let line    = String.trim raw_line in
  let cmd     = "push " in
  let cmdlen  = String.length cmd in
  let linelen = String.length line in
  if linelen > cmdlen
     && String.sub line 0 cmdlen = cmd
     && String.contains line '"'
  then
    let after_cmd = String.trim (String.sub line cmdlen (linelen - cmdlen)) in
    let alen = String.length after_cmd in
    if alen >= 2 && after_cmd.[0] = '"' && after_cmd.[alen - 1] = '"' then
      Some (String.sub after_cmd 1 (alen - 2))
    else None
  else None

(* ── Dispatcher ─────────────────────────────────────────────────────────── *)

(* Process one program line against [stack]; [write] is the output sink *)
let run_command write env stack raw_line =
  match quoted_push_arg raw_line with
  | Some contents -> (contents :: stack, env)
  | None ->
    let parts = String.split_on_char ' ' (String.trim raw_line) in
    (match parts with
    | "push"     :: word :: _ -> (push_token word stack, env)
    | "push"     :: []        -> (stack, env)
    | "pop"      :: _         -> (drop_top stack, env)
    | "add"      :: _         -> (run_add stack, env)
    | "sub"      :: _         -> (run_sub stack, env)
    | "mul"      :: _         -> (run_mul stack, env)
    | "div"      :: _         -> (run_div stack, env)
    | "rem"      :: _         -> (run_rem stack, env)
    | "neg"      :: _         -> (run_neg env stack, env)
    | "cat"      :: _         -> (run_cat stack, env)
    | "and"      :: _         -> (run_and env stack, env)
    | "or"       :: _         -> (run_or env stack, env)
    | "not"      :: _         -> (run_not env stack, env)
    | "equal"    :: _         -> (run_equal env stack, env)
    | "lessThan" :: _         -> (run_lessThan env stack, env)
    | "blind"    :: _         -> run_bind env stack
    | "if"       :: _         -> (run_if stack, env)
    | "swap"     :: _         -> (run_swap stack, env)
    | "toString" :: _         -> (run_to_string stack, env)
    | "println"  :: _         -> 
      (match stack with 
      | []        -> (":error:" :: [], env)
      | top :: tl -> write top; (tl, env))
    | "quit"     :: _         -> (stack, env)
    | _                       -> (stack, env))

(* ── Entry point ────────────────────────────────────────────────────────── *)

let interpreter ((src : string), (dst : string)) : unit =
  let in_chan  = open_in  src in
  let out_chan = open_out dst in
  let write ln = Printf.fprintf out_chan "%s\n" ln in
  let program  = load_lines in_chan in
  let (final_stack, _) =
    List.fold_left (fun (stk, e) line -> run_command write e stk line) ([], empty_env) program
  in
  List.iter write final_stack;
  close_in  in_chan;
  close_out out_chan
;;