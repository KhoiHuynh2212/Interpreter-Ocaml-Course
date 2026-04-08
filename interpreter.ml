(* ── Utilities ──────────────────────────────────────────────────────────── *)
let is_bool w = w = ":true:" || w = ":false:"
(* Drop a trailing '\r' from a string, if present *)
let trim_crlf str =
  let size = String.length str in
  if size > 0 && str.[size - 1] = '\r' then String.sub str 0 (size - 1)
  else str

(* Check whether a string is a valid decimal integer *)
let looks_like_int word =
  try ignore (int_of_string word); true
  with Failure _ -> false

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
let run_neg stack = match stack with
  | []              -> ":error:" :: []
  | head :: beneath ->
    if looks_like_int head then
      string_of_int (- (int_of_string head)) :: beneath
    else
      ":error:" :: head :: beneath 

let run_cat stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: []
  | top :: next :: tl -> 
    if looks_like_int top || looks_like_int next 
       || top = ":true:" || top = ":false:"
       || next = ":true:" || next = ":false:"
       || top = ":error:" || next = ":error:"
       || top = ":unit:"  || next = ":unit:"
    then ":error:" :: top :: next :: tl
    else (next ^ top) :: tl 

let run_and stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    if not (is_bool top) || not (is_bool nxt) then 
      ":error:" :: top :: nxt:: tl
    else if top = ":true:" && nxt = ":true:" then 
      ":true:" :: tl
    else    
      ":false:" :: tl

let run_or stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    if not (is_bool top) || not (is_bool nxt) then 
      ":error:" :: top :: nxt:: tl
    else if top = ":true:" || nxt = ":true:" then 
      ":true:" :: tl
    else    
      ":false:" :: tl

let run_not stack = match stack with
  | []              -> ":error:" :: []
  | head :: tl      ->
    if not(is_bool head) then ":error:" :: head :: tl
    else if head = ":true:" then
      ":false:" :: tl
    else
      ":true:" :: tl
let run_equal stack = match stack with 
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: [] 
  | top :: nxt :: tl -> 
    if not (looks_like_int top) || not( looks_like_int nxt) then 
      ":error:" :: top :: nxt :: tl
    else if (top = nxt) then 
      ":true:" :: tl 
    else   
      ":false:" :: tl
let run_lessThan stack = match stack with
  | []              -> ":error:" :: []
  | head :: []      -> ":error:" :: head :: []
  | top :: nxt :: tl -> 
     if not (looks_like_int top) || not( looks_like_int nxt) then 
      ":error:" :: top :: nxt :: tl 
    else if int_of_string nxt < int_of_string top then 
      ":true:" :: tl 
    else   
      ":false:" :: tl

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
let run_command write stack raw_line =
  match quoted_push_arg raw_line with
  | Some contents -> contents :: stack
  | None ->
    let parts = String.split_on_char ' ' (String.trim raw_line) in
    (match parts with
    | "push"     :: word :: _ -> push_token word stack
    | "push"     :: []        -> stack
    | "pop"      :: _         -> drop_top stack
    | "add"      :: _         -> run_add stack
    | "sub"      :: _         -> run_sub stack
    | "mul"      :: _         -> run_mul stack
    | "div"      :: _         -> run_div stack
    | "rem"      :: _         -> run_rem stack
    | "neg"      :: _         -> run_neg stack
    | "cat"      :: _         -> run_cat stack
    | "and"      :: _         -> run_and stack 
    | "or"       :: _         -> run_or stack 
    | "not"      :: _         -> run_not stack
    | "equal"    :: _         -> run_equal stack
    | "swap"     :: _         -> run_swap stack
    | "toString" :: _         -> run_to_string stack
    | "println"  :: _         -> run_println write stack
    | "quit"     :: _         -> stack
    | _                       -> stack)

(* ── Entry point ────────────────────────────────────────────────────────── *)

let interpreter ((src : string), (dst : string)) : unit =
  let in_chan   = open_in  src in
  let out_chan  = open_out dst in
  let write ln  = Printf.fprintf out_chan "%s\n" ln in
  let commands  = load_lines in_chan in
  let remaining = List.fold_left (run_command write) [] commands in
  List.iter write remaining;
  close_in  in_chan;
  close_out out_chan
;;