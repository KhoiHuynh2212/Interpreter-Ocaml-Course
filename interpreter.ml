
(*Reserve keyword*)
let keyword_list = [
  "push"; "pop"; "add"; "sub"; "mul"; "div"; "rem"; "neg"; "swap";
  "cat"; "and"; "or"; "not"; "equal"; "lessThan"; "bind"; "if";
  "let"; "end"; "quit"; "toString"; "println"; 
  "fun"; "funEnd"; "call"; "return"; "inOutFun"
]

(* Create a hash table sized appropriately for our keyword list *)
let reserved_keywords = Hashtbl.create (List.length keyword_list) 

(* Populate the hash table (we map the string to unit () since we just need to check existence) *)
let () = List.iter (fun kw -> Hashtbl.add reserved_keywords kw ()) keyword_list

(* Helper function to check if a string is a reserved keyword *)
let is_keyword w = Hashtbl.mem reserved_keywords w

(* Value type*)
type value =

  | VInt  of int

  | VBool of bool

  | VStr  of string    (* quoted string literal – distinct from VName *)

  | VName of string    (* unresolved name token *)

  | VUnit

  | VError 

  | VClosure of env * string * string list

and env = (string * value) list list   (* stack of scopes, innermost first *)
let show = function

  | VInt  n -> string_of_int n

  | VBool b -> if b then ":true:" else ":false:"

  | VStr  s -> s

  | VName n -> n

  | VUnit   -> ":unit:"

  | VError  -> ":error:"

  | VClosure _ -> ":fun:"

(* Utilities*)


let trim_crlf s =

  let n = String.length s in

  if n > 0 && s.[n-1] = '\r' then String.sub s 0 (n-1) else s


let is_int_string tok =

  try ignore (int_of_string tok); true

  with Failure _ -> false


let is_name_string w =

  let n = String.length w in

  n > 0

  && (w.[0] = '_' || (w.[0] >= 'a' && w.[0] <= 'z') || (w.[0] >= 'A' && w.[0] <= 'Z'))

  && String.for_all (fun c ->

       c = '_'

       || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

       || (c >= '0' && c <= '9')) w


(* Parse a raw token into a value (used by push) *)

let parse_value tok =

  if tok = ":true:"      then VBool true

  else if tok = ":false:" then VBool false

  else if tok = ":error:" then VError

  else if tok = ":unit:"  then VUnit

  else if is_int_string tok then VInt (int_of_string tok)

  else if is_name_string tok then VName tok

  else VError   (* unrecognised token -> :error: per spec *)



(* Environment*)

let empty_env : env = [[]]

let rec lookup name = function

  | [] -> None

  | scope :: rest ->

    (match List.assoc_opt name scope with

     | Some v -> Some v

     | None   -> lookup name rest)


let bind_in_env name v = function

  | [] -> [[(name, v)]]

  | scope :: rest ->

    ((name, v) :: List.remove_assoc name scope) :: rest


let push_scope env = [] :: env


let resolve v env =

  match v with

  | VName n -> lookup n env

  | other   -> Some other


let resolve_or_error v env =

  match resolve v env with Some r -> r | None -> VError


(* Stack helpers  *)

type stack = value list


let run_pop = function

  | []        -> VError :: []

  | _ :: rest -> rest


let run_swap = function

  | []           -> VError :: []

  | x :: []      -> VError :: x :: []

  | x :: y :: tl -> y :: x :: tl



(* Arithmetic *)


let int_binop op guard_zero env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | rhs :: lhs :: tl ->

    (match resolve lhs env, resolve rhs env with

     | Some (VInt lv), Some (VInt rv) ->

       if guard_zero && rv = 0 then VError :: rhs :: lhs :: tl

       else VInt (op lv rv) :: tl

     | _ -> VError :: rhs :: lhs :: tl)


let run_add env s = int_binop ( + )   false env s

let run_sub env s = int_binop ( - )   false env s

let run_mul env s = int_binop ( * )   false env s

let run_div env s = int_binop ( / )   true  env s

let run_rem env s = int_binop ( mod ) true  env s


let run_neg env = function

  | []           -> VError :: []

  | top :: rest  ->

    (match resolve top env with

     | Some (VInt n) -> VInt (-n) :: rest

     | _             -> VError :: top :: rest)



(* Boolean ops *)


let run_and env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | top :: nxt :: tl ->

    (match resolve top env, resolve nxt env with

     | Some (VBool a), Some (VBool b) -> VBool (a && b) :: tl

     | _ -> VError :: top :: nxt :: tl)


let run_or env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | top :: nxt :: tl ->

    (match resolve top env, resolve nxt env with

     | Some (VBool a), Some (VBool b) -> VBool (a || b) :: tl

     | _ -> VError :: top :: nxt :: tl)


let run_not env = function

  | []          -> VError :: []

  | top :: tl   ->

    (match resolve top env with

     | Some (VBool b) -> VBool (not b) :: tl

     | _              -> VError :: top :: tl)


let run_equal env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | top :: nxt :: tl ->

    (match resolve top env, resolve nxt env with

     | Some (VInt a), Some (VInt b) -> VBool (a = b) :: tl

     | _ -> VError :: top :: nxt :: tl)


let run_lessThan env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | top :: nxt :: tl ->

    (* top = y, nxt = x; result is x < y *)

    (match resolve top env, resolve nxt env with

     | Some (VInt y), Some (VInt x) -> VBool (x < y) :: tl

     | _ -> VError :: top :: nxt :: tl)



(* String ops *)

let run_cat env = function

  | []               -> VError :: []

  | x :: []          -> VError :: x :: []

  | top :: nxt :: tl ->

    (match resolve_or_error top env, resolve_or_error nxt env with

     | VStr s1, VStr s2 -> VStr (s2 ^ s1) :: tl

     | _                -> VError :: top :: nxt :: tl)



(* bind *)
let is_bindable = function

  | VInt _ | VBool _ | VStr _ | VUnit -> true

  | _ -> false

let run_bind env = function

  | v :: name :: tl ->

      (match name with

       | VName n ->

           (match resolve v env with

            | Some actual ->

                if is_bindable actual then

                  

                  (VUnit :: tl, bind_in_env n actual env)

                else

                  (VError :: v :: name :: tl, env)

            | None ->

             

                (VError :: v :: name :: tl, env))

       | _ -> 

           

           (VError :: v :: name :: tl, env))

  | stack -> 

      

      (VError :: stack, env)


(* if *)
let run_if env = function

  | []                    -> VError :: []

  | x :: []               -> VError :: x :: []

  | x :: y :: []          -> VError :: x :: y :: []

  | x :: y :: z :: tl     ->

    (match resolve z env with

     | Some (VBool true)  -> x :: tl

     | Some (VBool false) -> y :: tl

     | _                  -> VError :: x :: y :: z :: tl)



(* ── toString / println *)
let run_toString _env = function

  | []          -> VError :: []

  | top :: rest ->

    (* Spec §5.13: names convert to their name string "contents unchanged".

       We show the raw value as-is without resolving bound names. *)

    VStr (show top) :: rest


let run_println write env stack =

  match stack with

  | []           -> (VError :: [], env)

  | top :: rest  ->

    (match resolve top env with

     | Some (VStr s) -> write s; (rest, env)

     (* Non-string: consume the value and push :error: *)

     | _             -> (VError :: rest, env))



(* ── IO helpers  *)
let load_lines chan =

  let rec go acc =

    match (try Some (input_line chan) with End_of_file -> None) with

    | None   -> List.rev acc

    | Some l -> go (trim_crlf l :: acc)

  in go []


let quoted_push_string raw =

  let line = String.trim raw in

  let pfx  = "push " in

  let plen = String.length pfx in

  let llen = String.length line in

  if llen > plen && String.sub line 0 plen = pfx then

    let after = String.sub line plen (llen - plen) in

    let alen  = String.length after in

    let s = ref 0 in

    while !s < alen && after.[!s] = ' ' do incr s done;

    let rest = String.sub after !s (alen - !s) in

    let rlen = String.length rest in

    if rlen >= 2 && rest.[0] = '"' && rest.[rlen-1] = '"' then

      Some (String.sub rest 1 (rlen - 2))

    else None

  else None

(* Index-based scan helpers *)


(* Return the index of the "end" that closes the "let" whose body starts at [i] *)

let find_matching_end lines i =

  let n = Array.length lines in

  let depth = ref 1 and j = ref i in

  while !depth > 0 && !j < n do

    let tok = String.trim lines.(!j) in

    if tok = "let" then incr depth

    else if tok = "end" then decr depth;

    if !depth > 0 then incr j

  done;

  !j

(* Scans forward to find the matching "funEnd" and extracts the code body *)
let extract_fun_body lines start_idx =
  let n = Array.length lines in
  let j = ref start_idx in
  let body = ref [] in
  while !j < n && String.trim lines.(!j) <> "funEnd" do
    body := lines.(!j) :: !body;
    incr j
  done;
  (* Return the code lines in the correct order, and the index of funEnd *)
  (List.rev !body, !j)

(* ── Main execution loop *)

let rec exec lines i env stack write =

  let n = Array.length lines in

  if i >= n then (stack, env, n)

  else

    let raw     = lines.(i) in

    let trimmed = String.trim raw in

    if trimmed = "quit" then (stack, env, i+1)

    else if trimmed = "end" then (stack, env, i+1)

    (* NEW: Function Declarations *)
    else if String.length trimmed >= 3 && String.sub trimmed 0 3 = "fun" then begin
      (* 1. Split the line to get: ["fun"; "functionName"; "parameterName"] *)
      let parts = String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
      match parts with
      | ["fun"; fun_name; param_name] ->
          (* 2. Scoop up the code body starting from the next line *)
          let (body_lines, funEnd_idx) = extract_fun_body lines (i+1) in
          
          (* 3. Create the closure snapshot *)
          let closure_val = VClosure (env, param_name, body_lines) in
          
          (* 4. Bind the closure to the function name in the CURRENT scope *)
          let updated_env = bind_in_env fun_name closure_val env in
          
          (* 5. Push :unit: to the stack and resume execution AFTER the funEnd *)
          exec lines (funEnd_idx + 1) updated_env (VUnit :: stack) write
          
      | _ -> 
          (* Malformed fun command *)
          exec lines (i+1) env (VError :: stack) write
    end  

    else if trimmed = "let" then begin

      let end_idx   = find_matching_end lines (i+1) in

      let inner_env = push_scope env in

      let (inner_stk, _inner_env, _) = exec lines (i+1) inner_env [] write in

      let result = match inner_stk with 

        | top :: _ -> 

            (match resolve top _inner_env with

             | Some v -> v

             | None -> top)

        | [] -> VError 

      in

      exec lines (end_idx+1) env (result :: stack) write

    end else begin

      let (new_stk, new_env) = dispatch raw env stack write in

      exec lines (i+1) new_env new_stk write

    end


and dispatch raw env stack write =

  match quoted_push_string raw with

  | Some s -> (VStr s :: stack, env)

  | None ->

    let parts = 

      String.split_on_char ' ' (String.trim raw) 

      |> List.filter (fun s -> s <> "") 

    in

    match parts with

    | "push" :: tok :: _ -> (parse_value tok :: stack, env)

    | "push" :: []       -> (stack, env)

    | ["pop"]            -> (run_pop stack, env)

    | ["add"]            -> (run_add env stack, env)

    | ["sub"]            -> (run_sub env stack, env)

    | ["mul"]            -> (run_mul env stack, env)

    | ["div"]            -> (run_div env stack, env)

    | ["rem"]            -> (run_rem env stack, env)

    | ["neg"]            -> (run_neg env stack, env)

    | ["swap"]           -> (run_swap stack, env)

    | ["cat"]            -> (run_cat env stack, env)

    | ["and"]            -> (run_and env stack, env)

    | ["or"]             -> (run_or env stack, env)

    | ["not"]            -> (run_not env stack, env)

    | ["equal"]          -> (run_equal env stack, env)

    | ["lessThan"]       -> (run_lessThan env stack, env)

    | ["bind"]           -> run_bind env stack

    | ["if"]             -> (run_if env stack, env)

    | ["toString"]       -> (run_toString env stack, env)

    | ["println"]        -> run_println write env stack

    | _                  -> (stack, env)



(* ── Entry point *)

let interpreter ((src : string), (dst : string)) : unit =

  let in_chan  = open_in  src in

  let out_chan = open_out dst in

  let write ln = Printf.fprintf out_chan "%s\n" ln in

  let lines = Array.of_list (load_lines in_chan) in

  let (final_stack, _, _) = exec lines 0 empty_env [] write in

  List.iter (fun v -> write (show v)) final_stack;

  close_in  in_chan;

  close_out out_chan

;;
