(*Reserve keyword*)
let keyword_list = [
  "push"; "pop"; "add"; "sub"; "mul"; "div"; "rem"; "neg"; "swap";
  "cat"; "and"; "or"; "not"; "equal"; "lessThan"; "bind"; "if";
  "let"; "end"; "quit"; "toString"; "println"; 
  "fun"; "funEnd"; "call"; "return"; "inOutFun"
]
let reserved_keywords = Hashtbl.create (List.length keyword_list) 
let () = List.iter (fun kw -> Hashtbl.add reserved_keywords kw ()) keyword_list
let _is_keyword w = Hashtbl.mem reserved_keywords w
type value =
  | VInt    of int
  | VBool   of bool
  | VStr    of string
  | VName   of string
  | VUnit
  | VError
  | VClosure      of env * string * string list
  | VInOutClosure of env * string * string list
and env = (string * value) list list
let show = function
  | VInt  n -> string_of_int n
  | VBool b -> if b then ":true:" else ":false:"
  | VStr  s -> s
  | VName n -> n
  | VUnit   -> ":unit:"
  | VError  -> ":error:"
  | VClosure _ | VInOutClosure _ -> ":fun:"
exception Return of value list * env
let trim_crlf s =
  let n = String.length s in
  if n > 0 && s.[n-1] = '\r' then String.sub s 0 (n-1) else s
let is_int_string tok =
  try ignore (int_of_string tok); true with Failure _ -> false
let is_name_string w =
  let n = String.length w in
  n > 0
  && (w.[0] = '_' || (w.[0] >= 'a' && w.[0] <= 'z') || (w.[0] >= 'A' && w.[0] <= 'Z'))
  && String.for_all (fun c ->
       c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
       || (c >= '0' && c <= '9')) w
let parse_value tok =
  if tok = ":true:" then VBool true
  else if tok = ":false:" then VBool false
  else if tok = ":error:" then VError
  else if tok = ":unit:"  then VUnit
  else if is_int_string tok then VInt (int_of_string tok)
  else if is_name_string tok then VName tok
  else VError
let empty_env : env = [[]]
let rec lookup name = function
  | [] -> None
  | scope :: rest ->
    (match List.assoc_opt name scope with
     | Some v -> Some v | None -> lookup name rest)
let bind_in_env name v = function
  | [] -> [[(name, v)]]
  | scope :: rest -> ((name, v) :: List.remove_assoc name scope) :: rest
let push_scope env = [] :: env
let resolve v env = match v with VName n -> lookup n env | other -> Some other
let resolve_or_error v env = match resolve v env with Some r -> r | None -> VError
type stack = value list
let run_pop = function [] -> VError :: [] | _ :: rest -> rest
let run_swap = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | x :: y :: tl -> y :: x :: tl
let int_binop op guard_zero env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
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
  | [] -> VError :: []
  | top :: rest ->
    (match resolve top env with
     | Some (VInt n) -> VInt (-n) :: rest
     | _ -> VError :: top :: rest)
let run_and env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve top env, resolve nxt env with
     | Some (VBool a), Some (VBool b) -> VBool (a && b) :: tl
     | _ -> VError :: top :: nxt :: tl)
let run_or env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve top env, resolve nxt env with
     | Some (VBool a), Some (VBool b) -> VBool (a || b) :: tl
     | _ -> VError :: top :: nxt :: tl)
let run_not env = function
  | [] -> VError :: []
  | top :: tl ->
    (match resolve top env with
     | Some (VBool b) -> VBool (not b) :: tl
     | _ -> VError :: top :: tl)
let run_equal env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve top env, resolve nxt env with
     | Some (VInt a), Some (VInt b) -> VBool (a = b) :: tl
     | _ -> VError :: top :: nxt :: tl)
let run_lessThan env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve top env, resolve nxt env with
     | Some (VInt y), Some (VInt x) -> VBool (x < y) :: tl
     | _ -> VError :: top :: nxt :: tl)
let run_cat env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve_or_error top env, resolve_or_error nxt env with
     | VStr s1, VStr s2 -> VStr (s2 ^ s1) :: tl
     | _ -> VError :: top :: nxt :: tl)
let is_bindable = function
  | VInt _ | VBool _ | VStr _ | VUnit | VClosure _ | VInOutClosure _ -> true
  | _ -> false
let run_bind env = function
  | v :: name :: tl ->
      (match name with
       | VName n ->
           (match resolve v env with
            | Some actual ->
                if is_bindable actual then (VUnit :: tl, bind_in_env n actual env)
                else (VError :: v :: name :: tl, env)
            | None -> (VError :: v :: name :: tl, env))
       | _ -> (VError :: v :: name :: tl, env))
  | stack -> (VError :: stack, env)
let run_if env = function
  | [] -> VError :: []
  | x :: [] -> VError :: x :: []
  | x :: y :: [] -> VError :: x :: y :: []
  | x :: y :: z :: tl ->
    (match resolve z env with
     | Some (VBool true)  -> x :: tl
     | Some (VBool false) -> y :: tl
     | _ -> VError :: x :: y :: z :: tl)
let run_toString _env = function
  | [] -> VError :: []
  | top :: rest -> VStr (show top) :: rest
let run_println write env stack =
  match stack with
  | [] -> (VError :: [], env)
  | top :: rest ->
    (match resolve top env with
     | Some (VStr s) -> write s; (rest, env)
     | _ -> (VError :: rest, env))
let load_lines chan =
  let rec go acc =
    match (try Some (input_line chan) with End_of_file -> None) with
    | None -> List.rev acc
    | Some l -> go (trim_crlf l :: acc)
  in go []
let quoted_push_string raw =
  let line = String.trim raw in
  let pfx = "push " in
  let plen = String.length pfx in
  let llen = String.length line in
  if llen > plen && String.sub line 0 plen = pfx then
    let after = String.sub line plen (llen - plen) in
    let alen = String.length after in
    let s = ref 0 in
    while !s < alen && after.[!s] = ' ' do incr s done;
    let rest = String.sub after !s (alen - !s) in
    let rlen = String.length rest in
    if rlen >= 2 && rest.[0] = '"' && rest.[rlen-1] = '"' then
      Some (String.sub rest 1 (rlen - 2))
    else None
  else None
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
let extract_fun_body lines start_idx =
  let depth = ref 1 and j = ref start_idx and body = ref [] in
  while !depth > 0 && !j < Array.length lines do
    let tok = String.trim lines.(!j) in
    let parts = String.split_on_char ' ' tok |> List.filter (fun s -> s <> "") in
    (match parts with
     | ("fun" | "inOutFun") :: _ -> incr depth
     | ["funEnd"] -> decr depth
     | _ -> ());
    if !depth > 0 then (body := lines.(!j) :: !body; incr j)
  done;
  (List.rev !body, !j)
let rec exec lines i env stack write =
  let n = Array.length lines in
  if i >= n then (stack, env, n)
  else
    let raw = lines.(i) in
    let trimmed = String.trim raw in
    if trimmed = "quit" then (stack, env, i+1)
    else if trimmed = "end" then (stack, env, i+1)
    else if trimmed = "return" then raise (Return (stack, env))
    else if (let p = String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
             match p with ("fun"|"inOutFun") :: _ :: _ :: [] -> true | _ -> false)
    then begin
      let parts = String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
      match parts with
      | [kw; fun_name; param_name] ->
          let (body_lines, funEnd_idx) = extract_fun_body lines (i+1) in
          let mk kw e = if kw = "inOutFun" then VInOutClosure (e, param_name, body_lines)
                        else VClosure (e, param_name, body_lines) in
          let temp_closure  = mk kw env in
          let env_with_self = bind_in_env fun_name temp_closure env in
          let closure_val   = mk kw env_with_self in
          let updated_env   = bind_in_env fun_name closure_val env_with_self in
          exec lines (funEnd_idx + 1) updated_env (VUnit :: stack) write
      | _ -> exec lines (i+1) env (VError :: stack) write
    end
    else if trimmed = "let" then begin
      let end_idx   = find_matching_end lines (i+1) in
      let inner_env = push_scope env in
      let (inner_stk, _inner_env, _) = exec lines (i+1) inner_env [] write in
      let result = match inner_stk with
        | top :: _ -> (match resolve top _inner_env with Some v -> v | None -> top)
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
    let parts = String.split_on_char ' ' (String.trim raw) |> List.filter (fun s -> s <> "") in
    match parts with
    | "push" :: tok :: _ -> (parse_value tok :: stack, env)
    | "push" :: []       -> (stack, env)
    | ["pop"]      -> (run_pop stack, env)
    | ["add"]      -> (run_add env stack, env)
    | ["sub"]      -> (run_sub env stack, env)
    | ["mul"]      -> (run_mul env stack, env)
    | ["div"]      -> (run_div env stack, env)
    | ["rem"]      -> (run_rem env stack, env)
    | ["neg"]      -> (run_neg env stack, env)
    | ["swap"]     -> (run_swap stack, env)
    | ["cat"]      -> (run_cat env stack, env)
    | ["and"]      -> (run_and env stack, env)
    | ["or"]       -> (run_or env stack, env)
    | ["not"]      -> (run_not env stack, env)
    | ["equal"]    -> (run_equal env stack, env)
    | ["lessThan"] -> (run_lessThan env stack, env)
    | ["bind"]     -> run_bind env stack
    | ["if"]       -> (run_if env stack, env)
    | ["toString"] -> (run_toString env stack, env)
    | ["println"]  -> run_println write env stack
    | ["call"] ->
        (match stack with
         | arg :: fun_val :: rest ->
             (match resolve fun_val env with
              | Some (VClosure (clo_env, param, body))
              | Some (VInOutClosure (clo_env, param, body)) as maybe ->
                  let is_inout = match maybe with Some (VInOutClosure _) -> true | _ -> false in
                  (match resolve arg env with
                   | None | Some VError -> (VError :: arg :: fun_val :: rest, env)
                   | Some resolved_arg ->
                       (* Open a fresh scope on the closure's env, then:
                          1. Bind the function itself by name so the body can call
                             itself recursively (e.g. factorial calling factorial).
                          2. Bind the formal parameter to the resolved argument. *)
                       let base = push_scope clo_env in
                       let base = match fun_val with
                         | VName fname ->
                             (match resolve fun_val env with
                              | Some clo -> bind_in_env fname clo base
                              | None -> base)
                         | _ -> base
                       in
                       let call_env = bind_in_env param resolved_arg base in
                       let body_arr = Array.of_list body in
                       let (fn_stack, final_fn_env) =
                         try let (stk, fe, _) = exec body_arr 0 call_env [] write in (stk, fe)
                         with Return (stk, fe) -> (stk, fe)
                       in
                       let raw_top = match fn_stack with top :: _ -> top | [] -> VError in
                       let ret_val = resolve_or_error raw_top final_fn_env in
                       let caller_env =
                         if is_inout then
                           match arg with
                           | VName actual_name ->
                               (match lookup param final_fn_env with
                                | Some v -> bind_in_env actual_name v env
                                | None   -> env)
                           | _ -> env
                         else env
                       in
                       (ret_val :: rest, caller_env))
              | _ -> (VError :: arg :: fun_val :: rest, env))
         | _ -> (VError :: stack, env))
    | _ -> (stack, env)
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