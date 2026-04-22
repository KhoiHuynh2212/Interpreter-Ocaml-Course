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
  if tok = ":true:"  then VBool true
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
  | []           -> VError :: []
  | x :: []      -> VError :: x :: []
  | x :: y :: tl -> y :: x :: tl

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
  | []          -> VError :: []
  | top :: rest ->
    (match resolve top env with
     | Some (VInt n) -> VInt (-n) :: rest
     | _             -> VError :: top :: rest)

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
  | []        -> VError :: []
  | top :: tl ->
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
    (match resolve top env, resolve nxt env with
     | Some (VInt y), Some (VInt x) -> VBool (x < y) :: tl
     | _ -> VError :: top :: nxt :: tl)

let run_cat env = function
  | []               -> VError :: []
  | x :: []          -> VError :: x :: []
  | top :: nxt :: tl ->
    (match resolve_or_error top env, resolve_or_error nxt env with
     | VStr s1, VStr s2 -> VStr (s2 ^ s1) :: tl
     | _                -> VError :: top :: nxt :: tl)

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
  | []                -> VError :: []
  | x :: []           -> VError :: x :: []
  | x :: y :: []      -> VError :: x :: y :: []
  | x :: y :: z :: tl ->
    (match resolve z env with
     | Some (VBool true)  -> x :: tl
     | Some (VBool false) -> y :: tl
     | _                  -> VError :: x :: y :: z :: tl)

let run_toString _env = function
  | []          -> VError :: []
  | top :: rest -> VStr (show top) :: rest

let run_println write env stack =
  match stack with
  | []          -> (VError :: [], env)
  | top :: rest ->
    (match resolve top env with
     | Some (VStr s) -> write s; (rest, env)
     | _             -> (VError :: rest, env))

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
    let tok   = String.trim lines.(!j) in
    let parts = String.split_on_char ' ' tok |> List.filter (fun s -> s <> "") in
    (match parts with
     | ("fun" | "inOutFun") :: _ -> incr depth
     | ["funEnd"]               -> decr depth
     | _                        -> ());
    if !depth > 0 then (body := lines.(!j) :: !body; incr j)
  done;
  (List.rev !body, !j)

(* ── Explicit frame stack ───────────────────────────────────────────────
   Each function call pushes a frame onto a heap list rather than the OCaml
   call stack, so arbitrarily deep recursion never overflows.              *)

type frame_kind =
  | LetKind                           (* let…end scope block        *)
  | FunKind of bool * string * value  (* is_inout, param, orig_arg  *)

type frame = {
  fr_lines : string array;
  fr_idx   : int;
  fr_stack : value list;
  fr_env   : env;
  fr_kind  : frame_kind;
}

let run init_lines init_env write =
  let cur_lines = ref init_lines in
  let cur_idx   = ref 0 in
  let cur_env   = ref init_env in
  let cur_stack = ref [] in
  let frames    = ref [] in
  let running   = ref true in

  (* Build the caller env after a function exits (handles inout writeback).
     !cur_env must still be the function's final env when this is called.  *)
  let restored_env is_inout param actual saved_env =
    if is_inout then
      match actual with
      | VName aname ->
          (match lookup param !cur_env with
           | Some v -> bind_in_env aname v saved_env
           | None   -> saved_env)
      | _ -> saved_env
    else saved_env
  in

  (* Unwind to the nearest FunKind frame, skipping any LetKind frames.
     has_val: whether to push the top of cur_stack as a return value.    *)
  let do_return has_val =
    let ret_val =
      if has_val then
        (match !cur_stack with top :: _ -> resolve_or_error top !cur_env | [] -> VError)
      else VError
    in
    let found = ref false in
    while not !found do
      match !frames with
      | [] ->
          running := false;
          found   := true
      | fr :: rest ->
          frames := rest;
          (match fr.fr_kind with
           | LetKind -> ()     (* return escapes let blocks — keep searching *)
           | FunKind (is_inout, param, actual) ->
               cur_lines := fr.fr_lines;
               cur_idx   := fr.fr_idx;
               cur_env   := restored_env is_inout param actual fr.fr_env;
               cur_stack := (if has_val then ret_val :: fr.fr_stack
                             else fr.fr_stack);
               found := true)
    done
  in

  while !running do
    let n = Array.length !cur_lines in

    if !cur_idx >= n then begin
      (* Fell off the end of the current instruction stream *)
      match !frames with
      | [] -> running := false
      | _  -> do_return false   (* function body ended without return *)
    end else begin
      let raw     = !cur_lines.(!cur_idx) in
      let trimmed = String.trim raw in

      (* ── quit ─────────────────────────────────────────────────────── *)
      if trimmed = "quit" then
        running := false

      (* ── end: closes a let block ──────────────────────────────────── *)
      else if trimmed = "end" then begin
        match !frames with
        | fr :: rest
          when (match fr.fr_kind with LetKind -> true | _ -> false) ->
            frames := rest;
            let result =
              match !cur_stack with
              | top :: _ -> (match resolve top !cur_env with Some v -> v | None -> top)
              | []       -> VError
            in
            cur_lines := fr.fr_lines;
            cur_idx   := fr.fr_idx;
            cur_env   := fr.fr_env;
            cur_stack := result :: fr.fr_stack
        | _ ->
            cur_idx := !cur_idx + 1
      end

      (* ── return ───────────────────────────────────────────────────── *)
      else if trimmed = "return" then
        do_return true

      (* ── fun / inOutFun declaration ───────────────────────────────── *)
      else if
        (let p = String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
         match p with ("fun"|"inOutFun") :: _ :: _ :: [] -> true | _ -> false)
      then begin
        let parts = String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
        (match parts with
         | [kw; fun_name; param_name] ->
             let (body_lines, funEnd_idx) = extract_fun_body !cur_lines (!cur_idx+1) in
             let mk e = if kw = "inOutFun"
                        then VInOutClosure (e, param_name, body_lines)
                        else VClosure      (e, param_name, body_lines) in
             let temp = mk !cur_env in
             let e1   = bind_in_env fun_name temp !cur_env in
             let clo  = mk e1 in
             let e2   = bind_in_env fun_name clo e1 in
             cur_env   := e2;
             cur_stack := VUnit :: !cur_stack;
             cur_idx   := funEnd_idx + 1
         | _ ->
             cur_stack := VError :: !cur_stack;
             cur_idx   := !cur_idx + 1)
      end

      (* ── let: open a new scope ────────────────────────────────────── *)
      else if trimmed = "let" then begin
        let end_idx = find_matching_end !cur_lines (!cur_idx+1) in
        frames := {
          fr_lines = !cur_lines; fr_idx = end_idx + 1;
          fr_stack = !cur_stack; fr_env  = !cur_env;
          fr_kind  = LetKind;
        } :: !frames;
        cur_env   := push_scope !cur_env;
        cur_stack := [];
        cur_idx   := !cur_idx + 1
      end

      (* ── call: push a heap frame instead of recursing ─────────────── *)
      else if trimmed = "call" then begin
        match !cur_stack with
        | arg :: fun_val :: rest_stk ->
            (match resolve fun_val !cur_env with
             | Some (VClosure (clo_env, param, body))
             | Some (VInOutClosure (clo_env, param, body)) as maybe ->
                 let is_inout =
                   match maybe with Some (VInOutClosure _) -> true | _ -> false in
                 (match resolve arg !cur_env with
                  | None | Some VError ->
                      cur_stack := VError :: arg :: fun_val :: rest_stk;
                      cur_idx   := !cur_idx + 1
                  | Some resolved_arg ->
                      (* Save caller state, then switch to the function body *)
                      frames := {
                        fr_lines = !cur_lines; fr_idx = !cur_idx + 1;
                        fr_stack = rest_stk;   fr_env  = !cur_env;
                        fr_kind  = FunKind (is_inout, param, arg);
                      } :: !frames;
                      let base = push_scope clo_env in
                      (* Bind the function's own name for self-recursion *)
                      let base = match fun_val with
                        | VName fname ->
                            (match resolve fun_val !cur_env with
                             | Some clo -> bind_in_env fname clo base
                             | None     -> base)
                        | _ -> base
                      in
                      cur_lines := Array.of_list body;
                      cur_idx   := 0;
                      cur_env   := bind_in_env param resolved_arg base;
                      cur_stack := [])
             | _ ->
                 cur_stack := VError :: arg :: fun_val :: rest_stk;
                 cur_idx   := !cur_idx + 1)
        | _ ->
            cur_stack := VError :: !cur_stack;
            cur_idx   := !cur_idx + 1
      end

      (* ── all other instructions ───────────────────────────────────── *)
      else begin
        let (new_stk, new_env) =
          match quoted_push_string raw with
          | Some s -> (VStr s :: !cur_stack, !cur_env)
          | None ->
              let parts =
                String.split_on_char ' ' trimmed |> List.filter (fun s -> s <> "") in
              match parts with
              | "push" :: tok :: _ -> (parse_value tok :: !cur_stack, !cur_env)
              | "push" :: []       -> (!cur_stack, !cur_env)
              | ["pop"]      -> (run_pop !cur_stack,              !cur_env)
              | ["add"]      -> (run_add      !cur_env !cur_stack, !cur_env)
              | ["sub"]      -> (run_sub      !cur_env !cur_stack, !cur_env)
              | ["mul"]      -> (run_mul      !cur_env !cur_stack, !cur_env)
              | ["div"]      -> (run_div      !cur_env !cur_stack, !cur_env)
              | ["rem"]      -> (run_rem      !cur_env !cur_stack, !cur_env)
              | ["neg"]      -> (run_neg      !cur_env !cur_stack, !cur_env)
              | ["swap"]     -> (run_swap !cur_stack,              !cur_env)
              | ["cat"]      -> (run_cat      !cur_env !cur_stack, !cur_env)
              | ["and"]      -> (run_and      !cur_env !cur_stack, !cur_env)
              | ["or"]       -> (run_or       !cur_env !cur_stack, !cur_env)
              | ["not"]      -> (run_not      !cur_env !cur_stack, !cur_env)
              | ["equal"]    -> (run_equal    !cur_env !cur_stack, !cur_env)
              | ["lessThan"] -> (run_lessThan !cur_env !cur_stack, !cur_env)
              | ["bind"]     -> run_bind      !cur_env !cur_stack
              | ["if"]       -> (run_if       !cur_env !cur_stack, !cur_env)
              | ["toString"] -> (run_toString !cur_env !cur_stack, !cur_env)
              | ["println"]  -> run_println write !cur_env !cur_stack
              | _            -> (!cur_stack, !cur_env)
        in
        cur_stack := new_stk;
        cur_env   := new_env;
        cur_idx   := !cur_idx + 1
      end
    end
  done;
  !cur_stack

(* ── Entry point ──────────────────────────────────────────────────────── *)
let interpreter ((src : string), (dst : string)) : unit =
  let in_chan  = open_in  src in
  let out_chan = open_out dst in
  let write ln = Printf.fprintf out_chan "%s\n" ln in
  let lines = Array.of_list (load_lines in_chan) in
  let final_stack = run lines empty_env write in
  List.iter (fun v -> write (show v)) final_stack;
  close_in  in_chan;
  close_out out_chan
;;