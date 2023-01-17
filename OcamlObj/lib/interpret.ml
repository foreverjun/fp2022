(** Copyright 2021-2022, Kalashnikov Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Parser
open Format

module ContextMap = struct
  include Map.Make (String)

  let pp pp formatter map =
    Format.fprintf formatter "[";
    iter (fun key value -> Format.fprintf formatter "[\"%s\": %a],\n" key pp value) map;
    Format.fprintf formatter "]"
  ;;
end

module type Fail_monad = sig
  include Base.Monad.S2

  val fail : 'e -> ('a, 'e) t
  val run : ('a, 'e) t -> ok:('a -> ('b, 'e) t) -> err:('e -> ('b, 'e) t) -> ('b, 'e) t
  val ( let* ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
end

type value =
  | IntV of int
  | StringV of string
  | BoolV of bool
  | FunV of name * expr * ctx Lazy.t
  | ObjV of ctx
  | MethV of value
      (** wrapper, which is needed so that you can only call methods from the outside *)
[@@deriving show { with_path = false }]

and ctx = value ContextMap.t [@@deriving show { with_path = false }]

type error =
  | Wrong_type_binop of value * value
  | Wrong_type of expr
  | Match_non_exhaustive
  | Not_bound of name
  | Case_wrong_type of pattern * value
  | Div_0
[@@deriving show { with_path = false }]

let rec clear_value = function
  | MethV inner -> clear_value inner
  | other -> other
;;

let pp_value (k, v) =
  let open Format in
  let printer _ v =
    match clear_value v with
    | IntV n -> printf "%d" n
    | StringV s -> printf "%S" s
    | BoolV b -> printf "%b" b
    | FunV (_, _, _) -> printf "<fun>"
    | ObjV _ -> printf "<object>"
    | MethV _ -> printf "MethV printing error"
  in
  printf "val %s = %a\n%!" k printer v
;;

module Interpret (M : Fail_monad) = struct
  open M

  let find_in_ctx name ctx =
    match ContextMap.find name ctx with
    | (exception Not_found) | MethV _ -> fail @@ Not_bound name
    | value -> return value
  ;;

  let find_meth_in_ctx name ctx =
    match ContextMap.find name ctx with
    | exception Not_found -> fail @@ Not_bound name
    | MethV value -> return (clear_value value)
    | _ -> fail @@ Not_bound name
  ;;

  let match_pat (p, value) =
    match p, value with
    | PVar name, v -> Some (return [ name, v ])
    | PConst (CInt c), IntV v when c = v -> Some (return [])
    | PConst (CString c), StringV v when c = v -> Some (return [])
    | PConst (CBool c), BoolV v when c = v -> Some (return [])
    | PConst (CInt _), IntV _ -> None
    | PConst (CString _), StringV _ -> None
    | PConst (CBool _), BoolV _ -> None
    | p, v -> Some (fail (Case_wrong_type (p, v)))
  ;;

  let empty_ctx = ContextMap.empty
  let add_to_ctx name v ctx = ContextMap.add name v ctx

  let cmp op = function
    | IntV x, IntV y -> return (BoolV (op (Int.compare x y) 0))
    | StringV x, StringV y -> return (BoolV (op (String.compare x y) 0))
    | BoolV x, BoolV y -> return (BoolV (op (Bool.compare x y) 0))
    | b, c -> fail (Wrong_type_binop (b, c))
  ;;

  let apply_binop op x y =
    match op, x, y with
    | Add, IntV x, IntV y -> return (IntV (x + y))
    | Sub, IntV x, IntV y -> return (IntV (x - y))
    | Mul, IntV x, IntV y -> return (IntV (x * y))
    | Div, IntV x, IntV y -> if y = 0 then fail Div_0 else return (IntV (x / y))
    | Less, x, y -> cmp ( < ) (x, y)
    | Leq, x, y -> cmp ( <= ) (x, y)
    | Gre, x, y -> cmp ( > ) (x, y)
    | Geq, x, y -> cmp ( >= ) (x, y)
    | Eq, x, y -> cmp ( == ) (x, y)
    | Neq, x, y -> cmp ( != ) (x, y)
    | And, BoolV x, BoolV y -> return (BoolV (x && y))
    | Or, BoolV x, BoolV y -> return (BoolV (x || y))
    | _, b, c -> fail (Wrong_type_binop (b, c))
  ;;

  let rec eval ctx = function
    | EConst (CInt x) -> return (IntV x)
    | EConst (CBool x) -> return (BoolV x)
    | EConst (CString x) -> return (StringV x)
    | EVar x -> find_in_ctx x ctx >>= return
    | EBinop (op, l, r) ->
      let* l_expr = eval ctx l in
      let* r_expr = eval ctx r in
      let l_expr, r_expr = clear_value l_expr, clear_value r_expr in
      apply_binop op l_expr r_expr >>= return
    | EIf (expr1, expr2, expr3) ->
      eval ctx expr1
      >>= (function
      | BoolV true -> eval ctx expr2
      | BoolV false -> eval ctx expr3
      | _ -> fail (Wrong_type expr1))
    | EFun (name, expr) -> return (FunV (name, expr, lazy ctx))
    | EApp (l_expr, r_expr) ->
      eval ctx l_expr
      >>= (function
      | FunV (name, body, fun_ctx) ->
        let* r_val = eval ctx r_expr in
        let new_ctx = add_to_ctx name r_val (Lazy.force fun_ctx) in
        eval new_ctx body
      | _ -> fail (Wrong_type l_expr))
    | EMatch (expr, cases) ->
      eval ctx expr
      >>= fun value ->
      (match
         List.find_map
           (fun (p, body) -> Option.map (fun e -> e, body) (match_pat (p, value)))
           cases
       with
       | Some (case, body) ->
         case
         >>= fun case ->
         eval (List.fold_left (fun ctx (name, v) -> add_to_ctx name v ctx) ctx case) body
       | None -> fail Match_non_exhaustive)
    | EObj (self_name, obj) ->
      List.fold_left
        (fun ctx obj_expr ->
          let* ctx = ctx in
          match obj_expr with
          | OMeth (name, expr) ->
            let ctx_with_self =
              if self_name = "" then ctx else add_to_ctx self_name (ObjV ctx) ctx
            in
            let* value = eval ctx_with_self expr in
            return (add_to_ctx name (MethV value) ctx_with_self)
          | OVal (name, expr) ->
            let* value = eval ctx expr in
            return (add_to_ctx name value ctx))
        (return ctx)
        obj
      >>= fun obj_value -> return (ObjV obj_value)
    | ECallM (expr, name) ->
      eval ctx expr
      >>= (function
      | ObjV ctx -> find_meth_in_ctx name ctx
      | other -> return other)
    | ELet (bindings, expr1) ->
      let* _, st = eval_binding ctx bindings in
      return st >>= fun s -> eval s expr1

  and eval_binding ctx (is_rec, name, expr) =
    if is_rec
    then
      let* buffer_fun =
        match expr with
        | EFun (pat, body) ->
          let rec new_env = lazy (add_to_ctx name (FunV (pat, body, new_env)) ctx) in
          return @@ FunV (pat, body, new_env)
        | other -> eval ctx other
      in
      let new_ctx = add_to_ctx name buffer_fun ctx in
      let* value = eval new_ctx expr in
      return ((name, value), add_to_ctx name value new_ctx)
    else
      let* value = eval ctx expr in
      let new_ctx = add_to_ctx name value ctx in
      return ((name, value), new_ctx)
  ;;

  let eval_prog prog =
    List.fold_left
      (fun acc decl ->
        let decl =
          match decl with
          | DLet decl -> decl
        in
        let* binds, ctx = acc in
        let* new_binds, new_ctx = eval_binding ctx decl in
        return (new_binds :: binds, new_ctx))
      (return ([], empty_ctx))
      prog
    >>| fun (res, _) -> List.rev res
  ;;
end

module InterpretResult = struct
  include Base.Result

  let ( let* ) x f = x >>= f

  let run x ~ok ~err =
    match x with
    | Ok v -> ok v
    | Error e -> err e
  ;;
end

let eval_pp _ code =
  let open Interpret (InterpretResult) in
  match parse code with
  | Ok prog ->
    InterpretResult.run
      (eval_prog prog)
      ~err:(fun x -> printf "%a\n" pp_error x)
      ~ok:(fun binds -> List.iter pp_value binds)
  | _ -> Printf.printf "Parse error"
;;
