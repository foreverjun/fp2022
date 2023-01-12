(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(* Operator tree pretty printer goes here *)

open Base
open Meta
open Interpret

let pp_node =
  let rec pp fmt { op; header } =
    let pp_expr fmt expr =
      let rec pp_expr : type a. _ -> a expression -> _ =
       fun fmt ->
        let bin cons_s l r =
          Format.fprintf fmt "@[%s (@[%a,@ %a@])@]" cons_s pp_expr l pp_expr r
        in
        function
        | IntCol { index } -> Format.fprintf fmt "IntCol %d" index
        | StringCol { index } -> Format.fprintf fmt "StringCol %s" (string_of_int index)
        | ConstInt i -> Format.fprintf fmt "ConstInt %d" i
        | ConstString s -> Format.fprintf fmt "ConstString %s" s
        | Plus (l, r) -> bin "Plus" l r
        | Minus (l, r) -> bin "Minus" l r
        | Mult (l, r) -> bin "Mult" l r
        | Div (l, r) -> bin "Div" l r
        | Equal (l, r) -> bin "Equal" l r
        | NotEqual (l, r) -> bin "NotEqual" l r
        | Less (l, r) -> bin "Less" l r
        | Greater (l, r) -> bin "Greater" l r
        | LessOrEq (l, r) -> bin "LessOrEq" l r
        | GreaterOrEq (l, r) -> bin "GreaterOrEq" l r
        | Or (l, r) -> bin "Or" l r
        | And (l, r) -> bin "And" l r
      in
      pp_expr fmt expr
    in
    let pp_expr_type fmt = function
      | `Int (expr : int expression) -> pp_expr fmt expr
      | `String (expr : string expression) -> pp_expr fmt expr
      | `Bool (expr : bool expression) -> pp_expr fmt expr
    in
    let pp_proj fmt projection =
      List.iteri
        ~f:(fun i (item, cname) ->
          let format =
            format_of_string
              (if i + 1 = List.length projection then "%s (%a)" else "%s (%a),@ ")
          in
          Format.fprintf fmt format cname pp_expr_type item)
        (Caml.List.combine projection header)
    in
    let pp_join_type fmt = function
      | Left _ -> Format.fprintf fmt "LEFT"
      | Right _ -> Format.fprintf fmt "RIGHT"
      | Inner _ -> Format.fprintf fmt "INNER"
      | Cross -> Format.fprintf fmt "CROSS"
    in
    let pp_join_constraint fmt = function
      | Left pred | Right pred | Inner pred -> Format.fprintf fmt "@,ON %a" pp_expr pred
      | Cross -> ()
    in
    match op with
    | Projection { child; projection } ->
      Format.fprintf fmt "@[<v 4>PROJECT @[%a@] ->@ %a@]@." pp_proj projection pp child
    | Datasource { table } ->
      Format.fprintf fmt "@[<v 4>DATASOURCE (%s)@]" (Table.name table)
    | Filter { child; filter } ->
      Format.fprintf fmt "@[<v 4>FILTER (@[%a@]) ->@ @[%a@]@]" pp_expr filter pp child
    | Join { left; right; join_constraint } ->
      Format.fprintf
        fmt
        "@[<v 4>%a JOIN@,%a@]@,@[<v 4>AND@,%a@]%a"
        pp_join_type
        join_constraint
        pp
        left
        pp
        right
        pp_join_constraint
        join_constraint
    | OrderBy _ -> raise Utils.NotImplemented
  in
  pp
;;

let pp = pp_node Format.std_formatter
