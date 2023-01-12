(** Copyright 2021-2022, Kakadu and contributors *)

(** SPDX-License-Identifier: CC0-1.0 *)

open Sql_lib

let () =
  let s = Stdio.In_channel.input_all Caml.stdin in
  match Parser.parse s with
  | Result.Ok ast -> Format.printf "%s\n%!" (Ast.show_ast ast)
  | Result.Error e -> Format.printf "An error occured during parsing\n%s\n\t%s\n" s e
;;
