(** Copyright 2021-2022, Kalashnikov Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open OcamlObj_lib.Interpret

let _ =
  let prog = Stdio.In_channel.input_all Caml.stdin in
  Format.printf "%a=-------------------------------------------=\n" eval_pp prog
;;
