(** Copyright 2021-2022, Kakadu and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type error = string

(** Main entry of parser *)
val parse : string -> (Ast.statement, error) result
