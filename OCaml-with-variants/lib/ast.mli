(** Copyright 2021-2022, Kakadu and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type ident = string

type literal =
  | Int of int
  | Float of float
  | String of string

type arg =
  | Id of ident
  | Lit of literal

type binop =
  | Add
  | Sub
  | Mul
  | Div

type exps =
  | Exp_fun of string * ident * exps (* name + arg + body *)
  | Exp_letbinding of ident * exps (* name + value *)
  | Exp_ident of ident
  | Exp_literal of literal
  | Exp_seq of exps * exps
  | Exp_apply of ident * exps list
  | Exp_unit

(* Application [f g ] *)
(** In type definition above the 3rd constructor is intentionally without documentation
to test linter *)
