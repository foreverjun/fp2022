(** Copyright 2021-2022, Kalashnikov Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type const =
  | CInt of int
  | CString of string
  | CBool of bool
[@@deriving eq, show { with_path = false }]

type binop =
  | Add (**  +   *)
  | Sub (**  -   *)
  | Mul (**  *   *)
  | Div (**  /   *)
  | Less (**  <   *)
  | Leq (**  <=  *)
  | Gre (**  >   *)
  | Geq (**  >=  *)
  | Eq (** ==  *)
  | Neq (** <>  *)
  | And (** &&  *)
  | Or (** ||  *)
[@@deriving eq, show { with_path = false }]

type name = string [@@deriving eq, show { with_path = false }]

type expr =
  | EConst of const (** int string bool*)
  | EBinop of binop * expr * expr (** 5 + a*)
  | EVar of name (** a *)
  | EIf of expr * expr * expr (** if condition then a else b *)
  | ELet of decl * expr (** let a = 5 in a + 5 *)
  | EFun of name * expr (** fun a b c -> a + b * c *)
  | EApp of expr * expr (** mod 5 3*)
  | EMatch of expr * (pattern * expr) list
      (** match a with | true -> "true" | false -> false*)
  | ECallM of expr * name (** test_obj#another_obj#some_method*)
  | EObj of name * obj (** object (self) method a = 1 method b = 2 end*)
[@@deriving eq, show { with_path = false }]

and objexpr =
  | OMeth of name * expr
  | OVal of name * expr
[@@deriving eq, show { with_path = false }]

and obj = objexpr list [@@deriving eq, show { with_path = false }]

and pattern =
  | PVar of name
  | PConst of const
[@@deriving eq, show { with_path = false }]

and decl = bool * name * expr [@@deriving eq, show { with_path = false }]
and declaration = DLet of decl [@@deriving eq, show { with_path = false }]

type prog = declaration list [@@deriving eq, show { with_path = false }]
