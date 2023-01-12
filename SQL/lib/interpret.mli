(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(** Monadic interpreter of mini SQL *)

type expr_column =
  { index : int
  ; table : Meta.table
  ; column : Meta.column
  }

(** Evaluatable expression *)
type 'a expression =
  | IntCol : expr_column -> int expression
  | StringCol : expr_column -> string expression
  | ConstInt : int -> int expression
  | ConstString : string -> string expression
  | Plus : int expression * int expression -> int expression
  | Minus : int expression * int expression -> int expression
  | Mult : int expression * int expression -> int expression
  | Div : int expression * int expression -> int expression
  | Equal : 'a expression * 'a expression -> bool expression
  | NotEqual : 'a expression * 'a expression -> bool expression
  | Less : 'a expression * 'a expression -> bool expression
  | Greater : 'a expression * 'a expression -> bool expression
  | LessOrEq : 'a expression * 'a expression -> bool expression
  | GreaterOrEq : 'a expression * 'a expression -> bool expression
  | Or : bool expression * bool expression -> bool expression
  | And : bool expression * bool expression -> bool expression

(** Possible types of expressions *)
type expression_type =
  [ `Int of int expression
  | `String of string expression
  | `Bool of bool expression
  ]

type join_constraint =
  | Left of bool expression
  | Right of bool expression
  | Inner of bool expression
  | Cross

(* Header of the relation (and of the operator) is represented as a list of column names of
   the kind `tablename.columname`. This approach will not work for the aggregation or
   subqueries but since we don't support either such a representation should be enough.
   Also it's not the most efficient one (because of the linear search on column name, but I
   don't think it's an important issue now)
  *)

(** Operator header*)
type header = Ast.name list

(** Operator tree *)
type operator =
  | Projection of
      { child : node
      ; projection : expression_type list
      }
  | Join of
      { left : node
      ; right : node
      ; join_constraint : join_constraint
      }
  | Datasource of { table : Meta.table }
  | Filter of
      { child : node
      ; filter : bool expression
      }
  | OrderBy of
      { child : node
      ; order_expr : Ast.orderby_clause list
      }

(** Node of the operator tree *)
and node =
  { op : operator
  ; header : header
  }

module type Environment = sig
  val catalog_path : string
  val catalog : Meta.catalog

  (* Actually active database should not be here, but since we don't support
     switching databases at runtime let's just keep it here for simplicity *)
  val db : Meta.database
  val storage : Relation.AccessManager.storage
end

val interpret
  :  string
  -> (module Environment)
  -> (header * Relation.t, Utils.error) result

val explain : string -> (module Environment) -> (node, Utils.error) result
