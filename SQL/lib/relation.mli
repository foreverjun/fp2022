(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Meta

module Tuple : sig
  type t

  type element =
    | Int of int
    | String of string

  val from_string_list : string list -> table -> t
  val to_string_list : t -> string list
  val nth : int -> t -> element
  val nth_as_int : int -> t -> int
  val nth_as_string : int -> t -> string
  val of_list : element list -> t
  val length : t -> int
  val join : t -> t -> t
end

type t

val to_tuple_list : t -> Tuple.t list
val to_csv : t -> Csv.t
val filter : (Tuple.t -> bool) -> t -> t
val map : (Tuple.t -> Tuple.t) -> t -> t
val cross_product : t -> t -> t
val join : (Tuple.t -> Tuple.t -> bool) -> t -> t -> t

module AccessManager : sig
  type storage

  val load_db : database -> catalog -> storage
  val get_active_db : storage -> database
  val unset_active : storage option -> catalog -> unit
  val set_active : database -> storage option -> catalog -> storage
  val get_rel : table -> storage -> t
  val make_db_from : string -> catalog -> catalog
end
