(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(** Functions and types to work with DBMS entities such as catalog,
    databases, tables and columns *)

(** Type of values that the column stores *)
type column_type =
  | IntCol
  | StringCol
[@@deriving yojson]

val column_type_to_string : column_type -> string
val column_type_of_string : string -> column_type

(** Table attribute, constitutes column's name and type *)
type column

val column_type : column -> column_type

(** Header of the table, i.e. list of attributes *)
type header

(** Table in the database represented by a name and a header *)
type table

(** Database represented as a named list of tables *)
type database

(** Catalog represented as list of databases, there is only one catalog *)
type catalog
(** Catalog is stored with this directory structure:
   _catalog/┌──►Catalog.meta.json
            │
            ├──►Database1_name/┌───►Table1
            │                  │
            │                  └───►Table2
            │
            └──►Database2_name/┌───►Table1
                               │
                               ├───►Table2
                               │
                               └───►Table3
  Catalog.meta.json contains all information about this catalog,
  i.e. all databases (identified by their names), their tables, headers of
  the tables
*)

exception AmbiguousEntity

module Table : sig
  val name : table -> string
  val col_fullname : column -> table -> string
  val cols_as_fullnames : table -> string list

  (** [get_table name t] returns column in table [t] with name equal to [name]
      ignoring case
      @raise Not_found if there is no column named [name] in [t]
      @raise AmbigousEntity if there is more than one column named [name] in [t] *)
  val get_col_ci : string -> table -> column

  val get_table_by_name : string -> table list -> table
end

module Database : sig
  val get_name : database -> string

  (** [get_tables db c] returns all tables in database [db] *)
  val get_tables : database -> table list

  (** [get_table name db] returns table with name equal
      to [name] ignoring case
      @raise Not_found if there is no table named [name] in [db]
      @raise AmbigousEntity if there is more than one table named [name] in [db] *)
  val get_table_ci : string -> database -> table

  (** [get_table name db] returns table named [name] as [Some table] or
      [None] if there is no such table in database [db] *)
  val get_table : string -> database -> table option

  val get_col_table : column -> database -> table

  (** [get_col_ci name tables] searches for column named [name] among all tables
      in [tables] ignoring case and returns it
      @raise Not_found if there is not column named [name] among all tables in [tables]
      @raise AmbigousEntity if there is more than one column named [name]
      *)
  val get_col_ci : string -> table list -> table * column

  val get_col_by_fullname_ci : string -> database -> table * column
end

module Catalog : sig
  (** [create path] creates new catalog in [path] directory,
      throws an exception if one already exists *)
  val create : string -> catalog

  (** [load path] loads catalog from the [path] directory and returns it *)
  val load : string -> catalog

  (** [init path] as [load] but if catalog does not exist yet creates
      a new empty one *)
  val init : string -> catalog

  (** [recreate path] creates new catalog in [path] directory as [create],
      but if it already exists drops it and creates a new emtpy one *)
  val recreate : string -> catalog

  (** [dump c] writes catalog [c] (its meta and creates internal structure
      for data) to the disk to catalog's path *)
  val dump : catalog -> unit

  (** [dump_meta c] writes meta of catalog [c] to the disk to catalog's path *)
  val dump_meta : catalog -> unit

  (** [drop c] deletes catalog [c] from the disk *)
  val drop : catalog -> unit

  (** [create_db name c] creates a new empty database named [name] in
      corresponding catalog [c] *)
  val create_db : string -> catalog -> database * catalog

  (** [create_table name db] creates a new empty table named [name] in
      corresponding database [db] *)
  val create_table : string -> database -> catalog -> table * database * catalog

  (** [create_cols cols_list table] creates columns from [cols_list] list
      of <name, type> pairs and inserts them into [table] *)
  val create_cols
    :  (string * column_type) list
    -> table
    -> catalog
    -> table * database * catalog

  (** [to_string c] converts [c] to json string *)
  val to_string : catalog -> string

  (** [get_db name c] returns [Some database] with name [name] or
      [None] if none exists *)
  val get_db : string -> catalog -> database option

  (** [get_table_path table] returns path to the table *)
  val get_table_path : table -> catalog -> string

  (** [get_dbs c] returns all databases in [c] *)
  val get_dbs : catalog -> database list

  (** [get_table_types t] returns a list of table [t] column types *)
  val get_table_types : table -> column_type list
end
