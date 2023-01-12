(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Sql_lib
open Meta
open Relation

(* Tests of basic catalog/relation functionality *)
let pwd = Filename.current_dir_name
let db_name = "testdb"
let t1_name = "t1"
let t2_name = "t2"
let t3_name = "t3"
let c = Catalog.recreate pwd
let db, c = Catalog.create_db db_name c
let t1, db, c = Catalog.create_table t1_name db c
let t1, db, c = Catalog.create_cols [ "A", IntCol; "B", StringCol ] t1 c
let t2, db, c = Catalog.create_table t2_name db c
let t2, db, c = Catalog.create_cols [ "A", IntCol; "B", StringCol ] t2 c
let t3, db, c = Catalog.create_table t3_name db c
let t3, db, c = Catalog.create_cols [ "a", IntCol; "b", StringCol; "c", StringCol ] t3 c

let t1_rel = {|1,a
2,b
3,c
202,d
101,d
4,e
0,f|}

let t2_rel = {|6,a
5,b
4,c
3,d
2,e
1,f
101,101|}

let t3_rel = {|101,a,long
5,b,int
4,c,double
3,d,float
2,e,"notdouble"
12,f,ao
1,101,oa|}

let () = Catalog.dump c
let write_rel t rel = Core.Out_channel.write_all (Catalog.get_table_path t c) ~data:rel

let () =
  write_rel t1 t1_rel;
  write_rel t2 t2_rel;
  write_rel t3 t3_rel;
  let module Env : Interpret.Environment = struct
    let catalog_path = pwd
    let catalog = c
    let storage = AccessManager.load_db db c
    let db = Relation.AccessManager.get_active_db storage
  end
  in
  let query = Stdio.In_channel.(input_all stdin) |> Base.String.rstrip in
  match Interpret.explain query (module Env) with
  | Result.Error error -> Caml.Format.printf "%s\n%!" (Utils.show_error error)
  | Result.Ok tree -> Pprintnode.pp tree
;;
