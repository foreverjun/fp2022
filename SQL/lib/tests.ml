(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Meta
open Relation

(* Tests of basic catalog/relation functionality *)
let pwd = Filename.current_dir_name
let db_name = "testdb"
let t_name = "t1"
let c = Catalog.recreate pwd
let db, c = Catalog.create_db db_name c
let t1, db, c = Catalog.create_table t_name db c
let t1, db, c = Catalog.create_cols [ "A", IntCol; "B", StringCol ] t1 c

let t1_rel = {|1,abcd
2,cde
3,string
202,pepe
-203,frog
42,c
0,1|}
(* Absence of \n at the end is important for the test below *)

let () = Catalog.dump c
let () = Core.Out_channel.write_all (Catalog.get_table_path t1 c) ~data:t1_rel

let%test _ = c = Catalog.load pwd
let%test _ = [ t1 ] = Database.get_tables db

let db =
  let opt_db = Catalog.get_db db_name c in
  match opt_db with
  | Some db -> db
  | None -> raise Not_found
;;

let t1 =
  let t1_opt = Database.get_table t_name db in
  match t1_opt with
  | Some t1 -> t1
  | None -> raise Not_found
;;

let storage = AccessManager.load_db db c
let tuples = Relation.to_tuple_list (AccessManager.get_rel t1 storage)

let t1_rel_reconstructed =
  String.concat
    "\n"
    (List.map (fun tuple -> String.concat "," (Tuple.to_string_list tuple)) tuples)
;;

let%test _ = t1_rel = t1_rel_reconstructed
