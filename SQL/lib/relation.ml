(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Meta

module Tuple = struct
  type element =
    | Int of int
    | String of string

  type t = element array

  let of_list = Array.of_list

  let from_string_list string_tuple table =
    Array.of_list
      (List.map2
         (fun string_value -> function
           | IntCol -> Int (int_of_string string_value)
           | StringCol -> String string_value)
         string_tuple
         (Catalog.get_table_types table))
  ;;

  let to_string_array tuple =
    Array.map
      (function
       | Int i -> string_of_int i
       | String s -> s)
      tuple
  ;;

  let to_string_list tuple = Array.to_list (to_string_array tuple)
  let nth index tuple = Array.get tuple index

  let nth_as_int index tuple =
    match nth index tuple with
    | Int i -> i
    | String _ -> raise (Invalid_argument "Element is not an interger")
  ;;

  let nth_as_string index tuple =
    match nth index tuple with
    | Int _ -> raise (Invalid_argument "Element is not a string")
    | String s -> s
  ;;

  let length tuple = Array.length tuple
  let join ltuple rtuple = Array.append ltuple rtuple
end

type t = Tuple.t list

let filter f rel = List.filter f rel
let map f rel = List.map f rel

let join f left right =
  List.fold_left
    (fun joined left_tuple ->
      let joined_with_left = List.find_all (f left_tuple) right in
      let res = List.map (Tuple.join left_tuple) joined_with_left in
      (* super ineffective, it will die on big tables probably *)
      joined @ res)
    []
    left
;;

let cross_product left right = join (fun _ _ -> true) left right
let csv_to_string_rel = List.map Csv.Row.to_list

let from_string_rel str_rel table =
  List.map (fun string_tuple -> Tuple.from_string_list string_tuple table) str_rel
;;

let from_string str table =
  let csv_list = Csv.Rows.input_all (Csv.of_string str) in
  from_string_rel (csv_to_string_rel csv_list) table
;;

let load table c =
  let string_rel =
    List.map
      (fun row -> Csv.Row.to_list row)
      (Csv.Rows.load (Catalog.get_table_path table c))
  in
  from_string_rel string_rel table
;;

let to_tuple_list rel = rel
let to_csv rel = Csv.of_array (Array.map Tuple.to_string_array (Array.of_list rel))
let dump_csv table csv_table c = Csv.save (Catalog.get_table_path table c) csv_table
let dump_r table rel = dump_csv table (to_csv rel)

module AccessManager = struct
  type storage =
    { active_db : database
    ; data : (table * t) list
    }

  let load_db db c =
    { active_db = db
    ; data = List.map (fun table -> table, load table c) (Database.get_tables db)
    }
  ;;

  let get_active_db { active_db } = active_db

  let unset_active cur_storage c =
    match cur_storage with
    | Some { data } ->
      Catalog.dump c;
      List.iter (fun (table, relation) -> dump_r table relation c) data
    | _ -> ()
  ;;

  let set_active db cur_storage c =
    unset_active cur_storage c;
    load_db db c
  ;;

  let get_rel table { data } = snd (List.find (fun (t, _) -> t = table) data)

  let create_table coltypes colnames name db c =
    let types = List.map Meta.column_type_of_string coltypes in
    let table, _db, c = Catalog.create_table name db c in
    Catalog.create_cols (List.combine colnames types) table c
  ;;

  let update_db hdr_file rel_file db c =
    let hdr_rows = List.map Csv.Row.to_list (Csv.Rows.load hdr_file) in
    let types, names =
      match hdr_rows with
      | [ types; names ] when List.length types = List.length names -> types, names
      | _ -> raise (Utils.GeneralError (hdr_file ^ " has wrong format"))
    in
    let rel_csv = Csv.load rel_file in
    if Csv.columns rel_csv != List.length types
    then
      raise
        (Failure
           (Format.sprintf "%s and %s have different number of columns" hdr_file rel_file));
    let t, db, c =
      create_table
        types
        names
        (Filename.basename (Filename.remove_extension rel_file))
        db
        c
    in
    if not (Csv.is_square rel_csv)
    then raise (Utils.GeneralError (rel_file ^ " has empty cells"))
    else dump_csv t rel_csv c;
    db, c
  ;;

  let make_db_from path c =
    if not (Sys.is_directory path)
    then raise (Utils.GeneralError ("No directory " ^ path));
    let db, c = Catalog.create_db (Filename.basename path) c in
    Catalog.dump c;
    let load_if_csv name (db, c) =
      if Filename.extension name = ".csv"
      then (
        let hdr_file = Filename.remove_extension name ^ ".hdr" in
        if not (Sys.file_exists hdr_file)
        then (
          Format.eprintf
            "Encountered .csv file %s without corresponding .hdr file, skipping it\n"
            name;
          db, c)
        else update_db hdr_file name db c)
      else db, c
    in
    let _db, new_c =
      Sys.readdir path
      |> Array.fold_left
           (fun db_and_c name -> load_if_csv (Filename.concat path name) db_and_c)
           (db, c)
    in
    Catalog.dump_meta new_c;
    new_c
  ;;

  (* Code managing changes in existing tables should be placed here *)
end
