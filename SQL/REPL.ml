(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Base
open Sql_lib

let stat_query e query =
  let time s f =
    let t = Unix.gettimeofday () in
    let _fx = f query e in
    Format.printf "%s execution time: %fs\n%!" s (Unix.gettimeofday () -. t)
  in
  time "Parsing and transformation" Interpret.explain;
  time "Full execution" Interpret.interpret
;;

let run_query out_file print_plan e query =
  match Interpret.explain query e with
  | Result.Error error -> Caml.Format.printf "%s\n%!" (Utils.show_error error)
  | Result.Ok tree ->
    (match Interpret.interpret query e with
     | Result.Error error -> Caml.Format.printf "%s\n%!" (Utils.show_error error)
     | Result.Ok (header, rel) ->
       let output =
         match out_file with
         | Some out_file -> fun rel -> Csv.save out_file (Relation.to_csv rel)
         | None ->
           if print_plan then Pprintnode.pp tree;
           fun rel -> Csv.print_readable (List.concat [ [ header ]; Relation.to_csv rel ])
       in
       output rel)
;;

let run_single runner =
  let query = Stdio.In_channel.(input_all stdin) |> String.rstrip in
  runner query
;;

let run_repl runner =
  let get_char () =
    let termio = Unix.tcgetattr Unix.stdin in
    let () =
      Unix.tcsetattr Unix.stdin Unix.TCSADRAIN { termio with Unix.c_icanon = false }
    in
    let res = input_char stdin in
    Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
    res
  in
  while true do
    let rec helper query semicolon =
      let add_to_query query c = query ^ String.make 1 c in
      match get_char () with
      | ';' -> helper query true
      | c when Caml.( = ) c '\n' ->
        if semicolon
        then query
        else (
          Format.printf "\\ %!";
          helper (add_to_query query c) semicolon)
      | c -> helper (add_to_query query c) semicolon
    in
    Format.printf "> %!";
    runner (helper "" false)
  done
;;

type opts =
  { mutable batch : bool
  ; mutable catalog_path : string
  ; mutable dbname : string option
  ; mutable make_db_from : string option
  ; mutable out_file : string option
  ; mutable print_plan : bool
  ; mutable benchmark : bool
  }

let () =
  let opts =
    { batch = false
    ; catalog_path = Filename.current_dir_name
    ; make_db_from = None
    ; dbname = None
    ; out_file = None
    ; print_plan = false
    ; benchmark = false
    }
  in
  let open Caml.Arg in
  parse
    [ ( "-no-repl"
      , Unit (fun () -> opts.batch <- true)
      , "Read from stdin single program, instead of running full REPL" )
    ; ( "-catalog-path"
      , String (fun path -> opts.catalog_path <- path)
      , "Path to the directory where to store DB data. Defaults to current dir" )
    ; "-db", String (fun dbname -> opts.dbname <- Some dbname), "Database to use"
    ; ( "-make-db-from"
      , String (fun path -> opts.make_db_from <- Some path)
      , "Create database from specified directory and exit" )
    ; ( "-to-out-file"
      , String (fun path -> opts.out_file <- Some path)
      , "Save query results to the file instead of printing it to stdout" )
    ; ( "-print-plan"
      , Unit (fun () -> opts.print_plan <- true)
      , "Print query plan before its results" )
    ; "-benchmark", Unit (fun () -> opts.benchmark <- true), "Benchmark queries"
    ]
    (fun arg ->
      Caml.Format.eprintf "Unrecognized argument '%s', try --help\n" arg;
      Caml.exit 1)
    "Read-Eval-Print-Loop for mini SQL language.\n\tusage: /REPL.exe -db=<dbname>";
  try
    let catalog_path = opts.catalog_path in
    let catalog = Meta.Catalog.init catalog_path in
    match opts.make_db_from with
    | None ->
      let module Env : Interpret.Environment = struct
        let catalog_path = catalog_path
        let catalog = catalog

        let storage =
          let dbname =
            match opts.dbname with
            | None ->
              Format.eprintf
                "Changing database via repl commands is not supported yet, please \
                 specify it using '-db' command line option";
              Caml.exit 1
            | Some dbname -> dbname
          in
          match Meta.Catalog.get_db dbname catalog with
          | None ->
            Format.eprintf "No database named %s" dbname;
            Caml.exit 1
          | Some db -> Relation.AccessManager.set_active db None catalog
        ;;

        let db = Relation.AccessManager.get_active_db storage
      end
      in
      Format.printf "Connected to %s\n%!" (Meta.Database.get_name Env.db);
      let run = if opts.batch then run_single else run_repl in
      let runner =
        if opts.benchmark
        then stat_query (module Env)
        else run_query opts.out_file opts.print_plan (module Env)
      in
      run runner
    | Some path ->
      let _c = Relation.AccessManager.make_db_from path catalog in
      ()
  with
  | Failure s -> Format.eprintf "An error occured: %s\n%!" s
;;
