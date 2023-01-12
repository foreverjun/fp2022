(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(** Monadic interpreter of mini SQL *)

open Base
open Utils
open Meta

(* Column is represented by its index in the tuple *)
type expr_column =
  { index : int
  ; table : table
  ; column : Meta.column
  }

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

let rec show_expression : type a. a expression -> _ =
  let bin cons_s l r =
    Format.sprintf "%s (%s, %s)" cons_s (show_expression l) (show_expression r)
  in
  function
  | IntCol { index } -> Format.sprintf "IntCol %d" index
  | StringCol { index } -> Format.sprintf "StringCol %s" (string_of_int index)
  | ConstInt i -> Format.sprintf "ConstInt %d" i
  | ConstString s -> Format.sprintf "ConstString %s" s
  | Plus (l, r) -> bin "Plus" l r
  | Minus (l, r) -> bin "Minus" l r
  | Mult (l, r) -> bin "Mult" l r
  | Div (l, r) -> bin "Div" l r
  | Equal (l, r) -> bin "Equal" l r
  | NotEqual (l, r) -> bin "NotEqual" l r
  | Less (l, r) -> bin "Less" l r
  | Greater (l, r) -> bin "Greater" l r
  | LessOrEq (l, r) -> bin "LessOrEq" l r
  | GreaterOrEq (l, r) -> bin "GreaterOrEq" l r
  | Or (l, r) -> bin "Or" l r
  | And (l, r) -> bin "And" l r
;;

type expression_type =
  [ `Int of int expression
  | `String of string expression
  | `Bool of bool expression
  ]

let show_expression_type = function
  | `Int (i : int expression) -> show_expression i
  | `String (s : string expression) -> show_expression s
  | `Bool (b : bool expression) -> show_expression b
;;

(* Since GADTs are not supported by variants lib *)
let plus l r = Plus (l, r)
let minus l r = Minus (l, r)
let mult l r = Mult (l, r)
let div l r = Div (l, r)
let eq l r = Equal (l, r)
let not_eq l r = NotEqual (l, r)
let less l r = Less (l, r)
let greater l r = Greater (l, r)
let less_or_eq l r = LessOrEq (l, r)
let greater_or_eq l r = GreaterOrEq (l, r)
let or_pred l r = Or (l, r)
let and_pred l r = And (l, r)

type pred_cons_helper =
  { pred_cons : 'a. 'a expression -> 'a expression -> bool expression }

type header = Ast.name list

let get_table_header table = Table.cols_as_fullnames table

let header_findi value hdr =
  let rec helper lst curi =
    match lst with
    | [] -> raise Not_found
    | hd :: tl -> if String.( = ) hd value then curi else helper tl (curi + 1)
  in
  helper hdr 0
;;

type join_constraint =
  | Left of bool expression
  | Right of bool expression
  | Inner of bool expression
  | Cross

let show_join_constraint = function
  | Left e -> Format.sprintf "LEFT ON %s" (show_expression e)
  | Right e -> Format.sprintf "RIGHT ON %s" (show_expression e)
  | Inner e -> Format.sprintf "INNER ON %s" (show_expression e)
  | Cross -> Format.sprintf "CROSS"
;;

let left_join_cons pred = Left pred
let right_join_cons pred = Right pred
let inner_join_cons pred = Inner pred

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
  | Datasource of { table : table }
  | Filter of
      { child : node
      ; filter : bool expression
      }
  | OrderBy of
      { child : node
      ; order_expr : Ast.orderby_clause list
      }

and node =
  { op : operator
  ; header : header
  }

let ( let* ) = Result.( >>= )

module type Environment = sig
  val catalog_path : string
  val catalog : Meta.catalog
  val db : Meta.database
  val storage : Relation.AccessManager.storage
end

module QueryGenerator (M : MonadFail) (E : Environment) : sig
  val generate : Ast.statement -> (node, Utils.error) M.t
end = struct
  open M

  type expr_column_helper =
    { table_h : Meta.table
    ; column_h : Meta.column
    }

  let header_findi_by_col { table_h; column_h } hdr =
    let cname = Table.col_fullname column_h table_h in
    { index = header_findi cname hdr; table = table_h; column = column_h }
  ;;

  let resolve_table tname =
    try return (Meta.Database.get_table_ci tname E.db) with
    | Not_found -> fail (UnknownTable tname)
    | AmbiguousEntity -> fail (AmbiguousTable tname)
  ;;

  let types_mismatch l r =
    TypesMismatch (Format.sprintf "'%s' and '%s' have incompatible types" l r)
  ;;

  let expr_types_mismatch l r =
    types_mismatch (show_expression_type l) (show_expression_type r)
  ;;

  let col_to_expression_type ({ column } as expr_col) =
    match column_type column with
    | Meta.IntCol -> `Int (IntCol expr_col)
    | Meta.StringCol -> `String (StringCol expr_col)
  ;;

  let resolve_column fullname tables =
    let resolve_with f cname entity =
      try return (f cname entity) with
      | Not_found -> fail (UnknownColumn fullname)
      | AmbiguousEntity -> fail (AmbiguousColumn fullname)
    in
    let resolve_col_with_table tname cname =
      let* table = resolve_with Table.get_table_by_name tname tables in
      resolve_with (fun cname table -> table, Table.get_col_ci cname table) cname table
    in
    match Caml.String.split_on_char '.' fullname with
    | [ dbname; tname; cname ] ->
      if String.( <> ) (Database.get_name E.db) dbname
      then fail (WrongDatabase dbname)
      else resolve_col_with_table tname cname
    | [ tname; cname ] -> resolve_col_with_table tname cname
    | [ cname ] -> resolve_with Database.get_col_ci cname tables
    (* actually impossible case, because such names should not pass parsing *)
    | _ -> raise (Invalid_argument "Wrongly shaped fullnames should not pass parsing")
  ;;

  let rec transform_arithm_expression hdr tables =
    let bin op l r =
      let* lexpr = transform_arithm_expression hdr tables l in
      let* rexpr = transform_arithm_expression hdr tables r in
      match lexpr, rexpr with
      | `Int lexpr, `Int rexpr -> return (`Int (op lexpr rexpr))
      | _ -> fail (expr_types_mismatch lexpr rexpr)
    in
    function
    | Ast.Column fullname ->
      let* table_h, column_h = resolve_column fullname tables in
      return (col_to_expression_type (header_findi_by_col { table_h; column_h } hdr))
    | Ast.Int num -> return (`Int (ConstInt num))
    | Ast.Plus (l, r) -> bin plus l r
    | Ast.Minus (l, r) -> bin minus l r
    | Ast.Mult (l, r) -> bin mult l r
    | Ast.Div (l, r) -> bin div l r
  ;;

  let transform_atom_expression hdr tables = function
    | Ast.String e -> return (`String (ConstString e))
    | Ast.Arithm e -> transform_arithm_expression hdr tables e
  ;;

  let rec transform_predicate hdr tables =
    let simple_pred { pred_cons } l r =
      let* l_atom_expr = transform_atom_expression hdr tables l in
      let* r_atom_expr = transform_atom_expression hdr tables r in
      match l_atom_expr, r_atom_expr with
      | `Int l, `Int r -> return (pred_cons l r)
      | `String l, `String r -> return (pred_cons l r)
      | l, r -> fail (expr_types_mismatch l r)
    in
    let pred_pred { pred_cons } l r =
      let* l_pred = transform_predicate hdr tables l in
      let* r_pred = transform_predicate hdr tables r in
      return (pred_cons l_pred r_pred)
    in
    let complex_pred cons l r =
      let* l_pred = transform_predicate hdr tables l in
      let* r_pred = transform_predicate hdr tables r in
      return (cons l_pred r_pred)
    in
    function
    | Ast.Equal (l, r) -> simple_pred { pred_cons = eq } l r
    | Ast.NotEqual (l, r) -> simple_pred { pred_cons = not_eq } l r
    | Ast.Less (l, r) -> simple_pred { pred_cons = less } l r
    | Ast.Greater (l, r) -> simple_pred { pred_cons = greater } l r
    | Ast.LessOrEq (l, r) -> simple_pred { pred_cons = less_or_eq } l r
    | Ast.GreaterOrEq (l, r) -> simple_pred { pred_cons = greater_or_eq } l r
    | Ast.PredEqual (l, r) -> pred_pred { pred_cons = eq } l r
    | Ast.PredNotEqual (l, r) -> pred_pred { pred_cons = not_eq } l r
    | Ast.PredLess (l, r) -> pred_pred { pred_cons = less } l r
    | Ast.PredGreater (l, r) -> pred_pred { pred_cons = greater } l r
    | Ast.PredLessOrEq (l, r) -> pred_pred { pred_cons = less_or_eq } l r
    | Ast.PredGreaterOrEq (l, r) -> pred_pred { pred_cons = greater_or_eq } l r
    | Ast.OrPred (l, r) -> complex_pred or_pred l r
    | Ast.AndPred (l, r) -> complex_pred and_pred l r
  ;;

  let transform_const_predicate = transform_predicate [] []

  let transform_projection_item hdr tables = function
    | Ast.Star ->
      return
        (List.mapi
           ~f:(fun index fullname ->
             let table, column = Database.get_col_by_fullname_ci fullname E.db in
             col_to_expression_type { index; table; column })
           hdr)
    | ProjAtomItem (expr, _alias) ->
      (match expr with
       | AtomExpr atom_expr ->
         let* expr = transform_atom_expression hdr tables atom_expr in
         return [ expr ]
       | PredExpr pred_expr ->
         let* expr = transform_predicate hdr tables pred_expr in
         return [ `Bool expr ])
  ;;

  let calc_projection_header hdr =
    (* This is the name postgres uses for expressions without alias *)
    let dummy_name = "?column?" in
    let get_cname = function
      | Ast.PredExpr _ -> dummy_name
      | Ast.AtomExpr expr ->
        (match expr with
         | Ast.String _ -> dummy_name
         | Ast.Arithm expr ->
           (match expr with
            | Column name -> name
            | _ -> dummy_name))
    in
    function
    | Ast.Star -> hdr
    | ProjAtomItem (expr, alias) ->
      (match alias with
       | Some name -> [ name ]
       | None -> [ get_cname expr ])
  ;;

  let join_headers { header = lhdr } { header = rhdr } = lhdr @ rhdr
  let get_node_header { header } = header

  let cons_datasource table =
    { op = Datasource { table }; header = get_table_header table }
  ;;

  let cons_cross_join left right =
    { op = Join { left; right; join_constraint = Cross }
    ; header = join_headers left right
    }
  ;;

  let cons_projection ({ header = child_hdr } as child) proj_items tables =
    (* not very efficient, but concise *)
    let* projections =
      M.all (List.map ~f:(transform_projection_item child_hdr tables) proj_items)
    in
    let projection = List.concat projections in
    return
      { op = Projection { child; projection }
      ; header = List.concat (List.map ~f:(calc_projection_header child_hdr) proj_items)
      }
  ;;

  let collect_tables_from_expr =
    let rec helper : type a. a expression -> table list =
      let bin l r = helper l @ helper r in
      function
      | IntCol { table } | StringCol { table } -> [ table ]
      | ConstInt _ | ConstString _ -> []
      | Plus (l, r) | Minus (l, r) | Mult (l, r) | Div (l, r) -> bin l r
      | Equal (l, r) -> bin l r
      | NotEqual (l, r) -> bin l r
      | Less (l, r) -> bin l r
      | Greater (l, r) -> bin l r
      | LessOrEq (l, r) -> bin l r
      | GreaterOrEq (l, r) -> bin l r
      | Or (l, r) | And (l, r) -> bin l r
    in
    helper
  ;;

  let rec collect_tables_from_node { op } =
    match op with
    | Datasource { table } -> [ table ]
    | Filter { child } -> collect_tables_from_node child
    | Projection { child } -> collect_tables_from_node child
    | OrderBy { child } -> collect_tables_from_node child
    | Join { left; right } ->
      collect_tables_from_node left @ collect_tables_from_node right
  ;;

  module PredTables = Caml.Set.Make (struct
    type t = table

    let compare = Caml.compare
  end)

  let collect_tables_from_pred tables =
    let bin f l r =
      let* lt = f l in
      let* rt = f r in
      return (PredTables.union lt rt)
    in
    let rec collect_tables_from_arithm_expr =
      let bin l r = bin collect_tables_from_arithm_expr l r in
      function
      | Ast.Column name ->
        let* table, _col = resolve_column name tables in
        return (PredTables.singleton table)
      | Ast.Int _ -> return PredTables.empty
      | Ast.Plus (l, r) | Ast.Minus (l, r) | Ast.Mult (l, r) | Ast.Div (l, r) -> bin l r
    in
    let collect_tables_from_atom_expr = function
      | Ast.String _ -> return PredTables.empty
      | Ast.Arithm e -> collect_tables_from_arithm_expr e
    in
    let rec helper =
      let bin_pred l r = bin helper l r in
      let bin_atom l r = bin collect_tables_from_atom_expr l r in
      function
      | Ast.OrPred (l, r) -> bin_pred l r
      | Ast.AndPred (l, r) -> bin_pred l r
      | Ast.PredEqual (l, r) -> bin_pred l r
      | Ast.PredNotEqual (l, r) -> bin_pred l r
      | Ast.PredLess (l, r) -> bin_pred l r
      | Ast.PredGreater (l, r) -> bin_pred l r
      | Ast.PredLessOrEq (l, r) -> bin_pred l r
      | Ast.PredGreaterOrEq (l, r) -> bin_pred l r
      | Ast.Equal (l, r) -> bin_atom l r
      | Ast.NotEqual (l, r) -> bin_atom l r
      | Ast.Less (l, r) -> bin_atom l r
      | Ast.Greater (l, r) -> bin_atom l r
      | Ast.LessOrEq (l, r) -> bin_atom l r
      | Ast.GreaterOrEq (l, r) -> bin_atom l r
    in
    fun pred ->
      let* tables = helper pred in
      return (Caml.List.of_seq (PredTables.to_seq tables))
  ;;

  let rec conjuncts_of_pred = function
    | Ast.AndPred (l, r) ->
      (* This disunions predicates like t1.a=1 AND t2.b=1 AND t1.b=1 in not
         the most efficient way ([t1.a=1], [t2.b=1], [t1.b=1] instead of
         [t1.a=1 AND t1.b=1], [t2.b=1] which is better for predicate pushdown).
         I'll just combine them later during construction of filter operators cause
         it seems simpler *)
      conjuncts_of_pred l @ conjuncts_of_pred r
    | pred -> [ pred ]
  ;;

  let pred_of_conjuncts = function
    | [] -> raise (Invalid_argument "Conjuncts list should not be empty")
    | hd :: conjuncts ->
      List.fold conjuncts ~init:hd ~f:(fun acc cur -> Ast.AndPred (acc, cur))
  ;;

  let get_tables_from_ds =
    let rec helper = function
      | Ast.Table name ->
        let* table = resolve_table name in
        return [ table ]
      | Join { left; right } ->
        let* left_t = helper left in
        let* right_t = helper right in
        return (left_t @ right_t)
    in
    helper
  ;;

  let get_from_tables from =
    let* from = M.all (List.map ~f:get_tables_from_ds from) in
    let from_tables = List.concat from in
    let rec tables_unique = function
      | [] -> None
      | hd :: tl ->
        if List.exists ~f:(Caml.( = ) hd) tl then Some hd else tables_unique tl
    in
    match tables_unique from_tables with
    | None -> return (from, from_tables)
    | Some t -> fail (SpecifiedMoreThanOnce (Table.name t))
  ;;

  let cons_filter ({ header } as child) tables filter =
    let* filter = transform_predicate header tables filter in
    let op = Filter { child; filter } in
    return { op; header }
  ;;

  let add_pred_to_filter ({ op } as node) pred =
    match op with
    | Filter ({ filter } as filter_op) ->
      let new_filter = And (pred, filter) in
      { node with op = Filter { filter_op with filter = new_filter } }
    | _ -> raise (Invalid_argument "For filter only")
  ;;

  module TableMap = Caml.Map.Make (struct
    type t = table

    let compare t1 t2 = String.compare (Table.name t1) (Table.name t2)
  end)

  let merge_preds next_pred = function
    | None -> Some next_pred
    | Some pred -> Some (Ast.AndPred (pred, next_pred))
  ;;

  (* Constructs map<table, tree> where tree is a filter -> datasource or just
     a datasource operator *)
  let pushdown_predicates tables datasources (tables_per_pred, conjuncts) =
    let tables_to_filter =
      Caml.List.fold_left2
        (fun m table next_pred -> TableMap.update table (merge_preds next_pred) m)
        TableMap.empty
        tables_per_pred
        conjuncts
    in
    let pushdown table ds =
      let found = TableMap.find_opt table tables_to_filter in
      match found with
      | Some pred ->
        let* filter = cons_filter ds [ table ] pred in
        return (table, filter)
      | _ -> return (table, ds)
    in
    Caml.List.fold_left2
      (fun m table ds ->
        let* m = m in
        let* table, op = pushdown table ds in
        return (TableMap.add table op m))
      (return TableMap.empty)
      tables
      datasources
  ;;

  let classify_conjuncts tables conjuncts =
    (* Nightmare *)
    let* tables_per_pred =
      M.all (List.map ~f:(collect_tables_from_pred tables) conjuncts)
    in
    let const, non_const =
      List.partition_map
        ~f:(fun (tables, pred) ->
          match tables with
          | [] -> First pred
          | _ -> Second (tables, pred))
        (Caml.List.combine tables_per_pred conjuncts)
    in
    let pushdownable, non_pushdownable =
      List.partition_map
        ~f:(fun (tables, pred) ->
          match tables with
          | [ t ] -> First (t, pred)
          | _ -> Second (tables, pred))
        non_const
    in
    (* Some kinds of filter predicates with >2 tables can be transformed to inner join:
       E.g., in the query
          SELECT * FROM t1, t2 JOIN t3 ON t2.a=t3.a WHERE t1.a + t2.a = t3.a
       the filtration can be transformed to:
          SELECT * FROM t1 JOIN (t2 JOIN t3 ON t2.a=t3.a) ON t1.a + t2.a = t3.a
       whereas in the query
          SELECT * FROM t1, t2, t3 WHERE t1.a + t2.a = t3.a
       the same filtration cannot be expressed using only inner joins in any way
       (however it's possible to replace specifically this predicate with cross product
       and inner join, but that's another story).
       Its hard to distiguish between these cases, so for now transform filtration to
       join only if it has exactly two tables. Also, queries very rarely have such
       complex predicates, so for the vast majority of queries this algorithm will
       still be the most efficient.
    *)
    let join_preds, top_preds =
      List.partition_map
        ~f:(fun (tables, pred) ->
          match tables with
          | [ t1; t2 ] -> First (t1, t2, pred)
          | _ -> Second (tables, pred))
        non_pushdownable
    in
    return (const, pushdownable, join_preds, top_preds)
  ;;

  let cons_join left right type_cons pred tables =
    let header = join_headers left right in
    let* pred = transform_predicate header tables pred in
    let join = Join { left; right; join_constraint = type_cons pred } in
    return { op = join; header }
  ;;

  let rec transform_ds ds_tables dses_m = function
    | Ast.Table _ -> return (TableMap.find (List.hd_exn ds_tables) dses_m)
    | Ast.Join { left; right; join_constraint } ->
      let* left_tables = get_tables_from_ds left in
      let* right_tables = get_tables_from_ds right in
      let* left = transform_ds left_tables dses_m left in
      let* right = transform_ds right_tables dses_m right in
      let cons_join type_cons pred =
        cons_join left right type_cons pred (left_tables @ right_tables)
      in
      (match join_constraint with
       | Ast.Left pred -> cons_join left_join_cons pred
       | Ast.Right pred -> cons_join right_join_cons pred
       | Ast.Inner pred -> cons_join inner_join_cons pred
       | Ast.Cross -> return (cons_cross_join left right))
  ;;

  (* Place const filters above a random table. But actually they should be
     precalculated (or atleast places above the smallest table).
   *)
  let gen_const_preds dses_m = function
    | [] -> return dses_m
    | const_preds ->
      let table = fst (TableMap.choose dses_m) in
      let* const_pred = transform_const_predicate (pred_of_conjuncts const_preds) in
      let dses_m =
        TableMap.update
          table
          (function
           | Some tree -> Some (add_pred_to_filter tree const_pred)
           | None -> raise (Invalid_argument "dses_m cannot be an emtpy"))
          dses_m
      in
      return dses_m
  ;;

  let gen_bottom_level tables datasources = function
    | Some where ->
      let conjuncts = conjuncts_of_pred where in
      let* const_preds, pushdownable, join_preds, complex_preds =
        classify_conjuncts tables conjuncts
      in
      let* dses_m =
        pushdown_predicates tables datasources (Caml.List.split pushdownable)
      in
      let* dses_m = gen_const_preds dses_m const_preds in
      return (Some (join_preds, complex_preds), dses_m)
    | None ->
      return
        ( None
        , Caml.List.fold_left2
            (fun m t ds -> TableMap.add t ds m)
            TableMap.empty
            tables
            datasources )
  ;;

  (* Map <left, right> -> predicate means that items with indices `left` and `right`
     in the from clause can be inner joined using predicate `predicate` *)
  module JoinableIndicesMap = Caml.Map.Make (struct
    type t = int * int

    let compare = Caml.compare
  end)

  let find_joinable_dses preds_opt from_tables_per_ds =
    let find_joinable_dses (ltable, rtable) =
      let find_index t =
        Core.List.findi_exn from_tables_per_ds ~f:(fun _ -> List.exists ~f:(Caml.( = ) t))
      in
      fst (find_index ltable), fst (find_index rtable)
    in
    match preds_opt with
    | Some (join_preds, _complex_preds) ->
      List.fold
        join_preds
        ~f:(fun ji_map (ltable, rtable, next_pred) ->
          let li, ri = find_joinable_dses (ltable, rtable) in
          JoinableIndicesMap.update (li, ri) (merge_preds next_pred) ji_map)
        ~init:JoinableIndicesMap.empty
    | None -> JoinableIndicesMap.empty
  ;;

  let really_join_dses joinable_m from =
    let get_ds = List.nth_exn from in
    let not_joined =
      List.filteri from ~f:(fun i _ ->
        not
          (JoinableIndicesMap.fold
             (fun (l, r) _ acc -> acc || i = l || i = r)
             joinable_m
             false))
    in
    let* joined =
      JoinableIndicesMap.fold
        (fun indices pred joined ->
          let* joined = joined in
          let* ds =
            match indices with
            | li, ri when li = ri ->
              let child = get_ds li in
              (* It's not the most efficient tree (probably, actually it heavily depends on the
                 predicate and the join itself), we can try to generate the filter operator over
                 join's either left or right subtree if one of them has all the required tables.
                 I'll do it later if I have time. Note that the child here is guaranteed to be join
                 because it contains atleast several tables (guaranteed by the generation algorithm).
               *)
              let* filter = cons_filter child (collect_tables_from_node child) pred in
              return filter
            | li, ri ->
              let lds = get_ds li in
              let rds = get_ds ri in
              let tables = collect_tables_from_node lds @ collect_tables_from_node rds in
              let* join = cons_join lds rds inner_join_cons pred tables in
              return join
          in
          return (ds :: joined))
        joinable_m
        (return [])
    in
    return (not_joined @ joined)
  ;;

  let join_dses joinable_m from =
    let contains_same_table (ts1, _) (ts2, _) =
      let l1, r1 = ts1 in
      let l2, r2 = ts2 in
      let ( = ) = Caml.( = ) in
      if l1 = l2 || r1 = r2 || l1 = r2 || l2 = r1 then 0 else -1
    in
    (* If any table occurs more than once in joins predicates, don't join anything.
       Super inefficent for some types of queries but at least correct (I have no time to do
       it right)
     *)
    match
      Core.List.find_a_dup
        (JoinableIndicesMap.bindings joinable_m)
        ~compare:contains_same_table
    with
    | Some _ ->
      let unable_to_join =
        JoinableIndicesMap.fold (fun _ -> merge_preds) joinable_m None
      in
      return (unable_to_join, from)
    | None ->
      let* joined = really_join_dses joinable_m from in
      return (None, joined)
  ;;

  let generate = function
    (* Insert queries are not supported yet and won't pass the parsing *)
    | Ast.Insert ->
      raise
        (Invalid_argument "Insert queries are not supported and should not pass parsing")
    | Ast.Select { projection; from; where } ->
      let* from_tables_per_ds, all_tables = get_from_tables from in
      let datasources = List.map all_tables ~f:cons_datasource in
      let* preds_opt, dses_m = gen_bottom_level all_tables datasources where in
      let* from =
        M.all
          (List.map2_exn from_tables_per_ds from ~f:(fun ds_tables ast_ds ->
             transform_ds ds_tables dses_m ast_ds))
      in
      let joinable_m = find_joinable_dses preds_opt from_tables_per_ds in
      let* unable_to_join_opt, final_dses = join_dses joinable_m from in
      let datasources_hd = List.hd_exn final_dses in
      let datasources_tl = List.tl final_dses in
      let tree =
        match datasources_tl with
        | None -> datasources_hd
        | Some tl -> List.fold tl ~f:cons_cross_join ~init:datasources_hd
      in
      let* tree =
        let pred =
          match preds_opt, unable_to_join_opt with
          | Some (_, []), None -> None
          | Some (_, []), Some pred -> Some pred
          | None, Some pred -> Some pred
          | Some (_, complex_preds), None ->
            let _, preds = Caml.List.split complex_preds in
            Some (pred_of_conjuncts preds)
          | Some (_, complex_preds), Some pred ->
            let _, preds = Caml.List.split complex_preds in
            Some (Ast.AndPred (pred_of_conjuncts preds, pred))
          | None, None -> None
        in
        match pred with
        | None -> return tree
        | Some pred -> cons_filter tree all_tables pred
      in
      cons_projection tree projection all_tables
  ;;
end

module Interpret (M : MonadFail) (E : Environment) : sig
  val run : Ast.statement -> (header * Relation.t, Utils.error) M.t
  val explain : Ast.statement -> (node, Utils.error) M.t
end = struct
  open M
  open Relation

  let eval_expr expr t1 ?(t2 = None) =
    let rec eval_expr : type a. a expression -> a =
      let bin op l r = op (eval_expr l) (eval_expr r) in
      let nth get index =
        match t2 with
        | Some t2 ->
          let t1_len = Tuple.length t1 in
          if index < t1_len then get index t1 else get (index - t1_len) t2
        | None -> get index t1
      in
      function
      | IntCol { index } -> nth Tuple.nth_as_int index
      | StringCol { index } -> nth Tuple.nth_as_string index
      | ConstInt i -> i
      | ConstString s -> s
      | Plus (l, r) -> bin ( + ) l r
      | Minus (l, r) -> bin ( - ) l r
      | Mult (l, r) -> bin ( * ) l r
      | Div (l, r) -> bin ( - ) l r
      | Equal (l, r) -> bin Caml.( = ) l r
      | NotEqual (l, r) -> bin Caml.( <> ) l r
      | Less (l, r) -> bin Caml.( < ) l r
      | Greater (l, r) -> bin Caml.( > ) l r
      | LessOrEq (l, r) -> bin Caml.( <= ) l r
      | GreaterOrEq (l, r) -> bin Caml.( >= ) l r
      | Or (l, r) -> bin ( || ) l r
      | And (l, r) -> bin ( && ) l r
    in
    eval_expr expr
  ;;

  let rec eval { op } =
    match op with
    | Datasource { table } -> AccessManager.get_rel table E.storage
    | Filter { child; filter } ->
      let child_data = eval child in
      Relation.filter (eval_expr ~t2:None filter) child_data
    | Projection { child; projection } ->
      let child_data = eval child in
      let map t =
        Tuple.of_list
          (List.map
             ~f:
               (function
                | `Int e -> Tuple.Int (eval_expr ~t2:None e t)
                | `String e -> Tuple.String (eval_expr ~t2:None e t)
                | `Bool e -> Tuple.String (Bool.to_string (eval_expr ~t2:None e t)))
             projection)
      in
      Relation.map map child_data
    | Join { left; right; join_constraint } ->
      let left_data = eval left in
      let right_data = eval right in
      (match join_constraint with
       | Cross -> Relation.cross_product left_data right_data
       | Inner e ->
         Relation.join (fun t1 t2 -> eval_expr e t1 ~t2:(Some t2)) left_data right_data
       | Left _e | Right _e -> raise NotImplemented)
    | OrderBy _ -> raise NotImplemented
  ;;

  let run ast =
    let* ({ header } as plan) =
      let module Generator = QueryGenerator (M) (E) in
      Generator.generate ast
    in
    return (header, eval plan)
  ;;

  let explain ast =
    let module Generator = QueryGenerator (M) (E) in
    Generator.generate ast
  ;;
end

let execute f query =
  let ans =
    match Parser.parse query with
    | Caml.Result.Ok ast -> f ast
    | Caml.Result.Error error -> Result.fail (ParsingError error)
  in
  ans
;;

let interpret query (module E : Environment) =
  let module I = Interpret (Result) (E) in
  execute I.run query
;;

let explain query (module E : Environment) =
  let module I = Interpret (Result) (E) in
  execute I.explain query
;;
