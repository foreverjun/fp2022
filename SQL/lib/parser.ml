(** Copyright 2021-2022, Michael Polyntsov and contributors *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Angstrom
open Ast

(*** Test helper functions ***)

let parse_string parser s = Angstrom.parse_string ~consume:All parser s

let assert_ok show parser s expected =
  match parse_string parser s with
  | Result.Ok actual when actual = expected -> true
  | Result.Ok actual ->
    Format.printf
      "When parsing '%s':\nExpected\n\t%s\ngot\n\t%s\n"
      s
      (show expected)
      (show actual);
    false
  | Result.Error msg ->
    Format.printf "Parsing of '%s' failed with error %s\n" s msg;
    false
;;

let assert_ok_s parser s = assert_ok Fun.id parser s s

let assert_error parser s =
  match parse_string parser s with
  | Result.Error _ -> true
  | Result.Ok _ -> false
;;

(*** Small auxiliary parsers ***)

(* Returns true if provided char is any kind of whitespace *)
let is_space = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

(* Skips spaces *)
let spaces_p = skip_while is_space
let lspaces p = spaces_p *> p
let rspaces p = p <* spaces_p
let spaces p = spaces_p *> p <* spaces_p

(* Parses dot (symbol '.') *)
let dot_p =
  peek_char
  >>= function
  | Some '.' -> advance 1 >>| fun () -> true
  | _ -> return false
;;

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

(* Parses any string containing only letters, underscores and digits.
   The string must start with a letter or an underscore. *)
let entity_name_p =
  let is_letter = function
    | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false
  in
  (peek_char
  >>= function
  | Some c when is_letter c -> return (String.make 1 c)
  | Some c -> fail ("Entity name cannot start with " ^ String.make 1 c)
  | _ -> fail "Entity name cannot be empty")
  *> take_while1 (fun c -> is_letter c || is_digit c)
;;

(* Takes a parser and returns a new parser that is able to parse [topname.]name where
   [topname.] is parsed using top_p *)
let complex_entity_name_p top_p =
  top_p
  >>= fun name ->
  dot_p
  >>= function
  | false -> return name
  | true -> entity_name_p >>| Format.sprintf "%s.%s" name
;;

(*** Atomic expression parsers ***)

(* Table name parser, parses [database.]table strings *)
let table_name_p = complex_entity_name_p entity_name_p

let%test _ = assert_ok_s table_name_p "main"
let%test _ = assert_ok_s table_name_p "MaIn"
let%test _ = assert_ok_s table_name_p "maindb.main"
let%test _ = assert_error table_name_p ".main"
let%test _ = assert_error table_name_p "maindb..main"
let%test _ = assert_error table_name_p "Main."
let%test _ = assert_error table_name_p "maindb.main."
let%test _ = assert_error table_name_p "1table"

(* Column name parser, parses [[database.]table.]column strings *)
let column_name_p = complex_entity_name_p table_name_p

let%test _ = assert_ok_s column_name_p "main"
let%test _ = assert_ok_s column_name_p "main.a"
let%test _ = assert_ok_s column_name_p "main.main.a"
let%test _ = assert_error column_name_p "main.main.a."
let%test _ = assert_error column_name_p ".main.main.a"

let column_p =
  let column_p = column_name_p >>| column in
  lspaces column_p
;;

(* Parser for integer sign *)
let sign_p =
  peek_char
  >>= function
  | Some '-' -> advance 1 >>| fun () -> "-"
  | Some '+' -> advance 1 >>| fun () -> "+"
  | Some c when is_digit c -> return "+"
  | _ -> fail "Sign or digit expected"
;;

(* Parser of integer value *)
let integer_p =
  let integer_p =
    sign_p
    >>= fun sign ->
    take_while1 is_digit >>| fun str_int -> Int (int_of_string (sign ^ str_int))
  in
  lspaces integer_p
;;

let assert_ok_int s expected = assert_ok show_arithm_expression integer_p s expected

let%test _ = assert_ok_int "+10" (Int 10)
let%test _ = assert_ok_int " +10" (Int 10)
let%test _ = assert_ok_int "-10" (Int (-10))
let%test _ = assert_ok_int "42" (Int 42)
let%test _ = assert_error integer_p "42-"
let%test _ = assert_error integer_p "--42"
let%test _ = assert_error integer_p "42."

let single_quote = '\''
let single_quote_p = char single_quote

(* Parses single quoted string *)
let string_value_p =
  let string_value_p =
    single_quote_p *> take_while (( != ) single_quote) <* single_quote_p >>| string
  in
  lspaces string_value_p
;;

let parens_p p = lspaces (char '(' *> p <* lspaces (char ')'))

let infix_op_p ?(ci = false) str_op cons =
  let infix_op_p = (if ci then string_ci else Angstrom.string) str_op *> return cons in
  lspaces infix_op_p
;;

let add_p = infix_op_p "+" plus
let sub_p = infix_op_p "-" minus
let mul_p = infix_op_p "*" mult
let div_p = infix_op_p "/" div

let chainl1_p e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init
;;

let arithm_expr_p =
  fix (fun expr ->
    let factor = parens_p expr <|> integer_p <|> column_p in
    let term = chainl1_p factor (mul_p <|> div_p) in
    chainl1_p term (add_p <|> sub_p))
;;

let atom_expr_p = arithm_expr_p >>| arithm <|> string_value_p
let assert_ok_atom_expr s expected = assert_ok show_atom_expression atom_expr_p s expected

let%test _ = assert_ok_atom_expr "'abc'" (String "abc")
let%test _ = assert_ok_atom_expr "'  kakadu'" (String "  kakadu")
let%test _ = assert_ok_atom_expr "    'k a k a d u'" (String "k a k a d u")
let%test _ = assert_ok_atom_expr "'r_d_b_m_s'" (String "r_d_b_m_s")
let%test _ = assert_ok_atom_expr "'\"kakadu\"'" (String "\"kakadu\"")
let%test _ = assert_ok_atom_expr "''" (String "")
let%test _ = assert_ok_atom_expr "1 + 1" (Arithm (Plus (Int 1, Int 1)))
let%test _ = assert_ok_atom_expr "(1 + 1)" (Arithm (Plus (Int 1, Int 1)))

let%test _ =
  assert_ok_atom_expr "(1 + 1) * 2" (Arithm (Mult (Plus (Int 1, Int 1), Int 2)))
;;

let%test _ = assert_ok_atom_expr "1 * 1" (Arithm (Mult (Int 1, Int 1)))
let%test _ = assert_ok_atom_expr "1 *  8" (Arithm (Mult (Int 1, Int 8)))
let%test _ = assert_ok_atom_expr "1 - column" (Arithm (Minus (Int 1, Column "column")))
let%test _ = assert_ok_atom_expr "A / B" (Arithm (Div (Column "A", Column "B")))
let%test _ = assert_ok_atom_expr "  A/43" (Arithm (Div (Column "A", Int 43)))
(* It works like this iatom_n postgres, so I'll leave it as it is *)
let%test _ = assert_ok_atom_expr "1+-1" (Arithm (Plus (Int 1, Int (-1))))

let%test _ =
  assert_ok_atom_expr
    "1*8 + 3 + (2 * 4)"
    (Arithm (Plus (Plus (Mult (Int 1, Int 8), Int 3), Mult (Int 2, Int 4))))
;;

let%test _ =
  assert_ok_atom_expr
    "1*8 + 3 + (tablename.column * 4)"
    (Arithm
       (Plus (Plus (Mult (Int 1, Int 8), Int 3), Mult (Column "tablename.column", Int 4))))
;;

let%test _ =
  assert_ok_atom_expr
    "1 * (8 + 3) - db.table.col"
    (Arithm (Minus (Mult (Int 1, Plus (Int 8, Int 3)), Column "db.table.col")))
;;

let%test _ = assert_error atom_expr_p "1 + 'abc'"
let%test _ = assert_error atom_expr_p "'test'test'"
let%test _ = assert_error atom_expr_p "'''"
let%test _ = assert_error atom_expr_p "1 * (8 + 3) - db.db.table.col"

(*** Predicate parsers ***)

let equal_p = infix_op_p "=" equal
let not_equal_p = infix_op_p "!=" notequal
let less_p = infix_op_p "<" less
let greater_p = infix_op_p ">" greater
let less_or_eq_p = infix_op_p "<=" lessoreq
let greater_or_eq_p = infix_op_p ">=" greateroreq
let pred_equal_p = infix_op_p "=" predequal
let pred_not_equal_p = infix_op_p "!=" prednotequal
let pred_less_p = infix_op_p "<" predless
let pred_greater_p = infix_op_p ">" predgreater
let pred_less_or_eq_p = infix_op_p "<=" predlessoreq
let pred_greater_or_eq_p = infix_op_p ">=" predgreateroreq

let atom_predicate_p =
  let pred_p =
    equal_p <|> not_equal_p <|> less_or_eq_p <|> greater_or_eq_p <|> less_p <|> greater_p
  in
  lift3 (fun x pred y -> pred x y) atom_expr_p pred_p atom_expr_p
;;

let and_p = infix_op_p ~ci:true "AND" andpred
let or_p = infix_op_p ~ci:true "OR" orpred

let predicate_p =
  fix (fun expr ->
    let pred_predicate_p =
      let pred_pred_p =
        pred_equal_p
        <|> pred_not_equal_p
        <|> pred_less_or_eq_p
        <|> pred_greater_or_eq_p
        <|> pred_less_p
        <|> pred_greater_p
      in
      lift3 (fun x pred y -> pred x y) (parens_p expr) pred_pred_p (parens_p expr)
    in
    let factor = pred_predicate_p <|> parens_p expr <|> atom_predicate_p in
    let term = chainl1_p factor and_p in
    chainl1_p term or_p)
;;

let assert_ok_pred s expected = assert_ok show_predicate predicate_p s expected

let%test _ = assert_ok_pred "1 < 2" (Less (Arithm (Int 1), Arithm (Int 2)))
let%test _ = assert_ok_pred "1 > A" (Greater (Arithm (Int 1), Arithm (Column "A")))
let%test _ = assert_ok_pred "1=23" (Equal (Arithm (Int 1), Arithm (Int 23)))
let%test _ = assert_ok_pred "A<=B" (LessOrEq (Arithm (Column "A"), Arithm (Column "B")))
let%test _ = assert_ok_pred "A >= 0" (GreaterOrEq (Arithm (Column "A"), Arithm (Int 0)))
let%test _ = assert_ok_pred " i  != 0" (NotEqual (Arithm (Column "i"), Arithm (Int 0)))

let%test _ =
  assert_ok_pred
    "t1.id = t2.id"
    (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
;;

let%test _ =
  assert_ok_pred
    "t1.id = t2.id and c = 1000 and d < 101"
    (AndPred
       ( AndPred
           ( Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id"))
           , Equal (Arithm (Column "c"), Arithm (Int 1000)) )
       , Less (Arithm (Column "d"), Arithm (Int 101)) ))
;;

let%test _ = assert_ok_pred "'abc' = col" (Equal (String "abc", Arithm (Column "col")))

let%test _ =
  assert_ok_pred
    "1 + 1 >= 2 AND A < B"
    (AndPred
       ( GreaterOrEq (Arithm (Plus (Int 1, Int 1)), Arithm (Int 2))
       , Less (Arithm (Column "A"), Arithm (Column "B")) ))
;;

let%test _ =
  assert_ok_pred
    "2 * B < C OR 1 + 1 >= 2 AND A < B"
    (OrPred
       ( Less (Arithm (Mult (Int 2, Column "B")), Arithm (Column "C"))
       , AndPred
           ( GreaterOrEq (Arithm (Plus (Int 1, Int 1)), Arithm (Int 2))
           , Less (Arithm (Column "A"), Arithm (Column "B")) ) ))
;;

let%test _ =
  assert_ok_pred
    "(2 * B < C OR 1 + 1 >= 2) AND A < B"
    (AndPred
       ( OrPred
           ( Less (Arithm (Mult (Int 2, Column "B")), Arithm (Column "C"))
           , GreaterOrEq (Arithm (Plus (Int 1, Int 1)), Arithm (Int 2)) )
       , Less (Arithm (Column "A"), Arithm (Column "B")) ))
;;

let%test _ =
  assert_ok_pred
    "(A < C) < (D < B)"
    (PredLess
       ( Less (Arithm (Column "A"), Arithm (Column "C"))
       , Less (Arithm (Column "D"), Arithm (Column "B")) ))
;;

let%test _ = assert_error predicate_p "A < C < D < B"

(*** Expression parser *)
let expr_p = predicate_p >>| predexpr <|> (atom_expr_p >>| atomexpr)

(*** Projection item parsers ***)
let star_p = lspaces (char '*')
let as_p = spaces (string_ci "AS")

let alias_p =
  option "" as_p
  >>= function
  | "" -> return None
  | _ -> entity_name_p >>| fun name -> Some name
;;

let single_item_p = lift2 projatomitem expr_p alias_p
let proj_item_p = star_p *> return Star <|> single_item_p
let assert_ok_proj s expected = assert_ok show_projection_item proj_item_p s expected

let%test _ = assert_ok_proj "*" Star
let%test _ = assert_ok_proj " *" Star

let%test _ =
  assert_ok_proj "1 +3" (ProjAtomItem (AtomExpr (Arithm (Plus (Int 1, Int 3))), None))
;;

let%test _ =
  assert_ok_proj "col as A" (ProjAtomItem (AtomExpr (Arithm (Column "col")), Some "A"))
;;

let%test _ =
  assert_ok_proj
    "2 * col as Alias"
    (ProjAtomItem (AtomExpr (Arithm (Mult (Int 2, Column "col"))), Some "Alias"))
;;

(*** Order by item parsers ***)

let asc_p = string_ci "ASC" *> return asc
let desc_p = string_ci "DESC" *> return desc

let default_asc_p =
  peek_char
  >>= function
  | Some ',' | None -> return asc
  | Some c -> fail ("Unexpected character '%s' in order by clause" ^ String.make 1 c)
;;

let orderby_clause_p = lift2 ( |> ) expr_p (lspaces (desc_p <|> asc_p <|> default_asc_p))

let assert_ok_orderby s expected =
  assert_ok show_orderby_clause orderby_clause_p s expected
;;

let%test _ = assert_ok_orderby "1 + 1" (Asc (AtomExpr (Arithm (Plus (Int 1, Int 1)))))

let%test _ =
  assert_ok_orderby "1 + A desc" (Desc (AtomExpr (Arithm (Plus (Int 1, Column "A")))))
;;

let%test _ =
  assert_ok_orderby
    "Desc / Asc"
    (Asc (AtomExpr (Arithm (Div (Column "Desc", Column "Asc")))))
;;

let%test _ = assert_error orderby_clause_p "1 + A sc"

(*** Datasource parsers ***)

let table_p =
  let table_p = table_name_p >>| fun name -> Table name in
  lspaces table_p
;;

let on_word_p = string_ci "ON"
let join_word_p = string_ci "JOIN" *> return inner
let inner_p = string_ci "INNER JOIN" *> return inner
let left_p = string_ci "LEFT JOIN" *> return left
let right_p = string_ci "RIGHT JOIN" *> return right
let cross_p = string_ci "CROSS JOIN" *> return cross

let chain_joins chain link =
  let rec go chain =
    lift
      (fun (join_constraint, right) -> Join { left = chain; right; join_constraint })
      link
    >>= go
    <|> return chain
  in
  chain >>= go
;;

let join_p =
  fix (fun join ->
    let left = parens_p join <|> table_p in
    let right = parens_p join <|> join <|> table_p in
    let noncross_join =
      lift3
        (fun join_constraint right pred -> join_constraint pred, right)
        (lspaces (join_word_p <|> inner_p <|> left_p <|> right_p))
        (lspaces right)
        (lspaces (on_word_p *> predicate_p))
    in
    let cross_join =
      (* For cross join right side should be either nested join in parentheses or a table
         (and that's what we only parse as the left side of the non-cross join). This is not
         the case for the non-cross joins.
         Explanatory examples:
         Join:
            t1 join t2 join t3 on t2.id = t3.id on t1.id = t2.id
         is equivalent to (note the associativity):
            t1 join (t2 join t3 on t2.id = t3.id) on t1.id = t2.id
         whereas with cross join:
            t1 cross join t2 join t3 on t2.id = t3.id
         it is equivalent to:
            (t1 cross join t2) join t3 on t2.id = t3.id
         *)
      both (lspaces cross_p) (lspaces left)
    in
    let chained_join = noncross_join <|> cross_join in
    chain_joins
      (lift2
         (fun left (join_constraint, right) -> Join { left; right; join_constraint })
         (lspaces left)
         chained_join)
      chained_join)
;;

let datasource_p = join_p <|> parens_p join_p <|> table_p
let assert_ok_ds s expected = assert_ok show_datasource datasource_p s expected

let%test _ =
  assert_ok_ds
    "t1 join t2 on t1.id = t2.id"
    (Join
       { left = Table "t1"
       ; right = Table "t2"
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "(t1 join t2 on t1.id = t2.id)"
    (Join
       { left = Table "t1"
       ; right = Table "t2"
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join t2"
    (Join { left = Table "t1"; right = Table "t2"; join_constraint = Cross })
;;

let%test _ =
  assert_ok_ds
    "(t1 cross join t2)"
    (Join { left = Table "t1"; right = Table "t2"; join_constraint = Cross })
;;

let%test _ =
  assert_ok_ds
    "t1 join t2 join t3 on t2.id = t3.id on t1.id = t2.id"
    (Join
       { left = Table "t1"
       ; right =
           Join
             { left = Table "t2"
             ; right = Table "t3"
             ; join_constraint =
                 Inner (Equal (Arithm (Column "t2.id"), Arithm (Column "t3.id")))
             }
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 join (t2 join t3 on t2.id = t3.id) on t1.id = t2.id"
    (Join
       { left = Table "t1"
       ; right =
           Join
             { left = Table "t2"
             ; right = Table "t3"
             ; join_constraint =
                 Inner (Equal (Arithm (Column "t2.id"), Arithm (Column "t3.id")))
             }
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 join t2 on t1.id = t2.id join t3 on t1.id = t3.id"
    (Join
       { left =
           Join
             { left = Table "t1"
             ; right = Table "t2"
             ; join_constraint =
                 Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
             }
       ; right = Table "t3"
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t3.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 join t2 on t1.id = t2.id join t3 on t1.id = t3.id right join t4 on t2.id=t4.id"
    (Join
       { left =
           Join
             { left =
                 Join
                   { left = Table "t1"
                   ; right = Table "t2"
                   ; join_constraint =
                       Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
                   }
             ; right = Table "t3"
             ; join_constraint =
                 Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t3.id")))
             }
       ; right = Table "t4"
       ; join_constraint =
           Right (Equal (Arithm (Column "t2.id"), Arithm (Column "t4.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 join (t2 cross join t3) on t1.id = t2.id"
    (Join
       { left = Table "t1"
       ; right = Join { left = Table "t2"; right = Table "t3"; join_constraint = Cross }
       ; join_constraint =
           Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t2.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join (t2 left join t3 on t3.id = t2.id)"
    (Join
       { left = Table "t1"
       ; right =
           Join
             { left = Table "t2"
             ; right = Table "t3"
             ; join_constraint =
                 Left (Equal (Arithm (Column "t3.id"), Arithm (Column "t2.id")))
             }
       ; join_constraint = Cross
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join t2 left join t3 on t1.id = t3.id"
    (Join
       { left = Join { left = Table "t1"; right = Table "t2"; join_constraint = Cross }
       ; right = Table "t3"
       ; join_constraint = Left (Equal (Arithm (Column "t1.id"), Arithm (Column "t3.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join t2 cross join t3"
    (Join
       { left = Join { left = Table "t1"; right = Table "t2"; join_constraint = Cross }
       ; right = Table "t3"
       ; join_constraint = Cross
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join t2 inner join t3 on t1.id = t3.id cross join t4"
    (Join
       { left =
           Join
             { left =
                 Join { left = Table "t1"; right = Table "t2"; join_constraint = Cross }
             ; right = Table "t3"
             ; join_constraint =
                 Inner (Equal (Arithm (Column "t1.id"), Arithm (Column "t3.id")))
             }
       ; right = Table "t4"
       ; join_constraint = Cross
       })
;;

let%test _ =
  assert_ok_ds
    "t1 cross join (t2 inner join t3 on t2.id = t3.id) cross join t4"
    (Join
       { left =
           Join
             { left = Table "t1"
             ; right =
                 Join
                   { left = Table "t2"
                   ; right = Table "t3"
                   ; join_constraint =
                       Inner (Equal (Arithm (Column "t2.id"), Arithm (Column "t3.id")))
                   }
             ; join_constraint = Cross
             }
       ; right = Table "t4"
       ; join_constraint = Cross
       })
;;

let%test _ =
  assert_ok_ds
    "t1 left join t2 cross join t3 on t1.id >= t3.id"
    (Join
       { left = Table "t1"
       ; right = Join { left = Table "t2"; right = Table "t3"; join_constraint = Cross }
       ; join_constraint =
           Left (GreaterOrEq (Arithm (Column "t1.id"), Arithm (Column "t3.id")))
       })
;;

let%test _ =
  assert_ok_ds
    "t1 right join t2 on t1.a < 2 + t2.a OR t1.value = 10"
    (Join
       { left = Table "t1"
       ; right = Table "t2"
       ; join_constraint =
           Right
             (OrPred
                ( Less (Arithm (Column "t1.a"), Arithm (Plus (Int 2, Column "t2.a")))
                , Equal (Arithm (Column "t1.value"), Arithm (Int 10)) ))
       })
;;

let%test _ = assert_ok_ds "main.t1" (Table "main.t1")
let%test _ = assert_ok_ds "t1" (Table "t1")
let%test _ = assert_error datasource_p "(t1)"
let%test _ = assert_error datasource_p "t1 cross join t2 on t1.id = t2.id"
let%test _ = assert_error datasource_p "t1 join t2 on t1.id + t2.id"

let%test _ =
  assert_error datasource_p "(t1 join t2) join t3 on t2.id = t3.id on t1.id = t2.id"
;;

(*** SQL statement parsers ***)

let comma_p = spaces (char ',')
let insert_word_p = string_ci "INSERT"
let select_word_p = string_ci "SELECT"
let from_word_p = string_ci "FROM"
let where_word_p = string_ci "WHERE"
let orderby_word_p = string_ci "ORDER" *> satisfy is_space *> lspaces (string_ci "BY")
let clause wordp clausep = lspaces wordp *> clausep

let optional_clause wordp clausep =
  option None (lspaces wordp *> clausep >>| fun clause -> Some clause)
;;

let projection_p = clause select_word_p (sep_by1 comma_p proj_item_p)
let from_p = clause from_word_p (sep_by1 comma_p datasource_p)
let where_p = optional_clause where_word_p predicate_p
let orderby_p = optional_clause orderby_word_p (sep_by1 comma_p orderby_clause_p)

let select_p =
  lift4
    (fun projection from where orderby -> Select { projection; from; where; orderby })
    projection_p
    from_p
    where_p
    orderby_p
;;

let insert_p = insert_word_p *> fail "Insert statements are not supported yet"
let statement_p = spaces (select_p <|> insert_p)
let assert_ok_sql s expected = assert_ok show_statement statement_p s expected

let%test _ =
  assert_ok_sql
    "select * from t"
    (Select { projection = [ Star ]; from = [ Table "t" ]; where = None; orderby = None })
;;

type error = string

let parse = parse_string statement_p
