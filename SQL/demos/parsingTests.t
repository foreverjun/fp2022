Copyright 2021-2022, Kakadu, Michael Polyntsov and contributors
SPDX-License-Identifier: CC0-1.0

Tests about parsing go here. It's expected that programs parse something and
output a parse tree.
For example, where your test correctness of AST it's recommend to put both
input and output into this file. In this case it will be easier to check that
answer is correct

  $ ./demoParse.exe <<-EOF
  > select * from t
  Select {projection = [Star]; from = [(Table "t")]; where = None;
    orderby = None}

  $ ./demoParse.exe <<-EOF
  > select * , * from t
  Select {projection = [Star; Star]; from = [(Table "t")]; where = None;
    orderby = None}

  $ ./demoParse.exe <<-EOF
  > select * , * , A , B , 2 + 2 from t
  Select {
    projection =
    [Star; Star; (ProjAtomItem ((Column "A"), None));
      (ProjAtomItem ((Column "B"), None));
      (ProjAtomItem ((Plus ((Int 2), (Int 2))), None))];
    from = [(Table "t")]; where = None; orderby = None}
 

  $ ./demoParse.exe <<-EOF
  > select lo_extendedprice as price, lo_discount as discount
  > from lineorder, date
  > where lo_orderdate = d_datekey
  > and d_year = 1993
  > and lo_discount > 1 and lo_discound < 3
  > and lo_quantity < 25
  Select {
    projection =
    [(ProjAtomItem ((Column "lo_extendedprice"), (Some "price")));
      (ProjAtomItem ((Column "lo_discount"), (Some "discount")))];
    from = [(Table "lineorder"); (Table "date")];
    where =
    (Some (AndPred (
             (AndPred (
                (AndPred (
                   (AndPred (
                      (Equal ((Column "lo_orderdate"), (Column "d_datekey"))),
                      (Equal ((Column "d_year"), (Int 1993))))),
                   (Greater ((Column "lo_discount"), (Int 1))))),
                (Less ((Column "lo_discound"), (Int 3))))),
             (Less ((Column "lo_quantity"), (Int 25))))));
    orderby = None}

  $ ./demoParse.exe <<-EOF
  > select lo_revenue, d_year, p_brand1
  > from lineorder, date, part, supplier
  > where lo_orderdate = d_datekey
  > and lo_partkey = p_partkey
  > and lo_suppkey = s_suppkey
  > and p_brand1 >
  >   'MFGR#2221'
  > and p_brand1 < 'MFGR#2228'
  > and s_region = 'ASIA'
  > order by d_year, p_brand1
  Select {
    projection =
    [(ProjAtomItem ((Column "lo_revenue"), None));
      (ProjAtomItem ((Column "d_year"), None));
      (ProjAtomItem ((Column "p_brand1"), None))];
    from =
    [(Table "lineorder"); (Table "date"); (Table "part"); (Table "supplier")];
    where =
    (Some (AndPred (
             (AndPred (
                (AndPred (
                   (AndPred (
                      (AndPred (
                         (Equal ((Column "lo_orderdate"), (Column "d_datekey")
                            )),
                         (Equal ((Column "lo_partkey"), (Column "p_partkey")))
                         )),
                      (Equal ((Column "lo_suppkey"), (Column "s_suppkey"))))),
                   (Greater ((Column "p_brand1"), (String "MFGR#2221"))))),
                (Less ((Column "p_brand1"), (String "MFGR#2228"))))),
             (Equal ((Column "s_region"), (String "ASIA"))))));
    orderby = (Some [(Asc (Column "d_year")); (Asc (Column "p_brand1"))])}

  $ ./demoParse.exe <<-EOF
  > select c_city, s_city, d_year, lo_revenue as revenue
  > from customer, lineorder, supplier, date
  > where lo_custkey = c_custkey
  > and lo_suppkey = s_suppkey
  > and lo_orderdate = d_datekey
  > and (c_city='UNITED KI1' or
  >      c_city='UNITED KI5')
  > and (s_city='UNITED KI1' or
  >      s_city='UNITED KI5')
  > and d_year >= 1992 and d_year <= 1997
  > order by d_year asc, revenue desc
  Select {
    projection =
    [(ProjAtomItem ((Column "c_city"), None));
      (ProjAtomItem ((Column "s_city"), None));
      (ProjAtomItem ((Column "d_year"), None));
      (ProjAtomItem ((Column "lo_revenue"), (Some "revenue")))];
    from =
    [(Table "customer"); (Table "lineorder"); (Table "supplier");
      (Table "date")];
    where =
    (Some (AndPred (
             (AndPred (
                (AndPred (
                   (AndPred (
                      (AndPred (
                         (AndPred (
                            (Equal ((Column "lo_custkey"), (Column "c_custkey")
                               )),
                            (Equal ((Column "lo_suppkey"), (Column "s_suppkey")
                               ))
                            )),
                         (Equal ((Column "lo_orderdate"), (Column "d_datekey")
                            ))
                         )),
                      (OrPred (
                         (Equal ((Column "c_city"), (String "UNITED KI1"))),
                         (Equal ((Column "c_city"), (String "UNITED KI5")))))
                      )),
                   (OrPred ((Equal ((Column "s_city"), (String "UNITED KI1"))),
                      (Equal ((Column "s_city"), (String "UNITED KI5")))))
                   )),
                (GreaterOrEq ((Column "d_year"), (Int 1992))))),
             (LessOrEq ((Column "d_year"), (Int 1997))))));
    orderby = (Some [(Asc (Column "d_year")); (Desc (Column "revenue"))])}

  $ ./demoParse.exe <<-EOF
  > SELECT t1.id, t2.a - t3.b, 2 + 2, *, *
  > FROM table JOIN (t1 LEFT JOIN
  >                  (t2 RIGHT JOIN t3 ON t2.b = t3.b CROSS JOIN
  >                   t5 CROSS JOIN
  >                   t6 INNER JOIN t7 ON t6.A = t7.A CROSS JOIN (t8 JOIN t7 ON t8.a < t7.a))
  >                   ON t1.a = t2.a)
  >                 ON table.A = t2.a
  > ORDER BY t1.a + t2.a + t3.a + t3.a desc, table.b * 666
  Select {
    projection =
    [(ProjAtomItem ((Column "t1.id"), None));
      (ProjAtomItem ((Minus ((Column "t2.a"), (Column "t3.b"))), None));
      (ProjAtomItem ((Plus ((Int 2), (Int 2))), None)); Star; Star];
    from =
    [Join {left = (Table "table");
       right =
       Join {left = (Table "t1");
         right =
         Join {
           left =
           Join {
             left =
             Join {
               left =
               Join {
                 left =
                 Join {left = (Table "t2"); right = (Table "t3");
                   join_constraint =
                   (Right (Equal ((Column "t2.b"), (Column "t3.b"))))};
                 right = (Table "t5"); join_constraint = Cross};
               right = (Table "t6"); join_constraint = Cross};
             right = (Table "t7");
             join_constraint =
             (Inner (Equal ((Column "t6.A"), (Column "t7.A"))))};
           right =
           Join {left = (Table "t8"); right = (Table "t7");
             join_constraint =
             (Inner (Less ((Column "t8.a"), (Column "t7.a"))))};
           join_constraint = Cross};
         join_constraint = (Left (Equal ((Column "t1.a"), (Column "t2.a"))))};
       join_constraint = (Inner (Equal ((Column "table.A"), (Column "t2.a"))))}
      ];
    where = None;
    orderby =
    (Some [(Desc
              (Plus ((Plus ((Plus ((Column "t1.a"), (Column "t2.a"))), (Column "t3.a"))),
     (Column "t3.a"))));
            (Asc (Mult ((Column "table.b"), (Int 666))))])}

  $ ./demoParse.exe <<-EOF
  > SELECT *, a < b, 1 + 1, 'abc' AS jon, id=id,
  >        (id=id), (a + c) = (b - d), a+c=b-d,
  >        (a < c) < (b < d),
  >        ((id = id) = (id=id)) = ((id = id) = (id=id)),
  >        id = id OR id = id OR id = id,
  >        ( ( (a=a) =(a = a)) = ( (a=a)=(a=a) ) OR 1=1 ) = (a=a)
  > FROM t1
  Select {
    projection =
    [Star; (ProjAtomItem ((Less ((Column "a"), (Column "b"))), None));
      (ProjAtomItem ((Plus ((Int 1), (Int 1))), None));
      (ProjAtomItem ((String "abc"), (Some "jon")));
      (ProjAtomItem ((Equal ((Column "id"), (Column "id"))), None));
      (ProjAtomItem ((Equal ((Column "id"), (Column "id"))), None));
      (ProjAtomItem (
         (Equal ((Plus ((Column "a"), (Column "c"))),
     (Minus ((Column "b"), (Column "d"))))),
         None));
      (ProjAtomItem (
         (Equal ((Plus ((Column "a"), (Column "c"))),
     (Minus ((Column "b"), (Column "d"))))),
         None));
      (ProjAtomItem (
         (PredLess ((Less ((Column "a"), (Column "c"))),
     (Less ((Column "b"), (Column "d"))))),
         None));
      (ProjAtomItem (
         (PredEqual (
     (PredEqual ((Equal ((Column "id"), (Column "id"))),
        (Equal ((Column "id"), (Column "id"))))),
     (PredEqual ((Equal ((Column "id"), (Column "id"))),
        (Equal ((Column "id"), (Column "id")))))
     )),
         None));
      (ProjAtomItem (
         (OrPred (
     (OrPred ((Equal ((Column "id"), (Column "id"))),
        (Equal ((Column "id"), (Column "id"))))),
     (Equal ((Column "id"), (Column "id"))))),
         None));
      (ProjAtomItem (
         (PredEqual (
     (OrPred (
        (PredEqual (
           (PredEqual ((Equal ((Column "a"), (Column "a"))),
              (Equal ((Column "a"), (Column "a"))))),
           (PredEqual ((Equal ((Column "a"), (Column "a"))),
              (Equal ((Column "a"), (Column "a")))))
           )),
        (Equal ((Int 1), (Int 1))))),
     (Equal ((Column "a"), (Column "a"))))),
         None))
      ];
    from = [(Table "t1")]; where = None; orderby = None}

  $ ./demoParse.exe <<-EOF
  > select user_1.custid
  > from
  > (user_1 join user_4 on user_1.custid = user_4.custid)
  > join user_2 on user_1.custid = user_2.custid
  > join user_3 on user_1.custid = user_3.custid
  Select {projection = [(ProjAtomItem ((Column "user_1.custid"), None))];
    from =
    [Join {
       left =
       Join {
         left =
         Join {left = (Table "user_1"); right = (Table "user_4");
           join_constraint =
           (Inner (Equal ((Column "user_1.custid"), (Column "user_4.custid"))))};
         right = (Table "user_2");
         join_constraint =
         (Inner (Equal ((Column "user_1.custid"), (Column "user_2.custid"))))};
       right = (Table "user_3");
       join_constraint =
       (Inner (Equal ((Column "user_1.custid"), (Column "user_3.custid"))))}
      ];
    where = None; orderby = None}

  $ ./demoParse.exe <<-EOF
  > select user_1.custid
  > from
  > (user_1 join user_4 on user_1.custid = user_4.custid)
  > cross join user_3
  Select {projection = [(ProjAtomItem ((Column "user_1.custid"), None))];
    from =
    [Join {
       left =
       Join {left = (Table "user_1"); right = (Table "user_4");
         join_constraint =
         (Inner (Equal ((Column "user_1.custid"), (Column "user_4.custid"))))};
       right = (Table "user_3"); join_constraint = Cross}
      ];
    where = None; orderby = None}
