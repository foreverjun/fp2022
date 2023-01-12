Copyright 2021-2022, Michael Polyntsov and contributors
SPDX-License-Identifier: CC0-1.0

  $ ../../REPL.exe -make-db-from ./testdb

  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1
  > EOF
  Connected to testdb
  t1.A t1.B
  1    abc
  2    keks
  3    something
  4    again
  5    kakadu
  6    mmmonad

  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t2
  > EOF
  Connected to testdb
  t2.B     t2.A
  naoborot 1
  string   2
  a        4
  b        3
  c        5
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select a, *, 1+1, (2+2=4)=(2*2=4) as weird, (2+2)=(4) as parens
  > from t1 where b > 'a'
  > EOF
  Connected to testdb
  a t1.A t1.B      ?column? weird parens
  1 1    abc       2        true  true
  2 2    keks      2        true  true
  3 3    something 2        true  true
  4 4    again     2        true  true
  5 5    kakadu    2        true  true
  6 6    mmmonad   2        true  true
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1, t2
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A
  1    abc       naoborot 1
  1    abc       string   2
  1    abc       a        4
  1    abc       b        3
  1    abc       c        5
  2    keks      naoborot 1
  2    keks      string   2
  2    keks      a        4
  2    keks      b        3
  2    keks      c        5
  3    something naoborot 1
  3    something string   2
  3    something a        4
  3    something b        3
  3    something c        5
  4    again     naoborot 1
  4    again     string   2
  4    again     a        4
  4    again     b        3
  4    again     c        5
  5    kakadu    naoborot 1
  5    kakadu    string   2
  5    kakadu    a        4
  5    kakadu    b        3
  5    kakadu    c        5
  6    mmmonad   naoborot 1
  6    mmmonad   string   2
  6    mmmonad   a        4
  6    mmmonad   b        3
  6    mmmonad   c        5
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select t1.a, t2.a, t1.b, t2.b from t1 join t2 on t1.a = t2.a
  > EOF
  Connected to testdb
  t1.a t2.a t1.b      t2.b
  1    1    abc       naoborot
  2    2    keks      string
  3    3    something b
  4    4    again     a
  5    5    kakadu    c
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select t1.a, t2.a, t1.b, t2.b from t1, t2 where t1.a = t2.a
  > EOF
  Connected to testdb
  t1.a t2.a t1.b      t2.b
  1    1    abc       naoborot
  2    2    keks      string
  3    3    something b
  4    4    again     a
  5    5    kakadu    c
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select t1.a, t2.a, t1.b, t2.b from t1, t2
  > where t1.a = t2.a AND (t1.b = 'abc' OR t2.b = 'c')
  > EOF
  Connected to testdb
  t1.a t2.a t1.b   t2.b
  1    1    abc    naoborot
  5    5    kakadu c

  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select t1.a, t2.a, t1.b, t2.b from t1, t2
  > where t1.a = t2.a AND t1.b = 'abc' OR t2.b = 'c'
  > EOF
  Connected to testdb
  t1.a t2.a t1.b      t2.b
  1    1    abc       naoborot
  1    5    abc       c
  2    5    keks      c
  3    5    something c
  4    5    again     c
  5    5    kakadu    c
  6    5    mmmonad   c
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1, t2 join t3 on t2.a = t3.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A t3.a t3.b t3.c
  1    abc       naoborot 1    1    101  oa
  1    abc       string   2    2    e    notdouble
  1    abc       a        4    4    c    double
  1    abc       b        3    3    d    float
  1    abc       c        5    5    b    int
  2    keks      naoborot 1    1    101  oa
  2    keks      string   2    2    e    notdouble
  2    keks      a        4    4    c    double
  2    keks      b        3    3    d    float
  2    keks      c        5    5    b    int
  3    something naoborot 1    1    101  oa
  3    something string   2    2    e    notdouble
  3    something a        4    4    c    double
  3    something b        3    3    d    float
  3    something c        5    5    b    int
  4    again     naoborot 1    1    101  oa
  4    again     string   2    2    e    notdouble
  4    again     a        4    4    c    double
  4    again     b        3    3    d    float
  4    again     c        5    5    b    int
  5    kakadu    naoborot 1    1    101  oa
  5    kakadu    string   2    2    e    notdouble
  5    kakadu    a        4    4    c    double
  5    kakadu    b        3    3    d    float
  5    kakadu    c        5    5    b    int
  6    mmmonad   naoborot 1    1    101  oa
  6    mmmonad   string   2    2    e    notdouble
  6    mmmonad   a        4    4    c    double
  6    mmmonad   b        3    3    d    float
  6    mmmonad   c        5    5    b    int
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1, t2 join t3 on t2.a = t3.a
  > where t1.a = t2.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A t3.a t3.b t3.c
  1    abc       naoborot 1    1    101  oa
  2    keks      string   2    2    e    notdouble
  3    something b        3    3    d    float
  4    again     a        4    4    c    double
  5    kakadu    c        5    5    b    int
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1, t2 join t3 on t2.a = t3.a
  > where t1.a = t2.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A t3.a t3.b t3.c
  1    abc       naoborot 1    1    101  oa
  2    keks      string   2    2    e    notdouble
  3    something b        3    3    d    float
  4    again     a        4    4    c    double
  5    kakadu    c        5    5    b    int
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1, t2 join t3 on t2.a = t3.a
  > where t1.a = t2.a AND t3.c != 'int'
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A t3.a t3.b t3.c
  1    abc       naoborot 1    1    101  oa
  2    keks      string   2    2    e    notdouble
  3    something b        3    3    d    float
  4    again     a        4    4    c    double
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1 CROSS JOIN t2
  > where t1.a = t2.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B     t2.A
  1    abc       naoborot 1
  2    keks      string   2
  3    something b        3
  4    again     a        4
  5    kakadu    c        5
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1 CROSS JOIN (t2 join t3 on t2.a = t3.a and t3.b > 'b')
  > where t1.a = t2.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B   t2.A t3.a t3.b t3.c
  2    keks      string 2    2    e    notdouble
  3    something b      3    3    d    float
  4    again     a      4    4    c    double
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1 join t2 on t1.a = t2.a join t3 on t1.a = t3.a and t3.b > 'b'
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B   t2.A t3.a t3.b t3.c
  2    keks      string 2    2    e    notdouble
  3    something b      3    3    d    float
  4    again     a      4    4    c    double
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1 join (t2 join t3 on t2.b = t3.b) on t1.a = t2.a
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B t2.A t3.a t3.b t3.c
  3    something b    3    5    b    int
  4    again     a    4    101  a    long
  5    kakadu    c    5    4    c    double
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t1 join (t2 join t3 on t2.b = t3.b) on t1.a = t2.a
  > where t1.a != 4
  > EOF
  Connected to testdb
  t1.A t1.B      t2.B t2.A t3.a t3.b t3.c
  3    something b    3    5    b    int
  5    kakadu    c    5    4    c    double
 
  $ ../../REPL.exe -db testdb -no-repl <<EOF
  > select * from t3 where a = 101
  > EOF
  Connected to testdb
  t3.a t3.b    t3.c
  101  a       long
  101  nomatch random
 
