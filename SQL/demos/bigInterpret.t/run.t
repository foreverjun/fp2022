Copyright 2021-2022, Michael Polyntsov and contributors
SPDX-License-Identifier: CC0-1.0

  $ USER="tester"
  $ PASS="testerpass"

This will clone the repo on each `dune test` invocation,
but I have now idea how to fix it
  $ ./gen_test_data.sh 10MB $USER $PASS > /dev/null
  $ ../../REPL.exe -make-db-from ./ssbgen/testdb

  $ ./test.sh $USER $PASS <<EOF
  > select * from user_1 where custid = 1
  > EOF
  Connected to testdb

  $ ./test.sh $USER $PASS <<EOF
  > select * from user_1, user_2 where user_1.custid = user_2.custid
  > EOF
  Connected to testdb

  $ ./test.sh $USER $PASS <<EOF
  > select * from user_1, user_2
  > where user_1.custid = user_2.custid AND user_1.custid = 2 * user_2.custid
  > EOF
  Connected to testdb

  $ ./test.sh $USER $PASS <<EOF
  > select * from user_1, user_2 join user_3 on user_2.custid = user_3.custid
  > where user_1.custid = user_2.custid AND user_1.custid = 2 * user_2.custid
  > EOF
  Connected to testdb

  $ ./test.sh $USER $PASS <<EOF
  > select *
  > from user_1 join user_2 on user_1.custid = user_2.custid
  >      join user_3 on user_1.custid = user_3.custid
  > EOF
  Connected to testdb

  $ ./test.sh $USER $PASS <<EOF
  > select user_1.custid
  > from (user_1 join user_4 on user_1.custid = user_4.custid)
  >      join user_2 on user_1.custid = user_2.custid
  >      join user_3 on user_1.custid = user_3.custid
  Connected to testdb
