### An implementaion of mini SQL

This is a homework for functional programming course.

Author: Michael Polyntsov, arno9148@gmail.com

Usage:
...

To turn on MySQL verification tests on [SSB](https://github.com/polyntsov/SQL_Storage_Benchmark) do
the following steps:
1. Firstly create a user in MySQL and specify it's credentials in `USER` and `PASS` variables in
`bigInterpret.t/run.t` file.
2. Then run `dune test --profile=mysql`.

Implemented language:

SQL-99 syntax:
SELECT [ DISTINCT | ALL ]
{Column expression [ AS name ]} [ ,... ] | *
FROM <Table reference> [ {,<Table reference>} ... ]
[ WHERE search condition ]
[ GROUP BY Columns [ HAVING condition ] ]
[ORDER BY {col\_name | expr | position} [ASC | DESC],...]
[LIMIT {[offset,] row\_count | row\_count OFFSET offset}]
[PROCEDURE procedure\_name(argument\_list)]
[INTO OUTFILE 'file\_name' export\_options |
 INTO DUMPFILE 'file\_name' |
 INTO var\_name [, var\_name]]
[FOR UPDATE | LOCK IN SHARE MODE]

We support only a subset of it (the mini SQL):
SELECT
{Column expression [ AS name ]} [ ,... ] | *
FROM <Table reference> [ {,<Table reference>} ... ]
[ WHERE search condition ]
[ORDER BY {col\_name | expr} [ASC | DESC],...]

Table reference can be either a table name (without alias)
represented as a string of english letters or a join clause.
Join clause:
  <Table reference> [JOIN TYPE] JOIN <Table reference> ON <join condition>
OR:
  <Table reference> CROSS JOIN <Table reference>

Only INNER and CROSS joins are interpreted at the moment, however all other types
are parsed and generated. All kinds of nested joins and chained joins are supported (check the
tests to see the examples). OrderBy is only supported on the parser level.

Features done (append only):

- Parser of mini SQL
- Creation of databases from .csv files
- Query generation from AST
- Queries are generated with the following optimizations:
  - Predicates pushdown
  - Some kinds of predicates in filtration are transformed to joins
- Query interpretation
- Parser inline tests
- Parser cram tests
- Query generation cram tests
- Query interpretation (except orderby and left/right joins cause nulls are needed for them)
- Simple REPL (takes a query, prints its plan and result)
- Interpreter default cram tests
- Interpreter cram tests using verification by MySQL
- Small benchmarking done:
  It takes >15min to 1.5GB tables, didn't wait untill the end (because lists are a really bad
  choice to represent the relation, arrays won't help much too I think).
  It takes ~40 secs to join four 100MB tables.


Features in progress (and TODOs):

- Write a HOWTO/USAGE
- Improve error handling (especially in the catalog)
