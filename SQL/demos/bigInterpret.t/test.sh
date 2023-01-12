#!/bin/bash
# Copyright 2021-2022, Michael Polyntsov and contributors
# SPDX-License-Identifier: CC0-1.0

user=$1
pass=$2
actual="actual"
expected="expected"

# read query from stdin
query="$(cat -)"

#echo "Running '$query'"

rm -f $actual
rm -f $expected

# run our interpreter
../../REPL.exe -db testdb -no-repl -to-out-file $actual <<< "$query"

# run the same query in mysql

# just redirect output to the file chopping the header,
# because I don't want to mess with user permissions
mysql -u $user --password=$pass -D ssbtest -e "$query" | tr '\t' ',' > $expected &&
  sed -i '1d' $expected

# diff the results
diff actual expected
