#!/bin/bash
# Copyright 2021-2022, Michael Polyntsov and contributors
# SPDX-License-Identifier: CC0-1.0

function print_usage() {
cat << EOF
Usage: ./gen_test_data.sh <data_size> <mysql_user> <mysql_pass>

EOF
}

if [ $# != 3 ];then
    print_usage
    exit 1
fi

gendir="ssbgen"
testdb="testdb"
headers="testdb_headers"
data_size=$1
mysql_user=$2
mysql_pass=$3

[ ! -d $gendir ] &&
    git clone git@github.com:polyntsov/SQL_Storage_Benchmark.git ssbgen --quiet

[ ! -d $headers ] &&
    { echo "Unable to found directory with headers, exiting" ; exit 1; }

rootdir=$(pwd)

cd ssbgen
[ -d $testdb ] && rm -rf $testdb

mkdir $testdb
python3 setup3sb.py -s mysql -d $data_size -ut 5 -D ssbtest -H localhost \
    -l $mysql_user -p $mysql_pass -t ./$testdb/ -k &&

for tbl in $(ls $testdb)
do
    new_name=$(echo "$tbl" | grep -o "user_[0-9]")
    if [ ! -z "$new_name" ];then
        mv ./$testdb/$tbl ./$testdb/$new_name.csv
    fi
done

cd $rootdir
cp ./$headers/* ./$gendir/$testdb/
