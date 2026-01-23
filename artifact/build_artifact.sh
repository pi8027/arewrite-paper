#!/usr/bin/env bash

echo_exec() { echo "+ $@" ; "$@" ; }

git clone git@gitlab.com:SamuelArsac/graph-rewriting.git graph-rewriting \
  -b arewrite

DIR=itp26-submission-87

mkdir $DIR

echo_exec cp README.md $DIR/README.md
echo_exec cp monoid.v $DIR/monoid.v
echo_exec cp -r graph-rewriting $DIR/graph-rewriting
echo_exec rm -rf $DIR/graph-rewriting/.git* $DIR/graph-rewriting/README.md

tar czvf $DIR.tar.gz $DIR

rm -rf graph-rewriting $DIR
