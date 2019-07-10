#!/bin/bash

# This script packages up this repository for (hopefully) anonymous submission.
DIR=oxide-popl20
REV=`git rev-parse --short HEAD`
rm -rf $DIR

mkdir -p $DIR
git clone tests $DIR/tests
pushd $DIR/tests
../../anonymizer.sh
git remote remove origin
rm -rf .git/logs/*
popd

cp -r oxide $DIR
rm $DIR/oxide/.merlin

cp -r reducer $DIR
sed -i "" "s/Aaron Weiss <awe@pdgn\.co>/Anonymous Aardvaark <aardvark@email.com>/" $DIR/reducer/Cargo.toml
sed -i "" "s/Daniel Patterson <dbp@dbpmail\.net>/Anonymous Penguin <penguin@email.com>/" $DIR/reducer/Cargo.toml
rm -rf reducer/target

cp -r runner $DIR
rm $DIR/runner/.merlin

cp README-submission.md $DIR/README.md

cp dune-project $DIR
cp eval.sh $DIR

zip -r $DIR-$REV.zip $DIR/*
rm -rf $DIR
