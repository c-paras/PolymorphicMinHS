#!/bin/sh

if test -n "$1"
then
	file="/tmp/foo_$$.mhs"
	echo "$1" > $file
else
	file="foo.mhs"
	if ! test -e $file
	then
		echo "Usage: $0 \"<program>\"" >&2
		exit 1
	fi
fi

./dist/build/minhs-2/minhs-2 --dump parser-raw $file
./dist/build/minhs-2/minhs-2 --dump parser $file
./dist/build/minhs-2/minhs-2 --dump type-infer $file
