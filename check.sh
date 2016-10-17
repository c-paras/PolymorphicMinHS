#!/bin/sh

cabal build > /dev/null || exit 1
echo

if test -n "$1"
then
	file="/tmp/foo_$$.mhs"
	echo "$1" > $file
	remove=$file
else
	file="foo.mhs"
	if ! test -e $file
	then
		echo "Usage: $0 \"<program>\"" >&2
		exit 1
	fi
fi

./dist/build/minhs-2/minhs-2 --dump parser-raw $file
echo
./dist/build/minhs-2/minhs-2 --dump parser $file
echo
./dist/build/minhs-2/minhs-2 --dump type-infer $file
rm -f $remove
