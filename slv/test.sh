#!/bin/sh

fail=0

runt() {
	t=$1
	exp=$2
	./dpll < $t > /dev/null
	ret=$?
	if [ $ret -ne $exp ]
	then
		echo "test $t failed"
		let fail++
	fi
}

for t in test/*.u
do
	runt $t 1
done
for t in test/*.s
do
	runt $t 0
done

if [ $fail -eq 0 ]
then
	echo "all is good"
else
	echo "$fail failures"
fi
exit $fail
