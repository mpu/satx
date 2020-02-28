#!/bin/bash

for h in `seq 100`
do
	for p in `seq 100`
	do
		if [ $h -lt $p ]
		then
			out="php/php_${h}_${p}.uns"
		else
			out="php/php_${h}_${p}.sat"
		fi
		echo "$h holes; $p pigeons"
		./a.out $h $p > $out
	done
done
