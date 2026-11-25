#!/bin/sh
# usage: ./run_gen.sh t n [timeout_seconds]     e.g. ./run_gen.sh 2 3   then ./run_gen.sh 3 5   then ./run_gen.sh 5 10 3600
t=$1; n=$2; T=${3:-600}; mkdir -p gen
t1=$((t-1))
go() { name=$1; shift; python3 gen_pv.py "$@" > gen/${name}_${t}of${n}.pv; echo "=== ${name} ${t}-of-${n}"; timeout $T proverif gen/${name}_${t}of${n}.pv | grep -E "^RESULT|rror" || echo "(no result: timeout or error)"; }
go secrecy_unauth    secrecy     $t $n $t1      # expect: not attacker(s) true
go secrecy_auth      secrecy     $t $n $t       # expect: not attacker(s) false (sanity)
go soundness         soundness   $t $n          # expect: Accept ==> Dealt true ; not Accept false
go consistency       consistency $t $n          # expect: true / cannot be proved / false
go equiv_unauth      equiv       $t $n $t1      # optional, expect: Observational equivalence true
