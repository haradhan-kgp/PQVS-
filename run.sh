#!/bin/sh
# Hand-written 2-of-3 models. Requires ProVerif >= 2.04.   usage: ./run.sh
mkdir -p out
printf 'query attacker(s).\n' > out/q_secrecy.pv
printf 'query x: elem; event(Accept(x)) ==> event(Dealt(x)).\nquery x: elem; event(Accept(x)).\n' > out/q_sound.pv
: > out/q_none.pv
run() { name=$1; shift; cat "$@" > out/$name.pv; echo "=== $name"; proverif out/$name.pv | grep -E "^RESULT|rror"; }
mk() { name=$1; q=$2; proc=$3; printf 'process %s\n' "$proc" > out/$name.proc; run $name decl.pv honest.pv out/$q.pv out/$name.proc; }
mk secrecy_P1only q_secrecy "Deal(s,true,false,false)"
mk secrecy_P2only q_secrecy "Deal(s,false,true,false)"
mk secrecy_P3only q_secrecy "Deal(s,false,false,true)"
mk leak_P1P2      q_secrecy "Deal(s,true,true,false)"
mk soundness      q_sound   "DealRec(s)"
mk equiv_P1only   q_none    "Deal(choice[s0,s1],true,false,false)"
mk equiv_P2only   q_none    "Deal(choice[s0,s1],false,true,false)"
mk equiv_P3only   q_none    "Deal(choice[s0,s1],false,false,true)"
run consistency decl.pv consistency.pv
