#!/usr/bin/env python3
"""Generate ProVerif models of PQVS for a t-out-of-n minimal-set DNF.
usage: gen_pv.py MODE t n [k]      (writes the model to stdout)
  MODE secrecy     : honest dealer, parties 1..k corrupted (k=t-1 -> expect 'not attacker(s)' true; k=t -> false)
  MODE equiv       : same, with choice[s0,s1] (diff-equivalence), k = t-1 by default
  MODE soundness   : honest dealer, ONE clause, parties 2..t corrupted & supply their slots; party 1 honest
  MODE consistency : malicious dealer, all clauses (derived commitments) + earlier design (independent commitments)
Clause j = AND of parties P_1<...<P_t; coordinates v_{j,1..t-1} fresh; slot i<t gets v_{j,i}, last slot gets
s - v_{j,1} - ... - v_{j,t-1}.  Reconstruction: add(a_1, add(a_2, ... add(a_{t-1}, last))) = s by add(x,sub(y,x))=y."""
import sys, itertools

DECL = """free c: channel.
type elem.
type cm.
fun com(elem, elem): cm.
fun add(elem, elem): elem.
fun sub(elem, elem): elem.
fun csub(cm, cm): cm [private].
equation forall x: elem, y: elem; add(x, sub(y, x)) = y.
equation forall x1: elem, y1: elem, x2: elem, y2: elem;
  csub(com(x1, y1), com(x2, y2)) = com(sub(x1, x2), sub(y1, y2)).
event Dealt(elem).
event Accept(elem).
event RecDone(cm, elem).
event RecNaive(cm, elem).
free s: elem [private].
free s0, s1: elem [private].
"""

def tup(l): return l[0] if len(l) == 1 else "(" + ", ".join(l) + ")"
def nest(fn, base, items):
    e = base
    for it in items: e = f"{fn}({e}, {it})"
    return e
def nest_add(items, last):
    e = last
    for it in reversed(items): e = f"add({it}, {e})"
    return e

def slots(t, n):
    """list of clauses; each clause = (parties, [(s_expr_builder...)]) handled by callers"""
    return list(itertools.combinations(range(1, n + 1), t))

def secrecy(t, n, k, equiv):
    sv = "choice[s0,s1]" if equiv else "s"
    cl = slots(t, n)
    o = [DECL]
    o.append("let Deal(sv: elem) =")
    o.append("  new y1: elem;")
    for j in range(len(cl)):
        for i in range(1, t):
            o.append(f"  new v_{j}_{i}: elem; new y_{j}_{i}: elem;")
    o.append("  let D1 = com(sv, y1) in")
    allD = ["D1"]
    for j in range(len(cl)):
        for i in range(1, t):
            o.append(f"  let D_{j}_{i} = com(v_{j}_{i}, y_{j}_{i}) in"); allD.append(f"D_{j}_{i}")
    o.append(f"  out(c, {tup(allD)});")
    # corrupted parties 1..k : their slot data
    outs = []
    for q in range(1, k + 1):
        vals = []
        for j, P in enumerate(cl):
            if q in P:
                i = P.index(q)
                if i < t - 1: vals += [f"v_{j}_{i+1}", f"y_{j}_{i+1}"]
                else:
                    its_v = [f"v_{j}_{m}" for m in range(1, t)]; its_y = [f"y_{j}_{m}" for m in range(1, t)]
                    vals += [nest("sub", "sv", its_v), nest("sub", "y1", its_y)]
        if vals: outs.append(f"  out(c, {tup(vals)});")
    o += outs
    o.append("  0.")
    if not equiv: o.append("query attacker(s).")
    o.append(f"process Deal({sv})")
    return "\n".join(o)

def soundness(t, n):
    o = [DECL]
    o.append("let DealRec(sv: elem) =")
    o.append("  new y1: elem;")
    for i in range(1, t): o.append(f"  new v_{i}: elem; new y_{i}: elem;")
    o.append("  let D1 = com(sv, y1) in")
    Ds = []
    for i in range(1, t): o.append(f"  let D_{i} = com(v_{i}, y_{i}) in"); Ds.append(f"D_{i}")
    o.append("  event Dealt(sv);")
    # corrupt parties 2..t : slots 2..t-1 are v_i/y_i ; party t holds the last slot
    corr = []
    for i in range(2, t): corr += [f"v_{i}", f"y_{i}"]
    corr += [nest("sub", "sv", [f"v_{m}" for m in range(1, t)]), nest("sub", "y1", [f"y_{m}" for m in range(1, t)])]
    o.append(f"  out(c, {tup(['D1'] + Ds + corr)});")
    pats = []; chk = []
    for i in range(2, t): pats += [f"sa_{i}: elem", f"wa_{i}: elem"]; chk.append((f"sa_{i}", f"wa_{i}", f"D_{i}"))
    pats += ["sl: elem", "wl: elem"]
    lastC = nest("csub", "D1", Ds)
    o.append("  !( out(c, (v_1, y_1));")
    o.append(f"     in(c, {tup(pats)});")
    for a, b, C in chk: o.append(f"     if com({a}, {b}) = {C} then")
    o.append(f"     if com(sl, wl) = {lastC} then")
    svals = ["v_1"] + [f"sa_{i}" for i in range(2, t)]
    wvals = ["y_1"] + [f"wa_{i}" for i in range(2, t)]
    o.append(f"     let s' = {nest_add(svals, 'sl')} in")
    o.append(f"     let w' = {nest_add(wvals, 'wl')} in")
    o.append("     if com(s', w') = D1 then event Accept(s') ).")
    o.append("query x: elem; event(Accept(x)) ==> event(Dealt(x)).")
    o.append("query x: elem; event(Accept(x)).")
    o.append("process DealRec(s)")
    return "\n".join(o)

def consistency(t, n):
    cl = slots(t, n)
    o = [DECL]
    sp = [f"sx_{i}: elem, wx_{i}: elem" for i in range(1, t + 1)]
    o.append("let RecD(D1: cm, " + ", ".join(f"C_{i}: cm" for i in range(1, t + 1)) + ") =")
    o.append(f"  in(c, {tup(sp)});")
    for i in range(1, t + 1): o.append(f"  if com(sx_{i}, wx_{i}) = C_{i} then")
    sv = [f"sx_{i}" for i in range(1, t)]; wv = [f"wx_{i}" for i in range(1, t)]
    o.append(f"  let s' = {nest_add(sv, f'sx_{t}')} in")
    o.append(f"  let w' = {nest_add(wv, f'wx_{t}')} in")
    o.append("  if com(s', w') = D1 then event RecDone(D1, s').")
    o.append("let RecN(D1: cm, " + ", ".join(f"C_{i}: cm" for i in range(1, t + 1)) + ") =")
    o.append(f"  in(c, {tup(sp)});")
    for i in range(1, t + 1): o.append(f"  if com(sx_{i}, wx_{i}) = C_{i} then")
    o.append(f"  event RecNaive(D1, {nest_add(sv, f'sx_{t}')}).")
    names = ["D1"] + [f"D_{j}_{i}" for j in range(len(cl)) for i in range(1, t)]
    o.append("let Derived =")
    o.append(f"  in(c, {tup([x + ': cm' for x in names])});")
    calls = []
    for j in range(len(cl)):
        Ds = [f"D_{j}_{i}" for i in range(1, t)]
        calls.append(f"!RecD(D1, {', '.join(Ds)}, {nest('csub', 'D1', Ds)})")
    o.append("  ( " + " | ".join(calls) + " ).")
    ca = [f"Ca{i}: cm" for i in range(1, t + 1)]; cb = [f"Cb{i}: cm" for i in range(1, t + 1)]
    o.append("let Naive =")
    o.append(f"  in(c, {tup(['D1: cm'] + ca + cb)});")
    o.append("  ( !RecN(D1, " + ", ".join(f"Ca{i}" for i in range(1, t + 1)) + ") | !RecN(D1, " + ", ".join(f"Cb{i}" for i in range(1, t + 1)) + ") ).")
    o.append("query d: cm, x: elem, y: elem; event(RecDone(d, x)) && event(RecDone(d, y)) ==> x = y.")
    o.append("query d: cm, x: elem, y: elem; event(RecNaive(d, x)) && event(RecNaive(d, y)) ==> x = y.")
    o.append("query d: cm, x: elem; event(RecDone(d, x)).")
    o.append("process Derived | Naive")
    return "\n".join(o)

if __name__ == "__main__":
    mode, t, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    k = int(sys.argv[4]) if len(sys.argv) > 4 else t - 1
    if mode == "secrecy": print(secrecy(t, n, k, False))
    elif mode == "equiv": print(secrecy(t, n, k, True))
    elif mode == "soundness": print(soundness(t, n))
    elif mode == "consistency": print(consistency(t, n))
    else: sys.exit("bad mode")
