"""BCFGTIE post-seal spot check (DISCLOSED as added after the commit-1 seal; the
sealed runner bcfgtie_checks.py is byte-frozen and does not include this).

The committed reference file results/bcfg_n7.json (n=7 BCFG distribution rows) is
consumed by NO standing check (reconcile_om_bcfg.py stops at n=6).  The BCFGTIE
theorem (E_n^proj = 1 for all n) makes a falsifiable prediction about it, preregistered
in the unit conversation and in the note BEFORE this script was first run:

  PREREG-N7a:  sum_{r=0}^{7} P(7,r;q) == 1        (symbolic in q)
  PREREG-N7b:  sum_{r=0}^{7} r * P(7,r;q) == 1    (symbolic in q)  <- the theorem

Engine-free: touches only the committed JSON + sympy.
"""
import os, sys, json
import sympy as sp

q = sp.symbols('q', positive=True)
HERE = os.path.dirname(os.path.abspath(__file__))
fn = os.path.join(HERE, '..', 'results', 'bcfg_n7.json')
D = json.load(open(fn))['dist']
rows = {int(r): sp.cancel(sp.sympify(v, locals={'q': q})) for r, v in D.items()}
print("rows present: r =", sorted(rows))
s0 = sp.cancel(sum(rows.values()))
s1 = sp.cancel(sum(r * v for r, v in rows.items()))
ok0 = sp.simplify(s0 - 1) == 0
ok1 = sp.simplify(s1 - 1) == 0
print(f"sum_r P(7,r)   == 1 : {ok0}   [{s0 if not ok0 else '1'}]")
print(f"sum_r r*P(7,r) == 1 : {ok1}   [{s1 if not ok1 else '1'}]")
sys.exit(0 if (ok0 and ok1) else 1)
