#!/usr/bin/env python3
"""wmultdcx_derive_checks.py — W-MULT-DCX COMPOSER phase: machine checks for
every intermediate claim of the pool-identification DERIVATION
(lean/notes/openmath/WMULTDCX_2026-08-08.md), run on the SAME traced-row
selection as the sealed stress battery (wmultdcx_stress.py, seal d3950f2).

The derivation's claims under test (note labels W-D1..W-D7; every family
predicted-0 unless marked census):

  DCK-SEED    [W-D1]  a*a' == the single formal cell pi^{u1+u1'} prod Phi^sigma
                      (anchors are monomials; the stage-1 formal seeding is
                      L-EXACT-sound, not a convention).
  DCK-INV     [W-D2]  u-chain = Chat_m's principal weight chain; every d-cell
                      has j_{m-1}(D) = s_m(gamma_{m+1}) (g_{m-1} = 1 pin);
                      at interior-g == 1 and g_0 = 1: the principal cell is the
                      ONLY cell (exponents s_{l+1}(u_{l+1}), coeff weight u_0);
                      at g_0 >= 2: j_0(D) = s_1(u_1) + t e_0 (t < g_0) with
                      coeff weight u_0 - t h_0, all higher exponents principal.
                      (+ psi_0 coefficient census for the g_0 >= 2 fence.)
  DCK-LEDGER  [W-D3]  the per-level path ledger identity, per Q1 cell, per l:
                      j_l(cell) = sigma_{l+1} + j_l(D) + pi_l + dumps_l
                                  - consumed_l
                      (pi_l = promotions into level l on the ancestry;
                       dumps_l = correction-dump mass received at level l,
                       incl. +1 at level 0 per Y-junk edge; consumed_l = sum of
                       P_l per promotion/exit + (P_l - e_l k) per correction).
  DCK-TOP     [W-D4]  the top threshold, CELLWISE (strictly stronger than the
                      sealed PID-DEF part-level leg): every Q1 cell satisfies
                      pi_{m-1} = kdef + e_{m-1}*r + j_{m-1}(cell)  >= kdef
                      (r = level-(m-1) correction edges on the path); hence the
                      depth-(< kdef) promotion-profile parts of Q1 are EMPTY.
  DCK-LINE    [W-D5]  line(Q1 cell) >= lamhat + sum_l pi_l q_l with
                      lamhat := line(a-cell)+line(a'-cell)+gamma_{m+1}-2 w_mPhi_m,
                      q_l := h_l prod_{l<t<m} e_t; equality when the path took
                      no junk (X/Y) edge; and per live row
                      w_m(Q1) >= lamhat + max(kdef,0)*h_{m-1}.
  DCK-DFREE   [W-D6]  the dump-free cap: every Q1 cell with zero dumps and a
                      principal d-cell satisfies pi_l <= cP_l, the P-divisor
                      pool recursion cP_1 = floor(pool_1/P_0),
                      cP_l = floor((sigma_l + s_l(u_l) + cP_{l-1})/P_{l-1});
                      at interior-g == 1 and g_0 = 1, cP_l = c_l (the S6.1
                      floors): row 11c is EXACTLY the dump-free shadow.
  DCK-DIVERGE [W-D6c] every beyond-floor cell (pi_l > c_l some l) rides a
                      dump or a non-principal d-cell (the 72 sealed PID-MAX
                      divergences' mechanism, now the contrapositive of W-D6).
  DCK-GREEDY  [W-D7]  the two-stage greedy identity a_l + b_l = c_l (stage-1
                      sigma-pump a_l = floor((sigma_l + a_{l-1})/e_{l-1}),
                      stage-2 remainder pump b_l on r_l + s_l(u_l) + b_{l-1});
                      and on rows with the stage-1 stock sigma_m + a_{m-1} >=
                      e_{m-1} and the law's clause D + c_{m-1} >= 2e_{m-1}
                      (interior-g == 1, g_0 = 1 towers): the greedy Q1 cell
                      exists — dump-free, junk-free, pc = (c_1..c_{m-1}, 2).
  DCK-CONS            stage trees reassemble the canonical divisions (the
                      stress unit's CONS leg, re-asserted here).
  CENSUS (no prediction): min-nonzero-part depth vs kdef (live rows);
                      stage-1 stock failures; junk-free cell counts;
                      principal-cell presence at g_0 >= 2.

Consumption: wmultdcx_stress.py (roster, u-chain, window/anchors, pools,
pid-key selection — imported READ-ONLY, byte-untouched) and through it
rmengine_pe_reimpl.Eng/prep + the sealed harness chain.  This runner mutates
none of those files.  Deterministic, exact, no sampling.
"""
import sys, os, time, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_stress as WS                      # read-only consumption
import rmengine_pe_reimpl as PE
from grb_order2_check import (pnorm, padd, pneg, pmul, ppow, pscal,
                              pdivmod, eq12, w0)

VIOL = []
CNT = {}

def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:300]))
    if sum(1 for v in VIOL if v[0] == fam) <= 8:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:260]}")

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

TREE_CAP = 500000

# ============ the extended two-stage reduction (full path ledgers) ============
# cell state: (sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin)
#   pc[i]    = promotions into level i+1 on the ancestry (pc[m-1] = Phi_m exits)
#   dmp[l]   = dump mass received at level l (corr a_{d,l} + Y-junk +1 at l=0)
#   cons[l]  = exponent mass consumed at level l (P_l per promo/exit,
#              P_l - e_l k per correction)
#   ncorr[l] = correction edges taken at reduction level l
#   junk     = number of X/Y (junk) edges on the path (incl. stage-2 seeding)
#   jD       = the d-cell exponent vector joined at stage-2 seeding (None in
#              stage 1); prin = "jD is the principal vector" flag

def reduce_ext(E, cells, qsink, stats):
    R = E.R; m = E.m
    corr = E.corr_table()
    stack = list(cells)
    leaves = []
    nodes = 0
    while stack:
        st = stack.pop()
        sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin = st
        nodes += 1
        if nodes > TREE_CAP:
            viol("DCK-CONS", E.tag, "tree cap exceeded")
            return None, nodes
        i = next((l for l in range(m) if j[l] >= E.P[l]), None)
        if i is None:
            leaves.append(st)
            continue
        if i <= m-2:
            j2 = list(j); j2[i] -= E.P[i]; j2[i+1] += 1
            pc2 = list(pc); pc2[i] += 1
            cn2 = list(cons); cn2[i] += E.P[i]
            stack.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin))
        else:
            j2 = list(j); j2[m-1] -= E.P[m-1]
            pc2 = list(pc); pc2[m-1] += 1
            cn2 = list(cons); cn2[m-1] += E.P[m-1]
            qsink.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin))
        for (k, dcells) in corr[i]:
            base = list(j); base[i] -= E.P[i] - E.e[i]*k
            cn2 = list(cons); cn2[i] += E.P[i] - E.e[i]*k
            nc2 = list(ncorr); nc2[i] += 1
            for (cd, av) in dcells:
                Lc, Xc, Yc = E.digit_split(b, cd)
                nj = list(base); nd = list(dmp)
                for l in range(min(i, len(av))):
                    nj[l] += av[l]; nd[l] += av[l]
                for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                    if not pnorm(E.R, cc): continue
                    jj = list(nj); jj[0] += dj0
                    dd = list(nd); dd[0] += dj0
                    stack.append((-sign, cc, tuple(jj), pc, tuple(dd),
                                  tuple(cn2), tuple(nc2), junk + jtag,
                                  jD, prin))
    return leaves, nodes

def cellsum(E, cells):
    R = E.R
    acc = []
    for st in cells:
        sign, b, j = st[0], st[1], st[2]
        lp = E.cellpoly(b, j)
        acc = padd(R, acc, lp if sign > 0 else pneg(R, lp))
    return pnorm(R, acc)

# ============================ per-tower inventory =============================
def inv_checks(E, u, su):
    m = E.m
    prin = tuple(su[l+1] for l in range(m))
    # u_0 and integrality of the last chain step
    num = u[1] - su[1]*E.h[0]
    if num % E.e[0] != 0 or num < 0:
        viol("DCK-INV", E.tag, f"u_0 chain step not in Z>=0: u1={u[1]}")
        return prin, None
    u0 = num//E.e[0]
    has_prin = False
    for (cD, jD) in E.Dcells:
        if jD[m-1] != su[m]:
            viol("DCK-INV", E.tag,
                 f"d-cell top exponent {jD[m-1]} != s_m(u_m)={su[m]} (g_(m-1)=1 pin)")
        for l in range(1, m):
            if jD[l] != su[l+1]:
                viol("DCK-INV", E.tag,
                     f"d-cell level-{l} exponent {jD[l]} != s_({l+1})(u_({l+1}))"
                     f"={su[l+1]} at interior g=1: jD={jD}")
        if E.g[0] == 1:
            if jD[0] != su[1]:
                viol("DCK-INV", E.tag, f"d-cell j0={jD[0]} != s1(u1)={su[1]} at g0=1")
            if w0(E.R, cD) != u0:
                viol("DCK-INV", E.tag, f"principal coeff w0={w0(E.R,cD)} != u0={u0}")
            has_prin = True
        else:
            t, rem = divmod(jD[0] - su[1], E.e[0])
            if rem != 0 or not (0 <= t < E.g[0]):
                viol("DCK-INV", E.tag,
                     f"g0>=2 d-cell j0={jD[0]} not s1(u1)+t*e0, t<g0")
            elif w0(E.R, cD) != u0 - t*E.h[0]:
                viol("DCK-INV", E.tag,
                     f"g0>=2 d-cell coeff w0={w0(E.R,cD)} != u0-t*h0={u0-t*E.h[0]}")
            if jD == prin: has_prin = True
    if E.g[0] == 1 and E.d0 == 1 and len(E.Dcells) != 1:
        viol("DCK-INV", E.tag,
             f"{len(E.Dcells)} d-cells at interior-g=1,g0=1,d0=1 (expected 1)")
    if not has_prin:
        note("prin_absent")
        print(f"  CENSUS [{E.tag}]: principal d-cell ABSENT (theta_0 = 0 case)")
    # psi0 coefficient pattern (the g0 >= 2 fence census)
    T = E.grbT
    pat = [0 if T.K0["isz"](T.psi0[k]) else 1 for k in range(E.g[0])]
    return prin, dict(u0=u0, prin=list(prin), has_prin=has_prin, psi0_nz=pat,
                      ndcells=len(E.Dcells))

# ============================== one traced row ================================
def q_quanta(E):
    return [None] + [E.h[l]*prod(E.e[l+1:E.m]) for l in range(1, E.m)]

def cP_chain(E, sig, su):
    cp = 0; out = []
    for l in range(1, E.m):
        cp = (sig[l-1] + su[l] + cp)//E.P[l-1]
        out.append(cp)
    return out

def greedy_chains(E, sig, su, cs):
    """stage-1 pump a, remainders r, stage-2 pump b; identity a+b=c checked
    by the caller.  All with the P-divisors (= e at interior g == 1)."""
    m = E.m
    a = [0]*m
    for i in range(0, m-1):
        a[i+1] = (sig[i] + a[i])//E.P[i]
    r = [(sig[i] + a[i]) % E.P[i] for i in range(m-1)]
    b = [0]*m
    for i in range(0, m-1):
        b[i+1] = (r[i] + su[i+1] + b[i])//E.P[i]
    stock1 = sig[m-1] + a[m-1]
    return a, r, b, stock1

def check_row(E, sA, sB, u1a, u1b, aA, aB, su, pools, cs, D, kdef, live, key,
              prin, recs):
    R = E.R; m = E.m
    etop = E.e[m-1]
    sig = tuple(sA[l+1] + sB[l+1] for l in range(m))
    # --- W-D1: the product IS the formal cell ---
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    if pnorm(R, padd(R, prodp, pneg(R, E.cellpoly(b0, sig)))):
        viol("DCK-SEED", E.tag, f"a*a' != formal cell at {key}")
    lamhat = E.line(b0, sig) + E.gam[m+1] - 2*E.wmPhi
    qv = q_quanta(E)
    # --- stage 1 ---
    z = (0,)*m
    init = [(1, b0, sig, z, z, z, z, 0, None, False)]
    q1sink = []
    out = reduce_ext(E, init, q1sink, {})
    if out[0] is None: return
    leaves1, n1 = out
    E1c, E0c = pdivmod(R, prodp, E.Phis[m])
    if cellsum(E, q1sink) != pnorm(R, E1c):
        viol("DCK-CONS", E.tag, f"stage-1 exit sum != E1IH at {key}")
    if cellsum(E, leaves1) != pnorm(R, E0c):
        viol("DCK-CONS", E.tag, f"stage-1 leaf sum != rem at {key}")
    # --- stage 2 seeding: exit cofactor x d-cell, L-NORM split ---
    init2 = []
    for st in q1sink:
        sign, b, j, pc, dmp, cons, ncorr, junk = st[:8]
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sign, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp))
    q2sink = []
    out2 = reduce_ext(E, init2, q2sink, {})
    if out2[0] is None: return
    leaves2, n2 = out2
    Q1c, R1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])
    if cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("DCK-CONS", E.tag, f"stage-2 exit sum != Q1 at {key}")
    if cellsum(E, leaves2) != pnorm(R, R1c):
        viol("DCK-CONS", E.tag, f"stage-2 leaf sum != rem at {key}")
    # --- per-cell checks on Q1 cells ---
    cP = cP_chain(E, sig, su)
    min_top = None
    dfree_prof = set()
    for st in q2sink:
        sign, b, j, pc, dmp, cons, ncorr, junk, jD, isp = st
        if pc[m-1] != 2:
            viol("DCK-CONS", E.tag, f"Q1 cell with {pc[m-1]} exits at {key}")
        # W-D3 ledger, per level
        for l in range(m):
            pin = pc[l-1] if l >= 1 else 0
            if j[l] != sig[l] + jD[l] + pin + dmp[l] - cons[l]:
                viol("DCK-LEDGER", E.tag,
                     f"ledger fails at level {l}, key={key}: j={j} sig={sig} "
                     f"jD={jD} pc={pc} dmp={dmp} cons={cons}")
        # W-D4 top identity + threshold (uses the g_{m-1}=1 d-cell pin)
        pi_top = pc[m-2]
        if pi_top != kdef + etop*ncorr[m-1] + j[m-1] + (jD[m-1] - su[m]):
            viol("DCK-TOP", E.tag,
                 f"top identity fails at {key}: pi={pi_top} kdef={kdef} "
                 f"r={ncorr[m-1]} jtop={j[m-1]}")
        if pi_top < kdef:
            viol("DCK-TOP", E.tag,
                 f"CELL below deficit depth at {key}: pi={pi_top} < k={kdef}")
        if min_top is None or pi_top < min_top: min_top = pi_top
        # W-D5 line floor / equality
        lf = lamhat + sum(pc[l-1]*qv[l] for l in range(1, m))
        ln = E.line(b, j)
        if ln < lf:
            viol("DCK-LINE", E.tag,
                 f"line {ln} < floor {lf} at {key} (pc={pc}, junk={junk})")
        if junk == 0 and ln != lf:
            viol("DCK-LINEEQ", E.tag,
                 f"junk-free cell line {ln} != exact {lf} at {key}")
        note("cells");
        if junk == 0: note("cells_junkfree")
        # W-D6 dump-free cap + divergence channel
        dtot = sum(dmp)
        if dtot == 0 and isp:
            for l in range(1, m):
                if pc[l-1] > cP[l-1]:
                    viol("DCK-DFREE", E.tag,
                         f"dump-free principal cell pi_{l}={pc[l-1]} > "
                         f"cP_{l}={cP[l-1]} at {key}")
            dfree_prof.add(pc[:m-1])
        beyond = any(pc[l-1] > cs[l-1] for l in range(1, m))
        if beyond and dtot == 0 and isp:
            viol("DCK-DIVERGE", E.tag,
                 f"beyond-floor cell with no dumps, principal D at {key}: "
                 f"pc={pc} cs={cs}")
        if beyond: note("cells_beyond_floor")
    # min nonzero part depth census (live rows)
    if live:
        byk = {}
        for st in q2sink:
            byk.setdefault(st[3][m-2], []).append(st)
        minnz = None
        for kk in sorted(byk):
            if cellsum(E, byk[kk]):
                minnz = kk; break
        note(f"minnz_eq_kdef_{'yes' if minnz == kdef else 'NO'}")
        # W-D5 weight floor per live row
        wq = E.wm(Q1c)
        if wq < lamhat + max(kdef, 0)*E.h[m-1]:
            viol("DCK-WM", E.tag,
                 f"w_m(Q1)={wq} < lamhat+k*h = "
                 f"{lamhat + max(kdef,0)*E.h[m-1]} at {key}")
    # W-D7 greedy (interior-g == 1 AND g0 = 1 towers only)
    a, rr, bb, stock1 = greedy_chains(E, sig, su, cs)
    allg1 = all(E.g[l] == 1 for l in range(m))
    if allg1:
        for l in range(1, m):
            if a[l] + bb[l] != cs[l-1]:
                viol("DCK-GREEDY", E.tag,
                     f"a_l+b_l != c_l at {key}: a={a} b={bb} cs={cs}")
        lawfire = (D + (cs[-1] if cs else 0) >= 2*etop)
        if stock1 >= E.P[m-1]:
            note("stock1_ok")
            if lawfire:
                target = tuple(cs)
                if target in dfree_prof:
                    note("greedy_cell_found")
                else:
                    viol("DCK-GREEDY", E.tag,
                         f"greedy Q1 cell pc={target} absent at {key} "
                         f"(dump-free profiles: {sorted(dfree_prof)})")
        else:
            note("stock1_fail")
            if live: note("stock1_fail_live")
    recs.append(dict(key=key, cs=cs, D=D, kdef=kdef, live=live,
                     min_top_cell=min_top, ncells=len(q2sink),
                     stock1=stock1, allg1=allg1))

# ================================ tower loop ==================================
def run_tower(spec, results):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    u, su = WS.uchain(E)
    if u is None:
        viol("DCK-INV", tag, "u-chain failed"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m-1]
    prin, invrec = inv_checks(E, u, su)
    # replicate the sealed battery's pid-key selection VERBATIM
    pid_keys = {}
    R = E.R
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            strack = (sA[m+1] == E.e[m]-1 and sB[m+1] == E.e[m]-1)
            if not strack: continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            e1nz = bool(pnorm(R, E1))
            track = strack and e1nz
            if not (track and m >= 2): continue
            pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
            meas = False
            Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
            if pnorm(R, Q1):
                Tsum = sA[m+1] + sB[m+1]
                dpl = Tsum//E.e[m]
                locus = ((dpl == 1 and strack and E.e[m] >= 2)
                         or (Tsum == E.e[m]-1 and E.e[m] == 1))
                if locus: meas = True
            key = (tuple(sorted([(tuple(sA[l] for l in range(1, m+2)), u1a),
                                 (tuple(sB[l] for l in range(1, m+2)), u1b)])))
            if key not in pid_keys:
                kdef = 2*etop - Dd
                want = (meas or top in (2*etop - 1, 2*etop, 2*etop - 2)
                        or (len(cs) >= 2 and cs[0] > 0 and cs[1] > 0)
                        or (cs and max(cs) >= 2))
                if want:
                    pid_keys[key] = (ga, gb, cs, Dd, kdef, meas,
                                     sA, sB, u1a, u1b)
    cap = 14 if m >= 4 else 40
    chosen = sorted(pid_keys.items(), key=lambda kv: (
        not kv[1][5], -(kv[1][2][0] if kv[1][2] else 0), kv[0]))[:cap]
    recs = []
    for key, (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) in chosen:
        pools, _, _, _ = WS.pools_of(E, sA, sB, su)
        check_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                  pools, cs, Dd, kdef, meas, (ga, gb), prin, recs)
    print(f"-- {tag} m={m} {kind},p={p},d0={d0} g={E.g[:m]}: traced={len(recs)} "
          f"cells={sum(r['ncells'] for r in recs)} ({time.time()-t0:.1f}s)")
    results.append(dict(tag=tag, m=m, kind=kind, p=p, d0=d0, reads=reads,
                        inv=invrec, rows=recs))

def main():
    t0 = time.time()
    results = []
    for spec in WS.ROSTER:
        run_tower(spec, results)
    print()
    fams = ["DCK-SEED", "DCK-INV", "DCK-LEDGER", "DCK-TOP", "DCK-LINE",
            "DCK-LINEEQ", "DCK-DFREE", "DCK-DIVERGE", "DCK-WM",
            "DCK-GREEDY", "DCK-CONS"]
    labels = {
        "DCK-SEED":  "W-D1 a*a' == formal cell",
        "DCK-INV":   "W-D2 u-chain/d-cell inventory",
        "DCK-LEDGER":"W-D3 path ledger identity (per cell, per level)",
        "DCK-TOP":   "W-D4 top threshold cellwise (pi = k + e*r + j_top >= k)",
        "DCK-LINE":  "W-D5 line floor lamhat + sum pi_l q_l",
        "DCK-LINEEQ":"W-D5 junk-free line EQUALITY",
        "DCK-DFREE": "W-D6 dump-free principal cap (P-divisor pools)",
        "DCK-DIVERGE":"W-D6c beyond-floor => dumps or non-principal D",
        "DCK-WM":    "W-D5 w_m(Q1) >= lamhat + k*h_{m-1} (live rows)",
        "DCK-GREEDY":"W-D7 greedy a+b=c + greedy Q1 cell exists",
        "DCK-CONS":  "stage trees == canonical divisions",
    }
    nrows = sum(len(r["rows"]) for r in results)
    ncells = sum(rr["ncells"] for r in results for rr in r["rows"])
    for f in fams:
        n = sum(1 for v in VIOL if v[0] == f)
        print(f"{f} VERDICT ({labels[f]}, predicted-0): "
              f"{'GREEN' if n == 0 else 'RED'} [{n} violations]")
    print(f"rows traced: {nrows} (sealed battery: 412); Q1 cells checked: "
          f"{ncells}; beyond-floor cells: {CNT.get('cells_beyond_floor',0)}; "
          f"junk-free: {CNT.get('cells_junkfree',0)}/{CNT.get('cells',0)}")
    print(f"CENSUS min-nonzero-part == kdef on live rows: "
          f"yes={CNT.get('minnz_eq_kdef_yes',0)} "
          f"no={CNT.get('minnz_eq_kdef_NO',0)}")
    print(f"CENSUS stage-1 stock: ok={CNT.get('stock1_ok',0)} "
          f"fail={CNT.get('stock1_fail',0)} "
          f"(fail on live rows: {CNT.get('stock1_fail_live',0)}); "
          f"greedy cells found: {CNT.get('greedy_cell_found',0)}; "
          f"principal d-cell absent: {CNT.get('prin_absent',0)}")
    print(f"counters: {dict(sorted(CNT.items()))}")
    print(f"total violations: {len(VIOL)}; elapsed {time.time()-t0:.1f}s")
    def md5(fn):
        with open(os.path.join(HERE, fn), "rb") as fh:
            return hashlib.md5(fh.read()).hexdigest()
    out = dict(violations=VIOL, counters=CNT, towers=results,
               provenance={fn: md5(fn) for fn in
                           ("wmultdcx_derive_checks.py", "wmultdcx_stress.py",
                            "rmengine_pe_reimpl.py", "grb_order2_check.py")},
               elapsed=time.time() - t0)
    with open(os.path.join(HERE, "wmultdcx_derive_checks_results.json"),
              "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    return 0

if __name__ == "__main__":
    sys.exit(main())
