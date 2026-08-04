#!/usr/bin/env python3
"""ilnres_checks.py — machine leg of ILNRES_2026-08-08.md (the (DS-SUB)
engine-free-support lemma probe; [ILN] non-(RM) residual NR-4).

Tests the (P-DS) SUB-PACKAGE (support / E1=>CII / division-only case
construction) at rungs r = 1..3 on towers chosen OFF T-class (interior
flats e_i = 1 with d0 >= 2; e0 = 1 & d0 = 2; a d0 = 3 flat via engine_ext),
where (RM-m) is UNPROVEN — decorrelated evidence that the sub-package does
not ride the engine — plus a d0 = 1 T-control and a DCX-live e0 = 3 shape.
Families: DS-SUPP, DS-E1, DS-CASE, DS-CHAT, OB-OUT, DS-E0 (evidence-only),
DCX-CENSUS (measured), ENG-GATE.  Exact arithmetic; deterministic; no seed.
Committed engines consumed READ-ONLY; engine_ext is the single seam.
Usage: ilnres_checks.py [--shakedown]   (reduced windows, no json).
"""
import sys, os, math, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, pnorm, padd, pneg, pmul, ppow, pscal,
                              pdivmod, eq12, bezout, INF, mk_field_ext)
import engine_ext
engine_ext.install()                      # standing rule: beyond-wall shapes
import strata3_probe as S3MOD
import iterlawr_probe as ILP              # psi2 shim
from iterlaw4_probe import Tower4, Composite4

SHAKE = "--shakedown" in sys.argv
VIOL = []       # LAW families: DS-SUPP/DS-E1/DS-CASE/DS-CHAT/OB-OUT/ENG-GATE
EVID = []       # evidence-only family DS-E0 (never law-RED)
CNT = {}
MEAS = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def meas(fam, n=1): MEAS[fam] = MEAS.get(fam, 0) + n
def viol(fam, tag, detail):
    lst = EVID if fam == "DS-E0" else VIOL
    lst.append((fam, tag, str(detail)[:200]))
    print(f"  {'EVID-DEV' if fam == 'DS-E0' else 'VIOLATION'} "
          f"[{fam}] {tag}: {detail}")

def psub(R, A, B): return padd(R, A, pneg(R, B))
def pdeg(R, A):
    A = pnorm(R, A)
    return len(A) - 1 if A else -INF

# ---------------- per-tower data bundle ----------------
class TD:
    """Level data for one Tower4: (e_j,h_j,g_j) j=0..3, Phi_j, weights w_r,
    gammas, degrees — read off the committed objects only."""
    def __init__(self, T4):
        T3 = T4.T3; T = T3.T
        self.T4, self.T3, self.T, self.R = T4, T3, T, T.R
        self.e = [T.e0, T.e1, T3.e2, T4.e3]
        self.h = [T.h0, T.h1, T3.h2, T4.h3]
        self.g = [T.g0, T.g1, T3.g2, T4.g3]
        self.Phi = [T.Phi0, T.Phi1, T.Phi2, T3.Phi3]   # Phi_0..Phi_3
        self.dPhi = [pdeg(self.R, f) for f in self.Phi]
        self.w = [None, T.w1, T.w2, T3.w3]             # w_r on deg<degPhi_r
        # canonical correction digits Chat_m = Phi_{m+1} - Phi_m^{e_m}
        # (defined when g_m = 1; consumed for DCX flags at levels m = 1, 2)
        self.Chat = {}
        for m in (1, 2):
            if self.g[m] == 1:
                self.Chat[m] = psub(self.R, self.Phi[m+1],
                                    ppow(self.R, self.Phi[m], self.e[m]))

def cii_chain(td, s_a, s_b):
    """CII_r for r = 1..3 from integer split data (T_j = s_j(a)+s_j(b));
    delta_j = plain carry.  Returns (cii dict, T dict, delta dict)."""
    Tj = {j: s_a[j] + s_b[j] for j in (1, 2, 3, 4)}
    dj = {j: Tj[j] // td.e[j-1] for j in (1, 2, 3, 4)}
    cii = {1: (td.g[0] == 1 and dj[1] == 1)}
    for r in (2, 3):
        cii[r] = (td.g[r-1] == 1) and (
            dj[r] == 1 or (cii[r-1] and Tj[r] == td.e[r-1] - 1))
    return cii, Tj, dj

def dcx_flags(td, ddIH, Tj, dj, cii):
    """Constructive DCX_m flags, m = 2,3: at rung m the IH digits are
    ddIH[m-1] = dev(BP_{m-1}, Phi_{m-1}) (rel slots 0,1 <-> T_m, T_m+1).
    Flag = g_{m-1}=1 & E1IH != 0 & track-extreme & Q1 != 0."""
    flags = {}
    for m in (2, 3):
        f = False
        if td.g[m-1] == 1 and (m-1) in td.Chat:
            d = ddIH[m-1]
            E1 = d[1] if len(d) > 1 else []
            if E1:
                track = ((Tj[m] == 2*td.e[m-1] - 2 and dj[m] == 1)
                         or td.e[m-1] == 1)
                if track:
                    Q1, _ = pdivmod(td.R, pmul(td.R, E1, td.Chat[m-1]),
                                    td.Phi[m-1])
                    f = bool(pnorm(td.R, Q1))
        flags[m] = f
    return flags

# ---------------- the per-tower battery ----------------
ROSTER = [
    ("X1-FLATINT-d2", "Zp", 3, 2, [(2,1,1),(1,1,1),(2,1,1),(1,1,1)]),
    ("X1-FLATINT-d2", "Fpt", 2, 2, [(2,1,1),(1,1,1),(2,1,1),(1,1,1)]),
    ("X2-DEV1COR",   "Zp", 2, 2, [(1,1,2),(2,1,1),(1,1,1),(2,1,1)]),
    ("X2-DEV1COR",   "Fpt", 3, 2, [(1,1,2),(2,1,1),(1,1,1),(2,1,1)]),
    ("X3-FLAT-H2",   "Zp", 3, 2, [(3,1,1),(1,2,1),(2,1,1),(1,1,1)]),
    ("X3-FLAT-H2",   "Fpt", 2, 2, [(3,1,1),(1,2,1),(2,1,1),(1,1,1)]),
    ("X4-D3FLAT",    "Zp", 2, 3, [(2,1,1),(1,1,2),(2,1,1),(1,1,1)]),
    ("X5-TCTRL-d1",  "Zp", 3, 1, [(2,1,1),(2,1,1),(1,1,1),(2,1,1)]),
    ("X6-DCXLIVE",   "Zp", 2, 2, [(3,2,1),(2,1,1),(2,1,1),(1,1,1)]),
]

def run_tower(name, kind, p, d0, rs):
    tag = f"{name}/{kind}{p}"
    T4 = Tower4(kind, p, d0, rs[0], rs[1], rs[2], rs[3], tag)
    C = Composite4(T4, with_shadow=False)
    td = TD(T4)
    R = td.R
    # DS-CHAT: WELL-DEF instance — deg Chat_m < deg Phi_m
    for m, ch in td.Chat.items():
        note("DS-CHAT")
        if pdeg(R, ch) >= td.dPhi[m]:
            viol("DS-CHAT", tag, f"deg Chat_{m} = {pdeg(R, ch)} >= {td.dPhi[m]}")
    E4 = T4.E4
    W = 4 if SHAKE else E4 + min(E4, 8)
    G0 = C.Gamma0
    census = {"pairs": 0, "dcx2": 0, "dcx3": 0, "on_dcx_supp_ok": 0,
              "on_dcx_supp_dev": 0}
    for ga in range(G0, G0 + W):
        sa = C.split(ga)
        for gb in range(G0, G0 + W):
            sb = C.split(gb)
            census["pairs"] += 1
            s_a = {4: sa[0], 3: sa[1], 2: sa[2], 1: sa[3]}
            s_b = {4: sb[0], 3: sb[1], 2: sb[2], 1: sb[3]}
            Bv = {3: sa[4]+sb[4], 2: sa[5]+sb[5], 1: sa[6]+sb[6]}
            U = sa[7] + sb[7]
            cii, Tj, dj = cii_chain(td, s_a, s_b)
            # incremental base products BP_r and rung devs dd[r]
            BP = pscal(R, R["pi_pow"](U), ppow(R, td.Phi[0], Tj[1]))
            dd = {}
            for r in (1, 2, 3):
                if r > 1:
                    BP = pmul(R, BP, ppow(R, td.Phi[r-1], Tj[r]))
                dd[r] = dev(R, BP, td.Phi[r])
            flags = dcx_flags(td, dd, Tj, dj, cii)
            if flags[2]: census["dcx2"] += 1
            elif flags[3]: census["dcx3"] += 1
            offdcx = {1: True, 2: not flags[2],
                      3: not (flags[2] or flags[3])}
            for r in (1, 2, 3):
                d = dd[r]
                nz = [j for j, c in enumerate(d) if pnorm(R, c)]
                if not offdcx[r]:
                    # measured only: sub-package behavior ON DCX
                    if all(j <= 1 for j in nz): census["on_dcx_supp_ok"] += 1
                    else: census["on_dcx_supp_dev"] += 1
                    continue
                # DS-SUPP (rel slots 0,1 <-> T_{r+1}, T_{r+1}+1)
                note("DS-SUPP")
                if any(j > 1 for j in nz):
                    viol("DS-SUPP", tag,
                         f"r={r} pair=({ga},{gb}) slots={nz}")
                    continue
                E0 = d[0] if len(d) > 0 else []
                E1 = d[1] if len(d) > 1 else []
                # DS-E1: E1 != 0 => CII_r
                note("DS-E1")
                if pnorm(R, E1) and not cii[r]:
                    viol("DS-E1", tag,
                         f"r={r} pair=({ga},{gb}) E1!=0 off CII_{r}")
                # DS-E0 (evidence-only family): E0 != 0, w_r(E0) = B_r
                note("DS-E0")
                if not pnorm(R, E0):
                    viol("DS-E0", tag, f"r={r} pair=({ga},{gb}) E0 = 0")
                elif td.w[r](E0) != Bv[r]:
                    viol("DS-E0", tag,
                         f"r={r} pair=({ga},{gb}) w={td.w[r](E0)} != {Bv[r]}")
                # DS-CASE at r >= 2: one-substitution construction == dev
                if r >= 2:
                    dIH = dd[r-1]
                    eg = td.e[r-1]*td.g[r-1]
                    lo, hi = [], []
                    for j, c in enumerate(dIH):
                        if not pnorm(R, c): continue
                        a = Tj[r] + j          # absolute Phi_{r-1} slot
                        if a >= eg:
                            if td.g[r-1] != 1 or (r-1) not in td.Chat:
                                viol("DS-CASE", tag,
                                     f"r={r} overflow at g>=2 pair=({ga},{gb})")
                                hi = None; break
                            hi.append((a - eg, c))
                        else:
                            lo.append((a, c))
                    if hi is None: continue
                    note("DS-CASE")
                    E1c = []
                    for a, c in hi:
                        E1c = padd(R, E1c, pmul(R, c, ppow(R, td.Phi[r-1], a)))
                    E0c = []
                    for a, c in lo:
                        E0c = padd(R, E0c, pmul(R, c, ppow(R, td.Phi[r-1], a)))
                    if hi:
                        E0c = psub(R, E0c, pmul(R, E1c, td.Chat[r-1]))
                    if pnorm(R, psub(R, E0c, E0)) or pnorm(R, psub(R, E1c, E1)):
                        viol("DS-CASE", tag,
                             f"r={r} pair=({ga},{gb}) construction != dev")
            # OB-OUT: flagged DCX_m pairs lie in the outer locus
            for m in (2, 3):
                if not flags[m]: continue
                note("OB-OUT")
                em = td.e[m-1]
                ok = (td.g[m-1] == 1 and s_a[m] == em - 1
                      and s_b[m] == em - 1 and cii[m-1])
                if not ok:
                    viol("OB-OUT", tag,
                         f"m={m} pair=({ga},{gb}) outside outer locus")
    meas(f"{tag}:pairs", census["pairs"])
    return census

def main():
    t0 = time.time()
    print(f"=== ilnres_checks (SHAKE={SHAKE}) ===")
    gate_viol = engine_ext.agreement_gate(full=False)
    note("ENG-GATE-cases")
    print(f"ENG-GATE new violations: {gate_viol}")
    if gate_viol:
        viol("ENG-GATE", "agreement_gate", f"{gate_viol} new violations")
    censuses = {}
    for name, kind, p, d0, rs in ROSTER:
        tag = f"{name}/{kind}{p}"
        print(f"-- {tag} (d0={d0}, rs={rs})")
        censuses[tag] = run_tower(name, kind, p, d0, rs)
        print(f"   census: {censuses[tag]}")
    print("\n=== COUNTS ===")
    for k in sorted(CNT): print(f"  {k}: {CNT[k]}")
    print("=== DCX-CENSUS (measured) ===")
    for k, c in censuses.items(): print(f"  {k}: {c}")
    law = "GREEN" if not VIOL else f"RED ({len(VIOL)} violations)"
    evid = "GREEN" if not EVID else f"DEVIATIONS ({len(EVID)})"
    verdict = f"LAW {law} | EVIDENCE(DS-E0) {evid}"
    print(f"\nVERDICT: {verdict}   elapsed {time.time()-t0:.1f}s")
    if not SHAKE:
        out = {"verdict": verdict, "counts": CNT, "censuses": censuses,
               "violations": VIOL, "evidence_deviations": EVID,
               "eng_gate_new_viol": gate_viol,
               "roster": [list(map(str, r)) for r in ROSTER]}
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "ilnres_checks_results.json"), "w") as f:
            json.dump(out, f, indent=1, default=str)
    return 0 if not VIOL else 1

if __name__ == "__main__":
    sys.exit(main())
