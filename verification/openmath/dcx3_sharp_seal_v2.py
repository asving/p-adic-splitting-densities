#!/usr/bin/env python3
"""dcx3_sharp_seal_v2.py — DCX3 SHARP-LOCUS RESEAL CYCLE (v2; the one
resealed-candidate cycle of the DCX3_SHARP unit, prereg §S6 of
lean/notes/openmath/DCX3_SHARP_2026-08-08.md; sealed BEFORE run 2).

THE CORRECTED CANDIDATE (v2, THE UNIFORM CARRY LAW; separated post-run
from run 1, exact 3320/3320 there, display-only until THIS seal):

    TRACK := s3 = s3' = e2-1 AND E1IH != 0
    lvl2  := (s2+s2') + s2(gamma3),  pool := s1+s1'+s1(u0),
    u0    := (gamma3 - s2(gamma3)*gamma2)/e1
    DCX3v2 := TRACK AND lvl2 + floor(pool/e0) >= 2*e1

(v1 = v2 with the carry floor capped at 1 — REFUTED at run 1, 40
deficit-2 witnesses. Since pool <= 3(e0-1) < 3e0, floor(pool/e0) <= 2:
v2 predicts every lvl2 <= 2e1-3 row DEAD — a sealed fresh prediction.)

LEGS (predicted-0; any violation = probe finding):
  F-SHARP-2   DCX3v2 == DCX3meas pairwise on every window pair
              (DCX3meas operationalized verbatim as before).
  F-OUTER-2   measured-live rows satisfy {g1 = 1 AND s3 = s3' = e2-1}.
  F-CHAIN-2   depth-tracked two-stage trace (cell polys split by
              promotion count 0 / 1 / 2+ along ancestry):
              (C1) tree == division at both stages on every live row;
              (C2) on every live row with deficit k := 2e1 - lvl2 in
                   {1,2}: all depth-parts < k of Q1 are ZERO and the
                   depth->=k remainder is nonzero (the k missing
                   Phi1-exponents are ALL promotion-supplied);
              (C3) on every DIRECT live row (lvl2 >= 2e1): the depth-0
                   part of Q1 is NONZERO (clean-visible) — run-1's
                   103/103 census pattern, now sealed.
  F-BOUNDARY-2 meters (design-verified): M1 deficit-1 track rows >= 20;
              M2a deficit-2 & pool >= 2e0 rows >= 20; M2b deficit-2 &
              pool == 2e0-1 rows >= 5 (the just-miss dead edge);
              M4 deficit>=3 & pool >= 2e0 rows >= 10 (the maximal-pool
              dead stress for the new no-deficit-3 prediction).
Mutation controls (SEPARATE; one per v2 constant): MC-1 threshold
2e1 -> 2e1+1; MC-2 carry divisor e0 -> e0+1; MC-3 carry cap at 1
(= the REFUTED v1; must trip on the deficit-2 stratum); MC-4 u0 ->
floor(gamma3/e1). DETERMINISTIC, full window blocks, no sampling.
Usage: dcx3_sharp_seal_v2.py [--design]  (design = IH-side only).
"""
import sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grb_order2_check import (dev, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, INF, pdivmod)
import strata3_probe as S3MOD
import iterlawr_probe as ILP
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4, Composite4
from rm2_probe import Engine2, anchor2, digit_split, monomials

VIOL = []
CNT = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:240]))
    if sum(1 for v in VIOL if v[0] == fam) <= 10:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:200]}")

# EXTENSION roster (run 2): fresh tuples, disjoint from the RM-2 seven
# AND the run-1 nine; deficit-2 edges + deficit-3 dead stress targeted.
ROSTER = [
    ("EX1", 1, (3,1,1), (4,1,1), (2,3,1), (2,1,1),
     "e1=4 deep window, s2g3=3, s1u0=2: deficit-1/2/3 all realized; "
     "r3=(2,1,1) keeps the tuple disjoint from run-1 DS2; E4=48"),
    ("EX2", 1, (4,1,1), (3,1,1), (2,5,1), (1,1,1),
     "e0=4 rich pool (s1<=3, s1u0=3): deficit-2 needs pool>=8; "
     "deficit-3 dead stress at maximal pool 9"),
    ("EX3", 1, (3,1,2), (2,1,1), (2,1,1), (1,1,1),
     "g0=2 at e0=3, s1u0=2: the double carry at the g-pattern "
     "(literal-e0 twice)"),
    ("EX4", 2, (3,1,1), (3,2,1), (2,5,1), (1,1,1),
     "d0=2 junk-alive deficit-2 (s2g3=1, s1u0=2) + fresh p=5; l1=2"),
    ("EX5", 1, (3,1,1), (3,1,1), (2,1,1), (3,1,1),
     "e3=3 NEW (u1 in {0,1,2}): E4=54; s1u0=2; deficit-1/2/3 strata "
     "with 9-fold u1-multiplicity"),
    ("EX6", 2, (3,2,1), (3,2,1), (2,1,1), (1,1,1),
     "s1u0=0 pins the pool LOW (deficit-2 predicted all-dead: the "
     "u0-term's absence tested) + the ONLY MC-4-visible shape "
     "(mut s1u0'=2)"),
]
RINGS = {t[0]: [("Zp", 3)] for t in ROSTER}
RINGS["EX1"].append(("Fpt", 2))
RINGS["EX4"] = [("Zp", 5)]
RINGS["EX5"].append(("Fpt", 2))
CAP_POPS = 3000
MC = dict(m1=0, m2=0, m3=0, m4=0)
MCVIS = dict(m1=0, m2=0, m3=0, m4=0)


class DepthTree:
    """E1-priority reduction tree with per-cell polys split by promotion
    DEPTH (0 / 1 / 2+ promotion edges along ancestry). Exact linear
    bookkeeping: sum of depth parts == the canonical division."""
    ND = 3
    def __init__(self, E, init_cells):
        self.E = E; T = E.T
        self.e0g0, self.e1g1 = T.e0*T.g0, T.e1*T.g1
        self.mu1 = self.e0g0*(T.e1 + 1); self.mu0 = 2*T.e1
        self.cells = {}
        self.Q = [[] for _ in range(self.ND)]
        self.pops = 0; self.status = "OK"; self.n_promo = 0
        for (b, j0, j1, d) in init_cells:
            self.add(b, j0, j1, d)
    def mu(self, j0, j1): return self.mu1*j1 + self.mu0*j0
    def add(self, b, j0, j1, d):
        R = self.E.R
        b = pnorm(R, b)
        if not b: return
        d = min(d, self.ND - 1)
        key = (j0, j1)
        cur = self.cells.get(key, [[] for _ in range(self.ND)])
        cur[d] = padd(R, cur[d], b)
        if any(pnorm(R, x) for x in cur): self.cells[key] = cur
        elif key in self.cells: del self.cells[key]
    def run(self):
        E = self.E; T = E.T; R = E.R
        while True:
            red = [c for c in self.cells
                   if c[0] >= self.e0g0 or c[1] >= self.e1g1]
            if not red: break
            self.pops += 1
            if self.pops > CAP_POPS:
                self.status = "CAP"; return self
            j0, j1 = max(red, key=lambda c: self.mu(*c))
            parts = self.cells.pop((j0, j1))
            if j0 >= self.e0g0:                       # E1
                self.n_promo += 1
                for d, b in enumerate(parts):
                    b = pnorm(R, b)
                    if not b: continue
                    self.add(b, j0 - self.e0g0, j1 + 1, d + 1)  # promotion
                    for i, cf in E.lvl1:
                        L, X, Y = digit_split(T, pmul(R, b, cf))
                        nj0 = j0 - self.e0g0 + T.e0*i
                        for poly, dj in ((L, 0),
                                         (pscal(R, R["pi_pow"](1), X), 0),
                                         (Y, 1)):
                            if pnorm(R, poly):
                                self.add(pneg(R, poly), nj0 + dj, j1, d)
            else:                                     # E2
                for d, b in enumerate(parts):
                    b = pnorm(R, b)
                    if not b: continue
                    ex = pmul(R, pmul(R, b, ppow(R, T.Phi0, j0)),
                              ppow(R, T.Phi1, j1 - self.e1g1))
                    self.Q[d] = padd(R, self.Q[d], ex)
                    for k, digs in E.Ck_digits.items():
                        nj1 = j1 - self.e1g1 + T.e1*k
                        for i0c, dc in digs:
                            L, X, Y = digit_split(T, pmul(R, b, dc))
                            for poly, dj in ((L, 0),
                                             (pscal(R, R["pi_pow"](1), X), 0),
                                             (Y, 1)):
                                if pnorm(R, poly):
                                    self.add(pneg(R, poly), j0 + i0c + dj,
                                             nj1, d)
        Rp = [[] for _ in range(self.ND)]
        for (j0, j1), parts in self.cells.items():
            m = pmul(R, ppow(R, T.Phi0, j0), ppow(R, T.Phi1, j1))
            for d, b in enumerate(parts):
                if pnorm(R, b): Rp[d] = padd(R, Rp[d], pmul(R, b, m))
        self.Rp = [pnorm(R, x) for x in Rp]
        self.Q = [pnorm(R, x) for x in self.Q]
        return self


def two_stage_trace(E, usum, s1sum, s2sum, cache):
    """stage 1 on ahat*ahat' (depth-0 init) -> E1IH depth parts; stage 2
    on E1IH*Chat2 with stage-1 depths inherited -> Q1 depth parts."""
    key = (usum, s1sum, s2sum)
    if key in cache: return cache[key]
    T = E.T; R = E.R
    prod = pscal(R, R["pi_pow"](usum),
                 pmul(R, ppow(R, T.Phi0, s1sum), ppow(R, T.Phi1, s2sum)))
    t1 = DepthTree(E, [(pscal(R, R["pi_pow"](usum), [R["one"]]),
                        s1sum, s2sum, 0)]).run()
    rec = dict(status1=t1.status, promo1=t1.n_promo, cons1=None,
               status2=None, promo2=None, cons2=None, q1_depth_nz=None)
    if t1.status != "OK":
        cache[key] = rec; return rec
    E1IH, E0IH = pdivmod(R, prod, T.Phi2)
    sR = []; sQ = []
    for x in t1.Rp: sR = padd(R, sR, x)
    for x in t1.Q:  sQ = padd(R, sQ, x)
    rec["cons1"] = (pnorm(R, sR) == pnorm(R, E0IH)
                    and pnorm(R, sQ) == pnorm(R, E1IH))
    init2 = []
    for d, part in enumerate(t1.Q):
        if not pnorm(R, part): continue
        for (b, i0, i1) in monomials(T, part):
            for (c, k0, k1) in monomials(T, E.Chat2):
                L, X, Y = digit_split(T, pmul(R, b, c))
                init2.append((L, i0 + k0, i1 + k1, d))
                init2.append((pscal(R, R["pi_pow"](1), X), i0 + k0,
                              i1 + k1, d))
                init2.append((Y, i0 + k0 + 1, i1 + k1, d))
    t2 = DepthTree(E, init2).run()
    rec["status2"] = t2.status; rec["promo2"] = t2.n_promo
    if t2.status == "OK":
        Q1, R1 = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
        sR2 = []; sQ2 = []
        for x in t2.Rp: sR2 = padd(R, sR2, x)
        for x in t2.Q:  sQ2 = padd(R, sQ2, x)
        rec["cons2"] = (pnorm(R, sR2) == pnorm(R, R1)
                        and pnorm(R, sQ2) == pnorm(R, Q1))
        rec["q1_depth_nz"] = [bool(pnorm(R, x)) for x in t2.Q]
    cache[key] = rec
    return rec


def run_tower(tag, d0, r0, r1, r2, r3, kind, p, design):
    t0 = time.time()
    T4 = Tower4(kind, p, d0, r0, r1, r2, r3, f"{kind},p{p},{tag}")
    E = Engine2(T4)
    C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    name = f"{tag}/{kind},p={p}"
    core = (T.g0 == 1 and T.d0 == 1)
    vis = E.vis_certs()
    e2 = T3.e2
    s2g3 = E.s2(T3.gamma3)
    u0num = T3.gamma3 - s2g3*T.gamma2
    vis["u0_integral"] = (u0num % T.e1 == 0)
    u0 = u0num // T.e1
    vis["u0_nonneg"] = (u0 >= 0)
    if not (vis["u0_integral"] and vis["u0_nonneg"]):
        viol("HARNESS", name, "u0 integrality/nonneg cert failed")
        return dict(tower=name, vis=vis, harness_event=True)
    s1u0 = eq12(u0, T.e0, T.h0)[0]
    u0mut = T3.gamma3 // T.e1
    s1u0mut = eq12(u0mut, T.e0, T.h0)[0]
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    res = dict(tower=name, E4=T4.E4, Gamma0=C.Gamma0, vis=vis, core=core,
               degPhi2=T.degPhi2, gamma3=T3.gamma3, s2gamma3=s2g3,
               gamma2=T.gamma2, u0=u0, s1u0=s1u0, u0mut=u0mut,
               s1u0mut=s1u0mut)
    cen = dict(pairs=0, track=0, e1nz=0, d1=0, d2=0, d2_hi=0, d2_edge=0,
               d3_hi=0, pred_live=0, dcx_meas=0, mism=0, q1nz=0,
               live_k1=0, live_k2=0, live_dir=0)
    cache = {}; trace_cache = {}
    mism_samples = []
    for ga in W1:
        for gb in W1:
            cen["pairs"] += 1
            sa = C.split(ga); sb = C.split(gb)
            s3a, s2a, s1a, u1a = sa[1], sa[2], sa[3], sa[7]
            s3b, s2b, s1b, u1b = sb[1], sb[2], sb[3], sb[7]
            ah, _ = anchor2(C, cache, ga)
            bh, _ = anchor2(C, cache, gb)
            E1IH, E0IH = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            e1nz = bool(pnorm(R, E1IH))
            if e1nz: cen["e1nz"] += 1
            track = (s3a == e2 - 1 and s3b == e2 - 1 and e1nz)
            lvl2 = s2a + s2b + s2g3
            pool = s1a + s1b + s1u0
            carry = pool // T.e0
            pred = track and (lvl2 + carry >= 2*T.e1)
            mut = dict(
                m1=track and (lvl2 + carry >= 2*T.e1 + 1),
                m2=track and (lvl2 + pool//(T.e0 + 1) >= 2*T.e1),
                m3=track and (lvl2 + min(carry, 1) >= 2*T.e1),   # = v1
                m4=track and (lvl2 + (s1a + s1b + s1u0mut)//T.e0
                              >= 2*T.e1))
            if track:
                cen["track"] += 1
                k = 2*T.e1 - lvl2
                if k == 1: cen["d1"] += 1
                if k == 2:
                    cen["d2"] += 1
                    if pool >= 2*T.e0: cen["d2_hi"] += 1
                    if pool == 2*T.e0 - 1: cen["d2_edge"] += 1
                if k >= 3 and pool >= 2*T.e0: cen["d3_hi"] += 1
            if pred: cen["pred_live"] += 1
            for kk in MCVIS:
                if mut[kk] != pred: MCVIS[kk] += 1
            if design: continue
            # ---------------- sealed measurement side ----------------
            dcx_meas = False
            if e1nz:
                Q1, _ = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
                if pnorm(R, Q1):
                    cen["q1nz"] += 1
                    T3sum = s3a + s3b
                    d3pl = T3sum // e2
                    dcx_meas = ((d3pl == 1 and s3a == e2 - 1
                                 and s3b == e2 - 1)
                                or (T3sum == e2 - 1 and e2 == 1))
            note("F-SHARP-2" + ("-CORE" if core else "-EXT"))
            if dcx_meas != pred:
                cen["mism"] += 1
                viol("F-SHARP-2", name,
                     f"({ga},{gb}) meas={dcx_meas} pred={pred} track={track}"
                     f" lvl2={lvl2} 2e1={2*T.e1} pool={pool} carry={carry} "
                     f"e0={T.e0} s3=({s3a},{s3b}) s2=({s2a},{s2b}) "
                     f"s1=({s1a},{s1b}) u1=({u1a},{u1b}) core={core}")
                if len(mism_samples) < 8:
                    mism_samples.append((ga, gb, dcx_meas, pred))
            if dcx_meas:
                cen["dcx_meas"] += 1
                note("F-OUTER-2")
                if not (T.g1 == 1 and s3a == e2 - 1 and s3b == e2 - 1):
                    viol("F-OUTER-2", name, f"({ga},{gb}) g1={T.g1}")
            for kk in MC:
                if mut[kk] != dcx_meas: MC[kk] += 1
            # ---------------- F-CHAIN-2 trace on live rows -------------
            if dcx_meas and T.e0 >= 2:
                rec = two_stage_trace(E, u1a + u1b, s1a + s1b, s2a + s2b,
                                      trace_cache)
                note("F-CHAIN-2")
                k = 2*T.e1 - lvl2
                if (rec["status1"] != "OK" or rec["status2"] != "OK"
                        or not rec["cons1"] or not rec["cons2"]):
                    viol("F-CHAIN-2-C1", name,
                         f"({ga},{gb}) trace incomplete/inconsistent: {rec}")
                elif k >= 1:
                    cen["live_k1" if k == 1 else "live_k2"] += 1
                    nz = rec["q1_depth_nz"]
                    low_zero = all(not nz[d] for d in range(min(k, 2)))
                    hi_nz = any(nz[d] for d in range(min(k, 2), 3))
                    if not (low_zero and hi_nz):
                        viol("F-CHAIN-2-C2", name,
                             f"({ga},{gb}) k={k} q1_depth_nz={nz} "
                             f"promo={rec['promo1']}+{rec['promo2']}")
                else:
                    cen["live_dir"] += 1
                    if not rec["q1_depth_nz"][0]:
                        viol("F-CHAIN-2-C3", name,
                             f"({ga},{gb}) direct row not clean-visible: "
                             f"q1_depth_nz={rec['q1_depth_nz']}")
    res["census"] = cen
    res["mism_samples"] = mism_samples
    mode = "design census" if design else "census"
    print(f"-- {name}: E4={T4.E4} core={core} s2g3={s2g3} s1u0={s1u0} "
          f"(u0={u0}; mut s1u0'={s1u0mut}) {mode}: {cen}; "
          f"elapsed {time.time()-t0:.1f}s")
    return res


def main():
    design = "--design" in sys.argv
    t0 = time.time()
    print("dcx3_sharp_seal_v2 — DCX3 UNIFORM CARRY LAW (v2) RESEAL"
          + (" [DESIGN MODE: IH-side only]" if design else ""))
    all_res = []
    for (tag, d0, r0, r1, r2, r3, why) in ROSTER:
        for (kind, p) in RINGS[tag]:
            all_res.append(run_tower(tag, d0, r0, r1, r2, r3, kind, p,
                                     design))
    ok = [r for r in all_res if not r.get("harness_event")]
    M1 = sum(r["census"]["d1"] for r in ok)
    M2a = sum(r["census"]["d2_hi"] for r in ok)
    M2b = sum(r["census"]["d2_edge"] for r in ok)
    M4 = sum(r["census"]["d3_hi"] for r in ok)
    print("\n== COUNTS ==")
    for k in sorted(CNT): print(f"  {k}: {CNT[k]}")
    print(f"== COVERAGE METERS == M1(deficit-1)={M1}[>=20] "
          f"M2a(deficit-2,pool>=2e0)={M2a}[>=20] "
          f"M2b(deficit-2,pool==2e0-1)={M2b}[>=5] "
          f"M4(deficit>=3,pool>=2e0)={M4}[>=10]")
    print(f"== MUTANT VISIBILITY (mut != primary) == {MCVIS}")
    if not design:
        print("== CONTROLS (mut != measured; SEPARATE) ==")
        for k in ("m1", "m2", "m3", "m4"):
            print(f"  MC-{k[1]}: {'TRIPPED' if MC[k] > 0 else 'NOT-TRIPPED'}"
                  f" (count {MC[k]})")
    print(f"== VIOLATIONS: {len(VIOL)} ==")
    for v in VIOL[:60]: print("  ", v)
    out = dict(design=design, roster=[r[0] for r in ROSTER], counts=CNT,
               meters=dict(M1=M1, M2a=M2a, M2b=M2b, M4=M4),
               mcvis=MCVIS, violations=VIOL, controls=MC,
               towers=all_res, elapsed=round(time.time() - t0, 1))
    fn = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "dcx3_sharp_v2_results.json" if not design
                      else "dcx3_sharp_v2_design.json")
    with open(fn, "w") as fh: json.dump(out, fh, indent=1, default=str)
    print(f"results -> {fn}; total elapsed {time.time()-t0:.1f}s")
    if design:
        print("DESIGN MODE COMPLETE (no verdict; no sealed leg evaluated)")
        return 0
    def n(fams): return sum(1 for v in VIOL if v[0] in fams)
    nsharp = n(("F-SHARP-2",)); nouter = n(("F-OUTER-2",))
    nchain = n(("F-CHAIN-2-C1", "F-CHAIN-2-C2", "F-CHAIN-2-C3"))
    cov = (M1 >= 20 and M2a >= 20 and M2b >= 5 and M4 >= 10)
    print(f"SHARP-LOCUS VERDICT v2 (F-SHARP-2 both-inclusions, resealed "
          f"uniform carry law, predicted-0): "
          f"{'GREEN' if nsharp == 0 else 'RED (probe SUCCESS)'} "
          f"[{nsharp} violations]")
    print(f"OUTER VERDICT v2 (predicted-0): "
          f"{'GREEN' if nouter == 0 else 'RED (probe SUCCESS)'} "
          f"[{nouter} violations]")
    print(f"CHAIN-MECHANISM VERDICT v2 (C1+C2+C3 depth-exact, "
          f"predicted-0): {'GREEN' if nchain == 0 else 'RED (probe SUCCESS)'}"
          f" [{nchain} violations]")
    print(f"BOUNDARY COVERAGE v2 (M1>=20, M2a>=20, M2b>=5, M4>=10): "
          f"{'MET' if cov else 'NOT MET'} "
          f"[M1={M1}, M2a={M2a}, M2b={M2b}, M4={M4}]")
    print(f"CONTROL VERDICT v2 (MC-1..4 incl. the refuted v1 as MC-3, "
          f"SEPARATE): "
          f"{'MET' if all(MC[k] > 0 for k in MC) else 'PARTIAL: ' + str(MC)}")
    return 0 if len(VIOL) == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
