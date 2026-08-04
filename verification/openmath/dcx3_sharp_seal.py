#!/usr/bin/env python3
"""dcx3_sharp_seal.py — DCX3 SHARP-LOCUS SEALED CONFIRMATION (closure
program; the gate between the RM-2 probe's measured discovery and the
engine compose's consumption of it).
Sealed preregistration = lean/notes/openmath/DCX3_SHARP_2026-08-08.md.
Two-commit seal: this file + the prereg committed BEFORE the battery runs.

THE CANDIDATE UNDER SEAL (primary; the RM-2 probe's post-run separation,
display-only there, 102/102 on the probe's roster, never before exposed
to a sealed prediction on fresh data):

    TRACK(ga,gb)  := s3 = s3' = e2 - 1  AND  E1IH != 0
    lvl2          := (s2 + s2') + s2(gamma3)
    pool          := s1 + s1' + s1(u0),   u0 := (gamma3 - s2(gamma3)*gamma2)/e1
    PRED(ga,gb)   := TRACK AND [ lvl2 >= 2*e1                       (direct)
                                 OR (lvl2 == 2*e1 - 1 AND pool >= e0) (chained) ]

against the MEASURED locus, operationalized VERBATIM as in rm2_probe.py
(the [ILN] S4.7 DCX_m definition at m = 3):

    DCX3meas := E1IH != 0 AND Q1 := quo(E1IH*Chat2, Phi2) != 0
                AND [ (delta3pl = 1 AND s3 = s3' = e2-1)
                      OR (T3 = e2-1 AND e2 = 1) ].

(Equivalence note, on record: for all e2, the locus clause of DCX3meas is
exactly TRACK's s3-clause, so DCX3meas == TRACK AND Q1 != 0.)

LEGS (all predicted-0 unless marked; any violation = probe SUCCESS):
  F-SHARP    PRED == DCX3meas pairwise on EVERY window pair (both
             inclusions; CORE = g0=1&d0=1 rows / EXT = g0>=2 or d0=2 rows
             reported split, one verdict).
  F-BOUNDARY coverage meters (design-time verified): M1 = # track rows
             with lvl2 == 2e1-1 >= 20; M2 = # boundary rows with
             pool == e0 exactly >= 20 (roster-wide).
  F-OUTER    every DCX3meas row satisfies the PROVED outer bound
             {g1 = 1 AND s3 = s3' = e2-1}.
  F-CHAIN    the u0 mechanism, traced by a clean/dirty two-stage
             reduction tree (dirty = descended through an E1-promotion
             edge): (C1) tree == division at both stages on every live
             row; (C2) on every BOUNDARY-live row the promotion edge is
             load-bearing: Q1_clean == 0, Q1_dirty != 0, promo >= 1.
             (C3, census only, no prediction: clean/dirty split of Q1 on
             DIRECT-live rows.)
Mutation controls (teeth; SEPARATE verdict; design-time visibility
verified): MC-1 direct threshold 2e1 -> 2e1+1; MC-2 boundary 2e1-1 ->
2e1-2; MC-3 pool threshold e0 -> e0+1; MC-4 the u0 formula ->
u0_mut = floor(gamma3/e1) (the gamma2-correction dropped).
DETERMINISTIC: full W1 x W1 window blocks, exact arithmetic, no
sampling, no seed. Usage: dcx3_sharp_seal.py [--design]  (--design:
tower certs + IH-side censuses/meters/visibility ONLY — no Q1, no
DCX3meas, no F-leg, no trace).
"""
import sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, INF, pdivmod)
import strata3_probe as S3MOD
import iterlawr_probe as ILP      # installs the pick_irr3 shim (disclosed)
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4, Composite4
from rm2_probe import Engine2, anchor2, digit_split, monomials, poly_key

VIOL = []
CNT = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:240]))
    if sum(1 for v in VIOL if v[0] == fam) <= 10:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:200]}")

# Fresh roster (all g2 = 1; r_j = (e_j, h_j, g_j)); shapes DISJOINT from
# the RM-2 probe's seven (no (d0,r0,r1,r2,r3) tuple repeats).
ROSTER = [
    ("DS1", 1, (2,3,1), (2,1,1), (2,3,1), (1,1,1),
     "all-e=2 with fresh h-track (h0=h2=3) + fresh p=5; headline-class "
     "boundary shape (at e1=2 every live row is chained)"),
    ("DS2", 1, (3,1,1), (4,1,1), (2,3,1), (1,1,1),
     "e1=4 NEW; h2=3 -> s2(g3)=3: direct AND boundary rows; E4=24"),
    ("DS3", 2, (2,1,1), (3,2,1), (4,1,1), (1,1,1),
     "d0=2 junk-alive + e1=3 via h1=2 (l1=2) + e2=4 NEW; E4=24"),
    ("DS4", 1, (4,1,1), (2,1,1), (3,1,1), (1,1,1),
     "e0=4 NEW pool threshold; e2=3; boundary-rich (16 rows); E4=24"),
    ("DS5", 1, (3,2,1), (3,1,1), (1,2,1), (2,1,1),
     "e2=1 track-everywhere + e3=2 (u1 in {0,1}); h2=2 -> s2(g3)=2: "
     "direct + boundary; E4=18"),
    ("DS6", 1, (1,1,1), (2,1,1), (2,1,1), (1,1,1),
     "e0=1 degenerate pool: chain clause can never fire (s1=s1(u0)=0), "
     "boundary rows predicted ALL dead"),
    ("DS7", 1, (2,1,2), (2,1,1), (2,3,1), (1,1,1),
     "g0=2 with d0=1: the g-pattern the separation never fitted, "
     "d0-channel isolated away (RM2C old-data replay disclosed in note)"),
    ("DS8", 2, (2,1,1), (2,1,2), (3,1,1), (1,1,1),
     "g1=2 negative control (E1IH expected structurally 0 -> TRACK empty) "
     "with the d0=2 junk channel given a chance to break that"),
    ("DS9", 1, (2,1,1), (1,1,1), (2,3,1), (1,1,1),
     "e1=1 degenerate: lvl2=0 always, predicate dead everywhere; tests "
     "no-live-at-e1=1 on TRACK rows reachable by promotion"),
]
RINGS = {t[0]: [("Zp", 3)] for t in ROSTER}
RINGS["DS1"] = [("Zp", 5), ("Fpt", 2)]
RINGS["DS4"].append(("Fpt", 2))
RINGS["DS5"].append(("Fpt", 2))
CAP_POPS = 3000
MC = dict(m1=0, m2=0, m3=0, m4=0)      # run-time trips (mut != measured)
MCVIS = dict(m1=0, m2=0, m3=0, m4=0)   # design visibility (mut != primary)


class TraceTree:
    """clean/dirty E1-priority reduction tree (the F-CHAIN instrument).
    Cells (j0,j1) -> [clean poly, dirty poly]; dirty = the part of the
    cell that descended through >= 1 E1-promotion edge. Same three edge
    types as rm2_probe.Tree; the split is exact linear bookkeeping, so
    R_clean+R_dirty / Q_clean+Q_dirty reproduce the canonical division
    (validated per call, C1)."""
    def __init__(self, E, init_cells):
        self.E = E; T = E.T
        self.e0g0, self.e1g1 = T.e0*T.g0, T.e1*T.g1
        self.mu1 = self.e0g0*(T.e1 + 1); self.mu0 = 2*T.e1
        self.cells = {}
        self.Qc, self.Qd = [], []
        self.pops = 0; self.status = "OK"; self.n_promo = 0
        for (b, j0, j1, dirty) in init_cells:
            self.add(b, j0, j1, dirty)
    def mu(self, j0, j1): return self.mu1*j1 + self.mu0*j0
    def add(self, b, j0, j1, dirty):
        R = self.E.R
        b = pnorm(R, b)
        if not b: return
        key = (j0, j1)
        cur = self.cells.get(key, [[], []])
        cur[1 if dirty else 0] = padd(R, cur[1 if dirty else 0], b)
        if pnorm(R, cur[0]) or pnorm(R, cur[1]): self.cells[key] = cur
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
            bc, bd = self.cells.pop((j0, j1))
            parts = [(pnorm(R, bc), False), (pnorm(R, bd), True)]
            if j0 >= self.e0g0:                       # E1
                self.n_promo += 1
                for b, dirty in parts:
                    if not b: continue
                    # promotion child: ALWAYS dirty (this IS the edge)
                    self.add(b, j0 - self.e0g0, j1 + 1, True)
                    for i, cf in E.lvl1:
                        L, X, Y = digit_split(T, pmul(R, b, cf))
                        nj0 = j0 - self.e0g0 + T.e0*i
                        for poly, dj in ((L, 0),
                                         (pscal(R, R["pi_pow"](1), X), 0),
                                         (Y, 1)):
                            if pnorm(R, poly):
                                self.add(pneg(R, poly), nj0 + dj, j1, dirty)
            else:                                     # E2
                for b, dirty in parts:
                    if not b: continue
                    ex = pmul(R, pmul(R, b, ppow(R, T.Phi0, j0)),
                              ppow(R, T.Phi1, j1 - self.e1g1))
                    if dirty: self.Qd = padd(R, self.Qd, ex)
                    else:     self.Qc = padd(R, self.Qc, ex)
                    for k, digs in E.Ck_digits.items():
                        nj1 = j1 - self.e1g1 + T.e1*k
                        for i0c, dc in digs:
                            L, X, Y = digit_split(T, pmul(R, b, dc))
                            for poly, dj in ((L, 0),
                                             (pscal(R, R["pi_pow"](1), X), 0),
                                             (Y, 1)):
                                if pnorm(R, poly):
                                    self.add(pneg(R, poly), j0 + i0c + dj,
                                             nj1, dirty)
        Rc, Rd = [], []
        R = self.E.R; T = self.E.T
        for (j0, j1), (bc, bd) in self.cells.items():
            m = pmul(R, ppow(R, T.Phi0, j0), ppow(R, T.Phi1, j1))
            if pnorm(R, bc): Rc = padd(R, Rc, pmul(R, bc, m))
            if pnorm(R, bd): Rd = padd(R, Rd, pmul(R, bd, m))
        self.Rc, self.Rd = pnorm(R, Rc), pnorm(R, Rd)
        self.Qc, self.Qd = pnorm(R, self.Qc), pnorm(R, self.Qd)
        return self


def two_stage_trace(E, usum, s1sum, s2sum, cache):
    """stage 1: reduce pi^usum Phi0^s1sum Phi1^s2sum (= ahat*ahat') ->
    (E0IH | E1IH split clean/dirty, promo1, cons1); stage 2: reduce
    E1IH*Chat2 with the stage-1 dirt inherited -> (Q1 split, promo2,
    cons2). Returns the cached trace record."""
    key = (usum, s1sum, s2sum)
    if key in cache: return cache[key]
    T = E.T; R = E.R
    prod = pscal(R, R["pi_pow"](usum),
                 pmul(R, ppow(R, T.Phi0, s1sum), ppow(R, T.Phi1, s2sum)))
    t1 = TraceTree(E, [(pscal(R, R["pi_pow"](usum), [R["one"]]),
                        s1sum, s2sum, False)]).run()
    rec = dict(status1=t1.status, promo1=t1.n_promo, cons1=None,
               status2=None, promo2=None, cons2=None,
               q1c_nz=None, q1d_nz=None)
    if t1.status != "OK":
        cache[key] = rec; return rec
    E1IH, E0IH = pdivmod(R, prod, T.Phi2)
    rec["cons1"] = (pnorm(R, padd(R, t1.Rc, t1.Rd)) == pnorm(R, E0IH)
                    and pnorm(R, padd(R, t1.Qc, t1.Qd)) == pnorm(R, E1IH))
    init2 = []
    for part, dirty in ((t1.Qc, False), (t1.Qd, True)):
        if not pnorm(R, part): continue
        for (b, i0, i1) in monomials(T, part):
            for (c, k0, k1) in monomials(T, E.Chat2):
                L, X, Y = digit_split(T, pmul(R, b, c))
                init2.append((L, i0 + k0, i1 + k1, dirty))
                init2.append((pscal(R, R["pi_pow"](1), X), i0 + k0,
                              i1 + k1, dirty))
                init2.append((Y, i0 + k0 + 1, i1 + k1, dirty))
    t2 = TraceTree(E, init2).run()
    rec["status2"] = t2.status; rec["promo2"] = t2.n_promo
    if t2.status == "OK":
        Q1, R1 = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
        rec["cons2"] = (pnorm(R, padd(R, t2.Rc, t2.Rd)) == pnorm(R, R1)
                        and pnorm(R, padd(R, t2.Qc, t2.Qd)) == pnorm(R, Q1))
        rec["q1c_nz"] = bool(pnorm(R, t2.Qc))
        rec["q1d_nz"] = bool(pnorm(R, t2.Qd))
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
        print(f"  HARNESS EVENT {name}: u0 not a nonneg integer "
              f"(gamma3={T3.gamma3}, s2g3={s2g3}, gamma2={T.gamma2})")
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
    cen = dict(pairs=0, track=0, e1nz=0, boundary=0, pool_eq_e0=0,
               direct=0, pred_live=0, dcx_meas=0, mism=0, q1nz=0,
               bnd_live=0, dir_live=0, c3_clean_nz=0, c3_clean_z=0)
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
            pred = track and (lvl2 >= 2*T.e1
                              or (lvl2 == 2*T.e1 - 1 and pool >= T.e0))
            # sealed mutants (constants of the predicate)
            mut = dict(
                m1=track and (lvl2 >= 2*T.e1 + 1
                              or (lvl2 == 2*T.e1 - 1 and pool >= T.e0)),
                m2=track and (lvl2 >= 2*T.e1
                              or (lvl2 == 2*T.e1 - 2 and pool >= T.e0)),
                m3=track and (lvl2 >= 2*T.e1
                              or (lvl2 == 2*T.e1 - 1 and pool >= T.e0 + 1)),
                m4=track and (lvl2 >= 2*T.e1
                              or (lvl2 == 2*T.e1 - 1
                                  and s1a + s1b + s1u0mut >= T.e0)))
            if track:
                cen["track"] += 1
                if lvl2 == 2*T.e1 - 1:
                    cen["boundary"] += 1
                    if pool == T.e0: cen["pool_eq_e0"] += 1
                if lvl2 >= 2*T.e1: cen["direct"] += 1
            if pred: cen["pred_live"] += 1
            for k in MCVIS:
                if mut[k] != pred: MCVIS[k] += 1
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
            note("F-SHARP" + ("-CORE" if core else "-EXT"))
            if dcx_meas != pred:
                cen["mism"] += 1
                viol("F-SHARP", name,
                     f"({ga},{gb}) meas={dcx_meas} pred={pred} track={track} "
                     f"lvl2={lvl2} 2e1={2*T.e1} pool={pool} e0={T.e0} "
                     f"s3=({s3a},{s3b}) s2=({s2a},{s2b}) s1=({s1a},{s1b}) "
                     f"u1=({u1a},{u1b}) core={core}")
                if len(mism_samples) < 8:
                    mism_samples.append((ga, gb, dcx_meas, pred))
            if dcx_meas:
                cen["dcx_meas"] += 1
                note("F-OUTER")
                if not (T.g1 == 1 and s3a == e2 - 1 and s3b == e2 - 1):
                    viol("F-OUTER", name, f"({ga},{gb}) g1={T.g1}")
            for k in MC:
                if mut[k] != dcx_meas: MC[k] += 1
            # ---------------- F-CHAIN trace on live rows ----------------
            if dcx_meas and T.e0 >= 2:
                rec = two_stage_trace(E, u1a + u1b, s1a + s1b, s2a + s2b,
                                      trace_cache)
                note("F-CHAIN")
                if (rec["status1"] != "OK" or rec["status2"] != "OK"
                        or not rec["cons1"] or not rec["cons2"]):
                    viol("F-CHAIN-C1", name,
                         f"({ga},{gb}) trace incomplete/inconsistent: {rec}")
                elif lvl2 == 2*T.e1 - 1:
                    cen["bnd_live"] += 1
                    if not (rec["q1c_nz"] is False and rec["q1d_nz"]
                            and rec["promo1"] + rec["promo2"] >= 1):
                        viol("F-CHAIN-C2", name,
                             f"({ga},{gb}) boundary-live but q1c_nz="
                             f"{rec['q1c_nz']} q1d_nz={rec['q1d_nz']} "
                             f"promo={rec['promo1']}+{rec['promo2']}")
                else:
                    cen["dir_live"] += 1
                    if rec["q1c_nz"]: cen["c3_clean_nz"] += 1
                    else:             cen["c3_clean_z"] += 1
            elif dcx_meas:
                note("chain_skipped_e0_1")
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
    print("dcx3_sharp_seal — DCX3 SHARP-LOCUS SEALED CONFIRMATION"
          + (" [DESIGN MODE: IH-side censuses/meters only — no Q1, no "
             "DCX3meas, no F-leg, no trace]" if design else ""))
    all_res = []
    for (tag, d0, r0, r1, r2, r3, why) in ROSTER:
        for (kind, p) in RINGS[tag]:
            all_res.append(run_tower(tag, d0, r0, r1, r2, r3, kind, p,
                                     design))
    ok = [r for r in all_res if not r.get("harness_event")]
    M1 = sum(r["census"]["boundary"] for r in ok)
    M2 = sum(r["census"]["pool_eq_e0"] for r in ok)
    Mdir = sum(r["census"]["direct"] for r in ok)
    print("\n== COUNTS ==")
    for k in sorted(CNT): print(f"  {k}: {CNT[k]}")
    print(f"== COVERAGE METERS == M1(boundary rows)={M1} "
          f"M2(pool==e0 rows)={M2} [both need >= 20]; direct rows={Mdir}")
    print(f"== MUTANT VISIBILITY (mut != primary, design-computable) == "
          f"{MCVIS}")
    if not design:
        print("== CONTROLS (mut != measured; SEPARATE from the law) ==")
        for k in ("m1", "m2", "m3", "m4"):
            print(f"  MC-{k[1]}: {'TRIPPED' if MC[k] > 0 else 'NOT-TRIPPED'}"
                  f" (count {MC[k]})")
    print(f"== VIOLATIONS: {len(VIOL)} ==")
    for v in VIOL[:60]: print("  ", v)
    out = dict(design=design, roster=[r[0] for r in ROSTER], counts=CNT,
               meters=dict(M1=M1, M2=M2, direct=Mdir),
               mcvis=MCVIS, violations=VIOL, controls=MC,
               towers=all_res, elapsed=round(time.time() - t0, 1))
    fn = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "dcx3_sharp_results.json" if not design
                      else "dcx3_sharp_design.json")
    with open(fn, "w") as fh: json.dump(out, fh, indent=1, default=str)
    print(f"results -> {fn}; total elapsed {time.time()-t0:.1f}s")
    if design:
        print("DESIGN MODE COMPLETE (no verdict; no sealed leg evaluated)")
        return 0
    def n(fams): return sum(1 for v in VIOL if v[0] in fams)
    nsharp = n(("F-SHARP",)); nouter = n(("F-OUTER",))
    nchain = n(("F-CHAIN-C1", "F-CHAIN-C2")); nharn = n(("HARNESS",))
    cov = (M1 >= 20 and M2 >= 20)
    print(f"SHARP-LOCUS VERDICT (F-SHARP both-inclusions, sealed primary, "
          f"predicted-0): "
          f"{'GREEN' if nsharp == 0 else 'RED (probe SUCCESS)'} "
          f"[{nsharp} violations]")
    print(f"OUTER VERDICT (F-OUTER vs the proved bound, predicted-0): "
          f"{'GREEN' if nouter == 0 else 'RED (probe SUCCESS)'} "
          f"[{nouter} violations]")
    print(f"CHAIN-MECHANISM VERDICT (F-CHAIN C1+C2, predicted-0): "
          f"{'GREEN' if nchain == 0 else 'RED (probe SUCCESS)'} "
          f"[{nchain} violations]")
    print(f"BOUNDARY COVERAGE (F-BOUNDARY, M1>=20 & M2>=20): "
          f"{'MET' if cov else 'NOT MET'} [M1={M1}, M2={M2}]")
    print(f"CONTROL VERDICT (mutation teeth MC-1..4, SEPARATE): "
          f"{'MET' if all(MC[k] > 0 for k in MC) else 'PARTIAL: ' + str(MC)}")
    if nharn:
        print(f"HARNESS EVENTS: {nharn} (run NOT clean)")
    return 0 if len(VIOL) == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
