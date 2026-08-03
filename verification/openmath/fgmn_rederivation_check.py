#!/usr/bin/env python3
"""fgmn_rederivation_check.py — FGMN TRANSCRIPTION-SCALE RE-DERIVATION unit
(synthesis-7 queue #2; charter JUNCFORGE_S2_2026-08-08.md SR3 + pass-7 F1
riders).  The NON-TEXTUAL LEG of FGMN_REDERIVATION_2026-08-08.md: numerics
as FALSIFIERS ONLY, never proofs.

SOURCE (provenance-pinned): FGMN = Fernandez-Guardia-Montes-Nart, "Residual
ideals of MacLane valuations", arXiv:1305.0775v3; PDF sha256
651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35, pinned at
docs/references/fgmn_residual_ideals_1305.0775v3.pdf.  Fresh decorrelated
extraction: `pdftotext -layout` (poppler 22.02.0), pinned at
docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt (the shared
/tmp/litunit/fgmn.txt is KNOWN CORRUPTED at Def 3.15 and is not consumed).

THE QUESTION UNDER TEST.  The compiled `SideReads` (HC2/Defs.lean:280)
window functional reads  e*sigma.w(B_j) + j*h  against gam.  The FGMN print
keys the level-i Newton polygon at the PARENT valuation (fresh extraction:
"N_i := N_{mu_{i-1},phi_i}", l.871; ordinates "Q_s := (s, mu_{i-1}(a_s
phi_i^s))", l.937-938; on-line law (13) "mu_i(a_s phi_i^s) = alpha if and
only if mu_{i-1}(a_{s_j}) = alpha_j", l.940-944; Cor 4.4(2) "the j-th
coefficient of R_{i,alpha}(g) is non-zero if and only if mu_{i-1}(a_{s_j})
= alpha_j").  In stage vocabulary at a read-pair-graded junction stage
(MovesC RegradeOf: sigmaV.wPrev = parent w; sigmaV.w = the (e*,h*)-slot-min
= e*wPrev on the coefficient carrier), the source functional is

    (CORRECTED)   e * sigma.wPrev(B_j) + j * h   vs   gam
    (COMPILED)    e * sigma.w(B_j)     + j * h   vs   gam

which agree at every e = 1 / identity-regrade frame (all compiled gate
instances) and differ exactly at graded e >= 2 junction frames (the parity
wall / C-e escapee locus).

MACHINERY: juncforge_stage1 (sealed stage-1 harness; imported, not edited)
-> grb_order2_check Towers (N-1-certified).  Same ROWS x CONFIGS roster,
same family builders, same deterministic seed 20260816 (site STRUCTURE
identical to stage 1; random digits regenerated in this run's draw order —
the battery is the same preregistered distribution, not a byte-replay).

================== PREREGISTERED ROWS (predictions sealed pre-run) =========
 R0  bug detector: D0 node-1 pattern == psi1 exactly (T5-adjacent tie) on
     every instance.                                          PREDICT 0.
 R1  CORRECTED-CLAUSE BATTERY at every deep node-1 read site (D0-D3, DA;
     the stage-1 336-site battery under the corrected clause-(ii) scale):
     Lean-shape clauses instantiated with wPrev = parent w1:
       (i-a)  gam <= e*wPrev(B_j) + j*h  at every nonzero slot;
       (i-b)  equality slots == {s0 + e*k : pat_k != 0} (pat from the
              certified side read; Cor 4.4(2) support law);
       (ii)   at every pat_k != 0: B_{s0+e*k} != 0 AND equality;
       (iii)  ord_{psi1}(pattern) == recorded mu, consecutive stride.
     PREDICT 0 violations (source satisfiable at every site).
 R2  OLD-SCALE WALL at the same sites: the COMPILED clause-(ii) equalities
     (functional e*w(B_j) + j*h with w = e*wPrev, the graded scale) admit
     NO single gam value (tested: recorded gam AND any-gam solvability).
     PREDICT 0 sites satisfiable (the JuncForge parity wall is the
     transcription artifact, at nature).
 R3  ROW-A LEAN-SHAPE INSTANTIATION (Zp, p=2, row A; f = Phi2 + 2^4):
     the exact JuncForge fiber (fA = X^2+4X+28, Phi1A = X+2): corrected
     bundle SAT with the record (e,h,gam,s0,wSide,pat,mu,vtx) ==
     (2,3,6,0,2,(1,1),1,1); compiled clause (ii) UNSAT (12 != 6 display).
     PREDICT: exact match + UNSAT.
 R4  FROM-PRINT OPERATOR: independent transcription R2_print of Defs
     3.15/3.16/3.18 (this file, from the fresh extraction displays only;
     shares only ring primitives dev/w0/eq12/field ops with the certified
     operator) == certified T.R2s pattern + j0 at every deep site; j0 ==
     floor(s(g)/e) (Cor 4.4(3)).                              PREDICT 0.
     MISREAD METER: same recursion with the corrupted-extraction epsilon
     exponent (l*s - l'*u instead of l'*s - l*u): count differing sites
     per row (reported; >0 expected on some e0>1 rows — discrimination).
 R5  EQ-(14)/D0 SOURCE SHAPE: R2_print(Phi1^s) == [1] for s in {e1, 2*e1}
     (pure key-power residual holds NO pattern data — the D0 stratum is
     degenerate IN THE SOURCE; the corrected transcription must NOT and
     does not resurrect the compiled D0 gate).                PREDICT 0.

RED DISCIPLINE: R0/R4 are bug detectors first; a RED on R1/R2/R3/R5 with
R0/R4 green is mathematics and kills the proposal as written.
"""
import os, sys, time, random, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import juncforge_stage1 as J
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_ord, fp_eval, eq12, bezout, INF,
                              Tower)

VIOL, COUNTS = [], {}
def note(row, n=1): COUNTS[row] = COUNTS.get(row, 0) + n
def viol(row, tag, detail): VIOL.append((row, tag, detail))

# ---------------------------------------------------------------------------
# FROM-PRINT residual operator (Defs 3.15/3.16/3.18, fresh extraction
# ll.910-1000), transcribed on the project 2-level chain:
#   inner level: key Phi0, pair (e0,h0), constants z1, (l0,l0p)=bezout(e0,h0)
#   outer level: key Phi1, pair (e1,h1); weights in cumulative int scale
#   (w1 = e(mu_1)*mu_1, gam = e(mu_2)*mu_2 — the project normalization).
# Def 3.15 (column-verified prime placement): eps_i(alpha) =
#   z_i ^ (l'_i * s(alpha) - l_i * u(alpha)),  (s,u) split by (12).
# Def 3.16: j-th coeff of R_{i,alpha}(g) = eps_{i-1}(alpha_j) *
#   R_{i-1,alpha_j}(a_{s_j})(z_{i-1}),  s_j = s(alpha)+j*e_i,
#   alpha_j = alpha - s_j*(w_i+lambda_i).
# Def 3.18: R_i(g) = R_{i,alpha}(g)/y^{j0}, j0 = floor(s(g)/e_i).
# ---------------------------------------------------------------------------

def R0_print(T, b, beta0):
    """R_{0,beta0}(b) evaluated at z0 in K0: residue of b/pi^beta0 (print:
    R_0(g) = g(y)/pi^alpha, evaluated at the K0 generator for d0 > 1)."""
    if not b or w0(T.R, b) != beta0:
        return None                       # off-line (strictly above)
    return T.res_digit(b, beta0)          # K0 element (tuple)

def R1_print(T, a, beta, eps_mode="C"):
    """R_{1,beta}(a)(z1) in K1 from Def 3.16 at the inner level (eps_0 == 1
    by the print's convention, l.914-915): a in-carrier of Phi1, beta the
    target cumulative w1-value; None if w1(a) > beta cannot tie."""
    K1 = T.K1
    d0v = dev(T.R, a, T.Phi0)
    s, u = eq12(beta, T.e0, T.h0)         # print (12) at the inner level
    val, zp = K1["zero"], K1["one"]
    j = 0
    while True:
        sj = s + j*T.e0
        uj = u - j*T.h0                   # print: u_j = u(alpha) - j*h_i
        if sj >= len(d0v) and uj < 0:
            break
        b = d0v[sj] if sj < len(d0v) else []
        if b and uj >= 0:
            if w0(T.R, b) < uj:
                raise AssertionError("R1_print: point below the line")
            c0 = R0_print(T, b, uj)
            if c0 is not None and any(c0):
                val = K1["add"](val, K1["mul"](K1["embed"](c0), zp))
        zp = K1["mul"](zp, T.z1)
        j += 1
        if sj >= len(d0v):
            break
    return val

def eps1_print(T, beta, eps_mode="C"):
    """Def 3.15 at the inner level: z1^(l0p*s - l0*u) [mode C, the
    column-verified print reading]; mode P = the corrupted-extraction
    misread z1^(l0*s - l0p*u)."""
    s, u = eq12(beta, T.e0, T.h0)
    expo = (T.l0p*s - T.l0*u) if eps_mode == "C" else (T.l0*s - T.l0p*u)
    return T.K1["pow"](T.z1, expo)

def R2_print(T, f, eps_mode="C"):
    """(R_{2,gamma}(f) stripped per Def 3.18) as a K1-coefficient list +
    j0 + polygon metadata, from the print recursion only."""
    d1 = dev(T.R, f, T.Phi1)
    vals = [T.w1(c) if c else INF for c in d1]
    gam = min(T.e1*vals[j] + j*T.gamma2 for j in range(len(d1))
              if vals[j] < INF)
    s2, u2 = eq12(gam, T.e1, T.h1)        # print (12) at the outer level
    att = [j for j in range(len(d1))
           if vals[j] < INF and T.e1*vals[j] + j*T.gamma2 == gam]
    j0 = (min(att) - s2)//T.e1            # print: j0 = floor(s(g)/e_i)
    assert j0 == min(att)//T.e1, "print j0 identity fails"
    coeffs = []
    for j in range(j0, (max(att) - s2)//T.e1 + 1):
        sj = s2 + j*T.e1
        a = d1[sj] if sj < len(d1) else []
        num = gam - sj*T.gamma2           # alpha_j in cumulative w1 units:
        assert num % T.e1 == 0            # e(mu_1)*alpha_j = (gam-sj*gamma2)/e1
        bj = num//T.e1
        if a and bj >= 0 and vals[sj] == bj:
            c = T.K1["mul"](eps1_print(T, bj, eps_mode), R1_print(T, a, bj))
        else:
            c = T.K1["zero"]
        coeffs.append(c)
    return fp_norm(T.K1, coeffs), j0, dict(gam=gam, att=att, vals=vals, d1=d1)

# ---------------------------------------------------------------------------
# Lean-shape clause instantiation (corrected vs compiled scale)
# ---------------------------------------------------------------------------

def site_record(T, f):
    """Node record in Lean SideReads vocabulary at the deep node-1 read:
    e, h, gam, s0, wSide, pat (certified side read), mu."""
    d1, vals, gam = T.w2_data(f)
    att = [j for j in range(len(d1))
           if vals[j] < INF and T.e1*vals[j] + j*T.gamma2 == gam]
    side, j0obs, meta = T.R2s(f)
    s0, wSide = min(att), max(att) - min(att)
    mu = fp_ord(T.K1, side, fp_norm(T.K1, list(T.psi1)))
    return dict(d1=d1, vals=vals, gam=gam, att=att, e=T.e1, h=T.gamma2,
                s0=s0, wSide=wSide, pat=side, j0obs=j0obs, mu=mu)

def check_corrected(T, rec, fam):
    """R1: the corrected clauses (i-a)/(i-b)/(ii)/(iii) at one site."""
    d1, vals, gam = rec["d1"], rec["vals"], rec["gam"]
    e, h, s0 = rec["e"], rec["h"], rec["s0"]
    note("R1")
    # (i-a) lower bound at every nonzero slot
    for j in range(len(d1)):
        if vals[j] < INF and e*vals[j] + j*h < gam:
            viol("R1", T.tag, f"[{fam}] (i-a): slot {j} below gam"); return
    # (i-b) equality slots == stride slots with pat != 0
    stride = {s0 + e*k for k in range(len(rec["pat"]))
              if not T.K1["isz"](rec["pat"][k])}
    eqset = {j for j in range(len(d1))
             if vals[j] < INF and e*vals[j] + j*h == gam}
    if eqset != stride:
        viol("R1", T.tag, f"[{fam}] (i-b): equality {sorted(eqset)} != "
                          f"pat-stride {sorted(stride)}"); return
    # (ii) digit slots nonzero + equality (equality is eqset membership)
    for k in range(len(rec["pat"])):
        if T.K1["isz"](rec["pat"][k]):
            continue
        j = s0 + e*k
        if j >= len(d1) or not d1[j] or j not in eqset:
            viol("R1", T.tag, f"[{fam}] (ii): stride slot {j} empty/off-line")
            return
    # (iii) pattern within window, ord tie recorded consistently
    if rec["wSide"] % e != 0 or (rec["wSide"]//e + 1) < len(rec["pat"]):
        viol("R1", T.tag, f"[{fam}] (iii): pattern exceeds window")

def check_compiled_unsat(T, rec, fam):
    """R2: the COMPILED clause-(ii) equalities e*(e*wPrev) + j*h = gam' have
    no solution gam' (>= 2 stride slots with distinct old-functional
    values), and fail at the recorded gam."""
    e, h, s0, gam = rec["e"], rec["h"], rec["s0"], rec["gam"]
    vals = rec["vals"]
    note("R2")
    oldvals = {e*(e*vals[s0 + e*k]) + (s0 + e*k)*h
               for k in range(len(rec["pat"]))
               if not T.K1["isz"](rec["pat"][k])}
    if len(oldvals) <= 1 and (not oldvals or oldvals == {gam}):
        viol("R2", T.tag, f"[{fam}] compiled clause (ii) SATISFIABLE "
                          f"(oldvals={sorted(oldvals)}, gam={gam})")

# ---------------------------------------------------------------------------

def main():
    t0 = time.time()
    random.seed(20260816)
    sites = 0
    misread = {}
    for kind, p in J.CONFIGS:
        for tag, d0, r0, r1 in J.ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            C = J.Composite(T)
            fams, _ = J.build_families(T, C)
            # R0 bug detector: D0 pattern == psi1
            note("R0")
            side0, _, _ = T.R2s(T.Phi2)
            if side0 != fp_norm(T.K1, list(T.psi1)):
                viol("R0", T.tag, "D0 node-1 pattern != psi1")
            for fam, f in fams:
                if fam == "D4":
                    continue
                sites += 1
                rec = site_record(T, f)
                check_corrected(T, rec, fam)
                check_compiled_unsat(T, rec, fam)
                # R4 from-print operator vs certified
                note("R4")
                pat_p, j0_p, _ = R2_print(T, f, "C")
                if pat_p != rec["pat"] or j0_p != rec["j0obs"]:
                    viol("R4", T.tag, f"[{fam}] from-print R2 != certified "
                         f"R2s (print j0={j0_p}, obs j0={rec['j0obs']})")
                pat_m, _, _ = R2_print(T, f, "P")
                if pat_m != rec["pat"]:
                    misread[tag] = misread.get(tag, 0) + 1
            # R5 eq-(14): pure key powers
            for s in (T.e1, 2*T.e1):
                note("R5")
                pat_k, _, _ = R2_print(T, ppow(T.R, T.Phi1, s), "C")
                if pat_k != [T.K1["one"]]:
                    viol("R5", T.tag, f"R2_print(Phi1^{s}) != [1]")
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done, "
              f"viol={len(VIOL)}")
    # R3 row-A Lean-shape instantiation
    note("R3")
    TA = Tower("Zp", 2, 1, (1, 1, 1), (2, 1, 1), "Zp,p=2,A")
    fA = padd(TA.R, TA.Phi2, [16])
    recA = site_record(TA, fA)
    d2 = dev(TA.R, fA, TA.Phi2)
    vtx = TA.res_digit(d2[recA["mu"]], TA.w2(d2[recA["mu"]])//TA.E2) \
        if d2[recA["mu"]] else None
    got = (recA["e"], recA["h"], recA["gam"], recA["s0"], recA["wSide"],
           tuple(k2 for k2 in
                 [tuple(c) if isinstance(c, tuple) else c
                  for c in recA["pat"]]), recA["mu"])
    print(f"ROW-A record: Phi2={pnorm(TA.R, TA.Phi2)} fA={pnorm(TA.R, fA)} "
          f"(e,h,gam,s0,wSide,mu)={got[0],got[1],got[2],got[3],got[4],got[6]}"
          f" pat={recA['pat']} vtx_digit={vtx}")
    okA = (got[0], got[1], got[2], got[3], got[4], got[6]) == (2, 3, 6, 0, 2, 1) \
        and len(recA["pat"]) == 2 \
        and all(not TA.K1["isz"](c) for c in recA["pat"]) \
        and recA["att"] == [0, 2] and vtx is not None and any(vtx)
    if not okA:
        viol("R3", TA.tag, f"row-A corrected record mismatch: {got}")
    oldA = sorted({2*(2*recA['vals'][j]) + j*3 for j in recA["att"]})
    print(f"ROW-A compiled-scale display: old functional at slots "
          f"{recA['att']} = {oldA} (needs a single gam; corrected = "
          f"{sorted({2*recA['vals'][j] + j*3 for j in recA['att']})})")
    if len(oldA) <= 1:
        viol("R3", TA.tag, "row-A compiled clause (ii) unexpectedly SAT")
    # ------------------------------- report -------------------------------
    print("=" * 74)
    rows = [("R0", "bug detector: D0 pattern == psi1", 0),
            ("R1", "CORRECTED battery (wPrev scale) at deep sites", 0),
            ("R2", "COMPILED scale UNSAT at the same sites", 0),
            ("R3", "row-A Lean-shape record + compiled UNSAT display", 0),
            ("R4", "from-print Defs 3.15/3.16/3.18 == certified R2s", 0),
            ("R5", "eq-(14) key-power law (D0 source shape)", 0)]
    all_green = True
    for row, desc, pred in rows:
        obs = sum(1 for v in VIOL if v[0] == row)
        n = COUNTS.get(row, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED":
            all_green = False
        print(f"{row} {desc:52} pred {pred}  obs {obs:3d} ({n:4d})  {verdict}")
    print(f"deep node-1 sites: {sites}")
    print(f"MISREAD-EPSILON METER (from-print mode P != certified), by row: "
          f"{dict(sorted(misread.items()))}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 20):")
        for v in VIOL[:20]:
            print("  ", v)
    print(f"TOTAL checks {sum(COUNTS.values())}  elapsed {time.time()-t0:.1f}s")
    out = dict(violations=[list(v) for v in VIOL], counts=COUNTS,
               sites=sites, misread=misread)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "fgmn_rederivation_results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    print("VERDICT:", "ALL GREEN" if all_green and not VIOL
          else "RED — see above")
    return 0 if all_green and not VIOL else 1

if __name__ == "__main__":
    sys.exit(main())
