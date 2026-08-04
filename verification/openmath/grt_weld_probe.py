#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_weld_probe.py -- GRT WELD PROBE: the W-2 lift-junction falsification runner
(the mandated FIRST unit of the weld campaign, per
docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md S3.2 / S6.(1)).

THE JUNCTION UNDER TEST (blueprint W-2, quoted): "THE LIFT JUNCTION: the
classifier's canonical key polynomial at each level equals the harness
canonical eps-corrected lift Phi_{m+1} -- or, failing byte-equality, an
explicit unit-covariance law transporting all value-layer statements across
GMN-admissible representatives."

TWO DECORRELATED LEGS (extraction-corruption rule honored):
  HARNESS LEG (committed engine, used verbatim, never edited): the Tower class
    of verification/openmath/iterlawn_pe_reimpl.py -- the sealed ITERLAWN-PE
    F2c engine (baseline 940/0 on K7 THE LAW) -- whose _build_lift(m) IS the
    canonical eps-corrected lift builder (the build_Phi2/3/4 pattern), and
    whose check_pair/gamma_checks compute the anchors, values, and the cocycle
    law c_{n+1} = zbar^delta prod_j z_j^{D_j}.
  CLASSIFIER LEG (FRESH from-print transcription; nothing imported from
    grb_order2_check.py): GMN, "Newton polygons of higher order in algebraic
    number theory" (docs/references/HigherNewton.tex), the effective
    construction of a representative of a type:
      Proposition \\label{construct}  (tex lines 1166-1258): the recursive
        prescribed-residual construction P(x), with the auxiliary side T,
        the integral split (s,u) of V at (e_{r-1},h_{r-1}), the coefficients
        c_j(y) in F_{r-2}[y] of degree < f_{r-2} with c_j(z_{r-2}) = c_j
        (unique, hence canonical), the twisted sub-targets
        phi_j(y) = y^{(l_{r-2} u_j - s_j)/e_{r-2}} c_j(y) mod psi_{r-2},
        s_j the initial abscissa of T(j), and P = sum_j P_j phi_{r-1}^{s+j e};
      Theorem \\label{phir} (tex lines 1260-1283): phi_r =
        phi_{r-1}^{e_{r-1} f_{r-1}} + P with V = e_{r-1} f_{r-1} v_r(phi_{r-1}),
        varphi(y) = c (psi_{r-1}(y) - y^{f_{r-1}}), c = c_1^{e_{r-1} f_{r-1}},
        c_1 = 1 (r = 2) or z_{r-2}^{-l_{r-2} v_{r-1}(phi_{r-1})/e_{r-2}} (r > 2);
      Definition of representative (tex line 1285) = the project's "GMN Def
        2.12" citation (docs/GMN_citations.md maps Thm 2.11/Def 2.12 to
        exactly this construction/definition pair).
    Plus the FRESH residual evaluator for the Def-2.12 CRITERION
    R_{r-1}(phi_r) ~ psi_{r-1}: Definition \\label{t(i)} (twist exponents
    t_{r-1}(i) = (s_{r-1}(a_i) - l_{r-1} u_i)/e_{r-1}), Definition
    \\label{rescoeff} (c_i = z_{r-1}^{t} R_{r-2+1...}(a_i)(z_{r-1})),
    Definition \\label{defresidual}, order-one base case (tex ~line 460:
    c_i = red(a_i/pi^{u_i})), and the valuation laws v_1(P) = min v(coeffs),
    v_r(P) = min_i (e_{r-1} v_{r-1}(a_i) + i v_r(phi_{r-1})) (Prop
    \\label{propertiesv} items 3/4), v_r(phi_r) = e_{r-1} f_{r-1} v_r(phi_{r-1})
    (eq \\label{vrphir}).
  DISPLAYED CONVENTION PINS (the print leaves them free; both legs pinned,
  independently transcribed):
    (P-ell)  GMN fixes only l_r h_r - l'_r e_r = 1 (tex line 1291); we pin the
             canonical representative 0 <= l_r < e_r (l_r = 0 at e_r = 1) --
             the same normalization class the harness bez() uses, computed
             here by an independent modular inverse.
    (P-lift) residue-class digit lifts to O are the standard digit lifts
             (0..p-1 coefficientwise), both legs.
    (P-root) both legs share the SAME root key phi_1 = Phi_0 (GMN: "phi_1 an
             arbitrary monic lift of psi_0"; the junction content is r >= 2).
    (P-index) GMN level i = harness read i-1:  (e_i,h_i,f_i)^GMN =
             (e_{i-1},h_{i-1},g_{i-1})^har, f_0 = d0, psi_i^GMN = psi[i-1]^har,
             F_i = K[i-1], z_i^GMN = z[i]^har, v_{i+1}(phi_i) = gam[i],
             v_i(phi_i) = wPhi[i-1+1]... explicitly: vkey[i] := v_i(phi_i) =
             wPhi[i-1] (harness), vnext[i] := v_{i+1}(phi_i) = gam[i].
             GMN phi_r = harness Phi_{r-1}.

ROSTER: 13 exact towers (2/3/4 reads; base rings Z_2, Z_3, F_2[[t]], F_3[[t]];
wild ramification p | e_j on 8 rows; d0 = 2 rows; g >= 2 residue growth rows
(F4/F9-capable ambients per the H7ForgeDepth2 lesson); e_i = 1 flat rows (the
[RMG]-fenced-corner genre); the three committed 4-read ITERLAWN instances
I4A/I4B/I4C verbatim) + 5 concrete wild quartic-oracle-genre shapes over Z_2/Z_3
with the OM type extracted FRESH from f by the classifier leg's own
polygon/residual machinery, PARI factorpadic ground truth per Z_p row.

========================= PREREGISTERED FAMILIES ==============================
(violation counts; any family whose observed count differs from its sealed
prediction is RED; LAW-KEYED verdicts)

F0  CHAIN-BASE (r = 2 junction, untwisted): phi_2^cls == Phi_1^har byte-equal
    on every roster tower.  PREDICTED: 0 violations.  (Both recipes reduce to
    the standard lift; a violation here = transcription bug, not mathematics.)
F1  LIFT-BYTE (THE JUNCTION, r >= 3): phi_r^cls == Phi_{r-1}^har byte-equal at
    every level r >= 3 of every tower.  SEALED IDENTITY = W-2-as-stated.
    PREDICTED (build-phase smoke disclosed below): RED -- byte-equality FAILS
    on the twist-visible towers; every failure carries the per-slot unit-ratio
    table (F1-DIAG) as the mandated diagnostic.  ANY RED here = W-2 falsified
    as byte-equality (the blueprint's branch point); the ratio table then
    decides covariance-law vs broken-transfer.
F2  ADM-ORBIT (the covariance-law existence leg, SEALED): the fresh print
    evaluator certifies EVERY harness lift Phi_{r-1}^har as a GMN Def-2.12
    representative UP TO THE PRINT'S OWN CONVENTION FREEDOM: v_r =
    e_{r-1} f_{r-1} v_r(phi_{r-1}), polygon one-sided (s_init = 0,
    s_fin = e f), and R_{r-1}(Phi^har)(y) = w * psi_{r-1}(xi y)
    coefficientwise for SOME units w, xi (recorded per level).  The xi-orbit
    is forced by the print itself: GMN pins no Bezout representative ell_i
    (tex line 1291), and shifting ell_{r-2} by e_{r-2} rescales every
    residual by a character z^{k u_i} = unit * xi^j on the side -- so the
    convention-free Def-2.12 criterion is the orbit one.  PREDICTED: 0
    violations.  A violation = harness lift NOT GMN-admissible under ANY
    lawful convention = transfer broken (the blueprint's worst branch).
F2s ADM-STRICT (recorded, NOT RED-scored): the same with xi = 1 (the pinned
    (P-ell) convention).  Under the pinned convention the harness lift may
    represent the psi-TWISTED type; the count and the per-level (xi, w) pairs
    are the unit-covariance data W-2's second branch asks for.
F2b CLS-SELF: the classifier leg satisfies its own print criterion EXACTLY:
    R_{r-1}(phi_r^cls) == c * psi_{r-1} with c the Theorem-phir constant, all
    levels, all towers.  PREDICTED: 0 violations.  (Internal validation of the
    fresh transcription; correlated-corruption guard is F4/QO, not this.)
F3  COCYCLE TRANSPORT (blueprint T2): inject the classifier lifts phi^cls into
    the committed engine (ClsTower: _build_lift returns the GMN lifts; all
    valuations/reads/anchors/cocycle then run ON classifier lifts) and run the
    committed check_pair + gamma_checks over the in-window pair grid:
      K5 = L6-(n) anchor value law; K6 = W-MULT top; K7 = THE LAW
      c_{n+1} = zbar^delta prod z_j^{D_j}; K12 = pi-shift + rho monodromy;
      (K1-K4/K13 ride along, lift-independent).
    SEALED IDENTITY: the [ILN] closed form evaluated at the same (gamma,
    gamma') holds on classifier lifts.  PREDICTED: 0 violations in EVERY
    K-family on every ClsTower (W-2's transport clause; the blueprint's
    "PREDICTION under W-2-as-stated: 0 violations").  ANY RED = the exact
    revision-scope warning the directive asks for FIRST.
F3b BASELINE CONTROL: the same battery on the harness towers.  PREDICTED: 0
    violations (the committed engine's 940/0 genre, re-confirmed on this
    roster).
F4  PARI GROUND TRUTH (Z_p rows; F_p[[t]] honestly deferred -- no PARI equal-
    characteristic entry point): for BOTH top lifts (har and cls): factorpadic
    irreducible over Q_p, and nfinit/idealprimedec gives a unique prime with
    (e,f) == (prod e_j, d0 * prod g_j).  PREDICTED: 0 mismatches.
    (The external decorrelated anchor: a garbled twist transcription generically
    BREAKS irreducibility/(e,f) -- the grb P11/P12 kill-shot genre.)
QO  CONCRETE-SHAPE LEG (real classifier data): for each shape f (x^4-2,
    x^4+4x+4, x^4+2x^2+2, x^4+12 over Q_2; x^3-3 over Q_3): the classifier leg
    extracts the OM type of f FRESH (polygon + residual + factor, level by
    level), builds phi^cls per level; the harness tower for the SAME extracted
    type builds Phi^har; then F0/F1/F2/F2b comparisons per level, and PARI
    full-type of f agrees with the extraction verdict.  PREDICTED: extraction
    == PARI on all 5 shapes (0 mismatches); lift comparisons counted in
    F0/F1/F2 above.
MUTATION CONTROLS (teeth; visibility pre-verified at build time, sealed):
MG  cls-garble: drop the print twists (c_1 := 1, texp := 0) in the classifier
    leg.  PREDICTED: the strict self-check against the TRUE Theorem-phir
    constant FAILS (>= 1 level) on EACH designated tower T2C, T3C, T3A (rows
    with nonzero true total twist -- on the low-h f_top = 1 rows the two
    dropped twists cancel exactly, texp + cexp = floor(l h/e) = 0, so the
    designation is load-bearing and pre-verified).
MH  harness-garble: rebuild the harness tower under the REFUTED Def-3.15
    P-reading (eps exponent l*s - lp*u; the grb_order2_check AMENDMENT's
    garbled-prime artifact) and run the SAME committed cocycle battery on it.
    PREDICTED: >= 1 violation on EACH designated tower T2A, T2B, T2D (e0 >= 2,
    z nontrivial -- the grb P3 multiplicativity-break genre); i.e. the F3
    machinery detects a garbled operator (pre-verified: 10-15 violations per
    designated row in the build-phase smoke).

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest): reduced-roster smoke runs
during construction (T2A/T2B/T2C/T2D/T3A/T3B/T3C/T3E/T3F + QO + mutation
visibility) showed: F0 green; F1 byte-INEQUALITY exactly at top junctions of
twist-visible rows, always with a z-monomial slot ratio (T2A r=3: slot-0
ratio z1^2; T3B r=4: z1^1; interior junctions byte-equal on the smoked rows;
hand-derivation: at an f_top = 1 top slot the GMN total twist exponent is
floor(ell*h_top/e_top-ish small) while the harness eps-exponent is
l*u - lp*s at gamma_top -- different integers, equal in the field only when
ord(z) divides the difference); F2-orbit green everywhere smoked; F2s strict
failures exactly at the F1 rows; F2b green; F3 cocycle transport 0 violations
on every smoked ClsTower; F4/QO green.  The sealed predictions above are the
blueprint's W-2 identities, NOT sanitized: F1's sealed identity is
byte-equality (predicted verdict RED-with-ratio-table), F2/F3's sealed
predictions are 0.

Deterministic (no randomness).  Exact arithmetic only.  Outputs:
grt_weld_probe_output.txt (stdout tee'd by the caller) and
grt_weld_probe_results.json.

Note (two-commit seal): lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md --
commit 1 = this runner + the note's prereg section BEFORE the battery;
commit 2 = outputs + LAW-KEYED verdict from the artifacts.
"""
import sys, os, json, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL   # the committed harness engine (verbatim)

VIOL = []      # (family, tag, detail)
COUNTS = {}
RESULTS = {'towers': {}, 'qo': {}, 'mut': {}, 'families': {}}

def note(fam, n=1):
    COUNTS[fam] = COUNTS.get(fam, 0) + n

def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)))

def modinv_ell(h, e):
    """(P-ell) pin: the canonical GMN Bezout ell with ell*h - ell'*e = 1,
    0 <= ell < e (ell = 0 at e = 1).  Fresh (independent of ITL.bez)."""
    if e == 1: return 0
    return pow(h % e, -1, e)

# ===================== THE CLASSIFIER LEG (fresh from print) =================
class GmnLeg:
    """GMN HigherNewton: types, valuations, the Prop-construct/Thm-phir
    representative chain, and the residual evaluator.  GMN levels i = 1..RANK
    with data (e_i, h_i, psi_i), f_i = deg psi_i; f_0 = deg phi_1; keys
    phi[1..RANK+1].  Residue chain F_i = Kc[i-1] (F_1 = F[y]/psibar_0),
    z_i = y-class in F_{i+1} = Kc[i].  Field/poly SUBSTRATE shared with the
    engine (ITL.GFp/Ext/PolyO -- value-level arithmetic only); every GMN
    FORMULA below is a fresh transcription with tex citations inline."""

    def __init__(self, R, d0, phi1, levels, mut_droptwist=False):
        """levels: list of (e_i, h_i, psi_i) for i = 1..RANK, psi_i a monic
        coefficient list over Kc[i-1] (tuples), psi_i(0) != 0, built against
        the chain this constructor grows.  phi1: monic O[x] poly, deg d0."""
        self.R = R; self.P = ITL.PolyO(R); self.d0 = d0
        self.mut = mut_droptwist
        self.RANK = len(levels)
        self.e = {}; self.h = {}; self.f = {0: d0}; self.psis = {}
        self.ell = {}
        p = R.p
        phibar = tuple(R.res(c, 0) for c in phi1)
        assert phibar[-1] == 1 and len(phibar) == d0 + 1
        self.Kc = {0: ITL.Ext(ITL.GFp(p), phibar)}
        self.z = {}
        for i, (ei, hi, psi) in enumerate(levels, start=1):
            self.e[i] = ei; self.h[i] = hi; self.f[i] = len(psi) - 1
            self.psis[i] = list(psi)
            self.ell[i] = modinv_ell(hi, ei)
            self.Kc[i] = ITL.Ext(self.Kc[i-1], tuple(psi))
            # z_i = class of y in F_{i+1} = Kc[i]
            self.z[i] = self.Kc[i].reduce_list(
                [self.Kc[i-1].zero(), self.Kc[i-1].one()])
        # valuation table: vkey[i] = v_i(phi_i), vnext[i] = v_{i+1}(phi_i)
        # v_1(phi_1) = 0; propertiesv item 4; eq (vrphir).
        self.vkey = {1: 0}; self.vnext = {}
        for i in range(1, self.RANK + 1):
            self.vnext[i] = self.e[i]*self.vkey[i] + self.h[i]
            self.vkey[i+1] = self.e[i]*self.f[i]*self.vnext[i]
        # the key chain
        self.phi = {1: tuple(phi1)}
        for r in range(2, self.RANK + 2):
            self.phi[r] = self._thm_phir(r)

    # ---- small helpers ----
    def _liftF1(self, c):
        """(P-lift): F_1 = Kc[0] element (tuple of GFp ints) -> O[x],
        standard digit lifts, deg < f_0."""
        return self.P.canon([self.R.liftk(int(x)) for x in c])

    def _split(self, V, i):
        """initial point (s,u) of the greatest side T in the line of slope
        -h_i/e_i with ordinate V/e_i at the origin (Prop construct):
        s = smallest nonneg integer abscissa with integer ordinate."""
        e, h = self.e[i], self.h[i]
        s = (self.ell[i]*V) % e
        u = (V - s*h)//e
        assert u*e + s*h == V, "T-side split not integral"
        return s, u

    # ---- Prop \\label{construct} (fresh) ----
    def construct(self, r, V, phicoeffs):
        """P(x) with deg P < m_r, v_r(P) = V, y^nu R_{r-1}(P) = varphi(y);
        phicoeffs = the c_j in F_{r-1} = Kc[r-2], j = 0..(< f_{r-1})."""
        em, hm = self.e[r-1], self.h[r-1]
        assert V >= em*self.f[r-1]*self.vnext[r-1], "construct hypothesis"
        s, u = self._split(V, r-1)
        P = self.P
        out = P.zero()
        for j, cj in enumerate(phicoeffs):
            if self.Kc[r-2].is_zero(cj):
                continue
            uj = u - j*hm
            kslot = s + j*em
            if r == 2:
                # P = sum_j pi^{u - j h_1} c_j(x) phi_1^{s + j e_1}
                term = P.scal(self.R.pi_pow(uj),
                              P.mul(self._liftF1(cj), P.pow(self.phi[1], kslot)))
            else:
                # V_j = u_j - (s + j e_{r-1}) v_{r-1}(phi_{r-1})
                Vj = uj - kslot*self.vkey[r-1]
                # s_j = initial abscissa of T(j) (slope lam_{r-2},
                # ordinate V_j/e_{r-2})
                sj = (self.ell[r-2]*Vj) % self.e[r-2]
                num = self.ell[r-2]*uj - sj
                assert num % self.e[r-2] == 0, "t-exponent not integral"
                texp = 0 if self.mut else (num // self.e[r-2])
                # phi_j(y) = y^{texp} c_j(y) mod psi_{r-2}  ==  the canonical
                # coordinate tuple of z_{r-2}^{texp} * c_j in F_{r-1}
                celt = self.Kc[r-2].mul(
                    ITL.fpow(self.Kc[r-2], self.z[r-2], texp), cj)
                Pj = self.construct(r-1, Vj, list(celt))
                term = P.mul(Pj, P.pow(self.phi[r-1], kslot))
            out = P.add(out, term)
        return out

    # ---- Theorem \\label{phir} (fresh) ----
    def thm_c1(self, r):
        F = self.Kc[r-2]
        if r == 2:
            return F.one()
        num = self.ell[r-2]*self.vkey[r-1]
        assert num % self.e[r-2] == 0, "c_1 exponent not integral"
        if self.mut:
            return F.one()
        return ITL.fpow(F, self.z[r-2], -(num // self.e[r-2]))

    def thm_c(self, r):
        return ITL.fpow(self.Kc[r-2], self.thm_c1(r),
                        self.e[r-1]*self.f[r-1])

    def _thm_phir(self, r):
        fm, em = self.f[r-1], self.e[r-1]
        psi = self.psis[r-1]
        F = self.Kc[r-2]
        c = self.thm_c(r)
        # varphi(y) = c (psi_{r-1}(y) - y^{f_{r-1}}): coefficients j < f_{r-1}
        phiy = [F.mul(c, psi[j]) for j in range(fm)]
        Pc = self.construct(r, self.vkey[r], phiy)
        return self.P.add(Pc, self.P.pow(self.phi[r-1], em*fm))

    # ---- the generic valuations (propertiesv items 1/3) ----
    def vgen(self, k, g):
        """v_k(g) for nonzero g in O[x]; v_1 = min coefficient valuation;
        v_k = min_i (e_{k-1} v_{k-1}(a_i) + i v_k(phi_{k-1}))."""
        g = self.P.canon(list(g))
        if not g:
            return None
        if k == 1:
            return min(self.R.val(c) for c in g if not self.R.is_zero(c))
        dv = self.P.dev(g, self.phi[k-1])
        return min(self.e[k-1]*self.vgen(k-1, a) + i*self.vnext[k-1]
                   for i, a in enumerate(dv) if a)

    def _support(self, k, g, ek=None, hk=None):
        """lambda_k-support of the phi_k-dev of g: points (i, u_i) with
        u_i = v_k(a_i phi_k^i); minimizes e_k u_i + i h_k; returns
        (dev, {i: u_i}, attained list, s_init, s_fin, minval)."""
        ek = self.e.get(k) if ek is None else ek
        hk = self.h.get(k) if hk is None else hk
        dv = self.P.dev(self.P.canon(list(g)), self.phi[k])
        pts = {}
        for i, a in enumerate(dv):
            if a:
                pts[i] = self.vgen(k, a) + i*self.vkey[k]
        m = min(ek*u + i*hk for i, u in pts.items())
        att = sorted(i for i, u in pts.items() if ek*u + i*hk == m)
        return dv, pts, att, att[0], att[-1], m

    # ---- the residual evaluator: Def t(i) + rescoeff + defresidual ----
    def rres(self, k, g, ek=None, hk=None):
        """R_{lam_k}(g)(y) in F_k[y] (coefficients in Kc[k-1]); lam_k the
        level-k slope of the type (or the provided (ek,hk) for extraction)."""
        ek = self.e.get(k) if ek is None else ek
        hk = self.h.get(k) if hk is None else hk
        dv, pts, att, s0, s1, m = self._support(k, g, ek, hk)
        Fk = self.Kc[k-1]
        d = (s1 - s0)//ek
        coeffs = [Fk.zero()]*(d+1)
        for i in att:
            assert (i - s0) % ek == 0, "on-line abscissa off grid"
            j = (i - s0)//ek
            a = dv[i]; ui = pts[i]
            if k == 1:
                # order-one residual coefficient: red(a_i / pi^{u_i})
                ci = self.Kc[0].reduce_list(
                    [self.R.res(cc, ui) for cc in a])
            else:
                # c_i = z_{k-1}^{t_{k-1}(i)} R_{k-1}(a_i)(z_{k-1}),
                # t_{k-1}(i) = (s_{k-1}(a_i) - ell_{k-1} u_i)/e_{k-1}
                _, _, _, ssub, _, _ = self._support(k-1, a)
                num = ssub - self.ell[k-1]*ui
                assert num % self.e[k-1] == 0, "t(i) not integral"
                t = num // self.e[k-1]
                Rsub = self.rres(k-1, a)
                val = Fk.zero()
                zp = Fk.one()
                for cc in Rsub:
                    val = Fk.add(val, Fk.mul(Fk.from_base(cc) if k-1 == 0
                                             else self._embed_sub(k, cc), zp))
                    zp = Fk.mul(zp, self.z[k-1])
                ci = Fk.mul(ITL.fpow(Fk, self.z[k-1], t), val)
            coeffs[j] = ci
        return coeffs

    def _embed_sub(self, k, cc):
        """F_{k-1}-element -> F_k (= Kc[k-1], an Ext over Kc[k-2])."""
        return self.Kc[k-1].from_base(cc)

    # ---- the Def-2.12 criterion on a candidate lift at level r ----
    def criterion(self, r, X):
        """returns dict: vok (v_r(X) == e f v_r(phi_{r-1})), onesided
        (support attained exactly at 0 and e*f), unit (w with R = w*psi under
        the pinned (P-ell) convention, or None), and orbit = (k, w) with
        R(y) = w * psi(xi y)-coefficientwise, xi = z_{r-1}^{k h_{r-1}} -- the
        ell-freedom orbit (shifting ell_{r-1} by e_{r-1} rescales the residual
        coordinate y by z^{h}; the print pins no ell representative, so the
        orbit is the convention-free Def-2.12 criterion)."""
        fm, em = self.f[r-1], self.e[r-1]
        res = {'vok': None, 'onesided': None, 'unit': None, 'orbit': None}
        vX = self.vgen(r, X)
        res['vok'] = (vX == self.vkey[r])
        dv, pts, att, s0, s1, m = self._support(r-1, X)
        res['onesided'] = (s0 == 0 and s1 == em*fm)
        if not (res['vok'] and res['onesided']):
            return res
        Rl = self.rres(r-1, X)
        F = self.Kc[r-2]
        psi = self.psis[r-1]
        if len(Rl) != fm + 1 or F.is_zero(Rl[fm]):
            return res
        # strict leg (pinned ell): R = w * psi
        w = Rl[fm]   # psi monic => unit = leading coefficient of R
        if all(Rl[j] == F.mul(w, psi[j]) for j in range(fm + 1)):
            res['unit'] = w
        # orbit leg: exists a unit xi with R(y) = w * psi(xi y) coefficient-
        # wise (the ell-freedom orbit is generated by such coordinate
        # rescalings; the residue fields here are tiny, so scan all units)
        for xi in F.elems():
            if F.is_zero(xi):
                continue
            wk = F.mul(Rl[fm], F.inv(ITL.fpow(F, xi, fm)))
            if all(Rl[j] == F.mul(wk, F.mul(psi[j], ITL.fpow(F, xi, j)))
                   for j in range(fm + 1)):
                res['orbit'] = (elt_repr(xi), elt_repr(wk))
                break
        return res

# ================== harness-side helpers (committed engine) ==================
class ClsTower(ITL.Tower):
    """the committed engine run ON classifier lifts: _build_lift returns the
    injected GMN chain (phi^cls_{m+2} for _build_lift(m))."""
    def __init__(self, name, R, d0, Phi0_spec, reads, psi_specs, lifts):
        self._injected = lifts
        ITL.Tower.__init__(self, name, R, d0, Phi0_spec, reads, psi_specs)
    def _build_lift(self, m):
        return self._injected[m]

class SpecTower(ITL.Tower):
    """ITL.Tower accepting ('RAW', element) psi coefficient specs (for the
    QO leg, whose extracted psi coefficients are arbitrary field elements)."""
    def _coeff(self, Kj, sp, j):
        if isinstance(sp, tuple) and sp and sp[0] == 'RAW':
            return sp[1]
        return ITL.Tower._coeff(self, Kj, sp, j)

class MutHTower(ITL.Tower):
    """MH control: the REFUTED P-reading of Def 3.15 (eps exponent
    l*s - lp*u), used ONLY to build garbled lifts for the F2-teeth test."""
    def eps(self, m, beta):
        key = (m, beta)
        if key in self._ememo:
            return self._ememo[key]
        if m == 0:
            r = self.K[0].one()
        else:
            s, u = ITL.eq12(beta, self.e[m-1], self.h[m-1])
            expo = self.l[m-1]*s - self.lp[m-1]*u     # the garbled reading
            r = ITL.fpow(self.K[m], self.z[m], expo)
        self._ememo[key] = r
        return r

def gmn_from_tower(T, mut=False):
    """classifier leg for the SAME tower datum (P-root/P-index pins)."""
    levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]
    return GmnLeg(T.R, T.d0, T.Phi[0], levels, mut_droptwist=mut)

def top_lift(T):
    """the harness top lift Phi_{n+1} (committed _build_lift at m = n)."""
    return tuple(T._build_lift(T.n))

def elt_repr(x):
    return repr(x)

def ratio_name(T, m, ratio):
    """try to express a K[m] unit as z_j^t (j <= m); else raw."""
    K = T.K[m]
    if ratio == K.one():
        return '1'
    for j in range(1, m+1):
        zj = T.embed(T.z[j], j, m) if j < m else T.z[j]
        acc = K.one()
        for t in range(1, 64):
            acc = K.mul(acc, zj)
            if acc == ratio:
                return 'z%d^%d' % (j, t)
    return 'RAW' + elt_repr(ratio)

def t1_compare(T, G, tag):
    """F0/F1/F2/F2b at every level; returns per-level records."""
    recs = []
    for r in range(2, T.NR + 2):
        m = r - 1                       # harness lift index Phi_m
        har = tuple(T.Phi[m]) if m <= T.n else top_lift(T)
        cls = tuple(G.phi[r])
        fam = 'F0' if r == 2 else 'F1'
        note(fam)
        eq = (har == cls)
        rec = {'level_r': r, 'byte_equal': eq}
        if not eq:
            if fam == 'F0':
                viol('F0', tag, 'r=2 base lift differs')
            else:
                viol('F1', tag, 'byte-inequality at r=%d (W-2-as-stated RED)' % r)
            # F1-DIAG: per-slot unit ratios in the Phi_{m-1}-dev (harness read)
            diag = []
            try:
                dvh = T.P.dev(list(har), T.Phi[m-1])
                dvc = T.P.dev(list(cls), T.Phi[m-1])
                L = max(len(dvh), len(dvc))
                for kk in range(L):
                    ah = dvh[kk] if kk < len(dvh) else ()
                    ac = dvc[kk] if kk < len(dvc) else ()
                    if not ah and not ac:
                        continue
                    if bool(ah) != bool(ac):
                        diag.append((kk, 'SUPPORT-MISMATCH'))
                        continue
                    wh = T.wlev(m-1, ah); wc = T.wlev(m-1, ac)
                    if wh != wc:
                        diag.append((kk, 'WEIGHT %s vs %s' % (wh, wc)))
                        continue
                    if m-1 >= 1:
                        rh = T.read(m-1, wh, ah); rc = T.read(m-1, wc, ac)
                        K = T.K[m-1]
                    else:
                        rh = T.read(0, wh, ah); rc = T.read(0, wc, ac)
                        K = T.K[0]
                    if K.is_zero(rh):
                        diag.append((kk, 'ZERO-READ'))
                        continue
                    ratio = K.mul(rc, K.inv(rh))
                    diag.append((kk, ratio_name(T, m-1, ratio) if m-1 >= 1
                                 else elt_repr(ratio)))
            except AssertionError as e:
                diag.append(('ASSERT', str(e)))
            rec['ratio_table'] = diag
        # F2: harness lift under the fresh Def-2.12 criterion (orbit leg
        # sealed; strict pinned-ell leg recorded as F2s)
        note('F2'); note('F2s')
        crit = G.criterion(r, list(har))
        rec['adm_har'] = {'vok': crit['vok'], 'onesided': crit['onesided'],
                          'unit_strict': elt_repr(crit['unit']),
                          'orbit': crit['orbit']}
        if not (crit['vok'] and crit['onesided']
                and crit['orbit'] is not None):
            viol('F2', tag, 'harness lift fails the ORBIT Def-2.12 criterion '
                 'at r=%d: %s' % (r, rec['adm_har']))
        if crit['unit'] is None:
            viol('F2s', tag, 'strict (pinned-ell) unit fails at r=%d '
                 '(recorded, not RED-scored)' % r)
        # F2b: cls self-check R = c * psi exactly
        note('F2b')
        critc = G.criterion(r, list(cls))
        cthm = G.thm_c(r)
        okc = (critc['vok'] and critc['onesided'] and critc['unit'] == cthm)
        rec['self_cls'] = {'vok': critc['vok'], 'onesided': critc['onesided'],
                           'unit': elt_repr(critc['unit']),
                           'c_thm': elt_repr(cthm)}
        if not okc:
            viol('F2b', tag, 'cls self-check fails at r=%d: %s'
                 % (r, rec['self_cls']))
        recs.append(rec)
    return recs

def t2_cocycle(T, tag, prefix, pairn, register=True):
    """F3/F3b: committed check_pair + gamma_checks over the window grid."""
    import collections
    C = collections.defaultdict(int)
    vv = []
    W1 = ITL.window_reps(T, pairn)
    for ga in W1:
        try:
            ITL.gamma_checks(T, ga, C, frozenset(), vv)
        except AssertionError as e:
            vv.append('%s K-ASSERT (%d): %s' % (T.name, ga, e))
        for gb in W1:
            try:
                ITL.check_pair(T, ga, gb, C, muts=frozenset(), viol=vv)
            except AssertionError as e:
                vv.append('%s K-ASSERT (%d,%d): %s' % (T.name, ga, gb, e))
    if register:
        for v in vv:
            viol(prefix, tag, v)
        note(prefix, len(W1)**2)
    return dict(C), vv

# ============================ the QO extraction leg ==========================
def qo_extract(R, fcoeffs, maxdepth=3):
    """FRESH classifier-leg OM extraction of the type of f (phi_1 = x):
    returns (leg, levels, status) with status in {'complete', 'split',
    'depth-cap', 'not-x-power'}."""
    P = ITL.PolyO(R)
    f = P.canon([c for c in fcoeffs])
    p = R.p
    fbar = [R.res(c, 0) for c in f]
    n = len(f) - 1
    if any(fbar[i] for i in range(n)) or fbar[n] != 1:
        return None, [], 'not-x-power'
    levels = []
    while True:
        leg = GmnLeg(R, 1, (R.zero(), R.one()), levels)
        k = len(levels) + 1               # working order
        if len(f) - 1 == (1 if k == 1 else
                          leg.e[k-1]*leg.f[k-1]*(len(leg.phi[k])-1) if False
                          else len(leg.phi[k]) - 1):
            return leg, levels, 'complete'   # f == its own key degree bound
        # polygon of f at level k w.r.t. phi_k: find the negative sides
        dv = P.dev(f, leg.phi[k])
        pts = {}
        for i, a in enumerate(dv):
            if a:
                pts[i] = leg.vgen(k, a) + i*leg.vkey[k]
        # lower convex hull, negative-slope portion, from abscissa 0
        items = sorted(pts.items())
        hull = []
        for it in items:
            while len(hull) >= 2:
                (x1, y1), (x2, y2) = hull[-2], hull[-1]
                if (y2 - y1)*(it[0] - x1) >= (it[1] - y1)*(x2 - x1):
                    hull.pop()
                else:
                    break
            hull.append(it)
        sides = []
        for a, b in zip(hull, hull[1:]):
            if b[1] < a[1]:
                from math import gcd
                dy = a[1] - b[1]; dx = b[0] - a[0]
                gg = gcd(dy, dx)
                sides.append((dy//gg, dx//gg, a, b))   # slope -h/e
        if len(sides) != 1:
            return leg, levels, 'split(%d sides)' % len(sides)
        hk, ek, A, B = sides[0]
        Rl = leg.rres(k, f, ek=ek, hk=hk)
        Fk = leg.Kc[k-1]
        # factor R = unit * psi^a over F_k (deg <= 2 machinery)
        d = len(Rl) - 1
        lead = Rl[d]
        mon = [Fk.mul(Fk.inv(lead), c) for c in Rl]
        roots = [x for x in Fk.elems()
                 if Fk.is_zero(_fpeval(Fk, mon, x))]
        psi = None; a = None
        if not roots:
            if d == 1:
                psi, a = mon, 1
            elif d == 2:
                psi, a = mon, 1
            else:
                return leg, levels, 'residual-deg>2-no-root'
        else:
            rt = roots[0]
            lin = [Fk.neg(rt), Fk.one()]
            acc = list(lin); aa = 1
            while aa < d:
                acc = _fpmul(Fk, acc, lin); aa += 1
                if len(acc) - 1 == d:
                    break
            if len(acc) - 1 == d and acc == mon and len(set(map(tuple, [r for r in roots]))) == 1:
                psi, a = lin, d
            elif d == 1:
                psi, a = lin, 1
            else:
                # distinct roots or mixed factorization: type splits here
                if len(roots) >= 2 and roots[0] != roots[1]:
                    return leg, levels, 'split(residual)'
                psi, a = lin, d if acc == mon else 1
                if acc != mon:
                    return leg, levels, 'split(residual)'
        if Fk.is_zero(psi[0]):
            return leg, levels, 'psi(0)=0'
        levels.append((ek, hk, psi))
        if a == 1:
            leg = GmnLeg(R, 1, (R.zero(), R.one()), levels)
            return leg, levels, 'complete'
        if len(levels) >= maxdepth:
            leg = GmnLeg(R, 1, (R.zero(), R.one()), levels)
            return leg, levels, 'depth-cap'

def _fpeval(F, L, x):
    v = F.zero()
    for c in reversed(L):
        v = F.add(F.mul(v, x), c)
    return v

def _fpmul(F, A, B):
    out = [F.zero()]*(len(A)+len(B)-1)
    for i, a in enumerate(A):
        if not F.is_zero(a):
            for j, b in enumerate(B):
                out[i+j] = F.add(out[i+j], F.mul(a, b))
    return out

# ================================ PARI leg ===================================
def pari_init():
    sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari()
        pari.allocatemem(1 << 28, silent=True)
        return pari
    except Exception as exc:
        print('WARNING: cypari2 unavailable (%s); F4 predicted rows -> RED' % exc)
        return None

def pari_ef(pari, coeffs, p, e_pred, f_pred, tag, who):
    """factorpadic irreducibility + idealprimedec (e,f) tie (fresh, minimal)."""
    note('F4')
    F = pari.Pol(list(reversed([int(c) for c in coeffs])))
    prec = 160
    fac = pari.factorpadic(F, p, prec)
    if len(fac[0]) != 1 or int(fac[1][0]) != 1:
        viol('F4', tag, '%s lift NOT irreducible over Q_%d (%d factors)'
             % (who, p, len(fac[0])))
        return False
    nf = pari.nfinit([F, [p]])
    dec = pari.idealprimedec(nf, p)
    if len(dec) != 1:
        viol('F4', tag, '%s lift: %d primes above p' % (who, len(dec)))
        return False
    e_obs, f_obs = int(dec[0][2]), int(dec[0][3])
    if (e_obs, f_obs) != (e_pred, f_pred):
        viol('F4', tag, '%s lift: (e,f)=(%d,%d) != pred (%d,%d)'
             % (who, e_obs, f_obs, e_pred, f_pred))
        return False
    return True

def pari_fulltype(pari, coeffs, p):
    """sorted (e,f) multiset of f over Q_p (fresh factorpadic+idealprimedec)."""
    F = pari.Pol(list(reversed([int(c) for c in coeffs])))
    fac = pari.factorpadic(F, p, 160)
    out = []
    for g in fac[0]:
        d = int(pari.poldegree(g))
        if d == 1:
            out.append((1, 1)); continue
        G = pari.liftall(g)
        nf = pari.nfinit([G, [p]])
        dec = pari.idealprimedec(nf, p)
        got = None
        for pr in dec:
            e0, f0 = int(pr[2]), int(pr[3])
            if e0*f0 == d:
                got = (e0, f0); break
        out.append(got if got else (int(dec[0][2]), int(dec[0][3])))
    return tuple(sorted(out))

# ================================ the roster =================================
TOWERS = [
 dict(id='T2A', ring='Zp', p=2, d0=1, Phi0=[0, 1], reads=[(2,1,2),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1]], pairn=6),                      # F4, wild p=2
 dict(id='T2B', ring='Zp', p=3, d0=1, Phi0=[0, 1], reads=[(3,1,1),(2,1,1)],
      psi=[[1,1],[('z',1,1),1]], pairn=6),                        # wild p=3
 dict(id='T2C', ring='Zp', p=3, d0=1, Phi0=[0, 1], reads=[(2,1,1),(3,2,1)],
      psi=[[1,1],[('z',1,1),1]], pairn=6),                        # wild read 1
 dict(id='T2D', ring='Fpt', p=2, d0=2, Phi0=[1, 1, 1], reads=[(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]], pairn=4),                  # F4 base, eqchar
 dict(id='T2E', ring='Zp', p=2, d0=1, Phi0=[0, 1], reads=[(1,1,2),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1]], pairn=4),                      # flat e0=1, F4
 dict(id='T2F', ring='Fpt', p=3, d0=1, Phi0=[0, 1], reads=[(3,1,1),(2,1,1)],
      psi=[[1,1],[('z',1,1),1]], pairn=6),                        # eqchar wild p=3
 dict(id='T2G', ring='Zp', p=3, d0=2, Phi0=[1, 0, 1], reads=[(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]], pairn=4),                  # F9 base
 dict(id='T3A', ring='Zp', p=2, d0=2, Phi0=[1, 1, 1],
      reads=[(2,1,1),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]], pairn=8),    # E=8 wild, F4
 dict(id='T3B', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(3,1,1),(2,1,1),(2,1,1)],
      psi=[[1,1],[1,1],[1,1]], pairn=8),                          # z-chain = -1
 dict(id='T3C', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(2,1,1),(3,2,1),(2,1,1)],
      psi=[[1,1],[1,1],[1,1]], pairn=8),                          # wild middle
 dict(id='T3D', ring='Fpt', p=2, d0=1, Phi0=[0, 1],
      reads=[(2,1,2),(2,1,1),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1],[('z',1,1),1]], pairn=8),        # F4 via g0=2
 dict(id='T3E', ring='Zp', p=2, d0=1, Phi0=[0, 1],
      reads=[(2,1,2),(1,1,1),(2,3,1)],
      psi=[[1,1,1],[('z',1,1),1],[('z',1,1),1]], pairn=8),        # flat middle
 dict(id='T3F', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(1,2,2),(3,1,1),(2,1,1)],
      psi=[[1,0,1],[('z',1,1),1],[('z',1,1),1]], pairn=8),        # e0=1 g0=2, F9
] + [dict(s, pairn=6) for s in ITL.INSTANCES[:3]]                 # I4A/I4B/I4C

QO_SHAPES = [
    ('x4-2',     2, [-2, 0, 0, 0, 1]),
    ('x4+4x+4',  2, [4, 4, 0, 0, 1]),
    ('x4+2x2+2', 2, [2, 0, 2, 0, 1]),
    ('x4+12',    2, [12, 0, 0, 0, 1]),
    ('x3-3',     3, [-3, 0, 0, 1]),
]

MUTG_DESIGNATED = ['T2C', 'T3C', 'T3A']   # nonzero true GMN twist (visible)
MUTH_DESIGNATED = ['T2A', 'T2B', 'T2D']   # e0 >= 2, z nontrivial (grb P3 genre)

# ================================== main =====================================
def run_tower(spec, pari):
    tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
    T = ITL.build_tower(spec)
    G = gmn_from_tower(T)
    rec = {'tag': tag}
    rec['t1'] = t1_compare(T, G, tag)
    # F3b baseline control on harness tower
    Cb, vb = t2_cocycle(T, tag, 'F3b', spec['pairn'])
    rec['t2_baseline'] = {'counts': {k: v for k, v in Cb.items()
                                     if k.startswith('K')},
                          'violations': len(vb)}
    # F3 on classifier lifts
    lifts = {m: tuple(G.phi[m+2]) for m in range(0, T.n)}
    try:
        R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
        psis = [ps for ps in spec['psi']]
        TC = ClsTower(tag + '/cls', R2, spec['d0'], spec['Phi0'],
                      spec['reads'], psis, lifts)
        Cc, vc = t2_cocycle(TC, tag, 'F3', spec['pairn'])
        rec['t2_cls'] = {'counts': {k: v for k, v in Cc.items()
                                    if k.startswith('K')},
                         'violations': len(vc)}
    except AssertionError as e:
        note('F3')
        viol('F3', tag, 'W2-GATE: ClsTower key gate failed: %s' % e)
        rec['t2_cls'] = {'gate_failed': str(e)}
    # F4 PARI (Zp only; both top lifts)
    if spec['ring'] == 'Zp' and pari is not None:
        E = 1; F_ = T.d0
        for (e, h, g) in spec['reads']:
            E *= e; F_ *= g
        har_top = top_lift(T)
        cls_top = tuple(G.phi[T.NR + 1])
        rec['pari'] = {
            'har': pari_ef(pari, har_top, spec['p'], E, F_, tag, 'har'),
            'cls': pari_ef(pari, cls_top, spec['p'], E, F_, tag, 'cls'),
            'pred_ef': (E, F_)}
    RESULTS['towers'][tag] = rec
    return rec

def run_qo(pari):
    for name, p, fc in QO_SHAPES:
        tag = 'QO:%s/Q%d' % (name, p)
        R = ITL.Zp(p)
        leg, levels, status = qo_extract(R, fc)
        rec = {'status': status,
               'levels': [(e, h, len(psi)-1) for (e, h, psi) in levels]}
        note('QO')
        if status != 'complete':
            rec['note'] = 'extraction stopped: %s (recorded, no tie asserted)' \
                          % status
            if pari is not None:
                rec['pari_full'] = str(pari_fulltype(pari, fc, p))
            RESULTS['qo'][tag] = rec
            continue
        E = 1; F_ = 1
        for (e, h, psi) in levels:
            E *= e; F_ *= (len(psi) - 1)
        rec['pred_ef'] = (E, F_)
        if pari is not None:
            ft = pari_fulltype(pari, fc, p)
            rec['pari_full'] = str(ft)
            deg = len(fc) - 1
            if E*F_ == deg:
                if ft != ((E, F_),):
                    viol('QO', tag, 'extraction (%d,%d) != PARI %s'
                         % (E, F_, ft))
            else:
                if (E, F_) not in ft:
                    viol('QO', tag, 'extracted type (%d,%d) not among PARI %s'
                         % (E, F_, ft))
        # lift comparison for the extracted type: harness tower on RAW psis
        reads = [(e, h, len(psi)-1) for (e, h, psi) in levels]
        psi_specs = [[('RAW', c) for c in psi] for (e, h, psi) in levels]
        try:
            T = SpecTower(tag, ITL.Zp(p), 1, [0, 1], reads, psi_specs)
            G = gmn_from_tower(T)
            rec['t1'] = t1_compare(T, G, tag)
        except AssertionError as e:
            viol('QO', tag, 'harness tower for extracted type failed: %s' % e)
        RESULTS['qo'][tag] = rec

def run_mutations():
    # MG: garbled classifier leg (c_1 := 1, texp := 0) -> the fresh
    # evaluator's strict self-check against the TRUE Theorem-phir constant
    # must fail on the designated (visible-twist) rows.
    for tid in MUTG_DESIGNATED:
        spec = next(s for s in TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MG' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = gmn_from_tower(T)          # true leg (for the constant)
        Gm = gmn_from_tower(T, mut=True)
        caught = 0
        for r in range(2, T.NR + 2):
            critc = Gm.criterion(r, list(Gm.phi[r]))
            cthm = G.thm_c(r)
            if not (critc['vok'] and critc['onesided']
                    and critc['unit'] == cthm):
                caught += 1
        note('MG')
        RESULTS['mut'][tag] = {'selfcheck_failures': caught}
        if caught == 0:
            viol('MG', tag, 'garbled cls leg passed its own self-check '
                            '(no teeth)')
    # MH: P-reading harness lifts (the refuted Def-3.15 extraction reading)
    # -> the committed cocycle battery must fire on the designated rows
    # (e0 >= 2, z nontrivial: the grb P3 multiplicativity-break genre).
    for tid in MUTH_DESIGNATED:
        spec = next(s for s in TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MH' % (spec['ring'], spec['p'], spec['id'])
        R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
        TH = MutHTower(tag, R2, spec['d0'], spec['Phi0'], spec['reads'],
                       [ps for ps in spec['psi']])
        C, vv = t2_cocycle(TH, tag, 'MHX', spec['pairn'], register=False)
        note('MH')
        RESULTS['mut'][tag] = {'cocycle_violations': len(vv),
                               'first': vv[:3]}
        if len(vv) == 0:
            viol('MH', tag, 'P-reading tower passed the cocycle battery '
                            '(no teeth)')

def main():
    t0 = time.time()
    print('grt_weld_probe -- W-2 LIFT JUNCTION falsification runner '
          '(GRT_WELD_BLUEPRINT S3.2 T1/T2)')
    print('harness leg: iterlawn_pe_reimpl.Tower._build_lift (committed, '
          'verbatim import)')
    print('classifier leg: FRESH GMN HigherNewton Prop-construct/Thm-phir '
          'transcription')
    print()
    pari = pari_init()
    for spec in TOWERS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        tA = time.time()
        run_tower(spec, pari)
        print('  [%6.1fs] %-16s done (%.1fs)' % (time.time()-t0, tag,
                                                 time.time()-tA))
    run_qo(pari)
    print('  [%6.1fs] QO shapes done' % (time.time()-t0))
    run_mutations()
    print('  [%6.1fs] mutation controls done' % (time.time()-t0))
    # ------------------------------ report ------------------------------
    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violation counts; samples in parentheses)')
    print('=' * 78)
    fams = [
        ('F0',  'CHAIN-BASE r=2: cls == har byte',            '0'),
        ('F1',  'LIFT-BYTE r>=3 (W-2-as-stated)',             'RED expected'),
        ('F2',  'ADM-ORBIT: har lift is a Def-2.12 rep',      '0'),
        ('F2s', 'ADM-STRICT (pinned ell) -- recorded only',   'recorded'),
        ('F2b', 'CLS-SELF: R(cls) == c*psi exactly',          '0'),
        ('F3',  'COCYCLE TRANSPORT on cls lifts (K5/6/7/12)', '0'),
        ('F3b', 'baseline control on har lifts',              '0'),
        ('F4',  'PARI (e,f) tie, both lifts, Zp rows',        '0'),
        ('QO',  'concrete-shape extraction vs PARI',          '0'),
        ('MG',  'teeth: garbled cls leg caught by self-check','0'),
        ('MH',  'teeth: P-reading lifts rejected by ADM',     '0'),
    ]
    all_ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        if fam == 'F1':
            verdict = ('RED(W-2 byte-equality falsified)' if obs > 0
                       else 'GREEN(W-2 byte-equality HOLDS)')
        elif fam == 'F2s':
            verdict = 'recorded(%d strict failures)' % obs
        else:
            verdict = 'GREEN' if obs == 0 else 'RED'
            if obs > 0:
                all_ok = False
        print('%-4s %-46s pred %-13s obs %5d (%5d)  %s'
              % (fam, desc, pred, obs, nsm, verdict))
    print('-' * 78)
    f1v = [v for v in VIOL if v[0] == 'F1']
    if f1v:
        print('F1 byte-inequality rows (%d) -- unit-ratio tables in the JSON;'
              % len(f1v))
        print('   first divergences:')
        for v in f1v[:20]:
            print('   %s: %s' % (v[1], v[2]))
    others = [v for v in VIOL if v[0] != 'F1']
    if others:
        print('%d NON-F1 VIOLATIONS (first 30):' % len(others))
        for v in others[:30]:
            print('  ', v)
    RESULTS['families'] = {fam: {'pred': pred,
                                 'obs': sum(1 for v in VIOL if v[0] == fam),
                                 'samples': COUNTS.get(fam, 0)}
                           for fam, desc, pred in fams}
    RESULTS['violations'] = [list(v) for v in VIOL]
    RESULTS['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_weld_probe_results.json')
    with open(out, 'w') as fh:
        json.dump(RESULTS, fh, indent=1, default=repr)
    print('TOTAL samples: %d   elapsed %.1fs   JSON: %s'
          % (sum(COUNTS.values()), time.time()-t0, out))
    n_f1 = sum(1 for v in VIOL if v[0] == 'F1')
    print()
    print('LAW-KEYED VERDICT:')
    print('  W-2 BYTE-EQUALITY: %s (%d F1 rows)'
          % ('FALSIFIED' if n_f1 else 'HOLDS', n_f1))
    print('  W-2 ADMISSIBILITY (covariance-law leg): %s'
          % ('HOLDS' if not any(v[0] == 'F2' for v in VIOL) else 'FAILS'))
    print('  W-2 COCYCLE TRANSPORT ([ILN] law on cls lifts): %s'
          % ('HOLDS' if not any(v[0] == 'F3' for v in VIOL) else 'FAILS'))
    print('  controls: %s' % ('ALL GREEN' if all_ok else 'CONTROL RED -- see above'))
    return 0

if __name__ == '__main__':
    sys.exit(main())
