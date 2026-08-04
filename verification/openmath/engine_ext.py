#!/usr/bin/env python3
"""engine_ext.py — ENGINE REFIT unit (2026-08-08 campaign): the standing
extension module for the two committed capability walls.

Machine leg of lean/notes/openmath/ENGINE_EXT_2026-08-08.md.  The committed
engines are consumed byte-pinned by many sealed artifacts, so they are NEVER
edited; this module extends them IN MEMORY (imports read-only + disclosed
call-time patches), with an agreement battery proving byte-exact reproduction
of every shape the committed engines support.

THE TWO WALLS (ledger 1047b48 = (W1), e01ed12 = (W2)):
  (W1) grb_order2_check.fp_irreducible raises ValueError above degree 2 and
       pick_irreducible enumerates only [b, a, 1] at g >= 2 — at g = 3 the
       committed chain SILENTLY returns a degree-2 psi0 and then hangs in
       PE.prep (the SURVDISJ-CONSTRUCT CON-WALL disclosure).  The construct
       unit's fix (fp_irr_gen / pick_irr_gen, deg <= 3) is UNIT-LOCAL in
       survdisj_construct.py.
  (W2) grb_order2_check.Tower.__init__ hardcodes a QUADRATIC phibar for every
       d0 >= 2 ([1,1,1] at p = 2 else [1,0,1]) — at d0 = 3 it silently builds
       a deg-2 root key (the (SD-YJ') SDYJ-WALL disclosure).

WHAT THIS MODULE PROVIDES (importable; no patch installed at import time):
  * fp_irreducible_gen(F, A): general-degree irreducibility over any harness
    field dict.  deg <= 2 delegates to the COMMITTED test verbatim; deg >= 3
    computes TWO independent legs and cross-checks them on every call
    (raising on disagreement — the non-textual-decorrelation discipline):
      leg D: trial division by every monic divisor of degree 1..deg//2;
      leg F: Rabin/Frobenius — x^(q^d) == x mod A and, for each prime r | d,
             gcd(x^(q^(d/r)) - x, A) = 1.
  * irr_certificate(F, A): the machine certificate (both leg verdicts, the
    witness factor when reducible, re-verified by division).
  * pick_irreducible_gen(F, g, idx): g <= 2 delegates to the COMMITTED pick
    verbatim; g >= 3 enumerates [b, a_1, .., a_(g-1), 1] with b != 0
    outermost and a_(g-1) innermost in the committed _field_elems order —
    at g = 3 this is candidate-order-identical to the construct unit's
    pick_irr_gen (verified in AGR-PICK3), one degree up it is the same
    convention continued.  Full census, idx % len wraparound (committed
    convention).
  * phibar_of(p, d0): the root-key reduction.  d0 = 1 -> X and d0 = 2 at
    p in {2, 3} -> the committed hardcodes VERBATIM; every other (p, d0) ->
    the first monic irreducible of degree d0 over F_p with nonzero constant
    term in the committed enumeration order (which at (d0=2, p in {2,3})
    reproduces the committed hardcodes — checked in AGR-TOWER).  Always
    re-verified irreducible at pick time (certificate).
  * TowerExt(G.Tower): the corrected general-d0 order-2 tower.  __init__ is
    the committed constructor with exactly two blocks generalized: (i) the
    phibar/Phi0 block routes through phibar_of + a general-degree monic lift
    (Zp: coefficients verbatim; Fpt: the committed t-noise convention — the
    x^1 coefficient gets +t — continued to all degrees, byte-identical at
    d0 <= 2), and (ii) the psi0/psi1 picks route through
    pick_irreducible_gen (byte-identical at g <= 2 by delegation).  ALL
    methods are inherited from the committed Tower unchanged, so equal
    attributes imply equal behavior; AGR-TOWER checks the attributes.
  * install(): the disclosed call-time patch for the multi-level chain —
      G.fp_irreducible  = fp_irreducible_gen
      G.pick_irreducible = pick_irreducible_gen
      strata3_probe.Tower = TowerExt
    (Tower3/4/5 and PE.Eng all construct the level-0/1 tower through
    strata3_probe's Tower binding, so this one rebind carries TowerExt
    through every engine level.)  Files on disk untouched.
  * agreement_gate(): the re-runnable LAW-KEYED agreement battery (the
    standing rule: every future unit that imports engine_ext for
    beyond-wall shapes re-runs this gate and reports its counts).

============================ SEALED PREDICTIONS ==============================
(violation counts; any family whose observed count differs is RED.  Sealed at
commit 1 of the two-commit seal, BEFORE the battery runs.  A build-phase
prototype smoke of the same logic ran pre-seal, DISCLOSED in the note; the
--shakedown mode is a crash-freedom probe only.)

EXT-PIN     md5 pins on the 13 consumed artifacts.               PREDICTED 0.
EXT-WALL    both walls reproduce from the COMMITTED objects ((W1) pick deg-2
            + ValueError; (W2) deg-2 Phi0 at d0=3) AND TowerExt clears them
            (deg-3 Phi0, certified-irreducible phibar).          PREDICTED 0
            (wall counters exactly 3: wall_pick_deg2, wall_irr_valueerror,
            wall_quadratic_phi0).
EXT-WALL3   census (measured, never gates): the committed d0=2 hardcode
            [1,0,1] is REDUCIBLE mod p for p == 1 (mod 4) (X^2+1 has a root);
            witness roots printed at p = 5, 13.  The committed engine never
            ran d0 >= 2 outside p in {2,3}; machine-lit here as a THIRD
            (latent) wall.  phibar_of picks a certified irreducible there.
AGR-IRR     fp_irreducible_gen == committed fp_irreducible on EVERY monic
            candidate of deg 1, 2 over F2, F3, F5, F4, F9.       PREDICTED 0.
AGR-CERT    on EVERY monic candidate of deg 3 over F2/F3/F4/F9 and deg 4
            over F2/F3/F4: leg D == leg F; irreducible census count ==
            the Gauss/Moebius formula (1/d) sum_{r|d} mu(r) q^(d/r) minus
            the zero-constant irreducibles (only X, deg 1 — so equal on
            deg >= 2); reducible certificates carry a dividing witness of
            degree in [1, d//2] (re-verified).                   PREDICTED 0.
AGR-PICK    pick_irreducible_gen == committed pick_irreducible at g in {1,2},
            idx in {0,1,2}, over F2/F3/F5/F4/F9.                 PREDICTED 0.
AGR-IRR3    fp_irreducible_gen == the construct unit's fp_irr_gen on every
            monic cubic over F2/F3/F4/F9.                        PREDICTED 0.
AGR-PICK3   pick_irreducible_gen == the construct unit's pick_irr_gen at
            g = 3: FULL idx scan over F2/F3/F4 (all (q^3-q)/3 picks) and
            idx in {0,1,2} over F9.                              PREDICTED 0.
AGR-TOWER   TowerExt attribute-exact vs the committed Tower (phibar, Phi0,
            psi0, Phi1, psi1, Phi2, lift_terms1, gamma1/2, degPhi1/2,
            w1Phi1, w2Phi2, l0, l0p, l1, l1p, E1, E2) on the FULL committed
            grb ROSTER x 4 base rings, mode C (40 pairs) + mode P on the
            e0 >= 2 towers C/D/E/H/J (20 pairs).                 PREDICTED 0.
AGR-ENG     multi-level agreement through install(): E.Phis / E.PhiUp /
            E.gam / E.Chat byte-exact, reference engines (committed routing;
            for g0 = 3 the construct unit's own sealed routing) vs extension
            routing, on YJ2F / YJ3FLT / SDW3-shape / C3T0F.      PREDICTED 0.
EXT-GRB     the COMMITTED order-2 law families T1-T8 + T10 (harness code
            unchanged, RNG reseeded 20260808) run on the FIRST deg >= 3 root
            keys: TowerExt d0 in {3,4} x {(Fpt,2),(Zp,2),(Fpt,3),(Zp,3)}
            with reads (2,1,1)/(2,1,1), (2,3,1)/(2,1,1), (3,1,1)/(2,3,1).
            PREDICTED 0 (incl. the T8 TOTAL-form gate).
EXT-PARI    external oracle (cypari2): on the Zp TowerExt towers at
            d0 in {3,4}: factorpadic says Phi2 irreducible over Q_p and
            idealprimedec gives ONE prime with (e, f) == (e0*e1, d0*g0*g1).
            PREDICTED 0 mismatches.  (Fpt honest deferral as in N-1.)
REB         the REBUILD leg: the three committed g0 = 3 towers C3W2F /
            C3K2AF / C3OM3F re-run through survdisj_construct.run_tower with
            the extension routing installed; the 42 committed row records
            reproduce EXACTLY (dict-equal vs the pinned
            survdisj_construct_results.json), 0 new construct-family
            violations, 0 new findings.                          PREDICTED 0.
D3-SDYJ     the FIRST d0 = 3 towers (g0 = 1; the (SD-YJ) perimeter one d0
            up, engine-dark until now): the sdyj_checks_v2 portable families
            (SDYJ-GAM / SDYJ-DIG / SDYJ-CASC / SDYJ-SUPER / SDYJ-COMP /
            SDYJ-NEP + HARNESS — the proof is d0-blind) on the roster
            D3YJ2F, D3YJ3FLT, D3YJ3FLTB, D3YJ3Z, D3YJ3F3, D3YJ4FLT (m up
            to 4, p in {2,3}, Zp + Fpt, incl. one d0 = 4 FIRST).
            PREDICTED 0 violations, 0 tower skips; companions MEASURED
            (census; every gain >= 1 is enforced by SDYJ-COMP itself).

Deterministic, exact arithmetic; the only RNG is the committed harness's own
(reseeded at EXT-GRB).  Two-commit seal: module + note predictions committed
BEFORE the sealed run; verdict appended from the artifacts.
Usage: python3 engine_ext.py [outdir]      (sealed battery)
       python3 engine_ext.py --shakedown   (crash-freedom probe, no json)
"""
import sys, os, math, time, json, hashlib, collections, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import grb_order2_check as G
from grb_order2_check import (pnorm, padd, pneg, pmul, ppow, pscal, pdivmod,
                              mk_field_base, mk_field_ext, fp_norm, fp_mul,
                              fp_divmod, fp_eval, _field_elems, bezout, eq12,
                              w0, INF)

# the committed callables, captured at import (before any patch can land)
_COMMITTED_PICK = G.pick_irreducible
_COMMITTED_IRR = G.fp_irreducible

VIOL, CNT, FINDINGS = [], {}, []
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:400]))
    print(f"VIOLATION [{fam}] {tag}: {str(detail)[:360]}")
def finding(kind, tag, detail):
    FINDINGS.append((kind, tag, detail))
    print(f"*** FINDING [{kind}] {tag}: {str(detail)[:360]}")

PINS = {
    "grb_order2_check.py":             "dab62713175363a7185211890019ae2f",
    "strata3_probe.py":                "40ecf8c01425d7d221f471766f224834",
    "iterlaw4_probe.py":               "80b4c26587b22eb1892be978aeaf2160",
    "iterlawn_diag.py":                "cd7581b7fd9df555e517b69556199ef3",
    "iterlawr_probe.py":               "a5d7d68ebc9caa3dc416bea3c71b0ca7",
    "rmengine_pe_reimpl.py":           "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "wmultdcx_stress.py":              "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py":       "bea1a43d619a3c91a9a0b2f32c0920c0",
    "empty_derive_checks.py":          "8fed92402bcffe6e0c536f1f9d847612",
    "survk2_derive_checks.py":         "d8493ab90e3578fae60032cde73a3b81",
    "survdisj_construct.py":           "d8001674768b057d9de113574ee401ff",
    "survdisj_construct_results.json": "cdf2ce6fef7d3145c50b102da6dad05d",
    "sdyj_checks_v2.py":               "d58be8b80dd01e27eaa7094fe27c4709",
}

# ================= (a) general-degree irreducibility over F_q ================
def _fp_add(F, A, B):
    n = max(len(A), len(B))
    return fp_norm(F, [F["add"](A[i] if i < len(A) else F["zero"],
                                B[i] if i < len(B) else F["zero"])
                       for i in range(n)])

def _fp_neg(F, A):
    return [F["neg"](c) for c in A]

def _fp_monic(F, A):
    A = fp_norm(F, list(A))
    if not A: return []
    inv = F["inv"](A[-1])
    return [F["mul"](inv, c) for c in A]

def fp_gcd(F, A, B):
    """monic gcd in F[y] (Euclid on fp_divmod; divisor monic-normalized)."""
    A = fp_norm(F, list(A)); B = fp_norm(F, list(B))
    while B:
        Bm = _fp_monic(F, B)
        _, r = fp_divmod(F, A, Bm)
        A, B = Bm, fp_norm(F, r)
    return _fp_monic(F, A) if A else []

def fp_powmod_x(F, n, MOD):
    """x^n mod MOD (MOD monic, deg >= 1), square-and-multiply."""
    result = [F["one"]]
    base = fp_divmod(F, [F["zero"], F["one"]], MOD)[1]
    while n:
        if n & 1:
            result = fp_divmod(F, fp_mul(F, result, base), MOD)[1]
        base = fp_divmod(F, fp_mul(F, base, base), MOD)[1]
        n >>= 1
    return fp_norm(F, result)

def _prime_divisors(d):
    out = []; n = d; f = 2
    while f * f <= n:
        if n % f == 0:
            out.append(f)
            while n % f == 0: n //= f
        f += 1
    if n > 1: out.append(n)
    return out

def irr_division_leg(F, A):
    """(irreducible?, witness factor or None): trial division by every monic
    divisor of degree 1..deg//2 in the committed _field_elems order."""
    A = fp_norm(F, list(A)); d = len(A) - 1
    elems = list(_field_elems(F))
    for db in range(1, d // 2 + 1):
        for tail in itertools.product(*([elems] * db)):
            B = list(tail) + [F["one"]]
            if not fp_norm(F, fp_divmod(F, A, B)[1]):
                return False, B
    return True, None

def irr_frobenius_leg(F, A):
    """Rabin: A (monic-normalized) irreducible over F_q iff
    x^(q^d) == x mod A and gcd(x^(q^(d/r)) - x, A) = 1 for every prime r|d."""
    A = _fp_monic(F, fp_norm(F, list(A))); d = len(A) - 1
    q = F["q"]
    xm = fp_divmod(F, [F["zero"], F["one"]], A)[1]
    if fp_norm(F, _fp_add(F, fp_powmod_x(F, q**d, A), _fp_neg(F, xm))):
        return False
    for r in _prime_divisors(d):
        sub = fp_powmod_x(F, q**(d // r), A)
        g = fp_gcd(F, fp_norm(F, _fp_add(F, sub, _fp_neg(F, xm))), A)
        if len(g) - 1 != 0:
            return False
    return True

DEG_CAP = 8   # division-leg cost fence; raise deliberately if ever needed

def irr_certificate(F, A):
    """The machine certificate: both legs + witness, cross-checked."""
    A = fp_norm(F, list(A)); d = len(A) - 1
    if d > DEG_CAP:
        raise ValueError(f"engine_ext irreducibility capped at deg {DEG_CAP}")
    if d <= 2:
        v = _COMMITTED_IRR(F, A)
        # committed deg <= 2 = root test; division leg agrees by construction
        return dict(deg=d, irreducible=v, legs=("committed",), witness=None)
    div_ok, wit = irr_division_leg(F, A)
    frob_ok = irr_frobenius_leg(F, A)
    if div_ok != frob_ok:
        raise AssertionError(f"IRR LEGS DISAGREE deg={d}: div={div_ok} "
                             f"frob={frob_ok} A={A}")
    if wit is not None:
        if fp_norm(F, fp_divmod(F, A, wit)[1]):
            raise AssertionError("witness does not divide")
        if not (1 <= len(wit) - 1 <= d // 2):
            raise AssertionError("witness degree out of range")
    return dict(deg=d, irreducible=div_ok, legs=("division", "frobenius"),
                witness=wit)

def fp_irreducible_gen(F, A):
    """General-degree irreducibility: deg <= 2 committed verbatim; deg >= 3
    the double-leg certificate (cross-checked on EVERY call)."""
    d = len(fp_norm(F, list(A))) - 1
    if d <= 2:
        return _COMMITTED_IRR(F, A)
    return irr_certificate(F, A)["irreducible"]

def pick_irreducible_gen(F, g, idx=0):
    """(idx mod #matches)-th monic irreducible of degree g over F with
    nonzero constant term.  g <= 2: the COMMITTED pick verbatim; g >= 3: the
    committed convention continued ([b, a_1, .., a_(g-1), 1], b outermost,
    a_(g-1) innermost, _field_elems order, full census)."""
    if g <= 2:
        return _COMMITTED_PICK(F, g, idx)
    matches = []
    elems = list(_field_elems(F))
    for b in elems:
        if F["isz"](b): continue
        for mid in itertools.product(*([elems] * (g - 1))):
            cand = [b] + list(mid) + [F["one"]]
            if fp_irreducible_gen(F, cand):
                matches.append(cand)
    if not matches:
        raise RuntimeError("no irreducible found")
    return matches[idx % len(matches)]

# ==================== (b) the corrected general-d0 tower =====================
def phibar_of(p, d0):
    """Root-key reduction over F_p: committed values on the committed grid,
    first certified irreducible elsewhere; always re-verified."""
    if d0 == 1:
        return [0, 1]
    if d0 == 2 and p in (2, 3):
        pb = [1, 1, 1] if p == 2 else [1, 0, 1]      # committed hardcodes
    else:
        Fp = mk_field_base(p, [0, 1])
        cand = pick_irreducible_gen(Fp, d0, idx=0)
        pb = [(c[0] if c else 0) for c in cand]
    # certificate (the class pin, re-verified at pick time)
    Fp = mk_field_base(p, [0, 1])
    rep = [((c % p),) if c % p else Fp["zero"] for c in pb[:-1]] + [Fp["one"]]
    if not fp_irreducible_gen(Fp, rep):
        raise AssertionError(f"phibar_of({p},{d0}) not irreducible: {pb}")
    return pb

class TowerExt(G.Tower):
    """The committed order-2 Tower with the (W2) block corrected: general-d0
    root key (phibar_of + general monic lift, t-noise convention continued)
    and general-degree psi picks (pick_irreducible_gen).  Everything else is
    the committed constructor verbatim; ALL methods inherited unchanged."""
    def __init__(self, kind, p, d0, r0, r1, tag, mode="C", psi1_override=None):
        self.kind, self.p, self.tag, self.mode = kind, p, tag, mode
        self._psi1_override = psi1_override
        self.R = G.mk_ring(kind, p)
        R = self.R
        self.d0 = d0
        self.e0, self.h0, self.g0 = r0
        self.e1, self.h1, self.g1 = r1
        assert math.gcd(self.e0, self.h0) == 1 and math.gcd(self.e1, self.h1) == 1
        # --- the REFIT block ((W2) corrected; committed at d0 <= 2) ---
        if d0 == 1:
            phibar = [0, 1]                          # X (committed verbatim)
            self.Phi0 = pnorm(R, [R["zero"], R["one"]])
        else:
            phibar = phibar_of(p, d0)
            if kind == "Zp":
                self.Phi0 = pnorm(R, [phibar[i] for i in range(d0)] + [1])
            else:
                # committed t-noise convention: the x^1 coefficient gets +t
                coeffs = []
                for i in range(d0):
                    if i == 1:
                        coeffs.append((phibar[1] % p, 1))
                    else:
                        coeffs.append((phibar[i] % p,) if phibar[i] % p else ())
                coeffs.append((1,))
                self.Phi0 = pnorm(R, coeffs)
        # --- committed constructor, continued verbatim (picks re-routed) ---
        self.phibar = phibar
        self.K0 = mk_field_base(p, phibar)
        self.psi0 = pick_irreducible_gen(self.K0, self.g0, idx=(self.h1) % 2)
        self.K1 = mk_field_ext(self.K0, self.psi0)
        self.z1 = self.K1["z"]
        assert not self.K1["isz"](self.z1)
        self.gamma1 = self.h0
        Phi1 = []
        self.lift_terms1 = []
        for k, c in enumerate(self.psi0):
            if self.K0["isz"](c): continue
            term = pscal(R, R["pi_pow"]((self.g0 - k) * self.h0),
                         pmul(R, self.liftK0(c), ppow(R, self.Phi0, self.e0 * k)))
            self.lift_terms1.append(term)
            Phi1 = padd(R, Phi1, term)
        self.Phi1 = Phi1
        self.degPhi1 = self.e0 * self.g0 * d0
        self.w1Phi1 = self.e0 * self.g0 * self.h0
        self.gamma2 = self.e1 * self.w1Phi1 + self.h1
        self.l0, self.l0p = bezout(self.e0, self.h0)
        self.l1, self.l1p = bezout(self.e1, self.h1)
        self.E1, self.E2 = self.e0, self.e0 * self.e1
        self.psi1 = self._psi1_override if self._psi1_override is not None \
                    else pick_irreducible_gen(self.K1, self.g1, idx=(self.h0) % 2)
        self.Phi2 = self.build_Phi2()
        self.degPhi2 = self.e1 * self.g1 * self.degPhi1
        self.w2Phi2 = self.e1 * self.g1 * self.gamma2

def install():
    """The disclosed call-time patch: route the whole committed engine chain
    (grb picks + strata3's Tower binding, hence Tower3/4/5 and PE.Eng)
    through the extension.  In-memory only; files untouched.  Idempotent."""
    import strata3_probe as S3MOD
    G.fp_irreducible = fp_irreducible_gen
    G.pick_irreducible = pick_irreducible_gen
    S3MOD.Tower = TowerExt
    note("install_calls")

# ========================= the agreement battery =============================
FIELD_GRID = ((2, [0, 1], "F2"), (3, [0, 1], "F3"), (5, [0, 1], "F5"),
              (2, [1, 1, 1], "F4"), (3, [1, 0, 1], "F9"))

TOWER_ATTRS = ["phibar", "Phi0", "psi0", "Phi1", "psi1", "Phi2",
               "lift_terms1", "gamma1", "gamma2", "degPhi1", "degPhi2",
               "w1Phi1", "w2Phi2", "l0", "l0p", "l1", "l1p", "E1", "E2"]

def check_pins():
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("EXT-PIN", fn, f"md5 {got} != pinned {want}")
        else:
            note("pins_green")

def wall_reproduction():
    """EXT-WALL: both walls from the COMMITTED objects, then TowerExt clears
    them.  EXT-WALL3: the latent p == 1 (mod 4) hardcode defect, machine-lit."""
    # (W1) pick: silent deg-2 at (F2, g=3); irr: ValueError on a cubic
    F2 = mk_field_base(2, [0, 1])
    w = _COMMITTED_PICK(F2, 3, idx=1)
    if len(w) - 1 != 2:
        viol("EXT-WALL", "W1-pick", f"committed pick at (F2,g=3) returned "
             f"deg {len(w)-1}, expected the silent deg-2 wall")
    else:
        note("wall_pick_deg2")
    try:
        _COMMITTED_IRR(F2, [F2["one"], F2["one"], F2["zero"], F2["one"]])
        viol("EXT-WALL", "W1-irr", "committed fp_irreducible accepted a cubic")
    except ValueError:
        note("wall_irr_valueerror")
    # (W2) committed Tower at d0=3 builds a deg-2 Phi0
    T = G.Tower("Fpt", 2, 3, (2, 1, 1), (2, 1, 1), "wallprobe")
    degPhi0 = len(pnorm(T.R, T.Phi0)) - 1
    if degPhi0 != 2:
        viol("EXT-WALL", "W2", f"committed Tower at d0=3 built deg Phi0 = "
             f"{degPhi0} (disclosure said 2)")
    else:
        note("wall_quadratic_phi0")
    # TowerExt clears (W2): deg-3 Phi0, certified phibar
    TE = TowerExt("Fpt", 2, 3, (2, 1, 1), (2, 1, 1), "wallclear")
    if len(pnorm(TE.R, TE.Phi0)) - 1 != 3 or len(TE.phibar) - 1 != 3:
        viol("EXT-WALL", "clear", f"TowerExt d0=3 Phi0 deg "
             f"{len(pnorm(TE.R, TE.Phi0))-1} != 3")
    else:
        note("wall_cleared_d0_3")
    # EXT-WALL3 (census): [1,0,1] = X^2+1 reducible at p == 1 (mod 4)
    for p in (5, 13):
        root = next((r for r in range(p) if (r * r + 1) % p == 0), None)
        if root is not None:
            finding("EXT-WALL3", f"p={p}", dict(
                hardcode=[1, 0, 1], root=root,
                detail=f"committed d0=2 hardcode X^2+1 factors as "
                       f"(X-{root})(X+{root}) mod {p}; phibar_of picks "
                       f"{phibar_of(p, 2)} instead (certified)"))
            note("wall3_witnesses")

def agreement_gate(full=True):
    """The LAW-KEYED agreement battery (AGR-IRR/CERT/PICK/TOWER).  Returns
    the number of NEW violations; future importing units re-run this."""
    v0 = len(VIOL)
    # ---- AGR-IRR: full deg <= 2 grids ----
    for (p, pb, nm) in FIELD_GRID:
        F = mk_field_base(p, pb)
        elems = list(_field_elems(F))
        for d in (1, 2):
            for tail in itertools.product(*([elems] * d)):
                A = list(tail) + [F["one"]]
                note("agr_irr_cases")
                if fp_irreducible_gen(F, A) != _COMMITTED_IRR(F, A):
                    viol("AGR-IRR", nm, f"deg {d} mismatch at {A}")
    # ---- AGR-CERT: double-leg + Gauss census on deg 3/4 grids ----
    grids = [(nm, p, pb, d) for (p, pb, nm) in FIELD_GRID
             for d in ((3, 4) if nm in ("F2", "F3", "F4") else
                       ((3,) if nm == "F9" else ()))]
    if not full:
        grids = [g for g in grids if g[0] in ("F2", "F3")]
    for (nm, p, pb, d) in grids:
        F = mk_field_base(p, pb)
        q = F["q"]
        elems = list(_field_elems(F))
        nirr = 0
        for tail in itertools.product(*([elems] * d)):
            A = list(tail) + [F["one"]]
            note("agr_cert_cases")
            cert = irr_certificate(F, A)     # raises on leg disagreement
            nirr += cert["irreducible"]
        # Gauss/Moebius count of monic irreducibles of degree d over F_q
        def mu(n):
            out, nn, f = 1, n, 2
            while f * f <= nn:
                if nn % f == 0:
                    nn //= f
                    if nn % f == 0: return 0
                    out = -out
                f += 1
            if nn > 1: out = -out
            return out
        gauss = sum(mu(r) * q**(d // r) for r in range(1, d + 1)
                    if d % r == 0) // d
        if nirr != gauss:
            viol("AGR-CERT", nm, f"deg {d} census {nirr} != Gauss {gauss}")
        else:
            note("agr_gauss_confirms")
    # ---- AGR-PICK: g <= 2 delegation vs committed ----
    for (p, pb, nm) in FIELD_GRID:
        F = mk_field_base(p, pb)
        for g in (1, 2):
            for idx in (0, 1, 2):
                note("agr_pick_cases")
                if pick_irreducible_gen(F, g, idx) != _COMMITTED_PICK(F, g, idx):
                    viol("AGR-PICK", nm, f"g={g} idx={idx} mismatch")
    # ---- AGR-TOWER: attribute-exact on the committed roster ----
    modeP = {"C", "D", "E", "H", "J"}
    for kind, p in (("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)):
        for (tag, d0, r0, r1) in G.ROSTER:
            for mode in (("C", "P") if tag in modeP else ("C",)):
                Tc = G.Tower(kind, p, d0, r0, r1, "ref", mode=mode)
                Te = TowerExt(kind, p, d0, r0, r1, "ext", mode=mode)
                note("agr_tower_pairs")
                bad = [a for a in TOWER_ATTRS
                       if getattr(Tc, a) != getattr(Te, a)]
                if bad:
                    viol("AGR-TOWER", f"{kind},p={p},{tag},{mode}",
                         f"attribute mismatch: {bad}")
    return len(VIOL) - v0

# ============================= the sealed battery =============================
REBUILD_TOWERS = ("C3W2F", "C3K2AF", "C3OM3F")

D3_ROSTER = [
    ("D3YJ2F",    2, "Fpt", 2, 3, [(2,1,1), (2,1,1), (2,1,1)]),
    ("D3YJ3FLT",  3, "Fpt", 2, 3, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("D3YJ3FLTB", 3, "Fpt", 2, 3, [(2,3,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("D3YJ3Z",    3, "Zp",  2, 3, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("D3YJ3F3",   3, "Fpt", 3, 3, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("D3YJ4FLT",  4, "Fpt", 2, 3, [(2,1,1), (1,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    # d0 = 4 FIRST instance (bonus; same portable families)
    ("D4YJ3FLT",  3, "Fpt", 2, 4, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
]

EXT_GRB_SHAPES = [
    (("Fpt", 2), (2, 1, 1), (2, 1, 1)),
    (("Zp", 2),  (2, 1, 1), (2, 1, 1)),
    (("Fpt", 3), (2, 3, 1), (2, 1, 1)),
    (("Zp", 3),  (3, 1, 1), (2, 3, 1)),
]

def ext_grb_leg(shake=False):
    """EXT-GRB: the committed law families on the first deg >= 3 root keys."""
    import random
    random.seed(20260808)                      # disclosed reseed
    shapes = EXT_GRB_SHAPES[:1] if shake else EXT_GRB_SHAPES
    degs = (3,) if shake else (3, 4)
    for ((kind, p), r0, r1) in shapes:
        for d0 in degs:
            tag = f"{kind},p={p},d0={d0},{r0}{r1}"
            T = TowerExt(kind, p, d0, r0, r1, tag)
            v0 = len(G.VIOL)
            G.T1_T2(T, nf=10); G.T3_T4(T, npairs=8); G.T5(T)
            G.T6(T, nB=10); G.T7(T, nf=8); G.T8(T, nf=15, ncorner=5); G.T10(T)
            note("extgrb_towers")
            for v in G.VIOL[v0:]:
                viol("EXT-GRB", tag, v)

def ext_pari_leg():
    """EXT-PARI: the external factorpadic/(e,f) oracle at d0 in {3,4}."""
    sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari()
        pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        viol("EXT-PARI", "import", f"cypari2 unavailable ({exc}) — "
             f"predicted leg cannot run")
        return
    for (p, d0, r0, r1) in ((2, 3, (2,1,1), (2,1,1)), (3, 3, (2,1,1), (2,1,1)),
                            (2, 4, (2,1,1), (1,1,1)), (3, 4, (2,1,1), (1,1,1))):
        T = TowerExt("Zp", p, d0, r0, r1, f"Zp,p={p},d0={d0}/pari")
        note("pari_towers")
        Fx = pari.Pol(list(reversed([int(c) for c in T.Phi2])))
        fac = pari.factorpadic(Fx, p, 80)
        if not (len(fac[0]) == 1 and int(fac[1][0]) == 1):
            viol("EXT-PARI", T.tag, f"Phi2 NOT irreducible over Q_{p}")
            continue
        nf = pari.nfinit([Fx, [p]])
        dec = pari.idealprimedec(nf, p)
        e_pred, f_pred = T.e0 * T.e1, T.d0 * T.g0 * T.g1
        if len(dec) != 1:
            viol("EXT-PARI", T.tag, f"{len(dec)} primes above p (pred 1)")
            continue
        e_obs, f_obs = int(dec[0][2]), int(dec[0][3])
        if (e_obs, f_obs) != (e_pred, f_pred):
            viol("EXT-PARI", T.tag,
                 f"(e,f)=({e_obs},{f_obs}) != pred ({e_pred},{f_pred})")
        else:
            note("pari_ef_confirms")
            print(f"-- PARI: {T.tag} deg Phi2 = {len(T.Phi2)-1} irreducible, "
                  f"(e,f) = ({e_obs},{f_obs}) as predicted")

def rebuild_leg(SDC, shake=False):
    """REB: the three committed g0=3 towers through the extension routing."""
    towers = REBUILD_TOWERS[:1] if shake else REBUILD_TOWERS
    rowrecs = []
    v0, f0 = len(SDC.VIOL), len(SDC.FINDINGS)
    for spec in SDC.T1_ROSTER:
        if spec[0] in towers:
            SDC.run_tower(spec, "REBUILD", rowrecs)
    dv, df = len(SDC.VIOL) - v0, len(SDC.FINDINGS) - f0
    if dv:
        viol("REB", "construct-families", f"{dv} new violations: "
             f"{SDC.VIOL[v0:v0+3]}")
    if df:
        viol("REB", "findings", f"{df} new findings (committed run had none "
             f"on these towers): {SDC.FINDINGS[f0:f0+3]}")
    skips = SDC.CNT.get("tower_skipped", 0) + SDC.CNT.get("tower_budget_skips", 0)
    if skips:
        viol("REB", "skips", f"{skips} tower skips (predicted 0)")
    ref = json.load(open(os.path.join(HERE, "survdisj_construct_results.json")))
    refrows = sorted(json.dumps(r, sort_keys=True) for r in ref["rows"]
                     if r["tower"] in towers)
    myrows = sorted(json.dumps(dict(r), sort_keys=True) for r in rowrecs)
    if refrows != myrows:
        diff = len(set(refrows) ^ set(myrows))
        viol("REB", "rows", f"row records differ: {len(refrows)} committed vs "
             f"{len(myrows)} rebuilt, {diff} non-matching")
    else:
        note("reb_rows_exact", len(myrows))
        print(f"-- REB: {len(myrows)} committed rows reproduced EXACTLY "
              f"through the extension routing ({', '.join(towers)})")
    return rowrecs

def d3_leg(SDYJ, shake=False):
    """D3-SDYJ: the first d0 >= 3 towers under the sdyj_checks_v2 portable
    families."""
    roster = D3_ROSTER[1:2] if shake else D3_ROSTER
    rowrecs, comprecs = [], []
    v0 = len(SDYJ.VIOL)
    s0 = SDYJ.CNT.get("tower_skipped", 0) + SDYJ.CNT.get("tower_budget_skips", 0)
    for spec in roster:
        SDYJ.run_tower(spec, rowrecs, comprecs, budget=600)
    for v in SDYJ.VIOL[v0:]:
        viol("D3-SDYJ", v[1], f"{v[0]}: {v[2]}")
    s1 = SDYJ.CNT.get("tower_skipped", 0) + SDYJ.CNT.get("tower_budget_skips", 0)
    if s1 - s0:
        viol("D3-SDYJ", "skips", f"{s1-s0} tower skips (predicted 0)")
    # instance verification: the towers really are deg-d0 root keys via TowerExt
    for spec in roster:
        tag, m, kind, p, d0, reads = spec
        rows = [r for r in rowrecs if r["tower"] == tag]
        note("d3_towers")
        finding("D3-INSTANCE", tag, dict(
            m=m, kind=kind, p=p, d0=d0, reads=reads,
            live_rows=len(rows),
            casc=[r["casc"] for r in rows],
            ncomp=sum(r["ncomp"] for r in rows)))
    for c in comprecs:
        finding("D3-COMP", c["tower"], dict(
            key=c["key"], gain=c["gain"], junk=c["junk"], y2=c["y2"],
            w0=c["w0"], line=c["line"], xmate=c["xmate"]))
    return rowrecs, comprecs

def verify_towerext_routing():
    """After install(): a probe Eng at d0=3 must carry a TowerExt with a
    cubic root key (the wall really is cleared through the full chain)."""
    import rmengine_pe_reimpl as PE
    E = PE.Eng(2, "Fpt", 2, 3, [(2,1,1), (2,1,1), (2,1,1)], "routeprobe")
    ok = isinstance(E.grbT, TowerExt) and len(E.Phis[0]) - 1 == 3
    if not ok:
        viol("EXT-WALL", "routing", f"install() did not carry TowerExt "
             f"through Eng: type={type(E.grbT).__name__}, "
             f"deg Phi0={len(E.Phis[0])-1}")
    else:
        note("routing_verified")

# ==================================== main ====================================
def main():
    t0 = time.time()
    SHAKE = "--shakedown" in sys.argv
    outdir = HERE
    for a in sys.argv[1:]:
        if not a.startswith("--"):
            outdir = a
    print("=" * 78)
    print("ENGINE REFIT — engine_ext " +
          ("SHAKEDOWN (crash-freedom probe)" if SHAKE else "sealed battery"))
    print("=" * 78)
    check_pins()
    wall_reproduction()
    n = agreement_gate(full=not SHAKE)
    print(f"[{time.time()-t0:6.1f}s] agreement gate: {n} violations "
          f"(pairs={CNT.get('agr_tower_pairs',0)}, "
          f"irr cases={CNT.get('agr_irr_cases',0)}, "
          f"cert cases={CNT.get('agr_cert_cases',0)}, "
          f"pick cases={CNT.get('agr_pick_cases',0)})")
    # ---- SDC import PRISTINE (its own import-time walls/agreements rerun
    #      against the committed functions), then the g=3 agreements ----
    import survdisj_construct as SDC
    if SDC.VIOL:
        viol("REB", "SDC-import", f"construct unit import-time violations: "
             f"{SDC.VIOL[:3]}")
    # AGR-IRR3 / AGR-PICK3 vs the construct unit's local extension
    for (p, pb, nm) in ((2, [0,1], "F2"), (3, [0,1], "F3"),
                        (2, [1,1,1], "F4"), (3, [1,0,1], "F9")):
        F = mk_field_base(p, pb)
        elems = list(_field_elems(F))
        for tail in itertools.product(*([elems] * 3)):
            A = list(tail) + [F["one"]]
            note("agr_irr3_cases")
            if fp_irreducible_gen(F, A) != SDC.fp_irr_gen(F, A):
                viol("AGR-IRR3", nm, f"cubic verdict mismatch at {A}")
        q = F["q"]
        idxs = range((q**3 - q) // 3) if nm in ("F2", "F3", "F4") \
               else range(3)
        for idx in idxs:
            note("agr_pick3_cases")
            if pick_irreducible_gen(F, 3, idx) != SDC.pick_irr_gen(F, 3, idx):
                viol("AGR-PICK3", nm, f"g=3 idx={idx} mismatch")
    print(f"[{time.time()-t0:6.1f}s] construct-unit agreements: "
          f"irr3={CNT.get('agr_irr3_cases',0)} pick3={CNT.get('agr_pick3_cases',0)}")
    # ---- install the extension routing (disclosed patch), verify it ----
    install()
    verify_towerext_routing()
    # ---- AGR-ENG: multi-level byte agreement ref vs ext routing ----
    # references were built through the pristine/construct routing BEFORE
    # install(); rebuilt here through the ext routing and compared
    import rmengine_pe_reimpl as PE
    import strata3_probe as S3MOD
    engspecs = [("YJ2F-A", 2, "Fpt", 2, 2, [(2,1,1),(2,1,1),(2,1,1)]),
                ("YJ3FLT-A", 3, "Fpt", 2, 2, [(2,1,1),(1,1,1),(2,1,1),(2,1,1)]),
                ("C3T0F-A", 3, "Fpt", 2, 1, [(2,1,3),(2,1,1),(2,1,1),(2,1,1)]),
                ("M2B-A", 2, "Zp", 3, 2, [(3,1,2),(2,1,1),(2,3,1)])]
    saveT = S3MOD.Tower
    for (tag, m, kind, p, d0, reads) in engspecs:
        S3MOD.Tower = G.Tower          # reference routing (committed Tower;
        Eref = PE.Eng(m, kind, p, d0, reads, tag + "/ref")   # SDC picks at g=3)
        S3MOD.Tower = TowerExt         # extension routing
        Eext = PE.Eng(m, kind, p, d0, reads, tag + "/ext")
        note("agr_eng_pairs")
        same = (Eref.Phis == Eext.Phis and Eref.PhiUp == Eext.PhiUp
                and Eref.gam == Eext.gam and Eref.Chat == Eext.Chat)
        if not same:
            viol("AGR-ENG", tag, "multi-level tower data differ ref vs ext")
    S3MOD.Tower = saveT                # = TowerExt (install() state)
    print(f"[{time.time()-t0:6.1f}s] AGR-ENG: {CNT.get('agr_eng_pairs',0)} pairs")
    # ---- EXT-GRB + EXT-PARI on the first deg >= 3 root keys ----
    ext_grb_leg(shake=SHAKE)
    print(f"[{time.time()-t0:6.1f}s] EXT-GRB: {CNT.get('extgrb_towers',0)} "
          f"towers under the committed law families")
    if not SHAKE:
        ext_pari_leg()
    # ---- REB: the committed g0=3 towers via the extension ----
    rebuild_leg(SDC, shake=SHAKE)
    # ---- D3: the first d0 >= 3 towers under the SDYJ portable families ----
    import sdyj_checks_v2 as SDYJ
    d3rows, d3comps = d3_leg(SDYJ, shake=SHAKE)
    # ------------------------------- report ---------------------------------
    print("=" * 78)
    fams = ["EXT-PIN", "EXT-WALL", "AGR-IRR", "AGR-CERT", "AGR-PICK",
            "AGR-IRR3", "AGR-PICK3", "AGR-TOWER", "AGR-ENG", "EXT-GRB",
            "EXT-PARI", "REB", "D3-SDYJ"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    fk = collections.Counter(k for (k, _, _) in FINDINGS)
    print("FINDINGS census:", dict(sorted(fk.items())))
    print("counters:", {k: CNT[k] for k in sorted(CNT)})
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    print(f"VERDICT: {'ALL GREEN' if not VIOL else 'RED — see above'}")
    if not SHAKE:
        out = dict(final=True, violations=VIOL, findings=FINDINGS,
                   counters=CNT, d3_rows=d3rows, d3_companions=d3comps,
                   elapsed=el)
        with open(os.path.join(outdir, "engine_ext_results.json"), "w") as f:
            json.dump(out, f, indent=1, default=str)
        print("results -> engine_ext_results.json")
    return 0 if not VIOL else 1

if __name__ == "__main__":
    sys.exit(main())
