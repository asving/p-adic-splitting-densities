/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-E0 — THE ZpBridge COUNTERMODEL GATE (bridge campaign BP1, RISK R1; runs FIRST)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.6 (†11f) /
§4 group E / §5 R1, and `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (Q2: the
`MovesT.ramIdx`/`resDeg` repair path is signed off CONDITIONAL on this unit's
compiled countermodel — a fence event).

SEALED PREDICTION (recorded before any proving):
take p = 3, c = −1 (a non-square unit: p ≡ 3 mod 4), h := X² − p²·c = X² + 9 over
ℤ_[3].  Then
  (i)   h is monic of natDegree 2 and X² + 9 is irreducible over ℚ_3
        (roots ±3√−1, and −1 is not a square in ℚ_3);
  (ii)  `AdjoinRoot h = ℤ_3[π], π² = −9` IS a local ring (E0a): R/(3) =
        𝔽_3[X]/(X²) is local and 3 lies in the Jacobson radical of the finite
        ℤ_3-algebra R, so R has the unique maximal ideal m = (3, π);
  (iii) `MovesT.ramIdx h = 1` (E0b): (3) ≤ m but 3 ∉ m² = (9, 3π)
        (else 1 = 3a + πb ∈ m), so sSup {k | (3) ≤ m^k} = 1;
  (iv)  `MovesT.resDeg h = 1` (E0c): R/m = 𝔽_3[X]/(X, X²) = 𝔽_3, inertiaDeg 1;
  (v)   hence the aggregate degree conjunct of `ZpBridge.zf_factor` FAILS at
        g := h: the unique admissible factor multiset is {h} (monic ℚ_p
        factorizations are unique and `Polynomial.map PadicInt.Coe.ringHom` is
        injective), and {ramIdx h · resDeg h} = {1} ≠ {2} = {natDegree h} — so
        NO `ZpBridge 2 3 X` instance exists, for ANY classifier X (E0d).
TRUE INVARIANTS for contrast: ℚ_3(√−1)/ℚ_3 is the unramified quadratic extension,
(e, f) = (1, 2).  `ℤ_3[3√−1]` is a NON-MAXIMAL order, and `MovesT.ramIdx/resDeg`
read the ORDER's `IsLocalRing`-dispatched invariants, not the field's — exactly
blueprint finding R1.

DISPOSITION either way: if the pieces below PROVE, Q2's repair (re-point
`ramIdx`/`resDeg` at the valuation ring of the field `AdjoinRoot (h.map Coe)`) is
triggered and E5–E7 stay gated until it lands; if a piece REFUTES (a Mathlib
convention saves the aggregate), the deliverable is the refutation memo and E5–E7
un-gate.  CROSS-AREA FENCE (the M1 soundness lesson): once this countermodel
COMPILES sorry-free it must NOT coexist with an un-repaired sorried
`zf_factor`-instance universal — the Q2 repair lands in the same window.

Units: E0a `e0_isLocalRing` · E0b `e0_ramIdx` · E0c `e0_resDeg` ·
E0d `e0_zf_factor_false` + `e0_no_zpBridge`.  Deps: none (front-runner).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- The countermodel polynomial (†11f): h := X² − p²·c at p = 3, c = −1, i.e.
    X² + 9 over ℤ_[3].  Monic, degree 2, ℚ_3-irreducible; `AdjoinRoot e0Poly` is
    the non-maximal order ℤ_3[3√−1]. -/
noncomputable def e0Poly : Polynomial ℤ_[3] := X ^ 2 + C 9

/-- E0 piece: e0Poly is monic (leading coefficient 1 in degree 2). -/
theorem e0Poly_monic : e0Poly.Monic := sorry

/-- E0 piece: natDegree e0Poly = 2. -/
theorem e0Poly_natDegree : e0Poly.natDegree = 2 := sorry

/-- E0 piece: X² + 9 is irreducible over ℚ_3 — its roots ±3√−1 need √−1, and −1
    is not a square in ℚ_3 (not a square in 𝔽_3; p odd, unit square lifting). -/
theorem e0Poly_irreducible : Irreducible (e0Poly.map PadicInt.Coe.ringHom) := sorry

/-- E0a — LOCALITY of the order: `AdjoinRoot e0Poly = ℤ_3[π], π² = −9` is local
    (m = (3, π); R/(3) = 𝔽_3[X]/(X²) is local and 3 is in the Jacobson radical of
    the finite ℤ_3-algebra).  NOTE: this is the piece that makes the junk
    dispatch of `MovesT.ramIdx`/`resDeg` FIRE, so the countermodel reads the
    order's invariants, not junk 0. -/
theorem e0_isLocalRing : IsLocalRing (AdjoinRoot e0Poly) := sorry

/-- E0b — the order's ramification read is 1: (3) ≤ m = (3, π) but
    3 ∉ m² = (9, 3π) (else 1 = 3a + πb ∈ m), so
    `Ideal.ramificationIdx (max ℤ_3) (max R) = sSup {k | (3) ≤ m^k} = 1`. -/
theorem e0_ramIdx : MovesT.ramIdx e0Poly = 1 := sorry

/-- E0c — the order's residue read is 1: R/m = 𝔽_3[X]/(X, X²) = 𝔽_3, so
    inertiaDeg = 1.  (The FIELD's residue degree is 2 — the order is not maximal;
    that contrast is the whole finding.) -/
theorem e0_resDeg : MovesT.resDeg e0Poly = 1 := sorry

/-- E0d — THE COUNTERMODEL: no factor multiset satisfies `zf_factor`'s conjuncts
    1, 2 and the (3∧4)-composite at g := e0Poly.  Route: by conjuncts 1–2 and
    uniqueness of monic ℚ_p-factorizations (+ injectivity of
    `Polynomial.map PadicInt.Coe.ringHom`), factors = {e0Poly}; then the
    composite demands {ramIdx·resDeg} = {1} = {2} = {natDegree} — false. -/
theorem e0_zf_factor_false :
    ¬ ∃ factors : Multiset (Polynomial ℤ_[3]),
      e0Poly.map PadicInt.Coe.ringHom
          = (factors.map (Polynomial.map PadicInt.Coe.ringHom)).prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible (h.map PadicInt.Coe.ringHom)) ∧
      factors.map (fun h => MovesT.ramIdx h * MovesT.resDeg h)
        = factors.map Polynomial.natDegree := sorry

/-- E0d assembly — THE CONSEQUENCE (blueprint †11f): as currently typed, NO
    `ZpBridge` instance exists at (n, p) = (2, 3), for ANY classifier `X`
    (the ∃ in `zf_factor` gives no freedom).  The wiring below is REAL (compiled
    now); only the pieces above carry sorries. -/
theorem e0_no_zpBridge (X : ClassifierSpec 2 3) : IsEmpty (ZpBridge 2 3 X) := by
  constructor
  intro B
  obtain ⟨factors, hprod, hfac, hzf, hdeg⟩ :=
    B.zf_factor e0Poly e0Poly_monic e0Poly_natDegree
  refine e0_zf_factor_false ⟨factors, hprod, hfac, ?_⟩
  calc factors.map (fun h => MovesT.ramIdx h * MovesT.resDeg h)
      = (factors.map (fun h => (MovesT.ramIdx h, MovesT.resDeg h))).map
          (fun ef => ef.1 * ef.2) := by
        rw [Multiset.map_map]; rfl
    _ = (B.zfType e0Poly).map (fun ef => ef.1 * ef.2) := by rw [hzf]
    _ = factors.map Polynomial.natDegree := hdeg

end LeanUrat.MovesU
