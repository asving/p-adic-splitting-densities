/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H6.Emission
import LeanUrat.OM.Order0Hull

/-!
# Scaffold/DictIII/CU2tKp0 — the TerminalPolySem k′ = 0 face

Unit: synthesis pass-4 F2(b), re-queued at pass-5 F6 item 8 ("TerminalPolySem
k′=0"): `TerminalPolySem` (the III-S4-repair semantic row, `DictIII/CU2t.lean`)
has NO supplier at HEAD; its k′ = 0 face "may be derivable from the landed
emission specs (`terminalDatumD_slope_spec`/`ReadThroughIota`)".  Attempt-grade:
success OR compiled obstruction.  This file is the unit's full disposition —
NEW declarations only; no existing statement is touched.

LAYERING NOTE: `CU2t.lean` itself is fenced from importing H6 (the
`TerminalPolySem` docstring's ι-honesty fence).  This file is the CONSUMER
wiring the two sides together — exactly what the supplier charter demands —
and nothing imports it back, so the fence and the import graph both survive.

KEYING NOTE (load-bearing).  `TerminalPolySem` reads the side list at index
`H.nodes.length`; `ReadThroughIota` (H6-A6b) pins index 0 CORPUS-REAL
(= `principalData f`, clauses (i)/(ii)) and indices `i + 1 ≤ H.nodes.length`
only through `OL1 (Theta H)` grants (clause (iii)).  Hence "k′ = 0" splits
into TWO inequivalent readings, and this unit decides BOTH:

* **𝐇°-keyed (the H6 keying, `H.nodes = []`)** — the blueprint's displayed
  k′ = 0 seam (`HDISCHARGE_H6.md` G1/G2: "k′ = 0 seam with `H.nodes = []`").
  The terminal index is 0, the corpus-real level; the face is DERIVABLE here
  modulo one purely numerical polygon law — `terminalPolySem_kp0` below
  (proved), consuming ONLY clauses (i)/(ii) (the CUC's "unconditional at
  k′ = 0" bracket verbatim: no OL row, no clause (iii)).  The residual
  numerical input is the named open row `BasePolygonLengthLaw` (the OM base
  length law ℓ(N⁻) = ord_X(f̄) + side nondegeneracy) — displayed, not assumed,
  not discharged here: the corpus has NO general negative-prefix hull geometry
  (the III-A6a status note: OL5-adjacent "convexity work" unclaimed; only the
  FLAT machinery of `OM/Order0Hull.lean` exists at HEAD).

* **terminal-appended (the CU2t consumption keying, `H.nodes = [ν_term]`,
  DecHen terminal-first)** — the terminal index is 1, which `ReadThroughIota`
  does NOT constrain: clause (iii)'s grants are keyed to `(Theta H).slopes`,
  EMPTY on a terminal-first history, so index 1 is untouched junk.  The face
  is NOT derivable here — COMPILED obstruction `Kp0GateC.not_terminalPolySem_
  terminal_indexed` below: the real order-≤1 read (`gmnDataOrder1`, certified
  by the landed A6b positive gate) on a DEC-decided seam FAILS
  `TerminalPolySem`.  Any supplier at this keying needs new content tying the
  terminal-index list to level k′ + 1 of the CONTINUING part — the III-A3
  terminal-blindness seam family again, NOT owned here.

TEST BEFORE PROVING (the S4Refute precedent — this family has a compiled
countermodel history).  The face was decided at instances FIRST; the compiled
verdicts, which fixed the hypothesis row of `terminalPolySem_kp0`:
1. POSITIVE (`Kp0Gate.terminalPolySem_kp0_gate_pos`): p = 2, f = X + 2,
   `H.nodes = []`, D = the REAL corpus read `gmnDataOrder1` — every hypothesis
   fires and `TerminalPolySem` HOLDS.  This is the first real-read
   (ReadThroughIota-certified) `TerminalPolySem` witness at HEAD (the
   `S4SemGate.sem1` gate world's `D1` was hand-built data).
2. SATURATION NECESSARY (`Kp0GateA.not_terminalPolySem_unsat`): p = 2,
   f = X + 1 (unit constant term — an UNDECIDED seam), D = the empty-list
   datum: `ReadThroughIota` HOLDS, `TerminalPolySem` FAILS.  So the face
   cannot drop its saturation leg (`1 ≤ j₀`, supplied by `p ∣ f(0)` in the
   law row).
3. THE −∞ LEG IS NOT SUPPLIED (`Kp0GateB.not_terminalPolySem_neginf`): p = 2,
   f = X (so `f.coeff 0 = 0`), D = a junk slope-−∞ side with `e = 0`:
   `ReadThroughIota` HOLDS (clause (ii) permits the −∞ entry and constrains
   NOTHING else about it), `TerminalPolySem` FAILS at nondegeneracy.  So the
   face must carry `f.coeff 0 ≠ 0`; the −∞ corner (j₀-includes-the-−∞-side
   accounting) is a separately-priced open leg, exactly as `TerminalPolySem`'s
   own HONESTY block prices its residue.
4. The CU2t-keyed obstruction (bullet above, `Kp0GateC`).

VERDICT SUMMARY: the pass-4 charter "derivable from the landed emission
specs" is REFUTED as literally stated (compiled countermodels 2–4: neither
`ReadThroughIota` alone, nor at the CU2t index at all); the honest salvage is
PROVED (`terminalPolySem_kp0`): at the 𝐇°-keyed seam with the saturation +
finite-slope perimeter, the face reduces to `BasePolygonLengthLaw` — an
`H`-free, `D`-free, seam-free numerical polygon law, the next unit's target.
`terminalDatumD_slope_spec` (the other named landed spec) is not consumed:
it ties SLOPE reads, not the side-list mass that `TerminalPolySem` demands.

Unit record: `lean/notes/openmath/CU2T_KP0_2026-08-08.md`.
-/

namespace LeanUrat.Scaffold.DictIII

open LeanUrat.Scaffold.HDischarge.H6

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The named open numerical row — the face's ONE residual input -/

/-- **`BasePolygonLengthLaw`** — the OM base length law at the corpus carrier
    ([M]-row discipline: a NAMED hypothesis row, like `Lit3Hensel`/`OL1` —
    never an axiom, never discharged by fiat; no theorem at HEAD supplies it).
    For monic `f` with nonzero constant term divisible by `p` (the decided,
    finite-slope, saturated perimeter — countermodels `Kp0GateA`/`Kp0GateB`
    below show BOTH perimeter legs are necessary):
    (i) NONDEGENERACY — every principal side of the corpus base read has
    `1 ≤ e` and `1 ≤ ℓ`;
    (ii) the LENGTH TIE — the total horizontal length `Σ e·ℓ` of the corpus
    principal polygon `principalData f` equals the EXACT multiplicity `j₀` of
    `X` in the mod-p reduction (`ℓ(N⁻(f)) = ord_X(f̄)`, GMN — `X` is the
    corpus ψ̂₀-key: the base read is the coefficient polygon, the III-A6a
    scope caveat), with `1 ≤ j₀` (saturation: `p ∣ f(0)` and `f(0) ≠ 0`).
    PROOF ROUTE (not landed; the corpus lacks all general hull geometry
    beyond `Order0Hull`'s flat case): per-side `e ∣ length` + `1 ≤ length`
    (zip-consecutive + `npVertices_sorted` + `Rat.den` divisibility), adjacent
    slope monotonicity from the PROVED `npHeight_convexOn`, the negative
    prefix telescoping to the first zero-height vertex, and the endpoint pins
    (leftmost dot on hull at abscissa 0; `(natDegree, 0)` on hull for monic
    `f` via `valSupport_facts`). -/
def BasePolygonLengthLaw (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : Polynomial ℤ_[p], f.Monic → f.coeff 0 ≠ 0 →
    (p : ℤ_[p]) ∣ f.coeff 0 →
    (∀ S ∈ principalData f, 1 ≤ S.e ∧ 1 ≤ S.ℓ) ∧
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      Polynomial.X ^ j₀ ∣ Polynomial.map PadicInt.toZMod f ∧
      ¬Polynomial.X ^ (j₀ + 1) ∣ Polynomial.map PadicInt.toZMod f ∧
      ((principalData f).map fun S => S.e * S.ℓ).sum = j₀

/-! ## The k′ = 0 face, 𝐇°-keyed — PROVED (the reduction theorem) -/

/-- **THE k′ = 0 FACE** (𝐇°-keyed; per-`f` legs displayed).  On a k′ = 0 seam
    (`H.nodes = []` — the H6 blueprint's displayed k′ = 0 seam shape, where
    the terminal index `H.nodes.length` IS the corpus-real level 0), if the
    side lists are certified GMN-through-ι (`hread`, of which ONLY the
    corpus-real clauses (i)/(ii) are consumed — the CUC's "unconditional at
    k′ = 0"), the constant term is nonzero (finite-slope perimeter,
    countermodel `Kp0GateB`) and the corpus principal read satisfies the two
    numerical legs of the base length law (`hnd`/`hlaw` — supplied wholesale
    by `BasePolygonLengthLaw` via `terminalPolySem_kp0_of_law`, or concretely
    at an instance as in `Kp0Gate`), then `TerminalPolySem f H D` holds with
    witness key `φ = X`.  Pin: clauses (i)+(ii) force the terminal-index list
    to be EXACTLY `principalData f`. -/
theorem terminalPolySem_kp0 (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H))
    (h0 : H.nodes = [])
    (hread : ReadThroughIota f H D)
    (hc0 : f.coeff 0 ≠ 0)
    (hnd : ∀ S ∈ principalData f, 1 ≤ S.e ∧ 1 ≤ S.ℓ)
    (hlaw : ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      Polynomial.X ^ j₀ ∣ Polynomial.map PadicInt.toZMod f ∧
      ¬Polynomial.X ^ (j₀ + 1) ∣ Polynomial.map PadicInt.toZMod f ∧
      ((principalData f).map fun S => S.e * S.ℓ).sum = j₀) :
    TerminalPolySem f H D := by
  obtain ⟨h1, h2, -⟩ := hread
  have hlen : H.nodes.length = 0 := by rw [h0]; rfl
  have hpin : D.principalSides H.nodes.length = principalData f := by
    rw [hlen, ← h1]
    refine (List.filter_eq_self.mpr fun S hS => ?_).symm
    cases hne : S.isNegInfty
    · simp
    · exact absurd (h2 S hS hne) hc0
  obtain ⟨j₀, hj₀, hdvd, hndvd, hsum⟩ := hlaw
  refine ⟨by rw [hpin]; exact hnd,
    Polynomial.X, Polynomial.irreducible_X, j₀, hj₀, hdvd, hndvd, ?_⟩
  rw [hpin]; exact hsum

/-- The k′ = 0 face keyed to the named law row: `BasePolygonLengthLaw p` +
    the seam perimeter (monic, nonzero constant term, saturation `p ∣ f(0)`)
    supply `TerminalPolySem` on every 𝐇°-keyed k′ = 0 seam. -/
theorem terminalPolySem_kp0_of_law (hlawAll : BasePolygonLengthLaw p)
    (f : Polynomial ℤ_[p]) (H : EHist p F) (D : GMNData f (Theta H))
    (hf : f.Monic)
    (h0 : H.nodes = [])
    (hread : ReadThroughIota f H D)
    (hc0 : f.coeff 0 ≠ 0)
    (hsat : (p : ℤ_[p]) ∣ f.coeff 0) :
    TerminalPolySem f H D := by
  obtain ⟨hnd, hlaw⟩ := hlawAll f hf hc0 hsat
  exact terminalPolySem_kp0 f H D h0 hread hc0 hnd hlaw

/-! ## Shared gate world: the k′ = 0 seam (empty node list) -/

/-- The k′ = 0 seam world: `S4Refute.H0`'s dressing with an EMPTY node list
    (the `HDISCHARGE_H6.md` G1/G2 displayed seam shape `H.nodes = []`). -/
noncomputable def Hkp0 : EHist 2 (ZMod 2) := { S4Refute.H0 with nodes := [] }

/-- The empty seam's chain has no slopes (so the order-≤1 constructor's
    perimeter `slopes.length ≤ 1` is met). -/
theorem theta_Hkp0_slopes : (Theta Hkp0).slopes = [] := by
  simp [Theta, EHist.continuingPart, Hkp0]

/-! ## Gate 1 (POSITIVE, the instance decision): f = X + 2, the real read -/

namespace Kp0Gate

open Polynomial LeanUrat.OM

/-- The positive-gate polynomial: `X + 2` over `ℤ_[2]` — monic, decided
    (`2 ∣ f(0)`), nonzero constant term; its corpus base read is the single
    slope-−1 chord (the compiled `principalData_X_add_two`). -/
noncomputable def fkp0 : Polynomial ℤ_[2] := X + C 2

/-- The positive-gate datum: the REAL corpus order-≤1 read of `fkp0` over the
    empty chain (`gmnDataOrder1`, unit III-A6a) — certified through ι by the
    landed A6b positive gate. -/
noncomputable def Dkp0 : GMNData fkp0 (Theta Hkp0) :=
  gmnDataOrder1 fkp0 (Theta Hkp0) gateIota gateIota
    (by rw [theta_Hkp0_slopes]; exact Nat.zero_le 1)

/-- The positive gate's `hread` row: the real read is GMN-through-ι (the
    landed H6-A6b positive gate at the k′ = 0 seam). -/
theorem readThroughIota_kp0 : ReadThroughIota fkp0 Hkp0 Dkp0 :=
  readThroughIota_order1_gate fkp0 Hkp0 gateIota gateIota _

/-- The compiled corpus read of `X + 2`, restated at the gate name (the
    `fkp0` binder is definitionally `X + C 2`). -/
theorem principalData_fkp0 :
    principalData fkp0 = [sideToDatum ⟨0, 1, 1, 0⟩] :=
  principalData_X_add_two

/-- The mod-2 reduction of `X + 2` is `X`. -/
theorem map_fkp0 : fkp0.map PadicInt.toZMod = (X : Polynomial (ZMod 2)) := by
  rw [fkp0, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := by
    rw [map_ofNat PadicInt.toZMod 2]
    decide
  rw [h2, Polynomial.C_0, add_zero]

/-- The one corpus side of `X + 2` in datum dress: `(e, ℓ) = (1, 1)`
    (slope −1 in lowest terms; residual degree `length/e = 1`). -/
theorem sideDatum_fkp0 :
    (sideToDatum ⟨0, 1, 1, 0⟩).e = 1 ∧ (sideToDatum ⟨0, 1, 1, 0⟩).ℓ = 1 := by
  have hslope : (⟨0, 1, 1, 0⟩ : NewtonPolygon.Side).slope = -1 := by
    norm_num [NewtonPolygon.Side.slope]
  have he : (⟨0, 1, 1, 0⟩ : NewtonPolygon.Side).e = 1 := by
    unfold NewtonPolygon.Side.e
    rw [hslope]
    norm_num
  refine ⟨he, ?_⟩
  change M4.residualDeg ⟨0, 1, 1, 0⟩ = 1
  unfold M4.residualDeg
  rw [he]
  rfl

/-- **THE INSTANCE DECISION (positive)**: at the k′ = 0 seam with the REAL
    ι-certified read of `X + 2`, every hypothesis of the face fires
    concretely (`j₀ = 1`: `X ∣ X̄`, `X² ∤ X̄`, total length `1·1 = 1`) and
    `TerminalPolySem` HOLDS — the face is TRUE at the instance, and this is
    the first real-read `TerminalPolySem` witness at HEAD. -/
theorem terminalPolySem_kp0_gate_pos : TerminalPolySem fkp0 Hkp0 Dkp0 := by
  refine terminalPolySem_kp0 fkp0 Hkp0 Dkp0 rfl readThroughIota_kp0 ?_ ?_ ?_
  · -- f(0) = 2 ≠ 0
    rw [fkp0]
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    exact two_ne_zero
  · -- nondegeneracy of the corpus read
    intro S hS
    rw [principalData_fkp0] at hS
    rw [List.mem_singleton.mp hS]
    rw [sideDatum_fkp0.1, sideDatum_fkp0.2]
    exact ⟨le_refl 1, le_refl 1⟩
  · -- the length law at the instance: j₀ = 1
    refine ⟨1, le_refl 1, ?_, ?_, ?_⟩
    · rw [pow_one, map_fkp0]
    · rw [map_fkp0]
      have h := S4Refute.hsq0 X Polynomial.irreducible_X
      rwa [Polynomial.map_X] at h
    · rw [principalData_fkp0, List.map_cons, List.map_nil,
        sideDatum_fkp0.1, sideDatum_fkp0.2]
      rfl

end Kp0Gate

/-! ## Gate 2 (countermodel A): saturation is necessary -/

namespace Kp0GateA

open Polynomial LeanUrat.OM

/-- Countermodel-A polynomial: `X + 1` over `ℤ_[2]` — an UNDECIDED seam
    (unit constant term: the X-key does not divide the reduction). -/
noncomputable def fA : Polynomial ℤ_[2] := X + C 1

/-- The valuation support of `X + 1`: both coefficients are units, so both
    dots sit at height 0. -/
theorem valSupport_fA :
    M2.valSupport 2 fA = ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)) := by
  have hc0 : fA.coeff 0 = 1 := by simp [fA]
  have hc1 : fA.coeff 1 = 1 := by simp [fA, Polynomial.coeff_one]
  have hchar := (M2.valSupport_facts 2 fA).1
  ext ⟨i, v⟩
  rw [hchar i v, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl⟩
    match i with
    | 0 =>
        left
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, hc0, PadicInt.valuation_one]⟩
    | 1 =>
        right
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩
    | (n + 2) =>
        exfalso
        apply hne
        simp [fA, Polynomial.coeff_X, Polynomial.coeff_one]
  · rintro (h | h) <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · exact ⟨by rw [hc0]; exact one_ne_zero,
        by rw [M2.coeffVal, hc0, PadicInt.valuation_one]⟩
    · exact ⟨by rw [hc1]; exact one_ne_zero,
        by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩

/-- The corpus principal read of `X + 1` is EMPTY: the polygon is the flat
    chord (`Order0Hull`'s γ1 gate), whose slope-0 side is not principal. -/
theorem principalData_fA : principalData fA = [] := by
  have hne : (M2.valSupport 2 fA).Nonempty := by
    rw [valSupport_fA]
    exact ⟨(0, 0), by simp⟩
  have hflatmem : ((0 : ℕ), (0 : ℕ)) ∈ ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)) := by
    simp
  have hflatmem' : ((1 : ℕ), (0 : ℕ)) ∈ ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)) := by
    simp
  have hbound : ∀ P ∈ ({(0, 0), (1, 0)} : Finset (ℕ × ℕ)), P.1 ≤ 1 := by
    intro P hP
    rw [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl <;> norm_num
  have hne' : (({(0, 0), (1, 0)} : Finset (ℕ × ℕ))).Nonempty :=
    ⟨(0, 0), hflatmem⟩
  have hsl : sideList fA = [⟨0, 1, 0, 0⟩] := by
    rw [sideList, dif_pos hne,
      NewtonPolygon.npSides_congr _ ({(0, 0), (1, 0)} : Finset (ℕ × ℕ))
        hne hne' valSupport_fA,
      Order0.npSides_of_flat _ hne' 1 one_pos hflatmem hflatmem' hbound]
  rw [principalData, principalSideList, hsl]
  have hh : ¬((⟨0, 1, 0, 0⟩ : NewtonPolygon.Side).h < 0) := by
    rw [Order0.flatSide_h]
    exact lt_irrefl 0
  simp [hh]

/-- Countermodel-A datum: everything empty (over the empty read, the honest
    junk-free datum). -/
noncomputable def DA : GMNData fA (Theta Hkp0) :=
  { principalSides := fun _ => []
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 0 }

/-- `ReadThroughIota` HOLDS at the undecided seam: the empty list IS the real
    (empty) principal read of `X + 1`. -/
theorem readThroughIota_unsat : ReadThroughIota fA Hkp0 DA := by
  refine ⟨?_, ?_, ?_⟩
  · change (List.filter _ []) = principalData fA
    rw [principalData_fA]
    rfl
  · intro S hS
    exact absurd hS List.not_mem_nil
  · intro lift _ i hi
    exact absurd hi (by rw [show Hkp0.nodes.length = 0 from rfl] at *; omega)

/-- **COUNTERMODEL A (saturation leg)**: `ReadThroughIota` alone does NOT
    supply `TerminalPolySem` at k′ = 0 — at the undecided seam `f = X + 1`
    the certified read is empty, so the saturated sum `Σ e·ℓ = j₀ ≥ 1` is
    unsatisfiable.  The face's `p ∣ f(0)` perimeter is necessary. -/
theorem not_terminalPolySem_unsat : ¬ TerminalPolySem fA Hkp0 DA := by
  rintro ⟨-, φ, -, j₀, hj₀, -, -, hsum⟩
  have h0 : ((DA.principalSides Hkp0.nodes.length).map
      fun S => S.e * S.ℓ).sum = 0 := rfl
  omega

end Kp0GateA

/-! ## Gate 3 (countermodel B): the −∞ leg is not supplied -/

namespace Kp0GateB

open Polynomial LeanUrat.OM

/-- Local helper (no such lemma at HEAD): a support with at most one dot has
    NO polygon sides — the vertex list has at most one entry, so the
    consecutive-pair zip is empty.  (Pure list bookkeeping: no hull-height
    evaluation is consumed.) -/
theorem npSides_of_card_le_one (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (h1 : S.card ≤ 1) : NewtonPolygon.npSides S hS = [] := by
  classical
  have hsub : NewtonPolygon.hullDots S hS ⊆ S := Finset.filter_subset _ _
  have hcard : ((NewtonPolygon.hullDots S hS).image Prod.fst).card ≤ 1 :=
    le_trans Finset.card_image_le (le_trans (Finset.card_le_card hsub) h1)
  have hlen : (NewtonPolygon.hullAbscissae S hS).length ≤ 1 := by
    rw [NewtonPolygon.hullAbscissae, Finset.length_sort]
    exact hcard
  have hlenF : (NewtonPolygon.npVerticesFull S hS).length ≤ 1 := by
    rw [NewtonPolygon.npVerticesFull, List.length_map]
    exact hlen
  rw [NewtonPolygon.npSides, NewtonPolygon.npVertices]
  match hv : NewtonPolygon.npVerticesFull S hS with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t =>
      rw [hv] at hlenF
      simp at hlenF

/-- Countermodel-B polynomial: `X` over `ℤ_[2]` — zero constant term, the
    slope-−∞ corner. -/
noncomputable def fB : Polynomial ℤ_[2] := X

/-- The valuation support of `X` is the single unit dot at abscissa 1. -/
theorem valSupport_fB :
    M2.valSupport 2 fB = ({(1, 0)} : Finset (ℕ × ℕ)) := by
  have hc1 : fB.coeff 1 = 1 := by simp [fB]
  have hchar := (M2.valSupport_facts 2 fB).1
  ext ⟨i, v⟩
  rw [hchar i v, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl⟩
    match i with
    | 0 => exact absurd (by simp [fB]) hne
    | 1 =>
        rw [Prod.mk.injEq]
        exact ⟨rfl, by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩
    | (n + 2) =>
        exfalso
        apply hne
        simp [fB, Polynomial.coeff_X]
  · rintro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [hc1]; exact one_ne_zero,
      by rw [M2.coeffVal, hc1, PadicInt.valuation_one]⟩

/-- The corpus principal read of `X` is EMPTY (one support dot, no sides —
    the GMN slope-−∞ side has no `npSides` representative, the III-A6a scope
    note). -/
theorem principalData_fB : principalData fB = [] := by
  have hne : (M2.valSupport 2 fB).Nonempty := by
    rw [valSupport_fB]
    exact ⟨(1, 0), by simp⟩
  have hsl : sideList fB = [] := by
    rw [sideList, dif_pos hne]
    refine npSides_of_card_le_one _ hne ?_
    rw [valSupport_fB]
    exact le_refl 1
  rw [principalData, principalSideList, hsl]
  rfl

/-- The junk slope-−∞ side: `e = 0` — nothing in `ReadThroughIota` forbids
    it once `f.coeff 0 = 0`. -/
def junkNegInfty : SideDatum := ⟨0, 0, 0, 0, 0, true⟩

/-- Countermodel-B datum: the junk −∞ side at every level. -/
noncomputable def DB : GMNData fB (Theta Hkp0) :=
  { principalSides := fun _ => [junkNegInfty]
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 0 }

/-- `ReadThroughIota` HOLDS at the −∞ corner with the junk side: clause (i)
    filters the −∞ entry away (the finite-slope face is the empty real read),
    clause (ii)'s obligation `f.coeff 0 = 0` is real, clause (iii) is vacuous
    at the empty seam. -/
theorem readThroughIota_neginf : ReadThroughIota fB Hkp0 DB := by
  refine ⟨?_, ?_, ?_⟩
  · change (List.filter _ [junkNegInfty]) = principalData fB
    rw [principalData_fB]
    rfl
  · intro S hS h
    exact Polynomial.coeff_X_zero
  · intro lift _ i hi
    exact absurd hi (by rw [show Hkp0.nodes.length = 0 from rfl] at *; omega)

/-- **COUNTERMODEL B (the −∞ leg)**: `ReadThroughIota` does NOT supply
    `TerminalPolySem` when `f.coeff 0 = 0` — the certificate constrains a
    slope-−∞ entry ONLY through the vanishing of the constant term, so a
    degenerate `e = 0` entry survives certification and kills nondegeneracy.
    The face's `f.coeff 0 ≠ 0` perimeter is necessary; the −∞ corner stays a
    separately-priced open leg (the `TerminalPolySem` HONESTY residue). -/
theorem not_terminalPolySem_neginf : ¬ TerminalPolySem fB Hkp0 DB := by
  rintro ⟨hnd, -⟩
  have hmem : junkNegInfty ∈ DB.principalSides Hkp0.nodes.length :=
    List.mem_singleton_self _
  have h := (hnd junkNegInfty hmem).1
  exact absurd h (by rw [show junkNegInfty.e = 0 from rfl]; omega)

end Kp0GateB

/-! ## Gate 4 (countermodel C): the CU2t terminal-appended keying -/

namespace Kp0GateC

open Polynomial LeanUrat.OM

/-- The real order-≤1 read of `X + 2` over the TERMINAL-FIRST history
    `S4Refute.H0` (one terminal node, `H.nodes.length = 1` — the CU2t
    DecHen-seam shape; its chain has no slopes, `theta_H0_slopes`). -/
noncomputable def DC : GMNData Kp0Gate.fkp0 (Theta S4Refute.H0) :=
  gmnDataOrder1 Kp0Gate.fkp0 (Theta S4Refute.H0) gateIota gateIota
    (by rw [S4SemGate.theta_H0_slopes]; exact Nat.zero_le 1)

/-- The real read is ι-certified over the terminal-first history too (the
    landed A6b positive gate is perimeter-wide). -/
theorem readThroughIota_term : ReadThroughIota Kp0Gate.fkp0 S4Refute.H0 DC :=
  readThroughIota_order1_gate Kp0Gate.fkp0 S4Refute.H0 gateIota gateIota _

/-- The terminal-first seam is DEC-decided (`DecHen` via `a₀ = 1`, for any
    `f` — the `S4Refute.hdec0` shape). -/
theorem hdec_term :
    DecIrr S4Refute.H0 ∨ DecHen Kp0Gate.fkp0 S4Refute.H0 :=
  Or.inr ⟨rfl, Or.inl rfl⟩

/-- **COUNTERMODEL C (the CU2t keying — the naive charter refuted)**: on the
    DEC-decided terminal-first history (`H.nodes.length = 1`), the REAL,
    ι-certified, decided-seam read of `X + 2` FAILS `TerminalPolySem`: the
    row reads index 1, which `ReadThroughIota` leaves unconstrained (clause
    (iii)'s `OL1` grants are keyed to `(Theta H).slopes = []` — terminal
    blindness), and the order-≤1 constructor's deep levels are empty.  So at
    the CU2t consumption keying the k′ = 0 face is NOT derivable from the
    landed emission specs at all — a supplier there must tie the terminal
    index to the continuing part's level, new content not owned here. -/
theorem not_terminalPolySem_terminal_indexed :
    ¬ TerminalPolySem Kp0Gate.fkp0 S4Refute.H0 DC := by
  rintro ⟨-, φ, -, j₀, hj₀, -, -, hsum⟩
  have hlen : S4Refute.H0.nodes.length = 1 := rfl
  have h1 : DC.principalSides S4Refute.H0.nodes.length = [] := by
    rw [hlen]
    change (if (1 : ℕ) = 0 then principalData Kp0Gate.fkp0 else []) = []
    simp
  rw [h1] at hsum
  simp at hsum
  omega

end Kp0GateC

end LeanUrat.Scaffold.DictIII

-- Footprint audits (unit KP0): expect Lean core only (Classical.choice enters
-- through the noncomputable corpus polygon carriers).
#print axioms LeanUrat.Scaffold.DictIII.terminalPolySem_kp0
#print axioms LeanUrat.Scaffold.DictIII.terminalPolySem_kp0_of_law
#print axioms LeanUrat.Scaffold.DictIII.Kp0Gate.terminalPolySem_kp0_gate_pos
#print axioms LeanUrat.Scaffold.DictIII.Kp0GateA.not_terminalPolySem_unsat
#print axioms LeanUrat.Scaffold.DictIII.Kp0GateB.not_terminalPolySem_neginf
#print axioms LeanUrat.Scaffold.DictIII.Kp0GateC.not_terminalPolySem_terminal_indexed
