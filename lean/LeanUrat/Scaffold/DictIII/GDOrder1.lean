/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/DictIII/GDOrder1 — GD23's order-≤1 layer (BP_III §1.4)

E-phase transcription of `lean/blueprints/BP_III.md` §1.4 (module
`Scaffold/DictIII/GDOrder1.lean`, GD23's order-≤1 layer, Step 8, VERIFIED
leaf #4).  This file currently holds units III-G1 (`devCoeff`) and III-G2
(`devg_congr`), transcribed VERBATIM.  Unit III-G3a (`gaussW`) is BLOCKED —
its §1.4 display is ill-typed (`algebraMap ℤ (WithTop ℤ)`: no
`Semiring (WithTop ℤ)` exists) and statement changes are forbidden; see the
BLOCKED(III-G3a) record below for the verbatim display, the exact errors,
and the semantic-stub finding.  Source of record: GD23 §3 GAUSS-g(i).
-/

namespace LeanUrat.Scaffold.DictIII

/-- BP_III Wave-1 row III-G1 (GD23 §3 DEV-g): the Φ-adic development
coefficients, per the blueprint recipe "via `Polynomial.modByMonic` /
`divByMonic`": `devCoeff Φ B j` is the `j`-th coefficient `C_j` in
`B = Σ_j C_j Φ^j` — remainder at slot 0, then recurse on the monic quotient.
(Dependency def for unit III-G2; §1.4 displays only its use sites.) -/
noncomputable def devCoeff {O : Type*} [CommRing O] (Φ : Polynomial O) :
    Polynomial O → ℕ → Polynomial O
  | B, 0 => B %ₘ Φ
  | B, j + 1 => devCoeff Φ (B /ₘ Φ) j

/-- Helper for III-G2: development coefficients commute with ring-hom maps
when the key `Φ` is monic (division by a monic commutes with `map`). -/
theorem devCoeff_map {O S : Type*} [CommRing O] [CommRing S] (f : O →+* S)
    {Φ : Polynomial O} (hΦ : Φ.Monic) (B : Polynomial O) (j : ℕ) :
    (devCoeff Φ B j).map f = devCoeff (Φ.map f) (B.map f) j := by
  induction j generalizing B with
  | zero => simpa [devCoeff] using Polynomial.map_modByMonic f hΦ
  | succ j ih =>
    simp only [devCoeff]
    rw [ih (B /ₘ Φ), Polynomial.map_divByMonic f hΦ]

set_option linter.unusedVariables false in
/-- BP_III §1.4, unit III-G2 (GD23 §3 DEV-g): if `B ≡ B'` coefficientwise
mod `π^L` then every development-coefficient slot is congruent mod `π^L`,
for all `j` and all coefficient indices `k` (REV2 finding 9). VERBATIM.
(`hπ`/`hd` are verbatim-required binders, unused by this proof.) -/
theorem devg_congr {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal O)
    (Φ : Polynomial O) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (L : ℕ)
    {B B' : Polynomial O}
    (h : ∀ k, (B - B').coeff k ∈ (Ideal.span {π}) ^ L) :
    ∀ j k, (devCoeff Φ B j - devCoeff Φ B' j).coeff k ∈
      (Ideal.span {π}) ^ L := by
  intro j k
  set I : Ideal O := (Ideal.span {π}) ^ L with hI
  have hmap : B.map (Ideal.Quotient.mk I) = B'.map (Ideal.Quotient.mk I) := by
    ext n
    simp only [Polynomial.coeff_map]
    exact Ideal.Quotient.eq.mpr (by simpa using h n)
  have hdev : (devCoeff Φ B j - devCoeff Φ B' j).map (Ideal.Quotient.mk I)
      = 0 := by
    rw [Polynomial.map_sub, devCoeff_map _ hΦ, devCoeff_map _ hΦ, hmap,
      sub_self]
  have hz : (Ideal.Quotient.mk I)
      ((devCoeff Φ B j - devCoeff Φ B' j).coeff k) = 0 := by
    have := congrArg (fun P => Polynomial.coeff P k) hdev
    simpa [Polynomial.coeff_map] using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/- BLOCKED(III-G3a): the §1.4 `gaussW` display cannot compile as written and
statement changes are forbidden, so NO declaration is transcribed here yet.
The verbatim display is

  def gaussW {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      (B : Polynomial O) : WithTop ℤ :=
    if hB : B = 0 then ⊤ else
      Finset.min' (B.support.image fun k => algebraMap ℤ (WithTop ℤ) 0)
        (by simpa [Polynomial.support_nonempty] using hB)

Two independent blocks, needing an architect fix of the display:
1. TYPE ERROR (fatal): `algebraMap ℤ (WithTop ℤ)` requires the instances
   `Semiring (WithTop ℤ)` + `Algebra ℤ (WithTop ℤ)`; neither exists
   (`#synth Semiring (WithTop ℤ)` fails — `WithTop ℤ` is genuinely not a
   semiring: `⊤ * (1 + (-1)) = 0` but `⊤ * 1 + ⊤ * (-1) = ⊤`). Exact error
   at the `algebraMap` token: "typeclass instance problem is stuck
   Algebra ℤ (WithTop ℤ)". Not a renamed-token issue — the map is ill-typed
   in every Mathlib — so the sanctioned same-function respelling convention
   (cf. Carriers.lean on `List.get?`) does not apply.
2. SEMANTIC STUB: the mapped function `fun k => algebraMap ℤ (WithTop ℤ) 0`
   ignores `k` (constant 0), so under ANY compiling respelling the def would
   give `gaussW B = 0` for every nonzero `B` — contradicting the unit row's
   own gloss ("nonzero = minimum over finite support" of coefficient
   valuations, GD23 §3 GAUSS-g(i)) and making downstream unit III-G5
   `gaussW_keyBlock` (`gaussW B ≠ gaussW Φ`) FALSE (`0 ≠ 0`). The intended
   body presumably reads the π-adic valuation of `B.coeff k` into `WithTop ℤ`
   at each support index `k`.

Minor (curable by modifiers alone, recorded for the repaired display):
`if hB : B = 0` needs `Decidable (B = 0)`, unavailable over arbitrary `O`
(exact error: "failed to synthesize instance of type class
Decidable (B = 0)"); cure = `open Classical in` + `noncomputable def`. -/

end LeanUrat.Scaffold.DictIII
