/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136r0
import Uniformity.ChapC.C136d3
import Uniformity.ChapC.C136e2
import Uniformity.ChapC.C130cr

/-!
# Uniformity.ChapC.C136r3 — ambient letters and the canonical dictionary at depth four
[R5 2026-08-29]

**Row R5** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 ("*Define ambient
letters/canonical reads and prove the shared receiver/letter equalities required by G4*") —
the OPEN-LETTERS core, at the S2 depth-four data.  This is the one-witness supplier for the
two dictionary clauses G4's shared record (`I10DeepExport.DeepLevelExport`) demands at the
unique deep-live level `j = 3` of `r = 4`:

* the **receiver/letter equality** (`letter_receiver`'s body): the FGMN calculus letters
  `letterZ (a+2)` of the D3-19 μ₄ calculus, pushed through the SAME receiver
  `s2TerminalReceiverFour.levelHom 3` (R0) and the SAME terminal embedding
  `algebraMap Kt L`, equal the canonical letter values — the reads of C130cr's
  `letterClass` at the R0 normalizer;
* the **canonical-generator descent** (`CanonicalGeneratorDescent`'s `wrap`/`letter`
  bodies): every wrap/letter value at the constructed read is an embedded `Kt`-unit.

## What is constructed (the NP-6/NP-7 port, one/two levels up)

The depth-two witness supplied these clauses through `C130np6.s2AmbientLetter` (the
residue letters, forced to `1` by the `ψ`-root law) and `C130np7.s2CanonicalRead` (the
L-valued kernel read CONSTRUCTED as the distinguished-generator basis inversion, so the
generator regressions are consequences of coordinate formulas, not a freely chosen table —
the anti-cook content the TAU adjudication demands, cf. `C130s18.embeddedValue_not_uniform`).
This file is that construction at `s2DepthFour` (T3, `C136t`), live levels `1..4`:

* **Part 1** — the level height laws at the depth-four numerals `e ≡ 2`, `u = (1,5,21,85)`,
  `ê = (2,4,8,16)`: weighted sums `2p+q`, `4p+2q+5t₀`, `8p+4q+10t₀+21t₁`,
  `16p+8q+20t₀+42t₁+85t₂`, with the kernel membership laws.
* **Part 2** — `s2AmbientLetterFour`: the constant unit `1`, with the `psi_root` field law
  at the R0 receiver (`ψ_i = X − C 1` at every stage of the T3 datum, so `1` is its unique
  root in ANY `L`, no residue-cardinality input).
* **Part 3** — the distinguished-generator coordinates: `wrapGen = (−1,2,0)` at every
  level, and the six letter-class coordinate computations through the CC-4 Laurent solve
  (`n̂₂(10) = (2,1,0)`, `n̂₃(20) = (2,1,0,0)`, `n̂₃(42) = (4,0,1,0)`, `n̂₄(40) = (2,1,0,0,0)`,
  `n̂₄(84) = (4,0,1,0,0)`, `n̂₄(170) = (8,0,0,1,0)`), giving
  `Λ-coordinates (−2,−1,2), (−2,−1,2,0), (−4,0,−1,2), (−2,−1,2,0,0), (−4,0,−1,2,0),
  (−8,0,0,−1,2)` — the depth-four extension of D62w's regressed `d2g2/d3g2/d3g3` rows.
* **Part 4** — the canonical reads `s2CanonicalReadFour1..4` and the total field-shape
  `s2CanonicalReadFour`: each level's read is the basis inversion `g ↦ η^m ∏ β_a^{s_a}`
  written in raw lattice coordinates (the divisions are exact ON THE KERNEL — the kernel
  law forces every evenness), assembled from single-letter `zpow` homs (`zpowHom`) whose
  additivity is the kernel arithmetic.
* **Part 5** — the generator regressions: the read of the wrap class is `η` and the read
  of `Λ_a` is `β_{a+2} = s2AmbientLetterFour L (a+2)` at every live level, plus the
  distinguished-generator-word displays and their S2 collapse to `1`.
* **Part 6** — ★ the R5 dictionary at the campaign data: the named μ₄/μ₅ calculi
  (`s2Mu4Calculus`/`s2Mu5Calculus`, the explicit `fgmnCalculusOf` terms inside
  D3-19/D4-18's `Nonempty`s, `letterZ` pinned to the forced constant-1 letters), the
  ★★ receiver/letter equalities `algebraMap Kt L (levelHom j (letterZ (a+2))) = (read_j Λ_a : L)`
  at `j = 3` (G4's `letter_receiver` body — the OPEN-LETTERS core) and `j = 4` (the μ₅
  twin at the terminal level), and the wrap/letter descent clauses
  (`CanonicalGeneratorDescent`'s `wrap`/`letter` bodies) at EVERY gauge-live level.
* **Part 7** — the R7 handoff: for ANY future depth-four `SplitNodePointSource` at the R0
  receiver whose `canonicalRead` is pinned to this file's read, the `wrapValue`/
  `letterValue` descent clauses and the exact `letter_receiver` body FIRE (named
  conditional theorems).  Constructing that node/realization is row R7/R9 — per the GCW-6
  fence this file, like R0, is DATA + dictionary, and touches no `SplitNodePointSource`,
  `ChainRealization`, or `RealizedInput` instance.

## Named handoff to R7 (R34's precedent: recorded, not invented around)

1. **The node instance itself** (R7): `CanonicalGeneratorDescent`/`DeepLevelExport` are
   typed at an `ArisingCore`/`ChainRealization`, none of which exists at depth four yet.
   The Part-7 theorems are stated so that R7's node with `canonicalRead := s2CanonicalReadFour`
   inhabits both dictionary clauses by direct application.
2. **The site-calculus truncation transport** (R7/C0): G4's `site.calculus` lives on
   `core.T.trunc 3`, while D3-19's calculus lives on `s2DepthThree`; the two towers agree
   on the live range but differ at junk indices (`u 4 = 85` vs `21`), so the transport is
   an assembly step, NOT free.  `letter_receiver` reads ONLY `letterZ (a+2)` from the
   calculus, and the stage fields of all the S2 towers are the SAME constant
   `stageField` — the equalities proved here consume the letter VALUE and hence serve
   either typing verbatim.
3. **`key_value` at levels 2/3** (recorded at R34, unchanged here): untouched by this row.

## OPEN-LETTERS fence (charge item 4)

C.102 `letter_formula` and `gentow5w_one_shape`'s `htie` are HELD items
(`docs/in-progress/BLOCKERS_PLAN_2026-08-26.md` §Fence); their signed statements are not
touched, absorbed, or re-signed here.  What this file changes about their status is
recorded in `runs/wave-c/verdict_R5.md`.

Zero `sorry`; Lean-core axiom footprint (AxCheck footer).  No landed statement is touched.
`zpowHom` is this file's one generic helper (flagged as a general lemma).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C136r3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C136t Uniformity.Density.Tower.C136r0
open Uniformity.Density.Tower.C136d3 Uniformity.Density.Tower.C136e2

universe uE uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — liveness pins at `r = 4` -/

/-- The unique deep-live level of the depth-four tower is `j = 3` — the level every Part-6
dictionary statement is proved at (`DeepLive r j := 3 ≤ j ∧ j < r`, C130a). -/
theorem deepLive_four_iff {j : ℕ} : DeepLive 4 j ↔ j = 3 := by
  constructor
  · rintro ⟨h3, hlt⟩; omega
  · rintro rfl; exact ⟨le_rfl, by omega⟩

/-- The gauge-live levels of the depth-four tower are `{1, 2, 3}` — the range of the
descent clauses and of `psi_root`. -/
theorem gaugeLive_four_iff {j : ℕ} : GaugeLive 4 j ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
  constructor
  · rintro ⟨h1, hlt⟩; omega
  · rintro (rfl | rfl | rfl) <;> exact ⟨by omega, by omega⟩

/-! ## Part 1 — the level height laws at the depth-four numerals

`s2DepthFour` carries `e ≡ 2`, `u = (1, 5, 21, 85)`, hence `ê = (2, 4, 8, 16)`
(`C136t.s2WitnessFour_values`); the level-`j` Laurent height collapses to the weighted sums
below — the depth-four extension of D62w's regressed depth-two and depth-three lattices and of
`C130np7.s2_levelExponentHeight_one/two`. -/

/-- `ê₁ = 2` at the depth-four occurrence. -/
theorem s2four_ehat_one : (s2DepthFour h2 hq).ehat 1 = 2 := rfl

/-- `ê₂ = 4` at the depth-four occurrence. -/
theorem s2four_ehat_two : (s2DepthFour h2 hq).ehat 2 = 4 := rfl

/-- `ê₃ = 8` at the depth-four occurrence. -/
theorem s2four_ehat_three : (s2DepthFour h2 hq).ehat 3 = 8 := rfl

/-- `ê₄ = 16` at the depth-four occurrence. -/
theorem s2four_ehat_four : (s2DepthFour h2 hq).ehat 4 = 16 := rfl

/-- The level-one Laurent height at the depth-four numerals: `2p + q`. -/
theorem s2four_levelExponentHeight_one (v : ℤ × ℤ × (Fin 0 → ℤ)) :
    levelExponentHeight (s2DepthFour h2 hq) 1 (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (2 * v.1 + v.2.1) := by
  rw [levelExponentHeight_ofAdd]
  congr 1
  have he1 : (s2DepthFour h2 hq).e 1 = 2 := rfl
  have hu1 : (s2DepthFour h2 hq).u 1 = 1 := rfl
  simp only [he1, hu1, s2four_ehat_one h2 hq]
  ring

/-- The level-one kernel law: `2p + q = 0`. -/
theorem s2four_mem_ker_one_iff (v : ℤ × ℤ × (Fin 0 → ℤ)) :
    (Multiplicative.ofAdd v : LevelExponentLattice 1) ∈
        MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1) ↔
      2 * v.1 + v.2.1 = 0 := by
  rw [MonoidHom.mem_ker, s2four_levelExponentHeight_one, ofAdd_eq_one]

/-- General-element form of the level-one kernel law. -/
theorem s2four_mem_ker_one_iff' (g : LevelExponentLattice 1) :
    g ∈ MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1) ↔
      2 * (Multiplicative.toAdd g).1 + (Multiplicative.toAdd g).2.1 = 0 := by
  have h := s2four_mem_ker_one_iff h2 hq (Multiplicative.toAdd g)
  rwa [ofAdd_toAdd] at h

/-- The level-two Laurent height at the depth-four numerals: `4p + 2q + 5t₀` (the same
weights as the landed depth-two lattice — levels `1, 2` of T3 restrict to `S2DepthTwo`). -/
theorem s2four_levelExponentHeight_two (v : ℤ × ℤ × (Fin 1 → ℤ)) :
    levelExponentHeight (s2DepthFour h2 hq) 2 (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (4 * v.1 + 2 * v.2.1 + 5 * v.2.2 0) := by
  rw [levelExponentHeight_ofAdd]
  congr 1
  have he1 : (s2DepthFour h2 hq).e 1 = 2 := rfl
  have hu1 : (s2DepthFour h2 hq).u 1 = 1 := rfl
  have hu2 : (s2DepthFour h2 hq).u 2 = 5 := rfl
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, he1, hu1, hu2, s2four_ehat_two h2 hq]
  ring

/-- The level-two kernel law: `4p + 2q + 5t₀ = 0`. -/
theorem s2four_mem_ker_two_iff (v : ℤ × ℤ × (Fin 1 → ℤ)) :
    (Multiplicative.ofAdd v : LevelExponentLattice 2) ∈
        MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2) ↔
      4 * v.1 + 2 * v.2.1 + 5 * v.2.2 0 = 0 := by
  rw [MonoidHom.mem_ker, s2four_levelExponentHeight_two, ofAdd_eq_one]

/-- General-element form of the level-two kernel law. -/
theorem s2four_mem_ker_two_iff' (g : LevelExponentLattice 2) :
    g ∈ MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2) ↔
      4 * (Multiplicative.toAdd g).1 + 2 * (Multiplicative.toAdd g).2.1 +
          5 * (Multiplicative.toAdd g).2.2 0 = 0 := by
  have h := s2four_mem_ker_two_iff h2 hq (Multiplicative.toAdd g)
  rwa [ofAdd_toAdd] at h

/-- ★ The level-three Laurent height at the depth-four numerals: `8p + 4q + 10t₀ + 21t₁`
(D62w's regressed depth-three lattice `(8, 4, 10, 21)`, now a theorem of the T3 datum). -/
theorem s2four_levelExponentHeight_three (v : ℤ × ℤ × (Fin 2 → ℤ)) :
    levelExponentHeight (s2DepthFour h2 hq) 3 (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (8 * v.1 + 4 * v.2.1 + 10 * v.2.2 0 + 21 * v.2.2 1) := by
  rw [levelExponentHeight_ofAdd]
  congr 1
  have he1 : (s2DepthFour h2 hq).e 1 = 2 := rfl
  have hu1 : (s2DepthFour h2 hq).u 1 = 1 := rfl
  have hu2 : (s2DepthFour h2 hq).u 2 = 5 := rfl
  have hu3 : (s2DepthFour h2 hq).u 3 = 21 := rfl
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, he1, hu1, hu2, hu3, s2four_ehat_two h2 hq,
    s2four_ehat_three h2 hq]
  ring

/-- The level-three kernel law: `8p + 4q + 10t₀ + 21t₁ = 0`. -/
theorem s2four_mem_ker_three_iff (v : ℤ × ℤ × (Fin 2 → ℤ)) :
    (Multiplicative.ofAdd v : LevelExponentLattice 3) ∈
        MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3) ↔
      8 * v.1 + 4 * v.2.1 + 10 * v.2.2 0 + 21 * v.2.2 1 = 0 := by
  rw [MonoidHom.mem_ker, s2four_levelExponentHeight_three, ofAdd_eq_one]

/-- General-element form of the level-three kernel law. -/
theorem s2four_mem_ker_three_iff' (g : LevelExponentLattice 3) :
    g ∈ MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3) ↔
      8 * (Multiplicative.toAdd g).1 + 4 * (Multiplicative.toAdd g).2.1 +
          10 * (Multiplicative.toAdd g).2.2 0 + 21 * (Multiplicative.toAdd g).2.2 1 = 0 := by
  have h := s2four_mem_ker_three_iff h2 hq (Multiplicative.toAdd g)
  rwa [ofAdd_toAdd] at h

/-- ★ The level-four Laurent height at the depth-four numerals:
`16p + 8q + 20t₀ + 42t₁ + 85t₂`. -/
theorem s2four_levelExponentHeight_four (v : ℤ × ℤ × (Fin 3 → ℤ)) :
    levelExponentHeight (s2DepthFour h2 hq) 4 (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd
        (16 * v.1 + 8 * v.2.1 + 20 * v.2.2 0 + 42 * v.2.2 1 + 85 * v.2.2 2) := by
  rw [levelExponentHeight_ofAdd]
  congr 1
  have he1 : (s2DepthFour h2 hq).e 1 = 2 := rfl
  have hu1 : (s2DepthFour h2 hq).u 1 = 1 := rfl
  have hu2 : (s2DepthFour h2 hq).u 2 = 5 := rfl
  have hu3 : (s2DepthFour h2 hq).u 3 = 21 := rfl
  have hu4 : (s2DepthFour h2 hq).u 4 = 85 := rfl
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, he1, hu1, hu2, hu3, hu4,
    s2four_ehat_two h2 hq, s2four_ehat_three h2 hq, s2four_ehat_four h2 hq]
  ring

/-- The level-four kernel law: `16p + 8q + 20t₀ + 42t₁ + 85t₂ = 0`. -/
theorem s2four_mem_ker_four_iff (v : ℤ × ℤ × (Fin 3 → ℤ)) :
    (Multiplicative.ofAdd v : LevelExponentLattice 4) ∈
        MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4) ↔
      16 * v.1 + 8 * v.2.1 + 20 * v.2.2 0 + 42 * v.2.2 1 + 85 * v.2.2 2 = 0 := by
  rw [MonoidHom.mem_ker, s2four_levelExponentHeight_four, ofAdd_eq_one]

/-- General-element form of the level-four kernel law. -/
theorem s2four_mem_ker_four_iff' (g : LevelExponentLattice 4) :
    g ∈ MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4) ↔
      16 * (Multiplicative.toAdd g).1 + 8 * (Multiplicative.toAdd g).2.1 +
          20 * (Multiplicative.toAdd g).2.2 0 + 42 * (Multiplicative.toAdd g).2.2 1 +
          85 * (Multiplicative.toAdd g).2.2 2 = 0 := by
  have h := s2four_mem_ker_four_iff h2 hq (Multiplicative.toAdd g)
  rwa [ofAdd_toAdd] at h

/-! ## Part 2 — the depth-four ambient letters and the `psi_root` law

The T3 datum's stage residuals are all `ψ_i = X − C 1` (`C136t.s2WitnessFour`), so — exactly
as at NP-6 — the unit `1` is the transported root at EVERY index and for ANY field `L`,
with no appeal to the residue cardinality.  Off the constrained (gauge-live) range the
value is a total-function convenience; no law reads it. -/

section AmbientLetter

variable (L : Type uL) [Field L]

/-- **The depth-four ambient letters** (the `SplitNodePointSource.ambientLetter` field
shape at the T3 datum): the unit `1` at every index — NP-6's `s2AmbientLetter`, one tower
deeper. -/
noncomputable def s2AmbientLetterFour : ℕ → Lˣ := fun _ => 1

/-- Anti-drift pin: every ambient letter is the unit `1`. -/
theorem s2AmbientLetterFour_apply (i : ℕ) : s2AmbientLetterFour L i = 1 := rfl

variable [Algebra ((s2DepthFour h2 hq).fld 4) L]

/-- ★ **The `psi_root` field law at the R0 receiver**: the ambient letter is a root of the
stage residual `ψ_i = X − C 1`, transported through the SAME receiver level map every
Part-6 and Part-7 dictionary statement uses — the exact `SplitNodePointSource.psi_root` shape at
`(s2DepthFour, s2TerminalReceiverFour)`.  Holds at every index (stated gauge-live, the
field's own quantifier). -/
theorem s2AmbientLetterFour_psi_root (i : ℕ) (_hi : GaugeLive 4 i) :
    Polynomial.eval₂
        ((algebraMap ((s2DepthFour h2 hq).fld 4) L).comp
          ((s2TerminalReceiverFour h2 hq).levelHom i))
        ((s2AmbientLetterFour L i : Lˣ) : L) ((s2DepthFour h2 hq).ψ i) = 0 := by
  have hψ : (s2DepthFour h2 hq).ψ i = Polynomial.X - Polynomial.C 1 := rfl
  rw [hψ, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one]
  simp [s2AmbientLetterFour]

end AmbientLetter

/-! ## Part 3 — the distinguished-generator coordinates

The wrap generator is `(−1, 2, 0)` at every level (S2 frame numerals `u₁ = 1`, `e₁ = 2`).
Each letter `Λ_a = Φ_{a+1}^{e_{a+2}}·n̂_i(e_{a+2}·(ê_i/ê_{a+2})·u_{a+2})⁻¹` needs its CC-4
Laurent-solve exponents; the six solves below are the depth-four extension of D62w's
`d2g2`/`d3g2`/`d3g3` regressions.  Per the fleet lesson the WF-compiled solve is closed by
`simp only [DeepTower.laurentSolve, …]` + `decide`, never a bare `rfl`. -/

/-- The wrap class carries the coordinates `(−1, 2, 0)` at EVERY level of the depth-four
tower (D62w's `d2g1`/`d3g1` rows, uniformly): `wrapGen = x^{e₁}·π^{−u₁}` at `u₁ = 1`,
`e₁ = 2`. -/
theorem s2four_wrapClass_coe {i : ℕ} (hi : StageLive 4 i) :
    ((s2DepthFour h2 hq).wrapClass hi : LevelExponentLattice i) =
      Multiplicative.ofAdd ((-1 : ℤ), (2 : ℤ), (0 : Fin (i - 1) → ℤ)) := by
  rw [DeepTower.wrapClass_coe]
  rfl

/-- Laurent solve, level two, height `10 = e₂·u₂`: `n̂₂(10) = π²·x` (exponents `(2, 1, 0)`). -/
theorem s2four_laurentSolve_one_ten :
    (s2DepthFour h2 hq).laurentSolve 1 10 = (2, 1, fun _ => 0) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hh, he1]
  decide

/-- Laurent solve, level three, height `20 = e₂·(ê₃/ê₂)·u₂`: `n̂₃(20) = π²·x`
(exponents `(2, 1, 0, 0)`). -/
theorem s2four_laurentSolve_two_twenty :
    (s2DepthFour h2 hq).laurentSolve 2 20 = (2, 1, ![0, 0]) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hu3 : (s2DepthFour h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthFour h2 hq).e (1 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hu3, he3,
    hh, he1]
  decide

/-- Laurent solve, level three, height `42 = e₃·u₃`: `n̂₃(42) = π⁴·Φ₁`
(exponents `(4, 0, 1, 0)`). -/
theorem s2four_laurentSolve_two_fortytwo :
    (s2DepthFour h2 hq).laurentSolve 2 42 = (4, 0, ![1, 0]) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hu3 : (s2DepthFour h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthFour h2 hq).e (1 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hu3, he3,
    hh, he1]
  decide

/-- Laurent solve, level four, height `40 = e₂·(ê₄/ê₂)·u₂`: `n̂₄(40) = π²·x`
(exponents `(2, 1, 0, 0, 0)`). -/
theorem s2four_laurentSolve_three_forty :
    (s2DepthFour h2 hq).laurentSolve 3 40 = (2, 1, ![0, 0, 0]) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hu3 : (s2DepthFour h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthFour h2 hq).e (1 + 2) = 2 := rfl
  have hu4 : (s2DepthFour h2 hq).u (2 + 2) = 85 := rfl
  have he4 : (s2DepthFour h2 hq).e (2 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hu3, he3,
    hu4, he4, hh, he1]
  decide

/-- Laurent solve, level four, height `84 = e₃·(ê₄/ê₃)·u₃`: `n̂₄(84) = π⁴·Φ₁`
(exponents `(4, 0, 1, 0, 0)`). -/
theorem s2four_laurentSolve_three_eightyfour :
    (s2DepthFour h2 hq).laurentSolve 3 84 = (4, 0, ![1, 0, 0]) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hu3 : (s2DepthFour h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthFour h2 hq).e (1 + 2) = 2 := rfl
  have hu4 : (s2DepthFour h2 hq).u (2 + 2) = 85 := rfl
  have he4 : (s2DepthFour h2 hq).e (2 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hu3, he3,
    hu4, he4, hh, he1]
  decide

/-- Laurent solve, level four, height `170 = e₄·u₄`: `n̂₄(170) = π⁸·Φ₂`
(exponents `(8, 0, 0, 1, 0)`). -/
theorem s2four_laurentSolve_three_oneseventy :
    (s2DepthFour h2 hq).laurentSolve 3 170 = (8, 0, ![0, 1, 0]) := by
  have hu2 : (s2DepthFour h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthFour h2 hq).e (0 + 2) = 2 := rfl
  have hu3 : (s2DepthFour h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthFour h2 hq).e (1 + 2) = 2 := rfl
  have hu4 : (s2DepthFour h2 hq).u (2 + 2) = 85 := rfl
  have he4 : (s2DepthFour h2 hq).e (2 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu2, he2, hu3, he3,
    hu4, he4, hh, he1]
  decide

/-- Letter coordinates, level two: `Λ₀ = Φ₁²·n̂₂(10)⁻¹` has exponents `(−2, −1, 2)` —
D62w's `d2g2`, at the depth-four tower's own level two. -/
theorem s2four_letterClass_two_coe (hi : StageLive 4 2) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (2 - 1))) :
        LevelExponentLattice 2) =
      Multiplicative.ofAdd ((-2 : ℤ), (-1 : ℤ), fun _ : Fin 1 => (2 : ℤ)) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 2 = 2 from rfl, s2four_ehat_two h2 hq,
    show (s2DepthFour h2 hq).u 2 = 5 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_one_ten]
  rw [show (s2DepthFour h2 hq).laurentSolve (2 - 1) 10 = (2, 1, fun _ => 0) from
    s2four_laurentSolve_one_ten h2 hq]
  decide

/-- ★ Letter coordinates, level three, `a = 0`: `Λ₀ = Φ₁²·n̂₃(20)⁻¹` has exponents
`(−2, −1, 2, 0)` — D62w's `d3g2`, now a theorem of the T3 datum. -/
theorem s2four_letterClass_three_zero_coe (hi : StageLive 4 3) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (3 - 1))) :
        LevelExponentLattice 3) =
      Multiplicative.ofAdd ((-2 : ℤ), (-1 : ℤ), ![2, 0]) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 2 = 2 from rfl, s2four_ehat_two h2 hq,
    s2four_ehat_three h2 hq, show (s2DepthFour h2 hq).u 2 = 5 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_two_twenty]
  rw [show (s2DepthFour h2 hq).laurentSolve (3 - 1) 20 = (2, 1, ![0, 0]) from
    s2four_laurentSolve_two_twenty h2 hq]
  decide

/-- ★ Letter coordinates, level three, `a = 1`: `Λ₁ = Φ₂²·n̂₃(42)⁻¹` has exponents
`(−4, 0, −1, 2)` — D62w's `d3g3`, now a theorem of the T3 datum. -/
theorem s2four_letterClass_three_one_coe (hi : StageLive 4 3) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (1 : Fin (3 - 1))) :
        LevelExponentLattice 3) =
      Multiplicative.ofAdd ((-4 : ℤ), (0 : ℤ), ![-1, 2]) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 3 = 2 from rfl, s2four_ehat_three h2 hq,
    show (s2DepthFour h2 hq).u 3 = 21 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_two_fortytwo]
  rw [show (s2DepthFour h2 hq).laurentSolve (3 - 1) 42 = (4, 0, ![1, 0]) from
    s2four_laurentSolve_two_fortytwo h2 hq]
  decide

/-- ★ Letter coordinates, level four, `a = 0`: `Λ₀ = Φ₁²·n̂₄(40)⁻¹` has exponents
`(−2, −1, 2, 0, 0)`. -/
theorem s2four_letterClass_four_zero_coe (hi : StageLive 4 4) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (4 - 1))) :
        LevelExponentLattice 4) =
      Multiplicative.ofAdd ((-2 : ℤ), (-1 : ℤ), ![2, 0, 0]) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 2 = 2 from rfl, s2four_ehat_two h2 hq,
    s2four_ehat_four h2 hq, show (s2DepthFour h2 hq).u 2 = 5 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_three_forty]
  rw [show (s2DepthFour h2 hq).laurentSolve (4 - 1) 40 = (2, 1, ![0, 0, 0]) from
    s2four_laurentSolve_three_forty h2 hq]
  decide

/-- ★ Letter coordinates, level four, `a = 1`: `Λ₁ = Φ₂²·n̂₄(84)⁻¹` has exponents
`(−4, 0, −1, 2, 0)`. -/
theorem s2four_letterClass_four_one_coe (hi : StageLive 4 4) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (1 : Fin (4 - 1))) :
        LevelExponentLattice 4) =
      Multiplicative.ofAdd ((-4 : ℤ), (0 : ℤ), ![-1, 2, 0]) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 3 = 2 from rfl, s2four_ehat_three h2 hq,
    s2four_ehat_four h2 hq, show (s2DepthFour h2 hq).u 3 = 21 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_three_eightyfour]
  rw [show (s2DepthFour h2 hq).laurentSolve (4 - 1) 84 = (4, 0, ![1, 0, 0]) from
    s2four_laurentSolve_three_eightyfour h2 hq]
  decide

/-- ★ Letter coordinates, level four, `a = 2`: `Λ₂ = Φ₃²·n̂₄(170)⁻¹` has exponents
`(−8, 0, 0, −1, 2)`. -/
theorem s2four_letterClass_four_two_coe (hi : StageLive 4 4) :
    (((s2LaurentNormalizerFour h2 hq).letterClass hi (2 : Fin (4 - 1))) :
        LevelExponentLattice 4) =
      Multiplicative.ofAdd ((-8 : ℤ), (0 : ℤ), ![0, -1, 2]) := by
  rw [LaurentNormalizer.letterClass_coe, s2LaurentNormalizerFour_norm_eq]
  norm_num [show (s2DepthFour h2 hq).e 4 = 2 from rfl, s2four_ehat_four h2 hq,
    show (s2DepthFour h2 hq).u 4 = 85 from rfl,
    DeepTower.laurentNormAt, s2four_laurentSolve_three_oneseventy]
  rw [show (s2DepthFour h2 hq).laurentSolve (4 - 1) 170 = (8, 0, ![0, 1, 0]) from
    s2four_laurentSolve_three_oneseventy h2 hq]
  decide

/-! ## Part 4 — the canonical reads (the distinguished-generator basis inversion)

At each live level the generator coordinate matrix (Part 3) is triangular with `2`s on the
`Φ`-block diagonal, so the change of basis `g = W₀^m · ∏_a Λ_a^{s_a}` is solvable in raw
lattice coordinates; every division below is EXACT on the kernel (the Part-1 kernel law
forces the evenness — the `_add` lemmas are precisely that arithmetic).  NO spanning claim
is made beyond these formulas (the triangular-basis bridge stays OPEN, per C130cr): the
generator regressions of Part 5 are consequences of the formulas at the Part-3 coordinates,
exactly the NP-7 discipline. -/

/-- Generic single-letter exponent read (this file's one generic helper — general lemma,
flagged): an integer exponent functional additive on a group induces a one-letter `zpow`
read. -/
def zpowHom {G : Type*} [Group G] {A : Type*} [Group A] (β : A) (E : G → ℤ)
    (hE : ∀ g g', E (g * g') = E g + E g') : G →* A :=
  MonoidHom.mk' (fun g => β ^ E g) fun g g' => by rw [hE, zpow_add]

/-- Anti-drift pin: `zpowHom` is the displayed power, nothing else. -/
theorem zpowHom_apply {G : Type*} [Group G] {A : Type*} [Group A] (β : A) (E : G → ℤ)
    (hE : ∀ g g', E (g * g') = E g + E g') (g : G) : zpowHom β E hE g = β ^ E g := rfl

/-- Level-one η-exponent: `m = −p` (no letters at level one). -/
def s2Exp1Eta (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1)) : ℤ :=
  -(Multiplicative.toAdd (g : LevelExponentLattice 1)).1

theorem s2Exp1Eta_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1)) :
    s2Exp1Eta h2 hq (g * g') = s2Exp1Eta h2 hq g + s2Exp1Eta h2 hq g' := by
  simp only [s2Exp1Eta, MulMemClass.coe_mul, toAdd_mul, Prod.fst_add]
  ring

/-- Level-two η-exponent: `m = −p − t₀` (invert `(m, s)·((−1,2,0),(−2,−1,2))`). -/
def s2Exp2Eta (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2)) : ℤ :=
  -(Multiplicative.toAdd (g : LevelExponentLattice 2)).1 -
    (Multiplicative.toAdd (g : LevelExponentLattice 2)).2.2 0

theorem s2Exp2Eta_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2)) :
    s2Exp2Eta h2 hq (g * g') = s2Exp2Eta h2 hq g + s2Exp2Eta h2 hq g' := by
  simp only [s2Exp2Eta, MulMemClass.coe_mul, toAdd_mul, Prod.fst_add, Prod.snd_add,
    Pi.add_apply]
  ring

/-- Level-two `Λ₀`-exponent: `s₀ = t₀/2` (exact: the kernel law `4p + 2q + 5t₀ = 0` forces
`t₀` even). -/
def s2Exp2B2 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2)) : ℤ :=
  (Multiplicative.toAdd (g : LevelExponentLattice 2)).2.2 0 / 2

theorem s2Exp2B2_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2)) :
    s2Exp2B2 h2 hq (g * g') = s2Exp2B2 h2 hq g + s2Exp2B2 h2 hq g' := by
  have hg := (s2four_mem_ker_two_iff' h2 hq (g : LevelExponentLattice 2)).mp g.2
  have hg' := (s2four_mem_ker_two_iff' h2 hq (g' : LevelExponentLattice 2)).mp g'.2
  simp only [s2Exp2B2, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-three η-exponent: `m = −p − t₀ − 5·(t₁/2)` (invert the triangular basis
`(−1,2,0,0), (−2,−1,2,0), (−4,0,−1,2)`). -/
def s2Exp3Eta (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) : ℤ :=
  -(Multiplicative.toAdd (g : LevelExponentLattice 3)).1 -
    (Multiplicative.toAdd (g : LevelExponentLattice 3)).2.2 0 -
    5 * ((Multiplicative.toAdd (g : LevelExponentLattice 3)).2.2 1 / 2)

theorem s2Exp3Eta_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) :
    s2Exp3Eta h2 hq (g * g') = s2Exp3Eta h2 hq g + s2Exp3Eta h2 hq g' := by
  have hg := (s2four_mem_ker_three_iff' h2 hq (g : LevelExponentLattice 3)).mp g.2
  have hg' := (s2four_mem_ker_three_iff' h2 hq (g' : LevelExponentLattice 3)).mp g'.2
  simp only [s2Exp3Eta, MulMemClass.coe_mul, toAdd_mul, Prod.fst_add, Prod.snd_add,
    Pi.add_apply]
  omega

/-- Level-three `Λ₀`-exponent: `s₀ = (t₀ + t₁/2)/2` (both divisions exact on the kernel:
`8p + 4q + 10t₀ + 21t₁ = 0` forces `t₁` even and then `t₀ + t₁/2` even). -/
def s2Exp3B2 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) : ℤ :=
  ((Multiplicative.toAdd (g : LevelExponentLattice 3)).2.2 0 +
    (Multiplicative.toAdd (g : LevelExponentLattice 3)).2.2 1 / 2) / 2

theorem s2Exp3B2_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) :
    s2Exp3B2 h2 hq (g * g') = s2Exp3B2 h2 hq g + s2Exp3B2 h2 hq g' := by
  have hg := (s2four_mem_ker_three_iff' h2 hq (g : LevelExponentLattice 3)).mp g.2
  have hg' := (s2four_mem_ker_three_iff' h2 hq (g' : LevelExponentLattice 3)).mp g'.2
  simp only [s2Exp3B2, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-three `Λ₁`-exponent: `s₁ = t₁/2`. -/
def s2Exp3B3 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) : ℤ :=
  (Multiplicative.toAdd (g : LevelExponentLattice 3)).2.2 1 / 2

theorem s2Exp3B3_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) :
    s2Exp3B3 h2 hq (g * g') = s2Exp3B3 h2 hq g + s2Exp3B3 h2 hq g' := by
  have hg := (s2four_mem_ker_three_iff' h2 hq (g : LevelExponentLattice 3)).mp g.2
  have hg' := (s2four_mem_ker_three_iff' h2 hq (g' : LevelExponentLattice 3)).mp g'.2
  simp only [s2Exp3B3, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-four `Λ₂`-exponent: `s₂ = t₂/2` (kernel law `16p + 8q + 20t₀ + 42t₁ + 85t₂ = 0`
forces `t₂` even). -/
def s2Exp4B4 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) : ℤ :=
  (Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 2 / 2

theorem s2Exp4B4_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) :
    s2Exp4B4 h2 hq (g * g') = s2Exp4B4 h2 hq g + s2Exp4B4 h2 hq g' := by
  have hg := (s2four_mem_ker_four_iff' h2 hq (g : LevelExponentLattice 4)).mp g.2
  have hg' := (s2four_mem_ker_four_iff' h2 hq (g' : LevelExponentLattice 4)).mp g'.2
  simp only [s2Exp4B4, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-four `Λ₁`-exponent: `s₁ = (t₁ + t₂/2)/2`. -/
def s2Exp4B3 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) : ℤ :=
  ((Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 1 +
    (Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 2 / 2) / 2

theorem s2Exp4B3_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) :
    s2Exp4B3 h2 hq (g * g') = s2Exp4B3 h2 hq g + s2Exp4B3 h2 hq g' := by
  have hg := (s2four_mem_ker_four_iff' h2 hq (g : LevelExponentLattice 4)).mp g.2
  have hg' := (s2four_mem_ker_four_iff' h2 hq (g' : LevelExponentLattice 4)).mp g'.2
  simp only [s2Exp4B3, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-four `Λ₀`-exponent: `s₀ = (t₀ + (t₁ + t₂/2)/2)/2`. -/
def s2Exp4B2 (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) : ℤ :=
  ((Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 0 +
    ((Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 1 +
      (Multiplicative.toAdd (g : LevelExponentLattice 4)).2.2 2 / 2) / 2) / 2

set_option maxHeartbeats 1600000 in
theorem s2Exp4B2_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) :
    s2Exp4B2 h2 hq (g * g') = s2Exp4B2 h2 hq g + s2Exp4B2 h2 hq g' := by
  have hg := (s2four_mem_ker_four_iff' h2 hq (g : LevelExponentLattice 4)).mp g.2
  have hg' := (s2four_mem_ker_four_iff' h2 hq (g' : LevelExponentLattice 4)).mp g'.2
  simp only [s2Exp4B2, MulMemClass.coe_mul, toAdd_mul, Prod.snd_add, Pi.add_apply]
  omega

/-- Level-four η-exponent: `m = −p − 2s₀ − 4s₁ − 8s₂` (the `π`-row of the inversion). -/
def s2Exp4Eta (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) : ℤ :=
  -(Multiplicative.toAdd (g : LevelExponentLattice 4)).1 - 2 * s2Exp4B2 h2 hq g -
    4 * s2Exp4B3 h2 hq g - 8 * s2Exp4B4 h2 hq g

set_option maxHeartbeats 1600000 in
theorem s2Exp4Eta_add (g g' : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) :
    s2Exp4Eta h2 hq (g * g') = s2Exp4Eta h2 hq g + s2Exp4Eta h2 hq g' := by
  have hg := (s2four_mem_ker_four_iff' h2 hq (g : LevelExponentLattice 4)).mp g.2
  have hg' := (s2four_mem_ker_four_iff' h2 hq (g' : LevelExponentLattice 4)).mp g'.2
  simp only [s2Exp4Eta, s2Exp4B2, s2Exp4B3, s2Exp4B4, MulMemClass.coe_mul, toAdd_mul,
    Prod.fst_add, Prod.snd_add, Pi.add_apply]
  omega

section Reads

variable (L : Type uL) [Field L]

/-- **The depth-four canonical read, level one**: `g ↦ η^{−p}` — NP-7's level-one read at
the T3 datum. -/
noncomputable def s2CanonicalReadFour1 :
    MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1) →* Lˣ :=
  zpowHom (s2AmbientLetterFour L 1) (s2Exp1Eta h2 hq) (s2Exp1Eta_add h2 hq)

/-- Anti-drift pin: the level-one read is the displayed formula, nothing else. -/
theorem s2CanonicalReadFour1_coe
    (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 1)) :
    s2CanonicalReadFour1 h2 hq L g = s2AmbientLetterFour L 1 ^ s2Exp1Eta h2 hq g := rfl

/-- **The depth-four canonical read, level two**: `g ↦ η^{−p−t₀}·β₂^{t₀/2}` — NP-7's
level-two read at the T3 datum. -/
noncomputable def s2CanonicalReadFour2 :
    MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2) →* Lˣ :=
  zpowHom (s2AmbientLetterFour L 1) (s2Exp2Eta h2 hq) (s2Exp2Eta_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 2) (s2Exp2B2 h2 hq) (s2Exp2B2_add h2 hq)

/-- Anti-drift pin: the level-two read is the displayed formula, nothing else. -/
theorem s2CanonicalReadFour2_coe
    (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 2)) :
    s2CanonicalReadFour2 h2 hq L g =
      s2AmbientLetterFour L 1 ^ s2Exp2Eta h2 hq g *
        s2AmbientLetterFour L 2 ^ s2Exp2B2 h2 hq g := rfl

/-- ★ **The depth-four canonical read, level three** — the read of the unique deep-live
level: `g ↦ η^{−p−t₀−5(t₁/2)}·β₂^{(t₀+t₁/2)/2}·β₃^{t₁/2}`. -/
noncomputable def s2CanonicalReadFour3 :
    MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3) →* Lˣ :=
  zpowHom (s2AmbientLetterFour L 1) (s2Exp3Eta h2 hq) (s2Exp3Eta_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 2) (s2Exp3B2 h2 hq) (s2Exp3B2_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 3) (s2Exp3B3 h2 hq) (s2Exp3B3_add h2 hq)

/-- Anti-drift pin: the level-three read is the displayed formula, nothing else. -/
theorem s2CanonicalReadFour3_coe
    (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) :
    s2CanonicalReadFour3 h2 hq L g =
      s2AmbientLetterFour L 1 ^ s2Exp3Eta h2 hq g *
        s2AmbientLetterFour L 2 ^ s2Exp3B2 h2 hq g *
        s2AmbientLetterFour L 3 ^ s2Exp3B3 h2 hq g := rfl

/-- **The depth-four canonical read, level four** (the terminal level):
`g ↦ η^{m}·β₂^{s₀}·β₃^{s₁}·β₄^{s₂}` at the Part-4 exponents. -/
noncomputable def s2CanonicalReadFour4 :
    MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4) →* Lˣ :=
  zpowHom (s2AmbientLetterFour L 1) (s2Exp4Eta h2 hq) (s2Exp4Eta_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 2) (s2Exp4B2 h2 hq) (s2Exp4B2_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 3) (s2Exp4B3 h2 hq) (s2Exp4B3_add h2 hq) *
    zpowHom (s2AmbientLetterFour L 4) (s2Exp4B4 h2 hq) (s2Exp4B4_add h2 hq)

/-- Anti-drift pin: the level-four read is the displayed formula, nothing else. -/
theorem s2CanonicalReadFour4_coe
    (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 4)) :
    s2CanonicalReadFour4 h2 hq L g =
      s2AmbientLetterFour L 1 ^ s2Exp4Eta h2 hq g *
        s2AmbientLetterFour L 2 ^ s2Exp4B2 h2 hq g *
        s2AmbientLetterFour L 3 ^ s2Exp4B3 h2 hq g *
        s2AmbientLetterFour L 4 ^ s2Exp4B4 h2 hq g := rfl

/-- ★ **The total depth-four canonical L-valued kernel read** — the exact
`SplitNodePointSource.canonicalRead` field shape at the T3 datum: the constructed reads at
the four live levels, the trivial hom at junk indices (no law reads those — NP-7's total
pattern one tower deeper). -/
noncomputable def s2CanonicalReadFour :
    (i : ℕ) → MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) i) →* Lˣ
  | 1 => s2CanonicalReadFour1 h2 hq L
  | 2 => s2CanonicalReadFour2 h2 hq L
  | 3 => s2CanonicalReadFour3 h2 hq L
  | 4 => s2CanonicalReadFour4 h2 hq L
  | _ => 1

/-- Anti-drift pin: the total read at level one. -/
theorem s2CanonicalReadFour_one :
    s2CanonicalReadFour h2 hq L 1 = s2CanonicalReadFour1 h2 hq L := rfl

/-- Anti-drift pin: the total read at level two. -/
theorem s2CanonicalReadFour_two :
    s2CanonicalReadFour h2 hq L 2 = s2CanonicalReadFour2 h2 hq L := rfl

/-- Anti-drift pin: the total read at level three. -/
theorem s2CanonicalReadFour_three :
    s2CanonicalReadFour h2 hq L 3 = s2CanonicalReadFour3 h2 hq L := rfl

/-- Anti-drift pin: the total read at level four. -/
theorem s2CanonicalReadFour_four :
    s2CanonicalReadFour h2 hq L 4 = s2CanonicalReadFour4 h2 hq L := rfl

end Reads

/-! ## Part 5 — the generator regressions

The read of the wrap class is `η = s2AmbientLetterFour L 1` and the read of `Λ_a` is
`β_{a+2} = s2AmbientLetterFour L (a+2)` at every live level — proved through the Part-3
COORDINATES (the basis-inversion arithmetic), never through the S2 collapse of the letters
to `1`; the collapse is recorded separately as a consequence, exactly NP-7's discipline. -/

section Regressions

variable (L : Type uL) [Field L]

/-- ★ Generator regression, level one, wrap class: `m = −(−1) = 1`. -/
theorem s2CanonicalReadFour1_wrapClass (hi : StageLive 4 1) :
    s2CanonicalReadFour1 h2 hq L ((s2DepthFour h2 hq).wrapClass hi) =
      s2AmbientLetterFour L 1 := by
  rw [s2CanonicalReadFour1_coe]
  simp only [s2Exp1Eta, s2four_wrapClass_coe h2 hq hi, toAdd_ofAdd]
  norm_num

/-- ★ Generator regression, level two, wrap class: `(m, s₀) = (1, 0)`. -/
theorem s2CanonicalReadFour2_wrapClass (hi : StageLive 4 2) :
    s2CanonicalReadFour2 h2 hq L ((s2DepthFour h2 hq).wrapClass hi) =
      s2AmbientLetterFour L 1 := by
  rw [s2CanonicalReadFour2_coe]
  simp only [s2Exp2Eta, s2Exp2B2, s2four_wrapClass_coe h2 hq hi, toAdd_ofAdd,
    Pi.zero_apply]
  norm_num

/-- ★ Generator regression, level two, letter class: `(m, s₀) = (0, 1)` at the coordinates
`(−2, −1, 2)`. -/
theorem s2CanonicalReadFour2_letterClass (hi : StageLive 4 2) :
    s2CanonicalReadFour2 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (2 - 1))) =
      s2AmbientLetterFour L 2 := by
  rw [s2CanonicalReadFour2_coe]
  simp only [s2Exp2Eta, s2Exp2B2, s2four_letterClass_two_coe h2 hq hi, toAdd_ofAdd]
  norm_num

/-- ★ Generator regression, level three, wrap class: `(m, s₀, s₁) = (1, 0, 0)`. -/
theorem s2CanonicalReadFour3_wrapClass (hi : StageLive 4 3) :
    s2CanonicalReadFour3 h2 hq L ((s2DepthFour h2 hq).wrapClass hi) =
      s2AmbientLetterFour L 1 := by
  rw [s2CanonicalReadFour3_coe]
  simp only [s2Exp3Eta, s2Exp3B2, s2Exp3B3, s2four_wrapClass_coe h2 hq hi, toAdd_ofAdd,
    Pi.zero_apply]
  norm_num

/-- ★★ Generator regression, level three, `Λ₀`: `(m, s₀, s₁) = (0, 1, 0)` at the
coordinates `(−2, −1, 2, 0)` — the deep-live level's first letter tie. -/
theorem s2CanonicalReadFour3_letterClass_zero (hi : StageLive 4 3) :
    s2CanonicalReadFour3 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (3 - 1))) =
      s2AmbientLetterFour L 2 := by
  rw [s2CanonicalReadFour3_coe]
  simp only [s2Exp3Eta, s2Exp3B2, s2Exp3B3, s2four_letterClass_three_zero_coe h2 hq hi,
    toAdd_ofAdd, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- ★★ Generator regression, level three, `Λ₁`: `(m, s₀, s₁) = (0, 0, 1)` at the
coordinates `(−4, 0, −1, 2)` — the deep-live level's second letter tie. -/
theorem s2CanonicalReadFour3_letterClass_one (hi : StageLive 4 3) :
    s2CanonicalReadFour3 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (1 : Fin (3 - 1))) =
      s2AmbientLetterFour L 3 := by
  rw [s2CanonicalReadFour3_coe]
  simp only [s2Exp3Eta, s2Exp3B2, s2Exp3B3, s2four_letterClass_three_one_coe h2 hq hi,
    toAdd_ofAdd, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- ★★ The level-three letter regressions, uniformly: the read of `Λ_a` is the ambient
letter at the letter's own tower stage `a + 2` — the exact stage pairing of G4's
`letter_receiver` (`letterZ (a+2)` ↔ `Λ_a`, cf. `C130s17.S2SourceFrontier.letter_compat`). -/
theorem s2CanonicalReadFour3_letterClass (hi : StageLive 4 3) (a : Fin (3 - 1)) :
    s2CanonicalReadFour3 h2 hq L ((s2LaurentNormalizerFour h2 hq).letterClass hi a) =
      s2AmbientLetterFour L (a.1 + 2) := by
  fin_cases a
  · exact s2CanonicalReadFour3_letterClass_zero h2 hq L hi
  · exact s2CanonicalReadFour3_letterClass_one h2 hq L hi

/-- ★ Generator regression, level four, wrap class: `(m, s₀, s₁, s₂) = (1, 0, 0, 0)`. -/
theorem s2CanonicalReadFour4_wrapClass (hi : StageLive 4 4) :
    s2CanonicalReadFour4 h2 hq L ((s2DepthFour h2 hq).wrapClass hi) =
      s2AmbientLetterFour L 1 := by
  rw [s2CanonicalReadFour4_coe]
  simp only [s2Exp4Eta, s2Exp4B2, s2Exp4B3, s2Exp4B4, s2four_wrapClass_coe h2 hq hi,
    toAdd_ofAdd, Pi.zero_apply]
  norm_num

/-- ★ Generator regression, level four, `Λ₀`: `(m, s₀, s₁, s₂) = (0, 1, 0, 0)` at the
coordinates `(−2, −1, 2, 0, 0)`. -/
theorem s2CanonicalReadFour4_letterClass_zero (hi : StageLive 4 4) :
    s2CanonicalReadFour4 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (4 - 1))) =
      s2AmbientLetterFour L 2 := by
  rw [s2CanonicalReadFour4_coe]
  simp only [s2Exp4Eta, s2Exp4B2, s2Exp4B3, s2Exp4B4,
    s2four_letterClass_four_zero_coe h2 hq hi, toAdd_ofAdd,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [show (![(2 : ℤ), 0, 0]) 2 = 0 from by decide]

/-- ★ Generator regression, level four, `Λ₁`: `(m, s₀, s₁, s₂) = (0, 0, 1, 0)` at the
coordinates `(−4, 0, −1, 2, 0)`. -/
theorem s2CanonicalReadFour4_letterClass_one (hi : StageLive 4 4) :
    s2CanonicalReadFour4 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (1 : Fin (4 - 1))) =
      s2AmbientLetterFour L 3 := by
  rw [s2CanonicalReadFour4_coe]
  simp only [s2Exp4Eta, s2Exp4B2, s2Exp4B3, s2Exp4B4,
    s2four_letterClass_four_one_coe h2 hq hi, toAdd_ofAdd,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [show (![(-1 : ℤ), 2, 0]) 2 = 0 from by decide]

/-- ★ Generator regression, level four, `Λ₂`: `(m, s₀, s₁, s₂) = (0, 0, 0, 1)` at the
coordinates `(−8, 0, 0, −1, 2)`. -/
theorem s2CanonicalReadFour4_letterClass_two (hi : StageLive 4 4) :
    s2CanonicalReadFour4 h2 hq L
        ((s2LaurentNormalizerFour h2 hq).letterClass hi (2 : Fin (4 - 1))) =
      s2AmbientLetterFour L 4 := by
  rw [s2CanonicalReadFour4_coe]
  simp only [s2Exp4Eta, s2Exp4B2, s2Exp4B3, s2Exp4B4,
    s2four_letterClass_four_two_coe h2 hq hi, toAdd_ofAdd,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [show (![(0 : ℤ), -1, 2]) 2 = 2 from by decide]

/-- ★ The level-four letter regressions, uniformly (same stage pairing `Λ_a ↔ a + 2`). -/
theorem s2CanonicalReadFour4_letterClass (hi : StageLive 4 4) (a : Fin (4 - 1)) :
    s2CanonicalReadFour4 h2 hq L ((s2LaurentNormalizerFour h2 hq).letterClass hi a) =
      s2AmbientLetterFour L (a.1 + 2) := by
  fin_cases a
  · exact s2CanonicalReadFour4_letterClass_zero h2 hq L hi
  · exact s2CanonicalReadFour4_letterClass_one h2 hq L hi
  · exact s2CanonicalReadFour4_letterClass_two h2 hq L hi

/-- The distinguished-generator view, level two: the read of `W₀^m·Λ₀^{t₀}` is
`η^m·β₂^{t₀}` (NP-7's level-two display, at the depth-four tower). -/
theorem s2CanonicalReadFour2_generatorWord (hi : StageLive 4 2) (m : ℤ)
    (t : Fin (2 - 1) → ℤ) :
    s2CanonicalReadFour2 h2 hq L ((s2LaurentNormalizerFour h2 hq).generatorWord hi m t) =
      s2AmbientLetterFour L 1 ^ m * s2AmbientLetterFour L 2 ^ t 0 := by
  rw [LaurentNormalizer.generatorWord, map_mul, map_zpow,
    s2CanonicalReadFour2_wrapClass h2 hq L hi, map_prod, Fin.prod_univ_one, map_zpow,
    s2CanonicalReadFour2_letterClass h2 hq L hi]

/-- ★★ **The distinguished-generator view, level three, assembled**: the read of ANY
`W₀^m·Λ₀^{t₀}·Λ₁^{t₁}` is `η^m·β₂^{t₀}·β₃^{t₁}` — freeze v2 §4's display shape
(`canonicalRes(τ) = η^m·∏β_a^{t_a}`) at the unique deep-live level, mirroring
`C130cr.SplitNodePointSource.canonicalRead_generatorWord` at this concrete read. -/
theorem s2CanonicalReadFour3_generatorWord (hi : StageLive 4 3) (m : ℤ)
    (t : Fin (3 - 1) → ℤ) :
    s2CanonicalReadFour3 h2 hq L ((s2LaurentNormalizerFour h2 hq).generatorWord hi m t) =
      s2AmbientLetterFour L 1 ^ m * s2AmbientLetterFour L 2 ^ t 0 *
        s2AmbientLetterFour L 3 ^ t 1 := by
  rw [LaurentNormalizer.generatorWord, map_mul, map_zpow,
    s2CanonicalReadFour3_wrapClass h2 hq L hi, map_prod, Fin.prod_univ_two, map_zpow,
    map_zpow, s2CanonicalReadFour3_letterClass_zero h2 hq L hi,
    s2CanonicalReadFour3_letterClass_one h2 hq L hi, mul_assoc]

/-- The distinguished-generator view, level four, assembled. -/
theorem s2CanonicalReadFour4_generatorWord (hi : StageLive 4 4) (m : ℤ)
    (t : Fin (4 - 1) → ℤ) :
    s2CanonicalReadFour4 h2 hq L ((s2LaurentNormalizerFour h2 hq).generatorWord hi m t) =
      s2AmbientLetterFour L 1 ^ m * s2AmbientLetterFour L 2 ^ t 0 *
        s2AmbientLetterFour L 3 ^ t 1 * s2AmbientLetterFour L 4 ^ t 2 := by
  rw [LaurentNormalizer.generatorWord, map_mul, map_zpow,
    s2CanonicalReadFour4_wrapClass h2 hq L hi, map_prod, Fin.prod_univ_three, map_zpow,
    map_zpow, map_zpow, s2CanonicalReadFour4_letterClass_zero h2 hq L hi,
    s2CanonicalReadFour4_letterClass_one h2 hq L hi,
    s2CanonicalReadFour4_letterClass_two h2 hq L hi, mul_assoc, mul_assoc, mul_assoc]

/-- ★ **The S2 collapse** (recorded as a consequence, never used above): since every
ambient letter is the unit `1`, the read of every level-three generator word is `1`. -/
theorem s2CanonicalReadFour3_generatorWord_eq_one (hi : StageLive 4 3) (m : ℤ)
    (t : Fin (3 - 1) → ℤ) :
    s2CanonicalReadFour3 h2 hq L ((s2LaurentNormalizerFour h2 hq).generatorWord hi m t) =
      1 := by
  rw [s2CanonicalReadFour3_generatorWord h2 hq L hi m t]
  simp [s2AmbientLetterFour]

/-- The level-four twin of the S2 collapse. -/
theorem s2CanonicalReadFour4_generatorWord_eq_one (hi : StageLive 4 4) (m : ℤ)
    (t : Fin (4 - 1) → ℤ) :
    s2CanonicalReadFour4 h2 hq L ((s2LaurentNormalizerFour h2 hq).generatorWord hi m t) =
      1 := by
  rw [s2CanonicalReadFour4_generatorWord h2 hq L hi m t]
  simp [s2AmbientLetterFour]

end Regressions

/-! ## Part 6 — ★ the R5 dictionary at the campaign data (the OPEN-LETTERS core)

The two G4 clause bodies at the S2 depth-four witness data: the receiver/letter equalities
at the deep-live level `j = 3` (μ₄ calculus letters) and the terminal level `j = 4` (μ₅
twin), and the wrap/letter descent clauses at every gauge-live level.  `Kt` is the
witness's own terminal field `(s2DepthFour).fld 4`, the receiver is R0's
`s2TerminalReceiverFour`, the normalizer is R0's `s2LaurentNormalizerFour`, the embedding
is the SAME `algebraMap Kt L` — no owner, view, or receiver is swapped. -/

section Dictionary

/-- **The explicit μ₄ calculus** — the `fgmnCalculusOf` term inside D3-19's
`s2Mu4_calculus_nonempty` (the CC-16 packaging map at the D3-18 records), NAMED so its
`letterZ` field is consumable by the dictionary. -/
@[implicit_reducible] noncomputable def s2Mu4Calculus :
    FGMNCalculus (s2DepthThree h2 hq) 2 1 85 :=
  fgmnCalculusOf (s2DepthThreeKeyChain h2 hq) (s2SourceDataThree h2 hq)
    (s2SourceLawsThree h2 hq)

/-- read pin: the μ₄ calculus letters are the forced constant-`1` depth-three letters
(D3-18's `s2LetterThree`), definitionally. -/
theorem s2Mu4Calculus_letterZ :
    (s2Mu4Calculus h2 hq).letterZ = s2LetterThree h2 hq := rfl

/-- **The explicit μ₅ calculus** — the `fgmnCalculusOf` term inside D4-18's
`s2Mu5_calculus_nonempty`, NAMED for the same reason. -/
@[implicit_reducible] noncomputable def s2Mu5Calculus :
    FGMNCalculus (s2DepthFour h2 hq) 1 1 171 :=
  fgmnCalculusOf (s2DepthFourKeyChain h2 hq) (s2SourceDataFour h2 hq)
    (s2SourceLawsFour h2 hq)

/-- read pin: the μ₅ calculus letters are the forced constant-`1` depth-four letters
(D4-17's `s2LetterFour`), definitionally. -/
theorem s2Mu5Calculus_letterZ :
    (s2Mu5Calculus h2 hq).letterZ = s2LetterFour h2 hq := rfl

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]

/-- ★★★ **R5 — the receiver/letter equality at the deep-live level `j = 3`** (the
OPEN-LETTERS core; the exact `DeepLevelExport.letter_receiver` body at the S2 depth-four
data, with this file's read standing in the `canonicalRead` slot): the μ₄ calculus letter
`letterZ (a+2)`, pushed through the R0 receiver's level-3 map and the terminal embedding,
IS the canonical letter value — the read of `Λ_a` at the R0 normalizer.  The stage pairing
`letterZ (a+2) ↔ Λ_a` is G4's (`Λ_a` carries stage-`(a+2)` data, cf. C130cr
`letterClass`). -/
theorem s2four_letter_receiver_mu4 (hi : StageLive 4 3) (a : Fin (3 - 1)) :
    algebraMap ((s2DepthFour h2 hq).fld 4) L
        ((s2TerminalReceiverFour h2 hq).levelHom 3
          ((s2Mu4Calculus h2 hq).letterZ (a.1 + 2))) =
      ((s2CanonicalReadFour h2 hq L 3
          ((s2LaurentNormalizerFour h2 hq).letterClass hi a) : Lˣ) : L) := by
  have h1 : (s2TerminalReceiverFour h2 hq).levelHom 3
      ((s2Mu4Calculus h2 hq).letterZ (a.1 + 2)) = 1 :=
    map_one ((s2TerminalReceiverFour h2 hq).levelHom 3)
  rw [h1, map_one, s2CanonicalReadFour_three,
    s2CanonicalReadFour3_letterClass h2 hq L hi a, s2AmbientLetterFour_apply,
    Units.val_one]

/-- ★★ **R5 — the μ₅ twin at the terminal level `j = 4`**: the same equality for the μ₅
refinement calculus letters at the receiver's level-4 (terminal) map. -/
theorem s2four_letter_receiver_mu5 (hi : StageLive 4 4) (a : Fin (4 - 1)) :
    algebraMap ((s2DepthFour h2 hq).fld 4) L
        ((s2TerminalReceiverFour h2 hq).levelHom 4
          ((s2Mu5Calculus h2 hq).letterZ (a.1 + 2))) =
      ((s2CanonicalReadFour h2 hq L 4
          ((s2LaurentNormalizerFour h2 hq).letterClass hi a) : Lˣ) : L) := by
  have h1 : (s2TerminalReceiverFour h2 hq).levelHom 4
      ((s2Mu5Calculus h2 hq).letterZ (a.1 + 2)) = 1 :=
    map_one ((s2TerminalReceiverFour h2 hq).levelHom 4)
  rw [h1, map_one, s2CanonicalReadFour_four,
    s2CanonicalReadFour4_letterClass h2 hq L hi a, s2AmbientLetterFour_apply,
    Units.val_one]

/-- ★★ **R5 — the wrap descent clause** (`CanonicalGeneratorDescent.wrap`'s body at the
constructed read): at every gauge-live level, the read of the wrap class is an embedded
`Kt`-unit — the witness is the unit `1` (the S2 wrap value; `Units.map` along the same
`algebraMap` as I10's `unitAlgebraMap`). -/
theorem s2four_wrap_descent {j : ℕ} (hj : GaugeLive 4 j) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      s2CanonicalReadFour h2 hq L j ((s2DepthFour h2 hq).wrapClass hj.stageLive) =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  refine ⟨1, ?_⟩
  rw [map_one]
  have h1 : 1 ≤ j := hj.1
  have hlt : j < 4 := hj.2
  interval_cases j
  · rw [s2CanonicalReadFour_one, s2CanonicalReadFour1_wrapClass h2 hq L hj.stageLive,
      s2AmbientLetterFour_apply]
  · rw [s2CanonicalReadFour_two, s2CanonicalReadFour2_wrapClass h2 hq L hj.stageLive,
      s2AmbientLetterFour_apply]
  · rw [s2CanonicalReadFour_three, s2CanonicalReadFour3_wrapClass h2 hq L hj.stageLive,
      s2AmbientLetterFour_apply]

/-- Letter descent at level two (single letter). -/
theorem s2four_letter_descent_two (hi : StageLive 4 2) (a : Fin (2 - 1)) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      s2CanonicalReadFour h2 hq L 2 ((s2LaurentNormalizerFour h2 hq).letterClass hi a) =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  refine ⟨1, ?_⟩
  rw [map_one]
  fin_cases a
  show s2CanonicalReadFour h2 hq L 2
      ((s2LaurentNormalizerFour h2 hq).letterClass hi (0 : Fin (2 - 1))) = 1
  rw [s2CanonicalReadFour_two, s2CanonicalReadFour2_letterClass h2 hq L hi,
    s2AmbientLetterFour_apply]

/-- Letter descent at the deep-live level three (both letters). -/
theorem s2four_letter_descent_three (hi : StageLive 4 3) (a : Fin (3 - 1)) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      s2CanonicalReadFour h2 hq L 3 ((s2LaurentNormalizerFour h2 hq).letterClass hi a) =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  refine ⟨1, ?_⟩
  rw [map_one, s2CanonicalReadFour_three, s2CanonicalReadFour3_letterClass h2 hq L hi a,
    s2AmbientLetterFour_apply]

/-- ★★ **R5 — the letter descent clause** (`CanonicalGeneratorDescent.letter`'s body at
the constructed read): at every gauge-live level, every letter value is an embedded
`Kt`-unit. -/
theorem s2four_letter_descent {j : ℕ} (hj : GaugeLive 4 j) (a : Fin (j - 1)) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      s2CanonicalReadFour h2 hq L j
          ((s2LaurentNormalizerFour h2 hq).letterClass hj.stageLive a) =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  have h1 : 1 ≤ j := hj.1
  have hlt : j < 4 := hj.2
  interval_cases j
  · exact a.elim0
  · exact s2four_letter_descent_two h2 hq L hj.stageLive a
  · exact s2four_letter_descent_three h2 hq L hj.stageLive a

end Dictionary

/-! ## Part 7 — the R7 handoff: the clauses fire at any node carrying this read

`CanonicalGeneratorDescent`/`DeepLevelExport` are typed at an `ArisingCore`/
`ChainRealization`; none exists at depth four yet (row R7/R9 — the GCW-6 fence keeps this
file at DATA + dictionary).  The theorems below are the named handoff: for ANY future
depth-four `SplitNodePointSource` at the R0 receiver whose `canonicalRead` is pinned to
`s2CanonicalReadFour`, the node's `wrapValue`/`letterValue` satisfy the descent clauses and
the exact `letter_receiver` body — R7's realization inhabits G4's record by direct
application (through `DeepLevelExport.ofLetterEq`, whose remaining input is the G3 site
package). -/

section Handoff

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable {E : Type uE} [Field E] {K : KeyChain (s2DepthFour h2 hq)}

/-- ★ **R7 handoff, wrap clause**: any depth-four node at the R0 receiver whose canonical
read at a gauge-live level is this file's read has its `wrapValue` an embedded `Kt`-unit —
`CanonicalGeneratorDescent.wrap`'s body, node-typed. -/
theorem s2four_node_wrapValue_descent
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E
      (s2TerminalReceiverFour h2 hq) K)
    {j : ℕ} (hj : GaugeLive 4 j)
    (hread : S.canonicalRead j = s2CanonicalReadFour h2 hq L j) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      S.wrapValue hj.stageLive =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  rw [SplitNodePointSource.wrapValue_def, hread]
  exact s2four_wrap_descent h2 hq L hj

/-- ★ **R7 handoff, letter clause**: same, for every `letterValue` at the R0 normalizer —
`CanonicalGeneratorDescent.letter`'s body, node-typed. -/
theorem s2four_node_letterValue_descent
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E
      (s2TerminalReceiverFour h2 hq) K)
    {j : ℕ} (hj : GaugeLive 4 j) (a : Fin (j - 1))
    (hread : S.canonicalRead j = s2CanonicalReadFour h2 hq L j) :
    ∃ u : ((s2DepthFour h2 hq).fld 4)ˣ,
      S.letterValue (s2LaurentNormalizerFour h2 hq) hj.stageLive a =
        Units.map (algebraMap ((s2DepthFour h2 hq).fld 4) L) u := by
  rw [SplitNodePointSource.letterValue_def, hread]
  exact s2four_letter_descent h2 hq L hj a

/-- ★★ **R7 handoff, the `letter_receiver` body**: at any such node, the μ₄ calculus
letters tie through the receiver and the embedding to the node's OWN `letterValue`s at the
deep-live level — the exact `DeepLevelExport.letter_receiver` field body at the S2
depth-four witness (modulo R7/C0's site-calculus truncation transport, which reads only
this same letter value). -/
theorem s2four_node_letter_receiver
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E
      (s2TerminalReceiverFour h2 hq) K)
    (hread : S.canonicalRead 3 = s2CanonicalReadFour h2 hq L 3)
    (hi : StageLive 4 3) (a : Fin (3 - 1)) :
    algebraMap ((s2DepthFour h2 hq).fld 4) L
        ((s2TerminalReceiverFour h2 hq).levelHom 3
          ((s2Mu4Calculus h2 hq).letterZ (a.1 + 2))) =
      ((S.letterValue (s2LaurentNormalizerFour h2 hq) hi a : Lˣ) : L) := by
  rw [SplitNodePointSource.letterValue_def, hread]
  exact s2four_letter_receiver_mu4 h2 hq L hi a

end Handoff

end Uniformity.Density.Tower.C136r3

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Data + dictionary over the landed R0/T3/D3/D4 corpus (cite-free); nothing here may add to
the trusted base. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136r3.deepLive_four_iff
#print axioms Uniformity.Density.Tower.C136r3.gaugeLive_four_iff
#print axioms Uniformity.Density.Tower.C136r3.s2four_ehat_one
#print axioms Uniformity.Density.Tower.C136r3.s2four_ehat_two
#print axioms Uniformity.Density.Tower.C136r3.s2four_ehat_three
#print axioms Uniformity.Density.Tower.C136r3.s2four_ehat_four
#print axioms Uniformity.Density.Tower.C136r3.s2four_levelExponentHeight_one
#print axioms Uniformity.Density.Tower.C136r3.s2four_levelExponentHeight_two
#print axioms Uniformity.Density.Tower.C136r3.s2four_levelExponentHeight_three
#print axioms Uniformity.Density.Tower.C136r3.s2four_levelExponentHeight_four
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_one_iff
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_one_iff'
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_two_iff
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_two_iff'
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_three_iff
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_three_iff'
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_four_iff
#print axioms Uniformity.Density.Tower.C136r3.s2four_mem_ker_four_iff'
#print axioms Uniformity.Density.Tower.C136r3.s2AmbientLetterFour
#print axioms Uniformity.Density.Tower.C136r3.s2AmbientLetterFour_apply
#print axioms Uniformity.Density.Tower.C136r3.s2AmbientLetterFour_psi_root
#print axioms Uniformity.Density.Tower.C136r3.s2four_wrapClass_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_one_ten
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_two_twenty
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_two_fortytwo
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_three_forty
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_three_eightyfour
#print axioms Uniformity.Density.Tower.C136r3.s2four_laurentSolve_three_oneseventy
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_two_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_three_zero_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_three_one_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_four_zero_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_four_one_coe
#print axioms Uniformity.Density.Tower.C136r3.s2four_letterClass_four_two_coe
#print axioms Uniformity.Density.Tower.C136r3.zpowHom
#print axioms Uniformity.Density.Tower.C136r3.zpowHom_apply
#print axioms Uniformity.Density.Tower.C136r3.s2Exp1Eta
#print axioms Uniformity.Density.Tower.C136r3.s2Exp1Eta_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp2Eta
#print axioms Uniformity.Density.Tower.C136r3.s2Exp2Eta_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp2B2
#print axioms Uniformity.Density.Tower.C136r3.s2Exp2B2_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3Eta
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3Eta_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3B2
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3B2_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3B3
#print axioms Uniformity.Density.Tower.C136r3.s2Exp3B3_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B4
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B4_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B3
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B3_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B2
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4B2_add
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4Eta
#print axioms Uniformity.Density.Tower.C136r3.s2Exp4Eta_add
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour1
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour1_coe
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour2
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour2_coe
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_coe
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_coe
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour_one
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour_two
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour_three
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour_four
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour1_wrapClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour2_wrapClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour2_letterClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_wrapClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_letterClass_zero
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_letterClass_one
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_letterClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_wrapClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_letterClass_zero
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_letterClass_one
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_letterClass_two
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_letterClass
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour2_generatorWord
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_generatorWord
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_generatorWord
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour3_generatorWord_eq_one
#print axioms Uniformity.Density.Tower.C136r3.s2CanonicalReadFour4_generatorWord_eq_one
#print axioms Uniformity.Density.Tower.C136r3.s2Mu4Calculus
#print axioms Uniformity.Density.Tower.C136r3.s2Mu4Calculus_letterZ
#print axioms Uniformity.Density.Tower.C136r3.s2Mu5Calculus
#print axioms Uniformity.Density.Tower.C136r3.s2Mu5Calculus_letterZ
#print axioms Uniformity.Density.Tower.C136r3.s2four_letter_receiver_mu4
#print axioms Uniformity.Density.Tower.C136r3.s2four_letter_receiver_mu5
#print axioms Uniformity.Density.Tower.C136r3.s2four_wrap_descent
#print axioms Uniformity.Density.Tower.C136r3.s2four_letter_descent_two
#print axioms Uniformity.Density.Tower.C136r3.s2four_letter_descent_three
#print axioms Uniformity.Density.Tower.C136r3.s2four_letter_descent
#print axioms Uniformity.Density.Tower.C136r3.s2four_node_wrapValue_descent
#print axioms Uniformity.Density.Tower.C136r3.s2four_node_letterValue_descent
#print axioms Uniformity.Density.Tower.C136r3.s2four_node_letter_receiver

end AxCheck
