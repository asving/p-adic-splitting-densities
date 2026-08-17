/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C109a
import Uniformity.ChapC.C109i
import Uniformity.ChapC.C109ii
import Uniformity.ChapC.C109iii
import Uniformity.ChapC.C109iv
import Uniformity.ChapC.C109v
import Uniformity.ChapB.B36

/-!
# Uniformity.ChapC.C109 — the exact node cell count (the A-C.5 ASSEMBLY)

**Chapter C, NODE C.109** (`ht_node_cell_card`, statement byte-frozen from
`leanspec/Leanspec/ChapC.lean`, the A-C.2 re-sign) — the exact count of the level-`N` node
cell: `Q^{B_v(N)}` times the product of the side censuses.  This module ASSEMBLES the five
signed layers C.109-i … C.109-v (amendment A-C.5) into the frozen statement.

## Assembly route (A-C.5, with one recorded deviation)

Through C.109a's development bridge `E`, a cell class is a vector of `m` block classes; the
cell conditions decompose as: per-block height floors (`le_gaussVal_iff` at level `N`,
readable since `hvis`), vertex exactness = the height-`Pceil` digit is NONZERO (B.36), and
the per-side residual types = conditions on the PRICED digits, which assemble into a sweep
function `sweepRead` satisfying exactly C.109-v's `SweepCond` (the on-side height law makes
`resPoly`'s coefficients the priced digits).  The count then fibers over the sweep
assignment: every fibre is a product of blocks of `r`-independent size (`C.109-iii`'s
uniformity), and C.109-v counts the base.

**Recorded deviation from the route sketch**: C.109-ii's global box count enters through
its per-digit refinement C.109-iii (summing the uniform fibre over the `Q` digit values
recovers the box count blockwise), because the assembly needs the count in the free-lift
block carrier, not the dev-of-monic carrier.  C.109-ii is imported and its statement is the
blockwise special case; nothing is weakened.

## Status

SKELETON (in construction): the lemma chain is stated and elaborates; bodies land
hardest-first with per-lemma commits.  Zero `sorry` required before this node is declared
LANDED; final footprint must be Lean core only.
-/

set_option linter.style.longLine false
set_option linter.overlappingInstances false

namespace Uniformity.Density.Tower.C109asm

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. Class-level digit reads (level-`N` congruence) -/

/-- The height-`h` digit map factors through level-`N` classes (`h < N`): congruent
coefficient vectors give equal `resMk` reads. -/
theorem resMk_proj_congr (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {N h : ℕ} (hh : h < N) {A A' : Polynomial O}
    (hA : A.natDegree < Φ.natDegree) (hA' : A'.natDegree < Φ.natDegree)
    (hproj : proj O Φ.natDegree N (fun i => A.coeff i)
      = proj O Φ.natDegree N (fun i => A'.coeff i)) :
    resMk π Φ h A = resMk π Φ h A' := by
  sorry

/-- Vertex exactness at the digit: on the `h`-floor, the height-`h` digit is nonzero iff
the Gauss valuation is exactly `h` (B.36 both ways). -/
theorem resMk_ne_zero_iff_gaussVal (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h : ℕ} {A : Polynomial O} (hA : A.degree < Φ.degree)
    (hfl : (h : ℕ∞) ≤ gaussVal A) :
    resMk π Φ h A ≠ 0 ↔ gaussVal A = (h : ℕ∞) := by
  sorry

/-- the chosen integral lift of a level-`N` residue class. -/
noncomputable def liftRes {N : ℕ} (x : Res O N) : O :=
  (Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x).choose

theorem liftRes_spec {N : ℕ} (x : Res O N) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (liftRes x) = x :=
  (Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x).choose_spec

/-- the chosen polynomial lift of a block class (degree `< d` by construction). -/
noncomputable def blockPoly {d N : ℕ} (c : Coeff O d N) : Polynomial O :=
  ∑ i : Fin d, C (liftRes (c i)) * X ^ (i : ℕ)

theorem blockPoly_natDegree_lt {d N : ℕ} (hd : 0 < d) (c : Coeff O d N) :
    (blockPoly c).natDegree < d := by
  sorry

theorem blockPoly_proj {d N : ℕ} (c : Coeff O d N) :
    proj O d N (fun i => (blockPoly c).coeff i) = c := by
  sorry

/-- **the class-level digit read** at height `h`: the `resMk` of the chosen lift. -/
noncomputable def blockDigit (π : O) (Φ : Polynomial O) (h N : ℕ)
    (c : Coeff O Φ.natDegree N) : resField Φ :=
  resMk π Φ h (blockPoly c)

/-- `blockDigit` agrees with the `resMk` read of ANY lift of the class. -/
theorem blockDigit_eq (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {N h : ℕ} (hh : h < N) {A : Polynomial O} (hA : A.natDegree < Φ.natDegree) :
    blockDigit π Φ h N (proj O Φ.natDegree N (fun i => A.coeff i)) = resMk π Φ h A := by
  sorry

/-! ### 2. The development assembly (blocks → the monic member) -/

/-- Assembling blocks of degree `< deg Φ` below a monic top reproduces the blocks as the
`Φ`-adic development, with top coefficient `1` (B.06 `dev_unique`). -/
theorem dev_assemble {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (A : Fin m → Polynomial O) (hdeg : ∀ j, (A j).degree < Φ.degree) :
    (∀ j : Fin m, dev Φ (∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m) (j : ℕ) = A j)
      ∧ dev Φ (∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m) m = 1 := by
  sorry

/-- the assembled polynomial is monic of degree `m·d`, hence IS a `monicPoly`. -/
theorem assemble_eq_monicPoly {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (A : Fin m → Polynomial O) (hdeg : ∀ j, (A j).degree < Φ.degree) :
    ∃ a : Fin (m * Φ.natDegree) → O,
      monicPoly a = ∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m := by
  sorry

/-! ### 3. The sweep read and the block sets -/

open Classical in
/-- **the sweep read** of a block-class vector: the height-`Pceil j` digit at on-hull
positions below `m`, the monic `1` at `m`, `0` elsewhere. -/
noncomputable def sweepRead (π : O) (Φ : Polynomial O) (v : HTNode) (N : ℕ)
    (g : Fin v.m → Coeff O Φ.natDegree N) : ℕ → resField Φ :=
  fun j =>
    if hj : j < v.m then
      (if v.OnHull j then blockDigit π Φ (v.Pceil j) N (g ⟨j, hj⟩) else 0)
    else if j = v.m then 1 else 0

/-- **the floored block set** at height `h`: classes with a lift of degree `< d` above the
`h`-floor.  (The free-lift carrier of C.109-iii, without the digit prescription.) -/
def BlockSet (π : O) (Φ : Polynomial O) (h N : ℕ) : Set (Coeff O Φ.natDegree N) :=
  {c | ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
    proj O Φ.natDegree N (fun i => A.coeff i) = c ∧ (h : ℕ∞) ≤ gaussVal A}

/-- the priced refinement: C.109-iii's subtype is the `blockDigit` fibre of `BlockSet`. -/
theorem blockSet_digit_eq_iii (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    {c : Coeff O Φ.natDegree N | c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = {c | ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
          proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
          (h : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = x} := by
  sorry

/-- the priced block count, from C.109-iii. -/
theorem card_blockSet_digit (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    Nat.card {c : Coeff O Φ.natDegree N //
        c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = Nat.card (resField Φ) ^ (N - h - 1) := by
  sorry

/-- the floored block count: summing the uniform priced fibre over the `Q` digit values
(C.109-ii's content, recovered blockwise in the free-lift carrier). -/
theorem card_blockSet (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) :
    Nat.card (BlockSet π Φ h N) = Nat.card (resField Φ) ^ (N - h) := by
  sorry

/-! ### 4. The hull side dictionary from the height profile -/

/-- The on-side height law: along a genuine side, the ceiled heights are affine of slope
`−u/ℓ` (stated addition-form, ℕ-subtraction-free). -/
theorem pceil_on_side (v : HTNode) (hwf : v.WF) {u ℓ : ℕ} (hS : v.IsSide u ℓ)
    {k : ℕ} (hk : k ≤ v.nodeSideDeg u ℓ) :
    v.Pceil ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k) + u * k
      = v.Pceil ((v.nodeSideSet u ℓ).min.getD 0) := by
  sorry

/-- **the synthetic side dictionary**: for a monic degree-`m·d` polynomial whose height
profile has the node floors and vertex exactness, each genuine node side is read off `f`
with matching left endpoint, residual degree, and pinned left height.  (The floors+vertex
core of C.109-iv, needed in BOTH directions of the crux — C.109-iv itself takes full cell
membership, which the backward direction does not yet have.) -/
theorem side_dictionary_of_profile (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    (v : HTNode) (hwf : v.WF)
    {f : Polynomial O} (hmon : f.Monic) (hdeg : f.natDegree = v.m * Φ.natDegree)
    (hfl : ∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j)
    (hvx : ∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞))
    {u ℓ : ℕ} (hS : v.IsSide u ℓ) :
    ∃ hne : (sideSet Φ f u ℓ).Nonempty,
      sideMin Φ f u ℓ hne = (v.nodeSideSet u ℓ).min.getD 0 ∧
      sideDeg Φ f u ℓ hne = v.nodeSideDeg u ℓ ∧
      npHgt Φ f (sideMin Φ f u ℓ hne)
        = ((v.Pceil (sideMin Φ f u ℓ hne) : ℕ) : ℕ∞) := by
  sorry

/-! ### 5. The crux: cell membership ↔ sweep condition + block floors -/

/-- **The crux equivalence.**  Through a componentwise development bridge `E` (C.109a), a
level-`N` class is in the cell iff its sweep read satisfies C.109-v's `SweepCond` and every
block class lies in its floored block set. -/
theorem mem_iff_blocks (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]
    (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    (E : Coeff O (v.m * Φ.natDegree) N ≃ (Fin v.m → Coeff O Φ.natDegree N))
    (hE : ∀ (a : Fin (v.m * Φ.natDegree) → O) (j : Fin v.m) (i : Fin Φ.natDegree),
      E (proj O (v.m * Φ.natDegree) N a) j i
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
            ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ)))
    (c : Coeff O (v.m * Φ.natDegree) N) :
    (∃ a : Fin (v.m * Φ.natDegree) → O,
        proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v)
      ↔ (C109v.SweepCond v (sweepRead π Φ v N (E c))
          ∧ ∀ j : Fin v.m, E c j ∈ BlockSet π Φ (v.Pceil (j : ℕ)) N) := by
  sorry

/-! ### 6. Cardinality glue -/

/-- counting by fibres of a map into a finite base. -/
theorem card_eq_sum_fibers {α β : Type*} [Finite α] [Fintype β] (F : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // F a = b} := by
  sorry

/-- the sweep base is finite (assignments are supported on `≤ m + 1` positions). -/
theorem finite_sweepCond {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (v : HTNode) :
    Finite {r : ℕ → K // C109v.SweepCond v r} := by
  sorry

open Classical in
/-- the exponent arithmetic: the free digits left after pricing are exactly `B_v(N)`
(`hwf`'s `L`-law + `hvis` for the honest ℕ-subtraction). -/
theorem exponent_arith (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    ∑ j ∈ Finset.range v.m,
        (if v.OnHull j then N - v.Pceil j - 1 else N - v.Pceil j) = v.B N := by
  sorry

end Uniformity.Density.Tower.C109asm

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.109 — the exact node cell count** (`(HT-cell)`, `EFF.W12.83/84` step 1).
Statement byte-frozen from the A-C.2 re-signed leanspec block; proof = the A-C.5 assembly
of the five landed layers (module docstring). -/
theorem ht_node_cell_card (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]  -- all derivable from hΦ; binders for elaboration
    (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
        ∃ a : Fin (v.m * Φ.natDegree) → O,
          proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v}
      = Nat.card (resField Φ) ^ v.B N
        * ∏ p ∈ v.sides, sideCensus (resField Φ) (v.sideType p.1 p.2) := by
  sorry

end Uniformity.Density.Tower
