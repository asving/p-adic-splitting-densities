/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG26
import Uniformity.ChapI.IFCG30
import Uniformity.ChapI.IFCG31
import Uniformity.ChapI.IFCG33
import Uniformity.ChapB.B35c
import Uniformity.ChapB.B54
import Uniformity.ChapB.B57

/-!
# Uniformity.ChapI.IFCG34 — [ER4 2026-08-30] the five even-ramification `e = 4` types:
the residual dichotomy of the forced sector

Stage ER4 of the cone census (design record `runs/wave-c/verdict_ER4.md`).  CCA
(`IFCG31`) closed `ConeRemainderLaw 4` at every odd-ramification type and left the
`forcedBox` carrier (every class carries a visible slope-`1/2` face) as the exact home
of the five even-ramification types `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`,
`{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}`.  This file partitions the forced sector by the
slope-`1/2` face's shape and, on the `E1` cell, by the residual quadratic's GENRE, and
assembles the five value laws down to exactly named sector limits:

* **§1 the sector split** (Lean-core): `forcedBox = e1Box ⊔ e2Box` — the `E1` cell
  (`v₀ = 2` exact: the `[0,4]` slope-`1/2` face spans the whole quartic, every lift is
  `(1,2)`-pure) and the `E2` cell (`v₀ ≥ 3`, `v₂ = 1`: the `[2,4]` slope-`1/2` face of
  width 2, every lift splits off a `(2,1)` quadratic block).  Counts:
  `card e1Box = (q−1)q^(4K−7)`, `card e2Box = (q−1)q^(4K−8)`.
* **§2–§3 the E1 residual dichotomy**: the `[0,4]` residual is a monic quadratic over
  `resField X` with nonzero constant term, a CLASS invariant (IFCG28); its genre is
  EXACTLY one of SPLIT (two coprime monic linears), IRREDUCIBLE, DOUBLE ROOT (a monic
  linear squared) — `e1Box = e1SplitBox ⊔ e1IrrBox ⊔ e1DdBox`.
* **§4 the E1 decisions**:
  - SPLIT is DECIDED `{(2,1),(2,1)}` (IFCG31 §3b's leaf, fired on the whole sub-box);
  - IRREDUCIBLE is PINNED: every lift is an irreducible quartic of type `{(2,2)}` OR
    `{(4,1)}` (`typeOf_e1_irr_mem` — B.57 purity of factors + B.35c residual
    multiplicativity kill every proper factorization; B.54 bounds the inertia degree);
    the full `{(2,2)}` decision is EXACTLY the `ℓ = 2, deg ψ = 2` instance of the
    chapter's standing open perimeter `B-BOX-1`, named here as `E1IrrLeafDecision`;
  - every σ with an ODD-ramification member is REFUTED on all of `e1Box`
    (`not_decidedAt_e1_of_odd_member` — sharper than IFCG31 §3's all-odd exclusion);
* **§5 the E2 block structure**: every lift of an `e2Box` class factors as a `(2,1)`
  ramified quadratic times a monic quadratic cofactor (`exists_ramQuad_factor_of_e2`),
  so no singleton type (in particular neither `{(2,2)}` nor `{(4,1)}`) is ever decided
  on `e2Box`.
* **§6 the count partitions**: for each of the five types, the mass-4 remainder count
  at every finite level equals its decided depth-0 sector counts plus exactly named
  recursion terms (`decidedSet ∩ e1DdBox`, `decidedSet ∩ e2Box`).
* **§7 the conditional laws + the wire**: each `ConeRemainderLaw 4 σ` follows from
  `ZcURLim` premises for its named sector families, and the whole census front wires
  through IFCG33's `decidedSliceAt_all_of_ram5_even4_bridge`.

## The honest fence (record corrections included)

1. **The `(4,1)` sector is NOT parity-empty**: `X⁴ − 6X² − 36X − 18` over `ℤ₃` is
   irreducible with `e = 4, f = 1` (PARI `idealprimedec`: one prime, `e=4,f=1`) and its
   class lies in `e1DdBox` (`v₀ = 2, v₁ = 2, v₂ = 1`, residual `Y² + Y + 1 = (Y − 1)²`
   over `𝔽₃`).  CCA's battery observation "`(4,1)` only at `p = 2`" was a sampling
   artifact; the `(4,1)` law recurses at EVERY residue characteristic.
2. **The double-root sectors recurse at ORDER 2**: the `E1` double root recenters at
   the degree-2 key `X² − bπ` — this is the deep-wild OM tower (order ≥ 2), machinery
   not yet in the corpus; IFCG20's linear recentring does NOT reach it.  The recursion
   terms are therefore named `ZcURLim` premises, not discharged.
3. **`E1IrrLeafDecision`** (the `{(2,2)}` leaf) is the `ℓ = 2, deg ψ = 2` instance of
   `B-BOX-1` (B.61's `hBOX`, recorded OPEN-MATH); `typeOf_e1_irr_mem` reduces it to
   excluding `{(4,1)}` on the irreducible-residual sector.

## Axiom fence

§1 and the trichotomy are Lean core `{propext, Classical.choice, Quot.sound}`.  The
decision/forcing sections consume exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through
IFCG26/IFCG30/IFCG31.  The C.33 cites do NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
-- the sector limit families must mirror `ZcURLim`'s binder list byte-for-byte
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG34

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_qmonomial shallowSet
  mem_stratum_X_pow_iff card_setOf_le_resOrd card_setOf_resOrd_eq card_pi_set
  pureFaceSet coneRemainderCount ConeRemainderLaw ZeroConeClause
  zeroConeClause_of_remainderLaw npHeight_coe)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq dvd_ramIndexOf_of_isPure
  le_npHgt_monicPoly)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains
  exists_pure_factor_of_two_point_side dvd_natDegree_of_isPure
  irreducible_of_isPure_natDegree_eq monicFactors_of_irreducible
  exists_mem_monicFactors mem_sideSet_of_onSide irreducible_of_monic_natDegree_one)
open Uniformity.Density.IFCG28 (resPoly_monicPoly_eq)
open Uniformity.Density.IFCG31 (mixedType4 ramPairType box31a box31b forcedBox
  mem_box31a_iff mem_box31b_iff remainder_carrier_four decidedAt_quartic_31
  stratum_of_forced not_decidedAt_of_forced_of_odd decidedAt_forced_split)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the target types -/

section Types

/-- The inert ramified quartic type: one irreducible quartic with `e = 2, f = 2`. -/
def type22 : FactorizationType := ⟨{(2, 2)}⟩

/-- The wild totally ramified quartic type: one irreducible quartic with `e = 4, f = 1`. -/
def type41 : FactorizationType := ⟨{(4, 1)}⟩

/-- The split-tail type: two split linears plus a ramified quadratic. -/
def splitTailType : FactorizationType := ⟨{(1, 1), (1, 1), (2, 1)}⟩

/-- The inert-tail type: an unramified quadratic plus a ramified quadratic. -/
def inertTailType : FactorizationType := ⟨{(1, 2), (2, 1)}⟩

end Types

/-! ## §1 — the sector split of the forced carrier: `forcedBox = e1Box ⊔ e2Box` -/

section Sectors

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The `E1` cell** (`v₀ = 2` exact, `v₁ ≥ 2, v₂ ≥ 1, v₃ ≥ 1`): the `[0,4]`
slope-`1/2` face spans the whole quartic — every lift is `(1,2)`-pure (pi-set shape). -/
def e1Box (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | ∀ i : Fin 4,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | resOrd x = 2}
      else if (i : ℕ) = 1 then {x : Res O K | 2 ≤ resOrd x}
      else {x : Res O K | 1 ≤ resOrd x})}

/-- **The `E2` cell** (`v₀ ≥ 3, v₁ ≥ 2, v₂ = 1` exact, `v₃ ≥ 1`): the `[2,4]`
slope-`1/2` face has width 2 — every lift splits off a `(2,1)` quadratic block
(pi-set shape). -/
def e2Box (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | ∀ i : Fin 4,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | 3 ≤ resOrd x}
      else if (i : ℕ) = 1 then {x : Res O K | 2 ≤ resOrd x}
      else if (i : ℕ) = 2 then {x : Res O K | resOrd x = 1}
      else {x : Res O K | 1 ≤ resOrd x})}

theorem mem_e1Box_iff {K : ℕ} (c : Coeff O 4 K) :
    c ∈ e1Box O K ↔ resOrd (c 0) = 2 ∧ 2 ≤ resOrd (c 1)
      ∧ 1 ≤ resOrd (c 2) ∧ 1 ≤ resOrd (c 3) := by
  constructor
  · intro hc
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    have h3 := hc 3
    rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)] at h0
    rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)] at h1
    rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide)] at h2
    rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide)] at h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨hA, hB, hC, hD⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0, show i = 0 from Fin.ext hi0]
      exact hA
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1, show i = 1 from Fin.ext hi1]
        exact hB
      · rw [if_neg hi1]
        by_cases hi2 : (i : ℕ) = 2
        · rw [show i = 2 from Fin.ext hi2]
          exact hC
        · have hieq : i = 3 := by
            have h5 := i.isLt
            exact Fin.ext (by omega)
          rw [hieq]
          exact hD

theorem mem_e2Box_iff {K : ℕ} (c : Coeff O 4 K) :
    c ∈ e2Box O K ↔ 3 ≤ resOrd (c 0) ∧ 2 ≤ resOrd (c 1)
      ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3) := by
  constructor
  · intro hc
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    have h3 := hc 3
    rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)] at h0
    rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)] at h1
    rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
      if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)] at h2
    rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)] at h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨hA, hB, hC, hD⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0, show i = 0 from Fin.ext hi0]
      exact hA
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1, show i = 1 from Fin.ext hi1]
        exact hB
      · rw [if_neg hi1]
        by_cases hi2 : (i : ℕ) = 2
        · rw [if_pos hi2, show i = 2 from Fin.ext hi2]
          exact hC
        · rw [if_neg hi2]
          have hieq : i = 3 := by
            have h5 := i.isLt
            exact Fin.ext (by omega)
          rw [hieq]
          exact hD

/-- **The sector split**: the forced carrier is exactly the two cells. -/
theorem forcedBox_eq_union (K : ℕ) :
    forcedBox O K = e1Box O K ∪ e2Box O K := by
  ext c
  rw [Set.mem_union, mem_e1Box_iff, mem_e2Box_iff]
  show (1 ≤ resOrd (c 3) ∧ 1 ≤ resOrd (c 2) ∧
      ((resOrd (c 0) = 2 ∧ 2 ≤ resOrd (c 1))
        ∨ (3 ≤ resOrd (c 0) ∧ 2 ≤ resOrd (c 1) ∧ resOrd (c 2) = 1))) ↔ _
  constructor
  · rintro ⟨h3, h2, ⟨h0, h1⟩ | ⟨h0, h1, h2'⟩⟩
    · exact Or.inl ⟨h0, h1, h2, h3⟩
    · exact Or.inr ⟨h0, h1, h2', h3⟩
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩)
    · exact ⟨h3, h2, Or.inl ⟨h0, h1⟩⟩
    · exact ⟨h3, by omega, Or.inr ⟨h0, h1, h2⟩⟩

/-- The two cells are disjoint (`v₀ = 2` against `v₀ ≥ 3`). -/
theorem disjoint_e1Box_e2Box (K : ℕ) : Disjoint (e1Box O K) (e2Box O K) := by
  rw [Set.disjoint_left]
  intro c hc1 hc2
  rw [mem_e1Box_iff] at hc1
  rw [mem_e2Box_iff] at hc2
  omega

/-- The `E1` cell count: `(q−1)·q^(4K−7)`. -/
theorem card_e1Box {K : ℕ} (hK : 3 ≤ K) :
    Nat.card (e1Box O K : Set (Coeff O 4 K))
      = (residueCard O - 1) * residueCard O ^ (4 * K - 7) := by
  classical
  unfold e1Box
  rw [card_pi_set, Fin.prod_univ_four]
  rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide)]
  rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide)]
  rw [card_setOf_resOrd_eq (show 2 < K by omega),
    card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 2 - 1 = K - 3 from by omega,
    show 4 * K - 7 = (K - 3) + (K - 2) + ((K - 1) + (K - 1)) from by omega,
    pow_add, pow_add]
  ring

/-- The `E2` cell count: `(q−1)·q^(4K−8)`. -/
theorem card_e2Box {K : ℕ} (hK : 3 ≤ K) :
    Nat.card (e2Box O K : Set (Coeff O 4 K))
      = (residueCard O - 1) * residueCard O ^ (4 * K - 8) := by
  classical
  unfold e2Box
  rw [card_pi_set, Fin.prod_univ_four]
  rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
    if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)]
  rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)]
  rw [card_setOf_le_resOrd (show 3 ≤ K by omega),
    card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_resOrd_eq (show 1 < K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 1 - 1 = K - 2 from by omega,
    show 4 * K - 8 = (K - 3) + (K - 2) + ((K - 2) + (K - 1)) from by omega,
    pow_add, pow_add]
  ring

end Sectors

/-! ## §2 — the E1 lift bank: purity, side data, and the residual read -/

section E1Bank

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- The E1 class-polygon package: the `[0,4]` slope-`1/2` face, attained at both ends,
visible, on-stratum. -/
private theorem e1_class_bank {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e1Box O K) :
    classNPSupport c 1 2 = 4 ∧ NPAttains c 1 2 0 ∧ NPAttains c 1 2 4
      ∧ NPVisibleAt c 1 2 ∧ c ∈ levelZeroStratum O 4 K (X ^ 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e1Box_iff c).1 hc
  have hnp0 : npHeight c 0 = 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : 2 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : 1 ≤ npHeight c 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
    exact h2
  have hnp3 : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact h3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  have hsup : classNPSupport c 1 2 = 4 := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c 1 2 (show (0 : ℕ) ≤ 4 by norm_num)
      rw [hnp0] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · omega
      · omega
      · omega
      · omega
  have hAt0 : NPAttains c 1 2 0 := ⟨by omega, by rw [hnp0, hsup]⟩
  have hAt4 : NPAttains c 1 2 4 := ⟨le_refl 4, by rw [hnp4, hsup]⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  have hstr : c ∈ levelZeroStratum O 4 K (X ^ 4) := by
    refine (mem_stratum_X_pow_iff (by omega) c).2 ?_
    intro i
    fin_cases i
    · exact le_of_le_of_eq (by norm_num) h0.symm
    · exact le_trans (by norm_num) h1
    · exact h2
    · exact h3
  exact ⟨hsup, hAt0, hAt4, hvis, hstr⟩

/-- The E1 lift bank: every lift of an `e1Box` class is `(1,2)`-pure with support `4`,
left height `2` at the side minimum, and reduction `X⁴`. -/
private theorem e1_lift_bank {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    IsPure X (monicPoly a) 1 2
      ∧ suppVal X (monicPoly a) 1 2 = ((4 : ℕ) : ℕ∞)
      ∧ npHgt X (monicPoly a)
          (sideMin X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2))
        = ((2 : ℕ) : ℕ∞)
      ∧ (monicPoly a).map (IsLocalRing.residue O) = X ^ 4 := by
  obtain ⟨h0, -, -, -⟩ := (mem_e1Box_iff c).1 hc
  obtain ⟨hsup, hAt0, hAt4, hvis, hstr⟩ := e1_class_bank hK hc
  obtain ⟨hO0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt0 ha
  obtain ⟨hO4, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt4 ha
  have hdegdiv : (monicPoly a).natDegree / (X : Polynomial O).natDegree = 4 := by
    rw [monicPoly_natDegree, Polynomial.natDegree_X]
  have hpure : IsPure X (monicPoly a) 1 2 := ⟨hO0, by rw [hdegdiv]; exact hO4⟩
  have hsupp4 : suppVal X (monicPoly a) 1 2 = ((4 : ℕ) : ℕ∞) := by
    rw [hsupp, hsup]
  have hmin0 : sideMin X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2)
      = 0 := sideMin_of_pure hpure _
  have hH0 : npHgt X (monicPoly a)
      (sideMin X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2))
      = ((2 : ℕ) : ℕ∞) := by
    rw [hmin0, npHgt_monicPoly_eq hπ ha (by norm_num : (0 : ℕ) < 4)
      (lt_of_eq_of_lt h0 (by omega))]
    exact Nat.cast_inj.mpr h0
  exact ⟨hpure, hsupp4, hH0, hstr a ha⟩

/-- The E1 residual read: a MONIC quadratic with nonzero constant term. -/
private theorem e1_resPoly_spec {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    (resPoly π X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2) 2).Monic
      ∧ (resPoly π X (monicPoly a) 1 2
          (sideSet_nonempty_gen X (monicPoly a) 1 2) 2).natDegree = 2
      ∧ (resPoly π X (monicPoly a) 1 2
          (sideSet_nonempty_gen X (monicPoly a) 1 2) 2).coeff 0 ≠ 0 := by
  obtain ⟨hpure, hsupp4, hH0, hres⟩ := e1_lift_bank hK hπ hc ha
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hgdeg4 : (monicPoly a).natDegree = 4 * (X : Polynomial O).natDegree := by
    rw [monicPoly_natDegree, Polynomial.natDegree_X, Nat.mul_one]
  have htop : suppVal X (monicPoly a) 1 2 ≠ ⊤ := by
    rw [hsupp4]
    exact ENat.coe_ne_top _
  have hne : (sideSet X (monicPoly a) 1 2).Nonempty :=
    sideSet_nonempty_gen X (monicPoly a) 1 2
  obtain ⟨hdeg, hc0⟩ := natDegree_resPoly hπ isKey_X (by norm_num)
    (Nat.coprime_one_left 2) htop hne hH0
  have hsdeg : sideDeg X (monicPoly a) 1 2 hne = 2 := by
    have h5 := sideDeg_of_pure Polynomial.monic_X (by simp) hgm hgdeg4 (by norm_num)
      (Nat.coprime_one_left 2) hpure hne
    omega
  refine ⟨?_, by rw [hdeg, hsdeg], hc0⟩
  show (resPoly π X (monicPoly a) 1 2 hne 2).coeff
      (resPoly π X (monicPoly a) 1 2 hne 2).natDegree = 1
  rw [hdeg, hsdeg,
    resPoly_coeff_of_pure hπ Polynomial.monic_X (by simp) hgm hgdeg4 (by norm_num)
      (Nat.coprime_one_left 2) hpure hne 2 2,
    show (2 : ℕ) - 1 * 2 = 0 from by norm_num,
    show (2 : ℕ) * 2 = 4 from by norm_num,
    dev_top Polynomial.monic_X (by simp) hgm (μ := 4) hgdeg4, resMk_one hπ]

/-- CN1-for-residuals at the E1 face: the residual read is LIFT-INDEPENDENT
(IFCG28's class invariance, at the fixed left height `2`). -/
private theorem e1_resPoly_congr {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1Box O K) {a a' : Fin 4 → O}
    (ha : proj O 4 K a = c) (ha' : proj O 4 K a' = c) :
    resPoly π X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2) 2
      = resPoly π X (monicPoly a') 1 2 (sideSet_nonempty_gen X (monicPoly a') 1 2) 2 := by
  obtain ⟨-, -, -, hvis, -⟩ := e1_class_bank hK hc
  obtain ⟨-, -, hH0, -⟩ := e1_lift_bank hK hπ hc ha
  obtain ⟨-, -, hH0', -⟩ := e1_lift_bank hK hπ hc ha'
  exact (resPoly_monicPoly_eq hπ (by norm_num) hvis ha ha' _ _ hH0 hH0').2

end E1Bank

/-! ## §3 — the residual genre trichotomy and the three E1 sub-boxes -/

section Trichotomy

variable {k : Type*} [Field k]

/-- **The genre trichotomy**: any monic quadratic over a field is split (two coprime
monic linears), irreducible, or the square of a monic linear. -/
theorem monic_quadratic_trichotomy {F : Polynomial k} (hF : F.Monic)
    (hdeg : F.natDegree = 2) :
    (∃ G H : Polynomial k, G.Monic ∧ H.Monic ∧ G.natDegree = 1 ∧ H.natDegree = 1
        ∧ IsCoprime G H ∧ F = G * H)
      ∨ Irreducible F
      ∨ (∃ L : Polynomial k, L.Monic ∧ L.natDegree = 1 ∧ F = L ^ 2) := by
  by_cases hirr : Irreducible F
  · exact Or.inr (Or.inl hirr)
  have hFne : F ≠ 0 := hF.ne_zero
  have hFnu : ¬ IsUnit F := by
    intro hu
    have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have hex : ∃ A B : Polynomial k, F = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
    by_contra hcon
    refine hirr ⟨hFnu, ?_⟩
    intro A B hAB
    by_contra hab2
    rcases not_or.mp hab2 with ⟨hA, hB⟩
    exact hcon ⟨A, B, hAB, hA, hB⟩
  obtain ⟨A, B, hAB, hAnu, hBnu⟩ := hex
  have hA0 : A ≠ 0 := fun h => hFne (by rw [hAB, h, zero_mul])
  have hB0 : B ≠ 0 := fun h => hFne (by rw [hAB, h, mul_zero])
  have hnd : ∀ P : Polynomial k, P ≠ 0 → ¬ IsUnit P → P.natDegree ≠ 0 := by
    intro P hP0 hPnu h0
    have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc0 : P.coeff 0 ≠ 0 := fun hz => hP0 (by rw [hPC, hz, Polynomial.C_0])
    exact hPnu (by rw [hPC]; exact Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hc0))
  have hdegs : A.natDegree + B.natDegree = 2 := by
    have h5 : F.natDegree = A.natDegree + B.natDegree := by
      rw [hAB]
      exact Polynomial.natDegree_mul hA0 hB0
    omega
  have hA1 : A.natDegree = 1 := by
    have h5 := hnd A hA0 hAnu
    have h6 := hnd B hB0 hBnu
    omega
  have hB1 : B.natDegree = 1 := by
    have h5 := hnd A hA0 hAnu
    have h6 := hnd B hB0 hBnu
    omega
  have hlead : A.leadingCoeff * B.leadingCoeff = 1 := by
    have h5 : F.leadingCoeff = A.leadingCoeff * B.leadingCoeff := by
      rw [hAB]
      exact Polynomial.leadingCoeff_mul A B
    rw [hF.leadingCoeff] at h5
    exact h5.symm
  have hlA : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hA0
  have hlB : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hB0
  have hCA : (Polynomial.C A.leadingCoeff⁻¹ : Polynomial k) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero, inv_eq_zero]
    exact hlA
  have hCB : (Polynomial.C B.leadingCoeff⁻¹ : Polynomial k) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero, inv_eq_zero]
    exact hlB
  have hGm : (A * Polynomial.C A.leadingCoeff⁻¹).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv hA0
  have hHm : (B * Polynomial.C B.leadingCoeff⁻¹).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv hB0
  have hGd : (A * Polynomial.C A.leadingCoeff⁻¹).natDegree = 1 := by
    rw [Polynomial.natDegree_mul hA0 hCA, Polynomial.natDegree_C, hA1]
  have hHd : (B * Polynomial.C B.leadingCoeff⁻¹).natDegree = 1 := by
    rw [Polynomial.natDegree_mul hB0 hCB, Polynomial.natDegree_C, hB1]
  have hFGH : F = (A * Polynomial.C A.leadingCoeff⁻¹) * (B * Polynomial.C B.leadingCoeff⁻¹) := by
    calc F = F * Polynomial.C ((A.leadingCoeff * B.leadingCoeff)⁻¹) := by
          rw [hlead, inv_one, Polynomial.C_1, mul_one]
      _ = A * B * Polynomial.C (A.leadingCoeff⁻¹ * B.leadingCoeff⁻¹) := by
          rw [hAB, mul_inv]
      _ = (A * Polynomial.C A.leadingCoeff⁻¹) * (B * Polynomial.C B.leadingCoeff⁻¹) := by
          rw [Polynomial.C_mul]
          ring
  set G := A * Polynomial.C A.leadingCoeff⁻¹ with hGdef
  set H := B * Polynomial.C B.leadingCoeff⁻¹ with hHdef
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G = Polynomial.X + Polynomial.C g₀ :=
    ⟨G.coeff 0, hGm.eq_X_add_C hGd⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, H = Polynomial.X + Polynomial.C h₀ :=
    ⟨H.coeff 0, hHm.eq_X_add_C hHd⟩
  by_cases hgh : g₀ = h₀
  · refine Or.inr (Or.inr ⟨G, hGm, hGd, ?_⟩)
    rw [hFGH, sq, hg₀, hh₀, hgh]
  · refine Or.inl ⟨G, H, hGm, hHm, hGd, hHd,
      ⟨Polynomial.C (g₀ - h₀)⁻¹, -(Polynomial.C (g₀ - h₀)⁻¹), ?_⟩, hFGH⟩
    have hGH' : G - H = Polynomial.C (g₀ - h₀) := by
      rw [hg₀, hh₀, Polynomial.C_sub]
      ring
    calc Polynomial.C (g₀ - h₀)⁻¹ * G + -(Polynomial.C (g₀ - h₀)⁻¹) * H
        = Polynomial.C (g₀ - h₀)⁻¹ * (G - H) := by ring
      _ = Polynomial.C (g₀ - h₀)⁻¹ * Polynomial.C (g₀ - h₀) := by rw [hGH']
      _ = Polynomial.C ((g₀ - h₀)⁻¹ * (g₀ - h₀)) := by rw [Polynomial.C_mul]
      _ = 1 := by rw [inv_mul_cancel₀ (sub_ne_zero.2 hgh), Polynomial.C_1]

/-- Genre exclusivity, leg 1: a product of two linears is never irreducible. -/
theorem not_irreducible_mul_linear {G H : Polynomial k} (hGd : G.natDegree = 1)
    (hHd : H.natDegree = 1) : ¬ Irreducible (G * H) := by
  intro hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega

/-- Genre exclusivity, leg 2: a coprime product of monic linears is never a monic-linear
square. -/
theorem mul_ne_sq_of_coprime_linear {G H L : Polynomial k} (hGm : G.Monic) (hHm : H.Monic)
    (hLm : L.Monic) (hGd : G.natDegree = 1) (hHd : H.natDegree = 1) (hLd : L.natDegree = 1)
    (hcop : IsCoprime G H) : G * H ≠ L ^ 2 := by
  intro heq
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G = Polynomial.X + Polynomial.C g₀ :=
    ⟨G.coeff 0, hGm.eq_X_add_C hGd⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, H = Polynomial.X + Polynomial.C h₀ :=
    ⟨H.coeff 0, hHm.eq_X_add_C hHd⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, L = Polynomial.X + Polynomial.C l₀ :=
    ⟨L.coeff 0, hLm.eq_X_add_C hLd⟩
  have hne : g₀ ≠ h₀ := by
    intro hgh
    have hcop' : IsCoprime H H := by
      rw [hg₀, hgh, ← hh₀] at hcop
      exact hcop
    have hu : IsUnit H := hcop'.isUnit_of_dvd dvd_rfl
    have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have hev : (g₀ - l₀) * (h₀ - l₀) = 0 := by
    have h5 : (G * H).eval (-l₀) = 0 := by
      rw [heq, hl₀]
      simp
    rw [Polynomial.eval_mul, hg₀, hh₀] at h5
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h5
    linear_combination h5
  rcases mul_eq_zero.mp hev with h | h
  · have hgl : g₀ = l₀ := by linear_combination h
    have hGL : G = L := by rw [hg₀, hl₀, hgl]
    have hHL : H = L := by
      refine mul_left_cancel₀ hLm.ne_zero ?_
      calc L * H = G * H := by rw [hGL]
        _ = L ^ 2 := heq
        _ = L * L := sq L
    refine hne ?_
    have h6 : Polynomial.X + Polynomial.C g₀ = Polynomial.X + Polynomial.C h₀ := by
      rw [← hg₀, ← hh₀, hGL, hHL]
    have h7 := congrArg (fun P : Polynomial k => P.coeff 0) h6
    simpa using h7
  · have hhl : h₀ = l₀ := by linear_combination h
    have hHL : H = L := by rw [hh₀, hl₀, hhl]
    have hGL : G = L := by
      refine mul_right_cancel₀ hLm.ne_zero ?_
      calc G * L = G * H := by rw [hHL]
        _ = L ^ 2 := heq
        _ = L * L := sq L
    refine hne ?_
    have h6 : Polynomial.X + Polynomial.C g₀ = Polynomial.X + Polynomial.C h₀ := by
      rw [← hg₀, ← hh₀, hGL, hHL]
    have h7 := congrArg (fun P : Polynomial k => P.coeff 0) h6
    simpa using h7

end Trichotomy

section E1Genres

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The SPLIT genre**: some (hence, by IFCG28's invariance, every) lift's E1 residual
factors into two coprime monic linears.  Decided `{(2,1),(2,1)}` (§4). -/
def e1SplitBox (π : O) (K : ℕ) : Set (Coeff O 4 K) :=
  {c | c ∈ e1Box O K ∧ ∃ a : Fin 4 → O, proj O 4 K a = c ∧
    ∃ G H : Polynomial (resField (X : Polynomial O)),
      G.Monic ∧ H.Monic ∧ G.natDegree = 1 ∧ H.natDegree = 1 ∧ IsCoprime G H ∧
      resPoly π X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2) 2 = G * H}

/-- **The IRREDUCIBLE genre**: the E1 residual is an irreducible quadratic.  Every lift
is an irreducible quartic of type `{(2,2)}` or `{(4,1)}` (§4). -/
def e1IrrBox (π : O) (K : ℕ) : Set (Coeff O 4 K) :=
  {c | c ∈ e1Box O K ∧ ∃ a : Fin 4 → O, proj O 4 K a = c ∧
    Irreducible (resPoly π X (monicPoly a) 1 2
      (sideSet_nonempty_gen X (monicPoly a) 1 2) 2)}

/-- **The DOUBLE-ROOT genre**: the E1 residual is a monic-linear square — the ORDER-2
recursion sector (the recentring key is the degree-2 `X² − bπ`; `{(4,1)}` lives here at
every residue characteristic — see the module fence). -/
def e1DdBox (π : O) (K : ℕ) : Set (Coeff O 4 K) :=
  {c | c ∈ e1Box O K ∧ ∃ a : Fin 4 → O, proj O 4 K a = c ∧
    ∃ L : Polynomial (resField (X : Polynomial O)), L.Monic ∧ L.natDegree = 1 ∧
      resPoly π X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2) 2 = L ^ 2}

theorem e1SplitBox_subset (π : O) (K : ℕ) : e1SplitBox π K ⊆ e1Box O K :=
  fun _ hc => hc.1

theorem e1IrrBox_subset (π : O) (K : ℕ) : e1IrrBox π K ⊆ e1Box O K :=
  fun _ hc => hc.1

theorem e1DdBox_subset (π : O) (K : ℕ) : e1DdBox π K ⊆ e1Box O K :=
  fun _ hc => hc.1

/-- ★ **The E1 genre partition** (covering half): the cell is the union of the three
genres. -/
theorem e1Box_eq_genres {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    e1Box O K = e1SplitBox π K ∪ e1IrrBox π K ∪ e1DdBox π K := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 4 K c
    letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
    obtain ⟨hmon, hdeg, -⟩ := e1_resPoly_spec hK hπ hc ha
    rcases monic_quadratic_trichotomy hmon hdeg with hs | hi | hd
    · exact Or.inl (Or.inl ⟨hc, a, ha, hs⟩)
    · exact Or.inl (Or.inr ⟨hc, a, ha, hi⟩)
    · exact Or.inr ⟨hc, a, ha, hd⟩
  · rintro ((hc | hc) | hc) <;> exact hc.1

/-- Genre disjointness: split against irreducible. -/
theorem disjoint_e1SplitBox_e1IrrBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Disjoint (e1SplitBox π K) (e1IrrBox π K) := by
  rw [Set.disjoint_left]
  rintro c ⟨hc, a, ha, G, H, hGm, hHm, hGd, hHd, hcop, hres⟩ ⟨-, a', ha', hirr⟩
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rw [← e1_resPoly_congr hK hπ hc ha ha', hres] at hirr
  exact not_irreducible_mul_linear hGd hHd hirr

/-- Genre disjointness: split against double root. -/
theorem disjoint_e1SplitBox_e1DdBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Disjoint (e1SplitBox π K) (e1DdBox π K) := by
  rw [Set.disjoint_left]
  rintro c ⟨hc, a, ha, G, H, hGm, hHm, hGd, hHd, hcop, hres⟩ ⟨-, a', ha', L, hLm, hLd, hres'⟩
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  refine mul_ne_sq_of_coprime_linear hGm hHm hLm hGd hHd hLd hcop ?_
  rw [← hres, e1_resPoly_congr hK hπ hc ha ha', hres']

/-- Genre disjointness: irreducible against double root. -/
theorem disjoint_e1IrrBox_e1DdBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Disjoint (e1IrrBox π K) (e1DdBox π K) := by
  rw [Set.disjoint_left]
  rintro c ⟨hc, a, ha, hirr⟩ ⟨-, a', ha', L, hLm, hLd, hres'⟩
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rw [e1_resPoly_congr hK hπ hc ha ha', hres', sq] at hirr
  exact not_irreducible_mul_linear hLd hLd hirr

end E1Genres

/-! ## §4 — the E1 decisions: split DECIDED, irreducible PINNED, odd members REFUTED -/

section E1Decisions

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The split sector is DECIDED `{(2,1),(2,1)}`** — IFCG31 §3b's leaf, fired on the
whole sub-box. -/
theorem decidedAt_e1_split {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1SplitBox π K) : DecidedAt O 4 ramPairType K c := by
  obtain ⟨hcE1, a, ha, G, H, hGm, hHm, hGd, hHd, hcop, hres⟩ := hc
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e1Box_iff c).1 hcE1
  exact decidedAt_forced_split hK hπ h0 h1 h2 h3 ha
    (sideSet_nonempty_gen X (monicPoly a) 1 2) hGm hHm hGd hHd hcop hres

/-- ★★ **The irreducible-residual pin**: every lift of an `e1IrrBox` class is an
IRREDUCIBLE quartic of type `{(2,2)}` or `{(4,1)}`.  A degree-2 monic factor would be
`(1,2)`-pure with a linear residual (B.57), and B.35c's residual multiplicativity would
split the irreducible residual — so every lift is irreducible; B.54 bounds the inertia
degree by the residual degree `2`, and `e·f = 4` leaves exactly the two pairs. -/
theorem typeOf_e1_irr_mem {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1IrrBox π K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    typeOf (monicPoly a) = type22 ∨ typeOf (monicPoly a) = type41 := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨hcE1, a₀, ha₀, hirr₀⟩ := hc
  have hirr : Irreducible (resPoly π X (monicPoly a) 1 2
      (sideSet_nonempty_gen X (monicPoly a) 1 2) 2) := by
    rw [e1_resPoly_congr hK hπ hcE1 ha ha₀]
    exact hirr₀
  obtain ⟨hpure, hsupp4, hH0, hres4⟩ := e1_lift_bank hK hπ hcE1 ha
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hgdeg : (monicPoly a).natDegree = 4 := monicPoly_natDegree a
  have hne : (sideSet X (monicPoly a) 1 2).Nonempty :=
    sideSet_nonempty_gen X (monicPoly a) 1 2
  have hgdeg4 : (monicPoly a).natDegree = 4 * (X : Polynomial O).natDegree := by
    rw [monicPoly_natDegree, Polynomial.natDegree_X, Nat.mul_one]
  have hsdeg : sideDeg X (monicPoly a) 1 2 hne = 2 := by
    have h5 := sideDeg_of_pure Polynomial.monic_X (by simp) hgm hgdeg4 (by norm_num)
      (Nat.coprime_one_left 2) hpure hne
    omega
  have hspec := monicFactors_spec hgm
  -- STEP 1: no monic factor has degree 2 (else B.35c splits the residual)
  have hno2 : ∀ g' ∈ monicFactors (monicPoly a), g'.natDegree ≠ 2 := by
    intro g' hg' hd2
    obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hg'
    have hg'm : g'.Monic := (hspec.1 g' hg').1
    have hTm : T.prod.Monic := by
      have h2 := Polynomial.monic_multiset_prod_of_monic T id
        (fun q hq => (hspec.1 q (by rw [hT]; exact Multiset.mem_cons_of_mem hq)).1)
      rwa [Multiset.map_id] at h2
    have hprod : monicPoly a = g' * T.prod := by
      rw [← hspec.2, hT, Multiset.prod_cons]
    obtain ⟨-, -, hp₁, hp₂, -, -⟩ :=
      isPure_of_monic_factor hπ isKey_X (by norm_num) (by norm_num)
        (Nat.coprime_one_left 2) hgm hg'm hTm
        (by rw [Polynomial.natDegree_X]; exact one_dvd _) hprod hpure hne
    have hg'deg2 : g'.natDegree = 2 * (X : Polynomial O).natDegree := by
      rw [Polynomial.natDegree_X, Nat.mul_one]
      exact hd2
    have hTdeg : T.prod.natDegree = 2 := by
      have h6 : (monicPoly a).natDegree = g'.natDegree + T.prod.natDegree := by
        rw [hprod]
        exact Polynomial.natDegree_mul hg'm.ne_zero hTm.ne_zero
      omega
    have hTdeg2 : T.prod.natDegree = 2 * (X : Polynomial O).natDegree := by
      rw [Polynomial.natDegree_X, Nat.mul_one]
      exact hTdeg
    have htop₁ : suppVal X g' 1 2 ≠ ⊤ := by
      rw [suppVal_of_pure Polynomial.monic_X (by simp) hg'm hg'deg2 hp₁]
      exact ENat.coe_ne_top _
    have htop₂ : suppVal X T.prod 1 2 ≠ ⊤ := by
      rw [suppVal_of_pure Polynomial.monic_X (by simp) hTm hTdeg2 hp₂]
      exact ENat.coe_ne_top _
    have hfin₁ : npHgt X g' 0 ≠ ⊤ := npHgt_ne_top_of_onSide (by norm_num) htop₁ hp₁.1
    have hfin₂ : npHgt X T.prod 0 ≠ ⊤ := npHgt_ne_top_of_onSide (by norm_num) htop₂ hp₂.1
    obtain ⟨H₁, hH₁⟩ := WithTop.ne_top_iff_exists.mp hfin₁
    obtain ⟨H₂, hH₂⟩ := WithTop.ne_top_iff_exists.mp hfin₂
    have hH₁' : npHgt X g' 0 = ((H₁ : ℕ) : ℕ∞) := by
      have hw : ((H₁ : ℕ) : ℕ∞) = npHgt X g' 0 := hH₁
      exact hw.symm
    have hH₂' : npHgt X T.prod 0 = ((H₂ : ℕ) : ℕ∞) := by
      have hw : ((H₂ : ℕ) : ℕ∞) = npHgt X T.prod 0 := hH₂
      exact hw.symm
    have hsd₁ : sideDeg X g' 1 2 (sideSet_nonempty_gen X g' 1 2) = 1 := by
      have h5 := sideDeg_of_pure Polynomial.monic_X (by simp) hg'm hg'deg2 (by norm_num)
        (Nat.coprime_one_left 2) hp₁ (sideSet_nonempty_gen X g' 1 2)
      omega
    have hsd₂ : sideDeg X T.prod 1 2 (sideSet_nonempty_gen X T.prod 1 2) = 1 := by
      have h5 := sideDeg_of_pure Polynomial.monic_X (by simp) hTm hTdeg2 (by norm_num)
        (Nat.coprime_one_left 2) hp₂ (sideSet_nonempty_gen X T.prod 1 2)
      omega
    have hH₁eq : H₁ = 1 := by
      have h5 := height_eq_of_pure Polynomial.monic_X (by simp) hg'm hg'deg2 (by norm_num)
        (Nat.coprime_one_left 2) hp₁ (sideSet_nonempty_gen X g' 1 2) hH₁'
      rw [hsd₁] at h5
      omega
    have hH₂eq : H₂ = 1 := by
      have h5 := height_eq_of_pure Polynomial.monic_X (by simp) hTm hTdeg2 (by norm_num)
        (Nat.coprime_one_left 2) hp₂ (sideSet_nonempty_gen X T.prod 1 2) hH₂'
      rw [hsd₂] at h5
      omega
    subst hH₁eq
    subst hH₂eq
    have hmul := resPoly_mul_of_pure hπ isKey_X (by norm_num) (by norm_num)
      (Nat.coprime_one_left 2) hg'm hTm
      (by rw [Polynomial.natDegree_X]; exact one_dvd _)
      (by rw [Polynomial.natDegree_X]; exact one_dvd _) hp₁ hp₂ hH₁' hH₂'
      (sideSet_nonempty_gen X g' 1 2) (sideSet_nonempty_gen X T.prod 1 2)
      (sideSet_nonempty_gen X (g' * T.prod) 1 2)
    rw [show (1 + 1 : ℕ) = 2 from rfl] at hmul
    rw [hprod, hmul] at hirr
    have hmin₁ : sideMin X g' 1 2 (sideSet_nonempty_gen X g' 1 2) = 0 :=
      sideMin_of_pure hp₁ _
    have hmin₂ : sideMin X T.prod 1 2 (sideSet_nonempty_gen X T.prod 1 2) = 0 :=
      sideMin_of_pure hp₂ _
    have hH₁'' : npHgt X g' (sideMin X g' 1 2 (sideSet_nonempty_gen X g' 1 2))
        = ((1 : ℕ) : ℕ∞) := by
      rw [hmin₁]
      exact hH₁'
    have hH₂'' : npHgt X T.prod (sideMin X T.prod 1 2 (sideSet_nonempty_gen X T.prod 1 2))
        = ((1 : ℕ) : ℕ∞) := by
      rw [hmin₂]
      exact hH₂'
    have hd₁ : (resPoly π X g' 1 2 (sideSet_nonempty_gen X g' 1 2) 1).natDegree = 1 := by
      have h5 := (natDegree_resPoly hπ isKey_X (by norm_num) (Nat.coprime_one_left 2)
        htop₁ (sideSet_nonempty_gen X g' 1 2) hH₁'').1
      rw [h5, hsd₁]
    have hd₂ : (resPoly π X T.prod 1 2
        (sideSet_nonempty_gen X T.prod 1 2) 1).natDegree = 1 := by
      have h5 := (natDegree_resPoly hπ isKey_X (by norm_num) (Nat.coprime_one_left 2)
        htop₂ (sideSet_nonempty_gen X T.prod 1 2) hH₂'').1
      rw [h5, hsd₂]
    exact not_irreducible_mul_linear hd₁ hd₂ hirr
  -- STEP 2: hence every monic factor has degree 4 — the lift is irreducible
  have hdegsum : ((monicFactors (monicPoly a)).map Polynomial.natDegree).sum = 4 := by
    have h5 : (monicPoly a).natDegree
        = ((monicFactors (monicPoly a)).map Polynomial.natDegree).sum := by
      conv_lhs => rw [← hspec.2]
      exact Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => (hspec.1 p hp).1)
    omega
  obtain ⟨g₁, hg₁⟩ := exists_mem_monicFactors hgm (by omega)
  have hg₁m := (hspec.1 g₁ hg₁).1
  have hg₁irr := (hspec.1 g₁ hg₁).2
  have hg₁pos : 0 < g₁.natDegree := natDegree_pos_of_mem_monicFactors hgm hg₁
  have hram₁ : 2 ∣ ramIndexOf g₁ := dvd_ramIndexOf_of_isPure hπ (by norm_num)
    (Nat.coprime_one_left 2) hgm hpure hg₁
  have hmulef₁ : ramIndexOf g₁ * inertiaDegOf g₁ = g₁.natDegree :=
    ramIndexOf_mul_inertiaDegOf hg₁m hg₁pos
  have hdvd₁ : 2 ∣ g₁.natDegree := hram₁.trans ⟨inertiaDegOf g₁, hmulef₁.symm⟩
  obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hg₁
  have hsum : g₁.natDegree + (T.map Polynomial.natDegree).sum = 4 := by
    rw [hT, Multiset.map_cons, Multiset.sum_cons] at hdegsum
    omega
  have hg₁4 : g₁.natDegree = 4 := by
    have hne2 := hno2 g₁ hg₁
    omega
  have hT0 : T = 0 := by
    by_contra hTne
    obtain ⟨g₂, hg₂⟩ := Multiset.exists_mem_of_ne_zero hTne
    have hg₂mem : g₂ ∈ monicFactors (monicPoly a) := by
      rw [hT]
      exact Multiset.mem_cons_of_mem hg₂
    have hg₂pos : 0 < g₂.natDegree := natDegree_pos_of_mem_monicFactors hgm hg₂mem
    have h8 : g₂.natDegree ≤ (T.map Polynomial.natDegree).sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hg₂)
    omega
  have hFg : monicPoly a = g₁ := by
    have h9 := hspec.2
    rw [hT, hT0, Multiset.prod_cons, Multiset.prod_zero, mul_one] at h9
    exact h9.symm
  subst hFg
  -- STEP 3: the `(e, f)` pair — `f ∣ 2` (B.54) and `e·f = 4`
  have hres24 : (monicPoly a).map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O))
          ^ (2 * sideDeg X (monicPoly a) 1 2 hne) := by
    rw [Polynomial.map_X, hsdeg]
    exact hres4
  have hf12 : inertiaDegOf (monicPoly a) ∣ 2 := by
    have h5 := inertiaDegOf_dvd_key_mul_resDeg hπ isKey_X (by norm_num) (by norm_num)
      (Nat.coprime_one_left 2) hgm (by omega) hpure hne (by rw [hsdeg]; norm_num) hres24
    rwa [Polynomial.natDegree_X, one_mul, hsdeg] at h5
  have hmulef : ramIndexOf (monicPoly a) * inertiaDegOf (monicPoly a) = 4 := by
    rw [ramIndexOf_mul_inertiaDegOf hgm (by omega)]
    exact hgdeg
  have hdata : (typeOf (monicPoly a)).data
      = ({efPair (monicPoly a)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, monicFactors_of_irreducible hgm hg₁irr, Multiset.map_singleton]
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hf12 with hf1 | hf2
  · refine Or.inr ?_
    have hram4 : ramIndexOf (monicPoly a) = 4 := by
      rw [hf1, Nat.mul_one] at hmulef
      exact hmulef
    have hef : efPair (monicPoly a) = (4, 1) := by
      unfold efPair
      rw [hram4, hf1]
    calc typeOf (monicPoly a) = ⟨(typeOf (monicPoly a)).data⟩ := rfl
      _ = ⟨({(4, 1)} : Multiset (ℕ × ℕ))⟩ := by rw [hdata, hef]
      _ = type41 := rfl
  · refine Or.inl ?_
    have hram2 : ramIndexOf (monicPoly a) = 2 := by
      rw [hf2] at hmulef
      omega
    have hef : efPair (monicPoly a) = (2, 2) := by
      unfold efPair
      rw [hram2, hf2]
    calc typeOf (monicPoly a) = ⟨(typeOf (monicPoly a)).data⟩ := rfl
      _ = ⟨({(2, 2)} : Multiset (ℕ × ℕ))⟩ := by rw [hdata, hef]
      _ = type22 := rfl

/-- On the irreducible-residual sector nothing outside `{(2,2)}, {(4,1)}` is ever
decided. -/
theorem not_decidedAt_e1_irr {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1IrrBox π K) {σ : FactorizationType}
    (hσ2 : σ ≠ type22) (hσ4 : σ ≠ type41) : ¬ DecidedAt O 4 σ K c := by
  intro hdec
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  rcases typeOf_e1_irr_mem hK hπ hc ha with h | h
  · exact hσ2 ((hdec a ha).symm.trans h)
  · exact hσ4 ((hdec a ha).symm.trans h)

/-- ★ **The E1 odd-member exclusion** (sharper than IFCG31 §3's all-odd form): on the
`(1,2)`-pure cell EVERY monic factor of EVERY lift has even ramification index, so any
type with even ONE odd-ramification member is refuted — in particular the two tail
types `{(1,1),(1,1),(2,1)}` and `{(1,2),(2,1)}` never decide on `e1Box`. -/
theorem not_decidedAt_e1_of_odd_member {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e1Box O K) {σ : FactorizationType} (hodd : ∃ p ∈ σ.data, ¬ 2 ∣ p.1) :
    ¬ DecidedAt O 4 σ K c := by
  intro hdec
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  obtain ⟨hpure, -, -, -⟩ := e1_lift_bank hK hπ hc ha
  obtain ⟨p, hpmem, hp2⟩ := hodd
  rw [← hdec a ha, typeOf_data] at hpmem
  obtain ⟨g', hg', rfl⟩ := Multiset.mem_map.mp hpmem
  exact hp2 (dvd_ramIndexOf_of_isPure hπ (by norm_num) (Nat.coprime_one_left 2)
    (monicPoly_monic a) hpure hg')

end E1Decisions

/-! ## §4b — THE NAMED OPEN LEAF: the `{(2,2)}` decision of the irreducible sector -/

section NamedLeaf

/-- ★ **THE NAMED OPEN LEAF** — the `ℓ = 2, deg ψ = 2` instance of the chapter's
standing perimeter `B-BOX-1` (B.61's `hBOX`, recorded OPEN-MATH): every
irreducible-residual E1 class is decided `{(2,2)}`.  By `typeOf_e1_irr_mem` this is
EXACTLY the exclusion of the `{(4,1)}` alternative on the irreducible-residual sector
(the standard argument: the residue of `β²/π` in the factor's residue field is a root
of the irreducible residual quadratic, forcing `2 ∣ f` — the graded analogue of B.52,
norm-peel work of Chapter-B scale). -/
def E1IrrLeafDecision : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (K : ℕ), 3 ≤ K → ∀ (π : O), Irreducible π →
    ∀ c ∈ e1IrrBox (O := O) π K, DecidedAt O 4 type22 K c

/-- The named leaf follows from the `{(4,1)}`-exclusion alone (the pin does the rest). -/
theorem e1IrrLeafDecision_of_no41
    (h : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
      (K : ℕ), 3 ≤ K → ∀ (π : O), Irreducible π → ∀ c ∈ e1IrrBox (O := O) π K,
      ∀ a : Fin 4 → O, proj O 4 K a = c → typeOf (monicPoly a) ≠ type41) :
    E1IrrLeafDecision := by
  intro O _ _ _ _ _ K hK π hπ c hc a ha
  rcases typeOf_e1_irr_mem hK hπ hc ha with h22 | h41
  · exact h22
  · exact absurd h41 (h O K hK π hπ c hc a ha)

end NamedLeaf

/-! ## §5 — the E2 block structure: a forced `(2,1)` quadratic times a quadratic -/

section E2Structure

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The E2 class-polygon package: the `[2,4]` slope-`1/2` face, attained at both ends,
visible, on-stratum. -/
private theorem e2_class_bank {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e2Box O K) :
    classNPSupport c 1 2 = 4 ∧ NPAttains c 1 2 2 ∧ NPAttains c 1 2 4
      ∧ NPVisibleAt c 1 2 ∧ c ∈ levelZeroStratum O 4 K (X ^ 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e2Box_iff c).1 hc
  have hnp0 : 3 ≤ npHeight c 0 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : 2 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : npHeight c 2 = 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
    exact h2
  have hnp3 : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact h3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  have hsup : classNPSupport c 1 2 = 4 := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c 1 2 (show (2 : ℕ) ≤ 4 by norm_num)
      rw [hnp2] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · omega
      · omega
      · omega
      · omega
  have hAt2 : NPAttains c 1 2 2 := ⟨by omega, by rw [hnp2, hsup]⟩
  have hAt4 : NPAttains c 1 2 4 := ⟨le_refl 4, by rw [hnp4, hsup]⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  have hstr : c ∈ levelZeroStratum O 4 K (X ^ 4) := by
    refine (mem_stratum_X_pow_iff (by omega) c).2 ?_
    intro i
    fin_cases i
    · exact le_trans (by norm_num) h0
    · exact le_trans (by norm_num) h1
    · exact le_of_le_of_eq (by norm_num) h2.symm
    · exact h3
  exact ⟨hsup, hAt2, hAt4, hvis, hstr⟩

/-- ★ **The E2 block factorization**: every lift of an `e2Box` class splits off a
`(2,1)` ramified quadratic (the `[2,4]` slope-`1/2` block) against a monic quadratic
cofactor.  In particular NO singleton type — neither `{(2,2)}` nor `{(4,1)}` — is ever
decided on `e2Box`. -/
theorem exists_ramQuad_factor_of_e2 {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e2Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    ∃ F R : Polynomial O, F.Monic ∧ R.Monic ∧ Irreducible F ∧ efPair F = (2, 1)
      ∧ R.natDegree = 2 ∧ monicPoly a = F * R := by
  obtain ⟨h0, -, -, -⟩ := (mem_e2Box_iff c).1 hc
  obtain ⟨hsup, hAt2, hAt4, hvis, hstr⟩ := e2_class_bank hK hc
  obtain ⟨hO2, hsupp⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt2 ha
  obtain ⟨hO4, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt4 ha
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hgdeg : (monicPoly a).natDegree = 4 := monicPoly_natDegree a
  have hsupp4 : suppVal X (monicPoly a) 1 2 = ((4 : ℕ) : ℕ∞) := by
    rw [hsupp, hsup]
  have htop : suppVal X (monicPoly a) 1 2 ≠ ⊤ := by
    rw [hsupp4]
    exact ENat.coe_ne_top _
  have hres : (monicPoly a).map (IsLocalRing.residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hstr a ha
  obtain ⟨F, R, hFm, hRm, hFp, hFd, heqFR⟩ :=
    exists_pure_factor_of_two_point_side hπ hgm hres (by norm_num) (by norm_num)
      (Nat.coprime_one_left 2) (show (2 : ℕ) < 4 by norm_num)
      (le_of_eq (monicPoly_natDegree a).symm) hO2 hO4 htop
  have hFdvd : 2 ∣ F.natDegree := dvd_natDegree_of_isPure hπ hFm (by norm_num)
    (Nat.coprime_one_left 2) hFp
  have hdegsum : F.natDegree + R.natDegree = 4 := by
    have h6 : (monicPoly a).natDegree = F.natDegree + R.natDegree := by
      rw [heqFR]
      exact Polynomial.natDegree_mul hFm.ne_zero hRm.ne_zero
    omega
  -- the pure block cannot be the whole quartic: `v₀ ≥ 3` breaks `OnSide` at `0`
  have hFdeg2 : F.natDegree = 2 := by
    rcases (by omega : F.natDegree = 2 ∨ F.natDegree = 4) with h24 | h24
    · exact h24
    exfalso
    have hRdeg0 : R.natDegree = 0 := by omega
    have hR1 : R = 1 := (Polynomial.Monic.natDegree_eq_zero hRm).mp hRdeg0
    have hgF : monicPoly a = F := by rw [heqFR, hR1, mul_one]
    have hpure' : IsPure X (monicPoly a) 1 2 := by
      rw [hgF]
      exact hFp
    have hO0 : OnSide X (monicPoly a) 1 2 0 := hpure'.1
    have hfin : npHgt X (monicPoly a) 0 ≠ ⊤ :=
      npHgt_ne_top_of_onSide (by norm_num) htop hO0
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hw' : npHgt X (monicPoly a) 0 = ((w : ℕ) : ℕ∞) := by
      have h6 : ((w : ℕ) : ℕ∞) = npHgt X (monicPoly a) 0 := hw
      exact h6.symm
    have hOn : (2 : ℕ) • npHgt X (monicPoly a) 0 + ((1 * 0 : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) 1 2 := hO0
    rw [hw', hsupp4, nsmul_eq_mul, ← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.cast_add,
      Nat.cast_inj] at hOn
    have hge3 : ((3 : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) 0 := by
      refine le_trans ?_ (le_npHgt_monicPoly hπ ha (by norm_num : (0 : ℕ) < 4))
      exact_mod_cast h0
    rw [hw', Nat.cast_le] at hge3
    omega
  obtain ⟨hFirr, hFef⟩ := irreducible_of_isPure_natDegree_eq hπ hFm (by norm_num)
    (Nat.coprime_one_left 2) hFp hFdeg2
  exact ⟨F, R, hFm, hRm, hFirr, hFef, by omega, heqFR⟩

/-- No singleton type is decided on `e2Box` — every lift has at least two monic
irreducible factors. -/
theorem not_decidedAt_e2_of_singleton {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e2Box O K) {σ : FactorizationType} (hσ : σ.data.card = 1) :
    ¬ DecidedAt O 4 σ K c := by
  intro hdec
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  obtain ⟨F, R, hFm, hRm, hFirr, hFef, hRdeg, heq⟩ :=
    exists_ramQuad_factor_of_e2 hK hπ hc ha
  have hRne : (monicFactors R).card ≠ 0 := by
    obtain ⟨r, hr⟩ := exists_mem_monicFactors hRm (by omega)
    intro h5
    rw [Multiset.card_eq_zero] at h5
    rw [h5] at hr
    exact Multiset.notMem_zero r hr
  have hcard : 2 ≤ (typeOf (monicPoly a)).data.card := by
    rw [typeOf_data, heq, monicFactors_mul hFm hRm, monicFactors_of_irreducible hFm hFirr,
      Multiset.map_add, Multiset.card_add, Multiset.map_singleton, Multiset.card_singleton,
      Multiset.card_map]
    omega
  rw [hdec a ha, hσ] at hcard
  omega

end E2Structure

/-! ## §6 — THE DICHOTOMY COUNT: the mass-4 remainder through the sector partition -/

section CountPartition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem ne_of_data_ne {σ τ : FactorizationType} (h : σ.data ≠ τ.data) : σ ≠ τ :=
  fun he => h (congrArg FactorizationType.data he)

/-- The mass-4 remainder count of every non-mixed type localizes to the FORCED sector
(the two decided boxes are `mixedType4`-decided, hence σ-empty). -/
theorem count_forced {σ : FactorizationType} (hσm : σ ≠ mixedType4) (M : ℕ) :
    coneRemainderCount O 4 σ M
      = Nat.card ((decidedSet O 4 σ (M + 4) ∩ forcedBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) := by
  classical
  unfold coneRemainderCount
  have hK : 4 ≤ M + 4 := by omega
  have hassoc : ((decidedSet O 4 σ (M + 4)
        ∩ levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
        \ pureFaceSet O 4 (M + 4))
      = decidedSet O 4 σ (M + 4)
        ∩ ((levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
          \ pureFaceSet O 4 (M + 4)) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hassoc, remainder_carrier_four hK]
  have hempty : decidedSet O 4 σ (M + 4) ∩ (box31a O (M + 4) ∪ box31b O (M + 4))
      = (∅ : Set (Coeff O 4 (M + 4))) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, hcA | hcB⟩
    · rw [mem_box31a_iff] at hcA
      have hdec2 : DecidedAt O 4 mixedType4 (M + 4) c :=
        decidedAt_quartic_31 (t := 1) (by omega) (by norm_num) (by norm_num)
          hcA.1 hcA.2.1 hcA.2.2.1 hcA.2.2.2
      exact hσm (decidedAt_unique hdec hdec2)
    · rw [mem_box31b_iff] at hcB
      have hdec2 : DecidedAt O 4 mixedType4 (M + 4) c :=
        decidedAt_quartic_31 (t := 2) (by omega) (by norm_num) (by norm_num)
          hcB.1 hcB.2.1 hcB.2.2.1 hcB.2.2.2
      exact hσm (decidedAt_unique hdec hdec2)
  rw [Set.inter_union_distrib_left, hempty, Set.empty_union]

/-- ★★★ **THE DICHOTOMY COUNT** (charge item 1, general σ): at every finite level, the
mass-4 remainder count of every non-mixed type is EXACTLY the sum of its four sector
counts — split, irreducible, double-root, and E2. -/
theorem coneRemainderCount_four_forced_partition {σ : FactorizationType}
    (hσm : σ ≠ mixedType4) {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 σ M
      = Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 σ (M + 4) ∩ e2Box O (M + 4))
            : Set (Coeff O 4 (M + 4))) := by
  classical
  have hK : 3 ≤ M + 4 := by omega
  rw [count_forced hσm M, forcedBox_eq_union, e1Box_eq_genres hK hπ,
    Set.inter_union_distrib_left, Set.inter_union_distrib_left,
    Set.inter_union_distrib_left]
  haveI : Fintype (Coeff O 4 (M + 4)) := Fintype.ofFinite _
  have hSe1 : decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4) ⊆ e1Box O (M + 4) :=
    Set.inter_subset_right.trans (e1SplitBox_subset π (M + 4))
  have hIe1 : decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4) ⊆ e1Box O (M + 4) :=
    Set.inter_subset_right.trans (e1IrrBox_subset π (M + 4))
  have hDe1 : decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4) ⊆ e1Box O (M + 4) :=
    Set.inter_subset_right.trans (e1DdBox_subset π (M + 4))
  have hdSI : Disjoint (decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4))
      (decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4)) :=
    (((disjoint_e1SplitBox_e1IrrBox hK hπ).mono_left
      Set.inter_subset_right).mono_right Set.inter_subset_right)
  have hd1 : Disjoint
      (decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4)
        ∪ decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4))
      (decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4)) := by
    rw [Set.disjoint_union_left]
    constructor
    · exact ((disjoint_e1SplitBox_e1DdBox hK hπ).mono_left
        Set.inter_subset_right).mono_right Set.inter_subset_right
    · exact ((disjoint_e1IrrBox_e1DdBox hK hπ).mono_left
        Set.inter_subset_right).mono_right Set.inter_subset_right
  have hd2 : Disjoint
      ((decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4)
          ∪ decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4))
        ∪ decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4))
      (decidedSet O 4 σ (M + 4) ∩ e2Box O (M + 4)) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ((disjoint_e1Box_e2Box (M + 4)).mono_left hSe1).mono_right
        Set.inter_subset_right
    · exact ((disjoint_e1Box_e2Box (M + 4)).mono_left hIe1).mono_right
        Set.inter_subset_right
    · exact ((disjoint_e1Box_e2Box (M + 4)).mono_left hDe1).mono_right
        Set.inter_subset_right
  rw [Nat.card_coe_set_eq, Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hdSI (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq]

/-- At `{(2,1),(2,1)}` the split sector contributes FULLY (it is decided there). -/
theorem decided_inter_e1Split_eq_self {K : ℕ} (hK : 3 ≤ K) {π : O}
    (hπ : Irreducible π) :
    decidedSet O 4 ramPairType K ∩ e1SplitBox π K = e1SplitBox π K :=
  Set.inter_eq_self_of_subset_right (fun _ hc => decidedAt_e1_split hK hπ hc)

/-- Off `{(2,1),(2,1)}` the split sector contributes NOTHING. -/
theorem decided_inter_e1Split_eq_empty {K : ℕ} (hK : 3 ≤ K) {π : O}
    (hπ : Irreducible π) {σ : FactorizationType} (hσ : σ ≠ ramPairType) :
    decidedSet O 4 σ K ∩ e1SplitBox π K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hcS⟩
  exact hσ (decidedAt_unique hdec (decidedAt_e1_split hK hπ hcS))

/-- Off `{(2,2)}` and `{(4,1)}` the irreducible sector contributes NOTHING. -/
theorem decided_inter_e1Irr_eq_empty {K : ℕ} (hK : 3 ≤ K) {π : O}
    (hπ : Irreducible π) {σ : FactorizationType} (hσ2 : σ ≠ type22)
    (hσ4 : σ ≠ type41) :
    decidedSet O 4 σ K ∩ e1IrrBox π K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hcI⟩
  exact not_decidedAt_e1_irr hK hπ hcI hσ2 hσ4 hdec

/-- Odd-member types contribute NOTHING on the whole E1 cell. -/
theorem decided_inter_e1_eq_empty_of_odd {K : ℕ} (hK : 3 ≤ K)
    {σ : FactorizationType} (hodd : ∃ p ∈ σ.data, ¬ 2 ∣ p.1) :
    decidedSet O 4 σ K ∩ e1Box O K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hc1⟩
  exact not_decidedAt_e1_of_odd_member hK hc1 hodd hdec

/-- Singleton types contribute NOTHING on the E2 cell. -/
theorem decided_inter_e2_eq_empty_of_singleton {K : ℕ} (hK : 3 ≤ K)
    {σ : FactorizationType} (hσ : σ.data.card = 1) :
    decidedSet O 4 σ K ∩ e2Box O K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hc2⟩
  exact not_decidedAt_e2_of_singleton hK hc2 hσ hdec

/-- ★★ **The `{(2,1),(2,1)}` count**: the FULL split sector plus the two named
recursion terms. -/
theorem coneRemainderCount_four_ramPair {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 ramPairType M
      = Nat.card (e1SplitBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2Box O (M + 4))
            : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [coneRemainderCount_four_forced_partition (ne_of_data_ne (by decide)) hπ M,
    decided_inter_e1Split_eq_self hK hπ,
    decided_inter_e1Irr_eq_empty hK hπ (ne_of_data_ne (by decide))
      (ne_of_data_ne (by decide))]
  rw [Nat.card_coe_set_eq (s := (∅ : Set (Coeff O 4 (M + 4)))), Set.ncard_empty]
  omega

/-- ★★ **The `{(2,2)}` count**: the irreducible sector's decided part plus the
double-root recursion term (E2 and the split sector contribute nothing). -/
theorem coneRemainderCount_four_type22 {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type22 M
      = Nat.card ((decidedSet O 4 type22 (M + 4) ∩ e1IrrBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 type22 (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [coneRemainderCount_four_forced_partition (ne_of_data_ne (by decide)) hπ M,
    decided_inter_e1Split_eq_empty hK hπ (ne_of_data_ne (by decide)),
    decided_inter_e2_eq_empty_of_singleton hK (by decide)]
  rw [Nat.card_coe_set_eq (s := (∅ : Set (Coeff O 4 (M + 4)))), Set.ncard_empty]
  omega

/-- ★★ **The `{(4,1)}` count**: same two sectors as `{(2,2)}` — and under the named
leaf the irreducible term VANISHES (see `coneRemainderCount_four_type41_of_leaf`). -/
theorem coneRemainderCount_four_type41 {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type41 M
      = Nat.card ((decidedSet O 4 type41 (M + 4) ∩ e1IrrBox π (M + 4))
            : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 type41 (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [coneRemainderCount_four_forced_partition (ne_of_data_ne (by decide)) hπ M,
    decided_inter_e1Split_eq_empty hK hπ (ne_of_data_ne (by decide)),
    decided_inter_e2_eq_empty_of_singleton hK (by decide)]
  rw [Nat.card_coe_set_eq (s := (∅ : Set (Coeff O 4 (M + 4)))), Set.ncard_empty]
  omega

/-- ★★ **The tail counts** (`{(1,1),(1,1),(2,1)}` and `{(1,2),(2,1)}`, generically any
non-mixed type with an odd-ramification member): the whole E1 cell contributes nothing —
the count IS the E2 recursion term.  `π`-free. -/
theorem coneRemainderCount_four_of_odd_member {σ : FactorizationType}
    (hσm : σ ≠ mixedType4) (hodd : ∃ p ∈ σ.data, ¬ 2 ∣ p.1) (M : ℕ) :
    coneRemainderCount O 4 σ M
      = Nat.card ((decidedSet O 4 σ (M + 4) ∩ e2Box O (M + 4))
          : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [count_forced hσm M, forcedBox_eq_union, Set.inter_union_distrib_left,
    decided_inter_e1_eq_empty_of_odd hK hodd, Set.empty_union]

end CountPartition

/-! ## §6b — the named-leaf refinements (`O : Type` — the leaf's own universe) -/

section LeafConsumers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Under the named leaf: the irreducible sector is FULLY `{(2,2)}`-decided ... -/
theorem decided_inter_e1Irr_of_leaf (hL : E1IrrLeafDecision) {K : ℕ} (hK : 3 ≤ K)
    {π : O} (hπ : Irreducible π) :
    decidedSet O 4 type22 K ∩ e1IrrBox π K = e1IrrBox π K :=
  Set.inter_eq_self_of_subset_right (fun c hc => hL O K hK π hπ c hc)

/-- ... and the `{(4,1)}` alternative is EMPTY on it. -/
theorem decided41_inter_e1Irr_of_leaf (hL : E1IrrLeafDecision) {K : ℕ} (hK : 3 ≤ K)
    {π : O} (hπ : Irreducible π) :
    decidedSet O 4 type41 K ∩ e1IrrBox π K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hcI⟩
  have h22 : DecidedAt O 4 type22 K c := hL O K hK π hπ c hcI
  exact ne_of_data_ne (by decide) (decidedAt_unique hdec h22)

/-- ★ Under the named leaf, the `{(2,2)}` count is the FULL irreducible sector plus the
recursion term. -/
theorem coneRemainderCount_four_type22_of_leaf (hL : E1IrrLeafDecision) {π : O}
    (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type22 M
      = Nat.card (e1IrrBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4)))
        + Nat.card ((decidedSet O 4 type22 (M + 4) ∩ e1DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [coneRemainderCount_four_type22 hπ M, decided_inter_e1Irr_of_leaf hL hK hπ]

/-- ★ Under the named leaf, the `{(4,1)}` count is PURELY the double-root recursion
term — the wild sector is recursion-only at every level and every `q` (and the p = 3
witness `X⁴ − 6X² − 36X − 18` shows it is NOT parity-empty). -/
theorem coneRemainderCount_four_type41_of_leaf (hL : E1IrrLeafDecision) {π : O}
    (hπ : Irreducible π) (M : ℕ) :
    coneRemainderCount O 4 type41 M
      = Nat.card ((decidedSet O 4 type41 (M + 4) ∩ e1DdBox π (M + 4))
          : Set (Coeff O 4 (M + 4))) := by
  have hK : 3 ≤ M + 4 := by omega
  rw [coneRemainderCount_four_type41 hπ M, decided41_inter_e1Irr_of_leaf hL hK hπ]
  rw [Nat.card_coe_set_eq (s := (∅ : Set (Coeff O 4 (M + 4)))), Set.ncard_empty]
  omega

end LeafConsumers

/-! ## §7 — the sector limit families, the conditional laws, and the census wire -/

section Laws

/-- The normalized split-sector count (the whole box — decided `{(2,1),(2,1)}`). -/
def e1SplitFam : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card (e1SplitBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized irreducible-sector count (the whole box — `{(2,2)}` under the named
leaf). -/
def e1IrrFam : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card (e1IrrBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized σ-decided split-sector count. -/
def e1SplitDecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1SplitBox π (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized σ-decided irreducible-sector count. -/
def e1IrrDecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1IrrBox π (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized σ-decided DOUBLE-ROOT sector count — THE ORDER-2 RECURSION TERM. -/
def e1DdDecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized σ-decided E2 count — the `v₂ = 1` mixed-system recursion term. -/
def e2DecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e2Box O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- ★★★ **THE GENERAL CONDITIONAL LAW** (charge item 2): for every non-mixed σ, the
`e = 4` remainder law follows from `ZcURLim` premises for its FOUR sector families —
the dichotomy count is exact at every level, so the law is their sum. -/
theorem coneRemainderLaw_four_of_sectors {σ : FactorizationType} (hσm : σ ≠ mixedType4)
    (h1 : ZcURLim (e1SplitDecFam σ)) (h2 : ZcURLim (e1IrrDecFam σ))
    (h3 : ZcURLim (e1DdDecFam σ)) (h4 : ZcURLim (e2DecFam σ)) :
    ConeRemainderLaw 4 σ := by
  refine (((h1.add h2).add h3).add h4).congr ?_
  intro O _ _ _ _ _ π hπ M
  show e1SplitDecFam σ O π M + e1IrrDecFam σ O π M + e1DdDecFam σ O π M
      + e2DecFam σ O π M
    = (coneRemainderCount O 4 σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_forced_partition hσm hπ M]
  unfold e1SplitDecFam e1IrrDecFam e1DdDecFam e2DecFam
  push_cast
  ring

/-- ★★ **The `{(2,1),(2,1)}` law** from its three surviving premises: the split box's
own limit (its depth-0 count is decided), the double-root recursion term, and the E2
term. -/
theorem coneRemainderLaw_four_ramPair_of_sectors (h1 : ZcURLim e1SplitFam)
    (h2 : ZcURLim (e1DdDecFam ramPairType)) (h3 : ZcURLim (e2DecFam ramPairType)) :
    ConeRemainderLaw 4 ramPairType := by
  refine ((h1.add h2).add h3).congr ?_
  intro O _ _ _ _ _ π hπ M
  show e1SplitFam O π M + e1DdDecFam ramPairType O π M + e2DecFam ramPairType O π M
    = (coneRemainderCount O 4 ramPairType M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_ramPair hπ M]
  unfold e1SplitFam e1DdDecFam e2DecFam
  push_cast
  ring

/-- ★★ **The `{(2,2)}` law** under the named leaf, from two premises: the irreducible
box's own limit and the double-root recursion term. -/
theorem coneRemainderLaw_four_type22_of_sectors (hL : E1IrrLeafDecision)
    (h1 : ZcURLim e1IrrFam) (h2 : ZcURLim (e1DdDecFam type22)) :
    ConeRemainderLaw 4 type22 := by
  refine (h1.add h2).congr ?_
  intro O _ _ _ _ _ π hπ M
  show e1IrrFam O π M + e1DdDecFam type22 O π M
    = (coneRemainderCount O 4 type22 M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_type22_of_leaf hL hπ M]
  unfold e1IrrFam e1DdDecFam
  push_cast
  ring

/-- ★★ **The `{(4,1)}` law** under the named leaf, from ONE premise: the wild sector is
purely the order-2 recursion term (NOT parity-empty — the `p = 3` witness in the module
fence). -/
theorem coneRemainderLaw_four_type41_of_sectors (hL : E1IrrLeafDecision)
    (h : ZcURLim (e1DdDecFam type41)) : ConeRemainderLaw 4 type41 := by
  refine h.congr ?_
  intro O _ _ _ _ _ π hπ M
  show e1DdDecFam type41 O π M
    = (coneRemainderCount O 4 type41 M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_type41_of_leaf hL hπ M]
  unfold e1DdDecFam
  ring

/-- ★★ **The tail laws** (`{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}` — generically every
non-mixed type with an odd-ramification member) from ONE premise: the E2 recursion
term. -/
theorem coneRemainderLaw_four_of_odd_member {σ : FactorizationType}
    (hσm : σ ≠ mixedType4) (hodd : ∃ p ∈ σ.data, ¬ 2 ∣ p.1)
    (h : ZcURLim (e2DecFam σ)) : ConeRemainderLaw 4 σ := by
  refine h.congr ?_
  intro O _ _ _ _ _ π hπ M
  show e2DecFam σ O π M
    = (coneRemainderCount O 4 σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_of_odd_member hσm hodd M]
  unfold e2DecFam
  ring

end Laws

/-! ## §8 — ★★★ the census front, wired through IFCG33 -/

section Front

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)

/-- ★★★ **THE CENSUS FRONT, wired through the dichotomy** (charge item 3): the
all-degree decided slice rests on EXACTLY (a) the four sector limit families at mass 4
(split / irreducible / double-root / E2 — the two recursion families are the genuinely
open content; the split and irreducible depth-0 boxes carry exact decided counts), (b)
the `e ≥ 5` ramified remainder laws, and (c) the block bridges.  The unramified laws
(IFCG33), the odd-ramification `e = 4` laws (IFCG31), and `e ≤ 3` are all closed. -/
theorem decidedSliceAt_all_of_sector_limits
    (hSplit : ∀ σ : FactorizationType, ZcURLim (e1SplitDecFam σ))
    (hIrr : ∀ σ : FactorizationType, ZcURLim (e1IrrDecFam σ))
    (hDd : ∀ σ : FactorizationType, ZcURLim (e1DdDecFam σ))
    (hE2 : ∀ σ : FactorizationType, ZcURLim (e2DecFam σ))
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n := by
  refine Uniformity.Density.IFCG33.decidedSliceAt_all_of_ram5_even4_bridge hR ?_ hBr
  intro σ hdeg hwit heven
  have hσm : σ ≠ mixedType4 := by
    rintro rfl
    obtain ⟨p, hp, h2⟩ := heven
    have hmem : p = (1, 1) ∨ p = (3, 1) := by
      have hp' : p ∈ ({(1, 1), (3, 1)} : Multiset (ℕ × ℕ)) := hp
      simpa using hp'
    rcases hmem with rfl | rfl <;> omega
  exact coneRemainderLaw_four_of_sectors hσm (hSplit σ) (hIrr σ) (hDd σ) (hE2 σ)

end Front

end Uniformity.Density.IFCG34

end

/-! ## AXCHECK FOOTER — §§1,3 (the sector split, counts, trichotomy) expect Lean core
`{propext, Classical.choice, Quot.sound}`; the decision/forcing/count/law sections
expect Lean core PLUS exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through
IFCG26/IFCG30/IFCG31.  The C.33 cites must NOT occur. -/

#print axioms Uniformity.Density.IFCG34.forcedBox_eq_union
#print axioms Uniformity.Density.IFCG34.card_e1Box
#print axioms Uniformity.Density.IFCG34.card_e2Box
#print axioms Uniformity.Density.IFCG34.monic_quadratic_trichotomy
#print axioms Uniformity.Density.IFCG34.e1Box_eq_genres
#print axioms Uniformity.Density.IFCG34.disjoint_e1SplitBox_e1IrrBox
#print axioms Uniformity.Density.IFCG34.disjoint_e1SplitBox_e1DdBox
#print axioms Uniformity.Density.IFCG34.disjoint_e1IrrBox_e1DdBox
#print axioms Uniformity.Density.IFCG34.decidedAt_e1_split
#print axioms Uniformity.Density.IFCG34.typeOf_e1_irr_mem
#print axioms Uniformity.Density.IFCG34.not_decidedAt_e1_irr
#print axioms Uniformity.Density.IFCG34.not_decidedAt_e1_of_odd_member
#print axioms Uniformity.Density.IFCG34.e1IrrLeafDecision_of_no41
#print axioms Uniformity.Density.IFCG34.exists_ramQuad_factor_of_e2
#print axioms Uniformity.Density.IFCG34.not_decidedAt_e2_of_singleton
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_forced_partition
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_ramPair
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_type22
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_type41
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_of_odd_member
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_type22_of_leaf
#print axioms Uniformity.Density.IFCG34.coneRemainderCount_four_type41_of_leaf
#print axioms Uniformity.Density.IFCG34.coneRemainderLaw_four_of_sectors
#print axioms Uniformity.Density.IFCG34.coneRemainderLaw_four_ramPair_of_sectors
#print axioms Uniformity.Density.IFCG34.coneRemainderLaw_four_type22_of_sectors
#print axioms Uniformity.Density.IFCG34.coneRemainderLaw_four_type41_of_sectors
#print axioms Uniformity.Density.IFCG34.coneRemainderLaw_four_of_odd_member
#print axioms Uniformity.Density.IFCG34.decidedSliceAt_all_of_sector_limits
