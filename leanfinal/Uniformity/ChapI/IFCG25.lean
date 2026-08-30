/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG24
import Uniformity.ChapI.I02_I03w

/-!
# Uniformity.ChapI.IFCG25 — [CN5 2026-08-30] the point cone law: the linear arm proved,
the unramified base change named, the census front re-based

IFCG21 named the two open cone censuses (`PointConeLaw`, `CenteredConeLaw`); IFCG22–24
closed CN0–CN2 and CN4 (translation symmetry, the class NP, the pure-face criterion, the
pure-face monomial bank + the named `ConeRemainderLaw`).  This file executes the CN3 and
CN5 stages of ECONE's blueprint at the interface level:

* **§2 the off-menu fences**: the point family vanishes identically off the degree
  (`ptURLim_pointStrat_of_degree_ne`) and at unwitnessed labels
  (`ptURLim_pointStrat_of_unwitnessed`) — at EVERY base degree `δ`.
* **§3 ★ THE DEEP RECURSION (= stage CN3's heart)**: at every centre `γ`, the level-`(M+m)`
  stratum census of `(X+Cγ)^m` partitions EXACTLY as cone + deep
  (`stratDecCount_eq_cone_add_deep`, via IFCG20's range machinery), and the deep part is
  squeezed between `q^(−T_m)·decidedSeq(M)` and `q^(−T_m)·decidedSeq(M+m)`
  (lower: IFCG3's loop-parameter transport; upper: IFCG20's lift correspondence through
  the `q^(T_m)` mixed-truncation fibre), hence converges to `q^(−T_m)·decidedDensity`
  (`tendsto_deepDecCount`) — LANDED monotone convergence only, no drainage.
* **§4 ★★ THE LINEAR ARM (δ = 1) CLOSES** (`linearPointClause`,`linearPointClause_all`):
  given the degree-`e` decided value law (the kernel's own smaller-laws premise supplies
  it — `e < m` in EVERY `PointConeLaw` clause) and the zero-cone clause at `(e, σ)`
  (= IFCG24's `ConeRemainderLaw` through `zeroConeClause_of_remainderLaw`), the per-point
  stratum family over EVERY linear point is one uniform rational pair: cone value +
  `q^(−T_e)` × decided value.  Point-uniformity is DERIVED (IFCG22's translation
  symmetry + centre-blind deep squeeze), never assumed.
* **§5 ★★ THE NONVACUITY TOOTH** (`pointConeClause_two`): the `(δ, e) = (1, 2)` clause
  body fires UNCONDITIONALLY — `DecidedSliceAt 2` is landed (I02/I03w) and the `m = 2`
  zero-cone clause is IFCG24's unconditional first blood; the `m = 2` remainder law is
  also proved outright (`coneRemainderLaw_two`, remainder EMPTY at every type).
* **§6 ★ THE NAMED BASE CHANGE** (`UnramifiedBlockBridge`): the exact residue of CN5 —
  a per-`(δ ≥ 2, e)` Prop packaging (i) the degree-`δ` unramified extension `O'` as a
  complete DVR with `q' = q^δ`, and (ii) the class-level Hensel block correspondence
  `stratDecCount O (δe) ⟨fScale δ s'⟩ N (p^e) = stratDecCount O' e ⟨s'⟩ N (p'^e)` with
  the inertia scaling `fScale δ : (eᵢ, fᵢ) ↦ (eᵢ, δ·fᵢ)` (labels off `fScale`'s range
  vanish).  `ptURLim_pointStrat_of_bridge` PROVES the consumption: given the bridge, the
  `δ ≥ 2` clause is the `δ = 1` pair composed with `X^δ` — the `∀ O` quantifier of the
  linear arm instantiates at `O'`, so the VALUE side of base change is interface-free,
  exactly as ECONE predicted.
* **§7 ★★★ THE CAPSTONE** (`pointConeLaw_of_remainder_bridge`,
  `decidedSliceAt_all_of_remainder_bridge`): `PointConeLaw` — hence, with IFCG24, the
  WHOLE all-degree decided slice — from exactly TWO named open families:
  `ConeRemainderLaw e σ` at every `e ≥ 2` (NOTE: `e = 2` closed here, `e = 3` is a new
  member — the family is strictly larger than IFCG24's `m ≥ 4` wiring) and
  `UnramifiedBlockBridge δ e` at every `δ, e ≥ 2`.

## ⚠ Scoping disposition (charge item 1, machine-checked side)

The corpus CARRIES the unramified extension: the Quarry backport
(`Uniformity/Quarry/AdjoinRootDVR.lean`) provides `AdjoinRoot φ` as a DVR, unramified,
with residue field `𝔽_q[X]/(p)` (`AdjoinRoot.residueFieldEquiv`), and B53b's
`keyIsDomain` supplies the domain instance.  The bridge's genuinely OPEN legs are:
(i) `IsAdicComplete` transport to `AdjoinRoot φ` (finite module over a complete DVR);
(ii) the residue cardinality count `q' = q^δ` (power basis, easy); (iii) THE HEART —
the level-exact Hensel block correspondence with the `fScale δ` type transport (Galois
descent of the block factorization; `f`-divisibility by `δ` over the point).  These are
deliberately localized in the ONE named Prop; nothing else in `PointConeLaw` needs any
base-change input.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG25

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG1
open Uniformity.Density.IFCG3 (loopMapN kappaLoop bigTLoop kappaLoop_add_bigTLoop
  decidedAt_of_loopMapN card_preimage_mtruncN_kappaLoop card_MBoxN_kappaLoop)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed decidedValueLaw_of_unwitnessed)
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG20 (fullLoopClassN fullLoopClassN_injective mixedTruncN
  mixedTruncN_surjective decided_of_mixedTruncN)
open Uniformity.Density.IFCG21
open Uniformity.Density.IFCG22 (coneCellCount_translation)
open Uniformity.Density.IFCG24

attribute [local instance] Classical.propDecidable

/-! ## §1 — the inertia scaling and THE NAMED BASE-CHANGE BRIDGE -/

/-- **The inertia scaling of a type label under a degree-`δ` unramified base change**,
read in the DESCENT direction: a factor of type `(eᵢ, fᵢ)` over the extension descends
to a factor of type `(eᵢ, δ·fᵢ)` over the base (ramification unchanged, inertia
multiplied by the residue degree of the point). -/
def fScale (δ : ℕ) (s : Multiset (ℕ × ℕ)) : Multiset (ℕ × ℕ) :=
  s.map (fun ef => (ef.1, δ * ef.2))

/-- ★ **THE NAMED BASE-CHANGE BRIDGE at `(δ, e)`** — the exact open residue of ECONE's
stage CN5.  For every base `O` it provides:

1. a degree-`δ` scalar extension: SOME complete DVR `O'` with `q' = q^δ` (used only for
   the denominator obligation of the composed pair);
2. for every residual point `p` of degree `δ`: an extension `O'` with `q' = q^δ`, a
   LINEAR point `p'` over it, and the level-exact class correspondence
   `stratDecCount O (δe) ⟨fScale δ s'⟩ N (p^e) = stratDecCount O' e ⟨s'⟩ N (p'^e)`,
   with every label OUTSIDE `fScale δ`'s range vanishing.

Mathematically `O'` is the unramified extension `O[X]/(φ)` (a monic lift `φ` of `p`),
`p'` is `X − θ̄` at a residual root `θ̄` of `p`, and the correspondence is Galois descent
of the Hensel block decomposition `F = ∏ Frobᵏ(B)` at finite level (the corpus's Quarry
already provides the DVR/local/residue-field legs of `O'`; see the file header). -/
def UnramifiedBlockBridge (δ e : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    (∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (_ : IsAdicComplete (maximalIdeal O') O') (_ : Finite (ResidueField O')),
        residueCard O' = residueCard O ^ δ) ∧
    (∀ p : Polynomial (ResidueField O), p.Monic → p.natDegree = δ → Irreducible p →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
          (_ : IsAdicComplete (maximalIdeal O') O') (_ : Finite (ResidueField O'))
          (p' : Polynomial (ResidueField O')),
        residueCard O' = residueCard O ^ δ ∧
        p'.Monic ∧ p'.natDegree = 1 ∧ Irreducible p' ∧
        (∀ (s' : Multiset (ℕ × ℕ)) (N : ℕ), 1 ≤ N →
          stratDecCount O (δ * e) ⟨fScale δ s'⟩ N (p ^ e)
            = stratDecCount O' e ⟨s'⟩ N (p' ^ e)) ∧
        (∀ s : Multiset (ℕ × ℕ), (∀ s' : Multiset (ℕ × ℕ), s ≠ fScale δ s') →
          ∀ N : ℕ, 1 ≤ N → stratDecCount O (δ * e) ⟨s⟩ N (p ^ e) = 0))

/-! ## §2 — the off-menu fences (every base degree `δ`) -/

section Vanishing

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- An unwitnessed label's decided set is empty at every level (IFCG14's off-menu
mechanism, exported at the set level).  `O : Type` because the witness inhabits
`Witnessed`'s own telescope. -/
theorem decidedSet_eq_empty_of_unwitnessed {n : ℕ} {σ : FactorizationType}
    (h : ¬ Witnessed n σ) (N : ℕ) : decidedSet O n σ N = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro c hc
  obtain ⟨a, ha⟩ := proj_surjective O n N c
  exact h ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    a, hc a ha⟩

/-- An unwitnessed label's stratum-refined count vanishes at every level and stratum. -/
theorem stratDecCount_eq_zero_of_unwitnessed {n N : ℕ} {σ : FactorizationType}
    (h : ¬ Witnessed n σ) (g : Polynomial (ResidueField O)) :
    stratDecCount O n σ N g = 0 := by
  unfold stratDecCount
  rw [decidedSet_eq_empty_of_unwitnessed O h N, Set.empty_inter]
  simp

end Vanishing

/-- **The degree fence**: off the block degree `δ·e` the point family is identically `0`
— a point-uniform limit with the pair `(0, 1)`, at every base degree. -/
theorem ptURLim_pointStrat_of_degree_ne {δ e : ℕ} (s : Multiset (ℕ × ℕ))
    (h : (⟨s⟩ : FactorizationType).degree ≠ δ * e) :
    PtURLim δ (pointStratFamily δ e s) := by
  refine (PtURLim_const δ 0).congr ?_
  intro O _ _ _ _ _ p _ _ _ N _
  show ((0 : ℚ) : ℝ) = pointStratFamily δ e s O p N
  unfold pointStratFamily
  rw [stratPoly_apply, stratDecCount_eq_zero_of_degree_ne h]
  simp

/-- **The witness fence**: at an unwitnessed label the point family is identically `0`,
at every base degree. -/
theorem ptURLim_pointStrat_of_unwitnessed {δ e : ℕ} (s : Multiset (ℕ × ℕ))
    (h : ¬ Witnessed (δ * e) ⟨s⟩) :
    PtURLim δ (pointStratFamily δ e s) := by
  refine (PtURLim_const δ 0).congr ?_
  intro O _ _ _ _ _ p _ _ _ N _
  show ((0 : ℚ) : ℝ) = pointStratFamily δ e s O p N
  unfold pointStratFamily
  rw [stratPoly_apply, stratDecCount_eq_zero_of_unwitnessed O h]
  simp

/-! ## §3 — ★ THE DEEP RECURSION: the exact partition and the two-sided squeeze -/

section Deep

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The deep decided count at centre `γ`**: the mixed boxes whose centre-`γ` full
recentring is `σ`-decided at the target level — by IFCG24's zero-range theorem
(translated), exactly the decided classes of the deep box. -/
def deepDecCount (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (γ : ResidueField O) : ℕ :=
  Nat.card {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)}

/-- The mixed truncation forgets exactly `T_m` digits: its kernel has `q^(T_m)`
elements (the single-centre slice of IFCG20's `card_ker_pairTruncN`). -/
theorem card_ker_mixedTruncN (m M : ℕ) :
    Nat.card (mixedTruncN (O := O) m M).ker = residueCard O ^ bigTLoop m := by
  have h2 := card_preimage_of_surjective (mixedTruncN (O := O) m M)
    (mixedTruncN_surjective m M) Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ, card_coeff, card_MBoxN_kappaLoop] at h2
  have hq : 0 < residueCard O := residueCard_pos O
  have hpos : 0 < residueCard O ^ (m * M + kappaLoop m) := pow_pos hq _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h2, ← pow_add]
  congr 1
  have hsq := kappaLoop_add_bigTLoop m
  have hd : m * (M + m) = m * M + m * m := by ring
  omega

/-- ★ **THE EXACT STRATUM PARTITION at every centre**: stratum census = cone + deep.
The recentring range is inside the stratum (`fullLoopClassN_mem_stratum`), so the
`coneCellCount` subtraction splits the decided stratum classes exactly, and the range
part is counted by the boxes (injectivity). -/
theorem stratDecCount_eq_cone_add_deep {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (σ : FactorizationType) (M : ℕ) (γ : ResidueField O) :
    stratDecCount O m σ (M + m) ((X + C γ) ^ m)
      = coneCellCount O π m σ M γ + deepDecCount π m σ M γ := by
  classical
  have hinj : Function.Injective (fun d : MBoxN O m M => fullLoopClassN π (γ, d)) := by
    intro d d' hdd'
    exact congrArg Prod.snd (fullLoopClassN_injective hπ hm hdd')
  -- the stratum splits along the centre-γ recentring range
  have hsplit := (Set.ncard_inter_add_ncard_sdiff_eq_ncard
    ((decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
      : Set (Coeff O m (M + m)))
    (Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))) (Set.toFinite _)).symm
  -- the range part forgets the stratum constraint (the range IS inside the stratum)
  have hAB : (decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
      ∩ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))
      = decidedSet O m σ (M + m)
        ∩ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d)) := by
    ext c
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hd, -⟩, hb⟩
      exact ⟨hd, hb⟩
    · rintro ⟨hd, hb⟩
      refine ⟨⟨hd, ?_⟩, hb⟩
      obtain ⟨d, rfl⟩ := hb
      exact fullLoopClassN_mem_stratum hπ (by omega) (γ, d)
  -- the decided range part is counted by the boxes
  have himg : (fun d : MBoxN O m M => fullLoopClassN π (γ, d)) ''
      ((fun d : MBoxN O m M => fullLoopClassN π (γ, d)) ⁻¹' decidedSet O m σ (M + m))
      = decidedSet O m σ (M + m)
        ∩ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d)) :=
    Set.image_preimage_eq_inter_range
  have hdeep : (decidedSet O m σ (M + m)
      ∩ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))).ncard
      = deepDecCount π m σ M γ := by
    rw [← himg, Set.ncard_image_of_injective _ hinj]
    unfold deepDecCount
    rw [Nat.card_coe_set_eq]
    rfl
  have hcount : stratDecCount O m σ (M + m) ((X + C γ) ^ m)
      = ((decidedSet O m σ (M + m)
          ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m)) : Set (Coeff O m (M + m))).ncard := by
    rw [stratDecCount, Nat.card_coe_set_eq]
  have hcone : coneCellCount O π m σ M γ
      = (((decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
          \ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d)))
          : Set (Coeff O m (M + m))).ncard := by
    rw [coneCellCount, Nat.card_coe_set_eq]
  rw [hcount, hsplit, hAB, hdeep, hcone]
  omega

/-- **The deep lower bound**: every decided level-`M` class contributes its full
`q^(κ_m)` mixed-box fibre (IFCG3's loop transport `decidedAt_of_loopMapN`, at the
centre `γ`). -/
theorem deepDecCount_lower {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) (γ : ResidueField O) :
    decidedCount O m σ M * residueCard O ^ kappaLoop m ≤ deepDecCount π m σ M γ := by
  classical
  have hsub : (mtruncN (O := O) m M) ⁻¹' (decidedSet O m σ M)
      ⊆ {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)} := by
    intro d hd
    exact decidedAt_of_loopMapN hπ hd
  have hcard := card_preimage_mtruncN_kappaLoop (O := O) m M (decidedSet O m σ M)
  have hle : Nat.card ((mtruncN (O := O) m M) ⁻¹' (decidedSet O m σ M))
      ≤ deepDecCount π m σ M γ := by
    unfold deepDecCount
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  calc decidedCount O m σ M * residueCard O ^ kappaLoop m
      = Nat.card ((mtruncN (O := O) m M) ⁻¹' (decidedSet O m σ M)) := hcard.symm
    _ ≤ deepDecCount π m σ M γ := hle

/-- **The deep upper bound**: each decided box owns `q^(T_m)` distinct decided classes
at the target level (IFCG20's lift correspondence `decided_of_mixedTruncN`, at the
centre `γ`). -/
theorem deepDecCount_upper {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) (γ : ResidueField O) :
    deepDecCount π m σ M γ * residueCard O ^ bigTLoop m
      ≤ decidedCount O m σ (M + m) := by
  classical
  have hsub : (mixedTruncN (O := O) m M) ⁻¹'
      {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)}
      ⊆ decidedSet O m σ (M + m) := by
    intro c hc
    exact decided_of_mixedTruncN hπ hc rfl
  have hcard := card_preimage_of_surjective (mixedTruncN (O := O) m M)
    (mixedTruncN_surjective m M)
    {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)}
  rw [card_ker_mixedTruncN] at hcard
  have hle : Nat.card ((mixedTruncN (O := O) m M) ⁻¹'
      {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)})
      ≤ decidedCount O m σ (M + m) := by
    rw [Nat.card_coe_set_eq]
    rw [show decidedCount O m σ (M + m) = (decidedSet O m σ (M + m)).ncard by
      rw [decidedCount, Nat.card_coe_set_eq]]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  calc deepDecCount π m σ M γ * residueCard O ^ bigTLoop m
      = residueCard O ^ bigTLoop m * deepDecCount π m σ M γ := Nat.mul_comm _ _
    _ = Nat.card ((mixedTruncN (O := O) m M) ⁻¹'
          {d : MBoxN O m M | fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m)}) :=
        hcard.symm
    _ ≤ decidedCount O m σ (M + m) := hle

/-- ★ **THE DEEP LIMIT, centre-uniform**: the normalized deep count converges to
`q^(−T_m)` times the decided density — squeezed between `q^(−T_m)·decidedSeq(M)` and
`q^(−T_m)·decidedSeq(M+m)`, both convergent by the LANDED monotone convergence
`decidedSeq_tendsto` alone.  The limit does not see the centre. -/
theorem tendsto_deepDecCount {π : O} (hπ : Irreducible π) {m : ℕ}
    (σ : FactorizationType) (γ : ResidueField O) :
    Filter.Tendsto
      (fun M => (deepDecCount π m σ M γ : ℝ) / (residueCard O : ℝ) ^ (m * (M + m)))
      Filter.atTop
      (nhds (((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedDensity O m σ)) := by
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  have hqne : (residueCard O : ℝ) ≠ 0 := hq0.ne'
  have hTne : ((residueCard O : ℝ) ^ bigTLoop m) ≠ 0 := pow_ne_zero _ hqne
  have hexp : ∀ M : ℕ, m * (M + m) = kappaLoop m + bigTLoop m + m * M := by
    intro M
    have hsq := kappaLoop_add_bigTLoop m
    have hd : m * (M + m) = m * M + m * m := by ring
    omega
  -- the lower squeeze arm
  have hlo : ∀ M, ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ M
      ≤ (deepDecCount π m σ M γ : ℝ) / (residueCard O : ℝ) ^ (m * (M + m)) := by
    intro M
    have hEq : ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ M
        = ((decidedCount O m σ M : ℝ) * (residueCard O : ℝ) ^ kappaLoop m)
            / (residueCard O : ℝ) ^ (m * (M + m)) := by
      rw [hexp M]
      unfold decidedSeq
      rw [pow_add, pow_add]
      field_simp
    rw [hEq]
    gcongr
    exact_mod_cast deepDecCount_lower hπ m σ M γ
  -- the upper squeeze arm
  have hhi : ∀ M, (deepDecCount π m σ M γ : ℝ) / (residueCard O : ℝ) ^ (m * (M + m))
      ≤ ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ (M + m) := by
    intro M
    have hfam : (deepDecCount π m σ M γ : ℝ) / (residueCard O : ℝ) ^ (m * (M + m))
        = ((deepDecCount π m σ M γ : ℝ) * (residueCard O : ℝ) ^ bigTLoop m)
            / ((residueCard O : ℝ) ^ (m * (M + m)) * (residueCard O : ℝ) ^ bigTLoop m) := by
      field_simp
    have hEq : ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ (M + m)
        = (decidedCount O m σ (M + m) : ℝ)
            / ((residueCard O : ℝ) ^ (m * (M + m)) * (residueCard O : ℝ) ^ bigTLoop m) := by
      unfold decidedSeq
      field_simp
    rw [hfam, hEq]
    gcongr
    exact_mod_cast deepDecCount_upper hπ m σ M γ
  -- both arms converge to q^(−T)·decidedDensity (LANDED monotone convergence only)
  have hlim_lo : Filter.Tendsto
      (fun M => ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ M)
      Filter.atTop
      (nhds (((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedDensity O m σ)) :=
    (decidedSeq_tendsto (O := O) m σ).const_mul _
  have hlim_hi : Filter.Tendsto
      (fun M => ((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedSeq O m σ (M + m))
      Filter.atTop
      (nhds (((residueCard O : ℝ) ^ bigTLoop m)⁻¹ * decidedDensity O m σ)) :=
    (((decidedSeq_tendsto (O := O) m σ).comp (tendsto_add_atTop_nat m)).const_mul _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim_lo hlim_hi hlo hhi

end Deep

/-! ## §4 — ★★ THE LINEAR ARM: the `δ = 1` clauses of `PointConeLaw` -/

/-- ★★ **THE LINEAR POINT CLAUSE** — ECONE's stage CN3, proved: over every complete DVR
and EVERY linear residual point, the normalized stratum census of `p^e` converges to
ONE rational pair: (zero-cone value) + `q^(−T_e)` × (decided value at degree `e`).
Point-uniformity is derived from IFCG22's translation symmetry (cone part) and the
centre-blindness of the deep squeeze (deep part). -/
theorem linearPointClause {e : ℕ} (he : 1 ≤ e) (s : Multiset (ℕ × ℕ))
    (hDV : DecidedValueLaw e ⟨s⟩) (hZC : ZeroConeClause e ⟨s⟩) :
    PtURLim 1 (pointStratFamily 1 e s) := by
  obtain ⟨nc, dc, hdc, hvalc⟩ := hZC
  obtain ⟨nv, dv, hdv, hvalv⟩ := hDV
  refine ⟨nc * (Polynomial.X ^ bigTLoop e * dv) + dc * nv,
    dc * (Polynomial.X ^ bigTLoop e * dv),
    mul_ne_zero hdc (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hdv), ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hnec, hlimc⟩ := hvalc O
  obtain ⟨hnev, hdens⟩ := hvalv O
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hTQ : ((residueCard O : ℕ) : ℚ) ^ bigTLoop e ≠ 0 := pow_ne_zero _ hqQ
  have hden : (dc * (Polynomial.X ^ bigTLoop e * dv)).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero hnec (mul_ne_zero hTQ hnev)
  refine ⟨hden, ?_⟩
  intro p hpm hpd hpi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpeq : p = Polynomial.X + Polynomial.C (p.coeff 0) := hpm.eq_X_add_C hpd
  set γ : ResidueField O := p.coeff 0 with hγ
  -- the value identity in ℚ: cone value + q^(−T)·decided value = the composed pair value
  have hvalQ : (nc.eval ((residueCard O : ℕ) : ℚ) / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      + (((residueCard O : ℕ) : ℚ) ^ bigTLoop e)⁻¹
        * (nv.eval ((residueCard O : ℕ) : ℚ) / dv.eval ((residueCard O : ℕ) : ℚ))
      = ((nc * (Polynomial.X ^ bigTLoop e * dv) + dc * nv).eval ((residueCard O : ℕ) : ℚ)
          / (dc * (Polynomial.X ^ bigTLoop e * dv)).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    field_simp
  -- the two limits, summed
  have hlim_deep := tendsto_deepDecCount (m := e) hπ ⟨s⟩ γ
  rw [hdens] at hlim_deep
  have hsum := (hlimc π hπ).add hlim_deep
  -- fold the limit value into the pair shape
  have hvalR : (((nc.eval ((residueCard O : ℕ) : ℚ)
        / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ)
      + ((residueCard O : ℝ) ^ bigTLoop e)⁻¹
        * (((nv.eval ((residueCard O : ℕ) : ℚ)
            / dv.eval ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ)
      = ((((nc * (Polynomial.X ^ bigTLoop e * dv) + dc * nv).eval ((residueCard O : ℕ) : ℚ)
          / (dc * (Polynomial.X ^ bigTLoop e * dv)).eval ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ) := by
    rw [← hvalQ]
    push_cast
    ring
  rw [hvalR] at hsum
  -- the exact partition at every finite level, translated to the zero centre
  have hshift : ∀ M : ℕ,
      coneFamily e ⟨s⟩ O π M
        + (deepDecCount π e ⟨s⟩ M γ : ℝ) / (residueCard O : ℝ) ^ (e * (M + e))
      = (stratDecCount O e ⟨s⟩ (M + e) ((Polynomial.X + Polynomial.C γ) ^ e) : ℝ)
          / (residueCard O : ℝ) ^ (e * (M + e)) := by
    intro M
    rw [stratDecCount_eq_cone_add_deep hπ (by omega : 0 < e) ⟨s⟩ M γ]
    rw [coneCellCount_translation hπ (by omega : 1 ≤ e) ⟨s⟩ M γ 0]
    push_cast
    rw [add_div]
    rfl
  -- the M-shifted family converges, hence the N-family does
  have hN : Filter.Tendsto (fun N =>
      (stratDecCount O e ⟨s⟩ N ((Polynomial.X + Polynomial.C γ) ^ e) : ℝ)
        / (residueCard O : ℝ) ^ (e * N)) Filter.atTop
      (nhds ((((nc * (Polynomial.X ^ bigTLoop e * dv) + dc * nv).eval
          ((residueCard O : ℕ) : ℚ)
        / (dc * (Polynomial.X ^ bigTLoop e * dv)).eval
          ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ)) := by
    refine (Filter.tendsto_add_atTop_iff_nat e).mp ?_
    exact hsum.congr fun M => hshift M
  refine hN.congr fun N => ?_
  show (stratDecCount O e ⟨s⟩ N ((Polynomial.X + Polynomial.C γ) ^ e) : ℝ)
      / (residueCard O : ℝ) ^ (e * N) = pointStratFamily 1 e s O p N
  unfold pointStratFamily
  rw [stratPoly_apply, ← hpeq, one_mul]
  push_cast
  ring

/-- ★★ The linear arm assembled over ALL labels: value law + zero-cone clause on the
degree-`e` menu (witnessed labels), the fences off it. -/
theorem linearPointClause_all {e : ℕ} (he : 1 ≤ e)
    (hDV : ∀ σ : FactorizationType, σ.degree = e → DecidedValueLaw e σ)
    (hZC : ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ → ZeroConeClause e σ)
    (s : Multiset (ℕ × ℕ)) :
    PtURLim 1 (pointStratFamily 1 e s) := by
  by_cases hdeg : (⟨s⟩ : FactorizationType).degree = e
  · by_cases hwit : Witnessed e ⟨s⟩
    · exact linearPointClause he s (hDV ⟨s⟩ hdeg) (hZC ⟨s⟩ hdeg hwit)
    · refine ptURLim_pointStrat_of_unwitnessed s ?_
      rw [one_mul]
      exact hwit
  · refine ptURLim_pointStrat_of_degree_ne s ?_
    rw [one_mul]
    exact hdeg

/-! ## §5 — ★★ THE NONVACUITY TOOTH: the `(δ, e) = (1, 2)` clause, unconditional -/

section Tooth

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The `m = 2` cone remainder is EMPTY at every type (the ramified case is IFCG24's
`coneRemainder_two_ram_eq_zero`; every other type's cone is already zero). -/
theorem coneRemainderCount_two_eq_zero (σ : FactorizationType) (M : ℕ) :
    coneRemainderCount O 2 σ M = 0 := by
  by_cases hσ : σ = ⟨{(2, 1)}⟩
  · subst hσ
    exact coneRemainder_two_ram_eq_zero M
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    rw [← coneCellCount_eq_remainder_of_ne hπ (by omega) hσ M]
    exact coneCellCount_two_ne hπ hσ M

end Tooth

/-- ★ **The `m = 2` member of the remainder-law family, proved outright** — the family
`ConeRemainderLaw e σ` consumed by the capstone is closed at `e = 2` (pair `(0, 1)`). -/
theorem coneRemainderLaw_two (σ : FactorizationType) : ConeRemainderLaw 2 σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π _ M
  show (0 : ℝ)
      = (coneRemainderCount O 2 σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (2 * (M + 2))
  rw [coneRemainderCount_two_eq_zero σ M]
  simp

/-- ★★ **THE TOOTH**: the `(δ, e) = (1, 2)` clause body of `PointConeLaw`, UNCONDITIONAL
— the quadratic stratum census over EVERY linear point at EVERY complete DVR is one
uniform rational pair.  Supply: the landed `DecidedSliceAt 2` (I02/I03w) and IFCG24's
unconditional `zeroConeClause_two`. -/
theorem pointConeClause_two (s : Multiset (ℕ × ℕ)) :
    PtURLim 1 (pointStratFamily 1 2 s) := by
  by_cases hdeg : (⟨s⟩ : FactorizationType).degree = 2
  · exact linearPointClause (by omega) s (decidedSliceAt_two ⟨s⟩ hdeg)
      (zeroConeClause_two ⟨s⟩)
  · refine ptURLim_pointStrat_of_degree_ne s ?_
    rw [one_mul]
    exact hdeg

/-! ## §6 — ★ the bridge consumption: base change IS interface-level -/

/-- ★ **The bridge fires the `δ ≥ 2` clauses**: given the named block bridge and the
linear arm at exponent `e`, the degree-`δ` point clause holds with the pair COMPOSED
with `X^δ` — the `∀ O` quantifier of the linear pair instantiates at the extension
`O'`, so `q ↦ q^δ` is the whole of base change at the value level. -/
theorem ptURLim_pointStrat_of_bridge {δ e : ℕ} (hδ : 1 ≤ δ)
    (hBr : UnramifiedBlockBridge δ e)
    (hLin : ∀ s' : Multiset (ℕ × ℕ), PtURLim 1 (pointStratFamily 1 e s'))
    (s : Multiset (ℕ × ℕ)) :
    PtURLim δ (pointStratFamily δ e s) := by
  classical
  by_cases hs : ∃ s₀ : Multiset (ℕ × ℕ), s = fScale δ s₀
  · -- the label descends: the pair is the linear pair composed with X^δ
    obtain ⟨s₀, rfl⟩ := hs
    obtain ⟨n, d, hd, hval⟩ := hLin s₀
    have hdcomp : d.comp (Polynomial.X ^ δ) ≠ 0 := by
      have hX : (Polynomial.X ^ δ : Polynomial ℚ).natDegree ≠ 0 := by
        rw [Polynomial.natDegree_X_pow]
        omega
      intro hzero
      apply hd
      have h1 : (d.comp (Polynomial.X ^ δ)).leadingCoeff = 0 := by
        rw [hzero]
        simp
      rw [Polynomial.leadingCoeff_comp hX] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact Polynomial.leadingCoeff_eq_zero.mp h
      · exfalso
        rw [Polynomial.leadingCoeff_X_pow, one_pow] at h
        exact one_ne_zero h
    refine ⟨n.comp (Polynomial.X ^ δ), d.comp (Polynomial.X ^ δ), hdcomp, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hEx, hPt⟩ := hBr O
    constructor
    · -- the denominator obligation, through the scalar-extension witness
      obtain ⟨O'', hO''⟩ := hEx
      obtain ⟨iC, hO''⟩ := hO''
      letI := iC
      obtain ⟨iD, hO''⟩ := hO''
      letI := iD
      obtain ⟨iV, hO''⟩ := hO''
      letI := iV
      obtain ⟨iA, hO''⟩ := hO''
      letI := iA
      obtain ⟨iF, hq''⟩ := hO''
      letI := iF
      have h1 := (hval O'').1
      rw [hq'', Nat.cast_pow] at h1
      rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
      exact h1
    · intro p hpm hpd hpi
      obtain ⟨O', hO'⟩ := hPt p hpm hpd hpi
      obtain ⟨iC, hO'⟩ := hO'
      letI := iC
      obtain ⟨iD, hO'⟩ := hO'
      letI := iD
      obtain ⟨iV, hO'⟩ := hO'
      letI := iV
      obtain ⟨iA, hO'⟩ := hO'
      letI := iA
      obtain ⟨iF, hO'⟩ := hO'
      letI := iF
      obtain ⟨p', hq', hp'm, hp'd, hp'i, hcorr, -⟩ := hO'
      obtain ⟨hne', hlim'⟩ := hval O'
      have hlim := hlim' p' hp'm hp'd hp'i
      have hvv : ((n.eval ((residueCard O' : ℕ) : ℚ)
            / d.eval ((residueCard O' : ℕ) : ℚ) : ℚ) : ℝ)
          = (((n.comp (Polynomial.X ^ δ)).eval ((residueCard O : ℕ) : ℚ)
            / (d.comp (Polynomial.X ^ δ)).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
        rw [Polynomial.eval_comp, Polynomial.eval_comp, Polynomial.eval_pow,
          Polynomial.eval_X, hq', Nat.cast_pow]
      rw [hvv] at hlim
      refine hlim.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      show pointStratFamily 1 e s₀ O' p' N = pointStratFamily δ e (fScale δ s₀) O p N
      unfold pointStratFamily
      simp only [stratPoly_apply]
      rw [one_mul, ← hcorr s₀ N hN, hq', Nat.cast_pow, ← pow_mul, ← mul_assoc]
  · -- the label does not descend: the family vanishes identically
    have hs' : ∀ s₀ : Multiset (ℕ × ℕ), s ≠ fScale δ s₀ := fun s₀ h => hs ⟨s₀, h⟩
    refine (PtURLim_const δ 0).congr ?_
    intro O _ _ _ _ _ p hpm hpd hpi N hN
    obtain ⟨-, hPt⟩ := hBr O
    obtain ⟨O', hO'⟩ := hPt p hpm hpd hpi
    obtain ⟨iC, hO'⟩ := hO'
    letI := iC
    obtain ⟨iD, hO'⟩ := hO'
    letI := iD
    obtain ⟨iV, hO'⟩ := hO'
    letI := iV
    obtain ⟨iA, hO'⟩ := hO'
    letI := iA
    obtain ⟨iF, hO'⟩ := hO'
    letI := iF
    obtain ⟨p', hq', hp'm, hp'd, hp'i, -, hvan⟩ := hO'
    show ((0 : ℚ) : ℝ) = pointStratFamily δ e s O p N
    unfold pointStratFamily
    rw [stratPoly_apply, hvan s hs' N hN]
    simp

/-! ## §7 — ★★★ THE CAPSTONE: the census front re-based -/

/-- ★★★ **THE POINT CONE LAW from the two named families**: `ConeRemainderLaw e σ` at
every `e ≥ 2` (with the same conditional supply the law itself carries — note the
family INCLUDES `e = 2` (closed, `coneRemainderLaw_two`) and `e = 3` (open, NOT in
IFCG24's `m ≥ 4` wiring)) and `UnramifiedBlockBridge δ e` at every `δ, e ≥ 2`.
Every clause of `PointConeLaw` has `e < m`, so the premise's smaller value laws feed
both the deep recursion (at degree `e`) and the remainder family's own supply. -/
theorem pointConeLaw_of_remainder_bridge
    (hR : ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    PointConeLaw := by
  intro m hm hsm δ e hδ he hde hexcl s
  -- every clause has e < m: at δ = 1 by the self-call fence, at δ ≥ 2 by mass
  have hem : e < m := by
    rcases Nat.lt_or_ge δ 2 with h1 | h2
    · have hδ1 : δ = 1 := by omega
      subst hδ1
      rw [one_mul] at hde
      rcases Nat.lt_or_ge e m with h | h
      · exact h
      · exact absurd ⟨rfl, by omega⟩ hexcl
    · have h2e : 2 * e ≤ δ * e := Nat.mul_le_mul_right e h2
      omega
  have hDVe : ∀ σ' : FactorizationType, σ'.degree = e → DecidedValueLaw e σ' :=
    fun σ' h => hsm e hem σ' h
  have hZCe : ∀ σ' : FactorizationType, σ'.degree = e → Witnessed e σ' →
      ZeroConeClause e σ' := by
    intro σ' hdeg hwit
    exact zeroConeClause_of_remainderLaw (by omega : 0 < e) σ'
      (hR e he (fun k hk σ'' h'' => hsm k (by omega) σ'' h'') σ' hdeg hwit)
  have hLin : ∀ s' : Multiset (ℕ × ℕ), PtURLim 1 (pointStratFamily 1 e s') :=
    linearPointClause_all (by omega : 1 ≤ e) hDVe hZCe
  rcases Nat.lt_or_ge δ 2 with h1 | h2
  · have hδ1 : δ = 1 := by omega
    subst hδ1
    exact hLin s
  · exact ptURLim_pointStrat_of_bridge (by omega : 1 ≤ δ) (hBr δ e h2 he) hLin s

/-- ★★★ **THE CENSUS FRONT, re-based once more**: remainder laws (every `e ≥ 2`) +
block bridges (`δ, e ≥ 2`) fire the WHOLE all-degree decided slice — `PointConeLaw`
via this file, `CenteredConeLaw` via IFCG24's wiring. -/
theorem decidedSliceAt_all_of_remainder_bridge
    (hR : ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_pointCone_remainder (pointConeLaw_of_remainder_bridge hR hBr)
    (fun m hm hsm σ hσ hwit => hR m (by omega) hsm σ hσ hwit)

end Uniformity.Density.IFCG25

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG25.decidedSet_eq_empty_of_unwitnessed
#print axioms Uniformity.Density.IFCG25.stratDecCount_eq_zero_of_unwitnessed
#print axioms Uniformity.Density.IFCG25.ptURLim_pointStrat_of_degree_ne
#print axioms Uniformity.Density.IFCG25.ptURLim_pointStrat_of_unwitnessed
#print axioms Uniformity.Density.IFCG25.card_ker_mixedTruncN
#print axioms Uniformity.Density.IFCG25.deepDecCount_lower
#print axioms Uniformity.Density.IFCG25.deepDecCount_upper
#print axioms Uniformity.Density.IFCG25.coneRemainderCount_two_eq_zero
#print axioms Uniformity.Density.IFCG25.stratDecCount_eq_cone_add_deep
#print axioms Uniformity.Density.IFCG25.tendsto_deepDecCount
#print axioms Uniformity.Density.IFCG25.linearPointClause
#print axioms Uniformity.Density.IFCG25.linearPointClause_all
#print axioms Uniformity.Density.IFCG25.coneRemainderLaw_two
#print axioms Uniformity.Density.IFCG25.pointConeClause_two
#print axioms Uniformity.Density.IFCG25.ptURLim_pointStrat_of_bridge
#print axioms Uniformity.Density.IFCG25.pointConeLaw_of_remainder_bridge
#print axioms Uniformity.Density.IFCG25.decidedSliceAt_all_of_remainder_bridge
