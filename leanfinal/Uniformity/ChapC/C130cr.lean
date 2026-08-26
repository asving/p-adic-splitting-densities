/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130k2
import Uniformity.ChapC.C130ln
import Uniformity.ChapC.C130s2

/-!
# Uniformity.ChapC.C130cr — the canonical L-valued read (chain-carrier node CC-10)

**Chain-carrier node CC-10** of `docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` (§4.2,
§8 row C.130h, §10 row CC-10: *"Construct/export `canonicalRead` on level kernels and
synchronized product; prove distinguished-generator views"*), transcribing freeze-v2 layer
**C.130h** (`TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` §4, §7 row 8): the canonical
L-valued node-point residue read, exported from the carrier's `canonicalRead` SOURCE field
(C130k's `NodePointSource`) to the level kernels and to the synchronized product lattice
(C130f's `GaugeLattice0`/`GaugeLattice`), with the distinguished-generator views.

## Source rows (freeze v2 §4's clause table)

* **EFF.T1.01** (wrap generator `W₀`, the level-one node residue): the kernel element
  `x^{e₁}·π^{−u₁}` — here `DeepTower.wrapGen`/`wrapClass`, with kernel membership PROVED from
  the exact division `e₁ ∣ ê_i` (C.87's `ehat_dvd`).  D62w's `d2g1`/`d3g1 = (−1,2,0,…)` are the
  regressions (Teeth below, at the S2 chain).
* **DEF GENTOW5-1 S2.1 / S2.3 step (3)** (generator `Λ_a` at general depth): the letter
  `Φ_a^{e_{a+1}}` normalized by the chain normalizer at its exact height — here
  `LaurentNormalizer.letterClass`, a `heightClass` of CC-4's Laurent normalizer
  (`C130ln.laurentNormalizer`; `EFF.GENTOW5.16`'s `Λ`-numerator height is C130pt's
  `key_value_pow_e`, and the normalizer half consumed here is `exact_height`).  D62w's
  `d2g2 = (−2,−1,2)` and `d3g2`/`d3g3` are the regressions (Teeth: the S2 level-2 letter class
  IS `(−2,−1,2)`, machine-evaluated).
* **OM-8 §3.1 L2** (multiplicative extension at node points): the read of ANY
  distinguished-generator word factors through the generator values —
  `canonicalRead_generatorWord` is exactly freeze v2 §4's display shape
  `canonicalRes(τ) = η^m·∏ β_a^{t_a}`, L-valued.  The defect-corrected τ-multiplicativity
  (`heightClass_mul`/`canonicalRead_heightClass_mul`) is the general-depth form of D62w's τ
  reductions.
* **Freeze v2 §4, extension clause** ("extended to the synchronized product by sending the
  other level factors to `1`"): `canonicalRes0`/`canonicalRes` restrict the level read to the
  synchronized kernels along the level projection, and the other-factors-to-1 clause is a
  THEOREM (`canonicalRes0_eq_one_of_level_one`, `canonicalRes0_insert_ne`), not a convention.

**[PK-2/U15, 2026-08-25]** — packaging-route view-binder ripple
(`PACKAGING_ROUTE_2026-08-25.md` §4/PK-2): every node binder below is retyped
un-split→split (`NodePointSource` → `SplitNodePointSource`, C130k2), signature-only — the
one consumed node field (`canonicalRead`) is byte-identical between the two structures, so
every proof is byte-stable.  Prose mentions of the un-split name below are the historical
CC-10 record.

## Honesty ledger

* `canonicalRead` is a CARRIED source field of `NodePointSource`; its values at the
  distinguished generators (`wrapValue`, `letterValue`) are named EXPORTS, not constructions.
  The C.130g bridge tying `letterValue` to the node-point residue classes `β_a` is OPEN
  (freeze v2 §4) and is NOT claimed here.
* The triangular-basis bridge (every level-kernel element IS a distinguished-generator word,
  hence uniqueness of the extension) is OPEN (freeze v2 §4: "D62w currently proves general
  existence of a factorisation but not the complete chain-indexed uniqueness/instantiation");
  no spanning or uniqueness theorem is stated here.

## Fence (grep-tooth)

None of the four separate terminal-field W-leg identifiers of design §8 row C.130i (node
CC-11's objects) appears anywhere in this file, and no declaration states or implies any
agreement between the canonical L-valued read and the separate Kt-valued read — the
separation of the two residue reads is a design invariant (freeze v2 D-TIF-5, design §4.2).
Nothing in this file has a `Kt`-valued codomain.

DEPENDS: C130k (CC-1: `NodePointSource`, `LaurentNormalizer`, live ranges) · C130f
(`LevelExponentLattice`, `GaugeLattice0/`, `levelExponentHeight`, `levelHeight0/`,
`gaugeLatticeEquiv`) · C130ln (CC-4: `laurentNormalizer`, exact height) · C130s2 (CC-2:
`s2DepthTwo`, teeth) · C87 (`ehat` API).

## Status

Zero `sorry`; no new axiom; no `unsafe`; no `True` body; axiom footprint Lean-core only
(AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open scoped BigOperators
open Uniformity.Density.Leaf

universe uE uG uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## 1. The lattice letters and their exact heights

The distinguished multiplicative letters of the level-`i` Laurent lattice
`(π, x, Φ₁, …, Φ_{i−1})`, and their `levelExponentHeight` values — the raw material of the
generator classes.  Everything is total in `i`; liveness is consumed only where C.87's exact
`ehat` divisions or CC-4's exact heights are consumed. -/

/-- Anti-drift pin: the level height of an `ofAdd` exponent tuple is its weighted sum,
definitionally (the C130f weight pattern `(ê_i, (ê_i/e₁)u₁, (ê_i/ê_{a+2})u_{a+2})`). -/
theorem levelExponentHeight_ofAdd (T : DeepTower F H₀ hpin r) (i : ℕ)
    (v : ℤ × ℤ × (Fin (i - 1) → ℤ)) :
    levelExponentHeight T i (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd
        (v.1 * T.ehat i + v.2.1 * ((T.ehat i / T.e 1) * T.u 1) +
          ∑ a : Fin (i - 1), v.2.2 a * ((T.ehat i / T.ehat (a.1 + 2)) * T.u (a.1 + 2))) := rfl

/-- The `π`-letter of the level-`i` lattice. -/
def piLetter (i : ℕ) : LevelExponentLattice i := Multiplicative.ofAdd (1, 0, 0)

/-- The `x`-letter of the level-`i` lattice. -/
def xLetter (i : ℕ) : LevelExponentLattice i := Multiplicative.ofAdd (0, 1, 0)

/-- The `Φ_(a+1)`-letter of the level-`i` lattice (coordinate `a` of the key block). -/
def keyLetter (i : ℕ) (a : Fin (i - 1)) : LevelExponentLattice i :=
  Multiplicative.ofAdd (0, 0, Pi.single a 1)

/-- The `π`-letter sits at height `ê_i`. -/
theorem piLetter_height (T : DeepTower F H₀ hpin r) (i : ℕ) :
    levelExponentHeight T i (piLetter i) = Multiplicative.ofAdd (T.ehat i : ℤ) := by
  rw [piLetter, levelExponentHeight_ofAdd]
  congr 1
  simp

/-- The `x`-letter sits at height `(ê_i/e₁)·u₁`. -/
theorem xLetter_height (T : DeepTower F H₀ hpin r) (i : ℕ) :
    levelExponentHeight T i (xLetter i) =
      Multiplicative.ofAdd ((T.ehat i : ℤ) / (T.e 1 : ℤ) * (T.u 1 : ℤ)) := by
  rw [xLetter, levelExponentHeight_ofAdd]
  congr 1
  simp

/-- The `Φ_(a+1)`-letter sits at height `(ê_i/ê_{a+2})·u_{a+2}`. -/
theorem keyLetter_height (T : DeepTower F H₀ hpin r) (i : ℕ) (a : Fin (i - 1)) :
    levelExponentHeight T i (keyLetter i a) =
      Multiplicative.ofAdd ((T.ehat i : ℤ) / (T.ehat (a.1 + 2) : ℤ) * (T.u (a.1 + 2) : ℤ)) := by
  rw [keyLetter, levelExponentHeight_ofAdd]
  congr 1
  simp only [zero_mul, zero_add]
  rw [Fintype.sum_eq_single a fun b hb => by simp [Pi.single_eq_of_ne hb]]
  rw [Pi.single_eq_same, one_mul]

/-- Heights of products, in `ofAdd` form (the hypothesis feeder for `heightClass_mul`). -/
theorem levelExponentHeight_mul_ofAdd (T : DeepTower F H₀ hpin r) {i : ℕ}
    {g g' : LevelExponentLattice i} {k k' : ℤ}
    (hg : levelExponentHeight T i g = Multiplicative.ofAdd k)
    (hg' : levelExponentHeight T i g' = Multiplicative.ofAdd k') :
    levelExponentHeight T i (g * g') = Multiplicative.ofAdd (k + k') := by
  rw [map_mul, hg, hg', ofAdd_add]

/-! ## 2. Height classes: kernel elements from exact heights

Freeze v2 §4's "τ kernel-membership from exact heights", at the carrier: given any element of
exact height `k` (stage-live), dividing by the normalizer word `n̂_i(k)` lands in the level
kernel.  The normalizer is CC-4's honest integer/Laurent carrier (`C130k.LaurentNormalizer`),
NOT C.83's truncated `towerNorm` (C130B's refutation). -/

namespace LaurentNormalizer

variable {W : DeepTower.{0, uKt} F H₀ hpin r} (N : LaurentNormalizer W)

/-- Kernel membership from an exact height: `g · n̂_i(k)⁻¹` lies in the level kernel. -/
theorem mul_norm_inv_mem_ker {i : ℕ} (hi : StageLive r i) {g : LevelExponentLattice i}
    {k : ℤ} (hg : levelExponentHeight W i g = Multiplicative.ofAdd k) :
    g * (N.norm i k)⁻¹ ∈ MonoidHom.ker (levelExponentHeight W i) := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hg, N.exact_height i hi k]
  exact mul_inv_cancel _

/-- The τ-class of an exact height: the level-kernel element `g · n̂_i(k)⁻¹`. -/
def heightClass {i : ℕ} (hi : StageLive r i) (g : LevelExponentLattice i) (k : ℤ)
    (hg : levelExponentHeight W i g = Multiplicative.ofAdd k) :
    MonoidHom.ker (levelExponentHeight W i) :=
  ⟨g * (N.norm i k)⁻¹, N.mul_norm_inv_mem_ker hi hg⟩

/-- Anti-drift pin: the τ-class is `g · n̂_i(k)⁻¹`, nothing else. -/
theorem heightClass_coe {i : ℕ} (hi : StageLive r i) (g : LevelExponentLattice i) (k : ℤ)
    (hg : levelExponentHeight W i g = Multiplicative.ofAdd k) :
    (N.heightClass hi g k hg : LevelExponentLattice i) = g * (N.norm i k)⁻¹ := rfl

/-- The normalizer word itself has the trivial class. -/
theorem heightClass_norm {i : ℕ} (hi : StageLive r i) (k : ℤ) :
    N.heightClass hi (N.norm i k) k (N.exact_height i hi k) = 1 := by
  apply Subtype.ext
  rw [heightClass_coe, OneMemClass.coe_one]
  exact mul_inv_cancel _

/-- The normalizer defect at heights `k, k'`: the kernel element
`n̂_i(k)·n̂_i(k')·n̂_i(k+k')⁻¹` measuring the failure of `n̂_i` to be a homomorphism in the
height.  The τ-multiplicativity of the classes is exact up to multiplication by this
defect. -/
def defect {i : ℕ} (hi : StageLive r i) (k k' : ℤ) :
    MonoidHom.ker (levelExponentHeight W i) :=
  ⟨N.norm i k * N.norm i k' * (N.norm i (k + k'))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, N.exact_height i hi,
      N.exact_height i hi, N.exact_height i hi, ← ofAdd_add]
    exact mul_inv_cancel _⟩

/-- Anti-drift pin: the defect is `n̂_i(k)·n̂_i(k')·n̂_i(k+k')⁻¹`, nothing else. -/
theorem defect_coe {i : ℕ} (hi : StageLive r i) (k k' : ℤ) :
    (N.defect hi k k' : LevelExponentLattice i) =
      N.norm i k * N.norm i k' * (N.norm i (k + k'))⁻¹ := rfl

/-- **Defect-corrected τ-multiplicativity** (the general-depth form of D62w's τ reductions):
the class of a product is the product of the classes times the normalizer defect. -/
theorem heightClass_mul {i : ℕ} (hi : StageLive r i) {g g' : LevelExponentLattice i}
    {k k' : ℤ} (hg : levelExponentHeight W i g = Multiplicative.ofAdd k)
    (hg' : levelExponentHeight W i g' = Multiplicative.ofAdd k')
    (hgg' : levelExponentHeight W i (g * g') = Multiplicative.ofAdd (k + k')) :
    N.heightClass hi (g * g') (k + k') hgg' =
      N.heightClass hi g k hg * N.heightClass hi g' k' hg' * N.defect hi k k' := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, heightClass_coe, defect_coe]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv]
  abel

end LaurentNormalizer

/-! ## 3. The distinguished generators

Freeze v2 §4's distinguished generators of the level kernel: the wrap generator `W₀`
(EFF.T1.01's level-one node residue, D62w's `d2g1`/`d3g1`) and the letters `Λ_a`
(DEF GENTOW5-1 S2.1/S2.3 step (3), D62w's `d2g2`/`d3g2`/`d3g3`).  `W₀` is the explicit word
`x^{e₁}·π^{−u₁}`; `Λ_a` is the normalized key power `Φ_{a+1}^{e_{a+2}}·n̂_i(·)⁻¹` at its exact
height.  No spanning claim is made (the triangular-basis bridge is OPEN, freeze v2 §4). -/

namespace DeepTower

/-- **The wrap generator `W₀`** at level `i`: the Laurent word `x^{e₁}·π^{−u₁}` (EFF.T1.01;
D62w's `d2g1 = (−1, 2, 0)` at the S2 chain).  Total in `i`; kernel membership is live. -/
def wrapGen (T : DeepTower F H₀ hpin r) (i : ℕ) : LevelExponentLattice i :=
  Multiplicative.ofAdd (-(T.u 1 : ℤ), (T.e 1 : ℤ), 0)

/-- The wrap generator lies in the level kernel at every stage-live level: its height is
`−u₁·ê_i + e₁·(ê_i/e₁)·u₁ = 0`, by the exact division `e₁ ∣ ê_i` (C.87's `ehat_dvd`). -/
theorem wrapGen_mem_ker (T : DeepTower F H₀ hpin r) {i : ℕ} (hi : StageLive r i) :
    T.wrapGen i ∈ MonoidHom.ker (levelExponentHeight T i) := by
  have hdvd : (T.e 1 : ℤ) ∣ (T.ehat i : ℤ) :=
    Int.natCast_dvd_natCast.mpr (T.ehat_one ▸ T.ehat_dvd hi.1)
  rw [MonoidHom.mem_ker, wrapGen, levelExponentHeight_ofAdd, ofAdd_eq_one]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← mul_assoc, Int.mul_ediv_cancel' hdvd]
  ring

/-- The wrap generator, as a level-kernel element. -/
def wrapClass (T : DeepTower F H₀ hpin r) {i : ℕ} (hi : StageLive r i) :
    MonoidHom.ker (levelExponentHeight T i) :=
  ⟨T.wrapGen i, T.wrapGen_mem_ker hi⟩

/-- Anti-drift pin: the wrap class carries the wrap generator, nothing else. -/
theorem wrapClass_coe (T : DeepTower F H₀ hpin r) {i : ℕ} (hi : StageLive r i) :
    (T.wrapClass hi : LevelExponentLattice i) = T.wrapGen i := rfl

end DeepTower

namespace LaurentNormalizer

variable {W : DeepTower.{0, uKt} F H₀ hpin r} (N : LaurentNormalizer W)

/-- **The letter generator `Λ_a`** at a stage-live level `i`: the key power
`Φ_{a+1}^{e_{a+2}}` normalized by the chain normalizer at its exact height
`e_{a+2}·(ê_i/ê_{a+2})·u_{a+2}` (DEF GENTOW5-1 S2.1/S2.3 step (3); the numerator height is
C130pt's `key_value_pow_e` arithmetic, the normalizer half is CC-4's `exact_height`). -/
def letterClass {i : ℕ} (hi : StageLive r i) (a : Fin (i - 1)) :
    MonoidHom.ker (levelExponentHeight W i) :=
  N.heightClass hi (keyLetter i a ^ W.e (a.1 + 2))
    ((W.e (a.1 + 2) : ℤ) * ((W.ehat i : ℤ) / (W.ehat (a.1 + 2) : ℤ) * (W.u (a.1 + 2) : ℤ)))
    (by rw [map_pow, keyLetter_height, ← ofAdd_nsmul, nsmul_eq_mul])

/-- Anti-drift pin: `Λ_a` is the normalized key power, nothing else. -/
theorem letterClass_coe {i : ℕ} (hi : StageLive r i) (a : Fin (i - 1)) :
    (N.letterClass hi a : LevelExponentLattice i) =
      keyLetter i a ^ W.e (a.1 + 2) *
        (N.norm i ((W.e (a.1 + 2) : ℤ) *
          ((W.ehat i : ℤ) / (W.ehat (a.1 + 2) : ℤ) * (W.u (a.1 + 2) : ℤ))))⁻¹ := rfl

/-- A distinguished-generator word in the level kernel: `W₀^m · ∏_a Λ_a^{t_a}`. -/
def generatorWord {i : ℕ} (hi : StageLive r i) (m : ℤ) (t : Fin (i - 1) → ℤ) :
    MonoidHom.ker (levelExponentHeight W i) :=
  W.wrapClass hi ^ m * ∏ a, N.letterClass hi a ^ t a

/-- Anti-drift pin: the generator word is exactly its displayed factorization. -/
theorem generatorWord_def {i : ℕ} (hi : StageLive r i) (m : ℤ) (t : Fin (i - 1) → ℤ) :
    N.generatorWord hi m t = W.wrapClass hi ^ m * ∏ a, N.letterClass hi a ^ t a := rfl

end LaurentNormalizer

/-! ## 4. The canonical read at the distinguished generators (level kernels)

The carrier's `canonicalRead` SOURCE field, exported at the generators: the named values
`wrapValue`/`letterValue`, the L-valued factorization of every generator word (freeze v2 §4's
display `canonicalRes(τ) = η^m·∏ β_a^{t_a}`, OM-8 §3.1 L2's multiplicative extension), and the
defect-corrected τ reduction.  The values are exports of carried data, not constructions; the
bridge to the node-point residue classes is C.130g's OPEN transcription, not claimed here. -/

namespace SplitNodePointSource

variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- The canonical read of the wrap generator `W₀` — freeze v2 §4's η-value, exported. -/
def wrapValue (S : SplitNodePointSource (L := L) W E receiver K) {i : ℕ} (hi : StageLive r i) : Lˣ :=
  S.canonicalRead i (W.wrapClass hi)

/-- Anti-drift pin: the wrap value is the canonical read of the wrap class. -/
theorem wrapValue_def (S : SplitNodePointSource (L := L) W E receiver K) {i : ℕ}
    (hi : StageLive r i) : S.wrapValue hi = S.canonicalRead i (W.wrapClass hi) := rfl

/-- The canonical read of the letter generator `Λ_a` — freeze v2 §4's β-value, exported. -/
def letterValue (S : SplitNodePointSource (L := L) W E receiver K) (N : LaurentNormalizer W)
    {i : ℕ} (hi : StageLive r i) (a : Fin (i - 1)) : Lˣ :=
  S.canonicalRead i (N.letterClass hi a)

/-- Anti-drift pin: the letter value is the canonical read of the letter class. -/
theorem letterValue_def (S : SplitNodePointSource (L := L) W E receiver K) (N : LaurentNormalizer W)
    {i : ℕ} (hi : StageLive r i) (a : Fin (i - 1)) :
    S.letterValue N hi a = S.canonicalRead i (N.letterClass hi a) := rfl

/-- ★ **The distinguished-generator view on level kernels** (freeze v2 §4's L-valued
factorization display, OM-8 §3.1 L2): the canonical read of any generator word is the
corresponding word in the generator values, `η^m · ∏_a β_a^{t_a}` in `Lˣ`. -/
theorem canonicalRead_generatorWord (S : SplitNodePointSource (L := L) W E receiver K)
    (N : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i) (m : ℤ) (t : Fin (i - 1) → ℤ) :
    S.canonicalRead i (N.generatorWord hi m t) =
      S.wrapValue hi ^ m * ∏ a, S.letterValue N hi a ^ t a := by
  rw [LaurentNormalizer.generatorWord, map_mul, map_zpow, map_prod]
  simp only [map_zpow]
  rfl

/-- The defect-corrected τ reduction under the canonical read: the read of a product class is
the product of the reads times the read of the normalizer defect. -/
theorem canonicalRead_heightClass_mul (S : SplitNodePointSource (L := L) W E receiver K)
    (N : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i)
    {g g' : LevelExponentLattice i} {k k' : ℤ}
    (hg : levelExponentHeight W i g = Multiplicative.ofAdd k)
    (hg' : levelExponentHeight W i g' = Multiplicative.ofAdd k')
    (hgg' : levelExponentHeight W i (g * g') = Multiplicative.ofAdd (k + k')) :
    S.canonicalRead i (N.heightClass hi (g * g') (k + k') hgg') =
      S.canonicalRead i (N.heightClass hi g k hg) *
        S.canonicalRead i (N.heightClass hi g' k' hg') *
        S.canonicalRead i (N.defect hi k k') := by
  rw [N.heightClass_mul hi hg hg' hgg', map_mul, map_mul]

end SplitNodePointSource

/-! ## 5. The synchronized-product export

Freeze v2 §4's extension clause: the canonical read on the synchronized product kernel at a
live level `j` reads the `j`-factor through `canonicalRead j` and sends the other level
factors to `1` — here the extension is the restriction along the level projection, and the
other-factors-to-1 clause is a theorem.  The `ULift` export (`canonicalRes`) is the
`Type uG` form required by finding #28 (C130f's `GaugeLattice`). -/

/-- Projection of the synchronized kernel at a live level into that level's kernel. -/
def kerLevelProj0 (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight0 T j) →* MonoidHom.ker (levelExponentHeight T j.1) where
  toFun τ := ⟨(τ : GaugeLattice0 r) j, by
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp τ.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Anti-drift pin: the kernel projection is the level-`j` component, nothing else. -/
theorem kerLevelProj0_coe (T : DeepTower F H₀ hpin r) (j : LiveLevel r)
    (τ : MonoidHom.ker (levelHeight0 T j)) :
    (kerLevelProj0 T j τ : LevelExponentLattice j.1) = (τ : GaugeLattice0 r) j := rfl

/-- A level-kernel element inserted at its level (`1` at every other live level) lies in the
synchronized kernel of EVERY live level: at `j` by kernel membership, elsewhere trivially. -/
theorem mulSingle_mem_ker_levelHeight0 (T : DeepTower F H₀ hpin r) (j j' : LiveLevel r)
    (g : MonoidHom.ker (levelExponentHeight T j.1)) :
    Pi.mulSingle j (g : LevelExponentLattice j.1) ∈ MonoidHom.ker (levelHeight0 T j') := by
  rw [MonoidHom.mem_ker]
  show levelExponentHeight T j'.1
    ((Pi.mulSingle j (g : LevelExponentLattice j.1) : GaugeLattice0 r) j') = 1
  rcases eq_or_ne j' j with rfl | hne
  · rw [Pi.mulSingle_eq_same]
    exact MonoidHom.mem_ker.mp g.2
  · rw [Pi.mulSingle_eq_of_ne hne, map_one]

/-- Insertion of a level-kernel element into the synchronized kernel: `g` at level `j` and
`1` at every other live level (freeze v2 §4's "other level factors to `1`" direction). -/
def kerLevelInsert0 (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    MonoidHom.ker (levelExponentHeight T j.1) →* MonoidHom.ker (levelHeight0 T j) where
  toFun g := ⟨Pi.mulSingle j (g : LevelExponentLattice j.1),
    mulSingle_mem_ker_levelHeight0 T j j g⟩
  map_one' := by
    apply Subtype.ext
    exact Pi.mulSingle_one j
  map_mul' g g' := by
    apply Subtype.ext
    exact Pi.mulSingle_mul (f := fun j' : LiveLevel r => LevelExponentLattice j'.1) j
      (g : LevelExponentLattice j.1) (g' : LevelExponentLattice j.1)

/-- Anti-drift pin: the insertion is `Pi.mulSingle`, nothing else. -/
theorem kerLevelInsert0_coe (T : DeepTower F H₀ hpin r) (j : LiveLevel r)
    (g : MonoidHom.ker (levelExponentHeight T j.1)) :
    (kerLevelInsert0 T j g : GaugeLattice0 r) =
      Pi.mulSingle j (g : LevelExponentLattice j.1) := rfl

/-- Projection after insertion is the identity on the level kernel. -/
theorem kerLevelProj0_kerLevelInsert0 (T : DeepTower F H₀ hpin r) (j : LiveLevel r)
    (g : MonoidHom.ker (levelExponentHeight T j.1)) :
    kerLevelProj0 T j (kerLevelInsert0 T j g) = g := by
  apply Subtype.ext
  rw [kerLevelProj0_coe, kerLevelInsert0_coe]
  exact Pi.mulSingle_eq_same (M := fun j' : LiveLevel r => LevelExponentLattice j'.1) j
    (g : LevelExponentLattice j.1)

/-- The synchronized kernels of the concrete and the `ULift`ed lattice are multiplicatively
equivalent, through C130f's explicit `gaugeLatticeEquiv` (finding #28's export). -/
def kerGaugeEquiv (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight T j : GaugeLattice.{uG} r →* Multiplicative ℤ) ≃*
      MonoidHom.ker (levelHeight0 T j) where
  toFun τ := ⟨gaugeLatticeEquiv r (τ : GaugeLattice.{uG} r), by
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp τ.2⟩
  invFun τ := ⟨(gaugeLatticeEquiv r : GaugeLattice.{uG} r ≃* GaugeLattice0 r).symm
      (τ : GaugeLattice0 r), by
    rw [MonoidHom.mem_ker]
    show levelHeight0 T j
      ((gaugeLatticeEquiv r : GaugeLattice.{uG} r ≃* GaugeLattice0 r)
        ((gaugeLatticeEquiv r : GaugeLattice.{uG} r ≃* GaugeLattice0 r).symm
          (τ : GaugeLattice0 r))) = 1
    rw [MulEquiv.apply_symm_apply]
    exact MonoidHom.mem_ker.mp τ.2⟩
  left_inv τ := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv τ := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  map_mul' τ σ := Subtype.ext
    (map_mul (gaugeLatticeEquiv r : GaugeLattice.{uG} r ≃* GaugeLattice0 r) _ _)

namespace SplitNodePointSource

variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- ★ **The C.130h export, concrete form**: the canonical L-valued read on the synchronized
product kernel at a live level — `canonicalRead j` at the level factor; the other level
factors are provably sent to `1` (`canonicalRes0_eq_one_of_level_one`).  L-valued; no
`Kt`-descent field exists (freeze v2 D-TIF-5). -/
def canonicalRes0 (S : SplitNodePointSource (L := L) W E receiver K) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight0 W j) →* Lˣ :=
  (S.canonicalRead j.1).comp (kerLevelProj0 W j)

/-- Anti-drift pin: the synchronized read is the level read of the level factor. -/
theorem canonicalRes0_apply (S : SplitNodePointSource (L := L) W E receiver K) (j : LiveLevel r)
    (τ : MonoidHom.ker (levelHeight0 W j)) :
    S.canonicalRes0 j τ = S.canonicalRead j.1 (kerLevelProj0 W j τ) := rfl

/-- Freeze v2 §4's "other level factors to `1`", as a theorem: any synchronized kernel
element whose level-`j` factor is trivial reads to `1`. -/
theorem canonicalRes0_eq_one_of_level_one (S : SplitNodePointSource (L := L) W E receiver K)
    (j : LiveLevel r) (τ : MonoidHom.ker (levelHeight0 W j))
    (h : (τ : GaugeLattice0 r) j = 1) : S.canonicalRes0 j τ = 1 := by
  have hproj : kerLevelProj0 W j τ = 1 := Subtype.ext h
  rw [canonicalRes0_apply, hproj, map_one]

/-- The synchronized read of an inserted level-kernel element is its level read. -/
theorem canonicalRes0_kerLevelInsert0 (S : SplitNodePointSource (L := L) W E receiver K)
    (j : LiveLevel r) (g : MonoidHom.ker (levelExponentHeight W j.1)) :
    S.canonicalRes0 j (kerLevelInsert0 W j g) = S.canonicalRead j.1 g := by
  rw [canonicalRes0_apply, kerLevelProj0_kerLevelInsert0]

/-- At a DIFFERENT live level `j' ≠ j`, the synchronized read of the `j`-inserted element is
`1` — the other-factors-to-`1` clause across levels. -/
theorem canonicalRes0_insert_ne (S : SplitNodePointSource (L := L) W E receiver K)
    {j j' : LiveLevel r} (hne : j' ≠ j)
    (g : MonoidHom.ker (levelExponentHeight W j.1)) :
    S.canonicalRes0 j'
      ⟨Pi.mulSingle j (g : LevelExponentLattice j.1),
        mulSingle_mem_ker_levelHeight0 W j j' g⟩ = 1 :=
  S.canonicalRes0_eq_one_of_level_one j' _ (by
    show (Pi.mulSingle j (g : LevelExponentLattice j.1) : GaugeLattice0 r) j' = 1
    exact Pi.mulSingle_eq_of_ne (M := fun j'' : LiveLevel r => LevelExponentLattice j''.1)
      hne (g : LevelExponentLattice j.1))

/-- ★ **The C.130h export, `ULift` form** (finding #28): the canonical L-valued read on the
`Type uG` synchronized kernel, through the explicit `gaugeLatticeEquiv`. -/
def canonicalRes (S : SplitNodePointSource (L := L) W E receiver K) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight W j : GaugeLattice.{uG} r →* Multiplicative ℤ) →* Lˣ :=
  (S.canonicalRes0 j).comp (kerGaugeEquiv W j).toMonoidHom

/-- Anti-drift pin: the `ULift` read factors through the kernel equivalence. -/
theorem canonicalRes_apply (S : SplitNodePointSource (L := L) W E receiver K) (j : LiveLevel r)
    (τ : MonoidHom.ker (levelHeight W j : GaugeLattice.{uG} r →* Multiplicative ℤ)) :
    S.canonicalRes j τ = S.canonicalRes0 j (kerGaugeEquiv W j τ) := rfl

/-- Round trip: the `ULift` read of a lifted concrete kernel element is its concrete read. -/
theorem canonicalRes_symm_apply (S : SplitNodePointSource (L := L) W E receiver K) (j : LiveLevel r)
    (τ : MonoidHom.ker (levelHeight0 W j)) :
    S.canonicalRes j
        (((kerGaugeEquiv W j).symm τ :
          MonoidHom.ker (levelHeight W j : GaugeLattice.{uG} r →* Multiplicative ℤ))) =
      S.canonicalRes0 j τ := by
  rw [canonicalRes_apply, MulEquiv.apply_symm_apply]

end SplitNodePointSource

/-! ## 6. The distinguished generators on the synchronized product

The generator classes inserted at a live level, and their reads — the distinguished-generator
views of the exported synchronized read. -/

/-- The wrap generator `W₀`, inserted at live level `j` of the synchronized kernel. -/
def DeepTower.wrapClassSync (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight0 T j) :=
  kerLevelInsert0 T j (T.wrapClass j.2.stageLive)

/-- The letter generator `Λ_a`, inserted at live level `j` of the synchronized kernel. -/
def LaurentNormalizer.letterClassSync {W : DeepTower.{0, uKt} F H₀ hpin r}
    (N : LaurentNormalizer W) (j : LiveLevel r) (a : Fin (j.1 - 1)) :
    MonoidHom.ker (levelHeight0 W j) :=
  kerLevelInsert0 W j (N.letterClass j.2.stageLive a)

namespace SplitNodePointSource

variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- Distinguished-generator view, synchronized: the read of the inserted `W₀` is η. -/
theorem canonicalRes0_wrapClassSync (S : SplitNodePointSource (L := L) W E receiver K)
    (j : LiveLevel r) :
    S.canonicalRes0 j (W.wrapClassSync j) = S.wrapValue j.2.stageLive :=
  S.canonicalRes0_kerLevelInsert0 j _

/-- Distinguished-generator view, synchronized: the read of the inserted `Λ_a` is `β_a`. -/
theorem canonicalRes0_letterClassSync (S : SplitNodePointSource (L := L) W E receiver K)
    (N : LaurentNormalizer W) (j : LiveLevel r) (a : Fin (j.1 - 1)) :
    S.canonicalRes0 j (N.letterClassSync j a) = S.letterValue N j.2.stageLive a :=
  S.canonicalRes0_kerLevelInsert0 j _

/-- ★ **The distinguished-generator view on the synchronized product**: the synchronized read
of any inserted generator word is the word in the generator values, `η^m · ∏_a β_a^{t_a}`. -/
theorem canonicalRes0_generatorWordSync (S : SplitNodePointSource (L := L) W E receiver K)
    (N : LaurentNormalizer W) (j : LiveLevel r) (m : ℤ) (t : Fin (j.1 - 1) → ℤ) :
    S.canonicalRes0 j (kerLevelInsert0 W j (N.generatorWord j.2.stageLive m t)) =
      S.wrapValue j.2.stageLive ^ m *
        ∏ a, S.letterValue N j.2.stageLive a ^ t a := by
  rw [S.canonicalRes0_kerLevelInsert0 j, S.canonicalRead_generatorWord N j.2.stageLive m t]

end SplitNodePointSource

end Uniformity.Density.Tower

/-! ## Teeth — the S2 depth-two specialization (elaboration and value regressions)

D62w's depth-two lattice objects, recovered from the GENERAL constructions at the landed CC-2
occurrence (`s2DepthTwo`, chain `e = (2,2)`, `u = (1,5)`): the wrap generator is `d2g1`'s
exponent word, the general letter class evaluates to `d2g2 = Φ₁²·(π²x)⁻¹`, and the read views
specialize with no type/universe/index obstruction.  Statements about ANY carrier instance;
nothing here inhabits `NodePointSource` (the S2 point instance is CC-17's). -/

section Teeth

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {Kt : Type} [Field Kt] {E : Type} [Field E] {L : Type} [Field L] [Algebra Kt L]
variable (R : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 (s2DepthTwo h2 hq) Kt)
variable (S : SplitNodePointSource (L := L) (s2DepthTwo h2 hq) E R (s2DepthTwoKeyChain h2 hq))

-- D62w regression `d2g1`: the wrap generator at the S2 chain is `x²·π⁻¹` at both live levels
example : (s2DepthTwo h2 hq).wrapGen 1 = Multiplicative.ofAdd ((-1 : ℤ), (2 : ℤ), 0) := rfl
example :
    (s2DepthTwo h2 hq).wrapGen 2 =
      Multiplicative.ofAdd ((-1 : ℤ), (2 : ℤ), fun _ => (0 : ℤ)) := rfl

-- the word half of the `d2g2` regression: the S2 normalizer word at height 10 is `π²x`
-- (exponents `(2, 1, 0)`), computed through CC-4's rung recursion
example : (s2DepthTwo h2 hq).laurentSolve 1 10 = (2, 1, fun _ => 0) := by
  have hu : (s2DepthTwo h2 hq).u (0 + 2) = 5 := rfl
  have he : (s2DepthTwo h2 hq).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu, he, hh, he1]
  decide

-- D62w regression `d2g2`, assembled: the GENERAL letter class at S2 level 2 evaluates to
-- the numeric kernel word `Φ₁²·(π²x)⁻¹ = (−2, −1, 2)` (height `2·((4/4)·5) = 10`)
example :
    (((s2DepthTwo h2 hq).laurentNormalizer.letterClass
        (⟨by omega, by omega⟩ : StageLive 2 2) (⟨0, by omega⟩ : Fin (2 - 1)) :
      LevelExponentLattice 2)) =
      Multiplicative.ofAdd ((-2 : ℤ), (-1 : ℤ), fun _ => (2 : ℤ)) := by
  have hsolve : (s2DepthTwo h2 hq).laurentSolve 1 10 = (2, 1, fun _ => 0) := by
    have hu : (s2DepthTwo h2 hq).u (0 + 2) = 5 := rfl
    have he : (s2DepthTwo h2 hq).e (0 + 2) = 2 := rfl
    have hh : (s2Frame h2 hq).h = 1 := rfl
    have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
    simp only [DeepTower.laurentSolve, KeyFrame.slotIdx_eq_towerSolve, hu, he, hh, he1]
    decide
  have hnorm : (s2DepthTwo h2 hq).laurentNormalizer.norm = (s2DepthTwo h2 hq).laurentNormAt :=
    rfl
  rw [LaurentNormalizer.letterClass_coe, hnorm]
  norm_num [show (s2DepthTwo h2 hq).e 2 = 2 from rfl,
    show (s2DepthTwo h2 hq).ehat 2 = 4 from rfl, show (s2DepthTwo h2 hq).u 2 = 5 from rfl,
    DeepTower.laurentNormAt, hsolve]
  decide

-- the level-kernel generator view specializes at the S2 occurrence (level 1: no letters)
example (m : ℤ) (t : Fin 0 → ℤ) :
    S.canonicalRead 1
        ((s2DepthTwo h2 hq).laurentNormalizer.generatorWord
          (⟨le_rfl, by omega⟩ : StageLive 2 1) m t) =
      S.wrapValue (⟨le_rfl, by omega⟩ : StageLive 2 1) ^ m := by
  rw [SplitNodePointSource.canonicalRead_generatorWord]
  simp

-- the synchronized export and its wrap view specialize at the unique S2 live level
example (j : LiveLevel 2) :
    S.canonicalRes0 j ((s2DepthTwo h2 hq).wrapClassSync j) = S.wrapValue j.2.stageLive :=
  S.canonicalRes0_wrapClassSync j

end Teeth

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.levelExponentHeight_ofAdd
#print axioms Uniformity.Density.Tower.piLetter
#print axioms Uniformity.Density.Tower.xLetter
#print axioms Uniformity.Density.Tower.keyLetter
#print axioms Uniformity.Density.Tower.piLetter_height
#print axioms Uniformity.Density.Tower.xLetter_height
#print axioms Uniformity.Density.Tower.keyLetter_height
#print axioms Uniformity.Density.Tower.levelExponentHeight_mul_ofAdd
#print axioms Uniformity.Density.Tower.LaurentNormalizer.mul_norm_inv_mem_ker
#print axioms Uniformity.Density.Tower.LaurentNormalizer.heightClass
#print axioms Uniformity.Density.Tower.LaurentNormalizer.heightClass_coe
#print axioms Uniformity.Density.Tower.LaurentNormalizer.heightClass_norm
#print axioms Uniformity.Density.Tower.LaurentNormalizer.defect
#print axioms Uniformity.Density.Tower.LaurentNormalizer.defect_coe
#print axioms Uniformity.Density.Tower.LaurentNormalizer.heightClass_mul
#print axioms Uniformity.Density.Tower.DeepTower.wrapGen
#print axioms Uniformity.Density.Tower.DeepTower.wrapGen_mem_ker
#print axioms Uniformity.Density.Tower.DeepTower.wrapClass
#print axioms Uniformity.Density.Tower.DeepTower.wrapClass_coe
#print axioms Uniformity.Density.Tower.LaurentNormalizer.letterClass
#print axioms Uniformity.Density.Tower.LaurentNormalizer.letterClass_coe
#print axioms Uniformity.Density.Tower.LaurentNormalizer.generatorWord
#print axioms Uniformity.Density.Tower.LaurentNormalizer.generatorWord_def
#print axioms Uniformity.Density.Tower.SplitNodePointSource.wrapValue
#print axioms Uniformity.Density.Tower.SplitNodePointSource.wrapValue_def
#print axioms Uniformity.Density.Tower.SplitNodePointSource.letterValue
#print axioms Uniformity.Density.Tower.SplitNodePointSource.letterValue_def
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRead_generatorWord
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRead_heightClass_mul
#print axioms Uniformity.Density.Tower.kerLevelProj0
#print axioms Uniformity.Density.Tower.kerLevelProj0_coe
#print axioms Uniformity.Density.Tower.mulSingle_mem_ker_levelHeight0
#print axioms Uniformity.Density.Tower.kerLevelInsert0
#print axioms Uniformity.Density.Tower.kerLevelInsert0_coe
#print axioms Uniformity.Density.Tower.kerLevelProj0_kerLevelInsert0
#print axioms Uniformity.Density.Tower.kerGaugeEquiv
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_apply
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_eq_one_of_level_one
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_kerLevelInsert0
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_insert_ne
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes_apply
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes_symm_apply
#print axioms Uniformity.Density.Tower.DeepTower.wrapClassSync
#print axioms Uniformity.Density.Tower.LaurentNormalizer.letterClassSync
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_wrapClassSync
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_letterClassSync
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalRes0_generatorWordSync

end AxCheck
