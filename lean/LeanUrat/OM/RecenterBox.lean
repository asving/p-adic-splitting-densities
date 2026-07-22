/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.CellCard
import LeanUrat.OM.HenselCount
import LeanUrat.OM.RestartEquiv

/-!
# RecenterBox — Wave W5a: the box-level recenter–rescale staircase bijection at `n = 2`

**Provenance.** `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §2-W5a, ground truth
`notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` **Lemma 2.3** (recenter–rescale bijection,
whole-window linear case; ACCEPTED at pass 6), specialized to `s = n = 2` (all of `n = 2` is
whole-window). The classifier-side reading of the recentered run (lift invariance, boundary #5)
is W5c's business; this module is the PURE COUNTING content: exact bijections and cardinalities
over `ZMod (p^N)`, no axioms.

## The mathematics being formalized (note's numbering)

For a monic quadratic window `f = x² + a₁x + a₀` over `ℤ/p^N`, slope `m ≥ 1`, and a recentering
residue `c̃ ∈ F_p^×` with lift `ĉ`:

* **(S1)** (side on/above slope `−m`): `v(a₀) ≥ 2m`, `v(a₁) ≥ m`;
* **(S2)** (residual double root at `c̃`, note (2.3b) at `s = 2`): writing `ã₀ = a₀/p^{2m}`,
  `ã₁ = a₁/p^m`, the digit conditions `ã₀ ≡ c̃² (mod p)` and `ã₁ ≡ −2c̃ (mod p)`.
  These force `v(a₀) = 2m` EXACT (`c̃² ≠ 0`); at `p = 2` the second condition degenerates to
  `ã₁ ≡ 0`, i.e. `v(a₁) ≥ m + 1` — the note's `p = 2` ledger form ("v(a₀)=2m exact,
  v(a₁) ≥ m+1"). No case split is needed in Lean: the displayed conditions are uniform in `p`.
* **(2.3a) at `s = 2`** (the coefficient identity, monic window so `t_k = 0`): the child
  `g(y) = f(ĉp^m + p^m y)/p^{2m}` has
  `b₁ = ã₁ + 2ĉ` (read mod `p^{M₁}`, `M₁ = N − m`) and
  `b₀ = ã₀ + ĉã₁ + ĉ²` (read mod `p^{M₀}`, `M₀ = N − 2m`) —
  an affine unipotent triangular map on the STAIRCASE box `ℤ/p^{M₀} × ℤ/p^{M₁}`.
* **(2)+(3)**: `f ↦ g` restricted to (S1)∧(S2) is a bijection onto the CHILD STAIRCASE CLUSTER
  BOX `{(b₀, b₁) : b̄₀ = b̄₁ = 0}` (`recenterEquiv` below); (S1) alone bijects onto the FREE
  staircase box (`sideEquiv` below, the note's step (2)).
* **(2.3c) at `s = 2`**: stratum mass `p^{−s − m·s(s+1)/2} = p^{−2−3m}` per `(m, c̃)` relative
  to the full box `p^{2N}`.

## Normalization ledger (Case-A cross-checks, note §7; p = 2 values)

Full-box count of the depth-1 stratum: `p^{2N−3m−2}` (`card_descendStratum`), i.e. mass
`p^{−(3m+2)}`; summed over the `p−1` values of `c̃`: `(p−1)·p^{−(3m+2)}`. Relative to the
CLUSTER box (`p^{2N−2}` polynomials, the §7 ledger's conditional frame) this is the ledger's
`(p−1)·p^{−3m}` — at `p = 2, m = 1`: `1/8` of the cluster box (§7 Case A "descend: 1/8"),
`1/32` of the full box. Depth-2 all-descend prefix (chain `(m₁, m₂)`): full-box mass
`p^{−2−3(m₁+m₂)}` (`card_chain2`) — at `p = 2, m = (1,1)`: `2^{−8}`, the note's verified
depth-2 gate value ("census mod 2^{10}").

**Statement-fidelity note (vs the W5a task card).** The task card stated
`card_descendStratum = p^(2N−3m)` with the equiv landing in the FREE staircase box. That
cardinality belongs to the (S1)-only side stratum (`card_sideStratum`); the full (S1)∧(S2)
stratum has the additional `p^{−s} = p^{−2}` cluster-digit factor, exactly per the note's
(2.3c) and its depth-2 gate `2^{−8} = 2^{−2}·2^{−3}·2^{−3}`. Both bijections are provided;
the frozen semantic content (stratum ≃ staircase box with matching cardinalities) is
`recenterEquiv` + `card_descendStratum` in the note's normalization.

Discipline: no `sorry`, no new axioms; core-only footprint.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RecenterBox

open Polynomial
open LeanUrat.OM LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RestartEquiv

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ## 1. The staircase box (blueprint deliverable 1)

`stairBox p N m` is the child's digit frame at the staircase levels `M₀ = N − 2m` (the
`a₀`/constant slot) and `M₁ = N − m` (the `a₁`/linear slot); the leading coefficient of the
monic degree-2 child is implicit. -/

/-- **The staircase box** at level `N`, slope `m` (`n = 2`): the `b₀`-slot at level `N − 2m`,
the `b₁`-slot at level `N − m`. -/
abbrev stairBox (N m : ℕ) : Type := ZMod (p ^ (N - 2 * m)) × ZMod (p ^ (N - m))

/-- `#stairBox = p^{2N−3m}` (for `2m ≤ N`; ℕ-subtraction honesty). -/
theorem card_stairBox (N m : ℕ) (h : 2 * m ≤ N) :
    Nat.card (stairBox p N m) = p ^ (2 * N - 3 * m) := by
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, ← pow_add]
  congr 1
  omega

/-! ## 2. The digit-shift workhorse

`{x : ZMod (p^L) // p^k ∣ x.val} ≃ ZMod (p^{L−k})` by `x ↦ x.val / p^k` — the note's step-(2)
digit shift `a_i = p^{m(s−i)}·ã_i` in `ZMod`-native form. -/

/-- **Digit shift**: division by `p^k` is a bijection from the `p^k`-divisible elements at level
`L` onto level `L − k`. -/
def shiftEquiv {L k : ℕ} (hk : k ≤ L) :
    {x : ZMod (p ^ L) // p ^ k ∣ x.val} ≃ ZMod (p ^ (L - k)) where
  toFun x := ((x.1.val / p ^ k : ℕ) : ZMod (p ^ (L - k)))
  invFun u :=
    haveI : NeZero (p ^ L) := QuotientBox.instNeZeroPow p L
    haveI : NeZero (p ^ (L - k)) := QuotientBox.instNeZeroPow p (L - k)
    ⟨((p ^ k * u.val : ℕ) : ZMod (p ^ L)), by
      rw [ZMod.val_natCast]
      have hlt : p ^ k * u.val < p ^ L := by
        calc p ^ k * u.val < p ^ k * p ^ (L - k) :=
              mul_lt_mul_of_pos_left (ZMod.val_lt u) (pow_pos hp.out.pos k)
          _ = p ^ L := by rw [← pow_add]; congr 1; omega
      rw [Nat.mod_eq_of_lt hlt]
      exact dvd_mul_right _ _⟩
  left_inv x := by
    haveI : NeZero (p ^ L) := QuotientBox.instNeZeroPow p L
    haveI : NeZero (p ^ (L - k)) := QuotientBox.instNeZeroPow p (L - k)
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    dsimp only
    have hdivlt : x.val / p ^ k < p ^ (L - k) := by
      apply Nat.div_lt_of_lt_mul
      calc x.val < p ^ L := ZMod.val_lt x
        _ = p ^ k * p ^ (L - k) := by rw [← pow_add]; congr 1; omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdivlt, Nat.mul_div_cancel' hx]
    exact ZMod.natCast_rightInverse x
  right_inv u := by
    haveI : NeZero (p ^ L) := QuotientBox.instNeZeroPow p L
    haveI : NeZero (p ^ (L - k)) := QuotientBox.instNeZeroPow p (L - k)
    dsimp only
    have hlt : p ^ k * u.val < p ^ L := by
      calc p ^ k * u.val < p ^ k * p ^ (L - k) :=
            mul_lt_mul_of_pos_left (ZMod.val_lt u) (pow_pos hp.out.pos k)
        _ = p ^ L := by rw [← pow_add]; congr 1; omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
      Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k)]
    exact ZMod.natCast_rightInverse u

/-! ## 3. Coordinate conditions (the note's (S1)+(S2), per window coordinate) -/

/-- **One-coordinate stratum condition** at level `L`, height `k`, prescribed digit `d`:
`p^k ∣ x` (the (S1) side condition) and the level-`k` digit equals `d` (the (S2) residual
digit; `CellCard.digit p L k x = (x.val / p^k : ZMod p)`). For `d ≠ 0` this forces
`v(x) = k` exact. -/
def CoordCond (L k : ℕ) (d : ZMod p) (x : ZMod (p ^ L)) : Prop :=
  p ^ k ∣ x.val ∧ digit p L k x = d

instance (L k : ℕ) (d : ZMod p) : DecidablePred (CoordCond p L k d) := fun _ => by
  unfold CoordCond; infer_instance

/-- The mod-`p` residue of the shifted element is the height-`k` digit of the original:
`resp (x/p^k) = digit k x` on the `p^k`-divisible locus. -/
theorem resp_shiftEquiv {L k : ℕ} (hk : k ≤ L) (x : {x : ZMod (p ^ L) // p ^ k ∣ x.val}) :
    resp p (L - k) (shiftEquiv p hk x) = digit p L k x.1 := by
  haveI : NeZero (p ^ L) := QuotientBox.instNeZeroPow p L
  haveI : NeZero (p ^ (L - k)) := QuotientBox.instNeZeroPow p (L - k)
  show resp p (L - k) ((x.1.val / p ^ k : ℕ) : ZMod (p ^ (L - k))) = digit p L k x.1
  have hdivlt : x.1.val / p ^ k < p ^ (L - k) := by
    apply Nat.div_lt_of_lt_mul
    calc x.1.val < p ^ L := ZMod.val_lt x.1
      _ = p ^ k * p ^ (L - k) := by rw [← pow_add]; congr 1; omega
  show ((((x.1.val / p ^ k : ℕ) : ZMod (p ^ (L - k))).val : ℕ) : ZMod p)
      = ((x.1.val / p ^ k : ℕ) : ZMod p)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdivlt]

/-- The digit shift carries the digit condition to a `resp` (mod-`p` residue) condition at the
lower level. -/
def coordEquiv {L k : ℕ} (hk : k ≤ L) (d : ZMod p) :
    {x : ZMod (p ^ L) // CoordCond p L k d x} ≃
      {u : ZMod (p ^ (L - k)) // resp p (L - k) u = d} :=
  ((Equiv.subtypeSubtypeEquivSubtypeInter (fun x : ZMod (p ^ L) => p ^ k ∣ x.val)
      (fun x => digit p L k x = d)).symm).trans
    (Equiv.subtypeEquiv (shiftEquiv p hk) (fun x => by rw [resp_shiftEquiv p hk x]))

/-! ## 4. The pair level: stratum, cluster, the affine unipotent map (2.3a) -/

/-- **The `n = 2` descend-stratum condition on a coefficient pair** `(a₀, a₁)` in a (staircase)
frame with levels `(L₀, L₁)`, slope `m`, recentering digit `c`: the note's (S1)∧(S2) at `s = 2`
— `v(a₀) ≥ 2m` with digit `c̃²` at height `2m`, and `v(a₁) ≥ m` with digit `−2c̃` at height `m`.
(At `p = 2`: `−2c̃ = 0`, so the `a₁` leg degenerates to `v(a₁) ≥ m + 1` — the ledger's form.) -/
def StratumPair (L₀ L₁ m : ℕ) (c : (ZMod p)ˣ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) : Prop :=
  CoordCond p L₀ (2 * m) (((c : ZMod p)) ^ 2) a.1 ∧
    CoordCond p L₁ m (-(2 * (c : ZMod p))) a.2

instance (L₀ L₁ m : ℕ) (c : (ZMod p)ˣ) : DecidablePred (StratumPair p L₀ L₁ m c) := fun _ => by
  unfold StratumPair; infer_instance

/-- **The child cluster condition** on a staircase pair: both coordinates `≡ 0 (mod p)` — the
note's step-(3) conclusion `b̄_k = 0` for `k < s`. -/
def ClusterPair (M₀ M₁ : ℕ) (b : ZMod (p ^ M₀) × ZMod (p ^ M₁)) : Prop :=
  p ∣ b.1.val ∧ p ∣ b.2.val

instance (M₀ M₁ : ℕ) : DecidablePred (ClusterPair p M₀ M₁) := fun _ => by
  unfold ClusterPair; infer_instance

/-- **The coefficient identity (2.3a) at `s = 2` as an affine unipotent equivalence** of the
staircase box (levels `M₀ ≤ M₁`), with recentering lift `ĉ : ℕ`:
`(ã₀, ã₁) ↦ (b₀, b₁) = (ã₀ + ĉã₁ + ĉ², ã₁ + 2ĉ)` — `b₁ = (a₁ + 2ĉp^m)/p^m`,
`b₀ = f(ĉp^m)/p^{2m}` in digit form. Triangular: the `b₀`-slot reads `ã₁` through the level
drop `M₁ → M₀` (`ZMod.castHom`). -/
def affineEquiv (M₀ M₁ : ℕ) (hM : M₀ ≤ M₁) (ĉ : ℕ) :
    ZMod (p ^ M₀) × ZMod (p ^ M₁) ≃ ZMod (p ^ M₀) × ZMod (p ^ M₁) where
  toFun x := (x.1 + (ĉ : ZMod (p ^ M₀)) * (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ M₀)) x.2)
      + (ĉ : ZMod (p ^ M₀)) ^ 2,
    x.2 + 2 * (ĉ : ZMod (p ^ M₁)))
  invFun y := (y.1 - (ĉ : ZMod (p ^ M₀)) * (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ M₀)) y.2)
      + (ĉ : ZMod (p ^ M₀)) ^ 2,
    y.2 - 2 * (ĉ : ZMod (p ^ M₁)))
  left_inv x := by
    obtain ⟨x₀, x₁⟩ := x
    dsimp only
    refine Prod.ext ?_ ?_
    · dsimp only
      simp only [map_add, map_mul, map_natCast, map_ofNat]
      ring
    · dsimp only
      ring
  right_inv y := by
    obtain ⟨y₀, y₁⟩ := y
    dsimp only
    refine Prod.ext ?_ ?_
    · dsimp only
      simp only [map_sub, map_mul, map_natCast, map_ofNat]
      ring
    · dsimp only
      ring

/-- `resp` intertwines the level drop: `resp (castHom x) = resp x` (for `0 < M₀`). -/
theorem resp_castHom {M₀ M₁ : ℕ} (hM₀ : 0 < M₀) (hM : M₀ ≤ M₁) (x : ZMod (p ^ M₁)) :
    resp p M₀ (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ M₀)) x) = resp p M₁ x := by
  haveI : NeZero (p ^ M₁) := QuotientBox.instNeZeroPow p M₁
  rw [ZMod.castHom_apply, ← ZMod.natCast_val x, resp_natCast p M₀ hM₀]
  rfl

/-- Vanishing of `resp` is `p ∣ val`. -/
theorem resp_eq_zero_iff_dvd_val {M : ℕ} (x : ZMod (p ^ M)) :
    resp p M x = 0 ↔ p ∣ x.val := by
  show ((x.val : ℕ) : ZMod p) = 0 ↔ p ∣ x.val
  exact CharP.cast_eq_zero_iff (ZMod p) p x.val

/-- **The residual identity (note step (3)) in digit form**: on the staircase box, the parent's
(S2) digit values `(c̃², −2c̃)` correspond under the affine map (2.3a) EXACTLY to the child
cluster condition `b̄₀ = b̄₁ = 0` — "the stratum's residual condition IS the child cluster
condition; no digit is left over and none is missing". Uniform in `p`, including the `p = 2`
degeneracy (`−2c̃ = 0` there). -/
theorem affine_cond_iff (M₀ M₁ : ℕ) (hM₀ : 0 < M₀) (hM : M₀ ≤ M₁) (c : (ZMod p)ˣ)
    (x : ZMod (p ^ M₀) × ZMod (p ^ M₁)) :
    (resp p M₀ x.1 = ((c : ZMod p)) ^ 2 ∧ resp p M₁ x.2 = -(2 * (c : ZMod p))) ↔
      (ClusterPair p M₀ M₁ (affineEquiv p M₀ M₁ hM ((c : ZMod p)).val x)) := by
  have hM₁ : 0 < M₁ := lt_of_lt_of_le hM₀ hM
  set cres : ZMod p := (c : ZMod p) with hcdef
  have hcv : ((cres.val : ℕ) : ZMod p) = cres := ZMod.natCast_rightInverse cres
  have himg : affineEquiv p M₀ M₁ hM cres.val x =
      (x.1 + (cres.val : ZMod (p ^ M₀)) * (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ M₀)) x.2)
        + (cres.val : ZMod (p ^ M₀)) ^ 2, x.2 + 2 * (cres.val : ZMod (p ^ M₁))) := rfl
  have hprod : (2 : ZMod (p ^ M₁)) * ((cres.val : ℕ) : ZMod (p ^ M₁))
      = ((2 * cres.val : ℕ) : ZMod (p ^ M₁)) := by push_cast; ring
  have h1 : resp p M₀ ((affineEquiv p M₀ M₁ hM cres.val x).1)
      = resp p M₀ x.1 + cres * resp p M₁ x.2 + cres ^ 2 := by
    rw [himg]
    dsimp only
    rw [resp_add p M₀ hM₀, resp_add p M₀ hM₀, resp_mul p M₀ hM₀, resp_pow p M₀ hM₀,
      resp_natCast p M₀ hM₀, hcv, resp_castHom p hM₀ hM]
  have h2 : resp p M₁ ((affineEquiv p M₀ M₁ hM cres.val x).2)
      = resp p M₁ x.2 + 2 * cres := by
    rw [himg]
    dsimp only
    rw [resp_add p M₁ hM₁, hprod, resp_natCast p M₁ hM₁, Nat.cast_mul, Nat.cast_ofNat, hcv]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · rw [← resp_eq_zero_iff_dvd_val, h1, ha, hb]; ring
    · rw [← resp_eq_zero_iff_dvd_val, h2, hb]; ring
  · rintro ⟨ha, hb⟩
    rw [← resp_eq_zero_iff_dvd_val, h1] at ha
    rw [← resp_eq_zero_iff_dvd_val, h2] at hb
    have hb' : resp p M₁ x.2 = -(2 * cres) := by linear_combination hb
    exact ⟨by linear_combination ha - cres * hb', hb'⟩

/-- **The pair-level recenter–rescale bijection** (note Lemma 2.3(2)+(3) at `s = 2`, one step,
general staircase frame `L₀ ≤ L₁`): the stratum at slope `m` and digit `c` bijects onto the
child staircase cluster box at levels `(L₀ − 2m, L₁ − m)`. -/
def stratumPairEquiv (L₀ L₁ m : ℕ) (c : (ZMod p)ˣ) (h₀ : 2 * m + 1 ≤ L₀) (h01 : L₀ ≤ L₁) :
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StratumPair p L₀ L₁ m c a} ≃
      {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
        ClusterPair p (L₀ - 2 * m) (L₁ - m) b} :=
  (Equiv.subtypeProdEquivProd).trans <|
    (Equiv.prodCongr (coordEquiv p (by omega : 2 * m ≤ L₀) (((c : ZMod p)) ^ 2))
        (coordEquiv p (by omega : m ≤ L₁) (-(2 * (c : ZMod p))))).trans <|
      (Equiv.subtypeProdEquivProd).symm.trans
        (Equiv.subtypeEquiv
          (affineEquiv p (L₀ - 2 * m) (L₁ - m) (by omega) ((c : ZMod p)).val)
          (fun u => affine_cond_iff p (L₀ - 2 * m) (L₁ - m) (by omega) (by omega) c u))

/-- Cardinality of the staircase cluster box: `p^{M₀+M₁−2}`. -/
theorem card_clusterPair (M₀ M₁ : ℕ) (hM₀ : 1 ≤ M₀) (hM₁ : 1 ≤ M₁) :
    Nat.card {b : ZMod (p ^ M₀) × ZMod (p ^ M₁) // ClusterPair p M₀ M₁ b}
      = p ^ (M₀ + M₁ - 2) := by
  have e : {b : ZMod (p ^ M₀) × ZMod (p ^ M₁) // ClusterPair p M₀ M₁ b}
      ≃ ZMod (p ^ (M₀ - 1)) × ZMod (p ^ (M₁ - 1)) :=
    (Equiv.subtypeEquivRight (fun b => by
        show ClusterPair p M₀ M₁ b ↔ (p ^ 1 ∣ b.1.val ∧ p ^ 1 ∣ b.2.val)
        rw [pow_one]
        exact Iff.rfl)).trans <|
      (Equiv.subtypeProdEquivProd).trans
        (Equiv.prodCongr (shiftEquiv p hM₀) (shiftEquiv p hM₁))
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod, Nat.card_zmod, ← pow_add]
  congr 1
  omega

/-! ## 5. The `monicBox` layer (blueprint deliverables 2–3) -/

/-- Coefficients of a linear perturbation vanish from degree 2 on. -/
private theorem lin_coeff_top {R : Type*} [Semiring R] (a b : R) {i : ℕ} (hi : 2 ≤ i) :
    (C a + C b * X).coeff i = 0 := by
  simp [coeff_C, coeff_X, show i ≠ 0 by omega, show ¬(1 = i) by omega]

/-- Monic-quadratic reconstruction: a monic `natDegree = 2` polynomial is
`X² + (C a₀ + C a₁ X)` on its low coefficients. -/
private theorem eq_quad {R : Type*} [Semiring R] {A : R[X]} (hA : A.Monic)
    (hdeg : A.natDegree = 2) :
    A = X ^ 2 + (C (A.coeff 0) + C (A.coeff 1) * X) := by
  ext i
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i
    · simp [coeff_X_pow, coeff_C]
    · simp [coeff_X_pow, coeff_C]
    · have h2 : A.coeff 2 = 1 := by
        have hlead := hA.coeff_natDegree
        rwa [hdeg] at hlead
      rw [h2]
      simp [coeff_X_pow]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)]
    symm
    simp [coeff_X_pow, coeff_C, coeff_X, show i ≠ 2 by omega, show i ≠ 0 by omega,
      show ¬(1 = i) by omega]

/-- The monic quadratic box is coefficient pairs: `f ↦ (a₀, a₁) = (f.coeff 0, f.coeff 1)`. -/
def coeffEquiv (N : ℕ) (hN : 0 < N) :
    monicBox p N 2 ≃ ZMod (p ^ N) × ZMod (p ^ N) :=
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  { toFun := fun f => (f.1.coeff 0, f.1.coeff 1)
    invFun := fun a =>
      ⟨X ^ 2 + (C a.1 + C a.2 * X),
        (HenselCount.monic_add_of_coeff (monic_X_pow 2) (natDegree_X_pow 2)
          (fun _ hi => lin_coeff_top a.1 a.2 hi)).1,
        (HenselCount.monic_add_of_coeff (monic_X_pow 2) (natDegree_X_pow 2)
          (fun _ hi => lin_coeff_top a.1 a.2 hi)).2⟩
    left_inv := fun f => Subtype.ext (eq_quad f.2.1 f.2.2).symm
    right_inv := fun a => by
      refine Prod.ext ?_ ?_ <;> dsimp only <;> simp [coeff_X_pow, coeff_C, coeff_X] }

/-- **The parent descend-stratum predicate** (blueprint deliverable 2) at level `N`, slope `m`,
recentering digit `c ∈ (ZMod p)ˣ`, on the monic quadratic box: the note's (2.3b) digit
conditions at `s = 2` read on the coefficient pair — `v(a₀) ≥ 2m` with height-`2m` digit `c̃²`
(hence `v(a₀) = 2m` exact), `v(a₁) ≥ m` with height-`m` digit `−2c̃` (at `p = 2` this is
`v(a₁) ≥ m + 1`). Decidable. -/
def DescendStratum (N m : ℕ) (c : (ZMod p)ˣ) (f : monicBox p N 2) : Prop :=
  StratumPair p N N m c (f.1.coeff 0, f.1.coeff 1)

instance (N m : ℕ) (c : (ZMod p)ˣ) : DecidablePred (DescendStratum p N m c) := fun _ => by
  unfold DescendStratum; infer_instance

/-- Spelled-out form of the stratum conditions, for audit: divisibilities and digit reads. -/
theorem descendStratum_iff (N m : ℕ) (c : (ZMod p)ˣ) (f : monicBox p N 2) :
    DescendStratum p N m c f ↔
      (p ^ (2 * m) ∣ (f.1.coeff 0).val ∧ digit p N (2 * m) (f.1.coeff 0) = ((c : ZMod p)) ^ 2)
      ∧ (p ^ m ∣ (f.1.coeff 1).val ∧ digit p N m (f.1.coeff 1) = -(2 * (c : ZMod p))) :=
  Iff.rfl

/-- **The (S1)-only side stratum** (side on/above slope `−m`, no residual pinning) — the note's
step-(2) domain. -/
def SideStratum (N m : ℕ) (f : monicBox p N 2) : Prop :=
  p ^ (2 * m) ∣ (f.1.coeff 0).val ∧ p ^ m ∣ (f.1.coeff 1).val

instance (N m : ℕ) : DecidablePred (SideStratum p N m) := fun _ => by
  unfold SideStratum; infer_instance

/-- **THE STAIRCASE BIJECTION (blueprint deliverable 3; note Lemma 2.3(2)+(3) at `s = n = 2`).**
The level-`N` descend stratum at slope `m`, digit `c` bijects onto the child staircase CLUSTER
box — the map is `f(x) ↦ g(y) = f(ĉp^m + p^m y)/p^{2m}` read at the staircase levels
`(N − 2m, N − m)` via the coefficient identity (2.3a); the inverse reconstructs
`(a₀, a₁) = (p^{2m}(b₀ − ĉb₁ + ĉ²), p^m(b₁ − 2ĉ))`. -/
def recenterEquiv (N m : ℕ) (c : (ZMod p)ˣ) (h : 2 * m + 1 ≤ N) :
    {f : monicBox p N 2 // DescendStratum p N m c f} ≃
      {b : stairBox p N m // ClusterPair p (N - 2 * m) (N - m) b} :=
  (Equiv.subtypeEquiv (coeffEquiv p N (by omega)) (fun f => Iff.rfl)).trans
    (stratumPairEquiv p N N m c h le_rfl)

/-- **The free-staircase bijection for the (S1) side stratum** (note step (2) alone): card
`p^{2N−3m}` — the task card's stated cardinality lives here. -/
def sideEquiv (N m : ℕ) (h : 2 * m ≤ N) (hN : 0 < N) :
    {f : monicBox p N 2 // SideStratum p N m f} ≃ stairBox p N m :=
  (Equiv.subtypeEquiv (coeffEquiv p N hN) (fun f => Iff.rfl)).trans <|
    (Equiv.subtypeProdEquivProd).trans
      (Equiv.prodCongr (shiftEquiv p (by omega : 2 * m ≤ N)) (shiftEquiv p (by omega : m ≤ N)))

/-! ## 6. Counts and masses (blueprint deliverable 4; note (2.3c) at `s = 2`) -/

/-- `#(S1) = p^{2N−3m}`. -/
theorem card_sideStratum (N m : ℕ) (h : 2 * m ≤ N) (hN : 0 < N) :
    Nat.card {f : monicBox p N 2 // SideStratum p N m f} = p ^ (2 * N - 3 * m) := by
  rw [Nat.card_congr (sideEquiv p N m h hN)]
  exact card_stairBox p N m h

/-- **The stratum count (note (2.3c) at `s = 2`)**: `#(S1∧S2) = p^{2N−3m−2}` per `(m, c̃)` —
the free staircase `p^{2N−3m}` times the `p^{−2}` cluster-digit factor. -/
theorem card_descendStratum (N m : ℕ) (c : (ZMod p)ˣ) (h : 2 * m + 1 ≤ N) :
    Nat.card {f : monicBox p N 2 // DescendStratum p N m c f}
      = p ^ (2 * N - 3 * m - 2) := by
  rw [Nat.card_congr (recenterEquiv p N m c h),
    card_clusterPair p (N - 2 * m) (N - m) (by omega) (by omega)]
  congr 1
  omega

/-- The task card's `p^{2N−3m}` form, with the cluster factor made explicit:
`#stratum · p² = p^{2N−3m}`. -/
theorem card_descendStratum_mul (N m : ℕ) (c : (ZMod p)ˣ) (h : 2 * m + 1 ≤ N) :
    Nat.card {f : monicBox p N 2 // DescendStratum p N m c f} * p ^ 2
      = p ^ (2 * N - 3 * m) := by
  rw [card_descendStratum p N m c h, ← pow_add]
  congr 1
  omega

/-- **Mass form (full box)**: `μ(stratum) = p^{−(3m+2)}` per `(m, c̃)` — the note's (2.3c)
`p^{−s−m·s(s+1)/2}` at `s = 2`. At `p = 2, m = 1`: `1/32` of the full box. -/
theorem mass_descendStratum (N m : ℕ) (c : (ZMod p)ˣ) (h : 2 * m + 1 ≤ N) :
    (Nat.card {f : monicBox p N 2 // DescendStratum p N m c f} : ℚ) / (p : ℚ) ^ (2 * N)
      = ((p : ℚ) ^ (3 * m + 2))⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [card_descendStratum p N m c h, div_eq_iff (pow_ne_zero _ hp0), inv_mul_eq_div,
    eq_div_iff (pow_ne_zero _ hp0)]
  push_cast
  rw [← pow_add]
  congr 1
  omega

/-- **Mass form (cluster-conditional — the §7 Case-A ledger normalization)**: relative to the
cluster box `p^{2N−2}`, the stratum has mass `p^{−3m}` per `c̃`. At `p = 2, m = 1`: `1/8` of
the cluster box — the ledger's depth-1 descend value. -/
theorem massCond_descendStratum (N m : ℕ) (c : (ZMod p)ˣ) (h : 2 * m + 1 ≤ N) :
    (Nat.card {f : monicBox p N 2 // DescendStratum p N m c f} : ℚ) / (p : ℚ) ^ (2 * N - 2)
      = ((p : ℚ) ^ (3 * m))⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [card_descendStratum p N m c h, div_eq_iff (pow_ne_zero _ hp0), inv_mul_eq_div,
    eq_div_iff (pow_ne_zero _ hp0)]
  push_cast
  rw [← pow_add]
  congr 1
  omega

/-- **Summed over the `p − 1` recentering digits** (full-box form):
`Σ_c μ = (p−1)·p^{−(3m+2)}`; cluster-conditionally this is the ledger's `(p−1)·p^{−3m}`
(at `p = 2, m = 1`: `1/8` of the cluster box). -/
theorem massSum_descendStratum (N m : ℕ) (h : 2 * m + 1 ≤ N) :
    ∑ c : (ZMod p)ˣ,
        ((Nat.card {f : monicBox p N 2 // DescendStratum p N m c f} : ℚ) / (p : ℚ) ^ (2 * N))
      = ((p : ℚ) - 1) * ((p : ℚ) ^ (3 * m + 2))⁻¹ := by
  rw [Finset.sum_congr rfl (fun c _ => mass_descendStratum p N m c h), Finset.sum_const,
    Finset.card_univ, ZMod.card_units p, nsmul_eq_mul]
  congr 1
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]

/-! ## 7. Chain composition (blueprint deliverable 5; note Lemma 2.3(5) at depth 2)

The child frame `(N − 2m₁, N − m₁)` is a staircase frame of the same form, so
`stratumPairEquiv` iterates: the second step's (S1) at slope `m₂ ≥ 1` SUBSUMES the cluster
condition the first step delivered (`2m₂ ≥ 1` and `m₂ ≥ 1` digits of divisibility include the
first `p`-digit), which is the note's "the `s` cluster digits are priced ONCE per chain". -/

/-- Step-2 conditions subsume the step-1 cluster condition (`m ≥ 1`). -/
theorem clusterPair_of_stratumPair (M₀ M₁ m : ℕ) (hm : 1 ≤ m) (c : (ZMod p)ˣ)
    (b : ZMod (p ^ M₀) × ZMod (p ^ M₁)) (hb : StratumPair p M₀ M₁ m c b) :
    ClusterPair p M₀ M₁ b := by
  obtain ⟨⟨hd0, -⟩, ⟨hd1, -⟩⟩ := hb
  exact ⟨(dvd_pow_self p (by omega : 2 * m ≠ 0)).trans hd0,
    (dvd_pow_self p (by omega : m ≠ 0)).trans hd1⟩

/-- **The depth-2 composite bijection** (chain `(m₁, c₁), (m₂, c₂)`, all-descend prefix): the
set of `f` in the depth-1 stratum whose child lands in the depth-2 stratum bijects onto the
depth-2 staircase cluster box at levels `(N − 2m₁ − 2m₂, N − m₁ − m₂)`. -/
def chain2Equiv (N m₁ m₂ : ℕ) (c₁ c₂ : (ZMod p)ˣ) (h₁ : 2 * m₁ + 1 ≤ N)
    (h₂ : 2 * m₂ + 1 ≤ N - 2 * m₁) (hm₂ : 1 ≤ m₂) :
    {x : {f : monicBox p N 2 // DescendStratum p N m₁ c₁ f} //
        StratumPair p (N - 2 * m₁) (N - m₁) m₂ c₂ ((recenterEquiv p N m₁ c₁ h₁ x) : stairBox p N m₁)} ≃
      {b : ZMod (p ^ (N - 2 * m₁ - 2 * m₂)) × ZMod (p ^ (N - m₁ - m₂)) //
        ClusterPair p (N - 2 * m₁ - 2 * m₂) (N - m₁ - m₂) b} :=
  (Equiv.subtypeEquiv (recenterEquiv p N m₁ c₁ h₁) (fun x => Iff.rfl)).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun b : stairBox p N m₁ => ClusterPair p (N - 2 * m₁) (N - m₁) b)
      (fun b => StratumPair p (N - 2 * m₁) (N - m₁) m₂ c₂ b)).trans <|
      (Equiv.subtypeEquivRight (fun b =>
        ⟨fun hb => hb.2,
         fun hb => ⟨clusterPair_of_stratumPair p (N - 2 * m₁) (N - m₁) m₂ hm₂ c₂ b hb, hb⟩⟩)).trans
        (stratumPairEquiv p (N - 2 * m₁) (N - m₁) m₂ c₂ h₂ (by omega))

/-- **The depth-2 chain count** (note Lemma 2.3(5), `s = 2`, depth 2): `p^{2N−3(m₁+m₂)−2}` —
frame mass `p^{−2}·p^{−3m₁}·p^{−3m₂}`, the cluster digits priced once. At
`p = 2, m = (1,1)`: full-box mass `2^{−8}`, the note's verified depth-2 gate. -/
theorem card_chain2 (N m₁ m₂ : ℕ) (c₁ c₂ : (ZMod p)ˣ) (h₁ : 2 * m₁ + 1 ≤ N)
    (h₂ : 2 * m₂ + 1 ≤ N - 2 * m₁) (hm₂ : 1 ≤ m₂) :
    Nat.card {x : {f : monicBox p N 2 // DescendStratum p N m₁ c₁ f} //
        StratumPair p (N - 2 * m₁) (N - m₁) m₂ c₂ ((recenterEquiv p N m₁ c₁ h₁ x) : stairBox p N m₁)}
      = p ^ (2 * N - 3 * (m₁ + m₂) - 2) := by
  rw [Nat.card_congr (chain2Equiv p N m₁ m₂ c₁ c₂ h₁ h₂ hm₂),
    card_clusterPair p (N - 2 * m₁ - 2 * m₂) (N - m₁ - m₂) (by omega) (by omega)]
  congr 1
  omega

/-- **Depth-2 mass, full box**: `p^{−(3(m₁+m₂)+2)}`; at `p = 2, m = (1,1)` this is `2^{−8}`
(the note's depth-2 census gate), and summed over `(c₁, c₂)` it is the cluster-conditional
`(p−1)²·p^{−3(m₁+m₂)}` of the task card. -/
theorem mass_chain2 (N m₁ m₂ : ℕ) (c₁ c₂ : (ZMod p)ˣ) (h₁ : 2 * m₁ + 1 ≤ N)
    (h₂ : 2 * m₂ + 1 ≤ N - 2 * m₁) (hm₂ : 1 ≤ m₂) :
    (Nat.card {x : {f : monicBox p N 2 // DescendStratum p N m₁ c₁ f} //
        StratumPair p (N - 2 * m₁) (N - m₁) m₂ c₂ ((recenterEquiv p N m₁ c₁ h₁ x) : stairBox p N m₁)} : ℚ)
        / (p : ℚ) ^ (2 * N)
      = ((p : ℚ) ^ (3 * (m₁ + m₂) + 2))⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [card_chain2 p N m₁ m₂ c₁ c₂ h₁ h₂ hm₂, div_eq_iff (pow_ne_zero _ hp0), inv_mul_eq_div,
    eq_div_iff (pow_ne_zero _ hp0)]
  push_cast
  rw [← pow_add]
  congr 1
  omega

end

end LeanUrat.OM.RecenterBox
