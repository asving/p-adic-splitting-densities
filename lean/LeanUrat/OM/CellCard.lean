/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.Order0Count

/-!
# CellCard — Phase-B wave W4a/W4b: the cell partition and the per-cell fiber counts

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md`, W4 SPEC items W4a/W4b, consuming the
landed W2 module `CellMenu` (`cellMenu`/`InCell`/`cell_unique`/`cell_exists`), the R1 evaluator
`OMCountV2` (`mCell`/`choicePoly`), and the L3/β2 counting layer (`Order0Count`,
`necklaceQ_eq_card`). Ground truth: `/workspace-vast/asving/tmp/phaseb_w0/` (`SUMMARY.md`,
`cells_s{2,3,4}.tsv`).

**W4a (`cell_partition`).** The readable cluster box — `IsCluster` (`v_p(a_i) ≥ 1` for `i < s`,
the `cell_exists` hypothesis) and F1-readability `v_p(a₀) < N` — is partitioned by the `InCell`
fibers over `cellMenu s N`: disjointness is `cell_unique`, coverage is `cell_exists`, and every
fiber sits inside the readable box (`inCell_isReadable`). Card version `cell_partition`:
`#readable = Σ_{c ∈ cellMenu s N} #{f | InCell p f c}` (list-map sum; the menu is nodup).
Sanity closed forms: `card_clusterBox : #cluster = p^(s(N−1))` and
`card_readableBox : #readable = p^(s(N−1)) − p^((s−1)(N−1))`, gated at `p=2, N=3, s=2`: 16 / 12.

**W4b (`cell_card_raw`, the RAW closed form).** For menu data `(P, sh)`:

    #{f | InCell p f (mkCell s P sh)} = prodSC p sh · p ^ freeExp s N P

with `prodSC p sh = Π_side #{monic M, X ∤ M, polyShape M = shape}` (the per-side residual-shape
count) and the EXPLICIT free exponent

    freeExp s N P = Σ_{i<s} (N − 1 − ceilAt P i)  +  Σ_{sides} (run − d_S)

(each of the `s` coefficients contributes its `p^(N−1−⌈h_i⌉)` deep digits — the F-B1 atom shape;
each side additionally frees its `run − d_S` off-pattern residue digits; the on-pattern residue
digits are jointly counted by the shape count, anchored at the monic leading coefficient — the
right-to-left telescope `card_peel`/`chain_count`).

**mCell tie (partial banking, sanctioned).** `mCell (mkCell s P sh) p = Π_side (choicePoly true
shape).eval p` (`mCell_mkCell`), and the per-shape tie `#SC(l) = (choicePoly true l).eval p` is
BANKED for the shapes `[(1,1)]`, `[(1,μ)]`, `[(2,1)]` (all `p`; via `Order0Count.necklaceQ_eq_card`)
and `[(1,1),(1,1)]` at `p = 2` — every shape occurring in the W0 gates. `cell_card_mCell` gives the
headline `#fiber = mCell c p · p^freeExp` form whenever the ties of the cell's shapes are supplied.
The fully general tie (arbitrary multiplicity multisets, the `ff/sym` multinomial) is left to the
follow-up wave; the RAW form above is complete.

**MANDATORY W0 GATES** (`SUMMARY.md` per-cell census, `p = 2, N = 3`), all proved from the closed
form: s=2: S2C1 ↦ 8, S2C2 ↦ 2, S2C3 ↦ 2, split cell ↦ 0 (readable-but-unhit at p=2);
s=3: S3C1 ↦ 32, S3C3 ↦ 8; s=4: S4C1 ↦ 128. Consistency corollary: Σ over `cellMenu 2 3` of the
per-cell counts = 12 = `#readable` (and 48 at s=3, 192 at s=4 from W4a + the box closed forms).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.CellCard

open LeanUrat LeanUrat.OM Polynomial
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig FaceAssign mCell choicePoly poolPoly)

/-! ## 1. Generic counting helpers -/

section Helpers

/-- Sigma over a finite index with constant fiber size. -/
theorem card_sigma_const {α : Type*} [Finite α] {F : α → Type*} [∀ a, Finite (F a)] {K : ℕ}
    (h : ∀ a, Nat.card (F a) = K) : Nat.card (Σ a, F a) = Nat.card α * K := by
  cases nonempty_fintype α
  rw [Nat.card_sigma]
  simp only [h, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card, Finset.card_univ]

/-- Membership-aware `Forall₂` implication. -/
theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a b, a ∈ l → b ∈ l' → R a b → S a b) → List.Forall₂ S l l' := by
  intro l l' h
  induction h with
  | nil => intro _; exact List.Forall₂.nil
  | @cons a b l l' ha ht ih =>
      intro himp
      exact List.Forall₂.cons (himp a b (by simp) (by simp) ha)
        (ih fun a' b' hal hbl hr =>
          himp a' b' (List.mem_cons_of_mem _ hal) (List.mem_cons_of_mem _ hbl) hr)

/-- Fibered counting over a finite product: if each `π i` has constant fiber size `k i`, the count
of tuples whose image satisfies `Cond` is (count of admissible images) × `∏ k i`. -/
theorem card_pi_fiber {ι : Type*} [Fintype ι] {A B : ι → Type*}
    [∀ i, Finite (A i)] [∀ i, Finite (B i)]
    (π : ∀ i, A i → B i) (k : ι → ℕ)
    (hk : ∀ (i : ι) (b : B i), Nat.card {a : A i // π i a = b} = k i)
    (Cond : (∀ i, B i) → Prop) :
    Nat.card {a : ∀ i, A i // Cond (fun i => π i (a i))}
      = Nat.card {b : ∀ i, B i // Cond b} * ∏ i, k i := by
  classical
  set F : {a : ∀ i, A i // Cond (fun i => π i (a i))} → {b : ∀ i, B i // Cond b} :=
    fun a => ⟨fun i => π i (a.1 i), a.2⟩ with hF
  have e2 : ∀ b : {b : ∀ i, B i // Cond b},
      {a : {a : ∀ i, A i // Cond (fun i => π i (a i))} // F a = b}
        ≃ ∀ i, {x : A i // π i x = b.1 i} := fun b =>
    { toFun := fun a i => ⟨a.1.1 i, congrFun (congrArg Subtype.val a.2) i⟩
      invFun := fun g => ⟨⟨fun i => (g i).1, by
          have hc : (fun i => π i ((g i).1)) = b.1 := funext fun i => (g i).2
          rw [hc]
          exact b.2⟩,
        Subtype.ext (funext fun i => (g i).2)⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => funext fun i => Subtype.ext rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F)]
  exact card_sigma_const fun b => by
    rw [Nat.card_congr (e2 b), Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => hk i (b.1 i)

/-- Count of functions supported inside a fixed finset. -/
theorem card_support_subset {ι M : Type*} [Fintype ι] [DecidableEq ι] [Finite M] [Zero M]
    (T : Finset ι) :
    Nat.card {f : ι → M // ∀ i ∉ T, f i = 0} = Nat.card M ^ T.card := by
  have e : {f : ι → M // ∀ i ∉ T, f i = 0} ≃ ({ i // i ∈ T } → M) :=
    { toFun := fun f i => f.1 i.1
      invFun := fun g => ⟨fun i => if h : i ∈ T then g ⟨i, h⟩ else 0, fun i hi => dif_neg hi⟩
      left_inv := fun f => Subtype.ext (funext fun i => by
        by_cases h : i ∈ T
        · simp [h]
        · simp [h, f.2 i h])
      right_inv := fun g => funext fun i => by simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Additive support splice: if `Cond` only reads the `S`-coordinates, functions supported on the
disjoint union `S ∪ T` satisfying `Cond` split as (supported on `S`, satisfying) × (free on `T`). -/
theorem card_supp_split {ι M : Type*} [Fintype ι] [DecidableEq ι] [Finite M] [AddCommMonoid M]
    (S T : Finset ι) (hdisj : Disjoint S T)
    (Cond : (ι → M) → Prop)
    (hCond : ∀ f g : ι → M, (∀ i ∈ S, f i = g i) → Cond f → Cond g) :
    Nat.card {f : ι → M // (∀ i ∉ S ∪ T, f i = 0) ∧ Cond f}
      = Nat.card {f : ι → M // (∀ i ∉ S, f i = 0) ∧ Cond f} * Nat.card M ^ T.card := by
  classical
  have e : {f : ι → M // (∀ i ∉ S ∪ T, f i = 0) ∧ Cond f}
      ≃ {f : ι → M // (∀ i ∉ S, f i = 0) ∧ Cond f} × {g : ι → M // ∀ i ∉ T, g i = 0} :=
    { toFun := fun f =>
        (⟨fun i => if i ∈ S then f.1 i else 0, ⟨fun i hi => if_neg hi, by
            refine hCond f.1 _ (fun i hi => (if_pos hi).symm) f.2.2⟩⟩,
         ⟨fun i => if i ∈ T then f.1 i else 0, fun i hi => if_neg hi⟩)
      invFun := fun z =>
        ⟨fun i => z.1.1 i + z.2.1 i, ⟨fun i hi => by
            rw [Finset.mem_union] at hi
            show z.1.1 i + z.2.1 i = 0
            rw [z.1.2.1 i (fun h => hi (Or.inl h)), z.2.2 i (fun h => hi (Or.inr h)),
              add_zero], by
          refine hCond z.1.1 _ (fun i hi => ?_) z.1.2.2
          show z.1.1 i = z.1.1 i + z.2.1 i
          rw [z.2.2 i (Finset.disjoint_left.mp hdisj hi), add_zero]⟩⟩
      left_inv := fun f => Subtype.ext (funext fun i => by
        by_cases hS : i ∈ S
        · have hT : i ∉ T := Finset.disjoint_left.mp hdisj hS
          simp [hS, hT]
        · by_cases hT : i ∈ T
          · simp [hS, hT]
          · have : i ∉ S ∪ T := by
              rw [Finset.mem_union]
              tauto
            simp [hS, hT, f.2.1 i this])
      right_inv := fun z => by
        refine Prod.ext (Subtype.ext (funext fun i => ?_)) (Subtype.ext (funext fun i => ?_))
        · by_cases hS : i ∈ S
          · have hT : i ∉ T := Finset.disjoint_left.mp hdisj hS
            simp [hS, z.2.2 i hT]
          · simp [hS, z.1.2.1 i hS]
        · by_cases hT : i ∈ T
          · have hS : i ∉ S := Finset.disjoint_right.mp hdisj hT
            simp [hT, z.1.2.1 i hS]
          · simp [hT, z.2.2 i hT] }
  rw [Nat.card_congr e, Nat.card_prod, card_support_subset]

/-- Partition of a subtype count by a further (classical) predicate. -/
theorem card_subtype_and_compl {α : Type*} [Finite α] (P Q : α → Prop) :
    Nat.card {x // P x ∧ Q x} + Nat.card {x // P x ∧ ¬Q x} = Nat.card {x // P x} := by
  classical
  rw [← Nat.card_sum]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => Sum.elim (fun y => ⟨y.1, y.2.1⟩) (fun y => ⟨y.1, y.2.1⟩) x
      invFun := fun x => if h : Q x.1 then Sum.inl ⟨x.1, x.2, h⟩ else Sum.inr ⟨x.1, x.2, h⟩
      left_inv := fun x => by
        rcases x with y | y
        · simp [y.2.2]
        · simp [y.2.2]
      right_inv := fun x => by
        by_cases h : Q x.1 <;> simp [h] }

/-- List-map sum over the `toFinset` of a nodup list. -/
theorem sum_toFinset_eq_map_sum {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (f : α → ℕ) : ∑ c ∈ l.toFinset, f c = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.nodup_cons] at hl
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hl.1), List.map_cons,
        List.sum_cons, ih hl.2]

end Helpers

/-! ## 2. `ZMod (p^N)` digit atoms -/

section Digit

variable (p : ℕ) [hp : Fact p.Prime]

instance instNeZeroP : NeZero p := ⟨hp.out.ne_zero⟩

/-- The level-`m` digit of `x : ZMod (p^N)`: `(x.val / p^m) mod p`. For `v_p(x) ≥ m` this is the
residue that the classifier's guarded read `boxCoeffData` sees (unit residue on exact valuation,
`0` above — `bcd_digit` below). -/
def digit (N m : ℕ) (x : ZMod (p ^ N)) : ZMod p := ((x.val / p ^ m : ℕ) : ZMod p)

theorem pow_dvd_val_iff {N m : ℕ} (hm : m ≤ N) (x : ZMod (p ^ N)) :
    p ^ m ∣ x.val ↔ m ≤ PadicLift.zmodValuation p N x := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  by_cases hx : x = 0
  · subst hx
    simp only [ZMod.val_zero, PadicLift.zmodValuation_zero]
    exact ⟨fun _ => hm, fun _ => dvd_zero _⟩
  · have hval : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
    rw [PadicLift.zmodValuation_of_ne_zero p hx]
    exact Nat.Prime.pow_dvd_iff_le_factorization hp.out hval

theorem digit_eq_zero_of_dvd {N m : ℕ} {x : ZMod (p ^ N)} (h : p ^ (m + 1) ∣ x.val) :
    digit p N m x = 0 := by
  obtain ⟨k, hk⟩ := h
  have hp0 : 0 < p ^ m := pow_pos hp.out.pos m
  have hdiv : x.val / p ^ m = p * k := by
    rw [hk, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ hp0]
  rw [digit, hdiv]
  push_cast
  simp

theorem unitResidue_eq_digit {N m : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0)
    (hv : PadicLift.zmodValuation p N x = m) :
    PadicLift.zmodUnitResidue p N x = digit p N m x := by
  rw [PadicLift.zmodUnitResidue, digit]
  congr 2
  rw [← hv, PadicLift.zmodValuation_of_ne_zero p hx]

theorem valuation_eq_iff_digit_ne {N m : ℕ} (hm : m < N) {x : ZMod (p ^ N)}
    (hdvd : p ^ m ∣ x.val) :
    PadicLift.zmodValuation p N x = m ↔ digit p N m x ≠ 0 := by
  constructor
  · intro hv
    have hx : x ≠ 0 := by
      rintro rfl
      rw [PadicLift.zmodValuation_zero] at hv
      omega
    rw [← unitResidue_eq_digit p hx hv]
    exact PadicLift.zmodUnitResidue_ne_zero p hx
  · intro hne
    by_contra hv
    apply hne
    apply digit_eq_zero_of_dvd
    have hge : m ≤ PadicLift.zmodValuation p N x := (pow_dvd_val_iff p hm.le x).mp hdvd
    have hgt : m + 1 ≤ PadicLift.zmodValuation p N x := by omega
    exact (pow_dvd_val_iff p (by omega) x).mpr hgt

/-- Divisibility-truncation equivalence: `{x : ZMod(p^N) | p^m ∣ x.val} ≃ ZMod (p^{N−m})`. -/
noncomputable def dvdEquiv {N m : ℕ} (hm : m ≤ N) :
    ZMod (p ^ (N - m)) ≃ {x : ZMod (p ^ N) // p ^ m ∣ x.val} := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  haveI : NeZero (p ^ (N - m)) := QuotientBox.instNeZeroPow p (N - m)
  have hlt : ∀ y : ZMod (p ^ (N - m)), p ^ m * y.val < p ^ N := by
    intro y
    calc p ^ m * y.val < p ^ m * p ^ (N - m) :=
          mul_lt_mul_of_pos_left (ZMod.val_lt y) (pow_pos hp.out.pos m)
      _ = p ^ N := by rw [← pow_add]; congr 1; omega
  exact
    { toFun := fun y => ⟨((p ^ m * y.val : ℕ) : ZMod (p ^ N)), by
        rw [ZMod.val_cast_of_lt (hlt y)]
        exact dvd_mul_right _ _⟩
      invFun := fun x => ((x.1.val / p ^ m : ℕ) : ZMod (p ^ (N - m)))
      left_inv := fun y => by
        show ((((p ^ m * y.val : ℕ) : ZMod (p ^ N)).val / p ^ m : ℕ) : ZMod (p ^ (N - m))) = y
        rw [ZMod.val_cast_of_lt (hlt y), Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)]
        exact ZMod.natCast_rightInverse y
      right_inv := fun x => by
        have hdivlt : x.1.val / p ^ m < p ^ (N - m) := by
          rw [Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos m)]
          calc x.1.val < p ^ N := ZMod.val_lt x.1
            _ = p ^ (N - m) * p ^ m := by rw [← pow_add]; congr 1; omega
        have hx : p ^ m * (x.1.val / p ^ m) = x.1.val := Nat.mul_div_cancel' x.2
        refine Subtype.ext ?_
        show (((p ^ m * ((x.1.val / p ^ m : ℕ) : ZMod (p ^ (N - m))).val : ℕ)) : ZMod (p ^ N))
          = x.1
        rw [ZMod.val_cast_of_lt hdivlt, hx]
        exact ZMod.natCast_rightInverse x.1 }

theorem digit_dvdEquiv {N m : ℕ} (hm : m ≤ N) (y : ZMod (p ^ (N - m))) :
    digit p N m (dvdEquiv p hm y).1 = ((y.val : ℕ) : ZMod p) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  haveI : NeZero (p ^ (N - m)) := QuotientBox.instNeZeroPow p (N - m)
  have hlt : p ^ m * y.val < p ^ N := by
    calc p ^ m * y.val < p ^ m * p ^ (N - m) :=
          mul_lt_mul_of_pos_left (ZMod.val_lt y) (pow_pos hp.out.pos m)
      _ = p ^ N := by rw [← pow_add]; congr 1; omega
  show ((((((p ^ m * y.val : ℕ) : ZMod (p ^ N))).val / p ^ m : ℕ)) : ZMod p) = _
  rw [ZMod.val_cast_of_lt hlt, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)]

theorem card_dvd_subtype {N m : ℕ} (hm : m ≤ N) :
    Nat.card {x : ZMod (p ^ N) // p ^ m ∣ x.val} = p ^ (N - m) := by
  rw [← Nat.card_congr (dvdEquiv p hm), Nat.card_zmod]

/-- Fibers of the mod-`p` digit read on `ZMod (p^a)`. -/
theorem card_val_cast_fiber {a : ℕ} (ha : 0 < a) (c : ZMod p) :
    Nat.card {y : ZMod (p ^ a) // ((y.val : ℕ) : ZMod p) = c} = p ^ (a - 1) := by
  haveI : NeZero (p ^ a) := QuotientBox.instNeZeroPow p a
  set y₀ : ZMod (p ^ a) := ((c.val : ℕ) : ZMod (p ^ a)) with hy₀
  have hcast : ∀ y : ZMod (p ^ a),
      ((y.val : ℕ) : ZMod p) = ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p) y := by
    intro y
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  have hy₀c : ((y₀.val : ℕ) : ZMod p) = c := by
    rw [hcast, hy₀, map_natCast]
    exact ZMod.natCast_rightInverse c
  have e1 : {y : ZMod (p ^ a) // ((y.val : ℕ) : ZMod p) = c}
      ≃ {y : ZMod (p ^ a) // ((y.val : ℕ) : ZMod p) = 0} :=
    { toFun := fun y => ⟨y.1 - y₀, by
        rw [hcast, map_sub, ← hcast, ← hcast, y.2, hy₀c, sub_self]⟩
      invFun := fun y => ⟨y.1 + y₀, by
        rw [hcast, map_add, ← hcast, ← hcast, y.2, hy₀c, zero_add]⟩
      left_inv := fun y => Subtype.ext (by ring)
      right_inv := fun y => Subtype.ext (by ring) }
  have e2 : {y : ZMod (p ^ a) // ((y.val : ℕ) : ZMod p) = 0}
      ≃ {y : ZMod (p ^ a) // p ^ 1 ∣ y.val} :=
    Equiv.subtypeEquivRight fun y => by
      rw [pow_one, CharP.cast_eq_zero_iff (ZMod p) p y.val]
  rw [Nat.card_congr e1, Nat.card_congr e2, card_dvd_subtype p ha]

/-- **The per-coordinate digit atom**: within `{v_p ≥ m}` each digit value has exactly
`p^(N−m−1)` preimages. -/
theorem card_digit_fiber {N m : ℕ} (hm : m < N) (c : ZMod p) :
    Nat.card {x : {x : ZMod (p ^ N) // p ^ m ∣ x.val} // digit p N m x.1 = c}
      = p ^ (N - m - 1) := by
  have e : {y : ZMod (p ^ (N - m)) // ((y.val : ℕ) : ZMod p) = c}
      ≃ {x : {x : ZMod (p ^ N) // p ^ m ∣ x.val} // digit p N m x.1 = c} :=
    (dvdEquiv p hm.le).subtypeEquiv fun y => by rw [digit_dvdEquiv p hm.le y]
  rw [← Nat.card_congr e, card_val_cast_fiber p (by omega) c]

/-- Mixed-exponent divisibility product count (the sanity-card engine). -/
theorem card_dvd_pi {s N : ℕ} (m : Fin s → ℕ) (hm : ∀ i, m i ≤ N) :
    Nat.card {a : Fin s → ZMod (p ^ N) // ∀ i, p ^ m i ∣ (a i).val}
      = p ^ (∑ i, (N - m i)) := by
  have e : {a : Fin s → ZMod (p ^ N) // ∀ i, p ^ m i ∣ (a i).val}
      ≃ ∀ i, {x : ZMod (p ^ N) // p ^ m i ∣ x.val} :=
    { toFun := fun a i => ⟨a.1 i, a.2 i⟩
      invFun := fun b => ⟨fun i => (b i).1, fun i => (b i).2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_congr rfl
    (fun i _ => card_dvd_subtype p (hm i)), Finset.prod_pow_eq_pow_sum]

end Digit

/-! ## 3. Side/ceiling geometry: the containing-side formula and the line comparison -/

section Geometry

/-- The per-column ceiling of a single side (matches the `ceilAt` middle branch verbatim). -/
def ceilSide (pr : (ℕ × ℕ) × (ℕ × ℕ)) (i : ℕ) : ℕ :=
  pr.1.2 - (pr.1.2 - pr.2.2) * (i - pr.1.1) / (pr.2.1 - pr.1.1)

/-- The lattice step of a side: `e = run / d_S`. -/
def sideE (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := (pr.2.1 - pr.1.1) / sideDeg pr

/-- The lattice drop of a side per step: `h₀ = drop / d_S`. -/
def sideH (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := (pr.1.2 - pr.2.2) / sideDeg pr

variable {pr : (ℕ × ℕ) × (ℕ × ℕ)}

theorem sideDeg_pos (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) : 0 < sideDeg pr :=
  Nat.gcd_pos_of_pos_left _ (by omega)

theorem sideDeg_mul_sideE (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    sideDeg pr * sideE pr = pr.2.1 - pr.1.1 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

theorem sideDeg_mul_sideH (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    sideDeg pr * sideH pr = pr.1.2 - pr.2.2 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

theorem sideE_pos (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) : 0 < sideE pr :=
  Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) (sideDeg_pos hw hh)

theorem sideH_pos (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) : 0 < sideH pr :=
  Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) (sideDeg_pos hw hh)

/-- `ceilSide` at a pattern position: exact lattice height `v₀ − t·h₀`. -/
theorem ceilSide_pattern (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) {t : ℕ}
    (ht : t ≤ sideDeg pr) :
    ceilSide pr (pr.1.1 + t * sideE pr) = pr.1.2 - t * sideH pr := by
  unfold ceilSide
  rw [show pr.1.1 + t * sideE pr - pr.1.1 = t * sideE pr from by omega]
  have h2 : (pr.1.2 - pr.2.2) * (t * sideE pr) = (t * sideH pr) * (pr.2.1 - pr.1.1) := by
    rw [← sideDeg_mul_sideH hw hh, ← sideDeg_mul_sideE hw hh]
    ring
  rw [h2, Nat.mul_div_cancel _ (by omega : 0 < pr.2.1 - pr.1.1)]

theorem ceilSide_left (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    ceilSide pr pr.1.1 = pr.1.2 := by
  have h := ceilSide_pattern hw hh (t := 0) (Nat.zero_le _)
  simpa using h

theorem ceilSide_right (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    ceilSide pr pr.2.1 = pr.2.2 := by
  have h := ceilSide_pattern hw hh (t := sideDeg pr) (le_refl _)
  rw [sideDeg_mul_sideE hw hh, sideDeg_mul_sideH hw hh] at h
  rwa [show pr.1.1 + (pr.2.1 - pr.1.1) = pr.2.1 from by omega,
    show pr.1.2 - (pr.1.2 - pr.2.2) = pr.2.2 from by omega] at h

/-- Strictly inside the window, `ceilSide` stays strictly above the right endpoint height. -/
theorem ceilSide_ge (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) {i : ℕ}
    (hi : i < pr.2.1) : pr.2.2 + 1 ≤ ceilSide pr i := by
  have hlt : (pr.1.2 - pr.2.2) * (i - pr.1.1) / (pr.2.1 - pr.1.1) < pr.1.2 - pr.2.2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < pr.2.1 - pr.1.1)]
    exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) (by omega) (by omega)
  unfold ceilSide
  omega

theorem ceilSide_le_left (pr : (ℕ × ℕ) × (ℕ × ℕ)) (i : ℕ) : ceilSide pr i ≤ pr.1.2 :=
  Nat.sub_le _ _

/-- **Line vs ceiling**: for an integer height `v`, lying on/above the rational side line is the
same as lying on/above the integer ceiling of the side. -/
theorem lineAt_le_iff_ceilSide_le (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2)
    {i v : ℕ} (h1 : pr.1.1 ≤ i) :
    lineAt pr (i : ℚ) ≤ (v : ℚ) ↔ ceilSide pr i ≤ v := by
  have hrunQ : (0 : ℚ) < ((pr.2.1 - pr.1.1 : ℕ) : ℚ) := by
    have : (0 : ℕ) < pr.2.1 - pr.1.1 := by omega
    exact_mod_cast this
  have hline : lineAt pr (i : ℚ)
      = (pr.1.2 : ℚ) - ((pr.1.2 - pr.2.2 : ℕ) : ℚ) * ((i - pr.1.1 : ℕ) : ℚ)
          / ((pr.2.1 - pr.1.1 : ℕ) : ℚ) := by
    unfold lineAt slopeQ
    rw [Nat.cast_sub hh.le, Nat.cast_sub hw.le, Nat.cast_sub h1]
    field_simp
    ring
  rw [hline]
  set aQ : ℚ := ((pr.1.2 - pr.2.2 : ℕ) : ℚ) * ((i - pr.1.1 : ℕ) : ℚ) with haQ
  have haQnn : 0 ≤ aQ / ((pr.2.1 - pr.1.1 : ℕ) : ℚ) := by
    apply div_nonneg _ hrunQ.le
    rw [haQ]
    positivity
  rcases le_or_gt pr.1.2 v with hcase | hcase
  · -- v ≥ v₀: both sides trivially true
    constructor
    · intro _
      calc ceilSide pr i ≤ pr.1.2 := ceilSide_le_left pr i
        _ ≤ v := hcase
    · intro _
      have : (pr.1.2 : ℚ) ≤ (v : ℚ) := by exact_mod_cast hcase
      linarith
  · -- v < v₀
    have hkey : ((pr.1.2 : ℚ) - v) ≤ aQ / ((pr.2.1 - pr.1.1 : ℕ) : ℚ)
        ↔ pr.1.2 - v ≤ (pr.1.2 - pr.2.2) * (i - pr.1.1) / (pr.2.1 - pr.1.1) := by
      rw [le_div_iff₀ hrunQ]
      constructor
      · intro h
        have h' : ((pr.1.2 - v : ℕ) : ℚ) * ((pr.2.1 - pr.1.1 : ℕ) : ℚ) ≤ aQ := by
          rw [Nat.cast_sub hcase.le]
          exact h
        rw [haQ] at h'
        have h'' : ((pr.1.2 - v) * (pr.2.1 - pr.1.1) : ℕ) ≤ ((pr.1.2 - pr.2.2) * (i - pr.1.1) : ℕ) := by
          exact_mod_cast h'
        exact (Nat.le_div_iff_mul_le (by omega : 0 < pr.2.1 - pr.1.1)).mpr h''
      · intro h
        have h'' := (Nat.le_div_iff_mul_le (by omega : 0 < pr.2.1 - pr.1.1)).mp h
        have h' : ((pr.1.2 - v) * (pr.2.1 - pr.1.1) : ℕ) ≤ ((pr.1.2 - pr.2.2) * (i - pr.1.1) : ℕ) := h''
        have hQ : ((pr.1.2 - v : ℕ) : ℚ) * ((pr.2.1 - pr.1.1 : ℕ) : ℚ) ≤ aQ := by
          rw [haQ]
          exact_mod_cast h'
        rw [Nat.cast_sub hcase.le] at hQ
        exact hQ
    constructor
    · intro h
      have h2 : ((pr.1.2 : ℚ) - v) ≤ aQ / ((pr.2.1 - pr.1.1 : ℕ) : ℚ) := by linarith
      have h3 := hkey.mp h2
      unfold ceilSide
      omega
    · intro h
      have h3 : pr.1.2 - v ≤ (pr.1.2 - pr.2.2) * (i - pr.1.1) / (pr.2.1 - pr.1.1) := by
        unfold ceilSide at h
        omega
      have h2 := hkey.mpr h3
      linarith

/-- **The containing-side value of `ceilAt`** along a chain: on the window of any side of the
path, `ceilAt` computes that side's own ceiling formula. -/
theorem chainOK_ceilAt_window {s : ℕ} :
    ∀ {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}, ChainOK s p0 p1 T → p0.1 < p1.1 → p1.2 < p0.2 →
      ∀ pr ∈ sidePairs (p0 :: p1 :: T), ∀ i, pr.1.1 ≤ i → i ≤ pr.2.1 →
        ceilAt (p0 :: p1 :: T) i = ceilSide pr i := by
  intro T
  induction T with
  | nil =>
      intro p0 p1 _ hw hh pr hpr i h1 h2
      have hpr' : pr = (p0, p1) := by
        simpa [sidePairs] using hpr
      subst hpr'
      have h1' : p0.1 ≤ i := h1
      have h2' : i ≤ p1.1 := h2
      simp only [ceilAt]
      by_cases hi0 : i ≤ p0.1
      · have hie : i = p0.1 := by omega
        rw [if_pos hi0, hie]
        show p0.2 = p0.2 - (p0.2 - p1.2) * (p0.1 - p0.1) / (p1.1 - p0.1)
        simp
      · rw [if_neg hi0, if_pos h2']
        rfl
  | cons p2 T' ih =>
      intro p0 p1 hc hw hh pr hpr i h1 h2
      cases hc with
      | cons h1' h2' h3' h4' =>
        rw [sidePairs_cons₂, List.mem_cons] at hpr
        rcases hpr with rfl | hpr'
        · -- pr = (p0, p1): the window never reaches the recursion branch
          have ha : p0.1 ≤ i := h1
          have hb : i ≤ p1.1 := h2
          simp only [ceilAt]
          by_cases hi0 : i ≤ p0.1
          · have hie : i = p0.1 := by omega
            rw [if_pos hi0, hie]
            show p0.2 = p0.2 - (p0.2 - p1.2) * (p0.1 - p0.1) / (p1.1 - p0.1)
            simp
          · rw [if_neg hi0, if_pos hb]
            rfl
        · -- pr is a later side: its window is right of p1
          have hfacts := chainOK_side_facts (ChainOK.cons h1' h2' h3' h4') pr hpr'
          obtain ⟨hwpr, hhpr, hm1, hm2⟩ := hfacts
          have hge : p1.1 ≤ pr.1.1 := by
            rcases List.mem_cons.mp hm1 with heq | hm1'
            · rw [heq]
            · exact (chainOK_mem_bounds (ChainOK.cons h1' h2' h3' h4') pr.1 hm1').1.le
          simp only [ceilAt]
          rw [if_neg (by omega)]
          by_cases hi1 : i ≤ p1.1
          · -- i = p1.1 = pr.1.1: shared vertex, both formulas give the vertex height
            have hie : i = p1.1 := by omega
            have hpre : pr.1.1 = p1.1 := by omega
            have hpr1 : pr.1 = p1 := by
              rcases List.mem_cons.mp hm1 with heq | hm1'
              · exact heq
              · exact absurd (chainOK_mem_bounds (ChainOK.cons h1' h2' h3' h4') pr.1 hm1').1
                  (by omega)
            rw [if_pos hi1]
            have hlhs : p0.2 - (p0.2 - p1.2) * (i - p0.1) / (p1.1 - p0.1) = p1.2 := by
              have hcs := ceilSide_right (pr := (p0, p1)) hw hh
              rw [hie]
              exact hcs
            rw [hlhs, hie, ← hpre]
            rw [show ceilSide pr pr.1.1 = pr.1.2 from ceilSide_left hwpr hhpr]
            rw [← hpr1]
          · rw [if_neg hi1]
            exact ih h4' h1' h2' pr hpr' i h1 h2

theorem menuPath_ceilAt_window {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hpr : pr ∈ sidePairs P) {i : ℕ}
    (h1 : pr.1.1 ≤ i) (h2 : i ≤ pr.2.1) : ceilAt P i = ceilSide pr i := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hP
  exact chainOK_ceilAt_window hc hp1 (by simpa using hpH) pr hpr i h1 h2

theorem menuPath_ceilAt_le {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {i : ℕ} (hi : i < s) : ceilAt P i ≤ N - 1 := by
  obtain ⟨pr, hpr, h1, h2⟩ := menuPath_containing hP hi.le
  rw [menuPath_ceilAt_window hP hpr h1 h2]
  calc ceilSide pr i ≤ pr.1.2 := ceilSide_le_left pr i
    _ ≤ N - 1 := menuPath_height_le hP pr.1 (menuPath_side_facts hP pr hpr).2.2.1

theorem menuPath_ceilAt_pos {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {i : ℕ} (hi : i < s) : 1 ≤ ceilAt P i := by
  obtain ⟨pr, hpr, h1, h2⟩ := menuPath_containing hP hi.le
  obtain ⟨hw, hh, hm1, hm2⟩ := menuPath_side_facts hP pr hpr
  rw [menuPath_ceilAt_window hP hpr h1 h2]
  rcases eq_or_lt_of_le h2 with heq | hlt
  · -- i = pr.2.1 < s: a vertex left of s has positive height
    rw [heq, ceilSide_right hw hh]
    have hpw := menuPath_pairwise hP
    have hlast := menuPath_last_mem hP
    rcases pairwise_mem_rel hpw hm2 hlast with heq2 | hrel | hrel
    · have : pr.2.1 = s := congrArg Prod.fst heq2
      omega
    · exact hrel.2
    · have := hrel.1
      have hle := menuPath_mem_le hP pr.2 hm2
      omega
  · have := ceilSide_ge hw hh hlt
    omega

end Geometry

/-! ## 4. The digit-level cell condition `DigCond` and the `Matches` transport -/

section Box

variable (p : ℕ) [hp : Fact p.Prime]

/-- Digit read with the monic cap: positions `≥ s` read the leading coefficient's digit `1`. -/
def rho {s : ℕ} (r : Fin s → ZMod p) (j : ℕ) : ZMod p :=
  if h : j < s then r ⟨j, h⟩ else 1

theorem rho_lt {s : ℕ} (r : Fin s → ZMod p) {j : ℕ} (h : j < s) : rho p r j = r ⟨j, h⟩ :=
  dif_pos h

theorem rho_ge {s : ℕ} (r : Fin s → ZMod p) {j : ℕ} (h : ¬ j < s) : rho p r j = 1 :=
  dif_neg h

theorem rho_eq_of_agree {s : ℕ} {r r' : Fin s → ZMod p} {j₁ : ℕ}
    (h : ∀ i : Fin s, j₁ ≤ i.1 → r i = r' i) {j : ℕ} (hj : j₁ ≤ j) :
    rho p r j = rho p r' j := by
  unfold rho
  split
  · exact h _ hj
  · rfl

/-- The digit-level residual polynomial of a side (all `d_S + 1` pattern reads, monic-capped). -/
noncomputable def sidePolyR {s : ℕ} (r : Fin s → ZMod p) (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    (ZMod p)[X] :=
  ∑ t ∈ Finset.range (sideDeg pr + 1), C (rho p r (pr.1.1 + t * sideE pr)) * X ^ t

theorem sidePolyR_coeff {s : ℕ} (r : Fin s → ZMod p) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) :
    (sidePolyR p r pr).coeff k
      = if k ≤ sideDeg pr then rho p r (pr.1.1 + k * sideE pr) else 0 := by
  unfold sidePolyR
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (sideDeg pr + 1)) k
    (fun t => rho p r (pr.1.1 + t * sideE pr))]
  simp only [Finset.mem_range]
  by_cases hk : k ≤ sideDeg pr
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

theorem sidePolyR_congr {s : ℕ} {r r' : Fin s → ZMod p} (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (h : ∀ j, pr.1.1 ≤ j → rho p r j = rho p r' j) :
    sidePolyR p r pr = sidePolyR p r' pr := by
  unfold sidePolyR
  exact Finset.sum_congr rfl fun t _ => by rw [h _ (Nat.le_add_right _ _)]

/-- The per-side digit condition: the residual read off the digits has the assigned shape and
the left-vertex digit is a unit. -/
def SideCond {s : ℕ} (r : Fin s → ZMod p) (l : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  polyShape p (sidePolyR p r pr) = (l : Multiset (ℕ × ℕ)) ∧ rho p r pr.1.1 ≠ 0

theorem sideCond_congr {s : ℕ} {r r' : Fin s → ZMod p} {l : List (ℕ × ℕ)}
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (h : ∀ j, pr.1.1 ≤ j → rho p r j = rho p r' j) :
    SideCond p r l pr ↔ SideCond p r' l pr := by
  unfold SideCond
  rw [sidePolyR_congr p pr h, h pr.1.1 (le_refl _)]

/-- **The digit-level cell condition**: one `SideCond` per side. -/
def DigCond {s : ℕ} (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) (r : Fin s → ZMod p) : Prop :=
  List.Forall₂ (fun l pr => SideCond p r l pr) sh (sidePairs P)

theorem vOf_eq (N s : ℕ) (f : QuotientBox.monicBox p N s) (i : ℕ) :
    vOf p f i = PadicLift.zmodValuation p N ((f.1).coeff i) := rfl

/-- The unit residue of the monic leading coefficient is `1`. -/
theorem unitResidue_one {N : ℕ} (hN : 0 < N) :
    PadicLift.zmodUnitResidue p N (1 : ZMod (p ^ N)) = 1 := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  unfold PadicLift.zmodUnitResidue
  rw [ZMod.val_one]
  simp

/-- **The residual read is the digit read** (D7 guard ⟹ digit): on a matched-side window with
the divisibility conditions in hand, the classifier residual `residualOf` equals the digit-level
`sidePolyR` of the ceiling digits. -/
theorem residualOf_eq_sidePolyR {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : MenuPath s N P) {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hpr : pr ∈ sidePairs P)
    (f : QuotientBox.monicBox p N s)
    (hdvd : ∀ i : Fin s, p ^ ceilAt P i.1 ∣ (((f.1).coeff i.1).val)) :
    residualOf p f pr
      = sidePolyR p (fun i : Fin s => digit p N (ceilAt P i.1) ((f.1).coeff i.1)) pr := by
  obtain ⟨hw, hh, hm1, hm2⟩ := menuPath_side_facts hP pr hpr
  obtain ⟨hE, hH, hD, hgeE, hghH, -, -⟩ := side_data hw hh
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  have hEe : (mkSide pr).e = sideE pr := hE
  have hHh : (mkSide pr).h = -((sideH pr : ℕ) : ℤ) := hH
  have hgeE' : sideDeg pr * sideE pr = pr.2.1 - pr.1.1 := hgeE
  have hghH' : sideDeg pr * sideH pr = pr.1.2 - pr.2.2 := hghH
  ext k
  rw [residualOf, M4.residualPoly_coeff, sidePolyR_coeff, hD]
  by_cases hk : k ≤ sideDeg pr
  · rw [if_pos hk, if_pos hk]
    set j := pr.1.1 + k * sideE pr with hjdef
    have hidx : (mkSide pr).i₀ + k * (mkSide pr).e = j := by
      show pr.1.1 + k * (mkSide pr).e = j
      rw [hEe]
    have hjle : j ≤ pr.2.1 := by
      have h1 : k * sideE pr ≤ sideDeg pr * sideE pr := Nat.mul_le_mul_right _ hk
      omega
    have hkH : k * sideH pr ≤ pr.1.2 := by
      have h1 : k * sideH pr ≤ sideDeg pr * sideH pr := Nat.mul_le_mul_right _ hk
      omega
    by_cases hjs : j < s
    · -- window position below the monic cap
      have hceil : ceilAt P j = pr.1.2 - k * sideH pr := by
        rw [menuPath_ceilAt_window hP hpr (by omega) hjle, ceilSide_pattern hw hh hk]
      have hmlt : pr.1.2 - k * sideH pr < N := by
        have := menuPath_height_le hP pr.1 hm1
        omega
      have hdvdj : p ^ (pr.1.2 - k * sideH pr) ∣ (((f.1).coeff j).val) := by
        have h1 := hdvd ⟨j, hjs⟩
        rwa [hceil] at h1
      have hguard_iff : ((PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ)
          = ((mkSide pr).v₀ : ℤ) + k * (mkSide pr).h)
          ↔ PadicLift.zmodValuation p N ((f.1).coeff j) = pr.1.2 - k * sideH pr := by
        rw [hHh]
        show ((PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ)
            = (pr.1.2 : ℤ) + k * (-((sideH pr : ℕ) : ℤ))) ↔ _
        have hcast : ((pr.1.2 - k * sideH pr : ℕ) : ℤ)
            = (pr.1.2 : ℤ) + (k : ℤ) * (-((sideH pr : ℕ) : ℤ)) := by
          push_cast [Nat.cast_sub hkH]
          ring
        constructor
        · intro hg
          have : (PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ)
              = ((pr.1.2 - k * sideH pr : ℕ) : ℤ) := by rw [hcast]; exact hg
          exact_mod_cast this
        · intro hv
          rw [← hcast, hv]
      unfold B.boxCoeffData
      rw [hidx]
      by_cases hval : PadicLift.zmodValuation p N ((f.1).coeff j) = pr.1.2 - k * sideH pr
      · rw [if_pos (hguard_iff.mpr hval)]
        have hxne : (f.1).coeff j ≠ 0 := by
          intro h0
          rw [h0, PadicLift.zmodValuation_zero] at hval
          omega
        rw [unitResidue_eq_digit p hxne hval, rho_lt p _ hjs, hceil]
      · rw [if_neg (fun hg => hval (hguard_iff.mp hg)), rho_lt p _ hjs, hceil]
        symm
        apply digit_eq_zero_of_dvd
        have hge1 : pr.1.2 - k * sideH pr ≤ PadicLift.zmodValuation p N ((f.1).coeff j) :=
          (pow_dvd_val_iff p hmlt.le _).mp hdvdj
        have hgt1 : pr.1.2 - k * sideH pr + 1 ≤ PadicLift.zmodValuation p N ((f.1).coeff j) := by
          omega
        exact (pow_dvd_val_iff p (by omega) _).mpr hgt1
    · -- the monic cap position j = s (forces k = d_S and the right endpoint (s,0))
      have hmle := menuPath_mem_le hP pr.2 hm2
      have hjs' : j = s := by omega
      have hpr21 : pr.2.1 = s := by omega
      have hkd : k = sideDeg pr := by
        have h1 : k * sideE pr = sideDeg pr * sideE pr := by omega
        exact Nat.eq_of_mul_eq_mul_right (sideE_pos hw hh) h1
      have hv1 : pr.2.2 = 0 := by
        have : ((s : ℕ), pr.2.2) ∈ P := by
          have := hm2
          rwa [show pr.2 = (pr.2.1, pr.2.2) from rfl, hpr21] at this
        exact menuPath_s_height hP this
      have hcs : (f.1).coeff j = 1 := by
        rw [hjs']
        have h1 := f.2.1.coeff_natDegree
        rwa [f.2.2] at h1
      have hval1 : PadicLift.zmodValuation p N ((f.1).coeff j) = 0 := by
        have := vOf_leading p hN f
        rw [vOf_eq] at this
        rw [hjs']
        exact this
      have hguard : (PadicLift.zmodValuation p N ((f.1).coeff j) : ℤ)
          = ((mkSide pr).v₀ : ℤ) + k * (mkSide pr).h := by
        rw [hval1, hHh, hkd]
        show (0 : ℤ) = (pr.1.2 : ℤ) + (sideDeg pr : ℤ) * (-((sideH pr : ℕ) : ℤ))
        have hZ : (sideDeg pr : ℤ) * ((sideH pr : ℕ) : ℤ) = ((pr.1.2 - pr.2.2 : ℕ) : ℤ) := by
          exact_mod_cast congrArg (Nat.cast (R := ℤ)) hghH'
        rw [Nat.cast_sub hh.le] at hZ
        rw [mul_neg, hZ, hv1]
        push_cast
        ring
      unfold B.boxCoeffData
      rw [hidx, if_pos hguard, hcs, unitResidue_one p hN, rho_ge p _ hjs]
  · rw [if_neg hk, if_neg hk]

/-- **The `Matches ⟺ digits` transport** (the heart of the coefficient-space reduction): a box
element matches the menu data `(P, sh)` iff every coefficient clears its column ceiling
(divisibility) and the ceiling digits satisfy the per-side `SideCond`s. -/
theorem matches_iff {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) (f : QuotientBox.monicBox p N s) :
    Matches p f P sh ↔
      (∀ i : Fin s, p ^ ceilAt P i.1 ∣ (((f.1).coeff i.1).val))
        ∧ DigCond p P sh (fun i : Fin s => digit p N (ceilAt P i.1) ((f.1).coeff i.1)) := by
  have hceil_le : ∀ i : Fin s, ceilAt P i.1 ≤ N := fun i => by
    have := menuPath_ceilAt_le hP i.2
    omega
  constructor
  · rintro ⟨hexact, hsides⟩
    have hdvd : ∀ i : Fin s, p ^ ceilAt P i.1 ∣ (((f.1).coeff i.1).val) := by
      intro i
      obtain ⟨pr, hpr, hw1, hw2⟩ := menuPath_containing hP i.2.le
      obtain ⟨l, _, hl⟩ := forall₂_mem_right hsides pr hpr
      have habove := hl.1 i.1 hw1 hw2
      obtain ⟨hw, hh, _, _⟩ := menuPath_side_facts hP pr hpr
      have hceq := menuPath_ceilAt_window hP hpr hw1 hw2
      rw [hceq]
      have hle : ceilSide pr i.1 ≤ vOf p f i.1 :=
        (lineAt_le_iff_ceilSide_le hw hh hw1).mp habove
      rw [vOf_eq] at hle
      exact (pow_dvd_val_iff p (hceq ▸ hceil_le i) _).mpr hle
    refine ⟨hdvd, ?_⟩
    refine forall₂_imp_mem hsides ?_
    intro l pr hlm hpm hside
    constructor
    · rw [← residualOf_eq_sidePolyR p hN hP hpm f hdvd]
      exact hside.2
    · -- the left-vertex digit is a unit (vertex exactness)
      obtain ⟨hw, hh, hm1, hm2⟩ := menuPath_side_facts hP pr hpm
      have hj0s : pr.1.1 < s := by
        have := menuPath_mem_le hP pr.2 hm2
        omega
      rw [rho_lt p _ hj0s]
      have hex : vOf p f pr.1.1 = pr.1.2 := hexact pr.1 hm1
      have hceq : ceilAt P pr.1.1 = pr.1.2 :=
        ceilAt_vertex (menuPath_pairwise hP) (show (pr.1.1, pr.1.2) ∈ P from hm1)
      have hmN : pr.1.2 < N := by
        have := menuPath_height_le hP pr.1 hm1
        omega
      have hdvd0 : p ^ pr.1.2 ∣ (((f.1).coeff pr.1.1).val) := by
        have := hdvd ⟨pr.1.1, hj0s⟩
        rwa [hceq] at this
      rw [hceq]
      exact (valuation_eq_iff_digit_ne p hmN hdvd0).mp (by rw [← vOf_eq]; exact hex)
  · rintro ⟨hdvd, hdig⟩
    constructor
    · -- vertex exactness
      intro q hq
      rcases eq_or_lt_of_le (menuPath_mem_le hP q hq) with heq | hlt
      · -- q = (s, 0)
        have hq0 : q.2 = 0 := menuPath_s_height hP (by
          rwa [show q = (q.1, q.2) from rfl, heq] at hq)
        rw [show q.1 = s from heq, hq0]
        exact vOf_leading p hN f
      · obtain ⟨H, p1, T, hPe, hH1, hH2, hp1, hpH, hc⟩ := hP
        have hP' : MenuPath s N P := ⟨H, p1, T, hPe, hH1, hH2, hp1, hpH, hc⟩
        have hq' : q ∈ (0, H) :: p1 :: T := hPe ▸ hq
        obtain ⟨pr, hpr0, hpr1⟩ := chainOK_side_starting hc q hq' (by omega)
        have hpr : pr ∈ sidePairs P := by rw [hPe]; exact hpr0
        obtain ⟨l, _, hl⟩ := forall₂_mem_right hdig pr hpr
        have hne := hl.2
        have hceq : ceilAt P q.1 = q.2 := ceilAt_vertex (menuPath_pairwise hP') hq
        have hmN : q.2 < N := by
          have := menuPath_height_le hP' q hq
          omega
      -- rho reads the digit at q.1
        rw [hpr1] at hne
        rw [rho_lt p _ (show q.1 < s from hlt)] at hne
        have hdvd0 : p ^ q.2 ∣ (((f.1).coeff q.1).val) := by
          have := hdvd ⟨q.1, hlt⟩
          rwa [hceq] at this
        rw [vOf_eq]
        exact (valuation_eq_iff_digit_ne p hmN hdvd0).mpr (by rwa [hceq] at hne)
    · refine forall₂_imp_mem hdig ?_
      intro l pr hlm hpm hside
      obtain ⟨hw, hh, hm1, hm2⟩ := menuPath_side_facts hP pr hpm
      constructor
      · -- SideAbove
        intro i hi1 hi2
        by_cases his : i < s
        · have hceq := menuPath_ceilAt_window hP hpm hi1 hi2
          have hge : ceilAt P i ≤ vOf p f i := by
            rw [vOf_eq]
            exact (pow_dvd_val_iff p (by
              have := menuPath_ceilAt_le hP his
              omega) _).mp (hdvd ⟨i, his⟩)
          exact (lineAt_le_iff_ceilSide_le hw hh hi1).mpr (by rw [← hceq]; exact hge)
        · have hmle := menuPath_mem_le hP pr.2 hm2
          have hie : i = s := by omega
          have hpr21 : pr.2.1 = s := by omega
          have hv1 : pr.2.2 = 0 := menuPath_s_height hP (by
            have := hm2
            rwa [show pr.2 = (pr.2.1, pr.2.2) from rfl, hpr21] at this)
          have hiw : (i : ℚ) = (pr.2.1 : ℚ) := by
            rw [hie, hpr21]
          rw [hiw, lineAt_right hw, hv1, hie, vOf_leading p hN f]
      · rw [residualOf_eq_sidePolyR p hN hP hpm f hdvd]
        exact hside.1

end Box

/-! ## 5. The coefficient equivalence -/

section CoeffEquiv

variable (p : ℕ) [hp : Fact p.Prime]

theorem coeff_sum_fin {N s : ℕ} (a : Fin s → ZMod (p ^ N)) (k : ℕ) :
    (∑ i : Fin s, C (a i) * X ^ (i : ℕ)).coeff k
      = if h : k < s then a ⟨k, h⟩ else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : k < s
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin s)]
    · rw [if_pos rfl]
    · intro i _ hne
      rw [if_neg]
      intro hki
      exact hne (Fin.ext hki.symm)
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hki
    exact h (hki ▸ i.2)

/-- The monic completion of a low-coefficient vector. -/
noncomputable def lowPoly {N s : ℕ} (a : Fin s → ZMod (p ^ N)) : (ZMod (p ^ N))[X] :=
  X ^ s + ∑ i : Fin s, C (a i) * X ^ (i : ℕ)

theorem lowPoly_coeff {N s : ℕ} (a : Fin s → ZMod (p ^ N)) (k : ℕ) :
    (lowPoly p a).coeff k
      = if h : k < s then a ⟨k, h⟩ else if k = s then 1 else 0 := by
  unfold lowPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, coeff_sum_fin]
  by_cases h : k < s
  · rw [dif_pos h, dif_pos h, if_neg (by omega), zero_add]
  · rw [dif_neg h, dif_neg h, add_zero]

theorem lowPoly_monic {N s : ℕ} (hN : 0 < N) (a : Fin s → ZMod (p ^ N)) :
    (lowPoly p a).Monic ∧ (lowPoly p a).natDegree = s := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  have hcoeffs : (lowPoly p a).coeff s = 1 := by
    rw [lowPoly_coeff, dif_neg (by omega), if_pos rfl]
  have hle : (lowPoly p a).natDegree ≤ s := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [lowPoly_coeff, dif_neg (by omega), if_neg (by omega)]
  have hmon : (lowPoly p a).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one s hle hcoeffs
  refine ⟨hmon, le_antisymm hle ?_⟩
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hcoeffs]
  exact one_ne_zero

/-- **The coefficient equivalence**: a monic degree-`s` box polynomial IS its `s` low
coefficients. -/
noncomputable def coeffEquiv (N s : ℕ) (hN : 0 < N) :
    QuotientBox.monicBox p N s ≃ (Fin s → ZMod (p ^ N)) where
  toFun f i := (f.1).coeff i.1
  invFun a := ⟨lowPoly p a, (lowPoly_monic p hN a).1, (lowPoly_monic p hN a).2⟩
  left_inv f := by
    refine Subtype.ext ?_
    ext k
    rw [lowPoly_coeff]
    by_cases h : k < s
    · rw [dif_pos h]
    · rw [dif_neg h]
      by_cases hks : k = s
      · rw [if_pos hks, hks]
        have h1 := f.2.1.coeff_natDegree
        rw [f.2.2] at h1
        exact h1.symm
      · rw [if_neg hks]
        symm
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [f.2.2]
        omega
  right_inv a := by
    funext i
    show (lowPoly p a).coeff i.1 = a i
    rw [lowPoly_coeff, dif_pos i.2]

instance {N s : ℕ} : Finite (QuotientBox.monicBox p N s) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  apply Finite.of_injective
    (fun f : QuotientBox.monicBox p N s => fun i : Fin (s + 1) => (f.1).coeff i.1)
  intro f g hfg
  refine Subtype.ext ?_
  ext k
  by_cases hk : k ≤ s
  · exact congrFun hfg ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [f.2.2]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [g.2.2]; omega)]

end CoeffEquiv

/-! ## 6. The per-side residual-shape count and the anchored window count -/

section SideCount

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The per-side residual-shape count**: monic polynomials over `ZMod p` prime to `X`
(unit constant term) with factorization shape `l`. -/
noncomputable def shapeCount (l : List (ℕ × ℕ)) : ℕ :=
  Nat.card {M : (ZMod p)[X] // M.Monic ∧ ¬ X ∣ M ∧ polyShape p M = (l : Multiset (ℕ × ℕ))}

/-- The joint residual-shape count of a shape assignment. -/
noncomputable def prodSC (sh : List (List (ℕ × ℕ))) : ℕ := (sh.map (shapeCount p)).prod

/-- The off-pattern residue-digit count of the sides of a path. -/
def chainFree (P : List (ℕ × ℕ)) : ℕ :=
  ((sidePairs P).map fun pr => pr.2.1 - pr.1.1 - sideDeg pr).sum

/-- **The explicit free-digit exponent** of a menu path at level `N`: column `i` frees its
`N − 1 − ⌈h_i⌉` digits strictly below the residue read; each side frees its `run − d_S`
off-pattern residue digits. -/
def freeExp (s N : ℕ) (P : List (ℕ × ℕ)) : ℕ :=
  (∑ i ∈ Finset.range s, (N - 1 - ceilAt P i)) + chainFree P

/-- The degree of a shape-`l` polynomial is the shape degree. -/
theorem natDegree_of_polyShape {l : List (ℕ × ℕ)} {d : ℕ} (hl : l ∈ shapesOfDegree d)
    {M : (ZMod p)[X]} (hM : M ≠ 0) (hshape : polyShape p M = (l : Multiset (ℕ × ℕ))) :
    M.natDegree = d := by
  have hsum := polyShape_sum p hM
  rw [hshape, Multiset.map_coe, Multiset.sum_coe] at hsum
  obtain ⟨-, -, hsum'⟩ := mem_shapesOfDegree_iff.mp hl
  rw [← hsum]
  exact hsum'

/-- The per-side digit polynomial with an explicit right anchor `u`. -/
noncomputable def sidePolyA {s : ℕ} (x : Fin s → ZMod p) (u : ZMod p)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) : (ZMod p)[X] :=
  (∑ t ∈ Finset.range (sideDeg pr), C (rho p x (pr.1.1 + t * sideE pr)) * X ^ t)
    + C u * X ^ sideDeg pr

theorem sidePolyA_coeff {s : ℕ} (x : Fin s → ZMod p) (u : ZMod p)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) :
    (sidePolyA p x u pr).coeff k
      = if k < sideDeg pr then rho p x (pr.1.1 + k * sideE pr)
        else if k = sideDeg pr then u else 0 := by
  unfold sidePolyA
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (sideDeg pr)) k
    (fun t => rho p x (pr.1.1 + t * sideE pr))]
  simp only [Finset.mem_range]
  by_cases h1 : k < sideDeg pr
  · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

theorem sidePolyA_congr {s : ℕ} {x x' : Fin s → ZMod p} (u : ZMod p)
    (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (h : ∀ t, t < sideDeg pr →
      rho p x (pr.1.1 + t * sideE pr) = rho p x' (pr.1.1 + t * sideE pr)) :
    sidePolyA p x u pr = sidePolyA p x' u pr := by
  unfold sidePolyA
  congr 1
  exact Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.mp ht)]

theorem sidePolyR_eq_sidePolyA {s : ℕ} (r : Fin s → ZMod p) {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2) :
    sidePolyR p r pr = sidePolyA p r (rho p r pr.2.1) pr := by
  unfold sidePolyR sidePolyA
  rw [Finset.sum_range_succ,
    show pr.1.1 + sideDeg pr * sideE pr = pr.2.1 from by
      rw [sideDeg_mul_sideE hw hh]; omega]

/-- Unit scaling is invisible to the factorization shape. -/
theorem polyShape_C_mul {c : ZMod p} (hc : c ≠ 0) {R : (ZMod p)[X]} (hR : R ≠ 0) :
    polyShape p (C c * R) = polyShape p R := by
  classical
  have hu : IsUnit (C c : (ZMod p)[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hnf : UniqueFactorizationMonoid.normalizedFactors (C c * R)
      = UniqueFactorizationMonoid.normalizedFactors R := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (Polynomial.C_ne_zero.mpr hc) hR,
      UniqueFactorizationMonoid.normalizedFactors_of_isUnit hu, zero_add]
  unfold CellMenu.polyShape
  rw [hnf]

theorem pat_pos_lt {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1) (hh : pr.2.2 < pr.1.2)
    {t : ℕ} (ht : t < sideDeg pr) : pr.1.1 + t * sideE pr < pr.2.1 := by
  have h1 : t * sideE pr < sideDeg pr * sideE pr :=
    mul_lt_mul_of_pos_right ht (sideE_pos hw hh)
  have h2 := sideDeg_mul_sideE hw hh
  omega

/-- The pattern positions of a side inside `Fin s`. -/
def patFinset (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Finset (Fin s) :=
  Finset.univ.filter fun i => pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 ∧ (i.1 - pr.1.1) % sideE pr = 0

/-- The window positions of a side inside `Fin s`. -/
def winFinset (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Finset (Fin s) :=
  Finset.univ.filter fun i => pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1

theorem mem_patFinset {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} {i : Fin s} :
    i ∈ patFinset s pr
      ↔ pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 ∧ (i.1 - pr.1.1) % sideE pr = 0 := by
  unfold patFinset
  simp

theorem mem_winFinset {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} {i : Fin s} :
    i ∈ winFinset s pr ↔ pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 := by
  unfold winFinset
  simp

theorem patFinset_subset {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} :
    patFinset s pr ⊆ winFinset s pr := fun i hi => by
  rw [mem_patFinset] at hi
  rw [mem_winFinset]
  exact ⟨hi.1, hi.2.1⟩

theorem pat_pos_mem {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {t : ℕ} (ht : t < sideDeg pr) :
    ∃ h : pr.1.1 + t * sideE pr < s, (⟨pr.1.1 + t * sideE pr, h⟩ : Fin s) ∈ patFinset s pr := by
  have hlt := pat_pos_lt hw hh ht
  refine ⟨by omega, ?_⟩
  rw [mem_patFinset]
  show pr.1.1 ≤ pr.1.1 + t * sideE pr ∧ pr.1.1 + t * sideE pr < pr.2.1
      ∧ (pr.1.1 + t * sideE pr - pr.1.1) % sideE pr = 0
  refine ⟨by omega, by omega, ?_⟩
  rw [show pr.1.1 + t * sideE pr - pr.1.1 = t * sideE pr from by omega, Nat.mul_mod_left]

theorem card_winFinset {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hs : pr.2.1 ≤ s) :
    (winFinset s pr).card = pr.2.1 - pr.1.1 := by
  rw [← Nat.card_Ico pr.1.1 pr.2.1]
  refine Finset.card_bij' (fun i _ => i.1) (fun j hj => ⟨j, ?_⟩) ?_ ?_ ?_ ?_
  · rw [Finset.mem_Ico] at hj
    omega
  · intro i hi
    rw [mem_winFinset] at hi
    rw [Finset.mem_Ico]
    omega
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [mem_winFinset]
    exact ⟨hj.1, hj.2⟩
  · intro i hi
    rfl
  · intro j hj
    rfl

theorem card_patFinset {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) :
    (patFinset s pr).card = sideDeg pr := by
  have he0 := sideE_pos hw hh
  have hde := sideDeg_mul_sideE hw hh
  rw [← Finset.card_range (sideDeg pr)]
  refine Finset.card_bij' (fun i _ => (i.1 - pr.1.1) / sideE pr)
    (fun t ht => ⟨pr.1.1 + t * sideE pr, by
      rw [Finset.mem_range] at ht
      have h1 := pat_pos_lt hw hh ht
      omega⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_patFinset] at hi
    obtain ⟨h1, h2, h3⟩ := hi
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul he0]
    omega
  · intro t ht
    have ht' := ht
    rw [Finset.mem_range] at ht'
    have h1 := pat_pos_lt hw hh ht'
    rw [mem_patFinset]
    show pr.1.1 ≤ pr.1.1 + t * sideE pr ∧ pr.1.1 + t * sideE pr < pr.2.1
        ∧ (pr.1.1 + t * sideE pr - pr.1.1) % sideE pr = 0
    refine ⟨by omega, by omega, ?_⟩
    rw [show pr.1.1 + t * sideE pr - pr.1.1 = t * sideE pr from by omega, Nat.mul_mod_left]
  · intro i hi
    rw [mem_patFinset] at hi
    obtain ⟨h1, h2, h3⟩ := hi
    refine Fin.ext ?_
    show pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr = i.1
    rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h3)]
    omega
  · intro t ht
    rw [Finset.mem_range] at ht
    show (pr.1.1 + t * sideE pr - pr.1.1) / sideE pr = t
    rw [show pr.1.1 + t * sideE pr - pr.1.1 = t * sideE pr from by omega,
      Nat.mul_div_cancel _ he0]

/-- **The pattern-window count is the shape count** (the side-normalization bijection): digit
vectors supported on the pattern positions whose anchored side polynomial has shape `l` and unit
left read are exactly the monic shape-`l` polynomials, via `M = C u⁻¹ * R`. -/
theorem card_patPart {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {l : List (ℕ × ℕ)}
    (hl : l ∈ shapesOfDegree (sideDeg pr)) {u : ZMod p} (hu : u ≠ 0) :
    Nat.card {x : Fin s → ZMod p // (∀ i ∉ patFinset s pr, x i = 0)
        ∧ polyShape p (sidePolyA p x u pr) = (l : Multiset (ℕ × ℕ)) ∧ rho p x pr.1.1 ≠ 0}
      = shapeCount p l := by
  have he0 := sideE_pos hw hh
  have hd0 := sideDeg_pos hw hh
  have hj0s : pr.1.1 < s := by omega
  have hj0mem : (⟨pr.1.1, hj0s⟩ : Fin s) ∈ patFinset s pr := by
    rw [mem_patFinset]
    exact ⟨le_refl _, by omega, by simp⟩
  -- generic facts about the anchored polynomial
  have hA_deg : ∀ x : Fin s → ZMod p, (sidePolyA p x u pr).natDegree ≤ sideDeg pr := by
    intro x
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [sidePolyA_coeff, if_neg (by omega), if_neg (by omega)]
  have hA_ne : ∀ x : Fin s → ZMod p, sidePolyA p x u pr ≠ 0 := by
    intro x h0
    have h1 := congrArg (fun Q : (ZMod p)[X] => Q.coeff (sideDeg pr)) h0
    simp only [Polynomial.coeff_zero] at h1
    rw [sidePolyA_coeff, if_neg (by omega), if_pos rfl] at h1
    exact hu h1
  -- the assembled polynomial of a shape element
  have key : ∀ M : (ZMod p)[X], M.Monic → polyShape p M = (l : Multiset (ℕ × ℕ)) →
      sidePolyA p (fun i : Fin s => if i ∈ patFinset s pr
          then u * M.coeff ((i.1 - pr.1.1) / sideE pr) else 0) u pr = C u * M := by
    intro M hmon hshape
    have hMd : M.natDegree = sideDeg pr := natDegree_of_polyShape p hl hmon.ne_zero hshape
    ext k
    rw [sidePolyA_coeff, Polynomial.coeff_C_mul]
    by_cases h1 : k < sideDeg pr
    · rw [if_pos h1]
      have hlt := pat_pos_lt hw hh h1
      have hlts : pr.1.1 + k * sideE pr < s := by omega
      obtain ⟨hlts', hmem⟩ := pat_pos_mem hw hh hs h1
      rw [rho_lt p _ hlts, if_pos hmem]
      congr 2
      rw [show pr.1.1 + k * sideE pr - pr.1.1 = k * sideE pr from by omega,
        Nat.mul_div_cancel _ he0]
    · rw [if_neg h1]
      by_cases h2 : k = sideDeg pr
      · rw [if_pos h2, h2, ← hMd, hmon.coeff_natDegree, mul_one]
      · rw [if_neg h2, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hMd]; omega), mul_zero]
  symm
  refine Nat.card_congr ⟨fun M =>
      ⟨fun i => if i ∈ patFinset s pr then u * (M.1).coeff ((i.1 - pr.1.1) / sideE pr) else 0,
        fun i hi => if_neg hi, ?_, ?_⟩,
    fun x => ⟨C u⁻¹ * sidePolyA p x.1 u pr, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- shape of the assembled window vector
    rw [key M.1 M.2.1 M.2.2.2, polyShape_C_mul p hu M.2.1.ne_zero]
    exact M.2.2.2
  · -- unit left read
    rw [rho_lt p _ hj0s, if_pos hj0mem]
    simp only [Nat.sub_self, Nat.zero_div]
    exact mul_ne_zero hu (fun h0 => M.2.2.1 (Polynomial.X_dvd_iff.mpr h0))
  · -- monic
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (sideDeg pr)
    · calc (C u⁻¹ * sidePolyA p x.1 u pr).natDegree
          ≤ (C u⁻¹ : (ZMod p)[X]).natDegree + (sidePolyA p x.1 u pr).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ sideDeg pr := by
            rw [Polynomial.natDegree_C, zero_add]
            exact hA_deg x.1
    · rw [Polynomial.coeff_C_mul, sidePolyA_coeff, if_neg (by omega), if_pos rfl,
        inv_mul_cancel₀ hu]
  · -- prime to X
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_C_mul, sidePolyA_coeff, if_pos hd0,
      show pr.1.1 + 0 * sideE pr = pr.1.1 from by omega]
    have hx0 := x.2.2.2
    rw [rho_lt p _ hj0s] at hx0
    rw [rho_lt p _ hj0s]
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hu (by simpa using h)
    · exact hx0 h
  · -- shape
    rw [polyShape_C_mul p (inv_ne_zero hu) (hA_ne x.1)]
    exact x.2.2.1
  · -- left inverse: M ↦ window vector ↦ M
    intro M
    refine Subtype.ext ?_
    show C u⁻¹ * sidePolyA p (fun i => if i ∈ patFinset s pr
        then u * (M.1).coeff ((i.1 - pr.1.1) / sideE pr) else 0) u pr = M.1
    rw [key M.1 M.2.1 M.2.2.2, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hu,
      Polynomial.C_1, one_mul]
  · -- right inverse: window vector ↦ M ↦ window vector
    intro x
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : i ∈ patFinset s pr
    · simp only [if_pos hi]
      rw [Polynomial.coeff_C_mul]
      obtain ⟨h1, h2, h3⟩ := mem_patFinset.mp hi
      have hdvd : sideE pr ∣ (i.1 - pr.1.1) := Nat.dvd_of_mod_eq_zero h3
      have hte : (i.1 - pr.1.1) / sideE pr * sideE pr = i.1 - pr.1.1 :=
        Nat.div_mul_cancel hdvd
      have htd : (i.1 - pr.1.1) / sideE pr < sideDeg pr := by
        rw [Nat.div_lt_iff_lt_mul he0]
        have := sideDeg_mul_sideE hw hh
        omega
      have hieq : (⟨pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr,
          show pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr < s from by omega⟩ : Fin s) = i :=
        Fin.ext (show pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr = i.1 from by omega)
      rw [sidePolyA_coeff, if_pos htd,
        rho_lt p _ (show pr.1.1 + (i.1 - pr.1.1) / sideE pr * sideE pr < s from by omega),
        hieq, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    · simp only [if_neg hi]
      exact (x.2.1 i hi).symm

/-- **The anchored window count**: `SC(l) · p^(run − d_S)` for any unit anchor. -/
theorem card_sideSet {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {l : List (ℕ × ℕ)}
    (hl : l ∈ shapesOfDegree (sideDeg pr)) {u : ZMod p} (hu : u ≠ 0) :
    Nat.card {x : Fin s → ZMod p // (∀ i ∉ winFinset s pr, x i = 0)
        ∧ polyShape p (sidePolyA p x u pr) = (l : Multiset (ℕ × ℕ)) ∧ rho p x pr.1.1 ≠ 0}
      = shapeCount p l * p ^ (pr.2.1 - pr.1.1 - sideDeg pr) := by
  classical
  have hsplit := card_supp_split (patFinset s pr) (winFinset s pr \ patFinset s pr)
    (Finset.disjoint_sdiff)
    (fun x => polyShape p (sidePolyA p x u pr) = (l : Multiset (ℕ × ℕ)) ∧ rho p x pr.1.1 ≠ 0)
    ?_
  · rw [Finset.union_sdiff_of_subset patFinset_subset] at hsplit
    rw [hsplit, card_patPart p hw hh hs hl hu, Nat.card_zmod, Finset.card_sdiff,
      Finset.inter_eq_left.mpr patFinset_subset, card_winFinset hs, card_patFinset hw hh hs]
  · intro f g hagree hf
    have hrho : ∀ t, t < sideDeg pr →
        rho p f (pr.1.1 + t * sideE pr) = rho p g (pr.1.1 + t * sideE pr) := by
      intro t ht
      obtain ⟨hlt, hmem⟩ := pat_pos_mem hw hh hs ht
      rw [rho_lt p _ hlt, rho_lt p _ hlt]
      exact hagree _ hmem
    have h0 : rho p f pr.1.1 = rho p g pr.1.1 := by
      have h00 := hrho 0 (sideDeg_pos hw hh)
      rwa [show pr.1.1 + 0 * sideE pr = pr.1.1 from by omega] at h00
    rwa [sidePolyA_congr p u pr hrho, h0] at hf

end SideCount

/-! ## 7. The chain telescope: peeling sides right-to-left -/

section Chain

variable (p : ℕ) [hp : Fact p.Prime]

/-- All coordinates strictly below `j` vanish. -/
def ZeroBelow {s : ℕ} (j : ℕ) (r : Fin s → ZMod p) : Prop := ∀ i : Fin s, i.1 < j → r i = 0

/-- The residual bridge: the side polynomial reads only its window plus the right anchor. -/
theorem peel_bridge {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) (r x y : Fin s → ZMod p)
    (hx : ∀ i : Fin s, pr.1.1 ≤ i.1 → i.1 < pr.2.1 → x i = r i)
    (hy : ∀ i : Fin s, pr.2.1 ≤ i.1 → y i = r i) :
    sidePolyR p r pr = sidePolyA p x (rho p y pr.2.1) pr := by
  rw [sidePolyR_eq_sidePolyA p r hw hh]
  have hanch : rho p r pr.2.1 = rho p y pr.2.1 := by
    by_cases hjs : pr.2.1 < s
    · rw [rho_lt p _ hjs, rho_lt p _ hjs]
      exact (hy ⟨pr.2.1, hjs⟩ (le_refl _)).symm
    · rw [rho_ge p _ hjs, rho_ge p _ hjs]
  rw [hanch]
  apply sidePolyA_congr
  intro t ht
  have hlt := pat_pos_lt hw hh ht
  have hlts : pr.1.1 + t * sideE pr < s := by omega
  rw [rho_lt p _ hlts, rho_lt p _ hlts]
  exact (hx ⟨pr.1.1 + t * sideE pr, hlts⟩
    (show pr.1.1 ≤ pr.1.1 + t * sideE pr from by omega)
    (show pr.1.1 + t * sideE pr < pr.2.1 from hlt)).symm

/-- **The peel splice**: a zero-based digit vector satisfying the leftmost side condition plus a
right-suffix condition `Q` (reading only positions `≥ j₁`) splits into its suffix part and its
anchored window part. -/
noncomputable def peelEquiv {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) (l : List (ℕ × ℕ))
    (Q : (Fin s → ZMod p) → Prop)
    (hQ : ∀ r r' : Fin s → ZMod p, (∀ i : Fin s, pr.2.1 ≤ i.1 → r i = r' i) → Q r → Q r') :
    {r : Fin s → ZMod p // ZeroBelow p pr.1.1 r ∧ SideCond p r l pr ∧ Q r}
      ≃ {z : {y : Fin s → ZMod p // ZeroBelow p pr.2.1 y ∧ Q y} × (Fin s → ZMod p) //
          (∀ i ∉ winFinset s pr, z.2 i = 0)
            ∧ polyShape p (sidePolyA p z.2 (rho p z.1.1 pr.2.1) pr) = (l : Multiset (ℕ × ℕ))
            ∧ rho p z.2 pr.1.1 ≠ 0} where
  toFun r :=
    ⟨(⟨fun i => if i.1 < pr.2.1 then 0 else r.1 i,
        fun i hi => if_pos hi,
        hQ r.1 _ (fun i hi => (if_neg (by omega)).symm) r.2.2.2⟩,
      fun i => if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0),
     by
      refine ⟨fun i hi => if_neg (by rw [mem_winFinset] at hi; exact hi), ?_, ?_⟩
      · have hb := peel_bridge p hw hh hs r.1
          (fun i => if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0)
          (fun i => if i.1 < pr.2.1 then 0 else r.1 i)
          (fun i h1 h2 => if_pos ⟨h1, h2⟩) (fun i hi => if_neg (by omega))
        rw [← hb]
        exact r.2.2.1.1
      · have hj0s : pr.1.1 < s := by omega
        rw [rho_lt p _ hj0s]
        show (if pr.1.1 ≤ pr.1.1 ∧ pr.1.1 < pr.2.1 then r.1 ⟨pr.1.1, hj0s⟩ else 0) ≠ 0
        rw [if_pos ⟨le_refl _, hw⟩]
        have h1 := r.2.2.1.2
        rwa [rho_lt p _ hj0s] at h1⟩
  invFun z :=
    ⟨fun i => z.1.2 i + z.1.1.1 i,
     by
      intro i hi
      have h1 : i ∉ winFinset s pr := by
        rw [mem_winFinset]
        omega
      show z.1.2 i + z.1.1.1 i = 0
      rw [z.2.1 i h1, z.1.1.2.1 i (by omega), add_zero],
     by
      constructor
      · have hb := peel_bridge p hw hh hs (fun i => z.1.2 i + z.1.1.1 i) z.1.2 z.1.1.1
          (fun i h1 h2 => by
            show z.1.2 i = z.1.2 i + z.1.1.1 i
            rw [z.1.1.2.1 i h2, add_zero])
          (fun i hi => by
            show z.1.1.1 i = z.1.2 i + z.1.1.1 i
            rw [z.2.1 i (by rw [mem_winFinset]; omega), zero_add])
        rw [hb]
        exact z.2.2.1
      · have hj0s : pr.1.1 < s := by omega
        rw [rho_lt p _ hj0s]
        have h1 := z.2.2.2
        rw [rho_lt p _ hj0s] at h1
        show z.1.2 ⟨pr.1.1, hj0s⟩ + z.1.1.1 ⟨pr.1.1, hj0s⟩ ≠ 0
        rw [z.1.1.2.1 ⟨pr.1.1, hj0s⟩ hw, add_zero]
        exact h1,
     hQ z.1.1.1 _ (fun i hi => by
        show z.1.1.1 i = z.1.2 i + z.1.1.1 i
        rw [z.2.1 i (by rw [mem_winFinset]; omega), zero_add]) z.1.1.2.2⟩
  left_inv r := by
    refine Subtype.ext (funext fun i => ?_)
    show (if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0)
        + (if i.1 < pr.2.1 then 0 else r.1 i) = r.1 i
    by_cases h1 : i.1 < pr.1.1
    · rw [if_neg (by omega), if_pos (by omega), add_zero, r.2.1 i h1]
    · by_cases h2 : i.1 < pr.2.1
      · rw [if_pos ⟨by omega, h2⟩, if_pos h2, add_zero]
      · rw [if_neg (by omega), if_neg h2, zero_add]
  right_inv z := by
    refine Subtype.ext (Prod.ext (Subtype.ext (funext fun i => ?_)) (funext fun i => ?_))
    · show (if i.1 < pr.2.1 then 0 else z.1.2 i + z.1.1.1 i) = z.1.1.1 i
      by_cases h2 : i.1 < pr.2.1
      · rw [if_pos h2, (z.1.1.2.1 i h2)]
      · rw [if_neg h2, z.2.1 i (by rw [mem_winFinset]; omega), zero_add]
    · show (if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then z.1.2 i + z.1.1.1 i else 0) = z.1.2 i
      by_cases h1 : pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1
      · rw [if_pos h1, z.1.1.2.1 i h1.2, add_zero]
      · rw [if_neg h1, (z.2.1 i (by rw [mem_winFinset]; exact h1))]

/-- **The peel step count**: the leftmost side contributes `SC(l) · p^(run − d_S)`,
independently of the (unit) anchor supplied by the suffix. -/
theorem card_peel {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {l : List (ℕ × ℕ)}
    (hl : l ∈ shapesOfDegree (sideDeg pr)) (Q : (Fin s → ZMod p) → Prop)
    (hQ : ∀ r r' : Fin s → ZMod p, (∀ i : Fin s, pr.2.1 ≤ i.1 → r i = r' i) → Q r → Q r')
    (hanchor : ∀ r : Fin s → ZMod p, ZeroBelow p pr.2.1 r → Q r → rho p r pr.2.1 ≠ 0) :
    Nat.card {r : Fin s → ZMod p // ZeroBelow p pr.1.1 r ∧ SideCond p r l pr ∧ Q r}
      = (shapeCount p l * p ^ (pr.2.1 - pr.1.1 - sideDeg pr))
          * Nat.card {r : Fin s → ZMod p // ZeroBelow p pr.2.1 r ∧ Q r} := by
  classical
  have hK := card_sigma_const
    (α := {y : Fin s → ZMod p // ZeroBelow p pr.2.1 y ∧ Q y})
    (F := fun y => {x : Fin s → ZMod p // (∀ i ∉ winFinset s pr, x i = 0)
      ∧ polyShape p (sidePolyA p x (rho p y.1 pr.2.1) pr) = (l : Multiset (ℕ × ℕ))
      ∧ rho p x pr.1.1 ≠ 0})
    (K := shapeCount p l * p ^ (pr.2.1 - pr.1.1 - sideDeg pr))
    (fun y => card_sideSet p hw hh hs hl (hanchor y.1 y.2.1 y.2.2))
  rw [Nat.card_congr ((peelEquiv p hw hh hs l Q hQ).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun (y : {y : Fin s → ZMod p // ZeroBelow p pr.2.1 y ∧ Q y}) (x : Fin s → ZMod p) =>
        (∀ i ∉ winFinset s pr, x i = 0)
          ∧ polyShape p (sidePolyA p x (rho p y.1 pr.2.1) pr) = (l : Multiset (ℕ × ℕ))
          ∧ rho p x pr.1.1 ≠ 0))), hK, mul_comm]

/-- **The chain telescope**: the digit count of a zero-based suffix chain is the product of its
per-side shape counts times the off-pattern digit freedom. -/
theorem chain_count {s : ℕ} :
    ∀ {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}, ChainOK s p0 p1 T → p0.1 < p1.1 → p1.2 < p0.2 →
      ∀ {sh : List (List (ℕ × ℕ))},
        List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) sh
          (sidePairs (p0 :: p1 :: T)) →
      Nat.card {r : Fin s → ZMod p // ZeroBelow p p0.1 r
          ∧ List.Forall₂ (fun l pr => SideCond p r l pr) sh (sidePairs (p0 :: p1 :: T))}
        = prodSC p sh
            * p ^ (((sidePairs (p0 :: p1 :: T)).map
                fun pr => pr.2.1 - pr.1.1 - sideDeg pr).sum) := by
  intro T
  induction T with
  | nil =>
      intro p0 p1 hc hw hh sh hsh
      cases hc with
      | nil h1 h2 =>
        have hsp : sidePairs [p0, p1] = [(p0, p1)] := rfl
        rw [hsp] at hsh ⊢
        rw [List.forall₂_cons_right_iff] at hsh
        obtain ⟨l, sh', hl, hsh', rfl⟩ := hsh
        rw [List.forall₂_nil_right_iff] at hsh'
        subst hsh'
        have e1 : {r : Fin s → ZMod p // ZeroBelow p p0.1 r
              ∧ List.Forall₂ (fun l' pr => SideCond p r l' pr) [l] [(p0, p1)]}
            ≃ {r : Fin s → ZMod p // ZeroBelow p p0.1 r ∧ SideCond p r l (p0, p1) ∧ True} :=
          Equiv.subtypeEquivRight fun r => by
            rw [List.forall₂_cons]
            simp
        rw [Nat.card_congr e1]
        have hpeel := card_peel p (pr := (p0, p1)) hw hh (le_of_eq h1) hl (fun _ => True)
          (fun _ _ _ _ => trivial)
          (fun r _ _ => by
            rw [rho_ge p _ (show ¬ (p0, p1).2.1 < s from by
              show ¬ p1.1 < s
              omega)]
            exact one_ne_zero)
        rw [hpeel]
        have hone : Nat.card {r : Fin s → ZMod p // ZeroBelow p (p0, p1).2.1 r ∧ True} = 1 := by
          haveI : Unique {r : Fin s → ZMod p // ZeroBelow p (p0, p1).2.1 r ∧ True} :=
            { default := ⟨fun _ => 0, fun i _ => rfl, trivial⟩
              uniq := fun r => Subtype.ext (funext fun i => r.2.1 i (by
                show i.1 < p1.1
                have := i.2
                omega)) }
          exact Nat.card_unique
        rw [hone, mul_one]
        simp [prodSC]
  | cons p2 T' ih =>
      intro p0 p1 hc hw hh sh hsh
      cases hc with
      | cons h1 h2 h3 h4 =>
        rw [sidePairs_cons₂] at hsh ⊢
        rw [List.forall₂_cons_right_iff] at hsh
        obtain ⟨l, sh', hl, hsh', rfl⟩ := hsh
        have hs2 : p2.1 ≤ s := chainOK_le h4
        have e1 : {r : Fin s → ZMod p // ZeroBelow p p0.1 r
              ∧ List.Forall₂ (fun l' pr => SideCond p r l' pr) (l :: sh')
                  ((p0, p1) :: sidePairs (p1 :: p2 :: T'))}
            ≃ {r : Fin s → ZMod p // ZeroBelow p p0.1 r ∧ SideCond p r l (p0, p1)
                ∧ List.Forall₂ (fun l' pr => SideCond p r l' pr) sh'
                    (sidePairs (p1 :: p2 :: T'))} :=
          Equiv.subtypeEquivRight fun r => by
            rw [List.forall₂_cons]
        rw [Nat.card_congr e1]
        have hside_ge : ∀ pr' ∈ sidePairs (p1 :: p2 :: T'), p1.1 ≤ pr'.1.1 := by
          intro pr' hpr'
          obtain ⟨hw', hh', hm1, hm2⟩ :=
            chainOK_side_facts (ChainOK.cons h1 h2 h3 h4) pr' hpr'
          rcases List.mem_cons.mp hm1 with heq | hm1'
          · rw [heq]
          · exact (chainOK_mem_bounds (ChainOK.cons h1 h2 h3 h4) pr'.1 hm1').1.le
        have hpeel := card_peel p (pr := (p0, p1)) hw hh
          (show (p0, p1).2.1 ≤ s from by
            show p1.1 ≤ s
            omega) hl
          (fun r => List.Forall₂ (fun l' pr => SideCond p r l' pr) sh'
            (sidePairs (p1 :: p2 :: T')))
          (fun r r' hagree hQr => by
            refine forall₂_imp_mem hQr ?_
            intro l' pr' _ hpr'm hcond
            refine (sideCond_congr p ?_).mp hcond
            intro j hj
            exact rho_eq_of_agree p hagree (le_trans (hside_ge pr' hpr'm) hj))
          (fun r _ hQr => by
            rw [sidePairs_cons₂, List.forall₂_cons_right_iff] at hQr
            obtain ⟨l₂, sh'', hl₂, _, rfl⟩ := hQr
            exact hl₂.2)
        rw [hpeel, ih h4 h1 h2 hsh']
        simp only [prodSC, List.map_cons, List.prod_cons, List.sum_cons]
        rw [pow_add]
        ring

/-- **The digit count of a full menu cell**: `prodSC · p^chainFree`. -/
theorem digCond_count {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    Nat.card {r : Fin s → ZMod p // DigCond p P sh r} = prodSC p sh * p ^ chainFree P := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hP
  have e : {r : Fin s → ZMod p // DigCond p ((0, H) :: p1 :: T) sh r}
      ≃ {r : Fin s → ZMod p // ZeroBelow p (0, H).1 r
          ∧ List.Forall₂ (fun l pr => SideCond p r l pr) sh (sidePairs ((0, H) :: p1 :: T))} :=
    Equiv.subtypeEquivRight fun r => by
      unfold DigCond ZeroBelow
      constructor
      · exact fun h => ⟨fun i hi => absurd hi (by omega), h⟩
      · exact fun h => h.2
  rw [Nat.card_congr e]
  exact chain_count p hc hp1 (by simpa using hpH) hsh

end Chain

/-! ## 8. W4b: the RAW closed form -/

section CellCardRaw

variable (p : ℕ) [hp : Fact p.Prime]

/-- **W4b, RAW closed form** (blueprint W4 SPEC): the `InCell` fiber of a menu cell has exactly
`prodSC p sh · p^(freeExp s N P)` elements — the per-side residual-shape counts times the
explicit free-digit exponent. -/
theorem cell_card_raw {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    Nat.card {f : QuotientBox.monicBox p N s // InCell p f (mkCell s P sh)}
      = prodSC p sh * p ^ freeExp s N P := by
  classical
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  -- Step 1: InCell = Matches
  have e1 : {f : QuotientBox.monicBox p N s // InCell p f (mkCell s P sh)}
      ≃ {f : QuotientBox.monicBox p N s // Matches p f P sh} :=
    Equiv.subtypeEquivRight fun f => inCell_mkCell_iff p hP hsh
  -- Step 2: Matches = divisibility + digit condition, through the coefficient equivalence
  have e2 : {f : QuotientBox.monicBox p N s // Matches p f P sh}
      ≃ {a : Fin s → ZMod (p ^ N) //
          (∀ i : Fin s, p ^ ceilAt P i.1 ∣ ((a i).val))
            ∧ DigCond p P sh (fun i : Fin s => digit p N (ceilAt P i.1) (a i))} :=
    (coeffEquiv p N s hN).subtypeEquiv fun f => by
      rw [matches_iff p hN hP hsh f]
      rfl
  -- Step 3: pull the divisibility into the coordinate types
  have e3 : {a : Fin s → ZMod (p ^ N) //
        (∀ i : Fin s, p ^ ceilAt P i.1 ∣ ((a i).val))
          ∧ DigCond p P sh (fun i : Fin s => digit p N (ceilAt P i.1) (a i))}
      ≃ {b : ∀ i : Fin s, {x : ZMod (p ^ N) // p ^ ceilAt P i.1 ∣ x.val} //
          DigCond p P sh (fun i : Fin s => digit p N (ceilAt P i.1) (b i).1)} :=
    { toFun := fun a => ⟨fun i => ⟨a.1 i, a.2.1 i⟩, a.2.2⟩
      invFun := fun b => ⟨fun i => (b.1 i).1, fun i => (b.1 i).2, b.2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr (e1.trans (e2.trans e3))]
  -- Step 4: per-coordinate digit fibering
  rw [card_pi_fiber
    (fun (i : Fin s) (x : {x : ZMod (p ^ N) // p ^ ceilAt P i.1 ∣ x.val}) =>
      digit p N (ceilAt P i.1) x.1)
    (fun i => p ^ (N - ceilAt P i.1 - 1))
    (fun i c => card_digit_fiber p (by
      have := menuPath_ceilAt_le hP i.2
      omega) c)
    (DigCond p P sh)]
  -- Step 5: the digit count and the exponent assembly
  rw [digCond_count p hP hsh, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => N - ceilAt P j - 1) s]
  have hsum : ∑ i ∈ Finset.range s, (N - ceilAt P i - 1)
      = ∑ i ∈ Finset.range s, (N - 1 - ceilAt P i) :=
    Finset.sum_congr rfl fun i _ => by omega
  rw [hsum]
  unfold freeExp
  rw [pow_add]
  ring

end CellCardRaw

/-! ## 9. W4a: the cell partition of the readable cluster box -/

section Partition

variable (p : ℕ) [hp : Fact p.Prime]

/-- The cluster condition (exactly the `cell_exists` hypothesis). -/
def IsCluster {N s : ℕ} (f : QuotientBox.monicBox p N s) : Prop :=
  ∀ i, i < s → 1 ≤ vOf p f i

/-- F1-readability: cluster with readable left endpoint (`v_p(a₀) < N`). -/
def IsReadable {N s : ℕ} (f : QuotientBox.monicBox p N s) : Prop :=
  IsCluster p f ∧ vOf p f 0 < N

theorem vOf_le {N s : ℕ} (hN : 0 < N) (f : QuotientBox.monicBox p N s) (i : ℕ) :
    vOf p f i ≤ N := by
  rw [vOf_eq]
  by_cases hx : (f.1).coeff i = 0
  · rw [hx, PadicLift.zmodValuation_zero]
  · exact (PadicLift.zmodValuation_lt p hN hx).le

/-- Every `InCell` fiber sits inside the readable cluster box. -/
theorem inCell_isReadable {N s : ℕ} (hN : 0 < N) {f : QuotientBox.monicBox p N s}
    {c : NodeConfig} (h : InCell p f c) : IsReadable p f := by
  obtain ⟨P, sh, hP, hsh, rfl, hm⟩ := h
  have hdvd := ((matches_iff p hN hP hsh f).mp hm).1
  constructor
  · intro i hi
    have h1 := menuPath_ceilAt_pos hP hi
    have h2 : ceilAt P i ≤ vOf p f i := by
      rw [vOf_eq]
      exact (pow_dvd_val_iff p (by
        have := menuPath_ceilAt_le hP hi
        omega) _).mp (hdvd ⟨i, hi⟩)
    omega
  · obtain ⟨H, p1, T, hPe, hH1, hH2, hp1, hpH, hc⟩ := hP
    have h0 : vOf p f 0 = H := hm.1 (0, H) (by rw [hPe]; simp)
    omega

/-- **W4a, disjointness** (from `cell_unique`): distinct menu cells have disjoint fibers. -/
theorem cell_partition_disjoint {N s : ℕ} {c1 c2 : NodeConfig}
    (h1 : c1 ∈ cellMenu s N) (h2 : c2 ∈ cellMenu s N) (hne : c1 ≠ c2)
    (f : QuotientBox.monicBox p N s) : ¬(InCell p f c1 ∧ InCell p f c2) := by
  rintro ⟨hf1, hf2⟩
  exact hne (cell_unique p f h1 h2 hf1 hf2)

/-- **W4a, coverage** (from `cell_exists` + `cell_unique`): every readable cluster element lies
in exactly one menu-cell fiber. -/
theorem cell_partition_cover {N s : ℕ} (hN : 0 < N) (hs : 0 < s)
    (f : QuotientBox.monicBox p N s) (h : IsReadable p f) :
    ∃! c, c ∈ cellMenu s N ∧ InCell p f c := by
  obtain ⟨c, hcm, hc⟩ := cell_exists p hN hs f h.1 h.2
  exact ⟨c, ⟨hcm, hc⟩, fun c' hc' => cell_unique p f hc'.1 hcm hc'.2 hc⟩

/-- The readable box, fibered by the unique matched menu cell. -/
noncomputable def readableEquivSigma {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    {f : QuotientBox.monicBox p N s // IsReadable p f}
      ≃ Σ c : {c : NodeConfig // c ∈ (cellMenu s N).toFinset},
          {f : QuotientBox.monicBox p N s // InCell p f c.1} where
  toFun f :=
    have hex : ∃ c, InCell p f.1 c := by
      obtain ⟨c, _, hc⟩ := cell_exists p hN hs f.1 f.2.1 f.2.2
      exact ⟨c, hc⟩
    ⟨⟨hex.choose, List.mem_toFinset.mpr (inCell_mem_cellMenu p hex.choose_spec)⟩,
     ⟨f.1, hex.choose_spec⟩⟩
  invFun x := ⟨x.2.1, inCell_isReadable p hN x.2.2⟩
  left_inv f := rfl
  right_inv x := by
    rcases x with ⟨⟨c, hc⟩, f, hf⟩
    have hex : ∃ c', InCell p f c' := ⟨c, hf⟩
    have key : hex.choose = c := inCell_unique p hex.choose_spec hf
    subst key
    rfl

/-- **W4a, card version**: the readable box size is the menu-list sum of the fiber sizes. -/
theorem cell_partition {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s // IsReadable p f}
      = ((cellMenu s N).map fun c =>
          Nat.card {f : QuotientBox.monicBox p N s // InCell p f c}).sum := by
  classical
  rw [Nat.card_congr (readableEquivSigma p hN hs), Nat.card_sigma,
    Finset.sum_coe_sort ((cellMenu s N).toFinset)
      (fun c => Nat.card {f : QuotientBox.monicBox p N s // InCell p f c})]
  exact sum_toFinset_eq_map_sum (nodup_cellMenu s N) _

/-- The cluster-box count `p^(s(N−1))`. -/
theorem card_clusterBox {N s : ℕ} (hN : 0 < N) :
    Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} = p ^ (s * (N - 1)) := by
  have e : {f : QuotientBox.monicBox p N s // IsCluster p f}
      ≃ {a : Fin s → ZMod (p ^ N) // ∀ i, p ^ 1 ∣ ((a i).val)} :=
    (coeffEquiv p N s hN).subtypeEquiv fun f => by
      unfold IsCluster
      constructor
      · intro h i
        have h1 := h i.1 i.2
        rw [vOf_eq] at h1
        exact (pow_dvd_val_iff p hN _).mpr h1
      · intro h i hi
        have h1 := (pow_dvd_val_iff p hN _).mp (h ⟨i, hi⟩)
        rw [vOf_eq]
        exact h1
  rw [Nat.card_congr e, card_dvd_pi p (fun _ => 1) (fun _ => hN)]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The dead-`a₀` cluster count `p^((s−1)(N−1))` (W0's UNMATCHED tail). -/
theorem card_cluster_dead {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f ∧ ¬ vOf p f 0 < N}
      = p ^ ((s - 1) * (N - 1)) := by
  have e : {f : QuotientBox.monicBox p N s // IsCluster p f ∧ ¬ vOf p f 0 < N}
      ≃ {a : Fin s → ZMod (p ^ N) //
          ∀ i, p ^ (if i.1 = 0 then N else 1) ∣ ((a i).val)} :=
    (coeffEquiv p N s hN).subtypeEquiv fun f => by
      constructor
      · rintro ⟨hcl, hdead⟩ i
        by_cases hi0 : i.1 = 0
        · rw [if_pos hi0]
          have hle := vOf_le p hN f 0
          have hveq : vOf p f 0 = N := by omega
          have h1 : N ≤ vOf p f i.1 := by rw [hi0, hveq]
          rw [vOf_eq] at h1
          exact (pow_dvd_val_iff p (le_refl N) _).mpr h1
        · rw [if_neg hi0]
          have h1 := hcl i.1 i.2
          rw [vOf_eq] at h1
          exact (pow_dvd_val_iff p hN _).mpr h1
      · intro h
        constructor
        · intro i hi
          have h1 := h ⟨i, hi⟩
          have h2 : p ^ 1 ∣ (((f.1).coeff i).val) := by
            refine dvd_trans ?_ h1
            apply pow_dvd_pow
            split <;> omega
          rw [vOf_eq]
          exact (pow_dvd_val_iff p hN _).mp h2
        · have h1 : p ^ N ∣ (((f.1).coeff 0).val) := by
            have h1' := h ⟨0, hs⟩
            rwa [if_pos rfl] at h1'
          have h2 : N ≤ PadicLift.zmodValuation p N ((f.1).coeff 0) :=
            (pow_dvd_val_iff p (le_refl N) _).mp h1
          rw [vOf_eq]
          omega
  rw [Nat.card_congr e, card_dvd_pi p _ (fun i => by split <;> omega)]
  congr 1
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  have h0 : N - (if ((0 : Fin (s' + 1)) : ℕ) = 0 then N else 1) = 0 := by simp
  have hstep : ∀ i : Fin s', N - (if ((Fin.succ i : Fin (s' + 1)) : ℕ) = 0 then N else 1)
      = N - 1 := by
    intro i
    rw [if_neg (by simp)]
  rw [h0, zero_add, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel]

/-- **The readable-box count** `p^(s(N−1)) − p^((s−1)(N−1))` (blueprint W4a sanity form). -/
theorem card_readableBox {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s // IsReadable p f}
      = p ^ (s * (N - 1)) - p ^ ((s - 1) * (N - 1)) := by
  have hsplit := card_subtype_and_compl (α := QuotientBox.monicBox p N s)
    (IsCluster p) (fun f => vOf p f 0 < N)
  rw [card_clusterBox p hN, card_cluster_dead p hN hs] at hsplit
  have he : Nat.card {f : QuotientBox.monicBox p N s // IsReadable p f}
      = Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f ∧ vOf p f 0 < N} := rfl
  omega

/-- W0 gate: at `p = 2, N = 3, s = 2` the cluster box has `16` elements. -/
theorem sanity_cluster_s2 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 // IsCluster 2 f} = 16 := by
  rw [card_clusterBox 2 (by norm_num)]
  norm_num

/-- W0 gate: at `p = 2, N = 3, s = 2` the readable box has `12 = 8 + 2 + 2` elements. -/
theorem sanity_readable_s2 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 // IsReadable 2 f} = 12 := by
  rw [card_readableBox 2 (by norm_num) (by norm_num)]
  norm_num

theorem sanity_readable_s3 :
    Nat.card {f : QuotientBox.monicBox 2 3 3 // IsReadable 2 f} = 48 := by
  rw [card_readableBox 2 (by norm_num) (by norm_num)]
  norm_num

theorem sanity_readable_s4 :
    Nat.card {f : QuotientBox.monicBox 2 3 4 // IsReadable 2 f} = 192 := by
  rw [card_readableBox 2 (by norm_num) (by norm_num)]
  norm_num

end Partition

/-! ## 10. Shape counts of the gate shapes, and the mCell tie -/

section ShapeValues

variable (p : ℕ) [hp : Fact p.Prime]

/-- Singleton-shape extraction: a monic polynomial of shape `{(D, μ)}` is the `μ`-th power of a
monic irreducible of degree `D`. -/
theorem polyShape_singleton_extract {D μ : ℕ} (hμ : μ ≠ 0) {M : (ZMod p)[X]} (hmon : M.Monic)
    (hshape : polyShape p M = ({(D, μ)} : Multiset (ℕ × ℕ))) :
    ∃ ψ : (ZMod p)[X], ψ.Monic ∧ Irreducible ψ ∧ ψ.natDegree = D ∧ M = ψ ^ μ := by
  letI := Classical.decEq ((ZMod p)[X])
  unfold CellMenu.polyShape at hshape
  obtain ⟨ψ, hψset, hψpair⟩ := Multiset.map_eq_singleton.mp hshape
  have hdeg : ψ.natDegree = D := (Prod.ext_iff.mp hψpair).1
  have hcount : (UniqueFactorizationMonoid.normalizedFactors M).count ψ = μ :=
    (Prod.ext_iff.mp hψpair).2
  have hmem : ψ ∈ UniqueFactorizationMonoid.normalizedFactors M := by
    rw [← Multiset.count_pos, hcount]
    omega
  have hall : ∀ x ∈ UniqueFactorizationMonoid.normalizedFactors M, x = ψ := by
    intro x hx
    have hx'' : x ∈ (UniqueFactorizationMonoid.normalizedFactors M).toFinset.val :=
      Multiset.mem_toFinset.mpr hx
    rw [hψset] at hx''
    exact Multiset.mem_singleton.mp hx''
  have hrep := Multiset.eq_replicate_of_mem hall
  have hcard : (UniqueFactorizationMonoid.normalizedFactors M).card = μ := by
    rw [hrep, Multiset.count_replicate_self] at hcount
    exact hcount
  rw [hcard] at hrep
  refine ⟨ψ, Order0.monic_of_mem_normalizedFactors hmem,
    UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hmem, hdeg, ?_⟩
  rw [← Order0.prod_normalizedFactors_of_monic hmon, hrep, Multiset.prod_replicate]

/-- `SC([(1, μ)]) = p − 1`: the shape `{(1, μ)}` is exactly `(X + C a)^μ`, `a ≠ 0`. -/
theorem shapeCount_linear_pow {μ : ℕ} (hμ : μ ≠ 0) :
    shapeCount p [(1, μ)] = p - 1 := by
  classical
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have hcard : Nat.card {a : ZMod p // a ≠ 0} = p - 1 := by
    rw [← Nat.card_congr (unitsEquivNeZero (G₀ := ZMod p)), Nat.card_eq_fintype_card]
    exact ZMod.card_units p
  have hbij : Function.Bijective (fun a : {a : ZMod p // a ≠ 0} =>
      (⟨(X + C a.1) ^ μ, (monic_X_add_C a.1).pow μ,
        fun hdvd => a.2 (by
          have h1 := Prime.dvd_of_dvd_pow Polynomial.prime_X hdvd
          rw [Polynomial.X_dvd_iff] at h1
          simpa using h1),
        by
          rw [polyShape_pow_linear p a.1 hμ]
          rfl⟩ :
      {M : (ZMod p)[X] // M.Monic ∧ ¬ X ∣ M
        ∧ polyShape p M = (([(1, μ)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))})) := by
    constructor
    · intro a b hab
      have h1 : (X + C a.1) ^ μ = (X + C b.1) ^ μ := congrArg Subtype.val hab
      have h2 := congrArg (Polynomial.eval (-a.1)) h1
      simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C] at h2
      rw [neg_add_cancel, zero_pow hμ] at h2
      have h3 : -a.1 + b.1 = 0 := pow_eq_zero_iff hμ |>.mp h2.symm
      refine Subtype.ext ?_
      linear_combination -h3
    · rintro ⟨M, hmon, hX, hshape⟩
      have hcoe : (([(1, μ)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))
          = ({(1, μ)} : Multiset (ℕ × ℕ)) := rfl
      rw [hcoe] at hshape
      obtain ⟨ψ, hψmon, hψirr, hψdeg, hMeq⟩ :=
        polyShape_singleton_extract p hμ hmon hshape
      have hψeq : ψ = X + C (ψ.coeff 0) := hψmon.eq_X_add_C hψdeg
      have ha : ψ.coeff 0 ≠ 0 := by
        intro h0
        apply hX
        rw [hMeq, hψeq, h0, map_zero, add_zero]
        exact dvd_pow_self X hμ
      refine ⟨⟨ψ.coeff 0, ha⟩, ?_⟩
      refine Subtype.ext ?_
      show (X + C (ψ.coeff 0)) ^ μ = M
      rw [hMeq, ← hψeq]
  unfold shapeCount
  rw [← Nat.card_eq_of_bijective _ hbij, hcard]

theorem shapeCount_one_one : shapeCount p [(1, 1)] = p - 1 :=
  shapeCount_linear_pow p one_ne_zero

theorem shapeCount_one_two : shapeCount p [(1, 2)] = p - 1 :=
  shapeCount_linear_pow p two_ne_zero

/-- `SC([(2, 1)])` is the monic-irreducible-quadratic count. -/
theorem shapeCount_irred_two :
    shapeCount p [(2, 1)] = Nat.card (L3.monicIrreducibleDegree (ZMod p) 2) := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
  constructor
  · rintro ⟨hmon, hX, hshape⟩
    have hcoe : (([(2, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))
        = ({(2, 1)} : Multiset (ℕ × ℕ)) := rfl
    rw [hcoe] at hshape
    obtain ⟨ψ, hψmon, hψirr, hψdeg, hMeq⟩ :=
      polyShape_singleton_extract p one_ne_zero hmon hshape
    rw [pow_one] at hMeq
    subst hMeq
    exact ⟨hψirr, hψmon, hψdeg⟩
  · rintro ⟨hirr, hmon, hdeg⟩
    refine ⟨hmon, ?_, ?_⟩
    · intro hdvd
      obtain ⟨u, hu⟩ := Polynomial.irreducible_X.associated_of_dvd hirr hdvd
      have h2 : M.natDegree = 1 := by
        rw [← hu, Polynomial.natDegree_mul Polynomial.X_ne_zero (Units.ne_zero u),
          Polynomial.natDegree_X, Polynomial.natDegree_coe_units, add_zero]
      omega
    · rw [polyShape_irreducible_monic p hirr hmon, hdeg]
      rfl

/-- The necklace value `M₂(q) = (q² − q)/2`. -/
theorem necklaceQ_two (q : ℕ) : Necklace.necklaceQ 2 q = ((q : ℚ) ^ 2 - q) / 2 := by
  unfold Necklace.necklaceQ Necklace.necklaceSum
  rw [Nat.Prime.divisors (by norm_num : Nat.Prime 2),
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)]
  push_cast
  norm_num
  ring

/-- Over `F₂` there is exactly ONE monic irreducible quadratic (`y² + y + 1`). -/
theorem card_irred_quad_two : Nat.card (L3.monicIrreducibleDegree (ZMod 2) 2) = 1 := by
  have h := Order0.necklaceQ_eq_card (ZMod 2) 2 (by norm_num)
  rw [Nat.card_zmod, necklaceQ_two] at h
  norm_num at h
  exact_mod_cast h.symm

/-- **The split shape is empty over `F₂`** (W0's readable-but-unhit cell): there is only one
monic linear prime to `X`. -/
theorem shapeCount_split_two : shapeCount 2 [(1, 1), (1, 1)] = 0 := by
  letI := Classical.decEq ((ZMod 2)[X])
  unfold shapeCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨M, hmon, hX, hshape⟩
  unfold CellMenu.polyShape at hshape
  have hcard2 : (UniqueFactorizationMonoid.normalizedFactors M).toFinset.val.card = 2 := by
    have h1 := congrArg Multiset.card hshape
    rw [Multiset.card_map] at h1
    simpa using h1
  obtain ⟨ψ₁, ψ₂, hpair⟩ := Multiset.card_eq_two.mp hcard2
  have hnodup := (UniqueFactorizationMonoid.normalizedFactors M).toFinset.nodup
  rw [hpair] at hnodup
  have hne : ψ₁ ≠ ψ₂ := by
    intro heq
    rw [heq] at hnodup
    simp at hnodup
  have hdeg1 : ∀ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors M).toFinset.val,
      ψ.natDegree = 1 := by
    intro ψ hψ
    have h1 : ((ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors M).count ψ) : ℕ × ℕ)
        ∈ (([(1, 1), (1, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
      rw [← hshape]
      exact Multiset.mem_map_of_mem _ hψ
    have h2 : ((ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors M).count ψ) : ℕ × ℕ)
        = (1, 1) := by
      simpa using h1
    exact (Prod.ext_iff.mp h2).1
  have hlin : ∀ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors M).toFinset.val, ψ = X + 1 := by
    intro ψ hψ
    have hmem : ψ ∈ UniqueFactorizationMonoid.normalizedFactors M := by
      have := hψ
      rwa [Finset.mem_val, Multiset.mem_toFinset] at this
    have hψmon : ψ.Monic := Order0.monic_of_mem_normalizedFactors hmem
    have hψeq : ψ = X + C (ψ.coeff 0) := hψmon.eq_X_add_C (hdeg1 ψ hψ)
    have ha : ψ.coeff 0 ≠ 0 := by
      intro h0
      apply hX
      have : ψ = X := by rw [hψeq, h0, map_zero, add_zero]
      rw [← this]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
    have h1 : ψ.coeff 0 = 1 := by
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact this _ ha
    rw [hψeq, h1, map_one]
  have h1 : ψ₁ = X + 1 := hlin ψ₁ (by rw [hpair]; simp)
  have h2 : ψ₂ = X + 1 := hlin ψ₂ (by rw [hpair]; simp)
  exact hne (h1.trans h2.symm)

/-! ### choicePoly evaluations and the per-shape mCell ties -/

theorem choicePoly_one_mu_eval (μ : ℕ) (x : ℚ) :
    (choicePoly true [(1, μ)]).eval x = x - 1 := by
  unfold OMCountV2.choicePoly OMCountV2.symFactor OMCountV2.faceMus
  norm_num [Order0.ffPoly, Finset.prod_range_one, Nat.factorial]
  rw [show poolPoly true 1 = Order0.availPoly 1 from rfl]
  simp [OMCountV2.availPoly_one_eval]

theorem choicePoly_two_one_eval (x : ℚ) :
    (choicePoly true [(2, 1)]).eval x = (x ^ 2 - x) / 2 := by
  unfold OMCountV2.choicePoly OMCountV2.symFactor OMCountV2.faceMus
  norm_num [Order0.ffPoly, Finset.prod_range_one, Nat.factorial]
  rw [show poolPoly true 2 = Order0.availPoly 2 from rfl]
  simp [OMCountV2.availPoly_two_eval]

theorem choicePoly_split_eval (x : ℚ) :
    (choicePoly true [(1, 1), (1, 1)]).eval x = (x - 1) * (x - 1 - 1) / 2 := by
  unfold OMCountV2.choicePoly OMCountV2.symFactor OMCountV2.faceMus
  norm_num [Order0.ffPoly, Finset.prod_range_succ, Finset.prod_range_one, Nat.factorial]
  rw [show poolPoly true 1 = Order0.availPoly 1 from rfl]
  simp [OMCountV2.availPoly_one_eval]
  ring

/-- The `[(1,1)]` mCell tie. -/
theorem shapeCount_tie_one_one :
    ((shapeCount p [(1, 1)] : ℕ) : ℚ) = (choicePoly true [(1, 1)]).eval (p : ℚ) := by
  rw [shapeCount_one_one, OMCountV2.choicePoly_halfCluster_eval,
    Nat.cast_sub hp.out.one_lt.le, Nat.cast_one]

/-- The `[(1,2)]` mCell tie. -/
theorem shapeCount_tie_one_two :
    ((shapeCount p [(1, 2)] : ℕ) : ℚ) = (choicePoly true [(1, 2)]).eval (p : ℚ) := by
  rw [shapeCount_one_two, choicePoly_one_mu_eval,
    Nat.cast_sub hp.out.one_lt.le, Nat.cast_one]

/-- The `[(2,1)]` mCell tie (through `necklaceQ_eq_card`, the β2a cross-tie). -/
theorem shapeCount_tie_two_one :
    ((shapeCount p [(2, 1)] : ℕ) : ℚ) = (choicePoly true [(2, 1)]).eval (p : ℚ) := by
  rw [shapeCount_irred_two, choicePoly_two_one_eval]
  have h := Order0.necklaceQ_eq_card (ZMod p) 2 (by norm_num)
  rw [Nat.card_zmod, necklaceQ_two] at h
  exact h.symm

/-- The `[(1,1),(1,1)]` mCell tie at `p = 2` (both sides vanish). -/
theorem shapeCount_tie_split_two :
    ((shapeCount 2 [(1, 1), (1, 1)] : ℕ) : ℚ)
      = (choicePoly true [(1, 1), (1, 1)]).eval (2 : ℚ) := by
  rw [shapeCount_split_two, choicePoly_split_eval]
  norm_num

/-- `mCell` of a menu cell is the product of the per-side choice-polynomial values. -/
theorem map_eval_zipWith_mkFace (q : ℚ) :
    ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ))), sh.length = prs.length →
      (List.zipWith mkFace prs sh).map
          (fun F => (choicePoly F.punctured F.shape).eval (q ^ F.δ))
        = sh.map fun l => (choicePoly true l).eval q := by
  intro prs
  induction prs with
  | nil =>
      intro sh h
      rw [List.length_nil, List.length_eq_zero_iff] at h
      simp [h]
  | cons pr prs ih =>
      intro sh h
      cases sh with
      | nil => simp
      | cons l sh' =>
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [ih sh' (by simpa using h)]
          congr 1
          show (choicePoly (mkFace pr l).punctured (mkFace pr l).shape).eval
              (q ^ (mkFace pr l).δ) = _
          rw [show (mkFace pr l).punctured = true from rfl,
            show (mkFace pr l).shape = l from rfl,
            show (mkFace pr l).δ = 1 from rfl, pow_one]

theorem mCell_mkCell {s : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    (hlen : sh.length = (sidePairs P).length) (q : ℕ) :
    mCell (mkCell s P sh) q = (sh.map fun l => (choicePoly true l).eval (q : ℚ)).prod := by
  show ((List.zipWith mkFace (sidePairs P) sh).map
      (fun F => (choicePoly F.punctured F.shape).eval ((q : ℚ) ^ F.δ))).prod = _
  rw [map_eval_zipWith_mkFace (q : ℚ) (sidePairs P) sh hlen]

/-- **W4b, mCell form** (the blueprint headline `mCell c p · p^freeExp`), for cells all of whose
side shapes have a banked `shapeCount = choicePoly` tie (all gate shapes are banked; the fully
general tie is the sanctioned partial-banking remainder). -/
theorem cell_card_mCell {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh)
    (hties : ∀ l ∈ sh, ((shapeCount p l : ℕ) : ℚ) = (choicePoly true l).eval (p : ℚ)) :
    (Nat.card {f : QuotientBox.monicBox p N s // InCell p f (mkCell s P sh)} : ℚ)
      = mCell (mkCell s P sh) p * (p : ℚ) ^ freeExp s N P := by
  rw [cell_card_raw p hN hP hsh, Nat.cast_mul, Nat.cast_pow,
    mCell_mkCell hsh.length_eq p]
  congr 1
  unfold prodSC
  rw [Nat.cast_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun l hl => hties l hl)

end ShapeValues

/-! ## 11. THE W0 GATES (mandatory; `SUMMARY.md` per-cell census, ground truth) -/

section Gates

theorem menuPath_s2a : MenuPath 2 3 [(0, 1), (2, 0)] :=
  ⟨1, (2, 0), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem menuPath_s2b : MenuPath 2 3 [(0, 2), (2, 0)] :=
  ⟨2, (2, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem menuPath_s3a : MenuPath 3 3 [(0, 1), (3, 0)] :=
  ⟨1, (3, 0), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem menuPath_s3c : MenuPath 3 3 [(0, 2), (1, 1), (3, 0)] :=
  ⟨2, (1, 1), [(3, 0)], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
    ChainOK.cons (by norm_num) (by norm_num) (by decide) (ChainOK.nil rfl rfl)⟩

theorem menuPath_s4a : MenuPath 4 3 [(0, 1), (4, 0)] :=
  ⟨1, (4, 0), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num, ChainOK.nil rfl rfl⟩

theorem shapes_s2a : ShapesFor [(0, 1), (2, 0)] [[(1, 1)]] := by
  show List.Forall₂ _ [[(1, 1)]] [((0, 1), (2, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_s2b1 : ShapesFor [(0, 2), (2, 0)] [[(1, 2)]] := by
  show List.Forall₂ _ [[(1, 2)]] [((0, 2), (2, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_s2b2 : ShapesFor [(0, 2), (2, 0)] [[(2, 1)]] := by
  show List.Forall₂ _ [[(2, 1)]] [((0, 2), (2, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_s2b3 : ShapesFor [(0, 2), (2, 0)] [[(1, 1), (1, 1)]] := by
  show List.Forall₂ _ [[(1, 1), (1, 1)]] [((0, 2), (2, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_s3a : ShapesFor [(0, 1), (3, 0)] [[(1, 1)]] := by
  show List.Forall₂ _ [[(1, 1)]] [((0, 1), (3, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

theorem shapes_s3c : ShapesFor [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]] := by
  show List.Forall₂ _ [[(1, 1)], [(1, 1)]] [((0, 2), (1, 1)), ((1, 1), (3, 0))]
  exact List.Forall₂.cons (by decide) (List.Forall₂.cons (by decide) List.Forall₂.nil)

theorem shapes_s4a : ShapesFor [(0, 1), (4, 0)] [[(1, 1)]] := by
  show List.Forall₂ _ [[(1, 1)]] [((0, 1), (4, 0))]
  exact List.Forall₂.cons (by decide) List.Forall₂.nil

/-- **W0 GATE S2C1** (slope −1/2, shape `{(1,1)}`): total match count `8`. -/
theorem gate_card_S2C1 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 //
        InCell 2 f (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]])} = 8 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s2a shapes_s2a,
    show freeExp 2 3 [(0, 1), (2, 0)] = 3 from by decide,
    show prodSC 2 [[(1, 1)]] = 1 from by simp [prodSC, shapeCount_one_one]]
  norm_num

/-- **W0 GATE S2C2** (the SELF-LOOP cell, slope −1, shape `{(1,2)}`): total match count `2`. -/
theorem gate_card_S2C2 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 //
        InCell 2 f (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]])} = 2 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s2b shapes_s2b1,
    show freeExp 2 3 [(0, 2), (2, 0)] = 1 from by decide,
    show prodSC 2 [[(1, 2)]] = 1 from by simp [prodSC, shapeCount_one_two]]
  norm_num

/-- **W0 GATE S2C3** (slope −1, inert-quadratic shape `{(2,1)}`): total match count `2`. -/
theorem gate_card_S2C3 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 //
        InCell 2 f (mkCell 2 [(0, 2), (2, 0)] [[(2, 1)]])} = 2 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s2b shapes_s2b2,
    show freeExp 2 3 [(0, 2), (2, 0)] = 1 from by decide,
    show prodSC 2 [[(2, 1)]] = 1 from by
      unfold prodSC
      rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        shapeCount_irred_two, card_irred_quad_two]]
  norm_num

/-- **W0 GATE, the split cell** (readable-but-unhit at `p = 2`): total match count `0`. -/
theorem gate_card_S2split :
    Nat.card {f : QuotientBox.monicBox 2 3 2 //
        InCell 2 f (mkCell 2 [(0, 2), (2, 0)] [[(1, 1), (1, 1)]])} = 0 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s2b shapes_s2b3,
    show prodSC 2 [[(1, 1), (1, 1)]] = 0 from by simp [prodSC, shapeCount_split_two]]
  norm_num

/-- **W0 GATE S3C1** (s = 3, slope −1/3, shape `{(1,1)}`): total match count `32`. -/
theorem gate_card_S3C1 :
    Nat.card {f : QuotientBox.monicBox 2 3 3 //
        InCell 2 f (mkCell 3 [(0, 1), (3, 0)] [[(1, 1)]])} = 32 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s3a shapes_s3a,
    show freeExp 3 3 [(0, 1), (3, 0)] = 5 from by decide,
    show prodSC 2 [[(1, 1)]] = 1 from by simp [prodSC, shapeCount_one_one]]
  norm_num

/-- **W0 GATE S3C3** (s = 3, the two-sided polygon `(0,2)→(1,1)→(3,0)`): total match count `8`. -/
theorem gate_card_S3C3 :
    Nat.card {f : QuotientBox.monicBox 2 3 3 //
        InCell 2 f (mkCell 3 [(0, 2), (1, 1), (3, 0)] [[(1, 1)], [(1, 1)]])} = 8 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s3c shapes_s3c,
    show freeExp 3 3 [(0, 2), (1, 1), (3, 0)] = 3 from by decide,
    show prodSC 2 [[(1, 1)], [(1, 1)]] = 1 from by simp [prodSC, shapeCount_one_one]]
  norm_num

/-- **W0 GATE S4C1** (s = 4, slope −1/4, shape `{(1,1)}`): total match count `128`. -/
theorem gate_card_S4C1 :
    Nat.card {f : QuotientBox.monicBox 2 3 4 //
        InCell 2 f (mkCell 4 [(0, 1), (4, 0)] [[(1, 1)]])} = 128 := by
  rw [cell_card_raw 2 (by norm_num) menuPath_s4a shapes_s4a,
    show freeExp 4 3 [(0, 1), (4, 0)] = 7 from by decide,
    show prodSC 2 [[(1, 1)]] = 1 from by simp [prodSC, shapeCount_one_one]]
  norm_num

/-- The headline mCell form at the S2C1 gate: `#fiber = mCell · p^freeExp` with genuine
`OMCountV2.mCell`. -/
theorem gate_mCell_S2C1 :
    (Nat.card {f : QuotientBox.monicBox 2 3 2 //
        InCell 2 f (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]])} : ℚ)
      = mCell (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) 2
          * (2 : ℚ) ^ freeExp 2 3 [(0, 1), (2, 0)] := by
  refine cell_card_mCell 2 (by norm_num) menuPath_s2a shapes_s2a ?_
  intro l hl
  rw [show l = [(1, 1)] from by simpa using hl]
  exact shapeCount_tie_one_one 2

/-! ## 12. The consistency corollary (deliverable 3) -/

/-- **Consistency, partition side**: Σ over the s=2 menu of the fiber counts = 12 = #readable. -/
theorem consistency_s2 :
    ((cellMenu 2 3).map fun c =>
        Nat.card {f : QuotientBox.monicBox 2 3 2 // InCell 2 f c}).sum = 12 := by
  rw [← cell_partition 2 (by norm_num) (by norm_num), sanity_readable_s2]

theorem consistency_s3 :
    ((cellMenu 3 3).map fun c =>
        Nat.card {f : QuotientBox.monicBox 2 3 3 // InCell 2 f c}).sum = 48 := by
  rw [← cell_partition 2 (by norm_num) (by norm_num), sanity_readable_s3]

theorem consistency_s4 :
    ((cellMenu 4 3).map fun c =>
        Nat.card {f : QuotientBox.monicBox 2 3 4 // InCell 2 f c}).sum = 192 := by
  rw [← cell_partition 2 (by norm_num) (by norm_num), sanity_readable_s4]

/-- **Consistency, closed-form side**: the same s=2 menu sum, evaluated cell by cell through the
W4b closed form, is `8 + 2 + 2 + 0` — matching W0's census row by row. -/
theorem consistency_cells_s2 :
    ((cellMenu 2 3).map fun c =>
        Nat.card {f : QuotientBox.monicBox 2 3 2 // InCell 2 f c}).sum = 8 + (0 + (2 + (2 + 0))) := by
  have hmenu : cellMenu 2 3
      = (menuPaths 2 3).flatMap fun P => (shapeAssignments P).map (mkCell 2 P) := rfl
  rw [hmenu, show menuPaths 2 3 = [[(0, 1), (2, 0)], [(0, 2), (2, 0)]] from by decide]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [show shapeAssignments [(0, 1), (2, 0)] = [[[(1, 1)]]] from by decide,
    show shapeAssignments [(0, 2), (2, 0)]
      = [[[(1, 1), (1, 1)]], [[(1, 2)]], [[(2, 1)]]] from by decide]
  simp only [List.map_cons, List.map_nil, List.append_nil, List.map_append,
    List.sum_append, List.sum_cons, List.sum_nil]
  rw [gate_card_S2C1, gate_card_S2split, gate_card_S2C2, gate_card_S2C3]
  omega

example : (8 + (0 + (2 + (2 + 0))) : ℕ) = 12 := by norm_num

end Gates

end LeanUrat.OM.CellCard
