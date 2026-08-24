/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C127
import Uniformity.ChapC.C131h
import Uniformity.ChapC.C131m

/-!
# Uniformity.ChapC.C131n — upward recarry and the census floor

**Chapter C, NODES C.131n′–o′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.7 and §5).

## C.131n′ — recarry arithmetic (F9) and upward transport (F10)

Lemma F9 (`recarry_price`) is stated with the order hypotheses `j′ ≤ j ≤ μ₂` and `1 ≤ k`
visible, the guarded decomposition `(μ₂ − j′) = (μ₂ − j) + (j − j′)` proved first, and the
no-truncation lemma recorded explicitly, exactly as v2 §2.7 requires: the natural
subtraction `(μ₂ − j′)E₂ + kδ − (j − j′)E₂` is only ever consumed through the exact
cancellation `recarry_cancel`.

Lemma F10 (`recarry_moves_up`/`recarry_never_down`) is the upward transport of the
`devQ` coordinate under key absorption: absorbing one monic outer-key factor moves the
development coordinate from `j` to `j + 1` (`recarry_moves_up_one`), iterated absorption
moves it up by exactly `r`, and every coordinate below `r` reads zero — never a smaller
index.  These are thin public wrappers over C.127's generic `devQ` API (`devQ_mul_pow`,
`devQ_mul_pow_of_lt`), stated over an arbitrary commutative ring so they apply both at
`K_T` in `O[x][Y]` and at the transported key inside `(O[x]/Φ′)[Z]`.  The file also ties
C.71's front-recursive `devQ` to C.131h′'s end-recursive ledger tower
(`devQ_eq_quotDigit`), so the division ledger F6–F8 is available at `devQ` coordinates.

## C.131o′ — the census floor F11

`PaidFloor T base t` is v2 §2.6's pricing invariant on one tagged contribution: a term
with `paid = k` lies at weight at least `base + k·δ`.  The file proves the invariant's
transport through every census move —

* `xCarryStep_paidFloor`: both branches of one `x`-carry satisfy the invariant at the
  pre-carry monomial weight (tail keeps the tag, the `Y` branch pays exactly `δ`);
* `paidFloor_preserve`: multiplication by a floor-bounded tail contribution adds weights;
* `paidFloor_transport` (+ digit form): absorbing `j − j′` outer-key factors moves a
  contribution from coordinate `j′` to `j` and keeps the invariant at the new coordinate
  (F6 iterated, priced by F9's cancellation — "F9 pays for each absorbed outer-key
  factor and leaves at least one `δ`");

— and the two floor conclusions:

* ★ `census_floor` (**F11, parameterized**): any finite tagged census at coordinate `j`
  with all tags `≥ 1` and the invariant at base `(μ₂ − j)E₂` has, after erasure, every
  scalar monomial at weight at least `Θ_j = T.theta μ₂ j`;
* ★ `census_digit_floor` (F11, forward-fed form): an entry census at base `μ₂E₂` with all
  tags `≥ 1` keeps the `Θ_j` floor at every ledger digit `j ≤ μ₂` of its erased sum.

**Honest scope.**  F11's subject — "the structurally computed normal form of the
shadow/honest discrepancy" — is here a *hypothesis*: the theorems quantify over any
tagged list satisfying the entry ledger and paid-tag conditions.  The corpus does not yet
contain the concrete tagged-census discrepancy object (the missing object already named
by `runs/wave-b/verdict_C131u.md`; its semantic identification Cnv13 is node C.131v′,
in flight).  Instantiating `census_floor` at that object is exactly what C.131w′
(`shadow_floor`) will do; no claim about `shadowDev T f j − dev (composedKey T) f j`
is made in this file.

## Status

Sorry-free and axiom-free (Lean core only).  No new definitions except the invariant
carrier `PaidFloor`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131n

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131f
open Uniformity.Density.Tower.C131h Uniformity.Density.Tower.C131m

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## C.131n′, part 1 — F9: guarded recarry arithmetic -/

/-- The guarded decomposition behind F9: under `j′ ≤ j ≤ μ₂` the coefficient
`(μ₂ − j′)` splits exactly, before any distribution over the price `E`. -/
theorem recarry_decomp {μ₂ j j' : ℕ} (h1 : j' ≤ j) (h2 : j ≤ μ₂) (E : ℕ) :
    (μ₂ - j') * E = (μ₂ - j) * E + (j - j') * E := by
  have hdec : μ₂ - j' = (μ₂ - j) + (j - j') := by omega
  rw [hdec, Nat.add_mul]

/-- The explicit no-truncation lemma of v2 §2.7 (finding #7): the recarry subtraction
never exceeds the incoming floor, so the `ℕ`-subtraction in F9 is exact. -/
theorem recarry_no_truncation {μ₂ j j' : ℕ} (h1 : j' ≤ j) (h2 : j ≤ μ₂) (E k d : ℕ) :
    (j - j') * E ≤ (μ₂ - j') * E + k * d := by
  rw [recarry_decomp h1 h2 E]
  calc (j - j') * E ≤ (μ₂ - j) * E + (j - j') * E := Nat.le_add_left _ _
    _ ≤ (μ₂ - j) * E + (j - j') * E + k * d := Nat.le_add_right _ _

/-- The exact cancellation in F9's display: paying `(j − j′)` recarry prices out of the
birth floor leaves exactly the floor at the new coordinate, tag untouched. -/
theorem recarry_cancel {μ₂ j j' k E d : ℕ} (h1 : j' ≤ j) (h2 : j ≤ μ₂) :
    (μ₂ - j') * E + k * d - (j - j') * E = (μ₂ - j) * E + k * d := by
  rw [recarry_decomp h1 h2 E]
  have hcomm : (μ₂ - j) * E + (j - j') * E + k * d
      = (μ₂ - j) * E + k * d + (j - j') * E := by ring
  rw [hcomm, Nat.add_sub_cancel]

/-- One paid tag suffices for the threshold: `Θ_j = (μ₂ − j)E₂ + δ ≤ (μ₂ − j)E₂ + kδ`
whenever `1 ≤ k`.  This is the census's per-contribution arithmetic step. -/
theorem theta_le_floor_add_paid (T : TowerDatum F H₀ hpin) (μ₂ j : ℕ) {k : ℕ}
    (hk : 1 ≤ k) :
    T.theta μ₂ j ≤ (μ₂ - j) * T.E₂ + k * T.margin := by
  have h : T.margin ≤ k * T.margin := by
    simpa using Nat.mul_le_mul_right T.margin hk
  simp only [TowerDatum.theta]
  exact Nat.add_le_add_left h _

/-- **NODE C.131n′ (F9, `recarry_price`).**  With the order hypotheses `j′ ≤ j ≤ μ₂` and
`1 ≤ k` visible, the recarried paid floor stays above the threshold:
`Θ_j ≤ (μ₂ − j′)E₂ + kδ − (j − j′)E₂`. -/
theorem recarry_price (T : TowerDatum F H₀ hpin) {μ₂ j j' k : ℕ}
    (h1 : j' ≤ j) (h2 : j ≤ μ₂) (hk : 1 ≤ k) :
    T.theta μ₂ j ≤ (μ₂ - j') * T.E₂ + k * T.margin - (j - j') * T.E₂ := by
  rw [recarry_cancel h1 h2]
  exact theta_le_floor_add_paid T μ₂ j hk

/-! ## C.131n′, part 2 — F10: absorption moves the coordinate up, never down

Thin public wrappers over C.127's generic `devQ` API, in the ring-generic form both key
levels need. -/

/-- Absorbing one monic key factor erases the coordinate-`0` digit. -/
theorem recarry_step_zero {R : Type*} [CommRing R] {K : Polynomial R} (hK : K.Monic)
    (P : Polynomial R) : devQ K (K * P) 0 = 0 :=
  Polynomial.self_mul_modByMonic hK

/-- **F10, one step.**  Absorbing one monic key factor moves the development coordinate
from `j` to `j + 1`. -/
theorem recarry_moves_up_one {R : Type*} [CommRing R] {K : Polynomial R} (hK : K.Monic)
    (P : Polynomial R) (j : ℕ) : devQ K (K * P) (j + 1) = devQ K P j := by
  have h := devQ_mul_pow hK 1 P j
  rwa [pow_one, mul_comm P K, Nat.add_comm 1 j] at h

/-- **NODE C.131n′ (F10, `recarry_moves_up`).**  Iterated absorption of `r` monic key
factors moves every development coordinate up by exactly `r`. -/
theorem recarry_moves_up {R : Type*} [CommRing R] {K : Polynomial R} (hK : K.Monic)
    (P : Polynomial R) (r j : ℕ) :
    devQ K (K ^ r * P) (j + r) = devQ K P j := by
  have h := devQ_mul_pow hK r P j
  rwa [mul_comm P (K ^ r), Nat.add_comm r j] at h

/-- **F10, downward fence.**  Absorption never moves a contribution to a smaller index:
all development coordinates below the absorbed power read zero. -/
theorem recarry_never_down {R : Type*} [CommRing R] {K : Polynomial R} (hK : K.Monic)
    (P : Polynomial R) {r j : ℕ} (hj : j < r) :
    devQ K (K ^ r * P) j = 0 := by
  have h := devQ_mul_pow_of_lt hK r P j hj
  rwa [mul_comm P (K ^ r)] at h

/-! ## C.131n′, part 3 — tying C.71's `devQ` to C.131h′'s ledger tower

C.71's `devQ` recurses at the front (`g ↦ g /ₘ Ψ` first); C.131h′'s `quotIter` recurses
at the end.  The two agree, so the division ledger F6–F8 prices `devQ` coordinates. -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The front- and end-recursions of the quotient tower commute past one division. -/
theorem quotIter_divByMonic_comm (K P : Polynomial (Polynomial O)) (j : ℕ) :
    quotIter K (P /ₘ K) j = quotIter K P j /ₘ K := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show quotIter K (P /ₘ K) j /ₘ K = _
      rw [ih]
      rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- C.71's development coordinate IS the ledger digit of C.131h′, at every index. -/
theorem devQ_eq_quotDigit (K : Polynomial (Polynomial O)) :
    ∀ (j : ℕ) (P : Polynomial (Polynomial O)), devQ K P j = quotDigit K P j := by
  intro j
  induction j with
  | zero => intro P; rfl
  | succ j ih =>
      intro P
      show devQ K (P /ₘ K) j = _
      rw [ih (P /ₘ K)]
      unfold quotDigit
      rw [quotIter_divByMonic_comm]
      rfl

/-! ## C.131n′, part 4 — the ledger at an arbitrary incoming floor

F8 as landed starts at the exact multiple `μE₂`; the census feeds contributions forward
at floors of the form `base + kδ`, so the quotient/digit bounds are recorded at an
arbitrary natural floor `w`. -/

/-- Generalized quotient half of the ledger: each absorbed outer-key factor costs at
most `E₂` off any incoming floor. -/
theorem quotIter_floor_of_le (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (w : ℕ) (P : Polynomial (Polynomial O)) (hP : (w : ℕ∞) ≤ WT T P) :
    ∀ i : ℕ, ((w - i * T.E₂ : ℕ) : ℕ∞) ≤ WT T (quotIter (K_T T) P i)
  | 0 => by simpa [quotIter] using hP
  | i + 1 => by
      have ih := quotIter_floor_of_le T hπ w P hP i
      have hstep := WT_divByMonic_ge_sub T hπ (w - i * T.E₂) _ ih
      have harith : w - i * T.E₂ - T.E₂ = w - (i + 1) * T.E₂ := by
        rw [Nat.sub_sub, ← Nat.succ_mul]
      simpa [quotIter, harith] using hstep

/-- Generalized remainder half of the ledger: the digit at depth `i` keeps the quotient
floor `w − iE₂`. -/
theorem quotDigit_floor_of_le (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (w : ℕ) (P : Polynomial (Polynomial O)) (hP : (w : ℕ∞) ≤ WT T P) (i : ℕ) :
    ((w - i * T.E₂ : ℕ) : ℕ∞) ≤ WT T (quotDigit (K_T T) P i) := by
  unfold quotDigit
  exact WT_modByMonic_ge T hπ _ _ (quotIter_floor_of_le T hπ w P hP i)

/-! ## C.131o′ — the census floor F11 -/

/-- v2 §2.6's pricing invariant on one tagged contribution: a term with `paid = k` lies
at weight at least `base + k·δ`.  The base is the coordinate floor supplied by the
ledger; the tag counts paid `Y` branches. -/
def PaidFloor (T : TowerDatum F H₀ hpin) (base : ℕ)
    (t : TaggedTerm (Polynomial (Polynomial O))) : Prop :=
  ((base + t.paid * T.margin : ℕ) : ℕ∞) ≤ WT T t.term

/-- Weakening the base preserves the invariant. -/
theorem paidFloor_mono (T : TowerDatum F H₀ hpin) {base' base : ℕ} (h : base' ≤ base)
    {t : TaggedTerm (Polynomial (Polynomial O))} (ht : PaidFloor T base t) :
    PaidFloor T base' t := by
  unfold PaidFloor at ht ⊢
  exact le_trans (by exact_mod_cast Nat.add_le_add_right h _) ht

/-- A uniform weight floor on every tagged contribution passes through erasure: the
erased finite sum keeps the floor (ultrametricity, term by term). -/
theorem le_WT_eraseTagged (T : TowerDatum F H₀ hpin) {w : ℕ∞}
    {ts : List (TaggedTerm (Polynomial (Polynomial O)))}
    (h : ∀ t ∈ ts, w ≤ WT T t.term) : w ≤ WT T (eraseTagged ts) := by
  induction ts with
  | nil => simp [eraseTagged]
  | cons t ts ih =>
      show w ≤ WT T (t.term + eraseTagged ts)
      exact le_trans (le_min (h t List.mem_cons_self)
        (ih fun s hs => h s (List.mem_cons_of_mem t hs))) (WT_add T _ _)

/-- One paid contribution at the coordinate floor already clears the threshold `Θ_j`. -/
theorem theta_le_WT_of_paidFloor (T : TowerDatum F H₀ hpin) {μ₂ j : ℕ}
    {t : TaggedTerm (Polynomial (Polynomial O))} (hk : 1 ≤ t.paid)
    (ht : PaidFloor T ((μ₂ - j) * T.E₂) t) :
    (T.theta μ₂ j : ℕ∞) ≤ WT T t.term := by
  unfold PaidFloor at ht
  refine le_trans ?_ ht
  exact_mod_cast theta_le_floor_add_paid T μ₂ j hk

/-- ★ **NODE C.131o′ (F11, parameterized census floor).**  Any finite tagged census at
coordinate `j` whose contributions all carry a paid tag (`1 ≤ paid`) and the pricing
invariant at the ledger base `(μ₂ − j)E₂` has, after tag erasure, every scalar monomial
at weight at least `Θ_j = T.theta μ₂ j`.

The census list is a hypothesis: instantiating it at the tagged-census discrepancy
normal form (node C.131v′, Cnv13) is C.131w′'s `shadow_floor` splice. -/
theorem census_floor (T : TowerDatum F H₀ hpin) (μ₂ j : ℕ)
    {ts : List (TaggedTerm (Polynomial (Polynomial O)))}
    (hpaid : ∀ t ∈ ts, 1 ≤ t.paid)
    (hfloor : ∀ t ∈ ts, PaidFloor T ((μ₂ - j) * T.E₂) t) :
    (T.theta μ₂ j : ℕ∞) ≤ WT T (eraseTagged ts) :=
  le_WT_eraseTagged T fun t ht => theta_le_WT_of_paidFloor T (hpaid t ht) (hfloor t ht)

/-! ### Transport of the invariant through the census moves -/

/-- Multiplying by a tail contribution of known floor adds the floors and preserves the
tag (§2.6's tag-preserving branch, priced by `WT_mul`). -/
theorem paidFloor_preserve (T : TowerDatum F H₀ hpin) {v base : ℕ}
    {r : Polynomial (Polynomial O)} (hr : (v : ℕ∞) ≤ WT T r)
    {t : TaggedTerm (Polynomial (Polynomial O))} (ht : PaidFloor T base t) :
    PaidFloor T (v + base) (preserve r t) := by
  unfold PaidFloor at ht ⊢
  show ((v + base + t.paid * T.margin : ℕ) : ℕ∞) ≤ WT T (r * t.term)
  refine le_trans ?_ (WT_mul T r t.term)
  calc ((v + base + t.paid * T.margin : ℕ) : ℕ∞)
      = (v : ℕ∞) + ((base + t.paid * T.margin : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ WT T r + WT T t.term := add_le_add hr ht

/-- Both branches of one `x`-carry satisfy the invariant at the pre-carry monomial
weight `D′e₂h + a₀e₂h + bu₂`: the tail branch keeps tag `0` and the full key-side floor,
the `Y` branch has tag `1` and gains exactly `δ` (C.131e′'s exact branch weight). -/
theorem xCarryStep_paidFloor (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    ∀ t ∈ xCarryStep T a₀ b,
      PaidFloor T ((F.e₁ * F.f₁) * T.e₂ * F.h + a₀ * (T.e₂ * F.h) + b * T.u₂) t := by
  intro t ht
  rw [xCarryStep_eq, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl
  · unfold PaidFloor
    rw [(xCarryStep_tags T a₀ b).1]
    simpa using xCarryStep_tail_floor T a₀ b
  · unfold PaidFloor
    rw [(xCarryStep_tags T a₀ b).2, xCarryStep_paid_WT T a₀ b]
    have hbase : (F.e₁ * F.f₁) * T.e₂ * F.h + a₀ * (T.e₂ * F.h) + b * T.u₂ +
        1 * T.margin =
        a₀ * (T.e₂ * F.h) + b * T.u₂ +
          (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) := by ring
    rw [hbase]

/-- **The F9+F10+F6 splice.**  Absorbing `j − j′` outer-key factors moves a paid
contribution from birth coordinate `j′` up to coordinate `j` and keeps the pricing
invariant at the new ledger base: each absorbed factor is paid for by `recarry_cancel`,
and the tag — hence at least one `δ` — survives. -/
theorem paidFloor_transport (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ j j' : ℕ} (h1 : j' ≤ j) (h2 : j ≤ μ₂)
    {t : TaggedTerm (Polynomial (Polynomial O))}
    (ht : PaidFloor T ((μ₂ - j') * T.E₂) t) :
    PaidFloor T ((μ₂ - j) * T.E₂)
      ⟨t.paid, quotIter (K_T T) t.term (j - j')⟩ := by
  unfold PaidFloor at ht ⊢
  have h := quotIter_floor_of_le T hπ ((μ₂ - j') * T.E₂ + t.paid * T.margin)
    t.term ht (j - j')
  rwa [recarry_cancel h1 h2] at h

/-- Digit form of the transport: the ledger digit read after absorption keeps the
transported invariant as well. -/
theorem paidFloor_transport_digit (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ j j' : ℕ} (h1 : j' ≤ j) (h2 : j ≤ μ₂)
    {t : TaggedTerm (Polynomial (Polynomial O))}
    (ht : PaidFloor T ((μ₂ - j') * T.E₂) t) :
    PaidFloor T ((μ₂ - j) * T.E₂)
      ⟨t.paid, quotDigit (K_T T) t.term (j - j')⟩ := by
  unfold PaidFloor at ht ⊢
  have h := quotDigit_floor_of_le T hπ ((μ₂ - j') * T.E₂ + t.paid * T.margin)
    t.term ht (j - j')
  rwa [recarry_cancel h1 h2] at h

/-- ★ **C.131o′, forward-fed form of F11.**  An entry census at the full ledger base
`μ₂E₂` with every tag paid keeps the threshold floor at every ledger digit `j ≤ μ₂` of
its erased sum: "forward feeding is another application of F6–F8 to a contribution
already carrying the invariant". -/
theorem census_digit_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ j : ℕ} (hj : j ≤ μ₂)
    {ts : List (TaggedTerm (Polynomial (Polynomial O)))}
    (hpaid : ∀ t ∈ ts, 1 ≤ t.paid)
    (hfloor : ∀ t ∈ ts, PaidFloor T (μ₂ * T.E₂) t) :
    (T.theta μ₂ j : ℕ∞) ≤ WT T (quotDigit (K_T T) (eraseTagged ts) j) := by
  have hsum : ((μ₂ * T.E₂ + T.margin : ℕ) : ℕ∞) ≤ WT T (eraseTagged ts) := by
    refine le_WT_eraseTagged T fun t ht => ?_
    have h1 := hfloor t ht
    unfold PaidFloor at h1
    refine le_trans ?_ h1
    have h2 : T.margin ≤ t.paid * T.margin := by
      simpa using Nat.mul_le_mul_right T.margin (hpaid t ht)
    exact_mod_cast Nat.add_le_add_left h2 _
  have h := quotDigit_floor_of_le T hπ (μ₂ * T.E₂ + T.margin) (eraseTagged ts) hsum j
  have harith : μ₂ * T.E₂ + T.margin - j * T.E₂ = T.theta μ₂ j := by
    have hle : j * T.E₂ ≤ μ₂ * T.E₂ := Nat.mul_le_mul_right T.E₂ hj
    simp only [TowerDatum.theta, Nat.sub_mul]
    rw [Nat.sub_add_comm hle]
  rwa [harith] at h

end Uniformity.Density.Tower.C131n

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131n.recarry_decomp
#print axioms Uniformity.Density.Tower.C131n.recarry_no_truncation
#print axioms Uniformity.Density.Tower.C131n.recarry_cancel
#print axioms Uniformity.Density.Tower.C131n.theta_le_floor_add_paid
#print axioms Uniformity.Density.Tower.C131n.recarry_price
#print axioms Uniformity.Density.Tower.C131n.recarry_step_zero
#print axioms Uniformity.Density.Tower.C131n.recarry_moves_up_one
#print axioms Uniformity.Density.Tower.C131n.recarry_moves_up
#print axioms Uniformity.Density.Tower.C131n.recarry_never_down
#print axioms Uniformity.Density.Tower.C131n.quotIter_divByMonic_comm
#print axioms Uniformity.Density.Tower.C131n.devQ_eq_quotDigit
#print axioms Uniformity.Density.Tower.C131n.quotIter_floor_of_le
#print axioms Uniformity.Density.Tower.C131n.quotDigit_floor_of_le
#print axioms Uniformity.Density.Tower.C131n.PaidFloor
#print axioms Uniformity.Density.Tower.C131n.paidFloor_mono
#print axioms Uniformity.Density.Tower.C131n.le_WT_eraseTagged
#print axioms Uniformity.Density.Tower.C131n.theta_le_WT_of_paidFloor
#print axioms Uniformity.Density.Tower.C131n.census_floor
#print axioms Uniformity.Density.Tower.C131n.paidFloor_preserve
#print axioms Uniformity.Density.Tower.C131n.xCarryStep_paidFloor
#print axioms Uniformity.Density.Tower.C131n.paidFloor_transport
#print axioms Uniformity.Density.Tower.C131n.paidFloor_transport_digit
#print axioms Uniformity.Density.Tower.C131n.census_digit_floor

end AxCheck
