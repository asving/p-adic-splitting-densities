/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RecenterBox
import LeanUrat.OM.MultiSlopeMenu
import LeanUrat.RatFn

/-!
# ChainMenu — Wave W5b: the `n = 2` descent-chain menu (depth-windowed recenter chains)

**Provenance.** `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §1 + §2-W5b, ground truth
`notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` §1 (the stratum tree / chain index) and the
§7 **Case-A ledger** (externally verified to depth 3 at `p = 2`). The pure-counting engine is
Wave W5a's `OM/RecenterBox.lean` (the staircase bijection `stratumPairEquiv`, note Lemma 2.3 at
`s = n = 2`).

## The object

A depth-`k` chain stratum for `n = 2` is: recentering slopes `ms = [m₁, …, m_k]` (each `≥ 1`;
every descend at `n = 2` is whole-window) followed by a TERMINATING LEAF in the depth-`k`
staircase frame. The leaf menu (`ChainLeaf`) covers the terminating cluster-read outcomes of
the accepted note's Case-A tree:
* `ram H` (odd `H ≥ 1`): the W1-style single-side stratum, relocated to the recentered frame —
  `v(b₀) = H` exact (nonzero height-`H` digit), `v(b₁) ≥ (H+1)/2`; type `{(2,1)}`;
* `inert m` (`m ≥ 1`): the even-height (`2m`) side with SEPARABLE (root-free) residual
  `y² + β̄y + ᾱ` — the order-0-style separable leaf, inert pattern; type `{(1,2)}`;
* `split k` (`k ≥ 1`): the two-sided polygon (vertex at `(1, k)`: `v(b₁) = k` exact,
  `v(b₀) ≥ 2k + 1`), two degree-1 sides — the split pattern; type `{(1,1),(1,1)}`.
SHAPE is indexed, VALUES are counted (note (†)): each chain step contributes the factor
`(p−1)` (the recentering digit `c̃ ∈ F_p^×`) and mass `p^{−3m_t}` (cluster-conditional); the
leaf digit pools are `(p−1)` (ram), `#{root-free monic quadratics} = p(p−1)/2` (inert),
`(p−1)` (split).

**Deferred (named honest gap):** the even-height side with separable SPLIT residual (digit pool
`(p−1)(p−2)/2`) is NOT in this wave's leaf menu — it is EMPTY at `p = 2` (the ledger's
"split empty — honest-empty pool"), so the `p = 2` Case-A tree is fully covered; at odd `p` the
W6 exhaustion pass must add it.

## Normalization ledger (the cluster-normalization resolution; note §7 Case A, `p = 2`)

`RecenterBox` provides both normalizations: `mass_descendStratum` (FULL box: `p^{−(3m+2)}` per
`(m, c̃)`) and `massCond_descendStratum` (cluster box `p^{2N−2}`: `p^{−3m}` per `c̃` — the §7
ledger's conditional frame). The chain closed form below is stated in the FULL box: for the
chain `(ms, leaf)`,
```
  count / p^{2N} = (p−1)^k · (leaf pool) · p^{−(3·Σms + eLeaf)},
```
the `p^{−2}` cluster-digit factor priced ONCE, inside `eLeaf`. Case-A absolute anchors at
`p = 2` (`gate` module):
* depth-1 descend (m=1) → ram H=1 leaf: `(1/8)·(1/2)` cluster-conditional `= 1/16`, i.e.
  `1/64` of the FULL box — the note's Case C (`x² − 12`) value;
* depth-2 (1,1) → ram 1: `1/128` cluster-conditional `= 1/512` full-box;
* depth-1 (1) → inert 1: `(1/8)·(1/8) = 1/64` cluster-conditional `= 1/256` full-box;
* depth-1 (1) → split 1: `1/64` cluster-conditional `= 1/256` full-box.

**The `split` leaf level gate.** The note §7 records: "the two-sided split ledger values are
the ideal cylinder masses (a naive census that routes `v(a₀) ≥ N` to the tail undercounts
them…) — a bookkeeping caveat for the Lean statements". Accordingly `LeafPair (split k)`
carries the explicit readability gate `2k + 1 ≤ L₀` (below it, the level-`L₀` box cannot
certify `v(b₀) ≥ 2k+1` against the undecided tail), which makes the level staircase exact
(`0, …, 0, c, c, …`). `ram`/`inert` need no gate: their nonzero-digit conditions are
self-emptying below threshold.

## σ-keying and the W5c boundary

`typeOf5` keys a chain literal to its LEAF type (`leafType`). The DESIGN lemma behind this —
**translation invariance**: the recentering substitution `x ↦ x + ĉp^m` is a `ℤ_p`-algebra
automorphism of `ℤ_p[x]`, hence preserves factorization types, so the leaf decided in the
recentered frame carries the type of the original polynomial — is [COUNT] per the note §6/§1
(a one-lemma fact, NOT an axiom), but its Lean form belongs to the CLASSIFIER-side reading of
the chain fibers, which is **W5c's business** (axiom-scope #4 + the lift-invariance pin,
boundary #5). This wave proves only the DEFINITIONAL keying (`typeOf5_chainLit`); nothing in
this module claims the fibers' Montes types.

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ChainMenu

open scoped Classical
open LeanUrat LeanUrat.OM Finset Polynomial
open LeanUrat.OM.CellMenu
open LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox
open LeanUrat.RatFn

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. The leaf datatype -/

/-- **The terminating leaf** of an `n = 2` chain stratum (module docstring): the W1-style
ramified ladder rung `ram H`, the separable-residual inert leaf `inert m`, or the two-sided
split leaf `split k`. -/
inductive ChainLeaf where
  | ram (H : ℕ)
  | inert (m : ℕ)
  | split (k : ℕ)
  deriving DecidableEq

/-- Well-formedness of a leaf: `ram` heights are ODD (the `(2,1)`-type rungs) and positive;
`inert`/`split` parameters are positive. -/
def leafOK : ChainLeaf → Prop
  | .ram H => Odd H ∧ 1 ≤ H
  | .inert m => 1 ≤ m
  | .split k => 1 ≤ k

/-- **The leaf level need** (the `b₀`-slot depth the leaf conditions consume): the smallest
final-frame level `L₀` at which the leaf stratum is nonempty/readable. -/
def leafNeed : ChainLeaf → ℕ
  | .ram H => H + 1
  | .inert m => 2 * m + 1
  | .split k => 2 * k + 1

theorem one_le_leafNeed (leaf : ChainLeaf) : 1 ≤ leafNeed leaf := by
  cases leaf <;> simp only [leafNeed] <;> omega

/-- The factorization type σ NAMED by a leaf (the σ-keying payload; semantic faithfulness of
this keying on the real fibers is W5c's boundary — module docstring). -/
def leafType : ChainLeaf → FactorizationType
  | .ram _ => ⟨{(2, 1)}⟩
  | .inert _ => ⟨{(1, 2)}⟩
  | .split _ => ⟨{(1, 1), (1, 1)}⟩

/-! ## 2. The root-free residual pool (the inert leaf's digit set)

Over `F_p` a monic quadratic is irreducible iff it has no root (a quadratic with no root is
automatically separable: inseparable monic quadratics are Frobenius squares `(y − r)²`, which
have roots). The pool count is `p(p−1)/2`, via the Vieta parametrization of the rooted
quadratics by `Sym2 (F_p)`. -/

/-- The digit pairs `(ᾱ, β̄)` whose residual `y² + β̄y + ᾱ` is ROOT-FREE over `F_p`
(equivalently: irreducible — the inert pool). -/
noncomputable def noRootPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun s => ∀ r : ZMod p, r ^ 2 + s.2 * r + s.1 ≠ 0)

theorem mem_noRootPairs {s : ZMod p × ZMod p} :
    s ∈ noRootPairs p ↔ ∀ r : ZMod p, r ^ 2 + s.2 * r + s.1 ≠ 0 := by
  rw [noRootPairs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩

/-- A root-free pair has nonzero constant digit (`r = 0` would otherwise be a root). -/
theorem noRootPairs_fst_ne_zero {s : ZMod p × ZMod p} (h : s ∈ noRootPairs p) : s.1 ≠ 0 := by
  intro h0
  refine (mem_noRootPairs p).mp h 0 ?_
  rw [h0]
  ring

/-- **Vieta packaging**: the unordered root pair `{r, s}` maps to the coefficient pair
`(rs, −(r+s))` of `(y − r)(y − s)`. -/
noncomputable def vieta : Sym2 (ZMod p) → ZMod p × ZMod p :=
  Sym2.lift ⟨fun r s => (r * s, -(r + s)), fun r s => by
    show (r * s, -(r + s)) = (s * r, -(s + r))
    rw [mul_comm, add_comm]⟩

theorem vieta_mk (r s : ZMod p) : vieta p s(r, s) = (r * s, -(r + s)) := rfl

/-- Vieta is injective: the coefficient pair determines the root multiset (a field has unique
quadratic root multisets). -/
theorem vieta_injective : Function.Injective (vieta p) := by
  intro z w
  induction z using Sym2.ind with
  | _ r s =>
  induction w using Sym2.ind with
  | _ r' s' =>
  intro h
  rw [vieta_mk, vieta_mk] at h
  have hprod : r * s = r' * s' := congrArg Prod.fst h
  have hsum : r + s = r' + s' := neg_inj.mp (congrArg Prod.snd h)
  have hz : (r' - r) * (r' - s) = 0 := by
    linear_combination (-(r' : ZMod p)) * hsum + hprod
  rw [Sym2.eq_iff]
  rcases mul_eq_zero.mp hz with h0 | h0
  · have hr : r = r' := by linear_combination -h0
    exact Or.inl ⟨hr, by linear_combination hsum + h0⟩
  · have hs : s = r' := by linear_combination -h0
    exact Or.inr ⟨by linear_combination hsum + h0, hs⟩

/-- The rooted pairs are EXACTLY the Vieta image. -/
theorem hasRoot_iff_mem_vieta_image (s : ZMod p × ZMod p) :
    (∃ r : ZMod p, r ^ 2 + s.2 * r + s.1 = 0) ↔ s ∈ Finset.univ.image (vieta p) := by
  constructor
  · rintro ⟨r, hr⟩
    rw [Finset.mem_image]
    refine ⟨s(r, -s.2 - r), Finset.mem_univ _, ?_⟩
    rw [vieta_mk]
    refine Prod.ext ?_ ?_
    · show r * (-s.2 - r) = s.1
      linear_combination -hr
    · show -(r + (-s.2 - r)) = s.2
      ring
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨z, -, hz⟩ := h
    induction z using Sym2.ind with
    | _ r r' =>
    rw [vieta_mk] at hz
    refine ⟨r, ?_⟩
    have h1 : r * r' = s.1 := congrArg Prod.fst hz
    have h2 : -(r + r') = s.2 := congrArg Prod.snd hz
    linear_combination -h1 - r * h2

/-- **The inert pool count**: `2 · #noRootPairs = p(p−1)` — total `p²` minus the rooted
`#Sym2(F_p) = p(p+1)/2`. -/
theorem two_mul_card_noRootPairs : 2 * (noRootPairs p).card = p * (p - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hcompl : noRootPairs p = (Finset.univ.image (vieta p))ᶜ := by
    ext s
    rw [Finset.mem_compl, mem_noRootPairs, ← hasRoot_iff_mem_vieta_image]
    push_neg
    rfl
  have himg : (Finset.univ.image (vieta p)).card = Nat.choose (p + 1) 2 := by
    rw [Finset.card_image_of_injective _ (vieta_injective p), Finset.card_univ, Sym2.card,
      ZMod.card]
  have hcard : (noRootPairs p).card = p * p - Nat.choose (p + 1) 2 := by
    rw [hcompl, Finset.card_compl, himg, Fintype.card_prod, ZMod.card]
  have hchoose : Nat.choose (p + 1) 2 = (p + 1) * p / 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have heven : 2 * ((p + 1) * p / 2) = (p + 1) * p := by
    refine Nat.mul_div_cancel' ?_
    rw [Nat.mul_comm]
    exact (Nat.even_mul_succ_self p).two_dvd
  have hp1 : 1 ≤ p := hp.out.one_le
  have hexp : (p + 1) * p = p * p + p := by ring
  have hsub : p * (p - 1) + p = p * p := by
    have hpred : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
    calc p * (p - 1) + p = p * ((p - 1) + 1) := by ring
      _ = p * p := by rw [hpred]
  rw [hcard, hchoose]
  omega

/-- The inert pool count in `ℚ`: `(p² − p)/2` — the closed form `C5` evaluates. -/
theorem card_noRootPairs_q : ((noRootPairs p).card : ℚ) = ((p : ℚ) ^ 2 - p) / 2 := by
  have h := two_mul_card_noRootPairs p
  have hp1 : 1 ≤ p := hp.out.one_le
  have hq : (2 : ℚ) * ((noRootPairs p).card : ℚ) = (p : ℚ) * ((p : ℚ) - 1) := by
    rw [show ((p : ℚ) - 1) = ((p - 1 : ℕ) : ℚ) from by rw [Nat.cast_sub hp1, Nat.cast_one]]
    exact_mod_cast h
  have hsq : (p : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ 2 - p := by ring
  linarith [hq, hsq]

/-! ## 3. Counting atoms (digit-set fibers over the divisibility locus) -/

/-- **Generic disjoint-witness summation**: if the witness `c` of `Q c a` is unique per `a` and
every `c`-slice has the same card `M`, then the `∃ c` locus has card `#ι · M`. -/
theorem card_exists_eq_mul {α ι : Type*} [Fintype α] [Fintype ι] (Q : ι → α → Prop)
    (hdisj : ∀ c c' a, Q c a → Q c' a → c = c') (M : ℕ)
    (hM : ∀ c, Nat.card {a : α // Q c a} = M) :
    Nat.card {a : α // ∃ c, Q c a} = Fintype.card ι * M := by
  classical
  have hsplit : (Finset.univ.filter fun a => ∃ c, Q c a)
      = Finset.univ.biUnion (fun c : ι => Finset.univ.filter (fun a => Q c a)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  have hdis : ∀ c ∈ (Finset.univ : Finset ι), ∀ c' ∈ (Finset.univ : Finset ι), c ≠ c' →
      Disjoint (Finset.univ.filter (fun a => Q c a)) (Finset.univ.filter (fun a => Q c' a)) :=
    fun c _ c' _ hcc => Finset.disjoint_left.mpr
      (fun a ha ha' => hcc (hdisj c c' a (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2))
  calc Nat.card {a : α // ∃ c, Q c a}
      = (Finset.univ.filter fun a => ∃ c, Q c a).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = ∑ c : ι, (Finset.univ.filter (fun a => Q c a)).card := by
        rw [hsplit, Finset.card_biUnion hdis]
    _ = ∑ _c : ι, M := Finset.sum_congr rfl (fun c _ => by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact hM c)
    _ = Fintype.card ι * M := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Generic fiber-count summation**: if every fiber of `h` over `S` has the same card `M`,
the `h ∈ S` locus has card `S.card · M`. -/
theorem card_mem_fiber {β γ : Type*} [Fintype β] [DecidableEq γ] (h : β → γ) (S : Finset γ)
    (M : ℕ) (hM : ∀ c ∈ S, Nat.card {b : β // h b = c} = M) :
    Nat.card {b : β // h b ∈ S} = S.card * M := by
  classical
  have e : {b : β // h b ∈ S} ≃ {b : β // ∃ c : {c // c ∈ S}, h b = c.1} :=
    Equiv.subtypeEquivRight (fun b =>
      ⟨fun hb => ⟨⟨h b, hb⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ c.2⟩)
  rw [Nat.card_congr e,
    card_exists_eq_mul (fun (c : {c // c ∈ S}) (b : β) => h b = c.1)
      (fun c c' b hc hc' => Subtype.ext (hc ▸ hc'))
      M (fun c => hM c.1 c.2)]
  rw [Fintype.card_coe]

/-- Digit-value fiber over the divisibility locus, flattened:
`#{x : p^k ∣ x.val, digit_k x = c} = p^{L−k−1}` (`CellCard.card_digit_fiber` re-packaged). -/
theorem card_dvd_digit_eq {L k : ℕ} (hk : k < L) (c : ZMod p) :
    Nat.card {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x = c} = p ^ (L - k - 1) := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun x : ZMod (p ^ L) => p ^ k ∣ x.val) (fun x => digit p L k x = c)).symm]
  exact card_digit_fiber p hk c

/-- Digit-SET fiber over the divisibility locus: `#{x : p^k ∣ x.val, digit_k x ∈ S}
= #S · p^{L−k−1}`. -/
theorem card_dvd_digitSet {L k : ℕ} (hk : k < L) (S : Finset (ZMod p)) :
    Nat.card {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x ∈ S}
      = S.card * p ^ (L - k - 1) := by
  have e : {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x ∈ S}
      ≃ {x : {x : ZMod (p ^ L) // p ^ k ∣ x.val} // digit p L k x.1 ∈ S} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  rw [Nat.card_congr e]
  refine card_mem_fiber (fun x : {x : ZMod (p ^ L) // p ^ k ∣ x.val} => digit p L k x.1) S
    (p ^ (L - k - 1)) (fun c _ => ?_)
  exact card_digit_fiber p hk c

/-- Nonzero-digit fiber: `#{x : p^k ∣ x.val, digit_k x ≠ 0} = (p−1)·p^{L−k−1}`. -/
theorem card_dvd_digit_ne {L k : ℕ} (hk : k < L) :
    Nat.card {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x ≠ 0}
      = (p - 1) * p ^ (L - k - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have e : {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x ≠ 0}
      ≃ {x : ZMod (p ^ L) // p ^ k ∣ x.val ∧ digit p L k x ∈ ({0}ᶜ : Finset (ZMod p))} :=
    Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_compl, Finset.mem_singleton])
  rw [Nat.card_congr e, card_dvd_digitSet p hk]
  congr 1
  rw [Finset.card_compl, Finset.card_singleton, ZMod.card]

/-- **The joint two-coordinate digit-set count**: `#{(x, y) : p^{k₀} ∣ x, p^{k₁} ∣ y,
(digit x, digit y) ∈ S} = #S · p^{L₀−k₀−1} · p^{L₁−k₁−1}`. -/
theorem card_pair_digitSet {L₀ L₁ k₀ k₁ : ℕ} (h₀ : k₀ < L₀) (h₁ : k₁ < L₁)
    (S : Finset (ZMod p × ZMod p)) :
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
        p ^ k₀ ∣ a.1.val ∧ p ^ k₁ ∣ a.2.val
          ∧ (digit p L₀ k₀ a.1, digit p L₁ k₁ a.2) ∈ S}
      = S.card * (p ^ (L₀ - k₀ - 1) * p ^ (L₁ - k₁ - 1)) := by
  have e1 : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
        p ^ k₀ ∣ a.1.val ∧ p ^ k₁ ∣ a.2.val
          ∧ (digit p L₀ k₀ a.1, digit p L₁ k₁ a.2) ∈ S}
      ≃ {b : {x : ZMod (p ^ L₀) // p ^ k₀ ∣ x.val} × {y : ZMod (p ^ L₁) // p ^ k₁ ∣ y.val} //
          (digit p L₀ k₀ b.1.1, digit p L₁ k₁ b.2.1) ∈ S} :=
    { toFun := fun a => ⟨(⟨a.1.1, a.2.1⟩, ⟨a.1.2, a.2.2.1⟩), a.2.2.2⟩
      invFun := fun b => ⟨(b.1.1.1, b.1.2.1), b.1.1.2, b.1.2.2, b.2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr e1]
  refine card_mem_fiber
    (fun b : {x : ZMod (p ^ L₀) // p ^ k₀ ∣ x.val} × {y : ZMod (p ^ L₁) // p ^ k₁ ∣ y.val} =>
      (digit p L₀ k₀ b.1.1, digit p L₁ k₁ b.2.1)) S _ (fun c _ => ?_)
  have e3 : {b : {x : ZMod (p ^ L₀) // p ^ k₀ ∣ x.val} × {y : ZMod (p ^ L₁) // p ^ k₁ ∣ y.val} //
        (digit p L₀ k₀ b.1.1, digit p L₁ k₁ b.2.1) = c}
      ≃ {x : {x : ZMod (p ^ L₀) // p ^ k₀ ∣ x.val} // digit p L₀ k₀ x.1 = c.1}
          × {y : {y : ZMod (p ^ L₁) // p ^ k₁ ∣ y.val} // digit p L₁ k₁ y.1 = c.2} :=
    { toFun := fun b => (⟨b.1.1, congrArg Prod.fst b.2⟩, ⟨b.1.2, congrArg Prod.snd b.2⟩)
      invFun := fun z => ⟨(z.1.1, z.2.1), Prod.ext z.1.2 z.2.2⟩
      left_inv := fun b => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e3, Nat.card_prod, card_digit_fiber p h₀ c.1, card_digit_fiber p h₁ c.2]

/-! ## 4. The leaf conditions and their counts -/

/-- **The leaf digit conditions in a staircase frame `(L₀, L₁)`** (module docstring):
* `ram H`: `v(b₀) = H` exact (dvd + nonzero digit), `v(b₁) ≥ (H+1)/2`;
* `inert m`: `v(b₀) ≥ 2m`, `v(b₁) ≥ m`, residual digit pair root-free (forces `v(b₀) = 2m`
  exact — `noRootPairs_fst_ne_zero`);
* `split k`: `v(b₁) = k` exact, `v(b₀) ≥ 2k+1`, with the READABILITY GATE `2k+1 ≤ L₀` (the
  note §7 two-sided bookkeeping caveat: below the gate the level cannot certify the
  `v(b₀) ≥ 2k+1` side against the undecided tail). -/
def LeafPair : ChainLeaf → (L₀ L₁ : ℕ) → ZMod (p ^ L₀) × ZMod (p ^ L₁) → Prop
  | .ram H, L₀, L₁, a =>
      (p ^ H ∣ a.1.val ∧ digit p L₀ H a.1 ≠ 0) ∧ p ^ ((H + 1) / 2) ∣ a.2.val
  | .inert m, L₀, L₁, a =>
      p ^ (2 * m) ∣ a.1.val ∧ p ^ m ∣ a.2.val
        ∧ (digit p L₀ (2 * m) a.1, digit p L₁ m a.2) ∈ noRootPairs p
  | .split k, L₀, L₁, a =>
      2 * k + 1 ≤ L₀ ∧ p ^ (2 * k + 1) ∣ a.1.val
        ∧ (p ^ k ∣ a.2.val ∧ digit p L₁ k a.2 ≠ 0)

/-- **The leaf count** in the frame `(L₀, L₁)` (valid at `leafNeed ≤ L₀ ≤ L₁`):
pool × free digits. -/
noncomputable def leafCount : ChainLeaf → (L₀ L₁ : ℕ) → ℕ
  | .ram H, L₀, L₁ => (p - 1) * p ^ (L₀ - H - 1) * p ^ (L₁ - (H + 1) / 2)
  | .inert m, L₀, L₁ => (noRootPairs p).card * (p ^ (L₀ - 2 * m - 1) * p ^ (L₁ - m - 1))
  | .split k, L₀, L₁ => p ^ (L₀ - (2 * k + 1)) * ((p - 1) * p ^ (L₁ - k - 1))

/-- The leaf conditions subsume the staircase CLUSTER condition (both coordinates ≡ 0 mod `p`)
— the frame-glue fact that lets the chain recursion price the cluster digits once. -/
theorem clusterPair_of_leafPair {leaf : ChainLeaf} (hOK : leafOK leaf) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : LeafPair p leaf L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  cases leaf with
  | ram H =>
      obtain ⟨hodd, hH⟩ := hOK
      obtain ⟨⟨hd0, -⟩, hd1⟩ := h
      exact ⟨(dvd_pow_self p (by omega : H ≠ 0)).trans hd0,
        (dvd_pow_self p (by omega : (H + 1) / 2 ≠ 0)).trans hd1⟩
  | inert m =>
      have hm : 1 ≤ m := hOK
      obtain ⟨hd0, hd1, -⟩ := h
      exact ⟨(dvd_pow_self p (by omega : 2 * m ≠ 0)).trans hd0,
        (dvd_pow_self p (by omega : m ≠ 0)).trans hd1⟩
  | split k =>
      have hk : 1 ≤ k := hOK
      obtain ⟨-, hd0, hd1, -⟩ := h
      exact ⟨(dvd_pow_self p (by omega : 2 * k + 1 ≠ 0)).trans hd0,
        (dvd_pow_self p (by omega : k ≠ 0)).trans hd1⟩

/-- **The leaf count identity** (`leafNeed ≤ L₀ ≤ L₁`). -/
theorem card_leafPair (leaf : ChainLeaf) (hOK : leafOK leaf) (L₀ L₁ : ℕ)
    (hL : leafNeed leaf ≤ L₀) (h01 : L₀ ≤ L₁) :
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // LeafPair p leaf L₀ L₁ a}
      = leafCount p leaf L₀ L₁ := by
  cases leaf with
  | ram H =>
      rw [show leafNeed (ChainLeaf.ram H) = H + 1 from rfl] at hL
      have e : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // LeafPair p (ChainLeaf.ram H) L₀ L₁ a}
          ≃ {x : ZMod (p ^ L₀) // p ^ H ∣ x.val ∧ digit p L₀ H x ≠ 0}
              × {y : ZMod (p ^ L₁) // p ^ ((H + 1) / 2) ∣ y.val} :=
        Equiv.subtypeProdEquivProd
          (p := fun x : ZMod (p ^ L₀) => p ^ H ∣ x.val ∧ digit p L₀ H x ≠ 0)
          (q := fun y : ZMod (p ^ L₁) => p ^ ((H + 1) / 2) ∣ y.val)
      rw [Nat.card_congr e, Nat.card_prod, card_dvd_digit_ne p (by omega : H < L₀),
        card_dvd_subtype p (by omega : (H + 1) / 2 ≤ L₁)]
      rfl
  | inert m =>
      rw [show leafNeed (ChainLeaf.inert m) = 2 * m + 1 from rfl] at hL
      exact card_pair_digitSet p (by omega : 2 * m < L₀) (by omega : m < L₁) (noRootPairs p)
  | split k =>
      rw [show leafNeed (ChainLeaf.split k) = 2 * k + 1 from rfl] at hL
      have e : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // LeafPair p (ChainLeaf.split k) L₀ L₁ a}
          ≃ {x : ZMod (p ^ L₀) // p ^ (2 * k + 1) ∣ x.val}
              × {y : ZMod (p ^ L₁) // p ^ k ∣ y.val ∧ digit p L₁ k y ≠ 0} :=
        (Equiv.subtypeEquivRight (fun a => by
          show (2 * k + 1 ≤ L₀ ∧ _) ↔ _
          rw [and_iff_right hL])).trans
          (Equiv.subtypeProdEquivProd
            (p := fun x : ZMod (p ^ L₀) => p ^ (2 * k + 1) ∣ x.val)
            (q := fun y : ZMod (p ^ L₁) => p ^ k ∣ y.val ∧ digit p L₁ k y ≠ 0))
      rw [Nat.card_congr e, Nat.card_prod, card_dvd_subtype p (by omega : 2 * k + 1 ≤ L₀),
        card_dvd_digit_ne p (by omega : k < L₁)]
      rfl

/-- **Leaf emptiness below the level need** (the small-`N` engine): `ram`/`inert` are
self-emptying (the pinned nonzero digit cannot exist when the whole slot is tail), `split` by
its readability gate. -/
theorem leafPair_empty (leaf : ChainLeaf) {L₀ L₁ : ℕ} (hL : L₀ < leafNeed leaf)
    (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) : ¬ LeafPair p leaf L₀ L₁ a := by
  haveI : NeZero (p ^ L₀) := QuotientBox.instNeZeroPow p L₀
  cases leaf with
  | ram H =>
      rw [show leafNeed (ChainLeaf.ram H) = H + 1 from rfl] at hL
      rintro ⟨⟨hd0, hne⟩, -⟩
      have hval : a.1.val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hd0 (lt_of_lt_of_le (ZMod.val_lt a.1)
          (Nat.pow_le_pow_right hp.out.pos (by omega)))
      refine hne ?_
      show ((a.1.val / p ^ H : ℕ) : ZMod p) = 0
      rw [hval, Nat.zero_div, Nat.cast_zero]
  | inert m =>
      rw [show leafNeed (ChainLeaf.inert m) = 2 * m + 1 from rfl] at hL
      rintro ⟨hd0, -, hmem⟩
      have hval : a.1.val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hd0 (lt_of_lt_of_le (ZMod.val_lt a.1)
          (Nat.pow_le_pow_right hp.out.pos (by omega)))
      refine noRootPairs_fst_ne_zero p hmem ?_
      show ((a.1.val / p ^ (2 * m) : ℕ) : ZMod p) = 0
      rw [hval, Nat.zero_div, Nat.cast_zero]
  | split k =>
      rw [show leafNeed (ChainLeaf.split k) = 2 * k + 1 from rfl] at hL
      rintro ⟨hgate, -⟩
      omega

/-! ## 5. The chain recursion (`descendPair` transport + `ChainPair`) -/

/-- **The raw descend transport**: the value map of the staircase bijection
`f(x) ↦ g(y) = f(ĉp^m + p^m y)/p^{2m}` in digit coordinates — total on the pair box (its
bijectivity onto the child cluster box holds ON the stratum: `descendPair_eq_stratumPairEquiv`).
`b₀ = ã₀ + ĉã₁ + ĉ²`, `b₁ = ã₁ + 2ĉ` with `ã_i` the digit shifts. -/
noncomputable def descendPair (m ĉ : ℕ) {L₀ L₁ : ℕ} (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) :
    ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) :=
  (((a.1.val / p ^ (2 * m) : ℕ) : ZMod (p ^ (L₀ - 2 * m)))
      + (ĉ : ZMod (p ^ (L₀ - 2 * m))) * ((a.2.val / p ^ m : ℕ) : ZMod (p ^ (L₀ - 2 * m)))
      + (ĉ : ZMod (p ^ (L₀ - 2 * m))) ^ 2,
   ((a.2.val / p ^ m : ℕ) : ZMod (p ^ (L₁ - m))) + 2 * (ĉ : ZMod (p ^ (L₁ - m))))

/-- **The chain-stratum fiber predicate on a staircase pair frame** (blueprint §2-W5b
`ChainCell`, pair level): recursively, a recentering digit choice `c̃ ∈ F_p^×` whose (S1)∧(S2)
stratum conditions hold, followed by the tail chain on the `descendPair`-transported child in
the child staircase frame; at `ms = []`, the leaf conditions. VALUES counted, not indexed: the
digit `c` is existential (the note's (†) SHAPE×VALUES split). -/
def ChainPair : List ℕ → ChainLeaf → (L₀ L₁ : ℕ) → ZMod (p ^ L₀) × ZMod (p ^ L₁) → Prop
  | [], leaf, L₀, L₁, a => LeafPair p leaf L₀ L₁ a
  | m :: ms, leaf, L₀, L₁, a =>
      ∃ c : (ZMod p)ˣ, StratumPair p L₀ L₁ m c a ∧
        ChainPair ms leaf (L₀ - 2 * m) (L₁ - m) (descendPair p m ((c : ZMod p)).val a)

/-- Chain conditions subsume the cluster condition (head step at `m ≥ 1`, or leaf). -/
theorem clusterPair_of_chainPair (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : ChainPair p ms leaf L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  cases ms with
  | nil => exact clusterPair_of_leafPair p hOK h
  | cons m ms =>
      obtain ⟨c, hstep, -⟩ := h
      exact clusterPair_of_stratumPair p L₀ L₁ m (hms m List.mem_cons_self) c a hstep

/-- **The transport agrees with the staircase bijection on the stratum**: `descendPair` IS the
value map of W5a's `stratumPairEquiv` (the recursive frame bookkeeping is the bijection's). -/
theorem descendPair_eq_stratumPairEquiv (L₀ L₁ m : ℕ) (c : (ZMod p)ˣ)
    (h₀ : 2 * m + 1 ≤ L₀) (h01 : L₀ ≤ L₁)
    (x : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StratumPair p L₀ L₁ m c a}) :
    descendPair p m ((c : ZMod p)).val x.1
      = ((stratumPairEquiv p L₀ L₁ m c h₀ h01) x : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m))) := by
  obtain ⟨⟨a₀, a₁⟩, h⟩ := x
  refine Prod.ext ?_ rfl
  show ((a₀.val / p ^ (2 * m) : ℕ) : ZMod (p ^ (L₀ - 2 * m)))
      + (((c : ZMod p)).val : ZMod (p ^ (L₀ - 2 * m)))
          * ((a₁.val / p ^ m : ℕ) : ZMod (p ^ (L₀ - 2 * m)))
      + (((c : ZMod p)).val : ZMod (p ^ (L₀ - 2 * m))) ^ 2
    = ((a₀.val / p ^ (2 * m) : ℕ) : ZMod (p ^ (L₀ - 2 * m)))
      + (((c : ZMod p)).val : ZMod (p ^ (L₀ - 2 * m)))
          * (ZMod.castHom (pow_dvd_pow p (by omega : L₀ - 2 * m ≤ L₁ - m)) (ZMod (p ^ (L₀ - 2 * m)))
              ((a₁.val / p ^ m : ℕ) : ZMod (p ^ (L₁ - m))))
      + (((c : ZMod p)).val : ZMod (p ^ (L₀ - 2 * m))) ^ 2
  rw [map_natCast]

/-- **The step count transfer** (note Lemma 2.3(2)+(3) consumed): for any child predicate `P`
subsuming the cluster condition, the step-∧-transported-`P` stratum has the SAME card as the
plain `P` locus in the child staircase frame — the staircase bijection is measure-exact and the
cluster digits are priced once. -/
theorem card_step (L₀ L₁ m : ℕ) (c : (ZMod p)ˣ) (h₀ : 2 * m + 1 ≤ L₀) (h01 : L₀ ≤ L₁)
    (P : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) → Prop)
    (hP : ∀ b, P b → ClusterPair p (L₀ - 2 * m) (L₁ - m) b) :
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
        StratumPair p L₀ L₁ m c a ∧ P (descendPair p m ((c : ZMod p)).val a)}
      = Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) // P b} := by
  have e1 : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
        StratumPair p L₀ L₁ m c a ∧ P (descendPair p m ((c : ZMod p)).val a)}
      ≃ {x : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StratumPair p L₀ L₁ m c a} //
          P (descendPair p m ((c : ZMod p)).val x.1)} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have e2 : {x : {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // StratumPair p L₀ L₁ m c a} //
        P (descendPair p m ((c : ZMod p)).val x.1)}
      ≃ {y : {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
          ClusterPair p (L₀ - 2 * m) (L₁ - m) b} // P y.1} :=
    (stratumPairEquiv p L₀ L₁ m c h₀ h01).subtypeEquiv (fun x => by
      rw [descendPair_eq_stratumPairEquiv p L₀ L₁ m c h₀ h01 x])
  have e3 : {y : {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
        ClusterPair p (L₀ - 2 * m) (L₁ - m) b} // P y.1}
      ≃ {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
          ClusterPair p (L₀ - 2 * m) (L₁ - m) b ∧ P b} :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  have e4 : {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
        ClusterPair p (L₀ - 2 * m) (L₁ - m) b ∧ P b}
      ≃ {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) // P b} :=
    Equiv.subtypeEquivRight (fun b => ⟨fun h => h.2, fun h => ⟨hP b h, h⟩⟩)
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr e3, Nat.card_congr e4]

/-- The recentering digit is PINNED by the stratum digit pair `(c̃², −2c̃)`: two witnesses on
the same pair coincide (`(c − c')² = 0` in the field `F_p`). -/
theorem stratumPair_unit_unique {L₀ L₁ m : ℕ} {c c' : (ZMod p)ˣ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : StratumPair p L₀ L₁ m c a) (h' : StratumPair p L₀ L₁ m c' a) : c = c' := by
  have h1 : ((c : ZMod p)) ^ 2 = ((c' : ZMod p)) ^ 2 := by
    rw [← h.1.2, ← h'.1.2]
  have h2 : (2 : ZMod p) * (c : ZMod p) = 2 * (c' : ZMod p) := by
    have := h.2.2.symm.trans h'.2.2
    exact neg_inj.mp this
  have hd : ((c : ZMod p) - c') * ((c : ZMod p) - c') = 0 := by
    linear_combination h1 - (c' : ZMod p) * h2
  have h0 : ((c : ZMod p)) - c' = 0 := mul_self_eq_zero.mp hd
  exact Units.ext (by linear_combination h0)

/-- **The chain closed form (pair level)** — note Lemma 2.3(5) at `s = 2`, all depths: above
the level threshold `2·Σms + leafNeed`, the chain-stratum count is
`(p−1)^{depth} · leafCount(final staircase frame)` — one `(p−1)` per counted recentering
digit, the staircase transport preserving cards step by step. -/
theorem card_chainPair (ms : List ℕ) (leaf : ChainLeaf) :
    (∀ m ∈ ms, 1 ≤ m) → leafOK leaf →
    ∀ L₀ L₁ : ℕ, 2 * ms.sum + leafNeed leaf ≤ L₀ → L₀ ≤ L₁ →
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // ChainPair p ms leaf L₀ L₁ a}
      = (p - 1) ^ ms.length * leafCount p leaf (L₀ - 2 * ms.sum) (L₁ - ms.sum) := by
  induction ms with
  | nil =>
      intro _ hOK L₀ L₁ hL h01
      simp only [List.sum_nil, List.length_nil, pow_zero, one_mul, Nat.mul_zero,
        Nat.sub_zero]
      simp only [List.sum_nil, Nat.mul_zero, Nat.zero_add] at hL
      exact card_leafPair p leaf hOK L₀ L₁ hL h01
  | cons m ms ih =>
      intro hms hOK L₀ L₁ hL h01
      have hm1 : 1 ≤ m := hms m List.mem_cons_self
      have hneed : 1 ≤ leafNeed leaf := one_le_leafNeed leaf
      rw [List.sum_cons] at hL ⊢
      have hstep : Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
            ChainPair p (m :: ms) leaf L₀ L₁ a}
          = (p - 1) * Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
              ChainPair p ms leaf (L₀ - 2 * m) (L₁ - m) b} := by
        have hmain := card_exists_eq_mul
          (Q := fun (c : (ZMod p)ˣ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) =>
            StratumPair p L₀ L₁ m c a ∧
              ChainPair p ms leaf (L₀ - 2 * m) (L₁ - m) (descendPair p m ((c : ZMod p)).val a))
          (fun c c' a h h' => stratumPair_unit_unique p h.1 h'.1)
          (Nat.card {b : ZMod (p ^ (L₀ - 2 * m)) × ZMod (p ^ (L₁ - m)) //
              ChainPair p ms leaf (L₀ - 2 * m) (L₁ - m) b})
          (fun c => card_step p L₀ L₁ m c (by omega) h01
            (ChainPair p ms leaf (L₀ - 2 * m) (L₁ - m))
            (fun b hb => clusterPair_of_chainPair p ms leaf
              (fun m' hm' => hms m' (List.mem_cons_of_mem m hm')) hOK hb))
        rw [ZMod.card_units p] at hmain
        exact hmain
      rw [hstep, ih (fun m' hm' => hms m' (List.mem_cons_of_mem m hm')) hOK
        (L₀ - 2 * m) (L₁ - m) (by omega) (by omega)]
      rw [show (m :: ms).length = ms.length + 1 from rfl, pow_succ]
      rw [show L₀ - 2 * m - 2 * ms.sum = L₀ - 2 * (m + ms.sum) from by omega,
        show L₁ - m - ms.sum = L₁ - (m + ms.sum) from by omega]
      ring

/-- **Small-level emptiness of the chain fiber** (pair level): below the threshold
`2·Σms + leafNeed`, the chain stratum is EMPTY — the final-frame leaf slot is pure tail. -/
theorem chainPair_empty (ms : List ℕ) (leaf : ChainLeaf) :
    ∀ L₀ L₁ : ℕ, L₀ < 2 * ms.sum + leafNeed leaf →
    ∀ a : ZMod (p ^ L₀) × ZMod (p ^ L₁), ¬ ChainPair p ms leaf L₀ L₁ a := by
  induction ms with
  | nil =>
      intro L₀ L₁ hL a
      rw [show ([] : List ℕ).sum = 0 from rfl] at hL
      exact leafPair_empty p leaf (by omega) a
  | cons m ms ih =>
      intro L₀ L₁ hL a
      rintro ⟨c, -, hrest⟩
      rw [List.sum_cons] at hL
      have hneed : 1 ≤ leafNeed leaf := one_le_leafNeed leaf
      exact ih (L₀ - 2 * m) (L₁ - m) (by omega) _ hrest

/-! ## 6. The disjointness bank (pinned digit ledgers differ)

Every pair of DISTINCT chain strata conflicts on a pinned digit: distinct step slopes / leaf
heights pin `v(b₀)` (or `v(b₁)`) at different exact values; equal slopes with distinct
recentering digits pin different `(c̃², −2c̃)` pairs; a step vs a leaf at the same height
conflicts because the step's residual has a DOUBLE root (`(y−c̃)²`) while the inert leaf's is
root-free. All arguments are level-free digit facts. -/

/-- The digit conflict atom: a nonzero height-`k` digit is incompatible with divisibility at
any strictly higher height. -/
theorem digit_conflict {L k k' : ℕ} {x : ZMod (p ^ L)} (hkk : k < k')
    (h1 : digit p L k x ≠ 0) (h2 : p ^ k' ∣ x.val) : False :=
  h1 (digit_eq_zero_of_dvd p ((pow_dvd_pow p (by omega : k + 1 ≤ k')).trans h2))

/-- Units of `F_p` have nonzero squares. -/
theorem unit_sq_ne_zero (c : (ZMod p)ˣ) : ((c : ZMod p)) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (Units.ne_zero c)

/-- A nonzero digit read at height `k` forces `k < L` (else the whole slot is tail). -/
theorem lt_of_dvd_digit_ne {L k : ℕ} {x : ZMod (p ^ L)} (hdvd : p ^ k ∣ x.val)
    (hne : digit p L k x ≠ 0) : k < L := by
  by_contra hle
  rw [not_lt] at hle
  haveI : NeZero (p ^ L) := QuotientBox.instNeZeroPow p L
  have hval : x.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd
      (lt_of_lt_of_le (ZMod.val_lt x) (Nat.pow_le_pow_right hp.out.pos hle))
  refine hne ?_
  show ((x.val / p ^ k : ℕ) : ZMod p) = 0
  rw [hval, Nat.zero_div, Nat.cast_zero]

/-- The inert-leaf digit read at height `2m` is nonzero (root-free pool ⟹ `ᾱ ≠ 0`). -/
theorem inert_digit_ne_zero {L₀ L₁ m : ℕ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPair p (ChainLeaf.inert m) L₀ L₁ a) : digit p L₀ (2 * m) a.1 ≠ 0 :=
  noRootPairs_fst_ne_zero p h.2.2

/-- **Distinct leaves conflict** (the 6 pinned-ledger cases of the module docstring). -/
theorem leafPair_disjoint {leaf leaf' : ChainLeaf} (hOK : leafOK leaf) (hOK' : leafOK leaf')
    (hne : leaf ≠ leaf') {L₀ L₁ : ℕ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPair p leaf L₀ L₁ a) (h' : LeafPair p leaf' L₀ L₁ a) : False := by
  cases leaf with
  | ram H =>
      obtain ⟨hodd, hH1⟩ := hOK
      obtain ⟨⟨hra, hrd⟩, hrb⟩ := h
      cases leaf' with
      | ram H' =>
          obtain ⟨⟨hra', hrd'⟩, hrb'⟩ := h'
          have hHH : H ≠ H' := fun hc => hne (by rw [hc])
          rcases Nat.lt_or_gt_of_ne hHH with hlt | hgt
          · exact digit_conflict p hlt hrd hra'
          · exact digit_conflict p hgt hrd' hra
      | inert m' =>
          obtain ⟨hia', hib', him'⟩ := h'
          have hid' : digit p L₀ (2 * m') a.1 ≠ 0 := noRootPairs_fst_ne_zero p him'
          obtain ⟨t, rfl⟩ := hodd
          rcases Nat.lt_or_ge (2 * t + 1) (2 * m') with hlt | hge
          · exact digit_conflict p hlt hrd hia'
          · exact digit_conflict p (by omega) hid' hra
      | split k' =>
          obtain ⟨-, hsa', hsb', hsd'⟩ := h'
          obtain ⟨t, rfl⟩ := hodd
          rcases Nat.lt_or_ge k' (t + 1) with hlt | hge
          · exact digit_conflict p (by omega : k' < (2 * t + 1 + 1) / 2) hsd' hrb
          · exact digit_conflict p (by omega) hrd hsa'
  | inert m =>
      have hm1 : 1 ≤ m := hOK
      obtain ⟨hia, hib, him⟩ := h
      have hid : digit p L₀ (2 * m) a.1 ≠ 0 := noRootPairs_fst_ne_zero p him
      cases leaf' with
      | ram H' =>
          obtain ⟨hodd', -⟩ := hOK'
          obtain ⟨⟨hra', hrd'⟩, hrb'⟩ := h'
          obtain ⟨t, rfl⟩ := hodd'
          rcases Nat.lt_or_ge (2 * t + 1) (2 * m) with hlt | hge
          · exact digit_conflict p hlt hrd' hia
          · exact digit_conflict p (by omega) hid hra'
      | inert m' =>
          obtain ⟨hia', hib', him'⟩ := h'
          have hid' : digit p L₀ (2 * m') a.1 ≠ 0 := noRootPairs_fst_ne_zero p him'
          have hmm : m ≠ m' := fun hc => hne (by rw [hc])
          rcases Nat.lt_or_gt_of_ne hmm with hlt | hgt
          · exact digit_conflict p (show 2 * m < 2 * m' by omega) hid hia'
          · exact digit_conflict p (show 2 * m' < 2 * m by omega) hid' hia
      | split k' =>
          obtain ⟨-, hsa', hsb', hsd'⟩ := h'
          rcases Nat.lt_or_ge k' m with hlt | hge
          · exact digit_conflict p hlt hsd' hib
          · exact digit_conflict p (by omega) hid hsa'
  | split k =>
      have hk1 : 1 ≤ k := hOK
      obtain ⟨-, hsa, hsb, hsd⟩ := h
      cases leaf' with
      | ram H' =>
          obtain ⟨hodd', -⟩ := hOK'
          obtain ⟨⟨hra', hrd'⟩, hrb'⟩ := h'
          obtain ⟨t, rfl⟩ := hodd'
          rcases Nat.lt_or_ge k (t + 1) with hlt | hge
          · exact digit_conflict p (by omega : k < (2 * t + 1 + 1) / 2) hsd hrb'
          · exact digit_conflict p (by omega) hrd' hsa
      | inert m' =>
          obtain ⟨hia', hib', him'⟩ := h'
          have hid' : digit p L₀ (2 * m') a.1 ≠ 0 := noRootPairs_fst_ne_zero p him'
          rcases Nat.lt_or_ge k m' with hlt | hge
          · exact digit_conflict p hlt hsd hib'
          · exact digit_conflict p (by omega) hid' hsa
      | split k' =>
          obtain ⟨-, hsa', hsb', hsd'⟩ := h'
          have hkk : k ≠ k' := fun hc => hne (by rw [hc])
          rcases Nat.lt_or_gt_of_ne hkk with hlt | hgt
          · exact digit_conflict p hlt hsd hsb'
          · exact digit_conflict p hgt hsd' hsb
/-- **A leaf and a descend step conflict in the same frame**: distinct heights pin distinct
exact valuations; the same height pins a DOUBLE-root residual against the leaf's read (the
inert pool is root-free at exactly the step's root `c̃`). -/
theorem leaf_step_disjoint {leaf : ChainLeaf} (hOK : leafOK leaf) {L₀ L₁ m : ℕ} (hm : 1 ≤ m)
    {c : (ZMod p)ˣ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPair p leaf L₀ L₁ a) (h' : StratumPair p L₀ L₁ m c a) : False := by
  obtain ⟨⟨hca, hcd⟩, ⟨hcb, hce⟩⟩ := h'
  have hcne : digit p L₀ (2 * m) a.1 ≠ 0 := by
    rw [hcd]; exact unit_sq_ne_zero p c
  cases leaf with
  | ram H =>
      obtain ⟨hodd, -⟩ := hOK
      obtain ⟨⟨hra, hrd⟩, hrb⟩ := h
      obtain ⟨t, rfl⟩ := hodd
      rcases Nat.lt_or_ge (2 * t + 1) (2 * m) with hlt | hge
      · exact digit_conflict p hlt hrd hca
      · exact digit_conflict p (by omega) hcne hra
  | inert m' =>
      obtain ⟨hia, hib, him⟩ := h
      have hid : digit p L₀ (2 * m') a.1 ≠ 0 := noRootPairs_fst_ne_zero p him
      rcases Nat.lt_trichotomy m' m with hlt | heq | hgt
      · exact digit_conflict p (by omega) hid hca
      · subst heq
        refine (mem_noRootPairs p).mp him ((c : ZMod p)) ?_
        show ((c : ZMod p)) ^ 2 + digit p L₁ m' a.2 * (c : ZMod p) + digit p L₀ (2 * m') a.1 = 0
        rw [hce, hcd]
        ring
      · exact digit_conflict p (by omega) hcne hia
  | split k =>
      obtain ⟨-, hsa, hsb, hsd⟩ := h
      rcases Nat.lt_or_ge k m with hlt | hge
      · exact digit_conflict p hlt hsd hcb
      · exact digit_conflict p (by omega) hcne hsa

/-- **Two descend steps conflict unless slope AND digit agree** (v-pins for distinct slopes,
the `(c̃², −2c̃)` field pin for distinct digits at the same slope). -/
theorem step_step_disjoint {L₀ L₁ m m' : ℕ} {c c' : (ZMod p)ˣ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (hne : ¬(m = m' ∧ c = c'))
    (h : StratumPair p L₀ L₁ m c a) (h' : StratumPair p L₀ L₁ m' c' a) : False := by
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · exact digit_conflict p (show 2 * m < 2 * m' by omega)
      (by rw [h.1.2]; exact unit_sq_ne_zero p c) h'.1.1
  · subst heq
    exact hne ⟨rfl, stratumPair_unit_unique p h h'⟩
  · exact digit_conflict p (show 2 * m' < 2 * m by omega)
      (by rw [h'.1.2]; exact unit_sq_ne_zero p c') h.1.1

/-- **The master chain disjointness**: distinct `(ms, leaf)` indices have DISJOINT chain
fibers at every frame — the pinned digit ledgers differ (blueprint §2-W5b disjointness
deliverable, pair level). -/
theorem chainPair_disjoint :
    ∀ (ms : List ℕ) (leaf : ChainLeaf), (∀ m ∈ ms, 1 ≤ m) → leafOK leaf →
    ∀ (ms' : List ℕ) (leaf' : ChainLeaf), (∀ m ∈ ms', 1 ≤ m) → leafOK leaf' →
    ¬(ms = ms' ∧ leaf = leaf') →
    ∀ (L₀ L₁ : ℕ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)),
      ChainPair p ms leaf L₀ L₁ a → ChainPair p ms' leaf' L₀ L₁ a → False := by
  intro ms
  induction ms with
  | nil =>
      intro leaf _ hOK ms' leaf' hms' hOK' hne L₀ L₁ a h h'
      cases ms' with
      | nil =>
          exact leafPair_disjoint p hOK hOK'
            (fun hc => hne ⟨rfl, hc⟩) h h'
      | cons m' tl' =>
          obtain ⟨c', hstep', -⟩ := h'
          exact leaf_step_disjoint p hOK (hms' m' List.mem_cons_self) h hstep'
  | cons m tl ih =>
      intro leaf hms hOK ms' leaf' hms' hOK' hne L₀ L₁ a h h'
      obtain ⟨c, hstep, hrest⟩ := h
      cases ms' with
      | nil =>
          exact leaf_step_disjoint p hOK' (hms m List.mem_cons_self) h' hstep
      | cons m' tl' =>
          obtain ⟨c', hstep', hrest'⟩ := h'
          by_cases hmc : m = m' ∧ c = c'
          · obtain ⟨rfl, rfl⟩ := hmc
            refine ih leaf (fun x hx => hms x (List.mem_cons_of_mem m hx)) hOK tl' leaf'
              (fun x hx => hms' x (List.mem_cons_of_mem m hx)) hOK'
              (fun ⟨htl, hlf⟩ => hne ⟨by rw [htl], hlf⟩)
              (L₀ - 2 * m) (L₁ - m) _ hrest hrest'
          · exact step_step_disjoint p hmc hstep hstep'

/-! ## 7. The chain literal and its exact decode (blueprint §2-W5b item `chainLit`) -/

/-- The numeric head of a leaf: constructor tag in the middle slot, parameter in the last. -/
def leafHead : ChainLeaf → ℕ × ℕ × ℕ
  | .ram H => (3, 0, H)
  | .inert m => (3, 1, m)
  | .split k => (3, 2, k)

/-- **The chain literal** (tree-index encoding): head `(2, 2, depth)` — order-slot `2`,
discriminating from every order-0 head (W1/W3 families) and the multi-slope order-slot `1` —
then the `ms` entries `(0, m_t, 0)`, then the leaf head. Cells empty (the chain carries no
order-0 payload; its fiber is the `ChainCell` digit predicate). -/
def chainLit (ms : List ℕ) (leaf : ChainLeaf) : ClusterShape :=
  ⟨((2 : ℕ), 2, ms.length) :: (ms.map (fun m => ((0 : ℕ), m, 0)) ++ [leafHead leaf]), []⟩

theorem headOrd_chainLit (ms : List ℕ) (leaf : ChainLeaf) :
    MultiSlopeMenu.headOrd (chainLit ms leaf) = 2 := rfl

/-- Exact decode of the slope list: drop the head, drop the leaf, read the middle slots. -/
def decodeMs (T : ClusterShape) : List ℕ := (T.tree.tail.dropLast).map (fun t => t.2.1)

/-- Exact decode of the leaf head. -/
def decodeLeaf (T : ClusterShape) : ChainLeaf :=
  match T.tree.getLast? with
  | some (_, 1, x) => .inert x
  | some (_, 2, x) => .split x
  | some (_, _, x) => .ram x
  | none => .ram 0

theorem decodeMs_chainLit (ms : List ℕ) (leaf : ChainLeaf) :
    decodeMs (chainLit ms leaf) = ms := by
  show ((ms.map (fun m => ((0 : ℕ), m, 0)) ++ [leafHead leaf]).dropLast).map
    (fun t : ℕ × ℕ × ℕ => t.2.1) = ms
  rw [List.dropLast_concat, List.map_map]
  induction ms with
  | nil => rfl
  | cons m tl ih => rw [List.map_cons, ih]; rfl

theorem decodeLeaf_chainLit (ms : List ℕ) (leaf : ChainLeaf) :
    decodeLeaf (chainLit ms leaf) = leaf := by
  have hlast : (chainLit ms leaf).tree.getLast? = some (leafHead leaf) := by
    show ((((2 : ℕ), 2, ms.length) :: ms.map (fun m => ((0 : ℕ), m, 0)))
        ++ [leafHead leaf]).getLast? = some (leafHead leaf)
    exact List.getLast?_concat
  rw [decodeLeaf, hlast]
  cases leaf <;> rfl

/-- **Injectivity of the chain literal** (exact decode). -/
theorem chainLit_injective {ms ms' : List ℕ} {leaf leaf' : ChainLeaf}
    (h : chainLit ms leaf = chainLit ms' leaf') : ms = ms' ∧ leaf = leaf' := by
  have h1 := decodeMs_chainLit ms leaf
  rw [h, decodeMs_chainLit] at h1
  have h2 := decodeLeaf_chainLit ms leaf
  rw [h, decodeLeaf_chainLit] at h2
  exact ⟨h1.symm, h2.symm⟩

/-- W5b family discriminator: every W4 menu shape has head order-slot `0` or `1`, never `2`. -/
theorem headOrd_of_mem_omMenu4 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ MultiSlopeMenu.omMenu4 n K σ) : MultiSlopeMenu.headOrd T ≠ 2 := by
  rcases MultiSlopeMenu.mem_omMenu4_cases hT with hold | ⟨hOK, rfl⟩
  · rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hold]
    omega
  · rw [MultiSlopeMenu.headOrd_multiSideLit]
    omega

/-! ## 8. σ-keying: `typeOf5`

**[COUNT] design lemma (translation invariance — stated for W5c, NOT proved here).** The
recentering substitution `x ↦ x + ĉp^m` (per chain step) is a `ℤ_p`-algebra automorphism of
`ℤ_p[x]`, so it preserves factorization types; hence the type of a chain stratum IS its leaf's
type read in the final recentered frame (note §1 σ-keying, a one-lemma [COUNT] fact). Its Lean
form belongs to W5c's classifier-side scope-#4 extension (`om_leaf_faithful` over `omMenu5` +
the boundary-#5 lift-invariance pin, which MUST be completed before declaration). W5b consumes
only the DEFINITIONAL keying below. -/

/-- **The Wave-5 σ-decoder**: on chain heads (order-slot `2`) the LEAF type; on every other
head defer to the Wave-4 decoder. -/
noncomputable def typeOf5 (n : ℕ) (T : ClusterShape) : Option FactorizationType :=
  if MultiSlopeMenu.headOrd T = 2 then some (leafType (decodeLeaf T))
  else MultiSlopeMenu.typeOf4 n T

theorem typeOf5_chainLit (n : ℕ) (ms : List ℕ) (leaf : ChainLeaf) :
    typeOf5 n (chainLit ms leaf) = some (leafType leaf) := by
  rw [typeOf5, if_pos (headOrd_chainLit ms leaf), decodeLeaf_chainLit]

theorem typeOf5_typeOf4_compat {n : ℕ} {T : ClusterShape}
    (h : MultiSlopeMenu.headOrd T ≠ 2) : typeOf5 n T = MultiSlopeMenu.typeOf4 n T := by
  rw [typeOf5, if_neg h]

/-! ## 9. The depth-windowed chain menu -/

/-- The three degree-2 types by name. -/
def ramType2 : FactorizationType := ⟨{(2, 1)}⟩
def inertType2 : FactorizationType := ⟨{(1, 2)}⟩
def splitType2 : FactorizationType := ⟨{(1, 1), (1, 1)}⟩

theorem leafType_ram (H : ℕ) : leafType (ChainLeaf.ram H) = ramType2 := rfl
theorem leafType_inert (m : ℕ) : leafType (ChainLeaf.inert m) = inertType2 := rfl
theorem leafType_split (k : ℕ) : leafType (ChainLeaf.split k) = splitType2 := rfl

/-- The window-`D,K` slope-list menu: lists of length `≤ D` with entries in `[1, K]`. -/
def msMenu : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | D + 1, K => {[]} ∪ (Finset.Icc 1 K ×ˢ msMenu D K).image (fun x => x.1 :: x.2)

theorem mem_msMenu (D K : ℕ) (ms : List ℕ) :
    ms ∈ msMenu D K ↔ ms.length ≤ D ∧ ∀ m ∈ ms, 1 ≤ m ∧ m ≤ K := by
  induction D generalizing ms with
  | zero =>
      simp only [msMenu, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun m hm => absurd hm (List.not_mem_nil)⟩
      · rintro ⟨hlen, -⟩
        exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  | succ D ih =>
      simp only [msMenu, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_product]
      constructor
      · rintro (rfl | ⟨⟨m, tl⟩, ⟨hm, htl⟩, rfl⟩)
        · exact ⟨Nat.zero_le _, fun m hm => absurd hm (List.not_mem_nil)⟩
        · rw [Finset.mem_Icc] at hm
          obtain ⟨hlen, hall⟩ := (ih tl).mp htl
          refine ⟨by simpa using Nat.succ_le_succ hlen, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hm
          · exact hall x hx'
      · rintro ⟨hlen, hall⟩
        cases ms with
        | nil => exact Or.inl rfl
        | cons m tl =>
            refine Or.inr ⟨(m, tl), ⟨?_, ?_⟩, rfl⟩
            · rw [Finset.mem_Icc]
              exact hall m List.mem_cons_self
            · refine (ih tl).mpr ⟨?_, fun x hx => hall x (List.mem_cons_of_mem m hx)⟩
              simp only [List.length_cons] at hlen
              omega

/-- The window-`K` σ-keyed leaf menu: ram rungs `H = 2j−1 ≤ 2K−1` for the ramified type,
inert heights `m ≤ K`, split heights `k ≤ K`; empty for every other σ. -/
noncomputable def chainLeaves (K : ℕ) (σ : FactorizationType) : Finset ChainLeaf :=
  if σ = ramType2 then (Finset.Icc 1 K).image (fun j => ChainLeaf.ram (2 * j - 1))
  else if σ = inertType2 then (Finset.Icc 1 K).image ChainLeaf.inert
  else if σ = splitType2 then (Finset.Icc 1 K).image ChainLeaf.split
  else ∅

/-- Window facts of a menu leaf: well-formed and keyed to σ. -/
theorem of_mem_chainLeaves {K : ℕ} {σ : FactorizationType} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K σ) : leafOK leaf ∧ leafType leaf = σ := by
  by_cases h1 : σ = ramType2
  · rw [chainLeaves, if_pos h1, Finset.mem_image] at h
    obtain ⟨j, hj, rfl⟩ := h
    rw [Finset.mem_Icc] at hj
    exact ⟨⟨⟨j - 1, by omega⟩, by omega⟩, by rw [leafType_ram, h1]⟩
  · rw [chainLeaves, if_neg h1] at h
    by_cases h2 : σ = inertType2
    · rw [if_pos h2, Finset.mem_image] at h
      obtain ⟨m, hm, rfl⟩ := h
      rw [Finset.mem_Icc] at hm
      exact ⟨hm.1, by rw [leafType_inert, h2]⟩
    · rw [if_neg h2] at h
      by_cases h3 : σ = splitType2
      · rw [if_pos h3, Finset.mem_image] at h
        obtain ⟨k, hk, rfl⟩ := h
        rw [Finset.mem_Icc] at hk
        exact ⟨hk.1, by rw [leafType_split, h3]⟩
      · rw [if_neg h3] at h
        exact absurd h (Finset.notMem_empty leaf)

/-- **The σ-keyed chain-shape menu** (n = 2 ONLY emission: the note's general-n chains are
OPEN-D3/D5 territory; the enumerator must not emit them). -/
noncomputable def chainShapes (n D K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  if n = 2 then
    (((msMenu D K).filter (fun ms => ms ≠ [])) ×ˢ chainLeaves K σ).image
      (fun x => chainLit x.1 x.2)
  else ∅

theorem mem_chainShapes {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ chainShapes n D K σ ↔ n = 2 ∧ ∃ ms leaf, ms ∈ msMenu D K ∧ ms ≠ []
      ∧ leaf ∈ chainLeaves K σ ∧ T = chainLit ms leaf := by
  constructor
  · intro hT
    by_cases hn : n = 2
    · subst hn
      rw [chainShapes, if_pos rfl, Finset.mem_image] at hT
      obtain ⟨⟨ms, leaf⟩, hmem, rfl⟩ := hT
      rw [Finset.mem_product, Finset.mem_filter] at hmem
      exact ⟨rfl, ms, leaf, hmem.1.1, hmem.1.2, hmem.2, rfl⟩
    · rw [chainShapes, if_neg hn] at hT
      exact absurd hT (Finset.notMem_empty T)
  · rintro ⟨rfl, ms, leaf, hms, hne, hleaf, rfl⟩
    rw [chainShapes, if_pos rfl, Finset.mem_image]
    exact ⟨(ms, leaf), by
      rw [Finset.mem_product, Finset.mem_filter]
      exact ⟨⟨hms, hne⟩, hleaf⟩, rfl⟩

/-- Depth window `D = 0` has NO chains (recovery to the W4 menu). -/
theorem chainShapes_zero (n K : ℕ) (σ : FactorizationType) : chainShapes n 0 K σ = ∅ := by
  by_cases hn : n = 2
  · subst hn
    rw [chainShapes, if_pos rfl]
    have hfil : (msMenu 0 K).filter (fun ms => ms ≠ []) = ∅ := by
      show ({[]} : Finset (List ℕ)).filter (fun ms => ms ≠ []) = ∅
      simp
    rw [hfil, Finset.empty_product, Finset.image_empty]
  · rw [chainShapes, if_neg hn]

/-- **The Wave-5 σ-keyed menu**: the Wave-4 menu extended by the depth-`≤ D` chains. -/
noncomputable def omMenu5 (n D K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  MultiSlopeMenu.omMenu4 n K σ ∪ chainShapes n D K σ

/-- **The recovery gate**: at depth window `D = 0` the Wave-5 menu IS the Wave-4 menu. -/
theorem omMenu5_zero (n K : ℕ) (σ : FactorizationType) :
    omMenu5 n 0 K σ = MultiSlopeMenu.omMenu4 n K σ := by
  rw [omMenu5, chainShapes_zero, Finset.union_empty]

/-- The two menu parts are disjoint (head order-slot `2` vs `{0, 1}`). -/
theorem omMenu4_chainShapes_disjoint (n D K : ℕ) (σ σ' : FactorizationType) :
    Disjoint (MultiSlopeMenu.omMenu4 n K σ) (chainShapes n D K σ') :=
  Finset.disjoint_left.mpr (fun T hT4 hTc => by
    obtain ⟨-, ms, leaf, -, -, -, rfl⟩ := mem_chainShapes.mp hTc
    exact headOrd_of_mem_omMenu4 hT4 (headOrd_chainLit ms leaf))

/-- Menu case analysis. -/
theorem mem_omMenu5_cases {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu5 n D K σ) :
    T ∈ MultiSlopeMenu.omMenu4 n K σ
      ∨ (n = 2 ∧ ∃ ms leaf, ms ∈ msMenu D K ∧ ms ≠ []
          ∧ leaf ∈ chainLeaves K σ ∧ T = chainLit ms leaf) := by
  rw [omMenu5, Finset.mem_union] at hT
  rcases hT with h | h
  · exact Or.inl h
  · exact Or.inr (mem_chainShapes.mp h)

/-- **Every Wave-5 menu shape names its type** (the cross-σ disjointness lever). -/
theorem mem_omMenu5_type {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu5 n D K σ) : typeOf5 n T = some σ := by
  rcases mem_omMenu5_cases hT with h | ⟨-, ms, leaf, -, -, hleaf, rfl⟩
  · rw [typeOf5_typeOf4_compat (headOrd_of_mem_omMenu4 h)]
    exact MultiSlopeMenu.mem_omMenu4_type h
  · rw [typeOf5_chainLit, (of_mem_chainLeaves hleaf).2]

/-- Distinct types have disjoint Wave-5 menus — at ANY window bounds. -/
theorem eq_of_mem_omMenu5 {n D D' K K' : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenu5 n D K σ) (h' : T ∈ omMenu5 n D' K' σ') : σ = σ' := by
  have h1 := mem_omMenu5_type h
  have h2 := mem_omMenu5_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### The chain types are already on the Wave-4 type menu (no type-menu growth) -/

theorem constERam_ramType2 : WildMenu.constERam 2 ramType2 :=
  ⟨2, le_refl 2, by decide, by decide, by decide⟩

/-- The partition `2 = 2` (the inert pattern). -/
def partInert : Nat.Partition 2 :=
  ⟨{2}, fun {i} hi => by rw [Multiset.mem_singleton] at hi; omega, by rfl⟩

/-- The partition `2 = 1 + 1` (the split pattern). -/
def partSplit : Nat.Partition 2 :=
  ⟨{1, 1}, fun {i} hi => by
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
    omega, by rfl⟩

theorem unramType_partInert : Order0.unramType 2 partInert = inertType2 := rfl

theorem unramType_partSplit : Order0.unramType 2 partSplit = splitType2 := rfl

theorem ramType2_mem_typeMenu4 : ramType2 ∈ MultiSlopeMenu.typeMenu4 2 := by
  rw [MultiSlopeMenu.typeMenu4, Finset.mem_union]
  refine Or.inl ?_
  rw [WildMenuPrep.typeMenuW, Finset.mem_union]
  exact Or.inr (WildMenuPrep.mem_constERamTypes.mpr constERam_ramType2)

theorem inertType2_mem_typeMenu4 : inertType2 ∈ MultiSlopeMenu.typeMenu4 2 := by
  rw [MultiSlopeMenu.typeMenu4, Finset.mem_union]
  refine Or.inl ?_
  rw [WildMenuPrep.typeMenuW, Finset.mem_union]
  refine Or.inl ?_
  rw [RealInstanceV2Prep.unramTypeMenu, Finset.mem_image]
  exact ⟨partInert, Finset.mem_univ _, unramType_partInert⟩

theorem splitType2_mem_typeMenu4 : splitType2 ∈ MultiSlopeMenu.typeMenu4 2 := by
  rw [MultiSlopeMenu.typeMenu4, Finset.mem_union]
  refine Or.inl ?_
  rw [WildMenuPrep.typeMenuW, Finset.mem_union]
  refine Or.inl ?_
  rw [RealInstanceV2Prep.unramTypeMenu, Finset.mem_image]
  exact ⟨partSplit, Finset.mem_univ _, unramType_partSplit⟩

/-- Off the Wave-4 type menu the chain branch is EMPTY (the three chain types are already
menu types, so no new type appears — `typeMenu5 := typeMenu4`). -/
theorem chainShapes_eq_empty_off_menu {n D K : ℕ} {σ : FactorizationType}
    (hσ : σ ∉ MultiSlopeMenu.typeMenu4 n) : chainShapes n D K σ = ∅ := by
  by_cases hn : n = 2
  · subst hn
    have h1 : σ ≠ ramType2 := fun hc => hσ (hc ▸ ramType2_mem_typeMenu4)
    have h2 : σ ≠ inertType2 := fun hc => hσ (hc ▸ inertType2_mem_typeMenu4)
    have h3 : σ ≠ splitType2 := fun hc => hσ (hc ▸ splitType2_mem_typeMenu4)
    have hleaves : chainLeaves K σ = ∅ := by
      rw [chainLeaves, if_neg h1, if_neg h2, if_neg h3]
    rw [chainShapes, if_pos rfl, hleaves, Finset.product_empty, Finset.image_empty]
  · rw [chainShapes, if_neg hn]

/-- Mixed types cannot occur at degree 2 (two distinct `e ≥ 2` groups need degree ≥ 5) — the
mixed W4 leg is vacuous wherever chains live. -/
theorem not_mixedOK_two (σ : FactorizationType) : ¬ MultiSlopeMenu.mixedOK 2 σ := by
  intro h
  have hlen := MultiSlopeMenu.two_le_eVals_length h
  have hsum := MultiSlopeMenu.sum_eFof h
  cases heV : MultiSlopeMenu.eVals σ with
  | nil => rw [heV] at hlen; simp at hlen
  | cons e₁ tl =>
      cases tl with
      | nil => rw [heV] at hlen; simp at hlen
      | cons e₂ tl' =>
          have he₁ : 2 ≤ e₁ := MultiSlopeMenu.eVals_two_le h e₁ (by
            rw [heV]; exact List.mem_cons_self)
          have he₂ : 2 ≤ e₂ := MultiSlopeMenu.eVals_two_le h e₂ (by
            rw [heV]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          have hF₁ : 1 ≤ MultiSlopeMenu.Fof σ e₁ := MultiSlopeMenu.Fof_pos h (by
            rw [heV]; exact List.mem_cons_self)
          have hF₂ : 1 ≤ MultiSlopeMenu.Fof σ e₂ := MultiSlopeMenu.Fof_pos h (by
            rw [heV]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          have hp₁ : 2 ≤ e₁ * MultiSlopeMenu.Fof σ e₁ :=
            le_trans (by omega) (Nat.mul_le_mul he₁ hF₁)
          have hp₂ : 2 ≤ e₂ * MultiSlopeMenu.Fof σ e₂ :=
            le_trans (by omega) (Nat.mul_le_mul he₂ hF₂)
          rw [heV, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons] at hsum
          omega

/-! ## 10. The box-level chain fiber, its counts, and the coefficient `C5` -/

/-- **The chain-stratum fiber predicate on the monic box** (blueprint §2-W5b `ChainCell`): the
`ChainPair` digit recursion read on the coefficient pair `(a₀, a₁)` at the root frame `(N, N)`
(the plain box — NO cluster conditioning; the one-time `p^{−2}` cluster factor is inside the
first step's (S2) digits, per the module docstring's normalization ledger). Semantically
meaningful at `n = 2` (the menu's only emission). -/
def ChainCell (ms : List ℕ) (leaf : ChainLeaf) {N n : ℕ}
    (f : QuotientBox.monicBox p N n) : Prop :=
  ChainPair p ms leaf N N ((f.1).coeff 0, (f.1).coeff 1)

/-- **The chain closed form on the box** (`n = 2`, above the level threshold
`N₀ = 2·Σms + leafNeed`). -/
theorem card_chainCell (ms : List ℕ) (leaf : ChainLeaf) (hms : ∀ m ∈ ms, 1 ≤ m)
    (hOK : leafOK leaf) {N : ℕ} (hN : 2 * ms.sum + leafNeed leaf ≤ N) :
    Nat.card {f : QuotientBox.monicBox p N 2 // ChainCell p ms leaf f}
      = (p - 1) ^ ms.length * leafCount p leaf (N - 2 * ms.sum) (N - ms.sum) := by
  have hN0 : 0 < N := by
    have := one_le_leafNeed leaf
    omega
  have e : {f : QuotientBox.monicBox p N 2 // ChainCell p ms leaf f}
      ≃ {a : ZMod (p ^ N) × ZMod (p ^ N) // ChainPair p ms leaf N N a} :=
    Equiv.subtypeEquiv (coeffEquiv p N hN0) (fun f => Iff.rfl)
  rw [Nat.card_congr e]
  exact card_chainPair p ms leaf hms hOK N N hN le_rfl

/-- **Small-`N` vanishing** below the threshold (any degree `n`). -/
theorem card_chainCell_smallN (ms : List ℕ) (leaf : ChainLeaf) {N n : ℕ}
    (hN : N < 2 * ms.sum + leafNeed leaf) :
    Nat.card {f : QuotientBox.monicBox p N n // ChainCell p ms leaf f} = 0 := by
  haveI : IsEmpty {f : QuotientBox.monicBox p N n // ChainCell p ms leaf f} :=
    ⟨fun x => chainPair_empty p ms leaf N N hN _ x.2⟩
  exact Nat.card_of_isEmpty

/-- The leaf volume exponent (the leaf's normalized mass is `pool · p^{−eLeaf}`; the `+ 2` on
`inert`/`split` and the `+ 1 + (H+1)/2 − …` bookkeeping on `ram` include the ONE-TIME cluster
factor `p^{−2}`, per the Case-A ledger). -/
def eLeaf : ChainLeaf → ℕ
  | .ram H => H + 1 + (H + 1) / 2
  | .inert m => 3 * m + 2
  | .split k => 3 * k + 2

/-- The chain volume exponent: `3·Σms` per the descend steps (cluster-conditional `p^{−3m_t}`
per step) plus the leaf's exponent (which prices the cluster once). -/
def chainVolExp (ms : List ℕ) (leaf : ChainLeaf) : ℕ := 3 * ms.sum + eLeaf leaf

theorem one_le_eLeaf (leaf : ChainLeaf) : 1 ≤ eLeaf leaf := by
  cases leaf <;> simp only [eLeaf] <;> omega

theorem chainVolExp_le_two_mul (ms : List ℕ) (leaf : ChainLeaf) {N : ℕ}
    (hN : 2 * ms.sum + leafNeed leaf ≤ N) : chainVolExp ms leaf ≤ 2 * N := by
  cases leaf <;> simp only [chainVolExp, eLeaf, leafNeed] at hN ⊢ <;> omega

/-- The leaf digit pool as a rational function of the residue cardinality:
`q − 1` (ram: nonzero height digit), `(q² − q)/2` (inert: root-free monic quadratics),
`q − 1` (split: nonzero vertex digit). -/
noncomputable def leafPoolQ : ChainLeaf → ℕ → ℚ
  | .ram _, q' => (q' : ℚ) - 1
  | .inert _, q' => ((q' : ℚ) ^ 2 - q') / 2
  | .split _, q' => (q' : ℚ) - 1

/-- **The chain closed form, cast to `ℚ`** in the `pool · p^{2N − volExp}` shape. -/
theorem card_chainCell_cast (ms : List ℕ) (leaf : ChainLeaf) (hms : ∀ m ∈ ms, 1 ≤ m)
    (hOK : leafOK leaf) {N : ℕ} (hN : 2 * ms.sum + leafNeed leaf ≤ N) :
    ((Nat.card {f : QuotientBox.monicBox p N 2 // ChainCell p ms leaf f} : ℕ) : ℚ)
      = ((p : ℚ) - 1) ^ ms.length * leafPoolQ leaf p
          * (p : ℚ) ^ (2 * N - chainVolExp ms leaf) := by
  have hp1 : 1 ≤ p := hp.out.one_le
  have hpsub : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [card_chainCell p ms leaf hms hOK hN]
  cases leaf with
  | ram H =>
      simp only [leafNeed] at hN
      simp only [leafCount, leafPoolQ, chainVolExp, eLeaf]
      push_cast [hpsub]
      have hXY : (p : ℚ) ^ (N - 2 * ms.sum - H - 1) * (p : ℚ) ^ (N - ms.sum - (H + 1) / 2)
          = (p : ℚ) ^ (2 * N - (3 * ms.sum + (H + 1 + (H + 1) / 2))) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← hXY]
      ring
  | inert m =>
      simp only [leafNeed] at hN
      simp only [leafCount, leafPoolQ, chainVolExp, eLeaf]
      push_cast [hpsub, card_noRootPairs_q]
      rw [show (p : ℚ) ^ (N - 2 * ms.sum - 2 * m - 1) * (p : ℚ) ^ (N - ms.sum - m - 1)
          = (p : ℚ) ^ (2 * N - (3 * ms.sum + (3 * m + 2))) from by
        rw [← pow_add]
        congr 1
        omega]
      ring
  | split k =>
      simp only [leafNeed] at hN
      simp only [leafCount, leafPoolQ, chainVolExp, eLeaf]
      push_cast [hpsub]
      have hXY : (p : ℚ) ^ (N - 2 * ms.sum - (2 * k + 1)) * (p : ℚ) ^ (N - ms.sum - k - 1)
          = (p : ℚ) ^ (2 * N - (3 * ms.sum + (3 * k + 2))) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← hXY]
      ring

/-! ### The coefficient: multiplicity polynomial × volume monomial -/

/-- The leaf multiplicity polynomial (`leafPoolQ` as a genuine `Polynomial ℚ`). -/
noncomputable def leafMult : ChainLeaf → Polynomial ℚ
  | .ram _ => X - 1
  | .inert _ => Polynomial.C (1 / 2 : ℚ) * (X ^ 2 - X)
  | .split _ => X - 1

/-- **The chain multiplicity polynomial**: `(X − 1)^depth · leafMult` — one `(q−1)` pool per
counted recentering digit, times the leaf pool. -/
noncomputable def chainMult (ms : List ℕ) (leaf : ChainLeaf) : Polynomial ℚ :=
  (X - 1) ^ ms.length * leafMult leaf

theorem eval_leafMult (leaf : ChainLeaf) (q' : ℕ) :
    (leafMult leaf).eval (q' : ℚ) = leafPoolQ leaf q' := by
  cases leaf <;> simp only [leafMult, leafPoolQ, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C] <;> ring

theorem eval_chainMult (ms : List ℕ) (leaf : ChainLeaf) (q' : ℕ) :
    (chainMult ms leaf).eval (q' : ℚ) = ((q' : ℚ) - 1) ^ ms.length * leafPoolQ leaf q' := by
  rw [chainMult, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one, eval_leafMult]

/-- **The chain coefficient** (the closed form as a rational function of the residue
cardinality): `chainC = chainMult(q') · q'^{−volExp}` — `(poly in q)·q^{−const}`. -/
noncomputable def chainC (ms : List ℕ) (leaf : ChainLeaf) (q' : ℕ) : ℚ :=
  (chainMult ms leaf).eval (q' : ℚ) * ((q' : ℚ) ^ chainVolExp ms leaf)⁻¹

/-- `(poly)·q^{−V}` is a uniform rational function (`num := P`, `den := X^V`). -/
theorem isRationalFn_poly_mul_pow_inv (P : Polynomial ℚ) (V : ℕ) :
    IsRationalFn (fun q' : ℕ => P.eval (q' : ℚ) * ((q' : ℚ) ^ V)⁻¹) := by
  refine ⟨P, X ^ V, pow_ne_zero V Polynomial.X_ne_zero, fun q hq => ?_⟩
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_⟩
  · rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero V hq0
  · rw [Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv]

theorem chainC_isRational (ms : List ℕ) (leaf : ChainLeaf) :
    IsRationalFn (chainC ms leaf) :=
  isRationalFn_poly_mul_pow_inv (chainMult ms leaf) (chainVolExp ms leaf)

/-- `chainC ≥ 0` at every natural `q'` (at `q' = 0` the volume factor kills it). -/
theorem chainC_nonneg (ms : List ℕ) (leaf : ChainLeaf) (q' : ℕ) : 0 ≤ chainC ms leaf q' := by
  rcases Nat.eq_zero_or_pos q' with rfl | hq
  · rw [chainC, show ((0 : ℕ) : ℚ) ^ chainVolExp ms leaf = 0 from by
      rw [Nat.cast_zero]
      exact zero_pow (by have h1 := one_le_eLeaf leaf; unfold chainVolExp; omega)]
    rw [inv_zero, mul_zero]
  · rw [chainC, eval_chainMult]
    have hq1 : (1 : ℚ) ≤ (q' : ℚ) := by exact_mod_cast hq
    refine mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) ?_)
      (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg q') _))
    cases leaf with
    | ram H => simp only [leafPoolQ]; linarith
    | inert m =>
        simp only [leafPoolQ]
        have hfac : ((q' : ℚ) ^ 2 - q') = (q' : ℚ) * ((q' : ℚ) - 1) := by ring
        rw [hfac]
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg q') (by linarith)) (by norm_num)
    | split k => simp only [leafPoolQ]; linarith

/-! ### `stratumCount5` and `C5` (at the real prime) -/

/-- **The Wave-5 stratum count**: on chain heads (order-slot `2`), the genuine `Nat.card` of
the `ChainCell` digit fiber on the real box; the Wave-4 count on every other shape. -/
noncomputable def stratumCount5 (n : ℕ) (T : ClusterShape) (N : ℕ) : ℚ :=
  if MultiSlopeMenu.headOrd T = 2 then
    ((Nat.card {f : QuotientBox.monicBox M9.realP N n //
        ChainCell M9.realP (decodeMs T) (decodeLeaf T) f} : ℕ) : ℚ)
  else MultiSlopeMenu.stratumCount4 n T N

theorem stratumCount5_of_headOrd_ne {n : ℕ} {T : ClusterShape}
    (h : MultiSlopeMenu.headOrd T ≠ 2) (N : ℕ) :
    stratumCount5 n T N = MultiSlopeMenu.stratumCount4 n T N := by
  rw [stratumCount5, if_neg h]

theorem stratumCount5_chainLit (n : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    stratumCount5 n (chainLit ms leaf) N
      = ((Nat.card {f : QuotientBox.monicBox M9.realP N n //
          ChainCell M9.realP ms leaf f} : ℕ) : ℚ) := by
  rw [stratumCount5, if_pos (headOrd_chainLit ms leaf), decodeMs_chainLit, decodeLeaf_chainLit]

theorem stratumCount5_nonneg (n : ℕ) (T : ClusterShape) (N : ℕ) :
    0 ≤ stratumCount5 n T N := by
  by_cases h : MultiSlopeMenu.headOrd T = 2
  · rw [stratumCount5, if_pos h]
    exact Nat.cast_nonneg _
  · rw [stratumCount5, if_neg h]
    exact MultiSlopeMenu.stratumCount4_nonneg n T N

/-- **The Wave-5 coefficient**: the chain closed form on chain heads, `C4` elsewhere. -/
noncomputable def C5 (T : ClusterShape) (q' : ℕ) : ℚ :=
  if MultiSlopeMenu.headOrd T = 2 then chainC (decodeMs T) (decodeLeaf T) q'
  else MultiSlopeMenu.C4 T q'

theorem C5_of_headOrd_ne {T : ClusterShape} (h : MultiSlopeMenu.headOrd T ≠ 2) (q' : ℕ) :
    C5 T q' = MultiSlopeMenu.C4 T q' := by
  rw [C5, if_neg h]

theorem C5_chainLit (ms : List ℕ) (leaf : ChainLeaf) (q' : ℕ) :
    C5 (chainLit ms leaf) q' = chainC ms leaf q' := by
  rw [C5, if_pos (headOrd_chainLit ms leaf), decodeMs_chainLit, decodeLeaf_chainLit]

/-- **`C5` is a uniform rational function of `q`** on every shape. -/
theorem C5_isRational (T : ClusterShape) : IsRationalFn (fun q' => C5 T q') := by
  by_cases h : MultiSlopeMenu.headOrd T = 2
  · simp only [C5, if_pos h]
    exact chainC_isRational _ _
  · simp only [C5, if_neg h]
    exact MultiSlopeMenu.C4_isRational T

/-! ### Level behavior: constancy above threshold, vanishing below, the tendsto tie -/

/-- **Level constancy of the normalized chain count** above the threshold: the normalized
count IS the coefficient — the Case-A ledger values, exactly. -/
theorem normStratumCount5_chain_levelConst (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) {N : ℕ}
    (hN : 2 * ms.sum + leafNeed leaf ≤ N) :
    stratumCount5 2 (chainLit ms leaf) N / (M9.realP : ℚ) ^ (2 * N)
      = chainC ms leaf M9.realP := by
  rw [stratumCount5_chainLit, card_chainCell_cast M9.realP ms leaf hms hOK hN,
    chainC, eval_chainMult]
  have hp0 : (M9.realP : ℚ) ≠ 0 := by norm_num [M9.realP]
  have hVle := chainVolExp_le_two_mul ms leaf hN
  rw [show (M9.realP : ℚ) ^ (2 * N)
      = (M9.realP : ℚ) ^ chainVolExp ms leaf * (M9.realP : ℚ) ^ (2 * N - chainVolExp ms leaf)
      from by rw [← pow_add]; congr 1; omega]
  have h1 : (M9.realP : ℚ) ^ chainVolExp ms leaf ≠ 0 := pow_ne_zero _ hp0
  have h2 : (M9.realP : ℚ) ^ (2 * N - chainVolExp ms leaf) ≠ 0 := pow_ne_zero _ hp0
  field_simp

/-- **The chain-leg counting limit** (the `stratum_tendsto_C` feed): the normalized chain
count is EVENTUALLY CONSTANT `= chainC(realP)`, hence tends to it. -/
theorem stratum_tendsto_C5_chain (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) :
    Filter.Tendsto
      (fun N => stratumCount5 2 (chainLit ms leaf) N / (M9.realP : ℚ) ^ (2 * N))
      Filter.atTop (nhds (chainC ms leaf M9.realP)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (2 * ms.sum + leafNeed leaf)] with N hN
  exact (normStratumCount5_chain_levelConst ms leaf hms hOK hN).symm

/-- **Monotone staircase** of the normalized chain count: `0, …, 0, c, c, …` joining at the
threshold `N₀ = 2·Σms + leafNeed`. -/
theorem normChainCount_mono (ms : List ℕ) (leaf : ChainLeaf)
    (hms : ∀ m ∈ ms, 1 ≤ m) (hOK : leafOK leaf) :
    Monotone (fun N => stratumCount5 2 (chainLit ms leaf) N / (M9.realP : ℚ) ^ (2 * N)) := by
  intro N₁ N₂ h12
  dsimp only
  rcases Nat.lt_or_ge N₁ (2 * ms.sum + leafNeed leaf) with hlt | hge
  · have hz : stratumCount5 2 (chainLit ms leaf) N₁ = 0 := by
      rw [stratumCount5_chainLit, card_chainCell_smallN M9.realP ms leaf hlt, Nat.cast_zero]
    rw [hz, zero_div]
    exact div_nonneg (stratumCount5_nonneg _ _ _)
      (le_of_lt (RealInstanceV2.realP_pow_pos _))
  · rw [normStratumCount5_chain_levelConst ms leaf hms hOK hge,
      normStratumCount5_chain_levelConst ms leaf hms hOK (le_trans hge h12)]

/-! ## 11. The Wave-5 fiber, the keystone disjointness, and the box bound -/

/-- The Wave-5 counting fiber: the `ChainCell` digit fiber on chain heads, `Fiber4` else. -/
def Fiber5 (n N : ℕ) (T : ClusterShape) (f : QuotientBox.monicBox M9.realP N n) : Prop :=
  if MultiSlopeMenu.headOrd T = 2 then
    ChainCell M9.realP (decodeMs T) (decodeLeaf T) f
  else MultiSlopeMenu.Fiber4 n N T f

/-- `stratumCount5` IS the fiber card. -/
theorem stratumCount5_eq_card (n N : ℕ) (T : ClusterShape) :
    stratumCount5 n T N
      = ((Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber5 n N T f} : ℕ) : ℚ) := by
  by_cases h : MultiSlopeMenu.headOrd T = 2
  · rw [stratumCount5, if_pos h]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    simp only [Fiber5, if_pos h]
  · rw [stratumCount5, if_neg h, MultiSlopeMenu.stratumCount4_eq_card]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    simp only [Fiber5, if_neg h]

/-- The chain fiber pins the exact root valuation `v(a₀) = 2m₁` (EVEN, `≥ 2`). -/
theorem chainCell_valuation {n N m : ℕ} {rest : List ℕ} {leaf : ChainLeaf}
    {f : QuotientBox.monicBox p N n} (h : ChainCell p (m :: rest) leaf f) :
    PadicLift.zmodValuation p N ((f.1).coeff 0) = 2 * m ∧ 2 * m < N := by
  obtain ⟨c, hstep, -⟩ := h
  have hdvd : p ^ (2 * m) ∣ ((f.1).coeff 0).val := hstep.1.1
  have hne : digit p N (2 * m) ((f.1).coeff 0) ≠ 0 := by
    rw [hstep.1.2]
    exact unit_sq_ne_zero p c
  have hlt := lt_of_dvd_digit_ne p hdvd hne
  exact ⟨(valuation_eq_iff_digit_ne p hlt hdvd).mpr hne, hlt⟩

/-- At `n = 2`, constant-e ramified types have `fSum = 1` (so their window heights are the
ODD multipliers `k`). -/
theorem constERam_two_fSum {σ : FactorizationType} (h : WildMenu.constERam 2 σ) :
    WildMenu.fSum σ = 1 := by
  have hf := WildMenu.constERam_fSum_pos h
  obtain ⟨e, he2, -, -, hprod⟩ := h
  by_contra hne
  have hf2 : 2 ≤ WildMenu.fSum σ := by omega
  have h4 : 4 ≤ e * WildMenu.fSum σ := by
    calc 4 = 2 * 2 := rfl
    _ ≤ e * WildMenu.fSum σ := Nat.mul_le_mul he2 hf2
  omega

/-- **Chain-vs-old fiber disjointness at `n = 2`**: the chain pins `v(a₀) = 2m₁` even `≥ 2`;
the order-0 separable fiber pins `v(a₀) = 0`; the W1/W3 window fiber pins `v(a₀) = k` ODD
(`gcd(k, 2) = 1`). -/
theorem chain_old_disjoint {D K K' N : ℕ} {σ' : FactorizationType} {T' : ClusterShape}
    (hN : 0 < N) {ms : List ℕ} {leaf : ChainLeaf} (hms : ms ∈ msMenu D K) (hmsne : ms ≠ [])
    (hT' : T' ∈ WildMenuW3.omMenuW3 2 K' σ')
    {f : QuotientBox.monicBox M9.realP N 2}
    (h1 : ChainCell M9.realP ms leaf f) (h2 : M9.realClassify 2 N f = T') : False := by
  cases ms with
  | nil => exact hmsne rfl
  | cons m rest =>
      have hm1 : 1 ≤ m := (((mem_msMenu D K (m :: rest)).mp hms).2 m List.mem_cons_self).1
      obtain ⟨hval, hltN⟩ := chainCell_valuation M9.realP h1
      rcases MultiSlopeMenu.mem_omMenuW3_cases hT' with ⟨lam, rfl⟩ | ⟨hc', k, hk1, hke, rfl⟩
      · have h0 := Order0.classify_eq_sepShape_only_if M9.realP 2 N hN (by norm_num) lam f h2
        have := h0.1
        omega
      · have hfs : WildMenu.fSum σ' = 1 := constERam_two_fSum hc'
        have hgcd : Nat.gcd k 2 = 1 := by
          rw [hfs] at hke
          simpa using hke
        have hv0 := MultiSlopeMenu.classify_Tselfloop_v0 (by norm_num : 0 < 2) hN
          (WildMenu.wShape_ne hc') h2
        have hveq : PadicLift.zmodValuation M9.realP N ((f.1).coeff 0)
            = WildMenu.fSum σ' * k := hv0.1
        rw [hfs, one_mul] at hveq
        have hdvd2 : (2 : ℕ) ∣ k := ⟨m, by omega⟩
        have h2g : (2 : ℕ) ∣ Nat.gcd k 2 := Nat.dvd_gcd hdvd2 dvd_rfl
        rw [hgcd] at h2g
        exact absurd (Nat.le_of_dvd one_pos h2g) (by norm_num)

/-- **The keystone pairwise disjointness of the Wave-5 fibers** across the whole menu family:
chain-vs-chain by the master digit-ledger conflict, chain-vs-old by the `v(a₀)` pins,
old-vs-old by the banked Wave-4 keystone. -/
theorem fiber5_disjoint {n D K N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {σ σ' : FactorizationType} {T T' : ClusterShape}
    (hσT : T ∈ omMenu5 n D K σ) (hσT' : T' ∈ omMenu5 n D K σ') (hTT : T ≠ T')
    (f : QuotientBox.monicBox M9.realP N n)
    (h1 : Fiber5 n N T f) (h2 : Fiber5 n N T' f) : False := by
  rcases mem_omMenu5_cases hσT with h4 | ⟨hn2, ms, leaf, hms, hmsne, hleaf, rfl⟩
  · rcases mem_omMenu5_cases hσT' with h4' | ⟨hn2', ms', leaf', hms', hmsne', hleaf', rfl⟩
    · rw [Fiber5, if_neg (headOrd_of_mem_omMenu4 h4)] at h1
      rw [Fiber5, if_neg (headOrd_of_mem_omMenu4 h4')] at h2
      exact MultiSlopeMenu.fiber4_disjoint hn hN h4 h4' hTT f h1 h2
    · subst hn2'
      rw [Fiber5, if_neg (headOrd_of_mem_omMenu4 h4)] at h1
      rw [Fiber5, if_pos (headOrd_chainLit ms' leaf'), decodeMs_chainLit,
        decodeLeaf_chainLit] at h2
      rcases MultiSlopeMenu.mem_omMenu4_cases h4 with hold | ⟨hOK, rfl⟩
      · rw [MultiSlopeMenu.Fiber4, if_neg (by
          rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hold]; omega)] at h1
        exact chain_old_disjoint hN hms' hmsne' hold h2 h1
      · exact absurd hOK (not_mixedOK_two σ)
  · subst hn2
    rw [Fiber5, if_pos (headOrd_chainLit ms leaf), decodeMs_chainLit,
      decodeLeaf_chainLit] at h1
    rcases mem_omMenu5_cases hσT' with h4' | ⟨-, ms', leaf', hms', hmsne', hleaf', rfl⟩
    · rw [Fiber5, if_neg (headOrd_of_mem_omMenu4 h4')] at h2
      rcases MultiSlopeMenu.mem_omMenu4_cases h4' with hold' | ⟨hOK', rfl⟩
      · rw [MultiSlopeMenu.Fiber4, if_neg (by
          rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hold']; omega)] at h2
        exact chain_old_disjoint hN hms hmsne hold' h1 h2
      · exact absurd hOK' (not_mixedOK_two σ')
    · rw [Fiber5, if_pos (headOrd_chainLit ms' leaf'), decodeMs_chainLit,
        decodeLeaf_chainLit] at h2
      have hidx : ¬(ms = ms' ∧ leaf = leaf') := fun ⟨ha, hb⟩ => hTT (by rw [ha, hb])
      exact chainPair_disjoint M9.realP ms leaf
        (fun x hx => (((mem_msMenu D K ms).mp hms).2 x hx).1) (of_mem_chainLeaves hleaf).1
        ms' leaf'
        (fun x hx => (((mem_msMenu D K ms').mp hms').2 x hx).1) (of_mem_chainLeaves hleaf').1
        hidx N N _ h1 h2

/-- The union re-indexing over the type menu (distinct σ have disjoint Wave-5 menus). -/
theorem sum_omMenu5_eq_biUnion (n D K : ℕ) {M : Type*} [AddCommMonoid M]
    (g : ClusterShape → M) :
    ∑ σ ∈ MultiSlopeMenu.typeMenu4 n, ∑ T ∈ omMenu5 n D K σ, g T
      = ∑ T ∈ (MultiSlopeMenu.typeMenu4 n).biUnion (fun σ => omMenu5 n D K σ), g T := by
  refine (Finset.sum_biUnion ?_).symm
  intro σ _hσ σ' _hσ' hne
  exact Finset.disjoint_left.mpr fun T hT hT' => hne (eq_of_mem_omMenu5 hT hT')

/-- **The Wave-5 box bound** (the `undecidedCount ≥ 0` feed): at every level `N ≥ 1` the total
Wave-5 decided count over the type menu is at most the box count — the fibers are
pairwise-disjoint box subsets (`fiber5_disjoint`). -/
theorem sum_stratumCount5_le_box (n D K N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    (∑ σ ∈ MultiSlopeMenu.typeMenu4 n, ∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rw [sum_omMenu5_eq_biUnion]
  set S := (MultiSlopeMenu.typeMenu4 n).biUnion (fun σ => omMenu5 n D K σ) with hS
  haveI hfin : Finite (QuotientBox.monicBox M9.realP N n) := by
    have hpos : 0 < Nat.card (QuotientBox.monicBox M9.realP N n) := by
      rw [QuotientBox.card_monicBox M9.realP N n hN]
      exact pow_pos (pow_pos (by norm_num [M9.realP]) N) n
    exact (Nat.card_pos_iff.mp hpos).2
  have hdisj : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' →
      ∀ f : QuotientBox.monicBox M9.realP N n, Fiber5 n N T f → Fiber5 n N T' f → False := by
    intro T hT T' hT' hne f h1 h2
    rw [hS, Finset.mem_biUnion] at hT hT'
    obtain ⟨σ, -, hT⟩ := hT
    obtain ⟨σ', -, hT'⟩ := hT'
    exact fiber5_disjoint hn hN hT hT' hne f h1 h2
  have key : (∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber5 n N T f})
      ≤ M9.realP ^ (n * N) := by
    have hle := MultiSlopeMenu.sum_card_disjoint_le S (Fiber5 n N) hdisj
    rw [QuotientBox.card_monicBox M9.realP N n hN] at hle
    calc (∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber5 n N T f})
        ≤ (M9.realP ^ N) ^ n := hle
      _ = M9.realP ^ (n * N) := by rw [← pow_mul, Nat.mul_comm]
  calc (∑ T ∈ S, stratumCount5 n T N)
      = ((∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber5 n N T f} : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun T _ => stratumCount5_eq_card n N T
    _ ≤ ((M9.realP ^ (n * N) : ℕ) : ℚ) := by exact_mod_cast key
    _ = (M9.realP : ℚ) ^ (n * N) := by push_cast; ring

/-! ## 12. Monotonicity of the normalized Wave-5 menu sum -/

/-- **FULL monotonicity of the normalized Wave-5 menu sum** (the `decided_mono` discharge):
the W4 part is banked; each chain leg is a `0, …, 0, c, c, …` staircase. -/
theorem normSum_omMenu5_mono (n D K : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    Monotone (fun N => (∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N)
      / (M9.realP : ℚ) ^ (n * N)) := by
  have hsplit : ∀ N, (∑ T ∈ omMenu5 n D K σ, stratumCount5 n T N)
      = (∑ T ∈ MultiSlopeMenu.omMenu4 n K σ, MultiSlopeMenu.stratumCount4 n T N)
        + ∑ T ∈ chainShapes n D K σ, stratumCount5 n T N := by
    intro N
    rw [omMenu5, Finset.sum_union (omMenu4_chainShapes_disjoint n D K σ σ)]
    congr 1
    exact Finset.sum_congr rfl (fun T hT =>
      stratumCount5_of_headOrd_ne (headOrd_of_mem_omMenu4 hT) N)
  intro N₁ N₂ h12
  simp only [hsplit, add_div]
  refine add_le_add ?_ ?_
  · exact MultiSlopeMenu.normSum_omMenu4_mono n K hn σ h12
  · rw [Finset.sum_div, Finset.sum_div]
    refine Finset.sum_le_sum (fun T hT => ?_)
    obtain ⟨hn2, ms, leaf, hms, hne, hleaf, rfl⟩ := mem_chainShapes.mp hT
    subst hn2
    exact normChainCount_mono ms leaf
      (fun x hx => (((mem_msMenu D K ms).mp hms).2 x hx).1)
      (of_mem_chainLeaves hleaf).1 h12

/-! ## 13. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms noRootPairs
#print axioms two_mul_card_noRootPairs
#print axioms card_noRootPairs_q
#print axioms card_exists_eq_mul
#print axioms card_mem_fiber
#print axioms card_dvd_digit_eq
#print axioms card_dvd_digitSet
#print axioms card_dvd_digit_ne
#print axioms card_pair_digitSet
#print axioms LeafPair
#print axioms leafCount
#print axioms clusterPair_of_leafPair
#print axioms card_leafPair
#print axioms leafPair_empty
#print axioms descendPair
#print axioms ChainPair
#print axioms clusterPair_of_chainPair
#print axioms descendPair_eq_stratumPairEquiv
#print axioms card_step
#print axioms stratumPair_unit_unique
#print axioms card_chainPair
#print axioms chainPair_empty
#print axioms digit_conflict
#print axioms leafPair_disjoint
#print axioms leaf_step_disjoint
#print axioms step_step_disjoint
#print axioms chainPair_disjoint
#print axioms chainLit
#print axioms decodeMs_chainLit
#print axioms decodeLeaf_chainLit
#print axioms chainLit_injective
#print axioms headOrd_of_mem_omMenu4
#print axioms typeOf5
#print axioms typeOf5_chainLit
#print axioms typeOf5_typeOf4_compat
#print axioms msMenu
#print axioms mem_msMenu
#print axioms chainLeaves
#print axioms of_mem_chainLeaves
#print axioms chainShapes
#print axioms mem_chainShapes
#print axioms chainShapes_zero
#print axioms omMenu5
#print axioms omMenu5_zero
#print axioms mem_omMenu5_cases
#print axioms mem_omMenu5_type
#print axioms eq_of_mem_omMenu5
#print axioms ramType2_mem_typeMenu4
#print axioms inertType2_mem_typeMenu4
#print axioms splitType2_mem_typeMenu4
#print axioms chainShapes_eq_empty_off_menu
#print axioms not_mixedOK_two
#print axioms ChainCell
#print axioms card_chainCell
#print axioms card_chainCell_smallN
#print axioms card_chainCell_cast
#print axioms chainMult
#print axioms chainC
#print axioms chainC_isRational
#print axioms chainC_nonneg
#print axioms stratumCount5
#print axioms stratumCount5_chainLit
#print axioms stratumCount5_nonneg
#print axioms C5
#print axioms C5_isRational
#print axioms normStratumCount5_chain_levelConst
#print axioms stratum_tendsto_C5_chain
#print axioms normChainCount_mono
#print axioms Fiber5
#print axioms stratumCount5_eq_card
#print axioms chainCell_valuation
#print axioms chain_old_disjoint
#print axioms fiber5_disjoint
#print axioms sum_stratumCount5_le_box
#print axioms normSum_omMenu5_mono
end AxCheck

end LeanUrat.OM.ChainMenu
