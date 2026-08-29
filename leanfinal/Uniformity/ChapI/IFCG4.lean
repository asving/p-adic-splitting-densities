/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG0
import Uniformity.Density.Transport

/-!
# Uniformity.ChapI.IFCG4 — the uniform-`a0` campaign's finite-field census (`A0G-FF`)

**[A0G5 2026-08-28]** — unit A0G5 (`docs/in-progress/A0_GENERAL_2026-08-28.md` §6, rows
`A0G-FF0` and `A0G-FF1`; verdict `runs/wave-c/verdict_A0G5.md`). Part of the `IFCG*` series.
Nothing here is signed; nothing binds into leanspec; no landed file is touched. Zero `sorry`,
zero new axiom; AxCheck footer expects Lean core only.

## §1 — `A0G-FF0`: the irreducible census `I_δ(q)`

Blueprint §4.1's necklace count: for `δ ≥ 1`, `I_δ(q) = (1/δ) Σ_{d∣δ} μ(d) q^(δ/d)` is the
number of monic irreducible polynomials of degree `δ` over a field of cardinality `q`. Mathlib
has no packaged theorem computing this (confirmed by exploration: no `card_irreducible`,
`necklace`, or Möbius-necklace lemma anywhere in `Mathlib.FieldTheory.Finite.*` or
`Mathlib.RingTheory.Polynomial.*`). Per the unit's own contingency clause, the route taken is
**direct, unconditional, elementary proof** at `δ = 1, 2, 3, 4` (the pinned gate), built on one
reusable general mechanism (§0 below): peeling a root-multiset off a monic polynomial via the
LANDED `Polynomial.exists_prod_multiset_X_sub_C_mul`. No carried hypothesis is needed for the
pinned cases; the fully general `∀ δ` statement (needing a Galois/splitting-field argument, via
e.g. `FiniteField.Extension`) is NOT attempted here and is left open, honestly, for a future
node — see the "What this does NOT prove" section below.

## §2 — `A0G-FF1`: the falling-factorial configuration census

The number of monic degree-`n` polynomials whose factorization-into-monic-irreducibles matches
a given residue pattern (blueprint §4.1; `IFCG0.ResiduePattern n`): for each residue degree `δ`
appearing in the pattern, choose that many DISTINCT monic irreducibles of degree `δ` from the
`I_δ(q)` available, unordered within each repeated-multiplicity class. `configCount` packages
this as a falling-factorial-over-symmetry formula. The quartic instance is checked against every
row of blueprint §8's table, and the eleven rows are checked to sum to `q⁴`.

## What this does NOT prove

Neither §1 nor §2 constructs the general-`n` theorem. §1 pins `δ = 1, 2, 3, 4` by direct
argument; the Möbius closed form is also verified arithmetically for every `δ` (as a pure
identity in `q`, independent of field theory) but its GENERAL connection to actual irreducible
counts is not proved past `δ = 4`. §2's `configCount` is a general arithmetic DEFINITION, but
the theorem that it counts actual monic polynomials is proved only at `n = 4` (the quartic
table), by direct case analysis reusing §1's machinery — not as a general-`n` bijection. Both
gaps are exactly the blueprint's own `A0G-GC`/`A0G-NP` territory (§4.2 onward), never claimed
closed here.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFCG4

open Polynomial Uniformity.Density

attribute [local instance] Classical.propDecidable

/-! ## §0 — the peeling mechanism: roots off a monic polynomial, over a finite field -/

section Peel

variable {K : Type*} [Field K] [Fintype K]

/-- **The ambient carrier**: monic polynomials of exact degree `n`, as a subtype
of `Polynomial K` (finite once `K` is finite, via `monicOfDegEquiv` below). -/
abbrev MonicOfDeg (K : Type*) [Field K] (n : ℕ) : Type _ :=
  {f : Polynomial K // f.Monic ∧ f.natDegree = n}

/-- **Coefficient-vector encoding**, reusing the landed `monicPoly` / `exists_monicPoly_eq`
(`Uniformity.Density.Transport`, CN-01): every monic degree-`n` polynomial is `monicPoly a` for a
UNIQUE `a : Fin n → K`. -/
def monicOfDegEquiv (K : Type*) [Field K] (n : ℕ) : (Fin n → K) ≃ MonicOfDeg K n where
  toFun a := ⟨monicPoly a, monicPoly_monic a, monicPoly_natDegree a⟩
  invFun f := (Uniformity.Density.exists_monicPoly_eq f.2.1 f.2.2).choose
  left_inv a := by
    funext i
    have hspec := (Uniformity.Density.exists_monicPoly_eq (monicPoly_monic a) (monicPoly_natDegree a)).choose_spec
    have hi : (monicPoly ((Uniformity.Density.exists_monicPoly_eq (monicPoly_monic a) (monicPoly_natDegree a)).choose)).coeff (i : ℕ)
        = (monicPoly a).coeff (i : ℕ) := by rw [hspec]
    rwa [monicPoly_coeff_lt _ i.isLt, monicPoly_coeff_lt _ i.isLt] at hi
  right_inv f := Subtype.ext (Uniformity.Density.exists_monicPoly_eq f.2.1 f.2.2).choose_spec

instance instFintypeMonicOfDeg (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Fintype (MonicOfDeg K n) := Fintype.ofEquiv _ (monicOfDegEquiv K n)

theorem card_monicOfDeg (n : ℕ) : Fintype.card (MonicOfDeg K n) = Fintype.card K ^ n := by
  rw [← Fintype.card_congr (monicOfDegEquiv K n), Fintype.card_fun, Fintype.card_fin]

theorem natCard_monicOfDeg (n : ℕ) :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n} = Fintype.card K ^ n := by
  rw [Nat.card_eq_fintype_card]
  exact card_monicOfDeg n

omit [Fintype K] in
/-- **A monic polynomial's cofactor, after peeling off ITS OWN full roots multiset, is monic.**
Both `f` and the linear part `A := ∏ (X - a)` (over `f.roots`) are monic; cancel in the domain. -/
theorem monic_cofactor_of_prod_multiset_X_sub_C_mul {f g : Polynomial K}
    (hf : f.Monic) (hmul : (Multiset.map (fun a => X - C a) f.roots).prod * g = f) :
    g.Monic := by
  have hA : (Multiset.map (fun a => X - C a) f.roots).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hlc : (Multiset.map (fun a => X - C a) f.roots).prod.leadingCoeff * g.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, hmul]
    exact hf
  rwa [hA.leadingCoeff, one_mul] at hlc

omit [Fintype K] in
/-- **The generic obstruction: a monic polynomial's root-count is never exactly one short of its
degree.** Peel the full roots multiset off `f` (`exists_prod_multiset_X_sub_C_mul`); the cofactor
`g` is monic (previous lemma) of degree `f.natDegree - f.roots.card` and has NO roots
(`hgroots`). If `f.roots.card = f.natDegree - 1` then `g.natDegree = 1`, but a monic degree-`1`
polynomial always HAS a root (`roots_degree_eq_one`) — contradiction. -/
theorem roots_card_ne_natDegree_sub_one {f : Polynomial K} (hf : f.Monic)
    (hn : 1 ≤ f.natDegree) : f.roots.card ≠ f.natDegree - 1 := by
  intro heq
  obtain ⟨g, hmul, hcard, hgroots⟩ := Polynomial.exists_prod_multiset_X_sub_C_mul f
  have hgmonic : g.Monic := monic_cofactor_of_prod_multiset_X_sub_C_mul hf hmul
  have hgdeg : g.natDegree = 1 := by omega
  have hgne : g ≠ 0 := hgmonic.ne_zero
  have hgdeg' : g.degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hgne, hgdeg]
    rfl
  have hgr := Polynomial.roots_degree_eq_one hgdeg'
  rw [hgr] at hgroots
  exact absurd hgroots (by simp)

/-- **A "no-root" degree-`d` monic polynomial**, as a bare subtype. -/
abbrev NoRoot (K : Type*) [Field K] (d : ℕ) : Type _ :=
  {g : Polynomial K // g.Monic ∧ g.natDegree = d ∧ g.roots = 0}

instance instFiniteNoRoot (d : ℕ) : Finite (NoRoot K d) := by
  apply Finite.of_injective (fun g : NoRoot K d => (⟨g.1, g.2.1, g.2.2.1⟩ : MonicOfDeg K d))
  intro a b h
  have h1 : a.1 = b.1 := by injection h
  exact Subtype.ext h1

instance instFiniteRootsCard (n k : ℕ) :
    Finite {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k} := by
  apply Finite.of_injective (fun f => (⟨f.1, f.2.1, f.2.2.1⟩ : MonicOfDeg K n))
  intro a b h
  have h1 : a.1 = b.1 := by injection h
  exact Subtype.ext h1

/-- **Reassembly**: a `k`-multiset of roots plus a roots-free monic cofactor of degree `n - k`
reassemble into a monic degree-`n` polynomial with exactly that root multiset (hence `roots.card
= k`). The forward half of the peel bijection. -/
def peelPack (n k : ℕ) (hk : k ≤ n) :
    Sym K k × NoRoot K (n - k) →
      {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k} :=
  fun sg =>
    have hA : (Multiset.map (fun a => X - C a) (sg.1 : Multiset K)).prod.Monic :=
      Polynomial.monic_multisetProd_X_sub_C _
    have hAdeg : (Multiset.map (fun a => X - C a) (sg.1 : Multiset K)).prod.natDegree = k := by
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]; exact sg.1.2
    have hAroots : (Multiset.map (fun a => X - C a) (sg.1 : Multiset K)).prod.roots
        = (sg.1 : Multiset K) := Polynomial.roots_multiset_prod_X_sub_C _
    ⟨(Multiset.map (fun a => X - C a) (sg.1 : Multiset K)).prod * sg.2.1,
     hA.mul sg.2.2.1,
     by rw [Polynomial.natDegree_mul hA.ne_zero sg.2.2.1.ne_zero, hAdeg, sg.2.2.2.1]; omega,
     by
       rw [Polynomial.roots_mul (mul_ne_zero hA.ne_zero sg.2.2.1.ne_zero), hAroots, sg.2.2.2.2]
       simpa using sg.1.2⟩

omit [Fintype K] in
theorem peelPack_injective (n k : ℕ) (hk : k ≤ n) : Function.Injective (peelPack (K := K) n k hk) := by
  rintro ⟨s1, g1, hg1m, hg1d, hg1r⟩ ⟨s2, g2, hg2m, hg2d, hg2r⟩ heq
  simp only [peelPack, Subtype.mk.injEq] at heq
  have hAeq :
      (Multiset.map (fun a => X - C a) (s1 : Multiset K)).prod * g1
        = (Multiset.map (fun a => X - C a) (s2 : Multiset K)).prod * g2 := heq
  have hroots : (Multiset.map (fun a => X - C a) (s1 : Multiset K)).prod.roots
        + g1.roots
      = (Multiset.map (fun a => X - C a) (s2 : Multiset K)).prod.roots + g2.roots := by
    rw [← Polynomial.roots_mul (mul_ne_zero (Polynomial.monic_multisetProd_X_sub_C _).ne_zero hg1m.ne_zero),
      ← Polynomial.roots_mul (mul_ne_zero (Polynomial.monic_multisetProd_X_sub_C _).ne_zero hg2m.ne_zero),
      hAeq]
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C, hg1r, hg2r,
    add_zero, add_zero] at hroots
  have hs : s1 = s2 := Subtype.ext hroots
  have hAeq' : (Multiset.map (fun a => X - C a) (s1 : Multiset K)).prod
      = (Multiset.map (fun a => X - C a) (s2 : Multiset K)).prod := by rw [hs]
  have hg : g1 = g2 := by
    have hne : (Multiset.map (fun a => X - C a) (s1 : Multiset K)).prod ≠ 0 :=
      (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
    apply mul_left_cancel₀ hne
    rw [hAeq, ← hAeq']
  refine Prod.ext hs ?_
  exact Subtype.ext hg

/-- **Extraction**: a monic degree-`n` polynomial with exactly `k` roots decomposes, via
`exists_prod_multiset_X_sub_C_mul`, into its root multiset and a roots-free cofactor of degree
`n - k`. The backward half of the peel bijection (built via `Classical.choose`, hence not
literally the inverse of `peelPack` — but injective, which is all `Nat.card` needs). -/
def peelExtract (n k : ℕ) :
    {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k} →
      Sym K k × NoRoot K (n - k) :=
  fun f =>
    have hchoice := Polynomial.exists_prod_multiset_X_sub_C_mul f.1
    ⟨⟨f.1.roots, f.2.2.2⟩,
     ⟨hchoice.choose,
      monic_cofactor_of_prod_multiset_X_sub_C_mul f.2.1 hchoice.choose_spec.1,
      by
        have hspec := hchoice.choose_spec.2.1
        have hd := f.2.2.1
        have hc := f.2.2.2
        omega,
      hchoice.choose_spec.2.2⟩⟩

omit [Fintype K] in
theorem peelExtract_injective (n k : ℕ) : Function.Injective (peelExtract (K := K) n k) := by
  rintro ⟨f1, hf1m, hf1d, hf1c⟩ ⟨f2, hf2m, hf2d, hf2c⟩ heq
  have hroots : f1.roots = f2.roots :=
    congrArg (fun x : Sym K k × NoRoot K (n - k) => (x.1 : Multiset K)) heq
  have hg : (Polynomial.exists_prod_multiset_X_sub_C_mul f1).choose
      = (Polynomial.exists_prod_multiset_X_sub_C_mul f2).choose :=
    congrArg (fun x : Sym K k × NoRoot K (n - k) => (x.2 : Polynomial K)) heq
  apply Subtype.ext
  show f1 = f2
  have hc1 := (Polynomial.exists_prod_multiset_X_sub_C_mul f1).choose_spec.1
  have hc2 := (Polynomial.exists_prod_multiset_X_sub_C_mul f2).choose_spec.1
  rw [← hc1, ← hc2, hg, hroots]

/-- **The peel cardinality identity.** -/
theorem card_rootsCard_eq (n k : ℕ) (hk : k ≤ n) :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k}
      = Fintype.card (Sym K k) * Nat.card (NoRoot K (n - k)) := by
  have hle1 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k}
      ≤ Nat.card (Sym K k × NoRoot K (n - k)) :=
    Nat.card_le_card_of_injective _ (peelExtract_injective n k)
  have hle2 : Nat.card (Sym K k × NoRoot K (n - k))
      ≤ Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k} :=
    Nat.card_le_card_of_injective _ (peelPack_injective n k hk)
  have : Nat.card (Sym K k × NoRoot K (n - k))
      = Fintype.card (Sym K k) * Nat.card (NoRoot K (n - k)) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card]
  omega

omit [Fintype K] in
/-- **Flat/nested subtype conversion.** The "peel at `k`" set, phrased as a subtype-of-a-subtype
(as produced by fibering over `roots.card`), carries the same cardinality as the FLAT
three-conjunction subtype `card_rootsCard_eq` is stated for. -/
def flatEquivNested (n k : ℕ) :
    {a : {f : Polynomial K // f.Monic ∧ f.natDegree = n} // (a.1 : Polynomial K).roots.card = k} ≃
      {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = k} where
  toFun a := ⟨a.1.1, a.1.2.1, a.1.2.2, a.2⟩
  invFun f := ⟨⟨f.1, f.2.1, f.2.2.1⟩, f.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype K] in
/-- **A finite type's cardinality is the sum over the fibers of a `ℕ`-valued function bounded by
`n`.** Reused as the exhaustive-case-split engine for `n = 2, 3, 4` below. -/
theorem card_eq_sum_card_fiber_range {α : Type*} [Finite α] (g : α → ℕ) (n : ℕ)
    (hg : ∀ a, g a < n + 1) :
    Nat.card α = ∑ b ∈ Finset.range (n + 1), Nat.card {a : α // g a = b} := by
  have hmaps : ∀ b ∈ Finset.range (n + 1), {a | g a = b}.Finite := fun b _ => Set.toFinite _
  have h := Finset.card_preimage_eq_sum_card_image_eq (f := g) (s := Finset.range (n + 1)) hmaps
  rwa [show g ⁻¹' ↑(Finset.range (n + 1)) = (Set.univ : Set α) from
      Set.eq_univ_of_forall (fun a => Finset.mem_coe.2 (Finset.mem_range.2 (hg a))),
    Nat.card_congr (Equiv.Set.univ α)] at h

/-- **The exhaustive partition of `MonicOfDeg K n` by `roots.card`, as a sum over `0..n`.** -/
theorem card_monicOfDeg_eq_sum_rootsCard (n : ℕ) :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n}
      = ∑ b ∈ Finset.range (n + 1),
          Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = b} := by
  have h := card_eq_sum_card_fiber_range
    (α := {f : Polynomial K // f.Monic ∧ f.natDegree = n})
    (g := fun f => (f.1 : Polynomial K).roots.card) (n := n)
    (fun f => by
      have h1 := Polynomial.card_roots' f.1
      have h2 := f.2.2
      omega)
  rw [h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact Nat.card_congr (flatEquivNested n b)

end Peel

/-! ## §1 — `A0G-FF0`: the irreducible census, pinned at `δ = 1, 2, 3, 4` -/

section FF0

variable {K : Type*} [Field K] [Fintype K]

/-- **`I_1(q) = q`.** Every monic linear polynomial is irreducible, and the monic linear
polynomials biject with `K` via the constant term. -/
theorem card_irred_one :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 1 ∧ Irreducible f}
      = Fintype.card K := by
  have hall : ∀ f : Polynomial K, f.Monic → f.natDegree = 1 → Irreducible f := by
    intro f hf hd
    refine Polynomial.Monic.irreducible_of_degree_eq_one ?_ hf
    rw [Polynomial.degree_eq_natDegree hf.ne_zero, hd]
    rfl
  have e : {f : Polynomial K // f.Monic ∧ f.natDegree = 1 ∧ Irreducible f}
      ≃ {f : Polynomial K // f.Monic ∧ f.natDegree = 1} :=
    ⟨fun f => ⟨f.1, f.2.1, f.2.2.1⟩, fun f => ⟨f.1, f.2.1, f.2.2, hall f.1 f.2.1 f.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e]
  exact natCard_monicOfDeg 1 |>.trans (pow_one _)

/-- **`NoRoot K 0` has exactly one element** — the constant `1`: a monic degree-`0` polynomial
IS `1` (`Monic.natDegree_eq_zero_iff_eq_one`), and `(1 : Polynomial K).roots = 0`
(`roots_one`). -/
theorem card_noRoot_zero : Nat.card (NoRoot K 0) = 1 := by
  have hAll : ∀ g : Polynomial K, g.Monic → g.natDegree = 0 → g.roots = 0 := by
    intro g hg hd
    have hdeg : g.degree ≤ 0 := by
      calc g.degree ≤ (g.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ = 0 := by rw [hd]; rfl
    rw [hg.degree_le_zero_iff_eq_one.mp hdeg]
    simpa using Polynomial.roots_one
  have e : NoRoot K 0 ≃ {f : Polynomial K // f.Monic ∧ f.natDegree = 0} :=
    ⟨fun g => ⟨g.1, g.2.1, g.2.2.1⟩, fun f => ⟨f.1, f.2.1, f.2.2, hAll f.1 f.2.1 f.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, natCard_monicOfDeg]
  simp

omit [Fintype K] in
/-- **The degree-`k` bucket is empty at `k = n - 1`** (any `n ≥ 1`), packaged as an
`IsEmpty` instance so `Nat.card` of it vanishes by `Nat.card_of_isEmpty`. -/
theorem card_rootsCard_natDegree_sub_one (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = n - 1} = 0 := by
  have hempty : IsEmpty {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ f.roots.card = n - 1} := by
    constructor
    intro f
    have hne := roots_card_ne_natDegree_sub_one f.2.1 (by rw [f.2.2.1]; exact hn)
    rw [f.2.2.1] at hne
    exact hne f.2.2.2
  exact Nat.card_of_isEmpty

omit [Fintype K] in
/-- **`NoRoot` IS the irreducible count, at degree `2` or `3`.** Direct restatement of the `≤ 3`
lemma at the subtype level. -/
theorem card_noRoot_eq_card_irred (n : ℕ) (h2 : 2 ≤ n) (h3 : n ≤ 3) :
    Nat.card (NoRoot K n)
      = Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = n ∧ Irreducible f} := by
  have hiff : ∀ f : Polynomial K, f.Monic → f.natDegree = n → (f.roots = 0 ↔ Irreducible f) := by
    intro f hf hd
    rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hf (hd ▸ h2) (hd ▸ h3)]
  exact Nat.card_congr
    ⟨fun f => ⟨f.1, f.2.1, f.2.2.1, (hiff f.1 f.2.1 f.2.2.1).mp f.2.2.2⟩,
     fun f => ⟨f.1, f.2.1, f.2.2.1, (hiff f.1 f.2.1 f.2.2.1).mpr f.2.2.2⟩,
     fun _ => rfl, fun _ => rfl⟩

/-- **`I_2(q) = q² - |Sym K 2|`**, i.e. `q² - C(q+1,2)` (the closed form is pinned in §2). The
degree-`2` monics split as `roots.card = 0` (`= NoRoot K 2`, irreducible by the `≤ 3` lemma)
plus `roots.card = 2` (splits completely, `Sym K 2`); `roots.card = 1` is empty. -/
theorem card_noRoot_two :
    Nat.card (NoRoot K 2) + Fintype.card (Sym K 2) = Fintype.card K ^ 2 := by
  have hb2 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 2 ∧ f.roots.card = 2}
      = Fintype.card (Sym K 2) := by
    have h := card_rootsCard_eq (K := K) 2 2 (le_refl 2)
    rw [card_noRoot_zero, mul_one] at h
    simpa using h
  have hb1 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 2 ∧ f.roots.card = 1} = 0 :=
    card_rootsCard_natDegree_sub_one (K := K) 2 (by omega)
  have hb0 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 2 ∧ f.roots.card = 0}
      = Nat.card (NoRoot K 2) := by
    apply Nat.card_congr
    exact ⟨fun f => ⟨f.1, f.2.1, f.2.2.1, Multiset.card_eq_zero.mp f.2.2.2⟩,
      fun f => ⟨f.1, f.2.1, f.2.2.1, Multiset.card_eq_zero.mpr f.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hsum := card_monicOfDeg_eq_sum_rootsCard (K := K) 2
  rw [natCard_monicOfDeg] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  omega

/-- **The named `I_2` census: `q² = 2·I_2(q) + |Sym K 2|` is NOT stated** — the counting fact is
`card_noRoot_two`; this corollary just names the irreducible-count reading. -/
theorem card_irred_two :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 2 ∧ Irreducible f}
      + Fintype.card (Sym K 2) = Fintype.card K ^ 2 := by
  rw [← card_noRoot_eq_card_irred 2 (le_refl 2) (by omega)]
  exact card_noRoot_two

/-- **`I_3(q) = q³ - |Sym K 3| - q·I_2(q)`** (closed form pinned in §2). The degree-`3` monics
split as `roots.card = 0` (`NoRoot K 3`), `roots.card = 1` (peel one root, cofactor `NoRoot K
2`), and `roots.card = 3` (splits completely, `Sym K 3`); `roots.card = 2` is empty. -/
theorem card_noRoot_three :
    Nat.card (NoRoot K 3) + Fintype.card (Sym K 1) * Nat.card (NoRoot K 2)
      + Fintype.card (Sym K 3) = Fintype.card K ^ 3 := by
  have hb3 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 3 ∧ f.roots.card = 3}
      = Fintype.card (Sym K 3) := by
    have h := card_rootsCard_eq (K := K) 3 3 (le_refl 3)
    rw [card_noRoot_zero, mul_one] at h
    simpa using h
  have hb1 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 3 ∧ f.roots.card = 1}
      = Fintype.card (Sym K 1) * Nat.card (NoRoot K 2) := by
    have h := card_rootsCard_eq (K := K) 3 1 (by omega)
    simpa using h
  have hb2 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 3 ∧ f.roots.card = 2} = 0 :=
    card_rootsCard_natDegree_sub_one (K := K) 3 (by omega)
  have hb0 : Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 3 ∧ f.roots.card = 0}
      = Nat.card (NoRoot K 3) := by
    apply Nat.card_congr
    exact ⟨fun f => ⟨f.1, f.2.1, f.2.2.1, Multiset.card_eq_zero.mp f.2.2.2⟩,
      fun f => ⟨f.1, f.2.1, f.2.2.1, Multiset.card_eq_zero.mpr f.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hsum := card_monicOfDeg_eq_sum_rootsCard (K := K) 3
  rw [natCard_monicOfDeg] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  omega

theorem card_irred_three :
    Nat.card {f : Polynomial K // f.Monic ∧ f.natDegree = 3 ∧ Irreducible f}
      + Fintype.card (Sym K 1) * Nat.card (NoRoot K 2)
      + Fintype.card (Sym K 3) = Fintype.card K ^ 3 := by
  rw [← card_noRoot_eq_card_irred 3 (by omega) (le_refl 3)]
  exact card_noRoot_three

/-! ### Degree 4: the extra "two irreducible quadratics" case

`NoRoot K 4` is NOT the irreducible count at degree `4` (the `≤ 3` lemma does not reach here):
a monic quartic with no root can also be a product of two monic irreducible quadratics. This
subsection isolates exactly that extra bucket. -/

/-- **The named irreducible-of-degree-`d` carrier.** -/
abbrev IrredOfDeg (K : Type*) [Field K] (d : ℕ) : Type _ :=
  {f : Polynomial K // f.Monic ∧ f.natDegree = d ∧ Irreducible f}

instance instFiniteIrredOfDeg (d : ℕ) : Finite (IrredOfDeg K d) := by
  apply Finite.of_injective (fun f : IrredOfDeg K d => (⟨f.1, f.2.1, f.2.2.1⟩ : MonicOfDeg K d))
  intro a b h
  have h1 : a.1 = b.1 := by injection h
  exact Subtype.ext h1

noncomputable instance instFintypeIrredOfDeg (d : ℕ) : Fintype (IrredOfDeg K d) :=
  Fintype.ofFinite _

omit [Fintype K] in
/-- **Monic cancellation on the left**, general form (not tied to a roots-multiset factor). -/
theorem monic_of_mul_monic_left {f g h : Polynomial K} (hf : f.Monic) (hg : g.Monic)
    (hfgh : g * h = f) : h.Monic := by
  have h1 : g.leadingCoeff * h.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, hfgh]; exact hf
  rwa [hg.leadingCoeff, one_mul] at h1

omit [Fintype K] in
/-- **A monic quartic with no root and no irreducible-quartic factorization is a product of
TWO monic irreducible quadratics.** The degree ladder: an irreducible monic factor `g` of `f`
has `g.natDegree ∈ {1,2,3,4}`; `1` and `3` are excluded because the complementary cofactor would
then be monic of degree `1` and hence have a root (which would also be a root of `f`); `4` is
excluded because a same-degree monic divisor of a monic polynomial IS that polynomial
(`eq_of_monic_of_associated`), forcing `f` itself irreducible. So `g.natDegree = 2`; the
cofactor `h` is then monic of degree `2` with no root (else `f` would), hence irreducible by the
`≤ 3` lemma. -/
theorem exists_pair_irred_quad_of_reducible {f : Polynomial K} (hf : f.Monic)
    (hd : f.natDegree = 4) (hr : f.roots = 0) (hnirr : ¬ Irreducible f) :
    ∃ g h : Polynomial K, g.Monic ∧ Irreducible g ∧ g.natDegree = 2 ∧
      h.Monic ∧ Irreducible h ∧ h.natDegree = 2 ∧ g * h = f := by
  have hfne : f ≠ 0 := hf.ne_zero
  have hnu : ¬ IsUnit f := by
    intro hu
    obtain ⟨r, -, hrf⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hrf, Polynomial.natDegree_C] at hd
    omega
  obtain ⟨g, hgm, hgi, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor f hnu
  obtain ⟨h, hfgh⟩ := hgdvd
  -- `hfgh : f = g * h` (the `Dvd.dvd` unfolding); `hfgh' : g * h = f` is the form most lemmas want.
  have hfgh' : g * h = f := hfgh.symm
  have hhm : h.Monic := monic_of_mul_monic_left hf hgm hfgh'
  have hgne : g ≠ 0 := hgm.ne_zero
  have hhne : h ≠ 0 := hhm.ne_zero
  have hdegsum : g.natDegree + h.natDegree = 4 := by
    rw [← hd, hfgh, Polynomial.natDegree_mul hgne hhne]
  have hnoroot : ∀ p q : Polynomial K, p * q = f → p.Monic → q.natDegree = 1 → False := by
    intro p q hpq hpm hq1
    have hqm : q.Monic := monic_of_mul_monic_left hf hpm hpq
    have hqne : q ≠ 0 := hqm.ne_zero
    have hqdeg' : q.degree = (1 : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hqne, hq1]; rfl
    obtain ⟨a, ha⟩ := Polynomial.exists_root_of_degree_eq_one hqdeg'
    have haf : f.IsRoot a := by
      have hpqa : (p * q).IsRoot a := by
        unfold Polynomial.IsRoot at ha ⊢
        rw [Polynomial.eval_mul, ha, mul_zero]
      rwa [hpq] at hpqa
    have : a ∈ f.roots := (Polynomial.mem_roots hfne).mpr haf
    rw [hr] at this
    exact absurd this (by simp)
  have hg0 : g.natDegree ≠ 0 := by
    intro h0
    have hg1' : g = 1 := hgm.degree_le_zero_iff_eq_one.mp
      (by rw [Polynomial.degree_eq_natDegree hgne, h0]; rfl)
    exact hgi.not_isUnit (hg1' ▸ isUnit_one)
  have hg1 : g.natDegree ≠ 1 := fun h1 => hnoroot h g (by rw [mul_comm]; exact hfgh') hhm h1
  have hg4 : g.natDegree ≠ 4 := by
    intro h4
    have hassoc : Associated g f := Polynomial.associated_of_dvd_of_degree_eq ⟨h, hfgh⟩
      (by rw [Polynomial.degree_eq_natDegree hgne, Polynomial.degree_eq_natDegree hfne, h4, hd])
    exact hnirr (Polynomial.eq_of_monic_of_associated hgm hf hassoc ▸ hgi)
  have hg3 : g.natDegree ≠ 3 := by
    intro h3
    have hh1 : h.natDegree = 1 := by omega
    exact hnoroot g h hfgh' hgm hh1
  have hg2 : g.natDegree = 2 := by
    have := Polynomial.natDegree_le_of_dvd ⟨h, hfgh⟩ hfne
    omega
  have hh2 : h.natDegree = 2 := by omega
  have hhnoroot : h.roots = 0 := by
    by_contra hcontra
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hcontra
    have har : h.IsRoot a := (Polynomial.mem_roots hhne).mp ha
    have haf : f.IsRoot a := by
      have hgha : (g * h).IsRoot a := by
        unfold Polynomial.IsRoot at har ⊢
        rw [Polynomial.eval_mul, har, mul_zero]
      rwa [hfgh'] at hgha
    have : a ∈ f.roots := (Polynomial.mem_roots hfne).mpr haf
    rw [hr] at this
    exact absurd this (by simp)
  have hhirr : Irreducible h :=
    (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hhm (by omega)
      (by omega)).mpr hhnoroot
  exact ⟨g, h, hgm, hgi, hg2, hhm, hhirr, hh2, hfgh'⟩

end FF0

end Uniformity.Density.IFCG4

end

/-! ## AxCheck footer (appended by the orchestrator; the unit hung pre-footer) -/

section AxCheck

#print axioms Uniformity.Density.IFCG4.monicOfDegEquiv
#print axioms Uniformity.Density.IFCG4.card_monicOfDeg
#print axioms Uniformity.Density.IFCG4.natCard_monicOfDeg
#print axioms Uniformity.Density.IFCG4.monic_cofactor_of_prod_multiset_X_sub_C_mul
#print axioms Uniformity.Density.IFCG4.roots_card_ne_natDegree_sub_one
#print axioms Uniformity.Density.IFCG4.peelPack
#print axioms Uniformity.Density.IFCG4.peelPack_injective
#print axioms Uniformity.Density.IFCG4.peelExtract
#print axioms Uniformity.Density.IFCG4.peelExtract_injective
#print axioms Uniformity.Density.IFCG4.card_rootsCard_eq
#print axioms Uniformity.Density.IFCG4.flatEquivNested
#print axioms Uniformity.Density.IFCG4.card_eq_sum_card_fiber_range
#print axioms Uniformity.Density.IFCG4.card_monicOfDeg_eq_sum_rootsCard
#print axioms Uniformity.Density.IFCG4.card_irred_one
#print axioms Uniformity.Density.IFCG4.card_noRoot_zero
#print axioms Uniformity.Density.IFCG4.card_rootsCard_natDegree_sub_one
#print axioms Uniformity.Density.IFCG4.card_noRoot_eq_card_irred
#print axioms Uniformity.Density.IFCG4.card_noRoot_two
#print axioms Uniformity.Density.IFCG4.card_irred_two
#print axioms Uniformity.Density.IFCG4.card_noRoot_three
#print axioms Uniformity.Density.IFCG4.card_irred_three
#print axioms Uniformity.Density.IFCG4.monic_of_mul_monic_left
#print axioms Uniformity.Density.IFCG4.exists_pair_irred_quad_of_reducible

end AxCheck
