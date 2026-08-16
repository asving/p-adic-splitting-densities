/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B08
import Uniformity.ChapB.B24
import Uniformity.ChapB.B25
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C109iii — NODE C.109-iii, the priced-digit fibre at `resField Φ`

**Chapter C, NODE C.109-iii** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md`, the A-C.5
amendment, ITEM 1 — the C.109 SPLIT), **ENV-C1 + `[Finite (ResidueField O)]`**.
`[signed: A-C.5, 2026-08-16 — layer 3 of five under C.109's byte-unchanged assembly; the layer
A-C.3's append predicted would be the hard one]`.

On one block already floored at height `h < N`, prescribing the digit AT height `h` — B.25's
`resMk`, the corpus's `digit_{P(j)}(a_j) ∈ F_{q^d}` under the class map `b ↦ b mod P̄` — cuts
the count by exactly `Q = Nat.card (resField Φ)`, leaving `Q ^ (N − h − 1)` classes
**UNIFORMLY in the prescribed value `r`**, `r = 0` included.

## Why uniformity is the content, and where it lives in this proof

"Each integral boundary position prices ONE digit" is a DIVISION by `Q`, not an inequality:
the count must not depend on which residue is prescribed, or C.109-v's census product could not
factor out.  In this proof the uniformity is isolated in ONE statement —
`pricedAt_succ_singleton`: **at level `h + 1` the condition pins exactly one class, for every
`r`.**  That is the whole of the layer's content; everything else is the pullback bookkeeping
that turns "one class at level `h+1`" into "`Q^{N−h−1}` classes at level `N`".

## The three moves

1. **The condition is a level-`(h+1)` condition** (`pricedAt_preimage`).  Both clauses read
   only digits `< h + 1`: the floor `h ≤ gaussVal A` is `π^h`-divisibility of the coefficients
   (B.08's `le_gaussVal_iff`) and the residue is the digit AT `h`.  So the level-`N` set is the
   `coeffFactor`-preimage of the level-`(h+1)` set.  The backward direction rebuilds a witness
   from an arbitrary lift of the class, using `digAt_eq_iff_sub`: two elements both divisible by
   `π^h` have the same digit at `h` exactly when they agree mod `π^(h+1)`.
2. **At level `h + 1` the set is a SINGLETON** (`pricedAt_succ_singleton`).  Existence: pull `r`
   back to a degree-`< d` representative `g` over the residue field (`exists_repr_of_degree_lt`,
   division by the monic `Φ̄`), lift its coefficients to `O` and multiply by `π^h`.  Uniqueness:
   two witnesses have equal `resMk`, hence equal digit polynomials — both have degree `< d`, and
   `AdjoinRoot.mk Φ̄` is INJECTIVE on degree-`< d` representatives (`mk_inj_of_degree_lt`) — hence
   coefficientwise equal digits, hence agreement mod `π^(h+1)`.
3. **Count the fibre.**  Landed `card_preimage_coeffFactor` gives
   `#(preimage) · q^(d(h+1)) = 1 · q^(dN)`, so `#(preimage) = q^(d(N−h−1)) = Q^(N−h−1)` with
   `Q = q ^ d` (`card_resField'`).

## Why `card_resField` is re-proved here

B.26(c)'s elaborated signature carries `[IsAdicComplete (maximalIdeal O) O]`, which this node's
signed signature does not bind.  Same environment mismatch, same cure, as landed NODE C.04's
private `card_resField_X` and NODE C.109-ii's `card_resField'`; `private`, so no collision.

**DEPENDS.** B.08 (`le_gaussVal_iff`) · B.21/B.22 (`digAt`, `digAt_eq`) · B.23/B.24
(`digPoly`, `digPoly_coeff`, `degree_digPoly_le`) · B.25 (`resField`, `resMk`) · B.26
(`card_resField` — as a PATTERN) · landed `Coeff`/`proj`/`proj_surjective`/`coeffFactor`/
`coeffFactor_proj`/`card_coeff`/`card_preimage_coeffFactor`/`residueCard`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.23` (the three slot regimes, verbatim — the on-side clause's *"possibly
zero; priced jointly by `λ_S`"* is the `r = 0` case this layer must cover) · `EFF.W12.24`
(*"minus one priced digit if `j` is a lattice point"*).

**TEETH.** The blueprint's designated first check is the summation coherence: summing over
`r ∈ resField Φ` must return C.109-ii's per-block `Q^{N−h}`, which kills any `r`-dependent
mutant (e.g. `Q^{N−h−1}` for `r ≠ 0` and `Q^{N−h}` for `r = 0`).  Run independently before
landing over `O = ℤ_p` at `(p,d,N,h) ∈ {(2,1,3,0),(2,1,4,2),(3,1,3,1),(2,2,3,0),(2,2,3,1),
(2,2,4,2),(3,2,3,0),(3,2,3,1),(2,3,3,1)}`: every fibre has the SAME size `q^(d(N−h−1))` and the
fibres sum to `Q^{N−h}` — 9/9 pass.  `verification/c109_ac5_sweep_check.py` (124/0) and
`verification/c109_ac2_cell_check.py` re-run green the same day.

**NOTE on the unused binders.** `[Finite (resField Φ)]` is carried by the signed signature and
is not needed by the proof.  The binder is kept because the signature is signed;
`linter.unusedVariables` is silenced at the theorem only.

## Status

Sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's signed surface
is exactly `ht_priced_digit_fibre`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. Degree-`< d` blocks -/

private noncomputable def blk {d : ℕ} (b : Fin d → O) : Polynomial O :=
  ∑ i : Fin d, C (b i) * X ^ (i : ℕ)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem blk_coeff {d : ℕ} (b : Fin d → O) (k : ℕ) :
    (blk b).coeff k = if hk : k < d then b ⟨k, hk⟩ else 0 := by
  classical
  simp only [blk, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : k < d
  · rw [dif_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin d)]
    · simp
    · intro c _ hc
      exact if_neg fun hkk => hc (Fin.ext hkk.symm)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg hk]
    refine Finset.sum_eq_zero fun i _ => if_neg fun hkk => ?_
    exact hk (hkk ▸ i.isLt)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem natDegree_blk_lt {d : ℕ} (hd : 0 < d) (b : Fin d → O) :
    (blk b).natDegree < d := by
  have hle : (blk b).natDegree ≤ d - 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => by
      rw [blk_coeff]; exact dif_neg (by omega)
  omega

private theorem degree_lt_of_natDegree_lt {R : Type*} [Semiring R] {d : ℕ} {A : Polynomial R}
    (hA : A.natDegree < d) : A.degree < (d : WithBot ℕ) := by
  rcases eq_or_ne A 0 with rfl | h0
  · rw [degree_zero]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree h0]; exact_mod_cast hA

/-! ### 2. The digit at a common height is a level-`(h+1)` congruence -/

private theorem digAt_eq_iff_sub (hπ : Irreducible π) {h : ℕ} {x y : O}
    (hx : π ^ h ∣ x) (hy : π ^ h ∣ y) :
    digAt π h x = digAt π h y ↔ π ^ (h + 1) ∣ x - y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  rw [digAt_eq hπ rfl, digAt_eq hπ rfl, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton,
    ← mul_sub, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero h hπ.ne_zero)]

private theorem digAt_of_zero' (hπ : Irreducible π) (k : ℕ) : digAt π k (0 : O) = 0 := by
  rw [digAt_eq hπ (mul_zero (π ^ k)).symm, map_zero]

/-! ### 3. The residual-field read on degree-`< d` representatives -/

private theorem degree_map_key {Φ : Polynomial O} (hΦ : IsKey Φ) :
    (Φ.map (IsLocalRing.residue O)).degree = (Φ.natDegree : WithBot ℕ) := by
  rw [degree_eq_natDegree (hΦ.monic.map (IsLocalRing.residue O)).ne_zero,
    hΦ.monic.natDegree_map (IsLocalRing.residue O)]

/-- on degree-`< d` representatives the class map onto `resField Φ` is injective. -/
private theorem mk_inj_of_degree_lt {Φ : Polynomial O} (hΦ : IsKey Φ)
    {g₁ g₂ : Polynomial (ResidueField O)}
    (h₁ : g₁.degree < (Φ.natDegree : WithBot ℕ)) (h₂ : g₂.degree < (Φ.natDegree : WithBot ℕ))
    (he : AdjoinRoot.mk (Φ.map (IsLocalRing.residue O)) g₁
        = AdjoinRoot.mk (Φ.map (IsLocalRing.residue O)) g₂) : g₁ = g₂ := by
  by_contra hne
  have hsub : g₁ - g₂ ≠ 0 := sub_ne_zero.2 hne
  have hdvd : (Φ.map (IsLocalRing.residue O)) ∣ g₁ - g₂ := AdjoinRoot.mk_eq_mk.1 he
  have hlow := Polynomial.degree_le_of_dvd hdvd hsub
  rw [degree_map_key hΦ] at hlow
  have hhigh : (g₁ - g₂).degree < (Φ.natDegree : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le g₁ g₂) (max_lt h₁ h₂)
  exact absurd (lt_of_le_of_lt hlow hhigh) (lt_irrefl _)

/-- every residual class has a degree-`< d` representative. -/
private theorem exists_repr_of_degree_lt {Φ : Polynomial O} (hΦ : IsKey Φ) (r : resField Φ) :
    ∃ g : Polynomial (ResidueField O), g.natDegree < Φ.natDegree ∧
      AdjoinRoot.mk (Φ.map (IsLocalRing.residue O)) g = r := by
  obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (g := Φ.map (IsLocalRing.residue O)) r
  have hm : (Φ.map (IsLocalRing.residue O)).Monic := hΦ.monic.map (IsLocalRing.residue O)
  refine ⟨g %ₘ (Φ.map (IsLocalRing.residue O)), ?_, ?_⟩
  · have hlt := Polynomial.degree_modByMonic_lt g hm
    rw [degree_map_key hΦ] at hlt
    rcases eq_or_ne (g %ₘ (Φ.map (IsLocalRing.residue O))) 0 with h0 | h0
    · rw [h0]; simpa using hΦ.pos
    · rw [degree_eq_natDegree h0] at hlt
      exact_mod_cast hlt
  · rw [← hg]
    refine AdjoinRoot.mk_eq_mk.2 ?_
    rw [Polynomial.modByMonic_eq_sub_mul_div g (Φ.map (IsLocalRing.residue O))]
    exact ⟨-(g /ₘ (Φ.map (IsLocalRing.residue O))), by ring⟩

/-! ### 4. The priced-digit condition, read at any level -/

/-- the signed predicate of C.109-iii, read at level `ν`. -/
private def PricedAt (π : O) (Φ : Polynomial O) (h : ℕ) (r : resField Φ) (ν : ℕ)
    (c : Coeff O Φ.natDegree ν) : Prop :=
  ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
    proj O Φ.natDegree ν (fun i => A.coeff i) = c ∧
    ((h : ℕ) : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = r

private theorem degree_digPoly_lt (hπ : Irreducible π) {d h : ℕ} {A : Polynomial O}
    (hA : A.natDegree < d) : (digPoly π h A).degree < (d : WithBot ℕ) :=
  lt_of_le_of_lt (degree_digPoly_le hπ h A) (degree_lt_of_natDegree_lt hA)

/-- two degree-`< d` witnesses of the same residue have the same digits at height `h`. -/
private theorem digAt_witness_eq (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h : ℕ} {A₁ A₂ : Polynomial O} (hd₁ : A₁.natDegree < Φ.natDegree)
    (hd₂ : A₂.natDegree < Φ.natDegree) (hres : resMk π Φ h A₁ = resMk π Φ h A₂) (i : ℕ) :
    digAt π h (A₁.coeff i) = digAt π h (A₂.coeff i) := by
  have hpoly : digPoly π h A₁ = digPoly π h A₂ :=
    mk_inj_of_degree_lt hΦ (degree_digPoly_lt hπ hd₁) (degree_digPoly_lt hπ hd₂) hres
  have hco := congrArg (fun p => Polynomial.coeff p i) hpoly
  simpa only [digPoly_coeff hπ] using hco

/-! ### 5. At level `h + 1` the condition pins exactly ONE class — the uniformity -/

private theorem pricedAt_succ_singleton (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) (h : ℕ) (r : resField Φ) :
    ∃ c₀ : Coeff O Φ.natDegree (h + 1),
      {c : Coeff O Φ.natDegree (h + 1) | PricedAt π Φ h r (h + 1) c} = {c₀} := by
  classical
  obtain ⟨g, hgdeg, hgmk⟩ := exists_repr_of_degree_lt hΦ r
  choose γ hγ using fun i : Fin Φ.natDegree =>
    Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal O) (g.coeff (i : ℕ))
  have hA₀deg : (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)).natDegree < Φ.natDegree :=
    natDegree_blk_lt hΦ.pos _
  have hA₀dvd : ∀ k, π ^ h ∣ (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)).coeff k := by
    intro k
    rw [blk_coeff]
    by_cases hk : k < Φ.natDegree
    · rw [dif_pos hk]; exact ⟨γ ⟨k, hk⟩, rfl⟩
    · rw [dif_neg hk]; exact dvd_zero _
  have hA₀val : ((h : ℕ) : ℕ∞) ≤ gaussVal (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)) :=
    (le_gaussVal_iff hπ).2 hA₀dvd
  have hA₀dig : digPoly π h (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)) = g := by
    refine Polynomial.ext fun k => ?_
    rw [digPoly_coeff hπ, blk_coeff]
    by_cases hk : k < Φ.natDegree
    · rw [dif_pos hk, digAt_eq hπ rfl]
      exact hγ ⟨k, hk⟩
    · rw [dif_neg hk, digAt_of_zero' hπ]
      exact (g.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hA₀res : resMk π Φ h (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)) = r := by
    rw [resMk, hA₀dig, hgmk]
  refine ⟨proj O Φ.natDegree (h + 1)
    (fun i => (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)).coeff (i : ℕ)), ?_⟩
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨A, hAdeg, hAproj, hAval, hAres⟩
    rw [← hAproj]
    refine funext fun i => ?_
    have hdvdA : ∀ k, π ^ h ∣ A.coeff k := (le_gaussVal_iff hπ).1 hAval
    have hdig := digAt_witness_eq hπ hΦ hAdeg hA₀deg (hAres.trans hA₀res.symm) (i : ℕ)
    have hsub : π ^ (h + 1) ∣
        A.coeff (i : ℕ) - (blk (fun i : Fin Φ.natDegree => π ^ h * γ i)).coeff (i : ℕ) :=
      (digAt_eq_iff_sub hπ (hdvdA (i : ℕ)) (hA₀dvd (i : ℕ))).1 hdig
    change Ideal.Quotient.mk _ (A.coeff (i : ℕ))
      = Ideal.Quotient.mk _ ((blk (fun i : Fin Φ.natDegree => π ^ h * γ i)).coeff (i : ℕ))
    rw [Ideal.Quotient.eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hsub
  · rintro rfl
    exact ⟨_, hA₀deg, rfl, hA₀val, hA₀res⟩

/-! ### 6. The level-`N` condition is the pullback of the level-`(h+1)` one -/

private theorem pricedAt_preimage (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) {h N : ℕ} (hle : h + 1 ≤ N) (r : resField Φ) :
    {c : Coeff O Φ.natDegree N | PricedAt π Φ h r N c}
      = (coeffFactor (O := O) Φ.natDegree hle) ⁻¹'
          {c : Coeff O Φ.natDegree (h + 1) | PricedAt π Φ h r (h + 1) c} := by
  classical
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨A, hAdeg, hAproj, hAval, hAres⟩
    exact ⟨A, hAdeg, by rw [← hAproj, coeffFactor_proj], hAval, hAres⟩
  · rintro ⟨A₁, hA₁deg, hA₁proj, hA₁val, hA₁res⟩
    obtain ⟨a, rfl⟩ := proj_surjective O Φ.natDegree N c
    have hstep : ∀ i : Fin Φ.natDegree, π ^ (h + 1) ∣ a i - A₁.coeff (i : ℕ) := by
      intro i
      have heq : proj O Φ.natDegree (h + 1) (fun i => A₁.coeff (i : ℕ))
          = proj O Φ.natDegree (h + 1) a := by
        rw [hA₁proj, coeffFactor_proj]
      have h1 := congrFun heq i
      rw [proj, proj, Ideal.Quotient.eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h1
      exact (dvd_sub_comm).1 h1
    have hdvd₁ : ∀ k, π ^ h ∣ A₁.coeff k := (le_gaussVal_iff hπ).1 hA₁val
    have hAdeg : (blk a).natDegree < Φ.natDegree := natDegree_blk_lt hΦ.pos _
    have hAdvd : ∀ k, π ^ h ∣ (blk a).coeff k := by
      intro k
      rw [blk_coeff]
      by_cases hk : k < Φ.natDegree
      · rw [dif_pos hk]
        have h1 : π ^ h ∣ a ⟨k, hk⟩ - A₁.coeff k :=
          (pow_dvd_pow π (Nat.le_succ h)).trans (hstep ⟨k, hk⟩)
        have h2 : a ⟨k, hk⟩ = (a ⟨k, hk⟩ - A₁.coeff k) + A₁.coeff k := by ring
        rw [h2]
        exact dvd_add h1 (hdvd₁ k)
      · rw [dif_neg hk]; exact dvd_zero _
    refine ⟨blk a, hAdeg, ?_, (le_gaussVal_iff hπ).2 hAdvd, ?_⟩
    · refine funext fun i => ?_
      change Ideal.Quotient.mk _ ((blk a).coeff (i : ℕ)) = Ideal.Quotient.mk _ (a i)
      rw [blk_coeff, dif_pos i.isLt, Fin.eta]
    · have hdig : digPoly π h (blk a) = digPoly π h A₁ := by
        refine Polynomial.ext fun k => ?_
        rw [digPoly_coeff hπ, digPoly_coeff hπ]
        by_cases hk : k < Φ.natDegree
        · refine (digAt_eq_iff_sub hπ (hAdvd k) (hdvd₁ k)).2 ?_
          rw [blk_coeff, dif_pos hk]
          exact hstep ⟨k, hk⟩
        · rw [blk_coeff, dif_neg hk, A₁.coeff_eq_zero_of_natDegree_lt (by omega)]
      rw [resMk, hdig, ← resMk, hA₁res]

/-! ### 7. `|resField Φ| = q ^ d` at ENV-C1 -/

private theorem card_resField' [Finite (ResidueField O)] {Φ : Polynomial O} (hΦ : IsKey Φ) :
    Nat.card (resField Φ) = residueCard O ^ Φ.natDegree := by
  have hne : (Φ.map (IsLocalRing.residue O)) ≠ 0 := hΦ.irred.ne_zero
  haveI : Module.Finite (ResidueField O) (resField Φ) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfr : Module.finrank (ResidueField O) (resField Φ) = Φ.natDegree := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne,
      hΦ.monic.natDegree_map (IsLocalRing.residue O)]
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O), hfr]
  rfl

/-! ### 8. NODE C.109-iii -/

set_option linter.unusedVariables false in
theorem ht_priced_digit_fibre (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    (h N : ℕ) (hh : h < N) (r : resField Φ) :
    Nat.card {c : Coeff O Φ.natDegree N //
        ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
          proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
          ((h : ℕ) : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = r}
      = Nat.card (resField Φ) ^ (N - h - 1) := by
  classical
  have hle : h + 1 ≤ N := hh
  obtain ⟨c₀, hsing⟩ := pricedAt_succ_singleton hπ hΦ h r
  have hcard := card_preimage_coeffFactor (O := O) Φ.natDegree hle
    {c : Coeff O Φ.natDegree (h + 1) | PricedAt π Φ h r (h + 1) c}
  rw [← pricedAt_preimage hπ hΦ hle r, hsing, card_coeff, card_coeff] at hcard
  have hone : Nat.card ({c₀} : Set (Coeff O Φ.natDegree (h + 1))) = 1 := by simp
  rw [hone, one_mul] at hcard
  have hlhs : Nat.card {c : Coeff O Φ.natDegree N //
      ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
        proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
        ((h : ℕ) : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = r}
      = Nat.card {c : Coeff O Φ.natDegree N | PricedAt π Φ h r N c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hQ : Nat.card (resField Φ) ^ (N - h - 1)
      = residueCard O ^ (Φ.natDegree * (N - h - 1)) := by
    rw [card_resField' hΦ, ← pow_mul]
  rw [hlhs, hQ]
  refine Nat.eq_of_mul_eq_mul_right
    (pow_pos (residueCard_pos O) (Φ.natDegree * (h + 1))) ?_
  have hexp : N - h - 1 + (h + 1) = N := by omega
  rw [hcard, ← pow_add, ← Nat.mul_add, hexp]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_priced_digit_fibre

end AxCheck
