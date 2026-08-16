/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B26
import Uniformity.ChapB.B41b
import Uniformity.ChapB.B45
import Uniformity.ChapB.B46
import Uniformity.ChapB.B47

/-!
# Uniformity.ChapB.B48 — NODE B.48, the theorem of the residual polynomial (NS-2, first half)

**Chapter B, NODE B.48** `exists_residual_dissection` (`blueprint/CHAP-B_leaf_layer.md` §6),
ENV-C. Signature frozen at the A-F.6 form (`hu`, `hfd` added there).

A monic `(u,ℓ)`-pure `f` of `φ.natDegree`-divisible degree, whose residual polynomial has
positive degree, factors as `f = ∏_{ψ ∈ s} f_ψ` indexed by the monic irreducible factors of that
residual polynomial, with `f_ψ` pure of residual polynomial `ψ ^ a ψ` (up to a unit) and
`(f_ψ).natDegree = ℓ · m · a ψ · ψ.natDegree`.

## Route (blueprint steps 1–5), and two deviations

1. **Step 1 (the monic normalisation of `R`) is NOT needed** — `resPoly` of a monic `(u,ℓ)`-pure
   `f` of degree `ℓ·d·m` is already MONIC: its top coefficient is `resMk π φ 0 (dev φ f (ℓd))`
   and `dev φ f (ℓd) = 1` by B.13a (`dev_top`). So the unit `c` of the blueprint's `R = C c · R'`
   is `1`, and B.45 applies to `R` itself. (The conclusion's per-factor unit is `1` for the same
   reason; the existential keeps the frozen shape.)
2. **Steps 2–5 are one `Finset.induction_on`**, `exists_dissection_aux` below, with the exponent
   function `a` FIXED outside the induction (only the index set shrinks). Peeling `ψ₀` feeds B.41
   with `G := ψ₀ ^ a ψ₀` and `H := ∏_{ψ ∈ s'} ψ ^ a ψ`: coprime because `ψ₀` is coprime to every
   other member (B.45's pairwise clause) — `IsCoprime.prod_right` + `pow_left`/`pow_right`, so
   B.46 is not literally invoked (it is the same fact in its `¬ ψ₀ ∣ H` form).
   The recursion then runs on the cofactor `h`, whose residual polynomial is `H` **by B.41's
   strengthened conclusion** (this chain's amendment: `GradedCoprime` alone records only that the
   two residual polynomials are coprime, which does not identify them — see B41b's docstring).
3. Step 4's degree bookkeeping is B.47 (`natDegree_of_residual_piece`) verbatim.

**SPLIT DEVIATION.** The blueprint mandates a 3-way split whose first part is step 1's
normalisation; with that step gone the node is one induction plus a short contract, kept in one
file (~200 lines, inside the wave-1 budget).

**⚠ ENVIRONMENT NOTE (0e gate).** Both ENV-C instances are genuinely CONSUMED here:
`[IsAdicComplete (maximalIdeal O) O]` through B.41 (its limit step is B.40) and
`[Finite (ResidueField O)]` through B.45 (via B.26's `instFiniteResField`). So the §12 rule-7
`omit` rider recorded at A-F.8/A-F.9 for this node is **wrong** — an `omit` here would make the
node unprovable. The stub's `axiom` sheds both instances because its *statement* never names
them; the type diff is adjudicated against the landed B.40/B.41 precedent, exactly as recorded
in `B41b.lean`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-! ## 1. The recursion (blueprint steps 2, 3, 5) -/

omit [Finite (ResidueField O)] in
/-- **B.48's `Finset` recursion.** For a fixed exponent function `a`: if the residual polynomial
of a monic `(u,ℓ)`-pure `f` is `∏_{ψ ∈ s} ψ ^ a ψ` with the `ψ` monic irreducible and pairwise
coprime, then `f` splits accordingly. The induction is on `s`; the peel is B.41.

Residue finiteness is `omit`ted: it enters only through B.45, in the contract below. -/
private theorem exists_dissection_aux (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (a : Polynomial (resField φ) → ℕ) :
    ∀ s : Finset (Polynomial (resField φ)),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) →
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) →
      ∀ f : Polynomial O, f.Monic → φ.natDegree ∣ f.natDegree → IsPure φ f u ℓ →
      ∀ (hne : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), npHgt φ f 0 = (H₀ : ℕ∞) →
      resPoly π φ f u ℓ hne H₀ = ∏ ψ ∈ s, ψ ^ a ψ →
      ∃ F : Polynomial (resField φ) → Polynomial O,
        f = ∏ ψ ∈ s, F ψ ∧
        (∀ ψ ∈ s, (F ψ).Monic ∧ IsPure φ (F ψ) u ℓ ∧
          (F ψ).natDegree = ℓ * φ.natDegree * a ψ * ψ.natDegree) ∧
        (∀ ψ ∈ s, ∃ (hne' : (sideSet φ (F ψ) u ℓ).Nonempty) (H : ℕ) (c : (resField φ)ˣ),
          resPoly π φ (F ψ) u ℓ hne' H = Polynomial.C (c : resField φ) * ψ ^ a ψ) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ f hf hfd hpure hne H₀ hH₀ hres
    -- the residual polynomial is `1`, so the side has degree `0`, so `f` has degree `0`
    have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
      (Nat.div_mul_cancel hfd).symm
    have htf : suppVal φ f u ℓ ≠ ⊤ := by
      rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hpure]; exact ENat.coe_ne_top _
    have hfmin : sideMin φ f u ℓ hne = 0 := sideMin_of_pure hpure hne
    have hHf : npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := by rw [hfmin]; exact hH₀
    have hRdeg : (resPoly π φ f u ℓ hne H₀).natDegree = sideDeg φ f u ℓ hne :=
      (natDegree_resPoly hπ hφ hℓ hcop htf hne hHf).1
    have hsd : sideDeg φ f u ℓ hne = 0 := by
      rw [← hRdeg, hres, Finset.prod_empty, Polynomial.natDegree_one]
    have hdl : ℓ * sideDeg φ f u ℓ hne = f.natDegree / φ.natDegree :=
      sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hpure hne
    have hf0 : f.natDegree = 0 := by
      rw [hfdeg0, ← hdl, hsd, Nat.mul_zero, Nat.zero_mul]
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hf hf0, Finset.prod_empty]
    · intro ψ hψ; simp at hψ
    · intro ψ hψ; simp at hψ
  | insert ψ₀ s' hψ₀ ih =>
    intro hmon hpc f hf hfd hpure hne H₀ hH₀ hres
    have hψ₀mem : ψ₀ ∈ insert ψ₀ s' := Finset.mem_insert_self _ _
    have hψ₀m : ψ₀.Monic := (hmon ψ₀ hψ₀mem).1
    -- the two residual factors fed to B.41
    have hGm : (ψ₀ ^ a ψ₀).Monic := hψ₀m.pow _
    have hHm : (∏ ψ ∈ s', ψ ^ a ψ).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun ψ hψ =>
        ((hmon ψ (Finset.mem_insert_of_mem hψ)).1).pow _
    have hGH : IsCoprime (ψ₀ ^ a ψ₀) (∏ ψ ∈ s', ψ ^ a ψ) := by
      refine IsCoprime.pow_left (IsCoprime.prod_right fun ψ hψ => IsCoprime.pow_right ?_)
      exact hpc ψ₀ hψ₀mem ψ (Finset.mem_insert_of_mem hψ) fun hcon => hψ₀ (hcon ▸ hψ)
    have hprod : ∃ c : (resField φ)ˣ, resPoly π φ f u ℓ hne H₀
        = Polynomial.C (c : resField φ) * ((ψ₀ ^ a ψ₀) * ∏ ψ ∈ s', ψ ^ a ψ) := by
      refine ⟨1, ?_⟩
      rw [hres, Finset.prod_insert hψ₀]
      simp
    -- ## the peel: B.41 at `(u,ℓ)`
    obtain ⟨g, h, hgm, hhm, hfgh, hgdeg, hhdeg, hgp, hhp, -, -, hhH, hgres, hhres⟩ :=
      exists_graded_factorization hπ hφ hu hℓ hcop hf hfd hpure hH₀ hne hGm hHm hGH hprod
    have hhd : φ.natDegree ∣ h.natDegree := ⟨ℓ * (∏ ψ ∈ s', ψ ^ a ψ).natDegree, by
      rw [hhdeg]; ring⟩
    have hhne : (sideSet φ h u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    -- ## the recursion on the cofactor, whose residual polynomial is `∏_{s'} ψ ^ a ψ`
    obtain ⟨F', hF'prod, hF'props, hF'res⟩ :=
      ih (fun ψ hψ => hmon ψ (Finset.mem_insert_of_mem hψ))
        (fun ψ hψ χ hχ hne' =>
          hpc ψ (Finset.mem_insert_of_mem hψ) χ (Finset.mem_insert_of_mem hχ) hne')
        h hhm hhd hhp hhne (u * (∏ ψ ∈ s', ψ ^ a ψ).natDegree) hhH (hhres hhne)
    set F : Polynomial (resField φ) → Polynomial O :=
      fun ψ => if ψ = ψ₀ then g else F' ψ with hFdef
    have hFeq0 : F ψ₀ = g := by simp [hFdef]
    have hFeq : ∀ ψ ∈ s', F ψ = F' ψ := by
      intro ψ hψ
      have hnem : ψ ≠ ψ₀ := fun hcon => hψ₀ (hcon ▸ hψ)
      simp [hFdef, hnem]
    refine ⟨F, ?_, ?_, ?_⟩
    · rw [Finset.prod_insert hψ₀, hFeq0, hfgh, hF'prod]
      exact congrArg (g * ·) (Finset.prod_congr rfl fun ψ hψ => (hFeq ψ hψ).symm)
    · intro ψ hψ
      rcases Finset.mem_insert.1 hψ with rfl | hψ'
      · rw [hFeq0]
        exact ⟨hgm, hgp, natDegree_of_residual_piece (u := u) hψ₀m hgdeg⟩
      · rw [hFeq ψ hψ']
        exact hF'props ψ hψ'
    · intro ψ hψ
      rcases Finset.mem_insert.1 hψ with rfl | hψ'
      · rw [hFeq0]
        refine ⟨sideSet_nonempty_gen _ _ _ _, u * (ψ ^ a ψ).natDegree, 1, ?_⟩
        rw [hgres]
        simp
      · rw [hFeq ψ hψ']
        exact hF'res ψ hψ'

/-! ## 2. NODE B.48 — the signed contract -/

/-- **B.48 — the theorem of the residual polynomial at order 1** (NS-2, first half; signature
frozen at the A-F.6 form). The residual polynomial's factorisation into powers of monic
irreducibles lifts to a factorisation of `f` into monic `(u,ℓ)`-pure pieces of the pinned
degrees.

`(hu)` and `(hfd)` are load-bearing (A-F.6): without them the frozen form is refuted
(`f = X³+4X+3` at `φ = X²+1` over `ℤ₃`, `u = ℓ = 1` — pure with `sideDeg = 1 > 0`, yet every
conclusion factor has even degree `ℓ·m·aψ·deg ψ` while `deg f = 3`). Both are free at the only
consumer, B.63, from B.42's strengthened conclusion. -/
theorem exists_residual_dissection (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O}
    (hf : f.Monic) (hfd : φ.natDegree ∣ f.natDegree)
    (hpure : IsPure φ f u ℓ) (hne : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg φ f u ℓ hne) :
    ∃ (s : Finset (Polynomial (resField φ))) (a : Polynomial (resField φ) → ℕ)
      (F : Polynomial (resField φ) → Polynomial O),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ ∧ 0 < a ψ) ∧
      f = ∏ ψ ∈ s, F ψ ∧
      (∀ ψ ∈ s, (F ψ).Monic ∧ IsPure φ (F ψ) u ℓ ∧
        (F ψ).natDegree = ℓ * φ.natDegree * a ψ * ψ.natDegree) ∧
      (∀ ψ ∈ s, ∃ (hne' : (sideSet φ (F ψ) u ℓ).Nonempty) (H : ℕ) (c : (resField φ)ˣ),
        resPoly π φ (F ψ) u ℓ hne' H = Polynomial.C (c : resField φ) * ψ ^ a ψ) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  haveI : Finite (resField φ) := instFiniteResField hφ
  -- ## the side data of `f`, and the monicity of its residual polynomial
  have hfdeg0 : f.natDegree = (f.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hfd).symm
  have htf : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hf hfdeg0 hpure]; exact ENat.coe_ne_top _
  have hfmin : sideMin φ f u ℓ hne = 0 := sideMin_of_pure hpure hne
  have hHf : npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := by rw [hfmin]; exact hH₀
  have hdl : ℓ * sideDeg φ f u ℓ hne = f.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hf hfdeg0 hℓ hcop hpure hne
  have hfdegd : f.natDegree = ℓ * sideDeg φ f u ℓ hne * φ.natDegree := by rw [hdl]; exact hfdeg0
  have hH₀d : H₀ = u * sideDeg φ f u ℓ hne :=
    height_eq_of_pure hφ.monic hφ.pos hf hfdegd hℓ hcop hpure hne hH₀
  have hRdeg : (resPoly π φ f u ℓ hne H₀).natDegree = sideDeg φ f u ℓ hne :=
    (natDegree_resPoly hπ hφ hℓ hcop htf hne hHf).1
  have hRmonic : (resPoly π φ f u ℓ hne H₀).Monic := by
    show (resPoly π φ f u ℓ hne H₀).coeff (resPoly π φ f u ℓ hne H₀).natDegree = 1
    rw [hRdeg, resPoly_coeff_of_pure hπ hφ.monic hφ.pos hf hfdegd hℓ hcop hpure hne H₀
      (sideDeg φ f u ℓ hne), hH₀d, Nat.sub_self,
      dev_top hφ.monic hφ.pos hf (μ := ℓ * sideDeg φ f u ℓ hne) hfdegd, resMk_one hπ]
  -- ## B.45 factors the residual polynomial
  obtain ⟨s, a, hmon, hapos, hpc, hRprod, -⟩ :=
    exists_residual_factorization (K := resField φ) hRmonic (by rw [hRdeg]; exact hd)
  -- ## the recursion does the rest
  obtain ⟨F, hFprod, hFprops, hFres⟩ :=
    exists_dissection_aux hπ hφ hu hℓ hcop a s hmon hpc f hf hfd hpure hne H₀ hH₀ hRprod
  exact ⟨s, a, F, fun ψ hψ => ⟨(hmon ψ hψ).1, (hmon ψ hψ).2, hapos ψ hψ⟩,
    hFprod, hFprops, hFres⟩

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_residual_dissection
end AxCheck
