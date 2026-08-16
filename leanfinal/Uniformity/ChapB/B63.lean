/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B27
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B41b
import Uniformity.ChapB.B42
import Uniformity.ChapB.B45
import Uniformity.ChapB.B47
import Uniformity.ChapB.B57
import Uniformity.ChapB.B58
import Uniformity.ChapB.B60
import Uniformity.ChapB.B61
import Uniformity.ChapB.B63a
import Uniformity.ChapB.B66
import Uniformity.ChapB.B69
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.ChapB.B63 — NS-6 (⇐): separable residuals make the type the order-1 datum

**Chapter B, NODE B.63** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C, **re-signed at
amendment A-F.11 (2026-08-16)**. One signed declaration, plus the booked read-off lemma
`order1Type_data_eq_sum`.

*The statement.* Let `φ` be an order-1 key, `f` monic with `f̄ = φ̄ ^ μ`, `0 < μ`, and
`dev φ f 0 ≠ 0` (the classical `φ ∤ f`). If every two-point side of `f`'s `φ`-adic Newton
polygon has **separable** residual polynomial, then

```
(typeOf f).data = (order1Type π φ f).data
```

— B.66's canonical datum, i.e. `Σ_{S ∈ slopeFinset π φ f} Σ_{ψ ∈ resFactorFinset π φ f S}
{(ℓ_S, m · deg ψ)}` — together with the (deliberately index-free) NS-6 (⇐) factorization clause.

**A-F.11.** The committed A-F.9-era conclusion produced an existential index `T` tied to nothing,
so B.79a's term-by-term tie was underivable from any proof of this node (§14 item 12). The datum
identity below is what the blueprint's steps 1–4 actually prove, and `h0` comes with it: without
`h0` the canonical form is refuted at `f = φ` (`slopeFinset π φ φ = ∅` while
`typeOf φ = ⟨{(1, m)}⟩`).

## Proof

0. **Retired at A-F.11** — `h0` is a hypothesis, so there is nothing to peel.
1. **The slope leg of the canonical tie.** B.42's clause 5 (the two-point-side characterisation)
   and clause 1 (lowest terms) give `s = slopeFinset π φ f` by `Finset.ext` against B.66a's landed
   `mem_slopeFinset` / `mem_slopeFinset_imp`; the degree pin `f.natDegree = μ * φ.natDegree` is
   free from `hf`/`hres` by landed `natDegree_eq_of_map_eq`.
2. **The residual leg.** At each slope the block `F p` is `(p.1, p.2)`-pure with monic residual
   polynomial of positive degree; B.42's clause 6 (the residual tie) transports `hsep`'s
   separability from `f`'s pinned residual to the block's, so B.45's factorization has every
   multiplicity `1` and the block's residual is a product of **distinct** monic irreducibles.
   Its factor set is therefore exactly the set of monic irreducible divisors of `f`'s own
   `sideMin`-pinned residual — B.66a's reading of `resFactorFinset π φ f p` (the `←` half uses
   `Prime.exists_mem_finset_dvd` and `eq_of_monic_of_associated`).
3. **Each piece is a leaf.** `exists_pinned_dissection` (a `Finset.induction` over B.41's graded
   Hensel factorization) splits the block along that factorization into monic `(u,ℓ)`-pure pieces
   with residual polynomial *equal* to `ψ` and degree `ℓ · m · deg ψ`; `typeOf_leaf_block` then
   values each piece at `⟨{(ℓ, m · deg ψ)}⟩` by the three-way perimeter split — B.58 at
   `deg ψ = 1`, B.61 under `B-BOX-1`, and, at `ℓ = 1 ∧ m = 1`, B.60.
4. **Assembly.** B.63a's `typeOf_prod` twice (outer over `slopeFinset`, inner over
   `resFactorFinset`) plus `order1Type_data_eq_sum`.

## The `ℓ = 1, m = 1` corner: B.60 is signed at `φ = X`, the hypothesis says `φ.natDegree = 1`

A degree-1 key is `X + C c₀`, not literally `X`, and A-F.7 re-signed B.60 at the literal key `X`.
The gap is closed here, not by weakening anything: `typeOf_leaf_linear_key` shifts by `-c₀`.
B.69(a)/(b) make `dev` and `npHgt` shift-covariant, hence `suppVal`, `OnSide`, `sideSet`,
`sideMin`, `sideDeg` and `IsPure` all transport verbatim; the residual polynomials at `φ` and at
`X` are the images of the **same** polynomial over `ResidueField O` (at a degree-1 key every
`dev φ g k` is a constant, so `resMk` factors through `digAt`), and at a degree-1 key
`algebraMap (ResidueField O) (resField φ)` is bijective, so irreducibility transports along
`Polynomial.mapEquiv`. Landed `typeOf_shift` carries the answer back. This is the only place the
node uses B.69.

## The retained factorization clause is weak, deliberately

`∃ T F, f = ∏ t ∈ T, F t` is satisfied by any monic `f` at a singleton `T`; the leaf content lives
in the STATEMENT prose and in the per-leaf B.58/B.60/B.61 applications inside the proof. A-F.11 (IV)
records this honestly, and A-F.11 (VII) records the candidate strengthening that was NOT applied.

DEPENDS: B.27 · **B.42** (the signed literature axiom) · B.39b (`sideSet_nonempty_gen`) ·
B.41b (`exists_graded_factorization`) · B.45 · B.47 · B.57 (`map_residue_eq_key_pow_of_pure`) ·
B.58 · B.60 · B.61 · B.63a (`typeOf_prod`) · B.66 (`order1Type`, `order1Type_data`) ·
B.66a (`slopeFinset`, `resFactorFinset`, `mem_slopeFinset`, `mem_resFactorFinset` and the two
`_imp` halves) · B.69 (`dev_comp_shift`, `npHgt_comp_shift`) · landed
`Uniformity.Density.typeOf_shift`, `shift_monic`, `shift_natDegree`
(`Density/TypeOfInvariance.lean`), `Uniformity.Hensel.natDegree_eq_of_map_eq` · mathlib
`AdjoinRoot.mk_surjective`, `Polynomial.mapEquiv`, `MulEquiv.irreducible_iff`,
`Prime.exists_mem_finset_dvd`, `Polynomial.eq_of_monic_of_associated`.

**B.48 is NOT on the import path.** The blueprint routes step 2 through B.48
(`exists_residual_dissection`), whose *conclusion* records only the sub-blocks' own residual
polynomials `C c · ψ ^ a ψ` — it never states that the input's residual is the product of them,
which is exactly what the canonical index tie needs. The equivalent content is obtained here by
applying B.45 to the block's residual polynomial directly and then re-running B.41 along that
prescribed factorization (`exists_pinned_dissection`, §1 below), which is B.48's own proof
skeleton with the index set pinned. Recorded for the DEPENDS audit.

**SIZE.** blueprint 70 lines; landed 320.

**TEETH.** `W12-SHAPE` (0/164, both directions), `W12-ORACLE` (`[IND]`, 0 bad / 41,923) →
**executable regression** retained; `HE-SIG` (`EFF.HE3.52`) → **Lean theorem** inside the
perimeter.

SOURCE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1; `EFF.W12.27`; `EFF.HE3.15`
(DEFINITION 2 clause (a)); `EFF.W12.86` steps 5–6.

## Status

Sorry-free. **The axiom footprint is `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`** — the 2026-08-16 owner-signed B.42
literature cite (GN15 Thm 2.3 + FGMN Thm 6.6). This node is the first consumer of that axiom and
every downstream `#print axioms` will display it; that is correct and expected. No other axiom is
introduced. `order1Type_data_eq_sum` is Lean-core only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-! ## 1. The pinned dissection -/

omit [Finite (ResidueField O)] in
private theorem exists_pinned_dissection (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) :
    ∀ s : Finset (Polynomial (resField φ)),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) →
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) →
      ∀ f : Polynomial O, f.Monic → φ.natDegree ∣ f.natDegree → IsPure φ f u ℓ →
      ∀ (hne : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), npHgt φ f 0 = (H₀ : ℕ∞) →
      resPoly π φ f u ℓ hne H₀ = ∏ ψ ∈ s, ψ →
      ∃ G : Polynomial (resField φ) → Polynomial O,
        f = ∏ ψ ∈ s, G ψ ∧
        (∀ ψ ∈ s, (G ψ).Monic ∧ IsPure φ (G ψ) u ℓ ∧
          (G ψ).natDegree = ℓ * φ.natDegree * ψ.natDegree ∧
          npHgt φ (G ψ) 0 = ((u * ψ.natDegree : ℕ) : ℕ∞) ∧
          ∀ hne' : (sideSet φ (G ψ) u ℓ).Nonempty,
            resPoly π φ (G ψ) u ℓ hne' (u * ψ.natDegree) = ψ) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ f hf hfd hpure hne H₀ hH₀ hres
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
    refine ⟨fun _ => 1, ?_, ?_⟩
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hf hf0, Finset.prod_empty]
    · intro ψ hψ; simp at hψ
  | insert ψ₀ s' hψ₀ ih =>
    intro hmon hpc f hf hfd hpure hne H₀ hH₀ hres
    have hψ₀mem : ψ₀ ∈ insert ψ₀ s' := Finset.mem_insert_self _ _
    have hψ₀m : ψ₀.Monic := (hmon ψ₀ hψ₀mem).1
    have hHm : (∏ ψ ∈ s', ψ).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun ψ hψ => (hmon ψ (Finset.mem_insert_of_mem hψ)).1
    have hGH : IsCoprime ψ₀ (∏ ψ ∈ s', ψ) :=
      IsCoprime.prod_right fun ψ hψ =>
        hpc ψ₀ hψ₀mem ψ (Finset.mem_insert_of_mem hψ) fun hcon => hψ₀ (hcon ▸ hψ)
    have hprod : ∃ c : (resField φ)ˣ, resPoly π φ f u ℓ hne H₀
        = Polynomial.C (c : resField φ) * (ψ₀ * ∏ ψ ∈ s', ψ) := by
      refine ⟨1, ?_⟩
      rw [hres, Finset.prod_insert hψ₀]
      simp
    obtain ⟨g, h, hgm, hhm, hfgh, hgdeg, hhdeg, hgp, hhp, -, hgH, hhH, hgres, hhres⟩ :=
      exists_graded_factorization hπ hφ hu hℓ hcop hf hfd hpure hH₀ hne hψ₀m hHm hGH hprod
    have hhd : φ.natDegree ∣ h.natDegree := ⟨ℓ * (∏ ψ ∈ s', ψ).natDegree, by
      rw [hhdeg]; ring⟩
    have hhne : (sideSet φ h u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
    obtain ⟨G', hG'prod, hG'props⟩ :=
      ih (fun ψ hψ => hmon ψ (Finset.mem_insert_of_mem hψ))
        (fun ψ hψ χ hχ hne' =>
          hpc ψ (Finset.mem_insert_of_mem hψ) χ (Finset.mem_insert_of_mem hχ) hne')
        h hhm hhd hhp hhne (u * (∏ ψ ∈ s', ψ).natDegree) hhH (hhres hhne)
    refine ⟨fun ψ => if ψ = ψ₀ then g else G' ψ, ?_, ?_⟩
    · have hFeq : ∀ ψ ∈ s', (if ψ = ψ₀ then g else G' ψ) = G' ψ := by
        intro ψ hψ
        have hnem : ψ ≠ ψ₀ := fun hcon => hψ₀ (hcon ▸ hψ)
        simp [hnem]
      rw [Finset.prod_insert hψ₀, if_pos rfl, hfgh, hG'prod]
      exact congrArg (g * ·) (Finset.prod_congr rfl fun ψ hψ => (hFeq ψ hψ).symm)
    · intro ψ hψ
      rcases Finset.mem_insert.1 hψ with rfl | hψ'
      · simp only []
        exact ⟨hgm, hgp, hgdeg, hgH, hgres⟩
      · have hnem : ψ ≠ ψ₀ := fun hcon => hψ₀ (hcon ▸ hψ')
        simp only [if_neg hnem]
        exact hG'props ψ hψ'

/-! ## 2. `order1Type`'s datum as a double sum -/

private theorem sum_map_singleton_eq_map {α β : Type*} (m : Multiset α) (h : α → β) :
    (m.map (fun a => ({h a} : Multiset β))).sum = m.map h := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [ih]

omit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] in
/-- The `Multiset.bind` of B.66's definition, read as a double `Finset` sum over the two
canonical index finsets. -/
theorem order1Type_data_eq_sum (π : O) (φ f : Polynomial O) :
    (order1Type π φ f).data
      = ∑ p ∈ slopeFinset π φ f, ∑ ψ ∈ resFactorFinset π φ f p,
          ({(p.2, φ.natDegree * ψ.natDegree)} : Multiset (ℕ × ℕ)) := by
  classical
  rw [order1Type_data, Finset.sum_eq_multiset_sum]
  show (Multiset.map _ _).sum = _
  congr 1
  refine Multiset.map_congr rfl ?_
  intro p _
  rw [Finset.sum_eq_multiset_sum]
  exact (sum_map_singleton_eq_map _ _).symm

/-! ## 3. The `ℓ = 1`, `m = 1` corner: B.60 transported to a general linear key -/

private theorem min'_congr' {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

private theorem max'_congr' {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst h; rfl

omit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] in
/-- At a degree-1 key the `φ`-adic development is a constant polynomial. -/
private theorem dev_eq_C_of_natDegree_one {φ : Polynomial O} (hφm : φ.Monic)
    (hm : φ.natDegree = 1) (f : Polynomial O) (j : ℕ) :
    dev φ f j = Polynomial.C ((dev φ f j).coeff 0) := by
  refine Polynomial.eq_C_of_natDegree_eq_zero ?_
  rcases eq_or_ne (dev φ f j) 0 with h0 | h0
  · simp [h0]
  · have hlt : (dev φ f j).degree < φ.degree := degree_dev_lt hφm (by omega) f j
    have hφd : φ.degree = (1 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hφm.ne_zero, hm]
    rw [hφd] at hlt
    have := (Polynomial.natDegree_lt_iff_degree_lt h0 (n := 1)).mpr hlt
    omega

omit [Finite (ResidueField O)] in
/-- At a degree-1 key the residual field is the residue field: the structure map is bijective. -/
private theorem algebraMap_resField_bijective {φ : Polynomial O} (hφ : IsKey φ)
    (hm : φ.natDegree = 1) :
    Function.Bijective (algebraMap (IsLocalRing.ResidueField O) (resField φ)) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have hFm : (φ.map (IsLocalRing.residue O)).Monic := hφ.monic.map _
  have hFdeg : (φ.map (IsLocalRing.residue O)).natDegree = 1 := by
    rw [hφ.monic.natDegree_map]; exact hm
  have hFne1 : (φ.map (IsLocalRing.residue O)) ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hFdeg
    omega
  refine ⟨(algebraMap (IsLocalRing.ResidueField O) (resField φ)).injective, ?_⟩
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨(q %ₘ (φ.map (IsLocalRing.residue O))).coeff 0, ?_⟩
  have hmod : q %ₘ (φ.map (IsLocalRing.residue O))
      = Polynomial.C ((q %ₘ (φ.map (IsLocalRing.residue O))).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by
      have := Polynomial.natDegree_modByMonic_lt q hFm hFne1
      omega)
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← hmod]
  refine AdjoinRoot.mk_eq_mk.mpr ⟨-(q /ₘ (φ.map (IsLocalRing.residue O))), ?_⟩
  have h := Polynomial.modByMonic_add_div q (φ.map (IsLocalRing.residue O))
  linear_combination h

omit [Finite (ResidueField O)] in
/-- Irreducibility over the residual field of a degree-1 key is irreducibility over the residue
field: the structure map is a ring isomorphism. -/
private theorem irreducible_map_algebraMap_iff {φ : Polynomial O} (hφ : IsKey φ)
    (hm : φ.natDegree = 1) {R : Polynomial (IsLocalRing.ResidueField O)} :
    Irreducible (R.map (algebraMap (IsLocalRing.ResidueField O) (resField φ)))
      ↔ Irreducible R := by
  letI : Field (resField φ) := instFieldResField hφ
  set e : IsLocalRing.ResidueField O ≃+* resField φ :=
    RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField O) (resField φ))
      (algebraMap_resField_bijective hφ hm) with he
  have hmap : R.map (algebraMap (IsLocalRing.ResidueField O) (resField φ))
      = Polynomial.mapEquiv e R := rfl
  rw [hmap]
  exact MulEquiv.irreducible_iff (Polynomial.mapEquiv e)

omit [Finite (ResidueField O)] in
/-- At a degree-1 key the residual polynomial of a pure `f` is the image, under the structure map
of the residual field, of a polynomial over the residue field read off the development's digits.
-/
private theorem resPoly_eq_map_of_natDegree_one {φ : Polynomial O}
    (hφ : IsKey φ) (hm : φ.natDegree = 1) {u : ℕ} {g : Polynomial O}
    (hpure : IsPure φ g u 1) (hne : (sideSet φ g u 1).Nonempty) (H₀ : ℕ) :
    resPoly π φ g u 1 hne H₀
      = (∑ k ∈ Finset.range (sideDeg φ g u 1 hne + 1),
          Polynomial.C (digAt π (H₀ - u * k) ((dev φ g k).coeff 0)) * Polynomial.X ^ k).map
        (algebraMap (IsLocalRing.ResidueField O) (resField φ)) := by
  have hmin : sideMin φ g u 1 hne = 0 := sideMin_of_pure hpure hne
  rw [resPoly, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoef : resCoeff π φ g u 1 hne H₀ k
      = algebraMap (IsLocalRing.ResidueField O) (resField φ)
          (digAt π (H₀ - u * k) ((dev φ g k).coeff 0)) := by
    rw [resCoeff, hmin, Nat.zero_add, Nat.one_mul]
    conv_lhs => rw [dev_eq_C_of_natDegree_one hφ.monic hm g k]
    rw [resMk, digPoly_C, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  rw [hcoef, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

omit [Finite (ResidueField O)] in
/-- **The `ℓ = 1`, `m = 1` corner of D-3's perimeter — B.60 at a general linear key.** A degree-1
key is `X + C c₀`; B.69's shift covariance carries the whole `φ`-polygon to the key `X`, where
B.60 applies, and `typeOf` is shift-invariant (landed `typeOf_shift`). -/
private theorem typeOf_leaf_linear_key (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    (hm : φ.natDegree = 1) {u : ℕ} (hu : 0 < u) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure φ g u 1) (hne : (sideSet φ g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ g 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg φ g u 1 hne)
    (hirr : Irreducible (resPoly π φ g u 1 hne H₀)) :
    typeOf g = ⟨{(1, sideDeg φ g u 1 hne)}⟩ := by
  classical
  have hkeyX : IsKey (X : Polynomial O) :=
    ⟨monic_X, by rw [Polynomial.natDegree_X]; omega, by
      rw [Polynomial.map_X]; exact Polynomial.irreducible_X⟩
  set c₀ : O := -φ.coeff 0 with hc₀
  have hφshift : φ.comp (X + Polynomial.C c₀) = X := by
    conv_lhs => rw [hφ.monic.eq_X_add_C hm]
    simp [hc₀]
  set g₁ : Polynomial O := g.comp (X + Polynomial.C c₀) with hg₁
  -- ## the shift transports the polygon
  have hnp : ∀ j, npHgt (X : Polynomial O) g₁ j = npHgt φ g j := by
    intro j
    have h := npHgt_comp_shift hπ φ c₀ g j
    rw [hφshift, ← hg₁] at h
    exact h
  have hdeg1 : g₁.natDegree = g.natDegree := by
    have h := Uniformity.Density.shift_natDegree g c₀
    rw [Uniformity.Density.shift_apply, ← hg₁] at h
    exact h
  have hg₁m : g₁.Monic := by
    have h := Uniformity.Density.shift_monic hg c₀
    rw [Uniformity.Density.shift_apply, ← hg₁] at h
    exact h
  have hsupp : ∀ v w : ℕ, suppVal (X : Polynomial O) g₁ v w = suppVal φ g v w := by
    intro v w
    simp only [suppVal, hdeg1, hnp]
  have hOn : ∀ v w j : ℕ, OnSide (X : Polynomial O) g₁ v w j ↔ OnSide φ g v w j := by
    intro v w j
    simp only [OnSide, hnp, hsupp]
  have hset : sideSet (X : Polynomial O) g₁ u 1 = sideSet φ g u 1 := by
    ext j
    simp only [sideSet, Finset.mem_filter, Finset.mem_range, hdeg1]
    exact and_congr_right fun _ => hOn u 1 j
  have hne₁ : (sideSet (X : Polynomial O) g₁ u 1).Nonempty := by rw [hset]; exact hne
  have hminE : sideMin (X : Polynomial O) g₁ u 1 hne₁ = sideMin φ g u 1 hne :=
    min'_congr' hset _ _
  have hmaxE : sideMax (X : Polynomial O) g₁ u 1 hne₁ = sideMax φ g u 1 hne :=
    max'_congr' hset _ _
  have hsdeg : sideDeg (X : Polynomial O) g₁ u 1 hne₁ = sideDeg φ g u 1 hne := by
    simp only [sideDeg, hminE, hmaxE]
  have hpure₁ : IsPure (X : Polynomial O) g₁ u 1 := by
    obtain ⟨h1, h2⟩ := hpure
    refine ⟨(hOn u 1 0).mpr h1, ?_⟩
    have hq : g₁.natDegree / (X : Polynomial O).natDegree = g.natDegree / φ.natDegree := by
      rw [hdeg1, hm, Polynomial.natDegree_X]
    rw [hq]
    exact (hOn u 1 _).mpr h2
  have hH₀₁ : npHgt (X : Polynomial O) g₁ 0 = (H₀ : ℕ∞) := by rw [hnp]; exact hH₀
  -- ## the reduction at the key `X`
  have hcop1 : Nat.Coprime u 1 := Nat.coprime_one_right u
  have hdeg0 : g.natDegree = g.natDegree * φ.natDegree := by rw [hm, Nat.mul_one]
  have hDg : sideDeg φ g u 1 hne = g.natDegree := by
    have h := sideDeg_of_pure hφ.monic hφ.pos hg hdeg0 Nat.one_pos hcop1 hpure hne
    omega
  have hres₁ : g₁.map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O)) ^ (sideDeg (X : Polynomial O) g₁ u 1 hne₁) := by
    refine map_residue_eq_key_pow_of_pure hπ hkeyX hu Nat.one_pos hg₁m ?_ hpure₁
    rw [hsdeg, hDg, hdeg1, Polynomial.natDegree_X, Nat.mul_one]
  -- ## the residual polynomials at `φ` and at `X` are the same polynomial over the residue field
  have hdevX : ∀ k, dev (X : Polynomial O) g₁ k = dev φ g k := by
    intro k
    have h := dev_comp_shift φ c₀ g k
    rw [hφshift, ← hg₁] at h
    rw [h, dev_eq_C_of_natDegree_one hφ.monic hm g k, Polynomial.C_comp]
  have hirr₁ : Irreducible (resPoly π (X : Polynomial O) g₁ u 1 hne₁ H₀) := by
    rw [resPoly_eq_map_of_natDegree_one hkeyX Polynomial.natDegree_X hpure₁ hne₁ H₀]
    refine (irreducible_map_algebraMap_iff hkeyX Polynomial.natDegree_X).mpr ?_
    simp only [hsdeg, hdevX]
    refine (irreducible_map_algebraMap_iff hφ hm (R := _)).mp ?_
    rw [← resPoly_eq_map_of_natDegree_one hφ hm hpure hne H₀]
    exact hirr
  -- ## B.60 at the key `X`, transported back by shift-invariance of `typeOf`
  have h60 := typeOf_leaf_integral_slope hπ hu hg₁m hpure₁ hne₁ hH₀₁ (by rw [hsdeg]; exact hd)
    hres₁ hirr₁
  have hshift : typeOf g₁ = typeOf g := by rw [hg₁]; exact typeOf_shift hg c₀
  rw [← hshift, h60, Polynomial.natDegree_X, Nat.one_mul, hsdeg]

/-! ## 4. The leaf value at a dissection block -/

private theorem typeOf_leaf_block (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    {ψ : Polynomial (resField φ)} (hψi : Irreducible ψ)
    (hgdeg : g.natDegree = ℓ * φ.natDegree * ψ.natDegree)
    (hH : npHgt φ g 0 = ((u * ψ.natDegree : ℕ) : ℕ∞))
    (hgres : resPoly π φ g u ℓ hne (u * ψ.natDegree) = ψ)
    (hdisj : (ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
      ∀ g' ∈ monicFactors g, φ.natDegree * ψ.natDegree ∣ inertiaDegOf g') :
    typeOf g = ⟨{(ℓ, φ.natDegree * ψ.natDegree)}⟩ := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have hψpos : 0 < ψ.natDegree := hψi.natDegree_pos
  have hgdeg' : g.natDegree = (ℓ * ψ.natDegree) * φ.natDegree := by rw [hgdeg]; ring
  have htg : suppVal φ g u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hg hgdeg' u ℓ)
  have hming : sideMin φ g u ℓ hne = 0 := sideMin_of_pure hpure hne
  have hHg : npHgt φ g (sideMin φ g u ℓ hne) = ((u * ψ.natDegree : ℕ) : ℕ∞) := by
    rw [hming]; exact hH
  have hsd : sideDeg φ g u ℓ hne = ψ.natDegree := by
    rw [← (natDegree_resPoly hπ hφ hℓ hcop htg hne hHg).1, hgres]
  have hresmap : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * ψ.natDegree) :=
    map_residue_eq_key_pow_of_pure hπ hφ hu hℓ hg hgdeg' hpure
  rcases hdisj with ⟨hl1, hm1⟩ | hd1 | hBOX
  · -- the `ℓ = 1`, `m = 1` corner: B.60 at the linear key, through B.69's shift
    subst hl1
    have := typeOf_leaf_linear_key hπ hφ hm1 hu hg hpure hne hH (hsd ▸ hψpos)
      (by rw [hgres]; exact hψi)
    rw [this, hsd, hm1, one_mul]
  · -- residual degree 1: B.58, unconditionally
    have h1 : sideDeg φ g u ℓ hne = 1 := by rw [hsd, hd1]
    have hres' : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ ℓ := by
      rw [hresmap, hd1, Nat.mul_one]
    rw [typeOf_leaf_resDeg_one hπ hφ hu hℓ hcop hg hpure hne h1 hres', hd1, Nat.mul_one]
  · -- the general perimeter: B.61 under `B-BOX-1`
    have hres' : g.map (IsLocalRing.residue O)
        = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne) := by rw [hsd]; exact hresmap
    have hBOX' : ∀ g' ∈ monicFactors g,
        φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g' := by rw [hsd]; exact hBOX
    rw [typeOf_leaf_of_resDeg_lower_bound hπ hφ hu hℓ hcop hg hpure hne (hsd ▸ hψpos) hres' hBOX',
      hsd]

/-! ## 4. The node -/

theorem typeOf_of_separable_residuals (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0)
    (hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
      1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
        (resPoly π φ f u ℓ h H₀).Separable)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ f → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    (typeOf f).data = (order1Type π φ f).data ∧
      ∃ (T : Finset ((ℕ × ℕ) × Polynomial (resField φ)))
        (F : (ℕ × ℕ) × Polynomial (resField φ) → Polynomial O), f = ∏ t ∈ T, F t := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  haveI : Finite (resField φ) := instFiniteResField hφ
  have hdeg : f.natDegree = μ * φ.natDegree := by
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq hf hres, Polynomial.natDegree_pow,
      hφ.monic.natDegree_map]
  obtain ⟨s, F, hcl1, -, hcl3, hprod, hcl5, hcl6⟩ :=
    exists_slope_factorization hπ hφ hf hμ hres h0
  -- ## step 1 — the slope index is `slopeFinset`
  have hs : s = slopeFinset π φ f := by
    ext p
    constructor
    · intro hp
      obtain ⟨-, hp2, hpc⟩ := hcl1 p hp
      exact (mem_slopeFinset hφ hf hdeg).mpr ⟨hp2, hpc, (hcl5 p.1 p.2 hp2 hpc).mpr (by simpa using hp)⟩
    · intro hp
      obtain ⟨hp2, hpc, hcard⟩ := mem_slopeFinset_imp hp
      simpa using (hcl5 p.1 p.2 hp2 hpc).mp hcard
  -- ## steps 2-3 — every slope block dissects into leaves indexed by `resFactorFinset`
  have key : ∀ p : ℕ × ℕ, ∃ G : Polynomial (resField φ) → Polynomial O,
      p ∈ s → ((F p = ∏ ψ ∈ resFactorFinset π φ f p, G ψ) ∧
        (∀ ψ ∈ resFactorFinset π φ f p, (G ψ).Monic) ∧
        (∀ ψ ∈ resFactorFinset π φ f p,
          typeOf (G ψ) = ⟨{(p.2, φ.natDegree * ψ.natDegree)}⟩)) := by
    intro p
    by_cases hp : p ∈ s
    swap
    · exact ⟨fun _ => 1, fun h => absurd h hp⟩
    obtain ⟨hp1, hp2, hpc⟩ := hcl1 p hp
    obtain ⟨hFm, hFpure, hFdvd, hFdev, hFdegpos⟩ := hcl3 p hp
    have hneF : (sideSet φ (F p) p.1 p.2).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hnef : (sideSet φ f p.1 p.2).Nonempty := sideSet_nonempty_gen _ _ _ _
    obtain ⟨HF, hHF⟩ := WithTop.ne_top_iff_exists.mp
      (show npHgt φ (F p) 0 ≠ ⊤ from fun hcon => hFdev (npHgt_eq_top_iff.mp hcon))
    have htf : suppVal φ f p.1 p.2 ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg p.1 p.2)
    have hminmem : sideMin φ f p.1 p.2 hnef ∈ sideSet φ f p.1 p.2 := Finset.min'_mem _ _
    obtain ⟨Hf, hHf⟩ := WithTop.ne_top_iff_exists.mp
      (npHgt_ne_top_of_onSide hp2 htf (onSide_of_mem_sideSet hminmem))
    have hcard : 1 < (sideSet φ f p.1 p.2).card :=
      (hcl5 p.1 p.2 hp2 hpc).mpr (by simpa using hp)
    have hsepf : (resPoly π φ f p.1 p.2 hnef Hf).Separable :=
      hsep p.1 p.2 hp2 hpc hnef hcard Hf hHf.symm
    have hminF : sideMin φ (F p) p.1 p.2 hneF = 0 := sideMin_of_pure hFpure hneF
    have hHF' : npHgt φ (F p) (sideMin φ (F p) p.1 p.2 hneF) = (HF : ℕ∞) := by
      rw [hminF]; exact hHF.symm
    obtain ⟨c, hc⟩ := hcl6 p hp hnef hneF Hf HF hHf.symm hHF'
    have hsepF : (resPoly π φ (F p) p.1 p.2 hneF HF).Separable := by
      rw [hc] at hsepf; exact hsepf.of_mul_right
    -- the block's residual polynomial is monic of positive degree
    have hFdeg0 : (F p).natDegree = ((F p).natDegree / φ.natDegree) * φ.natDegree :=
      (Nat.div_mul_cancel hFdvd).symm
    have htF : suppVal φ (F p) p.1 p.2 ≠ ⊤ := by
      rw [suppVal_of_pure hφ.monic hφ.pos hFm hFdeg0 hFpure]; exact ENat.coe_ne_top _
    have hdl : p.2 * sideDeg φ (F p) p.1 p.2 hneF = (F p).natDegree / φ.natDegree :=
      sideDeg_of_pure hφ.monic hφ.pos hFm hFdeg0 hp2 hpc hFpure hneF
    have hdpos : 0 < sideDeg φ (F p) p.1 p.2 hneF := by
      rcases Nat.eq_zero_or_pos (sideDeg φ (F p) p.1 p.2 hneF) with hz | hz
      · exfalso
        rw [hz, Nat.mul_zero] at hdl
        have : (F p).natDegree = 0 := by rw [hFdeg0, ← hdl, Nat.zero_mul]
        omega
      · exact hz
    have hRdeg : (resPoly π φ (F p) p.1 p.2 hneF HF).natDegree
        = sideDeg φ (F p) p.1 p.2 hneF := (natDegree_resPoly hπ hφ hp2 hpc htF hneF hHF').1
    have hFdegd : (F p).natDegree = p.2 * sideDeg φ (F p) p.1 p.2 hneF * φ.natDegree := by
      rw [hdl]; exact hFdeg0
    have hHFd : HF = p.1 * sideDeg φ (F p) p.1 p.2 hneF :=
      height_eq_of_pure hφ.monic hφ.pos hFm hFdegd hp2 hpc hFpure hneF hHF.symm
    have hRmonic : (resPoly π φ (F p) p.1 p.2 hneF HF).Monic := by
      show (resPoly π φ (F p) p.1 p.2 hneF HF).coeff
        (resPoly π φ (F p) p.1 p.2 hneF HF).natDegree = 1
      rw [hRdeg, resPoly_coeff_of_pure hπ hφ.monic hφ.pos hFm hFdegd hp2 hpc hFpure hneF HF
        (sideDeg φ (F p) p.1 p.2 hneF), hHFd, Nat.sub_self,
        dev_top hφ.monic hφ.pos hFm (μ := p.2 * sideDeg φ (F p) p.1 p.2 hneF) hFdegd,
        resMk_one hπ]
    -- B.45: the residual polynomial is a product of distinct monic irreducibles
    obtain ⟨s', a', hmonirr, -, hcop', hRfact, hsepiff⟩ :=
      exists_residual_factorization hRmonic (by rw [hRdeg]; exact hdpos)
    have ha1 : ∀ ψ ∈ s', a' ψ = 1 := hsepiff.mp hsepF
    have hRprod : resPoly π φ (F p) p.1 p.2 hneF HF = ∏ ψ ∈ s', ψ := by
      rw [hRfact]
      exact Finset.prod_congr rfl fun ψ hψ => by rw [ha1 ψ hψ, pow_one]
    -- the pinned dissection of the block along that factorization
    obtain ⟨G, hGprod, hGprops⟩ :=
      exists_pinned_dissection hπ hφ hp1 hp2 hpc s' hmonirr hcop' (F p) hFm hFdvd hFpure hneF HF
        hHF.symm hRprod
    -- the index set is `resFactorFinset`
    have hcinv : resPoly π φ (F p) p.1 p.2 hneF HF
        = Polynomial.C ((↑c⁻¹ : resField φ)) * resPoly π φ f p.1 p.2 hnef Hf := by
      rw [hc, ← mul_assoc, ← Polynomial.C_mul]
      simp
    have hidx : s' = resFactorFinset π φ f p := by
      ext ψ
      constructor
      · intro hψ
        refine (mem_resFactorFinset hπ hφ hf hdeg hp2 hpc).mpr
          ⟨(hmonirr ψ hψ).1, (hmonirr ψ hψ).2, ?_⟩
        intro hne'' H₀'' hH₀''
        obtain rfl : hne'' = hnef := rfl
        obtain rfl : H₀'' = Hf := by
          have hcast : ((H₀'' : ℕ) : ℕ∞) = ((Hf : ℕ) : ℕ∞) := by
            rw [← hH₀'']; exact hHf.symm
          exact_mod_cast hcast
        rw [hc]
        refine Dvd.dvd.mul_left ?_ _
        rw [hRprod]
        exact Finset.dvd_prod_of_mem _ hψ
      · intro hψ
        obtain ⟨hψm, hψi, hψd⟩ := mem_resFactorFinset_imp hψ
        have hdvdR : ψ ∣ resPoly π φ (F p) p.1 p.2 hneF HF := by
          rw [hcinv]
          exact Dvd.dvd.mul_left (hψd hnef Hf hHf.symm) _
        rw [hRprod] at hdvdR
        obtain ⟨χ, hχ, hdχ⟩ := hψi.prime.exists_mem_finset_dvd hdvdR
        have : ψ = χ := Polynomial.eq_of_monic_of_associated hψm (hmonirr χ hχ).1
          (hψi.associated_of_dvd (hmonirr χ hχ).2 hdχ)
        rw [this]; exact hχ
    subst hidx
    refine ⟨G, fun _ => ⟨hGprod, fun ψ hψ => (hGprops ψ hψ).1, fun ψ hψ => ?_⟩⟩
    obtain ⟨hGm, hGp, hGdeg, hGH, hGres⟩ := hGprops ψ hψ
    have hneG : (sideSet φ (G ψ) p.1 p.2).Nonempty := sideSet_nonempty_gen _ _ _ _
    have hminG : sideMin φ (G ψ) p.1 p.2 hneG = 0 := sideMin_of_pure hGp hneG
    have hdvdf : G ψ ∣ f := by
      rw [hprod]
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem F hp)
      rw [hGprod]
      exact Finset.dvd_prod_of_mem G hψ
    refine typeOf_leaf_block hπ hφ hp1 hp2 hpc hGm hGp hneG (hmonirr ψ hψ).2
      hGdeg hGH (hGres hneG) ?_
    refine hperim p.1 p.2 hp2 hpc (G ψ) hGm hdvdf hGp hneG (p.1 * ψ.natDegree) ?_ ψ
      (hmonirr ψ hψ).1 (hmonirr ψ hψ).2 ⟨1, ?_⟩
    · rw [hminG]; exact hGH
    · rw [hGres hneG, one_smul]
  choose G hG using key
  have hFtype : ∀ p ∈ s, (typeOf (F p)).data
      = ∑ ψ ∈ resFactorFinset π φ f p,
          ({(p.2, φ.natDegree * ψ.natDegree)} : Multiset (ℕ × ℕ)) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hG p hp
    rw [h1, typeOf_prod h2]
    exact Finset.sum_congr rfl fun ψ hψ => by rw [h3 ψ hψ]
  have hsum : (typeOf f).data = ∑ p ∈ s, (typeOf (F p)).data := by
    rw [hprod]; exact typeOf_prod (fun p hp => (hcl3 p hp).1)
  refine ⟨?_, ⟨{((0, 0), 1)}, fun _ => f, by simp⟩⟩
  rw [hsum, order1Type_data_eq_sum, ← hs]
  exact Finset.sum_congr rfl hFtype

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.order1Type_data_eq_sum
#print axioms Uniformity.Density.Leaf.typeOf_of_separable_residuals
end AxCheck
