/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG29
import Uniformity.ChapI.IFCG31
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.ChapI.IFCG32 — [INS 2026-08-30] the inertia-scaling leg, closed

UBC (`IFCG29.lean`) reduced the census's whole bridge family to the ONE-PARAMETER leg
`InertiaScaling δ`: for a monic irreducible `C` over the unramified extension
`O' = AdjoinRoot φ` (`φ` a degree-`δ` key) whose residual is `(X − θ̄)^deg C`, and `G`
the base descent of its conjugate product `∏_β τ_β(C)`, the inertia degree scales:

    inertiaDegOf G = δ · inertiaDegOf C.

This file PROVES the leg, for every `δ`, and fires the chain: `UnramifiedBlockCount δ e`
and `UnramifiedBlockBridge δ e` hold unconditionally for ALL `δ, e`, and the census front
loses the bridge family entirely (§6).

## The mechanism: `normValues G = δ • normValues C`, then gcd arithmetic

`inertiaDegOf` is the gcd (as `sSup` of common divisors) of the valuations of norms from
the root algebra.  Both inclusions are proved through ONE master identity: for every base
polynomial `P`,

    addVal_O (N_{O[X]/G}(P)) = δ · addVal_{O'} (N_{O'[X]/C}(P)),          (E1)

whose engine is elementary linear algebra, NOT field theory:

* **§0 norm transport along a ring map** (`norm_mk_map'`): for any ring map `f : R → S`
  and monic `G`, `N_{S[X]/G^f}(P^f) = f (N_{R[X]/G}(P))` — the multiplication matrices in
  the two power bases correspond entrywise under `f`, so the determinants correspond
  (`RingHom.map_det`).  Applied twice: to the base change `O → O'`, and to each
  conjugation `τ_β : O' → O'` (a base polynomial is `τ`-fixed, so the `β`-factor of the
  conjugate product contributes `τ_β(N_{O'[X]/C}(P))`).
* **§1 norm multiplicativity in the MODULUS** (`norm_mk_mul`): for monic `F, H`,
  `N_{S[X]/(FH)}(P) = N_{S[X]/F}(P) · N_{S[X]/H}(P)`.  No CRT and no coprimality: the
  adapted basis `{X^i·H} ⊔ {X^j}` of `S[X]/(FH)` makes the multiplication matrix block
  triangular (`Matrix.det_fromBlocks_zero₂₁`) with the two factor matrices as blocks.
* **§2 valuation transport**: `addVal` is preserved by any ring map carrying one
  irreducible to an irreducible (`u·π^n ↦ u'·π'^n`) — used for `O → O'` (B-side:
  `irreducible_algebraMap_adjoinRoot`, the unramifiedness input) and for each `τ_β`
  (which fixes the base uniformizer).

`⊆` (LEG A) is (E1) at a `mk`-preimage.  `⊇` (LEG B, the WITNESS) needs the conjugate
tuple `(τ_β(y))_β` realized as a base element: a CRT solution
`P' ≡ τ_β(Q) (mod τ_β(C))` exists because the conjugate factors are pairwise comaximal —
their residuals `(X − β)^d` at DISTINCT roots are coprime, and residual coprimality lifts
to `O'[X]` by **Nakayama** (§3, `S[X]/(F,H)` is `𝔪`-divisible and module-finite via monic
`F`).  The reduced representative mod `tauProd C` is `τ`-invariant as a POLYNOMIAL
(uniqueness of reduced representatives + `tauProd_map_tau`), hence descends to `O[X]` by
IFCG29's invariants theorem; (E1) evaluates its norm valuation to exactly `δ·v`.

Finally (§5) the gcd arithmetic: `δ·f_C` divides every norm valuation of `G`, hence
divides `f_G` (the B.52 lcm trick); conversely `f_G ∣ δ·v` for every norm valuation `v`
of `C`, hence `f_G ∣ δ·f_C` after cancelling `gcd(f_G, δ)`; `Nat.dvd_antisymm`.

Classical sanity check: `f(L'/K') = lcm(f_G, δ)/δ`, so the leg is equivalent to
`δ ∣ f_G`, which is B.52's content — but the proof here is independent and Lean-core.

## Axiom fence

Everything through `unramifiedBlockBridge_all` is Lean core (`propext`,
`Classical.choice`, `Quot.sound`); the C.33 cite does not occur.  The final §6 wiring
through IFCG31's census front additionally inherits IFCG31's single signed cite
(B.42 `exists_slope_factorization`), exactly as IFCG31 does.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG32

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG25 (fScale UnramifiedBlockBridge)
open Uniformity.Density.IFCG27
open Uniformity.Density.IFCG29
open Uniformity.Density.Leaf (IsKey keyIsDomain)

attribute [local instance] Classical.propDecidable

/-! ## §0 — norm transport along a ring map (the two power bases correspond) -/

section NormMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The canonical ring map `R[X]/(G) → S[X]/(G^f)` over `f : R → S`. -/
noncomputable def mapAdjoin (f : R →+* S) (G : Polynomial R) :
    AdjoinRoot G →+* AdjoinRoot (G.map f) :=
  AdjoinRoot.lift ((AdjoinRoot.of (G.map f)).comp f) (AdjoinRoot.root (G.map f)) (by
    rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root (G.map f))

theorem mapAdjoin_mk (f : R →+* S) (G : Polynomial R) (P : Polynomial R) :
    mapAdjoin f G (AdjoinRoot.mk G P) = AdjoinRoot.mk (G.map f) (P.map f) := by
  rw [mapAdjoin, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

theorem mapAdjoin_algebraMap (f : R →+* S) (G : Polynomial R) (a : R) :
    mapAdjoin f G (algebraMap R (AdjoinRoot G) a)
      = algebraMap S (AdjoinRoot (G.map f)) (f a) := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
    ← AdjoinRoot.mk_C, mapAdjoin_mk, Polynomial.map_C]

variable [Nontrivial S]

/-- The power basis of `S[X]/(G^f)`, reindexed by `Fin (deg G)`. -/
noncomputable def mappedBasis (f : R →+* S) {G : Polynomial R} (hG : G.Monic) :
    Module.Basis (Fin G.natDegree) S (AdjoinRoot (G.map f)) :=
  (rootBasis (hG.map f)).reindex (finCongr (hG.natDegree_map f))

theorem mappedBasis_apply (f : R →+* S) {G : Polynomial R} (hG : G.Monic)
    (i : Fin G.natDegree) :
    mappedBasis f hG i = AdjoinRoot.root (G.map f) ^ (i : ℕ) := by
  rw [mappedBasis, Module.Basis.reindex_apply, rootBasis_apply]
  simp

theorem mapAdjoin_rootBasis (f : R →+* S) {G : Polynomial R} (hG : G.Monic)
    (i : Fin G.natDegree) :
    mapAdjoin f G (rootBasis hG i) = mappedBasis f hG i := by
  rw [rootBasis_apply, mappedBasis_apply, map_pow]
  congr 1
  rw [← AdjoinRoot.mk_X, ← AdjoinRoot.mk_X, mapAdjoin_mk, Polynomial.map_X]

/-- **The master relation**: in the two power bases the transport map is coordinatewise
`f`. -/
theorem repr_mapAdjoin (f : R →+* S) {G : Polynomial R} (hG : G.Monic)
    (z : AdjoinRoot G) (i : Fin G.natDegree) :
    (mappedBasis f hG).repr (mapAdjoin f G z) i = f ((rootBasis hG).repr z i) := by
  classical
  conv_lhs => rw [← (rootBasis hG).sum_repr z]
  rw [map_sum, map_sum]
  have hterm : ∀ j : Fin G.natDegree,
      mapAdjoin f G ((rootBasis hG).repr z j • rootBasis hG j)
        = f ((rootBasis hG).repr z j) • mappedBasis f hG j := by
    intro j
    rw [Algebra.smul_def, map_mul, mapAdjoin_algebraMap, mapAdjoin_rootBasis,
      ← Algebra.smul_def]
  simp only [hterm, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp

/-- **Norms correspond under `f`** — the multiplication matrices correspond entrywise. -/
theorem norm_mapAdjoin (f : R →+* S) {G : Polynomial R} (hG : G.Monic)
    (z : AdjoinRoot G) :
    Algebra.norm S (mapAdjoin f G z) = f (Algebra.norm R z) := by
  classical
  rw [Algebra.norm_eq_matrix_det (mappedBasis f hG) (mapAdjoin f G z),
    Algebra.norm_eq_matrix_det (rootBasis hG) z, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← repr_mapAdjoin f hG,
    map_mul (mapAdjoin f G) z (rootBasis hG j), mapAdjoin_rootBasis]

/-- The call-site form, with the mapped modulus given by an equation (avoids dependent
rewrites at use sites). -/
theorem norm_mk_map' (f : R →+* S) {G : Polynomial R} {M : Polynomial S} (hG : G.Monic)
    (hM : G.map f = M) (P : Polynomial R) :
    Algebra.norm S (AdjoinRoot.mk M (P.map f))
      = f (Algebra.norm R (AdjoinRoot.mk G P)) := by
  subst hM
  rw [← mapAdjoin_mk, norm_mapAdjoin f hG]

end NormMap

/-! ## §1 — norm multiplicativity in the modulus (adapted basis, block determinant) -/

section NormModulus

variable {S : Type*} [CommRing S] [Nontrivial S]

/-- Over the trivial modulus the root algebra is trivial and every norm is `1`. -/
theorem norm_mk_one (P : Polynomial S) :
    Algebra.norm S (AdjoinRoot.mk (1 : Polynomial S) P) = 1 := by
  classical
  have b : Module.Basis (Fin 0) S (AdjoinRoot (1 : Polynomial S)) :=
    (rootBasis Polynomial.monic_one).reindex (finCongr Polynomial.natDegree_one)
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_isEmpty]

/-- `mk` of a coefficient combination is the corresponding `smul` combination. -/
theorem mk_sum {n : ℕ} (M : Polynomial S) (c : Fin n → S) (E : Fin n → Polynomial S) :
    AdjoinRoot.mk M (∑ t, Polynomial.C (c t) * E t)
      = ∑ t, c t • AdjoinRoot.mk M (E t) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, AdjoinRoot.mk_C, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

/-- The mod-`F` coefficient combination of any `V` has the same `mk F` image. -/
theorem mk_sum_repr {F : Polynomial S} (hF : F.Monic) (V : Polynomial S) :
    AdjoinRoot.mk F (∑ t, Polynomial.C ((rootBasis hF).repr (AdjoinRoot.mk F V) t)
        * Polynomial.X ^ (t : ℕ))
      = AdjoinRoot.mk F V := by
  rw [mk_sum]
  have hpow : ∀ t : Fin F.natDegree,
      AdjoinRoot.mk F (Polynomial.X ^ (t : ℕ)) = rootBasis hF t := by
    intro t
    rw [rootBasis_apply, map_pow, AdjoinRoot.mk_X]
  simp only [hpow]
  exact (rootBasis hF).sum_repr (AdjoinRoot.mk F V)

/-- Basis expansion transported into a product modulus, upper part: for any `V`,
`(V·H mod F·H)` is the `X^t·H`-combination with `V`'s coordinates mod `F`. -/
theorem mk_mul_expand {F : Polynomial S} (hF : F.Monic) (H V : Polynomial S) :
    AdjoinRoot.mk (F * H) (V * H)
      = ∑ t, ((rootBasis hF).repr (AdjoinRoot.mk F V) t)
          • AdjoinRoot.mk (F * H) (Polynomial.X ^ (t : ℕ) * H) := by
  obtain ⟨u, hu⟩ := AdjoinRoot.mk_eq_mk.mp (mk_sum_repr hF V)
  have h2 : AdjoinRoot.mk (F * H)
      ((∑ t, Polynomial.C ((rootBasis hF).repr (AdjoinRoot.mk F V) t)
        * Polynomial.X ^ (t : ℕ)) * H)
      = AdjoinRoot.mk (F * H) (V * H) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨u, by rw [← sub_mul, hu]; ring⟩
  rw [← h2, Finset.sum_mul,
    show (∑ t, Polynomial.C ((rootBasis hF).repr (AdjoinRoot.mk F V) t)
        * Polynomial.X ^ (t : ℕ) * H)
      = ∑ t, Polynomial.C ((rootBasis hF).repr (AdjoinRoot.mk F V) t)
        * (Polynomial.X ^ (t : ℕ) * H) from
      Finset.sum_congr rfl fun t _ => by ring,
    mk_sum]

/-- Basis expansion transported into a product modulus, lower part. -/
theorem mk_expand_lower {H : Polynomial S} (hH : H.Monic) (F Q : Polynomial S) :
    ∃ V : Polynomial S, AdjoinRoot.mk (F * H) Q
      = ∑ j, ((rootBasis hH).repr (AdjoinRoot.mk H Q) j)
          • AdjoinRoot.mk (F * H) (Polynomial.X ^ (j : ℕ))
        + AdjoinRoot.mk (F * H) (V * H) := by
  obtain ⟨V, hV⟩ := AdjoinRoot.mk_eq_mk.mp (mk_sum_repr hH Q)
  refine ⟨-V, ?_⟩
  have hQ : Q = (∑ j, Polynomial.C ((rootBasis hH).repr (AdjoinRoot.mk H Q) j)
      * Polynomial.X ^ (j : ℕ)) + (-V) * H := by
    linear_combination -hV
  conv_lhs => rw [hQ]
  rw [map_add, mk_sum]

theorem natDegree_sum_C_X_pow_le (n : ℕ) (c : Fin n → S) :
    (∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
  have hi := i.isLt
  omega

theorem coeff_sum_C_X_pow {n : ℕ} (c : Fin n → S) (t : Fin n) :
    (∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).coeff (t : ℕ) = c t := by
  classical
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single t]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hit
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg fun h => hit (Fin.ext h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- The adapted family `{X^i·H} ⊔ {X^j}` is linearly independent in `S[X]/(F·H)`. -/
theorem linearIndependent_adapted {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic)
    (ha : 0 < F.natDegree) (hb : 0 < H.natDegree) :
    LinearIndependent S (Sum.elim
      (fun i : Fin F.natDegree => AdjoinRoot.mk (F * H) (Polynomial.X ^ (i : ℕ) * H))
      (fun j : Fin H.natDegree => AdjoinRoot.mk (F * H) (Polynomial.X ^ (j : ℕ)))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  rw [← mk_sum (F * H) (fun i => g (Sum.inl i)) (fun i => Polynomial.X ^ (i : ℕ) * H),
    ← mk_sum (F * H) (fun j => g (Sum.inr j)) (fun j => Polynomial.X ^ (j : ℕ)),
    ← map_add] at hg
  have hdvd := AdjoinRoot.mk_eq_zero.mp hg
  rw [show (∑ i, Polynomial.C (g (Sum.inl i)) * (Polynomial.X ^ (i : ℕ) * H))
      = (∑ i, Polynomial.C (g (Sum.inl i)) * Polynomial.X ^ (i : ℕ)) * H from by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring] at hdvd
  set PC := ∑ i, Polynomial.C (g (Sum.inl i)) * Polynomial.X ^ (i : ℕ) with hPCdef
  set PD := ∑ j, Polynomial.C (g (Sum.inr j)) * Polynomial.X ^ (j : ℕ) with hPDdef
  have hPCdeg : PC.natDegree ≤ F.natDegree - 1 := by
    rw [hPCdef]; exact natDegree_sum_C_X_pow_le _ _
  have hPDdeg : PD.natDegree ≤ H.natDegree - 1 := by
    rw [hPDdef]; exact natDegree_sum_C_X_pow_le _ _
  have hW0 : PC * H + PD = 0 := by
    by_contra hne
    have hge : (F * H).natDegree ≤ (PC * H + PD).natDegree := by
      obtain ⟨u, hu⟩ := hdvd
      have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hne hu
      have heq : (PC * H + PD).natDegree = (F * H).natDegree + u.natDegree := by
        rw [hu]
        exact Polynomial.natDegree_mul' (by
          rw [(hF.mul hH).leadingCoeff, one_mul]
          exact Polynomial.leadingCoeff_ne_zero.mpr hu0)
      omega
    have hFH : (F * H).natDegree = F.natDegree + H.natDegree := hF.natDegree_mul hH
    have h1 : (PC * H).natDegree ≤ PC.natDegree + H.natDegree :=
      Polynomial.natDegree_mul_le
    have h4 : (PC * H + PD).natDegree ≤ F.natDegree - 1 + H.natDegree := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) (by omega))
    omega
  have hPC0 : PC = 0 := by
    by_contra hne
    have hPD : PD = -(PC * H) := by linear_combination hW0
    have hdeg1 : (PC * H).natDegree = PC.natDegree + H.natDegree :=
      Polynomial.natDegree_mul' (by
        rw [hH.leadingCoeff, mul_one]
        exact Polynomial.leadingCoeff_ne_zero.mpr hne)
    have hPDdeg2 : PD.natDegree = PC.natDegree + H.natDegree := by
      rw [hPD, Polynomial.natDegree_neg, hdeg1]
    omega
  have hPD0 : PD = 0 := by
    have h := hW0
    rw [hPC0, zero_mul, zero_add] at h
    exact h
  intro k
  rcases k with i | j
  · have h : PC.coeff (i : ℕ) = 0 := by rw [hPC0]; exact Polynomial.coeff_zero _
    rw [hPCdef, coeff_sum_C_X_pow] at h
    exact h
  · have h : PD.coeff (j : ℕ) = 0 := by rw [hPD0]; exact Polynomial.coeff_zero _
    rw [hPDdef, coeff_sum_C_X_pow] at h
    exact h

/-- The adapted family spans `S[X]/(F·H)`. -/
theorem span_adapted {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic) :
    ⊤ ≤ Submodule.span S (Set.range (Sum.elim
      (fun i : Fin F.natDegree => AdjoinRoot.mk (F * H) (Polynomial.X ^ (i : ℕ) * H))
      (fun j : Fin H.natDegree => AdjoinRoot.mk (F * H) (Polynomial.X ^ (j : ℕ))))) := by
  rintro z -
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨V, hV⟩ := mk_expand_lower hH F Q
  rw [hV]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Sum.inr j, rfl⟩)) ?_
  rw [mk_mul_expand hF H V]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Sum.inl t, rfl⟩)

/-- **The adapted basis** of `S[X]/(F·H)`: `{X^i·H} ⊔ {X^j}`. -/
noncomputable def adaptedBasis {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic)
    (ha : 0 < F.natDegree) (hb : 0 < H.natDegree) :
    Module.Basis (Fin F.natDegree ⊕ Fin H.natDegree) S (AdjoinRoot (F * H)) :=
  Module.Basis.mk (linearIndependent_adapted hF hH ha hb) (span_adapted hF hH)

theorem adaptedBasis_inl {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic)
    (ha : 0 < F.natDegree) (hb : 0 < H.natDegree) (i : Fin F.natDegree) :
    adaptedBasis hF hH ha hb (Sum.inl i)
      = AdjoinRoot.mk (F * H) (Polynomial.X ^ (i : ℕ) * H) := by
  rw [adaptedBasis, Module.Basis.mk_apply]
  rfl

theorem adaptedBasis_inr {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic)
    (ha : 0 < F.natDegree) (hb : 0 < H.natDegree) (j : Fin H.natDegree) :
    adaptedBasis hF hH ha hb (Sum.inr j)
      = AdjoinRoot.mk (F * H) (Polynomial.X ^ (j : ℕ)) := by
  rw [adaptedBasis, Module.Basis.mk_apply]
  rfl

/-- Coordinates of an explicit combination in any basis. -/
theorem repr_basis_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module S M] (b : Module.Basis ι S M) (w : ι → S) (r : ι) :
    b.repr (∑ k, w k • b k) r = w r := by
  rw [map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ r]
  simp

/-- ★ **Norm multiplicativity in the modulus.**  No coprimality hypothesis: the adapted
basis `{X^i·H} ⊔ {X^j}` exhibits the multiplication matrix as block triangular. -/
theorem norm_mk_mul {F H : Polynomial S} (hF : F.Monic) (hH : H.Monic)
    (P : Polynomial S) :
    Algebra.norm S (AdjoinRoot.mk (F * H) P)
      = Algebra.norm S (AdjoinRoot.mk F P) * Algebra.norm S (AdjoinRoot.mk H P) := by
  classical
  rcases Nat.eq_zero_or_pos F.natDegree with ha0 | ha
  · have hF1 : F = 1 := hF.natDegree_eq_zero.mp ha0
    subst hF1
    rw [one_mul, norm_mk_one, one_mul]
  rcases Nat.eq_zero_or_pos H.natDegree with hb0 | hb
  · have hH1 : H = 1 := hH.natDegree_eq_zero.mp hb0
    subst hH1
    rw [mul_one, norm_mk_one, mul_one]
  -- the two column identities in the adapted basis
  have hcol1 : ∀ i : Fin F.natDegree,
      AdjoinRoot.mk (F * H) P * adaptedBasis hF hH ha hb (Sum.inl i)
        = ∑ k, (Sum.elim
            (fun t => Algebra.leftMulMatrix (rootBasis hF) (AdjoinRoot.mk F P) t i)
            (fun _ => (0 : S))) k • adaptedBasis hF hH ha hb k := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero, add_zero]
    rw [adaptedBasis_inl hF hH ha hb i, ← map_mul,
      show P * (Polynomial.X ^ (i : ℕ) * H) = (P * Polynomial.X ^ (i : ℕ)) * H from by ring,
      mk_mul_expand hF H (P * Polynomial.X ^ (i : ℕ))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [adaptedBasis_inl hF hH ha hb t]
    congr 1
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    congr 2
    rw [rootBasis_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul]
  have hcol2 : ∀ j : Fin H.natDegree, ∃ u : Fin F.natDegree → S,
      AdjoinRoot.mk (F * H) P * adaptedBasis hF hH ha hb (Sum.inr j)
        = ∑ k, (Sum.elim u
            (fun j' => Algebra.leftMulMatrix (rootBasis hH) (AdjoinRoot.mk H P) j' j)) k
              • adaptedBasis hF hH ha hb k := by
    intro j
    obtain ⟨V, hV⟩ := mk_expand_lower hH F (P * Polynomial.X ^ (j : ℕ))
    refine ⟨fun t => (rootBasis hF).repr (AdjoinRoot.mk F V) t, ?_⟩
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [adaptedBasis_inr hF hH ha hb j, ← map_mul, hV, mk_mul_expand hF H V, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [adaptedBasis_inl hF hH ha hb t]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [adaptedBasis_inr hF hH ha hb j']
      congr 1
      rw [Algebra.leftMulMatrix_eq_repr_mul]
      congr 2
      rw [rootBasis_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul]
  -- the three entry facts
  have hM11 : ∀ (t i : Fin F.natDegree),
      Algebra.leftMulMatrix (adaptedBasis hF hH ha hb) (AdjoinRoot.mk (F * H) P)
          (Sum.inl t) (Sum.inl i)
        = Algebra.leftMulMatrix (rootBasis hF) (AdjoinRoot.mk F P) t i := by
    intro t i
    rw [Algebra.leftMulMatrix_eq_repr_mul, hcol1 i, repr_basis_sum]
    rfl
  have hM21 : ∀ (j : Fin H.natDegree) (i : Fin F.natDegree),
      Algebra.leftMulMatrix (adaptedBasis hF hH ha hb) (AdjoinRoot.mk (F * H) P)
          (Sum.inr j) (Sum.inl i) = 0 := by
    intro j i
    rw [Algebra.leftMulMatrix_eq_repr_mul, hcol1 i, repr_basis_sum]
    rfl
  have hM22 : ∀ (j' j : Fin H.natDegree),
      Algebra.leftMulMatrix (adaptedBasis hF hH ha hb) (AdjoinRoot.mk (F * H) P)
          (Sum.inr j') (Sum.inr j)
        = Algebra.leftMulMatrix (rootBasis hH) (AdjoinRoot.mk H P) j' j := by
    intro j' j
    obtain ⟨u, hu⟩ := hcol2 j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hu, repr_basis_sum]
    rfl
  -- block triangularity and the determinant
  have hblock : Algebra.leftMulMatrix (adaptedBasis hF hH ha hb) (AdjoinRoot.mk (F * H) P)
      = Matrix.fromBlocks
          (Algebra.leftMulMatrix (rootBasis hF) (AdjoinRoot.mk F P))
          (Matrix.of fun t j => Algebra.leftMulMatrix (adaptedBasis hF hH ha hb)
            (AdjoinRoot.mk (F * H) P) (Sum.inl t) (Sum.inr j))
          0
          (Algebra.leftMulMatrix (rootBasis hH) (AdjoinRoot.mk H P)) := by
    ext r k
    rcases r with t | j <;> rcases k with i | j'
    · rw [Matrix.fromBlocks_apply₁₁, hM11]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [Matrix.fromBlocks_apply₂₁, hM21, Matrix.zero_apply]
    · rw [Matrix.fromBlocks_apply₂₂, hM22]
  rw [Algebra.norm_eq_matrix_det (adaptedBasis hF hH ha hb),
    Algebra.norm_eq_matrix_det (rootBasis hF), Algebra.norm_eq_matrix_det (rootBasis hH),
    hblock, Matrix.det_fromBlocks_zero₂₁]

/-- The `Finset`-product form. -/
theorem norm_mk_prod {ι : Type*} (s : Finset ι) (Fs : ι → Polynomial S)
    (hmon : ∀ i ∈ s, (Fs i).Monic) (P : Polynomial S) :
    Algebra.norm S (AdjoinRoot.mk (∏ i ∈ s, Fs i) P)
      = ∏ i ∈ s, Algebra.norm S (AdjoinRoot.mk (Fs i) P) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, norm_mk_one P]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      norm_mk_mul (hmon a (Finset.mem_insert_self a s))
        (Polynomial.monic_prod_of_monic _ _ fun i hi => hmon i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hmon i (Finset.mem_insert_of_mem hi)]

end NormModulus

/-! ## §2 — valuation transport -/

section AddValTransport

theorem addVal_isUnit {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {u : A} (hu : IsUnit u) : IsDiscreteValuationRing.addVal A u = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu

/-- `addVal` is preserved by any ring map carrying one irreducible to an irreducible. -/
theorem addVal_map_of_irreducible {A B : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (ψ : A →+* B) {π : A} (hπ : Irreducible π) (hψπ : Irreducible (ψ π)) (z : A) :
    IsDiscreteValuationRing.addVal B (ψ z) = IsDiscreteValuationRing.addVal A z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hπ
  rw [map_mul, map_pow, AddValuation.map_mul, AddValuation.map_mul,
    AddValuation.map_pow, AddValuation.map_pow, addVal_isUnit u.isUnit,
    addVal_isUnit (u.isUnit.map ψ), IsDiscreteValuationRing.addVal_uniformizer hπ,
    IsDiscreteValuationRing.addVal_uniformizer hψπ]

theorem addVal_finset_prod {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {ι : Type*} (s : Finset ι) (g : ι → A) :
    IsDiscreteValuationRing.addVal A (∏ i ∈ s, g i)
      = ∑ i ∈ s, IsDiscreteValuationRing.addVal A (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

end AddValTransport

/-! ## §3 — comaximality by Nakayama, and CRT -/

section Comaximal

/-- **Residual coprimality lifts** over a local ring, one modulus monic: the quotient
`S[X]/(F, H)` is module-finite (via monic `F`) and `𝔪`-divisible (via the residual Bézout
relation), hence vanishes by Nakayama. -/
theorem isCoprime_of_isCoprime_map_residue {S : Type*} [CommRing S] [IsLocalRing S]
    {F H : Polynomial S} (hF : F.Monic)
    (hcop : IsCoprime (F.map (residue S)) (H.map (residue S))) :
    IsCoprime F H := by
  classical
  set J : Ideal (Polynomial S) := Ideal.span {F, H} with hJ
  suffices h1 : (1 : Polynomial S) ∈ J by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp h1
    exact ⟨u, v, huv⟩
  have hFJ : F ∈ J := Ideal.subset_span (by simp)
  have hHJ : H ∈ J := Ideal.subset_span (by simp)
  -- scalars act through `C` on the quotient
  have hsmul : ∀ (c : S) (p : Polynomial S),
      c • Ideal.Quotient.mk J p = Ideal.Quotient.mk J (Polynomial.C c * p) := by
    intro c p
    have h : Ideal.Quotient.mk J (c • p) = c • Ideal.Quotient.mk J p := by
      rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := S)]
      exact map_smul (Ideal.Quotient.mkₐ S J) c p
    rw [← Polynomial.smul_eq_C_mul, ← h]
  -- (i) the quotient is a finitely generated `S`-module (division by the monic `F`)
  have hFG : (⊤ : Submodule S (Polynomial S ⧸ J)).FG := by
    rw [Submodule.fg_def]
    refine ⟨(fun t : ℕ => Ideal.Quotient.mk J (Polynomial.X ^ t)) '' Set.Iio F.natDegree,
      (Set.finite_Iio _).image _, ?_⟩
    rw [eq_top_iff]
    rintro z -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hmod : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p %ₘ F) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hdiff : p - p %ₘ F = F * (p /ₘ F) := by
        have h := Polynomial.modByMonic_add_div p F
        linear_combination -h
      rw [hdiff]
      exact Ideal.mul_mem_right _ _ hFJ
    rw [hmod]
    rcases eq_or_ne (p %ₘ F) 0 with h0 | h0
    · rw [h0, map_zero]
      exact Submodule.zero_mem _
    have hlt : (p %ₘ F).natDegree < F.natDegree :=
      Polynomial.natDegree_lt_natDegree h0 (Polynomial.degree_modByMonic_lt p hF)
    rw [show p %ₘ F = ∑ i ∈ Finset.range F.natDegree,
        Polynomial.C ((p %ₘ F).coeff i) * Polynomial.X ^ i from by
      conv_lhs => rw [Polynomial.as_sum_range' _ _ hlt]
      exact Finset.sum_congr rfl fun i _ => (Polynomial.C_mul_X_pow_eq_monomial).symm]
    rw [map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_range.mp hi, rfl⟩)
  -- (ii) the quotient is `𝔪`-divisible (the residual Bézout relation lifts to `1 − E`)
  have hsmul_top : (⊤ : Submodule S (Polynomial S ⧸ J))
      ≤ (maximalIdeal S) • (⊤ : Submodule S (Polynomial S ⧸ J)) := by
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨A0, hA0⟩ := Polynomial.map_surjective _ residue_surjective a
    obtain ⟨B0, hB0⟩ := Polynomial.map_surjective _ residue_surjective b
    set E := 1 - (A0 * F + B0 * H) with hE
    have hEcoeff : ∀ i, E.coeff i ∈ maximalIdeal S := by
      intro i
      have hmapE : E.map (residue S) = 0 := by
        rw [hE, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_add,
          Polynomial.map_mul, Polynomial.map_mul, hA0, hB0, hab, sub_self]
      have hcz := congrArg (fun p => Polynomial.coeff p i) hmapE
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcz
      exact (residue_eq_zero_iff _).mp hcz
    have hone : Ideal.Quotient.mk J 1 = Ideal.Quotient.mk J E := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hdiff : (1 : Polynomial S) - E = A0 * F + B0 * H := by rw [hE]; ring
      rw [hdiff]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hFJ) (Ideal.mul_mem_left _ _ hHJ)
    rintro z -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p * E) := by
      calc Ideal.Quotient.mk J p
          = Ideal.Quotient.mk J p * Ideal.Quotient.mk J 1 := by rw [map_one, mul_one]
        _ = Ideal.Quotient.mk J p * Ideal.Quotient.mk J E := by rw [hone]
        _ = Ideal.Quotient.mk J (p * E) := by rw [← map_mul]
    rw [hz, show p * E = ∑ i ∈ Finset.range (E.natDegree + 1),
        Polynomial.C (E.coeff i) * (p * Polynomial.X ^ i) from by
      conv_lhs => rw [Polynomial.as_sum_range' E (E.natDegree + 1) (Nat.lt_succ_self _)]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]; ring]
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem_smul (hEcoeff i) Submodule.mem_top
  -- (iii) Nakayama
  have hjac : maximalIdeal S ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hbot : (⊤ : Submodule S (Polynomial S ⧸ J)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) ⊤ hFG hsmul_top hjac
  have h10 : Ideal.Quotient.mk J 1 = 0 := by
    have hm : Ideal.Quotient.mk J 1 ∈ (⊥ : Submodule S (Polynomial S ⧸ J)) :=
      hbot ▸ Submodule.mem_top
    simpa using hm
  exact Ideal.Quotient.eq_zero_iff_mem.mp h10

/-- Elementary CRT for finitely many pairwise-coprime moduli. -/
theorem exists_forall_dvd_sub {S : Type*} [CommRing S] {ι : Type*} (s : Finset ι)
    (mods tgts : ι → Polynomial S)
    (hpair : (↑s : Set ι).Pairwise fun i j => IsCoprime (mods i) (mods j)) :
    ∃ P : Polynomial S, ∀ i ∈ s, mods i ∣ P - tgts i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a t ha ih =>
    obtain ⟨P₀, hP₀⟩ := ih (hpair.mono (by
      rw [Finset.coe_insert]; exact Set.subset_insert _ _))
    have hcop : IsCoprime (mods a) (∏ i ∈ t, mods i) := by
      refine IsCoprime.prod_right fun i hi => ?_
      refine hpair ?_ ?_ ?_
      · rw [Finset.coe_insert]; exact Set.mem_insert _ _
      · rw [Finset.coe_insert]; exact Set.mem_insert_of_mem _ hi
      · rintro rfl; exact ha hi
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨tgts a * (v * ∏ i ∈ t, mods i) + P₀ * (u * mods a), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hit
    · exact ⟨(P₀ - tgts i) * u, by linear_combination (tgts i) * huv⟩
    · obtain ⟨w, hw⟩ := hP₀ i hit
      obtain ⟨w2, hw2⟩ := Finset.dvd_prod_of_mem mods hit
      exact ⟨tgts a * v * w2 + w * u * mods a - tgts i * v * w2, by
        linear_combination (tgts a * v - tgts i * v) * hw2 + (u * mods a) * hw
          + tgts i * huv⟩

end Comaximal

/-! ## §4 — the engine over the unramified extension -/

section Engine

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {φ : Polynomial O}
  [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
  [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
  [Finite (ResidueField (AdjoinRoot φ))]

/-- The conjugations preserve the valuation (they fix the base uniformizer). -/
theorem addVal_tau (hφ : IsKey φ) (β : ResidueField (AdjoinRoot φ)) (z : AdjoinRoot φ) :
    IsDiscreteValuationRing.addVal (AdjoinRoot φ) (tau hφ β z)
      = IsDiscreteValuationRing.addVal (AdjoinRoot φ) z := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' := irreducible_algebraMap_adjoinRoot hφ hπ
  have hτπ : Irreducible ((tau hφ β).toRingHom (algebraMap O (AdjoinRoot φ) π)) := by
    have hfix : (tau hφ β).toRingHom (algebraMap O (AdjoinRoot φ) π)
        = algebraMap O (AdjoinRoot φ) π := (tau hφ β).commutes π
    rw [hfix]; exact hπ'
  exact addVal_map_of_irreducible (tau hφ β).toRingHom hπ' hτπ z

/-- The base change preserves the valuation (unramifiedness: the base uniformizer stays
irreducible). -/
theorem addVal_algebraMap_adjoinRoot (hφ : IsKey φ) (z : O) :
    IsDiscreteValuationRing.addVal (AdjoinRoot φ) (algebraMap O (AdjoinRoot φ) z)
      = IsDiscreteValuationRing.addVal O z := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact addVal_map_of_irreducible (algebraMap O (AdjoinRoot φ)) hπ
    (irreducible_algebraMap_adjoinRoot hφ hπ) z

/-- The residual of a conjugate factor: `(X − β)^deg C` at the conjugating root. -/
theorem map_tau_map_residue_eq (hφ : IsKey φ) {β : ResidueField (AdjoinRoot φ)}
    (hβ : β ∈ keyRoots hφ) {C : Polynomial (AdjoinRoot φ)}
    (hCres : C.map (residue (AdjoinRoot φ))
      = (Polynomial.X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree) :
    (C.map (tau hφ β).toRingHom).map (residue (AdjoinRoot φ))
      = (Polynomial.X - Polynomial.C β) ^ C.natDegree := by
  rw [map_resTau_map_residue hφ, hCres, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, resTau_apply_of_mem hφ hβ]

/-- Distinct conjugate factors are comaximal (distinct residual roots + Nakayama). -/
theorem isCoprime_map_tau (hφ : IsKey φ) {β γ : ResidueField (AdjoinRoot φ)}
    (hβ : β ∈ keyRoots hφ) (hγ : γ ∈ keyRoots hφ) (hne : β ≠ γ)
    {C : Polynomial (AdjoinRoot φ)} (hCm : C.Monic)
    (hCres : C.map (residue (AdjoinRoot φ))
      = (Polynomial.X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree) :
    IsCoprime (C.map (tau hφ β).toRingHom) (C.map (tau hφ γ).toRingHom) := by
  refine isCoprime_of_isCoprime_map_residue (hCm.map _) ?_
  rw [map_tau_map_residue_eq hφ hβ hCres, map_tau_map_residue_eq hφ hγ hCres]
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hne))).pow

variable {C : Polynomial (AdjoinRoot φ)} {G : Polynomial O}

/-- ★ **(E1a) The conjugate norm factorization**: the base norm of any `P`, pushed into
the extension, is the product of the conjugates of the extension norm of `P`. -/
theorem algebraMap_norm_mk_eq (hφ : IsKey φ) (hCm : C.Monic) (hGm : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) (P : Polynomial O) :
    algebraMap O (AdjoinRoot φ) (Algebra.norm O (AdjoinRoot.mk G P))
      = ∏ β ∈ (keyRoots hφ).toFinset,
          tau hφ β (Algebra.norm (AdjoinRoot φ)
            (AdjoinRoot.mk C (P.map (algebraMap O (AdjoinRoot φ))))) := by
  classical
  rw [← norm_mk_map' (algebraMap O (AdjoinRoot φ)) hGm hGmap P, tauProd,
    norm_mk_prod _ _ fun β _ => hCm.map _]
  refine Finset.prod_congr rfl fun β hβ => ?_
  conv_lhs => rw [← map_tau_map_algebraMap hφ β P]
  exact norm_mk_map' (tau hφ β).toRingHom hCm rfl (P.map (algebraMap O (AdjoinRoot φ)))

/-- ★★ **(E1b) The master valuation identity.** -/
theorem addVal_norm_mk_eq (hφ : IsKey φ) (hCm : C.Monic) (hGm : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) (P : Polynomial O) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (AdjoinRoot.mk G P))
      = φ.natDegree • IsDiscreteValuationRing.addVal (AdjoinRoot φ)
          (Algebra.norm (AdjoinRoot φ)
            (AdjoinRoot.mk C (P.map (algebraMap O (AdjoinRoot φ))))) := by
  classical
  rw [← addVal_algebraMap_adjoinRoot hφ, algebraMap_norm_mk_eq hφ hCm hGm hGmap P,
    addVal_finset_prod,
    Finset.sum_congr rfl fun β _ => addVal_tau hφ β _,
    Finset.sum_const]
  congr 1
  rw [Multiset.card_toFinset, Multiset.dedup_eq_self.mpr (nodup_keyRoots hφ),
    card_keyRoots hφ]

/-- **LEG A**: every norm valuation of `G` is `δ` times a norm valuation of `C`. -/
theorem normValues_descent (hφ : IsKey φ) (hCm : C.Monic) (hd : 0 < C.natDegree)
    (hGm : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) :
    ∀ k ∈ normValues G, ∃ v ∈ normValues C, k = φ.natDegree * v := by
  classical
  rintro k ⟨hkpos, x, -, hxval⟩
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
  haveI : Module.Finite (AdjoinRoot φ) (AdjoinRoot C) := (AdjoinRoot.powerBasis' hCm).finite
  haveI : Module.Free (AdjoinRoot φ) (AdjoinRoot C) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hCm).basis
  haveI : Nontrivial (AdjoinRoot C) := by
    have hdegne : C.degree ≠ 0 := ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 hd)
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hdegne).nontrivial
  set y := AdjoinRoot.mk C (P.map (algebraMap O (AdjoinRoot φ))) with hy
  have hE1 := addVal_norm_mk_eq hφ hCm hGm hGmap P
  rw [hxval, ← hy] at hE1
  have htop : IsDiscreteValuationRing.addVal (AdjoinRoot φ)
      (Algebra.norm (AdjoinRoot φ) y) ≠ ⊤ := by
    intro h
    rw [h, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hφ.pos.ne')] at hE1
    exact (ENat.coe_ne_top k) hE1
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp htop
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero] at htop
    exact htop rfl
  rw [← hv, nsmul_eq_mul] at hE1
  have hk : k = φ.natDegree * v := by exact_mod_cast hE1
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · rw [Nat.mul_zero] at hk; omega
    · exact h
  exact ⟨v, ⟨hvpos, y, hy0, hv.symm⟩, hk⟩

/-- **LEG B (the witness)**: `δ` times any norm valuation of `C` is a norm valuation of
`G` — the CRT conjugate tuple, descended by the invariants theorem. -/
theorem normValues_ascent (hφ : IsKey φ) (hCm : C.Monic) (hd : 0 < C.natDegree)
    (hCres : C.map (residue (AdjoinRoot φ))
      = (Polynomial.X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree)
    (hGm : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) :
    ∀ v ∈ normValues C, φ.natDegree * v ∈ normValues G := by
  classical
  rintro v ⟨hvpos, y, hy0, hyval⟩
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective y
  -- the conjugate factors are pairwise comaximal
  have hpair : ((keyRoots hφ).toFinset : Set (ResidueField (AdjoinRoot φ))).Pairwise
      fun β γ => IsCoprime (C.map (tau hφ β).toRingHom) (C.map (tau hφ γ).toRingHom) := by
    intro β hβ γ hγ hne
    exact isCoprime_map_tau hφ (Multiset.mem_toFinset.mp (Finset.mem_coe.mp hβ))
      (Multiset.mem_toFinset.mp (Finset.mem_coe.mp hγ)) hne hCm hCres
  -- the CRT solution and its reduced representative
  obtain ⟨P', hP'⟩ := exists_forall_dvd_sub (keyRoots hφ).toFinset
    (fun β => C.map (tau hφ β).toRingHom) (fun β => Q.map (tau hφ β).toRingHom) hpair
  have hTm : (tauProd hφ C).Monic := tauProd_monic hφ hCm
  set R0 := P' %ₘ tauProd hφ C with hR0def
  have hR0cong : ∀ β ∈ (keyRoots hφ).toFinset,
      (C.map (tau hφ β).toRingHom) ∣ (R0 - Q.map (tau hφ β).toRingHom) := by
    intro β hβ
    have h2 : (C.map (tau hφ β).toRingHom) ∣ (R0 - P') := by
      have hdvd : tauProd hφ C ∣ (R0 - P') := by
        have h := Polynomial.modByMonic_add_div P' (tauProd hφ C)
        exact ⟨-(P' /ₘ tauProd hφ C), by rw [hR0def]; linear_combination h⟩
      refine dvd_trans ?_ hdvd
      rw [tauProd]
      exact Finset.dvd_prod_of_mem _ hβ
    have h5 := dvd_add h2 (hP' β hβ)
    rw [sub_add_sub_cancel] at h5
    exact h5
  -- the reduced representative is `τ`-invariant AS A POLYNOMIAL
  have hinv : ∀ γ ∈ keyRoots hφ, R0.map (tau hφ γ).toRingHom = R0 := by
    intro γ hγ
    have hdiff : tauProd hφ C ∣ (R0.map (tau hφ γ).toRingHom - R0) := by
      rw [tauProd]
      refine Finset.prod_dvd_of_coprime hpair fun β hβ => ?_
      obtain ⟨η, hη, hηeq⟩ := exists_resTau_eq hφ γ (Multiset.mem_toFinset.mp hβ)
      have h1 : (C.map (tau hφ η).toRingHom) ∣ (R0 - Q.map (tau hφ η).toRingHom) :=
        hR0cong η (Multiset.mem_toFinset.mpr hη)
      have h2 := Polynomial.map_dvd (tau hφ γ).toRingHom h1
      have hcompC : (C.map (tau hφ η).toRingHom).map (tau hφ γ).toRingHom
          = C.map (tau hφ β).toRingHom := by
        rw [Polynomial.map_map]
        congr 1
        rw [← hηeq]
        exact congrArg AlgHom.toRingHom (tau_comp hφ hη)
      have hcompQ : (Q.map (tau hφ η).toRingHom).map (tau hφ γ).toRingHom
          = Q.map (tau hφ β).toRingHom := by
        rw [Polynomial.map_map]
        congr 1
        rw [← hηeq]
        exact congrArg AlgHom.toRingHom (tau_comp hφ hη)
      rw [Polynomial.map_sub, hcompC, hcompQ] at h2
      have h4 := dvd_sub h2 (hR0cong β hβ)
      rw [sub_sub_sub_cancel_right] at h4
      exact h4
    rcases eq_or_ne (R0.map (tau hφ γ).toRingHom - R0) 0 with h0 | h0
    · exact sub_eq_zero.mp h0
    exfalso
    have hTdeg := Polynomial.natDegree_le_of_dvd hdiff h0
    have hTdegpos : 0 < (tauProd hφ C).natDegree := by
      rw [tauProd_natDegree hφ hCm]
      exact Nat.mul_pos hφ.pos hd
    have hR0deg : R0.natDegree < (tauProd hφ C).natDegree := by
      rcases eq_or_ne R0 0 with hR00 | hR00
      · rw [hR00, Polynomial.natDegree_zero]; exact hTdegpos
      · exact Polynomial.natDegree_lt_natDegree hR00
          (Polynomial.degree_modByMonic_lt P' hTm)
    have hmapdeg : (R0.map (tau hφ γ).toRingHom).natDegree ≤ R0.natDegree :=
      Polynomial.natDegree_map_le
    have hsub : (R0.map (tau hφ γ).toRingHom - R0).natDegree
        < (tauProd hφ C).natDegree := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
      exact max_lt (lt_of_le_of_lt hmapdeg hR0deg) hR0deg
    omega
  -- descent by the invariants theorem
  have hlift : R0 ∈ Polynomial.lifts (algebraMap O (AdjoinRoot φ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine exists_algebraMap_eq_of_forall_tau hφ fun β hβ => ?_
    have h := congrArg (fun p => Polynomial.coeff p i) (hinv β hβ)
    simpa [Polynomial.coeff_map] using h
  obtain ⟨P, hPmap⟩ := (Polynomial.mem_lifts _).mp hlift
  -- the reduced representative recovers `y` at the identity conjugation
  have hyR : AdjoinRoot.mk C R0 = AdjoinRoot.mk C Q := by
    rw [AdjoinRoot.mk_eq_mk]
    have hθ := hR0cong (residue (AdjoinRoot φ) (AdjoinRoot.root φ))
      (Multiset.mem_toFinset.mpr (residue_root_mem_keyRoots hφ))
    rw [tau_residue_root hφ] at hθ
    simpa using hθ
  -- the valuation of the descended witness
  have hE1 := addVal_norm_mk_eq hφ hCm hGm hGmap P
  rw [hPmap, hyR, hyval] at hE1
  -- instances for `norm_zero` over the base
  have hGdeg : G.natDegree = φ.natDegree * C.natDegree := by
    have h1 := hGm.natDegree_map (algebraMap O (AdjoinRoot φ))
    rw [hGmap, tauProd_natDegree hφ hCm] at h1
    exact h1.symm
  have hGpos : 0 < G.natDegree := by
    rw [hGdeg]; exact Nat.mul_pos hφ.pos hd
  haveI : Module.Finite O (AdjoinRoot G) := (AdjoinRoot.powerBasis' hGm).finite
  haveI : Module.Free O (AdjoinRoot G) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hGm).basis
  haveI : Nontrivial (AdjoinRoot G) := by
    have hdegne : G.degree ≠ 0 := ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 hGpos)
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hdegne).nontrivial
  refine ⟨Nat.mul_pos hφ.pos hvpos, AdjoinRoot.mk G P, ?_, ?_⟩
  · intro h0
    rw [h0, Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul] at hE1
    have htop : ((φ.natDegree * v : ℕ) : ℕ∞) = ⊤ := by
      rw [Nat.cast_mul]; exact hE1.symm
    exact (ENat.coe_ne_top _) htop
  · rw [hE1, nsmul_eq_mul]
    exact (Nat.cast_mul _ _).symm

/-- Every common divisor of the norm valuations divides the `sSup`-gcd (B.52's lcm
trick, packaged). -/
theorem dvd_inertiaDegOf_of_mem_normDivisors {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {g : Polynomial A} (hne : (normValues g).Nonempty)
    {k : ℕ} (hk : k ∈ normDivisors g) : k ∣ inertiaDegOf g := by
  have hIpos : 0 < inertiaDegOf g := inertiaDegOf_pos hne
  have hI := inertiaDegOf_mem_normDivisors hne
  have hlcmpos : 0 < Nat.lcm k (inertiaDegOf g) := Nat.lcm_pos hk.1 hIpos
  have hlcm : Nat.lcm k (inertiaDegOf g) ∈ normDivisors g :=
    ⟨hlcmpos, fun x hx => Nat.lcm_dvd (hk.2 x hx) (hI.2 x hx)⟩
  have heq : Nat.lcm k (inertiaDegOf g) = inertiaDegOf g :=
    le_antisymm (le_inertiaDegOf hne hlcm)
      (Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_right _ _))
  exact heq ▸ Nat.dvd_lcm_left k (inertiaDegOf g)

/-- ★★★ **THE INERTIA SCALING** at a fixed key. -/
theorem inertiaDegOf_descent (hφ : IsKey φ) (hCm : C.Monic) (hCirr : Irreducible C)
    (hCres : C.map (residue (AdjoinRoot φ))
      = (Polynomial.X - Polynomial.C (residue (AdjoinRoot φ) (AdjoinRoot.root φ))) ^ C.natDegree)
    (hGm : G.Monic)
    (hGmap : G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C) :
    inertiaDegOf G = φ.natDegree * inertiaDegOf C := by
  classical
  have hd : 0 < C.natDegree := by
    rcases Nat.eq_zero_or_pos C.natDegree with h0 | h0
    · exact absurd ((hCm.natDegree_eq_zero).mp h0 ▸ isUnit_one) hCirr.not_isUnit
    · exact h0
  have hGdeg : G.natDegree = φ.natDegree * C.natDegree := by
    have h1 := hGm.natDegree_map (algebraMap O (AdjoinRoot φ))
    rw [hGmap, tauProd_natDegree hφ hCm] at h1
    exact h1.symm
  have hGpos : 0 < G.natDegree := by
    rw [hGdeg]; exact Nat.mul_pos hφ.pos hd
  have hneC : (normValues C).Nonempty := normValues_nonempty hCm hd
  have hneG : (normValues G).Nonempty := normValues_nonempty hGm hGpos
  have hfCpos : 0 < inertiaDegOf C := inertiaDegOf_pos hneC
  have hfGpos : 0 < inertiaDegOf G := inertiaDegOf_pos hneG
  -- Direction 1: `δ·f_C` is a common divisor of `normValues G`, hence divides `f_G`
  have hmem1 : φ.natDegree * inertiaDegOf C ∈ normDivisors G := by
    refine ⟨Nat.mul_pos hφ.pos hfCpos, fun k hk => ?_⟩
    obtain ⟨v, hv, rfl⟩ := normValues_descent hφ hCm hd hGm hGmap k hk
    exact Nat.mul_dvd_mul_left _ (inertiaDegOf_dvd hneC hv)
  have hdir1 : φ.natDegree * inertiaDegOf C ∣ inertiaDegOf G :=
    dvd_inertiaDegOf_of_mem_normDivisors hneG hmem1
  -- Direction 2: `f_G ∣ δ·v` for every `v`, hence `f_G ∣ δ·f_C` after cancelling the gcd
  have hdir2 : inertiaDegOf G ∣ φ.natDegree * inertiaDegOf C := by
    have hdvdall : ∀ v ∈ normValues C, inertiaDegOf G ∣ φ.natDegree * v := fun v hv =>
      inertiaDegOf_dvd hneG (normValues_ascent hφ hCm hd hCres hGm hGmap v hv)
    set d0 := Nat.gcd (inertiaDegOf G) φ.natDegree with hd0
    have hd0pos : 0 < d0 := Nat.gcd_pos_of_pos_left _ hfGpos
    have hgl : d0 ∣ inertiaDegOf G := Nat.gcd_dvd_left _ _
    have hgr : d0 ∣ φ.natDegree := Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime (inertiaDegOf G / d0) (φ.natDegree / d0) :=
      Nat.coprime_div_gcd_div_gcd hd0pos
    have hk'dvd : ∀ v ∈ normValues C, (inertiaDegOf G / d0) ∣ v := by
      intro v hv
      have h3 : d0 * (inertiaDegOf G / d0) ∣ d0 * ((φ.natDegree / d0) * v) := by
        rw [Nat.mul_div_cancel' hgl, ← mul_assoc, Nat.mul_div_cancel' hgr]
        exact hdvdall v hv
      exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hd0pos).mp h3)
    have hk'mem : inertiaDegOf G / d0 ∈ normDivisors C :=
      ⟨Nat.div_pos (Nat.le_of_dvd hfGpos hgl) hd0pos, hk'dvd⟩
    obtain ⟨w, hw⟩ := dvd_inertiaDegOf_of_mem_normDivisors hneC hk'mem
    refine ⟨(φ.natDegree / d0) * w, ?_⟩
    calc φ.natDegree * inertiaDegOf C
        = φ.natDegree * ((inertiaDegOf G / d0) * w) := by rw [← hw]
      _ = (d0 * (φ.natDegree / d0)) * ((inertiaDegOf G / d0) * w) := by
          rw [Nat.mul_div_cancel' hgr]
      _ = (d0 * (inertiaDegOf G / d0)) * ((φ.natDegree / d0) * w) := by ring
      _ = inertiaDegOf G * ((φ.natDegree / d0) * w) := by
          rw [Nat.mul_div_cancel' hgl]
  exact Nat.dvd_antisymm hdir2 hdir1

end Engine

/-! ## §5 — ★★★ the leg, uniformly in `δ` -/

/-- ★★★ **`InertiaScaling δ` holds for EVERY `δ`** — the one remaining leg of UBC's
block correspondence, closed. -/
theorem inertiaScaling_all (δ : ℕ) : InertiaScaling δ := by
  intro O _ _ _ _ _ φ hφ hdeg
  letI i1 : IsDomain (AdjoinRoot φ) := keyIsDomain hφ
  letI i2 : IsDiscreteValuationRing (AdjoinRoot φ) := adjoinRoot_isDVR hφ
  letI i3 : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  letI i4 : Finite (ResidueField (AdjoinRoot φ)) := adjoinRoot_finite_residueField hφ
  subst hdeg
  intro C G hCm hCirr hCres hGm hGmap
  exact inertiaDegOf_descent hφ hCm hCirr hCres hGm hGmap

/-! ## §6 — ★★★ the chain fired: the count law, the bridge, the census front -/

/-- ★★★ **The type-descent law, unconditionally, for all `δ, e`.** -/
theorem blockTypeDescent_all (δ e : ℕ) : BlockTypeDescent δ e :=
  blockTypeDescent_of_inertiaScaling (inertiaScaling_all δ)

/-- ★★★ **The count law `UnramifiedBlockCount δ e`, unconditionally, for all `δ, e`.** -/
theorem unramifiedBlockCount_all (δ e : ℕ) : UnramifiedBlockCount δ e :=
  unramifiedBlockCount_of_inertiaScaling (inertiaScaling_all δ) e

/-- ★★★ **The bridge `UnramifiedBlockBridge δ e`, unconditionally, for all `δ ≥ 1, e`.** -/
theorem unramifiedBlockBridge_all {δ : ℕ} (hδ : 1 ≤ δ) (e : ℕ) :
    UnramifiedBlockBridge δ e :=
  unramifiedBlockBridge_of_inertiaScaling hδ (inertiaScaling_all δ) e

/-- ★★★ **The census front WITHOUT the bridge family** (IFCG29 §8's shape, its
`InertiaScaling` hypothesis discharged): the all-degree decided slice rests on the
remainder laws alone. -/
theorem decidedSliceAt_all_of_remainder
    (hR : ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k →
        Uniformity.Density.IFCG14.DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Uniformity.Density.IFCG14.Witnessed e σ →
        Uniformity.Density.IFCG24.ConeRemainderLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_remainder_inertiaScaling hR (fun δ _ => inertiaScaling_all δ)

/-- ★★★ **The census front through IFCG31, WITHOUT the bridge family**: the all-degree
decided slice rests on exactly the remainder laws at `e ≥ 5` and the even-ramification
`e = 4` laws.  (Inherits IFCG31's signed B.42 cite.) -/
theorem decidedSliceAt_all_of_remainder5_even4
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k →
        Uniformity.Density.IFCG14.DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Uniformity.Density.IFCG14.Witnessed e σ →
        Uniformity.Density.IFCG24.ConeRemainderLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Uniformity.Density.IFCG14.Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → Uniformity.Density.IFCG24.ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG31.decidedSliceAt_all_of_remainder5_even4_bridge hR hR4
    (fun _ e h2δ _ => unramifiedBlockBridge_all (le_trans one_le_two h2δ) e)

end Uniformity.Density.IFCG32

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` for
everything except the LAST line, which inherits IFCG31's signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization`. -/

#print axioms Uniformity.Density.IFCG32.norm_mk_map'
#print axioms Uniformity.Density.IFCG32.norm_mk_mul
#print axioms Uniformity.Density.IFCG32.isCoprime_of_isCoprime_map_residue
#print axioms Uniformity.Density.IFCG32.exists_forall_dvd_sub
#print axioms Uniformity.Density.IFCG32.addVal_norm_mk_eq
#print axioms Uniformity.Density.IFCG32.normValues_descent
#print axioms Uniformity.Density.IFCG32.normValues_ascent
#print axioms Uniformity.Density.IFCG32.inertiaDegOf_descent
#print axioms Uniformity.Density.IFCG32.inertiaScaling_all
#print axioms Uniformity.Density.IFCG32.blockTypeDescent_all
#print axioms Uniformity.Density.IFCG32.unramifiedBlockCount_all
#print axioms Uniformity.Density.IFCG32.unramifiedBlockBridge_all
#print axioms Uniformity.Density.IFCG32.decidedSliceAt_all_of_remainder
#print axioms Uniformity.Density.IFCG32.decidedSliceAt_all_of_remainder5_even4
