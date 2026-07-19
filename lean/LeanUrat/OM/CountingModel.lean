/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.LevelNCount
import LeanUrat.OM.Classifier

/-!
# F1 — CountingModel: the normalized finite-counting model over the `ZMod(p^N)` tower

The level-`N` box `monicBox(p,N,n)` of monic degree-`n` polynomials over `O_K/p^N = ZMod(p^N)`
(unramified core `K = ℚ_p`) has cardinality `(p^N)^n = q^{nN}` (M1.`card_monicBox`). The deliverable
of this layer is the level-tower reduction `monicBox(p,N+1,n) ↠ monicBox(p,N,n)`, its per-coordinate
`p`-to-1 (total `p^n`-to-1) fiber count, and cylinder-set consistency (a level-`N`-decided set has a
stable normalized count `count / q^{nM}` for all `M ≥ N`).

Everything is built on `M1.monicBox`/`card_monicBox` and `M8.coordinateResidue_card_factor`, with NO
measure theory: counts are genuine `Nat.card`. The one conceptual import this layer does NOT prove (it
consumes it as a HYPOTHESIS) is the classifier's reduction-stability above a certification level — that
is Layer B's job; F1 packages its COUNTING consequence (`L9 ⟹ r = p^n`), turning
`M8.constantFiber`'s `∃ r` into a body-fill.

Blueprint: FOUNDATION_BLUEPRINT.md §"F1 — Counting model" (D1–D6, L1–L9).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.F1

open Polynomial
open scoped Classical

variable (p : ℕ) [hp : Fact p.Prime]

/-- The level-`N` box is a `Finite` type (monic polynomials of bounded degree over a finite ring). The
coefficient map `f ↦ (i : Fin (n+1)) ↦ f.coeff i` is injective on the box (a degree-`n` poly is
determined by its coefficients `0…n`). Provides the `Finite` instances the fiber counts need. -/
instance instFiniteMonicBox (N n : ℕ) : Finite (QuotientBox.monicBox p N n) := by
  apply Finite.of_injective
    (f := fun f : QuotientBox.monicBox p N n => fun i : Fin (n + 1) => f.1.coeff i)
  rintro ⟨f, hfmon, hfdeg⟩ ⟨g, hgmon, hgdeg⟩ h
  apply Subtype.ext
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ n
  · have := congrFun h ⟨k, by omega⟩
    simpa using this
  · rw [not_le] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < k)]

/-! ## Definitions (D1–D6) -/

/-- The `g ↦ X^n + g` monic-shift bijection `degreeLT (ZMod(p^N)) n ≃ monicBox(p,N,n)` (the exact
`hbij` bijection of `M1.card_monicBox`, repackaged). Needs `0 < N` so that `ZMod(p^N)` is nontrivial. -/
noncomputable def toMonicEquiv (N n : ℕ) (hN : 0 < N) :
    degreeLT (QuotientBox.ResidueRing p N) n ≃ QuotientBox.monicBox p N n := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  have hdeg : ∀ g : degreeLT (QuotientBox.ResidueRing p N) n,
      (X ^ n + (g : (QuotientBox.ResidueRing p N)[X])).Monic ∧
      (X ^ n + (g : (QuotientBox.ResidueRing p N)[X])).natDegree = n := by
    intro g
    have hdlt : (g : (QuotientBox.ResidueRing p N)[X]).degree
        < (X ^ n : (QuotientBox.ResidueRing p N)[X]).degree := by
      rw [degree_X_pow]; exact mem_degreeLT.1 g.2
    refine ⟨(monic_X_pow n).add_of_left hdlt, natDegree_eq_of_degree_eq_some ?_⟩
    rw [add_comm, degree_add_eq_right_of_degree_lt hdlt, degree_X_pow]
  refine Equiv.ofBijective (fun g => ⟨X ^ n + (g : (QuotientBox.ResidueRing p N)[X]), hdeg g⟩) ?_
  constructor
  · exact fun g₁ g₂ h => Subtype.ext (add_left_cancel (congrArg Subtype.val h))
  · rintro ⟨q, hqmonic, hqdeg⟩
    have hq0 : q ≠ 0 := hqmonic.ne_zero
    have hqdeg' : q.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hq0, hqdeg]
    have hqX : (q - X ^ n).degree < (n : WithBot ℕ) := by
      have := degree_sub_lt (hqdeg'.trans (degree_X_pow n).symm) hq0
        (by rw [hqmonic.leadingCoeff, (monic_X_pow n).leadingCoeff])
      rwa [hqdeg'] at this
    exact ⟨⟨q - X ^ n, mem_degreeLT.2 hqX⟩,
      Subtype.ext (by change X ^ n + (q - X ^ n) = q; ring)⟩

/-- The defining property of `toMonicEquiv`: it sends `g` to `X^n + g`. -/
@[simp] theorem toMonicEquiv_apply (N n : ℕ) (hN : 0 < N) (g : degreeLT (QuotientBox.ResidueRing p N) n) :
    (toMonicEquiv p N n hN g).1 = X ^ n + (g : (QuotientBox.ResidueRing p N)[X]) := rfl

/-- (D1) `boxCoeffEquiv` — the `n`-coordinate trivialization of the level-`N` box, reused from M1's
inline bijection. `g ↦ X^n + g` (the `toMonicEquiv` shift) followed by `Polynomial.degreeLTEquiv`.
Surfaced as a named `Equiv` so the tower reduction can be performed componentwise. -/
noncomputable def boxCoeffEquiv (N n : ℕ) (hN : 0 < N) :
    QuotientBox.monicBox p N n ≃ (Fin n → QuotientBox.ResidueRing p N) :=
  (toMonicEquiv p N n hN).symm.trans (degreeLTEquiv (QuotientBox.ResidueRing p N) n).toEquiv

/-- Coefficient-extraction for `boxCoeffEquiv`: the `i`-th coordinate of `f` is the `i`-th coefficient
of `f - X^n` (the `degreeLT` representative). -/
theorem boxCoeffEquiv_apply (N n : ℕ) (hN : 0 < N) (f : QuotientBox.monicBox p N n) (i : Fin n) :
    boxCoeffEquiv p N n hN f i = ((toMonicEquiv p N n hN).symm f).1.coeff i := rfl

/-- The `degreeLT` representative of `f` is `f.1 - X^n`. -/
theorem toMonicEquiv_symm_coe (N n : ℕ) (hN : 0 < N) (f : QuotientBox.monicBox p N n) :
    (((toMonicEquiv p N n hN).symm f) : (QuotientBox.ResidueRing p N)[X]) = f.1 - X ^ n := by
  have h : (toMonicEquiv p N n hN ((toMonicEquiv p N n hN).symm f)).1 = f.1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply (toMonicEquiv p N n hN) f)
  rw [toMonicEquiv_apply] at h
  -- `X^n + repr = f.1`  ⟹  `repr = f.1 - X^n`
  rw [← h]; ring

/-- (D2) `coeffReduce` — the per-coordinate tower reduction `ZMod(p^{N+1}) →+* ZMod(p^N)`. -/
noncomputable def coeffReduce (N : ℕ) :
    QuotientBox.ResidueRing p (N + 1) →+* QuotientBox.ResidueRing p N :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p ^ N))

/-- (D4, single-step generalization) `coeffReduceLE` — the `N ≤ M` general tower reduction
`ZMod(p^M) →+* ZMod(p^N)`. -/
noncomputable def coeffReduceLE (N M : ℕ) (h : N ≤ M) :
    QuotientBox.ResidueRing p M →+* QuotientBox.ResidueRing p N :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N))

/-- The level-`N` residue ring is nontrivial for `0 < N` (so `Monic.natDegree_map` applies, i.e. the
reduction preserves degree). Not an `instance` (the `0 < N` hypothesis is not synthesizable); used via
`haveI`. -/
theorem nontrivialResidue (N : ℕ) (hN : 0 < N) : Nontrivial (QuotientBox.ResidueRing p N) := by
  rw [← not_subsingleton_iff_nontrivial, QuotientBox.ResidueRing, ZMod.subsingleton_iff]
  have : 1 < p ^ N := Nat.one_lt_pow hN.ne' hp.out.one_lt
  omega

/-- (D3) `boxReduce` — the polynomial-level reduction `monicBox(p,N+1,n) → monicBox(p,N,n)`, by
`Polynomial.map` of `coeffReduce`. Requires `0 < N` so the codomain `ZMod(p^N)` is `Nontrivial`
(`Monic.natDegree_map`); for `N = 0` the trivial-ring image collapses degree and the map cannot
preserve `natDegree = n` for `n > 0`, so the count is only stated for `0 < N`. Well-definedness:
`Monic.map` (monicity) + `Monic.natDegree_map` (degree preservation). -/
noncomputable def boxReduce (N n : ℕ) (hN : 0 < N) :
    QuotientBox.monicBox p (N + 1) n → QuotientBox.monicBox p N n :=
  fun f => ⟨(f.1).map (coeffReduce p N),
    ⟨(f.2.1).map (coeffReduce p N), by
      haveI := nontrivialResidue p N hN
      rw [(f.2.1).natDegree_map (coeffReduce p N)]; exact f.2.2⟩⟩

/-- (D4) `boxReduceLE` — the `N ≤ M` general tower reduction `monicBox(p,M,n) → monicBox(p,N,n)`.
Requires `0 < N` for the same degree-preservation reason as `boxReduce`. -/
noncomputable def boxReduceLE (N M n : ℕ) (h : N ≤ M) (hN : 0 < N) :
    QuotientBox.monicBox p M n → QuotientBox.monicBox p N n :=
  fun f => ⟨(f.1).map (coeffReduceLE p N M h),
    ⟨(f.2.1).map (coeffReduceLE p N M h), by
      haveI := nontrivialResidue p N hN
      rw [(f.2.1).natDegree_map (coeffReduceLE p N M h)]; exact f.2.2⟩⟩

/-- (D6) `normCount` — the normalized finite count (no measure). `(p^N)^n = q^{nN}` for `q = p`. -/
noncomputable def normCount (N n : ℕ) (S : QuotientBox.monicBox p N n → Prop) : ℚ :=
  (Nat.card {f : QuotientBox.monicBox p N n // S f} : ℚ) / (p ^ N : ℚ) ^ n

/-! ## Lemmas (L1–L9) -/

/-- (L1) `coeffReduce_surjective`: `coeffReduce` is surjective. One line via `ZMod.castHom_surjective`. -/
theorem coeffReduce_surjective (N : ℕ) : Function.Surjective (coeffReduce p N) :=
  ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ N))

/-- (L2) `coeffReduceLE_trans`: the cylinder tower commutativity. For `N ≤ M ≤ L`,
`(coeffReduceLE N M) ∘ (coeffReduceLE M L) = coeffReduceLE N L`. The finite analogue of
`PadicInt.zmod_cast_comp_toZModPow`. -/
theorem coeffReduceLE_trans (N M L : ℕ) (h₁ : N ≤ M) (h₂ : M ≤ L) :
    (coeffReduceLE p N M h₁).comp (coeffReduceLE p M L h₂) = coeffReduceLE p N L (h₁.trans h₂) :=
  ZMod.castHom_comp (pow_dvd_pow p h₁) (pow_dvd_pow p h₂)

/-- (L3) `coeffReduce_fiber_card`: the per-coordinate `p`-to-1 fiber count. For every residue
`a : ZMod(p^N)`, the fiber `{x : ZMod(p^{N+1}) // coeffReduce x = a}` has cardinality exactly `p`.

Proof (the per-coordinate `p`-to-1 heart): `coeffReduce` is a surjective additive group hom between
finite types, so all its fibers are equinumerous by additive translation (translate the kernel
`{x // coeffReduce x = 0}` by a chosen preimage). The fibers partition the domain
(`Equiv.sigmaFiberEquiv` + `Nat.card_sigma`), giving `p^N · (common fiber size) = p^{N+1}`, hence the
common fiber size is `p`. -/
theorem coeffReduce_fiber_card (N : ℕ) (a : QuotientBox.ResidueRing p N) :
    Nat.card {x : QuotientBox.ResidueRing p (N + 1) // coeffReduce p N x = a} = p := by
  -- abbreviate the additive hom (as a bare function, via the coercion of the RingHom)
  set g : QuotientBox.ResidueRing p (N + 1) → QuotientBox.ResidueRing p N := ⇑(coeffReduce p N)
    with hg
  have hsurj : Function.Surjective g := coeffReduce_surjective p N
  have hmap_add : ∀ x y, g (x + y) = g x + g y := fun x y => map_add (coeffReduce p N) x y
  have hmap_zero : g 0 = 0 := map_zero (coeffReduce p N)
  -- (1) all fibers are equinumerous to the fiber over `g 0 = 0`, via additive translation
  have hfiber_const : ∀ b : QuotientBox.ResidueRing p N,
      Nat.card {x // g x = b} = Nat.card {x // g x = (0 : QuotientBox.ResidueRing p N)} := by
    intro b
    obtain ⟨x₀, hx₀⟩ := hsurj b
    -- translation `y ↦ y + x₀` : fiber over `0` ≃ fiber over `b`
    refine (Nat.card_congr ?_).symm
    refine
      { toFun := fun y => ⟨y.1 + x₀, by rw [hmap_add, y.2, hx₀, zero_add]⟩
        invFun := fun x => ⟨x.1 - x₀, by
          rw [show x.1 - x₀ = x.1 + (-x₀) from by ring, hmap_add, x.2,
            show g (-x₀) = -(g x₀) from map_neg (coeffReduce p N) x₀, hx₀]; ring⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
  -- (2) the fibers partition the domain
  -- the common fiber size
  have hcardN : Nat.card (QuotientBox.ResidueRing p N) = p ^ N := QuotientBox.card_residueRing p N
  have hcardN1 : Nat.card (QuotientBox.ResidueRing p (N + 1)) = p ^ (N + 1) :=
    QuotientBox.card_residueRing p (N + 1)
  have hsum : Nat.card (QuotientBox.ResidueRing p (N + 1))
      = (Nat.card (QuotientBox.ResidueRing p N))
        * Nat.card {x // g x = (0 : QuotientBox.ResidueRing p N)} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
    rw [Finset.sum_congr rfl (fun b _ => hfiber_const b)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  -- (3) solve `p^{N+1} = p^N · c` for the common fiber size `c = p`
  rw [hcardN1, hcardN, pow_succ] at hsum
  have hpN : 0 < p ^ N := pow_pos hp.out.pos N
  have hcp : Nat.card {x // g x = (0 : QuotientBox.ResidueRing p N)} = p := by
    -- `p^N * p = p^N * c`  ⟹  `c = p`
    exact (Nat.eq_of_mul_eq_mul_left hpN hsum).symm
  rw [hfiber_const a, hcp]

/-- The KEY COMMUTATION: `boxReduce` acts coordinatewise as `coeffReduce` under the trivialization
`boxCoeffEquiv`. `boxCoeffEquiv (boxReduce f) i = coeffReduce (boxCoeffEquiv f i)`. This is the seam
that turns the polynomial-level reduction into the per-coordinate `coeffReduce`. -/
theorem boxCoeffEquiv_boxReduce (N n : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p (N + 1) n) (i : Fin n) :
    boxCoeffEquiv p N n hN (boxReduce p N n hN f) i
      = coeffReduce p N (boxCoeffEquiv p (N + 1) n (by omega) f i) := by
  rw [boxCoeffEquiv_apply, boxCoeffEquiv_apply, toMonicEquiv_symm_coe, toMonicEquiv_symm_coe]
  -- `(boxReduce f).1 = f.1.map coeffReduce`; reductions commute with `- X^n` (coeffReduce fixes X^n)
  show (((boxReduce p N n hN f).1 - X ^ n).coeff i)
      = coeffReduce p N ((f.1 - X ^ n).coeff i)
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, map_sub]
  congr 1
  · -- the box-reduced poly's i-th coeff = coeffReduce of the original's i-th coeff
    show ((f.1).map (coeffReduce p N)).coeff i = coeffReduce p N (f.1.coeff i)
    rw [Polynomial.coeff_map]
  · -- `X^n`'s i-th coeff is fixed by the ring hom
    rw [Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    split <;> simp

/-- (L4) `boxReduce_surjective`: `boxReduce` is surjective. Transport `L1` across `boxCoeffEquiv`
componentwise: a monic poly over `ZMod(p^N)` lifts coefficientwise (each coeff surjects), and the
`X^n + g` shift preserves the monic/degree data (the commutation `boxCoeffEquiv_boxReduce`). -/
theorem boxReduce_surjective (N n : ℕ) (hN : 0 < N) :
    Function.Surjective (boxReduce p N n hN) := by
  intro g
  -- coordinate vector of the target
  set v : Fin n → QuotientBox.ResidueRing p N := boxCoeffEquiv p N n hN g with hv
  -- lift each coordinate via L1
  have hlift : ∀ i, ∃ w : QuotientBox.ResidueRing p (N + 1), coeffReduce p N w = v i :=
    fun i => coeffReduce_surjective p N (v i)
  choose w hw using hlift
  -- assemble the lifted polynomial in the level-(N+1) box
  refine ⟨(boxCoeffEquiv p (N + 1) n (by omega)).symm w, ?_⟩
  -- it suffices to show the coordinate vectors agree (boxCoeffEquiv is injective)
  apply (boxCoeffEquiv p N n hN).injective
  funext i
  rw [boxCoeffEquiv_boxReduce, Equiv.apply_symm_apply, hw, hv]

/-- (L5) `boxReduce_fiber_card`: the total `p^n`-to-1 fiber count. For every `g : monicBox(p,N,n)`,
the fiber `{f : monicBox(p,N+1,n) // boxReduce f = g}` has cardinality `p^n`.

Proof: transport the fiber across `boxCoeffEquiv` (D1); under the trivialization the fiber of
`boxReduce` over `g` is the product over the `n` free coordinates of the per-coordinate fibers of
`coeffReduce`; apply `M8.coordinateResidue_card_factor` with `P i x := coeffReduce x = v i`, then `L3`
gives each factor `= p`, and `∏_{Fin n} p = p^n`. -/
theorem boxReduce_fiber_card (N n : ℕ) (hN : 0 < N) (g : QuotientBox.monicBox p N n) :
    Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g} = p ^ n := by
  -- coordinate vector of `g`
  set v : Fin n → QuotientBox.ResidueRing p N := boxCoeffEquiv p N n hN g with hv
  -- the fiber of `boxReduce` over `g` is in bijection with the constrained coordinate-vector set,
  -- transported across `boxCoeffEquiv` at level `N+1`; the fiber constraint translates coordinatewise
  -- via the commutation `boxCoeffEquiv_boxReduce`
  have hbij : Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g}
      = Nat.card {c : Fin n → QuotientBox.ResidueRing p (N + 1) // ∀ i, coeffReduce p N (c i) = v i} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (boxCoeffEquiv p (N + 1) n (by omega)) ?_
    intro f
    constructor
    · -- `boxReduce f = g`  ⟹  coordinatewise `coeffReduce (boxCoeffEquiv f i) = v i`
      intro hf i
      rw [← boxCoeffEquiv_boxReduce, hf, hv]
    · -- coordinatewise constraint  ⟹  `boxReduce f = g` (boxCoeffEquiv injective at level N)
      intro hc
      apply (boxCoeffEquiv p N n hN).injective
      funext i
      rw [boxCoeffEquiv_boxReduce, hc i, hv]
  rw [hbij, M8.coordinateResidue_card_factor n (fun i x => coeffReduce p N x = v i)]
  -- each per-coordinate factor is `p` by L3
  have hfac : ∀ i : Fin n,
      Nat.card {x : QuotientBox.ResidueRing p (N + 1) // coeffReduce p N x = v i} = p :=
    fun i => coeffReduce_fiber_card p N (v i)
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- (L6) `card_monicBox_succ_ratio`: `#monicBox(p,N+1,n) = p^n · #monicBox(p,N,n)`. The cheap proof
via `M1.card_monicBox` on both sides + `pow` arithmetic. -/
theorem card_monicBox_succ_ratio (N n : ℕ) (hN : 0 < N) :
    Nat.card (QuotientBox.monicBox p (N + 1) n) = p ^ n * Nat.card (QuotientBox.monicBox p N n) := by
  rw [QuotientBox.card_monicBox p (N + 1) n (by omega), QuotientBox.card_monicBox p N n hN]
  rw [pow_succ p N]
  -- ((p^N * p))^n = p^n * (p^N)^n
  rw [mul_pow, mul_comm ((p ^ N) ^ n) (p ^ n)]

/-- (L7) `normCount_box_eq_one`: the box is the TOTAL, with normalized count `≡ 1`. -/
theorem normCount_box_eq_one (N n : ℕ) (hN : 0 < N) :
    normCount p N n (fun _ => True) = 1 := by
  unfold normCount
  have hnum : Nat.card {f : QuotientBox.monicBox p N n // True} = (p ^ N) ^ n := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))]
    exact QuotientBox.card_monicBox p N n hN
  rw [hnum]
  have hden : ((p ^ N : ℚ)) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast pow_ne_zero N hp.out.ne_zero
  push_cast
  field_simp

/-- (L8a) `cylinder_count_stable`: if a level-`N` predicate `S` is "decided" — there is `S'` at level
`N+1` whose subtype is the `boxReduce`-preimage of `S`'s subtype — then the normalized count is stable
across the step. The preimage of `S` under the `p^n`-to-1 surjection `boxReduce` has card
`p^n · #S`, and the `q^{nN}` normalization cancels the `p^n`.

Stated with the cylinder hypothesis in fiber form: `S'` exactly cuts out the `boxReduce`-preimage of
`S`. -/
theorem cylinder_count_stable (N n : ℕ) (hN : 0 < N)
    (S : QuotientBox.monicBox p N n → Prop) (S' : QuotientBox.monicBox p (N + 1) n → Prop)
    (hcyl : ∀ f, S' f ↔ S (boxReduce p N n hN f)) :
    normCount p (N + 1) n S' = normCount p N n S := by
  unfold normCount
  -- numerator at level N+1: `#{f // S' f}` = `#{f // S (boxReduce f)}` = `p^n · #{g // S g}`
  haveI : Fintype {g : QuotientBox.monicBox p N n // S g} := Fintype.ofFinite _
  have hnumeq : Nat.card {f : QuotientBox.monicBox p (N + 1) n // S' f}
      = p ^ n * Nat.card {g : QuotientBox.monicBox p N n // S g} := by
    -- rewrite the subtype by the cylinder hypothesis
    have hcong : Nat.card {f : QuotientBox.monicBox p (N + 1) n // S' f}
        = Nat.card {f : QuotientBox.monicBox p (N + 1) n // S (boxReduce p N n hN f)} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun f => hcyl f)
    rw [hcong]
    -- partition the preimage fiberwise over `{g // S g}`
    -- `{f // S (boxReduce f)} ≃ Σ (g : {g // S g}), {f // boxReduce f = g.1}`
    have hpart : Nat.card {f : QuotientBox.monicBox p (N + 1) n // S (boxReduce p N n hN f)}
        = ∑ g : {g : QuotientBox.monicBox p N n // S g},
            Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1} := by
      rw [← Nat.card_sigma (β := fun g : {g : QuotientBox.monicBox p N n // S g} =>
        {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1})]
      apply Nat.card_congr
      -- the preimage of the decided set, sliced over which decided `g` it lands on
      refine
        { toFun := fun f => ⟨⟨boxReduce p N n hN f.1, f.2⟩, ⟨f.1, rfl⟩⟩
          invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
          left_inv := fun f => by rfl
          right_inv := fun s => by
            obtain ⟨⟨g, hg⟩, ⟨f, hf⟩⟩ := s
            simp only at hf ⊢
            subst hf
            rfl }
    rw [hpart]
    -- each inner term is `p^n` by L5
    have hinner : ∀ g : {g : QuotientBox.monicBox p N n // S g},
        Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1} = p ^ n :=
      fun g => boxReduce_fiber_card p N n hN g.1
    rw [Finset.sum_congr rfl (fun g _ => hinner g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.mul_comm, Nat.card_eq_fintype_card]
  rw [hnumeq]
  -- arithmetic: `(p^n · #S) / (p^{N+1})^n = #S / (p^N)^n`
  have hpN : ((p : ℚ) ^ N) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.out.ne_zero
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast
  rw [show (p : ℚ) ^ (N + 1) = (p : ℚ) ^ N * p from pow_succ (p : ℚ) N]
  field_simp
  ring

/-- `boxReduce` is the unit step of `boxReduceLE`: `boxReduce p M n = boxReduceLE p M (M+1) n`. Both
are `Polynomial.map (ZMod.castHom (pow_dvd_pow p _))`; defeq. -/
theorem boxReduce_eq_boxReduceLE (M n : ℕ) (hM : 0 < M) :
    boxReduce p M n hM = boxReduceLE p M (M + 1) n (Nat.le_succ M) hM := rfl

/-- The `boxReduceLE` tower commutativity (`thm`-level glue for `L8b`): reducing from level `M+1`
straight to `N` equals first reducing `M+1 → M` then `M → N`.
`boxReduceLE N M (boxReduce M f) = boxReduceLE N (M+1) f`. Reduces to `Polynomial.map_map` +
`coeffReduceLE_trans`. -/
theorem boxReduceLE_boxReduce (N M n : ℕ) (h : N ≤ M) (hN : 0 < N) (hM : 0 < M)
    (f : QuotientBox.monicBox p (M + 1) n) :
    boxReduceLE p N M n h hN (boxReduce p M n hM f)
      = boxReduceLE p N (M + 1) n (h.trans (Nat.le_succ M)) hN f := by
  apply Subtype.ext
  show ((f.1).map (coeffReduce p M)).map (coeffReduceLE p N M h)
    = (f.1).map (coeffReduceLE p N (M + 1) (h.trans (Nat.le_succ M)))
  rw [Polynomial.map_map]
  congr 1
  -- `(coeffReduceLE N M).comp (coeffReduce M) = coeffReduceLE N (M+1)`
  show (coeffReduceLE p N M h).comp (coeffReduceLE p M (M + 1) (Nat.le_succ M))
    = coeffReduceLE p N (M + 1) (h.trans (Nat.le_succ M))
  exact coeffReduceLE_trans p N M (M + 1) h (Nat.le_succ M)

/-- (L8b) `cylinder_count_stable_LE`: iterate `L8a` along `N ≤ M`. For a level-`N`-decided `S`, the
normalized count of the level-`M` cylinder equals `normCount p N n S` for ALL `M ≥ N`. The cylinder
at level `M` is recorded as a predicate family `Scyl` with `Scyl M f ↔ S (boxReduceLE N M f)`.

CLOSED (WAVE-0): induction on `M = N + k`; base via `hbase`; step via `L8a` (`cylinder_count_stable`)
with the cylinder relation `Scyl (M+1) f ↔ Scyl M (boxReduce M f)` supplied by `hstep` +
`boxReduceLE_boxReduce` (the tower commutativity). The `boxReduceLE` well-definedness is now closed in
`D4` (`0 < N` makes the codomain `Nontrivial`). -/
theorem cylinder_count_stable_LE (N n : ℕ) (hN : 0 < N)
    (S : QuotientBox.monicBox p N n → Prop)
    (Scyl : (M : ℕ) → QuotientBox.monicBox p M n → Prop)
    (hbase : ∀ f, Scyl N f ↔ S f)
    (hstep : ∀ M (hM : N ≤ M) f, Scyl M f ↔ S (boxReduceLE p N M n hM hN f)) :
    ∀ M (hM : N ≤ M), normCount p M n (Scyl M) = normCount p N n S := by
  -- induct on the gap `k = M - N`
  intro M hM
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  clear hM
  induction k with
  | zero =>
    -- `Scyl N` agrees with `S` pointwise (and `N + 0 = N`)
    simp only [Nat.add_zero]
    unfold normCount
    congr 1
    exact_mod_cast Nat.card_congr (Equiv.subtypeEquivRight (fun f => hbase f))
  | succ k ih =>
    -- one L8a step from level `N+k` to `N+k+1 = N+(k+1)`, then the inductive hypothesis
    have hNk : 0 < N + k := by omega
    -- the cylinder relation: `Scyl (N+k+1) f ↔ Scyl (N+k) (boxReduce f)`
    have hstepcyl : ∀ f, Scyl (N + k + 1) f
        ↔ Scyl (N + k) (boxReduce p (N + k) n hNk f) := by
      intro f
      rw [hstep (N + k + 1) (by omega) f, hstep (N + k) (by omega) (boxReduce p (N + k) n hNk f)]
      rw [boxReduceLE_boxReduce p N (N + k) n (by omega) hN hNk f]
    -- rewrite `N + (k+1)` as `(N+k)+1` and apply L8a then `ih`
    rw [show N + (k + 1) = (N + k) + 1 from rfl]
    rw [cylinder_count_stable p (N + k) n hNk (Scyl (N + k)) (Scyl ((N + k) + 1)) hstepcyl]
    exact ih

/-- (L9) shape-fiber consistency bridge — DISCHARGES `M8.constantFiber`'s `∃ r` with `r = p^n`.
IF the classifier is reduction-stable above `N₀` (`classify M (boxReduceLE g) = classify N g` for
`N₀ ≤ N ≤ M`, a Core-B hypothesis), THEN `M8.shapeFiberCount T (N+1) = p^n · M8.shapeFiberCount T N`
for `N ≥ N₀` — exactly the per-step ratio `r = p^n` needed by `M8.constantFiber`.

CLOSED (WAVE-0): consumes the reduction-stability spec (B's deliverable, available as a hypothesis
here). The shape-`T` fiber at level `N+1` is the `boxReduce`-preimage of the shape-`T` fiber at level
`N` (stability: `classify (N+1) f = T ↔ classify N (boxReduce f) = T`); its card is `p^n` times by the
fiberwise partition (`Equiv.sigmaFiberEquiv` + `L5`/`boxReduce_fiber_card`), exactly as in `L8a`. This
DISCHARGES `M8.constantFiber`'s `∃ r` with `r = (p:ℚ)^n`. -/
theorem shapeFiber_consistency
    (n : ℕ) (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape) (T : ClusterShape)
    (N₀ : ℕ)
    (hstable : ∀ N M (_hN₀ : N₀ ≤ N) (hM : N ≤ M) (hNpos : 0 < N) (g : QuotientBox.monicBox p M n),
      classify M g = classify N (boxReduceLE p N M n hM hNpos g)) :
    ∀ N, N₀ ≤ N → 0 < N →
      (M8.shapeFiberCount p n classify T (N + 1) : ℤ)
        = (p : ℤ) ^ n * M8.shapeFiberCount p n classify T N := by
  intro N hN₀ hN
  -- the shape-`T` fiber at level `N+1` equals the `boxReduce`-preimage of the shape-`T` fiber at `N`
  -- `classify (N+1) f = T  ↔  classify N (boxReduce N f) = T`
  have hcyl : ∀ f : QuotientBox.monicBox p (N + 1) n,
      classify (N + 1) f = T ↔ classify N (boxReduce p N n hN f) = T := by
    intro f
    rw [hstable N (N + 1) hN₀ (Nat.le_succ N) hN f, boxReduce_eq_boxReduceLE p N n hN]
  -- the Nat-level count identity (the same fiberwise partition as L8a)
  have hnat : M8.shapeFiberCount p n classify T (N + 1)
      = p ^ n * M8.shapeFiberCount p n classify T N := by
    unfold M8.shapeFiberCount
    haveI : Fintype {g : QuotientBox.monicBox p N n // classify N g = T} := Fintype.ofFinite _
    -- rewrite the level-(N+1) fiber by stability
    have hcong : Nat.card {f : QuotientBox.monicBox p (N + 1) n // classify (N + 1) f = T}
        = Nat.card {f : QuotientBox.monicBox p (N + 1) n // classify N (boxReduce p N n hN f) = T} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun f => hcyl f))
    rw [hcong]
    -- partition the preimage fiberwise over the decided level-`N` shape fiber
    have hpart : Nat.card {f : QuotientBox.monicBox p (N + 1) n // classify N (boxReduce p N n hN f) = T}
        = ∑ g : {g : QuotientBox.monicBox p N n // classify N g = T},
            Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1} := by
      rw [← Nat.card_sigma (β := fun g : {g : QuotientBox.monicBox p N n // classify N g = T} =>
        {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1})]
      apply Nat.card_congr
      refine
        { toFun := fun f => ⟨⟨boxReduce p N n hN f.1, f.2⟩, ⟨f.1, rfl⟩⟩
          invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
          left_inv := fun f => by rfl
          right_inv := fun s => by
            obtain ⟨⟨g, hg⟩, ⟨f, hf⟩⟩ := s
            simp only at hf ⊢
            subst hf
            rfl }
    rw [hpart]
    have hinner : ∀ g : {g : QuotientBox.monicBox p N n // classify N g = T},
        Nat.card {f : QuotientBox.monicBox p (N + 1) n // boxReduce p N n hN f = g.1} = p ^ n :=
      fun g => boxReduce_fiber_card p N n hN g.1
    rw [Finset.sum_congr rfl (fun g _ => hinner g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.mul_comm, Nat.card_eq_fintype_card]
  -- cast to ℤ
  rw [hnat]
  push_cast
  ring

/- ⚠ **FALSE AS STATED — UNSOUND (flagged 2026-06-30; do NOT trust).** Same defect family as
`M8.selfLoop_childFiber_corrected`: quantified over FREE, UNRELATED `classify`/`cells`/`treeSize`, so the
across-level split cannot hold for all `cells` (the LHS is independent of `cells`). TRUE only when
`cells`/`treeSize` ARE the real OM decomposition of `classify`; the fix is to add that as a hypothesis. OFF
the capstone footprint after the 2026-06-30 `h_node` revert. ORIGINAL (over-strong) docstring follows:
**[CITE] GMN Thm 3.1/3.7 + Cor 3.8 / Lemma 3.11(3) (Guàrdia–Montes–Nart, arXiv:0807.2620v2 §3),
self-loop child across-level fiber, f-keyed + bulk-gated.** For a shape `T`, the level-`(N+1)` type-`T`
stratum splits as the NON-self-loop cells (children `ch` with `treeSize ch ≠ treeSize T`, recursing at
`N+1`) PLUS the diagonal self-loop child re-entering the level-`N` type-`T` stratum scaled by the
per-step ramification ratio `selfLoopRatio T q = q^{-w(treeSize T)}`, UP TO an additive error supported
on the disc-tail `{v_p(disc) ≥ N}` (bounded by `htail`, i.e. `|e| ≤ C·q^{nN}·q^{-N}`).

This is the across-level recursion that the proved single-level `stratumCount_factor` cannot see (it has
STRICT child descent `treeSize ch < treeSize T`, hence no diagonal self-loop term) and that the lumped
`shapeFiber_consistency` averages away (total `p^n` ratio, no geometric structure). It is imported
FAITHFULLY per GMN's theorem-of-the-product descent — a genuine structural fact about the OM tree, NOT
a counting tautology over the cells already exposed.

CRITICAL (resolves `M8.nodeTrunc_limit_denominator_mismatch`): the self-loop term is exactly
`selfLoopRatio T q · stratumCount T N` with NO extra `q^{-n}` factor — the inter-level `q^n` from the
`boxReduce` fiber is absorbed ONCE into the bulk preimage, not into the ratio.

The user authorized importing this descent identity as a named axiom; it is the single GMN structural
import for the F2/B self-loop split, NOT a sub-proof, and is α-equal to `shapeFiber_consistency_bulk`'s
goal. -/
/- ⚠ **AXIOM DELETED (2026-07-04).** `selfLoop_childFiber_fkeyed` (A6) was FALSE-AS-STATED over its
free `cells`/`treeSize` binders: the LHS `M8.stratumCount (M8.shapeFiberCount p n classify) T (N+1)`
depends only on `classify`, while the RHS filtered-cell sum + self-loop term depend on the FREE,
UNRELATED `cells`/`treeSize` (e.g. `cells := fun _ => []` empties the non-self-loop sum and forces the
whole level-`(N+1)` stratum into `selfLoopRatio · stratumCount T N + e`, false for a generic
`classify`). Same free-binder defect family as the deleted `M8.L2_reconstruct`,
`M8.selfLoop_childFiber_corrected` and `M8.boxVolumeScale_collapse` (LevelNCount.lean). Its content —
the GMN across-level self-loop descent split (Thm 3.1/3.7 + Cor 3.8 / Lemma 3.11(3),
arXiv:0807.2620v2) — is TRUE only when `cells`/`treeSize` ARE the genuine OM decomposition of
`classify`, and is now threaded as the explicit hypothesis `hA6` of `shapeFiber_consistency_bulk`
below (to be discharged at the pinned objects per `HNODE_GENUINE_FIX_BLUEPRINT.md` /
`PIN_ARCHITECTURE_BLUEPRINT.md`). -/

/-! ## REDSTAB Deliverable 3 — the per-shape self-loop / non-self-loop SPLIT

`REDSTAB_BLUEPRINT.md` §"DELIVERABLE 3". The lumped `p^n` ratio of `shapeFiber_consistency` (over-strong
+ dead code) is replaced by the GLUE-1-shaped per-shape decomposition: the non-self-loop cells'
contribution (strictly-descending children, recursion in `N+1`) PLUS the self-loop cell re-entering at
level `N` scaled by `selfLoopRatio`, UP TO a vanishing disc-tail error. This is the per-shape
combinatorial identity that GLUE-1 `stratumCount_selfLoop_rec` currently `sorry`s, with the bulk/tail
correction made explicit so the consumers (a `Filter.Tendsto` limit) tolerate the additive `o(q^{nN})`.

⚠ RISK (c) — THE riskiest mathematics in REDSTAB. The self-loop factor must land as
`selfLoopRatio · stratumCount T N` (the diagonal child genuinely re-enters at level `N`, the inter-level
`q^n` from `boxReduce_fiber_card` is applied ONCE to the bulk preimage), NOT
`selfLoopRatio · q^{-n} · stratumCount T N`. The latter type-checks but is mathematically WRONG: it
forces limit denominator `1 - selfLoopRatio·q^{-n} ≠ countPivot` for every `n ≥ 1` (the machine-checked
disproof `M8.nodeTrunc_limit_denominator_mismatch`, LevelNCount.lean).

**(2026-07-04) NO LONGER discharged by the axiom `selfLoop_childFiber_fkeyed` — that axiom was
FALSE-AS-STATED over its free `cells`/`treeSize` binders (LHS independent of `cells`; see its tombstone
above) and is DELETED.** Per `REDSTAB2_BLUEPRINT.md` §"TARGET 3": this statement is NOT derivable
in-repo. The proved single-level `stratumCount_factor` (LevelNCount.lean) has STRICT child descent
(`cells_descend : treeSize ch < treeSize T`), so it carries NO diagonal self-loop term; and the lumped
`shapeFiber_consistency` (above) gives only the total `p^n` ratio (no geometric self-loop structure).
The missing content is exactly GMN's serial-pole / theorem-of-the-product descent identifying WHICH
level-`(N+1)` cosets in the type-`T` fiber are the DIAGONAL self-loop re-entry of the level-`N`
type-`T` fiber, and that the diagonal child's across-level fiber ratio is `selfLoopRatio = q^{-w}`.
That content now enters as the explicit hypothesis `hA6` (VERBATIM the deleted axiom's conclusion), to
be discharged only at the genuine OM decomposition (`cells`/`treeSize` pinned to `classify` per
`HNODE_GENUINE_FIX_BLUEPRINT.md` / `PIN_ARCHITECTURE_BLUEPRINT.md`); this theorem is now the CONTRACT
recording the Deliverable-3 shape, not a closed cite. Off the capstone path (the capstone routes
through the top-level `LeanUrat.CountingModel`, not this F2 self-loop split). -/
theorem shapeFiber_consistency_bulk
    (n : ℕ) (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List LeanUrat.MontesAxiom.CountCell) (treeSize : ClusterShape → ℕ) (q : ℕ)
    (T : ClusterShape)
    (hstable : LeanUrat.OM.B.ClassifyReductionStableFKeyed p n classify)
    (C : ℚ)
    (htail : ∀ N, 0 < N →
      (Nat.card {g : QuotientBox.monicBox p (N + 1) n //
          N ≤ PadicLift.zmodValuation p (N + 1) (g.1.discr)} : ℚ)
        ≤ C * (q : ℚ) ^ (n * (N + 1)) * ((q : ℚ) ^ N)⁻¹)
    -- (2026-07-04) the across-level self-loop split, now an EXPLICIT HYPOTHESIS (the former axiom
    -- `selfLoop_childFiber_fkeyed` was FALSE-AS-STATED over the free `cells`/`treeSize` binders and is
    -- DELETED; the TRUE constrained form pins `cells`/`treeSize` to the genuine OM decomposition of
    -- `classify` per HNODE_GENUINE_FIX_BLUEPRINT.md / PIN_ARCHITECTURE_BLUEPRINT.md):
    (hA6 : ∀ N, 0 < N →
      ∃ e : ℚ, |e| ≤ C * (q : ℚ) ^ (n * N) * ((q : ℚ) ^ N)⁻¹ ∧
        (M8.stratumCount (M8.shapeFiberCount p n classify) T (N + 1) : ℚ)
          = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
              (fun c =>
                L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                  * (c.children.map (fun ch =>
                      M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
            + M8.selfLoopRatio treeSize T q
                * M8.stratumCount (M8.shapeFiberCount p n classify) T N
            + e) :
    ∀ N, 0 < N →
      ∃ e : ℚ, |e| ≤ C * (q : ℚ) ^ (n * N) * ((q : ℚ) ^ N)⁻¹ ∧
        (M8.stratumCount (M8.shapeFiberCount p n classify) T (N + 1) : ℚ)
          = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
              (fun c =>
                L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                  * (c.children.map (fun ch =>
                      M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
            + M8.selfLoopRatio treeSize T q
                * M8.stratumCount (M8.shapeFiberCount p n classify) T N
            + e :=
  hA6

end LeanUrat.OM.F1
