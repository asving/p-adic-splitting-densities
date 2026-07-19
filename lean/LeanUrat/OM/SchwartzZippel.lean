import Mathlib
import LeanUrat.OM.ResidueCount
import LeanUrat.OM.QuotientBox

/-!
# F4 (Stage C) — `SchwartzZippel`: the local-ring root-density lemma (the mathlib GAP)

This is **Bundle 0c / Layer F4 part 2** of the foundational-machinery fill (blueprint
`FOUNDATION_BLUEPRINT.md`, §"F4 — Discriminant tail", Stage C). It supplies the **Schwartz–Zippel /
root-density bound over the non-domain local ring `ZMod (p^N)`** that mathlib lacks: mathlib's
`MvPolynomial.schwartz_zippel_totalDegree` and `schwartz_zippel_sup_sum`
(`Algebra/MvPolynomial/SchwartzZippel.lean`) BOTH require `[IsDomain R]` (variable decl line 62), and
`ZMod (p^N)` is **not** an integral domain for `N ≥ 2` (`p · p^{N-1} = 0`). So the existing SZ is
unusable here; this module re-proves the root-density bound from scratch over the local ring, lifting
the mod-`p` (field) count to mod-`p^N` by the reduction-to-residue-field + uniform-fiber argument
(the "Hensel" lift, done crudely as `≤ p^{N-1}` lifts per mod-`p` root — sufficient for the `q^{-1}`
static density that feeds the discriminant tail).

The three nodes (blueprint Stage-C DAG `L-C3 → L-C2 → L-C1`):

* `castHom_fiber_card` (**L-C3**): every fiber of the reduction `ZMod (p^N) ↠ ZMod p` has exactly
  `p^{N-1}` elements. PROVED sorry-free (pure finite-group fiber count via equinumerous fibers of a
  surjective additive hom + `card_eq_sum_card_fiberwise`).
* `card_roots_zmod_ppow_le` (**L-C2**): a single-variable polynomial over `ZMod (p^N)` whose mod-`p`
  reduction is nonzero of degree `d` has `≤ d · p^{N-1}` roots in `ZMod (p^N)`. PROVED sorry-free
  (reduce to the residue field `ZMod p`, count roots there by `card_roots'`, lift each by L-C3).
* `schwartz_zippel_local` (**L-C1**): the multivariate local-ring Schwartz–Zippel bound, by peeling the
  first variable (`finSuccEquiv`) and fibering the tuple count over the frozen tail, with the
  unit-leading stratum charged to the mod-`p` slice degree via the sharper L-C2
  (`card_roots_zmod_ppow_le'`) and the vanishing stratum counted by the power-fiber `tail_fiber_card`
  times the *field* Schwartz–Zippel `field_zero_count_le` (mathlib's `schwartz_zippel_totalDegree`,
  valid over the residue field `ZMod p`). PROVED sorry-free (core-only). The local-ring `ih` is not
  needed — the vanishing stratum is bounded over the residue field, which IS a domain.

B-INDEPENDENT: nothing here depends on the Core-B classifier or the serial spine. Edits ONLY this file.

NAMES verified against mathlib v4.31.0 (`.lake/packages/mathlib`):
`ZMod.castHom` (Data/ZMod/Basic.lean:330), `ZMod.castHom_surjective` (:361), `ZMod.card`
(Data/ZMod/Defs.lean:173), `Polynomial.card_roots'` (Algebra/Polynomial/Roots.lean:79),
`Polynomial.natDegree_map_le` (Algebra/Polynomial/Eval/Degree.lean:151), `Polynomial.IsRoot.map`
(Algebra/Polynomial/Eval/Coeff.lean:218), `AddMonoidHom.card_fiber_eq_of_mem_range`
(GroupTheory/Index.lean:894), `Finset.card_eq_sum_card_fiberwise`
(Algebra/BigOperators/Group/Finset/Basic.lean:979), `dvd_pow_self` (Algebra/Divisibility/Basic.lean:144).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.SchwartzZippel

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## L-C3 — uniform fiber cardinality of the reduction `ZMod (p^N) ↠ ZMod p` -/

/-- The reduction ring hom `ZMod (p^(N+1)) →+* ZMod p` (the residue-field projection). We package it
for `N+1` so that `0 < N+1` is automatic and `p ∣ p^(N+1)` holds via `dvd_pow_self`. -/
noncomputable def redHom (N : ℕ) : ZMod (p ^ (N + 1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero N)) (ZMod p)

theorem redHom_surjective (N : ℕ) : Function.Surjective (redHom (p := p) N) :=
  ZMod.castHom_surjective _

/-- **L-C3 `castHom_fiber_card`.** Every fiber of the reduction `ZMod (p^(N+1)) ↠ ZMod p` has exactly
`p^N` elements.

PROOF: `redHom` is a surjective additive-group hom between the finite additive groups `ZMod (p^(N+1))`
and `ZMod p`. The total set partitions fiberwise over `ZMod p`; all fibers are equinumerous
(`AddMonoidHom.card_fiber_eq_of_mem_range`, every element being in the range by surjectivity), and
there are `p` of them, so each has card `p^(N+1) / p = p^N`. Pure finite-group fiber count. -/
theorem castHom_fiber_card (N : ℕ) (y : ZMod p) :
    Nat.card {x : ZMod (p ^ (N + 1)) // redHom (p := p) N x = y} = p ^ N := by
  classical
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- The additive-monoid-hom underlying `redHom`.
  let f : ZMod (p ^ (N + 1)) →+ ZMod p := (redHom (p := p) N).toAddMonoidHom
  have hfsurj : Function.Surjective f := redHom_surjective (p := p) N
  -- Each fiber of `f` as a `Finset` of `ZMod (p^(N+1))`.
  have hmem : ∀ z : ZMod p, z ∈ Set.range f := fun z => hfsurj z
  -- All fibers are equinumerous (surjective additive hom on a finite group).
  have hfib_eq : ∀ z : ZMod p, #{g | f g = z} = #{g | f g = y} := by
    intro z
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hmem z) (hmem y)
  -- Total card = sum over `ZMod p` of fiber cards (each lands in its image).
  have hsum : (Fintype.card (ZMod (p ^ (N + 1)))) = ∑ z : ZMod p, #{g | f g = z} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
  -- Replace every term by the `y`-fiber card; abbreviate the fiber count as `c`.
  set c : ℕ := #{g | f g = y} with hc
  rw [Finset.sum_congr rfl (fun z _ => hfib_eq z), Finset.sum_const, Finset.card_univ,
      ZMod.card, ZMod.card, smul_eq_mul] at hsum
  -- `hsum : p^(N+1) = p * c`. Cancel one `p`.
  have hp0 : 0 < p := hp.out.pos
  have hcard_fin : c = p ^ N := by
    have hmul : p * p ^ N = p * c := by rw [← pow_succ']; exact hsum
    exact (Nat.eq_of_mul_eq_mul_left hp0 hmul).symm
  -- Bridge `Nat.card` of the subtype to the `Finset.filter` card. `f x = (redHom N) x` defeq.
  rw [Nat.card_eq_fintype_card]
  have hbridge : Fintype.card {x : ZMod (p ^ (N + 1)) // (redHom (p := p) N) x = y} = c := by
    rw [hc, ← Fintype.card_subtype]
    rfl
  rw [hbridge, hcard_fin]

/-- A convenient `Finset` form of L-C3: the full `redHom`-fiber over `y`, as a `Finset` of
`ZMod (p^(N+1))`, has `p^N` elements. -/
theorem fiber_finset_card (N : ℕ) (y : ZMod p) :
    #{x : ZMod (p ^ (N + 1)) | redHom (p := p) N x = y} = p ^ N := by
  classical
  have h := castHom_fiber_card (p := p) N y
  rw [Nat.card_eq_fintype_card] at h
  rw [← h, Fintype.card_subtype]

/-! ## L-C2 — root count of a single-variable polynomial over `ZMod (p^(N+1))` -/

/-- **L-C2 `card_roots_zmod_ppow_le`.** A single-variable polynomial `D` over the local ring
`ZMod (p^(N+1))` whose **mod-`p` reduction is nonzero** has at most `D.natDegree · p^N` roots in
`ZMod (p^(N+1))`.

This is the heart of the local-ring lift: mathlib's `card_roots'` only counts roots over a domain,
and `ZMod (p^(N+1))` is not a domain for `N ≥ 1`. We reduce to the residue **field** `ZMod p`:

* a root `x` of `D` maps under `redHom` to a root `redHom x` of `D̄ := D.map redHom` (`IsRoot.map`);
* over the field `ZMod p`, `D̄ ≠ 0` has `≤ D̄.natDegree ≤ D.natDegree` distinct roots (`card_roots'`
  + `natDegree_map_le`), collected in the `Finset` `Rbar := D̄.roots.toFinset`;
* the root set of `D` therefore fibers over `Rbar` under `redHom`, and each fiber is contained in a
  full `redHom`-fiber of card `p^N` (**L-C3** `fiber_finset_card`);
* so `#roots(D) = ∑_{y ∈ Rbar} #(fiber) ≤ #Rbar · p^N ≤ D.natDegree · p^N`.

The crude `≤ p^N` lifts-per-residue-root bound is all the static `q^{-1}` discriminant density needs.
PROVED sorry-free. -/
theorem card_roots_zmod_ppow_le (N : ℕ) (D : Polynomial (ZMod (p ^ (N + 1))))
    (hred : D.map (redHom (p := p) N) ≠ 0) :
    Nat.card {x : ZMod (p ^ (N + 1)) // D.eval x = 0} ≤ D.natDegree * p ^ N := by
  classical
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set Dbar : Polynomial (ZMod p) := D.map (redHom (p := p) N) with hDbar
  -- The field root set, as a `Finset` over `ZMod p`.
  set Rbar : Finset (ZMod p) := Dbar.roots.toFinset with hRbar
  -- The root set of `D` over the local ring, as a `Finset`.
  set Rset : Finset (ZMod (p ^ (N + 1))) := {x | D.eval x = 0} with hRset
  -- `redHom` maps the local root set into the field root set.
  have hmaps : ∀ x ∈ Rset, redHom (p := p) N x ∈ Rbar := by
    intro x hx
    rw [hRset, Finset.mem_filter] at hx
    have hroot : D.IsRoot x := hx.2
    have hroot' : Dbar.IsRoot (redHom (p := p) N x) := hroot.map
    rw [hRbar, Multiset.mem_toFinset, mem_roots hred]
    exact hroot'
  -- Fiberwise card decomposition of the local root set over `Rbar`.
  have hsum : #Rset = ∑ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- Each fiber-restricted root set is contained in the full `redHom`-fiber over `y`.
  have hfib_le : ∀ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} ≤ p ^ N := by
    intro y _
    calc #{x ∈ Rset | redHom (p := p) N x = y}
        ≤ #{x : ZMod (p ^ (N + 1)) | redHom (p := p) N x = y} := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨Finset.mem_univ x, hx.2⟩
      _ = p ^ N := fiber_finset_card (p := p) N y
  -- Bound `#Rbar ≤ Dbar.natDegree ≤ D.natDegree`.
  have hRbar_le : #Rbar ≤ D.natDegree := by
    calc #Rbar ≤ Multiset.card Dbar.roots := Multiset.toFinset_card_le _
      _ ≤ Dbar.natDegree := Dbar.card_roots'
      _ ≤ D.natDegree := natDegree_map_le
  -- Assemble.
  have hRset_le : #Rset ≤ D.natDegree * p ^ N := by
    calc #Rset = ∑ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} := hsum
      _ ≤ ∑ _y ∈ Rbar, p ^ N := Finset.sum_le_sum hfib_le
      _ = #Rbar * p ^ N := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ D.natDegree * p ^ N := by exact Nat.mul_le_mul_right _ hRbar_le
  -- Bridge `Nat.card` of the root subtype to `#Rset`.
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hRset_le

/-- **Sharper L-C2.** Identical to `card_roots_zmod_ppow_le` but the degree factor is the
**mod-`p` degree** `(D.map redHom).natDegree` (the residue-field degree, which can be strictly
smaller than `D.natDegree` over the local ring). This sharper form is what the multivariate
induction's leading-variable stratum needs: the per-slice root count must be charged to the
mod-`p` degree `k = degreeOf 0 D̄`, not to the (possibly larger) local-ring slice degree.

PROOF: the L-C2 proof already bounds `#Rset ≤ #Rbar · p^N` with `#Rbar ≤ Dbar.natDegree`; we simply
stop one step earlier (do not weaken `Dbar.natDegree` to `D.natDegree`). PROVED sorry-free. -/
theorem card_roots_zmod_ppow_le' (N : ℕ) (D : Polynomial (ZMod (p ^ (N + 1))))
    (hred : D.map (redHom (p := p) N) ≠ 0) :
    Nat.card {x : ZMod (p ^ (N + 1)) // D.eval x = 0}
      ≤ (D.map (redHom (p := p) N)).natDegree * p ^ N := by
  classical
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set Dbar : Polynomial (ZMod p) := D.map (redHom (p := p) N) with hDbar
  set Rbar : Finset (ZMod p) := Dbar.roots.toFinset with hRbar
  set Rset : Finset (ZMod (p ^ (N + 1))) := {x | D.eval x = 0} with hRset
  have hmaps : ∀ x ∈ Rset, redHom (p := p) N x ∈ Rbar := by
    intro x hx
    rw [hRset, Finset.mem_filter] at hx
    have hroot : D.IsRoot x := hx.2
    have hroot' : Dbar.IsRoot (redHom (p := p) N x) := hroot.map
    rw [hRbar, Multiset.mem_toFinset, mem_roots hred]
    exact hroot'
  have hsum : #Rset = ∑ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib_le : ∀ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} ≤ p ^ N := by
    intro y _
    calc #{x ∈ Rset | redHom (p := p) N x = y}
        ≤ #{x : ZMod (p ^ (N + 1)) | redHom (p := p) N x = y} := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨Finset.mem_univ x, hx.2⟩
      _ = p ^ N := fiber_finset_card (p := p) N y
  have hRbar_le : #Rbar ≤ Dbar.natDegree := by
    calc #Rbar ≤ Multiset.card Dbar.roots := Multiset.toFinset_card_le _
      _ ≤ Dbar.natDegree := Dbar.card_roots'
  have hRset_le : #Rset ≤ Dbar.natDegree * p ^ N := by
    calc #Rset = ∑ y ∈ Rbar, #{x ∈ Rset | redHom (p := p) N x = y} := hsum
      _ ≤ ∑ _y ∈ Rbar, p ^ N := Finset.sum_le_sum hfib_le
      _ = #Rbar * p ^ N := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Dbar.natDegree * p ^ N := by exact Nat.mul_le_mul_right _ hRbar_le
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hRset_le

/-- **Scaled field Schwartz–Zippel count over `ZMod p`** (the residue field). Derived from mathlib's
`MvPolynomial.schwartz_zippel_totalDegree` (which DOES apply, `ZMod p` being a field, hence a domain):
a nonzero `n`-variable polynomial over `ZMod p` vanishes on `R` tuples with `R · p ≤ totalDegree · p^n`.
The scaled (multiply-through-by-`p`) form avoids truncated `n-1` subtraction and is exactly what the
vanishing-leading-coefficient stratum of L-C1 needs. -/
theorem field_zero_count_le {n : ℕ} (c : MvPolynomial (Fin n) (ZMod p)) (hc : c ≠ 0) :
    (Nat.card {a : Fin n → ZMod p // MvPolynomial.eval a c = 0}) * p
      ≤ c.totalDegree * p ^ n := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (p := c) hc (Finset.univ : Finset (ZMod p))
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  rw [hcard, Fintype.piFinset_univ] at hsz
  set Rn : ℕ := #{f : Fin n → ZMod p | MvPolynomial.eval f c = 0} with hRn
  have hbridge : Nat.card {a : Fin n → ZMod p // MvPolynomial.eval a c = 0} = Rn := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hbridge]
  have hp0 : (0 : ℚ≥0) < (p : ℚ≥0) := by exact_mod_cast hp.out.pos
  have hpn0 : (0 : ℚ≥0) < (p : ℚ≥0) ^ n := pow_pos hp0 n
  rw [div_le_div_iff₀ hpn0 hp0] at hsz
  have : ((Rn * p : ℕ) : ℚ≥0) ≤ ((c.totalDegree * p ^ n : ℕ) : ℚ≥0) := by
    push_cast
    convert hsz using 2
  exact_mod_cast this

/-- **Power-fiber count.** The number of tail tuples `a : Fin m → ZMod (p^(N+1))` reducing mod `p`
to a fixed `b : Fin m → ZMod p` is `(p^N)^m` — the `m`-th power of the single-coordinate fiber count
**L-C3** (`castHom_fiber_card`), via `Equiv.subtypePiEquivPi` + `Nat.card_pi`. -/
theorem tail_fiber_card (N m : ℕ) (b : Fin m → ZMod p) :
    Nat.card {a : Fin m → ZMod (p ^ (N + 1)) // (fun i => redHom (p := p) N (a i)) = b}
      = (p ^ N) ^ m := by
  classical
  have hequiv : {a : Fin m → ZMod (p ^ (N + 1)) // (fun i => redHom (p := p) N (a i)) = b}
      ≃ {a : Fin m → ZMod (p ^ (N + 1)) // ∀ i, redHom (p := p) N (a i) = b i} := by
    apply Equiv.subtypeEquivRight
    intro a
    rw [funext_iff]
  rw [Nat.card_congr hequiv,
    Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i x => redHom (p := p) N x = b i)),
    Nat.card_pi, Finset.prod_congr rfl (fun i _ => castHom_fiber_card (p := p) N (b i)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Naturality of `finSuccEquiv` under coefficient reduction.** Peeling the first variable commutes
with reducing the coefficients mod `p`. -/
theorem finSuccEquiv_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (D : MvPolynomial (Fin (m + 1)) R) :
    MvPolynomial.finSuccEquiv S m (D.map f)
      = (MvPolynomial.finSuccEquiv R m D).map (MvPolynomial.map f) := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro mm
  rw [Polynomial.coeff_map, MvPolynomial.coeff_map, MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map]

/-- **Slice-reduction naturality.** Reducing the (frozen-tail) univariate slice
`Polynomial.map (eval a') (finSuccEquiv D)` mod `p` equals the slice of the reduced polynomial at the
reduced tail. This is the bridge that turns "the slice's mod-`p` reduction" into "the slice of `D̄`",
so its degree is the mod-`p` degree and its leading-coefficient vanishing matches the field stratum. -/
theorem slice_reduce_natural {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (D : MvPolynomial (Fin (m + 1)) R) (a' : Fin m → R) :
    (Polynomial.map (MvPolynomial.eval a') (MvPolynomial.finSuccEquiv R m D)).map f
      = Polynomial.map (MvPolynomial.eval (fun i => f (a' i)))
          (MvPolynomial.finSuccEquiv S m (D.map f)) := by
  rw [Polynomial.map_map, finSuccEquiv_map f m D, Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro g
  show f (MvPolynomial.eval a' g) = MvPolynomial.eval (fun i => f (a' i)) (MvPolynomial.map f g)
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp]
  rfl

/-- **Cross-ring `totalDegree` monotonicity under coefficient maps.** Reducing coefficients can only
drop monomials, so the total degree does not increase. (Mathlib has the same-ring version
`totalDegree_le_of_support_subset`; this is the cross-ring `map` analogue it lacks.) -/
theorem totalDegree_map_le {R S σ : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (D : MvPolynomial σ R) : (D.map f).totalDegree ≤ D.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset f D)

/-! ## L-C1 — the multivariate local-ring Schwartz–Zippel bound (the GAP core)

The genuine novel content: a multivariate Schwartz–Zippel root-density bound over the **non-domain**
local ring `ZMod (p^(N+1))`. Mathlib's `schwartz_zippel_sup_sum` is unusable (it requires
`[IsDomain R]`), so the bound is re-proved here by induction on the number of variables, mirroring the
mathlib proof skeleton but replacing its single "domain ⟹ `≤ deg` roots" step (`card_roots'` over a
domain) by the reduction-to-residue-field count `card_roots_zmod_ppow_le` (**L-C2**).

The bound, with `Q := p^(N+1)` the level-`N+1` residue cardinality: a polynomial `D` in `n` variables
over `ZMod Q` whose **mod-`p` reduction is nonzero** vanishes on at most
`D.totalDegree · Q^(n-1) · p^N` tuples — i.e. density `≤ D.totalDegree · p^N / Q = D.totalDegree / p`,
the static `q^{-1}` density that `M0`'s mod-`p` count lifts to.

The blueprint flags this as the HIGH-risk long pole (`L-C1 schwartz_zippel_local: ~180 LOC, HIGH`). -/

/-- Reduction of an `n`-variable polynomial mod `p` (each coefficient pushed to the residue field). -/
noncomputable def mvRed (N n : ℕ) (D : MvPolynomial (Fin n) (ZMod (p ^ (N + 1)))) :
    MvPolynomial (Fin n) (ZMod p) :=
  D.map (redHom (p := p) N)

/-- **L-C1 `schwartz_zippel_local`** (multivariate local-ring Schwartz–Zippel).

For a polynomial `D` in `n` variables over `ZMod (p^(N+1))` whose mod-`p` reduction `mvRed N n D` is
**nonzero**, the number of zero-tuples is bounded by `D.totalDegree · (p^(N+1))^(n-1) · p^N`.

**STATUS: PROVED sorry-free** (core-only `[propext, Classical.choice, Quot.sound]`). The proof:

* `n = 0` base case: a nonzero-mod-`p` constant is a unit in the local ring, so it has no zeros; the
  unique empty tuple does not vanish.
* `n = m+1` inductive step: peel the FIRST variable `X₀` via `MvPolynomial.finSuccEquiv`, turning `D`
  into a univariate polynomial `p'` over `MvPolynomial (Fin m) (ZMod (p^(N+1)))`. The tuple count
  fibers over the frozen tail `a'` (`Equiv.subtypeProdEquivSigmaSubtype` + `Nat.card_sigma`); for each
  tail the head-count is the root count of the univariate slice `s(a') = p'.map (eval a')`. Split tails
  by whether the **mod-`p` leading coefficient** `cbar := (finSuccEquiv (ZMod p) m D̄).leadingCoeff`
  vanishes at the reduced tail:
  - **unit-leading stratum** (`eval ā' cbar ≠ 0`): the reduced slice has degree exactly `k = degreeOf₀
    D̄`, so the sharper **L-C2** `card_roots_zmod_ppow_le'` gives `≤ k·p^N` heads (charged to the
    *mod-`p`* slice degree, the key over the non-domain);
  - **vanishing stratum** (`eval ā' cbar = 0`): the bad tails are the lifts of the field root set of
    `cbar`; their count is `(#field-roots)·(p^N)^m` by the power-fiber `tail_fiber_card`, and the field
    root count is bounded by `field_zero_count_le` (mathlib's `schwartz_zippel_totalDegree`, valid over
    the residue **field** `ZMod p` which IS a domain) — so this stratum does NOT use the local-ring `ih`.

  The two strata combine within the degree budget `k + cbar.totalDegree ≤ D.totalDegree`
  (`totalDegree_coeff_finSuccEquiv_add_le`), after cancelling one factor of `p` to reach the
  `D.totalDegree · (p^(N+1))^m · p^N` envelope (density `D.totalDegree/p`). The novelty vs mathlib is
  exactly that every "domain ⟹ ≤ deg roots" step is replaced by the reduce-to-residue-field count
  L-C2/L-C3, since `ZMod (p^(N+1))` is not a domain for `N ≥ 1`. -/
theorem schwartz_zippel_local (N : ℕ) :
    ∀ {n : ℕ} (D : MvPolynomial (Fin n) (ZMod (p ^ (N + 1)))),
      mvRed (p := p) N n D ≠ 0 →
      Nat.card {a : Fin n → ZMod (p ^ (N + 1)) // MvPolynomial.eval a D = 0}
        ≤ D.totalDegree * (p ^ (N + 1)) ^ (n - 1) * p ^ N := by
  classical
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  intro n
  induction n with
  | zero =>
    -- Base case: `D : MvPolynomial (Fin 0) (ZMod (p^(N+1)))` is a constant `C r`.
    intro D hD
    -- The empty tuple is the unique point; we show `eval a D ≠ 0`, so the root set is empty.
    have hcard0 : Nat.card {a : Fin 0 → ZMod (p ^ (N + 1)) // MvPolynomial.eval a D = 0} = 0 := by
      rw [Nat.card_eq_zero]
      left
      rw [isEmpty_subtype]
      intro a
      -- Over zero variables, `eval a D = D.coeff 0`, and `D = C (D.coeff 0)`.
      have hevalD : MvPolynomial.eval a D = D.coeff 0 := by
        conv_lhs => rw [D.eq_C_of_isEmpty]
        rw [MvPolynomial.eval_C]
      intro hzero
      -- `eval a D = 0` ⟹ `D.coeff 0 = 0` ⟹ `D = 0` ⟹ `mvRed N 0 D = 0`, contradicting `hD`.
      apply hD
      have hD0 : D = 0 := by
        rw [D.eq_C_of_isEmpty, ← hevalD, hzero, map_zero]
      rw [mvRed, hD0, map_zero]
    rw [hcard0]
    exact Nat.zero_le _
  | succ m ih =>
    -- Inductive step: peel the FIRST variable via `finSuccEquiv`, fiber the tuple count over the
    -- frozen tail `a'`, and split tails by whether the mod-`p` leading coefficient `cbar` vanishes
    -- at the reduced tail. The unit-leading stratum is charged to the mod-`p` slice degree `k` via
    -- the sharper L-C2 (`card_roots_zmod_ppow_le'`); the vanishing stratum is the lifted field root
    -- set of `cbar`, counted by the power-fiber `tail_fiber_card` × the field Schwartz–Zippel
    -- `field_zero_count_le`. The two strata combine within the degree budget `k + cbar.totalDegree
    -- ≤ D.totalDegree` (from `totalDegree_coeff_finSuccEquiv_add_le`). The induction hypothesis `ih`
    -- is NOT needed: the vanishing stratum is bounded by the *field* SZ over the residue field
    -- `ZMod p` (a domain), not by the local-ring IH.
    intro D hD
    set redH := redHom (p := p) N with hredH
    have hD' : D.map redH ≠ 0 := hD
    -- The reduced polynomial and its first-variable peeling.
    set Dbar : MvPolynomial (Fin (m + 1)) (ZMod p) := D.map redH with hDbar
    have hDbar0 : Dbar ≠ 0 := by rw [hDbar]; exact hD'
    set pbar' : Polynomial (MvPolynomial (Fin m) (ZMod p)) :=
      MvPolynomial.finSuccEquiv (ZMod p) m Dbar with hpbar'
    have hpbar'0 : pbar' ≠ 0 := by
      rw [hpbar']; exact EmbeddingLike.map_ne_zero_iff.2 hDbar0
    set k : ℕ := pbar'.natDegree with hk
    set cbar : MvPolynomial (Fin m) (ZMod p) := pbar'.leadingCoeff with hcbar
    have hcbar0 : cbar ≠ 0 := by rw [hcbar]; exact Polynomial.leadingCoeff_ne_zero.2 hpbar'0
    -- Total-degree budget: k + cbar.totalDegree ≤ D.totalDegree.
    have hdeg_budget : k + cbar.totalDegree ≤ D.totalDegree := by
      have hcoeff_ne : pbar'.coeff k ≠ 0 := by
        rw [hk]; rw [← Polynomial.leadingCoeff]; exact Polynomial.leadingCoeff_ne_zero.2 hpbar'0
      have h1 : (MvPolynomial.finSuccEquiv (ZMod p) m Dbar).coeff k ≠ 0 := by
        rw [← hpbar']; exact hcoeff_ne
      have h2 := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Dbar k h1
      have hcbar_eq : cbar = (MvPolynomial.finSuccEquiv (ZMod p) m Dbar).coeff k := by
        rw [hcbar, Polynomial.leadingCoeff, ← hk, ← hpbar']
      have hDbar_le : Dbar.totalDegree ≤ D.totalDegree := by
        rw [hDbar]; exact totalDegree_map_le redH D
      rw [hcbar_eq]
      calc k + MvPolynomial.totalDegree ((MvPolynomial.finSuccEquiv (ZMod p) m Dbar).coeff k)
          = MvPolynomial.totalDegree ((MvPolynomial.finSuccEquiv (ZMod p) m Dbar).coeff k) + k := by
            ring
        _ ≤ Dbar.totalDegree := h2
        _ ≤ D.totalDegree := hDbar_le
    -- The first-variable peeling of D over the local ring.
    set pp' : Polynomial (MvPolynomial (Fin m) (ZMod (p ^ (N + 1)))) :=
      MvPolynomial.finSuccEquiv (ZMod (p ^ (N + 1))) m D with hpp'
    -- Per-tail bound: for every tail a', the count of heads x with eval (cons x a') D = 0
    -- is ≤ k·p^N when the reduced leading coeff does NOT vanish at the reduced tail, else ≤ Q.
    have hper_tail : ∀ a' : Fin m → ZMod (p ^ (N + 1)),
        Nat.card {x : ZMod (p ^ (N + 1)) //
            MvPolynomial.eval (Fin.cons x a' : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0}
          ≤ (if MvPolynomial.eval (fun i => redH (a' i)) cbar = 0 then p ^ (N + 1)
              else k * p ^ N) := by
      intro a'
      set s : Polynomial (ZMod (p ^ (N + 1))) := Polynomial.map (MvPolynomial.eval a') pp' with hs
      have hroot_iff : ∀ x, MvPolynomial.eval (Fin.cons x a') D = 0 ↔ s.eval x = 0 := by
        intro x
        rw [hs, hpp', MvPolynomial.eval_eq_eval_mv_eval']
      have hcong : {x : ZMod (p ^ (N + 1)) // MvPolynomial.eval (Fin.cons x a') D = 0}
          ≃ {x : ZMod (p ^ (N + 1)) // s.eval x = 0} :=
        Equiv.subtypeEquivRight hroot_iff
      rw [Nat.card_congr hcong]
      have hsred : s.map redH
          = Polynomial.map (MvPolynomial.eval (fun i => redH (a' i))) pbar' := by
        rw [hs, hpp', hredH]
        rw [slice_reduce_natural (redHom (p := p) N) m D a']
      by_cases hgood : MvPolynomial.eval (fun i => redH (a' i)) cbar = 0
      · rw [if_pos hgood]
        calc Nat.card {x : ZMod (p ^ (N + 1)) // s.eval x = 0}
            ≤ Nat.card (ZMod (p ^ (N + 1))) :=
              Nat.card_le_card_of_injective _ Subtype.val_injective
          _ = p ^ (N + 1) := by rw [Nat.card_eq_fintype_card, ZMod.card]
      · rw [if_neg hgood]
        have hcoeffk : (s.map redH).coeff k = MvPolynomial.eval (fun i => redH (a' i)) cbar := by
          rw [hsred, Polynomial.coeff_map, hcbar, Polynomial.leadingCoeff, hk]
        have hslicered_ne : s.map redH ≠ 0 := by
          intro h0
          apply hgood
          rw [← hcoeffk, h0, Polynomial.coeff_zero]
        have hdeg_le : (s.map redH).natDegree ≤ k := by
          rw [hsred, hk]
          exact Polynomial.natDegree_map_le
        calc Nat.card {x : ZMod (p ^ (N + 1)) // s.eval x = 0}
            ≤ (s.map redH).natDegree * p ^ N := card_roots_zmod_ppow_le' N s hslicered_ne
          _ ≤ k * p ^ N := Nat.mul_le_mul_right _ hdeg_le
    -- Count as a sum over tails, via the cons-equiv to the product.
    set E : (Fin m → ZMod (p ^ (N + 1))) × ZMod (p ^ (N + 1)) ≃ (Fin (m + 1) → ZMod (p ^ (N + 1))) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ZMod (p ^ (N + 1)))) with hE
    have hEapp : ∀ z, E z = Fin.cons z.2 z.1 := by intro z; rfl
    have hcount_sum :
        Nat.card {a : Fin (m + 1) → ZMod (p ^ (N + 1)) // MvPolynomial.eval a D = 0}
          = ∑ a' : Fin m → ZMod (p ^ (N + 1)),
              Nat.card {x : ZMod (p ^ (N + 1)) //
                MvPolynomial.eval (Fin.cons x a' : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0} := by
      have heq1 : {a : Fin (m + 1) → ZMod (p ^ (N + 1)) // MvPolynomial.eval a D = 0}
          ≃ {z : (Fin m → ZMod (p ^ (N + 1))) × ZMod (p ^ (N + 1)) //
                MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0} := by
        refine Equiv.subtypeEquiv E.symm ?_
        intro a
        have : Fin.cons (E.symm a).2 (E.symm a).1 = a := by
          rw [← hEapp]; exact E.apply_symm_apply a
        rw [this]
      rw [Nat.card_congr heq1]
      rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        (fun (a' : Fin m → ZMod (p ^ (N + 1))) (x : ZMod (p ^ (N + 1))) =>
          MvPolynomial.eval (Fin.cons x a' : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0))]
      rw [Nat.card_sigma]
    set ρ : (Fin m → ZMod (p ^ (N + 1))) → (Fin m → ZMod p) :=
      fun a' i => redH (a' i) with hρ
    set Bad : Finset (Fin m → ZMod (p ^ (N + 1))) :=
      Finset.univ.filter (fun a' => MvPolynomial.eval (ρ a') cbar = 0) with hBad
    set Rfield : Finset (Fin m → ZMod p) :=
      Finset.univ.filter (fun b => MvPolynomial.eval b cbar = 0) with hRfield
    haveI : DecidableEq (Fin m → ZMod p) := Classical.decEq _
    -- nbad ≤ #Rfield · (p^N)^m, by fibering the bad tails over their reduction.
    have hbad_card : Bad.card ≤ Rfield.card * (p ^ N) ^ m := by
      have hmaps : ∀ a' ∈ Bad, ρ a' ∈ Rfield := by
        intro a' ha'
        rw [hBad, Finset.mem_filter] at ha'
        rw [hRfield, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ha'.2⟩
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      have hfib : ∀ b ∈ Rfield, (Bad.filter (fun a' => ρ a' = b)).card ≤ (p ^ N) ^ m := by
        intro b _
        have hsub : Bad.filter (fun a' => ρ a' = b)
            ⊆ Finset.univ.filter (fun a' => ρ a' = b) :=
          Finset.filter_subset_filter _ (Finset.subset_univ Bad)
        have hbridge : (Finset.univ.filter (fun a' => ρ a' = b)).card
            = Nat.card {a' : Fin m → ZMod (p ^ (N + 1)) // (fun i => redH (a' i)) = b} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        calc (Bad.filter (fun a' => ρ a' = b)).card
            ≤ (Finset.univ.filter (fun a' => ρ a' = b)).card := Finset.card_le_card hsub
          _ = Nat.card {a' : Fin m → ZMod (p ^ (N + 1)) // (fun i => redH (a' i)) = b} := hbridge
          _ = (p ^ N) ^ m := tail_fiber_card N m b
      calc (∑ b ∈ Rfield, (Bad.filter (fun a' => ρ a' = b)).card)
          ≤ ∑ _b ∈ Rfield, (p ^ N) ^ m := Finset.sum_le_sum hfib
        _ = Rfield.card * (p ^ N) ^ m := by rw [Finset.sum_const, smul_eq_mul]
    -- Field SZ on cbar: #Rfield · p ≤ cbar.totalDegree · p^m.
    have hfield : Rfield.card * p ≤ cbar.totalDegree * p ^ m := by
      have hbridge : Nat.card {b : Fin m → ZMod p // MvPolynomial.eval b cbar = 0}
          = Rfield.card := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hsz := field_zero_count_le cbar hcbar0
      rw [hbridge] at hsz
      exact hsz
    have hQm : (Finset.univ : Finset (Fin m → ZMod (p ^ (N + 1)))).card = (p ^ (N + 1)) ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    -- Sum bound: combine per-tail with the good/bad split.
    have hsum_le :
        (∑ a' : Fin m → ZMod (p ^ (N + 1)),
            Nat.card {x : ZMod (p ^ (N + 1)) //
              MvPolynomial.eval (Fin.cons x a' : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0})
          ≤ Bad.card * p ^ (N + 1) + (p ^ (N + 1)) ^ m * (k * p ^ N) := by
      have hsplit :
          (∑ a' : Fin m → ZMod (p ^ (N + 1)),
              (if MvPolynomial.eval (ρ a') cbar = 0 then p ^ (N + 1) else k * p ^ N))
            = Bad.card * p ^ (N + 1)
              + (Finset.univ.filter
                  (fun a' => ¬ MvPolynomial.eval (ρ a') cbar = 0)).card * (k * p ^ N) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hBad]
      calc (∑ a' : Fin m → ZMod (p ^ (N + 1)),
              Nat.card {x : ZMod (p ^ (N + 1)) //
                MvPolynomial.eval (Fin.cons x a' : Fin (m + 1) → ZMod (p ^ (N + 1))) D = 0})
          ≤ ∑ a' : Fin m → ZMod (p ^ (N + 1)),
              (if MvPolynomial.eval (ρ a') cbar = 0 then p ^ (N + 1) else k * p ^ N) :=
            Finset.sum_le_sum (fun a' _ => hper_tail a')
        _ = Bad.card * p ^ (N + 1)
              + (Finset.univ.filter
                  (fun a' => ¬ MvPolynomial.eval (ρ a') cbar = 0)).card * (k * p ^ N) := hsplit
        _ ≤ Bad.card * p ^ (N + 1) + (p ^ (N + 1)) ^ m * (k * p ^ N) := by
            apply Nat.add_le_add_left
            apply Nat.mul_le_mul_right
            rw [← hQm]
            exact Finset.card_filter_le _ _
    -- Final arithmetic: cancel one factor of p; close within the degree budget.
    rw [hcount_sum]
    refine le_trans hsum_le ?_
    have hpm1 : m + 1 - 1 = m := rfl
    rw [hpm1]
    have hp0 : 0 < p := hp.out.pos
    have hbadterm : Bad.card * p ^ (N + 1)
        ≤ cbar.totalDegree * (p ^ (N + 1)) ^ m * p ^ N := by
      apply Nat.le_of_mul_le_mul_right _ hp0
      calc Bad.card * p ^ (N + 1) * p
          ≤ (Rfield.card * (p ^ N) ^ m) * p ^ (N + 1) * p :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbad_card)
        _ = (Rfield.card * p) * ((p ^ N) ^ m * p ^ (N + 1)) := by ring
        _ ≤ (cbar.totalDegree * p ^ m) * ((p ^ N) ^ m * p ^ (N + 1)) :=
            Nat.mul_le_mul_right _ hfield
        _ = cbar.totalDegree * (p ^ (N + 1)) ^ m * p ^ N * p := by
            rw [pow_succ p N, mul_pow]; ring
    have hgoodterm : (p ^ (N + 1)) ^ m * (k * p ^ N)
        = k * (p ^ (N + 1)) ^ m * p ^ N := by ring
    calc Bad.card * p ^ (N + 1) + (p ^ (N + 1)) ^ m * (k * p ^ N)
        ≤ cbar.totalDegree * (p ^ (N + 1)) ^ m * p ^ N
          + k * (p ^ (N + 1)) ^ m * p ^ N := by
          rw [hgoodterm]; exact Nat.add_le_add_right hbadterm _
      _ = (cbar.totalDegree + k) * (p ^ (N + 1)) ^ m * p ^ N := by ring
      _ ≤ D.totalDegree * (p ^ (N + 1)) ^ m * p ^ N := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_right
          omega

end LeanUrat.OM.SchwartzZippel
