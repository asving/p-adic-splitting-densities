/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0Classify
import LeanUrat.OM.Order0Fiber
import LeanUrat.OM.Order0Count
import LeanUrat.OM.RealInstance
import LeanUrat.OM.SchwartzZippel

/-!
# Order0Alpha — α (the count): `h_node0` discharged, `montes_order0` unconditional
(`notes/HNODE0_BLUEPRINT.md` §5 "α", with the DIRECT-reduction route change)

**The package.** The banked γ5 (`Order0Classify.classify_eq_sepShape`) and γ6
(`Order0Fiber.classify_eq_sepShape_only_if`) gates are combined into the FIBER CHARACTERIZATION
(`classify_eq_sepShape_iff`): the level-`N` classifier fiber of `sepShape n lam` is EXACTLY the
preimage of the level-1 separable stratum `sepStratum (ZMod p) n lam` (β's counting stratum,
`Order0Count`) under the DIRECT mod-`p` reduction
`red f := (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))` — no `ZMod (p^1) ≃ ZMod p`
transport anywhere.

Then the count chain:
* `card_red_fiber` — every monic degree-`n` reduction fiber has EXACTLY `p^((N-1)·n)` elements
  (coefficientwise: a monic-box element is its `n` low coefficients, and each coefficient fiber of
  `ZMod (p^N) ↠ ZMod p` has `p^(N-1)` elements — the banked `SchwartzZippel.tail_fiber_card`).
* `card_classify_fiber` — the classifier fiber count is `(∏_d C(avail_d, k_d)) · p^((N-1)·n)`
  (sigma-decompose over the stratum, `card_sepStratum` counts the base).
* `stratumCount_sepShape` — the same, as the ℚ-cast `M8.stratumCount (M9.rawCount n)` value at the
  pinned prime `M9.realP`.
* `rootCount_sepShape_eval` — the EVAL identity: the capstone's per-shape coefficient
  `rootCount (sepShape n lam) q` at `q = #F` is `(∏_d C(avail_d(F), k_d)) / q^n` (unfold
  `cellsOfShapeWF_sepShape`; `nodeDelta = 1`; `newtonExponent (flatFace n) = 0`; the choice
  polynomial evaluates through `availPoly` → `necklaceQ` → `avail` and the reversed
  `cast_choose_eq_prod_range_div`).
* `h_node0_proved` — for `N ≥ 1` the normalized count is the CONSTANT `(∏_d C(avail_d, k_d))/p^n`
  (`p^{(N-1)n}/p^{nN} = p^{-n}`), which by the eval identity IS `rootCount (sepShape n lam) realP`;
  the `h_node0` limit is an eventually-constant `Tendsto`.
* `montes_order0_unconditional` — `montes_order0` fired with the proved `h_node0`: the Phase-A
  capstone with NO counting hypothesis left.

All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.Order0

open LeanUrat LeanUrat.MontesAxiom Polynomial

/-! ## 1. The fiber characterization (γ5 + γ6 as an iff, on the DIRECT reduction) -/

/-- **The fiber characterization** (`HNODE0_BLUEPRINT` §5 α, the level-1 decidedness identity).
For `0 < N`, `0 < n`: the genuine classifier sends `f` to the separable leaf shape
`sepShape n lam` IFF the direct mod-`p` reduction of `f` lies on the level-1 separable stratum
`sepStratum (ZMod p) n lam` (monic, degree `n`, squarefree, `X ∤`, pattern `lam`). Forward is γ6
(`classify_eq_sepShape_only_if`) plus the coefficient-read bridges (`Monic.map`,
`Monic.natDegree_map`, `X_dvd_iff` + `coeff_map` + `zmodValuation_zero_iff_castHom_ne_zero`);
backward is γ5 (`classify_eq_sepShape`) with `hunit` read off `X ∤ red f`. -/
theorem classify_eq_sepShape_iff (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (lam : Nat.Partition n) (f : QuotientBox.monicBox p N n) :
    B.classify p n N f = sepShape n lam
      ↔ (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))
          ∈ sepStratum (ZMod p) n lam := by
  constructor
  · intro h
    obtain ⟨hunit, hsq, hpat⟩ := classify_eq_sepShape_only_if p n N hN hn lam f h
    have hmon : ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))).Monic :=
      (f.2.1).map _
    have hdeg : ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))).natDegree = n := by
      rw [Polynomial.Monic.natDegree_map f.2.1]
      exact f.2.2
    have hX : ¬ (X : (ZMod p)[X]) ∣ (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) := by
      intro hdvd
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_map] at hdvd
      exact (zmodValuation_zero_iff_castHom_ne_zero p N hN _).mp hunit hdvd
    exact ⟨hmon, hdeg, hsq, hX, hpat⟩
  · rintro ⟨hmon, hdeg, hsq, hX, hpat⟩
    have hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0 := by
      rw [zmodValuation_zero_iff_castHom_ne_zero p N hN]
      intro h0
      apply hX
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_map]
      exact h0
    exact classify_eq_sepShape p n N hN hn f hunit hsq lam hpat

/-! ## 2. The reduction fiber count -/

/-- The generic monic build `X^n + Σ_{i<n} C(c i)·X^i` — a monic-box element from its low
coefficient read `c`. -/
noncomputable def buildPoly {R : Type*} [Semiring R] (n : ℕ) (c : ℕ → R) : R[X] :=
  X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * X ^ i

theorem buildPoly_coeff_lt {R : Type*} [Semiring R] (n : ℕ) (c : ℕ → R) {k : ℕ} (hk : k < n) :
    (buildPoly n c).coeff k = c k := by
  unfold buildPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range n) => by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])]
  rw [if_neg (by omega : ¬ k = n)]
  have hite : ∀ i ∈ Finset.range n,
      c i * (if k = i then (1 : R) else 0) = if k = i then c i else 0 := by
    intro i _
    by_cases h : k = i
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk), zero_add]

theorem buildPoly_congr {R : Type*} [Semiring R] (n : ℕ) {c c' : ℕ → R}
    (h : ∀ i < n, c i = c' i) : buildPoly n c = buildPoly n c' := by
  unfold buildPoly
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem buildPoly_monic {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : ℕ → R) :
    (buildPoly n c).Monic := by
  apply Polynomial.monic_X_pow_add
  rw [Finset.sum_range (fun i => Polynomial.C (c i) * X ^ i)]
  exact Polynomial.degree_sum_fin_lt (fun i => c ↑i)

theorem buildPoly_natDegree {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : ℕ → R) :
    (buildPoly n c).natDegree = n := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  unfold buildPoly
  have hlt : (∑ i ∈ Finset.range n, Polynomial.C (c i) * X ^ i).degree
      < (X ^ n : R[X]).degree := by
    rw [Polynomial.degree_X_pow, Finset.sum_range (fun i => Polynomial.C (c i) * X ^ i)]
    exact Polynomial.degree_sum_fin_lt (fun i => c ↑i)
  rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]

theorem buildPoly_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (n : ℕ) (c : ℕ → R) :
    (buildPoly n c).map φ = buildPoly n (fun i => φ (c i)) := by
  unfold buildPoly
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

/-- **The monic decomposition**: a monic degree-`n` polynomial IS the build of its low
coefficients (`as_sum_range'` + the monic leading coefficient). -/
theorem buildPoly_decomp {R : Type*} [Semiring R] {g : R[X]} {n : ℕ} (hg : g.Monic)
    (hd : g.natDegree = n) : buildPoly n (fun i => g.coeff i) = g := by
  have h := Polynomial.as_sum_range' g (n + 1) (by omega)
  rw [Finset.sum_range_succ] at h
  have hcn : g.coeff n = 1 := by
    rw [← hd]
    exact hg.coeff_natDegree
  rw [hcn, ← Polynomial.X_pow_eq_monomial] at h
  unfold buildPoly
  conv_rhs => rw [h]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial

/-- **The reduction fiber count** (`HNODE0_BLUEPRINT` §5 α, the `p^{n(N−1)}`-fold cylinder). For
`0 < N` and monic degree-`n` `g` over `ZMod p`, the direct-reduction fiber over `g` inside the
level-`N` monic box has EXACTLY `p^((N-1)·n)` elements: a box element is its `n` low coefficients
(`buildPoly` bijection), and each coefficient ranges over a `castHom`-fiber of size `p^(N-1)`
(banked `SchwartzZippel.tail_fiber_card`). -/
theorem card_red_fiber (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    {g : (ZMod p)[X]} (hg : g.Monic) (hgd : g.natDegree = n) :
    Nat.card {f : QuotientBox.monicBox p N n //
        (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) = g}
      = p ^ ((N - 1) * n) := by
  rcases N with _ | M
  · omega
  · haveI : Fact (1 < p ^ (M + 1)) :=
      ⟨Nat.one_lt_pow (Nat.succ_ne_zero M) (Fact.out (p := p.Prime)).one_lt⟩
    have hhom : ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)
        = SchwartzZippel.redHom (p := p) M := rfl
    have E : {f : QuotientBox.monicBox p (M + 1) n //
        (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) = g}
        ≃ {a : Fin n → ZMod (p ^ (M + 1)) //
            (fun i => SchwartzZippel.redHom (p := p) M (a i)) = fun i : Fin n => g.coeff i} :=
      { toFun := fun f => ⟨fun i => (f.1.1).coeff i, by
          funext i
          show SchwartzZippel.redHom (p := p) M ((f.1.1).coeff i) = g.coeff i
          rw [← hhom, ← Polynomial.coeff_map, f.2]⟩
        invFun := fun a => ⟨⟨buildPoly n (fun k => if h : k < n then a.1 ⟨k, h⟩ else 0),
            buildPoly_monic n _, buildPoly_natDegree n _⟩, by
          rw [buildPoly_map]
          have hcg : ∀ i < n,
              ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)
                ((fun k => if h : k < n then a.1 ⟨k, h⟩ else 0) i)
              = (fun i => g.coeff i) i := by
            intro i hi
            show ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)
                (if h : i < n then a.1 ⟨i, h⟩ else 0) = g.coeff i
            rw [dif_pos hi, hhom]
            exact congrFun a.2 ⟨i, hi⟩
          rw [buildPoly_congr n hcg]
          exact buildPoly_decomp hg hgd⟩
        left_inv := fun f => Subtype.ext (Subtype.ext (by
          refine (buildPoly_congr n (fun i hi => ?_)).trans
            (buildPoly_decomp f.1.2.1 f.1.2.2)
          rw [dif_pos hi]))
        right_inv := fun a => Subtype.ext (by
          funext i
          show (buildPoly n (fun k => if h : k < n then a.1 ⟨k, h⟩ else 0)).coeff ↑i = a.1 i
          rw [buildPoly_coeff_lt n _ i.isLt, dif_pos i.isLt, Fin.eta]) }
    rw [Nat.card_congr E,
      SchwartzZippel.tail_fiber_card (p := p) M n (fun i : Fin n => g.coeff i), ← pow_mul]
    congr 1

/-! ## 3. The stratum count -/

/-- **The classifier fiber count** (`HNODE0_BLUEPRINT` §5 α, the stratum count in ℕ). For
`0 < N`, `0 < n`: the level-`N` fiber of `sepShape n lam` has EXACTLY
`(∏_d C(avail_d, k_d)) · p^((N-1)·n)` elements — sigma-decompose the fiber over the level-1
stratum (`classify_eq_sepShape_iff` partitions, `card_red_fiber` counts each reduction fiber,
`card_sepStratum` counts the base). -/
theorem card_classify_fiber (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (lam : Nat.Partition n) :
    Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = sepShape n lam}
      = (∏ d ∈ lam.parts.toFinset, (avail (ZMod p) d).choose (lam.parts.count d))
          * p ^ ((N - 1) * n) := by
  classical
  have hfin : (sepStratum (ZMod p) n lam).Finite :=
    (finite_monicDegree (ZMod p) n).subset (by
      rintro g ⟨hmon, hdeg, -, -, -⟩
      exact ⟨hmon, hdeg⟩)
  haveI : Fintype (sepStratum (ZMod p) n lam) := hfin.fintype
  have e1 : {f : QuotientBox.monicBox p N n // B.classify p n N f = sepShape n lam}
      ≃ {f : QuotientBox.monicBox p N n //
          (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))
            ∈ sepStratum (ZMod p) n lam} :=
    Equiv.subtypeEquivRight fun f => classify_eq_sepShape_iff p n N hN hn lam f
  let F0 : {f : QuotientBox.monicBox p N n //
      (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))
        ∈ sepStratum (ZMod p) n lam} → (sepStratum (ZMod p) n lam) :=
    fun f => ⟨(f.1.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)), f.2⟩
  have hper : ∀ g : sepStratum (ZMod p) n lam,
      Nat.card {x // F0 x = g} = p ^ ((N - 1) * n) := by
    intro g
    have e3 : {x // F0 x = g} ≃ {f : QuotientBox.monicBox p N n //
        (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) = g.1} :=
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, by rw [y.2]; exact g.2⟩, Subtype.ext y.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
    rw [Nat.card_congr e3]
    exact card_red_fiber p n N hN g.2.1 g.2.2.1
  rw [Nat.card_congr e1, Nat.card_congr (Equiv.sigmaFiberEquiv F0).symm, Nat.card_sigma,
    Finset.sum_congr rfl (fun g _ => hper g), Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_sepStratum]

/-- **The stratum count at the pinned prime** (`M8.stratumCount`-typed form of
`card_classify_fiber`): the ℚ-cast level-`N` count of the `sepShape n lam` stratum in the real
instance is `(∏_d C(avail_d, k_d)) · realP^((N-1)·n)`. -/
theorem stratumCount_sepShape (n : ℕ) (hn : 0 < n) (lam : Nat.Partition n) (N : ℕ) (hN : 0 < N) :
    M8.stratumCount (M9.rawCount n) (sepShape n lam) N
      = (((∏ d ∈ lam.parts.toFinset,
            (avail (ZMod M9.realP) d).choose (lam.parts.count d))
          * M9.realP ^ ((N - 1) * n) : ℕ) : ℚ) := by
  show ((M9.rawCount n (sepShape n lam) N : ℕ) : ℚ) = _
  rw [show M9.rawCount n (sepShape n lam) N
      = Nat.card {f : QuotientBox.monicBox M9.realP N n //
          B.classify M9.realP n N f = sepShape n lam} from rfl,
    card_classify_fiber M9.realP n N hN hn lam]

/-! ## 4. The eval identity: `rootCount (sepShape n lam) q = (∏_d C(avail_d, k_d)) / q^n` -/

/-- The flat face has Newton exponent `0`: every ceiling height along the slope-`0` side is
`⌈0 + 0·k⌉ = 0`. -/
theorem newtonExponent_flatFace (n : ℕ) : L4.newtonExponent (flatFace n) = 0 := by
  unfold L4.newtonExponent
  refine Finset.sum_eq_zero fun i _ => ?_
  show M7.sideCeilHeight (flatSide n) i.val = 0
  unfold M7.sideCeilHeight
  rw [show (flatSide n).slope = 0 from flatSide_slope n,
    show ((flatSide n).v₀ : ℚ) = 0 from by norm_num [flatSide]]
  norm_num

/-- The `dS`-list of the `sepShape` payload is the sorted parts list. -/
theorem dSList_sepShape (n : ℕ) (lam : Nat.Partition n) :
    dSList (M7.cellsOfShapeWF (sepShape n lam)) = lam.parts.sort (· ≤ ·) := by
  rw [cellsOfShapeWF_sepShape]
  unfold dSList
  rw [List.map_map]
  exact (List.map_congr_left fun d _ => rfl).trans (List.map_id _)

/-- The `sepShape` payload's residue-extension degree slot is `1` (every cell carries `δ = 1`;
the empty payload defaults to `1`). -/
theorem nodeDelta_sepShape (n : ℕ) (lam : Nat.Partition n) :
    nodeDelta (M7.cellsOfShapeWF (sepShape n lam)) = 1 := by
  rw [cellsOfShapeWF_sepShape]
  cases lam.parts.sort (· ≤ ·) with
  | nil => rfl
  | cons a l => rfl

/-- The `sepShape` volume exponent is `n`: flat-face Newton exponent `0` plus one `q`-digit per
residual coefficient (`Σ dS = Σ lam.parts = n`). -/
theorem nodeVolumeExp_sepShape (n : ℕ) (hn : 0 < n) (lam : Nat.Partition n) :
    nodeVolumeExp (M7.cellsOfShapeWF (sepShape n lam)) = n := by
  have hsum : (lam.parts.sort (· ≤ ·)).sum = n := by
    rw [← Multiset.sum_coe, Multiset.sort_eq]
    exact lam.parts_sum
  rw [cellsOfShapeWF_sepShape]
  cases hl : lam.parts.sort (· ≤ ·) with
  | nil =>
      exfalso
      rw [hl] at hsum
      simp only [List.sum_nil] at hsum
      omega
  | cons a l =>
      rw [hl] at hsum
      have hds : dSList ((a :: l).map
          (fun d => (⟨d, 1, flatFace n, []⟩ : CountCell))) = a :: l := by
        unfold dSList
        rw [List.map_map]
        exact (List.map_congr_left fun d _ => rfl).trans (List.map_id _)
      show L4.newtonExponent (flatFace n)
          + (dSList ((a :: l).map (fun d => (⟨d, 1, flatFace n, []⟩ : CountCell)))).sum = n
      rw [hds, newtonExponent_flatFace, hsum]
      omega

/-- **The necklace-polynomial eval bridge**: `necklacePoly d` evaluated at any natural `q` is the
abstract necklace count `Necklace.necklaceQ d q` (both are `(Σ_{e∣d} μ(e)·q^{d/e})/d` in ℚ). -/
theorem necklacePoly_eval (d q : ℕ) :
    (necklacePoly d).eval (q : ℚ) = Necklace.necklaceQ d q := by
  unfold necklacePoly Necklace.necklaceQ Necklace.necklaceSum
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ d.divisors) => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X])]
  push_cast
  ring

/-- **The pool-polynomial eval bridge**: `availPoly d` evaluated at the field cardinality is the
ℕ-valued pool size `avail F d` (the `q − 1` linear pool at `d = 1`; `necklaceQ = #Irr_d` via the
banked β2a cross-tie for `d ≥ 2`). -/
theorem availPoly_eval (F : Type*) [Field F] [Finite F] (d : ℕ) (hd : 1 ≤ d) :
    (availPoly d).eval ((Nat.card F : ℚ)) = (avail F d : ℚ) := by
  rcases eq_or_ne d 1 with rfl | hne
  · unfold availPoly
    rw [if_pos rfl, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, avail_one]
    have h1 : 1 ≤ Nat.card F := Nat.card_pos
    rw [Nat.cast_sub h1, Nat.cast_one]
  · unfold availPoly
    rw [if_neg hne, necklacePoly_eval, necklaceQ_eq_card F d hd, avail_of_ne_one F hne]

/-- **The per-degree choice factor eval**: `(1/k!)·ff(availPoly d, k)` at `q = #F` is the binomial
`C(avail F d, k)` (the reversed `cast_choose_eq_prod_range_div`). -/
theorem choiceFactor_eval (F : Type*) [Field F] [Finite F] (d k : ℕ) (hd : 1 ≤ d) :
    (Polynomial.C (1 / (Nat.factorial k : ℚ)) * ffPoly (availPoly d) k).eval ((Nat.card F : ℚ))
      = ((avail F d).choose k : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  unfold ffPoly
  rw [Polynomial.eval_prod]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.range k) => by
    rw [Polynomial.eval_sub, Polynomial.eval_C, availPoly_eval F d hd])]
  rw [one_div_mul_eq_div]
  exact (cast_choose_eq_prod_range_div _ _).symm

/-- **The choice-count polynomial eval on the `sepShape` payload**: the ambient-variable choice
polynomial at `q = #F` is `∏_d C(avail F d, k_d)`, `k_d = lam.parts.count d`. -/
theorem nodeChoicePolyQ_sepShape_eval (F : Type*) [Field F] [Finite F]
    (n : ℕ) (lam : Nat.Partition n) :
    (nodeChoicePolyQ (M7.cellsOfShapeWF (sepShape n lam))).eval ((Nat.card F : ℚ))
      = ∏ d ∈ lam.parts.toFinset, ((avail F d).choose (lam.parts.count d) : ℚ) := by
  unfold nodeChoicePolyQ
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
    nodeDelta_sepShape n lam, pow_one]
  unfold nodeChoicePoly
  rw [dSList_sepShape]
  have htf : (lam.parts.sort (· ≤ ·)).toFinset = lam.parts.toFinset := by
    apply Finset.ext
    intro a
    rw [List.mem_toFinset, Multiset.mem_toFinset, Multiset.mem_sort]
  rw [Polynomial.eval_prod, htf]
  refine Finset.prod_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := lam.parts_pos (Multiset.mem_toFinset.mp hd)
  have hcount : (lam.parts.sort (· ≤ ·)).count d = lam.parts.count d := by
    rw [← Multiset.coe_count, Multiset.sort_eq]
  rw [hcount]
  exact choiceFactor_eval F d (lam.parts.count d) hd1

/-- **The eval identity** (`HNODE0_BLUEPRINT` §5 assembly): the capstone's per-shape coefficient
on the separable leaf shape, at `q = #F`, is `(∏_d C(avail F d, k_d)) / q^n` — the childless
product is `1`, the choice polynomial evaluates by `nodeChoicePolyQ_sepShape_eval`, and the volume
exponent is `newtonExponent (flatFace n) + n = n`. -/
theorem rootCount_sepShape_eval (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 0 < n)
    (lam : Nat.Partition n) (q : ℕ) (hq : Nat.card F = q) :
    rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend (sepShape n lam) q
      = (∏ d ∈ lam.parts.toFinset, ((avail F d).choose (lam.parts.count d) : ℚ))
          / (q : ℚ) ^ n := by
  subst hq
  rw [rootCount]
  have h1 : ((M7.cellsOfShapeWF (sepShape n lam)).map (fun c =>
      (c.children.map (fun ch =>
        clusterCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend ch
          (Nat.card F))).prod)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [sepShape_leaf n lam c hc]
    simp
  rw [h1, mul_one, nodeChoicePolyQ_sepShape_eval F n lam, nodeVolumeExp_sepShape n hn lam,
    ← div_eq_mul_inv]

/-! ## 5. `h_node0` discharged at the real instance -/

/-- **`h_node0`, PROVED** (`HNODE0_BLUEPRINT` §5 α, the constant-sequence limit). For every menu
shape `T ∈ sepShapesOf n σ` (with `0 < n`), the normalized real stratum count
`M8.stratumCount (M9.rawCount n) T N / realP^(nN)` is, for `N ≥ 1`, the CONSTANT
`(∏_d C(avail_d, k_d))/realP^n` (`stratumCount_sepShape` + `p^{(N-1)n}/p^{nN} = p^{-n}`), which is
exactly `rootCount T realP` (`rootCount_sepShape_eval` at `F = ZMod realP`,
`Nat.card (ZMod realP) = realP`). The `Tendsto` is an eventually-constant limit. -/
theorem h_node0_proved (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    ∀ T ∈ sepShapesOf n σ,
      Filter.Tendsto
        (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP)) := by
  intro T hT
  rw [sepShapesOf, Finset.mem_image] at hT
  obtain ⟨lam, -, rfl⟩ := hT
  have hP0 : (M9.realP : ℚ) ≠ 0 := by
    unfold M9.realP
    norm_num
  rw [rootCount_sepShape_eval (ZMod M9.realP) n hn lam M9.realP (Nat.card_zmod M9.realP)]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  rw [stratumCount_sepShape n hn lam N (by omega)]
  rcases N with _ | M
  · omega
  · have hexp : (M9.realP : ℚ) ^ (n * (M + 1))
        = (M9.realP : ℚ) ^ ((M + 1 - 1) * n) * (M9.realP : ℚ) ^ n := by
      rw [← pow_add]
      congr 1
      have hMn : M + 1 - 1 = M := rfl
      rw [hMn]
      ring
    rw [hexp]
    push_cast
    have hne1 : (M9.realP : ℚ) ^ ((M + 1 - 1) * n) ≠ 0 := pow_ne_zero _ hP0
    have hne2 : (M9.realP : ℚ) ^ n ≠ 0 := pow_ne_zero _ hP0
    field_simp

/-! ## 6. The unconditional capstone -/

/-- **`montes_order0`, UNCONDITIONAL** (the Phase-A capstone with `h_node0` DISCHARGED). For every
degree `n > 0` and factorization type `σ`: the order-0 separable-stratum density function is a
uniform rational function of `q'`, AND the real normalized counts converge to its value at
`realP` — no counting hypothesis left; the per-shape limit is `h_node0_proved`. -/
theorem montes_order0_unconditional (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf n σ,
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) :=
  montes_order0 n σ (h_node0_proved n hn σ)

/-! ## 7. NON-VACUITY (V1 reversal — the mandatory acceptance gate, `VACUITY_SIGMA_BLUEPRINT` §A8.1)

The genuine order-0 capstone `montes_order0_unconditional` above is proved for the corrected
`Order0.rootCount` per-shape coefficients over the σ-keyed genuine menu `sepShapesOf` — a DIFFERENT
object from the degenerate `M9.shapeMenu` (`leafOMTypeOfSize`, `Rr := 0`, empty cells) that makes the
old `M9.montes_unconditional` certify the constant `0`. To DEMONSTRATE (machine-checked, not by
inspection) that this genuine capstone is NOT itself vacuous, we exhibit a concrete factorization
type whose certified density is STRICTLY POSITIVE.

The witness: `n = 2`, the INERT type `σ = unramType 2 (indiscrete 2)` (one irreducible degree-2
factor). Its single menu shape `sepShape 2 (indiscrete 2)` has, over `F₂`, exactly one monic
irreducible quadratic (`avail (ZMod 2) 2 = #{x²+x+1} = 1`), so the corrected coefficient is
`C(1,1)/2² = 1/4`. This is the audit's "1/4 gate", now tied to the capstone's certified value. -/

/-- The necklace value `M₂(q) = (q² − q)/2` (the degree-2 irreducible count over a `q`-element
field, as a polynomial identity in `q`). -/
theorem necklaceQ_two (q : ℕ) : Necklace.necklaceQ 2 q = ((q : ℚ) ^ 2 - q) / 2 := by
  unfold Necklace.necklaceQ Necklace.necklaceSum
  rw [Nat.Prime.divisors (by norm_num : Nat.Prime 2),
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  simp only [ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)]
  push_cast
  norm_num
  ring

/-- Over `F₂` there is exactly ONE monic irreducible quadratic (`x²+x+1`): `avail (ZMod 2) 2 = 1`. -/
theorem avail_zmod2_two : avail (ZMod 2) 2 = 1 := by
  rw [avail_of_ne_one _ (by norm_num)]
  have h : Necklace.necklaceQ 2 (Nat.card (ZMod 2))
      = (Nat.card (L3.monicIrreducibleDegree (ZMod 2) 2) : ℚ) :=
    necklaceQ_eq_card (ZMod 2) 2 (by norm_num)
  rw [Nat.card_zmod, necklaceQ_two] at h
  norm_num at h
  exact_mod_cast h.symm

/-- **NON-VACUITY GATE (V1 reversal), the inert `n = 2` order-0 stratum.** The certified per-shape
coefficient of the inert (single degree-2 factor) order-0 separable leaf shape at the real prime
`realP = 2` is `1/4` — NONZERO. This is the machine-checked witness that the genuine order-0 capstone
`montes_order0_unconditional` is NOT the vacuous constant-`0` density: the inert factorization type of
degree 2 has certified density `1/4` at `q = 2`. -/
theorem gate_rootCount_inert2 :
    rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
      (sepShape 2 (Nat.Partition.indiscrete 2)) M9.realP = 1 / 4 := by
  rw [rootCount_sepShape_eval (ZMod 2) 2 (by norm_num) (Nat.Partition.indiscrete 2) M9.realP
    (by rw [Nat.card_zmod]; rfl)]
  have hparts : (Nat.Partition.indiscrete 2).parts = {2} :=
    Nat.Partition.indiscrete_parts (by norm_num)
  rw [hparts]
  simp only [Multiset.toFinset_singleton, Finset.prod_singleton, Multiset.count_singleton_self]
  rw [avail_zmod2_two]
  norm_num [M9.realP]

/-- Every separable menu shape has NONNEGATIVE `rootCount` at `realP` (it is
`(∏_d C(avail_d, k_d))/realP^n`, a quotient of nonnegatives), via `rootCount_sepShape_eval` at
`F = ZMod M9.realP`. -/
theorem rootCount_sepShape_nonneg (n : ℕ) (hn : 0 < n) (lam : Nat.Partition n) :
    0 ≤ rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
      (sepShape n lam) M9.realP := by
  rw [rootCount_sepShape_eval (ZMod M9.realP) n hn lam M9.realP (Nat.card_zmod M9.realP)]
  apply div_nonneg
  · exact Finset.prod_nonneg (fun d _ => by positivity)
  · positivity

/-- **The inert degree-2 shape is IN its own σ-keyed menu** — the menu `sepShapesOf 2 (unramType 2
(indiscrete 2))` is genuinely non-empty. -/
theorem inert2_mem_menu :
    sepShape 2 (Nat.Partition.indiscrete 2)
      ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)) := by
  rw [sepShapesOf, Finset.mem_image]
  exact ⟨Nat.Partition.indiscrete 2, by simp [Finset.mem_filter], rfl⟩

/-- **THE CAPSTONE NON-VACUITY THEOREM (V1 reversal, certified value).** The genuine order-0 capstone
`montes_order0_unconditional` at `n = 2` and the INERT factorization type
`σ = unramType 2 (indiscrete 2)` certifies a density function whose value at the real prime
`realP = 2` is STRICTLY POSITIVE — NOT the vacuous constant `0`. Concretely: the existential rational
`num/den` the capstone produces evaluates (via its own `∀ q'` clause at `q' = realP`) to the order-0
separable menu sum `∑_{T ∈ sepShapesOf 2 σ} rootCount T realP`, which is
`≥ rootCount (sepShape 2 (indiscrete 2)) realP = 1/4 > 0` (`inert2_mem_menu` puts the inert term in
the menu; `rootCount_sepShape_nonneg` makes every menu term nonnegative; `gate_rootCount_inert2`
pins the inert term to `1/4`). This is the machine-checked reversal of the audit's V1 vacuity: the
certified real order-0 density of a genuine (inert) factorization type is genuinely nonzero. -/
theorem montes_order0_certified_value_pos :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
            M8.stratumCount (M9.rawCount 2) T N) / (M9.realP : ℚ) ^ (2 * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)))
      ∧ (0 : ℚ) < num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ) := by
  obtain ⟨num, den, hden, hall, hlim⟩ :=
    montes_order0_unconditional 2 (by norm_num) (unramType 2 (Nat.Partition.indiscrete 2))
  refine ⟨num, den, hden, hall, hlim, ?_⟩
  have hq : (1 : ℕ) < M9.realP := by unfold M9.realP; norm_num
  have hval := (hall M9.realP hq).2
  rw [← hval]
  have hpos : (0 : ℚ) < rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
      (sepShape 2 (Nat.Partition.indiscrete 2)) M9.realP := by
    rw [gate_rootCount_inert2]; norm_num
  calc (0 : ℚ)
      < rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
          (sepShape 2 (Nat.Partition.indiscrete 2)) M9.realP := hpos
    _ ≤ ∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
          rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP := by
        apply Finset.single_le_sum (f := fun T =>
          rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP)
        · intro T hT
          rw [sepShapesOf, Finset.mem_image] at hT
          obtain ⟨lam, _, rfl⟩ := hT
          exact rootCount_sepShape_nonneg 2 (by norm_num) lam
        · exact inert2_mem_menu

end LeanUrat.OM.Order0
