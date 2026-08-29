/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG15

/-!
# Uniformity.ChapI.IFCG16 — [FP1 2026-08-29] the per-genre census gap and the rational
assembly calculus

FP0 (`IFCG15.lean`, `runs/wave-c/verdict_FP0.md`) reduced IFCG14's socket to ONE named
remainder, `RationalNonloopRemainderAt m`: the canonical non-loop cell sequence has one
rational limit uniformly over the DVR.  Its verdict's items 1–4 record that the landed
corpus exports NO finite-level cell/split cardinality theorem (no classifier from
coefficient classes, no `q^{-skeletonExp}` cell measure, no split-parameter bijection, no
`combinedClass` product count), so the remainder cannot be discharged by assembly.

This file advances the boundary by ONE structural step, in FP0's own audit style:

* **§1 the rational assembly calculus.**  `exists_ratPair_childProd` — given the smaller
  value laws, the product of the decided densities over any finite child list (all degrees
  `< m`) is ONE rational function of `q` uniformly over `O`, with both denominator
  obligations.  `exists_ratPair_sum` — the ℚ-level common-denominator assembly of a finite
  bank of weighted products.  Together these are the reusable "RW2 rational package" layer
  (blueprint row A0G-RW2) at exactly the granularity the census interface below needs.
* **§2 the named per-genre census gap** `RationalNonloopCensusAt m`: there is a FINITE,
  `O`-independent bank of genres — each carrying a rational weight pair and a finite list
  of strictly smaller children `(k, σ')`, `k < m`, `σ'.degree = k` — such that at every
  `(O, π)` the non-loop decided cell splits EXACTLY (finite-level partition of
  `Nat.card (nonloopDecidedSet π m σ M)`) into per-genre counts whose normalizations
  converge to weight × ∏ children's decided densities.  This is the precise interface a
  future per-genre discharge (classifier GC0 + cell measure RW0 + cone sums RW1 + census
  FF1 + base change CL1) must fill; each future obligation is per-genre and localized.
* **§3 the reduction and the audit iff.**  `rationalNonloopRemainderAt_of_census` proves
  the census fires FP0's remainder: the finite bank sum passes to the limit, the children
  products become rational by the smaller laws, and the bank assembles to one
  `Polynomial ℚ` pair with both denominator obligations.  The converse
  `census_of_rationalNonloopRemainderAt` (one-genre bank, empty children) proves the
  interface is NOT stronger than the remainder: `rationalNonloopRemainderAt_iff_census`.
* **§4 uniform wiring.**  `UniformRationalNonloopCensus`, its equivalence with IFCG15's
  uniform remainder, and the new widest honest capstone
  `decidedSliceAt_all_of_census : UniformRationalNonloopCensus → ∀ n, DecidedSliceAt n`.
* **§5 limit helpers** for the future per-genre proofs: `tendsto_decidedSeq_comp` (child
  counts read at any level map diverging to `∞` converge to the child density) and
  `tendsto_list_prod` (finite products of convergent sequences).
* **§6 finite-precision Hensel uniqueness** (`factor_sub_mem_of_mul_sub_mem`): two monic
  factor pairs with the same coprime residual reductions whose products agree mod `𝔪 ^ N`
  agree factorwise mod `𝔪 ^ N` — the finite-precision companion of the landed exact
  `Uniformity.Hensel.monic_factorization_unique`, by the classical Newton filtration
  climb.  NEW: this is the theorem FP0's item 4 recorded as absent (the fold had NO
  injectivity statement).
* **§7 the class-level split bijection and the exact product count**, the BINARY
  residue-layer instance of the missing cardinality bridge: `mulClass_stratified_inj`
  (injectivity of the coprime fold on strata, from §6), `levelZeroStratum_mul_eq_image2`
  (surjectivity: the product stratum IS the fold image, from the landed Hensel
  factorization), and ★★ `card_levelZeroStratum_mul` — at every finite level `N ≥ 1`,
  `#stratum(g₁·g₂) = #stratum(g₁) · #stratum(g₂)` for coprime monic residuals: the
  first landed finite-level, measure-preserving split/count bridge into the `Coeff`
  cells.

## ⚠ Scoping disposition

★★★ `decidedSliceAt_all` is **NOT declared**: no unconditional instance of
`RationalNonloopCensusAt` at any mass `m ≥ 4` is provable from the landed signatures
(FP0's items 1–3 stand; item 4's injectivity/surjectivity/product-count gap is closed
HERE in binary residue-layer form by §§6–7, but the NP-layer per-skeleton classifier and
cell measure remain open).  The census gap is the sanctioned honest partial: the
remainder is re-expressed at per-genre granularity, provably without strengthening.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does not
occur (nothing here consumes the cover; the interface quantifies over its future output).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFCG16

open IsLocalRing Polynomial
open Uniformity.Density.IFCG14
open Uniformity.Density.IFCG15

/-! ## §1 — the rational assembly calculus (the RW2 layer at census granularity) -/

/-- **Children products are uniformly rational.**  Given the value laws at all degrees
`< m`, the product of decided densities over a finite child list (each entry of degree
`< m`) is ONE rational function of the residue cardinality, uniformly over the DVR, with
both denominator obligations. -/
theorem exists_ratPair_childProd {m : ℕ}
    (hsmaller : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (l : List (ℕ × FactorizationType))
    (hl : ∀ p ∈ l, p.1 < m ∧ p.2.degree = p.1) :
    ∃ n d : Polynomial ℚ, d ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          (l.map (fun p => decidedDensity O p.1 p.2)).prod
            = ((n.eval ((residueCard O : ℕ) : ℚ)
                / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
  induction l with
  | nil =>
      refine ⟨1, 1, one_ne_zero, ?_⟩
      intro O _ _ _ _ _
      simp
  | cons p t ih =>
      obtain ⟨hpm, hpd⟩ := hl p List.mem_cons_self
      obtain ⟨np, dp, hdp, hlawp⟩ := hsmaller p.1 hpm p.2 hpd
      obtain ⟨nt, dt, hdt, hlawt⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      refine ⟨np * nt, dp * dt, mul_ne_zero hdp hdt, ?_⟩
      intro O _ _ _ _ _
      obtain ⟨hpe, hpv⟩ := hlawp O
      obtain ⟨hte, htv⟩ := hlawt O
      refine ⟨by rw [eval_mul]; exact mul_ne_zero hpe hte, ?_⟩
      rw [List.map_cons, List.prod_cons, hpv, htv, eval_mul, eval_mul]
      push_cast
      ring

/-- **The ℚ-level bank assembly**: a finite sum of weighted rational products is one
rational pair, with the common-denominator evaluation identity at every point where all
the input denominators are nonzero. -/
theorem exists_ratPair_sum :
    ∀ (r : ℕ) (a b : Fin r → Polynomial ℚ × Polynomial ℚ),
      (∀ i, (a i).2 ≠ 0) → (∀ i, (b i).2 ≠ 0) →
      ∃ n d : Polynomial ℚ, d ≠ 0 ∧
        ∀ γ : ℚ, (∀ i, ((a i).2).eval γ ≠ 0) → (∀ i, ((b i).2).eval γ ≠ 0) →
          d.eval γ ≠ 0 ∧
            ∑ i, ((a i).1.eval γ / ((a i).2).eval γ)
                * ((b i).1.eval γ / ((b i).2).eval γ)
              = n.eval γ / d.eval γ := by
  intro r
  induction r with
  | zero =>
      intro a b _ _
      refine ⟨0, 1, one_ne_zero, ?_⟩
      intro γ _ _
      simp
  | succ r ih =>
      intro a b ha hb
      obtain ⟨nt, dt, hdt, hIH⟩ :=
        ih (fun i => a i.succ) (fun i => b i.succ)
          (fun i => ha i.succ) (fun i => hb i.succ)
      refine ⟨(a 0).1 * (b 0).1 * dt + (a 0).2 * (b 0).2 * nt,
        (a 0).2 * (b 0).2 * dt,
        mul_ne_zero (mul_ne_zero (ha 0) (hb 0)) hdt, ?_⟩
      intro γ hae hbe
      obtain ⟨hdte, hsum⟩ := hIH γ (fun i => hae i.succ) (fun i => hbe i.succ)
      have hae0 := hae 0
      have hbe0 := hbe 0
      constructor
      · simp only [eval_mul]
        exact mul_ne_zero (mul_ne_zero hae0 hbe0) hdte
      · rw [Fin.sum_univ_succ, hsum, div_mul_div_comm,
          div_add_div _ _ (mul_ne_zero hae0 hbe0) hdte]
        simp only [eval_add, eval_mul]

/-! ## §2 — the named per-genre census gap -/

/-- **Named FP1 gap: the per-genre census.**  Given all smaller value laws, each witnessed
degree-`m` label admits a FINITE, `O`-independent genre bank: rational weight pairs `w i`
(denominator nonzero as a polynomial, and nonzero at every residue cardinality) and finite
children lists `ch i` of strictly smaller degrees, such that at every `(O, π)` the
non-loop decided cell count partitions EXACTLY into per-genre counts `C i M`, and each
genre's normalized count converges to its weight times the product of its children's
decided densities.  A future discharge constructs the genres from the strong cover's
skeletons (classifier + cell measure + cone summation + census + base change); THIS file
proves the interface equivalent to FP0's remainder. -/
def RationalNonloopCensusAt (m : ℕ) : Prop :=
  (∀ k, k < m → ∀ σ : FactorizationType, σ.degree = k → DecidedValueLaw k σ) →
  ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
    ∃ (r : ℕ) (w : Fin r → Polynomial ℚ × Polynomial ℚ)
      (ch : Fin r → List (ℕ × FactorizationType)),
      (∀ i, (w i).2 ≠ 0) ∧
      (∀ i, ∀ p ∈ ch i, p.1 < m ∧ p.2.degree = p.1) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        (∀ i, ((w i).2).eval ((residueCard O : ℕ) : ℚ) ≠ 0) ∧
        ∀ π : O, Irreducible π →
          ∃ C : Fin r → ℕ → ℕ,
            (∀ M, Nat.card (nonloopDecidedSet π m σ M) = ∑ i, C i M) ∧
            ∀ i, Filter.Tendsto
              (fun M => (C i M : ℝ) / (residueCard O : ℝ) ^ (m * (M + m)))
              Filter.atTop
              (nhds ((((w i).1.eval ((residueCard O : ℕ) : ℚ)
                    / ((w i).2).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
                * ((ch i).map (fun p => decidedDensity O p.1 p.2)).prod))

/-! ## §3 — the reduction and the audit iff -/

/-- ★ **THE REDUCTION**: the per-genre census fires FP0's named remainder.  The finite
bank sum passes to the limit genre by genre, the children products are rational by the
smaller laws (§1), and the bank assembles into one `Polynomial ℚ` pair with both
denominator obligations. -/
theorem rationalNonloopRemainderAt_of_census {m : ℕ} (hm : 0 < m)
    (h : RationalNonloopCensusAt m) : RationalNonloopRemainderAt m := by
  intro hsmaller σ hσ hwit
  obtain ⟨r, w, ch, hwne, hch, hbank⟩ := h hsmaller σ hσ hwit
  -- one rational pair per genre's children product (chosen BEFORE the DVR)
  choose cn cd hcd hcval using fun i : Fin r =>
    exists_ratPair_childProd hsmaller (ch i) (hch i)
  -- the assembled bank pair
  obtain ⟨n, d, hd, hnd⟩ := exists_ratPair_sum r w (fun i => (cn i, cd i)) hwne hcd
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hwe, hπC⟩ := hbank O
  have hce : ∀ i, (cd i).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := fun i => (hcval i O).1
  obtain ⟨hde, hsum⟩ := hnd ((residueCard O : ℕ) : ℚ) hwe hce
  refine ⟨hde, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨C, hpart, hlim⟩ := hπC π hπ
  -- the canonical sequence IS the bank sum of the normalized genre counts
  have hseq : nonloopBaseSeq O m σ = fun M =>
      ∑ i, (C i M : ℝ) / (residueCard O : ℝ) ^ (m * (M + m)) := by
    funext M
    rw [nonloopBaseSeq_eq_nonloopCellSeq hπ hm σ M]
    show (Nat.card (nonloopDecidedSet π m σ M) : ℝ)
        / (residueCard O : ℝ) ^ (m * (M + m)) = _
    rw [hpart M]
    push_cast
    rw [Finset.sum_div]
  -- the genre limits sum to the bank value
  have htends : Filter.Tendsto (nonloopBaseSeq O m σ) Filter.atTop
      (nhds (∑ i, ((((w i).1.eval ((residueCard O : ℕ) : ℚ)
            / ((w i).2).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          * ((ch i).map (fun p => decidedDensity O p.1 p.2)).prod))) := by
    rw [hseq]
    exact tendsto_finsetSum _ (fun i _ => hlim i)
  -- and the bank value is the assembled rational pair
  have hT : (∑ i, ((((w i).1.eval ((residueCard O : ℕ) : ℚ)
          / ((w i).2).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
        * ((ch i).map (fun p => decidedDensity O p.1 p.2)).prod))
      = ((n.eval ((residueCard O : ℕ) : ℚ)
          / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [← hsum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hcval i O).2]
    push_cast
    ring
  rw [hT] at htends
  exact htends

/-- **The converse**: FP0's remainder yields the census with the ONE-genre bank (empty
children, the remainder's own pair as the weight).  So the census interface is not
stronger than the remainder. -/
theorem census_of_rationalNonloopRemainderAt {m : ℕ} (hm : 0 < m)
    (h : RationalNonloopRemainderAt m) : RationalNonloopCensusAt m := by
  intro hsmaller σ hσ hwit
  obtain ⟨num, den, hden, hlaw⟩ := h hsmaller σ hσ hwit
  refine ⟨1, fun _ => (num, den), fun _ => [], fun _ => hden,
    fun _ p hp => by simp at hp, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hlaw O
  refine ⟨fun _ => hne, ?_⟩
  intro π hπ
  refine ⟨fun _ M => Nat.card (nonloopDecidedSet π m σ M), fun M => by simp, fun i => ?_⟩
  simp only [List.map_nil, List.prod_nil, mul_one]
  show Filter.Tendsto (fun M => (Nat.card (nonloopDecidedSet π m σ M) : ℝ)
      / (residueCard O : ℝ) ^ (m * (M + m))) Filter.atTop _
  have hfun : (fun M => ((Nat.card (nonloopDecidedSet π m σ M) : ℝ))
      / (residueCard O : ℝ) ^ (m * (M + m))) = nonloopBaseSeq O m σ := by
    funext M
    rw [nonloopBaseSeq_eq_nonloopCellSeq hπ hm σ M]
    rfl
  rw [hfun]
  exact hlim

/-- **The audit iff** (FP0's style): at every positive mass, the per-genre census IS the
canonical non-loop remainder — neither weaker nor stronger. -/
theorem rationalNonloopRemainderAt_iff_census {m : ℕ} (hm : 0 < m) :
    RationalNonloopRemainderAt m ↔ RationalNonloopCensusAt m :=
  ⟨census_of_rationalNonloopRemainderAt hm, rationalNonloopRemainderAt_of_census hm⟩

/-! ## §4 — uniform wiring and the widest honest capstone -/

/-- The uniform per-genre census (masses `≥ 4`, matching IFCG14's socket window). -/
def UniformRationalNonloopCensus : Prop :=
  ∀ m, 4 ≤ m → RationalNonloopCensusAt m

/-- The uniform census is equivalent to IFCG15's uniform remainder. -/
theorem uniformNonloopRemainder_iff_census :
    UniformRationalNonloopRemainder ↔ UniformRationalNonloopCensus := by
  constructor
  · intro h m hm
    exact census_of_rationalNonloopRemainderAt (by omega) (h m hm)
  · intro h m hm
    exact rationalNonloopRemainderAt_of_census (by omega) (h m hm)

/-- **Widest honest capstone after FP1**: the per-genre census fires the all-degree
decided slice through IFCG15's remainder equivalence and IFCG14's assembly. -/
theorem decidedSliceAt_all_of_census (h : UniformRationalNonloopCensus) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  IFCG15.decidedSliceAt_all_of_nonloopRemainder
    (uniformNonloopRemainder_iff_census.mpr h)

/-! ## §5 — limit helpers for the future per-genre discharges -/

section Helpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **Child counts at any diverging level map converge to the child density** — the form
in which a future per-genre count law (children read at levels `φ M → ∞`) meets the
census interface's density product. -/
theorem tendsto_decidedSeq_comp {φ : ℕ → ℕ}
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (k : ℕ) (σ' : FactorizationType) :
    Filter.Tendsto (fun M => decidedSeq O k σ' (φ M)) Filter.atTop
      (nhds (decidedDensity O k σ')) :=
  (decidedSeq_tendsto k σ').comp hφ

end Helpers

/-- **Finite products of convergent sequences converge to the product of the limits** —
the list form matching the census interface's children products. -/
theorem tendsto_list_prod :
    ∀ (l : List ((ℕ → ℝ) × ℝ)),
      (∀ p ∈ l, Filter.Tendsto p.1 Filter.atTop (nhds p.2)) →
      Filter.Tendsto (fun M => (l.map (fun p => p.1 M)).prod) Filter.atTop
        (nhds ((l.map Prod.snd).prod))
  | [], _ => by
      simp only [List.map_nil, List.prod_nil]
      exact tendsto_const_nhds
  | p :: t, h => by
      simp only [List.map_cons, List.prod_cons]
      exact (h p List.mem_cons_self).mul
        (tendsto_list_prod t fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## §6 — finite-precision Hensel uniqueness (FP0 item 4, the injectivity core)

FP0's item 4: the corpus has no injectivity/surjectivity/product-cardinality theorem for
the class-level fold.  The EXACT-precision uniqueness is landed
(`Uniformity.Hensel.monic_factorization_unique`); what the class level needs is its
finite-precision congruence form: if two coprime-residual monic factorizations agree mod
`𝔪 ^ N`, the factors agree mod `𝔪 ^ N`.  Proof: the classical Newton filtration climb —
at each level the error's residual satisfies `Ū·B̄ + V̄·Ā = 0` with `deg Ū < deg Ā`,
`deg V̄ < deg B̄`, so coprimality kills it. -/

section FinitePrecision

open Uniformity.Hensel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The coefficient-ideal dictionary at a DVR: membership in `coeffIdeal (𝔪 ^ t)` is
divisibility by the constant `C (π ^ t)`. -/
theorem mem_coeffIdeal_pow_iff {π : O} (hπ : Irreducible π) (t : ℕ) (f : Polynomial O) :
    f ∈ coeffIdeal ((maximalIdeal O) ^ t) ↔ Polynomial.C (π ^ t) ∣ f := by
  rw [mem_coeffIdeal, Polynomial.C_dvd_iff_dvd_coeff]
  refine forall_congr' fun i => ?_
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- ★ **Finite-precision Hensel uniqueness.**  Two monic factor pairs with the SAME
coprime residual reductions whose products agree modulo `𝔪 ^ N` agree factorwise modulo
`𝔪 ^ N`.  The finite-precision companion of the landed exact
`Uniformity.Hensel.monic_factorization_unique`. -/
theorem factor_sub_mem_of_mul_sub_mem {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N)
    {A A' B B' : Polynomial O} (hA : A.Monic) (hA' : A'.Monic) (hB : B.Monic) (hB' : B'.Monic)
    (hdegA : A'.natDegree = A.natDegree) (hdegB : B'.natDegree = B.natDegree)
    (hredA : A'.map (residue O) = A.map (residue O))
    (hredB : B'.map (residue O) = B.map (residue O))
    (hcop : IsCoprime (A.map (residue O)) (B.map (residue O)))
    (hprod : A * B - A' * B' ∈ coeffIdeal ((maximalIdeal O) ^ N)) :
    A - A' ∈ coeffIdeal ((maximalIdeal O) ^ N)
      ∧ B - B' ∈ coeffIdeal ((maximalIdeal O) ^ N) := by
  have hπt : ∀ t : ℕ, (π : O) ^ t ≠ 0 := fun t => pow_ne_zero t hπ.ne_zero
  -- the residue-vanishing dictionary
  have hres : ∀ f : Polynomial O, f.map (residue O) = 0 ↔ Polynomial.C π ∣ f := by
    intro f
    rw [map_residue_eq_zero_iff]
    have h := mem_coeffIdeal_pow_iff hπ 1 f
    rwa [pow_one, pow_one] at h
  -- the filtration climb
  have main : ∀ t : ℕ, t + 1 ≤ N →
      Polynomial.C (π ^ (t + 1)) ∣ A - A' ∧ Polynomial.C (π ^ (t + 1)) ∣ B - B' := by
    intro t
    induction t with
    | zero =>
        intro _
        have hA1 : A - A' ∈ coeffIdeal (maximalIdeal O) :=
          sub_mem_coeffIdeal_maximalIdeal_iff.mpr hredA.symm
        have hB1 : B - B' ∈ coeffIdeal (maximalIdeal O) :=
          sub_mem_coeffIdeal_maximalIdeal_iff.mpr hredB.symm
        exact ⟨(mem_coeffIdeal_pow_iff hπ 1 _).mp (by rwa [pow_one]),
          (mem_coeffIdeal_pow_iff hπ 1 _).mp (by rwa [pow_one])⟩
    | succ t ih =>
        intro hle
        obtain ⟨hUdvd, hVdvd⟩ := ih (by omega)
        obtain ⟨U, hU⟩ := dvd_sub_comm.mp hUdvd
        obtain ⟨V, hV⟩ := dvd_sub_comm.mp hVdvd
        -- the Newton expansion of the error at this level
        have hexp : A' * B' - A * B
            = Polynomial.C (π ^ (t + 1))
                * (U * B + V * A + Polynomial.C (π ^ (t + 1)) * (U * V)) := by
          have hA'e : A' = A + Polynomial.C (π ^ (t + 1)) * U := by linear_combination hU
          have hB'e : B' = B + Polynomial.C (π ^ (t + 1)) * V := by linear_combination hV
          rw [hA'e, hB'e]
          ring
        -- the product congruence one level deeper
        have hstep : Polynomial.C (π ^ (t + 1 + 1)) ∣ A' * B' - A * B := by
          have h1 : Polynomial.C (π ^ N) ∣ A * B - A' * B' :=
            (mem_coeffIdeal_pow_iff hπ N _).mp hprod
          have h2 : Polynomial.C (π ^ (t + 1 + 1)) ∣ Polynomial.C (π ^ N) :=
            map_dvd Polynomial.C (pow_dvd_pow π (by omega))
          exact dvd_sub_comm.mp (h2.trans h1)
        -- cancel `C (π ^ (t+1))`: the linear+quadratic corrector is divisible by `C π`
        have hπW : Polynomial.C π
            ∣ U * B + V * A + Polynomial.C (π ^ (t + 1)) * (U * V) := by
          rw [hexp] at hstep
          rw [Polynomial.C_dvd_iff_dvd_coeff] at hstep ⊢
          intro i
          have h3 := hstep i
          rw [Polynomial.coeff_C_mul, pow_succ] at h3
          exact (mul_dvd_mul_iff_left (hπt (t + 1))).mp h3
        -- kill the quadratic term: `t + 1 ≥ 1`
        have hπQ : Polynomial.C π ∣ Polynomial.C (π ^ (t + 1)) * (U * V) :=
          Dvd.dvd.mul_right (map_dvd Polynomial.C (dvd_pow_self π (Nat.succ_ne_zero t))) _
        have hπL : Polynomial.C π ∣ U * B + V * A := by
          have he : U * B + V * A
              = (U * B + V * A + Polynomial.C (π ^ (t + 1)) * (U * V))
                - Polynomial.C (π ^ (t + 1)) * (U * V) := by ring
          rw [he]
          exact dvd_sub hπW hπQ
        -- to the residue field
        have hk : U.map (residue O) * B.map (residue O)
            + V.map (residue O) * A.map (residue O) = 0 := by
          have h0 : (U * B + V * A).map (residue O) = 0 := (hres _).mpr hπL
          simpa [Polynomial.map_add, Polynomial.map_mul] using h0
        -- degree bookkeeping: the residual correctors sit strictly below the factors
        have hUdeg : (U.map (residue O)).degree < (A.map (residue O)).degree := by
          have h1 : (U.map (residue O)).degree ≤ U.degree := Polynomial.degree_map_le
          have h2 : U.degree = (A' - A).degree := by
            rw [hU, Polynomial.degree_mul, Polynomial.degree_C (hπt (t + 1)), zero_add]
          have h3 : (A' - A).degree < (A'.natDegree : WithBot ℕ) :=
            degree_sub_lt_of_monic_of_natDegree_eq hA' hA hdegA
          have h4 : (A.map (residue O)).degree = (A'.natDegree : WithBot ℕ) := by
            rw [hA.degree_map, Polynomial.degree_eq_natDegree hA.ne_zero, hdegA]
          rw [h4]
          exact lt_of_le_of_lt (h1.trans h2.le) h3
        have hVdeg : (V.map (residue O)).degree < (B.map (residue O)).degree := by
          have h1 : (V.map (residue O)).degree ≤ V.degree := Polynomial.degree_map_le
          have h2 : V.degree = (B' - B).degree := by
            rw [hV, Polynomial.degree_mul, Polynomial.degree_C (hπt (t + 1)), zero_add]
          have h3 : (B' - B).degree < (B'.natDegree : WithBot ℕ) :=
            degree_sub_lt_of_monic_of_natDegree_eq hB' hB hdegB
          have h4 : (B.map (residue O)).degree = (B'.natDegree : WithBot ℕ) := by
            rw [hB.degree_map, Polynomial.degree_eq_natDegree hB.ne_zero, hdegB]
          rw [h4]
          exact lt_of_le_of_lt (h1.trans h2.le) h3
        -- coprimality kills the residual correctors
        have hUbar : U.map (residue O) = 0 := by
          have hdvdk : A.map (residue O) ∣ U.map (residue O) * B.map (residue O) :=
            ⟨-(V.map (residue O)), by linear_combination hk⟩
          exact Polynomial.eq_zero_of_dvd_of_degree_lt
            (hcop.dvd_of_dvd_mul_right hdvdk) hUdeg
        have hVbar : V.map (residue O) = 0 := by
          have hdvdk : B.map (residue O) ∣ V.map (residue O) * A.map (residue O) :=
            ⟨-(U.map (residue O)), by linear_combination hk⟩
          exact Polynomial.eq_zero_of_dvd_of_degree_lt
            (hcop.symm.dvd_of_dvd_mul_right hdvdk) hVdeg
        -- climb one level
        obtain ⟨U₂, hU₂⟩ := (hres U).mp hUbar
        obtain ⟨V₂, hV₂⟩ := (hres V).mp hVbar
        constructor
        · exact dvd_sub_comm.mpr
            ⟨U₂, by rw [hU, hU₂, ← mul_assoc, ← Polynomial.C_mul, ← pow_succ]⟩
        · exact dvd_sub_comm.mpr
            ⟨V₂, by rw [hV, hV₂, ← mul_assoc, ← Polynomial.C_mul, ← pow_succ]⟩
  obtain ⟨hAf, hBf⟩ := main (N - 1) (by omega)
  have hNe : N - 1 + 1 = N := by omega
  rw [hNe] at hAf hBf
  exact ⟨(mem_coeffIdeal_pow_iff hπ N _).mpr hAf, (mem_coeffIdeal_pow_iff hπ N _).mpr hBf⟩

end FinitePrecision

/-! ## §7 — the class-level split bijection and the exact product count
(FP0 item 4, both halves, binary residue-coprime form)

The finite-level, measure-preserving cardinality bridge at the FIRST (residue) layer:
`mulClass` restricted to coprime strata is injective (§6), surjective onto the product
stratum (the landed `Uniformity.Hensel.exists_monic_factorization`), and therefore
cardinality-exact.  This is the binary instance of the bridge the deeper NP-layer census
still lacks. -/

section ClassLevel

open Uniformity.Hensel Uniformity.Density.Induction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}

/-- ★ **Class-level injectivity of the coprime fold** — two stratified factor-class pairs
with the same coprime residual pair and the same `mulClass` product are equal. -/
theorem mulClass_stratified_inj (hN : 1 ≤ N) {n₁ n₂ : ℕ}
    {g₁ g₂ : Polynomial (ResidueField O)} (hcop : IsCoprime g₁ g₂)
    {c₁ c₁' : Coeff O n₁ N} {c₂ c₂' : Coeff O n₂ N}
    (h₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (h₁' : c₁' ∈ levelZeroStratum O n₁ N g₁)
    (h₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) (h₂' : c₂' ∈ levelZeroStratum O n₂ N g₂)
    (h : mulClass c₁ c₂ = mulClass c₁' c₂') :
    c₁ = c₁' ∧ c₂ = c₂' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨a₁', ha₁'⟩ := proj_surjective' O n₁ N c₁'
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  obtain ⟨a₂', ha₂'⟩ := proj_surjective' O n₂ N c₂'
  have hr₁ : (monicPoly a₁).map (residue O) = g₁ := h₁ a₁ ha₁
  have hr₁' : (monicPoly a₁').map (residue O) = g₁ := h₁' a₁' ha₁'
  have hr₂ : (monicPoly a₂).map (residue O) = g₂ := h₂ a₂ ha₂
  have hr₂' : (monicPoly a₂').map (residue O) = g₂ := h₂' a₂' ha₂'
  -- the product congruence, read at the lifts
  have hprodclass :
      proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
        = proj O (n₁ + n₂) N (fun i => (monicPoly a₁' * monicPoly a₂').coeff (i : ℕ)) := by
    rw [mulClass_proj, mulClass_proj, ha₁, ha₂, ha₁', ha₂', h]
  have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hd' : (monicPoly a₁' * monicPoly a₂').natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁').natDegree_mul (monicPoly_monic a₂'),
      monicPoly_natDegree, monicPoly_natDegree]
  have hmem : monicPoly a₁ * monicPoly a₂ - monicPoly a₁' * monicPoly a₂'
      ∈ coeffIdeal ((maximalIdeal O) ^ N) := by
    rw [mem_coeffIdeal]
    intro i
    rcases lt_or_ge i (n₁ + n₂) with hi | hi
    · have hsub : (monicPoly a₁ * monicPoly a₂).coeff i
          - (monicPoly a₁' * monicPoly a₂').coeff i ∈ (maximalIdeal O) ^ N :=
        Ideal.Quotient.eq.mp (congrFun hprodclass ⟨i, hi⟩)
      rwa [Polynomial.coeff_sub]
    · have hcoeff : (monicPoly a₁ * monicPoly a₂).coeff i
          = (monicPoly a₁' * monicPoly a₂').coeff i := by
        rcases eq_or_lt_of_le hi with he | hlt
        · have e1 : (monicPoly a₁ * monicPoly a₂).coeff i = 1 := by
            rw [← he, ← hd]
            exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
          have e2 : (monicPoly a₁' * monicPoly a₂').coeff i = 1 := by
            rw [← he, ← hd']
            exact ((monicPoly_monic a₁').mul (monicPoly_monic a₂')).coeff_natDegree
          rw [e1, e2]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt)]
      rw [Polynomial.coeff_sub, hcoeff, sub_self]
      exact Ideal.zero_mem _
  have hcore := factor_sub_mem_of_mul_sub_mem hπ hN
    (monicPoly_monic a₁) (monicPoly_monic a₁') (monicPoly_monic a₂) (monicPoly_monic a₂')
    (by rw [monicPoly_natDegree, monicPoly_natDegree])
    (by rw [monicPoly_natDegree, monicPoly_natDegree])
    (by rw [hr₁, hr₁']) (by rw [hr₂, hr₂'])
    (by rw [hr₁, hr₂]; exact hcop) hmem
  constructor
  · rw [← ha₁, ← ha₁']
    funext i
    have hmemi := mem_coeffIdeal.mp hcore.1 (i : ℕ)
    rw [Polynomial.coeff_sub, monicPoly_coeff_lt a₁ i.isLt,
      monicPoly_coeff_lt a₁' i.isLt] at hmemi
    exact Ideal.Quotient.eq.mpr hmemi
  · rw [← ha₂, ← ha₂']
    funext i
    have hmemi := mem_coeffIdeal.mp hcore.2 (i : ℕ)
    rw [Polynomial.coeff_sub, monicPoly_coeff_lt a₂ i.isLt,
      monicPoly_coeff_lt a₂' i.isLt] at hmemi
    exact Ideal.Quotient.eq.mpr hmemi

/-- ★ **Class-level surjectivity of the coprime split** — over a complete DVR, the product
stratum is EXACTLY the `mulClass` image of the factor strata (⊇ is the landed
`mulClass_mem_levelZeroStratum`; ⊆ is Hensel factorization of an arbitrary lift). -/
theorem levelZeroStratum_mul_eq_image2 [IsAdicComplete (maximalIdeal O) O] (hN : 1 ≤ N)
    {n₁ n₂ : ℕ} {g₁ g₂ : Polynomial (ResidueField O)}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂)
    (hcop : IsCoprime g₁ g₂) :
    levelZeroStratum O (n₁ + n₂) N (g₁ * g₂)
      = Set.image2 mulClass (levelZeroStratum O n₁ N g₁) (levelZeroStratum O n₂ N g₂) := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨a, ha⟩ := proj_surjective' O (n₁ + n₂) N c
    have hmap : (monicPoly a).map (residue O) = g₁ * g₂ := hc a ha
    obtain ⟨G, H, hGm, hHm, hFGH, hGr, hHr, hGd, hHd⟩ :=
      exists_monic_factorization (monicPoly_monic a) hg₁ hg₂ hcop hmap
    obtain ⟨vG, hvG⟩ := exists_monicPoly_eq hGm (by rw [hGd, hd₁])
    obtain ⟨vH, hvH⟩ := exists_monicPoly_eq hHm (by rw [hHd, hd₂])
    refine ⟨proj O n₁ N vG, ?_, proj O n₂ N vH, ?_, ?_⟩
    · rw [mem_levelZeroStratum_iff hN]
      exact ⟨vG, rfl, by rw [hvG]; exact hGr⟩
    · rw [mem_levelZeroStratum_iff hN]
      exact ⟨vH, rfl, by rw [hvH]; exact hHr⟩
    · rw [← mulClass_proj, ← ha]
      have hfun : (fun i : Fin (n₁ + n₂) => (monicPoly vG * monicPoly vH).coeff (i : ℕ))
          = fun i : Fin (n₁ + n₂) => a i := by
        funext i
        rw [hvG, hvH, ← hFGH, monicPoly_coeff_lt a i.isLt]
      rw [hfun]
  · rintro c ⟨c₁, h₁, c₂, h₂, rfl⟩
    exact mulClass_mem_levelZeroStratum hN h₁ h₂

/-- **The fold's exact product count on stratified subsets** — the `mulClass` image of any
two subsets of coprime strata has cardinality exactly the product (injectivity §6). -/
theorem card_image2_mulClass (hN : 1 ≤ N) {n₁ n₂ : ℕ}
    {g₁ g₂ : Polynomial (ResidueField O)} (hcop : IsCoprime g₁ g₂)
    {S₁ : Set (Coeff O n₁ N)} {S₂ : Set (Coeff O n₂ N)}
    (hS₁ : S₁ ⊆ levelZeroStratum O n₁ N g₁) (hS₂ : S₂ ⊆ levelZeroStratum O n₂ N g₂) :
    Nat.card (Set.image2 mulClass S₁ S₂) = Nat.card S₁ * Nat.card S₂ := by
  rw [← Set.image_uncurry_prod, Nat.card_image_of_injOn, Nat.card_congr
    (Equiv.Set.prod S₁ S₂), Nat.card_prod]
  rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩ hxy
  obtain ⟨e₁, e₂⟩ := mulClass_stratified_inj hN hcop
    (hS₁ hx₁) (hS₁ hy₁) (hS₂ hx₂) (hS₂ hy₂) hxy
  exact Prod.ext e₁ e₂

/-- ★★ **THE BINARY MEASURE-PRESERVING CARDINALITY BRIDGE at the residue layer**: over a
complete DVR, the cardinality of a coprime product stratum at EVERY finite level is
exactly the product of the factor strata's cardinalities.  This is the first landed
instance of the finite-level split/count bridge whose general (NP-layer, per-genre) form
is `RationalNonloopCensusAt`'s open content. -/
theorem card_levelZeroStratum_mul [IsAdicComplete (maximalIdeal O) O] (hN : 1 ≤ N)
    {n₁ n₂ : ℕ} {g₁ g₂ : Polynomial (ResidueField O)}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂)
    (hcop : IsCoprime g₁ g₂) :
    Nat.card (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂))
      = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂) := by
  rw [levelZeroStratum_mul_eq_image2 hN hg₁ hg₂ hd₁ hd₂ hcop,
    card_image2_mulClass hN hcop (subset_refl _) (subset_refl _)]

end ClassLevel

end Uniformity.Density.IFCG16

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG16.exists_ratPair_childProd
#print axioms Uniformity.Density.IFCG16.exists_ratPair_sum
#print axioms Uniformity.Density.IFCG16.rationalNonloopRemainderAt_of_census
#print axioms Uniformity.Density.IFCG16.census_of_rationalNonloopRemainderAt
#print axioms Uniformity.Density.IFCG16.rationalNonloopRemainderAt_iff_census
#print axioms Uniformity.Density.IFCG16.uniformNonloopRemainder_iff_census
#print axioms Uniformity.Density.IFCG16.decidedSliceAt_all_of_census
#print axioms Uniformity.Density.IFCG16.tendsto_decidedSeq_comp
#print axioms Uniformity.Density.IFCG16.tendsto_list_prod
#print axioms Uniformity.Density.IFCG16.mem_coeffIdeal_pow_iff
#print axioms Uniformity.Density.IFCG16.factor_sub_mem_of_mul_sub_mem
#print axioms Uniformity.Density.IFCG16.mulClass_stratified_inj
#print axioms Uniformity.Density.IFCG16.levelZeroStratum_mul_eq_image2
#print axioms Uniformity.Density.IFCG16.card_image2_mulClass
#print axioms Uniformity.Density.IFCG16.card_levelZeroStratum_mul
