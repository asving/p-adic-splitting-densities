/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H108

/-!
# Uniformity.ChapH.H109 — the child events

**Chapter H, NODE H.109** [def+lemma] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a's event list, source
`EFF.GENIND.08`).  Fourth node of **N-2**, the cluster event grammar over `O`.

`HasChildAt π c μ k z` says: the slope-`k` residual of the state `c` has the NONZERO root `z`
with multiplicity `μ ≥ 2`.  Per **DECISION D-H17.3** the event is carried by the corpus's own
recentring `x ↦ π ^ k (y + ẑ)` — as a π-divisibility pattern of the recentred coefficients at
the capped content `D = betaContent c k` — and *not* by a second Newton-polygon/residual
apparatus (GC-2: no new polygon type anywhere in §17).  Slopes that are not sides are excluded
automatically: a single-point support has no nonzero root of multiplicity `≥ 2`.

* `HasChildAt` (def half) — the ∀-lift form: EVERY monic lift `a` of the class and EVERY lift
  `w` of the residue `z` exhibits the pattern;
* `hasChildAt_of_exists` (lemma half, **conservativity**) — on a non-drain state at `1 ≤ N` the
  ∀-lift clauses hold as soon as they hold at ONE lift pair `(a, w)`.  Every threshold consulted
  is `≤ N` (H.108: `D ≤ N − 1`), so every consulted digit is class-determined.

## The transport, in one line each

The workhorse is `recentre_transport`: two lift pairs of the same `(c, z)` produce recentred
polynomials agreeing **coefficientwise mod `π ^ (D+1)`**.  It factors through the intermediate
lift `(a', w)` — first swap the coefficient vector, then the centre:

* *the coefficient swap* (`pow_dvd_coeff_comp_sub`).  `a − a' ∈ (𝔪 ^ N) ^ (Fin m)`, so
  `C (π ^ N) ∣ monicPoly a − monicPoly a'`; `C`-divisibility survives `comp`
  (`C_dvd_comp`), and `π ^ (D+1) ∣ π ^ N` because `D + 1 ≤ N`.
* *the centre swap* (`pow_succ_dvd_coeff_shift`).  The two centres differ by a Taylor shift:
  `f.comp (C t * (X + C (w + d))) = (f.comp (C t * (X + C w))).comp (X + C d)`
  (`comp_recentre_add`) with `d = w' − w ∈ 𝔪`.  Writing the (already `π ^ D`-divisible)
  recentred polynomial as `C (π ^ D) * h`, the shift moves it by
  `C (π ^ D) * (h.comp (X + C d) − h)`, and `C d ∣ h.comp (X + C d) − h`
  (`C_dvd_comp_X_add_C_sub`, from `Polynomial.sub_dvd_eval_sub` in `O[X]`), so the whole
  difference is divisible by `π ^ D * d`, hence by `π ^ (D+1)`.

**`residue w = z` is load-bearing** in the second bullet and is *not* implied by `1 ≤ k`: the
Taylor shift is by `w' − w`, not by `π ^ k (w' − w)` (the substitution is
`X ↦ π ^ k X + π ^ k w`, so re-centring to `w'` is the shift `X ↦ X + (w' − w)`).  The numeric
gate below carries the defeat witness that shows this: at `π = 2, m = 3, N = 4, k = 1`,
`a = (8, 4, 2)` and centres `w = 0`, `w' = 1` (DIFFERENT residues) the recentred constant terms
differ by `24`, which is not divisible by `π ^ (D+1) = 16`.

`0 < m` is not a hypothesis of the frozen signature and is not needed as one: at `m = 0` every
state is vacuously a drain (H.108's `isDrainState_of_eq_zero`), so `h0` supplies it.

DEPENDS: H.106 (`ClusterState`), H.107 (`resOrd`, `mem_maximalIdeal_pow_iff_dvd_of_irr`),
H.108 (`IsDrainState`, `betaContent`, `betaContent_le`, `isDrainState_of_eq_zero`) · landed
`monicPoly`, `proj`, `residue` (`Uniformity/Density/LocalData.lean`) · mathlib
`Polynomial.C_dvd_iff_dvd_coeff`, `Polynomial.comp_assoc`, `Polynomial.sub_dvd_eval_sub`,
`Polynomial.eval_map`, `Polynomial.sub_comp`, `Polynomial.mul_comp`.

The coefficient-swap step reproves (rather than imports) chapter B's `B78.monicPoly_congr`:
H.109's DEPENDS list is deliberately ChapB-free (D-H17.3 keeps the event carrier self-contained),
and the fact is six lines.  The `example` of §4 pins the re-derivation against the landed
statement it duplicates (at `q = X`, where `comp` is the identity).

## What this node does NOT claim

The **triangular expansion** `g.coeff j = ∑_{i ≥ j} aᵢ · C(i,j) · π ^ (k i) · w ^ (i−j)` is the
blueprint's split candidate **H.109a** (also H.115/H.116's step 1) and is NOT proved here: the
conservativity proof above routes around it entirely (through `sub_dvd_eval_sub`), so it is owed
by whichever node first needs the expansion itself.  The numeric gate below exercises the
expansion at the numeral level only, on an independent `ℤ`-model, and says nothing about the
Lean `Polynomial` term.

## TEETH (GC-8)

Battery `P1(a) partition total` of `verification/openmath/OM2_genindb_battery.py` (RESULTS
2026-08-16, 612/612) reads the child events of every state of every cell in both rings — the
reader's `children` list — so the node's certified content is the *event detection*, with no
single numeric cell to quote.  What is reproduced below is the arithmetic that detection rests
on, as three `#guard`s on an independent `ℤ`-model: (i) the closed-form recentred coefficients
evaluate to the recentred polynomial at five integer points (the model is pinned to the actual
substitution, not to itself); (ii) H.109's conservativity claim, at the cell
`π = 2, m = 3, N = 4, k = 1`; (iii) the defeat witness for the `residue w = z` binder.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. Recentring: the two elementary moves -/

section Moves

-- The three elementary moves are pure `CommRing` facts: no DVR structure is consulted.
variable {O : Type*} [CommRing O]

/-- **Re-centring is a Taylor shift.**  Moving the centre from `w` to `w + d` in the recentring
`X ↦ t (X + w)` is precomposition with `X ↦ X + d`.  (Note the shift is by `d`, NOT by `t d`:
the substituted argument is `t X + t w`, and `t (X + d) + t w = t X + t (w + d)`.) -/
theorem comp_recentre_add (f : Polynomial O) (t w d : O) :
    f.comp (C t * (X + C (w + d))) = (f.comp (C t * (X + C w))).comp (X + C d) := by
  have hq : (C t * (X + C w)).comp (X + C d) = C t * (X + C (w + d)) := by
    simp only [mul_comp, add_comp, C_comp, X_comp, map_add]
    ring
  rw [Polynomial.comp_assoc, hq]

/-- **`C`-divisibility survives composition.**  If `C t` divides `p` it divides `p.comp q`, for
any `q` — the witness is the composed cofactor. -/
theorem C_dvd_comp {t : O} {p : Polynomial O} (h : C t ∣ p) (q : Polynomial O) :
    C t ∣ p.comp q := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r.comp q, by rw [mul_comp, C_comp]⟩

/-- **A Taylor shift moves a polynomial by a multiple of `C d`.**  Read `p` in `(O[X])[X]` via
`p.map C`; then `p.comp (X + C d)` and `p` are its evaluations at `X + C d` and at `X`, whose
difference `sub_dvd_eval_sub` divides by `(X + C d) − X = C d`. -/
theorem C_dvd_comp_X_add_C_sub (p : Polynomial O) (d : O) :
    C d ∣ p.comp (X + C d) - p := by
  have h1 : ((p.map (C : O →+* Polynomial O)).eval (X + C d)) = p.comp (X + C d) := by
    rw [Polynomial.eval_map]; rfl
  have h2 : ((p.map (C : O →+* Polynomial O)).eval X) = p := by
    rw [Polynomial.eval_map]
    exact Polynomial.comp_X
  have hsub :=
    Polynomial.sub_dvd_eval_sub (X + C d) (X : Polynomial O) (p.map (C : O →+* Polynomial O))
  rw [h1, h2] at hsub
  have hx : (X + C d) - (X : Polynomial O) = C d := by ring
  rwa [hx] at hsub

end Moves

/-! ## 2. The two perturbation steps -/

section Perturb

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The coefficient swap.**  Two lifts of the same level-`N` class produce recentred
polynomials whose coefficients agree mod `π ^ N`, for ANY recentring `q`.

(This re-derives chapter B's `B78.monicPoly_congr` inside H.109's ChapB-free environment; the
`example` below pins the two statements together.) -/
theorem pow_dvd_coeff_comp_sub {π : O} (hπ : Irreducible π) {m N : ℕ} {a a' : Fin m → O}
    (h : proj O m N a = proj O m N a') (q : Polynomial O) (j : ℕ) :
    π ^ N ∣ ((monicPoly a).comp q - (monicPoly a').comp q).coeff j := by
  classical
  have hsub : ∀ i : Fin m, π ^ N ∣ (a i - a' i) := by
    intro i
    have hmk : (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) (a i)
        = (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) (a' i) := congrFun h i
    exact (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1 (Ideal.Quotient.eq.1 hmk)
  have hC : C (π ^ N) ∣ (monicPoly a - monicPoly a' : Polynomial O) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff _ _]
    intro i
    have hexp : (monicPoly a - monicPoly a' : Polynomial O)
        = ∑ t : Fin m, C (a t - a' t) * X ^ (t : ℕ) := by
      simp only [monicPoly, map_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hexp, finsetSum_coeff]
    refine Finset.dvd_sum fun t _ => ?_
    rw [coeff_C_mul]
    exact (hsub t).mul_right _
  have hcomp : C (π ^ N) ∣ ((monicPoly a).comp q - (monicPoly a').comp q) := by
    rw [← Polynomial.sub_comp]
    exact C_dvd_comp hC q
  exact ((Polynomial.C_dvd_iff_dvd_coeff _ _).1 hcomp) j

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The centre swap.**  A polynomial all of whose coefficients are divisible by `π ^ D` moves,
under a Taylor shift by `d`, by coefficients divisible by `π ^ D * d`; with `π ∣ d` that is
`π ^ (D+1)`.  (Like the moves of §1 this is a pure `CommRing` fact — `π` is an arbitrary ring
element here; only the CALLER knows it is a uniformizer.) -/
theorem pow_succ_dvd_coeff_shift {π : O} {p : Polynomial O} {D : ℕ}
    (hp : ∀ i, π ^ D ∣ p.coeff i) {d : O} (hd : π ∣ d) (j : ℕ) :
    π ^ (D + 1) ∣ (p.comp (X + C d) - p).coeff j := by
  obtain ⟨h, rfl⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 hp
  obtain ⟨r, hr⟩ := C_dvd_comp_X_add_C_sub h d
  have hrw : (C (π ^ D) * h).comp (X + C d) - C (π ^ D) * h
      = C (π ^ D * d) * r := by
    rw [mul_comp, C_comp, show C (π ^ D) * h.comp (X + C d) - C (π ^ D) * h
      = C (π ^ D) * (h.comp (X + C d) - h) from by ring, hr, ← mul_assoc, ← C_mul]
  rw [hrw, coeff_C_mul]
  obtain ⟨e, he⟩ := hd
  exact ⟨e * r.coeff j, by rw [he]; ring⟩

/-- **The transport (the engine of conservativity).**  Two lift pairs of the same class/residue
produce recentred polynomials agreeing coefficientwise mod `π ^ (D+1)`, given that the FIRST
pair already satisfies the `π ^ D`-clause. -/
theorem recentre_transport {π : O} (hπ : Irreducible π) {m N : ℕ} {a a' : Fin m → O} {w w' : O}
    {D k : ℕ} (hproj : proj O m N a = proj O m N a') (hres : residue O w = residue O w')
    (hDN : D + 1 ≤ N)
    (h1 : ∀ j, π ^ D ∣ ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff j) (j : ℕ) :
    π ^ (D + 1) ∣
      (((monicPoly a').comp (C (π ^ k) * (X + C w')))
        - ((monicPoly a).comp (C (π ^ k) * (X + C w)))).coeff j := by
  -- (A) swap the coefficient vector, keeping the centre `w`
  have hA : ∀ i, π ^ (D + 1) ∣
      (((monicPoly a').comp (C (π ^ k) * (X + C w)))
        - ((monicPoly a).comp (C (π ^ k) * (X + C w)))).coeff i := fun i =>
    (pow_dvd_pow π hDN).trans
      (pow_dvd_coeff_comp_sub hπ hproj.symm (C (π ^ k) * (X + C w)) i)
  -- the intermediate lift still satisfies the `π ^ D`-clause
  have h1' : ∀ i, π ^ D ∣ ((monicPoly a').comp (C (π ^ k) * (X + C w))).coeff i := by
    intro i
    have he : ((monicPoly a').comp (C (π ^ k) * (X + C w))).coeff i
        = ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff i
          + (((monicPoly a').comp (C (π ^ k) * (X + C w)))
              - ((monicPoly a).comp (C (π ^ k) * (X + C w)))).coeff i := by
      rw [coeff_sub]; ring
    rw [he]
    exact dvd_add (h1 i) ((pow_dvd_pow π (Nat.le_succ D)).trans (hA i))
  -- (B) swap the centre: `w' − w` lies in the maximal ideal
  have hd : π ∣ (w' - w) := by
    have hmk : (Ideal.Quotient.mk (maximalIdeal O)) w' = (Ideal.Quotient.mk (maximalIdeal O)) w :=
      hres.symm
    have hmem : w' - w ∈ (maximalIdeal O) ^ 1 := by
      rw [pow_one]; exact Ideal.Quotient.eq.1 hmk
    have hdvd := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 (w' - w)).1 hmem
    rwa [pow_one] at hdvd
  have hB : ∀ i, π ^ (D + 1) ∣
      (((monicPoly a').comp (C (π ^ k) * (X + C w')))
        - ((monicPoly a').comp (C (π ^ k) * (X + C w)))).coeff i := by
    intro i
    have hsh : (monicPoly a').comp (C (π ^ k) * (X + C w'))
        = ((monicPoly a').comp (C (π ^ k) * (X + C w))).comp (X + C (w' - w)) := by
      have hww : w + (w' - w) = w' := by ring
      calc (monicPoly a').comp (C (π ^ k) * (X + C w'))
          = (monicPoly a').comp (C (π ^ k) * (X + C (w + (w' - w)))) := by rw [hww]
        _ = ((monicPoly a').comp (C (π ^ k) * (X + C w))).comp (X + C (w' - w)) :=
            comp_recentre_add _ _ _ _
    rw [hsh]
    exact pow_succ_dvd_coeff_shift h1' hd i
  -- (A) + (B)
  have hsum : (((monicPoly a').comp (C (π ^ k) * (X + C w')))
        - ((monicPoly a).comp (C (π ^ k) * (X + C w)))).coeff j
      = (((monicPoly a').comp (C (π ^ k) * (X + C w')))
          - ((monicPoly a').comp (C (π ^ k) * (X + C w)))).coeff j
        + (((monicPoly a').comp (C (π ^ k) * (X + C w)))
            - ((monicPoly a).comp (C (π ^ k) * (X + C w)))).coeff j := by
    simp only [coeff_sub]; ring
  rw [hsum]
  exact dvd_add (hB j) (hA j)

end Perturb

/-! ## 3. The child events -/

/-- **H.109 (def half).** `HasChildAt π c μ k z`: the slope-`k` residual has the NONZERO root
`z` with multiplicity `μ ≥ 2` — stated conservatively (∀-lift) through the recentring
`x ↦ π ^ k (y + ẑ)` and π-divisibility of the recentred coefficients at the capped content. -/
def HasChildAt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) (μ k : ℕ) (z : ResidueField O) : Prop :=
  2 ≤ μ ∧ 1 ≤ k ∧ z ≠ 0 ∧
    ∀ (a : Fin m → O) (w : O), proj O m N a = c.1 → residue O w = z →
      (∀ j, π ^ betaContent c k ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j) ∧
      (∀ j < μ, π ^ (betaContent c k + 1) ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j) ∧
      ¬ π ^ (betaContent c k + 1) ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff μ

/-- **H.109 (lemma half).** Conservativity/lift-independence: on non-drain states with
`1 ≤ N`, the ∀-lift clauses hold as soon as they hold at ONE lift pair (every threshold is
`≤ N`, so every consulted digit is class-determined). -/
theorem hasChildAt_of_exists {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hN : 1 ≤ N)
    {c : ClusterState O m N} (h0 : ¬ IsDrainState c) {μ k : ℕ} {z : ResidueField O}
    (hμ : 2 ≤ μ) (hk : 1 ≤ k) (hz : z ≠ 0)
    (a : Fin m → O) (w : O) (ha : proj O m N a = c.1) (hw : residue O w = z)
    (h1 : ∀ j, π ^ betaContent c k ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j)
    (h2 : ∀ j < μ, π ^ (betaContent c k + 1) ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j)
    (h3 : ¬ π ^ (betaContent c k + 1) ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff μ) :
    HasChildAt π c μ k z := by
  refine ⟨hμ, hk, hz, ?_⟩
  intro a' w' ha' hw'
  -- `m = 0` is vacuously a drain, so non-drain supplies `0 < m`
  have hm : 1 ≤ m := by
    by_contra hm0
    exact h0 (isDrainState_of_eq_zero (by omega) c)
  have hDN : betaContent c k + 1 ≤ N := by
    have hle := betaContent_le hm hN c h0 k
    omega
  have hdiff : ∀ j, π ^ (betaContent c k + 1) ∣
      (((monicPoly a').comp (Polynomial.C (π ^ k) * (X + Polynomial.C w')))
        - ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w)))).coeff j :=
    fun j => recentre_transport hπ (ha.trans ha'.symm) (hw.trans hw'.symm) hDN h1 j
  have hsplit : ∀ j, ((monicPoly a').comp (Polynomial.C (π ^ k) * (X + Polynomial.C w'))).coeff j
      = ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j
        + (((monicPoly a').comp (Polynomial.C (π ^ k) * (X + Polynomial.C w')))
            - ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w)))).coeff j := by
    intro j
    rw [coeff_sub]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hsplit j]
    exact dvd_add (h1 j) ((pow_dvd_pow π (Nat.le_succ _)).trans (hdiff j))
  · intro j hj
    rw [hsplit j]
    exact dvd_add (h2 j hj) (hdiff j)
  · intro hcon
    refine h3 ?_
    have he : ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff μ
        = ((monicPoly a').comp (Polynomial.C (π ^ k) * (X + Polynomial.C w'))).coeff μ
          - (((monicPoly a').comp (Polynomial.C (π ^ k) * (X + Polynomial.C w')))
              - ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w)))).coeff μ := by
      rw [coeff_sub]; ring
    rw [he]
    exact dvd_sub hcon (hdiff μ)

end Uniformity.Density.Induction

/-! ## 4. Statement pins for the two re-derivations -/

section Pins

open Uniformity.Density Uniformity.Density.Induction Polynomial

/-- The coefficient-swap step, pinned against chapter B's landed `monicPoly_congr` (which lives
in `Uniformity.Density.Leaf` and is therefore not imported here): with the same hypotheses the
re-derived divisibility of §2 is available at `q = X`, where `comp` is the identity. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (hπ : Irreducible π) {m N : ℕ} {a a' : Fin m → O}
    (h : proj O m N a = proj O m N a') (j : ℕ) :
    π ^ N ∣ (monicPoly a - monicPoly a').coeff j := by
  have := pow_dvd_coeff_comp_sub hπ h X j
  rwa [Polynomial.comp_X, Polynomial.comp_X] at this

end Pins

/-! ## 5. TEETH — the recentring arithmetic, on an independent `ℤ`-model

`recCoeffZ m k π w a j` is the triangular expansion of the recentred coefficient, as a numeral
function; `recEvalZ` sums it against powers of `y`, and `monicEvalZ` evaluates the monic
polynomial itself.  Gate (i) below checks `recEvalZ … y = monicEvalZ … (π ^ k * (y + w))` at five
points, which pins the model to the actual substitution — the model is not allowed to certify
itself.  Gates (ii)/(iii) then run H.109's conservativity claim, and its defeat witness, at the
battery cell `π = 2, m = 3, N = 4, k = 1`.

Nothing here is a statement about the Lean `Polynomial` term (see "What this node does NOT
claim" in the header): the model is the battery's arithmetic, reproduced. -/

section NumericGate

/-- The triangular expansion of the `j`-th recentred coefficient of `X ^ m + ∑_{i<m} aᵢ Xⁱ`
under `X ↦ π ^ k (Y + w)`.  Terms with `i < j` vanish because `i.choose j = 0` there. -/
def recCoeffZ (m k : ℕ) (π w : ℤ) (a : ℕ → ℤ) (j : ℕ) : ℤ :=
  ((List.range (m + 1)).map fun i =>
    (if i = m then (1 : ℤ) else a i) * (i.choose j : ℤ) * π ^ (k * i) * w ^ (i - j)).sum

/-- The recentred polynomial, evaluated at `y`. -/
def recEvalZ (m k : ℕ) (π w : ℤ) (a : ℕ → ℤ) (y : ℤ) : ℤ :=
  ((List.range (m + 1)).map fun j => recCoeffZ m k π w a j * y ^ j).sum

/-- `X ^ m + ∑_{i<m} aᵢ Xⁱ`, evaluated at `x`. -/
def monicEvalZ (m : ℕ) (a : ℕ → ℤ) (x : ℤ) : ℤ :=
  x ^ m + ((List.range m).map fun i => a i * x ^ i).sum

/-- The battery cell's coefficient vector `a = (8, 4, 2)` at `m = 3` (capped content
`D = min(3, 2+1, 1+2, 3) = 3`, window `N = 4`, so `D ≤ N − 1` and the state is non-drain). -/
def aCell : ℕ → ℤ := fun i => if i = 0 then 8 else if i = 1 then 4 else 2

/-- The `π ^ N`-perturbed lift of `aCell` (`N = 4`, `π = 2`, so the perturbation is `16`). -/
def aCell' : ℕ → ℤ := fun i => aCell i + 16

-- (i) the model is pinned to the substitution it claims to expand
#guard [(0 : ℤ), 1, 2, -1, 5].all fun y =>
  recEvalZ 3 1 2 0 aCell y == monicEvalZ 3 aCell (2 ^ 1 * (y + 0))

#guard [(0 : ℤ), 1, 2, -1, 5].all fun y =>
  recEvalZ 3 1 2 3 aCell' y == monicEvalZ 3 aCell' (2 ^ 1 * (y + 3))

-- (ii) H.109's conservativity, at `π = 2, m = 3, N = 4, k = 1`, `D = 3`:
-- the lift `(aCell, 0)` and the lift `(aCell', 2)` (coefficients congruent mod `2 ^ 4 = 16`,
-- centres congruent mod `2`) recentre to coefficients congruent mod `2 ^ (D+1) = 16`.
#guard (List.range 4).all fun j =>
  (recCoeffZ 3 1 2 0 aCell j - recCoeffZ 3 1 2 2 aCell' j) % 16 == 0

-- the two moves separately: coefficient swap (mod `2 ^ N = 16`) and centre swap (mod `16`)
#guard (List.range 4).all fun j =>
  (recCoeffZ 3 1 2 0 aCell j - recCoeffZ 3 1 2 0 aCell' j) % 16 == 0
#guard (List.range 4).all fun j =>
  (recCoeffZ 3 1 2 0 aCell j - recCoeffZ 3 1 2 2 aCell j) % 16 == 0

-- (iii) DEFEAT: dropping `residue w = z` (centre `1` instead of `0`, different residues mod 2)
-- breaks the mod-`2 ^ (D+1)` agreement at `j = 0` — the constant terms differ by `24`.
#guard recCoeffZ 3 1 2 1 aCell 0 - recCoeffZ 3 1 2 0 aCell 0 == 24
#guard ¬ ((recCoeffZ 3 1 2 1 aCell 0 - recCoeffZ 3 1 2 0 aCell 0) % 16 == 0)

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.comp_recentre_add
#print axioms Uniformity.Density.Induction.C_dvd_comp
#print axioms Uniformity.Density.Induction.C_dvd_comp_X_add_C_sub
#print axioms Uniformity.Density.Induction.pow_dvd_coeff_comp_sub
#print axioms Uniformity.Density.Induction.pow_succ_dvd_coeff_shift
#print axioms Uniformity.Density.Induction.recentre_transport
#print axioms Uniformity.Density.Induction.HasChildAt
#print axioms Uniformity.Density.Induction.hasChildAt_of_exists

end AxCheck
