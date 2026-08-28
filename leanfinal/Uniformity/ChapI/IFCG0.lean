/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I02

/-!
# Uniformity.ChapI.IFCG0 — the uniform-`a0` campaign's openers: `A0G-Z` and `A0G-RP`

**[A0G1 2026-08-28]** — unit A0G1 (`docs/in-progress/A0_GENERAL_2026-08-28.md` §6, rows
`A0G-Z` and `A0G-RP`; verdict `runs/wave-c/verdict_A0G1.md`).  Part of the `IFCG*` series
proposed by that blueprint for the uniform general-`n` `a0` mechanism.  Nothing here is
signed; nothing binds into leanspec; no landed file is touched.  Zero `sorry`, zero new
axiom; AxCheck footer expects Lean core only.  Neither node touches the C.33 dissection cite.

## §1 — `A0G-Z`: the degree-zero slice

`DecidedSliceAt 0` (`I02.lean:98`).  The blueprint (§2) observes that `decidedSliceAt_all`'s
statement is deliberately guard-free at `n = 0`, and that node `A0G-Z` must prove this slice
*directly from the definitions*: the only monic degree-zero polynomial is `1`, its actual
splitting type is the empty multiset `⟨0⟩`, and **every other** `σ` with `σ.degree = 0` —
including every "malformed" degree-zero label such as `⟨{(0, 5)}⟩` (a nonempty multiset all of
whose products happen to vanish, since `FactorizationType.degree` places no positivity
constraint on its pairs) — gets decided density `0`.  No positivity assumption is used
anywhere in this section; the two values produced are literally `1/1` and `0/1`.

## §2 — `A0G-RP`: finite residue-divisor patterns

Blueprint §4.1's *first layer* of the uniform genre classification: for fixed `n`, a residue
pattern is a finite multiset of pairs `(δ, m)` with `δ ≥ 1`, `m ≥ 1`, `Σ δ·m = n`, describing
closed residue points of degree `δ` occurring with multiplicity `m`.  `ResiduePattern n` is
defined as exactly this — a constrained `FactorizationType` (reusing its `data : Multiset (ℕ ×
ℕ)` carrier, per the blueprint's explicit input list) — and proved finite, decidably
enumerable, and *complete*: `residuePatternFinset n` contains **every** `FactorizationType`
meeting the pattern constraints, not merely a sample.  The finiteness argument is symbolic
(uniform in `n`): every valid pattern's parts are bounded by `n` in both coordinates and in
multiset cardinality (`Multiset.single_le_sum` / `Multiset.card_nsmul_le_sum`), so the whole
object embeds into one finite Sigma-of-`Sym`-types ambient space, built once for every `n`.
This is the *same finiteness technique* `IFC6.exists_uniform_coveringMenu` uses for its output
covering menu (cited there as the precedent for this construction), but **not the same
object**: that theorem enumerates possible `typeOf`-images of actual polynomials at a fixed
degree; `ResiduePattern n` is the combinatorially prior residue-divisor layer that the genre
classification (blueprint §4) convolves *before* any Newton–Okutsu engine is invoked, and its
positivity/degree constraints are purely arithmetic (no `typeOf`, `monicPoly`, or `O` in
sight).  §2 also enumerates `ResiduePattern n` through `n = 6` and records the counts against
an independently-derived divisor/partition formula (see the verdict for the cross-check).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFCG0

open IsLocalRing Polynomial

/-! ## §1 `A0G-Z` — the degree-zero slice -/

section AZ

variable {O : Type*} [CommRing O] [IsDomain O]

omit [IsDomain O] in
/-- The unique `a : Fin 0 → O` produces the polynomial `1` under `monicPoly` — the sum over the
empty index type `Fin 0` vanishes regardless of `a`'s (nonexistent) values. -/
theorem monicPoly_finZero (a : Fin 0 → O) : monicPoly a = (1 : Polynomial O) := by
  simp [monicPoly]

end AZ

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The actual degree-zero splitting type is the empty multiset.** `1` is the only monic
degree-zero polynomial (`monicPoly_finZero`), and `typeOf` of a unit is `⟨0⟩`: any monic
factorization of a unit must be the empty multiset (a nonempty one would force an irreducible,
hence non-unit, factor to divide a unit). -/
theorem typeOf_one : typeOf (1 : Polynomial O) = (⟨(0 : Multiset (ℕ × ℕ))⟩ : FactorizationType) := by
  have hF : IsMonicFactorization (1 : Polynomial O) (0 : Multiset (Polynomial O)) :=
    ⟨by simp, Multiset.prod_zero⟩
  rw [typeOf, monicFactors_eq hF]
  simp

/-- **`A0G-Z`.**  `DecidedSliceAt 0`: at every complete DVR base, the degree-zero decided
density of the empty type `⟨0⟩` is `1` (value `1/1`), and of every other degree-zero label —
in particular every malformed one, e.g. `⟨{(0, 5)}⟩` below — is `0` (value `0/1`).  No
positivity hypothesis on `σ` is used. -/
theorem decidedSliceAt_zero : Uniformity.Density.DecidedSliceAt 0 := by
  intro σ _hσ
  by_cases hσ0 : σ = (⟨(0 : Multiset (ℕ × ℕ))⟩ : FactorizationType)
  · refine ⟨1, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    have hset : ∀ N, decidedSet O 0 σ N = Set.univ := by
      intro N
      apply Set.eq_univ_of_forall
      intro c a _
      rw [monicPoly_finZero a, typeOf_one, hσ0]
    have hseq : ∀ N, decidedSeq O 0 σ N = 1 := by
      intro N
      have hcount : decidedCount O 0 σ N = 1 := by
        unfold decidedCount
        rw [hset N, Nat.card_univ, card_coeff]
        simp
      unfold decidedSeq
      rw [hcount]
      simp
    have hdensity : decidedDensity O 0 σ = 1 := by
      unfold decidedDensity
      have heq : decidedSeq O 0 σ = fun _ => (1 : ℝ) := funext hseq
      rw [heq]
      exact ciSup_const
    rw [hdensity]
    norm_num
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    have hset : ∀ N, decidedSet O 0 σ N = ∅ := by
      intro N
      apply Set.eq_empty_iff_forall_notMem.2
      intro c hc
      obtain ⟨a, ha⟩ := proj_surjective O 0 N c
      have hty := hc a ha
      rw [monicPoly_finZero a, typeOf_one] at hty
      exact hσ0 hty.symm
    have hseq : ∀ N, decidedSeq O 0 σ N = 0 := by
      intro N
      have hcount : decidedCount O 0 σ N = 0 := by
        unfold decidedCount
        rw [hset N]
        simp
      unfold decidedSeq
      rw [hcount]
      simp
    have hdensity : decidedDensity O 0 σ = 0 := by
      unfold decidedDensity
      have heq : decidedSeq O 0 σ = fun _ => (0 : ℝ) := funext hseq
      rw [heq]
      exact ciSup_const
    rw [hdensity]
    norm_num

/-- A concrete witness of a **malformed** degree-zero label distinct from the empty type: the
multiset `{(0, 5)}` is nonempty yet has degree `0` (`FactorizationType.degree` imposes no
positivity constraint on its pairs), so it is exactly the kind of object `decidedSliceAt_zero`
must (and does) also decide, at value `0/1`. -/
example : (⟨({(0, 5)} : Multiset (ℕ × ℕ))⟩ : FactorizationType).degree = 0 := by
  simp [FactorizationType.degree]

example : (⟨({(0, 5)} : Multiset (ℕ × ℕ))⟩ : FactorizationType)
    ≠ (⟨(0 : Multiset (ℕ × ℕ))⟩ : FactorizationType) := by
  intro h
  have hd : ({(0, 5)} : Multiset (ℕ × ℕ)) = 0 := congrArg FactorizationType.data h
  simp at hd

/-! ## §2 `A0G-RP` — finite residue-divisor patterns -/

/-- The finite alphabet of possibly-occurring `(δ, m)` pairs at total `n`: those with `δ ≥ 1`,
`m ≥ 1`, and `δ * m ≤ n`.  Every pair occurring in a residue pattern of `n` lies here
(`mem_residuePatternFinset_iff`'s forward direction). -/
def rpAlphabet (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ n)

/-- **The finite Sigma-of-`Sym` ambient space** — the same technique
`IFC6.exists_uniform_coveringMenu` uses for its covering menu, replayed over the residue-pattern
alphabet: a multiset of size `k ≤ n` over `rpAlphabet n`, for every `k`.  `Finset.univ` on this
Sigma type is what makes `residuePatternFinset` a genuine `Finset`, not merely a `Set`. -/
abbrev RPSigma (n : ℕ) : Type :=
  (k : Fin (n + 1)) × Sym (↥(rpAlphabet n)) (k : ℕ)

/-- The degree of a Sigma-element, computed while staying inside `ℕ × ℕ` (no
`FactorizationType` in sight) — the computable core of the degree filter, and the one that
`#eval` can actually run (unlike a filter phrased on `FactorizationType`, whose only
`DecidableEq` instance is `Classical.decEq`). -/
def rpSigmaDegree (n : ℕ) (s : RPSigma n) : ℕ :=
  ((s.2 : Multiset (↥(rpAlphabet n))).map (fun q => (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2)).sum

/-- The `FactorizationType` reading of a Sigma-element: forget the size bound, keep the
multiset of pairs. -/
def rpEmbed (n : ℕ) (s : RPSigma n) : FactorizationType :=
  ⟨(s.2 : Multiset (↥(rpAlphabet n))).map Subtype.val⟩

theorem rpEmbed_degree (n : ℕ) (s : RPSigma n) : (rpEmbed n s).degree = rpSigmaDegree n s := by
  unfold rpEmbed rpSigmaDegree FactorizationType.degree
  simp [Multiset.map_map, Function.comp]

theorem rpEmbed_injective (n : ℕ) : Function.Injective (rpEmbed n) := by
  rintro ⟨k1, s1⟩ ⟨k2, s2⟩ h
  have hdata : (s1 : Multiset (↥(rpAlphabet n))).map Subtype.val
      = (s2 : Multiset (↥(rpAlphabet n))).map Subtype.val := congrArg FactorizationType.data h
  have hms : (s1 : Multiset (↥(rpAlphabet n))) = (s2 : Multiset (↥(rpAlphabet n))) :=
    Multiset.map_injective Subtype.val_injective hdata
  have hk : k1 = k2 := by
    have h1 : (s1 : Multiset (↥(rpAlphabet n))).card = (k1 : ℕ) := s1.2
    have h2 : (s2 : Multiset (↥(rpAlphabet n))).card = (k2 : ℕ) := s2.2
    have : (k1 : ℕ) = (k2 : ℕ) := by rw [← h1, ← h2, hms]
    exact Fin.ext this
  subst hk
  congr 1
  exact Subtype.ext hms

/-- **The residue-pattern Finset** at `n`: the image of the ambient Sigma space under
"forget the bound, keep the multiset of pairs", restricted to exact degree `n`.  Positivity of
every pair is automatic (every element of `rpAlphabet n` already satisfies it); only the exact
degree needs filtering. -/
def residuePatternFinset (n : ℕ) : Finset FactorizationType :=
  Finset.image (rpEmbed n) ((Finset.univ : Finset (RPSigma n)).filter (fun s => rpSigmaDegree n s = n))

/-- **Fully computable stand-in** for `(residuePatternFinset n).card`: the same filtered Sigma
space, but never routed through `FactorizationType` (hence never needing its `Classical`
`DecidableEq`), so `#eval` can run it. `residuePatternFinset_card_eq` proves it computes the
same number. -/
def rpCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (RPSigma n)).filter (fun s => rpSigmaDegree n s = n)).card

theorem residuePatternFinset_card_eq (n : ℕ) : (residuePatternFinset n).card = rpCount n :=
  Finset.card_image_of_injective _ (rpEmbed_injective n)

/-- **Completeness.**  `σ` is (the `FactorizationType` reading of) a residue pattern of `n` —
i.e. `σ.degree = n` and every pair in `σ.data` has both coordinates `≥ 1` — **iff**
`σ ∈ residuePatternFinset n`.  This is the symbolic (all-`n`) finiteness/completeness
argument the gate demands: no case split on `n`, no appeal to the `n ≤ 6` examples. -/
theorem mem_residuePatternFinset_iff (n : ℕ) (σ : FactorizationType) :
    σ ∈ residuePatternFinset n ↔ σ.degree = n ∧ ∀ p ∈ σ.data, 1 ≤ p.1 ∧ 1 ≤ p.2 := by
  unfold residuePatternFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    refine ⟨by rw [rpEmbed_degree]; exact hs.2, ?_⟩
    intro p hp
    unfold rpEmbed at hp
    obtain ⟨q, _, rfl⟩ := Multiset.mem_map.1 hp
    have hmem := q.2
    simp only [rpAlphabet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
    exact ⟨hmem.2.1, hmem.2.2.1⟩
  · rintro ⟨hdeg, hpos⟩
    have hdeg' : (σ.data.map (fun p => p.1 * p.2)).sum = n := hdeg
    have hbound : ∀ p ∈ σ.data, p ∈ rpAlphabet n := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hpos p hp
      have h1 : p.1 * p.2 ≤ n := by
        have hmem : p.1 * p.2 ∈ σ.data.map (fun q => q.1 * q.2) := Multiset.mem_map_of_mem _ hp
        have hle := Multiset.single_le_sum (fun x (_ : x ∈ σ.data.map (fun q => q.1 * q.2)) =>
          Nat.zero_le x) _ hmem
        rwa [hdeg'] at hle
      have hle1 : p.1 ≤ n := le_trans (Nat.le_mul_of_pos_right _ hp2) h1
      have hle2 : p.2 ≤ n :=
        le_trans (le_trans (Nat.le_mul_of_pos_right _ hp1) (le_of_eq (Nat.mul_comm p.2 p.1))) h1
      simp only [rpAlphabet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hp1, hp2, h1⟩
    have hcard : σ.data.card ≤ n := by
      have h1 : ∀ x ∈ σ.data.map (fun p => p.1 * p.2), 1 ≤ x := by
        rintro x hx
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
        obtain ⟨hp1, hp2⟩ := hpos p hp
        exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      have h2 := Multiset.card_nsmul_le_sum h1
      rw [Multiset.card_map, smul_eq_mul, mul_one, hdeg'] at h2
      exact h2
    set M' : Multiset (↥(rpAlphabet n)) :=
      σ.data.attach.map (fun x => (⟨x.1, hbound x.1 x.2⟩ : ↥(rpAlphabet n))) with hM'
    have hcardM' : M'.card = σ.data.card := by
      rw [hM', Multiset.card_map, Multiset.card_attach]
    have hvalmap : M'.map Subtype.val = σ.data := by
      rw [hM', Multiset.map_map]
      simp [Function.comp]
    have hEq : (⟨M'.map Subtype.val⟩ : FactorizationType) = σ := by rw [hvalmap]
    refine ⟨⟨⟨σ.data.card, by omega⟩, ⟨M', by rw [hcardM']⟩⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← rpEmbed_degree]
      show (⟨M'.map Subtype.val⟩ : FactorizationType).degree = n
      rw [hEq]
      exact hdeg
    · show rpEmbed n _ = σ
      unfold rpEmbed
      exact hEq

/-- **`ResiduePattern n`**: the finite type of residue-divisor patterns of total `n`
(blueprint §4.1) — realized concretely as the subtype of `residuePatternFinset n`, so
`Fintype`/`DecidableEq` are immediate from the ambient `Finset`. -/
def ResiduePattern (n : ℕ) : Type := {σ : FactorizationType // σ ∈ residuePatternFinset n}

instance (n : ℕ) : Fintype (ResiduePattern n) := inferInstanceAs (Fintype ↥(residuePatternFinset n))

instance (n : ℕ) : DecidableEq (ResiduePattern n) :=
  inferInstanceAs (DecidableEq ↥(residuePatternFinset n))

/-- The underlying `(δ, m)` multiset of a residue pattern. -/
def ResiduePattern.data {n : ℕ} (r : ResiduePattern n) : Multiset (ℕ × ℕ) := r.1.data

theorem ResiduePattern.sum_eq {n : ℕ} (r : ResiduePattern n) :
    (r.data.map (fun p => p.1 * p.2)).sum = n :=
  (mem_residuePatternFinset_iff n r.1).1 r.2 |>.1

theorem ResiduePattern.pos {n : ℕ} (r : ResiduePattern n) :
    ∀ p ∈ r.data, 1 ≤ p.1 ∧ 1 ≤ p.2 :=
  (mem_residuePatternFinset_iff n r.1).1 r.2 |>.2

/-! ### The `n ≤ 6` regression check (examples only — not part of the finiteness proof) -/

-- Recorded counts (`#eval`, logged in `runs/wave-c/verdict_A0G1.md`), cross-checked against an
-- independent divisor/partition count: `n=2` (3), `n=3` (5, IFC6's cubic bank), `n=4` (11,
-- blueprint §8's quartic table).  These four are the OFFICIAL count (`rpCount`, defined via the
-- same `Sym`-grid the completeness theorem uses) and are tractable to run.
#eval rpCount 0
#eval rpCount 1
#eval rpCount 2
#eval rpCount 3
#eval rpCount 4

-- The Sym/Sigma ambient space used above is symbolically finite (that is what the completeness
-- theorem proves), but it is combinatorially FAR too large to actually run: at `n = 5` alone
-- `#eval rpCount 5` did not return within 150s (mathlib's generic `Sym`/`Fintype` machinery is
-- built for proof, not computation).  The genuinely executable check below never touches `Sym`,
-- `Sigma`, or `Finset.univ`: it draws directly from the same `(δ, m)` candidates via the
-- standard combinations-with-repetition recursion, and is fast because it only ever builds
-- output-sized lists (no superset-then-filter).  `partial def`: this is a computational check,
-- never cited by a proof, so non-termination-checking costs nothing to the axiom footprint.

/-- Every `(δ, m)` pair with `δ, m ≥ 1` and `δ * m ≤ n`, as a fixed-order `List` — the same
alphabet as `rpAlphabet n`, read off directly instead of through a `Finset`/subtype detour. -/
def rpCandidates (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range n).map (· + 1)).flatMap (fun δ =>
    ((List.range n).map (· + 1)).filterMap (fun m => if δ * m ≤ n then some (δ, m) else none))

/-- All multisets (as non-increasing-in-list-position `List`s, so no multiset is listed twice)
of pairs drawn with repetition from a candidate list, whose `δ * m` weights sum to `remaining`
— the standard unbounded-knapsack/partition enumeration.  Purely a computational aid for the
regression check below; not used by, and not needed for, `mem_residuePatternFinset_iff`. -/
partial def rpGen : List (ℕ × ℕ) → ℕ → List (List (ℕ × ℕ))
  | [], 0 => [[]]
  | [], _ + 1 => []
  | p :: ps, remaining =>
      rpGen ps remaining ++
        (if p.1 * p.2 ≤ remaining then (rpGen (p :: ps) (remaining - p.1 * p.2)).map (p :: ·)
         else [])

/-- The fast regression-check count at `n`, cross-checked against `rpCount` (the official,
`Sym`-grid-derived count) at every `n` where `rpCount` is actually tractable to run (`n ≤ 4`,
below), and against the independently-hand-derived divisor/partition sequence
`1, 1, 3, 5, 11, 17, 34` for `n = 0, …, 6` (recorded in the verdict). -/
def rpCountFast (n : ℕ) : ℕ := (rpGen (rpCandidates n) n).length

#eval rpCountFast 0
#eval rpCountFast 1
#eval rpCountFast 2
#eval rpCountFast 3
#eval rpCountFast 4
#eval rpCountFast 5
#eval rpCountFast 6

end Uniformity.Density.IFCG0

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG0.monicPoly_finZero
#print axioms Uniformity.Density.IFCG0.typeOf_one
#print axioms Uniformity.Density.IFCG0.decidedSliceAt_zero
#print axioms Uniformity.Density.IFCG0.rpEmbed_degree
#print axioms Uniformity.Density.IFCG0.rpEmbed_injective
#print axioms Uniformity.Density.IFCG0.mem_residuePatternFinset_iff
#print axioms Uniformity.Density.IFCG0.residuePatternFinset_card_eq
#print axioms Uniformity.Density.IFCG0.ResiduePattern.sum_eq
#print axioms Uniformity.Density.IFCG0.ResiduePattern.pos
