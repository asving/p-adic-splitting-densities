/-
# IFCG13 — NODE A0G-RW: the rational weights of the genre bank

UNIT A0GW (uniform-a0 campaign, node A0G-RW = blueprint rows RW0/RW1/RW2 of
`docs/in-progress/A0_GENERAL_2026-08-28.md` §6).  For each skeleton `s` in IFCG5's finite
bank at mass `m` — the carrier of IFCG12's unconditional strong genre cover
(`IFCG12.finiteGenreCoverAt_strong_all`) — this file computes the exact valuation-box
measure of its realization locus as a rational function of `q`:

* **§1 the exponent calculus (RW0)**: at fixed slope numerators `num` (IFCG7's
  `ValidSlopeParams` carrier), the cell of coefficient vectors whose recentred polygon
  traces `(s, num)` with prescribed per-face residual patterns has measure
  `(∏ faces, pattern-unit-count) · q^(− skeletonExp s num)`, where `skeletonExp` is the
  explicit ℕ-valued exponent: per face `(b, pat)` of residual degree `d = pat.degree`,
  length `ℓ = b·d`, numerator `h`, sitting above the cumulative right-tail height `Y`,
  the contribution is `ℓ·Y + b·h·d(d−1)/2 + d(h−1)(b−1)/2 + d·h + ℓ` (both halvings
  exact: `d(d−1)` always even, `(h−1)(b−1)` even by `gcd(h,b)=1`).  The doubled affine
  law `2·skeletonExp = expConstD + ∑ₖ num k · expCoeffD k` with
  `expCoeffD k = dₖ(2·tailₖ + ℓₖ + 1) ≥ 2` is the RW1 gate's "positive decay per
  variable".  Machine pins: the loop skeleton gives `h·bigTLoop m + m` — IFCG3's
  `q^(1−T_m)` rescale weight, the A0G-RS anchor.
* **§2 the census interface (the FF boundary)**: `UnitPatternCensus`/`PatternCensus`,
  the carried FF-remainder hypotheses (the FF2 unit discharges them; IFCG4 pins the
  irreducible counts at `δ ≤ 3` and the general count is the recorded remainder).
* **§3 the geometric sums (RW1)**: `coneSum x s = ∑' num ∈ cone(s), x^skeletonExp` over
  the unbounded slope cone; summability from the affine decay; CLOSED FORMS: the general
  single-face law (any denominator `b`, per-unit-class geometric decomposition
  `h = b·t + u`) and the general all-`b=1` multiface staircase law — every geometric
  denominator is `1 − x^A`.
* **§4 the executable mirror**: exact-ℚ truncated evaluator of the full §5 recursion
  (never cited by a proof — IFCG0/IFCG5 `#eval` regression precedent).
* **§5 the value gates**: the n = 2 densities assembled from the weights EQUAL the
  landed G51 laws `q/(2(q+1)), q/(2(q+1)), 1/(q+1)`; the n = 3 assembly equals the five
  IFC7 §9 exact cubic forms, recovered BY NAME against
  `IFC7.genuineDensity_three_exact`; n = 4 is the blueprint §8 table (executable
  regression, §4).
* **§6 the rational package (RW2)**: numerator/denominator pairs in `Polynomial ℚ` with
  the q ≥ 2 nonvanishing gate.

RECORDED REMAINDERS (honest boundary, consumed/discharged downstream): (i) the general
mixed-denominator multiface closed form (Presburger class decomposition; the single-face
and all-`b=1` laws cover the m ≤ 3 symbolic gate, the executable mirror covers m = 4);
(ii) the census instances beyond the pinned low degrees (FF2); (iii) the formal
box-cardinality census tying `skeletonExp` to `MBoxN` counts per level (A0G-FP0's
socket; the loop-skeleton instance is pinned here against IFCG3's landed weight law).
-/

import Uniformity.ChapI.IFCG7
import Uniformity.ChapI.IFCG3
import Uniformity.ChapI.IFCG4
import Uniformity.ChapI.IFCG12

namespace Uniformity.Density.IFCG13

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5
open Uniformity.Density.IFCG7
open Uniformity.Density.IFCG3 (bigTLoop kappaLoop)

/-! ## §1 — The exponent calculus (RW0): the faces' explicit natural gaps -/

/-- **The per-face exponent**: face `f = (b, pat)` with residual degree `d`, length
`ℓ = b·d`, slope numerator `h`, sitting with its right endpoint at cumulative height `Y`
(faces are listed in increasing slope, i.e. right-to-left on the polygon; the polygon's
right endpoint is `(m, 0)`).  The `ℓ·Y` term is the rectangle below the face; the two
halved terms are the staircase under the face's own descent (`⌈·⌉` sums in closed form);
`d·h` is the drop itself; `+ℓ` counts one residue digit per abscissa covered, `+d` of
them lattice-pinned (the residual coefficients), totalling the exact `q`-power of the
cell at fixed parameters. -/
def faceExp (Y : ℕ) (f : FaceShape) (h : ℕ) : ℕ :=
  faceLen f * Y
    + f.1 * h * (faceResDeg f * (faceResDeg f - 1) / 2)
    + faceResDeg f * ((h - 1) * (f.1 - 1) / 2)
    + faceResDeg f * h + faceLen f

/-- The cumulative height of face `i`'s RIGHT endpoint: the total drop of the faces
strictly before it in the list (which sit to its right on the polygon). -/
def baseY (s : List FaceShape) (num : Fin s.length → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, dropAt s num j

/-- **The skeleton exponent** `E(s, num)`: the exact box measure of the realization cell
at fixed slope numerators is `(∏ counts) · q^(−E)`. -/
def skeletonExp (s : List FaceShape) (num : Fin s.length → ℕ) : ℕ :=
  ∑ i : Fin s.length, faceExp (baseY s num i.1) (s.get i) (num i)

/-- The DOUBLED `h k`-coefficient of the affine law: `dₖ · (2·(length after k) + ℓₖ + 1)`. -/
def expCoeffD (s : List FaceShape) (k : Fin s.length) : ℕ :=
  faceResDeg (s.get k)
    * (2 * ∑ j ∈ Finset.univ.filter (fun j : Fin s.length => k < j), faceLen (s.get j)
        + faceLen (s.get k) + 1)

/-- The DOUBLED constant of the affine law: `∑ (ℓₖ + dₖ)`. -/
def expConstD (s : List FaceShape) : ℕ :=
  (s.map (fun f => faceLen f + faceResDeg f)).sum

/-- The doubled per-face law (exact halving under coprimality). -/
theorem faceExp_doubled {f : FaceShape} {h : ℕ} (hcop : Nat.Coprime h f.1) (Y : ℕ) :
    2 * faceExp Y f h
      = 2 * (faceLen f * Y) + f.1 * h * (faceResDeg f * (faceResDeg f - 1))
        + faceResDeg f * ((h - 1) * (f.1 - 1))
        + 2 * (faceResDeg f * h) + 2 * faceLen f := by
  have h2d : 2 ∣ faceResDeg f * (faceResDeg f - 1) := by
    rcases Nat.mod_two_eq_zero_or_one (faceResDeg f) with he | ho
    · exact Dvd.dvd.mul_right (by omega) _
    · exact Dvd.dvd.mul_left (by omega) _
  have h2hb : 2 ∣ (h - 1) * (f.1 - 1) := by
    rcases Nat.mod_two_eq_zero_or_one f.1 with he | ho
    · -- even denominator forces an odd (coprime) numerator
      have hodd : h % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one h with h0 | h1
        · have : (2 : ℕ) ∣ Nat.gcd h f.1 := Nat.dvd_gcd (by omega) (by omega)
          rw [hcop] at this
          omega
        · exact h1
      exact Dvd.dvd.mul_right (by omega) _
    · exact Dvd.dvd.mul_left (by omega) _
  obtain ⟨c₁, hc₁⟩ := h2d
  obtain ⟨c₂, hc₂⟩ := h2hb
  unfold faceExp
  rw [hc₁, hc₂, Nat.mul_div_cancel_left c₁ (by norm_num), Nat.mul_div_cancel_left c₂
    (by norm_num)]
  ring

/-- `baseY` as a `Fin`-filtered sum (the `dropAt` dites discharged). -/
theorem baseY_eq_fin (s : List FaceShape) (num : Fin s.length → ℕ) (i : Fin s.length) :
    baseY s num i.1
      = ∑ j ∈ Finset.univ.filter (fun j : Fin s.length => j < i),
          num j * faceResDeg (s.get j) := by
  unfold baseY
  refine Finset.sum_nbij'
    (fun j => (⟨j % s.length, Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin s.length))
    (fun j => j.1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjs : j < s.length := lt_trans hj' i.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    simpa [Nat.mod_eq_of_lt hjs] using hj'
  · intro j hj
    exact Finset.mem_range.2 (Finset.mem_filter.1 hj).2
  · intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjs : j < s.length := lt_trans hj' i.isLt
    simp [Nat.mod_eq_of_lt hjs]
  · intro j hj
    exact Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt])
  · intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjs : j < s.length := lt_trans hj' i.isLt
    simp [dropAt, dif_pos hjs, Nat.mod_eq_of_lt hjs]

/-- **The triangle exchange**: the rectangle terms `ℓᵢ·Yᵢ` re-sum to the per-numerator
tail terms `hⱼ·dⱼ·tailⱼ` — the cross-term bookkeeping of the affine law. -/
theorem sum_len_baseY (s : List FaceShape) (num : Fin s.length → ℕ) :
    ∑ i : Fin s.length, faceLen (s.get i) * baseY s num i.1
      = ∑ j : Fin s.length, num j * faceResDeg (s.get j)
          * ∑ i ∈ Finset.univ.filter (fun i : Fin s.length => j < i), faceLen (s.get i) := by
  simp_rw [baseY_eq_fin, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ)
    (s' := fun j => Finset.univ.filter (fun i : Fin s.length => j < i))
    (by intro x y; simp)]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _

/-- `expConstD` as a `Fin`-indexed sum. -/
theorem expConstD_eq (s : List FaceShape) :
    expConstD s = ∑ k : Fin s.length, (faceLen (s.get k) + faceResDeg (s.get k)) := by
  unfold expConstD
  have h4 : List.ofFn (fun i => faceLen (s.get i) + faceResDeg (s.get i))
      = s.map (fun f => faceLen f + faceResDeg f) := by
    conv_rhs => rw [← List.ofFn_get s]
    rw [List.map_ofFn]
    rfl
  rw [← h4, List.sum_ofFn]

/-- **The affine law (RW1's decay carrier)**:
`2·E(s, num) = expConstD s + ∑ k, num k · expCoeffD s k` over valid parameters. -/
theorem skeletonExp_affine {s : List FaceShape} (hs : ∀ f ∈ s, ValidFace f)
    {num : Fin s.length → ℕ} (hnum : ValidSlopeParams s num) :
    2 * skeletonExp s num = expConstD s + ∑ k : Fin s.length, num k * expCoeffD s k := by
  have key : ∀ i : Fin s.length,
      (2 * faceExp (baseY s num i.1) (s.get i) (num i) : ℤ)
        = (faceLen (s.get i) + faceResDeg (s.get i) : ℤ)
          + (num i : ℤ) * (expCoeffD s i : ℤ)
          + 2 * ((faceLen (s.get i) : ℤ) * (baseY s num i.1 : ℤ))
          - 2 * ((num i : ℤ) * (faceResDeg (s.get i) : ℤ)
              * ((∑ j ∈ Finset.univ.filter (fun j : Fin s.length => i < j),
                  faceLen (s.get j) : ℕ) : ℤ)) := by
    intro i
    have hvf : ValidFace (s.get i) := hs _ (List.get_mem s i)
    have hb1 : 1 ≤ (s.get i).1 := hvf.1
    have hd1 : 1 ≤ faceResDeg (s.get i) := hvf.2.1
    have hh1 : 1 ≤ num i := (hnum.1 i).1
    have hdb := faceExp_doubled (hnum.1 i).2 (baseY s num i.1)
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hdb
    push_cast [Nat.cast_sub hd1, Nat.cast_sub hb1, Nat.cast_sub hh1] at hcast
    rw [hcast]
    unfold expCoeffD
    push_cast
    have hlen : (faceLen (s.get i) : ℤ) = ((s.get i).1 : ℤ) * (faceResDeg (s.get i) : ℤ) := by
      rw [show faceLen (s.get i) = (s.get i).1 * faceResDeg (s.get i) from rfl]
      push_cast
      ring
    rw [hlen]
    ring
  have hZ : (2 * skeletonExp s num : ℤ)
      = (expConstD s : ℤ) + ∑ k : Fin s.length, (num k : ℤ) * (expCoeffD s k : ℤ) := by
    have h2E : (2 * skeletonExp s num : ℤ)
        = ∑ i : Fin s.length, (2 * faceExp (baseY s num i.1) (s.get i) (num i) : ℤ) := by
      unfold skeletonExp
      push_cast [Finset.mul_sum]
      rfl
    rw [h2E, Finset.sum_congr rfl fun i _ => key i,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hexch := congrArg (Nat.cast : ℕ → ℤ) (sum_len_baseY s num)
    push_cast at hexch
    have hconst := congrArg (Nat.cast : ℕ → ℤ) (expConstD_eq s)
    push_cast at hconst
    rw [hconst]
    push_cast
    linear_combination (2 : ℤ) * hexch
  exact_mod_cast hZ

/-- Positive decay per variable: every doubled coefficient is at least `2`. -/
theorem two_le_expCoeffD {s : List FaceShape} (hs : ∀ f ∈ s, ValidFace f)
    (k : Fin s.length) : 2 ≤ expCoeffD s k := by
  have hvf : ValidFace (s.get k) := hs _ (List.get_mem s k)
  have hd1 : 1 ≤ faceResDeg (s.get k) := hvf.2.1
  have hl1 : 1 ≤ faceLen (s.get k) := faceLen_pos hvf
  calc 2 = 1 * 2 := by norm_num
    _ ≤ faceResDeg (s.get k)
        * (2 * ∑ j ∈ Finset.univ.filter (fun j : Fin s.length => k < j), faceLen (s.get j)
            + faceLen (s.get k) + 1) := Nat.mul_le_mul hd1 (by omega)

/-- The summability floor: `∑ num ≤ E(s, num)`. -/
theorem sum_num_le_skeletonExp {s : List FaceShape} (hs : ∀ f ∈ s, ValidFace f)
    {num : Fin s.length → ℕ} (hnum : ValidSlopeParams s num) :
    ∑ k : Fin s.length, num k ≤ skeletonExp s num := by
  have haff := skeletonExp_affine hs hnum
  have hterm : ∑ k : Fin s.length, num k * 2 ≤ ∑ k : Fin s.length, num k * expCoeffD s k :=
    Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_left _ (two_le_expCoeffD hs k))
  have h2 : ∑ k : Fin s.length, num k * 2 = 2 * ∑ k : Fin s.length, num k := by
    rw [← Finset.sum_mul, mul_comm]
  omega

/-- Singleton skeletons: the exponent is the lone face's at cumulative height `0`. -/
theorem skeletonExp_singleton (f : FaceShape) (num : Fin 1 → ℕ) :
    skeletonExp [f] num = faceExp 0 f (num 0) := by
  show ∑ i : Fin 1, faceExp (baseY [f] num i.1) (([f] : List FaceShape).get i) (num i)
      = faceExp 0 f (num 0)
  rw [Fin.sum_univ_one]
  rfl

/-- **The A0G-RS pin**: the loop skeleton's exponent is `h·T_m + m` — the box-relative
loop weight `q^(−h·T_m)` on `q^(−m)`-worth of re-entry box, IFCG3's `q^(1−T_m)` at
`h = 1` after the `(q−1)`-fold recentring count. -/
theorem skeletonExp_loopSkeleton (m : ℕ) (num : Fin 1 → ℕ) :
    skeletonExp (loopSkeleton m) num = num 0 * bigTLoop m + m := by
  have hT : bigTLoop m = kappaLoop m + m :=
    Uniformity.Density.IFCG3.bigTLoop_eq_kappaLoop_add m
  show skeletonExp [loopFace m] num = num 0 * bigTLoop m + m
  rw [skeletonExp_singleton, faceExp, faceResDeg_loopFace, faceLen_loopFace,
    show (loopFace m).1 = 1 from rfl, hT,
    show m * (m - 1) / 2 = kappaLoop m from rfl]
  simp only [Nat.sub_self, Nat.zero_div, mul_zero]
  ring

/-! ## §2 — The census interface: the FF boundary -/

section Census

open Polynomial

/-- The UFD factorization pattern of a polynomial over a field, as a `FactorizationType`
in the FACE reading of the pairs — `(δ, μ)` = (irreducible-factor degree, multiplicity).
Junk (`⟨0⟩`) at `g = 0` or units. -/
noncomputable def fieldPattern {K : Type*} [Field K] (g : Polynomial K) :
    FactorizationType :=
  letI := Classical.decEq K
  ⟨(UniqueFactorizationMonoid.normalizedFactors g).toFinset.val.map
    (fun p => (p.natDegree, (UniqueFactorizationMonoid.normalizedFactors g).count p))⟩

/-- **The unit-root census hypothesis (the carried FF remainder)**: `N ∈ Polynomial ℚ`
counts, over EVERY finite field, the monic polynomials of the pattern's degree with
NONZERO constant term and UFD pattern `pat` — the count entering each face's weight
(a face residual polynomial has exact endpoints, hence no zero root). -/
def UnitPatternCensus (pat : FactorizationType) (N : Polynomial ℚ) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K],
    (Nat.card {v : Fin pat.degree → K //
        (Uniformity.Density.monicPoly v).coeff 0 ≠ 0 ∧
        fieldPattern (Uniformity.Density.monicPoly v) = pat} : ℚ)
      = N.eval (Fintype.card K : ℚ)

/-- **The level-1 census hypothesis**: as `UnitPatternCensus` but with zero roots
allowed — the counts of the blueprint §8 second column, entering the residue-pattern
convolution of the affine assembly. -/
def PatternCensus (pat : FactorizationType) (N : Polynomial ℚ) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K],
    (Nat.card {v : Fin pat.degree → K //
        fieldPattern (Uniformity.Density.monicPoly v) = pat} : ℚ)
      = N.eval (Fintype.card K : ℚ)

end Census

/-! ### The face-pattern constants of the m ≤ 3 symbolic gate

FACE patterns use the `(δ, μ)` reading (IFCG5 §5: `p.1` = residual point degree,
`p.2` = multiplicity; `loopFace m = (1, ⟨{(1, m)}⟩)`). -/

/-- One simple rational point. -/
def rp11 : FactorizationType := ⟨{(1, 1)}⟩
/-- One rational double point (the mass-2 loop pattern). -/
def rp12 : FactorizationType := ⟨{(1, 2)}⟩
/-- Two distinct rational points. -/
def rp11p11 : FactorizationType := ⟨{(1, 1), (1, 1)}⟩
/-- One quadratic point. -/
def rp21 : FactorizationType := ⟨{(2, 1)}⟩
/-- One rational triple point (the mass-3 loop pattern). -/
def rp13 : FactorizationType := ⟨{(1, 3)}⟩
/-- A simple point beside a double point. -/
def rp11p12 : FactorizationType := ⟨{(1, 1), (1, 2)}⟩
/-- Three distinct rational points. -/
def rp11cube : FactorizationType := ⟨{(1, 1), (1, 1), (1, 1)}⟩
/-- A rational point beside a quadratic point. -/
def rp11p21 : FactorizationType := ⟨{(1, 1), (2, 1)}⟩
/-- One cubic point. -/
def rp31 : FactorizationType := ⟨{(3, 1)}⟩

/-! ## §3 — The cone sums (RW1): geometric summation over the unbounded numerators -/

section ConeSum

/-- The slope cone of a skeleton: IFCG7's canonical parameter carrier. -/
abbrev ConeType (s : List FaceShape) : Type :=
  {num : Fin s.length → ℕ // ValidSlopeParams s num}

/-- **The cone sum**: the total `x^E` mass over the unbounded slope cone (`x = q⁻¹`
downstream).  The face-count factors are constant on the cone and multiply outside. -/
noncomputable def coneSum (x : ℝ) (s : List FaceShape) : ℝ :=
  ∑' p : ConeType s, x ^ skeletonExp s p.1

/-- Summability over the cone (RW1's convergence gate), from the affine decay floor. -/
theorem coneSum_summable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {s : List FaceShape} (hs : ∀ f ∈ s, ValidFace f) :
    Summable (fun p : ConeType s => x ^ skeletonExp s p.1) := by
  sorry

/-- **The general single-face closed form** (any denominator `b ≥ 1`): decomposing
`h = b·t + u` over the unit classes `u ∈ [1, b]`, `gcd(u, b) = 1`, each class is one
geometric series of ratio `x^(b·c₂/2)` where `c₂ = d(ℓ+1)` is the doubled coefficient. -/
theorem coneSum_single {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {f : FaceShape}
    (hf : ValidFace f) :
    coneSum x [f]
      = (∑ u ∈ (Finset.Icc 1 f.1).filter (fun u => Nat.Coprime u f.1),
          x ^ skeletonExp [f] (fun _ => u))
        / (1 - x ^ (f.1 * (faceResDeg f * (faceLen f + 1)) / 2)) := by
  sorry

/-- **The all-`b = 1` staircase closed form**: when every face is unit-denominator the
cone is the staircase `num k = k + 1 + ∑_{i ≤ k} tᵢ` over `t ∈ ℕ^r`, and the sum
factors into one geometric series per variable with ratio exponent
`Aₖ = (∑_{j ≥ k} expCoeffD j)/2`. -/
theorem coneSum_unit_denominators {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {s : List FaceShape} (hs : ∀ f ∈ s, ValidFace f) (hb : ∀ f ∈ s, f.1 = 1) :
    coneSum x s
      = x ^ skeletonExp s (fun k => k.1 + 1)
        / ∏ k : Fin s.length,
            (1 - x ^ ((∑ j ∈ Finset.univ.filter (fun j : Fin s.length => k ≤ j),
              expCoeffD s j) / 2)) := by
  sorry

end ConeSum

/-! ## §5 — The value gates: n = 2 symbolic (against G51), n = 3 symbolic (against
IFC7's `genuineDensity_three_exact`), n = 4 executable (§4 mirror vs blueprint §8) -/

section Gates

/-- The loop factor `λ_m`: the total same-mass re-entry weight of the diagonal rescale
cell, box-relative — `(q−1)/(q^{T_m} − 1)` once solved. -/
noncomputable def loopFactor (m : ℕ) (q : ℝ) : ℝ :=
  q ^ m * (q - 1) * coneSum q⁻¹ (loopSkeleton m)

/-- Loop factor closed form (the A0G-RS full-weight pin, all masses). -/
theorem loopFactor_eq {q : ℝ} (hq : 2 ≤ q) (m : ℕ) (hm : 1 ≤ m) :
    loopFactor m q = (q - 1) / (q ^ bigTLoop m - 1) := by
  sorry

/-! ### n = 2: the five-skeleton bank assembled -/

/-- Mass-2 shallow split weight: the split-residual single face + the two-face staircase. -/
noncomputable def shallow2Split (q : ℝ) : ℝ :=
  (q - 1) * (q - 2) / 2 * coneSum q⁻¹ [((1 : ℕ), rp11p11)]
    + (q - 1) ^ 2 * coneSum q⁻¹ [((1 : ℕ), rp11), ((1 : ℕ), rp11)]

/-- Mass-2 shallow inert weight: the irreducible-quadratic-residual face. -/
noncomputable def shallow2Inert (q : ℝ) : ℝ :=
  (q ^ 2 - q) / 2 * coneSum q⁻¹ [((1 : ℕ), rp21)]

/-- Mass-2 shallow ramified weight: the denominator-2 face. -/
noncomputable def shallow2Ram (q : ℝ) : ℝ :=
  (q - 1) * coneSum q⁻¹ [((2 : ℕ), rp11)]

/-- The mass-2 cluster conditional probability of each type: the diagonal fixed point
`P = q²·shallow + λ₂·P` solved. -/
noncomputable def clusterP2 (shallow : ℝ → ℝ) (q : ℝ) : ℝ :=
  q ^ 2 * shallow q / (1 - loopFactor 2 q)

/-- The full monic quadratic density assembled from the weights: level-1 cell count
plus `q` double-root recentrings of the cluster conditional. -/
noncomputable def n2Density (level1 : ℝ) (P : ℝ) (q : ℝ) : ℝ :=
  (level1 + q * P) / q ^ 2

/-- **n = 2 GATE, split** = the landed `G51` law `X / (2(X+1))`. -/
theorem n2_gate_split {q : ℝ} (hq : 2 ≤ q) :
    n2Density (q * (q - 1) / 2) (clusterP2 shallow2Split q) q = q / (2 * (q + 1)) := by
  sorry

/-- **n = 2 GATE, inert** = the landed `G51` law `X / (2(X+1))`. -/
theorem n2_gate_inert {q : ℝ} (hq : 2 ≤ q) :
    n2Density ((q ^ 2 - q) / 2) (clusterP2 shallow2Inert q) q = q / (2 * (q + 1)) := by
  sorry

/-- **n = 2 GATE, ramified** = the landed `G51` law `1 / (X+1)`. -/
theorem n2_gate_ram {q : ℝ} (hq : 2 ≤ q) :
    n2Density 0 (clusterP2 shallow2Ram q) q = 1 / (q + 1) := by
  sorry

/-! ### n = 3: the fifteen-skeleton bank assembled -/

/-- The common mass-2-child factor of the mass-3 bank: the three skeletons carrying a
`(1,2)` entry (child mass 2, multiplied by the mass-2 conditional law downstream). -/
noncomputable def child3 (q : ℝ) : ℝ :=
  (q - 1) * (q - 2) * coneSum q⁻¹ [((1 : ℕ), rp11p12)]
    + (q - 1) ^ 2 * (coneSum q⁻¹ [((1 : ℕ), rp11), ((1 : ℕ), rp12)]
      + coneSum q⁻¹ [((1 : ℕ), rp12), ((1 : ℕ), rp11)])

/-- Mass-3 shallow split weight. -/
noncomputable def shallow3Split (q : ℝ) : ℝ :=
  (q - 1) * (q - 2) * (q - 3) / 6 * coneSum q⁻¹ [((1 : ℕ), rp11cube)]
    + (q - 1) ^ 2 * (q - 2) / 2 * (coneSum q⁻¹ [((1 : ℕ), rp11), ((1 : ℕ), rp11p11)]
      + coneSum q⁻¹ [((1 : ℕ), rp11p11), ((1 : ℕ), rp11)])
    + (q - 1) ^ 3 * coneSum q⁻¹ [((1 : ℕ), rp11), ((1 : ℕ), rp11), ((1 : ℕ), rp11)]
    + clusterP2 shallow2Split q * child3 q

/-- Mass-3 shallow linear-times-inert weight. -/
noncomputable def shallow3LinInert (q : ℝ) : ℝ :=
  (q - 1) * ((q ^ 2 - q) / 2) * (coneSum q⁻¹ [((1 : ℕ), rp11p21)]
      + coneSum q⁻¹ [((1 : ℕ), rp11), ((1 : ℕ), rp21)]
      + coneSum q⁻¹ [((1 : ℕ), rp21), ((1 : ℕ), rp11)])
    + clusterP2 shallow2Inert q * child3 q

/-- Mass-3 shallow linear-times-ramified weight (the two mixed-denominator pairs). -/
noncomputable def shallow3LinRam (q : ℝ) : ℝ :=
  (q - 1) ^ 2 * (coneSum q⁻¹ [((1 : ℕ), rp11), ((2 : ℕ), rp11)]
      + coneSum q⁻¹ [((2 : ℕ), rp11), ((1 : ℕ), rp11)])
    + clusterP2 shallow2Ram q * child3 q

/-- Mass-3 shallow inert (cubic residual) weight. -/
noncomputable def shallow3Inert (q : ℝ) : ℝ :=
  (q ^ 3 - q) / 3 * coneSum q⁻¹ [((1 : ℕ), rp31)]

/-- Mass-3 shallow totally-ramified weight (the denominator-3 face). -/
noncomputable def shallow3Ram (q : ℝ) : ℝ :=
  (q - 1) * coneSum q⁻¹ [((3 : ℕ), rp11)]

/-- The mass-3 cluster conditional: the diagonal fixed point at `λ₃` solved. -/
noncomputable def clusterP3 (shallow : ℝ → ℝ) (q : ℝ) : ℝ :=
  q ^ 3 * shallow q / (1 - loopFactor 3 q)

/-- The full monic cubic density assembled: level-1 count, plus the `q(q−1)` cells with
one double root carrying the mass-2 law, plus the `q` triple-root cells carrying the
mass-3 law. -/
noncomputable def n3Density (level1 : ℝ) (P2part P3part : ℝ) (q : ℝ) : ℝ :=
  (level1 + q * (q - 1) * P2part + q * P3part) / q ^ 3

/-- **n = 3 GATE, split** = IFC7 §9's exact form. -/
theorem n3_gate_split {q : ℝ} (hq : 2 ≤ q) :
    n3Density (q * (q - 1) * (q - 2) / 6) (clusterP2 shallow2Split q)
        (clusterP3 shallow3Split q) q
      = q ^ 3 * (q ^ 2 - q + 1)
        / (6 * (q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  sorry

/-- **n = 3 GATE, linear × inert** = IFC7 §9's exact form. -/
theorem n3_gate_linInert {q : ℝ} (hq : 2 ≤ q) :
    n3Density (q * ((q ^ 2 - q) / 2)) (clusterP2 shallow2Inert q)
        (clusterP3 shallow3LinInert q) q
      = q ^ 3 * (q ^ 2 + q + 1)
        / (2 * (q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  sorry

/-- **n = 3 GATE, inert** = IFC7 §9's exact form. -/
theorem n3_gate_inert {q : ℝ} (hq : 2 ≤ q) :
    n3Density ((q ^ 3 - q) / 3) 0 (clusterP3 shallow3Inert q) q
      = q ^ 3 * (q + 1) / (3 * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  sorry

/-- **n = 3 GATE, linear × ramified** = IFC7 §9's exact form. -/
theorem n3_gate_linRam {q : ℝ} (hq : 2 ≤ q) :
    n3Density 0 (clusterP2 shallow2Ram q) (clusterP3 shallow3LinRam q) q
      = q * (q ^ 3 + q + 1) / ((q + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) := by
  sorry

/-- **n = 3 GATE, totally ramified** = IFC7 §9's exact form. -/
theorem n3_gate_ram {q : ℝ} (hq : 2 ≤ q) :
    n3Density 0 0 (clusterP3 shallow3Ram q) q
      = (q ^ 2 + 1) / (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) := by
  sorry

/-! ### The by-name recovery against the landed cubic capstone -/

section Recovery

open IsLocalRing

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **THE LANDED-VALUE RECOVERY (totally ramified)**: the weight-calculus assembly of
this file EQUALS the landed `IFC7.genuineDensity_three_exact` value, by name, over every
complete DVR with finite residue field. -/
theorem n3_recovery_ram (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 3 (Uniformity.Density.c3ram)
      = n3Density 0 0 (clusterP3 shallow3Ram (residueCard O : ℝ)) (residueCard O : ℝ) := by
  sorry

/-- **THE LANDED-VALUE RECOVERY (split)**: as `n3_recovery_ram`, for the split type. -/
theorem n3_recovery_split (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 3 (Uniformity.Density.c3split)
      = n3Density ((residueCard O : ℝ) * ((residueCard O : ℝ) - 1)
            * ((residueCard O : ℝ) - 2) / 6)
          (clusterP2 shallow2Split (residueCard O : ℝ))
          (clusterP3 shallow3Split (residueCard O : ℝ)) (residueCard O : ℝ) := by
  sorry

end Recovery

end Gates

/-! ## §6 — The rational package (RW2): `Polynomial ℚ` pairs and the q ≥ 2 gate -/

section Package

open Polynomial

/-- **The RW2 carrier**: a rational function of `q` as a numerator/denominator pair with
BOTH denominator obligations (the exact shape `DecidedSliceAt` demands). -/
structure RatWeight where
  /-- The numerator. -/
  num : Polynomial ℚ
  /-- The denominator. -/
  den : Polynomial ℚ
  /-- The denominator is not the zero polynomial. -/
  den_ne : den ≠ 0
  /-- The denominator vanishes at no rational `q ≥ 2` (hence at no residue cardinality). -/
  den_eval_ne : ∀ γ : ℚ, 2 ≤ γ → den.eval γ ≠ 0

/-- The geometric denominators are safe: `c · ∏ (X^{aᵢ} − 1)` with `c ≠ 0`, `aᵢ ≥ 1`
never vanishes at `γ ≥ 2` (each factor is `≥ 2^{aᵢ} − 1 ≥ 1`). -/
theorem den_eval_ne_of_geom (c : ℚ) (hc : c ≠ 0) (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a)
    (γ : ℚ) (hγ : 2 ≤ γ) :
    (Polynomial.C c * (l.map (fun a => Polynomial.X ^ a - 1)).prod).eval γ ≠ 0 := by
  sorry

end Package

end Uniformity.Density.IFCG13

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` on the
§1/§3/§5/§6 calculus (nothing here consumes the dissection cite; the cover import is the
carrier binding only) -/

#print axioms Uniformity.Density.IFCG13.skeletonExp_loopSkeleton
