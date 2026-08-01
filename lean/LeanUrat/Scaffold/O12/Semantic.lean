/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.O12.PolygonData
import LeanUrat.L4

/-!
# Scaffold/O12/Semantic — the semantic hypothesis rows [unit II-M0]

STATEMENT LAYER ONLY: the `SemanticRows` structure, transcribed verbatim from
`lean/blueprints/BP_II.md` §1.9 (unit II-M0 of the unit table; rows table §1.10).
Semantic-guardian audit + Codex review REQUIRED before any prover consumes these
rows (BP_II §2 unit II-M0). The analytic inputs enter by the corpus's
recorded-via-hypothesis convention (cf. `LeanUrat.L4.cellVolume_eq`'s `hfactor`,
`R1.stratum_volume`, `L2core.perShapeVolume_baseChange`): ONE displayed structure
of rows, everything downstream derived sorry-free. These are NAMED hypothesis
rows — never axioms, never discharged by fiat.

## The named hypothesis rows (BP_II §1.10; the movement's honest conditionality)

| row | content | discharge path |
|---|---|---|
| **(HAAR-COORD)** `SemanticRows.haar*` | per-coordinate valuation measure law + independence | the corpus convention (L4 `hfactor`); a future `PadicMeasure` bridge could discharge it — out of Movement II scope |
| **(NP-SLOPES)** `SemanticRows.npSlopes` | root valuations = polygon slopes | standard (Neukirch II.6); consumed only by L6e(i)/L1-last-sentence — off the pole-free path |
| **(TYPE-INV)** `SemanticRows.type*` | L2/L3 splitting-type preservation | VALUE-side, expressly outside the O-12 claim; consumed by Movements IV–V only |

§1.9 results are conditional exactly on these displayed semantic rows.

## Display adjustment (sanctioned; same convention as `Scaffold/Spine.lean`)

BP_II §1 head: "Signatures are sketches: provers may adjust implicit
binders/instance arguments, never the mathematical content." The §1.9 display
binds `(Coeff … : Type*)` with no algebraic instance, but `Polynomial Coeff`
requires one (`Mathlib.Algebra.Polynomial.Basic`:
`structure Polynomial (R : Type*) [Semiring R]`); verbatim, elaboration fails
with "failed to synthesize Semiring Coeff". The unique minimal repair is the
instance binder `[Semiring Coeff]`, added below; no other token changes.
-/

set_option linter.style.longLine false

open scoped ENNReal

namespace LeanUrat.Scaffold

/-- **The semantic rows** (the [M]-style hypothesis structure of this movement;
each field is a standard cited fact, flagged for the semantic-guardian audit):
(HAAR-COORD) the per-coordinate valuation law μ{v ≥ t} = q₀^{−t}, μ{v = t} =
(1−q₀^{−1})q₀^{−t}, coordinates independent (brief §2.1; = L4.lean's `hfactor`
convention); (NP-SLOPES) the multiset of root valuations equals the multiset of
Newton-polygon slopes (brief L1 last sentence; standard, cite Neukirch II.6);
(TYPE-INV) splitting types invariant under x ↦ πx rescale and x ↦ x + c recenter
(brief L2/L3 — VALUE-side, consumed only by Movements IV–V). -/
structure SemanticRows
    (Coeff Root Γ TypeCode : Type*)
    [Semiring Coeff]
    [LinearOrderedCommGroupWithZero Γ]
    (valuation : Coeff → Γ)
    (coeffVector : Polynomial Coeff → ℕ → Coeff)
    (rootValues polygonSlopes : Polynomial Coeff → Multiset Γ)
    (splitType : Polynomial Coeff → TypeCode)
    (rescale recenter : Polynomial Coeff → Polynomial Coeff)
    (coordMeasure : Set Coeff → ℝ≥0∞)
    (q₀ : ℝ≥0∞) where
  haarBall :
    ∀ t : ℕ, coordMeasure {a | valuation a ≤ (valuation a) ^ t} = (q₀ ^ t)⁻¹
  haarShell :
    ∀ t : ℕ, coordMeasure {a | valuation a = (valuation a) ^ t} =
      (1 - q₀⁻¹) * (q₀ ^ t)⁻¹
  haarIndep :
    ∀ (I : Finset ℕ) (A : ℕ → Set Coeff),
      coordMeasure {a | ∀ i ∈ I, a ∈ A i} =
        ∏ i ∈ I, coordMeasure (A i)
  npSlopes :
    ∀ g : Polynomial Coeff, rootValues g = polygonSlopes g
  typeRescale :
    ∀ g : Polynomial Coeff, splitType (rescale g) = splitType g
  typeRecenter :
    ∀ g : Polynomial Coeff, splitType (recenter g) = splitType g

/-!
## Unit II-M5 — `recenter_triangular` (L3 algebraic half)

BP_II §1.9 displays this unit as `theorem recenter_triangular ...` — the signature is
elided in the blueprint; the mathematical content is pinned by the displayed docstring
("coeff i of h(c + y) = a_i + (polynomial in a_{<i}, c)", via `Polynomial.taylor`) and
the §2 unit-table sketch ("`Polynomial.taylor` coefficients: a_i + poly(a_{<i}, c)").
Formalization note (same sanctioned-adjustment convention as the `[Semiring Coeff]`
repair above): for `h := Polynomial.taylor c g` — i.e. `h(y) = g(y + c)`,
`Polynomial.taylor_apply` — the `i`-th coefficient is `g.coeff i` plus an EXPLICIT
polynomial expression in `c` and the coefficients `g.coeff k` for `k > i` ONLY.
Lean's `coeff` indexes bottom-up by degree; the blueprint's `a_j` is the monic
top-down index (`a_j` = coeff of `x^(n-j)`), so "poly(a_{<j}, c)" = higher-degree
coefficients = `g.coeff k, k > i` here. Triangularity with unit diagonal is manifest:
the correction term ranges over `Finset.Ioc i g.natDegree` (strictly above the
diagonal), and the diagonal entry is the unit `(i.choose i) * c ^ 0 = 1`.
-/

/-- L3 algebraic half: recentering is coefficient-triangular with unit diagonal:
coeff i of h(c + y) = a_i + (polynomial in a_{<i}, c) (`Polynomial.taylor`). -/
theorem recenter_triangular {Coeff : Type*} [Semiring Coeff]
    (g : Polynomial Coeff) (c : Coeff) (i : ℕ) :
    (Polynomial.taylor c g).coeff i =
      g.coeff i + ∑ k ∈ Finset.Ioc i g.natDegree,
        (k.choose i : Coeff) * g.coeff k * c ^ (k - i) := by
  -- Step 1: the coefficient as a support sum (Mathlib's Taylor/Hasse-derivative API).
  have hsupp : (Polynomial.taylor c g).coeff i =
      ∑ k ∈ g.support, (k.choose i : Coeff) * g.coeff k * c ^ (k - i) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.eval_sum,
      Polynomial.sum_def]
    simp only [Polynomial.eval_monomial]
  -- Step 2: enlarge the support sum to `range (natDegree + 1)` (missing coeffs are 0).
  have hrange : ∑ k ∈ g.support, (k.choose i : Coeff) * g.coeff k * c ^ (k - i) =
      ∑ k ∈ Finset.range (g.natDegree + 1),
        (k.choose i : Coeff) * g.coeff k * c ^ (k - i) :=
    Finset.sum_subset g.supp_subset_range_natDegree_succ fun k _ hk => by
      rw [Polynomial.notMem_support_iff.mp hk, mul_zero, zero_mul]
  -- Step 3: shrink to `Icc i natDegree` (below-diagonal binomial coefficients vanish).
  have hIcc : ∑ k ∈ Finset.Icc i g.natDegree,
        (k.choose i : Coeff) * g.coeff k * c ^ (k - i) =
      ∑ k ∈ Finset.range (g.natDegree + 1),
        (k.choose i : Coeff) * g.coeff k * c ^ (k - i) :=
    Finset.sum_subset
      (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2))
      fun k hk hk' => by
        have hki : k < i := by
          rcases Nat.lt_or_ge k i with h | h
          · exact h
          · exact absurd (Finset.mem_Icc.mpr
              ⟨h, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩) hk'
        rw [Nat.choose_eq_zero_of_lt hki, Nat.cast_zero, zero_mul, zero_mul]
  -- Step 4: split off the unit diagonal `k = i`.
  rcases Nat.lt_or_ge g.natDegree i with hi | hi
  · rw [hsupp, hrange, ← hIcc, Finset.Icc_eq_empty (by omega),
      Finset.Ioc_eq_empty (by omega), Finset.sum_empty,
      Polynomial.coeff_eq_zero_of_natDegree_lt hi, add_zero]
  · rw [hsupp, hrange, ← hIcc, Finset.Icc_eq_cons_Ioc hi, Finset.sum_cons,
      Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]

/-!
## Unit II-M4 — `rescale_coeff` (L2 algebraic half)

BP_II §1.9 displays this unit as `theorem rescale_coeff ...` — the signature is
elided in the blueprint; the mathematical content is pinned by the displayed docstring
(kept verbatim below) and by the source of mathematical truth, brief Lemma L2
(`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` line 380): for monic g with
h(y) := g(πy)/π^e, e = deg g, "h(y) = y^e + Σ b_i y^{e−i} with b_i = a_i/π^i" —
CODEGREE indexing (a_i, b_i are the x^{e−i}, y^{e−i} coefficients). Formalization
(same sanctioned-adjustment convention as above): h is transcribed literally as
`C (π^e)⁻¹ * g.comp (C π * X)` — g(πx) divided by π^e — and the claim is its
(e − i)-th coefficient law for i ≤ e. The companion `rescale_eq_scaleRoots` closes
the docstring's `Polynomial.scaleRoots` vocabulary: the rescaled polynomial IS
`g.scaleRoots π⁻¹` (bottom-index form of the same law, all coefficients at once).
The MEASURE half of L2 (independent Haar-uniformity of the b_i) is (HAAR-COORD)
territory consumed via `SemanticRows`, NOT this unit; the splitting-type half is
the (TYPE-INV) row `typeRescale`.
-/

/-- L2 algebraic half: the coefficients of h(y) = g(πy)/π^e are b_i = a_i/π^i
(`Polynomial.scaleRoots` vocabulary). [Unit II-M4; brief Lemma L2, codegree
indexing: h.coeff (e − i) = g.coeff (e − i) / π^i for i ≤ e = g.natDegree.] -/
theorem rescale_coeff {K : Type*} [Field K] (π : K) (hπ : π ≠ 0)
    (g : Polynomial K) {i : ℕ} (hi : i ≤ g.natDegree) :
    (Polynomial.C ((π ^ g.natDegree)⁻¹) *
        g.comp (Polynomial.C π * Polynomial.X)).coeff (g.natDegree - i) =
      g.coeff (g.natDegree - i) / π ^ i := by
  rw [Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  ring

/-- The `Polynomial.scaleRoots` identification for II-M4: the rescaled polynomial
h(y) = g(πy)/π^e is exactly `g.scaleRoots π⁻¹` — the L2 root correspondence
r ↦ r/π at the coefficient level, equivalently `rescale_coeff` in bottom-index
form h.coeff j = g.coeff j · π^{−(e−j)} for ALL j simultaneously. -/
theorem rescale_eq_scaleRoots {K : Type*} [Field K] (π : K) (hπ : π ≠ 0)
    (g : Polynomial K) :
    Polynomial.C ((π ^ g.natDegree)⁻¹) * g.comp (Polynomial.C π * Polynomial.X) =
      g.scaleRoots π⁻¹ := by
  ext j
  rw [Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_scaleRoots]
  rcases le_or_gt j g.natDegree with hj | hj
  · rw [inv_pow]
    field_simp
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
    ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj]
    ring

/-!
## Unit II-M8 — `intHeight_cols` (L6c column classification)

BP_II §1.9 displays this unit as `theorem intHeight_cols ...` — the signature is
elided in the blueprint; the mathematical content is pinned by the displayed docstring
(kept verbatim below) and the §2 unit-table sketch ("t·a_j/b_j ∈ ℤ ⟺ b_j ∣ t
(coprimality); ranges intersect in {x_{j+1}}"), realized over the II-P1/II-P2 data of
`Scaffold/O12/PolygonData.lean` (`FaceKind`, `SlopeTuple`, `heights`,
`vertexHeight_int`) per the math source of record
(`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` §3, L6c proof). Faces are
0-indexed (PolygonData convention: Lean face `j` is the blueprint's `j+1`), so face
`j`'s right endpoint is the vertex abscissa `x (j+1)` and the shared vertex column of
consecutive faces is `x (j+1)`. The column of face `j` at distance `t ≤ L_j` from its
right endpoint is the abscissa `x (j+1) − t`; its height is the (integer) vertex
height plus `t·a_j/b_j` (helper `heights_right_dist`), hence an integer iff
`b_j ∣ t` by `gcd(a_j, b_j) = 1`; and the column ranges `[x_j, x_{j+1}]`,
`[x_{j+1}, x_{j+2}]` of consecutive faces intersect in exactly `{x_{j+1}}`.
-/

variable {e : ℕ}

/-- Helper for II-M8: at distance `t ≤ L_j` left of face `j`'s right endpoint
`x_{j+1}`, the polygon height is the vertex height plus `t·a_j/b_j` — the faces
right of `j` contribute their full (t-independent) drops, face `j` contributes
the linear part `t·a_j/b_j`, the faces left of `j` contribute nothing. -/
theorem heights_right_dist (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) {t : ℕ} (ht : t ≤ ((κ.faces.get j).1 : ℕ)) :
    heights κ s (κ.x ((j : ℕ) + 1) - t) =
      ((s.a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) * (t : ℚ) +
        heights κ s (κ.x ((j : ℕ) + 1)) := by
  have hxj : κ.x ((j : ℕ) + 1) = κ.x (j : ℕ) + ((κ.faces.get j).1 : ℕ) := by
    simpa using κ.x_succ_of_lt j.isLt
  have hterm : ∀ j' : Fin κ.faces.length,
      ((s.a j' : ℕ) : ℚ) / (((κ.faces.get j').2 : ℕ) : ℚ) *
          ((max (κ.x ((j' : ℕ) + 1)) (κ.x ((j : ℕ) + 1) - t) -
              max (κ.x (j' : ℕ)) (κ.x ((j : ℕ) + 1) - t) : ℕ) : ℚ) =
        ((s.a j' : ℕ) : ℚ) / (((κ.faces.get j').2 : ℕ) : ℚ) *
            ((max (κ.x ((j' : ℕ) + 1)) (κ.x ((j : ℕ) + 1)) -
                max (κ.x (j' : ℕ)) (κ.x ((j : ℕ) + 1)) : ℕ) : ℚ) +
          (if j' = j then
            ((s.a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) * (t : ℚ)
          else 0) := by
    intro j'
    rcases lt_trichotomy ((j' : ℕ)) ((j : ℕ)) with h | h | h
    · -- face j' lies left of face j: both max-pairs collapse to the abscissa
      have h1 : κ.x ((j' : ℕ) + 1) ≤ κ.x (j : ℕ) := κ.x_mono (by omega)
      have h2 : κ.x (j' : ℕ) ≤ κ.x (j : ℕ) := κ.x_mono (by omega)
      have h3 : κ.x (j : ℕ) ≤ κ.x ((j : ℕ) + 1) - t := by omega
      have h4 : κ.x (j : ℕ) ≤ κ.x ((j : ℕ) + 1) := by omega
      rw [if_neg (Fin.ne_of_val_ne (by omega : (j' : ℕ) ≠ (j : ℕ))),
        max_eq_right (h1.trans h3), max_eq_right (h2.trans h3),
        max_eq_right (h1.trans h4), max_eq_right (h2.trans h4)]
      simp
    · -- face j' = j: the drop across the distance-t segment is exactly t·a_j/b_j
      have hj'j : j' = j := Fin.ext h
      subst hj'j
      have h3 : κ.x (j' : ℕ) ≤ κ.x ((j' : ℕ) + 1) - t := by omega
      rw [if_pos rfl, max_eq_left (Nat.sub_le _ _), max_eq_right h3, max_self,
        max_eq_right (by omega : κ.x (j' : ℕ) ≤ κ.x ((j' : ℕ) + 1)),
        (by omega : κ.x ((j' : ℕ) + 1) - (κ.x ((j' : ℕ) + 1) - t) = t)]
      simp
    · -- face j' lies right of face j: both max-pairs collapse to the vertices
      have h1 : κ.x ((j : ℕ) + 1) ≤ κ.x (j' : ℕ) := κ.x_mono (by omega)
      have h2 : κ.x ((j : ℕ) + 1) ≤ κ.x ((j' : ℕ) + 1) := κ.x_mono (by omega)
      rw [if_neg (Fin.ne_of_val_ne (by omega : (j' : ℕ) ≠ (j : ℕ))),
        max_eq_left ((Nat.sub_le _ _).trans h2),
        max_eq_left ((Nat.sub_le _ _).trans h1),
        max_eq_left h2, max_eq_left h1, add_zero]
  unfold heights
  rw [Finset.sum_congr rfl fun j' _ => hterm j', Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
  exact add_comm _ _

/-- **II-M8, L6c column classification**: integer-height columns of face j are those
at distance t ≡ 0 mod b_j from its right endpoint (t·a_j/b_j ∈ ℤ ⟺ b_j ∣ t by
coprimality); consecutive faces share EXACTLY the vertex column x_{j+1}. -/
theorem intHeight_cols (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) :
    (∀ t : ℕ, t ≤ ((κ.faces.get j).1 : ℕ) →
      ((∃ n : ℤ, heights κ s (κ.x ((j : ℕ) + 1) - t) = (n : ℚ)) ↔
        (((κ.faces.get j).2 : ℕ) ∣ t))) ∧
    Finset.Icc (κ.x (j : ℕ)) (κ.x ((j : ℕ) + 1)) ∩
        Finset.Icc (κ.x ((j : ℕ) + 1)) (κ.x ((j : ℕ) + 2)) =
      {κ.x ((j : ℕ) + 1)} := by
  constructor
  · -- the classification: h_{x_{j+1} − t} ∈ ℤ ⟺ b_j ∣ t
    intro t ht
    obtain ⟨N, hN⟩ : ∃ N : ℕ, heights κ s (κ.x ((j : ℕ) + 1)) = (N : ℚ) :=
      ⟨_, vertexHeight_int κ s ((j : ℕ) + 1)⟩
    have hb0 : (((κ.faces.get j).2 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (κ.faces.get j).2.ne_zero
    rw [heights_right_dist κ s j ht, hN]
    constructor
    · -- integral height forces b_j ∣ a_j·t, then b_j ∣ t by coprimality
      rintro ⟨n, hn⟩
      have h1 : ((s.a j : ℕ) : ℚ) * (t : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) =
          (n : ℚ) - (N : ℚ) := by
        rw [← hn]; ring
      have h2 : ((s.a j : ℕ) : ℚ) * (t : ℚ) =
          ((n : ℚ) - (N : ℚ)) * (((κ.faces.get j).2 : ℕ) : ℚ) := by
        rw [← h1, div_mul_cancel₀ _ hb0]
      have hz : ((s.a j : ℕ) : ℤ) * (t : ℤ) =
          ((n : ℤ) - (N : ℤ)) * (((κ.faces.get j).2 : ℕ) : ℤ) := by
        exact_mod_cast h2
      have hdvd : ((κ.faces.get j).2 : ℕ) ∣ (s.a j : ℕ) * t := by
        have hdz : (((κ.faces.get j).2 : ℕ) : ℤ) ∣ ((s.a j : ℕ) : ℤ) * (t : ℤ) :=
          ⟨(n : ℤ) - (N : ℤ), by linear_combination hz⟩
        exact_mod_cast hdz
      exact (s.hcop j).symm.dvd_of_dvd_mul_left hdvd
    · -- conversely t = b_j·m gives the integer height a_j·m + N
      rintro ⟨m, rfl⟩
      refine ⟨((s.a j : ℕ) * m + N : ℕ), ?_⟩
      push_cast
      field_simp
  · -- consecutive faces share exactly the vertex column x_{j+1}
    have h1 : κ.x (j : ℕ) ≤ κ.x ((j : ℕ) + 1) := κ.x_mono (Nat.le_succ _)
    have h2 : κ.x ((j : ℕ) + 1) ≤ κ.x ((j : ℕ) + 2) := κ.x_mono (by omega)
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_singleton]
    omega

/-!
## Unit II-M1 — `val_esymm_ge` (L1 (⇒): valuation lower bound on esymm)

Mathematical content (brief L1, (⇒) direction): for roots r₁, …, r_n and an additive
valuation v, the i-th elementary symmetric function satisfies
v(eᵢ(r)) ≥ i · min_j v(r_j) — each of the i-fold products in the eᵢ expansion has
valuation ≥ i·min, and the ultrametric sum bound preserves the floor.

**Display adjustment (FLAGGED for E-phase statement-fence sign-off — three token
repairs, each forced by elaboration, none touching the mathematical content; this
exceeds the pure binder/instance class sanctioned by the BP_II §1 head, so the unit
is reported PARTIAL pending sign-off).** The §1.9 display fails to elaborate as
written, at three independent points:

1. `Valuation K (Multiplicative Γ₀)`: *"failed to synthesize
   LinearOrderedCommMonoidWithZero (Multiplicative Γ₀)"*. Mathlib places the
   value-monoid instance on `Multiplicative Γ₀ᵒᵈ`
   (`Mathlib.Algebra.Order.GroupWithZero.Canonical`), and its OWN rendering of an
   additive valuation is verbatim `AddValuation R Γ₀ := Valuation R (Multiplicative
   Γ₀ᵒᵈ)` (`Mathlib.RingTheory.Valuation.Basic`). Repair: insert the `ᵒᵈ`.
2. With the `ᵒᵈ` in place, `(v (r j)).toAdd : Γ₀ᵒᵈ` breaks `Finset.univ.inf`
   (*"failed to synthesize OrderTop Γ₀ᵒᵈ"* — Γ₀ has ⊤, not ⊥) and would flip the
   displayed `≤`. Repair: wrap in `OrderDual.ofDual`, landing both sides in Γ₀ with
   the displayed orientation — exactly Mathlib's `AddValuation.ofValuation_apply`
   normal form `OrderDual.ofDual (Multiplicative.toAdd (v r))`.
3. `(Finset.univ.map ⟨r, fun _ _ h => h⟩).esymm i`: the anonymous injectivity proof
   does not typecheck (*"Type mismatch: h has type r x✝¹ = r x✝ but is expected to
   have type x✝¹ = x✝"* — arbitrary r is not injective), and `Finset.esymm` does not
   exist (*"Invalid field esymm: The environment does not contain Finset.esymm"*).
   Repair: `(Finset.univ.val.map r).esymm i` — the `Multiset.esymm` of the roots
   WITH multiplicity, per the §2 unit-table sketch ("`Multiset.esymm` expansion")
   and the LHS of Mathlib's `Finset.esymm_map_val`; this also avoids smuggling an
   injectivity hypothesis on r into the statement.

The `{n : ℕ}` binder is made explicit (sanctioned implicit-binder adjustment; the
display relies on auto-implicit). The proof route: restate over Mathlib's
`AddValuation K Γ₀` (definitionally the repaired codomain) and prove two multiset
ultrametric helpers — sum floor and i-fold-product floor — then specialize.
-/

/-- Ultrametric floor for multiset sums: a lower bound g on the additive valuation
of every term is a lower bound on the valuation of the sum (empty sum: w 0 = ⊤).
[II-M1 helper; also feeds II-M2/II-M3.] -/
theorem le_addVal_multiset_sum {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {g : Γ₀} (T : Multiset K) (hT : ∀ x ∈ T, g ≤ w x) : g ≤ w T.sum := by
  induction T using Multiset.induction with
  | empty => simp
  | cons a T ih =>
    rw [Multiset.sum_cons]
    exact w.map_le_add (hT a (Multiset.mem_cons_self a T))
      (ih fun x hx => hT x (Multiset.mem_cons_of_mem hx))

/-- Valuation floor for multiset products: if every factor has additive valuation
≥ g then a product of k factors has valuation ≥ k • g (additivity of w on products).
[II-M1 helper; also feeds II-M2/II-M3.] -/
theorem nsmul_le_addVal_multiset_prod {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {g : Γ₀} (S : Multiset K) (hS : ∀ x ∈ S, g ≤ w x) :
    Multiset.card S • g ≤ w S.prod := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.prod_cons, w.map_mul, Multiset.card_cons, succ_nsmul']
    exact add_le_add (hS a (Multiset.mem_cons_self a S))
      (ih fun x hx => hS x (Multiset.mem_cons_of_mem hx))

/-- II-M1 in Mathlib's `AddValuation` language: w(eᵢ(r)) ≥ i • min_j w(r_j). Every
i-subset product in the `Multiset.esymm` expansion has valuation ≥ i • inf by the
product floor, and the sum floor transports the bound through the outer sum. -/
theorem addValuation_esymm_ge {n : ℕ} {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀]
    (w : AddValuation K Γ₀) (r : Fin n → K) (i : ℕ) :
    i • (Finset.univ.inf fun j => w (r j)) ≤
      w ((Finset.univ.val.map r).esymm i) := by
  simp only [Multiset.esymm]
  refine le_addVal_multiset_sum w _ fun x hx => ?_
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hSle, hScard⟩ := Multiset.mem_powersetCard.mp hS
  have hbound : ∀ y ∈ S, (Finset.univ.inf fun j => w (r j)) ≤ w y := by
    intro y hyS
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hSle hyS)
    exact Finset.inf_le (Finset.mem_univ j)
  have h := nsmul_le_addVal_multiset_prod w S hbound
  rwa [hScard] at h

/-- **II-M1, L1 (⇒)**: valuation lower bound on the elementary symmetric functions,
i • inf_j v(r_j) ≤ v(eᵢ(r)) in the additive value group Γ₀ — the blueprint §1.9
display under the three documented token repairs (`ᵒᵈ` codomain,
`OrderDual.ofDual` reads, `Multiset.esymm` via `Finset.univ.val.map`). The
`AddValuation.ofValuation` specialization of `addValuation_esymm_ge` is
definitional. -/
theorem val_esymm_ge {n : ℕ}
    {K Γ₀ : Type*} [Field K] [LinearOrderedAddCommGroupWithTop Γ₀]
    (v : Valuation K (Multiplicative Γ₀ᵒᵈ)) (r : Fin n → K) (i : ℕ) :
    i • (Finset.univ.inf fun j => OrderDual.ofDual (v (r j)).toAdd) ≤
      OrderDual.ofDual (v ((Finset.univ.val.map r).esymm i)).toAdd :=
  addValuation_esymm_ge (AddValuation.ofValuation v) r i

/-!
## Unit II-M2 — `val_esymm_min_eq` (L1 (⇐): unique strict-minimum term)

Mathematical content (brief L1, (⇐) direction): if μ is a common lower bound of the
root valuations, exactly k roots attain μ, and the attaining set is the UNIQUE
k-subset all of whose members attain μ, then v(e_k(r)) = k • μ: the term of the
`Multiset.esymm` expansion indexed by the attaining set has valuation exactly k • μ,
every other k-subset product is strictly larger, and the ultrametric collapses the
sum onto its unique strict minimum (the blueprint's `Valuation.map_add_eq_of_lt`
chain = one application of `AddValuation.map_add_eq_of_lt_left` against the minimal
term of the remaining sum).

**Display adjustment**: the SAME three token repairs as II-M1 above (`ᵒᵈ` codomain,
`OrderDual.ofDual` reads, `Multiset.esymm` via `Finset.univ.val.map`) — the §1.9
display fails to elaborate at the identical three points — plus the explicit
`{n : ℕ}` binder; flagged for the same E-phase statement-fence sign-off as II-M1.

HARD-milestone split (BP_II §2 preamble; the §1 helper displays were not
materialized by the division lead, so the split is realized as the named in-file
helper declarations below, same convention as II-M1's helpers):
`nsmul_ne_top_of_ne_top` (Γ₀ arithmetic), `addVal_multiset_prod_eq_nsmul` /
`addVal_finset_prod_eq_nsmul` (the attaining term evaluates exactly),
`nsmul_lt_addVal_finset_prod` (every other k-subset term strictly exceeds),
`addVal_finset_sum_eq_of_lt` (the ultrametric strict-minimum collapse), assembled
in `addValuation_esymm_min_eq` and specialized to the displayed statement. The
μ = ⊤ corner (all roots have valuation ⊤, the k-subset family degenerates to the
single attaining set) is handled separately since strict domination is vacuous
there.
-/

/-- A finite ℕ-multiple of a non-⊤ element of a `LinearOrderedAddCommGroupWithTop`
stays non-⊤. [II-M2 helper.] -/
theorem nsmul_ne_top_of_ne_top {Γ₀ : Type*} [LinearOrderedAddCommGroupWithTop Γ₀]
    {μ : Γ₀} (hμ : μ ≠ ⊤) (m : ℕ) : m • μ ≠ ⊤ := by
  induction m with
  | zero => rw [zero_nsmul]; exact LinearOrderedAddCommGroupWithTop.zero_ne_top
  | succ m ih =>
    rw [succ_nsmul]; exact LinearOrderedAddCommGroupWithTop.add_ne_top.mpr ⟨ih, hμ⟩

/-- Exact valuation of a product all of whose factors have valuation exactly μ:
w(∏ T) = (card T) • μ (additivity of w on products). [II-M2 helper.] -/
theorem addVal_multiset_prod_eq_nsmul {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {μ : Γ₀} (T : Multiset K) (hT : ∀ x ∈ T, w x = μ) :
    w T.prod = Multiset.card T • μ := by
  induction T using Multiset.induction with
  | empty => rw [Multiset.prod_zero, Multiset.card_zero, zero_nsmul]; exact w.map_one
  | cons a T ih =>
    rw [Multiset.prod_cons, w.map_mul, Multiset.card_cons, succ_nsmul',
      hT a (Multiset.mem_cons_self a T), ih fun x hx => hT x (Multiset.mem_cons_of_mem hx)]

/-- `addVal_multiset_prod_eq_nsmul` in `Finset.prod` form: if every factor over `S`
has valuation exactly μ then w(∏_{j ∈ S} f j) = S.card • μ. [II-M2 helper.] -/
theorem addVal_finset_prod_eq_nsmul {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {ι : Type*} (f : ι → K) {μ : Γ₀} (S : Finset ι)
    (hS : ∀ j ∈ S, w (f j) = μ) : w (∏ j ∈ S, f j) = S.card • μ := by
  have h := addVal_multiset_prod_eq_nsmul w (S.val.map f) fun x hx => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact hS i (Finset.mem_def.mpr hi)
  rwa [Multiset.card_map] at h

/-- Strict valuation floor for a product: if every factor over `S` has valuation
≥ μ and SOME factor strictly exceeds μ (with μ ≠ ⊤), then the product valuation
strictly exceeds S.card • μ — split off the strict factor, floor the rest by
`nsmul_le_addVal_multiset_prod`, and add strictly on the non-⊤ side. [II-M2
helper.] -/
theorem nsmul_lt_addVal_finset_prod {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {ι : Type*} (f : ι → K) {μ : Γ₀} (hμ : μ ≠ ⊤)
    {S : Finset ι} (hS : ∀ j ∈ S, μ ≤ w (f j)) {j₀ : ι} (hj₀ : j₀ ∈ S)
    (hstrict : μ < w (f j₀)) : S.card • μ < w (∏ j ∈ S, f j) := by
  classical
  rw [← Finset.mul_prod_erase S f hj₀, w.map_mul, ← Finset.card_erase_add_one hj₀,
    succ_nsmul']
  calc μ + (S.erase j₀).card • μ
      < w (f j₀) + (S.erase j₀).card • μ :=
        (add_lt_add_iff_left_of_ne_top (nsmul_ne_top_of_ne_top hμ _)).mpr hstrict
    _ ≤ w (f j₀) + w (∏ j ∈ S.erase j₀, f j) := by
        refine add_le_add le_rfl ?_
        have h := nsmul_le_addVal_multiset_prod w ((S.erase j₀).val.map f)
          fun x hx => by
            obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
            exact hS i (Finset.mem_of_mem_erase (Finset.mem_def.mpr hi))
        rwa [Multiset.card_map] at h

/-- The ultrametric strict-minimum collapse (the blueprint's
`Valuation.map_add_eq_of_lt` chain): if the term at i₀ has strictly smaller
valuation than every other term of a finite sum, the sum has the valuation of
that term — the rest of the sum is floored by its own minimal term, which is
still strictly above w(f i₀), so `AddValuation.map_add_eq_of_lt_left` applies.
[II-M2 helper.] -/
theorem addVal_finset_sum_eq_of_lt {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀)
    {ι : Type*} (f : ι → K) {F : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ F)
    (hlt : ∀ i ∈ F, i ≠ i₀ → w (f i₀) < w (f i)) :
    w (∑ i ∈ F, f i) = w (f i₀) := by
  classical
  rw [← Finset.add_sum_erase F f hi₀]
  rcases (F.erase i₀).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, add_zero]
  · obtain ⟨i₁, hi₁, hmin₁⟩ := (F.erase i₀).exists_min_image (fun i => w (f i)) hne
    refine w.map_add_eq_of_lt_left ?_
    refine lt_of_lt_of_le
      (hlt i₁ (Finset.mem_of_mem_erase hi₁) (Finset.ne_of_mem_erase hi₁)) ?_
    exact le_addVal_multiset_sum w ((F.erase i₀).val.map f) fun x hx => by
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
      exact hmin₁ i (Finset.mem_def.mpr hi)

/-- II-M2 in Mathlib's `AddValuation` language: if μ bounds all root valuations
from below, k counts the roots attaining μ, and the attaining set is the unique
k-subset with all values μ, then w(e_k(r)) = k • μ. The attaining-set term of the
`Multiset.esymm` expansion evaluates to exactly k • μ, every other k-subset term
strictly exceeds it (it contains a strict factor), and the ultrametric collapse
lands the sum on the minimum. μ = ⊤ degenerates to a one-term sum. -/
theorem addValuation_esymm_min_eq {n : ℕ} {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀]
    (w : AddValuation K Γ₀) (r : Fin n → K) (μ : Γ₀) (k : ℕ)
    (hk : k = (Finset.univ.filter fun j => w (r j) = μ).card)
    (hmin : ∀ j, μ ≤ w (r j))
    (hunique : ∀ I : Finset (Fin n), I.card = k →
      (∀ j ∈ I, w (r j) = μ) →
      I = Finset.univ.filter fun j => w (r j) = μ) :
    w ((Finset.univ.val.map r).esymm k) = k • μ := by
  classical
  rw [Finset.esymm_map_val]
  by_cases hμ : μ = ⊤
  · -- corner μ = ⊤: every root valuation is ⊤, the attaining set is univ, k = n,
    -- and the k-subset family is the single set univ — a one-term sum.
    subst hμ
    have hall : ∀ j, w (r j) = ⊤ := fun j => le_antisymm le_top (hmin j)
    have hkn : k = (Finset.univ : Finset (Fin n)).card := by
      rw [hk, Finset.filter_true_of_mem fun j _ => hall j]
    rw [hkn, Finset.powersetCard_self, Finset.sum_singleton]
    exact addVal_finset_prod_eq_nsmul w r Finset.univ fun j _ => hall j
  · -- main case: the attaining set is the unique strict-minimum term.
    have hS₀card : (Finset.univ.filter fun j => w (r j) = μ).card = k := hk.symm
    have hS₀mem : (Finset.univ.filter fun j => w (r j) = μ)
        ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard_univ.mpr hS₀card
    have hPS₀ : w ((Finset.univ.filter fun j => w (r j) = μ).prod r) = k • μ := by
      rw [addVal_finset_prod_eq_nsmul w r _ fun j hj => (Finset.mem_filter.mp hj).2,
        hS₀card]
    have hstrict : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        T ≠ (Finset.univ.filter fun j => w (r j) = μ) →
        w ((Finset.univ.filter fun j => w (r j) = μ).prod r) < w (T.prod r) := by
      intro T hT hTne
      have hTcard : T.card = k := Finset.mem_powersetCard_univ.mp hT
      have hex : ¬ ∀ j ∈ T, w (r j) = μ := fun hall => hTne (hunique T hTcard hall)
      push Not at hex
      obtain ⟨j₀, hj₀T, hj₀⟩ := hex
      rw [hPS₀, ← hTcard]
      exact nsmul_lt_addVal_finset_prod w r hμ (fun j _ => hmin j) hj₀T
        ((hmin j₀).lt_of_ne (Ne.symm hj₀))
    exact (addVal_finset_sum_eq_of_lt w _ hS₀mem hstrict).trans hPS₀

/-- **II-M2, L1 (⇐)**: the unique strict-minimum term gives v(e_k(r)) = k • μ in
the additive value group Γ₀ — the blueprint §1.9 display under the same three
documented token repairs as II-M1 (`ᵒᵈ` codomain, `OrderDual.ofDual` reads,
`Multiset.esymm` via `Finset.univ.val.map`). The `AddValuation.ofValuation`
specialization of `addValuation_esymm_min_eq` is definitional. -/
theorem val_esymm_min_eq {n : ℕ}
    {K Γ₀ : Type*} [Field K] [LinearOrderedAddCommGroupWithTop Γ₀]
    (v : Valuation K (Multiplicative Γ₀ᵒᵈ)) (r : Fin n → K) (μ : Γ₀)
    (k : ℕ)
    (hk : k = (Finset.univ.filter fun j =>
      OrderDual.ofDual (v (r j)).toAdd = μ).card)
    (hmin : ∀ j, μ ≤ OrderDual.ofDual (v (r j)).toAdd)
    (hunique : ∀ I : Finset (Fin n), I.card = k →
      (∀ j ∈ I, OrderDual.ofDual (v (r j)).toAdd = μ) →
      I = Finset.univ.filter fun j => OrderDual.ofDual (v (r j)).toAdd = μ) :
    OrderDual.ofDual (v ((Finset.univ.val.map r).esymm k)).toAdd = k • μ :=
  addValuation_esymm_min_eq (AddValuation.ofValuation v) r μ k hk hmin hunique

/-!
## Unit II-M3 — `L1_root_coeff` (L1 (i)+(ii) + ℤ-snap; assembles II-M1/II-M2)

Mathematical content (brief L1, `O12_phaseB_verifybrief_rev4.md` line 358: monic
g = x^e + a₁x^{e−1} + ⋯ + a_e, top-down aᵢ): (i) all roots have additive valuation
> 0 ⟺ v(aᵢ) ≥ 1 for i = 1..e; (ii) all roots have valuation ≥ 1 ⟺ v(aᵢ) ≥ i. The
ℤ-snap is the §2 unit-table sketch "v(a) ∈ ℤ_{≥0} forces > 0 ⟹ ≥ 1": the value
group is DISCRETE (additively `WithTop ℤ`), so a strict bound snaps to the next
integer. Assembly: forward directions by II-M1 (`addValuation_esymm_ge`, every
eᵢ-term is an i-fold product of roots); backward directions by II-M2
(`addValuation_esymm_min_eq` at the minimal root valuation μ ≤ 0 — the attaining
set is AUTOMATICALLY the unique k-subset attaining μ, since any such subset sits
inside the attaining set with equal cardinality), giving a coefficient of
valuation k • μ ≤ 0 that violates the right-hand side at index k.

**Display adjustment (three documented token repairs; same convention and E-phase
statement-fence sign-off flag as II-M1/II-M2/II-M5 above; BP_II §1 head:
"Signatures are sketches"). The §1.9 display does NOT elaborate verbatim:**

1. **`ℤₘ₀` codomain.** This Mathlib pin has no `ℤₘ₀` notation (it appears only in
   comments referencing `Multiplicative.termℤₘ₀`, declared in later Mathlib as
   `WithZero (Multiplicative ℤ)`); verbatim, `ℤₘ₀` auto-binds as an implicit type
   and elaboration fails with *"failed to synthesize LinearOrderedCommMonoidWithZero
   ℤₘ₀"*. Supplying the standard notation does not cure the display: the reads
   `(v _).toAdd` then fail with *"Invalid field toAdd: The environment does not
   contain Option.toAdd"* — no total additive read exists on `WithZero
   (Multiplicative ℤ)` in any Mathlib. Repair: the II-M1/II-M2 additive-codomain
   dictionary at Γ₀ := `WithTop ℤ`, i.e. `v : Valuation K (Multiplicative
   (WithTop ℤ)ᵒᵈ)` (= `AddValuation K (WithTop ℤ)` definitionally). This codomain
   is order-anti-isomorphic to `ℤₘ₀` via 0 ↦ ⊤, ofAdd m ↦ −m — exactly the `ᵒᵈ`
   repair; the display's `.toAdd`-with-`0 ≤`-integrality semantics pin the
   ADDITIVE order, which is what the repaired reads deliver.
2. **Reads.** `(v _).toAdd` → `OrderDual.ofDual (v _).toAdd`, the identical repair
   as II-M1/II-M2 (the specialization through `AddValuation.ofValuation` is
   definitional: `AddValuation.ofValuation_apply` is `rfl`).
3. **Coefficient index.** The display's `g.coeff i` in the two `Finset.Icc
   1 g.natDegree`-guarded clauses → `g.coeff (g.natDegree - i)`: the blueprint's
   aᵢ is the monic TOP-DOWN index (aᵢ = coeff of x^(e−i), brief L1 line 358),
   while Lean's `coeff` is bottom-up — the II-M5 dictionary documented above.
   The literal bottom-up reading is REFUTED, not merely unidiomatic: at i =
   g.natDegree ≥ 1 it demands 1 ≤ w(leading coeff) = w(1) = 0 (and (ii) demands
   g.natDegree ≤ 0), so both clauses' forward directions are false for every
   monic g of positive degree with all root valuations positive.

`hintegral` is carried verbatim from the display; the proof does not consume it
(the equivalences hold without coefficient integrality, which is automatic here:
every coefficient is ± a sum of products of roots of nonnegative valuation on the
left-hand sides, and explicitly bounded on the right-hand sides).
-/

/-- ℤ-snap (a): a positive element of the discrete value group `WithTop ℤ` is ≥ 1
(the blueprint's "v(a) ∈ ℤ_{≥0} forces > 0 ⟹ ≥ 1"). [II-M3 helper.] -/
theorem intTop_one_le_of_pos {μ : WithTop ℤ} (h : 0 < μ) : 1 ≤ μ := by
  induction μ using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    have ha : (0 : ℤ) < a := by exact_mod_cast h
    exact_mod_cast (by omega : (1 : ℤ) ≤ a)

/-- ℤ-snap (b): an element of `WithTop ℤ` not ≥ 1 is ≤ 0. [II-M3 helper.] -/
theorem intTop_le_zero_of_not_one_le {μ : WithTop ℤ} (h : ¬ 1 ≤ μ) : μ ≤ 0 := by
  induction μ using WithTop.recTopCoe with
  | top => exact absurd le_top h
  | coe a =>
    have ha : ¬ (1 : ℤ) ≤ a := fun hle => h (by exact_mod_cast hle)
    exact_mod_cast (by omega : a ≤ (0 : ℤ))

/-- k • 1 = k in `WithTop ℤ`. [II-M3 helper.] -/
theorem intTop_nsmul_one (k : ℕ) : k • (1 : WithTop ℤ) = ((k : ℤ) : WithTop ℤ) := by
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul]
  norm_num

/-- The unit sign of Vieta is valuation-invisible: w((−1)^i) = 0. [II-M3 helper.] -/
theorem addVal_neg_one_pow {K Γ₀ : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ₀] (w : AddValuation K Γ₀) (i : ℕ) :
    w ((-1 : K) ^ i) = 0 := by
  rw [w.map_pow, w.map_neg, w.map_one, nsmul_zero]

set_option linter.unusedVariables false in  -- `hintegral` is display-carried (§II-M3 note)
/-- II-M3 in Mathlib's `AddValuation` language, discrete value group `WithTop ℤ`:
for monic g = ∏(X − C rⱼ), (i) all roots have valuation > 0 ⟺ the top-down
coefficients a₁..aₙ (= `g.coeff (n − i)`, i = 1..n) have valuation ≥ 1; (ii) all
roots have valuation ≥ 1 ⟺ aᵢ has valuation ≥ i. Vieta ties a_i to ±eᵢ(roots);
II-M1 floors the forward directions, II-M2 collapses the backward ones onto the
minimal-valuation term, and the ℤ-snap converts strict to next-integer bounds. -/
theorem addValuation_L1_root_coeff {K : Type*} [Field K]
    (w : AddValuation K (WithTop ℤ))
    (g : Polynomial K) (roots : Fin g.natDegree → K)
    (hroots : g = ∏ j, (Polynomial.X - Polynomial.C (roots j)))
    (hintegral : ∀ i, 0 ≤ w (g.coeff i)) :
    ((∀ j, 0 < w (roots j)) ↔
      ∀ i ∈ Finset.Icc 1 g.natDegree, 1 ≤ w (g.coeff (g.natDegree - i))) ∧
    ((∀ j, 1 ≤ w (roots j)) ↔
      ∀ i ∈ Finset.Icc 1 g.natDegree,
        (i : ℤ) ≤ w (g.coeff (g.natDegree - i))) := by
  classical
  -- the root multiset has cardinality n = g.natDegree
  have hcard : Multiset.card (Finset.univ.val.map roots) = g.natDegree := by
    rw [Multiset.card_map]
    exact Finset.card_univ.trans (Fintype.card_fin _)
  -- g as the product over the root multiset
  have hg : g = ((Finset.univ.val.map roots).map
      fun x => Polynomial.X - Polynomial.C x).prod := by
    rw [Multiset.map_map]
    exact hroots.trans (Finset.prod_eq_multiset_prod _ _)
  -- Vieta bridge: w(g.coeff (n − i)) = w(eᵢ(roots)) for i ∈ [1, n]
  have hbridge : ∀ i ∈ Finset.Icc 1 g.natDegree,
      w (g.coeff (g.natDegree - i)) = w ((Finset.univ.val.map roots).esymm i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hin : g.natDegree - i ≤ Multiset.card (Finset.univ.val.map roots) := by
      rw [hcard]; omega
    have hcoeff := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map roots) hin
    rw [← hg] at hcoeff
    have hidx : Multiset.card (Finset.univ.val.map roots) - (g.natDegree - i) = i := by
      rw [hcard]; omega
    rw [hidx] at hcoeff
    rw [hcoeff, w.map_mul, addVal_neg_one_pow, zero_add]
  -- II-M1 assembly: a common floor c on root valuations floors w(eᵢ) by i • c
  have hup : ∀ c : WithTop ℤ, (∀ j, c ≤ w (roots j)) → ∀ i : ℕ,
      i • c ≤ w ((Finset.univ.val.map roots).esymm i) := by
    intro c hc i
    exact le_trans (nsmul_le_nsmul_right (Finset.le_inf fun j _ => hc j) i)
      (addValuation_esymm_ge w roots i)
  -- II-M2 assembly: a root of valuation ≤ 0 yields k ∈ [1, n] with w(e_k) ≤ 0
  have hdown : ∀ j₀ : Fin g.natDegree, w (roots j₀) ≤ 0 →
      ∃ k ∈ Finset.Icc 1 g.natDegree,
        w ((Finset.univ.val.map roots).esymm k) ≤ 0 := by
    intro j₀ h₀
    obtain ⟨j₁, -, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun j => w (roots j)) ⟨j₀, Finset.mem_univ j₀⟩
    refine ⟨(Finset.univ.filter fun j => w (roots j) = w (roots j₁)).card, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨Finset.card_pos.mpr
        ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩, ?_⟩
      exact le_trans (Finset.card_filter_le _ _)
        (le_of_eq (Finset.card_univ.trans (Fintype.card_fin _)))
    · have hval := addValuation_esymm_min_eq w roots (w (roots j₁)) _ rfl
        (fun j => hmin j (Finset.mem_univ j))
        (fun I hIcard hIval => Finset.eq_of_subset_of_card_le
          (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ j, hIval j hj⟩)
          (le_of_eq hIcard.symm))
      rw [hval]
      calc (Finset.univ.filter fun j => w (roots j) = w (roots j₁)).card
              • w (roots j₁)
          ≤ (Finset.univ.filter fun j => w (roots j) = w (roots j₁)).card
              • (0 : WithTop ℤ) :=
            nsmul_le_nsmul_right (le_trans (hmin j₀ (Finset.mem_univ j₀)) h₀) _
        _ = 0 := nsmul_zero _
  constructor
  · -- (i): all roots > 0 ⟺ all a_i ≥ 1
    constructor
    · intro hpos i hi
      rw [hbridge i hi]
      have hle := hup 1 (fun j => intTop_one_le_of_pos (hpos j)) i
      rw [intTop_nsmul_one] at hle
      refine le_trans ?_ hle
      rw [Finset.mem_Icc] at hi
      exact_mod_cast (by omega : (1 : ℤ) ≤ (i : ℤ))
    · intro hcoeffs j
      by_contra hj
      obtain ⟨k, hk, hek⟩ := hdown j (not_lt.mp hj)
      have h1 := hcoeffs k hk
      rw [hbridge k hk] at h1
      have h10 : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by
        rw [WithTop.coe_one, WithTop.coe_zero]; exact le_trans h1 hek
      rw [WithTop.coe_le_coe] at h10
      omega
  · -- (ii): all roots ≥ 1 ⟺ all a_i ≥ i
    constructor
    · intro hge i hi
      rw [hbridge i hi]
      have hle := hup 1 hge i
      rwa [intTop_nsmul_one] at hle
    · intro hcoeffs j
      by_contra hj
      obtain ⟨k, hk, hek⟩ := hdown j (intTop_le_zero_of_not_one_le hj)
      have h1 := hcoeffs k hk
      rw [hbridge k hk] at h1
      have hk0 : ((k : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by
        rw [WithTop.coe_zero]; exact le_trans h1 hek
      rw [WithTop.coe_le_coe] at hk0
      rw [Finset.mem_Icc] at hk
      omega

/-- **II-M3, L1 (i)+(ii) + ℤ-snap**: root-valuation dichotomies ⟺ coefficient-
valuation bounds for a split monic polynomial over a discretely valued field —
the blueprint §1.9 display under the three documented token repairs of the
section header (`ℤₘ₀` → the additive codomain at Γ₀ := `WithTop ℤ`;
`OrderDual.ofDual` reads; top-down coefficient index `g.coeff (g.natDegree - i)`).
The `AddValuation.ofValuation` specialization of `addValuation_L1_root_coeff` is
definitional. -/
theorem L1_root_coeff
    {K : Type*} [Field K] (v : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ))
    (g : Polynomial K) (roots : Fin g.natDegree → K)
    (hroots : g = ∏ j, (Polynomial.X - Polynomial.C (roots j)))
    (hintegral : ∀ i, 0 ≤ OrderDual.ofDual (v (g.coeff i)).toAdd) :
    ((∀ j, 0 < OrderDual.ofDual (v (roots j)).toAdd) ↔
      ∀ i ∈ Finset.Icc 1 g.natDegree,
        1 ≤ OrderDual.ofDual (v (g.coeff (g.natDegree - i))).toAdd) ∧
    ((∀ j, 1 ≤ OrderDual.ofDual (v (roots j)).toAdd) ↔
      ∀ i ∈ Finset.Icc 1 g.natDegree,
        (i : ℤ) ≤ OrderDual.ofDual (v (g.coeff (g.natDegree - i))).toAdd) :=
  addValuation_L1_root_coeff (AddValuation.ofValuation v) g roots hroots hintegral

/-!
## Unit II-M7 — `cell_volume` (L6a volume; WRAPPER on landed `L4.cellVolume_eq`)

BP_II §1.9 displays this unit as `theorem cell_volume ...` — the signature is
elided in the blueprint; the mathematical content is pinned by the displayed
docstring (kept verbatim on `cell_volume` below) and the §2 unit-table sketch
("WRAPPER on landed `L4.cellVolume_eq`: FaceKind→LatticePolygon transport,
N(P) = `newtonExponent`, k = `newtonVertexCount`"), same convention as units
II-M4/II-M5/II-M8 above.

Realization: `FaceKind.toLatticePolygon` sends the II-P1/II-P2 data (κ, s) to
the landed BB1 lattice data (`LeanUrat.L4.LatticePolygon`) — width `e`, ceiling
heights `⌈h_i⌉` (naturals via `Int.toNat`, faithful by `one_le_ceil_height`),
vertex predicate marking the abscissa columns `x_j`, `j < k`. The two displayed
dictionary entries are certified as `toLatticePolygon_newtonExponent`
(N(P) = `newtonExponent`: same per-column ceiling sum) and
`toLatticePolygon_newtonVertexCount` (k = `newtonVertexCount`: the abscissas
`x_0 < x_1 < ⋯ < x_{k−1} < e` are exactly the vertex columns, counted by the
bijection `j ↦ x_j`). `cell_volume` then fires the landed `L4.cellVolume_eq`
through the transport, INHERITING its recorded-via-hypothesis convention: the
(HAAR-COORD) measure input enters as the same `hfactor` row (the per-column
box/shell factorization of the cell volume), and the closed value transports to
`(1 − Q⁻¹)^k · Q^{−N(P)}` (zpow: `Npg : ℤ`). The unit-table dep II-M6
(`hull_eq_iff_cell`, the L6a cell-identification companion of the same display)
identifies WHICH set the cell is; the volume transport does not consume it.
-/

/-- Vertex abscissas are strictly increasing while in range: `x_j < x_{j'}` for
`j < j' ≤ k` (each face has width `L_j ≥ 1`). [II-M7 helper.] -/
theorem FaceKind.x_lt_of_lt (κ : FaceKind e) {j j' : ℕ} (hjj' : j < j')
    (hj' : j' ≤ κ.faces.length) : κ.x j < κ.x j' := by
  have hjk : j < κ.faces.length := by omega
  have h1 : κ.x (j + 1) = κ.x j + (κ.faces[j].1 : ℕ) := κ.x_succ_of_lt hjk
  have hL : 1 ≤ (κ.faces[j].1 : ℕ) := κ.faces[j].1.pos
  have h2 : κ.x (j + 1) ≤ κ.x j' := κ.x_mono (by omega)
  omega

/-- In-range vertex abscissas lie strictly left of the width: `x_j < e` for
`j < k` (the rightmost vertex `x_k = e` is the excluded column). [II-M7
helper.] -/
theorem FaceKind.x_lt_width (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.x j < e := by
  have h := κ.x_lt_of_lt hj le_rfl
  rwa [κ.x_length] at h

/-- The FaceKind → LatticePolygon transport (unit II-M7): the BB1 lattice data
of the polygon of (κ, s) — width `e`, per-column integer ceiling heights
`⌈h_i⌉` (faithfully in ℕ: every `⌈h_i⌉ ≥ 1` by `one_le_ceil_height`), and the
vertex predicate marking the abscissa columns `x_j`, `j < k`, among
`{0,…,e−1}`. -/
noncomputable def FaceKind.toLatticePolygon (κ : FaceKind e) (s : SlopeTuple κ) :
    L4.LatticePolygon where
  width := e
  ceilHeights := fun i => ⌈heights κ s (i : ℕ)⌉.toNat
  isVertex := fun i => decide (∃ j, j < κ.faces.length ∧ κ.x j = (i : ℕ))

/-- Dictionary entry N(P) = `newtonExponent` (unit II-M7): the landed BB1
lattice exponent of the transported polygon is `Npg κ s` — both are the sum of
the per-column ceilings `⌈h_i⌉` over `i < e`, and the `Int.toNat` passage is
faithful since every ceiling is ≥ 1 (`one_le_ceil_height`). -/
theorem toLatticePolygon_newtonExponent (κ : FaceKind e) (s : SlopeTuple κ) :
    ((L4.newtonExponent (κ.toLatticePolygon s) : ℕ) : ℤ) = Npg κ s := by
  unfold L4.newtonExponent FaceKind.toLatticePolygon Npg
  rw [Nat.cast_sum, Finset.sum_range fun i => ⌈heights κ s i⌉]
  exact Finset.sum_congr rfl fun i _ =>
    Int.toNat_of_nonneg (le_trans zero_le_one (one_le_ceil_height κ s i.isLt))

/-- Dictionary entry k = `newtonVertexCount` (unit II-M7): the landed BB1
vertex count of the transported polygon is the face count `k`: the marked
columns are exactly the abscissas `x_0 < x_1 < ⋯ < x_{k−1} < e`
(`FaceKind.x_lt_of_lt`, `FaceKind.x_lt_width`), counted by the bijection
`j ↦ x_j`. -/
theorem toLatticePolygon_newtonVertexCount (κ : FaceKind e) (s : SlopeTuple κ) :
    L4.newtonVertexCount (κ.toLatticePolygon s) = κ.faces.length := by
  classical
  unfold L4.newtonVertexCount FaceKind.toLatticePolygon
  refine ((Finset.card_bij
    (fun j hj => (⟨κ.x j, κ.x_lt_width (Finset.mem_range.mp hj)⟩ : Fin e))
    ?_ ?_ ?_).symm.trans (Finset.card_range κ.faces.length))
  · -- maps into the marked columns: `x_j` is a vertex column (witness `j`)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  · -- injective: the abscissas are strictly increasing in range
    intro j hj j' hj' heq
    have hx : κ.x j = κ.x j' := congrArg Fin.val heq
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd hx (Nat.ne_of_lt
        (κ.x_lt_of_lt h (Nat.le_of_lt (Finset.mem_range.mp hj'))))
    · exact h
    · exact absurd hx.symm (Nat.ne_of_lt
        (κ.x_lt_of_lt h (Nat.le_of_lt (Finset.mem_range.mp hj))))
  · -- surjective: every marked column IS an `x_j`, `j < k`
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq] at hi
    obtain ⟨j, hjk, hxj⟩ := hi
    exact ⟨j, Finset.mem_range.mpr hjk, Fin.ext hxj⟩

/-- **L6a, volume** — REUSE: `LeanUrat.L4.cellVolume_eq` gives
(1 − q₀⁻¹)^k · q₀^{−N(P)} from (HAAR-COORD); this unit is the FaceKind → LatticePolygon
transport (N(P) = `newtonExponent`, k = `newtonVertexCount`). [Unit II-M7. The
`hfactor` hypothesis is the landed L4 recorded-via-hypothesis row carrying the
(HAAR-COORD) per-column box/shell factorization — the module-head convention;
`Q` is the residue size and the exponent `Npg κ s : ℤ` enters as a zpow.] -/
theorem cell_volume (cellVol : L4.LatticePolygon → ℕ → ℚ)
    (κ : FaceKind e) (s : SlopeTuple κ) (Q : ℕ) (hQ : 1 ≤ Q)
    (hfactor : cellVol (κ.toLatticePolygon s) Q =
      ∏ i : Fin (κ.toLatticePolygon s).width,
        L4.columnMeasure (κ.toLatticePolygon s) Q i) :
    cellVol (κ.toLatticePolygon s) Q =
      (1 - (Q : ℚ)⁻¹) ^ κ.faces.length * ((Q : ℚ) ^ Npg κ s)⁻¹ := by
  rw [L4.cellVolume_eq cellVol (κ.toLatticePolygon s) Q hQ hfactor]
  unfold L4.bb1Value
  rw [toLatticePolygon_newtonVertexCount κ s,
    ← toLatticePolygon_newtonExponent κ s, zpow_natCast]

/-!
## Unit II-M9 — `L6e_partition` (L6e(i): off Z_e the cells partition C_e\R_e)

BP_II §1.9 displays this unit as `theorem L6e_partition ...` — the signature is
elided in the blueprint; the mathematical content is pinned by the displayed
docstring ("(i) off Z_e the cells partition C_e\R_e (every a_e ≠ 0 point in
exactly ONE cell, no a_e = 0 point in any — the finite-hull argument +
(NP-SLOPES))") and the math source of record
(`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` §3, L6e proof (i)), same
sanctioned-adjustment convention as units II-M4/II-M5/II-M8/II-M7 above.
FLAGGED for E-phase statement-fence sign-off.

**Milestone split (BP_II §2 preamble).** II-M9 is a coordination milestone: the
partition theorem is split into named coverage/disjointness component
declarations (the same in-file convention as II-M2's helper split):
`L6e_covers` (existence), `L6e_disjoint` (uniqueness), `L6e_zero_notMem`
(the a_e = 0 exclusion), with `L6e_partition` the assembly; the companion
lemmas `cell_subset_Ce` / `cell_not_Re` / `cell_zero_ne_top` certify the
converse inclusion (every cell point lies in C_e\R_e with a_e ≠ 0), making the
partition of C_e\R_e honest as a set identity.

**Vocabulary.** A point of coefficient space enters as its column-valuation
vector `w : ℕ → WithTop ℤ`: column `c ∈ {0,…,e−1}` carries
`w c` = v(a_{e−c}) = v(g.coeff c) (top-down blueprint index a_i = coeff of
x^{e−i}; the II-M3 instantiation is `w c := OrderDual.ofDual
(v (g.coeff c)).toAdd`). The anchor column (e, 0) (monic, v(lead) = 0) is
data-independent and enters through `heights κ s e = 0`, so `w` is only read
on columns < e. In this vocabulary: g ∈ C_e ⟺ ∀ c < e, 1 ≤ w c;
g ∈ R_e ⟺ ∀ c < e, (e − c) ≤ w c; a_e = 0 ⟺ w 0 = ⊤. `CellMem` is the L6a
display verbatim: (α) `⌈h_c⌉ ≤ w c` at every column `c < e` (the display's own
ceiling form: v is an integer or ∞), (β) equality at the k vertex columns
`x_j`, `j < k` (there `⌈h⌉ = h ∈ ℤ`, `vertexHeight_int`, so the ceiling form
is exact).

**Honest deviation note (conditionality REDUCTION).** The unit-table sketch
routes admissibility through the (NP-SLOPES) row (root valuations = slopes);
the proofs below are purely coefficient-side over the `FaceKind`/`heights`
data — the C_e\R_e hypotheses pin the last-face slope into (0,1) directly on
the finite lower hull, so NO `SemanticRows` row is consumed and the component
theorems are unconditional. The dependency II-M6 (`hull_eq_iff_cell`, Wave 4a)
is likewise not consumed: uniqueness is proved directly (mutual chord bounds +
reading the face structure off the unit drops).

**As-built status (II-M9, this pass).** PROVED sorry-free: `CellMem` (the
L6a cell, definition), `L6e_zero_notMem` + `cell_zero_ne_top` (the a_e = 0
exclusion, both directions), `cell_subset_Ce` + `cell_not_Re` (the converse
inclusion: every cell point lies in C_e\R_e with a_e ≠ 0), `L6e_disjoint`
(uniqueness — every point lies in AT MOST one cell), and the assembly
`L6e_partition` (conditional only on its own components). BLOCKED (one
`sorry`): `L6e_covers`, the finite-hull existence leg — it needs the lower-
convex-hull construction layer that the un-landed Wave-4a unit II-M6 also
needs; the verified proof mechanism is recorded at the sorry site. Until
`L6e_covers` lands, `L6e_partition`'s existence half is conditional on it;
the uniqueness and exclusion halves are unconditional theorems.
-/

/-- **The L6a cell** (membership form, over column-valuation data): (α) at
every column `c < e`, `⌈h_c⌉ ≤ w c`; (β) at the k vertex columns `x_j`,
`j < k`, equality `w (x_j) = ⌈h_{x_j}⌉` (`= h_{x_j} ∈ ℤ` by
`vertexHeight_int`). [Unit II-M9 vocabulary; the L6a display's set, brief §3.] -/
def CellMem (κ : FaceKind e) (s : SlopeTuple κ) (w : ℕ → WithTop ℤ) : Prop :=
  (∀ c < e, ((⌈heights κ s c⌉ : ℤ) : WithTop ℤ) ≤ w c) ∧
  (∀ j < κ.faces.length,
    w (κ.x j) = ((⌈heights κ s (κ.x j)⌉ : ℤ) : WithTop ℤ))

/-- Vertex abscissas never exceed the width: `x j ≤ e`. [II-M9 helper.] -/
theorem FaceKind.x_le_width (κ : FaceKind e) (j : ℕ) : κ.x j ≤ e := by
  rcases le_or_gt j κ.faces.length with hj | hj
  · have := κ.x_mono hj
    rwa [κ.x_length] at this
  · have : κ.x j = κ.x κ.faces.length := by
      unfold FaceKind.x
      rw [List.take_of_length_le (by omega), List.take_of_length_le le_rfl]
    rw [this, κ.x_length]

/-- The right anchor: `heights κ s e = 0`. [II-M9 helper.] -/
theorem heights_width (κ : FaceKind e) (s : SlopeTuple κ) :
    heights κ s e = 0 := by
  unfold heights
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [max_eq_right (κ.x_le_width _), max_eq_right (κ.x_le_width _)]
  simp

/-- Every cell point has a_e ≠ 0 (`w 0 ≠ ⊤`): column 0 = x_0 is a vertex
column, where (β) pins `w 0` to an integer. [II-M9 component: the converse of
the exclusion leg.] -/
theorem cell_zero_ne_top {κ : FaceKind e} {s : SlopeTuple κ}
    {w : ℕ → WithTop ℤ} (he : 0 < e) (h : CellMem κ s w) : w 0 ≠ ⊤ := by
  have hne : κ.faces ≠ [] := by
    intro hnil
    have hs := κ.hsum
    rw [hnil] at hs
    simp at hs
    omega
  have hβ := h.2 0 (List.length_pos_of_ne_nil hne)
  simp only [FaceKind.x_zero] at hβ
  rw [hβ]
  exact WithTop.coe_ne_top

/-- **II-M9 exclusion component**: no `a_e = 0` point (`w 0 = ⊤`) lies in any
cell — the column-0 vertex equality is impossible at v = ∞. -/
theorem L6e_zero_notMem {w : ℕ → WithTop ℤ} (he : 0 < e) (h0 : w 0 = ⊤)
    (κ : FaceKind e) (s : SlopeTuple κ) : ¬ CellMem κ s w :=
  fun h => cell_zero_ne_top he h h0

/-- Every cell point lies in C_e: `1 ≤ w c` at every column (from (α) and
`one_le_ceil_height`). [II-M9 companion, converse inclusion half a.] -/
theorem cell_subset_Ce {κ : FaceKind e} {s : SlopeTuple κ}
    {w : ℕ → WithTop ℤ} (h : CellMem κ s w) : ∀ c < e, 1 ≤ w c := by
  intro c hc
  refine le_trans ?_ (h.1 c hc)
  exact_mod_cast one_le_ceil_height κ s hc

/-- No cell point lies in R_e: at the last vertex column `x_{k−1}` the pinned
value `a_{k−1}·d_{k−1}` is strictly below the R_e threshold
`e − x_{k−1} = L_{k−1} = b_{k−1}·d_{k−1}` (since `a_{k−1} < b_{k−1}`, `hlt1`).
[II-M9 companion, converse inclusion half b.] -/
theorem cell_not_Re {κ : FaceKind e} {s : SlopeTuple κ}
    {w : ℕ → WithTop ℤ} (he : 0 < e) (h : CellMem κ s w) :
    ¬ ∀ c < e, (((e - c : ℕ) : ℤ) : WithTop ℤ) ≤ w c := by
  intro hall
  have hne : κ.faces ≠ [] := by
    intro hnil
    have hs := κ.hsum
    rw [hnil] at hs
    simp at hs
    omega
  have hk : 0 < κ.faces.length := List.length_pos_of_ne_nil hne
  set jl : Fin κ.faces.length := ⟨κ.faces.length - 1, by omega⟩ with hjl
  have hjlval : (jl : ℕ) = κ.faces.length - 1 := rfl
  -- the last vertex column and its face data
  have hcstar : κ.x (κ.faces.length - 1) < e := κ.x_lt_width (by omega)
  have hxsucc := κ.x_succ_of_lt (show κ.faces.length - 1 < κ.faces.length by omega)
  have hxe : κ.x (κ.faces.length - 1 + 1) = e := by
    rw [(by omega : κ.faces.length - 1 + 1 = κ.faces.length), κ.x_length]
  -- e − x_{k−1} = L_{k−1}
  have hLwidth : e - κ.x (κ.faces.length - 1) = (κ.faces[κ.faces.length - 1].1 : ℕ) := by
    omega
  -- the vertex height at x_{k−1} is the single term a_{k−1}·d_{k−1}
  have hvh := vertexHeight_int κ s (κ.faces.length - 1)
  have hfilter : Finset.univ.filter
      (fun j' : Fin κ.faces.length => κ.faces.length - 1 ≤ (j' : ℕ)) = {jl} := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hle
      exact Fin.ext (by omega)
    · intro hj'
      subst hj'
      omega
  rw [hfilter, Finset.sum_singleton] at hvh
  -- b ∣ L, d = L/b, a < b, d ≥ 1
  have hmem : κ.faces[κ.faces.length - 1] ∈ κ.faces := List.getElem_mem _
  have hbdvd : (κ.faces[κ.faces.length - 1].2 : ℕ) ∣ (κ.faces[κ.faces.length - 1].1 : ℕ) :=
    κ.hdvd _ hmem
  have hd := κ.d_of_lt (show κ.faces.length - 1 < κ.faces.length by omega)
  have hLbd : (κ.faces[κ.faces.length - 1].1 : ℕ) =
      (κ.faces[κ.faces.length - 1].2 : ℕ) * κ.d (κ.faces.length - 1) := by
    rw [hd, Nat.mul_div_cancel' hbdvd]
  have hdpos : 0 < κ.d (κ.faces.length - 1) := by
    rcases Nat.eq_zero_or_pos (κ.d (κ.faces.length - 1)) with h0 | h
    · exfalso
      rw [h0, Nat.mul_zero] at hLbd
      have := κ.faces[κ.faces.length - 1].1.pos
      omega
    · exact h
  have hab : (s.a jl : ℕ) < (κ.faces[κ.faces.length - 1].2 : ℕ) := by
    have hlt1 := s.hlt1 hne
    have hgl : κ.faces.getLast hne = κ.faces[κ.faces.length - 1] := by
      rw [List.getLast_eq_getElem]
    rw [hgl] at hlt1
    have hbpos : (0 : ℚ) < ((κ.faces[κ.faces.length - 1].2 : ℕ) : ℚ) := by
      exact_mod_cast κ.faces[κ.faces.length - 1].2.pos
    rw [div_lt_one hbpos] at hlt1
    exact_mod_cast hlt1
  -- the pinned value is a·d < b·d = L = e − x_{k−1}
  have hstrict : (s.a jl : ℕ) * κ.d ((jl : ℕ)) < e - κ.x (κ.faces.length - 1) := by
    rw [hLwidth, hLbd]
    exact (Nat.mul_lt_mul_right hdpos).mpr hab
  -- fire the R_e hypothesis at the last vertex column
  have hRe' := hall (κ.x (κ.faces.length - 1)) hcstar
  have hβ := h.2 (κ.faces.length - 1) (by omega)
  rw [hβ, hvh, Int.ceil_natCast] at hRe'
  have : ((e - κ.x (κ.faces.length - 1) : ℕ) : ℤ) ≤
      (((s.a jl : ℕ) * κ.d ((jl : ℕ)) : ℕ) : ℤ) := by
    exact_mod_cast hRe'
  omega

/-- Within face `j` (columns `x_j ≤ i < x_{j+1}`), the unit drop of the
polygon is the slope: `h_i − h_{i+1} = a_j/b_j`. [II-M9 helper; the
`heights_right_dist` linearity read one unit step at a time.] -/
theorem heights_drop (κ : FaceKind e) (s : SlopeTuple κ)
    (j : Fin κ.faces.length) {i : ℕ} (hlo : κ.x (j : ℕ) ≤ i)
    (hhi : i < κ.x ((j : ℕ) + 1)) :
    heights κ s i - heights κ s (i + 1) =
      ((s.a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) := by
  have hxj := κ.x_succ_of_lt j.isLt
  have hget : κ.faces.get j = κ.faces[(j : ℕ)] := rfl
  set t := κ.x ((j : ℕ) + 1) - i with ht
  have ht1 : 1 ≤ t := by omega
  have htL : t ≤ ((κ.faces.get j).1 : ℕ) := by rw [hget]; omega
  have e1 := heights_right_dist κ s j htL
  have e2 := heights_right_dist κ s j
    (show t - 1 ≤ ((κ.faces.get j).1 : ℕ) by omega)
  rw [(show κ.x ((j : ℕ) + 1) - t = i by omega)] at e1
  rw [(show κ.x ((j : ℕ) + 1) - (t - 1) = i + 1 by omega)] at e2
  rw [e1, e2, Nat.cast_sub ht1]
  push_cast
  ring

/-- Every column `i < e` lies in a (unique) face: the largest `j` with
`x_j ≤ i` works. [II-M9 helper.] -/
theorem exists_face (κ : FaceKind e) {i : ℕ} (hi : i < e) :
    ∃ j : Fin κ.faces.length, κ.x (j : ℕ) ≤ i ∧ i < κ.x ((j : ℕ) + 1) := by
  have hP0 : κ.x 0 ≤ i := by simp
  have hspec : κ.x (Nat.findGreatest (fun m => κ.x m ≤ i) κ.faces.length) ≤ i :=
    Nat.findGreatest_spec (P := fun m => κ.x m ≤ i) (Nat.zero_le _) hP0
  have hjnle : Nat.findGreatest (fun m => κ.x m ≤ i) κ.faces.length ≤
      κ.faces.length := Nat.findGreatest_le _
  have hjnlt : Nat.findGreatest (fun m => κ.x m ≤ i) κ.faces.length <
      κ.faces.length := by
    rcases Nat.eq_or_lt_of_le hjnle with heq | h
    · exfalso
      rw [heq, κ.x_length] at hspec
      omega
    · exact h
  refine ⟨⟨Nat.findGreatest (fun m => κ.x m ≤ i) κ.faces.length, hjnlt⟩,
    hspec, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact Nat.findGreatest_is_greatest (P := fun m => κ.x m ≤ i)
    (Nat.lt_succ_self _) (by omega) hcon

/-- The unit drops are antitone in the column (slopes decrease left to
right): for `i ≤ i' < e`, `h_{i'} − h_{i'+1} ≤ h_i − h_{i+1}`. [II-M9
helper: discrete convexity of the polygon.] -/
theorem heights_drop_antitone (κ : FaceKind e) (s : SlopeTuple κ) {i i' : ℕ}
    (hii' : i ≤ i') (hi' : i' < e) :
    heights κ s i' - heights κ s (i' + 1) ≤
      heights κ s i - heights κ s (i + 1) := by
  obtain ⟨j, hj1, hj2⟩ := exists_face κ (lt_of_le_of_lt hii' hi')
  obtain ⟨j', hj'1, hj'2⟩ := exists_face κ hi'
  rw [heights_drop κ s j hj1 hj2, heights_drop κ s j' hj'1 hj'2]
  rcases lt_trichotomy (j : ℕ) (j' : ℕ) with h | h | h
  · exact le_of_lt (s.hdesc j j' (Fin.lt_def.mpr h))
  · rw [Fin.ext h]
  · exfalso
    have hxx : κ.x ((j' : ℕ) + 1) ≤ κ.x (j : ℕ) := κ.x_mono (by omega)
    omega

/-- Telescoping the unit drops: `h_A − h_B = Σ_{i ∈ [A,B)} (h_i − h_{i+1})`.
[II-M9 helper.] -/
theorem heights_telescope (κ : FaceKind e) (s : SlopeTuple κ) {A B : ℕ}
    (hAB : A ≤ B) :
    heights κ s A - heights κ s B =
      ∑ i ∈ Finset.Ico A B, (heights κ s i - heights κ s (i + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top hAB, ← ih]
    ring

/-- The chord bound (discrete convexity): for `A ≤ c ≤ B ≤ e`,
`(B−A)·h_c ≤ (B−c)·h_A + (c−A)·h_B` — the polygon lies on or below every
chord between its own columns. [II-M9 helper.] -/
theorem heights_chord (κ : FaceKind e) (s : SlopeTuple κ) {A c B : ℕ}
    (hAc : A ≤ c) (hcB : c ≤ B) (hB : B ≤ e) :
    ((B - A : ℕ) : ℚ) * heights κ s c ≤
      ((B - c : ℕ) : ℚ) * heights κ s A +
        ((c - A : ℕ) : ℚ) * heights κ s B := by
  rcases Nat.eq_or_lt_of_le hcB with rfl | hcB'
  · rw [Nat.sub_self]
    simp
  rcases Nat.eq_or_lt_of_le hAc with rfl | hAc'
  · rw [Nat.sub_self]
    simp
  have hc_lt_e : c < e := by omega
  set δc := heights κ s c - heights κ s (c + 1) with hδ
  -- the left stretch: every drop is ≥ δc
  have hS1 : ((c - A : ℕ) : ℚ) * δc ≤ heights κ s A - heights κ s c := by
    rw [heights_telescope κ s (le_of_lt hAc')]
    calc ((c - A : ℕ) : ℚ) * δc = ∑ _i ∈ Finset.Ico A c, δc := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.Ico A c, (heights κ s i - heights κ s (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_Ico] at hi
          exact heights_drop_antitone κ s (by omega) hc_lt_e
  -- the right stretch: every drop is ≤ δc
  have hS2 : heights κ s c - heights κ s B ≤ ((B - c : ℕ) : ℚ) * δc := by
    rw [heights_telescope κ s (le_of_lt hcB')]
    calc ∑ i ∈ Finset.Ico c B, (heights κ s i - heights κ s (i + 1))
        ≤ ∑ _i ∈ Finset.Ico c B, δc := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_Ico] at hi
          exact heights_drop_antitone κ s (by omega) (by omega)
      _ = ((B - c : ℕ) : ℚ) * δc := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : ((B - c : ℕ) : ℚ) * (((c - A : ℕ) : ℚ) * δc) ≤
      ((B - c : ℕ) : ℚ) * (heights κ s A - heights κ s c) :=
    mul_le_mul_of_nonneg_left hS1 (Nat.cast_nonneg _)
  have h2 : ((c - A : ℕ) : ℚ) * (heights κ s c - heights κ s B) ≤
      ((c - A : ℕ) : ℚ) * (((B - c : ℕ) : ℚ) * δc) :=
    mul_le_mul_of_nonneg_left hS2 (Nat.cast_nonneg _)
  have hsplit : ((B - A : ℕ) : ℚ) = ((B - c : ℕ) : ℚ) + ((c - A : ℕ) : ℚ) := by
    have : (B - A : ℕ) = (B - c : ℕ) + (c - A : ℕ) := by omega
    exact_mod_cast this
  rw [hsplit]
  nlinarith [h1, h2]

/-- At a κ'-vertex column, the κ-polygon lies on or below the κ'-polygon:
(β') pins `w` there to the integer κ'-height, and (α) bounds the κ-ceiling by
it. [II-M9 helper.] -/
theorem cell_le_at_vertex {w : ℕ → WithTop ℤ} {κ κ' : FaceKind e}
    {s : SlopeTuple κ} {s' : SlopeTuple κ'}
    (h : CellMem κ s w) (h' : CellMem κ' s' w) {j : ℕ}
    (hj : j < κ'.faces.length) :
    heights κ s (κ'.x j) ≤ heights κ' s' (κ'.x j) := by
  have hv : κ'.x j < e := κ'.x_lt_width hj
  have hα := h.1 (κ'.x j) hv
  have hβ := h'.2 j hj
  rw [hβ] at hα
  have hint : ⌈heights κ s (κ'.x j)⌉ ≤ ⌈heights κ' s' (κ'.x j)⌉ := by
    exact_mod_cast hα
  obtain ⟨N, hN⟩ : ∃ N : ℕ, heights κ' s' (κ'.x j) = (N : ℚ) :=
    ⟨_, vertexHeight_int κ' s' j⟩
  calc heights κ s (κ'.x j) ≤ (⌈heights κ s (κ'.x j)⌉ : ℚ) := Int.le_ceil _
    _ ≤ (⌈heights κ' s' (κ'.x j)⌉ : ℚ) := by exact_mod_cast hint
    _ = heights κ' s' (κ'.x j) := by rw [hN]; simp

/-- The κ-polygon lies on or below the κ'-polygon at EVERY column ≤ e when
both cells contain a common point: the κ'-face endpoints are pinned
(`cell_le_at_vertex`, or the shared anchor at `e`), the κ-polygon is below
its own chord (`heights_chord`), and the κ'-polygon IS that chord on its own
face (`heights_right_dist` linearity). [II-M9 helper.] -/
theorem cell_heights_le {w : ℕ → WithTop ℤ} {κ κ' : FaceKind e}
    {s : SlopeTuple κ} {s' : SlopeTuple κ'}
    (h : CellMem κ s w) (h' : CellMem κ' s' w) :
    ∀ c ≤ e, heights κ s c ≤ heights κ' s' c := by
  intro c hce
  rcases Nat.eq_or_lt_of_le hce with rfl | hclt
  · rw [heights_width, heights_width]
  obtain ⟨j', hj'1, hj'2⟩ := exists_face κ' hclt
  have hA : heights κ s (κ'.x (j' : ℕ)) ≤ heights κ' s' (κ'.x (j' : ℕ)) :=
    cell_le_at_vertex h h' j'.isLt
  have hB : heights κ s (κ'.x ((j' : ℕ) + 1)) ≤
      heights κ' s' (κ'.x ((j' : ℕ) + 1)) := by
    rcases Nat.lt_or_ge ((j' : ℕ) + 1) κ'.faces.length with hlt | hge
    · exact cell_le_at_vertex h h' hlt
    · have hxe : κ'.x ((j' : ℕ) + 1) = e := by
        have h1 : κ'.x ((j' : ℕ) + 1) ≤ e := κ'.x_le_width _
        have h2 := κ'.x_mono hge
        rw [κ'.x_length] at h2
        omega
      rw [hxe, heights_width, heights_width]
  have hBe : κ'.x ((j' : ℕ) + 1) ≤ e := κ'.x_le_width _
  have hchord := heights_chord κ s hj'1 (le_of_lt hj'2) hBe
  have hlin : ∀ x : ℕ, κ'.x (j' : ℕ) ≤ x → x ≤ κ'.x ((j' : ℕ) + 1) →
      heights κ' s' x =
        ((s'.a j' : ℕ) : ℚ) / (((κ'.faces.get j').2 : ℕ) : ℚ) *
            ((κ'.x ((j' : ℕ) + 1) - x : ℕ) : ℚ) +
          heights κ' s' (κ'.x ((j' : ℕ) + 1)) := by
    intro x hx1 hx2
    have hgt : κ'.faces.get j' = κ'.faces[(j' : ℕ)] := rfl
    have hxsucc := κ'.x_succ_of_lt j'.isLt
    have ht : κ'.x ((j' : ℕ) + 1) - x ≤ ((κ'.faces.get j').1 : ℕ) := by
      rw [hgt]; omega
    have hrd := heights_right_dist κ' s' j' ht
    rw [(show κ'.x ((j' : ℕ) + 1) - (κ'.x ((j' : ℕ) + 1) - x) = x by
      omega)] at hrd
    exact hrd
  set A := κ'.x (j' : ℕ) with hAdef
  set B := κ'.x ((j' : ℕ) + 1) with hBdef
  have hBA : (0 : ℚ) < ((B - A : ℕ) : ℚ) := by
    have : 0 < B - A := by omega
    exact_mod_cast this
  have hsplit : ((B - A : ℕ) : ℚ) =
      ((B - c : ℕ) : ℚ) + ((c - A : ℕ) : ℚ) := by
    have : (B - A : ℕ) = (B - c : ℕ) + (c - A : ℕ) := by omega
    exact_mod_cast this
  have hAeq := hlin A le_rfl (by omega)
  have hceq := hlin c hj'1 (le_of_lt hj'2)
  have hmid : ((B - c : ℕ) : ℚ) * heights κ' s' A +
      ((c - A : ℕ) : ℚ) * heights κ' s' B =
      ((B - A : ℕ) : ℚ) * heights κ' s' c := by
    rw [hAeq, hceq, hsplit]
    ring
  have hfinal : ((B - A : ℕ) : ℚ) * heights κ s c ≤
      ((B - A : ℕ) : ℚ) * heights κ' s' c := by
    calc ((B - A : ℕ) : ℚ) * heights κ s c
        ≤ ((B - c : ℕ) : ℚ) * heights κ s A +
            ((c - A : ℕ) : ℚ) * heights κ s B := hchord
      _ ≤ ((B - c : ℕ) : ℚ) * heights κ' s' A +
            ((c - A : ℕ) : ℚ) * heights κ' s' B :=
          add_le_add (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _))
            (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _))
      _ = ((B - A : ℕ) : ℚ) * heights κ' s' c := hmid
  exact le_of_mul_le_mul_left hfinal hBA

/-- Two cells through a common point have EQUAL polygons on all columns ≤ e
(mutual `cell_heights_le`). [II-M9 helper.] -/
theorem cell_heights_eq {w : ℕ → WithTop ℤ} {κ κ' : FaceKind e}
    {s : SlopeTuple κ} {s' : SlopeTuple κ'}
    (h : CellMem κ s w) (h' : CellMem κ' s' w) :
    ∀ c ≤ e, heights κ s c = heights κ' s' c := fun c hc =>
  le_antisymm (cell_heights_le h h' c hc) (cell_heights_le h' h c hc)

/-- Equal positive fractions in lowest terms have equal numerators and
denominators. [II-M9 helper.] -/
theorem coprime_frac_eq {a b a' b' : ℕ} (hb : 0 < b) (hb' : 0 < b')
    (hcop : Nat.Coprime a b) (hcop' : Nat.Coprime a' b')
    (h : (a : ℚ) / (b : ℚ) = (a' : ℚ) / (b' : ℚ)) : a = a' ∧ b = b' := by
  have hbq : ((b : ℕ) : ℚ) ≠ 0 := by positivity
  have hb'q : ((b' : ℕ) : ℚ) ≠ 0 := by positivity
  rw [div_eq_div_iff hbq hb'q] at h
  have hcross : a * b' = a' * b := by exact_mod_cast h
  have h1 : b ∣ b' := by
    refine hcop.symm.dvd_of_dvd_mul_left ?_
    exact ⟨a', by rw [hcross, Nat.mul_comm]⟩
  have h2 : b' ∣ b := by
    refine hcop'.symm.dvd_of_dvd_mul_left ?_
    exact ⟨a, by rw [← hcross, Nat.mul_comm]⟩
  have hbb : b = b' := Nat.dvd_antisymm h1 h2
  subst hbb
  exact ⟨Nat.eq_of_mul_eq_mul_right hb hcross, rfl⟩

/-- `FaceKind` is determined by its face list (the remaining fields are
propositional). [II-M9 helper.] -/
theorem FaceKind.faces_ext {κ κ' : FaceKind e} (h : κ.faces = κ'.faces) :
    κ = κ' := by
  cases κ
  cases κ'
  simp only at h
  subst h
  rfl

/-- `SlopeTuple` is determined by its numerator vector (the remaining fields
are propositional). [II-M9 helper.] -/
theorem SlopeTuple.a_ext {κ : FaceKind e} {s s' : SlopeTuple κ}
    (h : s.a = s'.a) : s = s' := by
  cases s
  cases s'
  simp only at h
  subst h
  rfl

/-- At an interior vertex column `x_j` (`0 < j < k`) the unit drop strictly
changes (`hdesc`). [II-M9 helper.] -/
theorem drop_ne_at_vertex (κ : FaceKind e) (s : SlopeTuple κ) {j : ℕ}
    (hj0 : 0 < j) (hj : j < κ.faces.length) :
    heights κ s (κ.x j - 1) - heights κ s (κ.x j) ≠
      heights κ s (κ.x j) - heights κ s (κ.x j + 1) := by
  have hx0j : κ.x 0 < κ.x j := κ.x_lt_of_lt hj0 (le_of_lt hj)
  have hx00 : κ.x 0 = 0 := κ.x_zero
  have hc1 : 0 < κ.x j := by omega
  have hxprev : κ.x (j - 1) < κ.x j := κ.x_lt_of_lt (by omega) (le_of_lt hj)
  have hd1 := heights_drop κ s ⟨j - 1, by omega⟩ (i := κ.x j - 1)
    (show κ.x (j - 1) ≤ κ.x j - 1 by omega)
    (show κ.x j - 1 < κ.x ((j - 1) + 1) by
      rw [(show j - 1 + 1 = j by omega)]; omega)
  rw [(show κ.x j - 1 + 1 = κ.x j by omega)] at hd1
  have hd2 := heights_drop κ s ⟨j, hj⟩ (i := κ.x j) le_rfl
    (κ.x_lt_of_lt (Nat.lt_succ_self j) hj)
  rw [hd1, hd2]
  exact ne_of_gt (s.hdesc ⟨j - 1, by omega⟩ ⟨j, hj⟩
    (Fin.lt_def.mpr (show j - 1 < j by omega)))

/-- At a non-vertex column `0 < c < e` the unit drop does not change (both
steps sit in the same face). [II-M9 helper.] -/
theorem drop_eq_at_nonvertex (κ : FaceKind e) (s : SlopeTuple κ) {c : ℕ}
    (hc0 : 0 < c) (hce : c < e)
    (hnv : ∀ j < κ.faces.length, κ.x j ≠ c) :
    heights κ s (c - 1) - heights κ s c =
      heights κ s c - heights κ s (c + 1) := by
  obtain ⟨j, hj1, hj2⟩ := exists_face κ hce
  have hne : κ.x (j : ℕ) ≠ c := hnv _ j.isLt
  have hd1 := heights_drop κ s j (i := c - 1)
    (show κ.x (j : ℕ) ≤ c - 1 by omega)
    (show c - 1 < κ.x ((j : ℕ) + 1) by omega)
  rw [(show c - 1 + 1 = c by omega)] at hd1
  have hd2 := heights_drop κ s j hj1 hj2
  rw [hd1, hd2]

/-- Vertex-column characterization: `c` is a vertex column of (κ, s) iff
`c = 0` or the unit drop strictly changes at `c` (with `0 < c < e`). The
right-hand side depends on the polygon only through `heights` — the key to
reading the face structure off the height function. [II-M9 helper.] -/
theorem mem_vertexSet_iff (κ : FaceKind e) (s : SlopeTuple κ) (he : 0 < e)
    {c : ℕ} :
    (∃ j < κ.faces.length, κ.x j = c) ↔
      (c = 0 ∨ (0 < c ∧ c < e ∧
        heights κ s (c - 1) - heights κ s c ≠
          heights κ s c - heights κ s (c + 1))) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Or.inl κ.x_zero
    · refine Or.inr ⟨?_, κ.x_lt_width hj, drop_ne_at_vertex κ s hj0 hj⟩
      have := κ.x_lt_of_lt hj0 (le_of_lt hj)
      simpa using this
  · rintro (rfl | ⟨hc0, hce, hne⟩)
    · have hnil : κ.faces ≠ [] := by
        intro hnil
        have hs := κ.hsum
        rw [hnil] at hs
        simp at hs
        omega
      exact ⟨0, List.length_pos_of_ne_nil hnil, κ.x_zero⟩
    · by_contra hcon
      push_neg at hcon
      exact hne (drop_eq_at_nonvertex κ s hc0 hce hcon)

/-- The parametrization (κ, s) ↦ heights is injective: equal height
functions on all columns ≤ e force equal face kinds and slope tuples. The
faces are read off the height function: vertex columns are where the unit
drop changes (`mem_vertexSet_iff`), widths are vertex differences, slopes
are the drops, and lowest-terms uniqueness recovers (a_j, b_j).
[II-M9 helper — the uniqueness engine.] -/
theorem heights_inj {κ κ' : FaceKind e} {s : SlopeTuple κ}
    {s' : SlopeTuple κ'}
    (hh : ∀ c ≤ e, heights κ s c = heights κ' s' c) :
    (⟨κ, s⟩ : Σ κ : FaceKind e, SlopeTuple κ) = ⟨κ', s'⟩ := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · -- e = 0: both face lists are empty
    have hnil : ∀ κ₀ : FaceKind 0, κ₀.faces = [] := by
      intro κ₀
      cases hfc : κ₀.faces with
      | nil => rfl
      | cons f rest =>
        exfalso
        have hs := κ₀.hsum
        rw [hfc] at hs
        simp only [List.map_cons, List.sum_cons] at hs
        have := f.1.pos
        omega
    have hκ : κ = κ' := FaceKind.faces_ext ((hnil κ).trans (hnil κ').symm)
    subst hκ
    have hs : s = s' := SlopeTuple.a_ext (funext fun j => by
      have hlen : κ.faces.length = 0 := by simp [hnil κ]
      exact absurd j.isLt (by omega))
    rw [hs]
  -- e > 0: the vertex sets agree, hence faces and slopes agree
  · have hmemV : ∀ c : ℕ, (∃ j < κ.faces.length, κ.x j = c) ↔
        (∃ j < κ'.faces.length, κ'.x j = c) := by
      intro c
      rw [mem_vertexSet_iff κ s he, mem_vertexSet_iff κ' s' he]
      constructor
      · rintro (h0 | ⟨hc0, hce, hne⟩)
        · exact Or.inl h0
        · refine Or.inr ⟨hc0, hce, ?_⟩
          rw [← hh (c - 1) (by omega), ← hh c (by omega),
            ← hh (c + 1) (by omega)]
          exact hne
      · rintro (h0 | ⟨hc0, hce, hne⟩)
        · exact Or.inl h0
        · refine Or.inr ⟨hc0, hce, ?_⟩
          rw [hh (c - 1) (by omega), hh c (by omega), hh (c + 1) (by omega)]
          exact hne
    have hVeq : (Finset.range κ.faces.length).image κ.x =
        (Finset.range κ'.faces.length).image κ'.x := by
      ext c
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, hjc⟩
        obtain ⟨j', hj', hj'c⟩ := (hmemV c).mp ⟨j, hj, hjc⟩
        exact ⟨j', hj', hj'c⟩
      · rintro ⟨j, hj, hjc⟩
        obtain ⟨j', hj', hj'c⟩ := (hmemV c).mpr ⟨j, hj, hjc⟩
        exact ⟨j', hj', hj'c⟩
    have hinjOn : Set.InjOn κ.x (Finset.range κ.faces.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with hl | hl | hl
      · exact absurd hab (Nat.ne_of_lt (κ.x_lt_of_lt hl (by omega)))
      · exact hl
      · exact absurd hab.symm (Nat.ne_of_lt (κ.x_lt_of_lt hl (by omega)))
    have hinjOn' : Set.InjOn κ'.x (Finset.range κ'.faces.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with hl | hl | hl
      · exact absurd hab (Nat.ne_of_lt (κ'.x_lt_of_lt hl (by omega)))
      · exact hl
      · exact absurd hab.symm (Nat.ne_of_lt (κ'.x_lt_of_lt hl (by omega)))
    have hcardV : ((Finset.range κ.faces.length).image κ.x).card =
        κ.faces.length := by
      rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
    have hcardV' : ((Finset.range κ'.faces.length).image κ'.x).card =
        κ'.faces.length := by
      rw [Finset.card_image_of_injOn hinjOn', Finset.card_range]
    have hkk : κ.faces.length = κ'.faces.length := by
      rw [← hcardV, hVeq]
      exact hcardV'
    -- both abscissa enumerations are THE ordered enumeration of the same set
    have hmono : StrictMono (fun j : Fin κ.faces.length => κ.x (j : ℕ)) :=
      fun a b hab => κ.x_lt_of_lt hab (le_of_lt b.isLt)
    have hmem : ∀ j : Fin κ.faces.length,
        (fun j : Fin κ.faces.length => κ.x (j : ℕ)) j ∈
          (Finset.range κ.faces.length).image κ.x := fun j =>
      Finset.mem_image.mpr ⟨(j : ℕ), Finset.mem_range.mpr j.isLt, rfl⟩
    have hmono' : StrictMono (fun j : Fin κ.faces.length => κ'.x (j : ℕ)) :=
      fun a b hab => κ'.x_lt_of_lt hab (by have := b.isLt; omega)
    have hmem' : ∀ j : Fin κ.faces.length,
        (fun j : Fin κ.faces.length => κ'.x (j : ℕ)) j ∈
          (Finset.range κ.faces.length).image κ.x := fun j => by
      rw [hVeq]
      exact Finset.mem_image.mpr
        ⟨(j : ℕ), Finset.mem_range.mpr (by have := j.isLt; omega), rfl⟩
    have hf := Finset.orderEmbOfFin_unique hcardV hmem hmono
    have hf' := Finset.orderEmbOfFin_unique hcardV hmem' hmono'
    have hxx : ∀ j : Fin κ.faces.length, κ.x (j : ℕ) = κ'.x (j : ℕ) := by
      intro j
      have h1 := congrFun hf j
      have h2 := congrFun hf' j
      rw [h1, ← h2]
    have hxxle : ∀ j : ℕ, j ≤ κ.faces.length → κ.x j = κ'.x j := by
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · have h1 : κ'.x κ.faces.length = e := by rw [hkk, κ'.x_length]
        rw [κ.x_length, h1]
      · exact hxx ⟨j, hlt⟩
    -- read the face data off the shared abscissas and drops
    have hdropeq : ∀ i, i < e →
        heights κ s i - heights κ s (i + 1) =
          heights κ' s' i - heights κ' s' (i + 1) := by
      intro i hi
      rw [hh i (by omega), hh (i + 1) (by omega)]
    have hdata : ∀ (j : ℕ) (hj : j < κ.faces.length)
        (hj' : j < κ'.faces.length),
        (s.a ⟨j, hj⟩ : ℕ) = (s'.a ⟨j, hj'⟩ : ℕ) ∧
          κ.faces[j] = κ'.faces[j] := by
      intro j hj hj'
      have e1 := κ.x_succ_of_lt hj
      have e2 := κ'.x_succ_of_lt hj'
      have q1 := hxxle j (le_of_lt hj)
      have q2 : κ.x (j + 1) = κ'.x (j + 1) := hxxle (j + 1) hj
      have hL : (κ.faces[j].1 : ℕ) = (κ'.faces[j].1 : ℕ) := by omega
      have hcv : κ.x j < e := κ.x_lt_width hj
      have hxlt : κ.x j < κ.x (j + 1) :=
        κ.x_lt_of_lt (Nat.lt_succ_self j) hj
      have d1 := heights_drop κ s ⟨j, hj⟩ (i := κ.x j) le_rfl hxlt
      have d2 := heights_drop κ' s' ⟨j, hj'⟩ (i := κ.x j)
        (show κ'.x j ≤ κ.x j by omega)
        (show κ.x j < κ'.x (j + 1) by omega)
      have hdropc := hdropeq (κ.x j) hcv
      rw [d1, d2] at hdropc
      obtain ⟨ha, hb⟩ := coprime_frac_eq
        (κ.faces.get ⟨j, hj⟩).2.pos (κ'.faces.get ⟨j, hj'⟩).2.pos
        (s.hcop ⟨j, hj⟩) (s'.hcop ⟨j, hj'⟩) hdropc
      refine ⟨ha, ?_⟩
      have hgt1 : κ.faces.get ⟨j, hj⟩ = κ.faces[j] := rfl
      have hgt2 : κ'.faces.get ⟨j, hj'⟩ = κ'.faces[j] := rfl
      rw [hgt1] at hb
      rw [hgt2] at hb
      exact Prod.ext (PNat.coe_injective hL) (PNat.coe_injective hb)
    have hfaces : κ.faces = κ'.faces :=
      List.ext_getElem hkk fun j hj hj' => (hdata j hj hj').2
    have hκ : κ = κ' := FaceKind.faces_ext hfaces
    subst hκ
    have hs : s = s' := SlopeTuple.a_ext (funext fun j =>
      PNat.coe_injective (by simpa using (hdata (j : ℕ) j.isLt j.isLt).1))
    rw [hs]

/-- **II-M9 disjointness component**: distinct cells are disjoint — a common
point forces the same face kind and slope tuple. Proof: mutual chord bounds
give `heights κ s = heights κ' s'` on all columns ≤ e
(`cell_heights_eq`), and the face structure is read off the unit drops
(`heights_inj`). -/
theorem L6e_disjoint {w : ℕ → WithTop ℤ} {κ κ' : FaceKind e}
    {s : SlopeTuple κ} {s' : SlopeTuple κ'}
    (h : CellMem κ s w) (h' : CellMem κ' s' w) :
    (⟨κ, s⟩ : Σ κ : FaceKind e, SlopeTuple κ) = ⟨κ', s'⟩ :=
  heights_inj (cell_heights_eq h h')

/-- **II-M9 coverage component**: every C_e\R_e point with `a_e ≠ 0`
(`w 0 ≠ ⊤`) lies in some cell — the finite-hull argument: the lower convex
hull of the finite diagram points is the polygon of an admissible (κ, s). -/
theorem L6e_covers {w : ℕ → WithTop ℤ}
    (hCe : ∀ c < e, 1 ≤ w c)
    (hRe : ¬ ∀ c < e, (((e - c : ℕ) : ℤ) : WithTop ℤ) ≤ w c)
    (h0 : w 0 ≠ ⊤) :
    ∃ (κ : FaceKind e) (s : SlopeTuple κ), CellMem κ s w := by
  -- BLOCKED(II-M9): the finite lower-convex-hull layer is not yet in the
  -- corpus — it is exactly the construction the un-landed Wave-4a dependency
  -- II-M6 (`hull_eq_iff_cell`, hull existence/reading) also needs. Verified
  -- mechanism for the eventual proof (math checked against the brief's L6e(i)
  -- proof, coefficient-side): peel faces right-to-left from the anchor
  -- (e, 0); at anchor column B take the minimal candidate slope
  -- σ = min_{c < B, w c ≠ ⊤} (w c − v_B)/(B − c) and extend the face to the
  -- LEFTMOST minimizer c* (so the next anchor's minimal slope is STRICTLY
  -- larger — the leftmost-tie-break gives `hdesc`); b ∣ L is automatic
  -- (integer drop w c* − v_B over width B − c* at coprime slope a/b);
  -- s_k ∈ (0,1) i.e. `hlast`/`hlt1` for the FIRST peel from hCe (all columns
  -- ≥ 1) + hRe (some column below the slope-1 line); (α) at every column is
  -- the min property, (β) at each vertex is attainment at c*. The recursion
  -- self-similarizes by shifting w by v_B (⊤ stays ⊤). No SemanticRows row
  -- is needed. Estimated as a dedicated unit of its own size (the blueprint
  -- lists II-M9 as a coordination milestone for precisely this reason).
  sorry

/-- **II-M9, L6e(i)** (assembly): off Z_e := (C_e\R_e) ∩ {a_e = 0} the cells
partition C_e\R_e — every a_e ≠ 0 point lies in exactly ONE cell
(`L6e_covers` + `L6e_disjoint`), and no a_e = 0 point lies in any
(`L6e_zero_notMem`; `0 < e` is forced by the C_e\R_e hypotheses). -/
theorem L6e_partition {w : ℕ → WithTop ℤ}
    (hCe : ∀ c < e, 1 ≤ w c)
    (hRe : ¬ ∀ c < e, (((e - c : ℕ) : ℤ) : WithTop ℤ) ≤ w c) :
    (w 0 ≠ ⊤ →
      ∃! P : Σ κ : FaceKind e, SlopeTuple κ, CellMem P.1 P.2 w) ∧
    (w 0 = ⊤ →
      ∀ (κ : FaceKind e) (s : SlopeTuple κ), ¬ CellMem κ s w) := by
  have he : 0 < e := by
    by_contra he
    exact hRe fun c hc => absurd hc (by omega)
  constructor
  · intro h0
    obtain ⟨κ, s, hmem⟩ := L6e_covers hCe hRe h0
    exact ⟨⟨κ, s⟩, hmem, fun ⟨κ', s'⟩ h' => (L6e_disjoint h' hmem)⟩
  · intro h0 κ s
    exact L6e_zero_notMem he h0 κ s

end LeanUrat.Scaffold
