/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.O12.PolygonData

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

end LeanUrat.Scaffold
