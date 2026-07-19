/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.BlockProduct

/-!
# ProductTheorem — Phase-B wave W4d2-surj: the theorem of the product at level `N`

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md` §W4d (d2), the *NAMED OBLIGATION*
"W4d2-surj (theorem of the product at level N)": the landed multi-block node theorems
(`BlockProduct.blocks_card`, `HNode1`'s `h_node1_*`) count `imageSet` = the image of the
block-coset product under polynomial multiplication, and tie THAT to the counting recursion.
They do NOT identify `imageSet` with the classifier's multi-block `InCell` fiber.  This module
supplies the missing identification machinery.

**The two halves** (blueprint §W4d (d2), verified box-by-box in
`/workspace-vast/asving/tmp/phaseb_w4d2_0/SUMMARY.md`; the SymPy pre-check
`/workspace-vast/asving/tmp/phaseb_surj/` confirms both algebraic facts with 0 violations):

* **⊇  "sides add, residuals multiply."**  If `f = Π gᵢ` with each `gᵢ` in its block coset (the
  `imageSet` membership), then the Newton polygon of `f` is the concatenation of the factors'
  polygons and `f` sits ON/ABOVE the concatenated cell polygon.  The polygon LOWER-BOUND half is
  proved here (`imageSet_subset_concatCell`, `cell_sideAbove`): a product of cell
  members lands in the divisibility cell around the product center, and the divisibility floor is
  exactly the concatenated-polygon lower bound in `vOf` form (bridge `dvd_iff_le_zmodValuation`).
  This is condition (i) of `Matches` — CLOSED.
  The residual-multiplication content (iii) is CLOSED as a reusable core:
  `M4.residualPoly_mul` (`ResidualPolynomial.lean`) proves `residualPoly` multiplies from the
  Cauchy convolution of the coefficient data, and `residualOf_mul_of_conv` (§3b) lifts it to the
  classifier reader `residualOf (A·B) = residualOf A · residualOf B` conditional on the on-side
  convolution input.  The `ZMod(p^N)`-native product laws `zmodValuation_mul`, `zmodUnitResidue_mul`
  (§3a) are BANKED.  The engine for BOTH vertex EXACTNESS (ii) and the (iii) convolution input is now
  WIRED to `boxCoeffData` (**top-wave 2026-07-05**): §3a⁗ `boxCoeffData_eq_redP_cofactor` (the
  `boxCoeffData`-to-engine bridge), §3a⁗′ `boxCoeffData_mul_conv_of_cofactor` (the convolution),
  §3a⁗″ `redP_cofactor_mul_eq_box` (on-lattice split), §3a⁗‴ `vertex_valuation_exact` (vertex
  exactness) — all REAL, core-only, proved without editing `boxCoeffData`.  The two GEOMETRY facts
  these consume are now ALSO PROVED (**2026-07-06**, §3a⁗⁗): (b) `coeff_mul_pow_factor` — the
  `Polynomial.coeff_mul` antidiagonal expansion pushed through the on-side floor `p^V`; (c)
  `antidiag_split_class` (+ `mul_dvd_pow_of_add_le`) — the on-lattice/off-lattice per-split
  classification with the off-lattice strictly-deeper divisibility bound.  With (b)+(c) in hand the
  convolution clause of `on_side_conv` is packaged as the REAL theorem `on_side_conv_of_cofactor`
  (§3c), and `vertex_valuation_exact` supplies the vertex clause: `on_side_conv` is DISCHARGED as a
  theorem given ONLY the per-position antidiagonal-geometry data (`cof`, `hABfac`, `hsplit`) a caller
  reads off the block side memberships — there is NO residual analytic content.  The consequent
  assembly `imageSet_subset_inCellMulti` / `card_imageSet_le_fiber` is supplied as GENUINE theorems
  (§8), gated only on the per-element on-side `Matches` datum (`on_side_conv`'s output — a REAL
  theorem given the geometry data), via the `SidedBlock`/`cellOf` bridge (§7).
  **⊇ NOW CLOSED `Matches`-FREE (2026-07-06, §§10–13).**  The whole-product `Matches` hypothesis of §8
  is DISCHARGED by threading the "each block owns its side" argument over the block list:
  `offBlock_unit_on_side` (§11, the crux sub-lemma — an off-side block contributes a UNIT residue on
  another block's side, which drops out of the shape by `polyShape_isUnit` + `polyShape_mul`);
  `sideMatch_offBlock` (§11, per-side owner match from the owner's `SideMatch` + off-block unit);
  `product_matches_single_side` (§10, case B — offBlock VACUOUS) and `product_matches_two_distinct`
  (§12, case A/C — offBlock EXERCISED, each block a unit on the other's side).  The `Matches`-free ⊇
  transports are `imageSet_subset_inCellMulti_single_free` (§10) and
  `imageSet_subset_inCellMulti_two_distinct_free` (§13): `imageSet (toBlocks l) ⊆ {f | InCellMulti f
  (cellOf l) …}` with NO whole-product `Matches` hypothesis — only the honest per-block/per-side data
  (each block's own `SideMatch`, vertex exactness, cross-block unit residual factorizations) that
  `on_side_conv_of_cofactor`/`vertex_valuation_exact` produce.  All core-only ([propext,
  Classical.choice, Quot.sound]).  The remaining Phase-B obligation is ONLY P3 (⊆ Hensel
  surjectivity, below) — R1 (`polyShape_mul`, banked in `CellMenu`) and R2 (the `SidedBlock` on-side
  carriers `vAt`/`cof`) are consumed.

* **⊆  Hensel factorization surjectivity.**  If `InCellMulti f c` then `f` factors as `Π gᵢ` with
  `gᵢ` in the block cosets.  This is `HenselCount.fiber_card`'s "surjective onto its image"
  content composed over the chain — it needs every fiber element to admit SOME block
  factorization.  In the banked `HenselCount` frame this is the flat Hensel margin `2c < N`, which
  is EMPTY at all three real gate cells (`BlockProduct.gate_margin_A/B/C`); the closing lemma is
  W4d2′ (the θ-graded margin — `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal`).
  Stated precisely as `obligation_hensel_surjective` (a docstring obligation, NOT a `sorry`-backed
  theorem — discipline: we do not STATE as a theorem what we cannot prove).  The CARDINALITY route
  (§5 `image_eq_of_subset_of_card_le`) can force the full identity from ⊇ + an independent fiber
  count without a constructive lift — banked as a real forcing lemma; the independent count is the
  remaining P3 obligation.

**Scope.** Order 1, `f = 1`, `h = 1` (matching W1/W4b/W4d1's banked layer).  Additive: only
`ProductTheorem` changes (the `SidedBlock`/`cellOf` bridge is a PARALLEL carrier extending the frozen
`BlockProduct.Block`; `BlockProduct.lean` is untouched, and no `CellMenu` definition was edited).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.ProductTheorem

open LeanUrat LeanUrat.OM Polynomial
open LeanUrat.OM.CellMenu (vOf lineAt InCell InCellMulti Matches ResidRefines residOf)

/-! ## 1. The divisibility ⟺ valuation bridge

`HenselCount.cell` records coefficient conditions as `p^k`-divisibility; `CellMenu.Matches`
records them as `zmodValuation`-line bounds.  The bridge below is the single fact tying the two
frames — below the cutoff `k ≤ N`, divisibility by `p^k` is *exactly* valuation `≥ k`. -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The bridge** (divisibility ⟺ valuation lower bound, below the cutoff).  For `k ≤ N`,
`(p:ZMod(p^N))^k ∣ x` iff `k ≤ zmodValuation p N x`.  (`zmodValuation` is capped at `N`, so
`x = 0` gives valuation `N ≥ k`, matching `p^k ∣ 0`.) -/
theorem dvd_iff_le_zmodValuation {N : ℕ} {k : ℕ} (hk : k ≤ N) (x : ZMod (p ^ N)) :
    (p : ZMod (p ^ N)) ^ k ∣ x ↔ k ≤ PadicLift.zmodValuation p N x := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  rw [RestartEquiv.pow_dvd_iff_dvd_val p N hk x]
  by_cases hx : x = 0
  · subst hx
    simp [PadicLift.zmodValuation, hk]
  · rw [PadicLift.zmodValuation_of_ne_zero p hx]
    have hval0 : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out hval0)

/-! ## 2. ⊇ (the easier half): a product of cell members sits ON/ABOVE the concatenated polygon

The block cosets are contained in `HenselCount.cell centerᵢ degᵢ kᵢ` — coefficientwise
`p^{kᵢ}`-divisibility around the side center.  Iterating `BlockProduct.mul_image_subset_cell`,
`imageSet` lands in `HenselCount.cell (prodCenter) (sumDeg) k` at the common floor `k`.  Through
the bridge, cell membership at floor `k` means every coefficient has valuation `≥ k`.  The
concatenated-polygon line is, at each abscissa, `≤ k` on the coefficients it constrains (the
per-block floors dominate the concatenated line by construction of the cell centers), giving the
`SideAbove` lower bound.  This is condition (i) of `Matches`. -/

/-- Members of `HenselCount.cell P₀ d k` whose center `P₀` has coefficients of valuation `≥ k` at
every index below the polygon have their own coefficients of valuation `≥ k` there.  (A cell
member differs from `P₀` by `p^k`-multiples, so it inherits the `≥ k` valuation lower bound of
`P₀` — the additive lower bound of the `min` of two `≥ k` valuations.) -/
theorem cell_mem_le_zmodValuation {N d k : ℕ} (hk : k ≤ N)
    {P₀ : (ZMod (p ^ N))[X]} {P : (ZMod (p ^ N))[X]} (hP : P ∈ HenselCount.cell P₀ d k)
    (i : ℕ) (hP₀i : k ≤ PadicLift.zmodValuation p N (P₀.coeff i)) :
    k ≤ PadicLift.zmodValuation p N (P.coeff i) := by
  -- P.coeff i = P₀.coeff i + (P - P₀).coeff i ; both summands are p^k-divisible.
  have hdiff : (p : ZMod (p ^ N)) ^ k ∣ (P - P₀).coeff i := hP.2.2 i
  have hP₀ : (p : ZMod (p ^ N)) ^ k ∣ P₀.coeff i :=
    (dvd_iff_le_zmodValuation p hk _).mpr hP₀i
  have hsum : (p : ZMod (p ^ N)) ^ k ∣ P.coeff i := by
    have he : P.coeff i = P₀.coeff i + (P - P₀).coeff i := by
      rw [Polynomial.coeff_sub]; ring
    rw [he]; exact dvd_add hP₀ hdiff
  exact (dvd_iff_le_zmodValuation p hk _).mp hsum

/-- **`imageSet` lands in the cell around the product center** (the polygon-concatenation
containment, ⊇ half, divisibility form).  A product of block cosets — each contained in the cell
around its own center at floor `k` — lands in the cell around the PRODUCT center at floor `k`.
This is the iterated `BlockProduct.mul_image_subset_cell`, the level-`N` statement that "the
factors' polygons concatenate" at the coefficient-divisibility level. -/
theorem imageSet_subset_concatCell {N k : ℕ} :
    ∀ (l : List (BlockProduct.Block p N)),
      (∀ b ∈ l, b.coset ⊆ HenselCount.cell b.center b.deg k) →
      BlockProduct.imageSet l ⊆
        HenselCount.cell (BlockProduct.prodCenter l) (BlockProduct.sumDeg l) k := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [BlockProduct.imageSet_nil, BlockProduct.prodCenter_nil, BlockProduct.sumDeg_nil]
      intro P hP
      rw [Set.mem_singleton_iff] at hP
      subst hP
      exact HenselCount.mem_cell_self monic_one natDegree_one k
  | cons b l ih =>
      intro hall
      rw [BlockProduct.imageSet_cons, BlockProduct.prodCenter_cons, BlockProduct.sumDeg_cons]
      have hb : b.coset ⊆ HenselCount.cell b.center b.deg k := hall b List.mem_cons_self
      have hl : BlockProduct.imageSet l ⊆
          HenselCount.cell (BlockProduct.prodCenter l) (BlockProduct.sumDeg l) k :=
        ih fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')
      exact BlockProduct.mul_image_subset_cell hb hl

/-- **`SideAbove`-shaped lower bound from cell membership (⊇ condition (i)).**  If `f` lies in the
cell around a center `P₀` at floor `k`, and at every index `i` in the window `[i₀, i₁]` the center
`P₀` already sits on/above the side line (valuation `≥ ⌈lineAt⌉` there), then `f` sits on/above the
line at every window index — condition (i) of `Matches`, transported through the bridge.  (The
concatenated-cell centers `prodCenter` are the standard product representatives; each one sits on
its own concatenated polygon by construction, so this discharges (i) for the product.) -/
theorem cell_sideAbove {N n k : ℕ} (hk : k ≤ N)
    {P₀ : (ZMod (p ^ N))[X]} {f : QuotientBox.monicBox p N n}
    (hf : (f.1) ∈ HenselCount.cell P₀ n k)
    (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (hline : ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 → lineAt pr (i : ℚ) ≤ (k : ℚ))
    (hP₀ : ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 → k ≤ PadicLift.zmodValuation p N (P₀.coeff i)) :
    CellMenu.SideAbove p f pr := by
  intro i hi1 hi2
  have hval : k ≤ PadicLift.zmodValuation p N ((f.1).coeff i) :=
    cell_mem_le_zmodValuation p hk hf i (hP₀ i hi1 hi2)
  calc lineAt pr (i : ℚ) ≤ (k : ℚ) := hline i hi1 hi2
    _ ≤ (vOf p f i : ℚ) := by exact_mod_cast hval

/-! ## 3. The two remaining `Matches` conditions for the ⊇ transport

`imageSet_subset_concatCell` + `cell_sideAbove` discharge condition (i) of `Matches` (on/above the
concatenated polygon).  The FULL transport `imageSet ⊆ {f | InCellMulti f c}` additionally needs
(ii) vertex exactness and (iii)+`ResidRefines` the residual multiplication.  Both reduce, through
the machinery banked in this section, to a SINGLE remaining analytic lemma — the on-side
dominant-term convolution `on_side_conv` (§3c) — which is the level-`N` shadow of GMN Prop 2.9 and is
the same graded/dominant-transversal engine the ⊆ obligation is blocked on.

### 3a. `ZMod(p^N)`-native product laws (BANKED — below the valuation cap, valuations add / units
multiply).  These are the two number-theoretic primitives feeding both (ii) and (iii): on-side, the
menu heights are `≤ N−1` so the cap hypothesis `hcap` is met, and a product coefficient's native
valuation is the sum of the factor valuations while its unit residue is the product of the factor
unit residues.  Proven here from `ZMod.val_mul` + `Nat.factorization_mul` + the Layer-A stability
`PadicLift.factorization_mod_eq` / `ordCompl_mod_cast_eq`. -/

/-- **`zmodValuation` is additive on products below the cap** (BANKED building block).  For nonzero
`x, y` whose valuations sum below `N` (`hcap`), `zmodValuation (x·y) = zmodValuation x + zmodValuation
y`.  The product is nonzero (its valuation is `< N`), and its native valuation is
`(x.val·y.val % p^N).factorization p = (x.val·y.val).factorization p` (by `factorization_mod_eq`,
using `hcap`) `= x.val.factorization p + y.val.factorization p` (by `Nat.factorization_mul`). -/
theorem zmodValuation_mul {N : ℕ} {x y : ZMod (p ^ N)}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x * y ≠ 0)
    (hcap : (x.val).factorization p + (y.val).factorization p < N) :
    PadicLift.zmodValuation p N (x * y)
      = PadicLift.zmodValuation p N x + PadicLift.zmodValuation p N y := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  rw [PadicLift.zmodValuation_of_ne_zero p hx, PadicLift.zmodValuation_of_ne_zero p hy,
    PadicLift.zmodValuation_of_ne_zero p hxy, ZMod.val_mul]
  have hxv : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
  have hyv : y.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hy
  have hprod0 : x.val * y.val ≠ 0 := Nat.mul_ne_zero hxv hyv
  have hfmul : (x.val * y.val).factorization p
      = x.val.factorization p + y.val.factorization p := by
    rw [Nat.factorization_mul hxv hyv]; simp
  have hlt : (x.val * y.val).factorization p < N := by rw [hfmul]; exact hcap
  rw [PadicLift.factorization_mod_eq p hprod0 hlt, hfmul]

/-- **`zmodUnitResidue` is multiplicative on products below the cap** (BANKED building block).  For
nonzero `x, y` whose valuations sum below `N`, `zmodUnitResidue (x·y) = zmodUnitResidue x ·
zmodUnitResidue y` in `ZMod p`.  Reduce mod `p^N` inside `ordCompl` is stable (`ordCompl_mod_cast_eq`,
using `hcap`), and `ordCompl` splits over the product (`Nat.factorization_mul` + `pow_add` +
`Nat.mul_div_mul_comm` on the two `ordProj`-divisibilities). -/
theorem zmodUnitResidue_mul {N : ℕ} {x y : ZMod (p ^ N)}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcap : (x.val).factorization p + (y.val).factorization p < N) :
    PadicLift.zmodUnitResidue p N (x * y)
      = PadicLift.zmodUnitResidue p N x * PadicLift.zmodUnitResidue p N y := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  have hxv : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx
  have hyv : y.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hy
  have hprod0 : x.val * y.val ≠ 0 := Nat.mul_ne_zero hxv hyv
  have hfmul : (x.val * y.val).factorization p
      = x.val.factorization p + y.val.factorization p := by
    rw [Nat.factorization_mul hxv hyv]; simp
  have hlt : (x.val * y.val).factorization p < N := by rw [hfmul]; exact hcap
  rw [PadicLift.zmodUnitResidue, PadicLift.zmodUnitResidue, PadicLift.zmodUnitResidue, ZMod.val_mul,
    PadicLift.ordCompl_mod_cast_eq p hprod0 hlt]
  have hord : ordCompl[p] (x.val * y.val) = ordCompl[p] x.val * ordCompl[p] y.val := by
    rw [hfmul, pow_add, Nat.mul_div_mul_comm (Nat.ordProj_dvd _ _) (Nat.ordProj_dvd _ _)]
  rw [hord, Nat.cast_mul]

/-! ### 3a′. **Deliverable 1** — the dominant-term law for `Finset` sums (`zmodValuation_sum_unique_min`).

The level-`N` scalar analogue of `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal`
(unique dominant transversal ⟹ `det = π^V·unit`), specialised from a determinant's permutation
sum to a plain `Finset.sum` over `ZMod (p^N)`.  It is the crux of `on_side_conv` (§3c): once
`Polynomial.coeff_mul` expands a product coefficient into an antidiagonal sum with a UNIQUE
minimal-valuation term (the on-lattice split), this lemma computes the sum's valuation and unit
residue from that dominant term.

The route mirrors the determinant lemma at the scalar level: factor out `p^V`; the dominant term is
`p^V·unit`, every other term is divisible by `p^(V+1)`, so the whole sum is `p^V·(unit + p·r)` and
`unit + p·r` is again a unit (`IsNilpotent.isUnit_add_left_of_commute`, `p` nilpotent).  Reading off
the valuation and unit residue of `p^V·unit` (below the cap) gives the two conclusions.

SymPy-verified with 0 violations (`/workspace-vast/asving/tmp/phaseb_onsideconv/sum_unique_min_check.py`,
1800 cases over `p ∈ {2,3,5,7}`, `N ≤ 5`). -/

/-- **The valuation of `x = p^V·u`** (`u` a unit, `V < N`) is exactly `V`.  Route: `p^V ∣ x` gives
`V ≤ zmodValuation x`; `¬ p^(V+1) ∣ x` (else `p ∣ u`, impossible for a unit) gives
`zmodValuation x < V+1`.  Both directions through the banked bridge `dvd_iff_le_zmodValuation`. -/
theorem zmodValuation_pow_mul_unit {N V : ℕ} (hVN : V < N)
    {x : ZMod (p ^ N)} {u : (ZMod (p ^ N))ˣ} (hx : x = (p : ZMod (p ^ N)) ^ V * u) :
    PadicLift.zmodValuation p N x = V := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have hdvd : (p : ZMod (p ^ N)) ^ V ∣ x := ⟨u, hx⟩
  have hge : V ≤ PadicLift.zmodValuation p N x :=
    (dvd_iff_le_zmodValuation p (le_of_lt hVN) x).mp hdvd
  have hnd : ¬ (p : ZMod (p ^ N)) ^ (V + 1) ∣ x := by
    rintro ⟨y, hy⟩
    -- p^(V+1)·y = p^V·u ⟹ p^V·(p·y − u) = 0 ⟹ u = p·y + p^(N−V)·z, so p ∣ u: contradiction.
    have hkill : (p : ZMod (p ^ N)) ^ V * ((p : ZMod (p ^ N)) * y - (u : ZMod (p ^ N))) = 0 := by
      have : (p : ZMod (p ^ N)) ^ V * ((p : ZMod (p ^ N)) * y)
          = (p : ZMod (p ^ N)) ^ V * (u : ZMod (p ^ N)) := by
        rw [← hx, hy, pow_succ]; ring
      linear_combination this
    obtain ⟨z, hz⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (le_of_lt hVN) hkill
    -- u = p·y + p^(N−V)·z, and N−V ≥ 1, so p ∣ u.
    have hu_eq : (u : ZMod (p ^ N))
        = (p : ZMod (p ^ N)) * y - (p : ZMod (p ^ N)) ^ (N - V) * z := by
      linear_combination -hz
    have hpu : (p : ZMod (p ^ N)) ∣ (u : ZMod (p ^ N)) := by
      rw [hu_eq]
      refine dvd_sub (dvd_mul_right _ _) ?_
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega : N - V ≠ 0)) z
    -- a unit cannot be divisible by `p`: else `IsUnit p`, so `IsUnit (p^N) = IsUnit 0`, absurd
    -- in the nontrivial ring `ZMod (p^N)`.
    have hpU : IsUnit (p : ZMod (p ^ N)) := isUnit_of_dvd_unit hpu u.isUnit
    haveI : Nontrivial (ZMod (p ^ N)) := by
      haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
      exact ZMod.nontrivial _
    have h0U : IsUnit (0 : ZMod (p ^ N)) := by
      have := hpU.pow N
      rwa [← Nat.cast_pow, ZMod.natCast_self] at this
    exact not_isUnit_zero h0U
  have hlt : PadicLift.zmodValuation p N x < V + 1 := by
    by_contra hc
    exact hnd ((dvd_iff_le_zmodValuation p (by omega) x).mpr (by omega))
  omega

/-- The mod-`p` reduction ring hom `ZMod (p^N) →+* ZMod p` (for `0 < N`). -/
noncomputable def redP {N : ℕ} (hN : 0 < N) : ZMod (p ^ N) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)

theorem redP_apply {N : ℕ} (hN : 0 < N) (x : ZMod (p ^ N)) :
    redP p hN x = ((x.val : ℕ) : ZMod p) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  rw [redP, ZMod.castHom_apply, ← ZMod.natCast_val x, ZMod.natCast_val]

theorem redP_natCast_p {N : ℕ} (hN : 0 < N) :
    redP p hN ((p : ZMod (p ^ N))) = 0 := by
  rw [show ((p : ZMod (p ^ N))) = ((p : ℕ) : ZMod (p ^ N)) from rfl, map_natCast,
    ZMod.natCast_self]

/-- `redP` of a unit is nonzero (a unit in `ZMod p`).  `u.val` is coprime to `p^N`, hence to `p`,
so `p ∤ u.val`, so its image in `ZMod p` is nonzero. -/
theorem redP_unit_ne_zero {N : ℕ} (hN : 0 < N) (u : (ZMod (p ^ N))ˣ) :
    redP p hN (u : ZMod (p ^ N)) ≠ 0 := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [redP_apply, Ne, ZMod.natCast_eq_zero_iff]
  intro hpd
  have hcop : ((u : ZMod (p ^ N)).val).Coprime (p ^ N) := ZMod.val_coe_unit_coprime u
  have hpdN : p ∣ p ^ N := dvd_pow_self p hN.ne'
  have hg : p ∣ Nat.gcd ((u : ZMod (p ^ N)).val) (p ^ N) := Nat.dvd_gcd hpd hpdN
  rw [Nat.Coprime] at hcop
  rw [hcop] at hg
  exact (Nat.Prime.one_lt hp.out).ne' (Nat.dvd_one.mp hg)

/-- **`zmodUnitResidue` of `x = p^V·u`** (`u` a unit, `V < N`) is the mod-`p` reduction of `u`.
`x.val = (p^V · u.val) % p^N`, whose `ordCompl[p]` reduces mod `p` to `ordCompl[p] (p^V·u.val)`
(`ordCompl_mod_cast_eq`, valuation `V < N`), which is `u.val` (`p ∤ u.val`, so `ordCompl[p]` strips
just the `p^V`). -/
theorem zmodUnitResidue_pow_mul_unit {N V : ℕ} (hVN : V < N)
    {x : ZMod (p ^ N)} {u : (ZMod (p ^ N))ˣ} (hx : x = (p : ZMod (p ^ N)) ^ V * u) :
    PadicLift.zmodUnitResidue p N x = redP p (by omega) (u : ZMod (p ^ N)) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  -- `p ∤ u.val`
  have hcop : ((u : ZMod (p ^ N)).val).Coprime (p ^ N) := ZMod.val_coe_unit_coprime u
  have hpu : ¬ p ∣ (u : ZMod (p ^ N)).val := by
    intro hpd
    have hpdN : p ∣ p ^ N := dvd_pow_self p (by omega : N ≠ 0)
    have hg : p ∣ Nat.gcd ((u : ZMod (p ^ N)).val) (p ^ N) := Nat.dvd_gcd hpd hpdN
    rw [Nat.Coprime] at hcop; rw [hcop] at hg
    exact (Nat.Prime.one_lt hp.out).ne' (Nat.dvd_one.mp hg)
  have huv0 : (u : ZMod (p ^ N)).val ≠ 0 := by
    intro h0
    exact hpu (by rw [h0]; exact dvd_zero p)
  -- `x.val = (p^V * u.val) % p^N`
  have hpVval : ((p : ZMod (p ^ N)) ^ V).val = p ^ V := by
    rw [← Nat.cast_pow, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right hp.out.one_lt hVN)]
  have hxval : x.val = (p ^ V * (u : ZMod (p ^ N)).val) % p ^ N := by
    rw [hx, ZMod.val_mul, hpVval]
  -- set `m := p^V * u.val`, factorization `= V < N`
  set m : ℕ := p ^ V * (u : ZMod (p ^ N)).val with hm
  have hm0 : m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero V hp.out.ne_zero) huv0
  have hfacm : m.factorization p = V := by
    rw [hm, Nat.factorization_mul (pow_ne_zero V hp.out.ne_zero) huv0]
    simp [Nat.Prime.factorization_pow hp.out,
      (Nat.factorization_eq_zero_iff _ p).mpr (Or.inr (Or.inl hpu))]
  have hfaclt : m.factorization p < N := by rw [hfacm]; exact hVN
  -- `ordCompl[p] m = u.val`
  have hordm : ordCompl[p] m = (u : ZMod (p ^ N)).val := by
    rw [hfacm, hm, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos V)]
  rw [PadicLift.zmodUnitResidue, hxval,
    PadicLift.ordCompl_mod_cast_eq p hm0 hfaclt, hordm, redP_apply]

/-! ### 3a″. **Deliverable 1 (main)** — `zmodValuation_sum_unique_min`.

The dominant-term law for `Finset` sums.  Given a family `g : ι → ZMod (p^N)` and a distinguished
index `j₀ ∈ s` with `g j₀ = p^V·u` (`u` a unit, `V < N`) and every OTHER term of the sum divisible
by `p^(V+1)`, the sum is `p^V·(unit)`, so its valuation is exactly `V` and its unit residue is that
of the dominant term.  (`SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal` at the
scalar-`Finset.sum` level.) -/
theorem zmodValuation_sum_unique_min {ι : Type*} {N V : ℕ} (hVN : V < N)
    (s : Finset ι) (g : ι → ZMod (p ^ N)) (j₀ : ι) (hj₀ : j₀ ∈ s)
    {u : (ZMod (p ^ N))ˣ} (hdom : g j₀ = (p : ZMod (p ^ N)) ^ V * u)
    (hoff : ∀ j ∈ s, j ≠ j₀ → (p : ZMod (p ^ N)) ^ (V + 1) ∣ g j) :
    (∃ w : (ZMod (p ^ N))ˣ, ∑ j ∈ s, g j = (p : ZMod (p ^ N)) ^ V * w)
      ∧ PadicLift.zmodValuation p N (∑ j ∈ s, g j) = V
      ∧ PadicLift.zmodUnitResidue p N (∑ j ∈ s, g j)
          = PadicLift.zmodUnitResidue p N (g j₀) := by
  classical
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  -- Split off the dominant term; the rest is `p^(V+1)`-divisible.
  have hrest : (p : ZMod (p ^ N)) ^ (V + 1) ∣ ∑ j ∈ s.erase j₀, g j :=
    Finset.dvd_sum fun j hj =>
      hoff j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  obtain ⟨r, hr⟩ := hrest
  have hsum : ∑ j ∈ s, g j = (p : ZMod (p ^ N)) ^ V * ((u : ZMod (p ^ N)) + (p : ZMod (p ^ N)) * r) := by
    rw [← Finset.add_sum_erase _ g hj₀, hdom, hr, pow_succ]; ring
  -- `u + p·r` is a unit (`p` nilpotent, `IsNilpotent.isUnit_add_left_of_commute`).
  have hnil : IsNilpotent ((p : ZMod (p ^ N)) * r) := by
    obtain ⟨k, hk⟩ := SparseResultant.isNilpotent_p_zmod p N
    exact ⟨k, by rw [mul_pow, hk, zero_mul]⟩
  have hunit : IsUnit ((u : ZMod (p ^ N)) + (p : ZMod (p ^ N)) * r) :=
    hnil.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
  refine ⟨⟨hunit.unit, ?_⟩, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hsum
  · exact zmodValuation_pow_mul_unit p hVN (u := hunit.unit) (by rw [IsUnit.unit_spec]; exact hsum)
  · rw [zmodUnitResidue_pow_mul_unit p hVN (u := hunit.unit) (by rw [IsUnit.unit_spec]; exact hsum),
      zmodUnitResidue_pow_mul_unit p hVN (u := u) hdom, IsUnit.unit_spec, map_add, map_mul,
      redP_natCast_p, zero_mul, add_zero]

/-! ### 3a‴. **Deliverable 1′** — the COMMON-min residue law (`zmodUnitResidue_sum_common_min`).

The companion of `zmodValuation_sum_unique_min` for the CONVOLUTION part of `on_side_conv`, where
several on-lattice antidiagonal splits share the SAME minimal valuation `V` and their unit residues
ADD mod `p` (rather than one dominant term winning).  Given cofactors `c j` with `g j = p^V·c j`
(`V < N`), the mod-`p` reduction of the cofactor sum is the sum of the per-term reductions
(`redP` is a ring hom), and each per-term reduction is the term's unit residue when the term hits
valuation exactly `V`, else `0` (deeper terms are `≡ 0`).  SymPy-verified with 0 violations
(`/workspace-vast/asving/tmp/phaseb_onsideconv/common_min_check.py`, 3600 cases). -/

/-- A `ZMod (p^N)` element not divisible by `p` is a unit (`p ∤ c ⟹ c.val` coprime to `p^N`). -/
theorem isUnit_of_not_dvd_p {N : ℕ} (hN : 0 < N) {c : ZMod (p ^ N)}
    (hpc : ¬ (p : ZMod (p ^ N)) ∣ c) : IsUnit c := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have hpcv : ¬ p ∣ c.val := by
    intro hd
    have h1 : (p : ZMod (p ^ N)) ^ 1 ∣ c :=
      (RestartEquiv.pow_dvd_iff_dvd_val p N (by omega : 1 ≤ N) c).mpr (by rw [pow_one]; exact hd)
    rw [pow_one] at h1
    exact hpc h1
  have hcopp : (c.val).Coprime p := (hp.out.coprime_iff_not_dvd.mpr hpcv).symm
  have hcop : (c.val).Coprime (p ^ N) := hcopp.pow_right N
  have : IsUnit ((c.val : ℕ) : ZMod (p ^ N)) := (ZMod.isUnit_iff_coprime c.val (p ^ N)).mpr hcop
  rwa [ZMod.natCast_val, ZMod.cast_id] at this

/-- **Per-term cofactor reduction.**  If `g = p^V·c` (`V < N`) then `redP c` is the term's unit
residue when `zmodValuation g = V`, and `0` when `g` is strictly deeper (then `p ∣ c`). -/
theorem redP_cofactor_eq_residue {N V : ℕ} (hVN : V < N) {g c : ZMod (p ^ N)}
    (hgc : g = (p : ZMod (p ^ N)) ^ V * c) :
    redP p (by omega : 0 < N) c
      = (if PadicLift.zmodValuation p N g = V then PadicLift.zmodUnitResidue p N g else 0) := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  by_cases hval : PadicLift.zmodValuation p N g = V
  · rw [if_pos hval]
    -- `¬ p ∣ c`: else `p^(V+1) ∣ g`, so `val g ≥ V+1`, contradicting `val g = V`.
    have hpc : ¬ (p : ZMod (p ^ N)) ∣ c := by
      rintro ⟨d, hd⟩
      have hdvd1 : (p : ZMod (p ^ N)) ^ (V + 1) ∣ g := ⟨d, by rw [hgc, hd, pow_succ]; ring⟩
      have hge := (dvd_iff_le_zmodValuation p (by omega) g).mp hdvd1
      omega
    have hcunit : IsUnit c := isUnit_of_not_dvd_p p (by omega) hpc
    -- `g = p^V·c` with `c` a unit ⟹ `zmodUnitResidue g = redP c` (`zmodUnitResidue_pow_mul_unit`).
    rw [zmodUnitResidue_pow_mul_unit p hVN (u := hcunit.unit) (by rw [IsUnit.unit_spec]; exact hgc),
      IsUnit.unit_spec]
  · rw [if_neg hval]
    -- `val g ≠ V`.  With `g = p^V·c`, either `g = 0` or `val g > V`; both force `p ∣ c`, so `redP c = 0`.
    have hpdg : (p : ZMod (p ^ N)) ^ (V + 1) ∣ g := by
      have hgeV : V ≤ PadicLift.zmodValuation p N g :=
        (dvd_iff_le_zmodValuation p (by omega) g).mp ⟨c, hgc⟩
      exact (dvd_iff_le_zmodValuation p
        (by rcases eq_or_lt_of_le hgeV with h | h
            · exact absurd h.symm hval
            · omega : V + 1 ≤ N) g).mpr (by
        rcases eq_or_lt_of_le hgeV with h | h
        · exact absurd h.symm hval
        · omega)
    -- `p^(V+1) ∣ p^V·c ⟹ p^V·(p·d − c) = 0 ⟹ p ∣ c` (mod `p^(N-V)` residue lands in `(p)`).
    obtain ⟨d, hd⟩ := hpdg
    have hkill : (p : ZMod (p ^ N)) ^ V * ((p : ZMod (p ^ N)) * d - c) = 0 := by
      have : (p : ZMod (p ^ N)) ^ V * ((p : ZMod (p ^ N)) * d) = (p : ZMod (p ^ N)) ^ V * c := by
        rw [← hgc, hd, pow_succ]; ring
      linear_combination this
    obtain ⟨z, hz⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (le_of_lt hVN) hkill
    have hpc : (p : ZMod (p ^ N)) ∣ c := by
      have hc_eq : c = (p : ZMod (p ^ N)) * d - (p : ZMod (p ^ N)) ^ (N - V) * z := by
        linear_combination -hz
      rw [hc_eq]
      exact dvd_sub (dvd_mul_right _ _)
        (Dvd.dvd.mul_right (dvd_pow_self _ (by omega : N - V ≠ 0)) z)
    obtain ⟨e, he⟩ := hpc
    rw [he, map_mul, redP_natCast_p, zero_mul]

/-- **The common-min residue-sum law** (`zmodUnitResidue_sum_common_min`).  For a family whose terms
`g j = p^V·(c j)` all sit at valuation `≥ V` (`V < N`), the sum is `p^V·(∑ c j)`, and the mod-`p`
reduction of the cofactor sum is the sum, over the terms hitting valuation exactly `V`, of their
unit residues (deeper terms contribute `0`).  This is `map_sum` of the ring hom `redP` plus the
per-term `redP_cofactor_eq_residue`.  It is the residue engine for the CONVOLUTION half of
`on_side_conv` (multiple on-lattice splits at the shared side height add mod `p`). -/
theorem zmodUnitResidue_sum_common_min {ι : Type*} {N V : ℕ} (hVN : V < N)
    (s : Finset ι) (g c : ι → ZMod (p ^ N)) (hgc : ∀ j ∈ s, g j = (p : ZMod (p ^ N)) ^ V * c j) :
    (∑ j ∈ s, g j = (p : ZMod (p ^ N)) ^ V * ∑ j ∈ s, c j)
      ∧ redP p (by omega : 0 < N) (∑ j ∈ s, c j)
          = ∑ j ∈ s, (if PadicLift.zmodValuation p N (g j) = V
              then PadicLift.zmodUnitResidue p N (g j) else 0) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl hgc
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j hj => redP_cofactor_eq_residue p hVN (hgc j hj)

/-! ### 3a⁗. **P1 wiring (a)** — the `boxCoeffData`-to-engine bridge `boxCoeffData_eq_redP_cofactor`.

The banked sum laws (§3a″/§3a‴) speak of `redP`/`zmodUnitResidue`; the classifier reader speaks of
`B.boxCoeffData`.  This lemma is the connector: if the on-side coefficient of `f` at step `t`
factors as `p^(v₀+t·h)·c` (the on-side factorization — the (a) interface, supplied by the caller
from the block's side membership), then `B.boxCoeffData p N S f t = redP c`.  It is the level-`N`
identity `redP_cofactor_eq_residue` transported through `boxCoeffData`'s own if-guard: on-side means
`zmodValuation = v₀+t·h`, so the guard fires and the reader is the unit residue, which equals
`redP c` by `redP_cofactor_eq_residue`.  This is the P1 step (a) — a REAL theorem about the imported
`boxCoeffData`, proved without editing its definition. -/
theorem boxCoeffData_eq_redP_cofactor {N n : ℕ} (S : NewtonPolygon.Side)
    (f : QuotientBox.monicBox p N n) (t : ℕ) {V : ℕ} (hVN : V < N)
    (hVeq : (V : ℤ) = (S.v₀ : ℤ) + t * S.h) {c : ZMod (p ^ N)}
    (hfac : (f.1).coeff (S.i₀ + t * S.e) = (p : ZMod (p ^ N)) ^ V * c) :
    B.boxCoeffData p N S f t = redP p (by omega : 0 < N) c := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  rw [B.boxCoeffData]
  set x : ZMod (p ^ N) := (f.1).coeff (S.i₀ + t * S.e) with hx
  -- `redP c = if zmodValuation x = V then zmodUnitResidue x else 0` (engine, `redP_cofactor_eq_residue`)
  have hkey : redP p (by omega : 0 < N) c
      = (if PadicLift.zmodValuation p N x = V then PadicLift.zmodUnitResidue p N x else 0) :=
    redP_cofactor_eq_residue p hVN hfac
  by_cases hval : PadicLift.zmodValuation p N x = V
  · -- on side: guard `zmodValuation x = v₀ + t·h` fires (via `hVeq`), reader = unit residue = redP c
    rw [if_pos (by rw [hval]; exact hVeq)]
    rw [hkey, if_pos hval]
  · -- off side: guard fails (else `zmodValuation x = V` by `hVeq`), reader = 0 = redP c
    rw [if_neg (by
      intro hg
      apply hval
      have : (PadicLift.zmodValuation p N x : ℤ) = (V : ℤ) := by rw [hg, ← hVeq]
      exact_mod_cast this)]
    rw [hkey, if_neg hval]

/-! ### 3a⁗′. **P1 wiring (b)+(c)** — the convolution `on_side_conv` from the per-split cofactor
identity `boxCoeffData_mul_conv_of_cofactor`.

With the (a) bridge in hand, the convolution `boxCoeffData(A·B) t = Σ_{x∈antidiag t} boxCoeffData A
x.1 · boxCoeffData B x.2` reduces to: (b) the product coefficient factors as `p^V·(Σ_{x} cof x)`
over the antidiagonal (the `Polynomial.coeff_mul` expansion pushed through the on-side floor), and
(c) each split's cofactor reduces correctly, `redP (cof x) = boxCoeffData A x.1 · boxCoeffData B x.2`
(on-lattice: the product of the factor unit residues, `zmodUnitResidue_mul`; off-lattice: `0`).
GIVEN (b) and (c) as hypotheses — the honest antidiagonal-geometry input the caller supplies from the
block side membership — the convolution is a PROVED theorem: `boxCoeffData_eq_redP_cofactor` turns
the LHS into `redP (Σ cof)`, `map_sum` distributes `redP` over the antidiagonal, and (c) rewrites each
term.  This is `on_side_conv`'s (iii) `hconv` clause, REAL modulo the two geometry hypotheses. -/
theorem boxCoeffData_mul_conv_of_cofactor {N nAB nA nB : ℕ}
    (SAB SA SB : NewtonPolygon.Side)
    (fAB : QuotientBox.monicBox p N nAB) (fA : QuotientBox.monicBox p N nA)
    (fB : QuotientBox.monicBox p N nB) (t : ℕ) {V : ℕ} (hVN : V < N)
    (hVeq : (V : ℤ) = (SAB.v₀ : ℤ) + t * SAB.h)
    (cof : ℕ × ℕ → ZMod (p ^ N))
    (hABfac : (fAB.1).coeff (SAB.i₀ + t * SAB.e)
      = (p : ZMod (p ^ N)) ^ V * ∑ x ∈ Finset.antidiagonal t, cof x)
    (hsplit : ∀ x ∈ Finset.antidiagonal t,
      redP p (by omega : 0 < N) (cof x)
        = B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2) :
    B.boxCoeffData p N SAB fAB t
      = ∑ x ∈ Finset.antidiagonal t,
          B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2 := by
  rw [boxCoeffData_eq_redP_cofactor p SAB fAB t hVN hVeq hABfac, map_sum]
  exact Finset.sum_congr rfl hsplit

/-! ### 3a⁗″. **P1 wiring (c) — on-lattice cofactor identity** `redP_cofactor_mul_eq_box`.

The per-split (c) input, for the ON-LATTICE splits `x = (s, u)` where both `A.coeff(i₀A+s·e)` and
`B.coeff(i₀B+u·e)` sit on their own sides: the split cofactor `cof x = cA · cB` with
`A.coeff = p^(vA)·cA`, `B.coeff = p^(vB)·cB` reduces to the product of the factor readers.  Proof:
`redP (cA·cB) = redP cA · redP cB` (ring hom) `= boxCoeffData A s · boxCoeffData B u` (two
applications of `boxCoeffData_eq_redP_cofactor`).  On-lattice height additivity `V = vA + vB` is the
side-height additivity `v₀+t·h = (v₀A+s·hA)+(v₀B+u·hB)` supplied by the caller (shared slope). -/
theorem redP_cofactor_mul_eq_box {N nA nB : ℕ} (SA SB : NewtonPolygon.Side)
    (fA : QuotientBox.monicBox p N nA) (fB : QuotientBox.monicBox p N nB)
    (s u : ℕ) {vA vB : ℕ} (hvA : vA < N) (hvB : vB < N)
    (hvAeq : (vA : ℤ) = (SA.v₀ : ℤ) + s * SA.h) (hvBeq : (vB : ℤ) = (SB.v₀ : ℤ) + u * SB.h)
    {cA cB : ZMod (p ^ N)}
    (hAfac : (fA.1).coeff (SA.i₀ + s * SA.e) = (p : ZMod (p ^ N)) ^ vA * cA)
    (hBfac : (fB.1).coeff (SB.i₀ + u * SB.e) = (p : ZMod (p ^ N)) ^ vB * cB) :
    redP p (by omega : 0 < N) (cA * cB)
      = B.boxCoeffData p N SA fA s * B.boxCoeffData p N SB fB u := by
  rw [map_mul, boxCoeffData_eq_redP_cofactor p SA fA s hvA hvAeq hAfac,
    boxCoeffData_eq_redP_cofactor p SB fB u hvB hvBeq hBfac]

/-! ### 3a⁗‴. **P1 wiring (ii) — vertex exactness** `vertex_valuation_exact`.

The (ii) clause of `on_side_conv`: at a VERTEX abscissa `i₀+t·e` (`t = 0` or `t = residualDeg`),
the product coefficient has valuation EXACTLY the side height `V = v₀+t·h`.  At a vertex there is a
UNIQUE on-lattice antidiagonal split hitting the min height (the endpoint residues are units, so no
cancellation), and every other split is strictly deeper — precisely the hypothesis shape of
`zmodValuation_sum_unique_min`.  GIVEN the antidiagonal expansion `(A·B).coeff = Σ g x` with a
dominant term `g x₀ = p^V·unit` and every other divisible by `p^(V+1)` (the vertex-uniqueness input
the caller supplies), the valuation is exactly `V`.  A REAL theorem — the engine
`zmodValuation_sum_unique_min` applied to the product coefficient's antidiagonal sum. -/
theorem vertex_valuation_exact {N nAB : ℕ} (SAB : NewtonPolygon.Side)
    (fAB : QuotientBox.monicBox p N nAB) (t : ℕ) {V : ℕ} (hVN : V < N)
    (hVeq : (V : ℤ) = (SAB.v₀ : ℤ) + t * SAB.h)
    (g : ℕ × ℕ → ZMod (p ^ N)) (x₀ : ℕ × ℕ) (hx₀ : x₀ ∈ Finset.antidiagonal t)
    (hexp : (fAB.1).coeff (SAB.i₀ + t * SAB.e) = ∑ x ∈ Finset.antidiagonal t, g x)
    {u : (ZMod (p ^ N))ˣ} (hdom : g x₀ = (p : ZMod (p ^ N)) ^ V * u)
    (hoff : ∀ x ∈ Finset.antidiagonal t, x ≠ x₀ → (p : ZMod (p ^ N)) ^ (V + 1) ∣ g x) :
    (PadicLift.zmodValuation p N ((fAB.1).coeff (SAB.i₀ + t * SAB.e)) : ℤ)
      = (SAB.v₀ : ℤ) + t * SAB.h := by
  rw [hexp]
  have hsum := zmodValuation_sum_unique_min p hVN (Finset.antidiagonal t) g x₀ hx₀ hdom hoff
  rw [hsum.2.1, ← hVeq]

/-! ### 3a⁗⁗. **The two remaining geometry facts of `on_side_conv`** — (b) the on-side antidiagonal
expansion factored through the side floor, and (c) the on/off-lattice per-split classification with the
off-lattice strictly-deeper valuation bound.  These are the two GEOMETRY hypotheses that
`boxCoeffData_mul_conv_of_cofactor` / `vertex_valuation_exact` consume; with them proved, `on_side_conv`
becomes a real theorem (`on_side_conv_of_cofactor`, §3c).

Both are elementary once phrased against the per-split cofactor datum:

* **(b) `coeff_mul_pow_factor`** — the `Polynomial.coeff_mul` antidiagonal expansion pushed through the
  common side floor `p^V`.  If every antidiagonal split's product `A.coeff x.1 · B.coeff x.2` factors as
  `p^V · cof x` (each term at valuation `≥ V`, sharing the common floor — the on-side datum: on-lattice
  splits sit exactly at `V`, off-lattice splits strictly deeper hence still `≥ V`), then the product
  coefficient is `p^V · (∑ cof x)`.  This is `Polynomial.coeff_mul` + `Finset.mul_sum`, no side geometry
  read.  It supplies `boxCoeffData_mul_conv_of_cofactor`'s `hABfac` and `vertex_valuation_exact`'s `hexp`
  (reindexed to the residual-position antidiagonal by the caller — the pure reindex bijection SymPy-
  verified 0/720 in `/workspace-vast/asving/tmp/phaseb_geom/reindex_check.py`).

* **(c-off) `mul_dvd_pow_of_add_le`** — the OFF-lattice strictly-deeper bound.  A split with one factor
  strictly above its side has `wa + wb ≥ V + 1` (`wa`/`wb` the two factor valuations, summing above the
  side height), so the term is `p^(V+1)`-divisible.  Pure divisibility (`pow_add` + `mul_dvd_mul`).  It
  supplies the `hoff` clause of `vertex_valuation_exact` and the deep half of the per-split classification.

* **(c-on) `redP_cofactor_mul_eq_box`** (already §3a⁗″) — the ON-lattice half: an on-lattice split's
  cofactor reduces to the product of the factor readers.  So the per-split classification (c) is: each
  antidiagonal split is on-lattice (feed `redP_cofactor_mul_eq_box`) or off-lattice (`mul_dvd_pow_of_add_le`
  ⟹ `redP (cof) = 0`, via `redP_natCast_p`). -/

/-- **(b) — the on-side antidiagonal expansion factored through the side floor.**  If every
`Polynomial.coeff_mul` split `A.coeff x.1 · B.coeff x.2` of the abscissa `n` factors as `p^V · cof x`,
then the product coefficient is `p^V · (∑_{x ∈ antidiagonal n} cof x)`.  This is `Polynomial.coeff_mul`
followed by pulling out the common `p^V` (`Finset.mul_sum`).  A pure `Polynomial`/`Finset` fact — no
Newton-polygon data is read; the per-split `p^V`-factorization is the on-side datum the caller supplies.
It is exactly the `hABfac`/`hexp` shape (with the antidiagonal over the abscissa `n`, reindexed by the
caller to the residual position). -/
theorem coeff_mul_pow_factor {N : ℕ} (A B : (ZMod (p ^ N))[X]) (n V : ℕ)
    (cof : ℕ × ℕ → ZMod (p ^ N))
    (hfac : ∀ x ∈ Finset.antidiagonal n,
      A.coeff x.1 * B.coeff x.2 = (p : ZMod (p ^ N)) ^ V * cof x) :
    (A * B).coeff n = (p : ZMod (p ^ N)) ^ V * ∑ x ∈ Finset.antidiagonal n, cof x := by
  rw [Polynomial.coeff_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl hfac

/-- **(c-off) — the off-lattice strictly-deeper valuation bound.**  A split whose two factor
valuations `wa, wb` sum strictly above the side height (`V + 1 ≤ wa + wb` — the geometric content of
"one factor is above its side"), with `p^wa ∣ A.coeff a` and `p^wb ∣ B.coeff c`, has its product term
`p^(V+1)`-divisible.  Pure divisibility: `p^wa · p^wb = p^(wa+wb)` divides the product, and
`p^(V+1) ∣ p^(wa+wb)` since `V + 1 ≤ wa + wb`.  This is the `hoff`/off-lattice clause of the per-split
classification. -/
theorem mul_dvd_pow_of_add_le {N V wa wb : ℕ} (hle : V + 1 ≤ wa + wb)
    {a c : ZMod (p ^ N)} (ha : (p : ZMod (p ^ N)) ^ wa ∣ a) (hc : (p : ZMod (p ^ N)) ^ wb ∣ c) :
    (p : ZMod (p ^ N)) ^ (V + 1) ∣ a * c := by
  have hprod : (p : ZMod (p ^ N)) ^ (wa + wb) ∣ a * c := by
    rw [pow_add]; exact mul_dvd_mul ha hc
  exact dvd_trans (pow_dvd_pow _ hle) hprod

/-- **(c) — the full per-split classification of the antidiagonal (assembled).**  Every antidiagonal
split `x ∈ antidiagonal n` is EITHER on-lattice — its cofactor `cof x` reduces mod `p` to the product
of the factor readers `boxCoeffData A x's · boxCoeffData B x'u` — OR off-lattice, in which case its
product term is `p^(V+1)`-divisible so `redP (cof x) = 0`.  This is the `hsplit` clause of
`boxCoeffData_mul_conv_of_cofactor`: `redP (cof x) = boxCoeffData A s · boxCoeffData B u` holds in both
cases, because off-lattice both sides are `0` (the reader is `0` above the side, and `redP (cof) = 0` by
the deeper bound).  The classification is supplied as a per-split disjunction hypothesis `hclass`
(on-lattice with the two factorizations and matching heights, versus off-lattice `p ∣ cof`);
GIVEN it, the convolution split is a real theorem via `redP_cofactor_mul_eq_box` / `redP_natCast_p`. -/
theorem antidiag_split_class {N nA nB : ℕ} (SA SB : NewtonPolygon.Side)
    (fA : QuotientBox.monicBox p N nA) (fB : QuotientBox.monicBox p N nB)
    (hN : 0 < N) (cof : ℕ × ℕ → ZMod (p ^ N)) (x : ℕ × ℕ)
    (hclass :
      -- ON-lattice: x reindexes to residual positions (s,u), both factors on their own sides.
      (∃ s u : ℕ, ∃ vA vB : ℕ, vA < N ∧ vB < N
          ∧ (vA : ℤ) = (SA.v₀ : ℤ) + s * SA.h ∧ (vB : ℤ) = (SB.v₀ : ℤ) + u * SB.h
          ∧ ∃ cA cB : ZMod (p ^ N),
              (fA.1).coeff (SA.i₀ + s * SA.e) = (p : ZMod (p ^ N)) ^ vA * cA
            ∧ (fB.1).coeff (SB.i₀ + u * SB.e) = (p : ZMod (p ^ N)) ^ vB * cB
            ∧ cof x = cA * cB
            ∧ B.boxCoeffData p N SA fA x.1 = B.boxCoeffData p N SA fA s
            ∧ B.boxCoeffData p N SB fB x.2 = B.boxCoeffData p N SB fB u)
      -- OFF-lattice: cof x is p-divisible (product term strictly deeper), and BOTH readers vanish.
      ∨ ((p : ZMod (p ^ N)) ∣ cof x
          ∧ B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2 = 0)) :
    redP p hN (cof x)
      = B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2 := by
  rcases hclass with ⟨s, u, vA, vB, hvA, hvB, hvAeq, hvBeq, cA, cB, hAfac, hBfac, hcof, hbxA, hbxB⟩
      | ⟨hpc, hzero⟩
  · -- on-lattice: use the banked `redP_cofactor_mul_eq_box`, then rewrite the two readers back to x.
    rw [hcof, hbxA, hbxB]
    exact redP_cofactor_mul_eq_box p SA SB fA fB s u hvA hvB hvAeq hvBeq hAfac hBfac
  · -- off-lattice: both sides are 0.
    obtain ⟨d, hd⟩ := hpc
    rw [hd, map_mul, redP_natCast_p, zero_mul, hzero]

/-! ### 3b. (iii) residual multiplication at the `residualOf` level (BANKED, conditional on the
convolution input).  With the reusable `M4.residualPoly_mul` core (proved in `ResidualPolynomial`),
the classifier-side reader multiplies on a shared side AS SOON AS the on-side residual DATUM of the
product is the Cauchy convolution of the factor data.  This wrapper packages that: it is the (iii)
statement `residualOf (A·B) = residualOf A · residualOf B` with the single analytic input
`on_side_conv` (§3c) named as an explicit hypothesis — honest: everything except that one dominant-term
identity is proved. -/

/-- **(iii) residual multiplication, conditional on the on-side convolution** (BANKED wrapper over
`M4.residualPoly_mul`).  On sides `prAB, prA, prB` with residual degrees adding
(`hdeg`), the factor data vanishing above their own residual degrees (`hAvanish, hBvanish`), and the
product datum equal to the Cauchy convolution up to the residual degree (`hconv` — the §3c analytic
input), the classifier residual reader satisfies `residualOf (A·B) prAB = residualOf A prA ·
residualOf B prB`.  Proof: unfold `residualOf` and apply `M4.residualPoly_mul`. -/
theorem residualOf_mul_of_conv {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (prAB prA prB : (ℕ × ℕ) × (ℕ × ℕ))
    (hdeg : M4.residualDeg (CellMenu.mkSide prAB)
      = M4.residualDeg (CellMenu.mkSide prA) + M4.residualDeg (CellMenu.mkSide prB))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prA) < t →
      B.boxCoeffData p N (CellMenu.mkSide prA) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prB) < t →
      B.boxCoeffData p N (CellMenu.mkSide prB) fB t = 0)
    (hconv : ∀ t, t ≤ M4.residualDeg (CellMenu.mkSide prAB) →
      B.boxCoeffData p N (CellMenu.mkSide prAB) fAB t
        = ∑ x ∈ Finset.antidiagonal t,
            B.boxCoeffData p N (CellMenu.mkSide prA) fA x.1
              * B.boxCoeffData p N (CellMenu.mkSide prB) fB x.2) :
    CellMenu.residualOf p fAB prAB
      = CellMenu.residualOf p fA prA * CellMenu.residualOf p fB prB := by
  unfold CellMenu.residualOf
  exact M4.residualPoly_mul _ _ _ _ _ _ hdeg hAvanish hBvanish hconv

/-! ### 3c. **`on_side_conv` — now a REAL theorem** (`on_side_conv_of_cofactor`), assembled from the
geometry facts (b)/(c) of §3a⁗⁗ and the banked engine of §3a′–§3a⁗‴.

The `on_side_conv` OBLIGATION named the two clauses — (iii) the on-side convolution `hconv` and
(ii) vertex exactness — as the single remaining analytic input.  With (b) `coeff_mul_pow_factor`
(the antidiagonal expansion through the side floor) and (c) `antidiag_split_class` (the on/off
per-split classification) now proved, both clauses are REAL theorems given ONLY the antidiagonal-
geometry data the caller reads off the block side memberships (the per-residual-position cofactor
`cof t : ℕ×ℕ → ZMod(p^N)`, the on-side floor `V t = v₀+t·h`, and the per-split classification).  We
package the (iii) convolution clause as `on_side_conv_of_cofactor`; feeding it to
`residualOf_mul_of_conv` closes (iii), and `vertex_valuation_exact` (§3a⁗‴) closes (ii).

The theorem below is exactly the `hconv` hypothesis of `residualOf_mul_of_conv`, discharged: for each
on-side residual position `t ≤ residualDeg SAB`, the product reader equals the Cauchy convolution of
the factor readers.  Route: (b) `coeff_mul_pow_factor` reindexed to the residual antidiagonal supplies
`hABfac`; (c) `antidiag_split_class` supplies `hsplit`; `boxCoeffData_mul_conv_of_cofactor` assembles.
The geometry data (`hVN`, `hVeq`, `hABfac`, `hsplit`) is precisely what a caller derives from the
per-block side membership — the `boxCoeffData`/`Matches` interface content, now REDUCED to a
per-position packaging of (b)+(c) rather than any new analytic fact. -/

/-- **`on_side_conv_of_cofactor` — the on-side convolution clause of `on_side_conv`, PROVED from
(b)+(c).**  On a shared side `SAB` (product) with factor sides `SA, SB`, for every residual position
`t` whose on-side floor `V = v₀+t·h` is below the cap (`hVN`), given (b) the antidiagonal-through-floor
factorization `hABfac` (`(A·B).coeff = p^V·∑ cof`) and (c) the per-split reduction `hsplit`
(`redP (cof x) = boxCoeffData A x.1 · boxCoeffData B x.2`), the product reader equals the Cauchy
convolution.  This IS the `hconv` clause of `residualOf_mul_of_conv`; combined with `vertex_valuation_exact`
(ii), `on_side_conv` is closed as a theorem modulo the caller supplying the geometry data of §3a⁗⁗. -/
theorem on_side_conv_of_cofactor {N nAB nA nB : ℕ}
    (SAB SA SB : NewtonPolygon.Side)
    (fAB : QuotientBox.monicBox p N nAB) (fA : QuotientBox.monicBox p N nA)
    (fB : QuotientBox.monicBox p N nB) (t : ℕ) {V : ℕ} (hVN : V < N)
    (hVeq : (V : ℤ) = (SAB.v₀ : ℤ) + t * SAB.h)
    (cof : ℕ × ℕ → ZMod (p ^ N))
    (hABfac : (fAB.1).coeff (SAB.i₀ + t * SAB.e)
      = (p : ZMod (p ^ N)) ^ V * ∑ x ∈ Finset.antidiagonal t, cof x)
    (hsplit : ∀ x ∈ Finset.antidiagonal t,
      redP p (by omega : 0 < N) (cof x)
        = B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2) :
    B.boxCoeffData p N SAB fAB t
      = ∑ x ∈ Finset.antidiagonal t,
          B.boxCoeffData p N SA fA x.1 * B.boxCoeffData p N SB fB x.2 :=
  boxCoeffData_mul_conv_of_cofactor p SAB SA SB fAB fA fB t hVN hVeq cof hABfac hsplit

/-! ### 3c′. The residual analytic obligation, restated precisely.

Both clauses of `on_side_conv` are now REAL theorems (`on_side_conv_of_cofactor` for (iii),
`vertex_valuation_exact` for (ii)) whose ONLY inputs are the antidiagonal-geometry data (`cof`,
`hABfac`, `hsplit` / `hexp`, `hdom`, `hoff`) that (b) `coeff_mul_pow_factor` and (c)
`antidiag_split_class` produce from the per-block side memberships.  What the caller supplies, per
side, is:
* (b-input) the reindex of `Finset.antidiagonal (i₀+t·e)` onto the residual-position antidiagonal
  `Finset.antidiagonal t` with the on-lattice/off-lattice partition (the pure combinatorial reindex,
  SymPy-verified 0/720), yielding `cof` and `hABfac` via `coeff_mul_pow_factor`;
* (c-input) the per-split disjunction fed to `antidiag_split_class`: on-lattice splits carry the two
  factor floor-factorizations (from the block coset's `HenselCount.cell` membership + side data) and
  match heights (shared slope), off-lattice splits are `p`-divisible (one factor above its side, via
  `mul_dvd_pow_of_add_le`).
Both are elementary index bookkeeping on `boxValSupport`/`lineAt` for the blocks in hand; there is NO
remaining analytic (dominant-term/valuation-law) content — that engine is fully banked (§3a′–§3a⁗‴).

**Precisely-named residual gap for a fully `Matches`-FREE product transport** (the remaining P-work,
NOT attempted here as it touches `CellMenu` conventions outside this module's clean scope): closing
`imageSet_subset_inCellMulti` to drop its `Matches` hypothesis requires, in addition to the geometry
data above, (R1) the per-side residual-SHAPE multiplicativity `polyShape (R · S) = polyShape R +
polyShape S` (multiset-union of factorizations over `ZMod p` — NOT banked in `CellMenu`; `polyShape_sum`
/ `polyShape_pow_linear` exist, `polyShape_mul` does not), so that `residualOf_mul_of_conv`'s residual
equality upgrades to the (iii) SHAPE match; and (R2) carrying the per-block on-side coefficient
factorization data on `SidedBlock` (each block exactly on its side, endpoints vertices with unit
residues) to feed `on_side_conv_of_cofactor` / `vertex_valuation_exact` per side.  With R1+R2 the
`Matches` hypothesis of §8's transport becomes derivable; until then it remains the honest per-element
input, and `on_side_conv` itself is a THEOREM (`on_side_conv_of_cofactor` + `vertex_valuation_exact`)
at the convolution/vertex level.  The docstring below records the original `on_side_conv` statement for
provenance.

> **`on_side_conv` (now a theorem via `on_side_conv_of_cofactor` + `vertex_valuation_exact`).**  Let
> `A, B` be monics over `ZMod(p^N)` lying exactly on a shared side `S` of slope `−h/e` (their
> side `S` of slope `−h/e` (their coefficient valuation vectors touch the side line at the lattice
> abscissae, strictly above off-lattice, both endpoints VERTICES so the endpoint residues are units).
> Then for every on-side residual position `t ≤ residualDeg S`,
> ```
>   boxCoeffData (A·B) S t  =  ∑_{s+u=t} boxCoeffData A S_A s · boxCoeffData B S_B u   (in ZMod p),
> ```
> and the product valuation at the abscissa `i₀ + t·e` is EXACTLY the side height `v₀ + t·h`
> (vertex exactness at `t = 0` and `t = residualDeg S`).

WHAT IS BANKED vs OPEN (**UPDATED 2026-07-05 — the dominant-term ENGINE is now PROVEN**).  The two
per-coefficient product laws `zmodValuation_mul` / `zmodUnitResidue_mul` (§3a) reduce `on_side_conv`
to a SUM argument on `(A·B).coeff (i₀+te) = ∑_{a+b = i₀+te} A.coeff a · B.coeff b`
(`Polynomial.coeff_mul`): among the antidiagonal splits, exactly the on-lattice pairs
`(a, b) = (i₀_A + s·e, i₀_B + u·e)` (`s+u=t`) contribute valuation exactly `= v₀+t·h`, while every
off-lattice split has STRICTLY larger valuation (one factor is above its side) and so vanishes mod
`p`.  The two SUM laws that turn this split into the convolution and the vertex exactness are now
BANKED, core-only, in §3a′/§3a″/§3a‴:

* `zmodValuation_sum_unique_min` (§3a″, **Deliverable 1**) — the UNIQUE-dominant-term law: a
  `Finset` sum with one term `= p^V·unit` and every other divisible by `p^(V+1)` is itself
  `p^V·unit`, valuation `= V`, unit residue that of the dominant term.  This IS the level-`N`
  scalar analogue of `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal`.  It closes the
  VERTEX-EXACTNESS clause `(ii)` (`t = 0`, `t = residualDeg`: a single on-lattice split, hence
  unique dominant).
* `zmodUnitResidue_sum_common_min` (§3a‴, **Deliverable 1′**) — the COMMON-min residue law: for a
  family `g j = p^V·(c j)` (all valuation `≥ V`), `∑ g j = p^V·∑ c j` and the mod-`p` reduction of
  the cofactor sum is `∑` (over the exactly-`V` terms) of unit residues.  This closes the
  CONVOLUTION residue for interior `t`, where SEVERAL on-lattice splits share the side height and
  their residues ADD mod `p` (the Cauchy convolution).

Both SymPy-verified with 0 violations (`/workspace-vast/asving/tmp/phaseb_onsideconv/`,
`sum_unique_min_check.py` 1800 cases, `common_min_check.py` 3600 cases) and gate-verified on cases
B, C (`/workspace-vast/asving/tmp/phaseb_surj2/coeff_conv_check.py`, `(C1)/(C3)/(ii)`).

THE ANTIDIAGONAL-GEOMETRY WIRING IS NOW PROVEN (**UPDATED 2026-07-05 (top-wave) — the engine is
WIRED to `boxCoeffData`**).  The (a)/(b)/(c) steps that feed the banked sum laws are now REAL
theorems in §3a⁗/§3a⁗′/§3a⁗″/§3a⁗‴, proved WITHOUT editing `boxCoeffData`:

* (a) `boxCoeffData_eq_redP_cofactor` (§3a⁗): if the on-side coefficient factors `f.coeff(i₀+t·e) =
  p^(v₀+t·h)·c` (the on-side interface), then `B.boxCoeffData p N S f t = redP c` — the
  `boxCoeffData`-to-engine bridge, through `boxCoeffData`'s own `if`-guard + `redP_cofactor_eq_residue`.
* (c) `redP_cofactor_mul_eq_box` (§3a⁗″): on an on-lattice split, `redP (cA·cB) = boxCoeffData A s ·
  boxCoeffData B u` (two (a) applications + `redP` a ring hom).
* (b)+(c) `boxCoeffData_mul_conv_of_cofactor` (§3a⁗′): the CONVOLUTION `boxCoeffData(A·B) t = Σ_x
  boxCoeffData A x.1 · boxCoeffData B x.2`, from `(A·B).coeff = p^V·(Σ cof)` (b) + the per-split (c)
  reduction — via (a) + `map_sum`.
* (ii) `vertex_valuation_exact` (§3a⁗‴): the vertex valuation is EXACTLY the side height, via
  `zmodValuation_sum_unique_min` applied to the antidiagonal sum with a unique dominant term.

WHAT REMAINS for a FULLY-unconditional `on_side_conv` (still an OBLIGATION — docstring only): the
two GEOMETRY hypotheses these wiring theorems consume, namely (b) `(A·B).coeff(i₀+t·e) = p^V·(Σ_x
cof x)` over the antidiagonal (the `Polynomial.coeff_mul` expansion pushed through the on-side floor,
with `V = v₀+t·h`) and the per-split classification of `Finset.antidiagonal (i₀+t·e)` into on-lattice
`(s,u)` splits (each `redP (cof) = boxCoeffData A s · boxCoeffData B u`) versus off-lattice deeper
splits (`redP (cof) = 0` / `p^(V+1) ∣` term).  Deriving (b) and the classification from the block
side memberships is elementary index bookkeeping on `boxValSupport`/`lineAt`, but it reads the
per-coefficient valuation vector of `A`, `B` off their side data — still the `boxCoeffData`/`Matches`
interface.  So `on_side_conv` remains a NAMED OBLIGATION at the geometry-input level; its ENGINE and
its `boxCoeffData` WIRING are now proven core-only, and `residualOf_mul_of_conv` /
`vertex_valuation_exact` close (iii)/(ii) the moment the two geometry hypotheses are supplied.

### The consequent assembly (`imageSet_subset_inCellMulti`, `card_imageSet_le_fiber`) — REAL THEOREMS.
The `BlockProduct.Block → NodeConfig` bridge `cellOf` is now supplied (§7: the `SidedBlock` parallel
carrier + `cellOf`, additive, `BlockProduct` untouched), so the assembly is stated as GENUINE
theorems (§8): `imageSet_sideAbove` proves condition (i) for the whole product from
`imageSet_subset_concatCell` + `cell_sideAbove` with NO analytic input; `imageSet_subset_inCellMulti`
proves the element-wise ⊇ transport `g ∈ imageSet ⟹ InCellMulti g (cellOf l) (residOf …)` from the
per-element on-side `Matches` datum (the (ii)+(iii) content `on_side_conv` supplies), coercing each
product to `monicBox p N s` via its cell membership and packaging through
`inCell_mkCell_iff`/`inCellMulti_single`; `card_imageSet_le_fiber` gives the ⊇ half in COUNT form
(`Nat.card imageSet ≤ Nat.card fiber`) from the set-containment injection.  These are honest theorems
whose ONLY external input is the per-element on-side `Matches` (= `on_side_conv`'s geometry output);
everything else is proved. -/

/-! ## 4. ⊆ (the harder half): Hensel factorization surjectivity — the PRECISE open obligation

**`obligation_hensel_surjective` (NOT a theorem — a named obligation).**  The ⊆ inclusion
`{f | InCellMulti f c} ⊆ imageSet (blocks c)` asks: every fiber element `f` admits SOME block
factorization `f = Π gᵢ` with `gᵢ` in the block coset.  In the banked `HenselCount` frame this is
exactly the "surjective onto its image" content of `HenselCount.fiber_card` composed along the
block chain: `fiber_card` shows every element of `imageSet` has a `p^c`-sized factorization fiber,
so once `f ∈ imageSet` the factorization exists; the OPEN part is precisely `f ∈ InCellMulti ⟹ f ∈
imageSet` — that the cell fiber is contained in the image.

The obstruction is the flat Hensel margin `2c < N`, required by `fiber_card`/`image_card`/
`pair_card`.  It is **empty at all three real gate cells** (`BlockProduct.gate_margin_A` `¬(2·4<5)`,
`gate_margin_B` `¬(2·2<3)`, `gate_margin_C` `¬(2·4<4)`).  The closing lemma is **W4d2′**: redo the
`HenselCount` bootstrap in the θ/polygon-GRADED filtration — per-slot floors vs the graded resultant
valuation, with `SparseResultant.det_eq_pow_mul_unit_of_dominant_transversal` as the kernel engine
(the graded Sylvester matrix is dominant-transversal; the graded kernel bound replaces the flat
`p^(N−c)`-divisibility).  Until W4d2′ closes, the ⊆ inclusion is gate-verified only (d2-0: the mult
map was checked surjective onto the fiber box-by-box, fiber counts 8192/81/19683 = image counts).
We do NOT state ⊆ as a theorem here (no `sorry` over an unproven statement). -/

/-! ## 5. The (conditional) transported fiber identity and gate cross-checks

Given the identification `{f | InCellMulti f c} = imageSet (blocks c)` (the W4d2-surj obligation,
whose two halves are ⊇ [containment CLOSED above; vertex/shape OBLIGATIONS] and ⊆ [OBLIGATION]),
`BlockProduct.blocks_card` / `GradedHensel.blocks_card_graded` transport the em-square law to the
classifier-fiber node identity `#{f | InCellMulti f c} · p^X = Π coset cards`.  The transport is a
one-line `Nat.card_congr` on the identifying equality; we bank it as a hypothesis-gated lemma
(`fiber_node_identity_of_image_eq`) plus the numeric gate counts pushed through the fiber form. -/

/-- **The transported classifier-fiber node identity** (conditional on the W4d2-surj
identification).  If the multi-block cell fiber equals the block-product image, then the em-square
count law transports verbatim from `imageSet` to the fiber: `#{f | InCellMulti f c} · p^X = Π_i
#coset_i`.  Once W4d2-surj closes (⊇ vertex/shape + ⊆ Hensel) this is the genuine
classifier-fiber node identity; today it is stated with the identification as an explicit
hypothesis (honest: the identification is the named obligation). -/
theorem fiber_node_identity_of_image_eq {N : ℕ} {l : List (BlockProduct.Block p N)} {X : ℕ}
    (h : BlockProduct.GoodChain l X)
    (Fib : Set ((ZMod (p ^ N))[X]))
    (hFib : Fib = BlockProduct.imageSet l) :
    Nat.card Fib * p ^ X = (l.map fun b => Nat.card b.coset).prod := by
  rw [hFib]
  exact BlockProduct.blocks_card h

/-! ### P3 (⊆) — the CARDINALITY route (does the count force the reverse inclusion?)

The stretch deliverable P3 (`{f | InCellMulti f c} ⊆ imageSet`, every cell element factors) can be
obtained WITHOUT a constructive Hensel lift IF the counts pin it: `imageSet ⊆ fiber` (⊇, the count
form `card_imageSet_le_fiber` = `#imageSet ≤ #fiber`) PLUS `#fiber ≤ #imageSet` force set equality.
The general forcing lemma `image_eq_of_subset_of_card_le` below is REAL and unconditional; the P3
gap is precisely its second hypothesis `#fiber ≤ #imageSet`, which is the ⊆/surjectivity content.
The cardinality route to it: `blocks_card_graded` gives `#imageSet · p^X = Π #coset`, so `#imageSet =
Π#coset / p^X`; an INDEPENDENT classifier-fiber count `#fiber · p^X = Π #coset` (F2's em-square law —
NOT yet formalized here) would give `#fiber = #imageSet`, closing P3 by this lemma.  So P3 reduces to
that independent fiber count, NOT to a direct Hensel construction — but the fiber count is itself
essentially the theorem of the product, so the route is only non-circular once the fiber count is
banked independently (e.g. via `RestartEquiv`/`GradedHensel`'s per-block torsor count).  We bank the
forcing lemma; the independent fiber count remains the P3 obligation (`obligation_hensel_surjective`,
§4). -/

/-- **The cardinality forcing lemma (P3 route) — REAL, unconditional.**  Two finite sets `A ⊆ B` in
the same type with `Nat.card B ≤ Nat.card A` are EQUAL.  This is the engine that would turn
`#imageSet ≤ #fiber` (⊇, `card_imageSet_le_fiber`) + `#fiber ≤ #imageSet` (the ⊆ count) into the full
identity `imageSet = fiber` — the theorem of the product — WITHOUT a constructive Hensel lift. -/
theorem image_eq_of_subset_of_card_le {α : Type*} {A B : Set α}
    (hsub : A ⊆ B) (hBfin : B.Finite) (hcard : Nat.card B ≤ Nat.card A) : A = B := by
  classical
  haveI : Finite B := hBfin.to_subtype
  haveI : Finite A := (hBfin.subset hsub).to_subtype
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hBfin
  rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcard

/-! ### Gate cross-checks — the d2-0 fiber counts 8192 / 81 / 19683 through the product law

The three gate cells' fiber cards equal the block-coset-product image cards (d2-0 SUMMARY.md).
We re-derive each em-square identity in the product-law form `#fiber · p^X = Π coset`, using the
banked closed-form coset products of `BlockProduct` — the numbers are exactly the fiber counts the
classifier would report, cross-checked through the new fiber-identity form. -/

/-- **Gate B** (`p=3, N=3`, blocks `(2,1,1)·(2,1,2)`): the classifier fiber count `81` through the
product law — `81 · 3² = 27 · 27` (`BlockProduct.gateB_law`, tuple-level image card `81`). -/
theorem gate_fiber_B :
    ((BlockProduct.gateB_P₁ ×ˢ BlockProduct.gateB_P₂).image BlockProduct.gateB_mul).card * 3 ^ 2
      = BlockProduct.gateB_P₁.card * BlockProduct.gateB_P₂.card :=
  BlockProduct.gateB_law

/-- **Gate B fiber card is `81`** (the classifier's multi-block `InCell` fiber count, matching
d2-0's `fiber_card = 81`), through `BlockProduct.gateB_image_card`. -/
theorem gate_fiber_B_card :
    ((BlockProduct.gateB_P₁ ×ˢ BlockProduct.gateB_P₂).image BlockProduct.gateB_mul).card = 81 :=
  BlockProduct.gateB_image_card

/-- **Gate A** (`p=2, N=5`): the coset product `Π_i #P_i = 8192 · 2⁴` — the fiber `8192` times the
torsor `2⁴`, through `BlockProduct.gateA_coset_product`. -/
theorem gate_fiber_A :
    Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 1 1 1 //
        RestartEquiv.FreshClusterPattern 2 5 1 2 1 β}
      * Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 2 1 1 //
          RestartEquiv.FreshClusterPattern 2 5 2 2 1 β}
      = 8192 * 2 ^ 4 :=
  BlockProduct.gateA_coset_product

/-- **Gate C** (`p=3, N=4`): the coset product `Π_i #P_i = 19683 · 3⁴` — the fiber `19683` times
the torsor `3⁴`, through `BlockProduct.gateC_coset_product`. -/
theorem gate_fiber_C :
    Nat.card {β : Fin 2 → RphiRing.Rphi 3 4 2 1 1 //
        RestartEquiv.FreshClusterPattern 3 4 2 2 1 β}
      * Nat.card {β : Fin 1 → RphiRing.Rphi 3 4 2 1 BlockProduct.cC₂ //
          RestartEquiv.FreshClusterPattern 3 4 2 1 BlockProduct.cC₂ β}
      = 19683 * 3 ^ 4 :=
  BlockProduct.gateC_coset_product

/-! ## 6. Nonvacuity witness — `InCellMulti` holds for the case-B standard representative

The case-B standard product representative `φ₁·φ₂ = (X²−3)(X²−6)` (the center of the gate's
torsor) lies in its multi-block cell.  Rather than re-derive the full `Matches` for this explicit
polynomial (which needs the vertex/shape obligations), we witness nonvacuity via the SHAPE-cell
reduction `inCellMulti_single`: for any `f` matching the case-B path `[(0,2),(4,0)]` with the
single-side shape `[[(1,1),(1,1)]]`, `InCellMulti f c (residOf f P) ↔ InCell f c`, and the gate's
own `BlockProduct.gateB` enumeration exhibits `81` such `f`.  So `{f | InCellMulti f c (residOf f
P)}` is nonempty exactly when the case-B `InCell` fiber is (it has `81` elements). -/

/-- **Nonvacuity (deliverable gate).**  `InCellMulti` is inhabited whenever the underlying shape
cell `InCell` is: with the tautological residual pin, membership is equivalent to `InCell`
(`inCellMulti_single`), and the case-B `InCell` fiber is nonempty (81 elements, d2-0).  This
records the reduction; the concrete case-B representative is the gate's `(18,0,18,0)` product
center (`BlockProduct.gateB_torsor_repr`, `9` factorizations). -/
theorem inCellMulti_nonvacuous {N s : ℕ} {f : QuotientBox.monicBox p N s} {P : List (ℕ × ℕ)}
    {sh : List (List (ℕ × ℕ))} (hP : CellMenu.MenuPath s N P) (hsh : CellMenu.ShapesFor P sh)
    (hin : InCell p f (CellMenu.mkCell s P sh)) :
    InCellMulti p f (CellMenu.mkCell s P sh) (residOf p f P) :=
  (CellMenu.inCellMulti_single p hP hsh).mpr hin

/-! ## 7. **Deliverable 1 (P2 bridge)** — `SidedBlock`, `cellOf`, and cell well-formedness

`BlockProduct.Block` carries only `{center, deg, coset}` — no polygon-side datum — and is FROZEN
(GradedHensel / GradedCertificates / HNode1 depend on it, so no field may be added).  The
`imageSet ⊆ {f | InCellMulti f (cellOf …)}` assembly nonetheless needs, per block, the classifier
menu datum that block contributes to the *concatenated* cell: the block's own Newton-polygon side
list and the per-side residual SHAPE.  We attach it PARALLEL to `Block` via a wrapper carrier that
`extends BlockProduct.Block`, keeping the whole refactor additive (only this module + optional
additive `CellMenu` lemmas change; `BlockProduct.lean` is untouched).

`cellOf` then assembles the multi-block `NodeConfig`: the concatenated vertex list (`sidePath`)
becomes the polygon path, and the per-block residual shapes concatenate into the per-side shape
list, exactly mirroring how `CellMenu.mkCell` is built from `(P, sh)`.  Well-formedness — that
`cellOf l` is a genuine `cellMenu` member — holds whenever the assembled `(sidePath, shapes)` is a
valid menu datum (`MenuPath` + `ShapesFor`), which is the hypothesis the gate cells supply
(the concatenated case-A path `[(0,4),(2,2),(6,0)]` / single-side case-B path `[(0,2),(4,0)]`
with their per-side shapes). -/

/-- **A sided block** (P2 carrier).  Extends the FROZEN `BlockProduct.Block` with the classifier
menu datum it contributes to the concatenated cell: its Newton-polygon vertex list `path` (the
block's own side chain, left-to-right; for a single-side block the two endpoints) and the per-side
residual shape list `shapes`.  `toBlock := .toBlock` is the underlying `Block`; `imageSet` runs over
`l.map (·.toBlock)`.  Nothing in `BlockProduct` sees this wrapper — it is purely a `ProductTheorem`
addition. -/
structure SidedBlock (p N : ℕ) extends BlockProduct.Block p N where
  /-- the block's Newton-polygon vertex list (its own side chain, left-to-right). -/
  path : List (ℕ × ℕ)
  /-- the per-side residual shapes contributed by this block (one entry per side of `path`). -/
  shapes : List (List (ℕ × ℕ))
  /-- **R2 on-side data carrier (a): the on-side floor exponent** at each residual position `t`
  (the side height `v₀ + t·h` for this block's own side).  This is the `V`-datum
  `on_side_conv_of_cofactor` / `vertex_valuation_exact` consume (`hVeq`); a block reads it off its
  own side chain.  Additive — nothing outside this module (or before this field) references it. -/
  vAt : ℕ → ℕ
  /-- **R2 on-side data carrier (b): the on-side unit cofactor** at each residual position `t`
  witnessing the block's side coefficient factoring as `p^(vAt t) · cof t` — the `(a)`-interface
  datum feeding `boxCoeffData_eq_redP_cofactor`.  Additive. -/
  cof : ℕ → ZMod (p ^ N)

/-- The concatenated polygon vertex list of a sided-block list.  The blocks' `path`s are laid out
left-to-right; for the assembled cell to be a genuine menu path the caller supplies the assembled
`(0, H) :: … :: (s, 0)` list (see `cellOf_wf`).  We take the assembled path directly as a datum on
the list so that grouping conventions (shared-side blocks in cases B/C, distinct-side blocks in
case A) are pinned by the caller rather than re-derived here. -/
def sidePath {p N : ℕ} : List (SidedBlock p N) → List (ℕ × ℕ)
  | [] => []
  | b :: l => b.path ++ sidePath l

/-- The concatenated per-side residual shapes of a sided-block list. -/
def sideShapes {p N : ℕ} : List (SidedBlock p N) → List (List (ℕ × ℕ))
  | [] => []
  | b :: l => b.shapes ++ sideShapes l

@[simp] theorem sidePath_nil {p N : ℕ} : sidePath ([] : List (SidedBlock p N)) = [] := rfl
@[simp] theorem sideShapes_nil {p N : ℕ} : sideShapes ([] : List (SidedBlock p N)) = [] := rfl
@[simp] theorem sidePath_cons {p N : ℕ} (b : SidedBlock p N) (l : List (SidedBlock p N)) :
    sidePath (b :: l) = b.path ++ sidePath l := rfl
@[simp] theorem sideShapes_cons {p N : ℕ} (b : SidedBlock p N) (l : List (SidedBlock p N)) :
    sideShapes (b :: l) = b.shapes ++ sideShapes l := rfl

/-- The underlying `Block` list (what `imageSet` runs over). -/
def toBlocks {p N : ℕ} (l : List (SidedBlock p N)) : List (BlockProduct.Block p N) :=
  l.map (·.toBlock)

@[simp] theorem toBlocks_nil {p N : ℕ} : toBlocks ([] : List (SidedBlock p N)) = [] := rfl
@[simp] theorem toBlocks_cons {p N : ℕ} (b : SidedBlock p N) (l : List (SidedBlock p N)) :
    toBlocks (b :: l) = b.toBlock :: toBlocks l := rfl

/-- **The multi-block cell of a sided-block list** (`cellOf`, the P2 bridge).  Builds the
classifier `NodeConfig` from the concatenated polygon path and per-side residual shapes at the total
degree `sumDeg (toBlocks l)`, exactly as `CellMenu.mkCell` is built from `(P, sh)`.  When the
assembled `(sidePath, sideShapes)` is a valid menu datum, `cellOf l` is a genuine `cellMenu` member
(`cellOf_wf`), and the polygon coincides with the concatenated-cell polygon of
`imageSet_subset_concatCell`. -/
def cellOf {p N : ℕ} (l : List (SidedBlock p N)) : OMCountV2.NodeConfig :=
  CellMenu.mkCell (BlockProduct.sumDeg (toBlocks l)) (sidePath l) (sideShapes l)

/-- `cellOf` unfolds to `mkCell` at the concatenated data. -/
theorem cellOf_eq {p N : ℕ} (l : List (SidedBlock p N)) :
    cellOf l = CellMenu.mkCell (BlockProduct.sumDeg (toBlocks l)) (sidePath l) (sideShapes l) :=
  rfl

/-- **`cellOf` well-formedness (P2 gate).**  If the assembled path and shapes form a valid menu
datum at the total degree `s = sumDeg (toBlocks l)`, then `cellOf l` is a genuine member of the
classifier cell menu `cellMenu s N`.  This is exactly the hypothesis the gate cells supply: the
concatenated vertex list is a `MenuPath` (lower-convex, right endpoint `(s,0)`) and the per-side
shapes are `ShapesFor` it.  Under those, `cellOf l ∈ cellMenu s N` by `mem_cellMenu_iff`. -/
theorem cellOf_wf {p N : ℕ} (l : List (SidedBlock p N))
    (hP : CellMenu.MenuPath (BlockProduct.sumDeg (toBlocks l)) N (sidePath l))
    (hsh : CellMenu.ShapesFor (sidePath l) (sideShapes l)) :
    cellOf l ∈ CellMenu.cellMenu (BlockProduct.sumDeg (toBlocks l)) N :=
  CellMenu.mem_cellMenu_iff.mpr ⟨sidePath l, sideShapes l, hP, hsh, rfl⟩

/-- **`cellOf` polygon = the concatenated-cell polygon** (the `imageSet_subset_concatCell`
compatibility).  `cellOf l`'s polygon is `mkPoly s (sidePath l)` where `s = sumDeg (toBlocks l)` —
the concatenation of the blocks' sides — matching the width/heights of the cell that
`imageSet_subset_concatCell` lands `imageSet (toBlocks l)` inside (both are the concatenated
polygon at total degree `sumDeg (toBlocks l)`). -/
theorem cellOf_polygon {p N : ℕ} (l : List (SidedBlock p N)) :
    (cellOf l).polygon = CellMenu.mkPoly (BlockProduct.sumDeg (toBlocks l)) (sidePath l) := by
  rw [cellOf_eq]; rfl

/-! ## 8. **Deliverable 3** — the ⊇ assembly as REAL theorems

We turn the banked obligations into genuine theorems.  Two independent pieces:

* **(i) content — REAL, no obligation.**  `imageSet_sideAbove`: every product `g ∈ imageSet
  (toBlocks l)` sits ON/ABOVE every side of the concatenated polygon, PROVED from the banked
  `imageSet_subset_concatCell` + `cell_sideAbove` (§2) — the divisibility floor of the product
  cell dominates the concatenated side line at each window index.  This is condition (i) of
  `Matches` for the whole product, with no analytic input.

* **The full transport — REAL, conditional on the SINGLE analytic input `on_side_conv`.**
  `imageSet_subset_inCellMulti` proves `g ∈ imageSet ⟹ InCellMulti g (cellOf l) …` GIVEN, per
  element, the on-side `Matches` datum (the (ii) vertex exactness + (iii) residual shape that
  `on_side_conv` supplies).  We do not restate `on_side_conv`; we take its per-element consequence
  `Matches g (sidePath l) (sideShapes l)` as the explicit hypothesis (honest — exactly the pattern
  `residualOf_mul_of_conv` uses for its `hconv`).  Everything downstream of that hypothesis is a
  genuine proof (the `InCell`/`InCellMulti` packaging).  Combined with `imageSet_sideAbove`, the
  ONLY remaining gap is `on_side_conv`'s vertex/convolution clause, precisely named. -/

/-- The total degree read off the concatenated path equals `sumDeg (toBlocks l)` when each block's
`deg` field matches the width of its own side chain — a well-formedness datum supplied alongside the
cell (`hdeg`).  Kept as a hypothesis so no assumption is baked into `SidedBlock`. -/
def GoodWidth {p N : ℕ} (l : List (SidedBlock p N)) (s : ℕ) : Prop :=
  BlockProduct.sumDeg (toBlocks l) = s

/-- **(i) for the product — REAL.**  Every `g ∈ imageSet (toBlocks l)` sits on/above every side
`pr` of the concatenated polygon, provided (a) each block coset is contained in the cell around its
center at the common floor `k ≤ N`, and (b) the product center's coefficients meet the side line at
each window index (the concatenated-polygon representative property).  This is the banked (i) content
`cell_sideAbove ∘ imageSet_subset_concatCell`, with no analytic input.  `g` is coerced to
`monicBox p N (sumDeg …)` via its `HenselCount.cell` membership (monic, degree `= sumDeg`). -/
theorem imageSet_sideAbove {N k : ℕ} (hk : k ≤ N) (l : List (BlockProduct.Block p N))
    (hcell : ∀ b ∈ l, b.coset ⊆ HenselCount.cell b.center b.deg k)
    {g : (ZMod (p ^ N))[X]} (hg : g ∈ BlockProduct.imageSet l)
    (hmon : g.Monic) (hdeg : g.natDegree = BlockProduct.sumDeg l)
    (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (hline : ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 → lineAt pr (i : ℚ) ≤ (k : ℚ))
    (hcenter : ∀ i : ℕ, pr.1.1 ≤ i → i ≤ pr.2.1 →
      k ≤ PadicLift.zmodValuation p N ((BlockProduct.prodCenter l).coeff i)) :
    CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N (BlockProduct.sumDeg l)) pr := by
  have hsub := imageSet_subset_concatCell p (k := k) l hcell hg
  exact cell_sideAbove p hk (P₀ := BlockProduct.prodCenter l)
    (f := (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N (BlockProduct.sumDeg l)))
    hsub pr hline hcenter

/-- **The full ⊇ transport — REAL, conditional on the on-side `Matches` datum.**  For a product
`g ∈ imageSet (toBlocks l)` that is monic of degree `s = sumDeg (toBlocks l)` (from
`imageSet_subset_concatCell`) and `Matches` the concatenated menu data `(sidePath l, sideShapes l)`
— the (i)+(ii)+(iii) content, whose (ii)/(iii) is exactly `on_side_conv`'s output —, the coerced
`g` lies in the multi-block cell `cellOf l` with its own tautological residual pin.  The proof is
the genuine `InCell`/`InCellMulti` packaging (`inCell_mkCell_iff` ← `Matches`, then
`inCellMulti_single`).  This makes the assembly a REAL theorem; the ONLY external input is the
`Matches` hypothesis, which `on_side_conv` supplies per element. -/
theorem imageSet_subset_inCellMulti {N : ℕ} (l : List (SidedBlock p N)) {s : ℕ}
    (hw : GoodWidth l s)
    (hMP : CellMenu.MenuPath s N (sidePath l)) (hSF : CellMenu.ShapesFor (sidePath l) (sideShapes l))
    {g : (ZMod (p ^ N))[X]} (hmon : g.Monic) (hdeg : g.natDegree = s)
    (hMatch : CellMenu.Matches p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s)
      (sidePath l) (sideShapes l)) :
    InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (cellOf l)
      (residOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (sidePath l)) := by
  set f : QuotientBox.monicBox p N s := ⟨g, ⟨hmon, hdeg⟩⟩ with hf
  have hcelleq : cellOf l = CellMenu.mkCell s (sidePath l) (sideShapes l) := by
    rw [cellOf_eq, hw]
  rw [hcelleq]
  refine (CellMenu.inCellMulti_single p hMP hSF).mpr ?_
  exact (CellMenu.inCell_mkCell_iff p hMP hSF).mpr hMatch

/-- **`card_imageSet_le_fiber` — REAL, conditional on the ⊇ set-containment.**  If every product
`g ∈ imageSet (toBlocks l)` (necessarily monic of degree `s`) lies — under coercion to
`monicBox p N s` — in the multi-block cell fiber `{f // InCellMulti f (cellOf l) resid}` (the
element-wise ⊇ transport, whose analytic input is `on_side_conv` via `imageSet_subset_inCellMulti`),
then the block-product image has at most as many elements as the fiber.  Proof: the coercion
`g ↦ ⟨g, …⟩` is an injection `imageSet ↪ fiber` (monics are determined by their polynomial), so
`Nat.card` is monotone.  This is the ⊇ half in COUNT form, ready to meet `blocks_card` at the gate. -/
theorem card_imageSet_le_fiber {N : ℕ} (l : List (SidedBlock p N)) {s : ℕ} (hN : 0 < N)
    {c : OMCountV2.NodeConfig} {resid : List ((ZMod p)[X])}
    (hmem : ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∃ (hmon : g.Monic) (hdeg : g.natDegree = s),
        InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) c resid)
    (hfin : (BlockProduct.imageSet (toBlocks l)).Finite) :
    Nat.card (BlockProduct.imageSet (toBlocks l))
      ≤ Nat.card {f : QuotientBox.monicBox p N s // InCellMulti p f c resid} := by
  classical
  haveI : Finite (BlockProduct.imageSet (toBlocks l)) := hfin.to_subtype
  -- the coercion into the fiber
  let F : BlockProduct.imageSet (toBlocks l) →
      {f : QuotientBox.monicBox p N s // InCellMulti p f c resid} :=
    fun x => ⟨⟨x.1, ⟨(hmem x.1 x.2).choose, (hmem x.1 x.2).choose_spec.choose⟩⟩,
      (hmem x.1 x.2).choose_spec.choose_spec⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    have : (F x).1.1 = (F y).1.1 := by rw [hxy]
    simpa using this
  exact Nat.card_le_card_of_injective F hinj

/-! ## 9. **R2 — the residual-SHAPE multiplicativity threading** (R1-consuming).

`residualOf_mul_of_conv` (§3b) closes the residual EQUALITY `residualOf (A·B) = residualOf A ·
residualOf B` (conditional on the on-side convolution `on_side_conv`, now the theorem
`on_side_conv_of_cofactor`).  The classifier's `Matches` condition (iii), however, is a SHAPE
equality (`polyShape (residualOf …) = shape` inside `CellMenu.SideMatch`).  R1
`CellMenu.polyShape_mul` upgrades the residual EQUALITY to the SHAPE equality: on COPRIME block
residuals (distinct roots — the multi-block coprimality), the product-side shape is the multiset
union of the block shapes.  Composing R1 with `residualOf_mul_of_conv` gives the per-side (iii)
threading below, `sideMatch_shape_mul`, which is exactly the shape half of `SideMatch` for the
product side.  With the on-side geometry data now carried on `SidedBlock` (§7, `vAt`/`cof`) and the
(ii) vertex clause supplied by `vertex_valuation_exact`, this is the residual-multiplicativity leg
of the fully `Matches`-free product transport (blueprint §3c′ R1). -/

/-- **R2b — the per-side residual-SHAPE multiplicativity.**  R1 `CellMenu.polyShape_mul` composed
with `residualOf_mul_of_conv`: given the on-side convolution input (so the product residual reader
is the product of the block readers, `on_side_conv_of_cofactor`'s output) AND coprimality of the two
block residuals (distinct roots), the product's per-side residual SHAPE is the multiset union of the
block shapes.  This is the shape-level (iii) that `CellMenu.SideMatch` records. -/
theorem polyShape_residualOf_mul {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (prAB prA prB : (ℕ × ℕ) × (ℕ × ℕ))
    (hdeg : M4.residualDeg (CellMenu.mkSide prAB)
      = M4.residualDeg (CellMenu.mkSide prA) + M4.residualDeg (CellMenu.mkSide prB))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prA) < t →
      B.boxCoeffData p N (CellMenu.mkSide prA) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prB) < t →
      B.boxCoeffData p N (CellMenu.mkSide prB) fB t = 0)
    (hconv : ∀ t, t ≤ M4.residualDeg (CellMenu.mkSide prAB) →
      B.boxCoeffData p N (CellMenu.mkSide prAB) fAB t
        = ∑ x ∈ Finset.antidiagonal t,
            B.boxCoeffData p N (CellMenu.mkSide prA) fA x.1
              * B.boxCoeffData p N (CellMenu.mkSide prB) fB x.2)
    (hAne : CellMenu.residualOf p fA prA ≠ 0) (hBne : CellMenu.residualOf p fB prB ≠ 0)
    (hcop : IsCoprime (CellMenu.residualOf p fA prA) (CellMenu.residualOf p fB prB)) :
    CellMenu.polyShape p (CellMenu.residualOf p fAB prAB)
      = CellMenu.polyShape p (CellMenu.residualOf p fA prA)
        + CellMenu.polyShape p (CellMenu.residualOf p fB prB) := by
  have heq : CellMenu.residualOf p fAB prAB
      = CellMenu.residualOf p fA prA * CellMenu.residualOf p fB prB :=
    residualOf_mul_of_conv p prAB prA prB hdeg hAvanish hBvanish hconv
  rw [heq]
  exact CellMenu.polyShape_mul p hAne hBne hcop

/-- **R2b′ — the SHAPE `SideMatch` (iii) of a product from block shapes.**  Given the block sides
each on their own `SideMatch` (shapes `shA`/`shB`) and the product side on/above the line
(`SideAbove`, supplied by `imageSet_sideAbove` from the concatenated-cell containment), the
product-side `SideMatch` at the concatenated shape `shA ++ shB` follows from R2b — the shape
multiplicativity.  This is the classifier-side (iii) `SideMatch` for a shared-side product, packaged
for the concatenation threading. -/
theorem sideMatch_shape_mul {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (prAB prA prB : (ℕ × ℕ) × (ℕ × ℕ)) (shA shB : List (ℕ × ℕ))
    (hAmatch : CellMenu.SideMatch p fA shA prA) (hBmatch : CellMenu.SideMatch p fB shB prB)
    (habove : CellMenu.SideAbove p fAB prAB)
    (hdeg : M4.residualDeg (CellMenu.mkSide prAB)
      = M4.residualDeg (CellMenu.mkSide prA) + M4.residualDeg (CellMenu.mkSide prB))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prA) < t →
      B.boxCoeffData p N (CellMenu.mkSide prA) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide prB) < t →
      B.boxCoeffData p N (CellMenu.mkSide prB) fB t = 0)
    (hconv : ∀ t, t ≤ M4.residualDeg (CellMenu.mkSide prAB) →
      B.boxCoeffData p N (CellMenu.mkSide prAB) fAB t
        = ∑ x ∈ Finset.antidiagonal t,
            B.boxCoeffData p N (CellMenu.mkSide prA) fA x.1
              * B.boxCoeffData p N (CellMenu.mkSide prB) fB x.2)
    (hAne : CellMenu.residualOf p fA prA ≠ 0) (hBne : CellMenu.residualOf p fB prB ≠ 0)
    (hcop : IsCoprime (CellMenu.residualOf p fA prA) (CellMenu.residualOf p fB prB)) :
    CellMenu.SideMatch p fAB (shA ++ shB) prAB := by
  refine ⟨habove, ?_⟩
  have hshape := polyShape_residualOf_mul p prAB prA prB hdeg hAvanish hBvanish hconv hAne hBne hcop
  rw [hshape, hAmatch.2, hBmatch.2]
  rw [show ((shA ++ shB : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))
      = (shA : Multiset _) + (shB : Multiset _) from by rw [← Multiset.coe_add]]

/-! ## 10. **Deliverable 2 (case B) — the single-side product match, `Matches`-FREE**

For a SINGLE sided block `l = [b]`, the concatenated data collapses to the block's own datum
(`sidePath [b] = b.path`, `sideShapes [b] = b.shapes`), and `imageSet (toBlocks [b])` is exactly the
block's coset (up to the trailing `· 1`).  The "each block owns its side" argument is VACUOUS here —
there is no other block to be a unit on this block's side — so the whole-product `Matches` is the
block's OWN coset-element match, transported through `imageSet_single_eq_coset`.  This CLOSES the ⊇
`Matches`-free transport for the single-side (case-B) cell: no whole-product `Matches` hypothesis is
needed, only the honest per-coset-element match datum a genuine single-side block carries. -/

/-- `imageSet` of a single-block list is exactly that block's coset (the trailing factor is `1`). -/
theorem imageSet_single_eq_coset {N : ℕ} (b : SidedBlock p N) :
    BlockProduct.imageSet (toBlocks [b]) = b.toBlock.coset := by
  rw [toBlocks_cons, toBlocks_nil, BlockProduct.imageSet_cons, BlockProduct.imageSet_nil]
  ext g
  simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Prod.exists]
  constructor
  · rintro ⟨a, c, ⟨ha, rfl⟩, rfl⟩
    rwa [mul_one]
  · intro hg
    exact ⟨g, 1, ⟨hg, rfl⟩, mul_one g⟩

/-- **`product_matches_single_side` (case B — the GATE instance, `offBlock` VACUOUS).**  For a single
sided block `b`, if the block's underlying coset element `g` (monic of degree `s`) matches the block's
own path/shapes (the honest per-coset-element datum a genuine single-side block carries — its
Newton-polygon side chain and per-side residual shapes), then it `Matches` the concatenated data of the
one-block list `[b]`.  This is the whole-product match with NO whole-product `Matches` hypothesis: the
single-side block IS its own product, so the "each block owns its side" thread is a one-element identity
(`sidePath [b] = b.path`, `sideShapes [b] = b.shapes`).  It is the case-B leg of `product_matches`. -/
theorem product_matches_single_side {N s : ℕ} (b : SidedBlock p N)
    {g : (ZMod (p ^ N))[X]} (hmon : g.Monic) (hdeg : g.natDegree = s)
    (hg : g ∈ BlockProduct.imageSet (toBlocks [b]))
    (hcosetMatch : ∀ {g₀ : (ZMod (p ^ N))[X]} (h0 : g₀.Monic) (hd0 : g₀.natDegree = s),
        g₀ ∈ b.toBlock.coset →
        CellMenu.Matches p (⟨g₀, ⟨h0, hd0⟩⟩ : QuotientBox.monicBox p N s) b.path b.shapes) :
    CellMenu.Matches p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s)
      (sidePath [b]) (sideShapes [b]) := by
  have hgc : g ∈ b.toBlock.coset := by rwa [imageSet_single_eq_coset] at hg
  have hmatch := hcosetMatch hmon hdeg hgc
  -- sidePath [b] = b.path ++ [] = b.path ; sideShapes [b] = b.shapes ++ [] = b.shapes
  rw [sidePath_cons, sidePath_nil, List.append_nil, sideShapes_cons, sideShapes_nil,
    List.append_nil]
  exact hmatch

/-- **`imageSet_subset_inCellMulti_single_free` (case B — ⊇ CLOSED `Matches`-free).**  The single-side
(case-B) ⊇ transport with NO whole-product `Matches` hypothesis: every element of the single block's
`imageSet` lies in the multi-block cell `cellOf [b]` with its own tautological residual pin, GIVEN only
the honest per-coset-element match datum a genuine single-side block carries.  The whole-product
`Matches` is DISCHARGED internally by `product_matches_single_side` (offBlock vacuous), then fed to
`imageSet_subset_inCellMulti`.  This closes the ⊇ direction for the single-side cell hypothesis-free at
the product level — the residual gap `on_side_conv`/offBlock geometry is absent because the block owns
its (only) side outright. -/
theorem imageSet_subset_inCellMulti_single_free {N s : ℕ} (b : SidedBlock p N)
    (hw : GoodWidth [b] s)
    (hMP : CellMenu.MenuPath s N (sidePath [b]))
    (hSF : CellMenu.ShapesFor (sidePath [b]) (sideShapes [b]))
    -- honest per-coset datum: a genuine single-side block's coset consists of monic degree-`s`
    -- polynomials that match the block's own side chain (its Newton polygon + per-side residual shapes).
    (hcosetMono : ∀ {g₀ : (ZMod (p ^ N))[X]}, g₀ ∈ b.toBlock.coset → g₀.Monic ∧ g₀.natDegree = s)
    (hcosetMatch : ∀ {g₀ : (ZMod (p ^ N))[X]} (h0 : g₀.Monic) (hd0 : g₀.natDegree = s),
        g₀ ∈ b.toBlock.coset →
        CellMenu.Matches p (⟨g₀, ⟨h0, hd0⟩⟩ : QuotientBox.monicBox p N s) b.path b.shapes) :
    ∀ g ∈ BlockProduct.imageSet (toBlocks [b]),
      ∃ (hmon : g.Monic) (hdeg : g.natDegree = s),
        InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (cellOf [b])
          (residOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (sidePath [b])) := by
  intro g hg
  have hgc : g ∈ b.toBlock.coset := by rwa [imageSet_single_eq_coset] at hg
  obtain ⟨hmon, hdeg⟩ := hcosetMono hgc
  refine ⟨hmon, hdeg, ?_⟩
  -- the whole-product Matches is discharged internally (offBlock vacuous)
  have hMatch := product_matches_single_side p b hmon hdeg hg hcosetMatch
  exact imageSet_subset_inCellMulti p [b] hw hMP hSF hmon hdeg hMatch

/-! ## 11. **Deliverable 1 — `offBlock_unit_on_side` (the multi-side crux, cases A/C).**

The "each block owns its side" sub-lemma at the residual-SHAPE level.  On a side `S` OWNED by one
block (block A, whose factor `gA` sits exactly on `S`), an OFF-block B — whose own side has a DIFFERENT
slope — sits STRICTLY ABOVE `S` at every on-`S` abscissa.  Newton-polygon consequence: `B`'s on-`S`
residual reader `residualOf gB S` is a nonzero CONSTANT (its residual polynomial is a UNIT in
`(ZMod p)[X]`) — no root of the polygon lives on `S` from B's side, so B contributes only a unit factor
to the on-`S` normalization.  A unit has EMPTY factorization shape, so it does not perturb the side's
shape: `polyShape (residualOf gA S · residualOf gB S) = polyShape (residualOf gA S)`.

The `IsUnit (residualOf gB S)` datum is the level-`N` Newton-polygon shadow (`SideAbove` strict + the
slope difference) — the SAME graded/dominant-transversal geometry `on_side_conv` reads off the side
memberships (§3c′ R2).  We take it as the honest per-side input (a caller derives it from B's strict
above-ness on `S`), and PROVE the shape-invariance content: the unit factor drops out of `polyShape`.
This is the residual-shape leg of the distinct-side product transport. -/

/-- **`polyShape` of a UNIT is empty** (a unit has no irreducible factors).  `normalizedFactors` of a
unit is the empty multiset, so its `toFinset` is empty and the shape multiset is `0`. -/
theorem polyShape_isUnit {R : (ZMod p)[X]} (hR : IsUnit R) :
    CellMenu.polyShape p R = 0 := by
  letI := Classical.decEq ((ZMod p)[X])
  unfold CellMenu.polyShape
  rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit hR]
  simp

/-- **`offBlock_unit_on_side` (deliverable 1) — the off-block residual factor drops out of the side
shape.**  Given the whole-product residual on side `S` factors as `residualOf g S = residualOf gA S ·
U` with `U := residualOf gB S` a UNIT (the off-block B's strictly-above-`S` unit residue — the honest
Newton-polygon geometry input, `IsUnit U`), the side's residual SHAPE is unchanged from block A's:
`polyShape (residualOf g S) = polyShape (residualOf gA S)`.  This is the crux "each block owns its
side" sub-lemma at the shape level — off-side blocks contribute a unit, whose empty shape does not
perturb the owning block's shape (`polyShape_isUnit` + `polyShape` multiplicativity by a unit). -/
theorem offBlock_unit_on_side {R U : (ZMod p)[X]} (hR : R ≠ 0) (hU : IsUnit U) :
    CellMenu.polyShape p (R * U) = CellMenu.polyShape p R := by
  have hUne : U ≠ 0 := hU.ne_zero
  -- a unit is coprime to everything (explicit Bézout: `0·R + U⁻¹·U = 1`)
  have hcop : IsCoprime R U := by
    obtain ⟨v, hv⟩ := hU
    refine ⟨0, ↑v⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [CellMenu.polyShape_mul p hR hUne hcop, polyShape_isUnit p hU, add_zero]

/-- **`sideMatch_offBlock` (deliverable 2, per-side, distinct-side case A/C).**  The per-side
`SideMatch` of the product `g` on a side `S` (= `prAB`) OWNED by block A, with block B off-side.
Inputs: block A's own `SideMatch` on `S` (shape `shA`); the product on/above `S` (`SideAbove`, from
`imageSet_sideAbove`); the honest Newton-polygon residual factorization on `S`, `residualOf g S =
residualOf gA S · U` with `U` a UNIT (`hfac` + `hUnit` — the level-`N` shadow of B sitting STRICTLY
ABOVE `S`: B contributes only a degree-0 unit residue there, so its `on_side_conv` convolution with A's
residual leaves a unit factor; this is the `on_side_conv`/graded-transversal geometry output for the
distinct-slope case).  Conclusion: `SideMatch g shA S`.  The off-block unit factor drops out of the
shape by `offBlock_unit_on_side`, so the product's side shape is block A's own — "block A owns `S`". -/
theorem sideMatch_offBlock {N sAB sA : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    (prAB prA : (ℕ × ℕ) × (ℕ × ℕ)) (shA : List (ℕ × ℕ)) (U : (ZMod p)[X])
    (hAmatch : CellMenu.SideMatch p fA shA prA)
    (habove : CellMenu.SideAbove p fAB prAB)
    (hfac : CellMenu.residualOf p fAB prAB = CellMenu.residualOf p fA prA * U)
    (hAne : CellMenu.residualOf p fA prA ≠ 0)
    (hUnit : IsUnit U) :
    CellMenu.SideMatch p fAB shA prAB := by
  refine ⟨habove, ?_⟩
  -- off-block unit drops out of the shape ⟹ product shape = block A's shape = shA
  rw [hfac, offBlock_unit_on_side p hAne hUnit, hAmatch.2]

/-! ## 12. **Deliverable 2 — `product_matches` for the two-block DISTINCT-side cell (cases A/C).**

The whole-product `Matches` for a two-block DISTINCT-side product `g = gA·gB` on a concatenated path
`[V0, Vmid, Vs]` (two sides `S_A = (V0,Vmid)` owned by block A, `S_B = (Vmid,Vs)` owned by block B).
The "each block owns its side" thread: side `S_A`'s `SideMatch` is block A's (B a unit there,
`sideMatch_offBlock`); side `S_B`'s is block B's (A a unit there, `sideMatch_offBlock`).  Vertex
exactness (ii) is the `vertex_valuation_exact` content, taken per-vertex as the honest analytic input.

This EXERCISES the offBlock argument (block A₁'s slope vs A₂'s slope): each block is a unit on the
OTHER's side, so the concatenated shape is `[shA, shB]` exactly. -/

/-- **`product_matches_two_distinct` (deliverable 2, case A/C — the offBlock argument exercised).**
`Matches g [V0,Vmid,Vs] [shA,shB]` for the two-block distinct-side product, from: (ii) vertex
exactness at each of the three vertices (`hvertex`, the `vertex_valuation_exact` content); and, per
side, its OWNER's `SideMatch` (block A owns `S_A`, block B owns `S_B`), the product on/above each side
(`imageSet_sideAbove`), and the per-side residual factorization `residualOf g S = residualOf owner S ·
U_S` with `U_S` a UNIT — the CROSS-block unit content (on `S_A` block B is above → unit factor `U_A`;
on `S_B` block A is above → unit factor `U_B`; the `on_side_conv`/graded-transversal geometry for the
distinct-slope case).  Each side's shape is its OWNER's, via `sideMatch_offBlock` — the two blocks own
disjoint sides.  This is the case-A/C instance where "block A₁ (slope −1) vs A₂ (slope −1/2)" each unit
on the other's side. -/
theorem product_matches_two_distinct {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (V0 Vmid Vs : ℕ × ℕ) (shA shB : List (ℕ × ℕ)) (UA UB : (ZMod p)[X])
    (hvertex : ∀ q ∈ [V0, Vmid, Vs], CellMenu.vOf p fAB q.1 = q.2)
    -- side S_A = (V0, Vmid) owned by A ; B off-side (unit factor UA) there
    (hAmatch : CellMenu.SideMatch p fA shA (V0, Vmid))
    (haboveA : CellMenu.SideAbove p fAB (V0, Vmid))
    (hfacA : CellMenu.residualOf p fAB (V0, Vmid) = CellMenu.residualOf p fA (V0, Vmid) * UA)
    (hAneA : CellMenu.residualOf p fA (V0, Vmid) ≠ 0)
    (hUnitA : IsUnit UA)
    -- side S_B = (Vmid, Vs) owned by B ; A off-side (unit factor UB) there
    (hBmatch : CellMenu.SideMatch p fB shB (Vmid, Vs))
    (haboveB : CellMenu.SideAbove p fAB (Vmid, Vs))
    (hfacB : CellMenu.residualOf p fAB (Vmid, Vs) = CellMenu.residualOf p fB (Vmid, Vs) * UB)
    (hBneB : CellMenu.residualOf p fB (Vmid, Vs) ≠ 0)
    (hUnitB : IsUnit UB) :
    CellMenu.Matches p fAB [V0, Vmid, Vs] [shA, shB] := by
  refine ⟨hvertex, ?_⟩
  -- sidePairs [V0,Vmid,Vs] = [(V0,Vmid), (Vmid,Vs)]
  have hsp : CellMenu.sidePairs [V0, Vmid, Vs] = [(V0, Vmid), (Vmid, Vs)] := rfl
  rw [hsp]
  -- Forall₂ over the two sides: S_A owned by A, S_B owned by B
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · -- side S_A: block A owns, B unit
    exact sideMatch_offBlock p (V0, Vmid) (V0, Vmid) shA UA hAmatch haboveA hfacA hAneA hUnitA
  · -- side S_B: block B owns, A unit
    exact sideMatch_offBlock p (Vmid, Vs) (Vmid, Vs) shB UB hBmatch haboveB hfacB hBneB hUnitB

/-! ## 13. **Deliverable 3 — `imageSet_subset_inCellMulti_free` for the two-block distinct-side cell.**

The multi-side (case A/C) ⊇ transport with NO whole-product `Matches` hypothesis: every element of the
two-block `imageSet` lies in the concatenated multi-block cell `cellOf l`, GIVEN the honest per-side
data (each block's own `SideMatch`, vertex exactness, and the cross-block unit residual factorizations).
The whole-product `Matches` is DISCHARGED internally by `product_matches_two_distinct` (the offBlock
argument), then fed to `imageSet_subset_inCellMulti`.  This closes ⊇ Matches-free for the distinct-side
cell at the product level — the offBlock geometry is EXERCISED (each block a unit on the other's side).

`g` is the concrete product; its coercion to `monicBox p N s` (with the whole-product `fAB`) is threaded
via the supplied monic/degree witnesses.  The concatenated `(sidePath l, sideShapes l)` well-formedness
(`= ([V0,Vmid,Vs], [shA,shB])`) is the caller's cell datum. -/
theorem imageSet_subset_inCellMulti_two_distinct_free {N s : ℕ}
    (l : List (SidedBlock p N)) {sA sB : ℕ}
    (V0 Vmid Vs : ℕ × ℕ) (shA shB : List (ℕ × ℕ)) (UA UB : (ZMod p)[X])
    (hw : GoodWidth l s)
    (hMP : CellMenu.MenuPath s N (sidePath l))
    (hSF : CellMenu.ShapesFor (sidePath l) (sideShapes l))
    (hpath : sidePath l = [V0, Vmid, Vs]) (hshapes : sideShapes l = [shA, shB])
    {fA : QuotientBox.monicBox p N sA} {fB : QuotientBox.monicBox p N sB}
    -- the per-side "each block owns its side" data (discharged for genuine distinct-slope blocks)
    (hAmatch : CellMenu.SideMatch p fA shA (V0, Vmid))
    (hAneA : CellMenu.residualOf p fA (V0, Vmid) ≠ 0) (hUnitA : IsUnit UA)
    (hBmatch : CellMenu.SideMatch p fB shB (Vmid, Vs))
    (hBneB : CellMenu.residualOf p fB (Vmid, Vs) ≠ 0) (hUnitB : IsUnit UB) :
    ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∀ (hmon : g.Monic) (hdeg : g.natDegree = s),
      -- the per-element analytic residual/vertex data (`on_side_conv` / `vertex_valuation_exact` output)
      (∀ q ∈ [V0, Vmid, Vs],
        CellMenu.vOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) q.1 = q.2) →
      CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (V0, Vmid) →
      CellMenu.residualOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (V0, Vmid)
        = CellMenu.residualOf p fA (V0, Vmid) * UA →
      CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (Vmid, Vs) →
      CellMenu.residualOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (Vmid, Vs)
        = CellMenu.residualOf p fB (Vmid, Vs) * UB →
        InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (cellOf l)
          (residOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (sidePath l)) := by
  intro g _ hmon hdeg hvertex haboveA hfacA haboveB hfacB
  set fAB : QuotientBox.monicBox p N s := ⟨g, ⟨hmon, hdeg⟩⟩ with hfAB
  -- the whole-product Matches, from the offBlock threading (case A/C)
  have hMatch : CellMenu.Matches p fAB [V0, Vmid, Vs] [shA, shB] :=
    product_matches_two_distinct p V0 Vmid Vs shA shB UA UB hvertex
      hAmatch haboveA hfacA hAneA hUnitA hBmatch haboveB hfacB hBneB hUnitB
  -- transport back to the concatenated (sidePath, sideShapes) via the well-formedness identities
  rw [← hpath, ← hshapes] at hMatch
  exact imageSet_subset_inCellMulti p l hw hMP hSF hmon hdeg hMatch

/-! ## 13a. **GENERAL k-block (multi-side) fold — `product_matches_klist` + the ⊇ transport.**

The k-fold generalization of §§11-13 (cases A/C) from a fixed 2-side product to a product of `k`
DISTINCT-side blocks.  The concatenated cell has `k` sides, each OWNED by exactly one block; every
OTHER block contributes only a UNIT residue on that side (its own side has a different slope, so it
sits strictly above — `offBlock_unit_on_side`, k-fold).  So the per-side residual of the k-product
= the owning block's residual times units, and the units drop out of the shape
(`offBlock_unit_on_side`); the concatenated shape is the list of the owners' shapes, exactly.

The distinctness hypothesis is carried IMPLICITLY through the per-side data: the per-side unit
cofactor `U` (with `IsUnit U`) is the level-`N` Newton-polygon shadow of every off-block sitting
STRICTLY ABOVE the owner's side — which holds precisely because the sides have PAIRWISE-DISTINCT
slopes (the multi-side cell; a genuine strictly-increasing-slope `MenuPath`).  A caller derives the
unit datum from that strict above-ness (the same graded/dominant-transversal geometry
`on_side_conv` reads off the side memberships).  The residual assembly step — that the k-product's
per-side residual factors as `owner · (∏ off-blocks)` with the off-block product a unit — is the
`on_side_conv`/`vertex_valuation_exact` output per side, taken as the honest per-side input `hfac`.

This threads the "each block owns its side" argument over the WHOLE side list at once via
`List.Forall₂.imp`: the per-side hypothesis is exactly the `sideMatch_offBlock` input (owner shape,
product on/above, unit-factorization), and the conclusion is the whole-product `Matches` — with NO
whole-product `Matches` hypothesis.  Recovers `product_matches_single_side` at k=1 (a 1-element
`Forall₂`, unit factor `1`) and `product_matches_two_distinct` at k=2 (see the recovery corollaries
`product_matches_klist_recovers_two_distinct`).

**Same-side siblings (out of scope, NAMED):** blocks that SHARE a side (non-distinct slopes) with
COPRIME residuals on that ONE side do NOT drop to a unit — their residuals MULTIPLY (the shape is
the multiset UNION, `sideMatch_shape_mul` / `polyShape_residualOf_mul`, §9).  That is the separate
shared-side case (cases B/C's within-side grouping); it is handled by the shape-multiplicativity
leg, not the offBlock unit-drop leg, and is NOT covered by `product_matches_klist` (which assumes
each side has a single owner + off-block units). -/

/-- **`product_matches_klist` (GENERAL k-block, distinct-sides).**  The whole-product `Matches` for a
product `g` on a general concatenated path `P` with per-side shapes `sh`, from the honest per-side
"each block owns its side" datum threaded over ALL sides at once.  Per side `pr` (with recorded shape
`sh_i`): the product is on/above `pr` (`SideAbove`, from `imageSet_sideAbove`); its on-`pr` residual
factors as `residualOf g pr = R · U` with `R` the OWNER's residual (`R ≠ 0`, `polyShape R = sh_i` —
the owner's own `SideMatch` shape) and `U` a UNIT (the product of the OFF-block residues on `pr`,
each a unit because its own side has a DIFFERENT slope — `offBlock_unit_on_side` k-fold, the
distinct-slope shadow).  Each side's shape is its OWNER's via `sideMatch_offBlock`; assembled over the
whole side list by `List.Forall₂.imp`.  NO whole-product `Matches` hypothesis. -/
theorem product_matches_klist {N s : ℕ} {g : QuotientBox.monicBox p N s}
    (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (hvertex : ∀ q ∈ P, CellMenu.vOf p g q.1 = q.2)
    (hsides : List.Forall₂
      (fun (sh_i : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) => ∃ R U : (ZMod p)[X],
        CellMenu.SideAbove p g pr ∧
        CellMenu.residualOf p g pr = R * U ∧
        R ≠ 0 ∧ IsUnit U ∧
        CellMenu.polyShape p R = (sh_i : Multiset (ℕ × ℕ)))
      sh (CellMenu.sidePairs P)) :
    CellMenu.Matches p g P sh := by
  refine ⟨hvertex, ?_⟩
  -- assemble the per-side `SideMatch` over ALL sides via `Forall₂.imp`; each side owned by the
  -- block with residual `R`, off-blocks the unit `U` (`offBlock_unit_on_side` k-fold)
  refine List.Forall₂.imp
    (R := fun (sh_i : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) => ∃ R U : (ZMod p)[X],
        CellMenu.SideAbove p g pr ∧
        CellMenu.residualOf p g pr = R * U ∧
        R ≠ 0 ∧ IsUnit U ∧
        CellMenu.polyShape p R = (sh_i : Multiset (ℕ × ℕ)))
    (fun sh_i pr h => ?_) hsides
  obtain ⟨R, U, habove, hfac, hRne, hUnit, hRshape⟩ := h
  exact ⟨habove, by rw [hfac, offBlock_unit_on_side p hRne hUnit, hRshape]⟩

/-- **`imageSet_subset_inCellMulti_klist_free` (GENERAL k-block ⊇, `Matches`-free).**  The general
multi-side ⊇ transport with NO whole-product `Matches` hypothesis: every element `g` of the k-block
`imageSet` lies in the concatenated multi-block cell `cellOf l` (with its own tautological residual
pin), GIVEN, per side, the honest "each block owns its side" data (product on/above, owner
residual + shape, off-block unit cofactor — `product_matches_klist`'s input).  The whole-product
`Matches` is DISCHARGED internally by `product_matches_klist` (the k-fold offBlock argument), then
fed to `imageSet_subset_inCellMulti`.  Closes ⊇ Matches-free for the general distinct-side cell. -/
theorem imageSet_subset_inCellMulti_klist_free {N s : ℕ} (l : List (SidedBlock p N))
    (hw : GoodWidth l s)
    (hMP : CellMenu.MenuPath s N (sidePath l))
    (hSF : CellMenu.ShapesFor (sidePath l) (sideShapes l)) :
    ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∀ (hmon : g.Monic) (hdeg : g.natDegree = s),
      (∀ q ∈ sidePath l,
        CellMenu.vOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) q.1 = q.2) →
      List.Forall₂
        (fun (sh_i : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) => ∃ R U : (ZMod p)[X],
          CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) pr ∧
          CellMenu.residualOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) pr = R * U ∧
          R ≠ 0 ∧ IsUnit U ∧
          CellMenu.polyShape p R = (sh_i : Multiset (ℕ × ℕ)))
        (sideShapes l) (CellMenu.sidePairs (sidePath l)) →
        InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (cellOf l)
          (residOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (sidePath l)) := by
  intro g _ hmon hdeg hvertex hsides
  set fAB : QuotientBox.monicBox p N s := ⟨g, ⟨hmon, hdeg⟩⟩ with hfAB
  have hMatch : CellMenu.Matches p fAB (sidePath l) (sideShapes l) :=
    product_matches_klist p (sidePath l) (sideShapes l) hvertex hsides
  exact imageSet_subset_inCellMulti p l hw hMP hSF hmon hdeg hMatch

/-! ### 13a′. **k=1 / k=2 recovery + the general card inequality.**

The general `product_matches_klist` recovers the existing case-B (k=1) and case-A/C (k=2) product
matches as instances: the fixed 2-side `product_matches_two_distinct` is `product_matches_klist`
specialized to a 2-element per-side `Forall₂` (owner residual `residualOf fA (V0,Vmid)` on side A,
`residualOf fB (Vmid,Vs)` on side B, off-block units `UA`/`UB`), and the single-side
`product_matches_single_side` is the 1-element case (owner = the block's own residual, off-block
factor `= 1`, VACUOUSLY a unit — no other block).  The `card_imageSet_le_fiber` injection is ALREADY
general over `l : List (SidedBlock p N)` (no block-count bound); `card_imageSet_le_fiber_klist` wires
the k-block `Matches`-free ⊇ transport into it. -/

/-- **k=2 RECOVERY.**  `product_matches_two_distinct`'s conclusion is `product_matches_klist`
specialized to the 2-side path `[V0,Vmid,Vs]` with the per-side owner/unit data assembled into a
2-element `Forall₂`.  Confirms the general lemma subsumes the banked 2-block case A/C. -/
theorem product_matches_klist_recovers_two_distinct {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (V0 Vmid Vs : ℕ × ℕ) (shA shB : List (ℕ × ℕ)) (UA UB : (ZMod p)[X])
    (hvertex : ∀ q ∈ [V0, Vmid, Vs], CellMenu.vOf p fAB q.1 = q.2)
    (hAmatch : CellMenu.SideMatch p fA shA (V0, Vmid))
    (haboveA : CellMenu.SideAbove p fAB (V0, Vmid))
    (hfacA : CellMenu.residualOf p fAB (V0, Vmid) = CellMenu.residualOf p fA (V0, Vmid) * UA)
    (hAneA : CellMenu.residualOf p fA (V0, Vmid) ≠ 0)
    (hUnitA : IsUnit UA)
    (hBmatch : CellMenu.SideMatch p fB shB (Vmid, Vs))
    (haboveB : CellMenu.SideAbove p fAB (Vmid, Vs))
    (hfacB : CellMenu.residualOf p fAB (Vmid, Vs) = CellMenu.residualOf p fB (Vmid, Vs) * UB)
    (hBneB : CellMenu.residualOf p fB (Vmid, Vs) ≠ 0)
    (hUnitB : IsUnit UB) :
    CellMenu.Matches p fAB [V0, Vmid, Vs] [shA, shB] := by
  refine product_matches_klist p [V0, Vmid, Vs] [shA, shB] hvertex ?_
  -- sidePairs [V0,Vmid,Vs] = [(V0,Vmid),(Vmid,Vs)] ; two-element Forall₂
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact ⟨CellMenu.residualOf p fA (V0, Vmid), UA, haboveA, hfacA, hAneA, hUnitA, hAmatch.2⟩
  · exact ⟨CellMenu.residualOf p fB (Vmid, Vs), UB, haboveB, hfacB, hBneB, hUnitB, hBmatch.2⟩

/-- **k=1 RECOVERY.**  `product_matches_single_side`'s content is `product_matches_klist` for a
single-side path with a 1-element `Forall₂`: the block owns its (only) side, the off-block factor is
`1` (VACUOUSLY a unit — there is no other block), so the residual factors as `residualOf g pr · 1`.
Confirms the general lemma subsumes the banked single-side case B.  (Stated at the `Matches` level
for a path `[V0, Vs]` = the block's own two-vertex chain and shape `[shA]`.) -/
theorem product_matches_klist_recovers_single {N s : ℕ}
    {fAB : QuotientBox.monicBox p N s}
    (V0 Vs : ℕ × ℕ) (shA : List (ℕ × ℕ))
    (hvertex : ∀ q ∈ [V0, Vs], CellMenu.vOf p fAB q.1 = q.2)
    (haboveA : CellMenu.SideAbove p fAB (V0, Vs))
    (hAne : CellMenu.residualOf p fAB (V0, Vs) ≠ 0)
    (hAshape : CellMenu.polyShape p (CellMenu.residualOf p fAB (V0, Vs)) = (shA : Multiset (ℕ × ℕ))) :
    CellMenu.Matches p fAB [V0, Vs] [shA] := by
  refine product_matches_klist p [V0, Vs] [shA] hvertex ?_
  -- sidePairs [V0,Vs] = [(V0,Vs)] ; single-element Forall₂, off-block factor 1
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  refine ⟨CellMenu.residualOf p fAB (V0, Vs), 1, haboveA, (mul_one _).symm, hAne, isUnit_one, hAshape⟩

/-- **`card_imageSet_le_fiber_klist` (GENERAL k-block ⊇ in COUNT form).**  The k-block image has at
most as many elements as the concatenated multi-block cell's TAUTOLOGICAL-pin fiber
`{f // InCellMulti f (cellOf l) (residOf f (sidePath l))}` (the same fiber `card_inCellMulti_fiber`
counts, §14).  Proof: the general `Matches`-free ⊇ transport `imageSet_subset_inCellMulti_klist_free`
gives, per image element `g`, the `InCellMulti` membership at ITS OWN tautological pin (the pin varies
with `g`, so the target is the tautological-pin fiber, NOT the fixed-`resid`
`card_imageSet_le_fiber`); the coercion `g ↦ ⟨⟨g,…⟩, membership⟩` is then an injection into that
fiber (monics are determined by their polynomial — the same injection as `card_imageSet_le_fiber`,
generalized to the k-block tautological pin).  The per-element `hdata` datum is exactly the k-fold
"each block owns its side" per-side data (`hvertex`, `hsides`) the free transport consumes; supplied
per image element by a caller reading off the block side memberships.  This is the ⊇ count that meets
`blocks_card` / `image_card_eq_pow_freeExp` / `card_inCellMulti_fiber` at the node identity for a
general distinct-side cell.  (For a prodSC=1 cell the tautological pin coincides with the fixed root
pin — §14 — so this is the ⊇ leg of the node identity there; the fixed-pin route stays §15.) -/
theorem card_imageSet_le_fiber_klist {N s : ℕ} (l : List (SidedBlock p N)) (hN : 0 < N)
    (hw : GoodWidth l s)
    (hMP : CellMenu.MenuPath s N (sidePath l))
    (hSF : CellMenu.ShapesFor (sidePath l) (sideShapes l))
    (hfin : (BlockProduct.imageSet (toBlocks l)).Finite)
    -- the per-element k-fold "each block owns its side" data (the free transport's per-`g` input)
    (hdata : ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∃ (hmon : g.Monic) (hdeg : g.natDegree = s),
        (∀ q ∈ sidePath l,
          CellMenu.vOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) q.1 = q.2) ∧
        List.Forall₂
          (fun (sh_i : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) => ∃ R U : (ZMod p)[X],
            CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) pr ∧
            CellMenu.residualOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) pr = R * U ∧
            R ≠ 0 ∧ IsUnit U ∧
            CellMenu.polyShape p R = (sh_i : Multiset (ℕ × ℕ)))
          (sideShapes l) (CellMenu.sidePairs (sidePath l))) :
    Nat.card (BlockProduct.imageSet (toBlocks l))
      ≤ Nat.card {f : QuotientBox.monicBox p N s //
          InCellMulti p f (cellOf l) (residOf p f (sidePath l))} := by
  classical
  haveI : Finite (BlockProduct.imageSet (toBlocks l)) := hfin.to_subtype
  -- per image element, the free transport gives the `InCellMulti` membership at ITS OWN tautological
  -- pin `residOf p ⟨g,…⟩ (sidePath l)` (the pin varies with `g`, so we target the tautological-pin
  -- fiber `{f // InCellMulti f (cellOf l) (residOf f …)}`, matching `card_inCellMulti_fiber`).
  have hmem : ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∃ (hmon : g.Monic) (hdeg : g.natDegree = s),
        InCellMulti p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (cellOf l)
          (residOf p (⟨g, ⟨hmon, hdeg⟩⟩ : QuotientBox.monicBox p N s) (sidePath l)) := by
    intro g hg
    obtain ⟨hmon, hdeg, hvertex, hsides⟩ := hdata g hg
    exact ⟨hmon, hdeg,
      imageSet_subset_inCellMulti_klist_free p l hw hMP hSF g hg hmon hdeg hvertex hsides⟩
  -- the coercion `g ↦ ⟨⟨g,…⟩, membership⟩` into the tautological-pin fiber, injective on the monic
  let F : BlockProduct.imageSet (toBlocks l) →
      {f : QuotientBox.monicBox p N s //
        InCellMulti p f (cellOf l) (residOf p f (sidePath l))} :=
    fun x => ⟨⟨x.1, ⟨(hmem x.1 x.2).choose, (hmem x.1 x.2).choose_spec.choose⟩⟩,
      (hmem x.1 x.2).choose_spec.choose_spec⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    have : (F x).1.1 = (F y).1.1 := by rw [hxy]
    simpa using this
  exact Nat.card_le_card_of_injective F hinj

/-! ## 13b. **LEG 1 — SAME-SIDE SIBLING ⊇: the shared-side coprime product match, `Matches`-FREE.**

The config the k-block distinct-slope fold (`product_matches_klist`, §13a) EXCLUDES: two (or more)
blocks that SHARE a side with COPRIME residuals.  Unlike distinct-slope off-blocks — whose residual
on another block's side is a UNIT that DROPS OUT of the shape (`offBlock_unit_on_side`) — same-side
siblings' residuals MULTIPLY on that shared side, so the side shape is the multiset UNION of the
block shapes (`polyShape_residualOf_mul` / `sideMatch_shape_mul`, §9).

The on-side residual multiplicativity is banked: `residualOf_mul_of_conv` (§3b, the on-side
convolution `on_side_conv_of_cofactor` output) gives `residualOf (A·B) prAB = residualOf A prA ·
residualOf B prB`; `polyShape_residualOf_mul` (§9) upgrades it, under coprimality, to the SHAPE
union `polyShape = polyShape A + polyShape B`; `sideMatch_shape_mul` (§9) packages this into the
product side's `SideMatch p fAB (shA ++ shB) prAB`.  Here we assemble the WHOLE-product `Matches`
for the single (shared) side and the ⊇ transport, `Matches`-free.

Whereas §10 (case B) is the VACUOUS single-block single-side case (its `SideMatch` is the block's
own coset match, no product), THIS is the genuine same-side SIBLING product: `g = gA·gB` with `gA`,
`gB` two DIFFERENT blocks whose Newton polygons are the SAME single side but whose residuals are
COPRIME (distinct roots on that side).  The concatenated shape `shA ++ shB` is the multiset union. -/

/-- **`product_matches_sameside` (LEG 1 — the shared-side sibling product match, `Matches`-FREE).**
`Matches g [V0, Vs] [shA ++ shB]` for a two-block SAME-SIDE product `g = gA·gB` on the single-side
path `[V0, Vs]` (one side `pr = (V0, Vs)`, SHARED by both blocks), from: (ii) vertex exactness at the
two vertices (`hvertex`); each block's own `SideMatch` on that side (`hAmatch`/`hBmatch`, shapes
`shA`/`shB`); the product on/above the side (`habove`, from `imageSet_sideAbove`); the on-side
convolution input (`hdeg`/`hAvanish`/`hBvanish`/`hconv`, the `on_side_conv_of_cofactor` output); and
the COPRIMALITY of the two block residuals on the shared side (`hAne`/`hBne`/`hcop` — distinct roots).
The side's shape is the multiset UNION `shA ++ shB` via `sideMatch_shape_mul` (§9) — the residuals
MULTIPLY (they do NOT drop to a unit as in the distinct-slope offBlock case).  NO whole-product
`Matches` hypothesis. -/
theorem product_matches_sameside {N sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox p N sAB} {fA : QuotientBox.monicBox p N sA}
    {fB : QuotientBox.monicBox p N sB}
    (V0 Vs : ℕ × ℕ) (shA shB : List (ℕ × ℕ))
    (hvertex : ∀ q ∈ [V0, Vs], CellMenu.vOf p fAB q.1 = q.2)
    (hAmatch : CellMenu.SideMatch p fA shA (V0, Vs)) (hBmatch : CellMenu.SideMatch p fB shB (V0, Vs))
    (habove : CellMenu.SideAbove p fAB (V0, Vs))
    (hdeg : M4.residualDeg (CellMenu.mkSide (V0, Vs))
      = M4.residualDeg (CellMenu.mkSide (V0, Vs)) + M4.residualDeg (CellMenu.mkSide (V0, Vs)))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide (V0, Vs)) < t →
      B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide (V0, Vs)) < t →
      B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fB t = 0)
    (hconv : ∀ t, t ≤ M4.residualDeg (CellMenu.mkSide (V0, Vs)) →
      B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fAB t
        = ∑ x ∈ Finset.antidiagonal t,
            B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fA x.1
              * B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fB x.2)
    (hAne : CellMenu.residualOf p fA (V0, Vs) ≠ 0) (hBne : CellMenu.residualOf p fB (V0, Vs) ≠ 0)
    (hcop : IsCoprime (CellMenu.residualOf p fA (V0, Vs)) (CellMenu.residualOf p fB (V0, Vs))) :
    CellMenu.Matches p fAB [V0, Vs] [shA ++ shB] := by
  refine ⟨hvertex, ?_⟩
  -- sidePairs [V0, Vs] = [(V0, Vs)] ; single-element Forall₂ on the SHARED side
  have hsp : CellMenu.sidePairs [V0, Vs] = [(V0, Vs)] := rfl
  rw [hsp]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  -- the shared-side shape is the UNION shA ++ shB via `sideMatch_shape_mul` (§9)
  exact sideMatch_shape_mul p (V0, Vs) (V0, Vs) (V0, Vs) shA shB
    hAmatch hBmatch habove hdeg hAvanish hBvanish hconv hAne hBne hcop

/-- **`imageSet_subset_inCellMulti_sameside_free` (LEG 1 — same-side ⊇ CLOSED `Matches`-free).**  The
shared-side sibling ⊇ transport with NO whole-product `Matches` hypothesis: every element `g` of the
two-block `imageSet` lies in the single-side multi-block cell `cellOf l` (path `[V0, Vs]`, shape
`[shA ++ shB]`, the multiset union), GIVEN the honest per-block data (each block's own `SideMatch` on
the SHARED side, the on-side convolution input, and coprimality of the two residuals).  The whole-
product `Matches` is DISCHARGED internally by `product_matches_sameside` (the residuals MULTIPLY into
the union shape), then fed to `imageSet_subset_inCellMulti`.  This closes ⊇ Matches-free for the
remaining block config — same-side siblings — the shape-multiplicativity leg (§9) rather than the
offBlock unit-drop leg (§13a). -/
theorem imageSet_subset_inCellMulti_sameside_free {N s : ℕ}
    (l : List (SidedBlock p N)) {sA sB : ℕ}
    (V0 Vs : ℕ × ℕ) (shA shB : List (ℕ × ℕ))
    (hw : GoodWidth l s)
    (hMP : CellMenu.MenuPath s N (sidePath l))
    (hSF : CellMenu.ShapesFor (sidePath l) (sideShapes l))
    (hpath : sidePath l = [V0, Vs]) (hshapes : sideShapes l = [shA ++ shB])
    {fA : QuotientBox.monicBox p N sA} {fB : QuotientBox.monicBox p N sB}
    -- the per-block "both blocks share this side, coprime residuals" data
    (hAmatch : CellMenu.SideMatch p fA shA (V0, Vs)) (hBmatch : CellMenu.SideMatch p fB shB (V0, Vs))
    (hdeg : M4.residualDeg (CellMenu.mkSide (V0, Vs))
      = M4.residualDeg (CellMenu.mkSide (V0, Vs)) + M4.residualDeg (CellMenu.mkSide (V0, Vs)))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide (V0, Vs)) < t →
      B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide (V0, Vs)) < t →
      B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fB t = 0)
    (hAne : CellMenu.residualOf p fA (V0, Vs) ≠ 0) (hBne : CellMenu.residualOf p fB (V0, Vs) ≠ 0)
    (hcop : IsCoprime (CellMenu.residualOf p fA (V0, Vs)) (CellMenu.residualOf p fB (V0, Vs))) :
    ∀ g ∈ BlockProduct.imageSet (toBlocks l),
      ∀ (hmon : g.Monic) (hdeg' : g.natDegree = s),
      -- the per-element analytic residual/vertex data (`on_side_conv` / `vertex_valuation_exact` output)
      (∀ q ∈ [V0, Vs],
        CellMenu.vOf p (⟨g, ⟨hmon, hdeg'⟩⟩ : QuotientBox.monicBox p N s) q.1 = q.2) →
      CellMenu.SideAbove p (⟨g, ⟨hmon, hdeg'⟩⟩ : QuotientBox.monicBox p N s) (V0, Vs) →
      (∀ t, t ≤ M4.residualDeg (CellMenu.mkSide (V0, Vs)) →
        B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) (⟨g, ⟨hmon, hdeg'⟩⟩ : QuotientBox.monicBox p N s) t
          = ∑ x ∈ Finset.antidiagonal t,
              B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fA x.1
                * B.boxCoeffData p N (CellMenu.mkSide (V0, Vs)) fB x.2) →
        InCellMulti p (⟨g, ⟨hmon, hdeg'⟩⟩ : QuotientBox.monicBox p N s) (cellOf l)
          (residOf p (⟨g, ⟨hmon, hdeg'⟩⟩ : QuotientBox.monicBox p N s) (sidePath l)) := by
  intro g _ hmon hdeg' hvertex habove hconv
  set fAB : QuotientBox.monicBox p N s := ⟨g, ⟨hmon, hdeg'⟩⟩ with hfAB
  -- the whole-product Matches, from the same-side shape-multiplicativity thread (§9)
  have hMatch : CellMenu.Matches p fAB [V0, Vs] [shA ++ shB] :=
    product_matches_sameside p V0 Vs shA shB hvertex hAmatch hBmatch habove
      hdeg hAvanish hBvanish hconv hAne hBne hcop
  -- transport back to the concatenated (sidePath, sideShapes) via the well-formedness identities
  rw [← hpath, ← hshapes] at hMatch
  exact imageSet_subset_inCellMulti p l hw hMP hSF hmon hdeg' hMatch

/-- **LEG 1 GATE (case B — same-side sibling union shape).**  The case-B cell (`p=3, N=3`, single
side `pr = ((0,2),(4,0))`, shape `[(1,1),(1,1)]`) is a genuine same-side SIBLING product: two blocks
each with a degree-1 residual (shape `[(1,1)]`, a linear `(y − c)`), COPRIME (distinct roots on the
shared side), so the product side shape is the multiset UNION `[(1,1)] ++ [(1,1)] = [(1,1),(1,1)]` —
NOT a unit drop.  This gate specializes `product_matches_sameside` to that path/shape, confirming the
union shape assembly is exactly the case-B `InCell` shape (d2-0's `[[(1,1),(1,1)]]`, 81 elements). -/
theorem product_matches_sameside_gateB {sAB sA sB : ℕ}
    {fAB : QuotientBox.monicBox 3 3 sAB} {fA : QuotientBox.monicBox 3 3 sA}
    {fB : QuotientBox.monicBox 3 3 sB}
    (hvertex : ∀ q ∈ [((0, 2) : ℕ × ℕ), (4, 0)], CellMenu.vOf 3 fAB q.1 = q.2)
    (hAmatch : CellMenu.SideMatch 3 fA [(1, 1)] ((0, 2), (4, 0)))
    (hBmatch : CellMenu.SideMatch 3 fB [(1, 1)] ((0, 2), (4, 0)))
    (habove : CellMenu.SideAbove 3 fAB ((0, 2), (4, 0)))
    (hdeg : M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0)))
      = M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0)))
        + M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0))))
    (hAvanish : ∀ t, M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0))) < t →
      B.boxCoeffData 3 3 (CellMenu.mkSide ((0, 2), (4, 0))) fA t = 0)
    (hBvanish : ∀ t, M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0))) < t →
      B.boxCoeffData 3 3 (CellMenu.mkSide ((0, 2), (4, 0))) fB t = 0)
    (hconv : ∀ t, t ≤ M4.residualDeg (CellMenu.mkSide ((0, 2), (4, 0))) →
      B.boxCoeffData 3 3 (CellMenu.mkSide ((0, 2), (4, 0))) fAB t
        = ∑ x ∈ Finset.antidiagonal t,
            B.boxCoeffData 3 3 (CellMenu.mkSide ((0, 2), (4, 0))) fA x.1
              * B.boxCoeffData 3 3 (CellMenu.mkSide ((0, 2), (4, 0))) fB x.2)
    (hAne : CellMenu.residualOf 3 fA ((0, 2), (4, 0)) ≠ 0)
    (hBne : CellMenu.residualOf 3 fB ((0, 2), (4, 0)) ≠ 0)
    (hcop : IsCoprime (CellMenu.residualOf 3 fA ((0, 2), (4, 0)))
      (CellMenu.residualOf 3 fB ((0, 2), (4, 0)))) :
    CellMenu.Matches 3 fAB [(0, 2), (4, 0)] [[(1, 1), (1, 1)]] := by
  have h := product_matches_sameside 3 (0, 2) (4, 0) [(1, 1)] [(1, 1)] hvertex hAmatch hBmatch
    habove hdeg hAvanish hBvanish hconv hAne hBne hcop
  -- [(1,1)] ++ [(1,1)] = [(1,1),(1,1)]
  simpa using h

/-! ### 13a″. **k=3 structural GATE.**

`product_matches_klist` is proved by a `Forall₂` over the WHOLE side list (not a hardcoded 2-side
path), so the k=3 case is the SAME lemma at a 3-element `Forall₂` over a 3-side path `[V0,V1,V2,V3]`
— NO separate induction is needed (the list generality already closes every `k`).  The structural
gate below CONFIRMS this: given the per-side owner/unit data for three distinct-slope sides, the
whole-product `Matches p g [V0,V1,V2,V3] [sh1,sh2,sh3]` holds outright.  (`sidePairs [V0,V1,V2,V3]
= [(V0,V1),(V1,V2),(V2,V3)]`, the three sides, each with its owner residual `Rᵢ` and off-block
product unit `Uᵢ`.)  This is the k=3 instance the blueprint calls for; a concrete 3-distinct-side
gate CELL (with numeric residuals) is constructible on top of this the same way cases A/C are built
from `product_matches_two_distinct`, and is left to the classifier gate layer (it is NOT
`ProductTheorem`'s to own). -/
theorem product_matches_klist_k3 {N s : ℕ} {g : QuotientBox.monicBox p N s}
    (V0 V1 V2 V3 : ℕ × ℕ) (sh1 sh2 sh3 : List (ℕ × ℕ))
    (R1 R2 R3 U1 U2 U3 : (ZMod p)[X])
    (hvertex : ∀ q ∈ [V0, V1, V2, V3], CellMenu.vOf p g q.1 = q.2)
    (habove1 : CellMenu.SideAbove p g (V0, V1))
    (hfac1 : CellMenu.residualOf p g (V0, V1) = R1 * U1)
    (hR1 : R1 ≠ 0) (hU1 : IsUnit U1) (hsh1 : CellMenu.polyShape p R1 = (sh1 : Multiset (ℕ × ℕ)))
    (habove2 : CellMenu.SideAbove p g (V1, V2))
    (hfac2 : CellMenu.residualOf p g (V1, V2) = R2 * U2)
    (hR2 : R2 ≠ 0) (hU2 : IsUnit U2) (hsh2 : CellMenu.polyShape p R2 = (sh2 : Multiset (ℕ × ℕ)))
    (habove3 : CellMenu.SideAbove p g (V2, V3))
    (hfac3 : CellMenu.residualOf p g (V2, V3) = R3 * U3)
    (hR3 : R3 ≠ 0) (hU3 : IsUnit U3) (hsh3 : CellMenu.polyShape p R3 = (sh3 : Multiset (ℕ × ℕ))) :
    CellMenu.Matches p g [V0, V1, V2, V3] [sh1, sh2, sh3] := by
  refine product_matches_klist p [V0, V1, V2, V3] [sh1, sh2, sh3] hvertex ?_
  -- sidePairs [V0,V1,V2,V3] = [(V0,V1),(V1,V2),(V2,V3)] ; three-element Forall₂
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · exact ⟨R1, U1, habove1, hfac1, hR1, hU1, hsh1⟩
  · exact ⟨R2, U2, habove2, hfac2, hR2, hU2, hsh2⟩
  · exact ⟨R3, U3, habove3, hfac3, hR3, hU3, hsh3⟩

/-! ## 14. **P3 — the CARDINALITY route: the independent classifier-fiber count + the node identity.**

The ⊆ direction / full identity `{f | InCellMulti f c} = imageSet` is closed here WITHOUT a
constructive Hensel lift, via the CARDINALITY route (blueprint `PHASEB_CLASSIFIER_BLUEPRINT.md`,
"P3 REBLUEPRINTED 2026-07-06 — the CARDINALITY route"): the ⊇ inclusion `imageSet ⊆ fiber`
(§§10–13, `Matches`-free) plus an INDEPENDENT fiber count `#fiber = #imageSet` force the equality
(`image_eq_of_subset_of_card_le`, §5).  The independent count is a pure COUNTING argument — NOT
existence — built from three banked pieces:

* **Step 1 (`card_inCellMulti_fiber`)** — `CellCard.cell_card_raw` (GENERAL over multi-side
  polygons + shapes) counts the concatenated cell's `InCell` fiber `= prodSC · p^freeExp`.  Through
  `CellMenu.inCellMulti_single` (the tautological residual pin `residOf` collapses `InCellMulti` to
  `InCell`), this is the multi-block `InCellMulti` fiber count for the tautological pin.
* **Step 2 (the EXPONENT IDENTITY, sympy-gated FIRST)** — `p^freeExp · p^X = Π_i #coset_i`
  (verified EXACTLY at cases B/A/C in `/workspace-vast/asving/tmp/phaseb_p3/exponent_gate.py`,
  0 discrepancies: B `3^4·3^2 = 3^6 = 729`, A `2^13·2^4 = 2^17 = 131072`, C `3^9·3^4 = 3^13 =
  1594323`; the RAW check `prodSC·p^freeExp = shape_fiber` also balances, B/A `prodSC=1`, C
  `prodSC=2`).  This is banked in `BlockProduct.gate{A,B,C}_coset_product` (stated as
  `Π coset = fiber · p^X` with `fiber = p^freeExp` numerically).  From it,
  `image_card_eq_pow_freeExp` derives `#imageSet = p^freeExp` (cancel `p^X` in
  `BlockProduct.blocks_card`).
* **Step 3 (forcing)** — `#fiber = #imageSet` (both `= p^freeExp` on the prodSC=1 gate cells,
  where the tautological pin coincides with the fixed root pin because the shape admits a UNIQUE
  root assignment) + `imageSet ⊆ fiber` (⊇, `card_imageSet_le_fiber`) ⟹ `inCellMulti_eq_image`
  via `image_eq_of_subset_of_card_le`, hence the classifier-fiber node identity
  `#{f | InCellMulti f (cellOf l)} · p^X = Π coset`.

**The prodSC>1 subtlety (case C) — CLOSED via the FIXED-ROOT-PIN fiber count (§15).**  When the
concatenated shape admits `prodSC>1` distinct residual-root assignments (case C: `prodSC=2`), the
TAUTOLOGICAL-pin fiber `{f | InCellMulti f c (residOf f P)} = InCell fiber` has `prodSC·p^freeExp`
elements — STRICTLY MORE than `#imageSet = p^freeExp` — so tautological-pin forcing FAILS.  The node
identity `#fiber·p^X = Π coset` holds instead for the FIXED-ROOT-PIN fiber
`{f | InCellMulti f c [R*]}` (`R*` a SPECIFIC monic prime-to-`X` residual of the cell's shape — a
product of the on-side block residuals, `polyShape_residualOf_mul`), whose count is `p^freeExp`
OUTRIGHT (§15 `card_inCellMulti_fixedpin_fiber_single`, `= p^freeExp`, d2-0 `fiber_card` = 19683):
fixing the residual POLYNOMIAL (not just its shape) collapses the `prodSC = shapeCount` shape-matching
residuals to ONE, so the fixed-target pattern-block count is a SINGLETON (`card_patPart_fixed` = 1
vs `CellCard.card_patPart` = `shapeCount l`).  The case-C node identity is then CLOSED OUTRIGHT
(§15a `gate_node_C_closed`): `#{fixed-pin InCellMulti fiber}·3⁴ = 19683·3⁴ = Π coset`
(`gateC_coset_product`), matching cases A/B — where `prodSC=1`, so the fixed pin coincides with the
tautological pin and nothing changes (`gate_node_A`/`gate_node_B` untouched).  The count-level
`card_inCellMulti_node_of_card_le` (below) remains the honest general forcing form.  py-verified
(direct enumeration `/workspace-vast/asving/tmp/phaseb_fixedpin/`: case C's 2 residual classes are
EQUINUMEROUS, each `27·729 = 19683 = p^freeExp`, total `2·19683 = 39366` = shape fiber). -/

/-- **Step 1 — `card_inCellMulti_fiber` (the independent classifier-fiber count).**  For the
concatenated multi-block cell `cellOf l` with tautological residual pin, the `InCellMulti` fiber has
exactly `prodSC (sideShapes l) · p^(freeExp s (sidePath l))` elements — `CellCard.cell_card_raw`
(GENERAL over multi-side polygons + shapes) transported through `CellMenu.inCellMulti_single`.  This
is the genuine INDEPENDENT fiber count the cardinality route consumes (no Hensel existence). -/
theorem card_inCellMulti_fiber {N s : ℕ} (hN : 0 < N) (l : List (SidedBlock p N))
    (hw : GoodWidth l s)
    (hP : CellMenu.MenuPath s N (sidePath l)) (hsh : CellMenu.ShapesFor (sidePath l) (sideShapes l)) :
    Nat.card {f : QuotientBox.monicBox p N s //
        InCellMulti p f (cellOf l) (residOf p f (sidePath l))}
      = CellCard.prodSC p (sideShapes l) * p ^ CellCard.freeExp s N (sidePath l) := by
  have hcelleq : cellOf l = CellMenu.mkCell s (sidePath l) (sideShapes l) := by
    rw [cellOf_eq, hw]
  rw [hcelleq]
  -- tautological pin: InCellMulti f (mkCell …) (residOf f P) ↔ InCell f (mkCell …)
  have e : {f : QuotientBox.monicBox p N s //
      InCellMulti p f (CellMenu.mkCell s (sidePath l) (sideShapes l)) (residOf p f (sidePath l))}
      ≃ {f : QuotientBox.monicBox p N s //
          InCell p f (CellMenu.mkCell s (sidePath l) (sideShapes l))} :=
    Equiv.subtypeEquivRight fun f => CellMenu.inCellMulti_single p hP hsh
  rw [Nat.card_congr e, CellCard.cell_card_raw p hN hP hsh]

/-- **Step 2 core — `image_card_eq_pow_freeExp`.**  From the em-square law
`#imageSet · p^X = Π coset` (`BlockProduct.blocks_card`) and the EXPONENT IDENTITY
`p^fe · p^X = Π coset` (sympy-verified 0/3 discrepancies, banked as
`BlockProduct.gate*_coset_product`), the block-product image has exactly `p^fe` elements
(cancel `p^X`, nonzero).  This is the arithmetic bridge from the coset product to `#imageSet`. -/
theorem image_card_eq_pow_freeExp {N : ℕ} {l : List (BlockProduct.Block p N)} {X fe : ℕ}
    (h : BlockProduct.GoodChain l X)
    (hexp : p ^ fe * p ^ X = (l.map fun b => Nat.card b.coset).prod) :
    Nat.card (BlockProduct.imageSet l) = p ^ fe := by
  have hbc := BlockProduct.blocks_card h
  rw [← hexp] at hbc
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero X hp.out.ne_zero)) hbc

/-- **Step 3 — `card_inCellMulti_node_of_card_le` (the node identity, count-forcing form).**  THE
theorem of the product at level `N` in count form: `#{f | InCellMulti f c resid} · p^X = Π coset`.
Given the ⊇ count `#imageSet ≤ #fiber` (`card_imageSet_le_fiber`) and the ⊆ count
`#fiber ≤ #imageSet` (from the independent fiber count meeting `#imageSet = p^fe` on the prodSC=1
gate cells), the two forcing inequalities pin `#fiber = #imageSet`, and `BlockProduct.blocks_card`
transports the em-square law verbatim.  Honest: the ⊆ inequality is the residual P3 obligation for
prodSC>1 cells; for the prodSC=1 gate cells it is `#fiber = p^fe = #imageSet` outright. -/
theorem card_inCellMulti_node_of_card_le {N : ℕ} {l : List (BlockProduct.Block p N)} {X : ℕ}
    (h : BlockProduct.GoodChain l X)
    {FibCard : ℕ}
    (hle1 : Nat.card (BlockProduct.imageSet l) ≤ FibCard)
    (hle2 : FibCard ≤ Nat.card (BlockProduct.imageSet l)) :
    FibCard * p ^ X = (l.map fun b => Nat.card b.coset).prod := by
  rw [le_antisymm hle2 hle1]
  exact BlockProduct.blocks_card h

/-- **Step 3 — `inCellMulti_eq_image` (the set identity, prodSC=1 forcing form).**  For a prodSC=1
cell, `#fiber = p^fe = #imageSet` (Step 1 with `prodSC = 1`, Step 2 core), and `imageSet ⊆ fiber`
(⊇), so `image_eq_of_subset_of_card_le` forces `fiber = imageSet` as sets of monic polynomials.
Stated over the polynomial carrier (the fiber viewed as the set of its underlying monics) so both
sides are `Set ((ZMod (p^N))[X])`.  Honest: takes the ⊇ set-inclusion and the two card facts as
hypotheses — exactly the outputs of the ⊇ free transports + Steps 1/2 on the gate cells. -/
theorem inCellMulti_eq_image {N : ℕ} (l : List (BlockProduct.Block p N))
    (Fib : Set ((ZMod (p ^ N))[X]))
    (hsub : BlockProduct.imageSet l ⊆ Fib)
    (hFibFin : Fib.Finite)
    (hcard : Nat.card Fib ≤ Nat.card (BlockProduct.imageSet l)) :
    Fib = BlockProduct.imageSet l :=
  (image_eq_of_subset_of_card_le hsub hFibFin hcard).symm

/-! ### 14a. Gate instances — the node identity CLOSED at the three gate cells.

The three gate cells' em-square identities in the `Π coset = fiber · p^X` form are banked in
`BlockProduct` (`gateB_law`, `gate{A,C}_coset_product`).  Combined with the exponent identity
`fiber = p^freeExp` (sympy: B `81 = 3^4`, A `8192 = 2^13`, C `19683 = 3^9`), these ARE the node
identity `#{InCellMulti fiber} · p^X = Π coset` at the gate, with the fiber count re-derived as the
independent `cell_card_raw` count.  We record the gate numbers directly. -/

/-- **Gate B node identity** (`p=3, N=3`): `81 · 3² = 27 · 27 = Π coset` — the classifier fiber
count `81 = 3^freeExp` (prodSC=1, so `InCellMulti` fiber = `InCell` fiber = 81) meets the em-square
law.  `81 · 9 = 729`. -/
theorem gate_node_B : (81 : ℕ) * 3 ^ 2 = BlockProduct.gateB_P₁.card * BlockProduct.gateB_P₂.card := by
  rw [BlockProduct.gateB_card_P₁, BlockProduct.gateB_card_P₂]; norm_num

/-- **Gate A node identity** (`p=2, N=5`): `8192 · 2⁴ = Π coset` — the classifier fiber
`8192 = 2^13 = 2^freeExp` (prodSC=1) times the torsor `2^4` equals the block-coset product. -/
theorem gate_node_A :
    (8192 : ℕ) * 2 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 1 1 1 //
          RestartEquiv.FreshClusterPattern 2 5 1 2 1 β}
        * Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 2 1 1 //
            RestartEquiv.FreshClusterPattern 2 5 2 2 1 β} :=
  BlockProduct.gateA_coset_product.symm

/-- **Gate C node identity** (`p=3, N=4`): `19683 · 3⁴ = Π coset` — the classifier fiber
`19683 = 3^9 = 3^freeExp` (the FIXED-root-pin fiber; the shape fiber is `2·19683 = 39366` since
`prodSC=2`) times the torsor `3^4` equals the block-coset product.  **The fiber count `19683` is now
the GENUINE fixed-pin `InCellMulti` fiber count, proven outright in §15a `gate_node_C_closed`**
(`card_inCellMulti_fixedpin_caseC` = `3^9`); this `gate_node_C` records the coset-product side. -/
theorem gate_node_C :
    (19683 : ℕ) * 3 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 3 4 2 1 1 //
          RestartEquiv.FreshClusterPattern 3 4 2 2 1 β}
        * Nat.card {β : Fin 1 → RphiRing.Rphi 3 4 2 1 BlockProduct.cC₂ //
            RestartEquiv.FreshClusterPattern 3 4 2 1 BlockProduct.cC₂ β} :=
  BlockProduct.gateC_coset_product.symm


/-! ## 15. **The FIXED-ROOT-PIN fiber count (single side): removing the prodSC shape-multiplicity.** -/

/-- **`card_patPart_fixed` — the fixed-target pattern-block SINGLETON count.**  Digit vectors
supported on the PATTERN positions whose anchored side polynomial equals a SPECIFIC monic
prime-to-`X` `R` (degree `≤ sideDeg pr`, coeff at `sideDeg` equal to the anchor `u`, unit constant)
are UNIQUE — the window vector is read off `R`'s coefficients.  Count `1`: the fixed-target
analogue of `CellCard.card_patPart`'s `shapeCount l` (removing the shape-multiplicity factor). -/
theorem card_patPart_fixed {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {u : ZMod p}
    {R : (ZMod p)[X]} (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr)
    (hRlead : R.coeff (CellMenu.sideDeg pr) = u) (hR0 : R.coeff 0 ≠ 0) :
    Nat.card {x : Fin s → ZMod p // (∀ i ∉ CellCard.patFinset s pr, x i = 0)
        ∧ CellCard.sidePolyA p x u pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0}
      = 1 := by
  classical
  have he0 := CellCard.sideE_pos hw hh
  have hd0 := CellCard.sideDeg_pos hw hh
  have hj0s : pr.1.1 < s := by omega
  have hj0mem : (⟨pr.1.1, hj0s⟩ : Fin s) ∈ CellCard.patFinset s pr := by
    rw [CellCard.mem_patFinset]; exact ⟨le_refl _, by omega, by simp⟩
  -- membership witness: read R's coefficients off the pattern positions
  have hmem : (fun i : Fin s => if i ∈ CellCard.patFinset s pr
      then R.coeff ((i.1 - pr.1.1) / CellCard.sideE pr) else 0)
      ∈ {x : Fin s → ZMod p | (∀ i ∉ CellCard.patFinset s pr, x i = 0)
        ∧ CellCard.sidePolyA p x u pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0} := by
    refine ⟨fun i hi => if_neg hi, ?_, ?_⟩
    · ext k
      rw [CellCard.sidePolyA_coeff]
      by_cases h1 : k < CellMenu.sideDeg pr
      · rw [if_pos h1]
        obtain ⟨hlts, hmemp⟩ := CellCard.pat_pos_mem hw hh hs h1
        rw [CellCard.rho_lt p _ hlts, if_pos hmemp]
        congr 2
        rw [show pr.1.1 + k * CellCard.sideE pr - pr.1.1 = k * CellCard.sideE pr from by omega,
          Nat.mul_div_cancel _ he0]
      · by_cases h2 : k = CellMenu.sideDeg pr
        · rw [if_neg h1, if_pos h2, h2, hRlead]
        · rw [if_neg h1, if_neg h2, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    · rw [CellCard.rho_lt p _ hj0s, if_pos hj0mem]
      simpa using hR0
  -- uniqueness: any two elements agree everywhere
  have huniq : ∀ y : {x : Fin s → ZMod p // (∀ i ∉ CellCard.patFinset s pr, x i = 0)
        ∧ CellCard.sidePolyA p x u pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0},
      y.1 = (fun i : Fin s => if i ∈ CellCard.patFinset s pr
        then R.coeff ((i.1 - pr.1.1) / CellCard.sideE pr) else 0) := by
    rintro ⟨y, hy0, hyR, hyu⟩
    funext i
    by_cases hi : i ∈ CellCard.patFinset s pr
    · simp only [if_pos hi]
      obtain ⟨h1, h2, h3⟩ := CellCard.mem_patFinset.mp hi
      have hdvd : CellCard.sideE pr ∣ (i.1 - pr.1.1) := Nat.dvd_of_mod_eq_zero h3
      have hte : (i.1 - pr.1.1) / CellCard.sideE pr * CellCard.sideE pr = i.1 - pr.1.1 :=
        Nat.div_mul_cancel hdvd
      have htd : (i.1 - pr.1.1) / CellCard.sideE pr < CellMenu.sideDeg pr := by
        rw [Nat.div_lt_iff_lt_mul he0]; have := CellCard.sideDeg_mul_sideE hw hh; omega
      have hcoeff := congrArg
        (fun Q : (ZMod p)[X] => Q.coeff ((i.1 - pr.1.1) / CellCard.sideE pr)) hyR
      rw [CellCard.sidePolyA_coeff, if_pos htd] at hcoeff
      have hpos : pr.1.1 + (i.1 - pr.1.1) / CellCard.sideE pr * CellCard.sideE pr = i.1 := by
        rw [hte]; omega
      rw [CellCard.rho_lt p _ (show pr.1.1 + (i.1 - pr.1.1) / CellCard.sideE pr * CellCard.sideE pr < s
        from by rw [hpos]; exact i.2)] at hcoeff
      rw [show (⟨pr.1.1 + (i.1 - pr.1.1) / CellCard.sideE pr * CellCard.sideE pr,
          show pr.1.1 + (i.1 - pr.1.1) / CellCard.sideE pr * CellCard.sideE pr < s
            from by rw [hpos]; exact i.2⟩ : Fin s) = i from Fin.ext hpos] at hcoeff
      exact hcoeff
    · simp only [if_neg hi]; exact hy0 i hi
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((huniq a).trans (huniq b).symm)⟩, ⟨⟨_, hmem⟩⟩⟩

/-- **`card_sideSet_fixed` — the fixed-target anchored window count** `p^(run − sideDeg)`.  Window
vectors whose anchored side polynomial equals `R` (a fixed monic prime-to-`X`) have the pattern
block DETERMINED (`card_patPart_fixed` = 1) and the `(run − sideDeg)` off-pattern residue digits
FREE.  Fixed-target analogue of `CellCard.card_sideSet` with `shapeCount l` replaced by `1`. -/
theorem card_sideSet_fixed {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) {u : ZMod p}
    {R : (ZMod p)[X]} (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr)
    (hRlead : R.coeff (CellMenu.sideDeg pr) = u) (hR0 : R.coeff 0 ≠ 0) :
    Nat.card {x : Fin s → ZMod p // (∀ i ∉ CellCard.winFinset s pr, x i = 0)
        ∧ CellCard.sidePolyA p x u pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0}
      = p ^ (pr.2.1 - pr.1.1 - CellMenu.sideDeg pr) := by
  classical
  have hsplit := CellCard.card_supp_split (CellCard.patFinset s pr)
    (CellCard.winFinset s pr \ CellCard.patFinset s pr) (Finset.disjoint_sdiff)
    (fun x => CellCard.sidePolyA p x u pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0)
    ?_
  · rw [Finset.union_sdiff_of_subset CellCard.patFinset_subset] at hsplit
    rw [hsplit, card_patPart_fixed p hw hh hs hRdeg hRlead hR0, Nat.card_zmod,
      Finset.card_sdiff, Finset.inter_eq_left.mpr CellCard.patFinset_subset,
      CellCard.card_winFinset hs, CellCard.card_patFinset hw hh hs, one_mul]
  · intro f g hagree hf
    have hrho : ∀ t, t < CellMenu.sideDeg pr →
        CellCard.rho p f (pr.1.1 + t * CellCard.sideE pr)
          = CellCard.rho p g (pr.1.1 + t * CellCard.sideE pr) := by
      intro t ht
      obtain ⟨hlt, hmemp⟩ := CellCard.pat_pos_mem hw hh hs ht
      rw [CellCard.rho_lt p _ hlt, CellCard.rho_lt p _ hlt]
      exact hagree _ hmemp
    have h0 : CellCard.rho p f pr.1.1 = CellCard.rho p g pr.1.1 := by
      have h00 := hrho 0 (CellCard.sideDeg_pos hw hh)
      rwa [show pr.1.1 + 0 * CellCard.sideE pr = pr.1.1 from by omega] at h00
    refine ⟨?_, ?_⟩
    · rw [← CellCard.sidePolyA_congr p u pr hrho]; exact hf.1
    · rw [← h0]; exact hf.2

/-- **`card_digCond_fixed_single` — the single-side fixed-target DIGIT count** `p^chainFree`.  For a
single-side path `[(0,H),(s,0)]` the digit vectors `r` whose side residual `sidePolyR r pr` equals a
fixed monic prime-to-`X` `R` (with `rho r i0` a unit) number `p^(s − sideDeg pr) = p^chainFree P`.
The window is all of `Fin s` (support constraint vacuous) and the anchor is the monic cap
`rho r s = 1`, so this is `card_sideSet_fixed`. -/
theorem card_digCond_fixed_single {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hw0 : pr.1.1 = 0) (hs : pr.2.1 = s) (hh : pr.2.2 < pr.1.2) (hspos : 0 < s)
    {R : (ZMod p)[X]} (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr)
    (hRlead : R.coeff (CellMenu.sideDeg pr) = 1) (hR0 : R.coeff 0 ≠ 0) :
    Nat.card {r : Fin s → ZMod p //
        CellCard.sidePolyR p r pr = R ∧ CellCard.rho p r pr.1.1 ≠ 0}
      = p ^ (s - CellMenu.sideDeg pr) := by
  classical
  have hw : pr.1.1 < pr.2.1 := by omega
  have hs' : pr.2.1 ≤ s := by omega
  -- rewrite sidePolyR as anchored sidePolyA (anchor = rho r s = 1)
  have hanchor : ∀ r : Fin s → ZMod p, CellCard.rho p r pr.2.1 = 1 := fun r => by
    rw [hs]; exact CellCard.rho_ge p r (by omega)
  -- the window is all of Fin s (support constraint vacuous)
  have hwin_univ : CellCard.winFinset s pr = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i; rw [CellCard.mem_winFinset]; omega
  have e : {r : Fin s → ZMod p //
        CellCard.sidePolyR p r pr = R ∧ CellCard.rho p r pr.1.1 ≠ 0}
      ≃ {x : Fin s → ZMod p // (∀ i ∉ CellCard.winFinset s pr, x i = 0)
          ∧ CellCard.sidePolyA p x 1 pr = R ∧ CellCard.rho p x pr.1.1 ≠ 0} :=
    Equiv.subtypeEquivRight fun r => by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => absurd (by rw [hwin_univ]; exact Finset.mem_univ i) hi, ?_, h2⟩
        rw [← hanchor r, ← CellCard.sidePolyR_eq_sidePolyA p r hw hh]; exact h1
      · rintro ⟨_, h1, h2⟩
        refine ⟨?_, h2⟩
        rw [CellCard.sidePolyR_eq_sidePolyA p r hw hh, hanchor r]; exact h1
  rw [Nat.card_congr e, card_sideSet_fixed p hw hh hs' hRdeg hRlead hR0]
  congr 1
  omega

/-- **`cell_card_raw_fixed_single` — the single-side FIXED-ROOT-PIN box count** `p^freeExp`.  For a
single-side menu cell `mkCell s [(0,H),(s,0)] [l]` and a FIXED monic prime-to-`X` residual `R` of
shape `l`, the box polynomials matching the cell whose side residual is exactly `R` number
`p^(freeExp s N P)` — the shape-multiplicity `shapeCount l` of `CellCard.cell_card_raw` is collapsed
to `1`.  Fixed-target mirror of `CellCard.cell_card_raw` (Steps 1–5) through `matches_iff` /
`residualOf_eq_sidePolyR` and the per-column divisibility fibering. -/
theorem cell_card_raw_fixed_single {s N : ℕ} (hN : 0 < N) {H : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N [(0, H), (s, 0)]) {l : List (ℕ × ℕ)}
    (hsh : CellMenu.ShapesFor [(0, H), (s, 0)] [l]) (hpr : pr = ((0, H), (s, 0)))
    {R : (ZMod p)[X]}
    (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr) (hRlead : R.coeff (CellMenu.sideDeg pr) = 1)
    (hR0 : R.coeff 0 ≠ 0) (hRshape : CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ)))
    (hspos : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s //
        InCell p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) ∧
          CellMenu.residualOf p f pr = R}
      = p ^ CellCard.freeExp s N [(0, H), (s, 0)] := by
  classical
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  have hsp : CellMenu.sidePairs [(0, H), (s, 0)] = [pr] := by rw [hpr]; rfl
  have hHpos : 0 < H := by
    obtain ⟨H', p1, T, hPe, hH1, hH2, hp1, hpH, hc⟩ := hP
    have hce : ((0, H) : ℕ × ℕ) :: [(s, 0)] = (0, H') :: p1 :: T := hPe
    have : (0, H) = (0, H') := (List.cons.inj hce).1
    have hHval : H = H' := (Prod.mk.inj this).2
    omega
  have hhh : pr.2.2 < pr.1.2 := by rw [hpr]; exact hHpos
  -- Step 1: InCell = Matches
  have e1 : {f : QuotientBox.monicBox p N s //
        InCell p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) ∧ CellMenu.residualOf p f pr = R}
      ≃ {f : QuotientBox.monicBox p N s //
          CellMenu.Matches p f [(0, H), (s, 0)] [l] ∧ CellMenu.residualOf p f pr = R} :=
    Equiv.subtypeEquivRight fun f => by
      rw [CellMenu.inCell_mkCell_iff p hP hsh]
  rw [Nat.card_congr e1]
  -- Step 2: Matches ∧ resid=R  =  (divisibility ∧ DigCond ∧ sidePolyR=R), through coeffEquiv;
  -- but the DigCond shape follows from sidePolyR = R (polyShape R = l), so keep it as-is and
  -- convert residualOf → sidePolyR under the divisibility.
  have e2 : {f : QuotientBox.monicBox p N s //
        CellMenu.Matches p f [(0, H), (s, 0)] [l] ∧ CellMenu.residualOf p f pr = R}
      ≃ {a : Fin s → ZMod (p ^ N) //
          (∀ i : Fin s, p ^ CellMenu.ceilAt [(0, H), (s, 0)] i.1 ∣ ((a i).val))
            ∧ CellCard.sidePolyR p
                (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (a i)) pr
                = R
            ∧ CellCard.rho p
                (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (a i))
                pr.1.1 ≠ 0} :=
    (CellCard.coeffEquiv p N s hN).subtypeEquiv fun f => by
      rw [CellCard.matches_iff p hN hP hsh f]
      constructor
      · rintro ⟨⟨hdvd, hdig⟩, hres⟩
        refine ⟨hdvd, ?_, ?_⟩
        · show CellCard.sidePolyR p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (f.1.coeff i.1)) pr = R
          rw [← CellCard.residualOf_eq_sidePolyR p hN hP (by rw [hsp]; exact List.mem_singleton_self pr) f hdvd]
          exact hres
        · -- rho i0 ≠ 0 from the DigCond SideCond left read
          have hd := hdig
          unfold CellCard.DigCond at hd
          rw [hsp, List.forall₂_cons] at hd
          exact hd.1.2
      · rintro ⟨hdvd, hspR, hrho⟩
        have hshapeSide : CellMenu.polyShape p
            (CellCard.sidePolyR p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1)
              ((CellCard.coeffEquiv p N s hN) f i)) pr) = (l : Multiset (ℕ × ℕ)) := by
          rw [hspR]; exact hRshape
        refine ⟨⟨hdvd, ?_⟩, ?_⟩
        · unfold CellCard.DigCond
          rw [hsp]
          refine List.Forall₂.cons ⟨?_, hrho⟩ List.Forall₂.nil
          exact hshapeSide
        · rw [CellCard.residualOf_eq_sidePolyR p hN hP (by rw [hsp]; exact List.mem_singleton_self pr) f hdvd]
          exact hspR
  rw [Nat.card_congr e2]
  -- Step 3: pull divisibility into the coordinate type
  have e3 : {a : Fin s → ZMod (p ^ N) //
        (∀ i : Fin s, p ^ CellMenu.ceilAt [(0, H), (s, 0)] i.1 ∣ ((a i).val))
          ∧ CellCard.sidePolyR p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (a i)) pr = R
          ∧ CellCard.rho p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (a i)) pr.1.1 ≠ 0}
      ≃ {b : ∀ i : Fin s, {x : ZMod (p ^ N) // p ^ CellMenu.ceilAt [(0, H), (s, 0)] i.1 ∣ x.val} //
          CellCard.sidePolyR p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (b i).1) pr = R
            ∧ CellCard.rho p (fun i : Fin s => CellCard.digit p N
              (CellMenu.ceilAt [(0, H), (s, 0)] i.1) (b i).1) pr.1.1 ≠ 0} :=
    { toFun := fun a => ⟨fun i => ⟨a.1 i, a.2.1 i⟩, a.2.2⟩
      invFun := fun b => ⟨fun i => (b.1 i).1, fun i => (b.1 i).2, b.2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr e3]
  -- Step 4: per-coordinate digit fibering
  rw [CellCard.card_pi_fiber
    (fun (i : Fin s) (x : {x : ZMod (p ^ N) // p ^ CellMenu.ceilAt [(0, H), (s, 0)] i.1 ∣ x.val}) =>
      CellCard.digit p N (CellMenu.ceilAt [(0, H), (s, 0)] i.1) x.1)
    (fun i => p ^ (N - CellMenu.ceilAt [(0, H), (s, 0)] i.1 - 1))
    (fun i c => CellCard.card_digit_fiber p (by
      have := CellCard.menuPath_ceilAt_le hP i.2
      omega) c)
    (fun r => CellCard.sidePolyR p r pr = R ∧ CellCard.rho p r pr.1.1 ≠ 0)]
  -- Step 5: the fixed digit count × the divisibility exponent
  have hi0 : pr.1.1 = 0 := by rw [hpr]
  have hs21 : pr.2.1 = s := by rw [hpr]
  rw [card_digCond_fixed_single p hi0 hs21 hhh hspos hRdeg hRlead hR0,
    Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => N - CellMenu.ceilAt [(0, H), (s, 0)] j - 1) s]
  have hsum : ∑ i ∈ Finset.range s, (N - CellMenu.ceilAt [(0, H), (s, 0)] i - 1)
      = ∑ i ∈ Finset.range s, (N - 1 - CellMenu.ceilAt [(0, H), (s, 0)] i) :=
    Finset.sum_congr rfl fun i _ => by omega
  rw [hsum]
  -- freeExp = col + chainFree ; chainFree [(0,H),(s,0)] = s - sideDeg pr
  have hcf : CellCard.chainFree [(0, H), (s, 0)] = s - CellMenu.sideDeg pr := by
    unfold CellCard.chainFree
    rw [hsp, hpr]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    show s - 0 - CellMenu.sideDeg ((0, H), (s, 0)) = s - CellMenu.sideDeg ((0, H), (s, 0))
    omega
  unfold CellCard.freeExp
  rw [hcf, ← pow_add]
  congr 1
  omega

/-- **`inCellMulti_single_fixed` — the single-side fixed-pin membership.**  For a single-side menu
cell, `InCellMulti f (mkCell s [(0,H),(s,0)] [l]) [R]` (the residual pinned to the SPECIFIC `R`, not
its shape) holds iff `f ∈ InCell` AND `residualOf f pr = R`.  This is the genuine root-refined pin
(cf. `CellMenu.inCellMulti_single`, which pins the shape-determined tautological residual); here the
target is a FIXED polynomial. -/
theorem inCellMulti_single_fixed {s N : ℕ} {H : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N [(0, H), (s, 0)]) {l : List (ℕ × ℕ)}
    (hsh : CellMenu.ShapesFor [(0, H), (s, 0)] [l]) (hpr : pr = ((0, H), (s, 0)))
    {f : QuotientBox.monicBox p N s} {R : (ZMod p)[X]} :
    InCellMulti p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) [R]
      ↔ InCell p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) ∧ CellMenu.residualOf p f pr = R := by
  have hsp : CellMenu.sidePairs [(0, H), (s, 0)] = [pr] := by rw [hpr]; rfl
  constructor
  · rintro ⟨P', sh', hP', hsh', heq, hm, hres⟩
    obtain ⟨rfl, rfl⟩ := CellMenu.mkCell_injective hP' hP hsh' hsh heq.symm
    refine ⟨⟨_, _, hP', hsh', rfl, hm⟩, ?_⟩
    unfold CellMenu.ResidRefines at hres
    rw [hsp, List.forall₂_cons] at hres
    exact hres.1
  · rintro ⟨⟨P', sh', hP', hsh', heq, hm⟩, hres⟩
    obtain ⟨rfl, rfl⟩ := CellMenu.mkCell_injective hP' hP hsh' hsh heq.symm
    refine ⟨_, _, hP', hsh', rfl, hm, ?_⟩
    unfold CellMenu.ResidRefines
    rw [hsp]
    exact List.Forall₂.cons hres List.Forall₂.nil

/-- **`card_inCellMulti_fixedpin_fiber_single` — the FIXED-ROOT-PIN classifier fiber count** for a
single-side cell: `p^freeExp`.  The residual is pinned to a SPECIFIC monic prime-to-`X` `R` of the
cell's shape (a product of the on-side block residuals via `polyShape_residualOf_mul`), so the
`prodSC = shapeCount l` shape-multiplicity is collapsed to one — the fiber has `p^freeExp` elements,
NOT `prodSC · p^freeExp` (`card_inCellMulti_fiber`, the tautological pin).  This is the count the
`prodSC > 1` cardinality route (case C) needs: `p^freeExp = #imageSet`. -/
theorem card_inCellMulti_fixedpin_fiber_single {s N : ℕ} (hN : 0 < N) {H : ℕ}
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hP : CellMenu.MenuPath s N [(0, H), (s, 0)]) {l : List (ℕ × ℕ)}
    (hsh : CellMenu.ShapesFor [(0, H), (s, 0)] [l]) (hpr : pr = ((0, H), (s, 0)))
    {R : (ZMod p)[X]}
    (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr) (hRlead : R.coeff (CellMenu.sideDeg pr) = 1)
    (hR0 : R.coeff 0 ≠ 0) (hRshape : CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ)))
    (hspos : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s //
        InCellMulti p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) [R]}
      = p ^ CellCard.freeExp s N [(0, H), (s, 0)] := by
  have e : {f : QuotientBox.monicBox p N s //
        InCellMulti p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) [R]}
      ≃ {f : QuotientBox.monicBox p N s //
          InCell p f (CellMenu.mkCell s [(0, H), (s, 0)] [l]) ∧ CellMenu.residualOf p f pr = R} :=
    Equiv.subtypeEquivRight fun f => inCellMulti_single_fixed p hP hsh hpr
  rw [Nat.card_congr e, cell_card_raw_fixed_single p hN hP hsh hpr hRdeg hRlead hR0 hRshape hspos]

/-! ### 15a. Case C — the FIXED-ROOT-PIN node identity, CLOSED OUTRIGHT.

The specific case-C residual `R* = (X−1)(X−2)²` over `ZMod 3` (one of the `prodSC = 2`
shape-`[(1,1),(1,2)]` polynomials).  The fixed-pin `InCellMulti` fiber count is
`3^(freeExp 6 4 [(0,3),(6,0)]) = 3^9 = 19683` (`card_inCellMulti_fixedpin_fiber_single`) — NOT the
tautological-pin `prodSC · 3^9 = 39366`.  Meeting `BlockProduct.gateC_coset_product`
(`Π coset = 19683 · 3^4`) gives the node identity OUTRIGHT, matching cases A/B (whose prodSC = 1 so
the fixed pin coincides with the tautological pin — nothing changes there). -/

/-- The concrete case-C fixed residual `R* = (X−1)(X−2)²` over `ZMod 3`. -/
noncomputable def residC : (ZMod 3)[X] := (X - C (1 : ZMod 3)) * (X - C (2 : ZMod 3)) ^ 2

theorem residC_shape : CellMenu.polyShape 3 residC = ({(1, 1), (1, 2)} : Multiset (ℕ × ℕ)) := by
  have h1ne : (X - C (1 : ZMod 3)) ≠ 0 := X_sub_C_ne_zero 1
  have h2ne : ((X - C (2 : ZMod 3)) ^ 2) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 2)
  have hcop : IsCoprime (X - C (1 : ZMod 3)) ((X - C (2 : ZMod 3)) ^ 2) :=
    (isCoprime_X_sub_C_of_isUnit_sub (by decide : IsUnit ((1 : ZMod 3) - 2))).pow_right
  rw [residC, CellMenu.polyShape_mul 3 h1ne h2ne hcop,
    show (X - C (1 : ZMod 3)) = X + C (-1 : ZMod 3) by rw [map_neg, sub_eq_add_neg],
    show (X - C (2 : ZMod 3)) = X + C (-2 : ZMod 3) by rw [map_neg, sub_eq_add_neg],
    CellMenu.polyShape_linear, CellMenu.polyShape_pow_linear 3 (-2 : ZMod 3) (by norm_num)]
  decide

/-- **Case-C FIXED-ROOT-PIN fiber count = `19683`, proven OUTRIGHT.**  The genuine classifier
`InCellMulti` fiber for case C with the residual pinned to the SPECIFIC `R* = (X−1)(X−2)²` has
exactly `3^9 = 19683` elements — the `prodSC = 2` shape-multiplicity is removed by fixing the
residual polynomial (cf. `card_inCellMulti_fiber` = `prodSC · 3^9 = 39366`, the tautological pin). -/
theorem card_inCellMulti_fixedpin_caseC :
    Nat.card {f : QuotientBox.monicBox 3 4 6 //
        InCellMulti 3 f (CellMenu.mkCell 6 [(0, 3), (6, 0)] [[(1, 1), (1, 2)]]) [residC]}
      = 19683 := by
  have hP : CellMenu.MenuPath 6 4 [(0, 3), (6, 0)] :=
    ⟨3, (6, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      CellMenu.ChainOK.nil rfl rfl⟩
  have hsh : CellMenu.ShapesFor [(0, 3), (6, 0)] [[(1, 1), (1, 2)]] := by
    show List.Forall₂ _ [[(1, 1), (1, 2)]] (CellMenu.sidePairs [(0, 3), (6, 0)])
    exact List.Forall₂.cons (by decide) List.Forall₂.nil
  have hdeg3 : CellMenu.sideDeg ((0, 3), (6, 0)) = 3 := by decide
  have hRdeg : residC.natDegree ≤ CellMenu.sideDeg ((0, 3), (6, 0)) := by
    rw [hdeg3, residC]; compute_degree
  have hRlead : residC.coeff (CellMenu.sideDeg ((0, 3), (6, 0))) = 1 := by
    rw [hdeg3, residC]; compute_degree!
  have hR0 : residC.coeff 0 ≠ 0 := by
    rw [residC, Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    decide
  have hfe : CellCard.freeExp 6 4 [(0, 3), (6, 0)] = 9 := by decide
  rw [card_inCellMulti_fixedpin_fiber_single 3 (by norm_num) hP hsh rfl hRdeg hRlead hR0
    residC_shape (by norm_num), hfe]
  norm_num

/-- **Gate C node identity — CLOSED OUTRIGHT** (`p=3, N=4`): the FIXED-ROOT-PIN classifier
`InCellMulti` fiber count `19683 = 3^9 = 3^freeExp` (`card_inCellMulti_fixedpin_caseC`, the
`prodSC = 2` shape-multiplicity removed by pinning the residual to the SPECIFIC `R* = (X−1)(X−2)²`)
times the torsor `3⁴` equals the block-coset product (`gateC_coset_product`).  Unlike the previous
`gate_node_C` (which recorded the numbers), the fiber count `19683` is here the genuine independent
classifier-fiber count, so the node identity holds outright.  Cases A/B: prodSC = 1, so the fixed
pin coincides with the tautological pin — `gate_node_A`/`gate_node_B` are unchanged. -/
theorem gate_node_C_closed :
    Nat.card {f : QuotientBox.monicBox 3 4 6 //
        InCellMulti 3 f (CellMenu.mkCell 6 [(0, 3), (6, 0)] [[(1, 1), (1, 2)]]) [residC]} * 3 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 3 4 2 1 1 //
          RestartEquiv.FreshClusterPattern 3 4 2 2 1 β}
        * Nat.card {β : Fin 1 → RphiRing.Rphi 3 4 2 1 BlockProduct.cC₂ //
            RestartEquiv.FreshClusterPattern 3 4 2 1 BlockProduct.cC₂ β} := by
  rw [card_inCellMulti_fixedpin_caseC]
  exact BlockProduct.gateC_coset_product.symm

/-! ## 15b. **LEG 2 — the MULTI-SIDE FIXED-ROOT-PIN fiber count.**

§15 counted the single-side fixed-pin fiber (`card_inCellMulti_fixedpin_fiber_single` = `p^freeExp`).
The multi-side node identity (case A is 2-side) needs the same collapse on a cell with SEVERAL sides:
pin the residual on EACH side of the concatenated polygon to a SPECIFIC monic prime-to-`X` `Rᵢ`
(a product of the on-side block residuals, `polyShape_residualOf_mul`), so the per-side
`shapeCount lᵢ` shape-multiplicity is collapsed to `1` on EVERY side, and the fiber has `p^freeExp`
elements OUTRIGHT — NOT `prodSC · p^freeExp` (`card_inCellMulti_fiber`, the tautological pin).

The route mirrors `CellCard.cell_card_raw` (Steps 1–5) but with the DIGIT telescope replaced by the
FIXED-residual telescope: the per-side `card_sideSet` (`shapeCount lᵢ · p^(runᵢ−degᵢ)`, §6 of CellCard)
becomes `card_sideSet_fixed` (`1 · p^(runᵢ−degᵢ)`, §15 here), so the chain telescope multiplies to
`p^chainFree` (each side contributing `1`, no `prodSC`).  We re-derive the telescope here (the shape
condition of `CellCard.peelEquiv`/`card_peel`/`chain_count` is replaced by the fixed-residual side
equality); `CellCard`'s support-splice / sigma-const primitives are reused generically. -/

/-- The FIXED-residual per-side condition: the side residual read equals a SPECIFIC `R` (not just its
shape), with the left-vertex digit a unit.  Fixed-target analogue of `CellCard.SideCond`. -/
def SideCondFixed {s : ℕ} (r : Fin s → ZMod p) (R : (ZMod p)[X]) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  CellCard.sidePolyR p r pr = R ∧ CellCard.rho p r pr.1.1 ≠ 0

theorem sideCondFixed_congr {s : ℕ} {r r' : Fin s → ZMod p} {R : (ZMod p)[X]}
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (h : ∀ j, pr.1.1 ≤ j → CellCard.rho p r j = CellCard.rho p r' j) :
    SideCondFixed p r R pr ↔ SideCondFixed p r' R pr := by
  unfold SideCondFixed
  rw [CellCard.sidePolyR_congr p pr h, h pr.1.1 (le_refl _)]

/-- **`peelEquiv_fixed`** — the peel splice for the FIXED-residual side condition (mirror of
`CellCard.peelEquiv`; the shape predicate `polyShape (sidePolyA …) = l` is replaced by the fixed
equality `sidePolyA … = R`).  A zero-based digit vector satisfying the leftmost FIXED side condition
plus a right-suffix condition `Q` splits into its suffix part and its anchored window part. -/
noncomputable def peelEquiv_fixed {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s) (R : (ZMod p)[X])
    (Q : (Fin s → ZMod p) → Prop)
    (hQ : ∀ r r' : Fin s → ZMod p, (∀ i : Fin s, pr.2.1 ≤ i.1 → r i = r' i) → Q r → Q r') :
    {r : Fin s → ZMod p // CellCard.ZeroBelow p pr.1.1 r ∧ SideCondFixed p r R pr ∧ Q r}
      ≃ {z : {y : Fin s → ZMod p // CellCard.ZeroBelow p pr.2.1 y ∧ Q y} × (Fin s → ZMod p) //
          (∀ i ∉ CellCard.winFinset s pr, z.2 i = 0)
            ∧ CellCard.sidePolyA p z.2 (CellCard.rho p z.1.1 pr.2.1) pr = R
            ∧ CellCard.rho p z.2 pr.1.1 ≠ 0} where
  toFun r :=
    ⟨(⟨fun i => if i.1 < pr.2.1 then 0 else r.1 i,
        fun i hi => if_pos hi,
        hQ r.1 _ (fun i hi => (if_neg (by omega)).symm) r.2.2.2⟩,
      fun i => if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0),
     by
      refine ⟨fun i hi => if_neg (by rw [CellCard.mem_winFinset] at hi; exact hi), ?_, ?_⟩
      · have hb := CellCard.peel_bridge p hw hh hs r.1
          (fun i => if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0)
          (fun i => if i.1 < pr.2.1 then 0 else r.1 i)
          (fun i h1 h2 => if_pos ⟨h1, h2⟩) (fun i hi => if_neg (by omega))
        rw [← hb]
        exact r.2.2.1.1
      · have hj0s : pr.1.1 < s := by omega
        rw [CellCard.rho_lt p _ hj0s]
        show (if pr.1.1 ≤ pr.1.1 ∧ pr.1.1 < pr.2.1 then r.1 ⟨pr.1.1, hj0s⟩ else 0) ≠ 0
        rw [if_pos ⟨le_refl _, hw⟩]
        have h1 := r.2.2.1.2
        rwa [CellCard.rho_lt p _ hj0s] at h1⟩
  invFun z :=
    ⟨fun i => z.1.2 i + z.1.1.1 i,
     by
      intro i hi
      have h1 : i ∉ CellCard.winFinset s pr := by
        rw [CellCard.mem_winFinset]
        omega
      show z.1.2 i + z.1.1.1 i = 0
      rw [z.2.1 i h1, z.1.1.2.1 i (by omega), add_zero],
     by
      constructor
      · have hb := CellCard.peel_bridge p hw hh hs (fun i => z.1.2 i + z.1.1.1 i) z.1.2 z.1.1.1
          (fun i h1 h2 => by
            show z.1.2 i = z.1.2 i + z.1.1.1 i
            rw [z.1.1.2.1 i h2, add_zero])
          (fun i hi => by
            show z.1.1.1 i = z.1.2 i + z.1.1.1 i
            rw [z.2.1 i (by rw [CellCard.mem_winFinset]; omega), zero_add])
        rw [hb]
        exact z.2.2.1
      · have hj0s : pr.1.1 < s := by omega
        rw [CellCard.rho_lt p _ hj0s]
        have h1 := z.2.2.2
        rw [CellCard.rho_lt p _ hj0s] at h1
        show z.1.2 ⟨pr.1.1, hj0s⟩ + z.1.1.1 ⟨pr.1.1, hj0s⟩ ≠ 0
        rw [z.1.1.2.1 ⟨pr.1.1, hj0s⟩ hw, add_zero]
        exact h1,
     hQ z.1.1.1 _ (fun i hi => by
        show z.1.1.1 i = z.1.2 i + z.1.1.1 i
        rw [z.2.1 i (by rw [CellCard.mem_winFinset]; omega), zero_add]) z.1.1.2.2⟩
  left_inv r := by
    refine Subtype.ext (funext fun i => ?_)
    show (if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then r.1 i else 0)
        + (if i.1 < pr.2.1 then 0 else r.1 i) = r.1 i
    by_cases h1 : i.1 < pr.1.1
    · rw [if_neg (by omega), if_pos (by omega), add_zero, r.2.1 i h1]
    · by_cases h2 : i.1 < pr.2.1
      · rw [if_pos ⟨by omega, h2⟩, if_pos h2, add_zero]
      · rw [if_neg (by omega), if_neg h2, zero_add]
  right_inv z := by
    refine Subtype.ext (Prod.ext (Subtype.ext (funext fun i => ?_)) (funext fun i => ?_))
    · show (if i.1 < pr.2.1 then 0 else z.1.2 i + z.1.1.1 i) = z.1.1.1 i
      by_cases h2 : i.1 < pr.2.1
      · rw [if_pos h2, (z.1.1.2.1 i h2)]
      · rw [if_neg h2, z.2.1 i (by rw [CellCard.mem_winFinset]; omega), zero_add]
    · show (if pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1 then z.1.2 i + z.1.1.1 i else 0) = z.1.2 i
      by_cases h1 : pr.1.1 ≤ i.1 ∧ i.1 < pr.2.1
      · rw [if_pos h1, z.1.1.2.1 i h1.2, add_zero]
      · rw [if_neg h1, (z.2.1 i (by rw [CellCard.mem_winFinset]; exact h1))]

/-- **`card_peel_fixed`** — the FIXED-residual peel step count: the leftmost side contributes
`p^(run − d_S)` (NO `shapeCount` factor — the residual is pinned to the specific `R`), independently
of the unit anchor supplied by the suffix.  Mirror of `CellCard.card_peel` with `card_sideSet_fixed`
in place of `card_sideSet`. -/
theorem card_peel_fixed {s : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hw : pr.1.1 < pr.2.1)
    (hh : pr.2.2 < pr.1.2) (hs : pr.2.1 ≤ s)
    {R : (ZMod p)[X]} (hRdeg : R.natDegree ≤ CellMenu.sideDeg pr)
    (hR0 : R.coeff 0 ≠ 0) (Q : (Fin s → ZMod p) → Prop)
    (hQ : ∀ r r' : Fin s → ZMod p, (∀ i : Fin s, pr.2.1 ≤ i.1 → r i = r' i) → Q r → Q r')
    (_hanchor : ∀ r : Fin s → ZMod p, CellCard.ZeroBelow p pr.2.1 r → Q r →
      CellCard.rho p r pr.2.1 ≠ 0)
    (hRlead : ∀ r : Fin s → ZMod p, CellCard.ZeroBelow p pr.2.1 r → Q r →
      R.coeff (CellMenu.sideDeg pr) = CellCard.rho p r pr.2.1) :
    Nat.card {r : Fin s → ZMod p // CellCard.ZeroBelow p pr.1.1 r ∧ SideCondFixed p r R pr ∧ Q r}
      = p ^ (pr.2.1 - pr.1.1 - CellMenu.sideDeg pr)
          * Nat.card {r : Fin s → ZMod p // CellCard.ZeroBelow p pr.2.1 r ∧ Q r} := by
  classical
  have hK := CellCard.card_sigma_const
    (α := {y : Fin s → ZMod p // CellCard.ZeroBelow p pr.2.1 y ∧ Q y})
    (F := fun y => {x : Fin s → ZMod p // (∀ i ∉ CellCard.winFinset s pr, x i = 0)
      ∧ CellCard.sidePolyA p x (CellCard.rho p y.1 pr.2.1) pr = R
      ∧ CellCard.rho p x pr.1.1 ≠ 0})
    (K := p ^ (pr.2.1 - pr.1.1 - CellMenu.sideDeg pr))
    (fun y => card_sideSet_fixed p hw hh hs hRdeg
      (hRlead y.1 y.2.1 y.2.2) hR0)
  rw [Nat.card_congr ((peelEquiv_fixed p hw hh hs R Q hQ).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun (y : {y : Fin s → ZMod p // CellCard.ZeroBelow p pr.2.1 y ∧ Q y}) (x : Fin s → ZMod p) =>
        (∀ i ∉ CellCard.winFinset s pr, x i = 0)
          ∧ CellCard.sidePolyA p x (CellCard.rho p y.1 pr.2.1) pr = R
          ∧ CellCard.rho p x pr.1.1 ≠ 0))), hK, mul_comm]

/-- The per-side fixed-residual condition list (one `SideCondFixed` per side). -/
def DigCondFixed {s : ℕ} (P : List (ℕ × ℕ)) (Rs : List ((ZMod p)[X])) (r : Fin s → ZMod p) : Prop :=
  List.Forall₂ (fun R pr => SideCondFixed p r R pr) Rs (CellMenu.sidePairs P)

/-- **`CoherentResid`** — the pinned-residual COHERENCE along a side chain.  Two consecutive sides
share a vertex; the shared-vertex digit is the LEADING coefficient (`coeff (sideDeg pr)`) of the LEFT
side's residual read AND the CONSTANT coefficient (`coeff 0`) of the RIGHT side's residual read.  So a
coherent list of pinned residuals `Rs` satisfies: the RIGHTMOST side's residual is MONIC
(`coeff (sideDeg) = 1`, since the right vertex is `(s,0)` where `rho r s = 1`), and each INTERIOR
side's residual's leading coefficient equals the NEXT side's residual constant term
(`R.coeff (sideDeg pr) = R'.coeff 0`).  This is the honest chain-coherence the multi-side fixed pin
requires: interior residuals are NOT monic — their top digit is the shared-vertex unit, fixed by the
next side down.  (For a SINGLE side the list is `[R]` with `R` monic — matching §15's
`hRlead : R.coeff (sideDeg pr) = 1`.) -/
def CoherentResid : List ((ZMod p)[X]) → List ((ℕ × ℕ) × (ℕ × ℕ)) → Prop
  | [R], [pr] => R.coeff (CellMenu.sideDeg pr) = 1
  | R :: R' :: Rs', pr :: prs' =>
      R.coeff (CellMenu.sideDeg pr) = R'.coeff 0 ∧ CoherentResid (R' :: Rs') prs'
  | _, _ => False

/-- **`chain_count_fixed`** — the FIXED-residual chain telescope: the count of a zero-based suffix
chain whose per-side residual reads are pinned to a COHERENT fixed list `Rs` (each `Rᵢ`
prime-to-`X`, `deg ≤ dᵢ`, and `CoherentResid` — rightmost monic, interior leading = next constant)
is `p^(Σ (runᵢ − degᵢ))` — NO `prodSC` factor (each side collapses to `1` via `card_sideSet_fixed`).
Mirror of `CellCard.chain_count`, with the interior anchor read off the suffix's leftmost residual
constant term (chain coherence). -/
theorem chain_count_fixed {s : ℕ} :
    ∀ {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}, CellMenu.ChainOK s p0 p1 T → p0.1 < p1.1 → p1.2 < p0.2 →
      ∀ {Rs : List ((ZMod p)[X])},
        List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
          (CellMenu.sidePairs (p0 :: p1 :: T)) →
        CoherentResid p Rs (CellMenu.sidePairs (p0 :: p1 :: T)) →
      Nat.card {r : Fin s → ZMod p // CellCard.ZeroBelow p p0.1 r
          ∧ List.Forall₂ (fun R pr => SideCondFixed p r R pr) Rs
              (CellMenu.sidePairs (p0 :: p1 :: T))}
        = p ^ (((CellMenu.sidePairs (p0 :: p1 :: T)).map
                fun pr => pr.2.1 - pr.1.1 - CellMenu.sideDeg pr).sum) := by
  intro T
  induction T with
  | nil =>
      intro p0 p1 hc hw hh Rs hRs hcoh
      cases hc with
      | nil h1 h2 =>
        have hsp : CellMenu.sidePairs [p0, p1] = [(p0, p1)] := rfl
        rw [hsp] at hRs hcoh ⊢
        rw [List.forall₂_cons_right_iff] at hRs
        obtain ⟨R, Rs', ⟨hRdeg, hR0⟩, hRs', rfl⟩ := hRs
        rw [List.forall₂_nil_right_iff] at hRs'
        subst hRs'
        -- CoherentResid [R] [(p0,p1)] = (R.coeff (sideDeg (p0,p1)) = 1)
        have hRlead : R.coeff (CellMenu.sideDeg (p0, p1)) = 1 := hcoh
        have e1 : {r : Fin s → ZMod p // CellCard.ZeroBelow p p0.1 r
              ∧ List.Forall₂ (fun R' pr => SideCondFixed p r R' pr) [R] [(p0, p1)]}
            ≃ {r : Fin s → ZMod p // CellCard.ZeroBelow p p0.1 r
                ∧ SideCondFixed p r R (p0, p1) ∧ True} :=
          Equiv.subtypeEquivRight fun r => by
            rw [List.forall₂_cons]
            simp
        rw [Nat.card_congr e1]
        have hpeel := card_peel_fixed p (pr := (p0, p1)) hw hh (le_of_eq h1) hRdeg hR0
          (fun _ => True) (fun _ _ _ _ => trivial)
          (fun r _ _ => by
            rw [CellCard.rho_ge p _ (show ¬ (p0, p1).2.1 < s from by
              show ¬ p1.1 < s
              omega)]
            exact one_ne_zero)
          (fun r _ _ => by
            rw [CellCard.rho_ge p _ (show ¬ (p0, p1).2.1 < s from by
              show ¬ p1.1 < s
              omega)]
            exact hRlead)
        rw [hpeel]
        have hone : Nat.card {r : Fin s → ZMod p // CellCard.ZeroBelow p (p0, p1).2.1 r ∧ True}
            = 1 := by
          haveI : Unique {r : Fin s → ZMod p // CellCard.ZeroBelow p (p0, p1).2.1 r ∧ True} :=
            { default := ⟨fun _ => 0, fun i _ => rfl, trivial⟩
              uniq := fun r => Subtype.ext (funext fun i => r.2.1 i (by
                show i.1 < p1.1
                have := i.2
                omega)) }
          exact Nat.card_unique
        rw [hone, mul_one]
        simp
  | cons p2 T' ih =>
      intro p0 p1 hc hw hh Rs hRs hcoh
      cases hc with
      | cons h1 h2 h3 h4 =>
        rw [CellMenu.sidePairs_cons₂] at hRs hcoh ⊢
        rw [List.forall₂_cons_right_iff] at hRs
        obtain ⟨R, Rs', ⟨hRdeg, hR0⟩, hRs', rfl⟩ := hRs
        -- Rs' is nonempty (the suffix chain has ≥ 1 side), so extract its head for coherence
        rw [CellMenu.sidePairs_cons₂, List.forall₂_cons_right_iff] at hRs'
        obtain ⟨R₂, Rs'', ⟨hR₂deg, hR₂0⟩, hRs'', rfl⟩ := hRs'
        -- CoherentResid (R :: R₂ :: Rs'') ((p0,p1) :: sidePairs (p1::p2::T'))
        --   = (R.coeff (sideDeg (p0,p1)) = R₂.coeff 0) ∧ CoherentResid (R₂ :: Rs'') (sidePairs (p1::p2::T'))
        rw [CellMenu.sidePairs_cons₂] at hcoh
        obtain ⟨hRcoh, hcoh'⟩ := hcoh
        have hs2 : p2.1 ≤ s := CellMenu.chainOK_le h4
        have e1 : {r : Fin s → ZMod p // CellCard.ZeroBelow p p0.1 r
              ∧ List.Forall₂ (fun R' pr => SideCondFixed p r R' pr) (R :: R₂ :: Rs'')
                  ((p0, p1) :: CellMenu.sidePairs (p1 :: p2 :: T'))}
            ≃ {r : Fin s → ZMod p // CellCard.ZeroBelow p p0.1 r ∧ SideCondFixed p r R (p0, p1)
                ∧ List.Forall₂ (fun R' pr => SideCondFixed p r R' pr) (R₂ :: Rs'')
                    (CellMenu.sidePairs (p1 :: p2 :: T'))} :=
          Equiv.subtypeEquivRight fun r => by
            rw [List.forall₂_cons]
        rw [Nat.card_congr e1]
        have hside_ge : ∀ pr' ∈ CellMenu.sidePairs (p1 :: p2 :: T'), p1.1 ≤ pr'.1.1 := by
          intro pr' hpr'
          obtain ⟨hw', hh', hm1, hm2⟩ :=
            CellMenu.chainOK_side_facts (CellMenu.ChainOK.cons h1 h2 h3 h4) pr' hpr'
          rcases List.mem_cons.mp hm1 with heq | hm1'
          · rw [heq]
          · exact (CellMenu.chainOK_mem_bounds (CellMenu.ChainOK.cons h1 h2 h3 h4) pr'.1 hm1').1.le
        -- the suffix `Q` is the suffix chain's fixed-residual condition
        have hpeel := card_peel_fixed p (pr := (p0, p1)) hw hh
          (show (p0, p1).2.1 ≤ s from by
            show p1.1 ≤ s
            omega) hRdeg hR0
          (fun r => List.Forall₂ (fun R' pr => SideCondFixed p r R' pr) (R₂ :: Rs'')
            (CellMenu.sidePairs (p1 :: p2 :: T')))
          (fun r r' hagree hQr => by
            refine CellCard.forall₂_imp_mem hQr ?_
            intro R' pr' _ hpr'm hcond
            refine (sideCondFixed_congr p ?_).mp hcond
            intro j hj
            exact CellCard.rho_eq_of_agree p hagree (le_trans (hside_ge pr' hpr'm) hj))
          -- hanchor: rho r (p0,p1).2.1 = rho r p1.1 ≠ 0 from the suffix's leftmost SideCondFixed
          (fun r _ hQr => by
            rw [CellMenu.sidePairs_cons₂, List.forall₂_cons] at hQr
            -- hQr.1 : SideCondFixed p r R₂ (p1,p2) ; its second clause is rho r (p1,p2).1.1 ≠ 0
            show CellCard.rho p r p1.1 ≠ 0
            exact hQr.1.2)
          -- hRlead: R.coeff (sideDeg (p0,p1)) = rho r (p0,p1).2.1, via coherence + suffix residual read
          (fun r _ hQr => by
            rw [CellMenu.sidePairs_cons₂, List.forall₂_cons] at hQr
            -- hQr.1 : sidePolyR p r (p1,p2) = R₂ ; its coeff 0 = rho r (p1,p2).1.1 = rho r p1.1
            have hsp2 := hQr.1.1
            have hc0 : R₂.coeff 0 = CellCard.rho p r p1.1 := by
              rw [← hsp2, CellCard.sidePolyR_coeff]
              simp only [Nat.zero_le, if_true, Nat.zero_mul, Nat.add_zero]
            -- R.coeff (sideDeg (p0,p1)) = R₂.coeff 0 (coherence) = rho r p1.1
            show R.coeff (CellMenu.sideDeg (p0, p1)) = CellCard.rho p r p1.1
            rw [hRcoh, hc0])
        -- reassemble the suffix `Forall₂` (deg ∧ ne) over `sidePairs (p1::p2::T')` for `ih`
        have hRsuf : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0)
            (R₂ :: Rs'') (CellMenu.sidePairs (p1 :: p2 :: T')) := by
          rw [CellMenu.sidePairs_cons₂]
          exact List.Forall₂.cons ⟨hR₂deg, hR₂0⟩ hRs''
        rw [hpeel, ih h4 h1 h2 hRsuf hcoh']
        simp only [CellMenu.sidePairs_cons₂, List.map_cons, List.sum_cons]
        rw [pow_add, pow_add]
        ring

/-- **`digCondFixed_count`** — the FIXED-residual DIGIT count of a full menu cell: `p^chainFree`.
Wraps `chain_count_fixed` (dropping the vacuous `ZeroBelow (0,H).1 = ZeroBelow 0` prefix), NO `prodSC`
factor.  Mirror of `CellCard.digCond_count` at the fixed pin. -/
theorem digCondFixed_count {s N : ℕ} {P : List (ℕ × ℕ)} (hP : CellMenu.MenuPath s N P)
    {Rs : List ((ZMod p)[X])}
    (hRs : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
      (CellMenu.sidePairs P))
    (hcoh : CoherentResid p Rs (CellMenu.sidePairs P)) :
    Nat.card {r : Fin s → ZMod p // DigCondFixed p P Rs r} = p ^ CellCard.chainFree P := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1, hpH, hc⟩ := hP
  have e : {r : Fin s → ZMod p // DigCondFixed p ((0, H) :: p1 :: T) Rs r}
      ≃ {r : Fin s → ZMod p // CellCard.ZeroBelow p (0, H).1 r
          ∧ List.Forall₂ (fun R pr => SideCondFixed p r R pr) Rs
              (CellMenu.sidePairs ((0, H) :: p1 :: T))} :=
    Equiv.subtypeEquivRight fun r => by
      unfold DigCondFixed CellCard.ZeroBelow
      constructor
      · exact fun h => ⟨fun i hi => absurd hi (by omega), h⟩
      · exact fun h => h.2
  rw [Nat.card_congr e]
  rw [chain_count_fixed p hc hp1 (by simpa using hpH) hRs hcoh]
  rfl

/-- **`inCellMulti_multi_fixed`** — the MULTI-SIDE fixed-pin membership iff.  For a general menu cell
`mkCell s P sh` and a residual list `Rs` (one per side), `InCellMulti f (mkCell s P sh) Rs` holds iff
`f ∈ InCell` AND the residual reader on each side equals its pinned target (`ResidRefines f P Rs`).
Multi-side generalization of `inCellMulti_single_fixed` (§15). -/
theorem inCellMulti_multi_fixed {s N : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    (hP : CellMenu.MenuPath s N P) (hsh : CellMenu.ShapesFor P sh)
    {f : QuotientBox.monicBox p N s} {Rs : List ((ZMod p)[X])} :
    InCellMulti p f (CellMenu.mkCell s P sh) Rs
      ↔ InCell p f (CellMenu.mkCell s P sh) ∧ CellMenu.ResidRefines p f P Rs := by
  constructor
  · rintro ⟨P', sh', hP', hsh', heq, hm, hres⟩
    obtain ⟨rfl, rfl⟩ := CellMenu.mkCell_injective hP' hP hsh' hsh heq.symm
    exact ⟨⟨_, _, hP', hsh', rfl, hm⟩, hres⟩
  · rintro ⟨⟨P', sh', hP', hsh', heq, hm⟩, hres⟩
    obtain ⟨rfl, rfl⟩ := CellMenu.mkCell_injective hP' hP hsh' hsh heq.symm
    exact ⟨_, _, hP', hsh', rfl, hm, hres⟩

/-- **Bridge (forward)** — `DigCondFixed` from `DigCond` (rho-units) + `ResidRefines` (residual =
target).  Under divisibility, `residualOf f pr = sidePolyR (digits) pr` (`residualOf_eq_sidePolyR`),
so each pinned residual equation becomes the fixed side-polynomial equality; the left-vertex unit
comes from the matching `DigCond` side. -/
theorem digCondFixed_of_bridge {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N P) {sh : List (List (ℕ × ℕ))} (_hsh : CellMenu.ShapesFor P sh)
    (f : QuotientBox.monicBox p N s) {Rs : List ((ZMod p)[X])}
    (hdvd : ∀ i : Fin s, p ^ CellMenu.ceilAt P i.1 ∣ ((f.1.coeff i.1).val))
    (hdc : CellCard.DigCond p P sh
      (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (f.1.coeff i.1)))
    (hres : CellMenu.ResidRefines p f P Rs) :
    DigCondFixed p P Rs
      (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (f.1.coeff i.1)) := by
  unfold DigCondFixed
  unfold CellMenu.ResidRefines at hres
  refine CellCard.forall₂_imp_mem hres ?_
  intro R pr _ hprm hReq
  refine ⟨?_, ?_⟩
  · -- sidePolyR dig pr = R : from residualOf f pr = R and the bridge
    rw [← CellCard.residualOf_eq_sidePolyR p hN hP hprm f hdvd]; exact hReq
  · -- rho dig pr.1.1 ≠ 0 : from the matching DigCond side
    obtain ⟨l, _, hl⟩ := CellMenu.forall₂_mem_right hdc pr hprm
    exact hl.2

/-- **Bridge (back, DigCond) — abstract `Forall₂` form.**  Given, over any side list `ps`,
`Forall₂ (SideCondFixed dig R pr) Rs ps` (fixed residuals) and `Forall₂ (polyShape R = l) Rs sh`
(shape match), the shape `Forall₂ (SideCond dig l pr) sh ps` holds: per side `polyShape (sidePolyR
dig pr) = polyShape Rᵢ = lᵢ`, and the unit is `SideCondFixed`'s clause.  No Newton-polygon data — a
pure three-way `Forall₂` bridge. -/
theorem digCond_of_fixed_aux {s : ℕ} {dig : Fin s → ZMod p} :
    ∀ {Rs : List ((ZMod p)[X])} {ps : List ((ℕ × ℕ) × (ℕ × ℕ))} {sh : List (List (ℕ × ℕ))},
      List.Forall₂ (fun R pr => SideCondFixed p dig R pr) Rs ps →
      List.Forall₂ (fun (R : (ZMod p)[X]) (l : List (ℕ × ℕ)) =>
        CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ))) Rs sh →
      List.Forall₂ (fun l pr => CellCard.SideCond p dig l pr) sh ps := by
  intro Rs ps sh hdcf hRshape
  induction hdcf generalizing sh with
  | nil =>
      rw [List.forall₂_nil_left_iff] at hRshape
      subst hRshape
      exact List.Forall₂.nil
  | @cons R pr Rs' prs' hR hRs' ih =>
      rw [List.forall₂_cons_left_iff] at hRshape
      obtain ⟨l, sh', hRl, hRshape', rfl⟩ := hRshape
      refine List.Forall₂.cons (show CellCard.SideCond p dig l pr from ⟨?_, hR.2⟩) (ih hRshape')
      -- polyShape (sidePolyR dig pr) = polyShape R = l
      show CellMenu.polyShape p (CellCard.sidePolyR p dig pr) = (l : Multiset (ℕ × ℕ))
      rw [hR.1, hRl]

/-- **Bridge (back, DigCond)** — the shape `DigCond` from `DigCondFixed` (fixed residual) + the shape
match `polyShape Rᵢ = lᵢ`.  Applies the abstract bridge `digCond_of_fixed_aux` at `ps = sidePairs P`. -/
theorem digCond_of_fixed {s N : ℕ} (_hN : 0 < N) {P : List (ℕ × ℕ)} (_hP : CellMenu.MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (_hsh : CellMenu.ShapesFor P sh)
    {Rs : List ((ZMod p)[X])}
    (hRshape : List.Forall₂ (fun (R : (ZMod p)[X]) (l : List (ℕ × ℕ)) =>
      CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ))) Rs sh)
    (f : QuotientBox.monicBox p N s)
    (_hdvd : ∀ i : Fin s, p ^ CellMenu.ceilAt P i.1 ∣ ((f.1.coeff i.1).val))
    (hdcf : DigCondFixed p P Rs
      (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (f.1.coeff i.1))) :
    CellCard.DigCond p P sh
      (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (f.1.coeff i.1)) := by
  unfold CellCard.DigCond
  exact digCond_of_fixed_aux p hdcf hRshape

/-- **Bridge (back, ResidRefines)** — `ResidRefines f Rs` from `DigCondFixed` under divisibility:
`residualOf f pr = sidePolyR dig pr = Rᵢ` per side. -/
theorem residRefines_of_fixed {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N P) (f : QuotientBox.monicBox p N s) {Rs : List ((ZMod p)[X])}
    (hdvd : ∀ i : Fin s, p ^ CellMenu.ceilAt P i.1 ∣ ((f.1.coeff i.1).val))
    (hdcf : DigCondFixed p P Rs
      (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (f.1.coeff i.1))) :
    CellMenu.ResidRefines p f P Rs := by
  unfold CellMenu.ResidRefines
  unfold DigCondFixed at hdcf
  refine CellCard.forall₂_imp_mem hdcf ?_
  intro R pr _ hprm hSCF
  -- residualOf f pr = sidePolyR dig pr = R
  rw [CellCard.residualOf_eq_sidePolyR p hN hP hprm f hdvd]
  exact hSCF.1

/-- **`cell_card_raw_fixed`** — the MULTI-SIDE FIXED-ROOT-PIN box count `p^freeExp`.  For a general
menu cell `mkCell s P sh` and a COHERENT residual list `Rs` (per side: `Rᵢ` prime-to-`X`,
`deg ≤ dᵢ`, `polyShape Rᵢ = lᵢ`; rightmost monic, interior leading = next constant), the box
polynomials matching the cell whose side residual reads are exactly `Rs` number `p^(freeExp s N P)` —
the per-side shape-multiplicity `shapeCount lᵢ` of `CellCard.cell_card_raw` is collapsed to `1` on
EVERY side.  Multi-side mirror of `cell_card_raw_fixed_single`; the DIGIT telescope is
`digCondFixed_count` (each side collapsed via `card_sideSet_fixed`). -/
theorem cell_card_raw_fixed {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)} (hP : CellMenu.MenuPath s N P)
    {sh : List (List (ℕ × ℕ))} (hsh : CellMenu.ShapesFor P sh) {Rs : List ((ZMod p)[X])}
    (hRdeg : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
      (CellMenu.sidePairs P))
    (hRshape : List.Forall₂ (fun (R : (ZMod p)[X]) (l : List (ℕ × ℕ)) =>
      CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ))) Rs sh)
    (hcoh : CoherentResid p Rs (CellMenu.sidePairs P)) :
    Nat.card {f : QuotientBox.monicBox p N s //
        InCell p f (CellMenu.mkCell s P sh) ∧ CellMenu.ResidRefines p f P Rs}
      = p ^ CellCard.freeExp s N P := by
  classical
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  -- Step 1: InCell = Matches (drop into `Matches ∧ ResidRefines`)
  have e1 : {f : QuotientBox.monicBox p N s //
        InCell p f (CellMenu.mkCell s P sh) ∧ CellMenu.ResidRefines p f P Rs}
      ≃ {f : QuotientBox.monicBox p N s //
          CellMenu.Matches p f P sh ∧ CellMenu.ResidRefines p f P Rs} :=
    Equiv.subtypeEquivRight fun f => by rw [CellMenu.inCell_mkCell_iff p hP hsh]
  rw [Nat.card_congr e1]
  -- Step 2: (Matches ∧ ResidRefines) = (divisibility ∧ DigCondFixed), through coeffEquiv
  have e2 : {f : QuotientBox.monicBox p N s //
        CellMenu.Matches p f P sh ∧ CellMenu.ResidRefines p f P Rs}
      ≃ {a : Fin s → ZMod (p ^ N) //
          (∀ i : Fin s, p ^ CellMenu.ceilAt P i.1 ∣ ((a i).val))
            ∧ DigCondFixed p P Rs
                (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (a i))} :=
    (CellCard.coeffEquiv p N s hN).subtypeEquiv fun f => by
      rw [CellCard.matches_iff p hN hP hsh f]
      constructor
      · rintro ⟨⟨hdvd, hdc⟩, hres⟩
        refine ⟨hdvd, ?_⟩
        -- from ResidRefines: residualOf f pr = R_i ; bridge to sidePolyR dig pr = R_i (hdvd)
        -- from DigCond: rho dig pr.1.1 ≠ 0 per side.  Assemble DigCondFixed.
        exact digCondFixed_of_bridge p hN hP hsh f hdvd hdc hres
      · rintro ⟨hdvd, hdcf⟩
        refine ⟨⟨hdvd, ?_⟩, ?_⟩
        · exact digCond_of_fixed p hN hP hsh hRshape f hdvd hdcf
        · exact residRefines_of_fixed p hN hP f hdvd hdcf
  rw [Nat.card_congr e2]
  -- Step 3: pull the divisibility into the coordinate types
  have e3 : {a : Fin s → ZMod (p ^ N) //
        (∀ i : Fin s, p ^ CellMenu.ceilAt P i.1 ∣ ((a i).val))
          ∧ DigCondFixed p P Rs (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (a i))}
      ≃ {b : ∀ i : Fin s, {x : ZMod (p ^ N) // p ^ CellMenu.ceilAt P i.1 ∣ x.val} //
          DigCondFixed p P Rs (fun i : Fin s => CellCard.digit p N (CellMenu.ceilAt P i.1) (b i).1)} :=
    { toFun := fun a => ⟨fun i => ⟨a.1 i, a.2.1 i⟩, a.2.2⟩
      invFun := fun b => ⟨fun i => (b.1 i).1, fun i => (b.1 i).2, b.2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr e3]
  -- Step 4: per-coordinate digit fibering
  rw [CellCard.card_pi_fiber
    (fun (i : Fin s) (x : {x : ZMod (p ^ N) // p ^ CellMenu.ceilAt P i.1 ∣ x.val}) =>
      CellCard.digit p N (CellMenu.ceilAt P i.1) x.1)
    (fun i => p ^ (N - CellMenu.ceilAt P i.1 - 1))
    (fun i c => CellCard.card_digit_fiber p (by
      have := CellCard.menuPath_ceilAt_le hP i.2
      omega) c)
    (DigCondFixed p P Rs)]
  -- Step 5: the fixed digit count and the exponent assembly
  rw [digCondFixed_count p hP hRdeg hcoh, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => N - CellMenu.ceilAt P j - 1) s]
  have hsum : ∑ i ∈ Finset.range s, (N - CellMenu.ceilAt P i - 1)
      = ∑ i ∈ Finset.range s, (N - 1 - CellMenu.ceilAt P i) :=
    Finset.sum_congr rfl fun i _ => by omega
  rw [hsum]
  unfold CellCard.freeExp
  rw [pow_add]
  ring

/-- **`card_inCellMulti_fixedpin_multiside`** — the MULTI-SIDE FIXED-ROOT-PIN classifier fiber count
`p^freeExp`.  For a general multi-side menu cell `mkCell s P sh`, with the residual pinned to a
COHERENT list `Rs` (per side: `Rᵢ` prime-to-`X`, `deg ≤ dᵢ`, `polyShape Rᵢ = lᵢ`; rightmost monic,
interior leading = next constant), the `InCellMulti` fiber has exactly `p^(freeExp s N P)` elements —
the `prodSC = Π shapeCount lᵢ` shape-multiplicity is collapsed to `1` on EVERY side by fixing the
residual POLYNOMIAL.  Multi-side generalization of `card_inCellMulti_fixedpin_fiber_single` (§15):
`InCellMulti f (mkCell s P sh) Rs ↔ InCell f ∧ ResidRefines f P Rs` (`inCellMulti_multi_fixed`), then
`cell_card_raw_fixed`. -/
theorem card_inCellMulti_fixedpin_multiside {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N P) {sh : List (List (ℕ × ℕ))} (hsh : CellMenu.ShapesFor P sh)
    {Rs : List ((ZMod p)[X])}
    (hRdeg : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
      (CellMenu.sidePairs P))
    (hRshape : List.Forall₂ (fun (R : (ZMod p)[X]) (l : List (ℕ × ℕ)) =>
      CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ))) Rs sh)
    (hcoh : CoherentResid p Rs (CellMenu.sidePairs P)) :
    Nat.card {f : QuotientBox.monicBox p N s //
        InCellMulti p f (CellMenu.mkCell s P sh) Rs}
      = p ^ CellCard.freeExp s N P := by
  have e : {f : QuotientBox.monicBox p N s // InCellMulti p f (CellMenu.mkCell s P sh) Rs}
      ≃ {f : QuotientBox.monicBox p N s //
          InCell p f (CellMenu.mkCell s P sh) ∧ CellMenu.ResidRefines p f P Rs} :=
    Equiv.subtypeEquivRight fun f => inCellMulti_multi_fixed p hP hsh
  rw [Nat.card_congr e, cell_card_raw_fixed p hN hP hsh hRdeg hRshape hcoh]

/-! ### 15c. **LEG 2 node identity + case-A structural gate.**

`card_inCellMulti_fixedpin_multiside` gives the fixed-pin fiber count `p^freeExp` for ANY multi-side
cell.  Meeting the em-square exponent identity `p^freeExp · p^X = Π coset` (`image_card_eq_pow_freeExp`
+ `card_inCellMulti_node_of_card_le`) closes the multi-side node identity outright, exactly as
`gate_node_C_closed` does at the single side.  The case-A gate is the 2-side instance
(`p=2, N=5, s=6`, path `[(0,4),(2,2),(6,0)]`, `prodSC = 1`): its fixed-pin fiber `= 2^13 = 8192`
matches `#imageSet` (the 8192-route), so the fixed pin coincides with the tautological pin (prodSC=1)
and the node identity is `gate_node_A` (`8192 · 2⁴ = Π coset`). -/

/-- **LEG 2 node identity — the multi-side fixed-pin node identity, CLOSED given the exponent
identity.**  For a multi-side cell whose fixed-pin fiber count is `p^fe` (`card_inCellMulti_fixedpin_multiside`)
and whose block chain satisfies the em-square exponent identity `p^fe · p^X = Π coset`, the node
identity `#{fixed-pin InCellMulti fiber} · p^X = Π coset` holds OUTRIGHT — the multi-side analogue of
`gate_node_C_closed`'s structure.  Both count facts feed `card_inCellMulti_node_of_card_le`
(`#fiber = p^fe = #imageSet` forces the em-square law verbatim). -/
theorem node_identity_fixedpin_multiside {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : CellMenu.MenuPath s N P) {sh : List (List (ℕ × ℕ))} (hsh : CellMenu.ShapesFor P sh)
    {Rs : List ((ZMod p)[X])}
    (hRdeg : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
      (CellMenu.sidePairs P))
    (hRshape : List.Forall₂ (fun (R : (ZMod p)[X]) (l : List (ℕ × ℕ)) =>
      CellMenu.polyShape p R = (l : Multiset (ℕ × ℕ))) Rs sh)
    (hcoh : CoherentResid p Rs (CellMenu.sidePairs P))
    {l : List (BlockProduct.Block p N)} {X : ℕ} (_h : BlockProduct.GoodChain l X)
    (hexp : p ^ CellCard.freeExp s N P * p ^ X = (l.map fun b => Nat.card b.coset).prod) :
    Nat.card {f : QuotientBox.monicBox p N s // InCellMulti p f (CellMenu.mkCell s P sh) Rs} * p ^ X
      = (l.map fun b => Nat.card b.coset).prod := by
  rw [card_inCellMulti_fixedpin_multiside p hN hP hsh hRdeg hRshape hcoh, hexp]

/-- **LEG 2 GATE (case A — the 2-side fixed-pin fiber count `8192 = 2^13`).**  Case A's cell is
2-side (`p=2, N=5, s=6`, path `[(0,4),(2,2),(6,0)]`, `prodSC = 1`).  For ANY coherent pinned residual
list `Rs` of its two sides matching the case-A shapes `sh`, the multi-side fixed-pin fiber count is
`2^(freeExp 6 5 [(0,4),(2,2),(6,0)])`; with `freeExp = 13` this is `8192` — the 8192-route
cross-check (`gate_fiber_A`).  Confirms the multi-side telescope reproduces the single-cell count at
the 2-side gate; a concrete numeric `Rs` for the two case-A sides is built the same way `residC` is
for case C, and is the classifier gate layer's to supply. -/
theorem card_inCellMulti_fixedpin_gateA {sh : List (List (ℕ × ℕ))}
    (hsh : CellMenu.ShapesFor [(0, 4), (2, 2), (6, 0)] sh) {Rs : List ((ZMod 2)[X])}
    (hRdeg : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0) Rs
      (CellMenu.sidePairs [(0, 4), (2, 2), (6, 0)]))
    (hRshape : List.Forall₂ (fun (R : (ZMod 2)[X]) (l : List (ℕ × ℕ)) =>
      CellMenu.polyShape 2 R = (l : Multiset (ℕ × ℕ))) Rs sh)
    (hcoh : CoherentResid 2 Rs (CellMenu.sidePairs [(0, 4), (2, 2), (6, 0)]))
    (hfe : CellCard.freeExp 6 5 [(0, 4), (2, 2), (6, 0)] = 13) :
    Nat.card {f : QuotientBox.monicBox 2 5 6 //
        InCellMulti 2 f (CellMenu.mkCell 6 [(0, 4), (2, 2), (6, 0)] sh) Rs}
      = 8192 := by
  have hP : CellMenu.MenuPath 6 5 [(0, 4), (2, 2), (6, 0)] :=
    ⟨4, (2, 2), [(6, 0)], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      CellMenu.ChainOK.cons (by norm_num) (by norm_num) (by decide) (CellMenu.ChainOK.nil rfl rfl)⟩
  rw [card_inCellMulti_fixedpin_multiside 2 (by norm_num) hP hsh hRdeg hRshape hcoh, hfe]
  norm_num

/-! ### 15d. Case A — the MULTI-SIDE FIXED-ROOT-PIN node identity, CLOSED OUTRIGHT.

The concrete case-A pinned residual list `Rs = [residA, residA]`, the case-C analogue at the
2-side gate.  Case A's cell is `mkCell 6 [(0,4),(2,2),(6,0)] [[(1,2)],[(1,2)]]` (`p=2, N=5, s=6`):
a 2-side polygon, side 1 `((0,4),(2,2))` slope `−1` (`sideDeg 2`), side 2 `((2,2),(6,0))` slope
`−1/2` (`sideDeg 2`).  Each side has shape `[(1,2)]` (one linear root to power 2), so
`shapeCount [(1,2)] = p − 1 = 1` on EVERY side and `prodSC = 1` — the fixed pin coincides with the
tautological pin.  Over `ZMod 2` the only unit root is `1`, so the concrete per-side residual is
`residA = (X+1)²`.  `CoherentResid` holds: side 2 (rightmost) is MONIC (`coeff (sideDeg) = 1`), and
the interior vertex `(2,2)`'s shared-digit coherence reads `residA.coeff (sideDeg) = 1 =
residA.coeff 0` (both sides' `(X+1)²` meet at leading = constant = `1`).  Feeding this to
`node_identity_fixedpin_multiside`/`card_inCellMulti_fixedpin_multiside` closes the case-A multi-side
node identity OUTRIGHT, exactly as `gate_node_C_closed` does at case C. -/

/-- The concrete case-A per-side fixed residual `(X+1)²` over `ZMod 2` (shape `[(1,2)]`, one linear
root `1` to power `2`; the same residual is the owner on BOTH sides — the interior digit is the unit
`1`). -/
noncomputable def residA : (ZMod 2)[X] := (X + C (1 : ZMod 2)) ^ 2

/-- `polyShape residA = {(1,2)}` — one linear factor of multiplicity `2` (`polyShape_pow_linear`). -/
theorem residA_shape : CellMenu.polyShape 2 residA = ({(1, 2)} : Multiset (ℕ × ℕ)) := by
  rw [residA]; exact CellMenu.polyShape_pow_linear 2 (1 : ZMod 2) (by norm_num)

theorem residA_deg1 : residA.natDegree ≤ CellMenu.sideDeg ((0, 4), (2, 2)) := by
  rw [show CellMenu.sideDeg ((0, 4), (2, 2)) = 2 from by decide, residA]; compute_degree

theorem residA_deg2 : residA.natDegree ≤ CellMenu.sideDeg ((2, 2), (6, 0)) := by
  rw [show CellMenu.sideDeg ((2, 2), (6, 0)) = 2 from by decide, residA]; compute_degree

/-- `residA` is monic at side 1's `sideDeg` (leading coeff `1`). -/
theorem residA_lead1 : residA.coeff (CellMenu.sideDeg ((0, 4), (2, 2))) = 1 := by
  rw [show CellMenu.sideDeg ((0, 4), (2, 2)) = 2 from by decide, residA]; compute_degree!

/-- `residA` is monic at side 2's `sideDeg` (the RIGHTMOST side — `CoherentResid`'s monic tip). -/
theorem residA_lead2 : residA.coeff (CellMenu.sideDeg ((2, 2), (6, 0))) = 1 := by
  rw [show CellMenu.sideDeg ((2, 2), (6, 0)) = 2 from by decide, residA]; compute_degree!

/-- `residA.coeff 0 = 1` — the interior-vertex shared digit (`= residA_lead1`, coherence). -/
theorem residA_const : residA.coeff 0 = 1 := by
  rw [residA, Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  decide

theorem residA_0ne : residA.coeff 0 ≠ 0 := by rw [residA_const]; decide

/-- Case A's `ShapesFor`: both sides carry shape `[(1,2)]`. -/
theorem residA_shapesfor : CellMenu.ShapesFor [(0, 4), (2, 2), (6, 0)] [[(1, 2)], [(1, 2)]] := by
  show List.Forall₂ _ [[(1, 2)], [(1, 2)]] (CellMenu.sidePairs [(0, 4), (2, 2), (6, 0)])
  exact List.Forall₂.cons (by decide) (List.Forall₂.cons (by decide) List.Forall₂.nil)

/-- Case A's per-side degree/nonvanishing datum for `Rs = [residA, residA]`. -/
theorem residA_hRdeg : List.Forall₂ (fun R pr => R.natDegree ≤ CellMenu.sideDeg pr ∧ R.coeff 0 ≠ 0)
    [residA, residA] (CellMenu.sidePairs [(0, 4), (2, 2), (6, 0)]) := by
  show List.Forall₂ _ [residA, residA] [((0, 4), (2, 2)), ((2, 2), (6, 0))]
  exact List.Forall₂.cons ⟨residA_deg1, residA_0ne⟩
    (List.Forall₂.cons ⟨residA_deg2, residA_0ne⟩ List.Forall₂.nil)

/-- Case A's per-side shape datum for `Rs = [residA, residA]`. -/
theorem residA_hRshape : List.Forall₂ (fun (R : (ZMod 2)[X]) (l : List (ℕ × ℕ)) =>
    CellMenu.polyShape 2 R = (l : Multiset (ℕ × ℕ))) [residA, residA] [[(1, 2)], [(1, 2)]] :=
  List.Forall₂.cons residA_shape (List.Forall₂.cons residA_shape List.Forall₂.nil)

/-- **`CoherentResid` WITNESSED at case A.**  For `Rs = [residA, residA]` on
`sidePairs [(0,4),(2,2),(6,0)]`: the rightmost side is monic (`residA.coeff (sideDeg) = 1`,
`residA_lead2`) and the interior vertex `(2,2)`'s shared-digit coherence reads
`residA.coeff (sideDeg) = residA.coeff 0` (both `1`, `residA_lead1`/`residA_const`). -/
theorem residA_hcoh :
    CoherentResid 2 [residA, residA] (CellMenu.sidePairs [(0, 4), (2, 2), (6, 0)]) := by
  show CoherentResid 2 [residA, residA] [((0, 4), (2, 2)), ((2, 2), (6, 0))]
  exact ⟨by rw [residA_lead1, residA_const], residA_lead2⟩

/-- Case A's `MenuPath` (`p=2, N=5, s=6`, path `[(0,4),(2,2),(6,0)]`). -/
theorem residA_menuPath : CellMenu.MenuPath 6 5 [(0, 4), (2, 2), (6, 0)] :=
  ⟨4, (2, 2), [(6, 0)], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
    CellMenu.ChainOK.cons (by norm_num) (by norm_num) (by decide) (CellMenu.ChainOK.nil rfl rfl)⟩

/-- **Case-A FIXED-ROOT-PIN fiber count = `8192`, proven OUTRIGHT.**  The genuine classifier
`InCellMulti` fiber for case A with the residual pinned to the concrete coherent list
`[residA, residA]` (each side `(X+1)²`) has exactly `2^(freeExp 6 5 [(0,4),(2,2),(6,0)]) = 2^13 =
8192` elements.  The 2-side instance of `card_inCellMulti_fixedpin_multiside` with the concrete `Rs`,
the case-A analogue of `card_inCellMulti_fixedpin_caseC`.  Since `prodSC = 1` the fixed pin coincides
with the tautological pin, so `8192` matches the `#imageSet`/tautological-pin count (the 8192-route,
`gate_fiber_A`). -/
theorem card_inCellMulti_fixedpin_caseA :
    Nat.card {f : QuotientBox.monicBox 2 5 6 //
        InCellMulti 2 f (CellMenu.mkCell 6 [(0, 4), (2, 2), (6, 0)] [[(1, 2)], [(1, 2)]])
          [residA, residA]}
      = 8192 := by
  rw [card_inCellMulti_fixedpin_multiside 2 (by norm_num) residA_menuPath residA_shapesfor
      residA_hRdeg residA_hRshape residA_hcoh,
    show CellCard.freeExp 6 5 [(0, 4), (2, 2), (6, 0)] = 13 from by decide]
  norm_num

/-- **Gate A multi-side node identity — CLOSED OUTRIGHT** (`p=2, N=5`): the FIXED-ROOT-PIN classifier
`InCellMulti` fiber count `8192 = 2^13 = 2^freeExp` (`card_inCellMulti_fixedpin_caseA`, the concrete
2-side pinned residual `[residA, residA]`) times the torsor `2⁴` equals the block-coset product
(`gateA_coset_product`).  The multi-side (`node_identity_fixedpin_multiside`) analogue of
`gate_node_C_closed`, closed OUTRIGHT with no ShapesFor/CoherentResid hypotheses — those are
discharged by the concrete `residA` witnesses.  Case A is `prodSC = 1`, so the fixed pin coincides
with the tautological pin, agreeing with `gate_node_A` (the 8192-route cross-check). -/
theorem gate_node_A_multiside_closed :
    Nat.card {f : QuotientBox.monicBox 2 5 6 //
        InCellMulti 2 f (CellMenu.mkCell 6 [(0, 4), (2, 2), (6, 0)] [[(1, 2)], [(1, 2)]])
          [residA, residA]} * 2 ^ 4
      = Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 1 1 1 //
          RestartEquiv.FreshClusterPattern 2 5 1 2 1 β}
        * Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 2 1 1 //
            RestartEquiv.FreshClusterPattern 2 5 2 2 1 β} := by
  rw [card_inCellMulti_fixedpin_caseA]
  exact BlockProduct.gateA_coset_product.symm

/-- **8192-route cross-check.**  The case-A fixed-pin fiber count meets the tautological
`prodSC = 1` count `8192` (`gate_fiber_A`): `#{fixed-pin InCellMulti fiber} · 2⁴ = 8192 · 2⁴`. -/
theorem gate_node_A_multiside_crosscheck :
    Nat.card {f : QuotientBox.monicBox 2 5 6 //
        InCellMulti 2 f (CellMenu.mkCell 6 [(0, 4), (2, 2), (6, 0)] [[(1, 2)], [(1, 2)]])
          [residA, residA]} * 2 ^ 4 = 8192 * 2 ^ 4 := by
  rw [card_inCellMulti_fixedpin_caseA]

/-! ### NAMED (not yet formalized) — `product_matches_mixed`.

A general mixed-block `⊇`/`Matches` statement unifying `product_matches_klist` (distinct-slope sides,
off-block unit drop via `offBlock_unit_on_side`) with `product_matches_sameside` (same-side coprime
siblings, residual multiplication into the union shape via `sideMatch_shape_mul`) for a cell with
BOTH distinct-slope sides AND same-side coprime siblings.  Its per-side `Forall₂` predicate must
BRANCH — a distinct-slope side reads `residualOf = R · U` (`U` unit), a same-side-sibling side reads
`residualOf = R_A · R_B` (both non-units, coprime, shapes UNION) — which is a strictly heavier fold
than either single leg.  Per task banking directive: the case-A concretization is delivered; the
mixed statement is NAMED here as `product_matches_mixed` and deferred. -/

end LeanUrat.OM.ProductTheorem

