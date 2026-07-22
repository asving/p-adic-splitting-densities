/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ChainMenu

/-!
# ChainMenuU — Wave W6q-a: the general-`p` splitU counting core (`n = 2`)

**Provenance.** `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §1.1/§1.2 (the general-`q` stratum
table and per-family masses) + §1.5 (the splitU delta) + §2-W6q-a, ground truth
`notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (ACCEPTED, general-`q` throughout). This
module is the PURE COUNTING content of the splitU family and the general-`p` order-0
residual-shape cells; it is purely additive over `OM/ChainMenu.lean` (whose patterns it
mirrors) and `OM/RecenterBox.lean` (whose `StratumPair`/`descendPair` staircase machinery it
consumes as-is).

## The objects

* **The splitU pool** `rootedPairs p`: residual digit pairs `(w̄₀, w̄₁)` whose quadratic
  `z² + w̄₁z + w̄₀` has TWO DISTINCT roots, BOTH NONZERO — the blueprint §1.1 splitU row.
  Count `(q−1)(q−2)/2`; HONESTLY EMPTY at `q = 2` (`rootedPairs_two_empty` — the W1
  honest-empty pattern, note Claim 4.3).
* **The splitU leaf** `LeafPairU m`: the even-height-`2m` staircase read with residual in the
  splitU pool — EXACTLY the `ChainMenu.LeafPair (.inert m)` digit shape with the pool swapped
  (`noRootPairs → rootedPairs`); keyed σ = `{(1,1),(1,1)}` (the keying itself is W6q-d's
  business). `leafNeedU = 2m + 1`.
* **The splitU chain** `ChainPairU ms m`: LITERALLY `ChainMenu.ChainPair`'s recursion with the
  leaf clause swapped — descend steps via `RecenterBox.StratumPair` + `descendPair`, closed
  form `(p−1)^depth · leafCountU` above the threshold `2·Σms + leafNeedU` (the per-step engine
  `card_exists_eq_mul`/`card_step`/`stratumPair_unit_unique` is INSTANTIATED from the banked
  general lemmas; only the induction wrapper is re-run, since `ChainPair` hard-codes the
  `ChainLeaf` inductive).
* **General-`p` order-0 cells** (replacing W6's `p = 2` digit cells `SepSplitCell`/
  `SepInertCell` by residual SHAPES): `Ord0SplitCell` (residual has two distinct roots, any —
  pool `splitResPairs p`, count `q(q−1)/2`) and `Ord0InertCell` (residual root-free — the pool
  IS `ChainMenu.noRootPairs p`, count `q(q−1)/2`). `p = 2` recovery gates tie them to the W6
  digit conditions (`ā₀ = 0 ∧ ā₁ = 1` resp. `ā₀ = 1 ∧ ā₁ = 1`) — stated on the raw
  divisibility conditions (NOT via a `SeriesAssembly` import, to keep the footprint light;
  `SeriesAssembly.SepSplitCell/SepInertCell` are definitionally these conditions, so W6q-c's
  tie is immediate).
* **The residual trichotomies** (the W6q-b decision-tree inputs): at `w̄₀ ≠ 0` every pair is
  EXACTLY ONE of root-free / two-distinct-nonzero-roots / unit-square `(c̃², −2c̃)` (the
  `StratumPair` residual form) — blueprint §1.1 (L): `q(q−1)/2 + (q−1)(q−2)/2 + (q−1) = q(q−1)`;
  and over ALL pairs: two-distinct-roots / root-free / square (any center) —
  `q(q−1)/2 + q(q−1)/2 + q = q²`. Covers and pairwise disjointness are separate consumable
  lemmas; the card identities are proved from them.

## Census anchors (blueprint §0/§1.2; machine-checked in the `GateCensus` section)

* `q = 3`: `(rootedPairs 3).card = 1` (the hand-enumerated splitU pool `{(z−1)(z−2)}` ✓),
  `(noRootPairs 3).card = 3`, `(splitResPairs 3).card = 3`.
* `q = 2`: `rootedPairs 2 = ∅` (splitU honestly empty — the `q = 2` ledger line),
  `(noRootPairs 2).card = 1`, `(splitResPairs 2).card = 1`, and the order-0 cells decode to
  the W6 digit cells.

**Counting-route note.** `card_rootedPairs` is derived from the unit-constant PARTITION
(cover + pairwise disjointness + the banked `two_mul_card_noRootPairs`), not by a separate
Sym2/Vieta image count — the partition lemmas are required deliverables anyway and the banked
`p(p−1)` inert-pool count already carries the Vieta/Sym2 content. Same route for
`card_splitResPairs` via the all-pairs partition.

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ChainMenuU

open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox
open LeanUrat.OM.ChainMenu

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. Quadratic-residual root algebra (the shared field facts)

All monic-quadratic facts below are stated on a coefficient pair `s = (s₁, s₂)` reading the
quadratic as `z² + s₂·z + s₁` — the SAME convention as `ChainMenu.noRootPairs` (constant digit
first, linear digit second). -/

/-- **The companion root**: if `r` is a root of `z² + s₂z + s₁`, so is `−s₂ − r`. -/
theorem companion_root {s₁ s₂ r : ZMod p} (hr : r ^ 2 + s₂ * r + s₁ = 0) :
    (-s₂ - r) ^ 2 + s₂ * (-s₂ - r) + s₁ = 0 := by
  linear_combination hr

/-- **Vieta from two distinct roots**: `s₁ = r·r'` and `s₂ = −(r + r')`. -/
theorem root_pair_vieta {s₁ s₂ r r' : ZMod p} (hne : r ≠ r')
    (hr : r ^ 2 + s₂ * r + s₁ = 0) (hr' : r' ^ 2 + s₂ * r' + s₁ = 0) :
    s₁ = r * r' ∧ s₂ = -(r + r') := by
  have hsum : r + r' + s₂ = 0 := by
    have hd : (r - r') * (r + r' + s₂) = 0 := by linear_combination hr - hr'
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (by linear_combination h) hne
    · exact h
  exact ⟨by linear_combination hr - r * hsum, by linear_combination hsum⟩

/-- **The double-root collapse**: a root `r` with coincident companion forces the square shape
`(s₁, s₂) = (r², −2r)` — the `(z − c̃)²` residual in digit-pair form. -/
theorem square_of_double_root {s₁ s₂ r : ZMod p} (hr : r ^ 2 + s₂ * r + s₁ = 0)
    (heq : -s₂ - r = r) : s₁ = r ^ 2 ∧ s₂ = -(2 * r) := by
  have hs₂ : s₂ = -(2 * r) := by linear_combination -heq
  exact ⟨by linear_combination hr - r * hs₂, hs₂⟩

/-- **A square residual `(c², −2c)` has ONLY the root `c`** (the `(z−c)²` read; uniform in `p`,
including `p = 2`). -/
theorem root_of_square {c r : ZMod p} (hr : r ^ 2 + -(2 * c) * r + c ^ 2 = 0) : r = c := by
  have hd : (r - c) * (r - c) = 0 := by linear_combination hr
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hd)

/-- The square-residual digit map `c ↦ (c², −2c)` is injective (the `stratumPair_unit_unique`
field algebra, center-level). -/
theorem square_map_injective : Function.Injective (fun c : ZMod p => (c ^ 2, -(2 * c))) := by
  intro c c' h
  have h1 : c ^ 2 = c' ^ 2 := congrArg Prod.fst h
  have h2 : -(2 * c) = -(2 * c') := congrArg Prod.snd h
  have hd : (c - c') * (c - c') = 0 := by linear_combination h1 + c' * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hd)

/-! ## 2. The pools: splitU (`rootedPairs`), order-0 split (`splitResPairs`), squares

Pool convention (as in `ChainMenu` §2): a pool is a `Finset (ZMod p × ZMod p)` of digit pairs
`(w̄₀, w̄₁)` = (constant, linear). The pools are COMPUTABLE (no `Classical` filter), so the
`p = 2, 3` census gates below are `decide`-checked. -/

/-- **The splitU pool** (blueprint §1.1 splitU row): residual pairs whose quadratic
`z² + w̄₁z + w̄₀` has two DISTINCT roots, BOTH NONZERO. Count `(p−1)(p−2)/2`
(`card_rootedPairs`); empty at `p = 2` (`rootedPairs_two_empty`). -/
def rootedPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun s => ∃ r r' : ZMod p, r ≠ r' ∧ r ≠ 0 ∧ r' ≠ 0
    ∧ r ^ 2 + s.2 * r + s.1 = 0 ∧ r' ^ 2 + s.2 * r' + s.1 = 0)

theorem mem_rootedPairs {s : ZMod p × ZMod p} :
    s ∈ rootedPairs p ↔ ∃ r r' : ZMod p, r ≠ r' ∧ r ≠ 0 ∧ r' ≠ 0
      ∧ r ^ 2 + s.2 * r + s.1 = 0 ∧ r' ^ 2 + s.2 * r' + s.1 = 0 := by
  rw [rootedPairs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩

/-- A splitU pair has nonzero constant digit: `w̄₀ = r·r' ≠ 0` (Vieta). -/
theorem rootedPairs_fst_ne_zero {s : ZMod p × ZMod p} (h : s ∈ rootedPairs p) : s.1 ≠ 0 := by
  obtain ⟨r, r', hne, hr0, hr'0, hr, hr'⟩ := (mem_rootedPairs p).mp h
  rw [(root_pair_vieta p hne hr hr').1]
  exact mul_ne_zero hr0 hr'0

/-- **The `q = 2` honest emptiness** (blueprint §1.1 (L): the splitU pool polynomial
`(q−1)(q−2)/2` vanishes at `q = 2`; note Claim 4.3's universal-polynomial emptiness). -/
theorem rootedPairs_two_empty : rootedPairs 2 = ∅ := by decide

/-- **The order-0 split pool** (blueprint §1.1 order-0 split cell): residual pairs whose
quadratic has two DISTINCT roots, any (0 allowed). Count `p(p−1)/2` (`card_splitResPairs`). -/
def splitResPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun s => ∃ r r' : ZMod p, r ≠ r'
    ∧ r ^ 2 + s.2 * r + s.1 = 0 ∧ r' ^ 2 + s.2 * r' + s.1 = 0)

theorem mem_splitResPairs {s : ZMod p × ZMod p} :
    s ∈ splitResPairs p ↔ ∃ r r' : ZMod p, r ≠ r'
      ∧ r ^ 2 + s.2 * r + s.1 = 0 ∧ r' ^ 2 + s.2 * r' + s.1 = 0 := by
  rw [splitResPairs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩

/-- The splitU pool sits inside the order-0 split pool (drop the nonzero-roots condition). -/
theorem rootedPairs_subset_splitResPairs : rootedPairs p ⊆ splitResPairs p := by
  intro s hs
  obtain ⟨r, r', hne, -, -, hr, hr'⟩ := (mem_rootedPairs p).mp hs
  exact (mem_splitResPairs p).mpr ⟨r, r', hne, hr, hr'⟩

/-- **The unit-square pool**: the descend/`StratumPair` residual shapes `(c̃², −2c̃)`,
`c̃ ∈ F_pˣ` — EXACTLY the digit pairs pinned by `RecenterBox.StratumPair`'s (S2). Count `p−1`. -/
def squareUnitPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.image (fun c : (ZMod p)ˣ => (((c : ZMod p)) ^ 2, -(2 * (c : ZMod p))))

theorem mem_squareUnitPairs {s : ZMod p × ZMod p} :
    s ∈ squareUnitPairs p
      ↔ ∃ c : (ZMod p)ˣ, s.1 = ((c : ZMod p)) ^ 2 ∧ s.2 = -(2 * (c : ZMod p)) := by
  rw [squareUnitPairs, Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact ⟨c, rfl, rfl⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, Finset.mem_univ c, (Prod.ext_iff.mpr ⟨h1.symm, h2.symm⟩)⟩

theorem card_squareUnitPairs : (squareUnitPairs p).card = p - 1 := by
  rw [squareUnitPairs, Finset.card_image_of_injective _
    (fun c c' h => Units.ext (square_map_injective p h)), Finset.card_univ, ZMod.card_units p]

/-- **The all-squares pool**: `(c̄², −2c̄)` for EVERY center `c̄ ∈ F_p` (the order-0 cluster
locus `(x − c̄)²`, `c̄ = 0` included). Count `p`. -/
def squareAllPairs : Finset (ZMod p × ZMod p) :=
  Finset.univ.image (fun c : ZMod p => (c ^ 2, -(2 * c)))

theorem mem_squareAllPairs {s : ZMod p × ZMod p} :
    s ∈ squareAllPairs p ↔ ∃ c : ZMod p, s.1 = c ^ 2 ∧ s.2 = -(2 * c) := by
  rw [squareAllPairs, Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact ⟨c, rfl, rfl⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, Finset.mem_univ c, (Prod.ext_iff.mpr ⟨h1.symm, h2.symm⟩)⟩

theorem card_squareAllPairs : (squareAllPairs p).card = p := by
  rw [squareAllPairs, Finset.card_image_of_injective _ (square_map_injective p),
    Finset.card_univ, ZMod.card]

/-! ## 3. Pairwise disjointness (the pinned residual reads conflict) -/

/-- SplitU vs inert pool: a rooted pair is not root-free. -/
theorem rootedPairs_disjoint_noRootPairs : Disjoint (rootedPairs p) (noRootPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨r, -, -, -, -, hr, -⟩ := (mem_rootedPairs p).mp hs
  exact (mem_noRootPairs p).mp hs' r hr

/-- **A splitU pair is NOT the descend square residual** `(c̃², −2c̃)` — two distinct roots vs
the double root at `c̃`. Stated in `RecenterBox.StratumPair`'s exact digit form (the (S2)
values), the shape the W6q-b covering consumes. -/
theorem rootedPairs_not_squareUnit {s : ZMod p × ZMod p} (h : s ∈ rootedPairs p)
    (c : (ZMod p)ˣ) : ¬(s.1 = ((c : ZMod p)) ^ 2 ∧ s.2 = -(2 * (c : ZMod p))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨r, r', hne, -, -, hr, hr'⟩ := (mem_rootedPairs p).mp h
  rw [h1, h2] at hr hr'
  exact hne ((root_of_square p hr).trans (root_of_square p hr').symm)

theorem rootedPairs_disjoint_squareUnitPairs :
    Disjoint (rootedPairs p) (squareUnitPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨c, h1, h2⟩ := (mem_squareUnitPairs p).mp hs'
  exact rootedPairs_not_squareUnit p hs c ⟨h1, h2⟩

/-- Inert pool vs unit squares: the square has the root `c̃`. -/
theorem noRootPairs_disjoint_squareUnitPairs :
    Disjoint (noRootPairs p) (squareUnitPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨c, h1, h2⟩ := (mem_squareUnitPairs p).mp hs'
  refine (mem_noRootPairs p).mp hs ((c : ZMod p)) ?_
  rw [h1, h2]
  ring

/-- Order-0 split pool vs inert pool. -/
theorem splitResPairs_disjoint_noRootPairs : Disjoint (splitResPairs p) (noRootPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨r, -, -, hr, -⟩ := (mem_splitResPairs p).mp hs
  exact (mem_noRootPairs p).mp hs' r hr

/-- An order-0 split pair is not a square residual (any center): distinct vs double root. -/
theorem splitResPairs_not_squareAll {s : ZMod p × ZMod p} (h : s ∈ splitResPairs p)
    (c : ZMod p) : ¬(s.1 = c ^ 2 ∧ s.2 = -(2 * c)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨r, r', hne, hr, hr'⟩ := (mem_splitResPairs p).mp h
  rw [h1, h2] at hr hr'
  exact hne ((root_of_square p hr).trans (root_of_square p hr').symm)

theorem splitResPairs_disjoint_squareAllPairs :
    Disjoint (splitResPairs p) (squareAllPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨c, h1, h2⟩ := (mem_squareAllPairs p).mp hs'
  exact splitResPairs_not_squareAll p hs c ⟨h1, h2⟩

theorem noRootPairs_disjoint_squareAllPairs :
    Disjoint (noRootPairs p) (squareAllPairs p) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨c, h1, h2⟩ := (mem_squareAllPairs p).mp hs'
  refine (mem_noRootPairs p).mp hs c ?_
  rw [h1, h2]
  ring

/-! ## 4. The covers (blueprint §1.1 (L) exhaustiveness — the W6q-b decision-tree inputs) -/

/-- **The unit-constant trichotomy COVER** (blueprint §1.1 (L)): every residual pair with
`w̄₀ ≠ 0` is root-free, splitU, or a UNIT square `(c̃², −2c̃)`. With the §3 disjointness
lemmas: EXACTLY ONE of the three. -/
theorem cover_of_fst_ne_zero {s : ZMod p × ZMod p} (h0 : s.1 ≠ 0) :
    s ∈ noRootPairs p ∨ s ∈ rootedPairs p ∨ s ∈ squareUnitPairs p := by
  by_cases hroot : ∃ r : ZMod p, r ^ 2 + s.2 * r + s.1 = 0
  · obtain ⟨r, hr⟩ := hroot
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact h0 (by linear_combination hr)
    have hr' := companion_root p hr
    by_cases heq : -s.2 - r = r
    · obtain ⟨h1, h2⟩ := square_of_double_root p hr heq
      refine Or.inr (Or.inr ((mem_squareUnitPairs p).mpr ⟨Units.mk0 r hr0, ?_, ?_⟩))
      · rw [Units.val_mk0]
        exact h1
      · rw [Units.val_mk0]
        exact h2
    · have hne : r ≠ -s.2 - r := fun hc => heq hc.symm
      have hr'0 : -s.2 - r ≠ 0 := by
        intro hz
        refine h0 ?_
        rw [(root_pair_vieta p hne hr hr').1, hz, mul_zero]
      exact Or.inr (Or.inl ((mem_rootedPairs p).mpr ⟨r, -s.2 - r, hne, hr0, hr'0, hr, hr'⟩))
  · exact Or.inl ((mem_noRootPairs p).mpr (not_exists.mp hroot))

/-- **The order-0 trichotomy COVER**: every residual pair is split-shape, root-free, or a
square (any center). With the §3 disjointness lemmas: EXACTLY ONE of the three. -/
theorem cover_all (s : ZMod p × ZMod p) :
    s ∈ splitResPairs p ∨ s ∈ noRootPairs p ∨ s ∈ squareAllPairs p := by
  by_cases hroot : ∃ r : ZMod p, r ^ 2 + s.2 * r + s.1 = 0
  · obtain ⟨r, hr⟩ := hroot
    have hr' := companion_root p hr
    by_cases heq : -s.2 - r = r
    · obtain ⟨h1, h2⟩ := square_of_double_root p hr heq
      exact Or.inr (Or.inr ((mem_squareAllPairs p).mpr ⟨r, h1, h2⟩))
    · have hne : r ≠ -s.2 - r := fun hc => heq hc.symm
      exact Or.inl ((mem_splitResPairs p).mpr ⟨r, -s.2 - r, hne, hr, hr'⟩)
  · exact Or.inr (Or.inl ((mem_noRootPairs p).mpr (not_exists.mp hroot)))

/-! ## 5. The partition card identities and the pool counts -/

/-- The unit-constant cover as a set identity: the three pools tile `{w̄₀ ≠ 0}`. -/
theorem unitFst_union_eq :
    noRootPairs p ∪ rootedPairs p ∪ squareUnitPairs p
      = Finset.univ.filter (fun s : ZMod p × ZMod p => s.1 ≠ 0) := by
  ext s
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ((h | h) | h)
    · exact noRootPairs_fst_ne_zero p h
    · exact rootedPairs_fst_ne_zero p h
    · obtain ⟨c, h1, -⟩ := (mem_squareUnitPairs p).mp h
      rw [h1]
      exact pow_ne_zero 2 (Units.ne_zero c)
  · intro h0
    rcases cover_of_fst_ne_zero p h0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- `#{(w̄₀, w̄₁) : w̄₀ ≠ 0} = (p−1)·p`. -/
theorem card_fst_ne_zero :
    (Finset.univ.filter (fun s : ZMod p × ZMod p => s.1 ≠ 0)).card = (p - 1) * p := by
  have hset : Finset.univ.filter (fun s : ZMod p × ZMod p => s.1 ≠ 0)
      = ({(0 : ZMod p)}ᶜ ×ˢ Finset.univ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_compl, Finset.mem_singleton, and_true]
  rw [hset, Finset.card_product, Finset.card_compl, Finset.card_singleton, Finset.card_univ,
    ZMod.card]

/-- **The unit-constant partition card identity** (blueprint §1.1 (L):
`q(q−1)/2 + (q−1)(q−2)/2 + (q−1) = q(q−1)`, in pool-card form). -/
theorem card_unitFst_partition :
    (noRootPairs p).card + (rootedPairs p).card + (squareUnitPairs p).card = (p - 1) * p := by
  have hd1 : Disjoint (noRootPairs p) (rootedPairs p) :=
    (rootedPairs_disjoint_noRootPairs p).symm
  have hd2 : Disjoint (noRootPairs p ∪ rootedPairs p) (squareUnitPairs p) :=
    Finset.disjoint_union_left.mpr ⟨noRootPairs_disjoint_squareUnitPairs p,
      rootedPairs_disjoint_squareUnitPairs p⟩
  calc (noRootPairs p).card + (rootedPairs p).card + (squareUnitPairs p).card
      = (noRootPairs p ∪ rootedPairs p).card + (squareUnitPairs p).card := by
        rw [Finset.card_union_of_disjoint hd1]
    _ = (noRootPairs p ∪ rootedPairs p ∪ squareUnitPairs p).card := by
        rw [Finset.card_union_of_disjoint hd2]
    _ = (p - 1) * p := by rw [unitFst_union_eq, card_fst_ne_zero]

/-- The order-0 cover as a set identity: the three pools tile ALL residual pairs. -/
theorem ord0_union_eq :
    splitResPairs p ∪ noRootPairs p ∪ squareAllPairs p = Finset.univ := by
  ext s
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rcases cover_all p s with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **The order-0 partition card identity** (blueprint §1.1:
`q(q−1)/2 + q(q−1)/2 + q = q²`, in pool-card form). -/
theorem card_ord0_partition :
    (splitResPairs p).card + (noRootPairs p).card + (squareAllPairs p).card = p * p := by
  have hd1 : Disjoint (splitResPairs p) (noRootPairs p) :=
    splitResPairs_disjoint_noRootPairs p
  have hd2 : Disjoint (splitResPairs p ∪ noRootPairs p) (squareAllPairs p) :=
    Finset.disjoint_union_left.mpr ⟨splitResPairs_disjoint_squareAllPairs p,
      noRootPairs_disjoint_squareAllPairs p⟩
  calc (splitResPairs p).card + (noRootPairs p).card + (squareAllPairs p).card
      = (splitResPairs p ∪ noRootPairs p).card + (squareAllPairs p).card := by
        rw [Finset.card_union_of_disjoint hd1]
    _ = (splitResPairs p ∪ noRootPairs p ∪ squareAllPairs p).card := by
        rw [Finset.card_union_of_disjoint hd2]
    _ = p * p := by
        rw [ord0_union_eq, Finset.card_univ, Fintype.card_prod, ZMod.card]

/-- **The splitU pool count, doubled**: `2·#rootedPairs = (p−1)(p−2)` — from the partition and
the banked inert-pool count `2·#noRootPairs = p(p−1)`. -/
theorem two_mul_card_rootedPairs : 2 * (rootedPairs p).card = (p - 1) * (p - 2) := by
  have hA := two_mul_card_noRootPairs p
  have hpart := card_unitFst_partition p
  have hC := card_squareUnitPairs p
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 from by omega] at hA hpart hC ⊢
  rw [show k + 2 - 2 = k from by omega]
  nlinarith [hA, hpart, hC]

/-- **The splitU pool count** (blueprint §1.1: `(q−1)(q−2)/2`; at `q = 2`: `0`; `q = 3`: `1`). -/
theorem card_rootedPairs : (rootedPairs p).card = (p - 1) * (p - 2) / 2 := by
  rw [← two_mul_card_rootedPairs p, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- **The order-0 split pool count, doubled**: `2·#splitResPairs = p(p−1)` — same count as the
inert pool (the note's split/inert order-0 symmetry). -/
theorem two_mul_card_splitResPairs : 2 * (splitResPairs p).card = p * (p - 1) := by
  have hA := two_mul_card_noRootPairs p
  have hpart := card_ord0_partition p
  have hC := card_squareAllPairs p
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 from by omega] at hA ⊢
  nlinarith [hA, hpart, hC]

/-- **The order-0 split pool count**: `q(q−1)/2` (blueprint §1.1 order-0 split cell). -/
theorem card_splitResPairs : (splitResPairs p).card = p * (p - 1) / 2 := by
  rw [← two_mul_card_splitResPairs p, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- The inert pool count in `ℕ`-division form (companion to the banked
`two_mul_card_noRootPairs`/`card_noRootPairs_q`). -/
theorem card_noRootPairs : (noRootPairs p).card = p * (p - 1) / 2 := by
  rw [← two_mul_card_noRootPairs p, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-! ## 6. The splitU leaf (`LeafPairU`) — the inert leaf shape with the pool swapped -/

/-- The splitU leaf level need (same staircase budget as the inert leaf at height `2m`). -/
def leafNeedU (m : ℕ) : ℕ := 2 * m + 1

theorem one_le_leafNeedU (m : ℕ) : 1 ≤ leafNeedU m := by
  simp only [leafNeedU]
  omega

/-- **The splitU leaf digit conditions** in a staircase frame `(L₀, L₁)` (blueprint §1.1 splitU
row): `v(b₀) ≥ 2m`, `v(b₁) ≥ m`, residual digit pair in the splitU pool (two distinct nonzero
roots — forces `v(b₀) = 2m` exact via `rootedPairs_fst_ne_zero`). EXACTLY
`ChainMenu.LeafPair (.inert m)` with `noRootPairs → rootedPairs`. -/
def LeafPairU (m L₀ L₁ : ℕ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) : Prop :=
  p ^ (2 * m) ∣ a.1.val ∧ p ^ m ∣ a.2.val
    ∧ (digit p L₀ (2 * m) a.1, digit p L₁ m a.2) ∈ rootedPairs p

/-- **The splitU leaf count** in the frame `(L₀, L₁)` (valid at `leafNeedU ≤ L₀ ≤ L₁`):
pool × free digits — the inert `leafCount` shape with the pool swapped. -/
def leafCountU (m L₀ L₁ : ℕ) : ℕ :=
  (rootedPairs p).card * (p ^ (L₀ - 2 * m - 1) * p ^ (L₁ - m - 1))

/-- The splitU leaf digit read at height `2m` is nonzero (splitU pool ⟹ `w̄₀ ≠ 0`). -/
theorem leafPairU_digit_ne_zero {m L₀ L₁ : ℕ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPairU p m L₀ L₁ a) : digit p L₀ (2 * m) a.1 ≠ 0 :=
  rootedPairs_fst_ne_zero p h.2.2

/-- The splitU leaf subsumes the staircase cluster condition (`m ≥ 1`) — the frame-glue fact
for the chain recursion (mirrors `clusterPair_of_leafPair`, inert case). -/
theorem clusterPair_of_leafPairU {m : ℕ} (hm : 1 ≤ m) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : LeafPairU p m L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  obtain ⟨hd0, hd1, -⟩ := h
  exact ⟨(dvd_pow_self p (by omega : 2 * m ≠ 0)).trans hd0,
    (dvd_pow_self p (by omega : m ≠ 0)).trans hd1⟩

/-- **The splitU leaf count identity** (`leafNeedU ≤ L₀ ≤ L₁`) — `card_pair_digitSet`
instantiated at the splitU pool (mirrors `card_leafPair`, inert case, verbatim). -/
theorem card_leafPairU (m L₀ L₁ : ℕ) (hL : leafNeedU m ≤ L₀) (h01 : L₀ ≤ L₁) :
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // LeafPairU p m L₀ L₁ a}
      = leafCountU p m L₀ L₁ := by
  rw [show leafNeedU m = 2 * m + 1 from rfl] at hL
  exact card_pair_digitSet p (by omega : 2 * m < L₀) (by omega : m < L₁) (rootedPairs p)

/-- **SplitU leaf emptiness below the level need** (self-emptying: the pinned nonzero residual
digit cannot exist when the whole slot is tail — mirrors `leafPair_empty`, inert case, via
`rootedPairs_fst_ne_zero`). -/
theorem leafPairU_empty (m : ℕ) {L₀ L₁ : ℕ} (hL : L₀ < leafNeedU m)
    (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) : ¬ LeafPairU p m L₀ L₁ a := by
  haveI : NeZero (p ^ L₀) := QuotientBox.instNeZeroPow p L₀
  rw [show leafNeedU m = 2 * m + 1 from rfl] at hL
  rintro ⟨hd0, -, hmem⟩
  have hval : a.1.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hd0 (lt_of_lt_of_le (ZMod.val_lt a.1)
      (Nat.pow_le_pow_right hp.out.pos (by omega)))
  refine rootedPairs_fst_ne_zero p hmem ?_
  show ((a.1.val / p ^ (2 * m) : ℕ) : ZMod p) = 0
  rw [hval, Nat.zero_div, Nat.cast_zero]

/-! ## 7. The splitU chain (`ChainPairU`) — `ChainPair`'s recursion, leaf clause swapped -/

/-- **The splitU chain-stratum fiber predicate** on a staircase pair frame: recursively, a
recentering digit `c ∈ F_pˣ` whose `StratumPair` (S1)∧(S2) conditions hold, followed by the
tail chain on the `descendPair`-transported child; at `ms = []`, the splitU leaf. LITERALLY
`ChainMenu.ChainPair`'s definition with the leaf clause swapped (the `ChainLeaf` inductive is
NOT extended — blueprint §1.6 design note: a parallel predicate keeps every banked
`cases leaf` proof intact). -/
def ChainPairU : List ℕ → ℕ → (L₀ L₁ : ℕ) → ZMod (p ^ L₀) × ZMod (p ^ L₁) → Prop
  | [], m, L₀, L₁, a => LeafPairU p m L₀ L₁ a
  | mstep :: ms, m, L₀, L₁, a =>
      ∃ c : (ZMod p)ˣ, StratumPair p L₀ L₁ mstep c a ∧
        ChainPairU ms m (L₀ - 2 * mstep) (L₁ - mstep)
          (descendPair p mstep ((c : ZMod p)).val a)

/-- SplitU chain conditions subsume the cluster condition (head step at `mstep ≥ 1`, or leaf
at `m ≥ 1`) — mirrors `clusterPair_of_chainPair`. -/
theorem clusterPair_of_chainPairU (ms : List ℕ) {m : ℕ}
    (hms : ∀ x ∈ ms, 1 ≤ x) (hm : 1 ≤ m) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : ChainPairU p ms m L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  cases ms with
  | nil => exact clusterPair_of_leafPairU p hm h
  | cons mstep ms =>
      obtain ⟨c, hstep, -⟩ := h
      exact clusterPair_of_stratumPair p L₀ L₁ mstep (hms mstep List.mem_cons_self) c a hstep

/-- **Small-level emptiness of the splitU chain fiber**: below the threshold
`2·Σms + leafNeedU m` the stratum is EMPTY (mirrors `chainPair_empty`). -/
theorem chainPairU_empty (ms : List ℕ) (m : ℕ) :
    ∀ L₀ L₁ : ℕ, L₀ < 2 * ms.sum + leafNeedU m →
    ∀ a : ZMod (p ^ L₀) × ZMod (p ^ L₁), ¬ ChainPairU p ms m L₀ L₁ a := by
  induction ms with
  | nil =>
      intro L₀ L₁ hL a
      rw [show ([] : List ℕ).sum = 0 from rfl] at hL
      exact leafPairU_empty p m (by omega) a
  | cons mstep ms ih =>
      intro L₀ L₁ hL a
      rintro ⟨c, -, hrest⟩
      rw [List.sum_cons] at hL
      have hneed : 1 ≤ leafNeedU m := one_le_leafNeedU m
      exact ih (L₀ - 2 * mstep) (L₁ - mstep) (by omega) _ hrest

/-- **The splitU chain closed form (pair level)**: above the level threshold
`2·Σms + leafNeedU m`, the chain-stratum count is `(p−1)^depth · leafCountU(final frame)` —
one `(p−1)` per counted recentering digit. The per-step engine (`card_exists_eq_mul`,
`card_step`, `stratumPair_unit_unique`) is INSTANTIATED from the banked `ChainMenu` generic
lemmas; only the induction wrapper mirrors `card_chainPair` (whose statement is hard-coded to
the `ChainLeaf` inductive and cannot be instantiated). -/
theorem card_chainPairU (ms : List ℕ) (m : ℕ) :
    (∀ x ∈ ms, 1 ≤ x) → 1 ≤ m →
    ∀ L₀ L₁ : ℕ, 2 * ms.sum + leafNeedU m ≤ L₀ → L₀ ≤ L₁ →
    Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) // ChainPairU p ms m L₀ L₁ a}
      = (p - 1) ^ ms.length * leafCountU p m (L₀ - 2 * ms.sum) (L₁ - ms.sum) := by
  induction ms with
  | nil =>
      intro _ hm L₀ L₁ hL h01
      simp only [List.sum_nil, List.length_nil, pow_zero, one_mul, Nat.mul_zero,
        Nat.sub_zero]
      simp only [List.sum_nil, Nat.mul_zero, Nat.zero_add] at hL
      exact card_leafPairU p m L₀ L₁ hL h01
  | cons mstep ms ih =>
      intro hms hm L₀ L₁ hL h01
      have hm1 : 1 ≤ mstep := hms mstep List.mem_cons_self
      have hneed : 1 ≤ leafNeedU m := one_le_leafNeedU m
      rw [List.sum_cons] at hL ⊢
      have hstep : Nat.card {a : ZMod (p ^ L₀) × ZMod (p ^ L₁) //
            ChainPairU p (mstep :: ms) m L₀ L₁ a}
          = (p - 1) * Nat.card {b : ZMod (p ^ (L₀ - 2 * mstep)) × ZMod (p ^ (L₁ - mstep)) //
              ChainPairU p ms m (L₀ - 2 * mstep) (L₁ - mstep) b} := by
        have hmain := card_exists_eq_mul
          (Q := fun (c : (ZMod p)ˣ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)) =>
            StratumPair p L₀ L₁ mstep c a ∧
              ChainPairU p ms m (L₀ - 2 * mstep) (L₁ - mstep)
                (descendPair p mstep ((c : ZMod p)).val a))
          (fun c c' a h h' => stratumPair_unit_unique p h.1 h'.1)
          (Nat.card {b : ZMod (p ^ (L₀ - 2 * mstep)) × ZMod (p ^ (L₁ - mstep)) //
              ChainPairU p ms m (L₀ - 2 * mstep) (L₁ - mstep) b})
          (fun c => card_step p L₀ L₁ mstep c (by omega) h01
            (ChainPairU p ms m (L₀ - 2 * mstep) (L₁ - mstep))
            (fun b hb => clusterPair_of_chainPairU p ms
              (fun x hx => hms x (List.mem_cons_of_mem mstep hx)) hm hb))
        rw [ZMod.card_units p] at hmain
        exact hmain
      rw [hstep, ih (fun x hx => hms x (List.mem_cons_of_mem mstep hx)) hm
        (L₀ - 2 * mstep) (L₁ - mstep) (by omega) (by omega)]
      rw [show (mstep :: ms).length = ms.length + 1 from rfl, pow_succ]
      rw [show L₀ - 2 * mstep - 2 * ms.sum = L₀ - 2 * (mstep + ms.sum) from by omega,
        show L₁ - mstep - ms.sum = L₁ - (mstep + ms.sum) from by omega]
      ring

/-! ## 8. General-`p` order-0 cells (residual SHAPES, replacing W6's `p = 2` digit cells) -/

/-- The height-0 digit vanishes iff `p` divides the value (the mod-`p` residue read). -/
theorem digit_zero_eq_zero_iff {N : ℕ} (x : ZMod (p ^ N)) :
    digit p N 0 x = 0 ↔ p ∣ x.val := by
  show ((x.val / p ^ 0 : ℕ) : ZMod p) = 0 ↔ p ∣ x.val
  rw [pow_zero, Nat.div_one]
  exact CharP.cast_eq_zero_iff (ZMod p) p x.val

/-- **The general-`p` order-0 split cell** (blueprint §1.1 order-0 split): the residual pair
`(ā₀, ā₁)` (height-0 digit reads) has `x² + ā₁x + ā₀` with two DISTINCT roots (0 allowed). -/
def Ord0SplitCell (N : ℕ) (a : ZMod (p ^ N) × ZMod (p ^ N)) : Prop :=
  (digit p N 0 a.1, digit p N 0 a.2) ∈ splitResPairs p

/-- **The general-`p` order-0 inert cell**: residual root-free — the pool IS
`ChainMenu.noRootPairs p` (reused, not duplicated). -/
def Ord0InertCell (N : ℕ) (a : ZMod (p ^ N) × ZMod (p ^ N)) : Prop :=
  (digit p N 0 a.1, digit p N 0 a.2) ∈ noRootPairs p

/-- **The order-0 split cell count**: pool × free tails, `#splitResPairs · p^{N−1} · p^{N−1}`. -/
theorem card_ord0Split (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0SplitCell p N a}
      = (splitResPairs p).card * (p ^ (N - 1) * p ^ (N - 1)) := by
  have e : {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0SplitCell p N a}
      ≃ {a : ZMod (p ^ N) × ZMod (p ^ N) //
          p ^ 0 ∣ a.1.val ∧ p ^ 0 ∣ a.2.val
            ∧ (digit p N 0 a.1, digit p N 0 a.2) ∈ splitResPairs p} :=
    Equiv.subtypeEquivRight (fun a =>
      ⟨fun h => ⟨by rw [pow_zero]; exact one_dvd _, by rw [pow_zero]; exact one_dvd _, h⟩,
       fun h => h.2.2⟩)
  rw [Nat.card_congr e]
  have h := card_pair_digitSet p (show 0 < N by omega) (show 0 < N by omega) (splitResPairs p)
  simp only [Nat.sub_zero] at h
  exact h

/-- **The order-0 inert cell count**: `#noRootPairs · p^{N−1} · p^{N−1}`. -/
theorem card_ord0Inert (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0InertCell p N a}
      = (noRootPairs p).card * (p ^ (N - 1) * p ^ (N - 1)) := by
  have e : {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0InertCell p N a}
      ≃ {a : ZMod (p ^ N) × ZMod (p ^ N) //
          p ^ 0 ∣ a.1.val ∧ p ^ 0 ∣ a.2.val
            ∧ (digit p N 0 a.1, digit p N 0 a.2) ∈ noRootPairs p} :=
    Equiv.subtypeEquivRight (fun a =>
      ⟨fun h => ⟨by rw [pow_zero]; exact one_dvd _, by rw [pow_zero]; exact one_dvd _, h⟩,
       fun h => h.2.2⟩)
  rw [Nat.card_congr e]
  have h := card_pair_digitSet p (show 0 < N by omega) (show 0 < N by omega) (noRootPairs p)
  simp only [Nat.sub_zero] at h
  exact h

/-- The order-0 split cell count, closed form: `q(q−1)/2 · q^{2(N−1)}` (blueprint §1.1: mass
`(q−1)/(2q)` of the `q^{2N}` box). -/
theorem card_ord0Split_closed (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0SplitCell p N a}
      = p * (p - 1) / 2 * p ^ (2 * (N - 1)) := by
  rw [card_ord0Split p N hN, card_splitResPairs p, ← pow_add,
    show N - 1 + (N - 1) = 2 * (N - 1) from by omega]

/-- The order-0 inert cell count, closed form: `q(q−1)/2 · q^{2(N−1)}` — EQUAL to the split
cell count (the order-0 split/inert symmetry feeding `R_split = R_inert` at order 0). -/
theorem card_ord0Inert_closed (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {a : ZMod (p ^ N) × ZMod (p ^ N) // Ord0InertCell p N a}
      = p * (p - 1) / 2 * p ^ (2 * (N - 1)) := by
  rw [card_ord0Inert p N hN, card_noRootPairs p, ← pow_add,
    show N - 1 + (N - 1) = 2 * (N - 1) from by omega]

/-! ## 9. `p = 2` recovery gates (the W6 digit cells decoded)

W6's `SeriesAssembly.SepSplitCell N a = (2 ∣ a.1.val ∧ ¬ 2 ∣ a.2.val)` and
`SepInertCell N a = (¬ 2 ∣ a.1.val ∧ ¬ 2 ∣ a.2.val)` — the gates below are stated on exactly
these raw divisibility conditions (no `SeriesAssembly` import: the tie there is definitional
and belongs to W6q-c). -/

/-- The `p = 2` split pool is the single W6 split residual `x(x+1)`: `(ā₀, ā₁) = (0, 1)`. -/
theorem splitResPairs_two : splitResPairs 2 = {((0 : ZMod 2), (1 : ZMod 2))} := by
  ext s
  rw [mem_splitResPairs, Finset.mem_singleton]
  revert s
  decide

/-- The `p = 2` inert pool is the single W6 inert residual `x² + x + 1`: `(ā₀, ā₁) = (1, 1)`. -/
theorem noRootPairs_two : noRootPairs 2 = {((1 : ZMod 2), (1 : ZMod 2))} := by
  ext s
  rw [mem_noRootPairs, Finset.mem_singleton]
  revert s
  decide

/-- **The `p = 2` order-0 split recovery gate**: the general-`p` residual-shape cell decodes to
EXACTLY W6's `SepSplitCell` digit conditions `ā₀ = 0 ∧ ā₁ = 1`. -/
theorem ord0Split_two_iff (N : ℕ) (a : ZMod (2 ^ N) × ZMod (2 ^ N)) :
    Ord0SplitCell 2 N a ↔ (2 ∣ a.1.val ∧ ¬ 2 ∣ a.2.val) := by
  have h01 : ∀ x : ZMod 2, x = 1 ↔ ¬ x = 0 := by decide
  rw [Ord0SplitCell, splitResPairs_two, Finset.mem_singleton, Prod.mk.injEq,
    h01 (digit 2 N 0 a.2), digit_zero_eq_zero_iff 2 a.1, digit_zero_eq_zero_iff 2 a.2]

/-- **The `p = 2` order-0 inert recovery gate**: the general-`p` residual-shape cell decodes to
EXACTLY W6's `SepInertCell` digit conditions `ā₀ = 1 ∧ ā₁ = 1`. -/
theorem ord0Inert_two_iff (N : ℕ) (a : ZMod (2 ^ N) × ZMod (2 ^ N)) :
    Ord0InertCell 2 N a ↔ (¬ 2 ∣ a.1.val ∧ ¬ 2 ∣ a.2.val) := by
  have h01 : ∀ x : ZMod 2, x = 1 ↔ ¬ x = 0 := by decide
  rw [Ord0InertCell, noRootPairs_two, Finset.mem_singleton, Prod.mk.injEq,
    h01 (digit 2 N 0 a.1), h01 (digit 2 N 0 a.2),
    digit_zero_eq_zero_iff 2 a.1, digit_zero_eq_zero_iff 2 a.2]

/-! ## 10. Census gates (blueprint §0/§4 mitigation: every pool card anchored at `p = 2, 3`) -/

section GateCensus

/-- `q = 3` splitU pool: exactly the hand-enumerated `(z−1)(z−2) = z² + 2`, i.e. `(2, 0)`. -/
theorem rootedPairs_three : rootedPairs 3 = {((2 : ZMod 3), (0 : ZMod 3))} := by
  ext s
  rw [mem_rootedPairs, Finset.mem_singleton]
  revert s
  decide

/-- `q = 3` gate: `#rootedPairs = (q−1)(q−2)/2 = 1` ✓ (blueprint §0 splitU pool check). -/
theorem card_rootedPairs_three : (rootedPairs 3).card = 1 := by decide

/-- `q = 3` gate: `#splitResPairs = q(q−1)/2 = 3` ✓. -/
theorem card_splitResPairs_three : (splitResPairs 3).card = 3 := by decide

/-- `q = 3` gate: `#noRootPairs = q(q−1)/2 = 3` ✓ (the three irreducibles
`z²+1, z²+z+2, z²+2z+2`). -/
theorem card_noRootPairs_three : (noRootPairs 3).card = 3 := by
  have h3 : noRootPairs 3 = {((1 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3)),
      ((2 : ZMod 3), (2 : ZMod 3))} := by
    ext s
    rw [mem_noRootPairs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    revert s
    decide
  rw [h3]
  decide

/-- `q = 2` gate: `#rootedPairs = 0` (the honest-empty splitU family at the wild prime). -/
theorem card_rootedPairs_two : (rootedPairs 2).card = 0 := by
  rw [rootedPairs_two_empty]
  rfl

/-- `q = 2` gate: `#splitResPairs = 1` (the W6 split cell pool `x(x+1)`). -/
theorem card_splitResPairs_two : (splitResPairs 2).card = 1 := by decide

end GateCensus

/-! ## 11. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms companion_root
#print axioms root_pair_vieta
#print axioms square_of_double_root
#print axioms root_of_square
#print axioms square_map_injective
#print axioms rootedPairs
#print axioms mem_rootedPairs
#print axioms rootedPairs_fst_ne_zero
#print axioms rootedPairs_two_empty
#print axioms splitResPairs
#print axioms mem_splitResPairs
#print axioms rootedPairs_subset_splitResPairs
#print axioms squareUnitPairs
#print axioms mem_squareUnitPairs
#print axioms card_squareUnitPairs
#print axioms squareAllPairs
#print axioms mem_squareAllPairs
#print axioms card_squareAllPairs
#print axioms rootedPairs_disjoint_noRootPairs
#print axioms rootedPairs_not_squareUnit
#print axioms rootedPairs_disjoint_squareUnitPairs
#print axioms noRootPairs_disjoint_squareUnitPairs
#print axioms splitResPairs_disjoint_noRootPairs
#print axioms splitResPairs_not_squareAll
#print axioms splitResPairs_disjoint_squareAllPairs
#print axioms noRootPairs_disjoint_squareAllPairs
#print axioms cover_of_fst_ne_zero
#print axioms cover_all
#print axioms unitFst_union_eq
#print axioms card_fst_ne_zero
#print axioms card_unitFst_partition
#print axioms ord0_union_eq
#print axioms card_ord0_partition
#print axioms two_mul_card_rootedPairs
#print axioms card_rootedPairs
#print axioms two_mul_card_splitResPairs
#print axioms card_splitResPairs
#print axioms card_noRootPairs
#print axioms leafNeedU
#print axioms one_le_leafNeedU
#print axioms LeafPairU
#print axioms leafCountU
#print axioms leafPairU_digit_ne_zero
#print axioms clusterPair_of_leafPairU
#print axioms card_leafPairU
#print axioms leafPairU_empty
#print axioms ChainPairU
#print axioms clusterPair_of_chainPairU
#print axioms chainPairU_empty
#print axioms card_chainPairU
#print axioms digit_zero_eq_zero_iff
#print axioms Ord0SplitCell
#print axioms Ord0InertCell
#print axioms card_ord0Split
#print axioms card_ord0Inert
#print axioms card_ord0Split_closed
#print axioms card_ord0Inert_closed
#print axioms splitResPairs_two
#print axioms noRootPairs_two
#print axioms ord0Split_two_iff
#print axioms ord0Inert_two_iff
#print axioms rootedPairs_three
#print axioms card_rootedPairs_three
#print axioms card_splitResPairs_three
#print axioms card_noRootPairs_three
#print axioms card_rootedPairs_two
#print axioms card_splitResPairs_two
end AxCheck

end LeanUrat.OM.ChainMenuU
