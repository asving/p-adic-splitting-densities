/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ChainMenuU
import LeanUrat.OM.ChainMenu6

/-!
# ChainMenu7 — Wave W6q-d: the splitU widening of the chain menu (scope-#6 menu)

**Provenance.** `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §1.5 (the splitU delta) and §3
(the re-scope #6 statement design), mirroring the W6c widening pattern of `OM/ChainMenu6.lean`.
ADDITIVE module: `OM/ChainMenu.lean`, `OM/ChainMenu6.lean`, `OM/ChainMenuU.lean` are not
touched.

## The object

The general-`p` splitU family (`OM/ChainMenuU.lean`: even-height separable residual with two
DISTINCT NONZERO roots, keyed `{(1,1),(1,1)}`; honestly EMPTY at `p = 2`) has NO literal on
any earlier menu — the `ChainLeaf` inductive was deliberately NOT extended (blueprint §1.6
design note), so the splitU strata need their own literal family and their own head slot.
THIS module supplies them:

* `splitULit ms m` — the splitU literal. **Head-encoding decision (the decode-collision
  audit demanded by the blueprint)**: `MultiSlopeMenu.headOrd` reads the FIRST component of
  the first tree triple (`headOrd T = ((T.tree.head?).map (·.1)).getD 0`), so a head
  `(2, 3, ms.length)` would carry `headOrd = 2` and be dispatched by `OmLeafFaithful.fiberOf5`
  into the CHAIN branch, where `decodeLeaf`'s wildcard maps the unknown last triple `(3, 3, m)`
  to `ram m` — a silent MIS-decode. The literal therefore takes the FRESH order slot `3`:
  head `(3, 2, ms.length)`, then the `ms` entries `(0, m_t, 0)`, then the splitU leaf head
  `(3, 3, m)`. Every existing dispatch (`headOrd ∈ {0, 1, 2}`) passes it through untouched
  and the NEW `fiberOf7` branch owns it. Proved no-collision inventory: `headOrd_splitULit`
  (`= 3`), exact decodes `decodeMsU_splitULit` (the slope list, via the SAME tail read as
  `ChainMenu.decodeMs`) / `decodeMU_splitULit` (the leaf height), `splitULit_injective`,
  `splitULit_ne_chainLit`, and `headOrd_ne_three_of_mem_omMenu6` (NO scope-#5 menu member
  carries the splitU head — the discriminator lemma the derived theorem
  `om_leaf_faithful_w6` consumes).
* `splitUShapes n D K σ` — the emission: `splitULit ms m` for `ms ∈ msMenu D K`
  (depth-0 `ms = []` INCLUDED — the splitU leaves live at every depth), `m ∈ Icc 1 K`;
  `n = 2` and `σ = splitType2` ONLY.
* `omMenu7 n D K σ := ChainMenu6.omMenu6 n D K σ ∪ splitUShapes n D K σ` — the Wave-6q
  σ-keyed menu, with `omMenu6_subset_omMenu7` (the scope-#5 → scope-#6 recovery inclusion)
  and the discriminator `mem_omMenu7_cases`.
* `typeOf7` — the σ-keying: on splitU heads (`headOrd = 3`) the constant `splitType2`; on
  every other head defer to `ChainMenu.typeOf5` (mirrors how `typeOf5` extended `typeOf4`).
  `mem_omMenu7_type` / `eq_of_mem_omMenu7` re-run the ChainMenu6 keying-alignment pattern.
* `ChainCellU` — the box-level splitU fiber (the `ChainMenu.ChainCell` analogue on the monic
  box): `ChainMenuU.ChainPairU` read on the coefficient pair at the root frame `(N, N)` —
  the EXACT fiber shape `OmLeafFaithful.fiberOf7` dispatches the new literals to.

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.ChainMenu7

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.CellMenu
open LeanUrat.OM.ChainMenu

/-! ## 1. The splitU literal and its exact decode -/

/-- The numeric head of the splitU leaf: order-slot `3` (fresh), tag `3` (below the
`ChainLeaf` tags `0/1/2` of `ChainMenu.leafHead`, which live in trees headed `(2, 2, ·)` —
different head, no overlap), parameter `m` in the last slot. -/
def splitUHead (m : ℕ) : ℕ × ℕ × ℕ := (3, 3, m)

/-- **The splitU literal** (tree-index encoding): head `(3, 2, depth)` — the FRESH order-slot
`3`, discriminating from every order-0 head (W1/W3 families), the multi-slope order-slot `1`,
AND the chain order-slot `2` (see the module docstring for why `(2, 3, ·)` would MIS-decode) —
then the `ms` entries `(0, m_t, 0)`, then the splitU leaf head `(3, 3, m)`. Cells empty. -/
def splitULit (ms : List ℕ) (m : ℕ) : ClusterShape :=
  ⟨((3 : ℕ), 2, ms.length) :: (ms.map (fun t => ((0 : ℕ), t, 0)) ++ [splitUHead m]), []⟩

/-- The splitU family discriminator: head order-slot `3`. -/
theorem headOrd_splitULit (ms : List ℕ) (m : ℕ) :
    MultiSlopeMenu.headOrd (splitULit ms m) = 3 := rfl

/-- Exact decode of the splitU leaf height: last-triple, last slot. -/
def decodeMU (T : ClusterShape) : ℕ := ((T.tree.getLast?).map (fun t => t.2.2)).getD 0

/-- The slope-list decode is SHARED with the chain literals (`ChainMenu.decodeMs` reads
tail-minus-last, middle slots — the splitU tree has the same shape). -/
theorem decodeMsU_splitULit (ms : List ℕ) (m : ℕ) :
    ChainMenu.decodeMs (splitULit ms m) = ms := by
  show ((ms.map (fun t => ((0 : ℕ), t, 0)) ++ [splitUHead m]).dropLast).map
    (fun t : ℕ × ℕ × ℕ => t.2.1) = ms
  rw [List.dropLast_concat, List.map_map]
  induction ms with
  | nil => rfl
  | cons x tl ih => rw [List.map_cons, ih]; rfl

theorem decodeMU_splitULit (ms : List ℕ) (m : ℕ) : decodeMU (splitULit ms m) = m := by
  have hlast : (splitULit ms m).tree.getLast? = some (splitUHead m) := by
    show ((((3 : ℕ), 2, ms.length) :: ms.map (fun t => ((0 : ℕ), t, 0)))
        ++ [splitUHead m]).getLast? = some (splitUHead m)
    exact List.getLast?_concat
  show (((splitULit ms m).tree.getLast?).map (fun t => t.2.2)).getD 0 = m
  rw [hlast]
  rfl

/-- **Injectivity of the splitU literal** (exact decode). -/
theorem splitULit_injective {ms ms' : List ℕ} {m m' : ℕ}
    (h : splitULit ms m = splitULit ms' m') : ms = ms' ∧ m = m' := by
  have h1 := decodeMsU_splitULit ms m
  rw [h, decodeMsU_splitULit] at h1
  have h2 := decodeMU_splitULit ms m
  rw [h, decodeMU_splitULit] at h2
  exact ⟨h1.symm, h2.symm⟩

/-- A splitU literal is NEVER a chain literal (head order-slot `3` vs `2`) — the blueprint's
"MUST NOT be a chainLit with a fourth leafHead" requirement, discharged by the head choice. -/
theorem splitULit_ne_chainLit (ms ms' : List ℕ) (m : ℕ) (leaf : ChainMenu.ChainLeaf) :
    splitULit ms m ≠ ChainMenu.chainLit ms' leaf := by
  intro h
  have h3 := headOrd_splitULit ms m
  rw [h, ChainMenu.headOrd_chainLit] at h3
  exact absurd h3 (by decide)

/-- **NO scope-#5 menu member carries the splitU head** — every `omMenu6` shape has head
order-slot `0` (W1/W3 families), `1` (the multi-slope literal), or `2` (chain literals,
depth-0 included), never `3`. This is the discriminator lemma behind the derived theorem
`OmLeafFaithful.om_leaf_faithful_w6` (fiber leg via `fiberOf7_not_splitU`). -/
theorem headOrd_ne_three_of_mem_omMenu6 {n D K : ℕ} {σ : FactorizationType}
    {T : ClusterShape} (hT : T ∈ ChainMenu6.omMenu6 n D K σ) :
    MultiSlopeMenu.headOrd T ≠ 3 := by
  rcases ChainMenu6.mem_omMenu6_cases.mp hT with h5 | ⟨-, leaf, -, rfl⟩
  · rcases ChainMenu.mem_omMenu5_cases h5 with h4 | ⟨-, ms, leaf, -, -, -, rfl⟩
    · rcases MultiSlopeMenu.mem_omMenu4_cases h4 with hold | ⟨-, rfl⟩
      · rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hold]
        omega
      · rw [MultiSlopeMenu.headOrd_multiSideLit]
        omega
    · rw [ChainMenu.headOrd_chainLit]
      omega
  · rw [ChainMenu.headOrd_chainLit]
    omega

/-! ## 2. The emission and the scope-#6 menu -/

/-- **The splitU emission** (blueprint §1.5): `splitULit ms m` over the window rectangle
`ms ∈ msMenu D K` (depth 0 INCLUDED), `m ∈ Icc 1 K` — at `n = 2`, `σ = splitType2` ONLY
(the splitU family is keyed `{(1,1),(1,1)}` and exists only for the quadratic model). -/
noncomputable def splitUShapes (n D K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  if n = 2 ∧ σ = ChainMenu.splitType2 then
    (ChainMenu.msMenu D K ×ˢ Finset.Icc 1 K).image (fun x => splitULit x.1 x.2)
  else ∅

theorem mem_splitUShapes {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ splitUShapes n D K σ ↔ n = 2 ∧ σ = ChainMenu.splitType2
      ∧ ∃ ms m, ms ∈ ChainMenu.msMenu D K ∧ m ∈ Finset.Icc 1 K ∧ T = splitULit ms m := by
  constructor
  · intro hT
    by_cases h : n = 2 ∧ σ = ChainMenu.splitType2
    · rw [splitUShapes, if_pos h, Finset.mem_image] at hT
      obtain ⟨x, hx, rfl⟩ := hT
      rw [Finset.mem_product] at hx
      exact ⟨h.1, h.2, x.1, x.2, hx.1, hx.2, rfl⟩
    · rw [splitUShapes, if_neg h] at hT
      exact absurd hT (Finset.notMem_empty T)
  · rintro ⟨rfl, rfl, ms, m, hms, hm, rfl⟩
    rw [splitUShapes, if_pos ⟨rfl, rfl⟩, Finset.mem_image]
    exact ⟨(ms, m), Finset.mem_product.mpr ⟨hms, hm⟩, rfl⟩

/-- **The Wave-6q σ-keyed menu** (the scope-#6 menu): the Wave-6 menu extended by the splitU
literals. -/
noncomputable def omMenu7 (n D K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  ChainMenu6.omMenu6 n D K σ ∪ splitUShapes n D K σ

/-- **The recovery inclusion**: every scope-#5 menu shape is a scope-#6 menu shape (the menu
leg of the derived theorem `OmLeafFaithful.om_leaf_faithful_w6`). -/
theorem omMenu6_subset_omMenu7 (n D K : ℕ) (σ : FactorizationType) :
    ChainMenu6.omMenu6 n D K σ ⊆ omMenu7 n D K σ :=
  Finset.subset_union_left

/-- Menu case analysis: a Wave-6q menu shape is a Wave-6 menu shape or a splitU literal. -/
theorem mem_omMenu7_cases {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ omMenu7 n D K σ
      ↔ T ∈ ChainMenu6.omMenu6 n D K σ
        ∨ (n = 2 ∧ σ = ChainMenu.splitType2
            ∧ ∃ ms m, ms ∈ ChainMenu.msMenu D K ∧ m ∈ Finset.Icc 1 K
                ∧ T = splitULit ms m) := by
  rw [omMenu7, Finset.mem_union, mem_splitUShapes]

/-- The two menu parts are disjoint (head order-slot `3` vs `{0, 1, 2}`) — at ANY window
bounds and any pair of types. -/
theorem omMenu6_splitUShapes_disjoint (n D D' K K' : ℕ) (σ σ' : FactorizationType) :
    Disjoint (ChainMenu6.omMenu6 n D K σ) (splitUShapes n D' K' σ') :=
  Finset.disjoint_left.mpr (fun T hT6 hTU => by
    obtain ⟨-, -, ms, m, -, -, rfl⟩ := mem_splitUShapes.mp hTU
    exact headOrd_ne_three_of_mem_omMenu6 hT6 (headOrd_splitULit ms m))

/-! ## 3. σ-keying: `typeOf7` -/

/-- **The Wave-6q σ-decoder**: on splitU heads (order-slot `3`) the split type; on every
other head defer to the Wave-5 decoder (which itself defers to the Wave-4 one — the
`typeOf5`-over-`typeOf4` extension pattern, re-run). -/
noncomputable def typeOf7 (n : ℕ) (T : ClusterShape) : Option FactorizationType :=
  if MultiSlopeMenu.headOrd T = 3 then some ChainMenu.splitType2
  else ChainMenu.typeOf5 n T

theorem typeOf7_splitULit (n : ℕ) (ms : List ℕ) (m : ℕ) :
    typeOf7 n (splitULit ms m) = some ChainMenu.splitType2 := by
  rw [typeOf7, if_pos (headOrd_splitULit ms m)]

theorem typeOf7_typeOf5_compat {n : ℕ} {T : ClusterShape}
    (h : MultiSlopeMenu.headOrd T ≠ 3) : typeOf7 n T = ChainMenu.typeOf5 n T := by
  rw [typeOf7, if_neg h]

/-- **Every Wave-6q menu shape names its type** (the `mem_omMenu6_type` analogue; new
members via `typeOf7_splitULit`). -/
theorem mem_omMenu7_type {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu7 n D K σ) : typeOf7 n T = some σ := by
  rcases mem_omMenu7_cases.mp hT with h6 | ⟨-, rfl, ms, m, -, -, rfl⟩
  · rw [typeOf7_typeOf5_compat (headOrd_ne_three_of_mem_omMenu6 h6)]
    exact ChainMenu6.mem_omMenu6_type h6
  · exact typeOf7_splitULit n ms m

/-- Distinct types have disjoint Wave-6q menus — at ANY window bounds (the
`eq_of_mem_omMenu6` analogue). -/
theorem eq_of_mem_omMenu7 {n D D' K K' : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenu7 n D K σ) (h' : T ∈ omMenu7 n D' K' σ') : σ = σ' := by
  have h1 := mem_omMenu7_type h
  have h2 := mem_omMenu7_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## 4. The box-level splitU fiber (`ChainCellU` — the `ChainCell` analogue) -/

/-- **The splitU-stratum fiber predicate on the monic box** (the `ChainMenu.ChainCell`
analogue): the `ChainMenuU.ChainPairU` digit recursion read on the coefficient pair
`(a₀, a₁)` at the root frame `(N, N)`. This is the EXACT fiber `OmLeafFaithful.fiberOf7`
dispatches splitU-headed literals to (at their exact decode), and the fiber the W6q
counting model counts. Semantically meaningful at `n = 2`. -/
def ChainCellU (p : ℕ) [Fact p.Prime] (ms : List ℕ) (m : ℕ) {N n : ℕ}
    (f : QuotientBox.monicBox p N n) : Prop :=
  ChainMenuU.ChainPairU p ms m N N ((f.1).coeff 0, (f.1).coeff 1)

/-! ## 5. AxCheck — every declaration of this module is core-only -/

section AxCheck
#print axioms LeanUrat.OM.ChainMenu7.splitUHead
#print axioms LeanUrat.OM.ChainMenu7.splitULit
#print axioms LeanUrat.OM.ChainMenu7.headOrd_splitULit
#print axioms LeanUrat.OM.ChainMenu7.decodeMU
#print axioms LeanUrat.OM.ChainMenu7.decodeMsU_splitULit
#print axioms LeanUrat.OM.ChainMenu7.decodeMU_splitULit
#print axioms LeanUrat.OM.ChainMenu7.splitULit_injective
#print axioms LeanUrat.OM.ChainMenu7.splitULit_ne_chainLit
#print axioms LeanUrat.OM.ChainMenu7.headOrd_ne_three_of_mem_omMenu6
#print axioms LeanUrat.OM.ChainMenu7.splitUShapes
#print axioms LeanUrat.OM.ChainMenu7.mem_splitUShapes
#print axioms LeanUrat.OM.ChainMenu7.omMenu7
#print axioms LeanUrat.OM.ChainMenu7.omMenu6_subset_omMenu7
#print axioms LeanUrat.OM.ChainMenu7.mem_omMenu7_cases
#print axioms LeanUrat.OM.ChainMenu7.omMenu6_splitUShapes_disjoint
#print axioms LeanUrat.OM.ChainMenu7.typeOf7
#print axioms LeanUrat.OM.ChainMenu7.typeOf7_splitULit
#print axioms LeanUrat.OM.ChainMenu7.typeOf7_typeOf5_compat
#print axioms LeanUrat.OM.ChainMenu7.mem_omMenu7_type
#print axioms LeanUrat.OM.ChainMenu7.eq_of_mem_omMenu7
#print axioms LeanUrat.OM.ChainMenu7.ChainCellU
end AxCheck

end LeanUrat.OM.ChainMenu7
