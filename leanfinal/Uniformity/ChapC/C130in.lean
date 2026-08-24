/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapC.C130fg
import Uniformity.ChapC.C130th
import Uniformity.ChapE.E11
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapC.C130in — `RealizedInput` and the input block (chain-carrier node CC-8)

**Chain-carrier node CC-8** (`CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.4, §5, §8 row C.130e,
§10 row CC-8): land `RealizedInput` — the input-specific record over `ArisingCore` (C130a) and
the assembled `ChainRealization` layer (C130fg) — and the producing theorem `inputBlock`
deriving E.11's `Ladder.BlockData` over CC-5's `stageCarrier`, together with the four views:
development, key-free, `A₀`, and threshold.

`RealizedInput`'s type is byte-identical to the elaboration authority
`leanfinal/scratch/U11_carrier_check.lean` (design §4.4): it "adds only dictionary equalities
and a selected legal point to `ArisingCore`; it does not contain `SlotCarrier`, `BlockData`, a
socket, or a consumer conclusion."  The three equality fields are REPOSITORY DICTIONARIES
(design §9: `receiver_eq`, `stageKey_eq`, `stageDeg_eq`); the point pair is EFF.GENTOW5.16's
selected legal node point.

## What this cures (the C.130e blocker, recorded in `C130d.lean`)

Freeze-v2 layer C.130e was BLOCKED because "its required `BlockData` needs the C.130c
`stageCarrier`, C.130b `stageKey`, and this source-pinned threshold."  All three now exist:
CC-5 landed `stageCarrier` (C130st), `ArisingCore` carries the C.130b `stageKey`/`stageDeg`
data tied to the key chain by the `stageKey_eq`/`stageDeg_eq` dictionaries, and CC-7 landed the
inherited-threshold dictionary (C130th).  Design §8 row C.130e prescribes the assembly exactly:
"reuse `ArisingCore`; use B.02/B.05/B.06 `dev`, `core.keyfree`, the generic `A₀ ≠ 0` lemma,
and `thresholdNat`.  No block is stored in the carrier."  Accordingly `inputBlock` is a
DERIVATION from a `RealizedInput` — no carrier field holds a block, and nothing here inhabits
`NodePointSource`, `ChainRealization`, or `RealizedInput`.

## Field provenance of the produced block (all supplied, none invented)

* `Φ`/`F`/`μ` are `core.stageKey`/`core.F₀`/`core.μ` with `core`'s monicity fields; the degree
  binding `hΦdeg` is the `stageKey_degree` ∘ `stageDeg_eq` dictionary — positivity of the key
  degree is NOT an `ArisingCore` field and genuinely needs the realization
  (`stageDeg_eq` + C130st's `Dcum_pos`), which is why the block exists only at a
  `RealizedInput` and not at a bare core;
* `A` is B.02's `dev` (`A j = dev Φ F₀ j` for `j < μ`, `0` above — E.11's stated convention,
  here enforced); `hdev` is the monic-top development identity (`sum_dev_eq_monic_top` below,
  from B.05 `sum_dev_eq` + B.06 `dev_unique`; `EFF.W12.23`'s "Monic division gives the UNIQUE
  `Φ`-adic development `f = Φ^m + Σ_{j<m} a_j Φ^j`", which is `EFF.T2.11`'s `(DEV)` shape);
* `hkeyfree` is `core.keyfree`, verbatim (the spellings match by construction: C130a froze
  `ArisingCore.keyfree` in E.11's `IsCoprime`-over-`FractionRing` spelling);
* `hA0` is the GENERIC `A₀ ≠ 0` lemma (`dev_zero_ne_zero_of_isCoprime` below) — `EFF.T2.11`'s
  own derivation "(KEY-FREE) implies A₀ ≠ 0", proved here once and for all monic keys of
  positive degree, not assumed;
* `T` is the INHERITED `A.node.thresholdNat core.i` (CC-7's dictionary; design §5: "not
  derivable from `(DeepTower,i,F₀)`" — no numeral and no formula appears in this file).

## The four views (row CC-8's exit condition)

1. **Development** (`inputBlock_dev`, with `inputBlock_A_eq_dev`/`inputBlock_A_of_le` and the
   core-vocabulary `F₀_dev`): the block's development is `(DEV)` at `core.F₀`, and its
   coefficients are exactly B.02's `dev` — canonical by B.06, not freely chosen tables.
2. **Key-free** (`inputBlock_keyfree`, `inputBlock_keyfree_core`, `inputBlock_keyfree_keyAt`):
   the block carries `(KEY-FREE)` verbatim from `core.keyfree`, including at the carrier's own
   `keyAt` through the `stageKey_eq` dictionary.
3. **`A₀`** (`inputBlock_A0_ne_zero`, `inputBlock_A0_eq_dev`, `F₀_dev_zero_ne_zero`): the
   consumed polygon shadow `A₀ ≠ 0`, derived from key-freeness, never assumed.
4. **Threshold** (`inputBlock_canonicalThreshold`, `canonicalThresholdAt_iff_inputBlock`,
   `inputBlock_window`): the block's `T` is CC-7-canonical at the realized occurrence — this
   file's `RealizedInput.CanonicalThresholdAt` is the definitional specialization of C130th's
   carrier predicate at `(A.node, core.i, X.point)`, byte-for-byte design §5's display
   (`canonicalThresholdAt_def` is the `Iff.rfl` anti-drift pin) — and EFF.T2.11's `(WINDOW)`
   holds at the block's own key through the `stageKey_eq` dictionary.

## Deliberately NOT here (later CC nodes)

Any instance of `NodePointSource`/`ChainRealization`/`RealizedInput` (CC-6/CC-9/CC-17); the
socket-level view equalities and transports (CC-12); the FGMN packaging (CC-14/15/16); every
socket application (CC-18).

DEPENDS: C130fg (CC-13: `ChainRealization`), C130th (CC-7: threshold dictionary,
`CanonicalThresholdAt`), C130st via C130th (CC-5: `stageCarrier`), C130a via C130k
(`ArisingCore`, live ranges), E11 (`Ladder.BlockData`), B02/B05/B06 (`dev`, `sum_dev_eq`,
`dev_unique`, `degree_dev_lt`), `Uniformity.HenselFactorization`
(`degree_sub_lt_of_monic_of_natDegree_eq`).
Sources: EFF.T2.11 (`(DEV)`, `(KEY-FREE)`, the `A₀ ≠ 0` derivation, `(WINDOW)`), EFF.T2.04
(inherited `T`), EFF.W12.23 (the unique monic-top development).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no `True` body, no
numeral threshold; the only new structure is the design-mandated `RealizedInput`.
-/

set_option linter.style.longLine false

/-! ## Generic development lemmas (B.02/B.05/B.06 companions)

These four lemmas live at the B-layer level of generality (any monic key of positive degree
over the standing bundle `O`); nothing about towers or carriers enters.  They are the exact
supply named by design §8 row C.130e. -/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Degree bound for the development coefficients in `natDegree` form (B.03's
`degree_dev_lt`, respelled for E.11's `natDegree`-valued `hdegA` field). -/
theorem natDegree_dev_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) (j : ℕ) : (dev φ f j).natDegree < φ.natDegree := by
  rcases eq_or_ne (dev φ f j) 0 with h | h
  · rw [h, Polynomial.natDegree_zero]; exact hd
  · exact Polynomial.natDegree_lt_natDegree h (degree_dev_lt hφ hd f j)

/-- The top development coefficient of a monic polynomial of exact degree `μ · deg φ` is `1`
(`EFF.W12.23`'s monic top; the `Φ^μ` head of `EFF.T2.11`'s `(DEV)`).  Proof: the family that
is `1` at `μ` and `dev φ (f - φ^μ)` below sums to `f`, so B.06's uniqueness identifies it with
`dev φ f`. -/
theorem dev_top_eq_one {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 1 ≤ μ)
    (hdeg : f.natDegree = μ * φ.natDegree) :
    dev φ f μ = 1 := by
  have hφμ : (φ ^ μ).Monic := hφ.pow μ
  set g : Polynomial O := f - φ ^ μ with hg
  have hgdeg : g.natDegree < μ * φ.natDegree := by
    rcases eq_or_ne g 0 with h0 | hne
    · rw [h0, Polynomial.natDegree_zero]
      exact Nat.mul_pos hμ hd
    · have hlt : g.degree < (f.natDegree : WithBot ℕ) :=
        Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hf hφμ
          (by rw [hφ.natDegree_pow, hdeg])
      have := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hlt
      omega
  have hbdeg : ∀ j, ((if j = μ then 1 else dev φ g j) : Polynomial O).degree < φ.degree := by
    intro j
    by_cases hj : j = μ
    · rw [if_pos hj]
      exact degree_lt_degree (by simpa using hd)
    · rw [if_neg hj]
      exact degree_dev_lt hφ hd g j
  have hbsum : ∑ j ∈ Finset.range (μ + 1),
      (if j = μ then (1 : Polynomial O) else dev φ g j) * φ ^ j = f := by
    rw [Finset.sum_range_succ, if_pos rfl, one_mul]
    have hcongr : ∑ j ∈ Finset.range μ,
        (if j = μ then (1 : Polynomial O) else dev φ g j) * φ ^ j
        = ∑ j ∈ Finset.range μ, dev φ g j * φ ^ j :=
      Finset.sum_congr rfl fun j hj => by
        rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
    rw [hcongr, sum_dev_eq hφ hd g hgdeg, hg]
    ring
  have h := dev_unique hφ hd hbdeg hbsum μ (Nat.lt_succ_self μ)
  rw [if_pos rfl] at h
  exact h.symm

/-- The monic-top development identity — `EFF.T2.11`'s `(DEV)` `F = Φ^μ + Σ_{j<μ} A_j Φ^j`
with `A_j = dev Φ F j` (`EFF.W12.23`: "Monic division gives the UNIQUE `Φ`-adic
development").  B.05's `sum_dev_eq` truncated one step past the degree, with the top term
evaluated by `dev_top_eq_one`. -/
theorem sum_dev_eq_monic_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 1 ≤ μ)
    (hdeg : f.natDegree = μ * φ.natDegree) :
    f = φ ^ μ + ∑ j ∈ Finset.range μ, dev φ f j * φ ^ j := by
  have hk : f.natDegree < (μ + 1) * φ.natDegree := by
    rw [hdeg, add_mul, one_mul]; omega
  have hsum := sum_dev_eq hφ hd f hk
  rw [Finset.sum_range_succ, dev_top_eq_one hφ hd hf hμ hdeg, one_mul] at hsum
  linear_combination -hsum

/-- The GENERIC `A₀ ≠ 0` lemma (design §8 row C.130e): `EFF.T2.11`'s own derivation
"(KEY-FREE) implies A₀ ≠ 0", as a theorem.  If the constant development coefficient
`dev φ f 0 = f %ₘ φ` vanished, `φ` would divide `f`, so its fraction-field image would divide
both coprime images and be a unit — impossible for a monic polynomial of positive degree. -/
theorem dev_zero_ne_zero_of_isCoprime {φ f : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree)
    (hcop : IsCoprime (f.map (algebraMap O (FractionRing O)))
      (φ.map (algebraMap O (FractionRing O)))) :
    dev φ f 0 ≠ 0 := by
  intro h0
  have h0' : f %ₘ φ = 0 := h0
  have hdvd : φ ∣ f := (Polynomial.modByMonic_eq_zero_iff_dvd hφ).mp h0'
  have hunit : IsUnit (φ.map (algebraMap O (FractionRing O))) :=
    hcop.isUnit_of_dvd' (Polynomial.map_dvd _ hdvd) dvd_rfl
  have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [hφ.natDegree_map] at hdeg0
  omega

end Uniformity.Density.Leaf

/-! ## `RealizedInput` and the input block -/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]

/-- The input degree ledger of an `ArisingCore`, closed under its own dictionary fields:
`deg F₀ = n = μ · stageDeg = μ · deg stageKey`. -/
theorem ArisingCore.F₀_natDegree {n : ℕ} (core : ArisingCore (O := O) Kt L n) :
    core.F₀.natDegree = core.μ * core.stageKey.natDegree := by
  rw [core.stageKey_degree, core.degree_input]
  exact core.degree_block

/-- ★ **CC-8 — `RealizedInput`** (design §4.4, byte-identical to the elaboration authority
`scratch/U11_carrier_check.lean`): the input-specific layer over `ArisingCore` and a
`ChainRealization` on the core's own tower.  "It reuses `ArisingCore`; the only new fields
are dictionary equalities and a selected legal point, never a socket conclusion."  The three
equalities are REPOSITORY DICTIONARIES (design §9); the point pair is EFF.GENTOW5.16's
selected legal node point at the core's live stage. -/
structure RealizedInput {n e' f' u' : ℕ} (core : ArisingCore Kt L n)
    (A : ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin)
      core.T Kt L e' f' u') where
  /-- Repository dictionary: the realization's terminal receiver is the core's. -/
  receiver_eq : A.receiver = core.receiver
  /-- Repository dictionary: the core's C.130b stage key is the key chain's `keyAt i`. -/
  stageKey_eq : core.stageKey = A.keys.keyAt core.i
  /-- Repository dictionary: the core's stage degree is C.83's cumulative `Dcum i`. -/
  stageDeg_eq : core.stageDeg = core.T.Dcum core.i
  /-- EFF.GENTOW5.16: a selected node point. -/
  point : A.node.Point
  /-- EFF.GENTOW5.16: the selected point is legal at the core's stage. -/
  point_mem : A.node.Pt core.i point

namespace RealizedInput

variable {n e' f' u' : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {A : ChainRealization (O := O) (π := core.π) (F := core.F)
    (H₀ := core.H₀) (hpin := core.hpin) core.T Kt L e' f' u'}

/-! ### The realized degree dictionary

`ArisingCore` does NOT carry positivity of `stageDeg`; it is the realization that supplies it
(`stageDeg_eq` + C130st's `Dcum_pos` on the live stage).  This is why the input block exists
only at a `RealizedInput`. -/

/-- Realized dictionary: the stage key's degree is the cumulative tower degree `Dcum i`. -/
theorem stageKey_natDegree (X : RealizedInput core A) :
    core.stageKey.natDegree = core.T.Dcum core.i :=
  core.stageKey_degree.trans X.stageDeg_eq

/-- Realized dictionary: the stage key has positive degree (via `Dcum_pos` at the core's
live stage — not an `ArisingCore` field). -/
theorem stageKey_natDegree_pos (X : RealizedInput core A) :
    0 < core.stageKey.natDegree := by
  rw [X.stageKey_natDegree]
  exact core.T.Dcum_pos core.hi.2

/-! ### The development and `A₀` supply, in core vocabulary -/

/-- `(DEV)` at the realized input: `F₀ = Φ^μ + Σ_{j<μ} dev Φ F₀ j · Φ^j` with
`Φ = core.stageKey` (B.02/B.05/B.06 through `sum_dev_eq_monic_top`; the positivity leg is the
realization's). -/
theorem F₀_dev (X : RealizedInput core A) :
    core.F₀ = core.stageKey ^ core.μ + ∑ j ∈ Finset.range core.μ,
      dev core.stageKey core.F₀ j * core.stageKey ^ j :=
  sum_dev_eq_monic_top core.stageKey_monic X.stageKey_natDegree_pos
    core.F₀_monic core.hμ core.F₀_natDegree

/-- `(KEY-FREE) ⟹ A₀ ≠ 0` at the realized input (the generic lemma, fired by
`core.keyfree`). -/
theorem F₀_dev_zero_ne_zero (X : RealizedInput core A) :
    dev core.stageKey core.F₀ 0 ≠ 0 :=
  dev_zero_ne_zero_of_isCoprime core.stageKey_monic X.stageKey_natDegree_pos core.keyfree

/-! ### The realized threshold predicate (design §5's display) -/

/-- Design §5's `CanonicalThresholdAt` at a realized occurrence — the DEFINITIONAL
specialization of C130th's carrier predicate at `(A.node, core.i, X.point)` (verdict CC-7's
standing note).  No numeral and no formula: the predicate pins `T` to the inherited datum. -/
def CanonicalThresholdAt (X : RealizedInput core A) (T : ℕ) : Prop :=
  A.node.CanonicalThresholdAt core.i X.point T

/-- Anti-drift pin: the realized predicate is byte-for-byte design §5's display. -/
theorem canonicalThresholdAt_def (X : RealizedInput core A) (T : ℕ) :
    X.CanonicalThresholdAt T ↔
      (T = A.node.thresholdNat core.i ∧
       (A.node.thresholdZ core.i : WithTop ℤ) <
           A.node.pointHgt core.i X.point (A.keys.keyAt core.i) ∧
       A.node.pointHgt core.i X.point (A.keys.keyAt core.i) ≠ ⊤) := Iff.rfl

/-! ### The producing theorem (row CC-8's `inputBlock`) -/

/-- ★ **CC-8, the producing theorem — freeze-v2 layer C.130e's `inputBlock`**: every realized
input yields E.11's `Ladder.BlockData` over CC-5's `stageCarrier` at the core's stage.

Field provenance (design §8 row C.130e: "reuse `ArisingCore`; use B.02/B.05/B.06 `dev`,
`core.keyfree`, the generic `A₀ ≠ 0` lemma, and `thresholdNat`"): `Φ`/`F`/`μ` and their laws
are `core`'s; `hΦdeg` is the `stageKey_degree` ∘ `stageDeg_eq` dictionary; `A` is B.02's
`dev` below `μ` and `0` above (E.11's convention, enforced); `hdev` is the monic-top
development identity; `hkeyfree` is `core.keyfree` VERBATIM; `hA0` is the generic
`(KEY-FREE) ⟹ A₀ ≠ 0` lemma; `T` is the INHERITED `A.node.thresholdNat core.i` — no numeral,
no formula, exactly CC-7's dictionary.  No block is stored in any carrier: this is a
derivation. -/
noncomputable def inputBlock (X : RealizedInput core A) :
    Ladder.BlockData (A.node.stageCarrier core.i core.hi) where
  Φ := core.stageKey
  F := core.F₀
  μ := core.μ
  hμ := core.hμ
  hΦ := core.stageKey_monic
  hΦdeg := X.stageKey_natDegree
  A := fun j => if j < core.μ then dev core.stageKey core.F₀ j else 0
  hdev := by
    show core.F₀ = core.stageKey ^ core.μ + ∑ j ∈ Finset.range core.μ,
      (if j < core.μ then dev core.stageKey core.F₀ j else 0) * core.stageKey ^ j
    have hcongr : ∑ j ∈ Finset.range core.μ,
        (if j < core.μ then dev core.stageKey core.F₀ j else 0) * core.stageKey ^ j
        = ∑ j ∈ Finset.range core.μ,
          dev core.stageKey core.F₀ j * core.stageKey ^ j :=
      Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
    rw [hcongr]
    exact X.F₀_dev
  hdegA := fun j hj => by
    show (if j < core.μ then dev core.stageKey core.F₀ j else 0).natDegree
      < (A.node.stageCarrier core.i core.hi).D
    rw [if_pos hj]
    exact lt_of_lt_of_eq
      (natDegree_dev_lt core.stageKey_monic X.stageKey_natDegree_pos core.F₀ j)
      X.stageKey_natDegree
  hkeyfree := core.keyfree
  hA0 := by
    show (if 0 < core.μ then dev core.stageKey core.F₀ 0 else 0) ≠ 0
    rw [if_pos (show 0 < core.μ by have := core.hμ; omega)]
    exact X.F₀_dev_zero_ne_zero
  T := A.node.thresholdNat core.i

/-! ### Anti-drift pins (all `rfl`): the block's fields are the realized data, verbatim -/

/-- Pin: the block's key is the core's C.130b stage key. -/
theorem inputBlock_Φ (X : RealizedInput core A) :
    X.inputBlock.Φ = core.stageKey := rfl

/-- Pin: the block's developed polynomial is the core's input `F₀`. -/
theorem inputBlock_F (X : RealizedInput core A) :
    X.inputBlock.F = core.F₀ := rfl

/-- Pin: the block's development length is the core's `μ`. -/
theorem inputBlock_μ (X : RealizedInput core A) :
    X.inputBlock.μ = core.μ := rfl

/-- Pin: the block's threshold is the INHERITED natural threshold of the carrier (CC-7's
dictionary; no numeral, no formula of `(W, i, F₀)`). -/
theorem inputBlock_T (X : RealizedInput core A) :
    X.inputBlock.T = A.node.thresholdNat core.i := rfl

/-- Dictionary pin: the block's key is the key chain's `keyAt` at the core's stage
(`stageKey_eq`, so the block and the carrier window speak about the SAME key). -/
theorem inputBlock_Φ_eq_keyAt (X : RealizedInput core A) :
    X.inputBlock.Φ = A.keys.keyAt core.i := X.stageKey_eq

/-! ### View 1 — development -/

/-- **Development view**: `(DEV)` in core vocabulary — `F₀ = Φ^μ + Σ_{j<μ} A_j Φ^j` with the
block's own coefficients. -/
theorem inputBlock_dev (X : RealizedInput core A) :
    core.F₀ = core.stageKey ^ core.μ + ∑ j ∈ Finset.range core.μ,
      X.inputBlock.A j * core.stageKey ^ j :=
  X.inputBlock.hdev

/-- Development view, coefficient read: below `μ` the block's coefficients are exactly B.02's
`dev` — canonical by B.06's uniqueness, not freely chosen tables. -/
theorem inputBlock_A_eq_dev (X : RealizedInput core A) {j : ℕ} (hj : j < core.μ) :
    X.inputBlock.A j = dev core.stageKey core.F₀ j := if_pos hj

/-- Development view, boundary read: at and above `μ` the block's coefficients are `0`
(E.11's stated convention, enforced rather than left informal). -/
theorem inputBlock_A_of_le (X : RealizedInput core A) {j : ℕ} (hj : core.μ ≤ j) :
    X.inputBlock.A j = 0 := if_neg (Nat.not_lt.mpr hj)

/-! ### View 2 — key-free -/

/-- **Key-free view**: `(KEY-FREE)` at the block's own fields (E.11's `IsCoprime` spelling
over `FractionRing O`). -/
theorem inputBlock_keyfree (X : RealizedInput core A) :
    IsCoprime (X.inputBlock.F.map (algebraMap O (FractionRing O)))
      (X.inputBlock.Φ.map (algebraMap O (FractionRing O))) :=
  X.inputBlock.hkeyfree

/-- Key-free view, core vocabulary: the block carries `core.keyfree` VERBATIM (the `F`/`Φ`
pins are definitional). -/
theorem inputBlock_keyfree_core (X : RealizedInput core A) :
    IsCoprime (core.F₀.map (algebraMap O (FractionRing O)))
      (core.stageKey.map (algebraMap O (FractionRing O))) :=
  X.inputBlock.hkeyfree

/-- Key-free view at the CARRIER's key: through the `stageKey_eq` dictionary, `F₀` is
key-free against the key chain's `keyAt` at the core's stage. -/
theorem inputBlock_keyfree_keyAt (X : RealizedInput core A) :
    IsCoprime (core.F₀.map (algebraMap O (FractionRing O)))
      ((A.keys.keyAt core.i).map (algebraMap O (FractionRing O))) := by
  rw [← X.stageKey_eq]
  exact core.keyfree

/-! ### View 3 — `A₀` -/

/-- **`A₀` view**: the consumed polygon shadow `A₀ ≠ 0` — derived from `(KEY-FREE)` by the
generic lemma, never assumed. -/
theorem inputBlock_A0_ne_zero (X : RealizedInput core A) :
    X.inputBlock.A 0 ≠ 0 :=
  X.inputBlock.hA0

/-- `A₀` view, coefficient read: the constant coefficient is B.02's `dev Φ F₀ 0 = F₀ %ₘ Φ`. -/
theorem inputBlock_A0_eq_dev (X : RealizedInput core A) :
    X.inputBlock.A 0 = dev core.stageKey core.F₀ 0 :=
  X.inputBlock_A_eq_dev (by have := core.hμ; omega)

/-! ### View 4 — threshold -/

/-- **Threshold view** (the design §5 theorem at the realized occurrence): the block's
inherited `T` IS canonical at `(A.node, core.i, X.point)`.  "The proof is projection plus the
dictionary equality; the mathematical content is the EFF.T2.11 `window` obligation" — consumed
at the core's live stage and the selected legal point. -/
theorem inputBlock_canonicalThreshold (X : RealizedInput core A) :
    X.CanonicalThresholdAt X.inputBlock.T :=
  A.node.canonicalThresholdAt_thresholdNat core.i core.hi X.point X.point_mem

/-- Threshold view, rigidity: on the realized occurrence, a candidate is canonical EXACTLY
when it is the block's inherited `T` — no arbitrary numeral can inhabit the predicate. -/
theorem canonicalThresholdAt_iff_inputBlock (X : RealizedInput core A) (T : ℕ) :
    X.CanonicalThresholdAt T ↔ T = X.inputBlock.T :=
  A.node.canonicalThresholdAt_iff core.i core.hi X.point X.point_mem T

/-- Threshold view, `(WINDOW)` at the block's OWN key: `T < d(Φ(ρ)) < ∞` with `Φ` the block's
key — the `stageKey_eq` dictionary makes the carrier window and the block key agree. -/
theorem inputBlock_window (X : RealizedInput core A) :
    ((X.inputBlock.T : ℕ) : WithTop ℤ)
        < A.node.pointHgt core.i X.point X.inputBlock.Φ ∧
      A.node.pointHgt core.i X.point X.inputBlock.Φ ≠ ⊤ := by
  rw [X.inputBlock_Φ, X.stageKey_eq]
  exact A.node.window_nat core.i core.hi X.point X.point_mem

end RealizedInput

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Leaf.natDegree_dev_lt
#print axioms Uniformity.Density.Leaf.dev_top_eq_one
#print axioms Uniformity.Density.Leaf.sum_dev_eq_monic_top
#print axioms Uniformity.Density.Leaf.dev_zero_ne_zero_of_isCoprime
#print axioms Uniformity.Density.Tower.ArisingCore.F₀_natDegree
#print axioms Uniformity.Density.Tower.RealizedInput
#print axioms Uniformity.Density.Tower.RealizedInput.stageKey_natDegree
#print axioms Uniformity.Density.Tower.RealizedInput.stageKey_natDegree_pos
#print axioms Uniformity.Density.Tower.RealizedInput.F₀_dev
#print axioms Uniformity.Density.Tower.RealizedInput.F₀_dev_zero_ne_zero
#print axioms Uniformity.Density.Tower.RealizedInput.CanonicalThresholdAt
#print axioms Uniformity.Density.Tower.RealizedInput.canonicalThresholdAt_def
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_Φ
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_F
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_μ
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_T
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_Φ_eq_keyAt
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_dev
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_A_eq_dev
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_A_of_le
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_keyfree
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_keyfree_core
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_keyfree_keyAt
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_A0_ne_zero
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_A0_eq_dev
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_canonicalThreshold
#print axioms Uniformity.Density.Tower.RealizedInput.canonicalThresholdAt_iff_inputBlock
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlock_window

end AxCheck
