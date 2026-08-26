/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130st
import Uniformity.ChapC.C130k2

/-!
# Uniformity.ChapC.C130th — the threshold dictionary and `CanonicalThresholdAt` (chain-carrier node CC-7)

**Chain-carrier node CC-7** (`CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.2, §5, §10 row CC-7):
the integer/natural threshold dictionary and the `CanonicalThresholdAt` predicate.  This node
is the carrier-level cure of the freeze-v2 layer C.130d that verdict C130A found BLOCKED
(recorded in `C130d.lean`): every object C130A named missing — the legal point class `Pt`, a
point `ρ`, the stage valuation `d`, the polynomial key `Φ_i`, the inherited threshold `T`, and
the window proof — now exists as CARRIED DATA of the landed `NodePointSource`/`KeyChain`
(C130k, node CC-1), so the predicate is finally stateable without inventing anything.

**[PK-2/U15, 2026-08-25]** — packaging-route view-binder ripple
(`PACKAGING_ROUTE_2026-08-25.md` §4/PK-2): every binder below is retyped un-split→split
(`NodePointSource` → `SplitNodePointSource`, C130k2), signature-only — the consumed fields
(`thresholdZ`/`thresholdNat`/`threshold_nonneg`/`window`/`pointHgt`/`point_exists`/
`key_value`) are byte-identical between the two structures, so every proof is byte-stable.
The un-split `NodePointSource` (C130k) survives only as the U13-refutation quarantine
record; prose mentions of it below are the historical CC-7 record.

## The design §5 ruling (quoted, and respected exactly)

> "EFF.T2.04 says the carrier has an **inherited** integer threshold.  EFF.T2.11 asserts
> `T < d(Φ(ρ)) < ∞`.  Neither row gives a formula for `T`, and C130A correctly found no
> function of `(DeepTower,i,F₀)` that determines it.  Therefore the threshold is an extra
> carrier input: `thresholdZ i`.  The window is a source law field.  `thresholdNat i` and
> `threshold_nonneg` are only the repository dictionary needed to fill E.11's current
> `BlockData.T : ℕ`."

Final ruling 3: "**Threshold:** extra inherited field, with WINDOW as a source law; not
derivable from `(DeepTower,i,F₀)`."

Accordingly, NOTHING below computes a threshold: there is **no numeral and no function of
`(W, i, F₀)`** anywhere in this file.  Every threshold-valued term is a projection of the
inherited `thresholdZ`/`thresholdNat` fields of a `NodePointSource` instance, and
`CanonicalThresholdAt` pins its `T` argument to that inherited datum — it cannot be inhabited
by an arbitrary numeral (`not_canonicalThresholdAt_of_ne`).

## The integer/natural dictionary (EFF.T2.04's `T ∈ 𝐙` vs E.11's `BlockData.T : ℕ`)

EFF.T2.04's inherited threshold is an INTEGER; E.11's landed `BlockData.T` is natural-valued.
The bridge is the `threshold_nonneg` source field (design §4.2: "the dictionary obligation
forced by the current natural-valued `BlockData.T`"; if a source instance has a genuinely
negative inherited threshold that field is uninhabitable and E.11 must be re-signed to `ℤ` —
no truncation to zero is allowed).  The derived dictionary here: `thresholdZ_nonneg`,
`thresholdZ_eq_natCast`, `thresholdNat_eq_toNat`, `thresholdNat_unique` (the ℕ avatar is
uniquely determined — the dictionary is rigid, not a choice), `coe_thresholdNat` (the
`WithTop ℤ` spelling used by the window), and `window_nat` (EFF.T2.11's `(WINDOW)` respelled
at the natural avatar).

## `CanonicalThresholdAt` (design §5's schematic, at the carrier level)

Design §5 ties the eventual theorem to a realized occurrence (`RealizedInput`, node CC-8).
CC-7 sits below CC-8 in the node DAG, so the predicate lands here in the carrier vocabulary —
a `NodePointSource` instance `S`, a stage `i`, a point `x`, a candidate `T : ℕ`:

* clause 1: `T` IS the inherited natural threshold (`T = S.thresholdNat i`);
* clauses 2–3: EFF.T2.11's `(WINDOW)` `T < d(Φ_i(ρ)) < ∞` at the point, with `d(Φ_i(ρ))`
  read as `S.pointHgt i x (K.keyAt i)` — an actual polynomial evaluation by `pointHgt_eval`.

CC-8's realized form is the definitional specialization at `(A.node, core.i, X.point)`, byte-
for-byte design §5's display.  The producing theorem `canonicalThresholdAt_thresholdNat` is
"projection plus the dictionary equality" (§5): its mathematical content is exactly the
`window` source obligation, consumed at a live stage and a legal point.  `keyAt i` has
`natDegree = Dcum i`, NOT `< Dcum i`, so no slot law applies to the key itself — the window is
irreducibly a source law, as the design demands.

## Teeth against the tower (no new data consumed)

At a gauge-live stage the `key_value` source law pins `d(Φ_i(ρ)) = u_{i+1}`, so the window
FORCES `thresholdZ i < u_{i+1}` (`thresholdZ_lt_u_succ`, point-free via `point_exists`) and
`thresholdNat i < u (i+1)` (`thresholdNat_lt_u_succ`).  These are consequences of carried
source laws, not new constraints: they show the inherited threshold interacts non-vacuously
with C.83's inherited height chain.

## Deliberately NOT here (later CC nodes)

`RealizedInput` and the threshold view on it, `inputBlock`, and the `BlockData.T` binding
(CC-8); any instantiation of `NodePointSource` (CC-6/CC-9); every socket application (CC-18).
No consumer structure is built and no carrier structure is inhabited here.

DEPENDS: C130st (CC-5: stage layer over `NodePointSource`), C130k (CC-1: `NodePointSource`,
`KeyChain`, live-range lint), C130a (CC-0: `StageLive`/`GaugeLive`), C83 (`DeepTower`).
Sources: EFF.T2.04 (inherited `T ∈ 𝐙`), EFF.T2.11 `(WINDOW)`.

## Status

Sorry-free, axiom-free (Lean core only); no new structure, no new axiom, no `unsafe`, no
numeral, no threshold formula.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uE uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

namespace SplitNodePointSource

/-! ## The integer/natural threshold dictionary

All of these are consequences of the single source field `threshold_nonneg`; none computes a
threshold.  Live-range guards are inherited from the field (the dictionary is only asserted
where the source asserts it). -/

/-- Dictionary: on the live range the inherited integer threshold is nonnegative (forced by
the `threshold_nonneg` source field — E.11's `BlockData.T : ℕ` could not otherwise be
filled without truncation, which is forbidden). -/
theorem thresholdZ_nonneg (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : 0 ≤ S.thresholdZ i := by
  have h := S.threshold_nonneg i hi
  omega

/-- Dictionary, ℤ-side spelling: the inherited integer threshold is the cast of its natural
avatar (the `threshold_nonneg` field, symmetrized). -/
theorem thresholdZ_eq_natCast (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : S.thresholdZ i = (S.thresholdNat i : ℤ) :=
  (S.threshold_nonneg i hi).symm

/-- Dictionary, ℕ-side spelling: the natural avatar is `Int.toNat` of the inherited integer
threshold.  This is a THEOREM about the carried pair, not a definition of `thresholdNat` —
the truncation direction is derivable only because `threshold_nonneg` holds. -/
theorem thresholdNat_eq_toNat (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : S.thresholdNat i = (S.thresholdZ i).toNat := by
  have h := S.threshold_nonneg i hi
  omega

/-- Dictionary rigidity: the natural avatar is the UNIQUE natural number casting to the
inherited integer threshold.  `thresholdNat` is a dictionary entry, not a free choice. -/
theorem thresholdNat_unique (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) {m : ℕ} (hm : (m : ℤ) = S.thresholdZ i) :
    m = S.thresholdNat i := by
  have h := S.threshold_nonneg i hi
  omega

/-- Dictionary at the window's value type: the two threshold casts agree in `WithTop ℤ`
(the codomain of `hgt`/`pointHgt`, where EFF.T2.11's `(WINDOW)` lives). -/
theorem coe_thresholdNat (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) :
    ((S.thresholdNat i : ℕ) : WithTop ℤ) = (S.thresholdZ i : WithTop ℤ) := by
  rw [← S.threshold_nonneg i hi, WithTop.coe_natCast]

/-- EFF.T2.11 `(WINDOW)` at the natural avatar: `T < d(Φ_i(ρ)) < ∞` with `T` read through
the dictionary.  Same source law, respelled for the ℕ-valued consumers (E.11's block). -/
theorem window_nat (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) (x : S.Point) (hx : S.Pt i x) :
    ((S.thresholdNat i : ℕ) : WithTop ℤ) < S.pointHgt i x (K.keyAt i) ∧
      S.pointHgt i x (K.keyAt i) ≠ ⊤ := by
  rw [S.coe_thresholdNat i hi]
  exact S.window i hi x hx

/-! ## `CanonicalThresholdAt` (freeze-v2 layer C.130d, per the design §5 ruling) -/

/-- ★ **CC-7 — freeze-v2 layer C.130d's `CanonicalThresholdAt`**, at the carrier level (the
design §5 schematic with `(A.node, core.i, X.point)` generalized to `(S, i, x)`; CC-8's
realized-occurrence form is the definitional specialization).

`S.CanonicalThresholdAt i x T` says: `T` is the INHERITED natural threshold of the carrier
(clause 1 — the design ruling: the threshold is an extra inherited field, "not derivable from
`(DeepTower,i,F₀)`", so the predicate PINS `T` to the carried datum instead of computing it),
and EFF.T2.11's `(WINDOW)` `T < d(Φ_i(ρ)) < ∞` holds at the point `x` (clauses 2–3, with
`d(Φ_i(ρ)) = S.pointHgt i x (K.keyAt i)`, an actual evaluation by `pointHgt_eval`). -/
def CanonicalThresholdAt (S : SplitNodePointSource (L := L) W E receiver K)
    (i : ℕ) (x : S.Point) (T : ℕ) : Prop :=
  T = S.thresholdNat i ∧
  (S.thresholdZ i : WithTop ℤ) < S.pointHgt i x (K.keyAt i) ∧
  S.pointHgt i x (K.keyAt i) ≠ ⊤

/-- Anti-drift pin: `CanonicalThresholdAt` is byte-wise its three design clauses. -/
theorem canonicalThresholdAt_def (S : SplitNodePointSource (L := L) W E receiver K)
    (i : ℕ) (x : S.Point) (T : ℕ) :
    S.CanonicalThresholdAt i x T ↔
      (T = S.thresholdNat i ∧
       (S.thresholdZ i : WithTop ℤ) < S.pointHgt i x (K.keyAt i) ∧
       S.pointHgt i x (K.keyAt i) ≠ ⊤) := Iff.rfl

/-- ★ The producing theorem (design §5: "the proof is projection plus the dictionary
equality; the mathematical content is the EFF.T2.11 `window` obligation"): at every live
stage and legal point, the inherited natural threshold IS canonical.  No other value is
(`not_canonicalThresholdAt_of_ne`). -/
theorem canonicalThresholdAt_thresholdNat (S : SplitNodePointSource (L := L) W E receiver K)
    (i : ℕ) (hi : StageLive r i) (x : S.Point) (hx : S.Pt i x) :
    S.CanonicalThresholdAt i x (S.thresholdNat i) :=
  ⟨rfl, S.window i hi x hx⟩

/-- Projection: a canonical threshold is the inherited natural threshold — nothing else can
inhabit the predicate.  (No guard needed: clause 1 is unconditional.) -/
theorem CanonicalThresholdAt.eq_thresholdNat
    {S : SplitNodePointSource (L := L) W E receiver K} {i : ℕ} {x : S.Point} {T : ℕ}
    (h : S.CanonicalThresholdAt i x T) : T = S.thresholdNat i := h.1

/-- Projection: the strict lower window bound `T < d(Φ_i(ρ))`, in the ℤ-threshold spelling. -/
theorem CanonicalThresholdAt.window_lt
    {S : SplitNodePointSource (L := L) W E receiver K} {i : ℕ} {x : S.Point} {T : ℕ}
    (h : S.CanonicalThresholdAt i x T) :
    (S.thresholdZ i : WithTop ℤ) < S.pointHgt i x (K.keyAt i) := h.2.1

/-- Projection: the finiteness window bound `d(Φ_i(ρ)) < ∞`. -/
theorem CanonicalThresholdAt.window_ne_top
    {S : SplitNodePointSource (L := L) W E receiver K} {i : ℕ} {x : S.Point} {T : ℕ}
    (h : S.CanonicalThresholdAt i x T) :
    S.pointHgt i x (K.keyAt i) ≠ ⊤ := h.2.2

/-- Rigidity: two canonical thresholds at the same stage and point are equal. -/
theorem CanonicalThresholdAt.unique
    {S : SplitNodePointSource (L := L) W E receiver K} {i : ℕ} {x : S.Point} {T T' : ℕ}
    (h : S.CanonicalThresholdAt i x T) (h' : S.CanonicalThresholdAt i x T') : T = T' :=
  h.1.trans h'.1.symm

/-- The no-arbitrary-numeral refuter (design §5: "C.130d should not introduce an opaque
predicate which can be inhabited by an arbitrary numeral"): any `T` other than the inherited
threshold is refuted, at every stage and point, with no liveness or legality needed. -/
theorem not_canonicalThresholdAt_of_ne (S : SplitNodePointSource (L := L) W E receiver K)
    (i : ℕ) (x : S.Point) {T : ℕ} (hT : T ≠ S.thresholdNat i) :
    ¬ S.CanonicalThresholdAt i x T := fun h => hT h.1

/-- Characterization on the honest domain (live stage, legal point): being canonical is
EXACTLY being the inherited natural threshold.  Forward is projection; backward consumes the
`window` source law. -/
theorem canonicalThresholdAt_iff (S : SplitNodePointSource (L := L) W E receiver K)
    (i : ℕ) (hi : StageLive r i) (x : S.Point) (hx : S.Pt i x) (T : ℕ) :
    S.CanonicalThresholdAt i x T ↔ T = S.thresholdNat i :=
  ⟨fun h => h.1, fun h => by
    rw [h]; exact S.canonicalThresholdAt_thresholdNat i hi x hx⟩

/-- The window at a canonical threshold, in the ℕ-cast spelling CC-8's block binding
consumes: `(T : WithTop ℤ) < d(Φ_i(ρ))`.  Needs the live guard for the dictionary leg. -/
theorem CanonicalThresholdAt.natCast_lt
    {S : SplitNodePointSource (L := L) W E receiver K} {i : ℕ} {x : S.Point} {T : ℕ}
    (h : S.CanonicalThresholdAt i x T) (hi : StageLive r i) :
    ((T : ℕ) : WithTop ℤ) < S.pointHgt i x (K.keyAt i) := by
  rw [h.eq_thresholdNat, S.coe_thresholdNat i hi]
  exact h.window_lt

/-! ## Teeth against the tower's inherited height chain

At a gauge-live stage the `key_value` source law reads `d(Φ_i(ρ)) = u_{i+1}` (C.83's
inherited stage height), so EFF.T2.11's window bounds the inherited threshold by inherited
tower data.  Point-free via `point_exists`.  These consume only carried source laws. -/

/-- The window forces `thresholdZ i < u_{i+1}` at every gauge-live stage: the inherited
threshold sits strictly below the next inherited stage height. -/
theorem thresholdZ_lt_u_succ (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hg : GaugeLive r i) : S.thresholdZ i < (W.u (i + 1) : ℤ) := by
  obtain ⟨⟨x, hx⟩⟩ := S.point_exists i hg.stageLive
  have hw := (S.window i hg.stageLive x hx).1
  rw [S.key_value i hg x hx] at hw
  exact_mod_cast hw

/-- The natural-avatar spelling: `thresholdNat i < u (i+1)` at every gauge-live stage
(dictionary + `thresholdZ_lt_u_succ`). -/
theorem thresholdNat_lt_u_succ (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hg : GaugeLive r i) : S.thresholdNat i < W.u (i + 1) := by
  have h1 := S.thresholdZ_lt_u_succ i hg
  have h2 := S.threshold_nonneg i hg.stageLive
  omega

end SplitNodePointSource

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdZ_nonneg
#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdZ_eq_natCast
#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdNat_eq_toNat
#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdNat_unique
#print axioms Uniformity.Density.Tower.SplitNodePointSource.coe_thresholdNat
#print axioms Uniformity.Density.Tower.SplitNodePointSource.window_nat
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalThresholdAt_def
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalThresholdAt_thresholdNat
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt.eq_thresholdNat
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt.window_lt
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt.window_ne_top
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt.unique
#print axioms Uniformity.Density.Tower.SplitNodePointSource.not_canonicalThresholdAt_of_ne
#print axioms Uniformity.Density.Tower.SplitNodePointSource.canonicalThresholdAt_iff
#print axioms Uniformity.Density.Tower.SplitNodePointSource.CanonicalThresholdAt.natCast_lt
#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdZ_lt_u_succ
#print axioms Uniformity.Density.Tower.SplitNodePointSource.thresholdNat_lt_u_succ

end AxCheck
