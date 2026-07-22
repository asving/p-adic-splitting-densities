/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.WildMenuW3
import LeanUrat.OM.MultiSlopeMenu
import LeanUrat.OM.QpTypeChain
import LeanUrat.OM.ChainMenu6
import LeanUrat.OM.ChainMenu7
import LeanUrat.OM.QpTypeSplitU

/-!
# OmLeafFaithful — the Montes-paper semantic axiom `om_leaf_faithful` (Wave 2b,
`notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md` §2 W2b; **RE-SCOPED 2026-07-21, Wave 3c** to the
K-windowed menu per `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 4; **RE-SCOPED AGAIN
2026-07-22, Wave 4c** to the mixed-e menu `MultiSlopeMenu.omMenu4` with the per-family fiber
dispatch `fiberOf4`, per `notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §W4c; **RE-SCOPED AGAIN
2026-07-22, Wave 5c — scope #4** to the depth-windowed chain menu `ChainMenu.omMenu5` with the
three-family fiber dispatch `fiberOf5`, per `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §2-W5c,
after completion of the boundary-#5 lift-invariance pin
`notes/GMN_citations.md` §"Lift/representative invariance — pin (P4)" — the DECLARATION GATE;
**RE-SCOPED AGAIN 2026-07-22, Wave 6c — scope #5** to the depth-0-widened menu
`ChainMenu6.omMenu6` — a pure MENU widening, fiber dispatch `fiberOf5` and conclusion
byte-identical — per `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §3; **RE-SCOPED AGAIN
2026-07-22, Wave 6q — scope #6** to the splitU-widened menu `ChainMenu7.omMenu7` with the
four-family fiber dispatch `fiberOf7`, per `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md`
§1.5/§3 — the general-`p` splitU literals `splitULit ms m` (keyed `{(1,1),(1,1)}`, honestly
EMPTY at `p = 2`), whose payload is GUARDED by the axiom-free masters of
`OM/QpTypeSplitU.lean` and REQUIRED to stay redundant-in-consumers)

Wave 1's σ-keying is DEFINITIONAL (`WildMenu.typeOfW` reads `(e,f)` off shape literals); Wave 2a
(`OM/QpType.lean`) built the genuine ℚ_p-factorization vocabulary (`LocalFactorData`,
`QpFactorization`, `qpType`). THIS module declares the ONE Wave-2 axiom tying the two together:

* `fiberOf4` — the UNIFIED per-family fiber predicate of the W4c re-scope: on multi-slope
  literals (head order-slot `1`) the genuine order-1 `classify1`/`InCell` fiber at the decoded
  menu cell; on every other shape the old `B.classify … = T` equation, byte-identical
  (unfolding lemmas `fiberOf4_mixed` / `fiberOf4_old`). This mirrors the PROVED Wave-4a
  counting fiber `MultiSlopeMenu.Fiber4` exactly (same discriminator `headOrd T = 1`, same
  decoded cell), so the axiom quantifies over the very fibers the Wave-4 counting model counts.
* `om_leaf_faithful` — **[CITE GMN]** every genuine monic `f : ℤ_[p][X]` that the level-`N`
  classifier ACTUALLY sends into the fiber of a shape of the Wave-4 σ-keyed menu
  `MultiSlopeMenu.omMenu4 n K σ` (∀ K — the K-windowed constant-e strata PLUS the one
  canonical mixed-e multi-slope stratum per mixed σ) has a genuine ℚ_p-factorization of type
  σ. MENU-FIBER-SCOPED; existence only; no uniformity / rationality / measure / density
  content. The W3 (omMenuW3, `B.classify`-fiber) instance is derived below as the THEOREM
  `om_leaf_faithful_w3`, and the `K = 1` Wave-2 form as `om_leaf_faithful_w1`
  (`WildMenuW3.omMenuW3_one`).
* `menuFiber_hasType` — the Wave-2 faithfulness theorem (footprint = core + the axiom; statement
  UNCHANGED by the W3c re-scope — routed through `om_leaf_faithful_w1`), and its σ-specialized
  corollary `gateFiber_hasType` at the Wave-1 wild gate
  (`T = Tselfloop 2 gateSide gateShape`, `σ = {(2,1)}`).
* **Mutation-consistency probe** (the axiom-safety evidence, blueprint §2 W2b last bullet):
  - `gateFiber_nonempty` — the gate fiber is INHABITED by a concrete named polynomial
    (`gatePoly = X² + 2X + 2` over `ℤ_[2]`, level `N = 3`), via the banked numeric gate
    `CellMenu.gate_S2C1` + the fiber characterization
    `ClassifierBridgeFiber2.classify_eq_selfloop_iff`. So the axiom's gate instance is NOT
    vacuous, and the mutation probe below genuinely fires.
  - the MUTATED axiom (same hypotheses, conclusion replaced by the SPLIT type `{(1,1),(1,1)}`)
    yields `False` against the PROVED Eisenstein irreducibility
    `QpType.wildGateFiber_eisenstein` — machine-checked in a scratch file (NOT committed; its
    verbatim text and output are recorded in the `Mutation probe evidence` comment block below).
  - `gate_axiom_coherent` — the POSITIVE coherence check: the real axiom's concrete gate instance
    (type `{(2,1)}`, a singleton factorization) COEXISTS with the proved irreducibility.

**Why `0 < N` (no decision-threshold hypothesis) is sound** (audit note; W3c: verbatim per
window leg): a nonempty `B.classify`-fiber of a menu shape forces the level to exceed the
shape's decision threshold. The wild k-leg literal
`Tselfloop n ((0, fSum σ · k), (n, 0)) (wShape σ)` carries its side in the emitted face payload,
and the classifier only emits sides read from the box Newton polygon, whose support dots have
box valuation `< N` (`PadicLift.zmodValuation_lt`); a left vertex `(0, fSum σ · k)` in the fiber
therefore forces `fSum σ · k < N`, i.e. exactly the `MenuPath` range in which
`classify_eq_selfloop_iff` proves the fiber IS the genuine stratum, whose digit conditions decode
to genuine `ℤ_[p]`-valuation data (`QpType.valuation_eq_of_zmodValuation_lt`). Below the leg's
own threshold the fiber is EMPTY (the banked count-level form is
`WildMenuW3.stratumCount_ramShapeAt_smallN`) and the axiom instance is vacuous. The order-0
separable leg reads only the mod-`p` reduction, decided at every `N ≥ 1`. **W4c addendum
(mixed branch)**: the mixed fiber hypothesis IS an `InCell` membership (`classify1`), which
carries its own threshold — `InCell` requires a level-`N` `MenuPath`, whose left vertex forces
`H_total = fSum σ ≤ N − 1`; below the canonical threshold the mixed fiber is EMPTY
(`MultiSlopeMenu.stratumCount4_mixed_smallN`) and the instance vacuous; in the readable range
the `Matches` digit conditions decode to genuine `ℤ_[p]`-valuation data exactly as above
(anchor: `OM/QpTypeMixed.lean`, `mixedGateFiber_valuation`).

Leaf module discipline (unchanged): exactly ONE axiom, zero `sorry`. **W3c change record
(2026-07-21)**: the axiom's menu hypothesis was re-scoped from `WildMenu.omMenuW n σ` (K = 1
only) to `(K : ℕ) … WildMenuW3.omMenuW3 n K σ`; everything else in the statement was
byte-identical. **W4c change record (2026-07-22)**: the menu hypothesis is re-scoped from
`WildMenuW3.omMenuW3 n K σ` to `MultiSlopeMenu.omMenu4 n K σ` and the fiber hypothesis from
the bare `B.classify … = T` equation to the per-family dispatch `fiberOf4` (see its docstring
for the vacuity trap this avoids); everything else is byte-identical. The W3 form survives as
the derived THEOREM `om_leaf_faithful_w3` (definitional on old shapes), and the Wave-2/W1 form
as `om_leaf_faithful_w1`, so all consumers compile unchanged. The H = 3 axiom-free anchor +
the W3c mutation probes live in `OM/QpTypeH3.lean`; the mixed-gate (n = 5) axiom-free anchor +
the W4c mutation probes live in `OM/QpTypeMixed.lean`.

**W5c change record (2026-07-22, scope #4)**: the menu hypothesis is re-scoped from
`(K : ℕ) … MultiSlopeMenu.omMenu4 n K σ` to `(D K : ℕ) … ChainMenu.omMenu5 n D K σ` (the W4
menu ∪ the depth-`≤ D` n = 2 descent chains — general `n` kept for the old families; chains
are only ever emitted at `n = 2` per W5b's `chainShapes`), and the fiber hypothesis from
`fiberOf4` to the three-family dispatch `fiberOf5` (chain heads, `headOrd T = 2`: the PROVED
Wave-5a/5b counting fiber `ChainMenu.ChainCell` at the decoded chain index; every other head:
`fiberOf4`, byte-identical). Everything else is byte-identical. The W4 form survives as the
derived THEOREM `om_leaf_faithful_w4` (menu leg by `ChainMenu.omMenu5_zero` at `D = 0`, fiber
leg definitional via `fiberOf5_notChain` + `ChainMenu.headOrd_of_mem_omMenu4`), and the
W3c/W2 forms keep deriving as before, so all consumers compile unchanged. **The chain branch's
semantic content** (axiom docstring below): per-step lift invariance — pin (P4),
`notes/GMN_citations.md` — + Cor 1.20 (ram leaves) resp. the order-0 Hensel/Thm 1.19 reads
(inert/split leaves) applied to the genuine recentered polynomial in the FINAL staircase
frame, composed back by the PROVED translation lemma `QpTypeChain.qpType_translate_rescale`.
The depth-1 chain-gate axiom-free anchor + the W5c mutation probes live in
`OM/QpTypeChain.lean` (`chainGate_irreducible`, `chainGate_ef_forced`); the positive coherence
check at the chain gate is `chainGate_axiom_coherent` below.

**W6c change record (2026-07-22, scope #5)**: the menu hypothesis is re-scoped from
`(D K : ℕ) … T ∈ ChainMenu.omMenu5 n D K σ` to `(D K : ℕ) … T ∈ ChainMenu6.omMenu6 n D K σ`
(the W5 menu ∪ the depth-0 leaf literals `chainLit [] leaf`, `leaf ∈ chainLeaves K σ`,
`n = 2` only — `ChainMenu6.chainShapes0`, the `chainShapes` emission without the `ms ≠ []`
filter); the fiber hypothesis `fiberOf5` and the conclusion are BYTE-IDENTICAL (`fiberOf5`
already dispatches chain-headed literals — including the new depth-0 ones — to
`ChainMenu.ChainCell (decodeMs T) (decodeLeaf T)`, which at `ms = []` is the `LeafPair`
digit fiber the W6 full model counts). The W5 form survives as the derived THEOREM
`om_leaf_faithful_w5` (menu leg `ChainMenu6.omMenu5_subset_omMenu6`; fiber leg verbatim),
and the W4/W3/W2 chains keep deriving as before, so all consumers compile unchanged. The
per-literal GMN statement map for the three depth-0 literal kinds is in the axiom docstring
below (blueprint `WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §3 — the declaration-gate content for
the new instances).

**W6q change record (2026-07-22, scope #6)**: the menu hypothesis is re-scoped from
`ChainMenu6.omMenu6 n D K σ` to `ChainMenu7.omMenu7 n D K σ` (the W6 menu ∪ the general-`p`
splitU literals `ChainMenu7.splitULit ms m` — `ms ∈ msMenu D K`, depth 0 included,
`m ∈ Icc 1 K`; `n = 2`, `σ = splitType2` ONLY), and the fiber hypothesis from `fiberOf5` to
the four-family dispatch `fiberOf7` (splitU heads, `headOrd T = 3` — a FRESH order slot,
chosen because a `(2, ·, ·)` head would be MIS-decoded by the chain branch (see
`ChainMenu7`'s head-encoding audit): the PROVED W6q-a counting fiber
`ChainMenu7.ChainCellU` at the exact decode `decodeMs`/`decodeMU`; every other head:
`fiberOf5`, byte-identical). Everything else is byte-identical. The W6c form survives as
the derived THEOREM `om_leaf_faithful_w6` (menu leg `ChainMenu7.omMenu6_subset_omMenu7`;
fiber leg `fiberOf7_not_splitU` + `ChainMenu7.headOrd_ne_three_of_mem_omMenu6`), the W5
derivation is repointed through it (statement unchanged), and the W4/W3/W2 chains keep
deriving as before. **The splitU legs are split-keyed, hence — per the blueprint §3
REQUIREMENT — REDUNDANT-IN-CONSUMERS**: their entire payload is PROVED axiom-free in
`OM/QpTypeSplitU.lean` (masters + unwind + translate, core-only footprints), consumers must
fire those masters and never this axiom's splitU instances, and a census line showing the
axiom inside a split-keyed corollary's cone is a stop-the-line defect. The `p = 3` witness
gates + the wrong-keying mutation probe live in Block 5c below; at `p = 2` the splitU pool
is honestly EMPTY (`ChainMenuU.rootedPairs_two_empty`).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.OmLeafFaithful

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## Block 1 — the unified fiber predicate and the axiom -/

/-- **The unified per-family fiber predicate** (W4c, blueprint `WILD_WAVE4` §W4c statement-design
point). The Wave-4 menu `MultiSlopeMenu.omMenu4` mixes TWO fiber notions, dispatched by the
family discriminator `headOrd T = 1` (which separates the multi-slope literals from every old
shape — `MultiSlopeMenu.headOrd_multiSideLit` vs `headOrd_of_mem_omMenuW3`):

* multi-slope literals (`headOrd T = 1`): the GENUINE order-1 fiber
  `classify1 p (toBox …) = some (mkCell n (decodePath T) (decodeShapes T))` — the
  `classify1`/`InCell` fiber at the decoded menu cell;
* every old shape: the old equation `B.classify p n N (toBox …) = T`, byte-identical to the
  W2/W3 axiom's hypothesis (`fiberOf4_old` is definitional).

**The vacuity trap this dispatch avoids** (the V1 failure mode): `B.classify` reads only the
FIRST Newton side and can never emit a multi-slope literal (recorded no-go, `WILD_WAVE4` §1),
so keeping the bare `B.classify … = T` hypothesis over the enlarged menu would make every
mixed instance of the axiom vacuously true — true but empty. The dispatch instead mirrors the
PROVED Wave-4a counting fiber `MultiSlopeMenu.Fiber4` exactly (same discriminator, same
decoded cell, `Fiber4` being its box-level `M9.realP` counterpart), so the axiom quantifies
over the very fibers the Wave-4 counting model counts. -/
def fiberOf4 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (T : ClusterShape)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n) : Prop :=
  if MultiSlopeMenu.headOrd T = 1 then
    classify1 p (PadicLift.toBox p n N hN f hf hdeg)
      = some (mkCell n (MultiSlopeMenu.decodePath T) (MultiSlopeMenu.decodeShapes T))
  else B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T

/-- `fiberOf4` on a multi-slope literal IS the genuine order-1 `classify1` fiber at the decoded
cell. -/
theorem fiberOf4_mixed (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T = 1) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf4 p n N hN T f hf hdeg
      ↔ classify1 p (PadicLift.toBox p n N hN f hf hdeg)
          = some (mkCell n (MultiSlopeMenu.decodePath T) (MultiSlopeMenu.decodeShapes T)) := by
  unfold fiberOf4
  rw [if_pos hT]

/-- `fiberOf4` on every old (non-multi-slope-headed) shape IS the old `B.classify` equation —
the W2/W3 fiber hypothesis, byte-identical. -/
theorem fiberOf4_old (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T ≠ 1) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf4 p n N hN T f hf hdeg
      ↔ B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T := by
  unfold fiberOf4
  rw [if_neg hT]

/-- **The unified three-family fiber predicate** (W5c, blueprint `WILD_WAVE56` §2-W5c). The
Wave-5 menu `ChainMenu.omMenu5` adds the chain literals (head order-slot `2`,
`ChainMenu.headOrd_chainLit`, never produced by any W4 shape —
`ChainMenu.headOrd_of_mem_omMenu4`); on them the fiber is the PROVED Wave-5a/5b counting
fiber `ChainMenu.ChainCell` at the decoded chain index (`decodeMs`/`decodeLeaf` — exact
decode, `ChainMenu.chainLit_injective`), i.e. the very digit fibers `stratumCount5` counts;
on every other head it is `fiberOf4`, byte-identical. (Same anti-vacuity design as `fiberOf4`:
the old classifiers never emit a chain literal, so keeping `fiberOf4` over the enlarged menu
would make every chain instance vacuously true — true but empty.) -/
def fiberOf5 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (T : ClusterShape)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n) : Prop :=
  if MultiSlopeMenu.headOrd T = 2 then
    ChainMenu.ChainCell p (ChainMenu.decodeMs T) (ChainMenu.decodeLeaf T)
      (PadicLift.toBox p n N hN f hf hdeg)
  else fiberOf4 p n N hN T f hf hdeg

/-- `fiberOf5` on a chain literal IS the genuine `ChainCell` digit fiber at the decoded chain
index. -/
theorem fiberOf5_chain (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T = 2) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf5 p n N hN T f hf hdeg
      ↔ ChainMenu.ChainCell p (ChainMenu.decodeMs T) (ChainMenu.decodeLeaf T)
          (PadicLift.toBox p n N hN f hf hdeg) := by
  unfold fiberOf5
  rw [if_pos hT]

/-- `fiberOf5` on every non-chain-headed shape IS `fiberOf4` — the W4c fiber hypothesis,
byte-identical. -/
theorem fiberOf5_notChain (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T ≠ 2) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf5 p n N hN T f hf hdeg ↔ fiberOf4 p n N hN T f hf hdeg := by
  unfold fiberOf5
  rw [if_neg hT]

/-- **The unified four-family fiber predicate** (W6q, blueprint `WILD_WAVE6Q` §3). The
Wave-6q menu `ChainMenu7.omMenu7` adds the splitU literals (head order-slot `3`,
`ChainMenu7.headOrd_splitULit`, carried by NO earlier menu shape —
`ChainMenu7.headOrd_ne_three_of_mem_omMenu6`); on them the fiber is the PROVED W6q-a
counting fiber `ChainMenu7.ChainCellU` at the exact decode (`decodeMs`/`decodeMU` —
`ChainMenu7.splitULit_injective`), i.e. the very `ChainPairU` digit fibers the W6q model
counts; on every other head it is `fiberOf5`, byte-identical. (Same anti-vacuity design as
`fiberOf4`/`fiberOf5`: no old classifier or dispatch ever emits/reads a splitU head — a
`headOrd = 3` literal under `fiberOf5` would fall through to the vacuous `B.classify`
equation, true but empty; the new branch instead quantifies over the counted fibers.
Head-encoding audit: `headOrd` reads the FIRST tree component, so the tempting
`(2, 3, len)` head would be dispatched to the CHAIN branch and MIS-decoded by
`decodeLeaf`'s wildcard — hence the fresh slot `3`; see `ChainMenu7`.) -/
def fiberOf7 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (T : ClusterShape)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n) : Prop :=
  if MultiSlopeMenu.headOrd T = 3 then
    ChainMenu7.ChainCellU p (ChainMenu.decodeMs T) (ChainMenu7.decodeMU T)
      (PadicLift.toBox p n N hN f hf hdeg)
  else fiberOf5 p n N hN T f hf hdeg

/-- `fiberOf7` on a splitU literal IS the genuine `ChainCellU` digit fiber at the decoded
splitU index. -/
theorem fiberOf7_splitU (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T = 3) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf7 p n N hN T f hf hdeg
      ↔ ChainMenu7.ChainCellU p (ChainMenu.decodeMs T) (ChainMenu7.decodeMU T)
          (PadicLift.toBox p n N hN f hf hdeg) := by
  unfold fiberOf7
  rw [if_pos hT]

/-- `fiberOf7` on every non-splitU-headed shape IS `fiberOf5` — the W6c fiber hypothesis,
byte-identical. -/
theorem fiberOf7_not_splitU (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T ≠ 3) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf7 p n N hN T f hf hdeg ↔ fiberOf5 p n N hN T f hf hdeg := by
  unfold fiberOf7
  rw [if_neg hT]

/-- **[CITE] GMN (Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
theory*, TAMS 364 (2012); arXiv:0807.2620v2) Thm 1.15 + Thm 1.19 + Cor 1.20 — the order-1
dissections with the explicit leaf `(e,f)` (Thm 1.15, Theorem of the polygon: one coprime
factor block per side of pairwise-distinct slope; Thm 1.19, Theorem of the residual polynomial:
one coprime factor per residual irreducible; Cor 1.20: `a_i = 1 ⟹ G_i` irreducible,
`f(L/K) = m·deg ψ_i`, `e(L/K) = e`) — these being the order-≤1 instances of Thm 3.1 / Thm 3.7 /
Cor 3.8 — plus Def 3.10 / eq. (37) (the assembled OM factorization `f = f_{r,∞} · ∏ f_t`),
TOGETHER WITH the standard structure theory of local fields the paper presupposes (the integer
ring of a finite extension of `ℚ_p` is a DVR, module-finite over `ℤ_p`, with the
residue/ramification bookkeeping; Serre, *Local Fields*, Ch. I–II) — packaged as the existence
of the `QpType.LocalFactorData` bundles (mathlib at the pin cannot prove DVR-ness of
`integralClosure ℤ_[p] L` for wild `L`; that existence content is exactly what this axiom
carries, cf. `OM/QpType.lean` header and `notes/GMN_citations.md` §§1–2).**

**MENU-FIBER-SCOPED** (the arising-shape restriction — the house discipline of
`B.omReadValuation_lt_of_certLevel_fkeyed`): quantified ONLY over genuine monic `f : ℤ_[p][X]`
that the level-`N` classifier ACTUALLY sends into the `fiberOf7`-fiber of a shape `T` of the
CURRENT Wave-6q σ-keyed menu `ChainMenu7.omMenu7 n D K σ` (order-0 separable `sepShape`s ∪
the constant-e `Tselfloop` window strata at all admissible heights `H = fSum σ · k`,
`gcd(k, e) = 1`, `1 ≤ k ≤ K`, ∪ — for mixed-all-e≥2 σ — the ONE canonical multi-slope literal
`multiSideLit n (mixedPath σ) (mixedSh σ)`, ∪ — at `n = 2` ONLY — the depth-`≤ D` descent
chains `chainLit ms leaf` with leaf keyed to σ, ∪ — at `n = 2` ONLY (W6c) — the depth-0
leaf literals `chainLit [] leaf` with `leaf ∈ ChainMenu.chainLeaves K σ`, ∪ — at `n = 2`,
`σ = splitType2` ONLY, NEW (W6q) — the splitU literals `ChainMenu7.splitULit ms m` with
`ms ∈ msMenu D K` (depth 0 included) and `m ∈ Icc 1 K`; nothing else;
∀ D K). A nonempty fiber forces
the level past the shape's own decision threshold (module docstring; small-N emptiness =
`WildMenuW3.stratumCount_ramShapeAt_smallN` resp. `MultiSlopeMenu.stratumCount4_mixed_smallN`
resp. `ChainMenu.card_chainCell_smallN` for the chain branch — below the threshold
`2·Σms + leafNeed` the `ChainCell` fiber is EMPTY, `ChainMenu.chainPair_empty` — resp.
`ChainMenuU.chainPairU_empty` for the splitU branch, threshold `2·Σms + leafNeedU m`),
where the banked fiber characterizations (`Order0`,
`ClassifierBridgeFiber2.classify_eq_selfloop_iff`, `CellMenu.inCell_mkCell_iff`) exhibit the
fiber as the genuine Ore/GMN stratum:

* squarefree order-0 residue with partition λ ⟹ Hensel factors, type `{(1, dᵢ)}`;
* single-side polygon `(0, fSum σ · k)–(n, 0)` with all-μ=1 residual of degrees `fᵢ` —
  **Cor 1.20 applies VERBATIM to every window leg**: each k-leg is single-slope all-μ=1 with
  the SAME side degree `sideDeg = gcd(fSum σ · k, n) = fSum σ` (`WildMenuW3.gcd_admissible`)
  and the SAME residual shape `wShape σ`, so the Thm 1.19/Cor 1.20 leaves carry type
  `{(n/fSum σ, fᵢ)} = σ` at every admissible height;
* NEW (W4c), the mixed multi-slope stratum: the `classify1`/`InCell` fiber pins (via
  `Matches`) the full multi-slope polygon — vertices exact, all dots on-or-above — with
  strictly increasing slopes `−1/e_j`, one side per distinct `e_j` of σ, and per-side all-μ=1
  separable residuals with parts of degrees `f`. **Thm 1.15 (slope dissection)** splits `f`
  into one coprime factor block per side; per side, **Thm 1.19 + Cor 1.20** (`a_i = 1`,
  `m = 1`, slope `−1/e_j` in lowest terms) make every residual part an irreducible leaf with
  `(e(L/K), f(L/K)) = (e_j, f)`; the assembled `(e,f)`-multiset is exactly
  `σ = ⋃_j {(e_j, f) : f a part of side j}` — the same multiset the definitional decoder
  recovers (`MultiSlopeMenu.typeOf4_multiSideLit`).
* NEW (W5c), the `n = 2` descent-chain strata: the `ChainCell` fiber pins (via the PROVED
  staircase machinery, `RecenterBox.stratumPairEquiv` + `ChainMenu.ChainPair`) the per-step
  (S1)∧(S2) digit conditions of the whole-window recenterings `x ↦ ĉ_t p^{m_t} + p^{m_t}·x`
  composed through the chain, and the terminating leaf's digit conditions in the FINAL
  staircase frame. Semantic content, per the completed boundary-#5 pin
  (`notes/GMN_citations.md` §(P4), the W5c DECLARATION GATE, completed 2026-07-22):
  (i) **lift invariance (P4a–P4c)** — each recentered read is a genuine Ore/GMN order-1 read
  of `f` at the shifted degree-1 key polynomial `φ = x − ĉp^m`, inside GMN §1.2's stated
  arbitrary-monic-lift scope, per admissible choice of lift (GMN §1.5: the data are
  non-intrinsic, the dissections and their leaf `(e,f)` hold per choice; Def 2.12 sequel and
  Def 3.10 remark at order `r`); (ii) **the leaf read in the final frame** — the genuine
  recentered polynomial `g` (itself monic over `ℤ_[p]`) satisfies the W1-shaped leaf
  conditions, where **Cor 1.20** (`ram H`: single side `(0,H)–(2,0)`, `d(S) = 1` ⟹
  irreducible with `(e,f) = (2,1)`) resp. the order-0 Hensel/Thm 1.19 reads (`inert`/`split`)
  give `g`'s factorization of the leaf's type; (iii) **the transport back is PROVED, not
  imported** — `QpTypeChain.qpType_translate_rescale` carries `g`'s factorization to `f` with
  the same type along `f(p^m·y + ĉp^m) = p^{2m}·g(y)` (per (P4d) the paper does not state a
  translation form; the lift-choice independence `ĉ ↦ ĉ + pδ` is the pure-translation instance
  of the same proved lemma). The AXIOM-FREE depth-1 anchor `QpTypeChain.chainGate_irreducible`
  + `chainGate_ef_forced` machine-checks exactly this composite at the `ms = [1]`, `ram 1`
  gate: fiber ⟹ `f` irreducible over ℚ_p with EVERY bundle forced to `(e,f) = (2,1)`.
* NEW (W6c), the `n = 2` DEPTH-0 leaf literals `chainLit [] leaf`, `leaf ∈ chainLeaves K σ`
  (`ChainMenu6.chainShapes0` — the scope-#5 menu widening; `fiberOf5` dispatches them, via
  `decodeMs`/`decodeLeaf`, to `ChainCell [] leaf`, i.e. the `LeafPair leaf` digit fiber at
  the ROOT frame `(N, N)` — no recentering step, no lift choice; these are formally NEW
  digit-form fiber predicates for the axiom, so their GMN statement map is displayed PER
  LITERAL (blueprint `WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §3, the declaration-gate content
  for the new instances):
  - **`chainLit [] (ram H)`** (`H` odd, `leafOK`): the `LeafPair` conditions `v(b₀) = H`
    EXACT (box dvd + nonzero digit at `H`, readable since `leafNeed = H + 1 ≤ L₀`) and
    `v(b₁) ≥ (H+1)/2` pin the principal Newton polygon of `y² + b₁y + b₀` to the single side
    `(0,H)–(2,0)`: the middle dot `(1, v(b₁))` lies strictly above it since
    `v(b₁) ≥ (H+1)/2 > H/2`. Slope `−H/2` with `gcd(H, 2) = 1` ⟹ `d(S) = 1`: **Cor 1.20**
    gives exactly one irreducible factor with `(e,f) = (2,1)`. This is the same Cor-1.20
    reading the W1/W3 window legs receive (there routed through the classify-fiber
    characterization; here directly from the digits) — same cited theorem, new instance
    form; guarded by the W6c-a all-fiber ram master (R) at ALL odd `H` (strictly stronger
    than the banked `H ∈ {1, 3}` anchors).
  - **`chainLit [] (inert m)`** (`m ≥ 1`): `v(b₀) = 2m` exact (the root-free pair's first
    digit is nonzero — `noRootPairs_fst_ne_zero`), `v(b₁) ≥ m`: single side `(0,2m)–(2,0)`
    of slope `−m = −m/1` in lowest terms ⟹ `e = 1`, side degree 2, residual = the digit
    quadratic `z² + w̄₁z + w̄₀`, root-free hence irreducible: **Thm 1.19 + Cor 1.20** give
    one leaf with `(e,f) = (1,2)`. Guarded by the W6c-a all-fiber inert master (I).
  - **`chainLit [] (split k)`** (`k ≥ 1`): `v(b₁) = k` exact (with nonzero digit, so
    `b₁ ≠ 0`), `v(b₀) ≥ 2k+1`, readability gate `2k+1 ≤ L₀`. Case `b₀ ≠ 0`: polygon
    vertices `(0, v(b₀))–(1, k)–(2, 0)` with DISTINCT slopes (left side slope
    `−(v(b₀) − k) ≤ −(k+1) < −k` = right side slope): **Thm 1.15** dissects into two
    coprime width-1 (hence linear) blocks, each `(e,f) = (1,1)`. Case `b₀ = 0` (ADMITTED by
    the fiber): `g = y·(y + b₁)` factors LITERALLY into two linear (hence `(1,1)`) factors
    — the GMN reading applies via the standard split-off of the x-power factor (the paper's
    `f = x^{ord₀ f}·f′` convention) and the width-1 side `(1,k)–(2,0)` for `f′`; no finite
    point `(0, v(b₀))` exists and none is needed. Both cases guarded by the W6c-a split
    master (S), whose proof uses only `v(b₀) ≥ 2k+1` (`w₀ = 0` allowed) — indeed for split
    literals the certificate is PROVED outright (axiom-free) and the axiom instance is
    REDUNDANT in consumers (kept in the menu for uniform emission).
  Ram/inert existence for the new literals rests on the axiom exactly as every
  irreducible-leaf leg has since W2 (the Serre `LocalFactorData` carrier); "no new citation"
  means: same cited theorems (Thm 1.15/1.19/Cor 1.20 + the carrier), new INSTANCES,
  statement-mapped above. Translate (`c = 1`) coverage is deliberately NOT in the axiom —
  the (P4d) discipline: the paper states no translation form, so none may enter; translate
  coverage is DERIVED (blueprint §1.3, the PROVED `QpTypeChain.qpType_translate_rescale` at
  `a = 1`).
* NEW (W6q), the `n = 2` general-`p` SPLITU literals `splitULit ms m` (`m ≥ 1`, window
  `(D, K)`, `σ = splitType2` only — `ChainMenu7.splitUShapes`; `fiberOf7` dispatches them,
  via the exact decode `decodeMs`/`decodeMU`, to `ChainMenu7.ChainCellU ms m` — the
  `ChainMenuU.ChainPairU` digit fiber: the SAME per-step (S1)∧(S2) recentering reads as the
  chain literals, same `StratumPair`/`descendPair` machinery, same (P4) lift-invariance
  pin, terminating in the splitU leaf `LeafPairU m` in the final staircase frame:
  `v(b₀) = 2m` EXACT (the rooted pair's constant digit is nonzero —
  `ChainMenuU.rootedPairs_fst_ne_zero`), `v(b₁) ≥ m`, residual digit pair in
  `ChainMenuU.rootedPairs p` — two DISTINCT roots, both nonzero). **Statement map (per
  literal, blueprint §3)**: single side `(0, 2m)–(2, 0)`, slope `−m/1` in lowest terms ⟹
  `e = 1`, side degree 2; residual = the digit quadratic `z² + w̄₁z + w̄₀`, separable with
  two distinct linear factors ⟹ **Thm 1.19**: TWO coprime factors, each with
  `(e, f) = (1, 1)` by **Cor 1.20** (`a_i = 1`, `deg ψ_i = 1`); assembled type
  `{(1,1),(1,1)} = splitType2`. **Guard + REQUIREMENT (blueprint §3, Codex pass-1 gap
  #2)**: the entire splitU payload is PROVED AXIOM-FREE by the `OM/QpTypeSplitU.lean`
  masters (`leafSplitU_master_hasType` through `transChainFiberU_split_hasType` — the
  root-generic Hensel at `h̄'(r̄) = r̄ − s̄ ≠ 0`, char-2-safe, plus the transcribed unwind
  and the general-`p` translate commutation `transBoxP_comp`), so these axiom instances are
  REDUNDANT-IN-CONSUMERS **by requirement, not observation**: every split-keyed consumer
  branch MUST fire the axiom-free masters, never this leg; split-keyed corollaries are
  packaged with machine-checked CORE-ONLY footprints, and a census line showing this axiom
  inside a split-keyed corollary's cone is a stop-the-line defect. The legs are kept on the
  menu for uniform emission only. Non-vacuity: the `p = 3` witness `y² + 9y + 18` (Block 5c;
  pool nonempty ⟺ `q ≥ 3`); at `p = 2` the pool is honestly EMPTY
  (`ChainMenuU.rootedPairs_two_empty` — the W1 honest-empty pattern, note Claim 4.3).

**W4c re-scope record (2026-07-22, blueprint `WILD_WAVE4` §W4c; third scope)**: hypothesis
`hT` re-scoped from `T ∈ WildMenuW3.omMenuW3 n K σ` to `T ∈ MultiSlopeMenu.omMenu4 n K σ`, and
hypothesis `hfib` from the bare `B.classify … = T` equation to the per-family dispatch
`fiberOf4 p n N hN T f hf hdeg` (see `fiberOf4`'s docstring for the vacuity trap the dispatch
avoids); everything else byte-identical. The W3 instance is EXACTLY the previously accepted
W3c form (derived below as `om_leaf_faithful_w3`, definitional on old shapes via
`fiberOf4_old`), and the `K = 1` Wave-2 form survives as `om_leaf_faithful_w1`.

**W5c re-scope record (2026-07-22, blueprint `WILD_WAVE56` §2-W5c; scope #4; declaration
gated on the (P4) pin, completed the same day)**: hypothesis `hT` re-scoped from
`(K : ℕ) … T ∈ MultiSlopeMenu.omMenu4 n K σ` to `(D K : ℕ) … T ∈ ChainMenu.omMenu5 n D K σ`,
and hypothesis `hfib` from `fiberOf4` to the three-family dispatch `fiberOf5`; everything else
byte-identical. The W4 instance is EXACTLY the previously accepted W4c form (derived below as
`om_leaf_faithful_w4` — menu leg `ChainMenu.omMenu5_zero` at `D = 0`, fiber leg definitional
via `fiberOf5_notChain` + `ChainMenu.headOrd_of_mem_omMenu4`).

**W6c re-scope record (2026-07-22, blueprint `WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §3;
scope #5)**: hypothesis `hT` re-scoped from `(D K : ℕ) … T ∈ ChainMenu.omMenu5 n D K σ` to
`(D K : ℕ) … T ∈ ChainMenu6.omMenu6 n D K σ` — a pure MENU widening: the new members are
exactly the depth-0 leaf literals `{chainLit [] leaf : leaf ∈ chainLeaves K σ}` (`n = 2`
only, σ-keyed, window `K`; `ChainMenu6.chainShapes0` = the `chainShapes` emission without
the `ms ≠ []` filter). Hypothesis `hfib` is BYTE-IDENTICAL (`fiberOf5` already dispatches
chain-headed literals, including the depth-0 ones, to `ChainMenu.ChainCell (decodeMs T)
(decodeLeaf T)`; at `ms = []` that is the `LeafPair leaf` digit fiber — the EXACT fiber the
W6 full model counts at depth 0), and the conclusion is byte-identical. The W5 instance is
EXACTLY the previously accepted W5c form (derived below as `om_leaf_faithful_w5` — menu leg
`ChainMenu6.omMenu5_subset_omMenu6`, fiber leg verbatim); the W4/W3/W2 chains keep deriving
as before. Anti-vacuity of the new legs: below the leaf threshold (`L₀ < leafNeed leaf`) the
depth-0 fiber is EMPTY (`ChainMenu.chainPair_empty` at `ms = []`, i.e. `leafPair_empty`);
nonemptiness witnesses + mutation probes at the new legs are task W6c-d.

**W6q re-scope record (2026-07-22, blueprint `WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §1.5/§3;
scope #6)**: hypothesis `hT` re-scoped from `(D K : ℕ) … T ∈ ChainMenu6.omMenu6 n D K σ` to
`(D K : ℕ) … T ∈ ChainMenu7.omMenu7 n D K σ` (the new members are exactly the splitU
literals `{splitULit ms m : ms ∈ msMenu D K, m ∈ Icc 1 K}` at `n = 2`, `σ = splitType2`),
and hypothesis `hfib` from `fiberOf5` to the four-family dispatch `fiberOf7` (splitU heads
`headOrd T = 3` → the PROVED counting fiber `ChainMenu7.ChainCellU` at the exact decode;
every other head → `fiberOf5`, byte-identical). Conclusion byte-identical. The W6c
instance is EXACTLY the previously accepted scope-#5 form (derived below as
`om_leaf_faithful_w6` — menu leg `ChainMenu7.omMenu6_subset_omMenu7`, fiber leg
`fiberOf7_not_splitU` at `ChainMenu7.headOrd_ne_three_of_mem_omMenu6`); the W5/W4/W3/W2
chains keep deriving as before (the W5 derivation now routes through `om_leaf_faithful_w6`,
statement unchanged). The splitU instances are guarded by the AXIOM-FREE
`OM/QpTypeSplitU.lean` masters and are redundant-in-consumers by REQUIREMENT (see the
NEW (W6q) bullet above). Guardian audit #7 owns this re-scope.

**NO uniformity / rationality / measure / density term appears in the statement** (existence
only; no uniqueness clause — consumers need none). Deliberate NON-imports (blueprint §2 W2b,
unchanged): drainage (false of the truncated classifier), residual equidistribution (not
GMN-stated), and any translation-form GMN statement (none exists — (P4d); that content is
PROVED).

Mutation probes: `gateFiber_nonempty` + the recorded MUTATED-axiom `False` derivation (comment
block below) + the positive check `gate_axiom_coherent`; re-run at the H = 3 window stratum
after the W3c re-scope (split-type AND fine-(e,f)-swap — `OM/QpTypeH3.lean` evidence blocks);
re-run at the NEW mixed-gate stratum (n = 5, σ = {(2,1),(3,1)}) after the W4c re-scope
(all-unramified `{(1,1)}⁵` AND wrong-e singleton `{(2,1)}` — both against the AXIOM-FREE
`OM/QpTypeMixed.lean` anchors; evidence blocks there); re-run at the NEW depth-1 chain-gate
stratum (n = 2, `ms = [1]`, `ram 1`, σ = {(2,1)}) after the W5c re-scope (split-type
`{(1,1),(1,1)}` AND fine-(e,f)-swap `{(1,2)}` — both against the AXIOM-FREE
`OM/QpTypeChain.lean` anchors; evidence block in Block 4b below) plus the positive check
`chainGate_axiom_coherent`; re-run at the NEW splitU stratum (p = 3, n = 2, `splitULit [] 1`,
σ = {(1,1),(1,1)}) after the W6q re-scope (wrong-keying `{(1,2)}` against the AXIOM-FREE
two-factor refuter `QpTypeSplitU.w6qSplitU_not_irreducible`; evidence block in Block 5c
below) plus the positive check `gate_w6q_splitU_coherent`. -/
axiom om_leaf_faithful (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu7.omMenu7 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : fiberOf7 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ

/-- **The Wave-6c form of the axiom, now a THEOREM** (W6q re-scope, 2026-07-22): the
previously accepted `om_leaf_faithful` statement over the depth-0-widened menu
`ChainMenu6.omMenu6 n D K σ` with the `fiberOf5` dispatch is an instance of the re-scoped
axiom — the menu leg by the recovery inclusion `ChainMenu7.omMenu6_subset_omMenu7` (the W6q
menu is the W6 menu ∪ the splitU literals), the fiber leg by `fiberOf7_not_splitU` (NO
scope-#5 menu shape carries the splitU head `3` —
`ChainMenu7.headOrd_ne_three_of_mem_omMenu6`). Every W6c consumer keeps compiling against
this form. -/
theorem om_leaf_faithful_w6 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu6.omMenu6 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful p n N hN σ T D K
    (ChainMenu7.omMenu6_subset_omMenu7 n D K σ hT) f hf hdeg
    ((fiberOf7_not_splitU p n N hN
      (ChainMenu7.headOrd_ne_three_of_mem_omMenu6 hT) f hf hdeg).mpr hfib)

/-- **The Wave-5c form of the axiom, now a THEOREM** (W6c re-scope, 2026-07-22; routed
through the derived W6 form `om_leaf_faithful_w6` since the W6q re-scope): the
previously accepted `om_leaf_faithful` statement over the depth-windowed chain menu
`ChainMenu.omMenu5 n D K σ` with the `fiberOf5` dispatch is an instance of the re-scoped
axiom — the menu leg by the recovery inclusion `ChainMenu6.omMenu5_subset_omMenu6` (the W6
menu is the W5 menu ∪ the depth-0 leaf literals), the fiber leg VERBATIM (`hfib` was not
re-scoped at W6c). Every W5c consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w5 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu.omMenu5 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : fiberOf5 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w6 p n N hN σ T D K
    (ChainMenu6.omMenu5_subset_omMenu6 n D K σ hT) f hf hdeg hfib

/-- **The Wave-4c form of the axiom, now a THEOREM** (W5c re-scope, 2026-07-22; routed
through the derived W5 form `om_leaf_faithful_w5` since the W6c re-scope): the
previously accepted `om_leaf_faithful` statement over the mixed-e menu
`MultiSlopeMenu.omMenu4 n K σ` with the `fiberOf4` dispatch is an instance of the re-scoped
axiom — the menu leg by the recovery gate `ChainMenu.omMenu5_zero` (`D = 0`: no chains), the
fiber leg definitionally (`fiberOf5_notChain`: no W4 menu shape has a chain head,
`ChainMenu.headOrd_of_mem_omMenu4`). Every W4c consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w4 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ)
    (hT : T ∈ MultiSlopeMenu.omMenu4 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : fiberOf4 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w5 p n N hN σ T 0 K
    (by rw [ChainMenu.omMenu5_zero]; exact hT) f hf hdeg
    ((fiberOf5_notChain p n N hN (ChainMenu.headOrd_of_mem_omMenu4 hT) f hf hdeg).mpr hfib)

/-- **The Wave-3c form of the axiom, now a THEOREM** (W4c re-scope, 2026-07-22; routed
through the derived W4 form `om_leaf_faithful_w4` since the W5c re-scope): the previously
accepted `om_leaf_faithful` statement over the K-windowed menu `WildMenuW3.omMenuW3 n K σ` with
the `B.classify` fiber equation is an instance of the re-scoped axiom — the menu leg by
`omMenu4 = omMenuW3 ∪ …` (left injection), the fiber leg definitionally (`fiberOf4_old`: every
W3 menu shape has an order-0 head, `MultiSlopeMenu.headOrd_of_mem_omMenuW3`). Every W3c
consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w3 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w4 p n N hN σ T K
    (by rw [MultiSlopeMenu.omMenu4]; exact Finset.mem_union_left _ hT) f hf hdeg
    ((fiberOf4_old p n N hN
      (by rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hT]; exact zero_ne_one)
      f hf hdeg).mpr hfib)

/-- **The Wave-2 (K = 1) form of the axiom, a THEOREM since the W3c re-scope** (routed through
`om_leaf_faithful_w3` since the W4c re-scope): the originally accepted `om_leaf_faithful`
statement over the Wave-1 menu `WildMenu.omMenuW n σ` is the `K = 1` instance, via the
compatibility gate `WildMenuW3.omMenuW3_one : omMenuW3 n 1 σ = WildMenu.omMenuW n σ`. Every
Wave-2 consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w1 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w3 p n N hN σ T 1 ((WildMenuW3.omMenuW3_one n σ).symm ▸ hT) f hf hdeg hfib

/-! ## Block 2 — the faithfulness theorem (the Wave-2 payoff) and the gate corollary -/

/-- **The Wave-2 semantic faithfulness theorem** (blueprint §2 W2c): a genuine monic
`f : ℤ_[p][X]` classified into the σ-keyed menu has a genuine ℚ_p-factorization of type σ —
its TRUE factorization type IS the type its menu shape is keyed by. Consumed footprint =
Lean core + `om_leaf_faithful` (see the census). Statement UNCHANGED by the W3c re-scope;
routed through the derived K = 1 form `om_leaf_faithful_w1`. -/
theorem menuFiber_hasType (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w1 p n N hN σ T hT f hf hdeg hfib

/-- The Wave-1 wild gate shape `Tselfloop 2 gateSide gateShape` is a member of the σ-keyed menu
at `σ = {(2,1)}` — via `WildMenu.omMenuW`'s ramified leg and `QpType.ramShape_gate` (itself
`WildMenu.ramShape_of_constERam` at the constant-e instance `e = 2, f = 1`). -/
theorem gate_mem_omMenuW :
    ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape
      ∈ WildMenu.omMenuW 2 (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) := by
  rw [WildMenu.omMenuW, QpType.ramShape_gate, Option.toFinset_some]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The σ-specialized faithfulness corollary at the Wave-1 wild gate**: every genuine monic
quadratic in the level-`N` classifier fiber of `Tselfloop 2 gateSide gateShape` has genuine
ℚ_p-factorization type `{(2,1)}` — one totally ramified quadratic factor. (Coheres with the
PROVED `QpType.wildGateFiber_eisenstein`: the same fiber is Eisenstein-irreducible.) -/
theorem gateFiber_hasType (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 0 < N)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify p 2 N (PadicLift.toBox p 2 N hN f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) :=
  menuFiber_hasType p 2 N hN _ _ gate_mem_omMenuW f hf hdeg hfib

/-! ## Block 3 — mutation probe leg 1: the gate fiber is INHABITED

Route (probe design note): `decide` on `B.classify` is structurally unavailable (`classifyAux`
is well-founded recursion — `WellFounded.fix` does not kernel-reduce — and `polyShape` carries
`Classical.decEq`), and extracting ℕ-positivity from the ℚ-valued `stratumCount_selfloop_R`
would still need a box→`ℤ_[p]` lift. Instead: the CONCRETE banked witness. `CellMenu.gate_S2C1`
(the W0 numeric gate, `p = 2, N = 3`) proves `InCell 2 gbox1 (mkCell 2 [(0,1),(2,0)] [[(1,1)]])`
for the box of `X² + 2X + 2`; `gatePoly` is its genuine `ℤ_[2]` lift (`toBox` sends one to the
other by direct coefficient computation), and `classify_eq_selfloop_iff` (mpr) converts `InCell`
into the classifier-fiber equation. -/

/-- The concrete gate-fiber witness: `X² + 2X + 2` over `ℤ_[2]` (Eisenstein at 2;
the `ℤ_[2]`-lift of the banked W0 gate box `CellMenu.gbox1`). -/
noncomputable def gatePoly : Polynomial ℤ_[2] := X ^ 2 + C 2 * X + C 2

theorem gatePoly_monic : gatePoly.Monic := by unfold gatePoly; monicity!

theorem gatePoly_natDegree : gatePoly.natDegree = 2 := by unfold gatePoly; compute_degree!

/-- `toBox` sends the genuine witness to the banked gate box: the level-3 reduction of
`X² + 2X + 2` is `gbox1`. -/
theorem toBox_gatePoly :
    PadicLift.toBox 2 2 3 (by norm_num) gatePoly gatePoly_monic gatePoly_natDegree
      = CellMenu.gbox1 := by
  apply Subtype.ext
  rw [PadicLift.toBox_val]
  show gatePoly.map (PadicInt.toZModPow 3) = (X ^ 2 + C 2 * X + C 2 : (ZMod (2 ^ 3))[X])
  unfold gatePoly
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat]

/-- **Mutation-probe leg 1 (fiber-nonemptiness).** The Wave-1 wild gate fiber is INHABITED by
the concrete `gatePoly = X² + 2X + 2` at `p = 2`, `N = 3`: the axiom's gate instance
quantifies over a genuinely nonempty fiber, so the mutation probe (comment block below) and the
coherence check `gate_axiom_coherent` have real force. Banked route: `CellMenu.gate_S2C1`
(`InCell`) + `ClassifierBridgeFiber2.classify_eq_selfloop_iff` (mpr). -/
theorem gateFiber_nonempty :
    ∃ (f0 : Polynomial ℤ_[2]) (hf : f0.Monic) (hdeg : f0.natDegree = 2),
      B.classify 2 2 3 (PadicLift.toBox 2 2 3 (by norm_num) f0 hf hdeg)
        = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape := by
  refine ⟨gatePoly, gatePoly_monic, gatePoly_natDegree, ?_⟩
  rw [toBox_gatePoly]
  exact (ClassifierBridgeFiber2.classify_eq_selfloop_iff 2 3 (by norm_num) (by norm_num)
    QpType.gatePath (QpType.menuPath_gate (by norm_num)) QpType.gateSide
    QpType.sidePairs_gatePath QpType.gateShape QpType.shapesFor_gate
    (by decide) (by decide) CellMenu.gbox1).mpr CellMenu.gate_S2C1.1

/-! ## Block 4 — mutation probe leg 2: the MUTATED axiom is refuted (evidence block)

**Mutation probe evidence (machine-checked 2026-07-21, scratch NOT committed; W2-era record —
the scratch below quotes the axiom's PRE-W3c hypotheses over `WildMenu.omMenuW`, which are now
exactly those of the derived theorem `om_leaf_faithful_w1`; the probes were RE-RUN against the
re-scoped W3 hypotheses at the H = 3 window stratum the same day, evidence blocks in
`OM/QpTypeH3.lean` — those W3-form hypotheses are, since the W4c re-scope of 2026-07-22,
exactly those of the derived theorem `om_leaf_faithful_w3`; the W4c probes at the NEW mixed
menu content live in `OM/QpTypeMixed.lean`).**
**W6c note (2026-07-22, scope #5): the menu widening `ChainMenu.omMenu5 → ChainMenu6.omMenu6` preserves this record verbatim — every hypothesis form quoted or referenced in this block is that of a DERIVED theorem (`om_leaf_faithful_w1`/`_w3`/`_w4`/`_w5`), unchanged by the re-scope; the probes re-fire at the NEW depth-0 legs in task W6c-d.**
**W6q note (2026-07-22, scope #6): same preservation again — the widening `ChainMenu6.omMenu6 → ChainMenu7.omMenu7` + the `fiberOf5 → fiberOf7` dispatch leaves every quoted hypothesis form that of a DERIVED theorem (now including `om_leaf_faithful_w6`, the exact former scope-#5 statement); the probe at the NEW splitU leg is recorded in Block 5d below.**
The following scratch module — the (W2) axiom's hypotheses verbatim,
conclusion mutated to the SPLIT type `{(1,1),(1,1)}` — was compiled against this module and
`lake env lean` accepted it with zero errors, i.e. `False` DERIVES from the mutated axiom +
`gateFiber_nonempty` + `QpType.wildGateFiber_eisenstein`. A wrong-(e,f) payload at the gate is
therefore machine-refutable, not silently absorbable: the axiom's conclusion is load-bearing at
its concrete instances.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful

namespace LeanUrat.OM.OmLeafFaithfulScratch

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of `om_leaf_faithful` verbatim, conclusion
replaced by the SPLIT type `{(1,1),(1,1)}`. -/
axiom om_leaf_faithful_MUTATED (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

/-- The mutated axiom is REFUTED: at the inhabited gate fiber (`OmLeafFaithful.gateFiber_nonempty`)
it forces a 2-factor ℚ_2-factorization of a polynomial that is PROVEN irreducible over ℚ_2
(`QpType.wildGateFiber_eisenstein`). -/
theorem mutation_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := OmLeafFaithful.gateFiber_nonempty
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED 2 2 3 (by norm_num)
    (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) _ OmLeafFaithful.gate_mem_omMenuW
    f0 hf hdeg hfib
  have hirr : Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) :=
    QpType.wildGateFiber_eisenstein 2 (by norm_num) (by norm_num) hf hdeg hfib
  -- the mutated conclusion forces EXACTLY TWO factors
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, g₂, hfac⟩ := List.length_eq_two.mp hlen
  -- both factors are ℚ_2-irreducible, hence NON-UNITS after mapping
  have h1 : ¬ IsUnit (g₁.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₁ (by rw [hfac]; exact List.mem_cons_self ..)).not_isUnit
  have h2 : ¬ IsUnit (g₂.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₂ (by rw [hfac]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).not_isUnit
  -- but their product is the irreducible f0.map — contradiction
  have hmap : f0.map (algebraMap ℤ_[2] ℚ_[2])
      = g₁.map (algebraMap ℤ_[2] ℚ_[2]) * g₂.map (algebraMap ℤ_[2] ℚ_[2]) := by
    rw [← F.prod_eq, hfac]
    simp [Polynomial.map_mul]
  rcases hirr.isUnit_or_isUnit hmap with h | h
  · exact h1 h
  · exact h2 h

end LeanUrat.OM.OmLeafFaithfulScratch

#print axioms LeanUrat.OM.OmLeafFaithfulScratch.mutation_refuted
```

`lake env lean` output on the scratch (2026-07-21): NO errors; the single info line

```
'LeanUrat.OM.OmLeafFaithfulScratch.mutation_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.OmLeafFaithfulScratch.om_leaf_faithful_MUTATED]
```

i.e. `False` follows from the MUTATED axiom + Lean core + this module's PROVED theorems alone
(the real `om_leaf_faithful` does NOT appear in the refutation's cone). -/

/-! ## Block 5 — mutation probe leg 3: the POSITIVE coherence check -/

/-- **Mutation-probe leg 3 (positive coherence).** The REAL axiom's concrete gate instance
COEXISTS with the proved Eisenstein irreducibility: the inhabited gate fiber carries a
factorization of type `{(2,1)}` — a SINGLETON factorization — alongside
`Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2]))`. (Where the mutated split-type conclusion
yields `False`, the real conclusion is consistent — the two probe legs together pin the
axiom's (e,f) payload at the gate.) -/
theorem gate_axiom_coherent :
    ∃ (f0 : Polynomial ℤ_[2]) (F : QpType.QpFactorization 2 f0),
      QpType.qpType 2 F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) ∧
      Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := gateFiber_nonempty
  obtain ⟨F, hF⟩ := gateFiber_hasType 2 (by norm_num) f0 hf hdeg hfib
  exact ⟨f0, F, hF, QpType.wildGateFiber_eisenstein 2 (by norm_num) (by norm_num) hf hdeg hfib⟩

/-! ## Block 5b — W5c positive coherence at the depth-1 chain gate -/

/-- The chain-gate witness `QpTypeChain.chainGatePoly = X² + 4` (`p = 2`, `N = 4`) lies in the
`fiberOf5`-fiber of the chain-gate shape `chainLit [1] (ram 1)` — the scope-#4 chain instance
of the axiom is NOT vacuous. -/
theorem chainGateFiber5_nonempty :
    fiberOf5 2 2 4 (by norm_num) (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.ram 1))
      QpTypeChain.chainGatePoly QpTypeChain.chainGatePoly_monic
      QpTypeChain.chainGatePoly_natDegree := by
  rw [fiberOf5_chain 2 2 4 (by norm_num) (ChainMenu.headOrd_chainLit _ _) _ _ _,
    ChainMenu.decodeMs_chainLit, ChainMenu.decodeLeaf_chainLit]
  exact QpTypeChain.chainGateFiber_nonempty

/-- **W5c positive coherence at the chain gate.** The re-scoped axiom's concrete depth-1
chain-gate instance (`p = 2`, `N = 4`, `chainGatePoly = X² + 4`, type `{(2,1)}` = `ramType2`)
COEXISTS with the PROVED axiom-free anchor: the same fiber carries a factorization of type
`{(2,1)}` (the axiom, via the inhabited fiber) alongside machine-checked ℚ_2-irreducibility
(`QpTypeChain.chainGate_irreducible`). Together with the recorded W5c mutation probes
(split-type AND fine-(e,f)-swap both derive `False` — evidence block below), the chain
branch's `(e,f)` payload is pinned in both coordinates. -/
theorem chainGate_axiom_coherent :
    ∃ (f0 : Polynomial ℤ_[2]) (F : QpType.QpFactorization 2 f0),
      QpType.qpType 2 F = ChainMenu.ramType2 ∧
      Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_w5 2 2 4 (by norm_num) ChainMenu.ramType2
    (ChainMenu.chainLit [1] (ChainMenu.ChainLeaf.ram 1)) 1 1
    QpTypeChain.chainGate_mem_omMenu5 QpTypeChain.chainGatePoly
    QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
    chainGateFiber5_nonempty
  exact ⟨QpTypeChain.chainGatePoly, F, hF,
    QpTypeChain.chainGate_irreducible 2 (by norm_num) (by norm_num)
      QpTypeChain.chainGatePoly_monic QpTypeChain.chainGatePoly_natDegree
      QpTypeChain.chainGateFiber_nonempty⟩

/-! ## Block 5c — W6q gates at the splitU witness (scope-#6 non-vacuity + positive coherence)

The witness OBJECTS live with the axiom-free masters (`OM/QpTypeSplitU.lean` Block 7):
`w6qSplitUPoly = y² + 9y + 18 = (y + 3)(y + 6)` over `ℤ_[3]` (residual pair `(2, 0)` — the
`rootedPairs 3` singleton), its `LeafPairU` membership `w6qSplitUPair_mem` at the minimal
frame `N = leafNeedU 1 = 3` (digit checks by `decide`), the DIRECT two-factor
irreducibility refuter `w6qSplitU_not_irreducible`, and the CORE-ONLY master gate
`gate_w6q_splitU_hasType_axfree`. HERE: the omMenu7 membership, the `fiberOf7` fiber
membership, and the axiom-consuming positive coherence gate (the probe pattern of Blocks
3–5b, re-run at the scope-#6 emission). -/

/-- The splitU literal `splitULit [] 1` is on the scope-#6 menu at `σ = splitType2`, window
`D = 0`, `K = 1` — via the NEW `splitUShapes` leg (it is on NO earlier menu: the head
order-slot `3` is fresh, `ChainMenu7.headOrd_ne_three_of_mem_omMenu6`). -/
theorem w6qSplitU_mem_omMenu7 :
    ChainMenu7.splitULit [] 1 ∈ ChainMenu7.omMenu7 2 0 1 ChainMenu.splitType2 := by
  refine ChainMenu7.mem_omMenu7_cases.mpr (Or.inr ⟨rfl, rfl, [], 1, ?_, ?_, rfl⟩)
  · rw [ChainMenu.mem_msMenu]
    exact ⟨Nat.le_refl 0, fun m hm => absurd hm (List.not_mem_nil)⟩
  · rw [Finset.mem_Icc]
    omega

/-- The splitU witness inhabits the `fiberOf7` fiber of the NEW splitU literal — the
scope-#6 instance of the axiom is NOT vacuous (the anti-vacuity leg of blueprint §3 at the
new emission; the pool itself is nonempty exactly for `q ≥ 3`). -/
theorem w6qSplitUFiber7_nonempty :
    fiberOf7 3 2 3 (by norm_num) (ChainMenu7.splitULit [] 1)
      QpTypeSplitU.w6qSplitUPoly QpTypeSplitU.w6qSplitUPoly_monic
      QpTypeSplitU.w6qSplitUPoly_natDegree := by
  rw [fiberOf7_splitU 3 2 3 (by norm_num) (ChainMenu7.headOrd_splitULit _ _) _ _ _,
    ChainMenu7.decodeMsU_splitULit, ChainMenu7.decodeMU_splitULit]
  unfold ChainMenu7.ChainCellU
  have hcoeff : ∀ i, ((PadicLift.toBox 3 2 3 (by norm_num) QpTypeSplitU.w6qSplitUPoly
      QpTypeSplitU.w6qSplitUPoly_monic QpTypeSplitU.w6qSplitUPoly_natDegree).1).coeff i
      = PadicInt.toZModPow 3 (QpTypeSplitU.w6qSplitUPoly.coeff i) := by
    intro i
    rw [PadicLift.toBox_val, Polynomial.coeff_map]
  rw [hcoeff 0, hcoeff 1]
  exact QpTypeSplitU.w6qSplitUPair_mem

/-- **W6q positive coherence at the splitU witness.** The re-scoped axiom's concrete splitU
instance (`p = 3`, `N = 3`, `w6qSplitUPoly = y² + 9y + 18`, type `{(1,1),(1,1)}` =
`splitType2`) COEXISTS with the PROVED two-factor reducibility
(`QpTypeSplitU.w6qSplitU_not_irreducible`, from the literal factorization `(y+3)(y+6)`).
Together with the recorded W6q wrong-keying mutation probe (evidence block below, Block 5d),
the axiom's keying at the new splitU leg is pinned. Footprint: core + `om_leaf_faithful`
EXACTLY. **NOTE (the blueprint §3 REQUIREMENT)**: this gate is a PROBE of the axiom's
keying, NOT a consumer route — the production split-keyed payload at this fiber is the
CORE-ONLY `QpTypeSplitU.gate_w6q_splitU_hasType_axfree` (same witness, same type, no
axiom). -/
theorem gate_w6q_splitU_coherent :
    ∃ (f0 : Polynomial ℤ_[3]) (F : QpType.QpFactorization 3 f0),
      QpType.qpType 3 F = ChainMenu.splitType2 ∧
      ¬ Irreducible (f0.map (algebraMap ℤ_[3] ℚ_[3])) := by
  obtain ⟨F, hF⟩ := om_leaf_faithful 3 2 3 (by norm_num) ChainMenu.splitType2
    (ChainMenu7.splitULit [] 1) 0 1 w6qSplitU_mem_omMenu7 QpTypeSplitU.w6qSplitUPoly
    QpTypeSplitU.w6qSplitUPoly_monic QpTypeSplitU.w6qSplitUPoly_natDegree
    w6qSplitUFiber7_nonempty
  exact ⟨QpTypeSplitU.w6qSplitUPoly, F, hF, QpTypeSplitU.w6qSplitU_not_irreducible⟩

/-! ## Block 5d — W6q mutation probe evidence (machine-checked 2026-07-22, scratch NOT
committed)

**The wrong-keying mutation at the NEW scope-#6 splitU leg** — the re-scoped axiom's
hypotheses VERBATIM (over `ChainMenu7.omMenu7` with `fiberOf7`), conclusion replaced by the
INERT type `{(1,2)}`, fired at the `p = 3` splitU witness — was compiled against this module
and `OM/QpTypeSplitU.lean`, and `lake env lean` accepted the following scratch with zero
errors: `False` DERIVES from the mutated axiom + the inhabited fiber
(`w6qSplitUFiber7_nonempty`) + the AXIOM-FREE two-factor refuter
(`QpTypeSplitU.w6qSplitU_not_irreducible`, from the literal factorization
`y² + 9y + 18 = (y + 3)(y + 6)`). The real `om_leaf_faithful` appears NOWHERE in the
refutation cone (footprint below: core + the mutated axiom ONLY); the positive check
`gate_w6q_splitU_coherent` (Block 5c) consumes exactly core + the real axiom. A singleton
keying at the splitU family is therefore machine-refutable, and — by the §3 REQUIREMENT —
the split keying itself never needs the axiom (`gate_w6q_splitU_hasType_axfree`, core-only).

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful

namespace LeanUrat.OM.OmLeafFaithfulScratchW6q

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of the W6q-re-scoped `om_leaf_faithful`
verbatim (menu `ChainMenu7.omMenu7`, fiber `fiberOf7`), conclusion replaced by the
wrong-keying INERT type `{(1,2)}`. -/
axiom om_leaf_faithful_MUTATED_splitUinert (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (D K : ℕ)
    (hT : T ∈ ChainMenu7.omMenu7 n D K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : OmLeafFaithful.fiberOf7 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

/-- The mutated axiom is REFUTED at the inhabited splitU witness fiber: a `{(1,2)}`
conclusion forces a SINGLETON certificate, whose one factor is ℚ₃-irreducible and equals
the witness — but the witness factors LITERALLY as `(y+3)(y+6)`
(`QpTypeSplitU.w6qSplitU_not_irreducible`). -/
theorem mutation_w6q_splitUwrongkey_refuted : False := by
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_splitUinert 3 2 3 (by norm_num)
    ChainMenu.splitType2 (ChainMenu7.splitULit [] 1) 0 1
    OmLeafFaithful.w6qSplitU_mem_omMenu7 QpTypeSplitU.w6qSplitUPoly
    QpTypeSplitU.w6qSplitUPoly_monic QpTypeSplitU.w6qSplitUPoly_natDegree
    OmLeafFaithful.w6qSplitUFiber7_nonempty
  -- the mutated conclusion forces EXACTLY ONE factor
  have hlen : F.factors.length = 1 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, hfac⟩ := List.length_eq_one_iff.mp hlen
  have hg₁ : g₁ = QpTypeSplitU.w6qSplitUPoly := by
    have hprod := F.prod_eq
    rw [hfac, List.prod_singleton] at hprod
    exact hprod
  -- the one factor is ℚ₃-irreducible and IS the witness — against the two-factor refuter
  have hirr : Irreducible (QpTypeSplitU.w6qSplitUPoly.map (algebraMap ℤ_[3] ℚ_[3])) := by
    rw [← hg₁]
    exact F.irred g₁ (by rw [hfac]; exact List.mem_singleton_self _)
  exact QpTypeSplitU.w6qSplitU_not_irreducible hirr

end LeanUrat.OM.OmLeafFaithfulScratchW6q

#print axioms LeanUrat.OM.OmLeafFaithfulScratchW6q.mutation_w6q_splitUwrongkey_refuted
```

`lake env lean` output on the scratch (2026-07-22): NO errors; the single info line

```
'LeanUrat.OM.OmLeafFaithfulScratchW6q.mutation_w6q_splitUwrongkey_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.OmLeafFaithfulScratchW6q.om_leaf_faithful_MUTATED_splitUinert]
```

i.e. `False` follows from the MUTATED axiom + Lean core + PROVED theorems alone — the real
`om_leaf_faithful` appears in neither the refutation cone nor the refuter. -/

/-! ## Block 6 — axiom census (this module declares EXACTLY ONE axiom, the W6q-re-scoped one)

Expected footprints: `om_leaf_faithful` = itself; `om_leaf_faithful_w6` /
`om_leaf_faithful_w5` / `om_leaf_faithful_w4` /
`om_leaf_faithful_w3` / `om_leaf_faithful_w1` / `menuFiber_hasType` / `gateFiber_hasType` /
`gate_axiom_coherent` / `chainGate_axiom_coherent` / `gate_w6q_splitU_coherent` = Lean core
+ `om_leaf_faithful`;
`fiberOf4` / `fiberOf4_mixed` / `fiberOf4_old` / `fiberOf5` / `fiberOf5_chain` /
`fiberOf5_notChain` / `fiberOf7` / `fiberOf7_splitU` / `fiberOf7_not_splitU` /
`gate_mem_omMenuW` / `gatePoly*` / `toBox_gatePoly` /
`gateFiber_nonempty` / `chainGateFiber5_nonempty` / `w6qSplitU_mem_omMenu7` /
`w6qSplitUFiber7_nonempty` = Lean core ONLY (the split-keyed PAYLOAD gate
`QpTypeSplitU.gate_w6q_splitU_hasType_axfree` is core-only in ITS module — the §3
requirement).
The density capstones (`RealInstanceW.montes_unconditional_w`,
`RealInstanceV2.montes_unconditional`, `RealInstanceW3.montes_unconditional_w3`,
`RealInstanceW4.montes_unconditional_w4`, `RealInstanceW5.montes_unconditional_w5`) do NOT
consume this module — their core-only footprints are re-printed in `AxChk_baseline.lean`. -/

section AxCheck

#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_mixed
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_old
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf5
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf5_chain
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf5_notChain
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf7
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf7_splitU
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf7_not_splitU
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w6
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w5
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w4
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w3
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w1
#print axioms LeanUrat.OM.OmLeafFaithful.menuFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gate_mem_omMenuW
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly_monic
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly_natDegree
#print axioms LeanUrat.OM.OmLeafFaithful.toBox_gatePoly
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_nonempty
#print axioms LeanUrat.OM.OmLeafFaithful.gate_axiom_coherent
#print axioms LeanUrat.OM.OmLeafFaithful.chainGateFiber5_nonempty
#print axioms LeanUrat.OM.OmLeafFaithful.chainGate_axiom_coherent
#print axioms LeanUrat.OM.OmLeafFaithful.w6qSplitU_mem_omMenu7
#print axioms LeanUrat.OM.OmLeafFaithful.w6qSplitUFiber7_nonempty
#print axioms LeanUrat.OM.OmLeafFaithful.gate_w6q_splitU_coherent

end AxCheck

end LeanUrat.OM.OmLeafFaithful
