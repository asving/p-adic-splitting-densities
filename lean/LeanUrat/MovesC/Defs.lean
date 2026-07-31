/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL

/-!
# MovesC/Defs — shared vocabulary for §C, the composition theorem  [ROUND 6]

**ROUND 6 (2026-07-27).** ONE targeted change, closing the single defect of the round-5 audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R5_2026-07-27.md` (REJECT — finding 7 / blocking list
1–3: `inFreshBand` bounded the fresh band by the COARSE post-landing `childWidth` staircase
`Node.lineStep`, while rev 14 C.1(ii)'s species inventory runs per FINE slot — frame-`i`
blocks of width `Dwidth`, C.1.0(a). Since `childWidth = e·g·Dwidth` and the line descends, at
`e·g > 1` the coarse left-edge value exceeds the later fine slots' true valuations: coordinates
with heights in `(slotVal(fineSlot b), lineStep b]` — which rev 14 leaves UNCONSTRAINED — were
admitted into the band, tagged non-value, and forced into spurious zero strips by
`fresh_cover` + `fresh_assembled`: a locus shrink and an `mstar` inflation). The change:
* **the fine-slot band boundary** — `inFreshBand`'s upper edge is retyped to
  `H.htH i c ≤ ν.slotVal (ν.fineSlot idx)`: each coordinate is bounded by ITS OWN fine slot's
  exact valuation `new(j) = line.at(j·Dwidth)` — the recorded fine-slot valuation law, the SAME
  granularity at which round 5's `IsValueCoord`/`IsValueSupport` already read the geometry. The
  band at fine slot `j` is now exactly `(floor, new(j)]`: the strip zeros strictly between floor
  and `new(j)`, plus — at span slots — the on-lattice level set AT `new(j)` (the value
  positions, the band's upper edge): rev 14 C.1(ii)'s actual per-slot inventory, nothing above
  it. Past the (γ) crossing `new(j) ≤ floor` empties the slot's band — the self-truncation now
  cuts per FINE slot (no coarse overhang). `Node.lineStep` is retained as the post-landing
  (ZC-a) staircase convention ONLY (its docstring retagged); at recenterings
  (`childWidth = Dwidth`) the two boundaries coincide, so all round-5 semantics there are
  unchanged. `fresh_band`/`fresh_cover`/`mstar_eq` consume the band BY NAME — byte-stable; the
  23 frozen units are BYTE-STABLE.

[ROUND 5 header, kept for the audit trail:]

**ROUND 5 (2026-07-27).** ONE targeted change, closing the single blocking structure of the
round-4 audit `lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R4_2026-07-27.md` (REJECT — finding 10 /
blocking list 1–4: the fresh laws determined only a partition of the band and its total
cardinality, not the geometric clause SPECIES; an all-singleton-zero construction impersonated
the value clauses, changing Theorem C(a)'s locus). The 23 frozen units are BYTE-STABLE; every
other round-4 field is unchanged. The change:
* **exact geometric fresh-clause identification** — `Node.fineSlot`/`Node.spanSlot`/
  `Node.slotVal` name the read's OWN development geometry (C.1.0(a): frame-`i` blocks of width
  `Dwidth = deg Φ_i`; the side span `[s₀, s₀+wSide]`; the exact valuation
  `new(j) = line.at(j·Dwidth)`). `IsValueCoord` (the VALUE positions: span slot ∧ height = that
  slot's exact valuation — rev 14 C.1(ii)'s on-lattice value-digit locus: (α) digits + the
  non-adjacent endpoint; β/γ slots carry STRICT bounds, never a value) and `IsValueSupport`
  (support = the COMPLETE level set of ONE recorded span slot at its recorded exact valuation,
  membership as an IFF over the whole box — never `⊆`) retype `fresh_assembled`: the STRIP
  branch (singleton zero, codim 1) now additionally requires its coordinate NOT a value
  position; the VALUE branch requires `IsValueSupport` (subsuming round 4's bare
  constant-height law); the per-type codim laws are unchanged (strip: `codim = 1`; value:
  `codim = support.card`). The audit's all-singleton-zero construction is UNBUILDABLE — walk in
  `fresh_assembled`'s docstring and blueprint § ROUND 5. The only remaining freedom in a value
  clause is the emitted value `v` inside its alphabet — the declared graded-provenance boundary
  (blueprint R4.B.2), not geometry.

[ROUND 4 header, kept for the audit trail:]

**ROUND 4 (2026-07-27).** Retype of the global layer against §C REV 14 EXACTLY, after the
round-3 audit `lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R3_2026-07-27.md` (REJECT — the rev-14
delta). The 23 frozen units are BYTE-STABLE. Changes, keyed to the audit's final-disposition
list (its finding 20):
* **(SAE) + the full realizability class (findings 8/9)** — `TransitionAdmissible νp ν` is the
  NAMED per-step predicate: (NA)+(HV)+(SAE) at the appended read. (SAE) is rev 12's two-line
  display: `new(j) > old(j)` STRICT at every span slot `j ∈ [s₀', j*]` with `j < μ`, and
  `new(μ) = old(μ)` at the adjacent tie. `Realizable H` := every appended read is
  transition-admissible — the THREE-condition class (the round-3 two-condition docstring and
  definition are gone; the certified F-EMPTY configuration now violates `Realizable`).
* **TRANSITION-ADMISSIBLE per-step interface (findings 10/16)** — per-step consumers take it
  through `JetSetup.realizable` (definitionally the ∀-step form of `TransitionAdmissible`);
  `C3.lineDom` now HYPOTHESIZES `Realizable` (rev 14's DOM: "for every realizable prefix").
  The round-3 weak vertex-entry ties (`old ≤ new` at `j*`, hinge equality) are DELETED from
  `HistoryCoherent`: the span-entry inequality is (SAE)'s, sourced from REALIZABILITY, never
  from coherence (finding 16's "wrong semantic hypothesis boundary" repaired).
* **u*, the side height (finding 11)** — `Node.ustar` (absolute v_p-scale) with `hLineU`: the
  read line passes through `(j*, u*)` — slope from coherence's slope law, intercept pinned by
  `u*`. `Node.gam : ℤ` records the augmented-scale TOTAL SIDE WEIGHT `γ = e·(STR·u*) + j*·h`
  (rev 14 C.0, the argument of D.3(c)'s stride positions); the tie lives in `HistoryCoherent`
  (where `STR` exists) and its ℤ-typing IS the on-lattice condition. Adjacent vertex
  anchoring (`u* =` the standing window-vertex height) = (SAE)'s equality line + `hLineU`.
* **canonical Bézout pair (finding 12)** — `hbezCanon : 0 ≤ t < e` selects THE canonical pair:
  unique in the window, hence a FUNCTION of `(e, h)` only (rev 14's `(sᴮ, tᴮ)`). It extends
  the accepted `Stage.he1t` (P2) pinning to every `e`: at `e = 1` the window FORCES
  `t = 0, s = 1`, so `m̂ = 0` at recenterings BY the convention — rev 14's exact sentence;
  the round-3 field `hspecRecBez` is deleted as now derivable.
* **ψ irreducible (finding 13)** — `hψirr : Irreducible ψ` (rev 14: "monic irreducible over
  F_i"; recenterings are consistent — degree-1 polynomials over a field are irreducible).
* **anchored-residual provenance (finding 14)** — `hAnchor : e·a = s₀ − t·γ` pins the anchor
  to D.3(c/d): `a = p_{s₀}(γ) = (s₀ − t·γ)/e` is the z-order of the side residual (its lead
  digit is nonzero, `hpat0`), so with `hRanch`'s consecutive powers `Ranch` IS rev 14's
  `R_anch = Σ_j d_j·z^{p_j(γ)−a}`; `a` can no longer move freely under (HV).
* **fresh-species coverage (finding 17)** — `inFreshBand` names the D.11 band as a coordinate
  predicate; `fresh_band` (every clause support ⊆ the band — replaces
  `fresh_above`/`fresh_interior`, adding the upper edge), `fresh_cover` (every band coordinate
  lies in SOME clause's support — EXACTLY one, by `FreshData.disj`), and `fresh_assembled`'s
  value branch adds the per-clause `codim = support.card` (TYP(b)'s |alphabet| = |piece|,
  now placed PER CLAUSE). The permutation loophole is dead: the total codimension decomposes
  coordinate-by-coordinate over the band; nothing can move to unrelated above-floor supports.
* **cutoff (finding 18)** — `hN : 1 ≤ N` (Theorem C's quantifier is `N ≥ N(H,Z)` with
  `N(H,Z) ≥ 1`; the `≥ N(H,Z)` half is automatic inside the box — `coordOf_lt` bounds every
  equation level below `N` — and otherwise existence-side). `N = 0` presentations are gone.
* **root-side height (finding 19)** — `root_height`: the root line dominates the cluster
  floor (`1 ≤ line₀.at b` on the root factor interior — DOM's rev-11 base display), so
  `mstar_eq` at `i = 0` counts the cluster zeros; the root intercept is no longer free.

[ROUND 3 header, kept for the audit trail:]

**ROUND 3 (2026-07-26).** Rebuild of the GLOBAL layer after the round-2 audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_R2_2026-07-26.md` (REJECT: blockers 55-60 — the local
layer certified sound, the global layer admitted trivial presentations). The local layer
(C0/C1/C2 clause vocabulary, `LevelClause`/`FreshData`/`TypObject`/`DomData`/`ZCData`, lines,
species) is BYTE-STABLE. Changes, keyed to blockers:
* **B55 (no provenance ties)** — `JetSetup` gains the presentation spine `pres`
  (`pres_zero` = the concrete frame-0 p-adic digit chart `baseDigit`; `pres_theta` = each
  `Theta i` translates frame-(i+1) presentations of `f` to frame-i presentations of the SAME
  `f`; `pres_block` = frame-(i+1) presentations are block-local over the recorded landing key's
  development — C.1.0(a)); the recorded landing keys `keys` with `keys_mid`+`landing`
  (`LandingKey`, D.5/D.10 at the node's data); `Sigma`'s `recursion` now runs through the
  STRATUM (`stratum` + `inh_implied` — C.1(i) as a sentence); `fresh` is pinned by
  `fresh_assembled` (strip / TypObject-value shapes on ht-level sets) and `mstar_eq`.
* **B56 (final landing)** — `landing` holds at EVERY `i < len` including the last: the final
  read's landing key obeys the same recorded-data lift law (`LandingKey`).
* **B57 (mstar RHS)** — `mstar_eq`: `(fresh i).mstar` EQUALS the D.11 species-inventory count,
  the fresh-band cardinality `#{c : idx < prevRim, floor_i < htH_i(c) ≤ lineStep_i(c)}`
  computed from node data (the band self-truncates at the (γ) crossing slot).
* **B58 (thmC_a)** — `S(H,Z)` is INDEPENDENTLY defined (`JetSetup.SHZ`, the transported system
  `T(H,Z)` as an ∃-chain over the recorded moves); `thmC_a` states the classifier-locus =
  transported-image EQUALITY plus the mass carriage.
* **B59 (ht + line ties)** — the bare `ht` field is DELETED: heights are the DEFINED K1-chain
  formula `History.htH` (LST(i)'s sentence now exists; the graded-bridge FLAG moves to its
  docstring). The read-line intercept is tied by the new `HistoryCoherent` vertex-entry clauses
  (endpoint comparison at `j*`, hinge EQUALITY at adjacent reads).
* **B60 (degenerate fresh)** — `fresh_assembled` + `mstar_eq` exclude empty/afresh-free
  presentations wherever the recorded geometry has a nonempty fresh band.
* **F10 (the m̂ index)** — CONFIRMED A REAL BUG and fixed: D.3's header fixes "(a stage with)
  READ INDEX (e,h) and Bézout (s,t)" — the D.5 lift positions and D.8 normalization
  `m̂ = −t·h·g` use the READ's own pair, while `Stage.(e,h,s,t)` records the frame-CREATING
  read's. `Node` now records its read-side Bézout pair `(s,t)` (`hbez`, recentering pinning
  `hspecRecBez`), `Node.mhat := −t·h·g` uses it, `IsNodeLift` replaces the mis-indexed
  `IsStandardLift σ` call in `HistoryCoherent`, and the child-frame ties `σ'.s = ν.s`,
  `σ'.t = ν.t` pin the recorded pair to the tower.

[ROUND 2 header, still accurate for the local layer:]

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §C REV 2 (ACCEPTED 2026-07-26, passes 12+13
CLEAN), derivations `C10B_DERIVATION_2026-07-26.md` / `C15_DERIVATION_2026-07-26.md` (Route B).
ROUND-2 rebuild after the round-1 STOP-THE-LINE audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_2026-07-26.md`. Point-by-point answers:
blueprint `MOVESC_LEAN_BLUEPRINT_2026-07-26.md` § ROUND 2. Definitions only — no theorems,
no `sorry`, no axioms.

## What round 2 changes (the audit's five principal failures)

1. **`Node`/`History` now ENFORCE the §C meanings as `Prop` fields**: `Ranch` is literally the
   anchored residual `Σ_k pat(k)·z^k` (stride positions collapse to consecutive powers since
   `e·s + h·t = 1`); `ψ` is monic of degree `g` with `ord_ψ(Ranch) = μ` exactly; species
   constraints (`increment → e·g > 1`, `recentering → e = g = 1`, `ψ = z − center`); the frame
   link `Dwidth = deg Φ`; the residue root `z̄` is a genuine root of `ψ`. `HistoryCoherent` keys
   the transition on the PARENT node's recorded data (`IsStandardLift` of the recorded `ψ, g` +
   `TransitionCoreL` at the recorded `e, h, z̄`; `IsRecenteringCore` at the RECORDED lift — no
   free existentials), adds window containment `s₀'+w' ≤ μ`, the (I-aug) slope chain, the width
   chain `D_{i+1} = e·g·D_i`, the absolute-scale slope law `slope·(e·STR·D) = h`, and the root
   frame `deg Φ₀ = 1`. Later `root` species are excluded by `History.root_iff`.
2. **`Realizable` is the genuine (NA)/(HV)**: (NA) compares the two lines at the BASE index
   `μ_i·D_{i+1}` (the audit's slot/base mismatch fixed); (HV) is the data IDENTITY
   `pattern lead of ν_{i+1} = vtx(ν_i)` with the FULL transported vertex value
   `vtx = z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F` — scalar factors included, valued through the
   ambient field (the round-1 `∃ lead, vtxPoly = lead` tautology is gone).
3. **The counting layer is ADDRESS-FREE (Route B / rev 9)**: `FreshData` no longer assigns
   coordinate values. A fresh clause is a `LevelClause` — a constraint carried by a SUPPORT
   (the weight-γ′ level set / strip region), a codimension, and an EXACT-FIBER-COUNT law
   (division-free: `#{supported y | sat y}·p^codim = p^{|support|}`) — exactly what TYP(b)'s
   kernel-coset argument supplies (`TypObject → LevelClause` is a manifest unit). The state is
   loci + masses + the (ZC) invariant; no pin address is data anywhere.
4. **`JetSetup` is re-indexed and LINKED**: `Sigma 0` is the FULL BOX `Σ_{−1}` (field `init`),
   `fresh i` is consumed once, between `Sigma i` and `Sigma (i+1)` (the audit's k = 0
   countermodel is unbuildable); all recursion/invariant fields are bounded by
   `H.nodes.length`; it carries `HistoryCoherent` + `Realizable` (so every consuming theorem
   consumes them), the ≺-SORTED coordinate chart `coordOf` (`Fin`-order ⟺ `CoordPrec`, range
   the `n×N` box — `m = n·N` enforced), the height map `ht`, and the NODE-TIED (ZC) data:
   per-prefix `ZCData` whose floor is the HISTORY's staircase max `floorH` and whose rim
   threshold is the recorded `μ_i·D_{i+1}`; fresh supports are pinned strictly above the floor
   and inside the previous read's factor interior. Freshness-on-`Σ` is now a THEOREM
   (`C2.freshFree`) consuming these links, not an assumed field.
5. **The final statements are Theorem C**: C(b) counts `S(H,Z)` — the `Ψ_H`-image of
   `Σ_k ∩ locus(Z)` under the RECORDED move composite `JetSetup.Psi` — against
   `p^{nN}·∏vol(E_fresh)·vol(Z)` in division-free pin arithmetic; C(a) is the bijective
   carriage with equal mass; `AdmissibleZ` is checked against the FINAL state `Sigma len`.

## The honest boundary (deferred, never approximated)

The EXISTENCE of a `JetSetup` for a real classifier history — the global jet-coordinate
presentation (Fact A down the tower, D.3(e)(ii)), the K1-height reading of `ht`, the graded
piece maps behind each fresh `LevelClause`, and (ZC) persistence — is the unbuilt graded ring
(§B2-DEF gap R4.5 items 1&3). It enters ONLY as the `JetSetup`/`TypObject` hypotheses, exactly
as `L6.measureExact` takes `codeN`/`ΘN`/`hcylN`. Everything in the manifest is provable from
the interface. Flagged for semantic-guardian review throughout.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

/-! ## C0. Base coordinates, the global order ≺, loci, unitriangular moves -/

/-- A **base coordinate** `c = (ℓ, i)`: `c.1 = ℓ` the p-adic level, `c.2 = i` the coefficient
(base) index (§C.0). -/
abbrev Coord : Type := ℕ × ℕ

/-- The **global order** `≺` (§C.0): `(ℓ,i) ≺ (ℓ',i')` iff `ℓ < ℓ'`, or `ℓ = ℓ'` and `i > i'`
(within a level, from the TOP coefficient down — Fact A's elimination order). -/
def CoordPrec (c c' : Coord) : Prop := c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c'.2 < c.2)

/-- A **§C locus**: a unitriangular digit system over `m = n·N` base digits in ≺-SORTED
coordinates (`Fin m`-order = `≺`, witnessed by `JetSetup.coordOf_sorted`), alphabet `ZMod p`
(the BLOCK CONVENTION: an `F`-digit of residue degree `d` is its `d` base equations, each a
factor `p⁻¹`). Reuses the accepted `DigitSystem` (DefsT); its solution set is the cylinder. -/
abbrev Locus (p m : ℕ) : Type := DigitSystem m (ZMod p)

/-- The **mass** of a locus: the number of its solutions among the `p^m` box points
(`= p^{m−numPinned}`, `C0.digitSystemMass`). -/
noncomputable def Locus.mass {p m : ℕ} (D : Locus p m) : ℕ :=
  Nat.card {x : Fin m → ZMod p // D.IsSolution x}

/-- The full box mass `p^{nN} = p^m`. -/
def boxMass (p m : ℕ) : ℕ := p ^ m

/-- **A move map is unitriangular for `≺`** (§C.0.5): `(Θx)_i = x_i + φ_i(x_j : j ≺ i)` — the
diagonal is the identity and the correction is an arbitrary function of ≺-earlier coordinates
(in ≺-sorted `Fin m` coordinates, `j < i`). This is the shape Fact A's division accounting
produces, in both directions. -/
def IsUnitriangular {m : ℕ} {R : Type*} [Add R] (Θ : (Fin m → R) → (Fin m → R)) : Prop :=
  ∀ i : Fin m, ∃ corr : ((j : Fin m) → j < i → R) → R,
    ∀ x, Θ x i = x i + corr (fun j _ => x j)

/-- The **pullback** of a locus `D` by a move `Θ` (`Θ*(E)` of the §C.0.5 pin-transport
corollary): the points whose `Θ`-image solves `D`. `C0.pinTransport` re-presents it as a
digit system with the SAME pinned coordinates (per-coordinate status, rev-9 PIN-WELLDEF). -/
def Locus.pullback {p m : ℕ} (D : Locus p m) (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) :
    Set (Fin m → ZMod p) := {x | D.IsSolution (Θ x)}

/-! ## C1. Lines, staircases, heights (absolute v_p-scale, §C.1.5 scale declaration) -/

/-- A **read-side line** as an AFFINE function of the base index, absolute v_p-scale (§C DOM):
`at b = intercept − slope·b` with `slope > 0` in genuine instances (lines DESCEND). -/
structure Line where
  intercept : ℚ
  slope : ℚ

/-- Evaluate a line at a base index. -/
def Line.at (L : Line) (b : ℕ) : ℚ := L.intercept - L.slope * (b : ℚ)

/-- The **absolute-height** map `ht(ℓ, i) = ℓ + off(i)` (§C.1.5 scale declaration): a base
coordinate's v_p-height in the current frame. DEFERRED CONTENT (flag): that a `JetSetup`'s `ht`
is the genuine K1-chain weight of the coordinate's basis monomial (`off(i) = Σ_r innerslot·κ_r`,
κ current — LST(i)) is the unbuilt jet-coordinate bridge. -/
abbrev HtMap : Type := Coord → ℚ

/-- The pointwise max of a family of lines over `[0, i]` (§C DOM's floor of RAW lines; the
step-function floor of a history is `History.floorH` below). -/
noncomputable def floorOf (lines : ℕ → Line) (i b : ℕ) : ℚ :=
  Finset.sup' (Finset.range (i + 1)) (by simp) (fun m => (lines m).at b)

/-- **DOM interface** (§C Lemma DOM): the two displayed inputs of the affine induction — the
(I-aug) strict-steepness chain and the vertex-entry endpoint inequality. `HistoryCoherent`
supplies `steeper` for the history's recorded lines (`C3.steeperChain`); `vertex_entry` is
D.8/D.4 geometry (per-instance input). `C2.DOM` derives interior domination; `C2.DOM_floorForm`
the floor form. -/
structure DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop where
  /-- (I-aug): the current line descends strictly faster than every earlier one. -/
  steeper : ∀ m, m < i → (lines m).slope < (lines i).slope
  /-- vertex-entry (§C DOM(2)): at the interior end the current line dominates every earlier
  one — the endpoint inequality that seeds the affine induction. -/
  vertex_entry : ∀ m, m ≤ i → (lines m).at interiorEnd ≤ (lines i).at interiorEnd

/-! ## C2. The address-free clause layer (Route B, §C.1.5′/rev 9)

A fresh clause never names a pin address. It is carried by a SUPPORT (the strip region or the
weight-γ′ level set), a CODIMENSION, and an exact-fiber-count law — the only three statistics
the counting consumes (C15 S4b). Strip zeros are the `codim = 1`, singleton-support case;
fresh VALUE clauses come from `TypObject` (the graded piece map) via `C1.TYP_toClause`. -/

/-- **A level-set clause** (§C.1.5′ fresh content, address-free): a constraint `sat` that
(i) depends only on the coordinates of its `support` (`dep`), and (ii) cuts EXACTLY
`p^{−codim}` among the support assignments (`count`, division-free on the supported
representatives). The `count` law is self-policing: it forces satisfiability and exactness, so
no vacuous clause instance exists. -/
structure LevelClause (p m : ℕ) where
  /-- the constrained coordinate set: a strip region or a weight-γ′ level set. -/
  support : Finset (Fin m)
  /-- the D.11-nominal codimension this clause cuts (`log_p` of the digit alphabet). -/
  codim : ℕ
  /-- the constraint itself (e.g. `R_δ'(level set) = v`); never a coordinate assignment. -/
  sat : (Fin m → ZMod p) → Prop
  /-- `sat` reads only the support coordinates. -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ support, x c = y c) → (sat x ↔ sat y)
  /-- EXACT CONDITIONAL VOLUME (TYP(b)'s kernel-coset count, division-free):
  `#{y supported in support | sat y} · p^codim = p^{|support|}`. -/
  count : Nat.card {y : Fin m → ZMod p // sat y ∧ ∀ c ∉ support, y c = 0} * p ^ codim
    = p ^ support.card

/-- **The fresh data of one read** (§C.1(ii)'s species inventory, address-free): the finite
clause list (α-strips/value digits, β-strips, γ-strips left of `j×`, the non-adjacent endpoint —
after BLOCK-CONVENTION expansion), with pairwise-DISJOINT supports (one clause per slot/level
region; §C.1.5′ "pairwise disjoint: the factors multiply"). Freeness on the state cylinder is
NOT a field: it is the theorem `C2.freshFree`, derived from the (ZC) floor exactness and the
above-floor/interior placement links of `JetSetup`. -/
structure FreshData (p m : ℕ) where
  clauses : List (LevelClause p m)
  disj : clauses.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support)

/-- The D.11-nominal fresh base-digit count `m*(ν) = Σ codim`; `vol_nom(E_fresh) = p^{−m*}`. -/
def FreshData.mstar {p m : ℕ} (fd : FreshData p m) : ℕ :=
  (fd.clauses.map LevelClause.codim).sum

/-- The joint membership predicate of the fresh clauses. -/
def FreshData.sat {p m : ℕ} (fd : FreshData p m) (x : Fin m → ZMod p) : Prop :=
  ∀ cl ∈ fd.clauses, cl.sat x

/-- **TYP object** (§C Lemma TYP, the typed degree-γ′ initial form) — BOUNDARY-DEFERRED (needs
the graded piece `gr^Ĉ_{δ'}` and its piece map `R_δ`, the unbuilt graded ring). The fresh value
digit of a slot coefficient is an ADDITIVE map of exactly the weight-γ′ level set `S`, SURJECTIVE
onto the digit alphabet (image = the additive span of the slot images, D.3(e)(i)). Its provable
consequences: equal kernel-coset fibers (`C1.TYP_fiberCount`), hence a `LevelClause` of the
alphabet's codimension (`C1.TYP_toClause`). -/
structure TypObject (p m : ℕ) (S : Finset (Fin m)) (α : Type*) [AddCommGroup α] where
  /-- the piece map `R_δ'` composed with the level-set assignment (graded content; DEFERRED). -/
  φ : (Fin m → ZMod p) →+ α
  /-- `φ` reads only the level-set coordinates `S` (LST/TYP support typing). -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → φ x = φ y
  /-- surjective onto the alphabet (D.3(e)(i): the emitted value lies in the image). -/
  surj : Function.Surjective φ

/-! ## C3. Read species and nodes (§C.0), with the §C meanings as Prop fields -/

/-- The **species of a read** (§C.0): the ROOT read `ν₀`, an INCREMENT (`e·g > 1`, genuine
stage growth), or a RECENTERING (`e_read = 1`, `g = 1`, degree unchanged, recorded lift). -/
inductive ReadSpecies where
  | root
  | increment
  | recentering
deriving DecidableEq

/-- **A node** `ν` — one read of the OM classifier (§C.0). Frame `σ : Stage p F` (the stage it
reads in), read side `(e, h)` on slots `[s0, s0+wSide]`, descend data `(ψ, g, μ)`, anchor `a`,
the fixed side-pattern digits `pat` (D.3(c): `pat k` at stride position `k` past the anchor —
consecutive `z`-powers, since consecutive lattice slots differ by `e·s + h·t = 1`), the anchored
residual `Ranch`, the read-side `line` (absolute v_p-scale), the residue root `zbar` selected by
the read (D.6/D.7 witness), the recentering `center`/`lift` (D.10), and the frame block width
`Dwidth = deg Φ`. The `Prop` fields make every recorded datum carry its §C meaning (round-1
audit: "many appropriately named fields … not enforced"). -/
structure Node (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  species : ReadSpecies
  σ : Stage p F
  e : ℕ
  h : ℕ
  /-- ROUND 3 (audit R2 F10): the READ side's own Bézout pair `e·s + h·t = 1` — D.3's header
  data "read index (e, h) and Bézout (s, t)". D.5's realizer positions and D.8's normalization
  `m̂ = −t·h·g` consume THIS `t` (the frame's `σ.t` is the frame-CREATING read's — wrong index).
  `HistoryCoherent` ties the child frame's recorded pair to it (`σ'.s = s`, `σ'.t = t`). -/
  s : ℤ
  t : ℤ
  g : ℕ
  μ : ℕ
  a : ℤ
  s0 : ℕ
  wSide : ℕ
  Dwidth : ℕ
  line : Line
  /-- ROUND 4 (audit R3 finding 11): the **SIDE HEIGHT** `u*` — the read side's right-endpoint
  height, ABSOLUTE v_p-scale (rev 14 C.0: "on-lattice; at an ADJACENT read, u* = the standing
  window-vertex height"). Its three rev-14 roles: (i) it pins the read line's INTERCEPT
  (`hLineU`: the line of slope `−h/e` per slot passes through `(j*, u*)`); (ii) it is
  on-lattice — the augmented-scale weight `γ = e·(STR·u*) + j*·h` is the INTEGER `gam`
  (`HistoryCoherent`'s γ-tie, where the stretch `STR` lives); (iii) at an adjacent read it is
  vertex-anchored ((SAE)'s equality line + `hLineU`). -/
  ustar : ℚ
  /-- ROUND 4 (findings 11/14): the read's **TOTAL SIDE WEIGHT** `γ := e·u* + j*·h` in the
  augmented (stage) scale — rev 14 C.0's `γ_i`, the argument of D.3(c)'s stride positions
  `p_j(γ) = (j − t·γ)/e`. Recorded as an INTEGER: its ℤ-typing is the on-lattice condition;
  `HistoryCoherent` ties it to `(ustar, e, h, s0, wSide)` at the history's stretch. -/
  gam : ℤ
  zbar : Fˣ
  center : ↥σ.K
  lift : Polynomial ℤ_[p]
  ψ : Polynomial ↥σ.K
  pat : ℕ → ↥σ.K
  Ranch : Polynomial ↥σ.K
  /-- the read side is a genuine polygon side: `e, h ≥ 1`, coprime (lowest terms). -/
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  /-- the recorded pair is a genuine Bézout pair for the read side (ROUND 3, F10). -/
  hbez : (e : ℤ) * s + (h : ℤ) * t = 1
  /-- ROUND 4 (audit R3 finding 12): the pair is CANONICAL — `t` in the window `[0, e)` is the
  UNIQUE Bézout coefficient there (any two solutions differ by `(h·k, −e·k)`), so `(s, t)` is
  rev 14's `(sᴮ, tᴮ)`: "a function of `(e, h)` only", not a recorded choice. Extends the
  accepted `Stage.he1t` (D.5 P2) pinning to every `e`: at `e = 1` the window forces `t = 0`,
  whence `s = 1` by `hbez` — so at a recentering `m̂ = −t·h·g = 0` BY the convention (rev 14:
  "NOT because the lift `t_i` is zero"); the round-3 `hspecRecBez` field is deleted as
  derivable. -/
  hbezCanon : 0 ≤ t ∧ t < (e : ℤ)
  /-- the descend data are genuine: `g ≥ 1`, `μ ≥ 1` (the read DESCENDS into `ψ`). -/
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  /-- the side width is a whole number of lattice cells: `e ∣ wSide` (`deg R_S = wSide/e`). -/
  hEdvd : e ∣ wSide
  /-- FRAME LINK: `Dwidth` IS the frame's block width `deg Φ` (C.1.0(a)). -/
  hDwidth : Dwidth = σ.Φ.natDegree
  /-- `ψ` is monic of degree `g` (D.3(c)). -/
  hψmonic : ψ.Monic
  hψdeg : ψ.natDegree = g
  /-- ROUND 4 (audit R3 finding 13): `ψ` is IRREDUCIBLE over the stage's residue field (rev 14
  C.0: "ψ_i: … monic irreducible over F_i"; D.3's header). Reducible residual factors are no
  longer legal nodes; `F_{i+1} = F_i[z]/(ψ_i)` is a field. (Recenterings are consistent:
  `ψ = z − c̃` has degree 1.) -/
  hψirr : Irreducible ψ
  /-- ANCHORED RESIDUAL (§C.0, rev 8): `Ranch = Σ_k pat(k)·z^k`, `k ≤ wSide/e` — the pattern
  DETERMINES `Ranch` (pattern-only data; the anchor `a` locates it: absolute position `a + k`). -/
  hRanch : Ranch = ∑ k ∈ Finset.range (wSide / e + 1), Polynomial.C (pat k) * Polynomial.X ^ k
  /-- polygon conventions: the endpoint digits are nonzero (anchor exact, side width exact). -/
  hpat0 : pat 0 ≠ 0
  hpatTop : pat (wSide / e) ≠ 0
  /-- ROUND 4 (audit R3 finding 14) — **ANCHORED-RESIDUAL PROVENANCE**: the anchor is D.3(c)'s
  stride position of the side's LEFT endpoint, `a = p_{s₀}(γ) = (s₀ − t·γ)/e` — displayed
  division-free. Why this is `ord_z R` (D.8's anchoring, as recorded stratum data): the side's
  minimizing slots are `s₀, s₀+e, …, s₀+wSide` at the constant total weight `γ`, their
  positions `p_j(γ)` increase by 1 per `e`-step (D.3(c)), and the lead digit is nonzero
  (`hpat0`) — so the smallest occupied position is `p_{s₀}(γ)`. With `hRanch`'s consecutive
  powers, `Ranch` is exactly rev 14's `R_anch = Σ_j d_j·z^{p_j(γ)−a}`; `a` can no longer be
  shifted independently of the side data (the (HV) exponent `z̄^{a−μm̂}` is now pinned). -/
  hAnchor : (e : ℤ) * a = (s0 : ℤ) - t * gam
  /-- ROUND 4 (finding 11, role (i)): the read line PASSES THROUGH `(j*, u*)` — evaluated at
  the right endpoint's base index `j*·Dwidth`. Slope is fixed by `HistoryCoherent`'s
  absolute-scale slope law, so `u*` pins the intercept: intercept translations (audit R2
  B59's residue) are dead. -/
  hLineU : line.at ((s0 + wSide) * Dwidth) = ustar
  /-- `ord_ψ(Ranch) = μ` EXACTLY (D.3(c): `ψ^μ ∥ Ranch`). -/
  hOrd : OrdPsiPoly ψ Ranch μ
  /-- `zbar` is a genuine root of `ψ` in the ambient field (D.6: `F' = K(z̄)`, `ψ(z̄) = 0`). -/
  hzbarRoot : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0
  /-- SPECIES (§C.0): an increment grows the stage, `e·g > 1`. -/
  hspecInc : species = ReadSpecies.increment → 1 < e * g
  /-- SPECIES (§C.0/D.10): a recentering has `e_read = 1` and degree unchanged (`g = 1`). -/
  hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
  /-- SPECIES (D.10): a recentering consumes the linear factor `ψ = z − c̃` at its recorded
  center, and its residue "root" is the center itself (no field growth). -/
  hspecRecCenter : species = ReadSpecies.recentering →
    ψ = Polynomial.X - Polynomial.C center ∧ ((zbar : Fˣ) : F) = ((center : ↥σ.K) : F)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The CHILD frame's block width `D_{i+1} = e·g·D_i` (C.1.0(a); recenterings: `e = g = 1`,
unchanged). `HistoryCoherent` pins the successor node's `Dwidth` to this. -/
def Node.childWidth (ν : Node p F) : ℕ := ν.e * ν.g * ν.Dwidth

/-- The D.8 normalization exponent `m̂ = −t·h·g` of the READ (the vertex unit `z̄^{−μm̂}` of
D.8's (VERTEX)). ROUND 3 (audit R2 F10 — a REAL index bug in round 2): `(t, h)` are the read
side's OWN slope numerator and recorded Bézout coefficient (D.3's header pair), NOT the
frame's `(σ.t, σ.h)` (which record the frame-CREATING read, one step earlier). ROUND 4: the
pair is CANONICAL (`hbezCanon`); at `e = 1` — every recentering — the window forces `t = 0`,
so `m̂ = 0` BY the convention (D.10's normalization, rev 14's exact sentence). -/
def Node.mhat (ν : Node p F) : ℤ := -ν.t * (ν.h : ℤ) * (ν.g : ℤ)

/-- The polynomial factor `(Ranch/ψ^μ) mod ψ` of the transported vertex value — pattern-only
data (§C.0 rev 8: the descend stratum fixes the side-digit tuple, which determines `Ranch`;
D.8's split is a factorization OF this fixed polynomial). Nonzero by `hOrd`
(`C3.vtxPolyNe`). -/
noncomputable def Node.vtxPoly (ν : Node p F) : Polynomial ↥ν.σ.K :=
  (ν.Ranch /ₘ ν.ψ ^ ν.μ) %ₘ ν.ψ

/-- **The transported vertex value** `vtx(ν) := z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F`
(§C.0, rev 8) — ALL scalar factors included, valued in the ambient field (which contains
`F_{i+1} = K(z̄)`). An explicit function of node data alone, so (HV) below is a predicate on
the history. [Round-1 audit: `vtxPoly` "omits the scalar factors … valued in the parent
field" — repaired.] -/
noncomputable def Node.vtx (ν : Node p F) : F :=
  (((ν.zbar ^ (ν.a - (ν.μ : ℤ) * ν.mhat)) : Fˣ) : F) *
    Polynomial.eval₂ ν.σ.K.subtype ((ν.zbar : Fˣ) : F) ν.vtxPoly

/-- The node's **line staircase** (§C (ZC-a)/DOM floor form): on its factor interior
`[0, μ·D_{i+1})`, the line's value at the LEFT EDGE of the base index's frame-`(i+1)` block;
`⊥` outside (its clause region contributes no floor beyond the interior). -/
noncomputable def Node.staircase (ν : Node p F) (b : ℕ) : WithBot ℚ :=
  if b < ν.μ * ν.childWidth
    then ((ν.line.at ((b / ν.childWidth) * ν.childWidth) : ℚ) : WithBot ℚ)
    else ⊥

/-- The read line as a COARSE step function of the base index over the WHOLE window
(`childWidth` block-left-edge value; NO factor-interior cutoff — cf. `staircase`, its
factor-interior truncation). ROUND 6 (audit R5 finding 7): NO LONGER the fresh-band upper edge
— `childWidth = e·g·Dwidth` groups `e·g` fine slots under ONE left-edge value, so at `e·g > 1`
this exceeds the later fine slots' true valuations (the line descends); the band boundary is
now the fine-slot law `Node.slotVal ∘ Node.fineSlot` (`inFreshBand`). Retained SOLELY as the
post-landing (ZC-a) staircase convention; the two boundaries coincide at recenterings
(`childWidth = Dwidth`). -/
def Node.lineStep (ν : Node p F) (b : ℕ) : ℚ := ν.line.at ((b / ν.childWidth) * ν.childWidth)

/-- ROUND 5 (audit R4 blocking list): the **FINE SLOT** of base index `b` — the read's OWN
frame-`i` development slot, blocks of width `Dwidth = deg Φ_i` (C.1.0(a): slot `j`'s
coefficient `B_j` occupies base indices `[j·Dwidth, (j+1)·Dwidth)`). The read's per-slot
clauses ((α)/(β)/(γ), the value digits) live at THIS granularity; `lineStep`'s coarser
`childWidth` blocks are the post-landing (ZC-a) staircase convention. -/
def Node.fineSlot (ν : Node p F) (b : ℕ) : ℕ := b / ν.Dwidth

/-- ROUND 5: `j` is a **SPAN SLOT** of the read — `j ∈ [s₀, s₀+wSide]`, the side's own slots
(C.1.0(b)(i)(α)). Exact-valuation VALUE digits live only at span slots (the (α) on-lattice
digits and the non-adjacent endpoint); β (`j < s₀`) and γ (`j > s₀+wSide`) slots assert
STRICT bounds — pure strip content, zeros through the line level included. -/
def Node.spanSlot (ν : Node p F) (j : ℕ) : Prop := ν.s0 ≤ j ∧ j ≤ ν.s0 + ν.wSide

/-- ROUND 5: the read line's **EXACT VALUATION at fine slot `j`** — `new(j) = line.at(j·Dwidth)`,
the height of slot `j`'s value digit (C.1.5′(1): "fresh VALUE clauses pin the first residual
digit of a slot coefficient B at its exact valuation γ′ = new(slot)"). -/
def Node.slotVal (ν : Node p F) (j : ℕ) : ℚ := ν.line.at (j * ν.Dwidth)

/-- **The node's standard lift** — D.5 displayed AT THE NODE's READ INDEX (ROUND 3, audit R2
F10): `Φ̂ = Φ^{e·g} + Σ_{ψ_k ≠ 0} t_k·Φ^{e·k}` over the frame's key/valuation/residual map,
with stride `ν.e`, realizer weights `σ.w(t_k) = h·(g−k)` (the READ's `h`, on the frame's
CURRENT valuation — the scale the coming augmentation stretches), digit scalars the literal
`ψ`-coefficients at the frame's forced (S5) positions `−σ.t·wPrev(t_k)`. Round 2 invoked
`IsStandardLift ν.σ`, whose stride/weights are the frame's stage pair `(σ.e, σ.h)` — the
frame-CREATING read's index, wrong for the node's own read. Replaces it in `HistoryCoherent`
and supplies the FINAL read's landing key (`LandingKey`, blocker 56). -/
def IsNodeLift (ν : Node p F) (Φhat : Polynomial ℤ_[p]) : Prop :=
  ∃ tt : ℕ → Polynomial ℤ_[p],
    (∀ k, ν.ψ.coeff k = 0 → tt k = 0) ∧
    (∀ k, k < ν.g → ν.ψ.coeff k ≠ 0 →
        tt k ≠ 0 ∧ inC ν.σ.Φ (tt k) ∧
          ν.σ.w (tt k) = (ν.h : ℤ) * ((ν.g : ℤ) - (k : ℤ)) ∧
          ν.σ.R (tt k) = LaurentPolynomial.C (ν.ψ.coeff k) *
            LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (tt k))) ∧
    Φhat = ν.σ.Φ ^ (ν.e * ν.g) + ∑ k ∈ Finset.range ν.g, tt k * ν.σ.Φ ^ (ν.e * k)

/-- **The landing-key law of one read** (D.5 increment/root; D.10 recentering — ROUND 3,
blocker 56): the key the read's landing produces, tied to the RECORDED node data. At a
recentering: `Φ' = Φ − lift` with the recorded lift a genuine center realizer (`w(lift) =
w(Φ)`, digit = the recorded center at position 0 — `IsRecentering`'s lift clauses, stated on
the node alone). Otherwise: the standard lift of the recorded `(ψ, g)` at the read's index.
`JetSetup.landing` imposes this at EVERY read `i < len` on the recorded key `keys i` —
including the FINAL read, whose landing transition round 2 left unrepresented. -/
def LandingKey (ν : Node p F) (Φtop : Polynomial ℤ_[p]) : Prop :=
  (ν.species = ReadSpecies.recentering →
    inC ν.σ.Φ ν.lift ∧ ν.lift ≠ 0 ∧ ν.σ.w ν.lift = ν.σ.w ν.σ.Φ ∧
      ν.σ.R ν.lift = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0 ∧
      Φtop = ν.σ.Φ - ν.lift) ∧
  (ν.species ≠ ReadSpecies.recentering → IsNodeLift ν Φtop)

end

/-! ## C4. Histories: coherence (tower provenance) and realizability ((NA)/(HV)) -/

/-- **A read history** `H = (ν₀, …, ν_k)` (§C.0): nonempty, the root read FIRST and ONLY first
(round-1 audit: "a later node may have species root" — excluded by `root_iff`). -/
structure History (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  nodes : List (Node p F)
  nonempty : nodes ≠ []
  root_iff : ∀ (j : ℕ) (hj : j < nodes.length),
    (nodes[j]'hj).species = ReadSpecies.root ↔ j = 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The accumulated stretch `STR_i = ∏_{m<i} e_m` of frame `i`'s valuation over `v_p`
(C.1.0(c)/the scale declaration: each transition stretches coefficient weights by its read's
`e`). -/
def History.strFrame (H : History p F) (i : ℕ) : ℕ := ((H.nodes.take i).map Node.e).prod

/-- **The cumulative floor** `F_{i−1}` carried by the prefix of length `i` (§C.1.5 (ZC-a)): the
pointwise max of the first `i` nodes' line staircases over their factor interiors, as a step
function of the base index. `floorH 0 = ⊥` (the root reads against an empty floor:
`E_fresh(ν₀) = E(ν₀)`). -/
noncomputable def History.floorH (H : History p F) (i b : ℕ) : WithBot ℚ :=
  ((H.nodes.take i).map (fun ν => ν.staircase b)).foldr max ⊥

/-- Level-`r` weight `κ_r = h_r/(e_r·STR_r)` (the C.1.5 scale declaration / LST(i)): FIXED by
node `r`'s READ data at the read that created the level; recenterings create no level (their
`innerslotH` below is 0, since `childWidth = Dwidth`). Junk `0` beyond the history. -/
noncomputable def History.kappaH (H : History p F) (r : ℕ) : ℚ :=
  (H.nodes[r]?).elim 0 (fun ν => (ν.h : ℚ) / ((ν.e : ℚ) * (H.strFrame r : ℚ)))

/-- The level-`r` inner slot of base index `b`: `(b mod D_{r+1}) / D_r` on the recorded width
chain (C.1.0(a) BLOCKS). At a recentering `D_{r+1} = D_r`, so the slot is 0 — no level. -/
def History.innerslotH (H : History p F) (r b : ℕ) : ℕ :=
  (H.nodes[r]?).elim 0 (fun ν => (b % ν.childWidth) / ν.Dwidth)

/-- **The K1-chain height, DEFINED from node data** (LST(i)/KEY OBS 1 — ROUND 3, audit R2
F47 + blocker 59; the round-2 bare `JetSetup.ht` field is DELETED): the frame-`i` absolute
v_p-height of base coordinate `c = (ℓ, b)` is `ℓ + Σ_{r<i} innerslot_r(b)·κ_r` — the current
key never enters (levels `r < i` only), κ's are birth-fixed, recentering levels contribute 0.
FLAG (the deferred graded bridge, its content unchanged but now attached to a SENTENCE):
that this formula is the K1-chain weight of the basis monomial `p^ℓ·Π_r Φ̂_r^{innerslot_r}`
(LST(i)) and that `log_p|𝔸(γ)| = |{c : htH = γ}|` per block (D.3(e)(ii)'s attainable
accounting, consumed by `mstar_eq`) are graded-ring content. -/
noncomputable def History.htH (H : History p F) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (H.innerslotH r c.2 : ℚ) * H.kappaH r)

/-- Read `i`'s constraint-region bound (C.1(ii)'s rim rule): fresh content of read `i` sits at
base indices `< μ_{i−1}·D_i` (the PREVIOUS read's rim threshold); the root read constrains the
whole `n`-index box. -/
def History.prevRim (H : History p F) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => (H.nodes[i]?).elim n (fun ν => ν.μ * ν.childWidth)

/-- **The READ REGRADE** `σ → σV` at a read pair `(e★, h★)` — HK-06 WAVE (task #44, the
ratified (S-a) two-step transition keying, BP2 §3.1(c), executed 2026-07-31): the
intermediate stage `σV` keeps the parent's key/fields/base/representatives, hosts the
READ pair (`σV.e = e★`, `σV.h = h★`), records the parent's `w` as its `wPrev`
(`child_wPrev`-style history invariant, one step earlier), and carries the
`(e★, h★)`-slot-minimum weight over the parent's `w`.  PAIR-PARAMETERIZED (the clause
list reads only the node's `(e, h)`), so `HC2.StageTransHyp`'s re-key can consume it
without a `Node` (dissolves BP2 REVISION-2 finding 6's layering cycle).  The clause
list is the HK-05-CERTIFIED staged core list (`HC2/HK05_countermodelGate.lean`'s
`StagedRegradeOf`, byte-per modulo the pair parameterization; the stall gate ran
against exactly these clauses).  The D.7(i)–(v) σV residual-law clauses are a NAMED
OPEN ADDENDUM — never ratified (BP2 pass-8: §B2-FINAL not accepted); the `e★ = 1`
recording fence in `HistoryCoherent` below keeps the recorded perimeter where the S9
route discharges them.  At a read with `(e★, h★) = (σ.e, σ.h)` and `σ.wPrev = σ.w`
pointwise, `σV := σ` satisfies every clause (the identity regrade; root reads at the
frame pair use a wPrev-re-dressed copy when `σ.wPrev ≠ σ.w`). -/
def RegradeOf (σ : Stage p F) (estar hstar : ℕ) (σV : Stage p F) : Prop :=
  σV.Φ = σ.Φ ∧ σV.e = estar ∧ σV.h = hstar ∧ σV.K = σ.K ∧ σV.FQ = σ.FQ ∧
  σV.reps = σ.reps ∧ (∀ f, σV.wPrev f = σ.w f) ∧
  IsSlotMinWeight σV.w σ.Φ estar hstar σ.w

/-- Regrade API: the regraded stage keeps the parent's residue field, so the D.6 next
field is unchanged (consumer supply for the `child_field` chains re-keyed by the HK-06
wave). -/
theorem RegradeOf.nextField_eq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {σ σV : Stage p F} {estar hstar : ℕ} (h : RegradeOf σ estar hstar σV) (zbar : Fˣ) :
    σV.nextField zbar = σ.nextField zbar := by
  unfold Stage.nextField
  rw [h.2.2.2.1]

/-- Regrade API: at an UNRAMIFIED read regrade (`e★ = 1`) the regraded weight agrees
with the parent's weight on the parent's coefficient carrier (the `e★ = 1` face of
C.1.0(c)'s stretch `σV.w B = e★·σ.w B`; the recorded slot-minimum at the single-slot
development).  This is the wave's replacement supply for consumers that read the OLD
`child_wPrev : σ'.wPrev = σᵢ.w` as landing on the parent — under (NEW) it lands on
`σV.w`, which THIS lemma folds back at the RG-2 perimeter `e★ = 1`. -/
theorem RegradeOf.w_coeff {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {σ σV : Stage p F} {hstar : ℕ} (h : RegradeOf σ 1 hstar σV)
    {B : Polynomial ℤ_[p]} (hB : B ≠ 0) (hin : inC σ.Φ B) : σV.w B = σ.w B := by
  have hsm := h.2.2.2.2.2.2.2
  have hdev : IsDevelopment σ.Φ B (fun j => if j = 0 then B else 0) 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = 0
      · simpa [hj] using (show B.degree < σ.Φ.degree from hin)
      · simp only [hj, if_false, Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr
          (fun hb => σ.hmonic.ne_zero (Polynomial.degree_eq_bot.mp hb))
    · intro j hj
      have : j ≠ 0 := by omega
      simp [this]
    · simp
  obtain ⟨hle, j, hjlt, hnz, heq⟩ := hsm B (fun j => if j = 0 then B else 0) 1 hB hdev
  have hj0 : j = 0 := by omega
  subst hj0
  norm_num at heq
  have hle0 := hle 0 (by omega) (by simpa using hB)
  norm_num at hle0
  omega

/-- **History coherence** (§C.0 + C.1.0): the recorded frames are linked by the ACCEPTED
§B2-DEF transitions AT THE RECORDED NODE DATA — no free existentials (round-1 audit repairs:
the increment transition consumes the PARENT node's recorded `ψ, g, e, h, zbar` through
`IsNodeLift` + `TransitionCoreL`; the recentering consumes the RECORDED `center`/`lift`
through `IsRecenteringCore`; the root frame is the base frame `deg Φ₀ = 1`; windows are
contained (`s₀'+w' ≤ μ`); the width chain `D_{i+1} = e_i·g_i·D_i` holds; lines steepen along
the history ((I-aug), absolute scale) and obey the absolute-scale slope law
`slope_i·(e_i·STR_i·D_i) = h_i`).
ROUND 3 additions: `IsNodeLift` replaces the round-2 `IsStandardLift ν.σ` call (F10: the lift
must use the READ's index, not the frame-creating read's); the child frame's Bézout pair is
tied to the node's recorded read pair (`σ'.s = s`, `σ'.t = t` — so `Node.mhat`/`vtx` carry the
tower's D.8 unit).
ROUND 4 (audit R3 findings 11/16): the round-3 vertex-entry/hinge clauses — a WEAKENED,
non-strict shadow of (SAE) — are DELETED: the span-entry inequality belongs to the
REALIZABILITY class (`TransitionAdmissible`/`Realizable`), rev 14's hypothesis boundary, and
never to coherence. In their place, the per-node **γ-TIE** (the on-lattice condition, role
(ii) of `Node.ustar`): the recorded integer `gam` equals the augmented-scale total side
weight `e_i·(STR_i·u*_i) + j*_i·h_i` (stage scale = `STR_i ×` absolute, C.1.0(c); `γ ∈ ℤ`
IS on-lattice, and `hAnchor` reads the stride-position anchor off it).
**HK-06 WAVE (task #44; the ratified (S-a) two-step regrade re-key, executed
2026-07-31 — BP2 §3.1(c) + the HK-22 emptiness certificate
`HC2/HK22_twoNodeGate.lean` proving the OLD keying's necessity-of-repair).** The OLD
non-recentering leg keyed BOTH the lift stride and `TransitionCoreL` at the PARENT
node's pair `(νᵢ.e, νᵢ.h)` with ties `σᵢ₊₁.s/t = νᵢ.s/t` — CONTRADICTORY at every
genuinely steep read (V10 findings 1–2, Lean-core on disk; the machine-certified gate
instance is `HK22.twoNodeGate_isEmpty`). The repaired leg decomposes the transition
per D.5→D.7: STEP 1, the READ REGRADE `RegradeOf σᵢ νᵢ.e νᵢ.h σV` (against which the
recorded `IsNodeLift` is the frame-pair standard-lift shape — S9's hypothesis class);
STEP 2, `TransitionCoreL σV σᵢ₊₁` at the NEXT pair `(νᵢ₊₁.e, νᵢ₊₁.h)` (D.7's next-side
keying; the child stage pair = the child node's read pair via `child_e`/`child_h`).
Wave riders, decided by the /goal rule with compiled evidence, recorded in
`lean/notes/QUEUE_EXECUTION_2026-07-31.md` §Item 3:
* **RG-2 recording fence** (the Q2-extension; evidence: §B2-FINAL NOT accepted at
  pass 8): the leg conjoins `νᵢ.e = 1` — non-recentering reads with regrade stride
  `e ≥ 2` (the open carry-algebra interior) are UNRECORDABLE, a disclosed definitional
  scope restriction (visible here, unlike the OLD silent contradiction). The V9 cone's
  `e ≥ 2` legs close by this disclosed emptiness, statements byte-unchanged.
* **R-tie guard** (evidence: the HK-15 per-leg pair-pin adjudication, item 16
  2026-07-31 — the ∀-(s,t) stage tie is UNPROVABLE for choice-built stages at
  `e' ≥ 2`, Bézout non-uniqueness under `Exists.choose`): the Bézout ties re-key to
  the CHILD node's pair (`σᵢ₊₁.s/t = νᵢ₊₁.s/t`, per the (S-a) display) and are
  GUARDED by `σᵢ₊₁.e = 1`, where `he1t`/`hbezCanon` force both sides. -/
def HistoryCoherent (H : History p F) : Prop :=
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (((H.nodes[i]'hi).gam : ℤ) : ℚ)
      = ((H.nodes[i]'hi).e : ℚ) * ((H.strFrame i : ℚ) * (H.nodes[i]'hi).ustar)
        + ((((H.nodes[i]'hi).s0 + (H.nodes[i]'hi).wSide) : ℕ) : ℚ) * ((H.nodes[i]'hi).h : ℚ)) ∧
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    ((H.nodes[i]'(by omega)).species = ReadSpecies.recentering →
      IsRecenteringCore (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
        (H.nodes[i]'(by omega)).center (H.nodes[i]'(by omega)).lift) ∧
    ((H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering →
      (H.nodes[i]'(by omega)).e = 1 ∧
      ∃ σV : Stage p F,
        RegradeOf (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).e
            (H.nodes[i]'(by omega)).h σV ∧
        IsNodeLift (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi).σ.Φ ∧
        TransitionCoreL σV (H.nodes[i+1]'hi).σ
          (H.nodes[i+1]'hi).σ.Φ (H.nodes[i+1]'hi).e (H.nodes[i+1]'hi).h
          (H.nodes[i]'(by omega)).zbar) ∧
    ((H.nodes[i+1]'hi).σ.e = 1 → (H.nodes[i+1]'hi).σ.s = (H.nodes[i+1]'hi).s) ∧
    ((H.nodes[i+1]'hi).σ.e = 1 → (H.nodes[i+1]'hi).σ.t = (H.nodes[i+1]'hi).t) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope)

/-- **TRANSITION-ADMISSIBLE** (§C.0, rev 13 — ROUND 4, audit R3 finding 10): the read `ν`
appended after the standing node `νp` satisfies the THREE data conditions (NA)+(HV)+(SAE) at
the appended read — all equations/inequalities of NO `E`, on node data alone. Lines are
compared at BASE indices: standing-window slot `j` ↔ `j·νp.childWidth` (= `j·ν.Dwidth` under
coherence). This is THE per-step interface rev 14's C.1/C.1.0(b)(iii)/C.1.5 hypothesize of
their appended reads (consumed here through `Realizable`/`JetSetup.realizable`, and directly
by `C3.lineDom`); without it their conclusions are FALSE on the certified F-EMPTY data.
* **(NA)** at a NON-ADJACENT read (`s₀'+w' < μ`): the pinned old vertex lies STRICTLY ABOVE
  the extended new line at the vertex's base index `μ·D_{i+1}`;
* **(HV)** at an ADJACENT read (`s₀'+w' = μ`): the pattern LEAD of `ν` (its endpoint digit
  `pat(wSide/e)`, the vertex digit) EQUALS the transported vertex value `vtx(νp)` in `F`;
* **(SAE)** SPAN-ENTRY INEQUALITY (rev 12 — the third condition; ROUND 4, audit R3 findings
  8/9: absent in round 3, whose coherence tie allowed equality — the F-EMPTY configuration):
  the read side lies STRICTLY ABOVE the old box line at every span slot below the window
  vertex, and MATCHES it at the vertex when the span reaches it:
    `new(j) > old(j)` for every span slot `j ∈ [s₀', j*]` with `j < μ`;
    `new(μ) = old(μ)` when `j* = μ` (adjacent — the vertex-anchored side height:
    with `hLineU`, `u* =` the standing window-vertex height). -/
def TransitionAdmissible (νp ν : Node p F) : Prop :=
  (ν.s0 + ν.wSide < νp.μ →
    ν.line.at (νp.μ * νp.childWidth) < νp.line.at (νp.μ * νp.childWidth)) ∧
  (ν.s0 + ν.wSide = νp.μ →
    ((ν.pat (ν.wSide / ν.e) : ↥ν.σ.K) : F) = νp.vtx) ∧
  (∀ j : ℕ, ν.s0 ≤ j → j ≤ ν.s0 + ν.wSide → j < νp.μ →
    νp.line.at (j * νp.childWidth) < ν.line.at (j * νp.childWidth)) ∧
  (ν.s0 + ν.wSide = νp.μ →
    ν.line.at (νp.μ * νp.childWidth) = νp.line.at (νp.μ * νp.childWidth))

/-- **Realizability** (§C.0, rev 12/14 — ROUND 4, audit R3 finding 9: the FULL three-condition
class): a lift-carrying history is REALIZABLE iff EVERY appended read is transition-admissible
— (NA)+(HV)+(SAE) at every read `ν_{i+1}`, `i ≥ 0`. A history failing any of the three has
EMPTY joint stratum (the classifier never emits it), and Theorem C's quantifier ranges over
realizable histories only. The round-3 two-condition version admitted (SAE)-violating
histories (the F-EMPTY instance: nominal fresh volume `2⁻⁶`, actual census count 0). -/
def Realizable (H : History p F) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    TransitionAdmissible (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi)

end

/-! ## C5. The (ZC) invariant and the presented history (jet setup) -/

/-- **The (ZC) invariant on a state cylinder** (§C.1.5), against a coordinate chart `coordOf`,
a height map `ht`, the cumulative floor `floor` (a step function of the base index), and the
rim threshold `rimIdx = μ_i·D_{i+1}` (a BASE-INDEX region — round-1 audit: a rim condition "is
not a suffix of the global order"; the `rimStart : Fin m` encoding and its `rimStart := 0`
vacuity are gone, and `m = 0` is unproblematic):
* **(ZC-a) EXACT DOWNSET** — at interior base indices (`< rimIdx`), a coordinate is pinned IFF
  its height is at most the floor (BOTH directions: the round-1 `pin_dichotomy` allowed
  under-pinning);
* **(ZC-a) LITERAL ZEROS** — interior pins solve to the constant `0` (the zero downset
  `Z(F_i)`);
* **(ZC-b) LEADS AT RIM** — every other pin is at a rim base index; its `solve` is
  unrestricted (`DIG_i`: unitriangular, non-lead arguments free). [The finer §C statement that
  each `DIG_i` equation solves for one rim-block LEVEL SET is presentation content of the
  deferred jet bridge; the counting consumes rim-ness of the leads only — C15 S4c.] -/
structure ZCData {p m : ℕ} (D : Locus p m) (coordOf : Fin m → Coord) (ht : HtMap)
    (floor : ℕ → WithBot ℚ) (rimIdx : ℕ) : Prop where
  downset_exact : ∀ j : Fin m, (coordOf j).2 < rimIdx →
    (D.pinned j = true ↔ ((ht (coordOf j) : ℚ) : WithBot ℚ) ≤ floor (coordOf j).2)
  interior_zero : ∀ j : Fin m, (coordOf j).2 < rimIdx → D.pinned j = true →
    ∀ f : (j' : Fin m) → j' < j → ZMod p, D.solve j f = 0

/-- The `ℓ`-th base-`p` digit of a p-adic integer, valued in `ZMod p` — concretely
`(a mod p^{ℓ+1}) / p^ℓ`. The FRAME-0 jet chart (`JetSetup.pres_zero`) reads a polynomial's
base coordinate `(ℓ, i)` as `baseDigit p ℓ (f.coeff i)`: the presentation spine bottoms out
at literal p-adic digits of literal coefficients (ROUND 3, blocker 55). -/
noncomputable def baseDigit (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (a : ℤ_[p]) : ZMod p :=
  (((PadicInt.toZModPow (ℓ + 1) a).val / p ^ ℓ : ℕ) : ZMod p)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The FRESH BAND of read `i`** (ROUND 4, audit R3 finding 17 — §C.1(ii)'s D.11 species
inventory, named as a COORDINATE predicate; ROUND 6, audit R5 finding 7 / blocking list — the
upper edge moved from the coarse `childWidth` staircase to the FINE-slot boundary): coordinate
`c` is in read `i`'s band iff it lies in the read's constraint region (base index `< prevRim`
— C.1(ii)'s rim rule), STRICTLY ABOVE the cumulative floor (LST(iii) selection), and
AT-OR-BELOW its own fine slot's EXACT VALUATION `new(j) = slotVal (fineSlot idx)` — the
recorded fine-slot valuation law, rev 14 C.1(ii)'s per-slot inventory granularity (C.1.0(a):
frame-`i` blocks of width `Dwidth`). The round-4/5 bound `Node.lineStep` (coarse `childWidth`
left edges — the post-landing (ZC-a) staircase) exceeds `slotVal (fineSlot b)` at the later
fine slots of each coarse block whenever `e·g > 1` (the line descends), so it admitted
coordinates rev 14 leaves UNCONSTRAINED and — via `fresh_cover` + `fresh_assembled`'s strip
tag — forced spurious zeros there. The band at fine slot `j` is now exactly `(floor, new(j)]`:
strip zeros strictly between floor and `new(j)`, plus the on-lattice level set AT `new(j)` at
span slots (`IsValueCoord`, the value positions — the band's upper edge). Past the (γ)
crossing slot `new(j) ≤ floor`: the band self-truncates per FINE slot — C.1(i)(γ)'s cut,
exact. `ν` is instantiated at `H.nodes[i]`; heights are the DEFINED `History.htH`. Consumed BY
NAME (byte-stable) by `JetSetup.fresh_band`/`fresh_cover`/`mstar_eq`: together they say each
band coordinate belongs to EXACTLY its strip/level-set clause and nothing else. -/
def inFreshBand (H : History p F) (n : ℕ) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (c : Fin m) : Prop :=
  (coordOf c).2 < H.prevRim n i ∧
  H.floorH i (coordOf c).2 < ((H.htH i (coordOf c) : ℚ) : WithBot ℚ) ∧
  H.htH i (coordOf c) ≤ ν.slotVal (ν.fineSlot (coordOf c).2)

/-- **The VALUE POSITIONS of read `i`** (ROUND 5, audit R4 finding 10 / blocking item 2 — the
strip/value species label, now a FUNCTION of node geometry, per coordinate): `c` is a VALUE
position iff its FINE slot (the read's own development slot, width `Dwidth` — C.1.0(a)) is a
SPAN slot AND its height is that slot's EXACT VALUATION `new(j)`. This is rev 14 C.1(ii)'s
on-lattice value-digit locus: the (α) span digits and the non-adjacent endpoint's value digit
(the adjacent hinge block sits at/beyond `prevRim`, outside the band — the (HV) no-pin
clause). Everything else in the band is STRIP content: (α)-strips strictly between floor and
exact valuation, (β)/(γ)-strips through the line at off-span slots (their clauses are strict
bounds, so the line-level coordinate is a ZERO there, not a value), cluster zeros at the
root. Off-lattice span heights select the empty level set — no coordinate sits there. -/
def IsValueCoord (H : History p F) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (c : Fin m) : Prop :=
  ν.spanSlot (ν.fineSlot (coordOf c).2) ∧
    H.htH i (coordOf c) = ν.slotVal (ν.fineSlot (coordOf c).2)

/-- **The VALUE-SUPPORT law** (ROUND 5, audit R4 blocking item 3): a value clause's support is
the COMPLETE height-level set of ONE recorded span slot at its recorded exact valuation —
membership as an IFF over the whole box, never a `⊆`:
`c ∈ S ⟺ (c lies in fine block j) ∧ (ht(c) = new(j))`, `j` a span slot. Cross-block subsets,
partial level sets, level sets of off-span slots, and arbitrary constant-height supports (the
round-4 permutations, audit finding 10) are all illegal. Membership in a legal value support
is exactly `IsValueCoord` at the recorded slot. -/
def IsValueSupport (H : History p F) {m : ℕ} (coordOf : Fin m → Coord)
    (i : ℕ) (ν : Node p F) (S : Finset (Fin m)) : Prop :=
  ∃ j : ℕ, ν.spanSlot j ∧
    ∀ c : Fin m, c ∈ S ↔ (ν.fineSlot (coordOf c).2 = j ∧ H.htH i (coordOf c) = ν.slotVal j)

/-- **The jet presentation of a history** — the BOUNDARY-DEFERRED bridge from the accepted
tower to digit systems (§C.2's `Ψ_H`; D.3(e)(ii) down the whole tower, at a level cutoff
`N ≥ N(H, Z)` — largeness of `N` is an existence condition on the presentation). Indexing:
`Sigma 0` = the full box; read `ν_i` is consumed once between `Sigma i` and `Sigma (i+1)`;
junk beyond `H.nodes.length` is never consumed. ROUND 3 (blockers 55-60): every field now
carries a PROVENANCE law tying it to `H.nodes` — see the module header. The deferred content
(the unbuilt graded ring, R4.5 items 1&3) is the EXISTENCE of this bundle for a real
classifier history, plus the two flagged identifications on `History.htH`; the SENTENCES all
exist below. FLAGGED for semantic-guardian review throughout. -/
structure JetSetup (H : History p F) (n N m : ℕ) where
  /-- the box is the `n·N` coefficient box (BLOCK CONVENTION, base digits). -/
  hm : m = n * N
  /-- ROUND 4 (audit R3 finding 18) — the CUTOFF condition: Theorem C's quantifier is
  "for every `N ≥ N(H, Z)`", with `N(H, Z) := 1 + the largest base level among `T(H,Z)`'s
  equations `≥ 1`. The `≥ 1` floor is recorded here (killing the `N = 0`, `m = 0` degenerate
  presentations, whose `pres_zero` was vacuous); the `≥ N(H, Z)` half is automatic INSIDE the
  box (`coordOf_lt` bounds every equation's level below `N`) and is otherwise the
  existence-side largeness condition on the presentation. -/
  hN : 1 ≤ N
  /-- the ≺-SORTED coordinate chart: `Fin m`-order IS the global order `≺`. -/
  coordOf : Fin m → Coord
  coordOf_sorted : ∀ j j' : Fin m, j < j' ↔ CoordPrec (coordOf j) (coordOf j')
  /-- the chart lands in the box: levels `< N`, base indices `< n`. -/
  coordOf_lt : ∀ j : Fin m, (coordOf j).1 < N ∧ (coordOf j).2 < n
  /-- the presented history is coherent (consumed by every downstream theorem). -/
  coherent : HistoryCoherent H
  /-- and realizable — ROUND 4: the FULL (NA)+(HV)+(SAE) class, definitionally
  `∀ i, TransitionAdmissible ν_i ν_{i+1}`: every per-step consumer (the C.1/C.1.5 mirrors
  `C2.EInh_implied`/`C4.stepMass`) receives rev 13's per-step hypothesis for its read through
  this field; §C's quantifier ranges over realizable histories only. -/
  realizable : Realizable H
  /-- ROUND 4 (audit R3 finding 19) — the ROOT-SIDE HEIGHT condition (DOM's rev-11 base
  display): the root line dominates the CLUSTER FLOOR — height `≥ 1` at every base index of
  the root factor interior (D.4's ROOT case: every side slope `≥ 1`; the cluster zeros pin
  level 0, floor height 1). So `mstar_eq` at `i = 0` COUNTS the cluster zeros (level-0
  coordinates sit in the root band), and the root intercept can no longer be translated
  below the cluster floor. -/
  root_height : ∀ (hj : 0 < H.nodes.length) (b : ℕ),
    b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth → 1 ≤ (H.nodes[0]'hj).line.at b
  /-- the state cylinder before read `i`: `Sigma i = Σ_{i−1}` in frame-`i` coordinates. -/
  Sigma : ℕ → Locus p m
  /-- INITIALIZATION: `Σ_{−1}` is the full box — nothing is pinned before the root read. -/
  init : ∀ c : Fin m, (Sigma 0).pinned c = false
  /-- the fresh clause data of read `ν_i` (§C.1(ii)'s species inventory, address-free);
  PINNED to the node by `fresh_assembled`/`mstar_eq`/`fresh_band`/`fresh_cover` (ROUND 4). -/
  fresh : ℕ → FreshData p m
  /-- the move maps `Θ_i` (child-to-parent coordinate reading); PINNED to the recorded keys
  by `pres_theta`/`pres_block` (ROUND 3, blocker 55). -/
  Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  /-- (§C.0.5) each move is unitriangular for `≺` (Fact A's division accounting; DEFERRED). -/
  Theta_uni : ∀ i : ℕ, IsUnitriangular (Theta i)
  /-- the recorded LANDING KEYS: `keys i` = the key read `ν_i`'s landing produces (frame-(i+1)
  key). Interior: pinned to the child frame (`keys_mid`); ALL reads incl. the FINAL one obey
  the recorded-data landing law (`landing` — ROUND 3, blocker 56). -/
  keys : ℕ → Polynomial ℤ_[p]
  keys_mid : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ
  landing : ∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)
  /-- **the presentation spine** (ROUND 3, blocker 55): `pres i x f` = "`x` is the frame-`i`
  digit presentation of the integral polynomial `f`". The spine is what ties the abstract
  digit-level data to actual polynomials; its EXISTENCE laws are the deferred jet bridge. -/
  pres : ℕ → (Fin m → ZMod p) → Polynomial ℤ_[p] → Prop
  /-- frame 0 is the LITERAL p-adic coefficient chart — fully concrete. -/
  pres_zero : ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]),
    pres 0 x f ↔ ∀ j : Fin m, x j = baseDigit p (coordOf j).1 (f.coeff (coordOf j).2)
  /-- every monic degree-`n` integral polynomial has a frame-`i` presentation (D.3(e)(ii)
  existence; DEFERRED — the graded bridge). -/
  pres_total : ∀ i : ℕ, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p],
    f.Monic → f.natDegree = n → ∃ x, pres i x f
  /-- **`Θ_i` IS read `ν_i`'s move** (blocker 55): it translates frame-(i+1) presentations of
  `f` to frame-`i` presentations of the SAME `f` — the Fact-A re-reading, on actual
  polynomials. -/
  pres_theta : ∀ i : ℕ, i < H.nodes.length →
    ∀ (x : Fin m → ZMod p) (f : Polynomial ℤ_[p]), pres (i+1) x f → pres i (Theta i x) f
  /-- frame-(i+1) presentations are BLOCK-LOCAL over the recorded landing key's development
  (C.1.0(a)): the digits over slot `j`'s base-index block depend on the development slot
  `B j` alone. -/
  pres_block : ∀ i : ℕ, i < H.nodes.length →
    ∀ (f f' : Polynomial ℤ_[p]) (x x' : Fin m → ZMod p), pres (i+1) x f → pres (i+1) x' f' →
    ∀ (B B' : ℕ → Polynomial ℤ_[p]) (Nd Nd' : ℕ),
      IsDevelopment (keys i) f B Nd → IsDevelopment (keys i) f' B' Nd' →
      ∀ c : Fin m,
        B ((coordOf c).2 / (keys i).natDegree) = B' ((coordOf c).2 / (keys i).natDegree) →
        x c = x' c
  /-- read `ν_i`'s STRATUM, in frame-`i` coordinates (the full clause content `E(ν_i)`,
  inherited + fresh). -/
  stratum : ℕ → (Fin m → ZMod p) → Prop
  /-- **the stratum equation** (ROUND 3, F43/blocker 55 — replaces the round-2 fresh-only
  `recursion`): `Σ_i = Θ_i(Σ_{i−1} ∩ stratum(ν_i))` — D.8/D.10 two-sidedness AT THE STRATUM,
  no implication absorbed. -/
  recursion : ∀ i : ℕ, i < H.nodes.length → ∀ x : Fin m → ZMod p,
    (Sigma (i+1)).IsSolution x ↔ ((Sigma i).IsSolution (Theta i x) ∧ stratum i (Theta i x))
  /-- **C.1(i) AS A SENTENCE** (ROUND 3): on the state cylinder, the stratum's inherited
  content is implied — the stratum reduces to exactly its fresh clauses. -/
  inh_implied : ∀ i : ℕ, i < H.nodes.length → ∀ y : Fin m → ZMod p,
    (Sigma i).IsSolution y → (stratum i y ↔ (fresh i).sat y)
  /-- the (ZC) invariant at every prefix, at the HISTORY's floor, the DEFINED K1 heights
  (`History.htH`, frame `i+1`), and the RECORDED rim threshold (§C.1.5). -/
  zc : ∀ (i : ℕ) (hi : i < H.nodes.length),
    ZCData (Sigma (i+1)) coordOf (H.htH (i+1)) (H.floorH (i+1))
      ((H.nodes[i]'hi).μ * (H.nodes[i]'hi).childWidth)
  /-- **every fresh clause support lies INSIDE the band** (ROUND 4, audit R3 finding 17 —
  replaces the round-3 `fresh_above` + `fresh_interior`, which gave only the floor and rim
  bounds and left the band's UPPER EDGE open): each supported coordinate is in read `i`'s
  region (`< prevRim`), strictly above the cumulative floor (LST(iii)), and at-or-below its
  own fine slot's exact valuation (ROUND 6: `inFreshBand`'s fine boundary). No fresh
  codimension can sit on unrelated above-floor coordinates. -/
  fresh_band : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (fresh i).clauses,
    ∀ c ∈ cl.support, inFreshBand H n coordOf i (H.nodes[i]'hi) c
  /-- **every band coordinate is covered** (ROUND 4, finding 17): each coordinate of read
  `i`'s fresh band lies in SOME fresh clause's support — and in EXACTLY ONE, by
  `FreshData.disj`. With `fresh_band` (supports ⊆ band) and `fresh_assembled`'s per-clause
  codimension, every counted band coordinate belongs to exactly its strip/level-set clause:
  the permutation loophole (equal totals on permuted supports) is unbuildable. -/
  fresh_cover : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ c : Fin m,
    inFreshBand H n coordOf i (H.nodes[i]'hi) c → ∃ cl ∈ (fresh i).clauses, c ∈ cl.support
  /-- **fresh clauses are ASSEMBLED from the two §C shapes, GEOMETRICALLY TAGGED** (ROUND 3,
  blocker 60; ROUND 4, finding 17; ROUND 5, audit R4 finding 10 / blocking list — the one
  remaining loophole). Each clause is
  * a **STRIP** — singleton support `{c}`, `codim = 1`, the literal zero `x c = 0`, at a
    coordinate that is NOT a value position (`¬ IsValueCoord` — the ROUND-5 tag): β/γ strips
    through the line, (α)-strips strictly between floor and exact valuation, cluster zeros; or
  * a **VALUE clause** — support THE COMPLETE level set of ONE recorded span slot at its exact
    valuation (`IsValueSupport`, an IFF — subsumes round 4's bare constant-height law),
    `codim = support.card` (TYP(b)'s `|alphabet| = |piece|` / D.3(e)(ii)'s attainable
    accounting, per clause), constraint a `TypObject` surjection onto `(ZMod p)^codim` at an
    emitted value `v` (whose provenance from the node's pattern digit is the declared graded
    boundary — blueprint R4.B.2, not geometry).
  THE IMPERSONATION WALK (audit R4 blocking item 4, the all-singleton-zero construction: cover
  every band coordinate by its own `x c = 0` strip): at any VALUE position `c₀` (a span slot's
  exact-valuation level set), the strip branch now FAILS — `IsValueCoord c₀` holds and the tag
  forbids it; a "value" clause with support `{c₀} ⊊ L` FAILS the `IsValueSupport` iff whenever
  the level set `L` has a second coordinate (block convention: every residue degree ≥ 2); and
  `fresh_cover` + `FreshData.disj` put `c₀` in EXACTLY one clause — which must therefore be THE
  complete-level-set value clause of its slot. Where `L` is a genuine singleton the forced
  clause IS the species-correct value clause (only `v` stays existential — R4.B.2). So clause
  species and support geometry are functions of node data; the construction is unbuildable. -/
  fresh_assembled : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (fresh i).clauses,
    (∃ c : Fin m, cl.support = {c} ∧ cl.codim = 1 ∧ (∀ x, (cl.sat x ↔ x c = 0)) ∧
      ¬ IsValueCoord H coordOf i (H.nodes[i]'hi) c) ∨
    (IsValueSupport H coordOf i (H.nodes[i]'hi) cl.support ∧
      cl.codim = cl.support.card ∧
      ∃ (T : TypObject p m cl.support (Fin cl.codim → ZMod p)) (v : Fin cl.codim → ZMod p),
        ∀ x, (cl.sat x ↔ T.φ x = v))
  /-- **`m*(ν_i)` IS the D.11 species inventory** (ROUND 3, blocker 57; ROUND 4: stated via
  the named band `inFreshBand`): the presented fresh codimension sum equals the FRESH-BAND
  count computed from node data (strips + value level sets; past the (γ) crossing the
  fine-slot value `new(j)` is below the floor, so the band self-truncates per fine slot —
  C.1(i)(γ), ROUND 6's exact boundary; at an adjacent read the hinge
  block sits at/beyond `prevRim`, so it is excluded — the (HV) no-pin clause). With
  `fresh_band`/`fresh_cover`/`fresh_assembled` this total now also decomposes PER CLAUSE. -/
  mstar_eq : ∀ (i : ℕ) (hi : i < H.nodes.length),
    (fresh i).mstar = Nat.card {c : Fin m // inFreshBand H n coordOf i (H.nodes[i]'hi) c}

/-- The partial move composite `seg i k = Θ_i ∘ Θ_{i+1} ∘ … ∘ Θ_{k−1}` (frame-`k` coordinates
down to frame-`i` coordinates); `seg 0 k` is `Ψ_H^{−1}` up to prefix `k`. -/
def JetSetup.seg {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (i : ℕ) :
    ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  | 0 => id
  | k + 1 => if i ≤ k then J.seg i k ∘ J.Theta k else id

/-- **The recorded move composite** `Ψ_H^{−1}`-side: `Psi k = Θ_0 ∘ … ∘ Θ_{k−1}` carries the
final-frame presentation back to `f`-coordinates (§C.2: `S(H,Z) = Ψ_H^{−1}(Σ_k ∩ locus Z)`,
stated in `C6.thmC_a/b` about THIS composite — round-1 audit: "no history move composition"). -/
def JetSetup.Psi {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (k : ℕ) :
    (Fin m → ZMod p) → (Fin m → ZMod p) := J.seg 0 k

/-- **The classifier locus `S(H, Z)`, INDEPENDENTLY defined** (ROUND 3, blocker 58 — §C.2's
transported system `T(H, Z)` as a sentence): `x` (frame-0 digits) lies in `S(H, Z)` iff it
carries a presentation chain `y` down the recorded moves (`y 0 = x`, `y i = Θ_i (y (i+1))`)
whose frame-`i` stage satisfies read `ν_i`'s fresh clauses and whose final stage solves `Z`.
This is `E(ν₀) ∪ Θ₀*(E_fresh(ν₁) ∪ Θ₁*( … ∪ Θ_k*(Z)))` with the pullbacks unfolded as the
∃-chain — NO reference to `Sigma` or to any image; `C6.thmC_a` PROVES the equality with the
transported image of the final joint locus. -/
def JetSetup.SHZ {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (Z : Locus p m) :
    Set (Fin m → ZMod p) :=
  {x | ∃ y : ℕ → (Fin m → ZMod p), y 0 = x ∧
    (∀ i : ℕ, i < H.nodes.length → y i = J.Theta i (y (i+1))) ∧
    (∀ i : ℕ, i < H.nodes.length → (J.fresh i).sat (y i)) ∧
    Z.IsSolution (y H.nodes.length)}

/-- **Admissible terminal system `Z`** (§C.2, rev 9 — a LOCUS condition): `Z` solves only for
coordinates FREE on the FINAL state cylinder (round-1 audit: admissibility was checked against
the wrong prefix in the `k = 0` countermodel; consumers instantiate `Sigma := J.Sigma
H.nodes.length`). -/
def AdmissibleZ {p m : ℕ} (Sigma Z : Locus p m) : Prop :=
  ∀ c : Fin m, Z.pinned c = true → Sigma.pinned c = false

/-- The **total pin count** of `T(H, Z)`: `Σ_{i<len} m*(ν_i) + |pins(Z)|` — the codimension of
the joint locus, read off the mass (PIN-WELLDEF; division-free form `mass·p^K = p^{nN}`). -/
def totalPins {H : History p F} {n N m : ℕ} (J : JetSetup H n N m)
    (Z : Locus p m) : ℕ :=
  (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) + Z.numPinned

end

end LeanUrat.MovesC
