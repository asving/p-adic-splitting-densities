# Verdict: UNIT R34 — deep-witness realization rows R3 (points/evaluation) + R4 (thresholds/windows)

**Status: LANDED, first attempt, zero repairs, zero `sorry`.**

Source: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 rows R3
("Extend the NP point, coefficient hom, coordinate, and valuation laws
through both new live stages"; models: `C130s17.s2EvalHom` + `C130sg.s2SplitNode`;
inputs: R1/R2; blocker: "valuation realization") and R4 ("Supply source-backed
thresholds at levels 1–4 and prove strict windows; no invented numeral branch";
model: `C130sg.S2LevelOneThreshold` + `.ofSplitNode`; inputs: R1/R2).

New file: `leanfinal/Uniformity/ChapC/C136r2.lean`
(namespace `Uniformity.Density.Tower.C136r2`). No landed file edited;
`C136e2.lean` (D4-17/18, in flight elsewhere) neither touched nor imported.

## R3 — what landed

* **Part A** (generic infrastructure): `s2Hgt₅_eq_top_iff` (genuinely new — the
  μ₅ finiteness-iff, built from the two already-landed halves `s2Hgt₅_zero`/
  `s2Hgt₅_ne_top`), and a generic combinator `s2ExtendVal` that packages +
  extends ANY landed `AddValuation (Polynomial O) (WithTop ℤ)` to
  `E = FractionRing (Polynomial O)` — replaying NV-5/NV-6's hand-written
  pipeline (`Val → hS → extendToLocalization → ofValuation → restriction pin`)
  ONCE instead of three more times by hand.
* **Part B**: the combinator instantiated at the blocker note's own two named
  datums plus the pre-campaign μ₃ input: `s2AddEVal₃` (from `C132nv6.s2AddVal₃`),
  `s2AddEVal₄` (from `C136d1.s2AddVal₄`, D3-05), `s2AddEVal₅` (from
  `C136e0.s2AddVal₅`, D4-03) — each with its restriction PIN back to
  `s2Hgt₃`/`s2Hgt₄`/`s2Hgt₅`, plus the four unconditional valuation laws at μ₅.
* **Part C** (R3's core exit): `s2NPValuationFour`/`s2NPValueOnFour`/
  `s2NPPointHgtFour` — the depth-four four-branch point-valuation dispatcher,
  reusing NP-0's `S2NPPoint`/`s2NPCoeffHom`/`s2NPCoord` verbatim (branches 1/2
  unchanged; branches 3/4 = Part B, the genuinely new content). The four
  unfenced `valueOn` laws transfer with NO extra proof (every branch is a
  genuine `AddValuation`). Restriction dictionaries
  `s2NPPointHgtFour_one/two/three/four` tie the point read to
  `s2PHgt₁`/`s2Hgt₂`/`s2Hgt₃`/`s2Hgt₄`.
* **Part D** (superset, mirroring R1/R2's own ambiguity resolution): the
  μ₅-refinement point read `s2NPPointHgtMu5`, tied to `s2Hgt₅` and, via R2's
  `s2SlotFourMu5_hgt_eq`, to the landed level-four slot carrier
  (`s2NPPointHgtMu5_eq_slot`).

**Named open (disclosed, not invented):** whether the direct choice
`pointHgt i = s2Hgt_i`'s extension ALSO satisfies the eventual `key_value` law
at the now-gauge-live levels 2/3 (`s2Hgt₂ (keyAt 2) =? u₃`, `s2Hgt₃ (keyAt 3)
=? u₄`) is unverified — no landed theorem decides it, and if false, a bespoke
fix analogous to NP-0's own `s2PHgt₁` discovery would be needed one level up.
Recorded by name in the module docstring as R7's problem.

## R4 — what landed

* Three new open-datum structures mirroring `C130sg.S2LevelOneThreshold`'s
  exact field shape (`T`, `Tnat`, `T_natCast`, `T_lt_key`) at levels 2, 3, 4:
  `S2LevelTwoThresholdFour` (`T < 21`), `S2LevelThreeThresholdFour` (`T < 85`),
  `S2LevelFourThresholdFour` (`T < 171`).
* Bound-source pins threading each bound from the landed height-at-key facts
  (never re-derived): `s2LevelTwoThresholdFour_bound_source` (=
  `C132nv1.s2Hgt₃_Φ₂`), `s2LevelThreeThresholdFour_bound_source` (=
  `C136d0.s2Hgt₄_g8`), `s2LevelFourThresholdFour_bound_source` (=
  `C136e0.s2Hgt₅_g16`).
* Disclosure teeth (anonymous, non-consumable) at exactly the campaign's
  stated margins `4 < 5`, `20 < 21`, `84 < 85`, `170 < 171`.
* `s2StrictWindow_of_key_value` — the generic one-line strict-window step
  (mirroring `s2SplitNode`'s own `window` proof: `WithTop.coe_lt_coe.mpr
  w.T_lt_key`), instantiated at all four levels
  (`s2LevelOneWindow_strict/Two/Three/Four`), so a future full split-node
  assembly (R7) does not re-derive it per level.

**Named open (disclosed, not invented):** the necessity direction
(`.ofSplitNode`'s converse) needs an actual depth-four `SplitNodePointSource`,
which does not exist yet (R7); left as R7's exit condition.

## Verification

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136r2.lean
```

Exit code 0, zero stderr output beyond the 43 `#print axioms` lines. Every
declaration's footprint is `[propext, Classical.choice, Quot.sound]`
(Lean-core only); zero `sorry`; zero warnings (verified separately before the
AxCheck footer was appended). Built incrementally (Parts A → B → C → D → R4
thresholds → windows → AxCheck), each increment re-checked before the next was
appended, per discipline.

## Scope discipline

No bare `rfl` through composed internals: the one place a plain `rfl` would
not close post-`rw` (`s2ExtendVal_algebraMap`'s final `AddValuation.toValuation
v A = v A` step, hidden behind `Multiplicative.ofAdd`/`OrderDual.toDual`
wrapping) is discharged by an explicit `show` unfolding the definitional
target first, then `rw` + a terminal `rfl` — never a blind `rfl` against the
wrapped mathlib API. No landed statement touched; no git operations performed;
no dependence on `C136e2.lean`.
