# UNIT A0GA — VERDICT: nodes A0G-CL / A0G-AS / A0G-DS / A0G-ALL (the assembly)

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG14.lean` (NEW, 474 lines).
Verification: `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean
Uniformity/ChapI/IFCG14.lean` — **exit 0, zero errors, zero warnings, zero `sorry`,
zero new axioms**.  Repo footprint: exactly this file + this verdict; no landed file
touched; no git ops.

## Headline

**The four assembly nodes are LANDED — in the blueprint §2's OWN named-package
architecture, not the unconditional form.**  The ★ prize `decidedSliceAt_all : ∀ n,
DecidedSliceAt n` is deliberately NOT declared (the name is reserved): it is not
reachable by assembly of the landed inputs, for reasons recorded in the consumed nodes'
own verdicts (see "The honest boundary" below).  What IS landed:

* ★ `decidedSliceAt_all_of_recursion : UniformClusterRecursion → ∀ n, DecidedSliceAt n`
  — the a0 capstone field at EVERY degree, **no `0 < n` guard**, conditional on ONE
  named socket (`ClusterRecursionAt`, needed only at masses `≥ 4`) — **PURE LEAN CORE**
  (the C.33 cite does not even enter this chain; it appears only on the cover
  consumption pin).
* Unconditional `DecidedSliceAt` at `n = 0, 1, 2, 3`, all routed THROUGH the DS socket
  (`vacuousPackage`); **`decidedSliceAt_one` is NEW** (nowhere previously landed).
* `DecidedSliceAt 4` from exactly `ClusterRecursionAt 4` — the quartic needs only its
  own recurrence.
* **The off-menu `0/1` law at EVERY degree, unconditional**
  (`decidedValueLaw_of_unwitnessed`) + the quantifier reduction
  (`decidedSliceAt_of_witnessed_valueLaws`) + menu finiteness of the witnessed labels
  (`witnessed_types_in_menu`, consuming `IFC6.exists_uniform_coveringMenu`): each
  degree's remaining obligation is FINITELY many witnessed labels.
* **The fixed-point bridge** (`decidedValueLaw_of_loopStep`): an exact loop-step
  recurrence (shift `m`, decay `q^{-(T_m−1)}`) with uniform rational base limit yields
  the uniform rational value law, via IFCG3's `decidedDensity_eq_of_step_eq`, with both
  denominator obligations.
* **Masses-sum-to-one gates**: the three assembled n = 2 laws and the five assembled
  n = 3 laws of IFCG13's weight calculus each sum to exactly `1`
  (`n2_masses_sum_to_one`, `n3_masses_sum_to_one` — hand-verified before Lean:
  the n = 3 numerator telescopes to `(q+1)(q⁴+q³+q²+q+1)`).

## Node-by-node, with the row gates QUOTED

### A0G-CL (§1) — carrier + step + bridge

Row demand: "clusterLaw_all by strong induction on m, **all recursive calls
syntactically < m, the one self-call only under FP**."

* `DecidedValueLaw n σ` — blueprint §5's display, byte-parallel to `DecidedSliceAt`'s
  body; **anti-drift pin** `example : DecidedSliceAt n ↔ ∀ σ, σ.degree = n →
  DecidedValueLaw n σ := Iff.rfl` (fails the build on any binder drift).
* `LoopStepLaw m σ` — the exact recurrence carrier: `bs M + (q^(T_m −1))⁻¹ ·
  decidedSeq O m σ M = decidedSeq O m σ (M + m)`, base limit ONE rational function
  uniformly over `O`.
* GATE "self-call only under FP": **met** — the only same-mass occurrence anywhere is
  `decidedSeq O m σ M` inside `LoopStepLaw`, consumed solely by
  `decidedValueLaw_of_loopStep` through `IFCG3.decidedDensity_eq_of_step_eq`.
* GATE "all recursive calls syntactically < m": **met** — the socket's smaller-law
  input is quantified `∀ k, k < m` (see DS), and the induction feeds it from `ih`
  applications at `k < n` only.
* Shape-template pins: `step_exponent_three : bigTLoop 3 − 1 = 5` (IFC7's hard-coded
  `q^{-5}`, shift 3 — the m = 3 instance is exactly IFC7's step shape) and
  `step_exponent_two : bigTLoop 2 − 1 = 2`; `step_exponent_pos` for every `m ≥ 2` via
  `T_m = κ_m + m`.
* `cover_for_recursion` — `IFCG12.finiteGenreCoverAt_strong_all` re-exported at the
  point of CL's consumption (EXHAUSTIVE ∧ DISJOINT ∧ DECREASING); the DECREASING clause
  is the `k < m` quantifier's polynomial-level justification.
* NAMING: `clusterLaw_all` is NOT declared — like `decidedSliceAt_all`, that name is
  reserved for the unconditional theorem; the CL row's provable content is the bridge +
  the DS induction.

### A0G-AS (§3) — off-menu 0/1, witnessed reduction, mass sums

Row demand: "convolve cluster laws over residue patterns, **masses sum to one
algebraically, off-menu 0/1**."

* GATE "off-menu 0/1": **met, at every degree, unconditional** —
  `decidedValueLaw_of_unwitnessed` (unwitnessed labels have empty decided sets at every
  level via `proj_surjective`; value `0/1`).  `Witnessed n σ` is the cross-`O` witness
  Prop.
* GATE "masses sum to one algebraically": **met at the landed masses** —
  `n2_masses_sum_to_one` (three laws) and `n3_masses_sum_to_one` (five laws), pure
  algebra on IFCG13's gate values (`field_simp; ring` after the eight gate rewrites).
  The general-`n` mass identity needs the general census (IFCG4 is `δ ≤ 4`-pinned) and
  is part of the socket's future discharge, honestly out of scope.
* The full residue-pattern CONVOLUTION at the `decidedSeq` level is exactly the FP0
  counting boundary (see below) — not fabricated here.  What the reduction does land:
  every degree's obligation collapses to finitely many witnessed labels
  (`witnessed_types_in_menu`).

### A0G-DS (§4) — the slice socket

Row demand: "`decidedSliceAt_of_clusterRecursion` with **the theorem body exposing
numerator/denominator/nonzero**."

* `ClusterRecursionAt m : Prop` — THE one socket: `(∀ k < m laws) → ∀ σ witnessed of
  degree m, LoopStepLaw m σ`.
* `decidedSliceAt_of_clusterRecursion : ∀ n, (∀ m, 4 ≤ m → m ≤ n → ClusterRecursionAt m)
  → DecidedSliceAt n` — **the strong induction** (`Nat.strong_induction_on`): degrees
  0–3 by the landed slices (IFCG0 zero / NEW one / I02_I03w two / IFC7 three); from 4
  on, off-menu → `0/1`, witnessed → socket (fed `ih`) → FP bridge.
* GATE "numerator/denominator/nonzero exposed": **met** — every produced law is a
  `DecidedValueLaw`: an explicit `(num, den)` pair with `den ≠ 0` AND
  `den.eval q ≠ 0` per `O`; the bridge constructs `(num·X^d, den·(X^d − 1))` and
  discharges both via `eval_pow_sub_one_ne` (`γ^d − 1 ≥ 2^d − 1 ≥ 1` at `γ ≥ 2`).

### A0G-ALL (§5) — the capstone

Row demand: "`decidedSliceAt_all` with **the exact `#check` gate, instantiations at
0,1,2,3,4, NO `0<n` guard**."

* `UniformClusterRecursion := ∀ m, 4 ≤ m → ClusterRecursionAt m`;
  `decidedSliceAt_all_of_recursion (h) : ∀ n : ℕ, DecidedSliceAt n` — the blueprint §2
  package display, conditional form.
* GATE "no `0<n` guard": **met** — bare `∀ n : ℕ` (the n = 0 leg is real:
  `IFCG0.decidedSliceAt_zero` fires inside the induction).
* GATE "#check": `#check @decidedSliceAt_all_of_recursion` prints
  `UniformClusterRecursion → ∀ (n : ℕ), DecidedSliceAt n`.
* GATE "instantiations 0,1,2,3,4": **met in the honest split** — `n = 0,1,2,3`
  UNCONDITIONAL `example`s routed through the DS socket with the vacuous package;
  `n = 4` as `example (h : ClusterRecursionAt 4) : DecidedSliceAt 4`.  An unconditional
  `n = 4` instantiation does not exist in the corpus (the quartic table is numerical
  evidence only, blueprint §8), so none is claimed.

## The honest boundary (why the unconditional prize did not land)

The socket `ClusterRecursionAt m` (= blueprint row **A0G-FP0** + the base-limit
rationality of CL0/CL1/AS0) is the assembly's exact missing input, per the consumed
verdicts themselves:

1. `verdict_A0GW.md` (IFCG13) "Recorded remainders" item 3: "The formal box-cardinality
   census tying `skeletonExp` to `MBoxN` level counts — **A0G-FP0's socket**."  The
   cover is a polynomial-realization statement; the weights are ℝ cone-sum identities;
   the level-`N` `decidedSeq` recurrence between them is unlanded.
2. Same verdict, item 1: the general mixed-denominator multiface cone closed form is
   open (single-face + all-`b=1` landed).
3. IFCG4's header: the general-`δ` irreducible census is "left open, honestly, for a
   future node" (`δ = 1,2,3,4` pinned) — needed by the residue-pattern convolution at
   general `n`.
4. Blueprint row A0G-CL1's "stage-field/base-change laws" (`q ↦ q^δ`, `f ↦ δf`):
   landed nowhere.

Discharging `ClusterRecursionAt` for all `m ≥ 4` = closing exactly these four items.
The socket is SHAPE-VALIDATED: at `m = 3` it is IFC7's landed step form (shift 3,
`q^{-5}`) upgraded from the five inequalities + squeeze to the blueprint-mandated exact
equality; at `m = 2` it is the quadratic rescale (`q^{-2}`).

## AxCheck (per-decl, as the fence demands)

* **Lean core ONLY** (`propext, Classical.choice, Quot.sound`): `step_exponent_pos`,
  `eval_pow_sub_one_ne`, `decidedValueLaw_of_loopStep`, `typeOf_monicPoly_one`,
  `decidedSliceAt_one`, `decidedValueLaw_of_unwitnessed`,
  `decidedSliceAt_of_witnessed_valueLaws`, `witnessed_types_in_menu`,
  `n2_masses_sum_to_one`, `n3_masses_sum_to_one`,
  ★ `decidedSliceAt_of_clusterRecursion`, ★ `decidedSliceAt_all_of_recursion`.
* **Lean core + exactly `Uniformity.Density.Tower.exists_dvDissection`** (the
  allowlisted C.33 cite): `cover_for_recursion` only — the cover consumption pin, NOT
  on the capstone chain.

## Build/repair log (for the record)

Skeleton compiled first-try (8 planned sorries).  Fills: FP bridge — one repair
(trailing `ring` after a closing `field_simp`); DS induction, n = 1 slice, off-menu,
menu finiteness, both mass sums — all first-try.  Total: one repair across seven holes.

## Candidate follow-ups for the orchestrator

1. **The FP0 discharge campaign** — the socket is now ONE named Prop with an exact
   statement; the discharge decomposes per the blueprint's own FP0/CL0/CL1/AS0 rows
   against `cover_for_recursion` + IFCG13's cone sums + IFCG3's `loopVecN_weight`.
2. PROJECT_STATE/frontier update: a0's remaining open surface is now exactly
   `UniformClusterRecursion` (masses ≥ 4), machine-checked to imply the full field.
3. `ClusterRecursionAt 4` alone yields the quartic slice — a natural first target with
   the §8 table as the numerical oracle.
