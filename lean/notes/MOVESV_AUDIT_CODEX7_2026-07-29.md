# MovesV round-7 Codex verdict (2026-07-29): REJECT 8/2 — 12/20 rows PASS incl. all four prior rulings except C4/C6; residues: Tgam only <= chainCount (not the direct count); the h1-refinement contradicts the PUnit-carrier RefEvents cover law; entInst untied to lands_sel; markReading law absent from the conclusion surface; stepKey transport direction; the prose-as-def closure class (ReadFits etc., jcellPG); V7-9 type mismatch

I’ll audit REV 7 against the frozen §V-TABLES text and the post-ratification MovesS interfaces, then run a separate adversarial sweep for new defects. I’ll treat each §6.6 row as independently needing a textual/type-level witness; no repairs will be proposed or applied.

The core adversarial checks are complete. The most consequential failures are not cosmetic: the proposed direct `Tgam` is only support-equivalent to realization, the h₁-refinement conflicts with the stated `RefEvents.tevt_cover` on the actual PUnit-history toy, and the entrance census is still not tied to a selection-reading cut. HMC itself is not accidentally proved, but several claimed repairs do not hold.

Verdict: **REJECT (8/2)** — 8 critical defects, 2 material gaps.

§6.6 has 20 physical rows covering 21 finding labels because G1 appears both in the combined C4+G1 row and separately.

## Critical findings

### N1 — `Tgam` is not the note’s direct chain count

REV 7 defines:

> `Tgam ... := (TE.tinst γ x h (TE.tmplLvl γ)).card`

But the only quantitative connection to actual assignment chains is:

> `marks_chains : ... Tgam ... ≤ chainCount S γ x h`

This does not make the census cardinality equal to

> “`#{fresh-assignment chains from x realizing (γ,h)}`”

as §V-TABLES defines \(T_\gamma\). The other ties, `real_marks` and `marks_realize`, establish only positivity/support equivalence. An instance with two realizing chains but a singleton `tinst` satisfies all three mark facts and both `XHDd` laws.

Therefore:

- `XHDd` is indeed keyed two-sidedly to `0 < Tgam`.
- HMC remains non-definitional.
- But `Tgam` itself is not the note’s \(T_\gamma\) verbatim.

Disposition C6 fails.

### N2 — V4-11’s claimed h₁-refinement contradicts `RefEvents.tevt_cover`

The proposed separation says:

> “in the h₁ = 0 refined state the tail domain excludes h₂ = 0”

But the cited toy inherits V1-8a’s pool histories:

> `Hist q₀ α := PUnit`

and `RefEvents` requires, separately for every refined source state and history:

> `TE.tevt γ (R.histOf α' x') h N = union of the corresponding TE'.tevt ...`

The coarse one-step tail at \(h_2=0\) is realized by `tevt_last_iff`. Since both refined flag histories project to the same PUnit coarse history, `tevt_cover` forces some refined tail event at \(h_2=0\) to remain nonempty in the \(h_1=0\) state. Its refined `XHDd` must then include \(h_2=0\), contradicting the proposed excluded tail domain.

Equivalently, if the refined composite remains empty at \((0,0)\), its domain omits that point while the refined first-step and tail domains both contain their zero points, so HMC still fails.

Thus the recorded construction does not prove:

> `¬HMC ∧ HMCAug`

Every operative stale `¬HMCAug` assertion was removed, and V4-13 is separately valid in shape, but the advertised separation witness is incorrect. Disposition C4 fails.

### N3 — selection-ignoring measured entrances can still pass

`EntranceCut` now has the useful law:

> `lands_sel : ∀ i, lands i → SelMatches ε i`

so `iotaCount` is selection-sensitive.

However, `CtsMeasured.entEvt` and `entInst` are independent free fields. Their new law is only:

> sibling labels with different `selRec` have disjoint `entInst` Finsets.

No typed map or equality identifies an `entInst` member with a prefix accepted by a `lands_sel`-bounded `EntranceCut`. A selection-ignoring implementation can assign arbitrary disjoint tags to different `selRec` labels, satisfy `ent_sel` and `ent_card`, and still ignore the actual selected continuation.

The prose claim that V3-6/V7-4b supplies this identification is not represented by a displayed field or definition.

Disposition C1 fails.

### N4 — the marked reading repair is not present in the recorded conclusion

V4-10 promises:

> “`markReading` — THE READING LAW”

but `Meas_Stmt` records only:

> `p ≠ p' → Disjoint (mEvt L p N) (mEvt L p' N)`

plus `EqualProjInstance L`.

It contains no `reading` function or law connecting a marked point to its `(m,o,β,height-class)` reading. `MStep` and `mEvt` themselves appear only through the name-to-home prose table. Consequently the claimed derivation of `MarkDisj`/`MarkDisjT` from the reading law is not auditable from the displayed capstone statement.

The old hypothesis fields are successfully removed, but the replacement typed law is missing from the actual conclusion surface. Disposition C8 fails.

### N5 — displayed `stepKey` has a wrong dependent transport

For the inverse datum, the blueprint has:

> `d.2 : W.toStepCells.symm d.src = αc`

and `x : S.Hist q₀ αc`.

It then calls:

> `W.cellOfA d.1 (d.2 ▸ x) ...`

To obtain a history at `W.toStepCells.symm d.src`, the necessary transport is along `d.2.symm`, not `d.2`. As written, this branch is ill-typed. The terminal branch repeats the same direction error.

Moreover, `castAssignKey` and `castAssignKeyT`, on which the definition depends, are only described as wrappers; their bodies are not displayed.

Disposition C10 fails.

### N6 — the Option/dite Defs layer remains non-closed

The supposed closed definitions consume names that are only described in comments:

- `ReadFits`
- `ShapeWFOf`
- `EntTiesAt`
- `emptyPrefix`
- `castAssignKey`
- `castAssignKeyT`

For example:

> “`ReadFits n P s hslot uslot R` is the Defs-local Prop pinning … each clause one equation, displayed at the ReadFits decl”

but no such declaration is displayed. Likewise:

> “`ShapeWFOf / EntTiesAt: Defs-local abbreviations`”

is prose rather than a Lean definition.

The forward references to V3 theorems were removed conceptually, but the replacement Defs-layer objects are still placeholders. Disposition C11 fails.

### N7 — the per-cell J interface is described but not actually defined

The repair relies on:

> “`jcellPG c (§2.H: countT := hcell.P …, countS := 1, geom := …)`”

Yet neither `jcellPG` nor the referenced `μcellVal` is given as a closed Lean definition; `μcellVal` appears only as commented pseudocode. Consequently the promised constructions of:

- `jPCell`
- `jcell_ok`
- `jcell_interp`
- `jcell_sum`

cannot be checked against the built `RatBurdens` type.

The intended carrier is correctly `M.Cell`, and the proposed symbolic sum has the right conceptual shape, but the claimed closed supplier is absent. Disposition C15 fails.

### N8 — V7-9 cannot derive the built `PolyGeomLaws.tCount`

The unit says:

> “`tCount e τ o := the table count (C.T … d.tix).eval`”

but built MovesS requires:

> `tCount : ... → ℚ → ℕ`

A rational polynomial evaluation is not definitionally a natural number. At pools, `ValA.tbl_count` provides a natural-cast equality only when a listed `mdom` component supplies a base point. If that list is empty, no `tbl_count` premise constrains the own-key value. Outside `M.Pools`, no valuation law applies at all.

Thus V7-9 lacks:

- a total ℕ-valued definition for every rational `q₀`;
- a proof that the polynomial evaluation is a natural at every pool, including empty-domain outcomes;
- an explicit construction at the bare `(e,τ,o)` index;
- an explicit supply of the newer `tcount_deg` and `scount_deg` fields.

Disposition F-GAP-2 fails.

## Material gaps

### M1 — `RealizedBranching` lacks its promised finite-census bridge

The carrier is plausibly the correct MovesD predicate:

> `EligibleImage p w ν.g ν.μ (RanchImage ν)`

but the blueprint merely asserts that E6/E7 give:

> `RealizedBranching → IsBranchSlot`

No unit or displayed theorem supplies that implication, nor is finiteness of the polynomial subtype recorded where `Nat.card` is used. This is not enough to audit the claimed “≥2 realized eligibles” interpretation.

Disposition C2 is only partial.

### M2 — `XhdS_Stmt` is written out, but not verbatim

The terminal `GcellT` triple is no longer replaced by prose, which repairs the principal C12 defect. However, its `HasSum` clauses take an arbitrary:

> `(hok : F.GcellT ... ∈ OKat q₀)`

before the pool premise, whereas the original structure obtains that proof specifically from `GcellT_ok ... hq`. The forms are propositionally close but not verbatim as claimed.

Disposition C12 is substantively repaired but its “verbatim” record is overstated.

## §6.6 row census

| Row | Result |
|---|---|
| C4 + G1 — separation / V4-13 | **FAIL N2** for separation; V4-13 itself is correctly allocated |
| C6 — direct `Tgam` | **FAIL N1** |
| C8 — derived marked disjointness | **FAIL N4** |
| C3 — designated-member `tcellM_sel` | PASS |
| C1 — selection load-bearing | **FAIL N3** |
| C2 — `RealizedBranching` | **PARTIAL M1** |
| C5 — HMC in `SolveCond_Stmt` | PASS |
| C7 — `XHDsEnt` as V3-8a premise | PASS |
| C9 — `L.RB`/`L.hK` scoping | PASS |
| C10 — closed cell/event key defs | **FAIL N5** |
| C11 — no forward references | **FAIL N6** |
| C12 — explicit `GcellT` triple | **PARTIAL M2** |
| C13 — `legs_read` row | PASS |
| C14 — V7-8 at built `W17ii` type | PASS as a scheduled, explicitly sorry-gated duty |
| C15 — built per-cell J interface | **FAIL N7** |
| G1 — standalone V4-13 unit | PASS |
| G2 — XRBPackage co-build dependency | PASS as an explicitly recorded dependency |
| F-GAP-2 — `PolyGeomLaws` | **FAIL N8** |
| F-GAP-3 — refreshed citations | PASS against the supplied excerpts |
| F-GAP-4 — Option-indexed branching reads | PASS |

## HMC status

HMC remains **OPEN and unclosed**:

- `XHDd` is no longer keyed to recursive `chainCount`.
- No composite `tinst` recursion is present.
- `marks_chains` is one-way only.
- `COMP-Σ`, `CompAgg`, `SolveCond_Stmt`, and `LedgerIV.hmc` retain explicit HMC premises.
- `hmcaug_of_hmc` proves only `HMC → HMCAug`, not HMC.

The failed V4-11 refinement removes the claimed false-HMC/HMCAug separation witness, but it does not accidentally prove HMC.

**Final: REJECT (8/2).**