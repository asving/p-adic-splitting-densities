# verdict_CCT — UNIT CCT: the carrier→calculus transcription — `FGMNCalculus` from the completed packs; the depth-four calculus re-derived through the PACK route (2026-08-31)

**Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10CalcBridge.lean` (NEW, 566 lines, namespace
`Uniformity.Density.Tower.I10cct`) — 0 errors, 0 warnings, **0 `sorry`**; all **18**
printed footprints exactly `[propext, Classical.choice, Quot.sound]` (one is
propext-only).  Verified per-file (`timeout 580 ~/.elan/bin/lake env lean
Uniformity/ChapI/I10CalcBridge.lean`, exit 0, **8.8 s**), per-target (`lake build
Uniformity.ChapI.I10CalcBridge` — Build completed successfully, 8862 jobs), and the
chapter aggregator `Uniformity/ChapI.lean` exit 0 after the one standing import-line
edit.  Cite ledger: **empty** — Lean core over the landed corpus.  No instance
declared (`@[implicit_reducible]` defs only, the C130pk convention).  No git operations.

## FRONTIER CORRECTION (the charge's premise, adjudicated first)

The charge's ★ ("a SECOND unconditional calculus instance after C130sg's depth-one")
was already landed before this unit, at EVERY depth, via the μ-operator route:
C130sg depth-1 `(2,1,5)` · C132kp6b depth-2 `(2,1,21)` · C136d3 depth-3 `(2,1,85)` ·
C136e2 depth-4 `(1,1,171)` (`s2Mu5_calculus_nonempty`, named `C136r3.s2Mu5Calculus`) ·
C136c0 site `(2,1,85)`.  So the GENTOW2-consumer hypotheses at those parameters were
already dischargeable.  What was genuinely open — SPB's named successor charge, verbatim
"the carrier→CALCULUS transcription (producing `FGMNCalculus` operators + B-1 grades
from `RungPack` data)" — is the transcription MAP itself.  That is what this unit lands,
generic in `q` and the frame, plus the keystone fire as an independent second derivation
of the deepest instance.

## CHARGE 1 — the SCOPE adjudication (class field ⟷ pack export)

The pack chain supplies exactly the GRADED HALF of the A-C.11 class; the rest is
genuinely extra.  Full table in the file docstring; the summary:

| class field(s) | verdict |
|---|---|
| `ExactGrade`/`AboveGrade` | DERIVED — definitions from the one `nextValue := natToInt ∘ nextSupp` (U7 §3's one-field discipline) |
| `Rgr` | DERIVED — `(nextRead · ·).coeff 0` (CC-14's coefficient-zero projection at the pack residual) |
| `Rgr_zero_of_above` / `Rgr_add` / `Rgr_mul` / `Rgr_ne_zero` | FIRE from `nextRead_above` / `nextRead_add` / `nextSupp_mul`+`nextRead_mul` / `exact_ne` — the four graded laws are PACK THEOREMS |
| `PrevGrade` | LEG-CHOSEN — no pack law rides it (see below); semantic realization stays the instantiator's obligation (U14/A-C.13) |
| `keyAt`/`keyAt_one`/`keyAt_deg` | EXTRA — OPEN-DICT-1's `KeyChain` (a pack carries ONE key); consumed via `fgmnCalculusOf` + a `key_deg` fence tie |
| `Rres`/`Rres_mul`/`Rres_recipe`/`Rres_exists` | EXTRA — Def 3.15 / Cor 4.12(3) / eq. (11) / **Thm 5.7 = RUNG §7's adjudicated per-rung obligation** (the `RungLift` genre), one interface over |
| `KP` + 3 laws, `nuEquiv` + 1 law, `letterZ` + 1 law | EXTRA — §1.2 / Lem 5.2(2)+Cor 4.9 / Lem 1.8+Cor 1.10 / Prop 1.7(4) / Def 1.2+Prop 5.6 / §3.3 letters (OPEN-DICT-4 territory) |

Count: 4 of 10 data fields (+1 leg-chosen) and **4 of 13 laws** — the entire graded
layer — from the packs; the remainder (5 data fields, 9 laws, the chain tie) is the
named structure ★ `PackNormalizedLeg`, i.e. exactly what the OPEN-DICT items demand.

**The `Rgr_mul` finding (the table's one surprise):** the pack law is PREMISE-FREE —
the RUNG §1 coboundary twist absorbed the carry, so the pack residual is exactly
multiplicative and the restored `PrevGrade` premise is never consumed.  No tension with
A-C.13: the plain law is machine-refuted for the PUBLISHED-shape μ-layer residual
(`C130rp2.tooth_graded_mul_plain_shape_refuted`); the pack residual is a DIFFERENT
(raw-abscissa, twist-normalized) realization of the same class fields, on which the
plain law is a theorem.

## CHARGE 2 — what is built (all Lean-core)

Generic layer (uniform in `q` and the frame; any `W : DeepTower`, any
`R : RungPack O (W.fld r) u ℓ`):

* `natToInt : ℕ∞ → WithTop ℤ` + `natToInt_eq_natCast_iff`/`natCast_lt_natToInt_iff`
  (the grade-codomain bridge).
* ★ `nextSupp_of_deg_lt` — below the key-degree fence the iterated support is the pure
  `j = 0` line value `ℓ · supp` — and ★ `packRgr_ne_zero` — **the B-1 grade
  transcription**: the pack's `exact_ne` becomes the class-shape scalar nonvanishing
  through the development collapse.
* ★ `PackNormalizedLeg` (the honest remainder, field-per-OPEN-item, published loci on
  every docstring) → `packSourceData` (`nextValue := natToInt ∘ nextSupp`,
  `gradedResidual := nextRead` — R4K's landed dictionary shape) + grade bridges
  `packExact_iff`/`packAbove_iff` + ★ `packSourceLaws` (13 = 4 pack + 9 leg) →
  ★★ **`fgmnCalculusOf_packs : PackNormalizedLeg → FGMNCalculus W e' f' u'`** and
  `pack_calculus_nonempty`, routed through the landed CC-16 `fgmnCalculusOf` (no new
  route into the class); 8 rfl anti-drift teeth (the transcribed `Rgr` IS
  `fun β g => (nextRead R.C R.P β g).coeff 0`, etc.).

Keystone fire (§4):

* ★ `s2_packExact_iff` — pack exact grade = landed μ₅ exact grade (R4K's
  `s2_nextSupp3_eq_dv4Supp` + `S2Mu5ExactGrade_iff_dv4Supp`); `s2Rung3Pack_key`/
  `s2_key_deg` (the fence tie: `keyAt 4 = g16` = the pack key, rfl).
* ★ `s2PackLegFour` — the keystone leg, EVERY field landed content (C136e2's μ₅ bank,
  byte-parallel with `s2SourceDataFour`/`s2SourceLawsFour`'s normalized rows;
  `PrevGrade := S2Mu5PrevGrade`, the landed all-grades predicate; the recipe clause =
  D4-17's `s2Mu5_normalized_recipe_field` read through the two dictionaries).
* ★★ **`s2PackCalculusFour : FGMNCalculus (s2DepthFour) 1 1 171`** +
  `s2_pack_calculus_discharge` — the SAME statement as C136e2's landed
  `s2Mu5_calculus_nonempty`, now derived through the PACK route: an independent second
  derivation of the deep-tower calculus discharge (decorrelation value: the two routes
  share the tower and the normalized bank but derive the graded half from disjoint
  mechanisms — μ-layer tables vs. the abstract convolution carrier).
* ★ `s2PackCalculusFour_residual_agree` — the two routes carry the SAME polynomial
  graded residual on the lawful domain (R4K's dictionary in calculus coordinates); rfl
  teeth pin `Rgr`/`keyAt`/`Rres`/`PrevGrade`.
* ★ **Consumer fire** (machine-checked `example`): C136d3's chain-level depth-four
  GENTOW normalizer read `s2Mu5_chainNormBelow_four_one_seventy_one_chain` fires at the
  pack calculus with the `hkey` premise closed by `rfl` —
  `(s2PackCalculusFour).chainNormBelow 4 171 = s2Mu5Lambda`.

**Consumers, exactly** (grep census): at `(s2DepthFour, 1, 1, 171)` the two Λ-normalizer
consumers — C136t:397 (pointwise-key premises) and C136d3:1841 (chain-level, FIRED
in-file).  The parameter-generic consumers (C107gt5's generic-`(W, r)` Props, C107ac14's
`thetaRatio` layer) accept any instance including this one at their own bindings.  The
depth-1/2/3 and site consumers (C132rp9, C132fd1, C136c0) ride the landed μ-route
instances at their parameters — not re-derived here (the pack route reaches them the
same way given the corresponding legs; only depth-four is landed in this unit).

## Honest remainder (what stays open)

* `PackNormalizedLeg` is the remainder, verbatim: at any NON-keystone tower the
  normalized layer (Def 3.15 / Thm 5.7 / KP / letters) and the `KeyChain` must be
  supplied — the OPEN-DICT-1/3/4 + Thm 5.7 frontier, unchanged in content, now with a
  single named Lean carrier.  The general-`q` payoff: RUNG §3's `rung2Pack` exists at
  EVERY level datum over a finite residue field, so the graded half of a general-tower
  calculus is now free — the open mathematics is concentrated in the leg.
* **C.92 stands**: no theorem from a bare `DeepTower`; the transcription consumes a
  pack + the leg.  No instance declared anywhere.
* **Faithfulness**: the transcribed `gradedResidual` is the raw-abscissa
  twist-normalized read — at ℓ = 1 rungs it IS the landed μ₅ operator (agreement
  theorem); at ramified rungs it is the ℓ-dilated read (W3P's `X ↦ X²`), eval-1-equal
  but not polynomial-equal to the published shape.  Identification of ANY landed
  instance's operators with the published `F_(r+1)` objects remains OPEN-DICT-3's
  standing open — unchanged.
* No μ₆/depth-five object touched (per [G5F]: the `(1,1,171)` triple is terminal; the
  rung-4 pack's up-level read would be μ₆-genre data with no tower or consumer to bind
  to — deliberately not transcribed).

## New statements flagged for the standing review

`natToInt` (+2 iffs), `nextSupp_of_deg_lt`, `packRgr_ne_zero`, `PackNormalizedLeg`
(structure — the one genuinely new interface), `packSourceData`, `packExact_iff`,
`packAbove_iff`, `packSourceLaws`, `fgmnCalculusOf_packs`, `pack_calculus_nonempty`,
`s2Rung3Pack_key`, `s2_key_deg`, `s2_packExact_iff`, `s2PackLegFour`,
`s2PackCalculusFour`, `s2_pack_calculus_discharge`, 4 named rfl teeth +
`s2PackCalculusFour_residual_agree` — all supplier-side; `FGMNCalculus`,
`FGMNSourceData/Laws`, `fgmnCalculusOf` consumed verbatim on conclusion sides; nothing
weakened.  Local twins flagged for the standing dedup: `wcoeff_of_guard` (8th corpus
repetition), `dev_zero_of_deg_lt`/`dev_pos_of_deg_lt` (the `modByMonic_eq_self` collapse,
twin of RUNG's `dev_key_mul_one` step).

## Repair log (2 real rounds + one NEW GOTCHA generalizing SPB's)

1. Mechanical: `x.map` on `ℕ∞` resolves to `ENat.map` (use explicit `WithTop.map`);
   `WithTop.mul_top` needs the RUNG-style typed `have`; `Int.natCast_lt` does not exist
   (`Nat.cast_lt` + `ENat.coe_lt_coe.symm`); mixed-coercion iffs on `ℕ∞` resist
   `exact_mod_cast` (recTopCoe's `WithTop.coe` vs `Nat.cast`) — closed with
   `ENat.coe_inj.symm`/`ENat.coe_lt_coe.symm` after `simp only` collapses the ℤ side.
2. **THE `show`-METAVARIABLE-MIXING GOTCHA (new; the elaboration-side sibling of SPB's
   meta-core blowup).**  When a structure field's expected type is typed at
   `(s2DepthFour).fld 4` but the proof's lemma bank at the defeq-unfolded
   `(s2DepthTwo).fld 2`, a `show` restating the goal at the fld2 typing MIXES the two:
   `show`/`change` elaborates its statement WITH the goal as expected type, so unpinned
   ambient atoms (`Polynomial.X`, the `-`/`*` instances) unify against the fld4 goal
   while lemma-pinned atoms stay fld2 — surfacing as bogus `HMul fld2[X] fld4[X] fld4[X]`
   / `HSub` synthesis failures.  Partial pinning is whack-a-mole.  **Fix: never `show`
   across a structure-literal defeq boundary — assemble the identity as a `have` chain
   entirely at the source typing (every rewrite then fires syntactically) and hand it
   over with a single `exact`,** whose one defeq check is exactly the boundary.  Same
   family: `rw` across the boundary fails with "pattern not found" even when the display
   matches — the type args differ.
3. Argument-order lesson (unifier-directed): declare the `W`-pinning argument
   (`K : KeyChain W`) BEFORE the pack in every signature, so application sites pin the
   tower from the chain and the pack lands by the field defeq — the reverse order infers
   `W := s2DepthTwo` from the pack and rejects the depth-four chain.

## Verification, footprint

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10CalcBridge.lean`
  throughout (5 passes); FINAL: exit 0, 0 errors, 0 warnings, real-`sorry` count 0
  (one docstring word); AxChk **18/18** Lean-core; `lake build
  Uniformity.ChapI.I10CalcBridge` — Build completed successfully (8862 jobs);
  aggregator `Uniformity/ChapI.lean` exit 0 after the one import line; final timed run
  8.8 s at the corpus-standard 800000 heartbeats (keystone records at 1600000, matching
  C136e2's own).
* Footprint: `leanfinal/Uniformity/ChapI/I10CalcBridge.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed file
  edited; no git operations.
