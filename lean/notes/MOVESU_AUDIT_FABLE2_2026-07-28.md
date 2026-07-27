# MovesU Lean blueprint REV 4 — fresh-instance CONFIRMATION audit (Fable #2)

- **Date**: 2026-07-28
- **Auditor**: fresh Fable instance #2 (no prior context; parallel to the Codex FINAL
  audit on the identical rev-4 text)
- **Scope**: rev 4 confirmation — verify the F3-C1/C2/G1/G2/G3/G4 repairs are genuine,
  verify the spine is unchanged from rev 3, then a full fresh sweep. Settled
  architecture (concrete Box over ZMod (p^N); the two-clause U10 conclusion with the
  U11 second squeeze; D9's declared non-vacuity boundary) audited for execution only.
- **Charge**: `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` below its `---`; corpus = MovesU
  (`MOVESU_LEAN_BLUEPRINT_2026-07-28.md`, rev 4, 989 lines, read in full)
- **Ground truth**: `MOVES_2026-07-24.md` lines 12879–13630 (§U-SQUEEZE through STATUS,
  stopping before the PASS RECORD heading), read in full
- **Method note**: rev 3 → rev 4 additionally verified MECHANICALLY
  (`git diff 4cfeb20 93bafb6` on the blueprint file, every hunk reviewed)

---

## Part I — the six charge-specified pressure points, adjudicated first

**(1) `KsubM1C1` binds same-size CONTINUATIONS only — CONFIRMED FIXED (F3-C1).**
Spec (§2): `def KsubM1C1 (M : MenuData) : Prop := ∀ s, ∀ o ∈ M.menu s,
o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1`.
Note display (13116–13118): "equal-e continuation rides EXCLUSIVELY in K_e's
(c = 1, m = 1) rows ((K-SUB)'s (m, c) classification … the same-size single-child
direction)". The `o.c ≠ 0` guard makes the Prop exactly the exclusivity direction:
every same-size CONTINUING outcome is a (1,1) row. Checked against the charge's test
case: a faithful catalogue with same-size c = 0 halts (the b_e^{term,fin} leaves)
satisfies it — the inner implication is vacuous at c = 0, so halts are exempt. Checked
the residual mixed case (m ≥ 2 with a same-size member): unrealizable in a faithful
catalogue — (K-TRI) (13119–13121) puts every continuing split leg at e_j < e, and an
m ≥ 2 outcome cannot contain a degree-e member at all (member degrees of a genuine
split sum to ≤ e with every part ≥ 1), so `sameSize`'s per-outcome granularity is
adequate. The `MenuEntry.sameSize` gloss ("whether it stays at equal block size") is
mildly ambiguous for outcomes that cannot occur; not a finding.

**(2) `ctsmSyntax` + `cl13` carry CL-13 in full — CONFIRMED FIXED (F3-C2).**
Spec (§2b): `ctsmSyntax : Prop` slot reinstated, docstring quoting the full CTS-M(i)
content; `cl13 : K.ctsmSyntax ∧ MenuWF M`. Note CL-13 (13315–13318): "the ONE fixed
finite p-independent state set with DISPLAYED cell predicates and globally compatible
target-cell maps; without it no path product or kernel index type-checks". The full
content rides the slot in the SAME accepted pattern as every other open kernel
(escapeE0, trackCount, …): opaque named Prop + docstring + D9/G4's True-filling-is-a-
fidelity-violation rule. That is what rev-3 CRITICAL 2 demanded — the critical was the
slot's DELETION leaving only the strictly-weaker face, not the bare-slot pattern
itself. The face `MenuWF` is now honestly labeled ("PER-ENTRY TARGET TOTALITY … this
is NOT the global compatibility"), and "replacing NOTHING" is stated at the slot. With
`M` p-uniform (point 3), a faithful filling of the slot can now literally refer to
"the ONE fixed p-independent state set" — the expressibility defect is gone. No tag
dropped: cl13 asserts BOTH conjuncts (SQ.4's acceptance-record rule, 13163–13166,
satisfied).

**(3) `M`/`K` in the p-UNIFORM layer — CONFIRMED (F3-C2/G4).** The theoremU signature
(§3 U10): `theorem theoremU (n : ℕ) (hn : 2 ≤ n) (S : SolveData n) (M : MenuData)
(K : KernelStatements) (inst : ∀ p : ℕ, p.Prime → UInstance n S M K p) : …` — one `M`
and one `K` bound BEFORE the ∀ p (both in `inst` and in the conclusion's ∀ p), the
same ∃/bind-before-∀ discipline as `S`. `UInstance` (§2b) correspondingly drops its
`M`/`K` fields and takes them as parameters; `CapstoneLedger n p X F S D M K`
references the shared pack at every prime. p-independence of the state set and the
slots' p-uniform referents (TRACK-COUNT "uniformly in p, N, and depth", 12969–12977)
are now expressible. Verified no residual `.M`/`.K` access anywhere in §3.

**(4) Menu pins — CONFIRMED FIXED (F3-G1).** `menuCount : State → ℕ` +
`menu_card : ∀ s, (menu s).card = menuCount s` + `menu_not_all_empty : ∃ s,
menuCount s ≠ 0`. The all-∅ dodge is dead: all menus empty forces menuCount ≡ 0 via
`menu_card`, contradicting `menu_not_all_empty`; conversely a fabricated nonzero
`menuCount` at an empty menu falsifies `menu_card`. A single state with an empty menu
stays allowed — the halt/(BDY) convention, correctly preserved. The VALUES' fidelity
to the [2a]/[1v] catalogue is the declared G8 owner-data boundary — the same
ruling-(C) pattern the settled architecture already accepts for `blockDim` etc. Meets
the rev-3 GAP-1 repair standard exactly (a `menuCount`-style pin was the prescribed
shape).

**(5) Dropped `cellCount_pos`/`shapeCount_pos` — CONFIRMED CORRECT (F3-G3).** I
re-checked the (r2) entry-list display myself (13185–13197): the note determines the
MEMBERSHIP of E(e) — all seven families: K entries, b_e BOTH components, per-cell J
(CL-18), ι_e, W_Ŝ, every β leg "at every pool of Q(p)" — and NO positivity for
branching-cell or shape counts, per block or globally. `RegData` keeps exactly the
note-supported content: index types with cardinality EQUATIONS (`JIdx_card`,
`WIdx_card`, `legIdx_card`), `entryList` the defined seven-family union with β images
over EVERY δ ∈ depthSet. The retained positivity pins are only `instBiNe`/
`blockDim_pos` (every block's table has rows — the anti-det = 1 pin, audited safe at
rev 3) and `pool_eq`/`one_mem_depthSet` (p ∈ Q(p)). (K-TRI)'s minimal blocks
("every b_e^split leg has e_j < e") make per-block cell/leg positivity plausibly FALSE
on the real tables, so the drop removes a genuine truthful-uninstantiability risk; the
owed owner-table confirmation is recorded at G8 and §6. Correct in both directions.

**(6) Spine unchanged from rev 3 — CONFIRMED MECHANICALLY, with one wording remark.**
`git diff 4cfeb20 93bafb6`: the only §2/§2b/§3 changes are the menu layer (MenuData/
KsubM1C1/MenuWF/ctsmSyntax/cl13), the two dropped `_pos` fields, the UInstance/
theoremU re-parameterization, and prose (§1 D5/D7, §4 G1/G4/G8, §6, §7). U0, U0b,
U1–U9, U11: byte-identical statements. U10's CONCLUSION is byte-identical; its
PARAMETER PREFIX changed (gains `M`, `K`; `UInstance n S p` → `UInstance n S M K p`)
— which is precisely the F3-C2/G4 repair the rev-3 audit prescribed ("bind `M` before
∀ p (with S)"). See the remark below on the header's "spine untouched" phrasing.

## Part II — F3 repair-execution table

| repair | verdict |
|---|---|
| F3-C1 (KsubM1C1 over-bound halts) | GENUINE: `o.c ≠ 0` guard; faithful catalogue with same-size halts now satisfies it; docstring accurate |
| F3-C2 (cl13 weakened / tag dropped) | GENUINE: `ctsmSyntax` slot reinstated with full CL-13 content in its docstring; `cl13 : K.ctsmSyntax ∧ MenuWF M`; face relabeled honestly; `M` p-uniform makes p-independence expressible |
| F3-G1 (menu emptiness dodge) | GENUINE: `menuCount` + `menu_card` + `menu_not_all_empty`; halt convention preserved |
| F3-G2 (§7 misstatements) | GENUINE: R2-1 row now says NON-VACUOUS-but-satisfiable-by-unfaithful (matching D9); R2-3 row corrected (no `legCount_pos`; the two `_pos` drops recorded); G1 flag reworded |
| F3-G3 (`_pos` over-strong) | GENUINE: both dropped, equation pins stay, `instBiNe`/`blockDim_pos` kept, owner-table confirmation owed at G8/§6 |
| F3-G4 (per-prime K) | GENUINE: `K` (with `M`) now theoremU parameters before ∀ p; one pack, audited once |

## Part III — fresh sweep (whole blueprint vs the note, all five charge checks)

Checked and CLEAN (selection; the rev-3 positives were re-spot-checked, not assumed):

- **(BOX-N)/U1** = the 13042 display exactly (sides swapped); tag-free as a
  partition-by-`Option`-value count identity; edge case N = 0 fine (`Box p n 0` is a
  point, both sides 1).
- **U2/U3/U4 (SQ.2 route)**: Tonelli retyped to existence + domination only (rev-2
  clause, 13085–13092); U3 re-exposes `finiteness_stack` as an identity (not ≤);
  U4 under full ledger + `RegP` + `p.Prime` with the explicit `0 ≤ evalℝ` conjunct
  (RS.3's clause, 13100–13102) — the ℝ≥0∞ → ℝ transfer is sound.
- **U5 (SQ.3)**: re-derived by hand from 13127–13129 — correct; `1 < p` declared
  scaffolding; the note's display asserted only through U6/U10 at primes (G6 holds).
- **U6 (U-n)**: two-sided under `hreg` on BOTH legs — "the qualifier binds the
  DISPLAYED BOUNDS themselves" (13136–13139); lower leg's extra RS.4 inherited set =
  `rs4_eval` with the verbatim-tag docstring (13129–13132).
- **U7/U10/U11**: squeeze and second squeeze both re-verified (decided ≤ trueCount ≤
  decided + undec from `VPSound` + single-valuedness — correct); ∃-R-before-∀-p
  intact, checksum conjunct OUTSIDE ∀ p ("identically in q"); clause (iii) env → 0
  emitted under RegP, matching the theorem sentence's scope; D8's no-claim/
  removable-zero semantics = the restricted quantifier, exact (13204–13211).
- **(REG-p)/U8**: (r1) full determinant incl. junk blocks; (r2) over the DEFINED
  seven-family union at every q₀ ∈ Q(p) with β legs at every δ (13181–13197 covered in
  full); the ruling-(D) evaluability clause = "UNDER (REG-p), the literal evaluation
  R_σ(p) … is DEFINED" (13199–13201); separateness from E0/ACT stated both ways
  (rev-5/rev-6 clauses, 13150–13155, 13564) and guarded at G5.
- **Ledger completeness**: CL-1…CL-19 all asserted; CL-5 = nine slots; CL-8 = six with
  rel2c correctly absent ((c) lives at CL-10's (SIB), 13245–13247); CL-12 correctly
  absent ("NOTHING at CL-12 is open", 13290–13306) with the O3 residue carried as
  `o3_teichmuller` (the SQ.4 display duty, 13212–13221); (ns-null) correctly needs no
  slot (PROVED/CLOSED at REV 15, 13270–13272); CL-11 = `noEqualEFeedback` slot
  (+ DEG-CONS) ∧ typed `KsubM1C1 M`.
- **Non-vacuity**: every hypothesis structure has an inhabitation story (U0b
  nonemptiness; `RegData`'s pinned nonempty pool/blocks/bidx; `MenuData`'s
  not-all-empty; `FiberSeries`' tie via `finiteness_stack` — empty `Tree σ` forces
  decided_σ ≡ 0, not smuggled); no truthful-uninstantiability introduced (the F3-G3
  drop REMOVED the one identified risk). The degenerate-instance boundary is D9's
  settled, honestly-declared one (G1 now worded correctly).
- **Defs soundness**: no definition decides an open question; `VPSound`/`DefinedAt`/
  `entryList`/`evalℝ` match their displays; three-file order coherent; U9's (L-meas)
  equivalence re-derived — one-directional IMPLIED-BY preserved (13518–13528), gate
  SQUEEZE-n3 correctly NOT a Lean unit (census artifact).
- **Decomposition/counts**: 13 units, one display each; §6's 4 + 2 + 7 and 5 easy /
  8 medium tallies check; the 26-finding table = 13 + 7 + 6.

## Part IV — findings

**None counted.** (0 critical / 0 gap.)

**Uncounted remark (record wording, repair suggested at next touch).** The rev-4
header's closing phrase "No spine unit touched" (and the title's "spine untouched")
is loose: U10 — a spine unit, the capstone — had its parameter prefix changed by the
F3-C2/G4 repair (M/K bound before ∀ p; `UInstance` re-parameterized), which changes
the theorem's Lean-visible statement (for the better, exactly as the rev-3 audit
prescribed). The change is disclosed three times in the same document (the header's
own preceding clause, U10's inline comment, the F3-G4 row, §6), so no reader of the
spec can be misled about the artifact itself — hence not a counted finding under the
charge's taxonomy (which classifies unit-spec faithfulness, not delta summaries). An
accurate phrasing would be "no spine unit's conclusion touched; U10's hypothesis
prefix re-bound per F3-C2/G4". Similarly trivial: §6 records the G8 owner-table
confirmation as owed unconditionally while G8 scopes it "if any positivity is ever
wanted" — harmless, §6's stronger reading governs.

## Counts and verdict

CRITICAL: 0. GAP: 0.

All six rev-3 findings verified genuinely repaired; the spine re-verified (statements
byte-identical except U10's prescribed hypothesis re-binding); the fresh sweep found
no new faithfulness, vacuity, hypothesis-fidelity, Defs, or decomposition defect.

**VERDICT: ACCEPT**

(Standing conditions carried, not waived by this verdict: acceptance is of the
BLUEPRINT as a faithful conditional formalization plan — Theorem U stays conditional
on CL-1…CL-19 with (REG-p) the one explicit hypothesis; the D9/G8 instantiation-
fidelity boundary and the owed owner-table confirmation on zero-cell/zero-shape
blocks bind the E-phase; per the campaign rule, dual acceptance requires the parallel
Codex pass to concur.)
