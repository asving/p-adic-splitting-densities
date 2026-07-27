# MovesU Lean blueprint REV 3 — fresh-instance semantic audit (Fable)

- **Date**: 2026-07-28 (audit executed on the rev-3 text of
  `MOVESU_LEAN_BLUEPRINT_2026-07-28.md`, 927 lines, read in full)
- **Auditor**: fresh Fable instance (no prior context; charge =
  `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` below its `---`, corpus = MovesU,
  note = §U-SQUEEZE)
- **Ground truth**: `MOVES_2026-07-24.md` lines 12879–13630 (§U-SQUEEZE through the
  STATUS paragraph, stopping before the PASS RECORD heading), read in full
- **Scope**: rev 3 audit — verify the R2-1…R2-7 repairs are genuine AND fresh sweep;
  settled design rulings (concrete Box; clause (i)/(ii) split; ℤ_p-Haar = HC-2's bridge)
  audited for execution only, not re-litigated

---

## Part I — the five pressure points, adjudicated first

**(1) Degenerate instance vs the full Theorem U statement.** I constructed the
adversarial instance explicitly: `canonical N f = some σ₀` (constant), `trueType N f =
some σ₀` (constant), `Tree σ₀ = Unit` with `mass = 1, thr = 0`, `Tree τ = Empty`
elsewhere, `S.R σ₀ = 1`/`S.R τ = 0`, all `KernelStatements` slots `True`, `MenuData`
with all menus `∅`, `RegData` with `Block = Unit`, `blockDim = 1`, `K = 0`,
`act := literal eval`. This satisfies **every** ledger field (`finiteness_stack`,
`solve_stack`, `rs4_*`, `cl4_env_tendsto`, a non-vacuous `VPSound`), makes `RegP` TRUE,
and the full U10 conclusion — clauses (i), (ii), (iii) — holds. **Disposition: NOT a
finding under the settled ruling (B).** Rev 3's D9 no longer claims otherwise: it
declares exactly this boundary (clause (i) true-but-about-an-unfaithful-classifier;
clause (ii)'s residue in `trueType`/VP-SOUND fidelity + True-filled slots, owner-audited
at instantiation, the MovesC `JetSetup` precedent), and the refuted "fake instance is
dead" claim is withdrawn in the text. Residual overclaim-shorthand in §7's R2-1 row
("makes clause (i) degenerate-proof") — noted under GAP 2.

**(2) RegP cardinality pins.** Confirmed present and load-bearing: `instBiNe` +
`blockDim_pos` + `bidx_card` kill the empty-matrix `det = 1` dodge; `cellCount_pos`/
`JIdx_card`, `shapeCount_pos`/`WIdx_card` force (r2) to range over inhabited J/W
families; `pool_eq` + `one_mem_depthSet` force `p ∈ Pool`. Two caveats: `legCount` has
NO positivity field though §7 claims "all `_pos`" (GAP 2), and the positivity pins
themselves are note-unsupported strengthenings whose truth on the real tables is
unverified (GAP 3).

**(3) U11's second squeeze.** `decided ≤ trueCount ≤ decided + undec` is checked
correct: left = `VPSound` injection; right = {true-σ} ⊆ {decided-σ} ⊎ {undec}, since
`canonical N f = some τ` + VPSound + single-valued `trueType` forces τ = σ. Dividing by
p^{nN} and squeezing with `hd`/`henv` is valid. This IS the note's identification
argument made explicit — "the undecided complement has mass 0 and the classifier
verdicts are the true factorization types" (13171–13173) at exactly the note's
granularity; the ℤ_p-Haar reading of the limit is HC-2's declared bridge (settled).
FAITHFUL. Correctly NOT counted as a fifth tag-free step (it is derived arithmetic
whose inputs carry VP-SOUND/CL-4's tags at U10).

**(4) ∃-R-before-∀-p.** Intact in U10: `∃ R, (∑ σ, R σ = 1) ∧ ∀ p hp, RegP → …`, one
family bound before the prime quantifier, witness `S.R`, the checksum conjunct OUTSIDE
the ∀ p (matching "identically in q"). FAITHFUL. (But the same discipline is NOT
applied to `MenuData`/`KernelStatements`, which sit per-p in `UInstance` — see
CRITICAL 2 / GAP 4.)

**(5) The four tag-free units.** U1 (BOX-N: a partition-by-`Option`-value identity,
true for ANY canonical map — matching "tag-free as an identity of counts", 13042–13043);
U2 (ℝ≥0∞ partial-sum domination — exactly the retyped Tonelli clause, existence only);
U5 (SQ.3's arithmetic verified: from (BOX-N) + hupper at τ≠σ + Σ R = 1, the display at
13127–13129 reproduces exactly; `1 < p` declared scaffolding, the note's display
asserted only through U6/U10 at primes); U7 (the env → 0 forcing, explicit arguments).
All four consume no ledger/Prop field. GENUINELY UNCONDITIONAL. (U1/U2 quantify over
structures that bundle Prop fields — `canonical_stable` — but the proofs consume only
data; `canonical_stable` is attributed to the dual-accepted decomposition note's
Thm 2.1, a proved upstream law, so baking it in is instantiable, unlike the correctly
evicted soundness law.)

## Part II — R2 repair verification

| repair | verdict |
|---|---|
| R2-1 (degenerate instance) | GENUINE under settled ruling (B): concrete `Box`/`Nat.card` counts + honest D9 boundary declaration; overclaim withdrawn in body text (shorthand residue in §7, GAP 2) |
| R2-2 (ℤ_p identification) | GENUINE: clause (ii) + U11 second squeeze (verified sound, pressure point 3); HC-2 bridge declared, out of scope per ruling |
| R2-3 (empty (REG-p) families) | GENUINE in the main (index-typed, cardinality-pinned, `_pos` kills det = 1 dodge); caveats GAP 2 (legCount/"all _pos" misstatement) and GAP 3 (positivity possibly over-strong vs the real tables) |
| R2-4 (R_σ(p) definedness) | GENUINE: `RegP` second conjunct `∀ σ, DefinedAt (S.R σ) p`; `RegP.R_defined` accessor; U4/U10 consume `evalℝ` only under it. (Note: (REG-p) thereby becomes explicitly STRONGER than the note's iff-definition (r1)∧(r2) — the note derives definedness from the assembly, the blueprint hypothesizes it; documented, conservative direction, no finding.) |
| R2-5 (bare slots) | PARTIAL: `cl10_vpsound : VPSound X` is the full VP-SOUND statement over the box — genuine. `KsubM1C1` mis-transcribes the note's clause (CRITICAL 1). `cl13 : MenuWF M` is strictly weaker than CL-13 with the full-statement slot deleted (CRITICAL 2). Menus unpinned (GAP 1). |
| R2-6 (O3 pin) | GENUINE: `BaseSection` enum + `baseSection` field + `o3_teichmuller` ledger equation — the SQ.4 display duty (13212–13221) carried |
| R2-7 (circularity/DecidableEq) | GENUINE: three-file order coherent (no `∑ σ` before U0b; `rs4_checksum` lives in DefsLedger); `instTreeDeq` added |

## Part III — findings (fresh sweep + repair-execution defects)

### CRITICAL 1 — `KsubM1C1` binds halting outcomes the note's clause does not

Offending spec (§2, Defs):
> `def KsubM1C1 (M : MenuData) : Prop := ∀ s, ∀ o ∈ M.menu s, o.sameSize = true → o.m = 1 ∧ o.c = 1`
with `sameSize` glossed "whether it stays at equal block size".

Note display (13116–13118): "equal-e **continuation** rides EXCLUSIVELY in K_e's
(c = 1, m = 1) rows ((K-SUB)'s (m, c) classification … the same-size single-child
direction)".

The note's clause qualifies CONTINUING outcomes only. The Lean Prop binds EVERY
same-size outcome, including terminal ones (c = 0) — and same-size terminal outcomes
are generic (they are exactly what feeds `b_e^{term,fin}`; the (τ-irr)/(τ-hen) leaves
halt inside their block). Under the docstring's own semantics for `sameSize`, the
faithful [2a]/[1v] catalogue falsifies `KsubM1C1` (a same-size halt has c = 0 ≠ 1), so
either `cl11` is truthfully uninstantiable or the instantiator must assign `sameSize =
false` to same-size halts against the declared gloss. STRONGER than the display.
Repair shape: `o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1`, or pin `sameSize`'s
semantics to continuing rows. **CRITICAL.**

### CRITICAL 2 — `cl13` weakened: the full CTS-M(i) tag is dropped from the ledger

Offending spec (§2b): `cl13 : MenuWF M`, with (§2)
> `def MenuWF (M : MenuData) : Prop := ∀ s, ∀ o ∈ M.menu s, 1 ≤ o.m ∧ o.c ≤ o.m ∧ (o.c ≠ 0 → o.target.isSome)`
docstring: "… and a target whenever it continues (globally compatible target-cell
maps)"; and (§2b comment) "ctsmSyntax: DELETED as slots at REV 3".

Note CL-13 (13315–13318): "the ONE fixed finite **p-independent** state set with
DISPLAYED **cell predicates** and **globally compatible target-cell maps**; without it
no path product or kernel index type-checks".

Three losses, none carried anywhere: (a) cell predicates — absent entirely; (b) global
compatibility — `o.target.isSome` is per-entry target TOTALITY, not compatibility of
the target-cell maps (the docstring's parenthetical mislabels a weaker condition);
(c) p-independence — `MenuData` sits per-prime inside `UInstance`, so "the ONE fixed
p-independent state set" is not even expressible (each prime may carry a different `M`).
Unlike cl11 (where `noEqualEFeedback` retains a full-statement slot beside the typed
face) the `ctsmSyntax` slot was deleted WITHOUT a surviving full-statement carrier, so
the `CapstoneLedger` — the artifact whose one job is tag-completeness — asserts
strictly less than CL-13 while CL-13 is open. This violates the ledger's own binding
rule, quoted at SQ.4 (13163–13166): "neither this display nor any acceptance record may
drop a tag while any cited CL-item is open — plan §7's acceptance-record rule". Repair
shape: restore a `ctsmSyntax : Prop` slot asserted alongside `MenuWF M` in `cl13`, and
bind `M` before ∀ p (with S). **CRITICAL.**

### GAP 1 — `MenuData.menu` unpinned: the empty-menu vacuity dodge survives

Offending spec (§2): `menu : State → Finset (MenuEntry State)` — no nonemptiness, no
cardinality equation to the [2a]/[1v] catalogue. An instance with every menu `∅`
satisfies `KsubM1C1 M ∧ MenuWF M` vacuously (both quantify `∀ o ∈ M.menu s`). This is
the exact dodge ruling (C) closed for `RegData`'s families (rev-2 critical 3 class),
left open in the structure introduced at the same revision for the same
anti-bare-slot purpose. G8 declares menu fidelity owner-audited, so this is a declared
boundary rather than a statement falsity — but the typed faces were introduced to be
CHECKABLE, and as specced they check nothing on the degenerate M. A `menuCount`-style
pin (per-state outcome count = table data, `_pos` where the catalogue is nonempty)
would meet the rev-3 standard. **GAP.**

### GAP 2 — §7 audit trail misstates the skeleton ("all `_pos`"; "degenerate-proof")

Offending spec (§7, R2-3 row): "cardinality EQUATIONS pinned to count data
(`bidx_card`/`JIdx_card`/`WIdx_card`/`legIdx_card`, **all `_pos`**)" — but §2's
`RegData` has NO `legCount_pos` (and correctly so: (K-TRI)'s well-foundedness, note
13119–13121, means minimal blocks have no β legs, so leg positivity would be false).
The repairs table claims a field the skeleton does not have. Same row family: R2-1's
"makes clause (i) degenerate-proof" is shorthand the careful D9 body text does not
support (clause (i) remains SATISFIABLE by a degenerate instance; it is non-vacuous,
not degenerate-proof). Audit-trail inaccuracies in the acceptance record. **GAP.**

### GAP 3 — `cellCount_pos` (and `shapeCount_pos`) are note-unsupported positivity pins; truthful instantiability unverified

Offending spec (§2): `cellCount_pos : ∀ e, 0 < cellCount e` (with `cellCount` = "the
branching-cell count of the block's table"). The note's E(e) display (13185–13194) and
CL-18 (13337–13343) list the per-cell J entries as a family with NO per-block
positivity claim. By the note's own well-foundedness — "every b_e^split leg has
e_j < e — (K-TRI)" (13119–13121) — minimal-size blocks have no split legs, and
branching cells are what feed `b_e^split`, so the real tables plausibly contain blocks
with ZERO branching cells. If so, `RegData` is truthfully uninstantiable and the
conditional capstone lands in the uninstantiable-hypothesis-structure failure mode
(vacuity by overconstraint — the pre-rebase trap in its dual form). Not decidable from
the note text alone, hence GAP not CRITICAL: needs owner-table confirmation
([3]/[1v]) before E-phase, or relax to per-block data (quantify (r2)'s J clause over
possibly-empty `JIdx e`, keeping `instBiNe`/`blockDim_pos` which ARE safe). **GAP.**

### GAP 4 — `KernelStatements` bundled per-prime though its referents are p-uniform

Offending spec (§2b): `UInstance … where … K : KernelStatements` — each prime's
instance may fill the slots with DIFFERENT propositions, though every slot's referent
(TRACK-COUNT "uniformly in p, N, and depth", 12969–12977; WEIGHT-CHARGE; the CL-5
nine; …) is a single p-independent statement. The ∃-R-before-∀-p discipline (F11) was
applied to `S` but not to `K` (nor `M` — folded into CRITICAL 2). Formally harmless
(slots are opaque either way; fidelity is owner-audited), but the faithful shape — ONE
`K`, audited once — is strictly better and costless: bind `K` (and `M`) as `theoremU`
parameters before the prime quantifier. **GAP.**

## Part IV — sweep positives (checked, no finding)

- (BOX-N)/U1 statement = the 13042 display exactly (sides swapped); tag-free verified.
- SQ.2 route: U3's identity-first form (not ≤) = `finiteness_stack` re-exposed; tags
  CL-7 + CL-10 named — matches 13044–13045. U4 under full ledger + `RegP` + `p.Prime`;
  the (U-n) qualifier "binds the DISPLAYED BOUNDS themselves" (13136–13138) is the
  `hreg` argument on BOTH legs — faithful, D8's no-claim semantics exact.
- SQ.3/U5 arithmetic re-derived by hand from the 13127–13129 display: correct.
- (U-n)/U6 two-sided form and stacks faithful; lower leg's extra RS.4 set = `rs4_eval`
  field with the inherited-set docstring.
- U7 squeeze and U10's assembly (clause (i) = U7∘U6; (ii) = U11; (iii) =
  `cl4_env_tendsto`) type-check on paper; `evalℝ` consumed only under `RegP` (G2 holds
  across all units as specced).
- RegP: (r1) det clause is the right formalization (entrywise definedness from (r2)
  makes eval-det = det-eval on the local ring; the extra `DefinedAt (det …)` conjunct
  is redundant-but-harmless); (r2) ranges over the DEFINED seven-family union with β
  legs at EVERY δ ∈ depthSet — the 13185–13194 display covered in full; `act` abstract
  is G5's declared boundary.
- Ledger completeness otherwise: CL-5 nine slots enumerated (count = 9); CL-8 six
  items with rel2c correctly absent (content at CL-10's (SIB), 13245–13247); CL-12
  correctly absent ("NOTHING at CL-12 is open", 13290–13306) with the O3 residue
  carried as `o3_teichmuller`; CL-2/CL-3 present; `solve_stack` carries the explicit
  `0 ≤ evalℝ` conjunct (RS.3's clause, 13100–13102); U9's (L-meas) equivalence
  re-derived by hand — correct, one-directional IMPLIED-BY faithfully preserved
  (13518–13528), gate correctly NOT a Lean unit.
- Defs soundness: no definition decides an open question; `thrSlice : Finset` =
  finiteness-as-data with CL-7 named open (G3); `VPSound`/`DefinedAt`/`entryList` are
  statements/definitions matching displays. Decomposition: 13 units, one display each;
  counts in §6 internally consistent.

## Counts and verdict

CRITICAL: 2 (KsubM1C1 over-binds halting outcomes; cl13's full CTS-M(i) tag dropped
from the ledger, p-independence inexpressible).
GAP: 4 (menu emptiness dodge; §7 audit-trail misstatements; cellCount/shapeCount
positivity pins unverified against the real tables; per-prime KernelStatements).

Both criticals are localized to the ruling-(E) menu layer; the spine (Box/counts,
SQ.1–SQ.4 units U1–U11, RegP, the ledger's operative fields) is faithful as specced.

**VERDICT: REJECT (2 crit / 4 gap)**
