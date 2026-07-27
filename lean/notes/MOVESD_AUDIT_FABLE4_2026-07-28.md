# MOVESD BLUEPRINT AUDIT — FRESH FABLE #4 (confirmation pass on REV 5)

Date: 2026-07-28 · Auditor: fresh Fable instance #4 (no prior context; read-only)
Scope: `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` REV 5 in full (1066 lines), verified
against the sole ground truth `MOVES_2026-07-24.md` §D4-R rev 9 (lines 4580–5435)
+ the dual-acceptance record (6783–6831) + `lean/LeanUrat/MovesC/Defs.lean`.
Charge: the eight rev-5 reconciling designs (§12), HARDEST-FIRST per the
orchestrator's list, INCLUDING a from-scratch gate recomputation on the changed
carrier (Option-rooted TreeModel, MonicTie, PrefOpt) — per the standing warning
that Fable auditors have been too charitable on generality/domain readings, every
verdict below is checked against a DISPLAY or an explicit construction, not
plausibility.

## 1. TreeModel on the Option carrier (charge item 1) — PASS

Fields walked law by law (`blueprint §3.4, lines 544–559`):
- `root_mem : ∀ x : Box p m, mem none x` — exactly L2's "its root is the empty
  chain ∅" + L6's "{f : ∅ ∈ T_can(f)} is the full box too (every tree carries the
  empty chain, L2)" (note 4872–4873). Codex#3-f.6's reading satisfied as a LAW.
- No law forces `some`-chain inhabitation: `mem_single`/`mem_snoc` are IFFs
  relating `some`-membership to `child`, satisfiable with `child := fun _ _ _ =>
  False` (∅ a leaf — L5's (ns) case, note 4817–4819). Fable#3-C-8's computation
  stands. Both rev-4 readings verified coexistent on this carrier.
- `mem_single`: the singleton history `⟨[ν], h1.1, h1.2⟩` — `root_iff` inside the
  History structure forces `ν.species = root`, so children-of-∅ are exactly root
  reads; for non-root ν no such history exists and `child none ν x` is junk
  consumed by nothing. Correct.
- `mem_snoc` (`hν : ν.species ≠ root`): every ≥2-node history decomposes as a
  snoc of a non-root node (root_iff at index ≥ 1), so with `mem_single` the two
  generation laws cover all nonempty chains — T1a's downward induction closes;
  its base `mem (some H) x → mem none x` is immediate from `root_mem`.
- Quantifier sweep for accidental `none`-quantification: `mem_realizable`,
  `D4R_CYL` (`some (reprOf i)` — matching L6's "the two inclusions below
  therefore range over NONEMPTY η", note 4875), T1a, D15, `halt_iff` (nonempty
  History carrier; ∅-verdict documented as MovesT's VP-2 corner) — all on `some`
  / proper History. The ∅ clause of (D4R-CYL) ("holds by display", note 4873) is
  `root_mem` + `emptyFiber = univ`, trivially true, correctly not a unit. NO law
  quantifies over `none` where the note means a proper node.
- Empty-shape D4R_CYL is vacuous (MatchesHist forces length 0, impossible) —
  consistent with the note's dispatch. NO finding.

## 2. Presented.hnorm / PresentNorm (charge item 2) — PASS

`PresentNorm` (§3.2, lines 348–351): totality over the POLICY-FREE `PrefSetAny`
(∃ Galois-mate in PrefIdx) ∧ Galois uniqueness on PrefSet classes.
- Note support checked: L1 totality (kernel-(a), math-DISCHARGED per the dual
  record, note 6820–6823), the L6 corollary "realizable ⟺ realized, now for
  EVERY branch" (note 4913–4915), equivariance/rigidity = the declared HC-2
  residue — carried as the FIELD `hnorm`, i.e. in hypothesis_fields, never
  strengthened into a definition or axiom. Conforms to the ledger policy.
- CONSTRUCTION CHECK (the empty-PrefIdx junk instance): PrefIdx empty +
  PrefSetAny nonempty → totality's `∃ i : PrefIdx …` has no witness — hnorm
  VIOLATED, `Presented` uninhabited. Confirmed by direct inspection.
- CONSTRUCTION CHECK (history-voiding policy): on a shape with a mid-history
  recentering, `HistoryCoherent`'s `IsRecenteringCore … (nodes[i]).lift` pins
  the recorded lift to a genuine realizer; a `pol.liftOf` returning non-realizer
  values makes `IsCanon` contradict coherence → PrefSet = ∅ vs PrefSetAny ≠ ∅ →
  totality violated. The vacuity instance is unbuildable. (Conversely a merely
  RELABELING junk pol — constant realizer-irrelevant lifts on shapes whose lifts
  are coherence-unconstrained — leaves PrefIdx literally unchanged, since
  `etaData` reads no lifts: harmless, C unchanged. Checked.)
- Uniqueness direction stress-tested at the gate (p = 3): a nontrivial φ moving
  F₉ would have to move the (HV)-forced d′₁ = ω₀ − r (ω₀ = canonRoot, pinned),
  which no second PrefSet member carries — the clause merges only genuine
  conjugate presentations, never distinct η's. NO finding.
- `canonRoot` vs `hspecRecCenter` consistency at recenterings: ψ linear, unique
  root = center = zbar — the IsCanonPres root clause is automatic there, no
  conflict. Checked.

## 3. The F3 bridge (charge item 3) — PASS

`PrefOpt` (lines 357–361): `none ↦ P.reads = []`; `some H ↦ H ∈ PrefSet ∧ reads ≠ []`.
- `PrefOpt_empty`: at `hP`, none qualifies, no `some` does → `= {Option.none}`.
  This IS the note's "Pref(∅) = {∅}" (note 5169: "(present iff P̂ = ∅,
  Pref(∅) = {∅})") with none = the empty chain — literal, not a relabel.
- `CD_correspondence` recomputed both branches: empty — `etaDataO '' {none} =
  {none}`, card 1 = CD's if-branch; nonempty — `etaDataO ∘ some` image has the
  card of `etaData '' PrefSet` (some injective) = `Nat.card PrefIdx` = CD.
  The consumed arithmetic (D14a's C_∅ = 1 · p^{nN}, D10's constant via CD_eq) is
  therefore theorem-equivalent to the note's ontology; nothing shifts. The
  redundant `reads ≠ []` conjunct on the some branch is harmless (MatchesHist
  already forbids it). NO finding.

## 4. Threshold / D4R4_all / TW (charge item 4) — PASS

- L12 QUOTE CHECK: the unit's moves_ref (blueprint 876–878) matches note
  5150–5157 verbatim (elision marked); the empty-case convention N(P̂) := 1
  (note 5139) is `hNP1` + D14b's explicit `hN : 1 ≤ N`.
- `Threshold` fields = the L12-visible content: `hstab` (A stable from NP on —
  exactly what D4R.4-SUM at N ≥ N(P̂) forces: every fiber cut at level ≤ N, all
  A pins below NP) and `jets` (§C C.2 presentability) — both declared HC-2
  structure fields, displayed in hypothesis_fields. Not smuggled.
- COVERAGE [NP, Nshape): genuine — D10/D12/D13 carry `hA : P.A n N = P.A' n`
  (a hypothesis, discharged by L9s at N ≥ Nshape and by `T.hstab` at N ≥ NP);
  D4R4_all's proof is a one-line hA-swap. Verified against the displayed D10/D12
  statements (lines 835, 853). Conclusion has NO ∃-over-presentations (the
  presentation is T's datum), matching "the note quantifies over LEVELS only".
- `TW_threshold_witness` proves exactly what it claims: Threshold INHABITATION
  with NP := Nshape (1 ≤ Nshape by construction; hstab := L9s; jets := hex via
  choice) under PRESENT-EXIST — consumed HERE and only here per the ledger. It
  does NOT claim minimality; "Nshape ≥ N(P̂) materialized as witness-hood" is an
  accurate gloss. The trivial-hex attack: a junk pol voiding PrefSet against
  nonempty PrefSetAny makes `Presented` (hence hex) uninhabitable via hnorm;
  a genuinely empty shape gives the honest L12 C = 0 case. NO finding.

## 5. MonicTie (charge item 5) — PASS

`ShapePrefix.MonicTie` (lines 247–249): `monicTop = true ↔ (r = 0 ∧ s0 + wSide = n)`.
- FORCES the top slot = the degree-n coefficient: forward, monicTop only at the
  root read whose span reaches slot n (root Dwidth = 1: slot = base index) — the
  monic lead of the degree-n box, the note's own displayed convention ("slot 3 =
  the monic lead, digit 1", note 5264). Backward, a root full-span read CANNOT
  hide the lead (inflate W): monicTop forced true. Faking it elsewhere (shrink W)
  fails the iff; as a PrefSet ∧ PrefSetAny clause the shape's C is 0 — the
  junk-W instance is unbuildable on C-carrying territory. Codex#3-f.1 answered.
- NO contradiction with the L11 reconstruction at the gate: P̂* read 0 has
  s0 + wSide = 0 + 3 = 3 = n → monicTop = true, d₀ = ℓ₀ = 3; read 1: r ≠ 0 →
  false, d₁ = ℓ₁ + 1 = 2 — the note's counts. `Matches.hmonic` then pins
  sideDigit(ℓ₀) = 1, exactly §D4-R.6's display; `hmonicRoot` (species guard) is
  consistent with root_iff under MatchesHist. NO finding.

## 6. MANDATORY GATE RECOMPUTATION from the rev-5 definitions (charge, item 5/6)

Recomputed from §3.1/§3.3 defs at the pinned P̂* (NOT copied from §0.6):
- lineS₀ = 3 − b (sl = 1/(1·1·1), intercept = 0 + 3); lineS₁ = 4 − (3/2)b
  (sl = 3/(1·1·2), intercept = 1 + 3). κ₀ = 1; innerslot₀(b) = b % 2;
  htS 1 (ℓ,b) = ℓ + (b % 2); floorS 1 = 3 on b ∈ {0,1}; prevRim = (3, 2).
- Band r = 0: {ℓ ≤ 3 − b} = 4 + 3 + 2 = 9; band r = 1: {b < 2, 3 < ℓ + (b%2) ≤ 4}
  = {(4,0), (3,1)} = 2. **A = 11 ✓** (needs ℓ = 4 in grid: any N ≥ 5).
- **Nshape = 1 + max(⌈3⌉, ⌈4⌉) = 5 ✓**; **W = 1·3 + 2·2 = 7 ✓** (d₀ = 3 via
  MonicTie-forced monicTop); **M = ⌊3/2⌋·⌊1/1⌋ = 1 ✓**.
- Classes (etaData on PrefSet with IsCanonPres): p = 2 — one realizable root
  tuple (0,0,1) × one ψ-image × zbar₀ pinned to canonRoot (×1; the rev-3
  conjugate split is gone) × [d′₁ (HV)-forced ×1 · d′₀ ∈ F₄ˣ ×3]:
  **C_P̂*(2) = 3 ✓**; p = 3 — 6 root tuples × 8: **C_P̂*(3) = 48 ✓**.
- **mult ≡ 1 ✓**: deg R₀ = 3 < 4 forces the unique eligible quadratic per cell,
  R₁ linear; one class per realized cell (note 5396–5404 verbatim mechanism).
All sealed values reproduced on the NEW carrier (Option carrier, MonicTie, and
PrefOpt touch neither A/W/M/Nshape's defs nor PrefIdx's count at this shape).

## 7. Spot-checks (6 units, randomized) + full sweep of all 46

Spot-checked in depth: **E4** (natDegree from hRanch + hpatTop — matches L11's
ℓ_r = w′_r/e_r, note 5046–5051), **E6** (coprime-irreducibles degree count ≤
⌊ℓ/(gμ)⌋ — L11's m̄_r, Nat-division = floor ✓), **W1** (InBox root case
wSide/e ≤ s0+wSide ≤ n; step via coherence's window containment
`s0′+wSide′ ≤ μ_prev` — field verified in MovesC HistoryCoherent — + E5),
**D9** (topLocus numPinned = 0; mstar_eq → band → grid via D4a/D4b → A's
summand; the division-free pin form of L9's display), **D13** (pointwise-on-
the-event iff — note 5180–5182's "carries no measure-zero exception" ✓),
**D14b** (matches L12's empty case, note 5143–5147, incl. "for EVERY N ≥ 1").
Sweep of the remaining 40: D0a–c, E1–E3, E5, E7–E9 (EligibleImage's ∃-lift
clause transports irreducibility over the pool SUBFIELD, never over F — the
rev-4 repair intact; rank-membership forces m̄ ≥ 1), D1c, D2a, F1, F3, W2, W3
(unconditional via the empty/member split ✓), D3a–b, D4a–b, D5a–b, D6a–e,
D7a–c (bandS's upper edge is the FINE-slot boundary `(c.2/Dwidth)·Dwidth` —
mirrors MovesC ROUND 6's `inFreshBand` exactly; floorS stays the coarse
staircase, also mirror-exact), D8, L9s (band levels < Nshape via ht ≤ line ≤
intercept, sl ≥ 0 ✓), D10–D12, D4R4_all(+TW), D11a–b, D14a, T1a, D15.
Checklist §7 items 1–7 re-verified (E1–E9 consume only MovesC Props + Matches;
`Presented.jet` + `hnorm` the only assumed fields; CD's if-branch definitional).
NO criticals, NO gaps found.

## 8. Observations (non-blocking; recorded for the implementer, not counted)

- O-1 `mem_single`'s binder `(h1 : _)` (line 556) will not elaborate as written
  (a structure-field binder type cannot be inferred from `.1`/`.2` uses); the
  intended type — the conjunction of the two History proof obligations for
  `[ν]` — is unambiguous. Same spec-level ellipsis convention as the accepted
  `…` in `RanchImage`/`poolSubfield`/`History.snoc`.
- O-2 D4R4_all packages D4R.4-SUM + D4R.4-EV but not the display's "with
  equality iff mult ≡ 1" tail (note 5158–5159). Not dropped from the corpus:
  D13 carries the iff at the `hA` level and `T.hstab` discharges hA at every
  N ≥ NP — the threshold-form iff is the one-line composite
  `D4R1_EV_iff hne N (T.hstab N hN) (T.jets N hN)`. Flagged so no consumer
  mistakes the wrapper for the full three-clause display.
- O-3 D15's `hwd : ClassFiberWelldef` is carried per reconciliation (7) but the
  displayed proof sketch (rewrite along hcyl) does not consume it — it is
  wiring, making the semantic pin visible at the consumption site. Harmless
  (hypotheses only weaken); intent documented in the unit.

## Counts and verdict

Critical: 0 · Gap: 0 (three non-blocking observations recorded above).
Gate acceptance test: C_P̂*(2) = 3 ✓ · C_P̂*(3) = 48 ✓ · mult_P̂* ≡ 1 ✓ ·
A = 11 ✓ · W = 7 ✓ · M = 1 ✓ · Nshape = 5 ✓ — all recomputed from the rev-5
definitions on the new carrier.

**ACCEPT**
