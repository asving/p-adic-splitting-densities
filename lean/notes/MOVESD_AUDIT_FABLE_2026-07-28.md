# MOVESD LEAN BLUEPRINT REV 2 — FRESH-INSTANCE SEMANTIC AUDIT (Fable)

Date: 2026-07-27 (filed under the campaign's 2026-07-28 charge name).
Auditor: fresh Fable instance (no prior contact with this blueprint or the Codex audit).
Scope: RE-AUDIT of `lean/notes/MOVESD_LEAN_BLUEPRINT_2026-07-28.md` (rev 2, 783 lines, read
in full) after the Codex REJECT (8 crit / 2 gap; §9 findings→repairs table). Charge:
`CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, <CORPUS> = MovesD, <NOTE> = §D4-R. Ground truth read
in full: `MOVES_2026-07-24.md` lines 4580–5435 (§D4-R rev 9) + the rev-9 repair record and
DUAL-ACCEPTED/kernel-status records at lines 6783–6831. Consumed interface read in full:
`lean/LeanUrat/MovesC/Defs.lean` (979 lines) + signature checks in the MovesC unit files.
Duties: (1) verify each rev-2 repair is genuine; (2) fresh sweep (repair-introduced defects
count fully); (3) verify the claimed MovesC names/signatures exist and the blueprint's usage
type-checks conceptually. I fix nothing.

## 1. MovesC interface verification (name/arity check — all PASS)

| blueprint claim | ground truth (`MovesC/Defs.lean` unless noted) | verdict |
|---|---|---|
| `History p F` | `structure History (p) [Fact p.Prime] (F) [Field F] [Finite F]` — fields `nodes`, `nonempty : nodes ≠ []`, `root_iff` | PASS (note: every `History` is nonempty, so "NONEMPTY η" is automatic — consistent with the blueprint's η = ∅ design) |
| `Node` fields `ustar/gam/pat/s0/wSide/Dwidth/e/h/g/μ/a/species` | all present; types `ustar : ℚ`, `gam : ℤ`, `a : ℤ`, `pat : ℕ → ↥σ.K`, `s0 wSide Dwidth : ℕ`, `e h g μ : ℕ` — ShapeRead's field types match exactly | PASS |
| `Realizable` = (NA)+(HV)+(SAE) | `def Realizable (H : History p F) : Prop := ∀ i hi, TransitionAdmissible (nodes[i]) (nodes[i+1])`; `TransitionAdmissible` carries (NA), (HV), (SAE)-strict, (SAE)-adjacent-tie | PASS (rev-14 three-condition class, live) |
| `HistoryCoherent` | present; supplies the root `deg Φ₀ = 1` clause, the slope law `slope·(e·STR·D) = h`, the γ-tie, the width chain `D_{i+1} = childWidth_i` — exactly the clauses D5a/D5b consume | PASS |
| `JetSetup H n N m` w/ `hm, hN, coordOf(_sorted/_lt), coherent, realizable, fresh, mstar_eq` | all fields present with the claimed content | PASS |
| `JetSetup.SHZ (Z : Locus p m) : Set (Fin m → ZMod p)` | present; `Box p m` is a defeq abbrev | PASS |
| `mstar_eq : (fresh i).mstar = Nat.card {c // inFreshBand H n coordOf i (nodes[i]) c}` | verbatim | PASS (exactly what D9 consumes) |
| `C6_thmC_b : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m` | `MovesC/C6_thmC_b.lean:155`: `theorem C6_thmC_b (J) (Z) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z) : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m` | PASS — the extra `hZ` argument matches D0b's sketch `C6_thmC_b J top (topLocus_admissible _)` (instantiated at `Σf := J.Sigma len`) |
| `topLocus` constructor | `Locus p m = DigitSystem m (ZMod p)` (DefsT:187) has exactly `pinned : Fin m → Bool`, `solve : (i) → ((j) → j < i → α) → α`; `IsSolution`/`numPinned` exist as claimed | PASS — `{pinned := fun _ => false, solve := fun _ _ => 0}` type-checks; D0a's three statements are trivially true of it |
| shape-transfer targets | `History.{strFrame,kappaH,innerslotH,htH,floorH,prevRim}`, `Node.{line,staircase,slotVal,fineSlot,childWidth}`, `Line`/`Line.at`, `Coord`, `CoordPrec`, `inFreshBand` — all present; §3.3's shape-side formulas replicate them token-for-token (checked each: strS/kappaS/innerslotS/htS/staircaseS/floorS/prevRimS/bandS vs their History/Node counterparts) | PASS |
| `Stage.K` | `K : Subfield F` (Moves/Defs.lean:132) — `Node.sideDigit`'s coercion `↥ν.σ.K → F` is canonical | PASS |
| "MovesC 36/36 PROVED" | 36 unit files besides Defs; `grep sorry` hits are docstring mentions only (C5_massCodim header, Defs header); no `axiom` declarations | PASS |

No name mismatch, no arity mismatch. The one omission in §1's summary line (C6_thmC_b's
`hZ` hypothesis not shown there) is repaired by D0b's own sketch, which supplies it — not a
finding.

## 2. Repair verification (Codex findings 1–10 → all repairs GENUINE)

1. (idx := Empty vacuity) — `PrefSet Canon P` is defined literally as L3's display
   ("{η : shape(η) = P̂, η realizable, canonical lifts}" ← MatchesHist ∧ HistoryCoherent ∧
   Realizable ∧ Canon); new fields `hcanon`, `complete`; D2b states `range hist = PrefSet` and
   `C = Nat.card PrefSet`, provable from `hshape/hcanon/jet.coherent/jet.realizable` (⊆) and
   `complete` (⊇). Empty idx now forces `PrefSet = ∅` — the note's own L12 allowance
   ("no restriction to C_P̂(p) > 0 is imposed"). GENUINE.
2. (arbitrary enc) — `encOf` is DEFINED from actual `Node.pat` digits + `sel`; `henc` is
   restated on the actual data with the k ≤ ℓ_r bound (= `hRanch`'s range); the cardinal
   bound is DERIVED (D1a digits-in-pool via the Matches pool-card clause + `FiniteField`
   arithmetic; D1b #pool ≤ p^w needs exactly the stated `hp`/`hw`, and `hw` is genuinely
   necessary — at w = 0 the polynomial X^{p^w} − X degenerates — and is available from
   `ShapeRead.hw`; D1c codomain count; D2a `encOf_inj` closes off-slot positions by
   `offSlots_forced`, both sides = 1). The bridge encOf(slots)→henc(all k ≤ ℓ) is complete:
   `hslots ⊆ range(len+1)` puts every slot under the k ≤ len quantifier. GENUINE.
3. (M ≤ n^{|P̂|} dropped) — D3a states BOTH clauses of the PLAN RECONCILIATION display;
   `hn` is the note's "deg R_anch,r ≤ n always" (coarse chain), ledgered §2. GENUINE.
4. (A undefined / ad-hoc hA) — `ShapePrefix.A n N` is now DEFINED (§3.3) as the shape-side
   fresh-band count; I verified the band formula against `inFreshBand` conjunct-by-conjunct
   (prevRim / floor-strict-above / fine-slot upper edge `line.at((b/D)·D)`), the line
   against `hLineU` + the coherence slope law (intercept = ustar + sl·((s0+wSide)·D) —
   u* enters exactly through the intercept, the rev-9 pass-10-F1 point), and the junk
   conventions (getElem?-elim ⊥/0/False) against the History-side junk conventions. D9
   makes L9 a THEOREM (`totalPins = P.A n N`) through `mstar_eq` + D8 + D4b; D10/D12/D13
   carry `P.A n N` with no `hA`; D3b is Corollary D4R.2 in exact division-free transposition
   (count·p^A ≤ M·p^{W+nN} ⟺ μ(P̂) ≤ M·p^{−A_net}). GENUINE — and the def does not decide
   anything open: it replicates the formula `mstar_eq` already pins, and the identity with
   the jet-side count is a theorem (D9), conditional exactly on the jet (HC-2).
5. (empty shape C = 0 vs C_∅ = 1) — `hne` keeps P̂ = ∅ out of families; D14a carries the
   note's display verbatim (full box, literal 1 = C_∅, exponent through `A_nil`), clear of
   Theorem C(b). GENUINE.
6. (N = 0 instantiation) — `hN : 1 ≤ N` is the note's OWN quantifier ("for EVERY N ≥ 1",
   L12 empty case) — not a silent strengthening; `hm` fixes the box shape. On D14a and
   D14b, ledgered. GENUINE.
7. (TreeModel mem := False) — `mem_realizable` added (exactly L2's "emits only realizable
   patterns … canonical lifts", no termination/maximality growth); D0c (`fiber_pos`, from
   Theorem C(b)'s positive mass) makes `mem := False` violate `cyl` for any inhabited
   family; maximality-on-the-family = `cyl` + `complete`, documented, with the cell-level
   eligibility semantics correctly left to kernel-(b)/HC-2. GENUINE.
8. (VerdictModel leaf := False) — typed V (finite, nonempty), `vdict : … → Option V`,
   `leaf_iff`, and L2's "no children IFF terminal verdict" in BOTH directions
   (`leaf_maximal` + `leaf_of_maximal`; under prefix-closure "no proper extension" = "no
   children"); `cap` typed with `hcap`. Stays a statements-only OPEN surface consumed by
   nothing in MovesD — matching the kernel record's (c)/VP ownership (§T-ASSEMBLY → MovesT).
   GENUINE.
9. (hidden multi-lemma D4) — chart uniqueness deleted (A lives on the raw grid); D4a
   (injectivity from `coordOf_sorted` + CoordPrec irreflexivity; surjectivity by pigeonhole
   with `hm`, card grid = N·n = m) + D4b (count pushforward) are honest one-lemma AUX units.
   GENUINE.
10. (D6/D7 bundles) — unbundled one lemma per unit (D6a–e, D7a–c, D5a); I checked each
    transfer statement against the MovesC definition it mirrors, including the coherence
    dependencies (hcoh appears exactly where the slope law / width chain is needed: D5a,
    D5b, D7a, D7b, D7c, D8-via-J.coherent; kappa/innerslot/htH/prevRim need none — correct).
    GENUINE.

## 3. Fresh sweep (all 32 units + §3 Defs; faithfulness / non-vacuity / hypothesis
fidelity / Defs soundness / decomposition)

Unit dispositions — D0a, D0b, D0c, D1a, D1b, D1c, D2a, D2b, D3a, D3b, D4a, D4b, D5a, D5b,
D6a–e, D7a–c, D8, D9, D10, D11a, D11b, D12, D13, D14a, D14b, D15: ALL CLEAN. Spot-verified
in particular:

- D10 = D4R.1-SUM/D4R.4-SUM in the declared division-free level-N form; the sum is over the
  INDEX type (no disjointness anywhere — rev-6 F1 respected); empty idx gives the L12
  0 = 0 clause inside the statement. Provability chain (per-summand D9-rewrite + thmC_top,
  then constant sum) checks.
- D12 = the EV union bound; D13's equality criterion is pointwise-on-the-event
  (`∀ x ∈ S.event, S.mult x = 1`) — the note's finite-level pointwise upgrade, never a.e.
- D15 matches the L6-corollary display; `T.cyl` is an iff for EVERY x, no termination
  hypothesis anywhere in the corpus (checklist 3 holds).
- ShapeRead retains EXACTLY rev-9 L3's list incl. BOTH heights (h, u*), γ, w, and the slot
  sets; nothing digit-valued rides in the shape data (the off-slot forced 1 is a Matches
  constraint, not shape data — and the note's own gate display records "slot 3 = the monic
  lead, digit 1" inside the shape spec). The Defs reproduce the gate numbers: len₀ = 3,
  mbar₀ = ⌊3/2⌋ = 1, mbar₁ = ⌊1/1⌋ = 1, M = 1, W = 1·3 + 2·2 = 7 — matching §D4-R.6.
- Kernel conditionality (checklist 5): no unit cites `D4R0K_DERIVATION` as a Lean
  discharge; (a)/(b) appear only as "note-discharged; Lean = HC-2" annotations on hypothesis
  FIELDS (`henc`, `cyl`); (c)/VP appears only in `VerdictModel`. §0's kernel-status report
  matches the 2026-07-27 record verbatim.
- Hypothesis ledger (§2) is complete against the note's open kernels: Canon (§B2-DEF/HC-1),
  jet/complete/henc/sel-semantics (HC-2), offSlots_forced (flagged), TreeModel fields,
  VerdictModel, hn, hN/hm. Nothing silently dropped, strengthened, or smuggled into an
  axiom; the corpus declares no axioms.
- Perimeter (§5) mirrors §D4-R.5: no p-uniformity, no catalogue/aggregation, no
  resummation/termination, no literal (3i), D4R.3 stays retired, consumer-duty COVER note
  carried.

ADJUDICATION OF THE STANDING FLAG (`Matches.offSlots_forced`, §3.2 / checklist 7 — "reject
if it misreads the note"): NOT a misreading. Evidence: the note's own W-accounting at the
pinned instance excludes exactly one side position — the monic lead, whose digit the note
displays as the literal 1 ("slot 3 = the monic lead, digit 1"; d₀ = 3 of 4 side slots) —
while the (HV)-forced depth-1 lead d'₁ is RETAINED in the slot set (d₁ = 2, "the pool bound
strict — slack displayed, not hidden"). So the note's convention is: transport-forced digits
stay IN the slot set; only structurally-monic positions (digit ≡ 1) may be excluded — which
is precisely the blueprint's clause. It is also what makes the slots-restricted enc′
injective and W the pool dimension, as the blueprint's bridge note says. The flag should
stay live for future waves (the note states no general exclusion rule; new shapes arrive
with the [2a]/[2b] menu), but rev 2 is faithful to every displayed instance.

Remarks (below finding threshold, not counted):
- D1c is labeled AUX yet cites a moves_ref (L11's injection display, codomain side); the §4
  header defines AUX as display-less. Cosmetic mislabel; nothing is hidden — the unit itself
  is display-keyed and faithful.
- `PrefSet Canon P` at `P.reads = []` is ∅ in Lean while the note has Pref(∅) = {∅}; this
  edge is consumed by NO unit (hne blocks families; D14a hard-codes the literal C_∅ = 1) and
  is explicitly declared in design note (iii). No statement conflates the two.
- The note's "∀ N ≥ N(P̂)" quantifier is absorbed into per-family jet existence at a common
  N (declared FINITE-LEVEL POLICY, §1/§5); the empty-case N ≥ 1 clause is carried exactly
  (hN). The ∀-N content is recovered by quantifying over families. Declared design, faithful.

## 4. Counts and verdict

Repairs 1–10: all verified GENUINE. Fresh defects introduced by repairs: NONE found.
MovesC signature check: all names exist with the claimed signatures; conceptual
type-checking of every consuming statement passes. Checklist §7 items 1–8: all verified.

CRITICAL: 0. GAP: 0.

VERDICT: ACCEPT
