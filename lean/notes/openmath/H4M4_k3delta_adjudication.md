/-
# H4-M4 — §3.2's STATEMENT-PRECISION step for (UB-X)(b) + (K3-δ): both routes' exact statements, the pressure display, the adjudication (Fable prover H4-M4, 2026-08-01, Wave 2)

Unit H4-M4 of `lean/blueprints/HDISCHARGE_H4.md` (§M table + §3.2's plan).
This file is a LITERATE LEAN MARKDOWN NOTE (the H4-M2 format): prose in
comment blocks, every Lean declaration compiles. Gate command (from `lean/`):
`lake env lean notes/openmath/H4M4_k3delta_adjudication.md` — green, zero
sorry. The unit's OTHER gate (Codex adversarial read of the adjudication) is
run on this text after composition; record at §7.

CHARGE (blueprint §M row, verbatim): "`lean/notes/openmath/
H4M4_k3delta_adjudication.md` — §3.2's precision step | both routes' exact
statements; the split-countermodel pressure on naive (b) displayed;
recommendation + ROOT-sync note (a Route-B adoption is a ledger statement
change — ROOT owner's touch, per the standing rule) | H4-M2 (the dictionary);
O-11 §3.4 (K3-c); REL.2(e) adjacency | MED | Codex adversarial read of the
adjudication."

STATEMENT-FENCE RECORD: the blueprint has NO §L Lean spec for H4-M4 (it is a
§M math-note unit); the charge text is transcribed verbatim above, the §3.2
route texts are transcribed verbatim in §§2–3 below, and every Lean
declaration here is adjudication-layer vocabulary of this unit (fresh
namespace `LeanUrat.Scaffold.HDischarge.H4.Adjud`). The corpus faces
`UBXbStmt`/`K3deltaStmt`/`RealizedLedger`/`AlphabetData.Stable` are consumed
by IMPORT, verbatim, never re-transcribed or weakened. H4-M2's dictionary
theorems live in a literate note OUTSIDE the import graph, so their
CONCLUSION is consumed here as the displayed interface `DictSlice` (§2.2) —
an interface citation, not a new assumption and not a duplicate declaration.

## §0. Verdict summary

1. Naive (UB-X)(b) is NOT WELL-POSED as worded (blueprint §3.2 finding,
   transcribed §1). Both precise routes are stated exactly (§2 Route A, §3
   Route B).
2. The split-countermodel PRESSURE on naive (b) is displayed (§2.3, Lean
   faces `not_k3delta_of_noncoprime_pool` / `not_ubxb_of_noncoprime_realized`
   + the F₉-shape seed) — NO countermodel is claimed: whether the O_δ
   classifier's realized ledger contains a matched gcd(m, δ) > 1 position at
   any consumed (n, p, δ) is the OPEN realization question (H4-M2 §5 residue
   item 5); composite δ alone does not force it.
3. ADJUDICATION (§5): the dictionary (H4-M2, on file, compile gate green;
   its own hostile-pass gate rides Wave 1 and is NOT asserted here) does
   NOT land a cheap Route A — it reduces A's per-pool obligation to realized
   coprimality (`k3delta_iff_pool_coprime`), a REALIZATION property the
   dictionary does not control, quantified over every consumed (n, p, δ).
   **RECOMMENDATION: ROUTE B**, branch-robust in N-K3's pending verdict
   (branch table §5.3; N-K3 verdict NOT on file at composition time).
4. ROOT-SYNC NOTE (§6): Route-B adoption is a LEDGER STATEMENT CHANGE
   ((UB-X)(b) member text + (K3-δ) fragment content replaced by the intrinsic
   law) — ROOT owner's touch, per the standing rule. Nothing is discharged by
   a Route-B proof until that re-scope lands; H4-M5 + H4-M7 travel together;
   H4-F5 stays fenced until BOTH gates (this recommendation ACCEPTED and the
   ROOT re-scope LANDED) fire.

## §1. The precision finding, transcribed (what makes this unit necessary)

Blueprint §3.2, verbatim (scope corrected at the Codex fold, finding 1):

> Member (b) is NOT WELL-POSED as worded: "realized ledger" and the
> cross-base matching of position classes have NO recorded definition (the
> (a6)/(EQ-1) dictionary is an owed REL.1 artifact), so (b) can be neither
> proved nor refuted as it stands. Under ONE candidate reading — the
> same-keys-transport matching — there is refutation PRESSURE: M14 Lemma 4
> (dictionary-conditional) makes a transported position with gcd(m, δ) > 1
> unstable, and the note's worked F₉ instance is out-of-domain in exactly
> that way; whether the O_δ classifier's OWN realized ledger contains such a
> matched position at a given (n, p, δ) is an open realization question, NOT
> an established countermodel — and composite δ alone does not force a
> realized m sharing a factor with δ. N-gate N-K3 (§N) probes this
> empirically.

The AUTHORITATIVE row texts being precised (ROOT_ASSEMBLY_2026-08-02.md,
(UB-X) row): "(b) δ-stable position classes exhaust the realized ledger at
every δ — whose restriction to Step 18 K3-c's realized δ > 1 pools is the
named fragment (K3-δ), consumed by clause (R)". The CONSUMER being served
(O-11 §3.4, K3-c, verbatim head): "(K3-c) Unramified pools (q₀ = p^δ,
δ > 1): the re-based classifier obeys the same digit/alphabet laws with
a_δ = δ·a₁ — O-8b (M14), PROVED-UNVERIFIED conditional on (R1)–(R4)".

STATUS UPDATE SINCE THE BLUEPRINT WAS WRITTEN (Wave 1 landed, on file):
H4-M2's dictionary makes the same-keys-transport matching PRECISE at this
group's slice and PROVES Stable ⟺ (R4) ⟺ gcd(m, δ) = 1 there (its own
named rows [IN-R1]/[IN-U]/`GcdSlice` displayed, not absorbed). H4-M1's
(R1)–(R3) pass is PROVED over W(F_q) at its §0.4 perimeter. So the two
undefined terms of naive (b) now have exactly ONE recorded candidate
precisification each: "matching" = H4-M2's same-keys device at the M2 slice;
"realized ledger" = the interface shape typed at H4-L7's `RealizedLedger`
(realization SEMANTICS still fenced at H4-F2). (b) remains unposed at FULL
scope — the full (a6) dictionary is still an owed REL.1 artifact — which is
exactly why the two routes below are the only precise statements on offer.

ADJACENCY FENCE (blueprint §1, verbatim): "Adjacent, NOT this group:
REL.2(e) β-IDENTIFICATION (the [2r]-side typing of the same D-c seam —
(e1)–(e5), owned by the CL-8/[2r] rows)". Both routes below leave (e1)–(e5)
untouched: the typing of each K3-c pool as a REL.1-side state over O_D is
CONSUMED as the pools' presentation, never re-derived here. The MovesRBase
BASE-INDEX CONVENTION (δ ABSOLUTE) binds throughout, matching REL.2(e2).
-/

import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.Scaffold.HDischarge.H4.Kernel

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4.Adjud

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-!
## §2. Route A — the direct match display, (K3-δ)-only scope: EXACT statement

### §2.1 The statement, verbatim (blueprint §3.2, Route A bullet)

> **Route A — the direct match display, (K3-δ)-only scope.** Prove exactly
> the fragment clause (R) consumes: K3-c's REALIZED δ > 1 pools are δ-stable
> position classes. The pools arise as family-(vi) β-legs β_{μ}(σ)(q^{D}) —
> continuation reads at accumulated residue degree D (the child's tower
> fields); the β-IDENTIFICATION seam (REL.2(e), adjacent) types each pool as
> a REL.1-side state over O_D. THE PROOF OBLIGATION, exact (corrected at the
> Codex fold, finding 2 — intrinsic irreducibility of the O_D-side residuals
> over their own fields does NOT imply cross-base letter equality): per
> realized pool, display matched-prefix letter equality against the
> (a6)/(EQ-1) dictionary (H4-M2) — i.e. a per-pool argument that the matched
> prefix's stage tuples and residual degrees persist (under the same-keys
> matching this is a gcd/structure condition on the pool's accumulated
> residue degrees, Lemma 4's criterion; a pool violating it is a REFUTER of
> Route A, which N-K3 hunts). Deliverable: (K3-δ) retires from clause (R);
> clause (R) returns to (H4a)-only at this interface (ROOT's anticipated
> outcome). Member (b) at FULL scope stays open.

Typed face (already on file, consumed by import — H4-L8, Kernel.lean):
Route A's target is EXACTLY `K3deltaStmt p RL` (per-pool `Stable`), and the
naive-(b) reading it restricts is `UBXbStmt p RL`; the restriction law is
`k3delta_of_ubxb`. Nothing is re-declared here.

### §2.2 The dictionary interface (H4-M2's conclusion, consumed as displayed)
-/

/-- The (a6)/(EQ-1) dictionary's conclusion at this group's slice, as an
INTERFACE: `Stable` ⟺ gcd(m, δ) = 1 at the same-keys matching, where
`mdeg x` is x's accumulated residue degree m = d·g₁···g_k. This is EXACTLY
the conclusion of H4-M2's `alphabetData_stable_iff_coprime` (proved there at
any §7.2-conforming instance carrying the `GcdSlice` rows, with
`mdeg x = G.dDeg x * (G.gDegs x).prod`; conditional on M2's named rows
[IN-R1]/[IN-U] + `GcdSlice.l4_persist`/`coincide` — see M2 §5). It enters
here as a hypothesis ONLY because M2 is a literate note outside the import
graph; every consumer below displays it. It is NOT a new assumption of this
unit. -/
def DictSlice {Sp : SpeciesSyntax} (AD : AlphabetData p Sp)
    (mdeg : AD.Pos → ℕ) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos),
    AlphabetData.Stable p AD δ x ↔ Nat.Coprime (mdeg x) (δ : ℕ)

/-- **Route A's proof obligation, reduced through the dictionary (the
adjudication's load-bearing display):** given the H4-M2 slice, (K3-δ) is
EQUIVALENT to per-pool realized coprimality — for every realized δ > 1 pool,
the pool position's accumulated residue degree m is coprime to the pool
index δ. Route A therefore has NO content beyond a REALIZATION property of
the classifier's own ledger, which the dictionary does not control. -/
theorem k3delta_iff_pool_coprime {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) {mdeg : AD.Pos → ℕ}
    (hdict : DictSlice p AD mdeg) :
    K3deltaStmt p RL ↔
      ∀ P : RL.Pool, Nat.Coprime (mdeg (RL.poolPos P)) ((RL.poolIdx P) : ℕ) :=
  forall_congr' fun P => hdict (RL.poolIdx P) (RL.poolPos P)

/-- Naive (b) under the same reading: full-ledger realized coprimality.
Displayed to make the pressure's TARGET exact — one realized non-coprime
position at ANY δ refutes it. -/
theorem ubxb_iff_realized_coprime {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) {mdeg : AD.Pos → ℕ}
    (hdict : DictSlice p AD mdeg) :
    UBXbStmt p RL ↔
      ∀ (δ : ℕ+) (x : AD.Pos), x ∈ RL.realized δ → Nat.Coprime (mdeg x) (δ : ℕ) :=
  forall_congr' fun δ => forall_congr' fun x =>
    imp_congr_right fun _ => hdict δ x

/-!
### §2.3 The split-countermodel PRESSURE on naive (b), displayed — no countermodel claimed

The pressure, exactly: under the same-keys reading, M14 Lemma 4 (now H4-M2's
proved `stable_iff_coprime`) makes ANY realized matched position with
gcd(m, δ) > 1 an outright refuter. The two Lean faces below display the
refutation MECHANISM at both scopes; they fire only on a WITNESS (a realized
non-coprime pool/position), and no such witness is on file. What IS on file:
the F₉-shape seed (m, δ) = (2, 2) is out-of-domain as abstract species data
(M2 §4, `f9_out_of_domain`), and composite δ alone does NOT force a realized
m sharing a factor with δ (blueprint finding 1). The realization question is
open; N-K3 probes it empirically (§5.3).
-/

/-- Pressure at (K3-δ) scope: ONE realized pool violating Lemma 4's gcd
criterion refutes (K3-δ) under the same-keys reading — the refuter shape
N-K3 hunts. Fires only on a witness `P`; none is claimed. -/
theorem not_k3delta_of_noncoprime_pool {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (RL : RealizedLedger p AD) {mdeg : AD.Pos → ℕ}
    (hdict : DictSlice p AD mdeg) (P : RL.Pool)
    (hP : ¬ Nat.Coprime (mdeg (RL.poolPos P)) ((RL.poolIdx P) : ℕ)) :
    ¬ K3deltaStmt p RL :=
  fun h => hP ((hdict (RL.poolIdx P) (RL.poolPos P)).mp (h P))

/-- Pressure at full-(b) scope: one realized non-coprime position at any δ
refutes naive (b) under the same-keys reading. -/
theorem not_ubxb_of_noncoprime_realized {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (RL : RealizedLedger p AD) {mdeg : AD.Pos → ℕ}
    (hdict : DictSlice p AD mdeg) {δ : ℕ+} {x : AD.Pos}
    (hx : x ∈ RL.realized δ) (hnc : ¬ Nat.Coprime (mdeg x) (δ : ℕ)) :
    ¬ UBXbStmt p RL :=
  fun h => hnc ((hdict δ x).mp (h δ x hx))

/-- Direction of travel of the pressure (consistency with H4-L8): pool-level
pressure already refutes full (b) — the fragment is the WEAKER claim. -/
theorem not_ubxb_of_not_k3delta {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (RL : RealizedLedger p AD) (h : ¬ K3deltaStmt p RL) : ¬ UBXbStmt p RL :=
  fun hb => h (k3delta_of_ubxb p RL hb)

/-- The F₉-shape arithmetic seed (M2 §4's instance read at this note's
interface): (m, δ) = (2, 2) violates the criterion — the shape a realized
refuter would have; (m, δ) = (2, 3) is the in-domain contrast. Decide-checked;
NOT a realization claim. -/
theorem pressure_seed_shapes : ¬ Nat.Coprime 2 2 ∧ Nat.Coprime 2 3 := by decide

/-!
## §3. Route B — the intrinsic per-base ledger law: EXACT statement

### §3.1 The statement, verbatim (blueprint §3.2, Route B bullet)

> **Route B — the intrinsic re-scope (recommended target).** Replace the
> cross-base matching by the intrinsic per-base ledger law: for every δ and
> every position y the O_δ classifier REALIZES, a_δ(y) = δ · a_sym(letter_δ(y)),
> where a_sym is the letter's p-free symbolic exponent (the ℤ_p-side
> per-letter law is Theorem C's accepted conformance at q = p). Proof shape:
> (R1)–(R3) at base W(F_q) (H4-M1, all q at once) + M14's Theorem run against
> the SYMBOLIC skeleton (the letter's catalogue slot tree) instead of against
> the ℤ_p realization — the skeleton comparison is H4-M1's Lemma-1 leverage;
> NO cross-base dictionary and no δ-stability hypothesis remain. STATUS OF
> ROUTE B, exact (corrected at the Codex fold, finding 3): Route B does NOT
> discharge the rows AS STATED — the intrinsic law does not imply that
> realized positions are δ-stable, and the authoritative (UB-X)(b)/(K3-δ)
> texts quantify over stability. Route B is a REPLACEMENT obligation: it
> retires the current rows only through a ledger-level re-scope (per ROOT,
> riding the next O-11/O-8b touch) that substitutes the intrinsic law as the
> row content, with a displayed argument that the CONSUMERS (Step 16's
> alphabet-law scope; Step 18 K3-c's per-pool exponent reads) need exactly
> the intrinsic law. Until the ROOT owner lands that re-scope, nothing is
> discharged by a Route-B proof; the proof + re-scope brief travel together
> (H4-M5 + H4-M7).

### §3.2 Route B's Lean face: FENCED (H4-F5) — deliberately NOT landed here

The Route-B statement shape, for the record (prose display only; the fence
text verbatim): "the stability-free intrinsic exponent law (`∀ δ, ∀ x ∈
realized δ, aDim δ x = δ * aSym (letter δ x)` over a symbolic-exponent
carrier)". CARRIER CAUTION, displayed for the H4-F5 designer: `letter δ x`
here is the O_δ classifier's OWN realized letter — it is NOT automatically
the §7.2 `posLetter` (which, at a §7.2-conforming instance, returns the
designated OFF-DOMAIN letter at split prefixes, exactly the positions where
Route B's law must still read a genuine letter). Which letter carrier the
face uses is an H4-F5 design decision, made against H4-M5's proven note.
The face is fenced unit H4-F5 (blueprint §L.5): "Gated on H4-M4 selecting
Route B AND the ROOT re-scope landing; consumers re-point from
`UBXbStmt`/`K3deltaStmt` only then." This unit SELECTS Route B (§5) — the
FIRST of the two gates — and lands no face: declaring it now would invite
consumption before the ROOT authorization exists. L7/L8 remain the CURRENT
typed rows.

## §4. What the two routes cost and deliver (the comparison the call is made on)

| | Route A | Route B |
|---|---|---|
| statement | `K3deltaStmt` (per-pool δ-stability), (K3-δ)-only | intrinsic exponent law at realized positions, all δ (H4-F5 shape) |
| discharges as stated? | YES for the (K3-δ) row (fragment retires from clause (R)); (b) at FULL scope stays open | NO — REPLACEMENT obligation; retires (UB-X)(b)+(K3-δ) only through the ROOT re-scope |
| post-dictionary residue | realized per-pool coprimality (`k3delta_iff_pool_coprime`) at EVERY consumed (n, p, δ) — an open realization property; no structural mechanism on file forces it | (R1)–(R3) over W(F_q) (H4-M1, PROVED at its §0.4 perimeter) + M14's Theorem vs the symbolic skeleton (H4-M5 work, mechanism displayed in M14) |
| cross-base dictionary consumed? | YES (H4-M2 + its [IN-R1]/[IN-U]/`GcdSlice` conditionality) | NO |
| refutable by N-K3? | YES — one non-coprime realized pool kills it | only via an intrinsic-law violation (which escalates to (EQ-2) itself) |
| ROOT touch needed | none for the fragment (anticipated outcome) | YES — ledger statement change, ROOT owner's touch |

## §5. ADJUDICATION (with the dictionary in hand)

### §5.1 The blueprint's criterion

"Recommends B unless the dictionary lands a cheap A" (§3.2). "Cheap A" =
the dictionary's content alone closes Route A's per-pool obligation, leaving
only bookkeeping.

### §5.2 The cheap-A test: FAILS

With H4-M2 on file, Route A's obligation is exactly the right-hand side of
`k3delta_iff_pool_coprime`: every realized δ > 1 pool's accumulated residue
degree m is coprime to its pool index δ. Three reasons this is NOT cheap:

1. **It is a realization property, not a dictionary property.** M2 §5
   (residue item 5, verbatim): "Whether the O_δ classifier's REALIZED ledger
   contains a matched position with gcd(m, δ) > 1 at a given (n, p, δ) is
   the OPEN realization question of blueprint §3.2 — N-K3's empirical probe,
   nothing here settles it." The dictionary sharpened A's obligation; it
   cannot discharge it.
2. **The quantifier is theorem-strength.** (K3-δ) is consumed by clause (R)
   at EVERY degree n and every (p, δ) the assembled theorem touches. N-K3
   (n = 3) is a falsifier gate: a violation kills A, but a pass proves
   nothing beyond n = 3. A cheap A would need a STRUCTURAL coprimality
   mechanism (e.g. "continuation reads at accumulated degree D only realize
   child species with m coprime to D"); no such display exists in M1, M2,
   the pack notes, or the R11 β-leg design — and the F₉-shape species
   (m = δ = 2) exists abstractly at every even D, so any such mechanism
   would have to be a genuinely new realization theorem. Grading that lemma:
   it is (UB-X)(b)-realization content — the very thing §3.2 found unposed.
3. **Route A inherits the dictionary's full conditionality** ([IN-R1] —
   M1's perimeter row; [IN-U] MacLane-uniqueness, literature-pinned, pin
   precision still a LITUNIT duty; the `GcdSlice` rows' Lean discharge
   fenced at H4-F6) PLUS the realization residue. Route B consumes none of
   the cross-base chain.

### §5.3 N-K3's verdict feeds the call — branch table (the call is robust)

N-K3 (blueprint §N): enumerate the n = 3 pack's verdict-row β-legs' δ > 1
pools; check each realized pool against Lemma 4's gcd criterion AND against
Route B's intrinsic exponent law. Sealed predictions per the standing
falsifier discipline; M2 §4's decide-checked tables are the seed.

ON-FILE STATUS at composition time (repo search, 2026-08-01): NO N-K3 run
artifact exists (`verification/openmath/` has no N-K3 script/results; the
only N-K3 material is M2's seed tables). The route call is therefore issued
in BRANCH-ROBUST form. The branches are NOT mutually exclusive (one run can
trigger several; Codex read, finding 2) — they are ordered by PRECEDENCE:
check (iii) first, then (i), then (ii); folding the verdict means applying
the FIRST branch that fires, with re-adjudication needed only on (iii):

- **(iii) [dominates] N-K3 finds an INTRINSIC-law violation (a_δ ≠ δ·a_sym
  at a realized letter, at any position, stable or not):** Route B is
  REFUTED AS STATED, and the adjudication RE-OPENS — with NO automatic
  fallback to Route A. The blueprint's own §N disposition, verbatim: "A
  violation of the INTRINSIC law refutes Route B (and (EQ-2) itself —
  escalate)". Honest scope of that escalation (Codex read, finding 1): a
  violation at a STABLE realized position contradicts (EQ-2)'s own
  conclusion read at the letter (there a_δ = δ·a₁ and letter_δ = letter_1,
  so the intrinsic law is (EQ-2)'s restatement) — that impeaches O-8b's law,
  the very thing (K3-δ) exists to deliver to K3-c, so Route A's target loses
  its consumer value even if A's stability condition itself survives; a
  violation at an UNSTABLE position refutes only the intrinsic EXTENSION,
  leaving (EQ-2)-at-stable-classes untouched — Route A then remains
  formally available and the re-opened adjudication weighs it against a
  repaired Route B. Either way: stop, re-adjudicate; nothing is forced.
- **(i) N-K3 finds a realized pool violating the gcd criterion (and no
  intrinsic violation in the run):** Route A is REFUTED outright
  (`not_k3delta_of_noncoprime_pool` fires at the witness). Recommendation B
  stands — "forced" only in the sense that A is dead; B's own standing is
  untouched by this branch.
- **(ii) N-K3 passes (all realized pools coprime, intrinsic law exact):**
  Route A gains n = 3 empirical support only; §5.2's reasons 1–3 stand
  untouched (the all-n obligation and the realization residue remain).
  Recommendation stands: B.

### §5.4 Consumer evidence (adjudication-grade; the binding walk is deferred)

STATUS OF THIS SECTION (Codex read, finding 3): what follows is EVIDENCE at
adjudication grade, from the consumer texts on file — it is NOT the displayed
consumer-need argument the Route-B re-scope requires. That argument (an
exact-text, quote-by-quote walk of Step 16 and Step 18 establishing that the
consumers need exactly the intrinsic law) is H4-M7's duty; the
recommendation of §5.5 rests on §5.2 and does NOT presuppose this section's
claim at full strength.

- O-11 §3.4 (K3-c), the row this fragment serves — its need as stated
  (quoted verbatim, §1): "the re-based classifier obeys the same
  digit/alphabet laws with a_δ = δ·a₁" — an exponent law at the classifier's
  OWN reads, with no stability quantifier in the row text. Stability enters
  only because O-8b/M14's proof is DECLARED at δ-stable classes (ROOT §3.1
  (R1)–(R4) row, quoted §1). Reading: (K3-δ) exists to bridge a SCOPE
  MISMATCH between the law's declared hypothesis and its consumption site.
- Step 16's alphabet-law scope: asserted here from the blueprint §1
  consumption map only ("(H4a) → Step 16 (O-8b: the alphabet law at
  δ-stable classes …)"); its exact text is NOT walked in this note — an
  open item for H4-M7, displayed as such.

Route A KEEPS the mismatch and certifies the bridge pool-by-pool; Route B
dissolves it at the source (the law re-proved at realized positions, no
stability hypothesis to supply) — IF the M7 walk confirms the reading above.

### §5.5 RECOMMENDATION

**ROUTE B.** Per §5.2 the dictionary does not land a cheap A — this alone
settles the blueprint's criterion; per §5.3 the call is robust in N-K3's
pending verdict (modulo the dominating escalation branch); §5.4's consumer
evidence corroborates without being load-bearing. Route A is retained
on the record as the fallback ONLY if the ROOT owner declines the re-scope
(in which case its obligation is the displayed realization lemma of §5.2
reason 2 — priced honestly as new open content, not bookkeeping).

## §6. ROOT-SYNC NOTE (for the ROOT owner — this unit drafts, never self-serves)

A Route-B adoption is a LEDGER STATEMENT CHANGE, ROOT owner's touch, per the
standing rule (§M row, verbatim). Exactly what changes and in what order:

1. **The row texts.** (UB-X) member (b) ("δ-stable position classes exhaust
   the realized ledger at every δ") and the (K3-δ) fragment's content are
   REPLACED by the intrinsic per-base ledger law (§3.2's display) as the row
   content — a substitution, not a weakening-in-place: the old stability
   quantification is WITHDRAWN as a row, and the withdrawal must be
   displayed so no consumer silently keeps reading stability. Clause (R)'s
   attribution re-points from (K3-δ) to the intrinsic law at K3-c's pools.
2. **The authorization precedes any discharge claim** (blueprint Wave plan,
   finding 10): until the re-scope lands, NOTHING is discharged by a Route-B
   proof. H4-M5's proof and H4-M7's re-scope brief travel together; the
   brief must carry the displayed consumer-need argument (§5.4's sketch,
   executed against Step 16's and Step 18's exact texts).
3. **Lean faces.** L7/L8 (`UBXbStmt`/`K3deltaStmt`, Route-A-shaped) remain
   the CURRENT typed rows throughout; H4-F5 (the Route-B face) unfences only
   after BOTH gates (this recommendation accepted + re-scope landed);
   consumers re-point only then. H4-F2 (the `RealizedLedger` value-side
   instance) was gated on this adjudication: under Route B it should be
   designed against the H4-F5 shape, not the pool-stability shape.
4. **Rides the next O-11/O-8b touch** (per ROOT's own (R1)–(R4) row: "the
   match display (or a re-scope) rides the next O-11/O-8b touch and would
   retire (K3-δ) from clause (R)"). The REL.2(e) seam is UNTOUCHED by the
   re-scope ((e1)–(e5) type the pools' presentation, which both routes
   consume identically); its CL-8/[2r] owners should be notified, not
   tasked.
5. **N-K3 remains owed** regardless of route: under B it is the intrinsic
   law's falsifier gate (branch (iii) = stop-the-line), and H4-M5's gate
   consumes its sealed predictions.

## §7. Consumption map, gate record, declaration list

CONSUMED: H4-M2 (`H4M2_dict_attempt.md`: DICT-1, `stable_iff_coprime`
chain, §4 F₉ instance, §5 residue list) — via the `DictSlice` interface,
each use displayed; O-11 §3.4 (K3-c) row text; ROOT (UB-X)/(R1)–(R4) row
texts; blueprint §3.2 route texts (verbatim above); H4-L7/L8 typed faces
(by import); H4-M1's resolution (status input to §5.2 only). NOT consumed:
REL.2(e) internals; the n = 3 pack's realization data (N-K3's business); any
Route-B proof step (H4-M5's business).

GATES: (1) `lake env lean notes/openmath/H4M4_k3delta_adjudication.md` —
GREEN, zero sorry (this file, re-run after every fold edit). (2) Codex
adversarial read — PASS 1 RAN (2026-08-01, gpt-5.6-sol, fresh context,
quote-and-classify charge): verdict REVISE — 2 CRITICAL + 1 GAP, all in
§5.3/§5.4, all ACCEPTED and FOLDED IN PLACE: [C1] branch (iii) overclaimed
"both routes dead" + an unconditional (EQ-2) refutation → branch rewritten
with the blueprint §N disposition quoted verbatim and the escalation's
honest scope split by the violating position's stability (no automatic
fallback, no overclaim); [C2] branches not mutually exclusive → precedence
ordering displayed ((iii) dominates, then (i), then (ii)); [G3] §5.4's
consumer-need claim not displayed at full strength → section re-graded to
adjudication-level evidence, Step-16 walk displayed as an H4-M7 open item,
and §5.5 re-weighted so the recommendation rests on §5.2 alone. Codex pass
1 also confirmed: both route statements transcribed accurately; no
countermodel or discharge claimed; the Lean declarations match the prose;
[M]-content stays hypothetical; H4-F5 not landed; ROOT-sync authorization
fence correct. PASS 2 (on the folded text): verdict recorded below. N-K3
is NOT this unit's gate (it seals M4/M5 jointly); its on-file status and
branch handling are §5.3.

DECLARATION LIST (all in `LeanUrat.Scaffold.HDischarge.H4.Adjud`, this
file, zero sorry): `DictSlice`, `k3delta_iff_pool_coprime`,
`ubxb_iff_realized_coprime`, `not_k3delta_of_noncoprime_pool`,
`not_ubxb_of_noncoprime_realized`, `not_ubxb_of_not_k3delta`,
`pressure_seed_shapes`. Every theorem is proved outright (no sorry, no new
axiom); the [M]-semantic content stays in NAMED hypothesis position
(`DictSlice` arguments), never discharged by fiat.

AXIOM FOOTPRINT (external `#print axioms` run, 2026-08-01): Lean-core only —
`k3delta_iff_pool_coprime`, `ubxb_iff_realized_coprime`,
`not_k3delta_of_noncoprime_pool`, `not_ubxb_of_noncoprime_realized`,
`not_ubxb_of_not_k3delta` each at {propext, Classical.choice, Quot.sound};
`pressure_seed_shapes` axiom-free; `DictSlice` a def.
-/

end LeanUrat.Scaffold.HDischarge.H4.Adjud
