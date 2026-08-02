# K1CANON_discharge — the (K1-CANON) warrant note (H9-C1)

**Unit:** the (K1-CANON) discharge per `lean/blueprints/HDISCHARGE_H9.md` §3
(the Codex-restructured route: M04-side SCOPE PIN DISPLAY, guard-in-statement).
**Written:** 2026-08-02 machine clock. *Dating convention [g-A round-1
finding 1, folded]:* this campaign's ledger entries carry SESSION labels
(2026-08-05/-06) that run AHEAD of the machine clock (2026-08-01/-02) — the
same skew the H9 blueprint itself displays ("Written: 2026-08-01 machine
clock (the 2026-08-05-dispatch session)"). Temporal provenance is the
ledger's APPEND-ONLY ORDER, not the wall-clock labels: the standing-authority
entry ("ASVIN SIGN-OFF + STANDING AUTHORITY", ledger line ~1900) precedes
this unit's dispatch and this note in that order. No future-dated authority
is consumed.
**Role of this note:** it SUPPORTS the authority gate and the hostile pass; it
is NOT itself the discharge. The discharge event is the (ed-1) edit APPLIED +
the hostile pass CLOSED + the authority gate (g-B) — the discharge is
COMPLETE only when the gate record at the end of this note shows all four
gates closed, and the ledger entry is appended only after that record is
filled.

**Authority (g-B).** The blueprint priced g-B as an Asvin sign-off naming the
exact diff (statement fence). This discharge rides Asvin's STANDING
statement-change authority (ledger entry "ASVIN SIGN-OFF + STANDING
AUTHORITY", complete verbatim [g-A round-2 GAP folded — the full sentence,
including its occasioning first clause]: "sign-off granted on the
DictIII.FRESH restatement - in general, as long as the lean proof is on track
without introducing fake axioms or contradictions etc, go for it";
adjudicated scope:
statement-level changes proceed without per-item sign-off provided (a) no new
axioms outside the policy loop, (b) no vacuity/contradiction, (c) the
honest-pricing invariant — never weaken to prove) and is **SURFACED FOR
ASVIN'S REVIEW** per that entry's own rider ("Consequential statement changes
still get SURFACED in reports after the fact"): the exact applied diffs are
displayed verbatim at §D below. Scope honesty: the adjudicated wording says
"Lean statement-level changes"; this edit is a NOTE-side statement change
(M04 §5.5, an open kernel's displayed scope) — the dispatching orchestrator's
charge extends the authority to exactly this edit, and the surfacing rider is
honored: if Asvin rejects on review, (ed-1) reverts and (K1-CANON) re-opens.
The edit is a scope RESTRICTION (honest pricing of what K1's quantifier was
always consumed as), not a weakening of any proved claim: K1 is an OPEN
kernel (OL-1), no proof of it exists to weaken, and both consumers of the K1
regrouping (C1-1) read the pinned corpus already.

---

## C1-0. Claim + bookkeeping (layer discipline up front)

The premise being discharged (verbatim, ROOT §3.1 (H9) row / HDISCHARGE_H9
§3.1):

> **(K1-CANON)** — at every consumed Step-18 site, K1's "canonical tree"
> denotes (q-4)'s pinned notion; equivalently (the interface-lemma form),
> every tree at which the mandatory path invokes K1 satisfies the
> all-leaves-(τ-irr)/(τ-hen) guard.

**The discharge event** := the (ed-1) edit (§D) applied under the g-B
authority + the g-A hostile pass. Nothing in this note is a derivation of the
premise from the quotes on file — the interface-lemma-only route was WITHDRAWN
at the blueprint's Codex review (HDISCHARGE_H9 §3.5; findings 2/3/4/5): the
central range identity ("the post-K4 sum's index set = the pinned/carrier
corpus") is NOT derivable from the displayed quotes, and (q-4) was
already-on-file evidence when pass-1 gap 5 was filed and adjudicated
insufficient. The missing range display is therefore SUPPLIED AT THE SOURCE by
the edit.

**Layer discipline (review finding 5, honored throughout):** the as-built leg
(the Lean `bridgeTree` carrier, C1-3) and the intended/paper leg (M04's K1
quantifier, C1-2/C1-4) are argued SEPARATELY. No inference in this note
crosses from `bridgeTree` to M04's paper-level quantifier or back; the (ed-1)
parenthetical MENTIONS the carrier only as the wired instance of the pinned
notion, with the compiled units cited under their exact billing (C1-3).

**The interface quotes consumed as CONTEXT (verbatim from D-11 r4 §4; they are
context, NOT proof — none of them derives the range identity):**

* **(q-1) [the bundled predicate — O-1thr §1.4]:** "**decided ns-free** :=
  every maximal chain is a (τ-irr) leaf and the Hensel payload covers the
  simple part — no ns-marks"; and the ns-halt is a MARKED halt: "(τ-ns) —
  write **NsHalts(o, f)** := o is a REALIZED non-saturated state whose window
  has no principal face on f — the ns-halt, MARKED". (Classification trees
  carry "leaf verdicts, and ns-marks" in the vocabulary.)
* **(q-2) [the counted corpus — O-1thr Theorem 3(c)]:** "D_σ(N) := #{x
  level-N : fiber(T, x) for some decided ns-free T with type(T) = σ and
  thr(T) ≤ N}" — decided-ns-free-quantified IN ITS DISPLAYED DEFINITION, and
  the whole package scoped there: "Throughout: T decided ns-free, t :=
  thr(T), fibers per §1.4" (Theorem 3's opening line).
* **(q-3) [the K1/K4 corpus quantifier — the TREE-N/TREE-EXP source scope,
  quoted on file at M02]:** "The note's TREE-N … is stated for trees
  'complete finite realizable with all leaves (τ-irr)/(τ-hen)' — the ns
  leaves are excluded; the machine-checked discharge candidate `treeN`
  (E11_treeN.lean) carries `hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H`". M04's K1
  quantifies over "each complete finite realizable canonical tree" (= this
  source scope) and its K4 reads "`bridgeMass` T … equals μ(fiber T) —
  level-exact cylinder reading; plus (ns-null) excluding infinite trees".
* **(q-4) [the interface pin — the ClassifierSpec docstring,
  `MovesU/Defs.lean`]:** "`canonical`: T_can^τ's verdict-type map … **`some
  σ` = complete finite realizable tree, all leaves (τ-irr)/(τ-hen),
  certified at level N (thr ≤ N)**"; and the counts are DEFINED from it
  ("decided_σ(N) — DEFINED from the canonical map (never a free field)").
* **(q-5) [what the partition identity actually is — M04 Theorem 2, proof
  step (a)]:** "At each level N the verdict map f ↦ canonical N f partitions
  the p^{nN}-element box into the σ-fibers and the none-fiber:
  Σ_σ decided_σ(N) + undec(N) = p^{nN}" — TRUE FOR ANY Option-valued map; it
  routes NOTHING. The routing content lives in (q-4), not in the identity.
* **(q-6) [the intended drainage — O-1thr Remark 4]:** "The ns-free
  hypothesis is NOT removable: an exact-square family (n = 2: classes of
  (X − b)², v_p(b) = 1 held to level N) fibers an ns-marked tree whose
  counts scale by p, not p² — the countermodel is PARI-verified in the
  source campaign. Undecided/ns loci drain into the undecided envelope
  instead; their treatment is the drainage node, not this package."

---

## C1-1. The closed K1 invocation-site list (= I-2's K1 restriction)

* **(s-a)** ROOT Step 18's K1 line (`docs/ROOT_ASSEMBLY_2026-08-02.md`, the
  Step-18 display: "K1 ← O-10 (guarded) + (I-τ)→GD … + the Lemma-3.3
  shallow-cut regrouping … + the ns-ROUTING of K1's labeled corpus at (H9) =
  (NSF)") — consumes exactly the Theorem-4 regrouping that (s-b) displays.
* **(s-b)** M04 §5.5 Theorem 4's proof step: "K4 turns the LHS into
  Σ_{T type σ} μ(fiber T). K1 + Lemma 3.3 turn it into the shallow
  convolution" (the SOLE in-proof K1 consumption; K1 is invoked exactly once,
  immediately after K4, at that sum).

Identity with the D-11 r4 §4A walked closure: §4A's walk closed the
corpus-consuming sites to {K1 (M04 §5.5 (K1) + Lemma 3.3), K4 (M04 §5.5 (K4) +
D-15 = O-1thr Thm 3(b)/(c))} — the K1 restriction of that list is exactly
{(s-a), (s-b)}. Closure is RELATIVE to the walked corpus, i.e. to the residue
**(CH-RES)**; no stronger completeness is claimed (crux x-1).

---

## C1-2. The no-loss warrant (why the edit loses no consumed instance)

With the pin, K1's narrowed quantifier + the pinned Σ-reading still supply
every use on file:

* Theorem 4's proof consumes K1 exactly once, immediately after K4, at the sum
  "Σ_{T type σ} μ(fiber T)" — and (ed-1)(b) pins THAT SAME SUM to the same
  corpus in the same edit. The regrouped object and the quantifier's range are
  pinned coherently; no proof line in §5.5 applies K1 to any tree outside the
  pinned corpus.
* ROOT's Step-18 K1 line consumes the same regrouping (it cites the M04
  Theorem-4 walk), already priced at (H9) = exactly the ns-routing of K1's
  labeled corpus; the pin is what that price always presupposed.
* Lemma 3.3 (§5.4) is untouched: its hypothesis is the weight-preserving
  bijection, owned by (H8′)/the K-CUT package, a DISJOINT object (see the H8
  coordination check, gate g-C).

**The residual, displayed honestly (review finding 3; crux x-3):** that the
paper sum "Σ_{T type σ}" was ALWAYS INTENDED over the labeled corpus is
exactly what the edit STIPULATES at the source. It is a scope DECISION by the
kernel's owner (K1 = OL-1, the project's own open kernel — its statement scope
is the note owner's to fix under the statement fence), WARRANTED — not proved
— by (q-4)'s decided_σ definition ("DEFINED from the canonical map, never a
free field") and by series_tie's LHS being built from decided_σ. This note
does NOT present the range identity as a derivation.

---

## C1-3. The as-built conformance leg (compiled; `bridgeTree` layer ONLY)

At the wired instance (no inference to the paper layer — display only):

* the carrier's third conjunct: `bridgeTree n p σ = {V // V.typemult = σ.1 ∧
  RealizedSelf n p V ∧ MovesT.NsFree V}` (`BridgeD3_treeCarrier.lean:94–96`,
  Unit C), with `bridgeVt_nsFree` the compiled projection;
* **H9-U5** `bridgeVt_maximal_irrHalts` (probe-proved, landed:
  `Scaffold/HDischarge/H9/NsfKeyProp.lean`): every CARRIED tree has all
  maximal chains IrrHalts;
* **H9-U3** `nsFree_iff_maximal_irrHalts` (same module): at `fiberAt`
  witnesses, `NsFree` ⟺ all-maximal-chains-IrrHalts.

**Billing (review finding 6, verbatim discipline):** these compile the guard's
MARK COMPONENT only — complete/finite/canonical are `VTree` structural fields
(the carrier docstring's "BY CONSTRUCTION"), realizability is `RealizedSelf`,
and the (τ-hen) content is the `henV` payload (`hhen`'s (1,g)-shape), not a
chain; the FULL (q-3) package at the carrier = structure fields +
`RealizedSelf` + U5 + payload shape. NO claim that U3/U5 alone supply the
whole guard. (Non-vacuity caveat carried from the blueprint §5.2: no compiled
element of `bridgeTree` exists at HEAD; U3/U5 are conformance witnesses, not
existence claims.)

---

## C1-4. What the edit discharges

After (ed-1), K1's "canonical tree" denotes the pinned notion BY DISPLAY AT
THE SOURCE at every consumed site — both C1-1 sites read §5.5 ((s-b) IS §5.5;
(s-a) cites §5.5's Theorem-4 walk) — so the (K1-CANON) display holds; and the
(q-3)-scoped source lemmas' proved range (TREE-EXP/TREE-N, `hdet`-guarded)
covers the now-displayed consumed range. Layer discipline: this is the
intended/paper layer, discharged by the authorized edit; the as-built layer is
C1-3's compiled record; no cross-layer step exists or is needed.

---

## C1-5. Honest cruxes for the verifier

* **(x-1)** the invocation-site closure (C1-1) is (CH-RES)-relative — closed
  against §4A's walked corpus, not absolutely.
* **(x-2)** U3/U5 operate at `fiberAt` witnesses = the carrier's
  `RealizedSelf` scope, no broader.
* **(x-3)** the scope pin is a STIPULATION under the statement fence, priced
  as a statement change with a no-loss warrant (C1-2) — the note claims no
  derivation of the range identity.

---

## §D. The applied (ed-1) diff, verbatim (SURFACED FOR ASVIN'S REVIEW)

File: `lean/notes/openmath/M04-series-tie_fable.md`, §5.5 only. Three
sub-edits; §5.4 Lemma 3.3 and everything else byte-identical.

**(ed-1)(a) — K1's statement, the scope parenthetical.** Old:

> each complete finite realizable canonical tree's fiber mass factors as the
> grammar weight of its derivation,

New:

> each complete finite realizable canonical tree's (canonical tree := (q-4)'s
> pinned notion — complete finite realizable, ALL leaves (τ-irr)/(τ-hen), the
> (q-3)/TREE-N scope; at the wired instance the `bridgeTree` carrier, whose
> `MovesT.NsFree` clause equals this guard's MARK COMPONENT at realized trees
> [H9-U3/U5]) fiber mass factors as the grammar weight of its derivation,

**(ed-1)(b) — Theorem 4's proof display, the pinned Σ-reading.** Old:

> *Proof.* K4 turns the LHS into Σ_{T type σ} μ(fiber T). K1 + Lemma 3.3 turn
> it into the shallow convolution of the numeric B's.

New:

> *Proof.* K4 turns the LHS into Σ_{T type σ} μ(fiber T) (the sum over the
> SAME pinned corpus — the carrier's type-σ trees). K1 + Lemma 3.3 turn it
> into the shallow convolution of the numeric B's.

**(ed-1)(c) — the §5.5 preamble line.** Inserted between the §5.5 heading and
Theorem 4:

> *Scope pin [(K1-CANON) discharge, ed-1(c), 2026-08-02]:* throughout this
> subsection "canonical tree" and the type-σ tree corpus denote (q-4)'s pinned
> notion — complete finite realizable, ALL leaves (τ-irr)/(τ-hen), the
> (q-3)/TREE-N scope (provenance of the pin: D-11 r4 pass-1 gap 5 / pass-2
> gap 3; discharge record `K1CANON_discharge_2026-08-02.md`; HDISCHARGE_H9 §3).

---

## Gate record (g-A..g-D per HDISCHARGE_H9 §3.4)

* **(g-A) hostile Codex pass on the package (note + applied diff):** fresh
  context, charge = quote-and-classify, verify (a) C1-1 = I-2's K1
  restriction, (b) the no-loss warrant's honesty, (c) the layer discipline,
  (d) U3/U5 billing, (e) the pin matches (q-4) verbatim, (f) no consumer
  silently broken. **RESULT — ROUND 1 (2026-08-02 machine clock; raw output
  `/tmp/openmath/K1CANON/gA_out.txt`): REJECT-WITH-FINDINGS, 2 CRITICAL, both
  bookkeeping-level; the substance passed explicitly** ("Checks (a)–(f)
  otherwise pass: the site list is exact, the range identity is consistently
  presented as a stipulation, layer separation and U3/U5 billing are
  respected, the pin matches the sanctioned wording, and Lemma 3.3 is
  untouched"). Finding 1 (authority "future-dated"): folded — the dual
  machine-clock/session-label dating convention + append-only-order
  provenance now displayed in the header. Finding 2 (gate record a
  placeholder while the note read as complete): folded — the discharge-event
  wording now conditions completion on THIS record being filled, and the
  ledger entry is appended only after it. **ROUND 2 (confirmation pass on the
  folded text): result recorded at the end of this section.**
* **(g-B) authority:** the standing statement-change authority per the header
  paragraph — diffs surfaced at §D for review. Honesty check: scope
  restriction of an OPEN kernel's quantifier to its always-consumed range; no
  axiom, no contradiction, no proved claim weakened; consumers verified at
  C1-2.
* **(g-C) execution:** (ed-1) applied (§D); Theorem 4's text re-read coherent
  (the pin, the quantifier, and the Σ-reading name the same corpus; Honesty
  inventory and OL-1..OL-4 unchanged — K1 remains OPEN, now at pinned scope).
  H8-coordination check: HDISCHARGE_H9 §3.4's flag honored — the H8 fleet
  completed (11/11) WITHOUT editing M04 (git history of
  `M04-series-tie_fable.md`: untouched since e5cd6b1, pre-blueprint); (ed-1)
  does not touch Lemma 3.3's hypothesis (the (H8′)-owned object); no edit
  collision. Companion compile gate: `lake env lean
  LeanUrat/Scaffold/HDischarge/H9/NsfKeyProp.lean` re-run this session,
  EXIT=0, no output — the cited H9-U3/U5 stand at HEAD.
* **(g-D) ledger:** the (K1-CANON) DISCHARGED entry + the H9-C3 (NSF-INT)
  retirement adjudication, to be appended to
  `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` only AFTER the round-2
  result below is recorded [tense corrected per round-2's quote — the append
  is downstream of this record, never before it].

**(g-A) round-2 result (Codex, fresh context, folds-only charge + fresh
sweep; raw output `/tmp/openmath/K1CANON/gA2_out.txt`):** F1-check **PASS**
("Given the stipulated ledger ordering, the authority entry precedes the
entries dispatching this unit… honestly explains why the displayed dates are
not temporal provenance"). F2-check: flagged CRITICAL **against the reviewed
snapshot** — the round-2 slot was necessarily a placeholder in the text the
verifier saw (no pass can be recorded before it runs), and g-D's past-tense
"was recorded" contradicted it. LEAD ADJUDICATION of that finding: the tense
slip is REPAIRED above (g-D now conditions the append on this record), and
the slot is FILLED by this very paragraph — the structural self-reference
(a pass cannot see its own result pre-recorded) is resolved the only way it
can be: record-after-run, append-after-record. The verifier's own words
grant the frame: "the general completion condition is now stated correctly."
One GAP (the "verbatim" label on a truncated authority quote) folded at the
g-B paragraph (complete sentence now quoted). Substance across both rounds:
all six charged checks PASS; zero findings against the (ed-1) diff, the site
list, the stipulation pricing, the layer discipline, the billing, or any
consumer. With the two rounds run, all findings folded, and this record
filled, gates g-A/g-B/g-C are CLOSED; g-D (the ledger append) executes
next, after this file is saved.
