# O-14a′ Phase-B attempt, REV 3 (RESCOPE) — the RunRealizerExists residue: verified core + the demoted general-F law

**Leaf** (docs/MATH_COMPLETION_TREE_2026-08-01.md, D-10 split of O-14; §D1.6 critical-path
step 1): the open residue of `RunRealizerExists` — (a) the (S6b′) monomial-shape support
clause at deg Φ > 1, (b) the last-node (terminal) flank.
**Round-4 action** (2026-07-31 late): RESCOPE, per the round-4 protocol (repeated UNSOUND
rounds with repair-introduced defects ⇒ retreat to the stable verified core). Responds to
the hostile verification V15 (`V15_o14apr2.jsonl`, verdict UNSOUND on the rev-2 package;
findings classified below). Supersedes rev 2 (`O14ap_phaseB_attempt_rev2.md`) as the
statement of record; revs 1–2 retained for the audit trail. Companion self-contained
verifier package: `O14ap_phaseB_verifybrief_rev3.md`.
**Author**: Phase-B prover unit O14ap. **No Lean edits**; math + records only.
**Falsifier suite**: `O14ap_check.py` — ALL PASS (16/16; rev-2 checks A–G byte-unchanged;
round-3 additions H1–H2 = the WITHDRAWAL certificate: the verifier's evading class for the
rev-2 void claim is real and populated).

---

## Round-3 findings classification (the churn audit; every V15 finding, no silent drops)

Protocol: classify each finding as (a) repeat/deepening of an old gap, (b) NEW defect
introduced by the round-2 repairs, or (c) fresh discovery in a previously-confirmed
section. If (b) dominates, rescope rather than patch again.

| # | V15 finding (gist, quoted) | V15 class | Round-4 class | Disposition |
|---|---|---|---|---|
| 0 | "The repaired scale calculation is correct … (THR) is derived correctly, including the previously missing factor e★ … The scale repair succeeds at every actual recursive ascent covered by (U) … There is no remaining w/wPrev scale error here." Also: Prop 5.4.2 "sound within its explicitly stated shaped class." | (confirmations) | — | RETAINED as proved: (THR), the threshold clearing via Lemma 5.4.0, Proposition 5.4.2. These stay theorems in rev 3. |
| 1 | "The universal void conclusion does not follow … Proposition 5.4.3 rules out only descend polynomials having a nonzero coefficient ψ_k with e ∤ (g−k). A stretched frame can evade the clash when every nonzero coefficient occurs in a congruent degree class … z²+1 is irreducible over 𝔽₃ … sparse irreducibles whose nonzero exponents satisfy k ≡ g (mod e) evade the argument." | CRITICAL | **(b)** — the void/exhaustiveness argument was CREATED by the round-2 repair (rev-2 §5.6/brief Prop 5.4.3 consequence) to justify the (U) scoping; it did not exist in rev 1. | **WITHDRAWN in full** (brief §5.4 "Withdrawal" block). The conditional divisibility implication — which V15 confirmed — is retained as the restated Proposition 5.4.3. The evading class is recorded and machine-checked (checks H1–H2). The honest fenced-perimeter fact replacing the void claim is the new Proposition 5.4.4 ((U) automatic under the fence + intended base pin), whose clause chase is the same one V15 itself displayed as "sound" (its fence-based obstruction paragraph). |
| 2 | "The formal index r initially indexes stages, including stages separated by recentering transitions, but the induction later treats r−1 as the preceding field-extension/read level … Remark 5.4.R supplies transport calculations but never formally defines the collapsed read-level indexing … the induction as written needs a precise reindexing or a separate recentering case." | GAP | **(b)** — rev 2's rebuilt induction added the recentering-collapse device (Remark 5.4.R / attempt Remark 5.3.1) without the formal reindexing; rev 1's induction did not have this structure. | **ABSORBED INTO DEMOTION**: named open lemma **OL-1** of Conjecture 5.4.C. The transport computations (uncontested by V15) are demoted from proof component to design material; they remain on file in rev 2 §5.3/Remark 5.3.1 and are cited as such, claimed nowhere. |
| 3 | "Definitions 1–3 do not state that the base wPrev-normalization sends p to 1, that arbitrary elements of K₀ have constant unit lifts with the asserted digit, or that wPrev₀(Φ₀) = 0 … the brief claims that only (F1) remains externally consumed. That claim is too strong." | GAP | **(b)** with an (a) root — the base case consumed these facts silently in rev 1 too, but the false "only (F1)" FLAG CLAIM is rev 2's (it retired (F2) and overclaimed the remainder). | **ABSORBED INTO DEMOTION**: named open flag **OL-2** — the base normalization package (F0-a) (wPrev₀(p^W·û) = W with prescribed leading digit at position 0) and (F0-b) (wPrev₀(Φ₀) = 0) is now flagged alongside (F1); the "only (F1)" sentence is withdrawn. |
| 4 | "A stretched σ₀ is permitted by Definitions 1–3 and is not created by any transition. The intended base has pair (1,1), but Proposition 5.4.3 is worded for a stage of a coherent history generally." | overstatement (within the critical item) | **(b)** — part of rev 2's new stretch-provenance paragraph. | **REPAIRED**: the rev-3 stretch definition states the base frame is unconstrained by Definitions 1–3 and pins σ₀.e = 1 only as a flagged instance property; Proposition 5.4.4 carries that flag as an explicit hypothesis. |

**Tally: 4/4 findings are class (b)** — every defect lives in material the round-2 repair
added; zero findings in the twice-verified core (§§1–4, §5.1–5.3: confirmed by V11,
undisturbed by V15). The §5.4 general-F layer has now produced a critical error in two
consecutive rounds from two different mechanisms (rev-1 scale seam; rev-2 exhaustiveness
argument). That is churn, and the protocol verdict is RESCOPE: keep the stable core as
the theorem set, demote the churning layer to a labeled conjecture, stop patching.

---

## 0. Verdict summary (rev 3 — the rescoped statement of record)

1. **THEOREM (last-node flank; twice-stable).** At every coherent history whose final
   node is a recentering, a center realizer ((CR1)+(CR3)) exists, from bare coherence
   alone — the threshold is derived at the run anchor (Lemma 3.1) and transported along
   the recentering run (Lemma 3.2). [V11 CONFIRMED; V15 no findings; byte-stable.]
2. **THEOREM (prime-field collapse + Corollary 4; twice-stable).** `RRE(p, ZMod p)` —
   the exact statement the critical path consumes — holds for every prime p under the
   current (RG-2-fenced) coherence predicate; (CR2) is free at F = 𝔽_p because every
   frame key is linear. [V11 CONFIRMED; V15 no findings; byte-stable. FORMALIZED:
   `MovesD/R7_runRealizer.lean`, `runRealizerExists_zmod`, Lean-core — the consumed
   instance is machine-checked independently of everything below.]
3. **REFUTATION (general F; twice-stable).** The compiled singleton-support clause
   (CR2) is REFUTED-AS-STATED at deg Φ > 1: the F₉ inert-quadratic countermodel (center
   of order 8 vs the order-4 monomial digit coset). [V11 CONFIRMED arithmetic + honest
   conditionality flag; V15 no findings; byte-stable.]
4. **PROVED FRAGMENTS of the §5.4 layer (V15-ratified, now stated as theorems):**
   Lemma 5.4.0 (general steepening), (THR) (the threaded slot law), Proposition 5.4.2
   (sharpness at every g within the shaped class), Proposition 5.4.3 (stretched-frame
   display obstruction, CONDITIONAL form only), and NEW Proposition 5.4.4 ((U) is
   automatic on the fenced perimeter given the flagged base pin σ₀.e = 1).
5. **CONJECTURE 5.4.C (the stretch-threaded support law (S6b′-SUPP-2) on class (U)) —
   DEMOTED from rev 2's Theorem 5.4.1.** Scale-verified design (V15 §1), two named open
   lemmas (OL-1 read-level indexing; OL-2 base normalization (F0-a)/(F0-b)), full
   falsifier suite attached (checks A, E, G, H + the recorded-lift bookkeeping witness).
   Claimed nowhere; consumed by nothing on the tree's mandatory path (audit below).
6. **WITHDRAWN (rev-2 claims struck by this rev):** (i) "the complement of (U) is a
   definitional void / (U) is the entire statable domain" (rev-2 §5.6 consequence and
   the corresponding §0 items 3 and 5 of rev 2); (ii) "every stretched frame arises
   from a non-recentering transition"; (iii) "(F1) is the only externally consumed
   intended-apparatus fact". Each withdrawal is displayed in the rev-3 brief at the
   point of use.

Grade requested: **RESCOPED** (not REPAIRED): the churned layer is no longer asserted;
everything still asserted has survived two hostile passes or is new-this-round with
proofs from the displayed clauses only (Propositions 5.4.3-restated and 5.4.4 — the
short clause chases V15's own report already exhibited as sound).

---

## 1. DELTA-1 consumption audit (what the mandatory path actually needs — checked)

The tree's mandatory-path obligation for this leaf (docs/MATH_COMPLETION_TREE_2026-08-01.md
§D1.6, attack order item 1, node D-10/O-14a′) is verbatim: *"close or remove the (S6b′) +
landing-flank residue"*. Disposition against the rescoped claim set:

* **Landing flank: CLOSED.** Theorem 3 (twice-stable), unconditionally from coherence.
* **The (S6b′) monomial-shape clause: REMOVED-as-stated + REDUNDANT-as-consumed.** At
  general F it is refuted (the F₉ countermodel — twice-stable), so no faithful general-F
  strengthening of (CR2) exists to close; at the CONSUMED instance F = ZMod p (TreeCan's
  (†15) pair, `canPolicyC_pin`, and every mandatory-path consumer run at the prime
  ambient field) the clause is automatic by Theorem 1(iii), and `RRE(p, ZMod p)` is
  PROVED and FORMALIZED (`runRealizerExists_zmod`, Lean-core, on file since the wave-2
  fill). Both halves of the leaf obligation are therefore discharged by the twice-stable
  core alone.
* **Conjecture 5.4.C is consumed by NOTHING on the mandatory path.** Checked against the
  tree + DELTA 1 (2026-07-31 late): the string (S6b′) occurs in the tree ONLY inside the
  O-14a′ residue descriptions themselves (§2.4 O-14(a′) and §D1.5/D-10) — never as an
  input to another node; the §D1.6 critical path consumes O-14a′ only through the
  "close or remove" adjudication above. The conjecture's only forward consumer is the
  CONDITIONAL fence-lift obligation (rev-2 §5.5, byte-stable in the rev-3 brief §5.3
  mechanism (ii)): IF the RG-2 fence is ever lifted, (CR2) must be re-adjudicated to the
  faithful law BEFORE the lift — a parked statement-change/sign-off item, not a node of
  the mandatory path. Demoting the law to a conjecture therefore costs the root
  NOTHING; it removes an unstable claim from the certified perimeter.

---

## 2. What changed, artifact by artifact (rev 2 → rev 3)

* `O14ap_phaseB_verifybrief_rev3.md` (NEW; the package sent back to verification):
  §§1–4 + §5.1–5.3 byte-identical to revs 1–2 EXCEPT one disclosed sentence (§1 claim
  structure: "stated and proved" → "stated; proved fragments separated; law = labeled
  conjecture", marked inline). §5.4 rebuilt as the RESCOPE: kept theorems = Lemma 5.4.0,
  (THR), forced-class arithmetic, Prop 5.4.2 (framing de-coupled from the demoted
  theorem: "in the setting above"), Prop 5.4.3 restated conditional-only with honest
  frame provenance, NEW Prop 5.4.4; the law displayed as Conjecture 5.4.C with OL-1/OL-2
  and the falsifier suite; the void claim withdrawn in a dedicated block displaying the
  verifier's evading instance. Rev 2's Remark 5.4.R (recentering transport) is REMOVED
  from the brief (it was proof apparatus of the demoted theorem); it survives in rev 2
  as design material under OL-1, uncontested but insufficient, claimed nowhere.
* `O14ap_check.py`: +2 checks (H1 the 𝔽₃ evading instance; H2 the evading class
  populated at (e,p) ∈ {(2,3),(2,5),(3,7)} — counts 1/2/4). 16/16 PASS, exit 0.
  Checks A–G byte-unchanged.
* This file: the round-3 classification, the rescoped verdict, this delta, the ledger.
* NO Lean edits (per charge). The Lean corpus is already aligned with the rescope: the
  consumed instance `runRealizerExists_zmod` (prime field) never referenced the
  general-F layer, and the compiled gates (HK23/HK25) exhibit stretched frames only
  terminally — consistent with Proposition 5.4.4 (corroboration, non-load-bearing).

---

## 3. Design material retained under the conjecture (not asserted)

For the future prover of Conjecture 5.4.C (or its refuter — the falsifier suite is the
faster route if the law is false):

* The 6-step proof design of rev 2 §5.4.1 stands with its scale arithmetic ratified by
  V15 §1; the two open seams are exactly OL-1 (define the collapsed read-level index
  formally: levels = non-recentering reads; prove the induction commutes with the
  recentering transport of rev-2 Remark 5.3.1, or add a recentering case) and OL-2
  (state (F0-a)/(F0-b) as intended-model lemmas of the base-stage construction — they
  are standard Gauss-valuation facts, but they must be DISPLAYED, per the V15 finding).
* Expected difficulty: OL-2 is bookkeeping against the dual-accepted base-stage
  construction; OL-1 is the genuine content (the same stage-vs-level collapse that the
  B2-FINAL carry-algebra write-up owes independently — one shared mechanism, two
  consumers; solving it there solves it here).
* The stretched (e★ ≥ 2) territory is OPEN both ways after the withdrawal: the evading
  class shows the current clause triple does not empty it; no law is claimed on it
  ((S6b′-DEEP) remains a named design option, conjecture-level, from rev 2 §5.6 — its
  "what the faithful e ≥ 2 interior should say" paragraph survives as a question, its
  void justification does not).

---

## 4. Honest-scope ledger (rev 3)

* **Proved outright (bare coherence + node/stage typing):** Theorem 1 (F = ZMod p;
  part (ii) exactly as conditional as the RG-2 fence), Lemma 3.1, Lemma 3.2, Theorem 3,
  Corollary 4 [twice-stable]; Lemma 5.4.0, (THR), Proposition 5.4.3 (conditional form),
  Proposition 5.4.4 (+ the flagged base pin σ₀.e = 1). Every use cited by clause label.
* **Proved at the intended tower (consuming the flagged (F1)):** Proposition 5.4.2 —
  sharpness at every g within the shaped class [V15-ratified].
* **Refutations:** §5.1–5.2 the F₉ countermodel [twice-stable]; §5.2 recorded-lift
  form; §5.3(ii)/rev-2 §5.5 fence-lift flag (conditional, machine-checked).
* **Conjecture (labeled, consumed by nothing mandatory):** 5.4.C = (S6b′-SUPP-2) on
  (U), with OL-1/OL-2 open and the falsifier suite attached.
* **Withdrawn (this round):** the (U)-exhaustiveness/void claim; the stretch-provenance
  overstatement; the "only (F1)" flag claim. Rev 2's §0 items 3 and 5 are superseded
  accordingly.
* **Open / not claimed:** OL-1, OL-2; the e★ ≥ 2 interior law; the arbitrary-realizer
  sharpness strengthening; the compiled 𝔽₉ Stage instances (falsifier follow-up).
* **Predictions falsifiable now:** (P1) the LIVE flank countermodel search returns
  empty [unchanged, twice-stable core]; (P2) a hostile pass on the rev-3 brief finds
  the §§1–4/5.1–5.3 core clean for a third time; (P3) any attempted proof of the
  rev-2 void claim fails on the H1 instance (z²+1 over 𝔽₃ at a (2,h)-frame with
  wPrev(Φ) < h); (P4) the (S6b′-DEEP)/stretched design, if ever adjudicated, must
  reproduce checks E3 + H1-H2 (the un-MacLane regrade slopes and the evading class).

## 5. Consumed tree nodes and evidence

T-1 (§B2-DEF stage laws — §5.4's setting only; §§2–4 consume nothing above the compiled
definitions' mathematical content); the D-10/O-14a′ leaf statement; DELTA 1 §D1.6 (the
consumption audit of §1). Evidence artifacts cited for provenance only: V11/V15 reports,
`R7_runRealizer.lean` (the formalized consumed instance), HK23/HK25/HK52 gates,
`O14ap_check.py`. Nothing here depends on O-1/O-2/O-3; the unit sits at the top of the
§D1.6 critical path (V6 finding 22 honored: O-14a′ before O-3).
