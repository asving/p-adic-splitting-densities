# O14ap owed hostile pass (2026-08-03) — Codex fresh-context verification

**Campaign**: the OWED-PASS QUEUE of the ROOT r10 ledger entry
(`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`). **Target document**:
`lean/notes/openmath/O14ap_phaseB_verifybrief_rev3.md` (pasted in full into the prompt; Codex
sandbox cannot read the repo). **Charge**: hostile fresh-context proof verifier,
quote-and-classify CRITICAL vs GAP, falsifier-first, fix nothing, single-line verdict.
**Prompt/raw output**: `/tmp/openmath/O14AP_PROMPT.txt` / `/tmp/openmath/O14AP_OUT.jsonl`.
**Codex budget at launch**: 7-day window 52% used.

## VERDICT: GAPS-ONLY

## Adjudication (campaign manager, from the report text only)

NOT BANKED. The standing bar for banking an owed pass is verdict CLEAN; this pass returned GAPS-ONLY (3 GAP findings, 0 CRITICAL). The verifier explicitly found NO defect in the core chain (Theorem 1, Lemmas 3.1-3.2, Theorem 3, Corollary 4) and its falsification attempts against it all failed; all three gaps sit in section 5 (the paragraph-5.2 'whenever' overgeneralization; the 5.3(i) recorded-lift mechanism's (r7)-(r10) omission; the Conjecture 5.4.C honesty audit missing a residual-assembly obligation beyond OL-1/OL-2) - i.e. in the flag-honesty perimeter the charge included, not in the certified theorems. Per protocol, no repair performed and no banking; P(O-14a' r3) does NOT upgrade on this pass.

## Verifier report (verbatim, unedited)

I found no defect in the core logical chain through Theorem 1, Lemmas 3.1–3.2, Theorem 3, and Corollary 4. Falsification attempts against the degree induction, anchor inequality, equal-value cancellation argument, terminal use of (S6b), and interior/terminal split all fail under the displayed axioms.

I found three noncritical gaps elsewhere.

1. **GAP — §5.2 overgeneralizes its counterexample.**

> “...and (CR2) — which at recenterings demands singleton support — is unfaithful whenever deg(frame key) > 1.”

The proof establishes failure for the particular degree-two frame, residual map, and center \(\tilde c\). Nothing in Definitions 1–3 implies that every frame of degree greater than one has a center outside the residual images of its \(X\)-monomials. The displayed axioms place no such image-size or linear-independence restriction on \(R\). Thus the literal “whenever” assertion is not proved. It is not consumed downstream.

2. **GAP — §5.3(i) does not produce an equally lawful recentering record.**

> “then \(t+s\) is an equally lawful record — (r5) via the strict triangle ... and (r6) via (R<) — with X-support anywhere.”

The argument verifies only (r4)–(r6). A coherent recentering record also includes

> “(r7) \(\sigma_{i+1}.\Phi=\sigma_i.\Phi-\mathrm{lift}\)”

and the compatibility requirements (r8)–(r10). Replacing \(t\) by \(t+s\) while retaining the existing successor violates (r7); changing the successor key instead requires proving that a compatible successor stage and residual map exist. No such construction is given. Moreover, the axioms do not guarantee higher-weight \(s\) with arbitrary desired support. Consequently the asserted recorded-lift refutation mechanism has a justification gap, though it is unused by §§2–4.

3. **GAP — the conjecture-status account omits a residual-assembly obligation.**

> “One standard fact of the intended apparatus is consumed, flagged:  
> (F1) the slot positions ... are consecutive...”

and later:

> “Two obligations block theorem status; they are displayed as OPEN LEMMAS and asserted nowhere”

F1 specifies only the positions assigned to progression slots. It does not state that equal-minimum slot residuals add with their coefficient digits to produce
\[
\bar z^{\,m}\sum_k a_k\bar z^k.
\]
The displayed stage axioms provide only multiplicativity and the strict-inequality rule (R<); they impose no behavior on sums of equal weight. Such an assembly law is necessary for the proposed recursive construction to realize an arbitrary prescribed \(\tilde c\). Proposition 5.4.2 avoids this by explicitly restricting itself to objects whose

> “digits assembl[e] per (F1),”

but that assembly property does not follow from F1 as stated. Therefore the claim that OL-1 and OL-2 are the only outstanding obligations, and the associated accounting of flagged intended-model facts, is incomplete. This affects the honesty audit of Conjecture 5.4.C, not any theorem consuming it.

The independently stated §5.4 results survive falsification attempts: Lemma 5.4.0 has the correct \(e_{i+1}e_i g_i\) factor; (THR) follows directly from (STR); Proposition 5.4.2 is valid conditional on its explicit shaped-assembly hypothesis; Proposition 5.4.3 is the stated divisibility obstruction only; the \(e^\star=g=2\) example genuinely evades it; and Proposition 5.4.4’s boundary indexing is valid.

VERDICT: GAPS-ONLY
