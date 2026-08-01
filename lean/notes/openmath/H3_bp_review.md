# H3 blueprint — Codex adversarial review (pass 1)

Object: `lean/blueprints/HDISCHARGE_H3.md` (pre-fold text). Verifier: Codex
(fresh context, repo-blind, charge = quote-and-classify, fix nothing).
Launched detached from /tmp/openmath (H3_bp_prompt.txt, 637 lines);
machine clock 2026-08-01 (2026-08-05 directive window).
VERDICT: **BLUEPRINT-CRITICAL** — 4 critical + 12 gap.
Disposition: every finding folded or rebutted at HDISCHARGE_H3.md §6
(the fold edits landed in the same commit as this archive).

---

The blueprint is not a valid discharge chain as written. Most importantly, D-12r is retired by relabeling an unshown conditional perimeter as “internal,” while the Lean Hensel unit formalizes only factor lifting—not the irreducibility and invariant read-off actually required. The (ADM) and (E-N) sections are more candid, but several proposed gates do not decide the quantified claims assigned to them.

## Detailed audit

1. **CRITICAL — impossible provenance date**

> “compile-probed … 2026-08-05: all statements elaborate”

> “G-ADM-1 (pre-run 2026-08-05, this lead)”

> “Mathlib probe — RAN by this lead (2026-08-05)”

The supplied machine date is 2026-08-01. These are future completed-action claims, not future plans. Consequently none of the alleged machine evidence can be credited from the blueprint’s own chronology.

2. **CRITICAL — D-12r’s “exactly two cites” reduction is not displayed sufficiently**

> “the (c) remainder list reduced to **{VP-SOUND's cites}**”

This displays only a set-valued label. The blueprint does not quote the referenced VP-SOUND passage establishing that this set contains exactly HEN-LIFT and OM-SAT, nor the surrounding hypotheses under which the reduction holds. The two bullets that follow are the blueprint’s consolidation, not displayed verbatim artifacts.

The further assertions—

> “MOVES §T.2 rev 2, ‘declared precisely’”

> “the residual is ALREADY REDUCED on file”

—rest on artifacts the blueprint does not display. This is load-bearing and must be flagged under the charge.

3. **CRITICAL — “internal conditionality” does not discharge a condition**

> “(irr) PROVED conditional on the standing §C C.2 perimeter”

> “the conditionality is INTERNAL to the verified corpus”

> “TB-CAP(irr)'s perimeter internal to the dual-accepted corpus”

A theorem conditional on C.2 remains conditional regardless of whether the condition is called internal. To retire D-12r, the blueprint must display a derivation that C.2 is precisely and only the two proposed citations, and that no other hypothesis enters the consuming instances. That bridge is absent. Moving the row from `[M]` to a literature class is therefore fiat unless the missing bridge is supplied.

4. **GAP — other residual dependencies are admitted but excluded without a displayed separation**

> “Discharges (τ-irr), and (τ-ns) modulo (z-3)'s exact identification.”

> “the identification is the (H1)/(GR-B)-adjacent dictionary … ALREADY PRICED”

> “P(O5t r3) … carries the (τ-hen)/(τ-irr) READ-OFF's consumption”

These are additional dependencies on the claimed verdict-soundness path. They may belong to other rows, but the blueprint does not display the dependency decomposition proving that they are logically external to D-12r rather than part of its residual.

5. **CRITICAL — the HEN-LIFT Lean theorem proves the wrong statement**

Required HEN-LIFT includes:

> “ψ irreducible”

> “g irreducible generating an unramified extension, (E, F) = (1, deg ψ)”

But `henLift_padic` assumes no irreducibility of `ψ` and concludes only a lifted monic factorization with matching reductions. It contains no conclusion that `g` is irreducible, no unramified-extension statement, and no `(E,F)` computation.

Thus the claim—

> “A landed D12R-U2 upgrades (HEN-LIFT) from literature pin to VERIFIED-LEAN”

—is false for the pasted signature. Even with the proposed uniqueness companion, this unit cannot discharge HEN-LIFT.

6. **GAP — the literature route knowingly lacks confirmed statements**

> “the printed STATEMENT may assert existence only”

> “cite separately, this is a SECOND statement riding the same brief”

> “exact numbered statement … owed”

The candidate Hensel citation has not yet been shown to contain uniqueness, irreducibility, unramifiedness, and the invariant read-off. Calling all of this one of “the two cites” conceals that HEN-LIFT itself requires multiple results or companion arguments. This is a plausible future literature route, not an already pinned discharge.

7. **GAP — G-ADM-2 is not an adjudicating gate for a universal claim**

Track A requires:

> “every census datum D consumed by Step 14”

But G-ADM-2 searches only:

> “n ≤ 5, p ∈ {2, 3, 5}, N ≤ the harness caps”

A hit refutes Track A. A no-hit cannot prove or adjudicate the universal statement, distinguish “abstract-only” from merely “not found,” or authorize the `all-full` branch. The blueprint partly corrects this by still scheduling ADM-U7, but the labels “adjudicating gate,” “two exclusive tracks,” and `G-ADM-2 = all-full` overstate what the finite scan establishes.

8. **GAP — ADM-REAL’s quantifier domain is not defined**

> “at the intended instance, every census datum D consumed by Step 14”

> “within its (DET) window”

The promised `consumedData` carrier does not yet exist, and the blueprint assigns it elsewhere. It is therefore unclear whether ADM-REAL quantifies over all primes, degrees, levels, unramified bases, faces, and realized branches, or only a fixed engine instance. The eventual field

> `h3_adm := ∀ D ∈ consumedData, ADMFull D`

does not repair this until `consumedData` and all ambient parameters are explicitly bound.

9. **GAP — Track B is sufficient only in principle, not from the cited slot law alone**

> “each slot law ALREADY PROVED”

> “This retires (ADM) wholesale”

The image/fiber law for one graded piece does not by itself establish the global product formula CEN-W′. One still needs independence or compatible iteration between slots, exact exponent bookkeeping, the treatment of repeated heights and vertices, and reassembly of CEN-J and every consumer. The discharge criterion correctly demands end-to-end verification, but the actual scheduled ADM-U6:

> “DESIGNS; it does not land the change”

is only a design note. No proof unit in the table completes Track B. Track B could retire ADM if fully carried through, but this blueprint does not yet provide a complete execution route.

10. **GAP — F-ADM-2 overreaches from relaxed models**

> “under coprime-only axioms”

> “REFUTES any plan to prove it from the lattice axioms alone”

A countermodel under relaxed axioms refutes derivability from those relaxed axioms. It does not refute derivability from the actual repaired carrier unless every remaining carrier field and constraint is verified on the countermodel. The blueprint does not display that verification. Its narrower conclusion—“coprimality plus the weight recursion is insufficient”—is sound; the broader “bare-carrier theorem” conclusion is not established from the displayed evidence.

11. **GAP — ADM-U2 has visible degenerate-carrier risks**

> `hclass : ∀ c, classCount D c = D.d`

> `Finset.univ.filter …).sup D.wt`

The proof sketch needs every relevant residue class to be nonempty, normally from `D.d > 0` and `D.period > 0`. Those hypotheses are not visible. On an empty filtered class, `Finset.sup` on naturals returns the default bottom value, so the max-weight inequality can become vacuous. The pasted signature may elaborate while failing to encode the intended mathematical domain.

12. **GAP — the primary E-N rescope is not established by the quoted consumer map**

The blueprint quotes CU-4 as:

> “conditional on … perimeter: TB-CAP (D-12r) + (E-N)”

and says the touch is:

> “F4-C's decision-level scoping through Theorem 3(c)”

That is evidence that the current F4-C leg regards E-N as a condition, not evidence that it consumes only the scoped definition. The contrary architectural assertion—

> “every FINITE-N counting object on the mandatory path is thr-scoped BY CONSTRUCTION”

—is not backed by quotations from CU-4, Step 13, Step 19, or the `(UB-X)(a)` transport. EN-U1 is therefore a legitimate audit proposal, but RESCOPE-CLEAN is not presently justified.

13. **GAP — the E-N absorption argument risks circularly changing “decided”**

> “a decided box whose … tree has thr > N is not DETECTED at cap N, i.e. sits in the undecided-at-N envelope”

The implication “not detected at cap N ⇒ undecided-at-N” depends on the envelope’s definition. The hypothetical box is explicitly assumed to fiber a “decided ns-free tree.” The blueprint does not quote the definitions showing that semantic tree decidedness and operational decided-at-level-N are different predicates, or that such boxes are included in the drainage set. Without that display, the claimed absorption may simply assume the scoped interpretation whose adequacy E-N questions.

14. **GAP — the E-N Lean target does not visibly encode the stated hypothesis**

The mathematical row concerns a:

> “decided ns-free tree”

but `ENRedundancyAt` assumes only:

> `NsFree Tr → Tr.fiberAt T χ x → Tr.thr n ≤ N`

No `Decided Tr` premise appears. Unless `fiberAt` entails decidedness—a fact not displayed—the Lean proposition is strictly stronger than E-N and may be refuted by irrelevant undecided trees. Conversely, a numerical search restricted to decided trees would not be a complete falsifier for this Lean proposition.

There is also a vacuity risk from arbitrary `m`: for `n > 0, m = 0`, the parameter type `Fin n → Fin m` is empty. A universally wrapped theorem over `χ` could therefore be vacuously true on a degenerate model unless positivity constraints are explicit.

15. **GAP — route (a) is mostly honest, but overstates its quadratic progress**

The blueprint candidly says:

> “a bound of the WRONG SHAPE”

> “genuinely open at n ≥ 3”

That is honest. However:

> “the n = 2 case squeezes to separation ≤ N − 1/2”

and

> “redundancy holds at n = 2 up to the ±1 boundary”

are not supported by a displayed discriminant bound, proof that the discriminant is nonzero in every relevant case, or a conversion from root separation to the exact read ceiling. This should remain a heuristic subcase, not a result.

16. **GAP — several per-object statements are used as global statements**

Examples include:

> “a realized branch η”

being used toward tree completeness without displaying universal coverage of every saturated branch; a fixed-parameter `ENRedundancyAt` being presented as the typed home of a claim across all levels and models; and `∀ D ∈ consumedData` without displaying how all Step-14 and unramified-base instances enter that set. These are per-branch/per-model/per-datum statements until the outer quantifiers and transport lemmas are stated.

BLUEPRINT-CRITICAL

1. **CRITICAL** — The blueprint reports machine runs dated four days after its stated machine date.
2. **CRITICAL** — D-12r’s “exactly two cites” bridge is not displayed; only the opaque label `{VP-SOUND's cites}` is quoted.
3. **CRITICAL** — Calling TB-CAP(irr)’s C.2 conditionality “internal” does not discharge it.
4. **CRITICAL** — `henLift_padic` omits irreducibility, unramifiedness, and the `(E,F)` read-off, so it cannot verify HEN-LIFT.
5. **GAP** — D-12r also depends on unquoted dictionary, `z-3`, and read-off seams whose exclusion from the residual is not demonstrated.
6. **GAP** — The Hensel literature pin is unconfirmed and actually comprises several statements.
7. **GAP** — G-ADM-2 can refute ADM-REAL but cannot certify its universal truth.
8. **GAP** — ADM-REAL’s consumed-data quantifier domain is not yet defined.
9. **GAP** — Track B is sufficient only after an unscheduled end-to-end census reproof; ADM-U6 is merely a design note.
10. **GAP** — Relaxed-axiom countermodels do not refute a theorem of the full repaired carrier without conformance checks.
11. **GAP** — ADM-U2 lacks visible positivity/nonemptiness hypotheses needed to avoid empty-class vacuity.
12. **GAP** — E-N route (b) rests on unquoted consumer and drainage displays, while the quoted CU-4 description still lists E-N as a perimeter.
13. **GAP** — The E-N absorption step may conflate semantic decidedness with detection at level N.
14. **GAP** — `ENRedundancyAt` omits an explicit decidedness premise and admits degenerate-parameter vacuity.
15. **GAP** — The claimed quadratic partial result in route (a) is only an unsupported heuristic.
16. **GAP** — Per-datum, per-branch, and fixed-model statements are repeatedly promoted to global consumption claims without outer quantifiers.