# O11 pass 1 — hostile verification (fresh context, Fable, 2026-07-31). ID: O11V

**Charge.** Audit `O11_phaseB_attempt.md` (no verifybrief exists; the attempt is the
subject) on four axes: (1) every consumption of the §3 assembly against the displayed
tier-1 dependency set {(GR-B), (FRESH), CU-2t, D-11} — anything consumed beyond it is
a finding; (2) the interface-level equivalences' directions; (3) the falsifier's
coverage claim; (4) quote-and-classify, fix nothing.

**Sources read** (fresh-context discipline: NO other proof notes): the attempt itself;
its own falsifier `verification/openmath/o11_seriestie_check.py` + logs
`o11_seriestie_run{1,2,3}.log`; the header/`alpha_full` docstring of
`verification/om_density_engine.py` (needed to adjudicate the "REAL PACK" coverage
claim); `git log` on the harness. Classifications per the repo verifier discipline:
**CRITICAL ERROR** (breaks the audited claim's chain) vs **JUSTIFICATION GAP** (assume
and continue).

**VERDICT: NOT ACCEPTED AS STATED — 1 CRITICAL + 8 JUSTIFICATION GAPS.** The Theorem
O11 walk (§3.5 glue over K1–K4) survives the pass structurally, and the equivalence
directions check clean. What fails is the unit's headline deliverable, the §0 residue
display: one consumed open modulus — **(M6b)(iii)** — is named in the attempt's own
§3.1/row-4 status and then never priced into any tier, so the "conditional on exactly
FOUR named open items" claim is unsupported by the document as written. The falsifier
record also contains factual inaccuracies (37 checks, not 38/38; "dead-code" defects
that in fact crashed runs 1–2 live).

---

## CRITICAL

### C-1. (M6b)(iii) is consumed but absent from the tier-1 set — a fifth open item as written

§3.1 (K4-CYL), quoted:

> "Statuses: O-1thr Thm 3 proved modulo (M6b)(iii) + the (V1)/(V2) citation inputs
> beyond degree-1 first transitions — (V1)/(V2) are LITUNIT-pinned and GD23-proved at
> order ≤ 1 over an arbitrary DVR, so the order ≥ 2 residue is **(GR-B)**"

and §5 row 4, status column: "proved mod (M6b)(iii) + (V1)/(V2) beyond order 1", with
residue column "**(GR-B)** (order ≥ 2)".

The "so" clause prices ONLY (V1)/(V2). **(M6b)(iii) is displayed as an open modulus of
the consumed theorem (D-15 = O-1thr Thm 3, a load-bearing K4-CYL input) and is then
priced into nothing**: it is not in the §0 tier-1 four, not in the §0/§6 tier-2 lists,
and not asserted to be contained in (GR-B). The §0 headline "conditional on exactly
FOUR named open items ... no fifth mathematical open is consumed" and the §5 footer
"Tier-1 union over the table: {(GR-B), (FRESH), CU-2t, D-11}" are therefore
unsupported by the document's own consumption display. Classification: **CRITICAL
ERROR** for the residue-set claim (the unit's principal deliverable). Possibly curable
by a one-line pricing (if (M6b)(iii) is closed at O-1thr rev 4, or is itself an
order ≥ 2 item inside (GR-B)) — but the document must say so; it does not, and this
pass reads only the document.

## JUSTIFICATION GAPS

### G-1. K1-c: the OL-3 → (GR-B) reduction is asserted, not evidenced

§3.2 (K1-c), quoted:

> "OPEN, owned by M07 OL-3; its ingredients are the GD-2/GD-3 dictionary (O-10 §4.3's
> own pricing), proved at order ≤ 1 (GD23 over an arbitrary DVR; pass-2 0-critical),
> so the residue is **(GR-B)**."

The inference "its ingredients are GD-2/GD-3, order ≤ 1 proved ⇒ residue is (GR-B)"
requires a PROVED reduction: (I-τ)/K-LOC follows from the GD-2/GD-3 dictionary at all
orders. The citation given ("O-10 §4.3's own pricing") is to a *pricing*, not to a
proof-by-citation of the reduction. If OL-3 needs any content beyond the dictionary
(e.g. the τ(c) ≤ thr(c) + ρ(c) inequality itself, or the (A1)–(A3) presentation
existence), a fifth open item hides under (GR-B)'s label. Classification: gap.

### G-2. K3-c: the (R1)–(R4) order ≤ 1 discharge is asserted via "the discipline", not displayed

§3.4 (K3-c), quoted:

> "the adopted arbitrary-DVR discipline (DELTA-2 §D2.6 step 3) states the GD families
> over an arbitrary absolutely-unramified complete DVR from the start — GD23's order
> ≤ 1 layer is proved at that generality, so (R1)–(R4)'s residue at order ≥ 2 is
> **(GR-B)** again"

Missing: the display that O-8b's (R1)–(R4) — the O_δ re-base stage laws with
a_δ = δ·a₁ — restricted to order ≤ 1 are literally *instances* of the GD families
proved by GD23, rather than requiring an additional base-change/re-base lemma on top
of them. This is exactly the attempt's own suggested charge (iii), i.e. the author
flagged it and it remains unadjudicated. Classification: gap.

### G-3. D-11's content is elastic across the document's own displays

The §0 tier-1 entry defines D-11 as: kernel entries = Haar volumes of the T-3/T-6
continuation events, block system = 𝔅_n (or O-12 Thm 3-covered), per-box lift
uniformity, "Enters through K2 ..., K3 ..., and the wiring fence of §2.4." But two
additional contents are later made to "ride" D-11 without appearing in that display:

* §3.4 (K3-c): "the remaining scope-hygiene audit (each consumed table law stated at
  DVR generality at the pack) rides **D-11**'s instance pin."
* §5 row 20: rsh_interp / r_bdd / wsh_ok, consumed at §3.5 (a fourth entry point,
  beyond the §0 K2/K3/fence list), residue column "(rides **D-11**)".

A residue set is only "exactly four" if each name's content is stable; here D-11's
scope widens twice after the headline display. Classification: gap (display
consistency; the D-11 unit's owner must accept the widened charge or the items are
undisplayed opens).

### G-4. K1-a: "the CU cluster" is an unnamed, unstatused consumption

§3.2 (K1-a), quoted:

> "its open kernels (SIB-STEP)/CUT-WD are now served at statement level by O-10 + the
> CU cluster (O-10 §5.3 consumer audit names exactly this unit's use)."

and §5 row 9: "kernels served by O-10 + CU cluster", residue "—". Which CU units serve
CUT-WD/SIB-STEP, and at what status, is nowhere named — this is the only load-bearing
consumption in the table with no named theorem and no status, in a document whose
standard is "EVERY consumption displayed". If any serving CU piece is open (other than
CU-2t, already priced), it is a consumption beyond the displayed set. Classification:
gap.

### G-5. K3-a: the H.6 fence-respect claim rests on n = 3 numerics, undisplayed as a conditionality

§3.4 (K3-a), quoted:

> "its six H.6 fences are respected by the table construction (they gate THIS event,
> and V-n3/H-n3 are the sealed evidence that the built tables sit inside them)."

"Sealed evidence" = numeric harnesses at n = 3. The fences "gate THIS event" at every
n; that the per-n tables sit inside them at general n is thus a consumed claim
supported only by n = 3 numerics — evidence, not proof — and it appears in no tier.
Classification: gap.

### G-6. Falsifier V1: "EXECUTED AT THE REAL PACK" overstates what ran

§0/§2.4(ii)/§7 claim "Finding F1's test EXECUTED AT THE REAL PACK" / "the falsifier V1
(§7) verifies the REAL pack's n = 2 solve." What runs is
`om_density_engine.alpha_full(2)` — a Python symbolic engine building cluster laws
from a coupled fixpoint (per its own docstring, the "S-area engine") — not the pack
object the theorem binds C to. The pack's pinning is D-11, **PENDING**, and the Lean
row "stays untouched, PARKED" (§8): strictly, "the REAL pack" does not yet denote a
pinned object, and the identification of the engine with it is by provenance only
("the same block-recursion pipeline RESUM-n3 gates at n = 3"). The test is meaningful
(a proxy presumed equal to the pack reproduces the true triple identically in ℚ(q) —
verified in the run-3 log, difference ≡ 0, all three types + Σ = 1), but the
fence-execution language claims more than was executed. Classification: gap.

### G-7. Falsifier T1: proxy classifier + count inaccuracy

Two quoted claims against the harness as inspected:

* §7 T1: "Any bracket violation would have refuted (D_σ) at the real classifier and
  killed the row." The harness's `decide()` is a hand-written discriminant rule
  (parity of v_p(disc) + QR of the unit part; unit-mod-8 at p = 2) — verified sound by
  direct inspection in this pass — NOT the project's OM classifier. A bracket
  violation would refute the VALUE ρ_σ(p) = true σ-density (given the rule's
  soundness), which transfers to "(D_σ) at the real classifier" only through
  soundness/exhaustion facts about the real classifier that are exactly this unit's
  conditional inputs. The §7 presentation ("Exhaustive enumeration ... per-σ decided
  mass") invites the reading that the real classifier's decided classes were
  enumerated; they were not.
* §7 header: "**38/38 PASS, exit 0**" and T1 "24/24". The run-3 log contains exactly
  **37** PASS report lines (V1 8, V2 6, T1 23 = (10+1) + (6+1) + (4+1)); the 38th
  "PASS" match is the final "ALL PASS" summary line. T1 is 23/23, the total 37/37. The
  commit message (3fc8f52) repeats 38/38. No check failed; the record is inaccurate.

Classification: gap (coverage over-statement + record inaccuracy).

### G-8. Falsifier honesty note: "dead-code defects" mischaracterizes the run history; run-3 V2 is weaker than the sealed prediction

§7, quoted:

> "Harness-bug honesty: two dead-code defects in V2's oracle call (q = 1 division;
> Fraction-vs-symbol typing) were fixed between runs 1–3; no sealed prediction
> changed; run 3 is the run of record."

The logs show both defects were on the LIVE path and each **crashed its run**: run 1
aborted with `ZeroDivisionError` at `pt.monic_cubic_pred(1)`, run 2 with `TypeError`
at `pt.monic_cubic_pred(q)` — in both cases BEFORE any V2 check or any T1 check
executed. So (a) "dead-code" is false as a description; (b) the sealed V2 and T1
predictions were first exercised only on run 3, after two rounds of harness edits.
Further, the sealed prediction reads "alpha_full(3) == monic_cubic_pred identically
(all five types)", but run 3 establishes the symbolic identity against a
hand-transcribed in-harness copy (`true3`) and checks the actual oracle only
numerically at p ∈ {2, 3, 5, 7} — four points do not pin a rational function, so the
executed test is strictly weaker than the sealed one unless the transcription is
trusted. The attempt does display the transcription ("transcribed line-for-line"), so
this is a shortfall against the sealed docstring, not a concealment. Classification:
gap (minor; no evidence any sealed prediction was ALTERED — the harness has a single
commit, so runs 1–2 predate version control and the "no sealed prediction changed"
claim is unverifiable from the repo).

## MINOR display notes (no separate classification)

* §0 says (GR-B) "Enters through THREE faces here" (K1 presentation, K3 census, O-8b
  re-base), but §5 charges (GR-B) at SIX rows (4/5/6/11/17/18) — the K4-CYL face
  (D-15's (V1)/(V2), CU-1, CU-2) is missing from the §0 face list.
* The standing ns-free perimeter (§3.1 K4-ns "carried") appears in no §0 tier-2 line.
* §7 T1 writes "ρ_σ(p)" for the solve value elsewhere written R_σ(p); ρ(c) already
  means the Jacobian exponent (§3.2) — undefined symbol + collision.
* The unit and its run of record are dated 2026-08-02 — a date that had not occurred
  at file mtime (Jul 31); cosmetic, but the run-of-record label should be accurate.

## Checked and CLEAN (the charge's remaining axes)

* **Equivalence directions (charge axis 2): PASS.** §2.1/§3.1's "row ⇔ (D_σ) given
  the count/cylinder law" is consumed orientation-ward only: the §3.5 glue uses the
  K4 rewrite (LHS = Σ_{T type σ} μ(fiber T)) directly and never routes through
  (D_σ) ⇒ row. §2.2's Theorem 2 direction (σ-sum FROM sibling rows) is consumed as
  orientation only, and drainage/env_tendsto is verifiably not used anywhere in the
  §3 walk (§4's first bullet is accurate against the §3 text). T1's evidential
  bearing on the row is correctly displayed as conditional ("given K4-CYL").
* **The four tier-1 items are each consumed at displayed steps**: (GR-B) rows
  4/5/6/11/17/18; (FRESH) row 17 (CEN-J); CU-2t rows 7/8 (K4-CYL, K1-e); D-11 rows
  15/18/20 (K2 pack side, K3-d, fence, §3.5) — the "nothing smaller" half of §0 is
  supported; the "no fifth" half fails at C-1.
* **D-8 guard usage (attempt's charge ii)**: within the §3 text, the guard is engaged
  only at K1-b's fiber-value clause (p^{−ρ(c)} as the per-site Jacobian factor);
  K4-CYL's every-N ≥ thr(T) exactness is routed through D-15, not through K-COUNT.
  No sub-guard usage is visible in the document. (Adjudication against O-10's own
  text is outside this pass's read scope.)
* **(E-N) non-consumption (attempt's charge v)**: on the document's own routing the
  σ-grading of decided classes goes through K1-e (O5triple + CU-2t), not through
  Thm 3(c)'s σ-count clause, and fibers of distinct trees are disjoint for free
  (fibers of a function); the displayed non-consumption is internally coherent.
  Final adjudication requires O-1thr's Thm 3 text — stands as an open verification
  charge, correctly flagged by the attempt itself (§8 item v).
* **Falsifier T1 internals**: the decision rule is sound (p odd: v < N determines
  u mod p; p = 2: v ≤ N−3 determines u mod 8; unramified quadratic ext of ℚ₂ is
  ℚ₂(√5) so {1: split, 5: inert, else ram} at even v is correct); the true triple
  sums to 1; env values in the log match the claimed geometric decay
  (env ≈ p^{−N}-scale at the caps: 7.81e-3 / 1.37e-3 / 1.60e-3).
* **Consumption sweep of the remaining §5 rows** (1, 2, 3, 8, 10, 12, 13, 14, 16,
  19): each is either VERIFIED/VERIFIED-DUAL, PROVED-UNVERIFIED with the duty in the
  §6 registry (tier-2 by the repo's discipline), or literature at LIT-1's displayed
  conditional grade — no further beyond-set consumption found.

## Disposition

The assembly walk is structurally sound and the quantifier-hygiene displays (§4) are
accurate against the §3 text. The unit cannot be graded PROVED-UNVERIFIED *at the
displayed residue set* until C-1 is resolved: either price (M6b)(iii) (into (GR-B)
with justification, into tier-2 with an owner, or as a FIFTH tier-1 item) or display
its closure. G-1 through G-5 are pricing/display repairs on the same theme (reduction
claims asserted by citation to "pricings" rather than proofs); G-6 through G-8 are
falsifier-record corrections (37/37; live crashes, not dead code; proxy scope stated
plainly). Nothing found refutes the mathematics of any consumed piece.
