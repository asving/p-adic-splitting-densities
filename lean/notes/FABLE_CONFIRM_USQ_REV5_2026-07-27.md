# FABLE FRESH-INSTANCE CONFIRM — §U-SQUEEZE rev 5 (2026-07-27)

Confirming verifier (Fable half of the FINAL dual-acceptance shot; predecessor's
rev-4 pass: FABLE_VERIFY_USQ_2026-07-27.md, 0 crit / 1 gap D-G2 / 5 WATCH).
Target: MOVES_2026-07-24.md '## §U-SQUEEZE' (lines 12879–13629, rev 5).

## A. The two rev-5 clauses (D-G2 repair)

SITE 1, (U-n) qualifier (ll. 13150–56), quoted (trimmed): "(REG-p) is a SEPARATE
NAMED HYPOTHESIS — RELATED to but NOT identical with the solve stack's E0/CL-1 and
ACT/CL-5 citations ... neither implies the other." SITE 2, Theorem U (ll. 13177–81):
"(REG-p) is a SEPARATE hypothesis for the EVALUATION step — related to, but neither
implied by nor implying, §S's per-pool ESCAPE(E0)/CL-1 and the CTS-M(ii) ACT
agreement (ii-c)/CL-5". BOTH-WAYS CHECK vs §S S.4 AS DISPLAYED (ll. 12208–11):
S.4 records junk-block dets with "a blanket det(I − D_{q₀}) ≠ 0 is NOT required"
— so (r1)'s full det strictly strengthens S.4 at wild pools (E0+ACT ⇏ (REG-p));
and det(I − K(q₀)) ≠ 0 yields no ρ < 1 (scalar K = 2: det = −1 ≠ 0, ρ = 2), so
(REG-p) ⇏ E0. Both directions VERIFIED; NO-CLAIM failure semantics and the
NOT-ASSERTED removable-zero paragraph untouched; conservative direction stated.

## B. Identification-language sweep

The rev-4 glosses ("it is §S's per-pool ..." at SQ.4; "its CONTENT already rides
..." at (U-n)) are GONE (grep: no "already rides"/"IS §S's" in ll. 12879–13629);
the only "rev 5" markers are the two clause sites; l. 13414 "(REG-p) is the ONE
explicit hypothesis" (DAG) consistent with separateness. ONE residual echo, NEW
WATCH C-W6: SQ.6 item 6(vii) (l. 13564) annotates CTS-M(ii) ACT as "(REG-p)'s
second leg" — loose ((r2) strengthens (ii-c): over-inclusive E(e) per A-W2 +
literal definedness); coda-list annotation, not the statement-of-record,
conservative. Suggest "the ACT face (r2) cites" at a future rev. Not a gap.

## C. Fresh-angle checks (verbatim-quote fidelity vs plan — unprobed at rev 4)

Mechanical word-normalized diff vs ASSEMBLY_PLAN_2026-07-26.md §6:
 C-1 THE CAPSTONE LEDGER (note ll. 13228–13360, 133 lines, CL-1…CL-19) vs plan
   ll. 2981–3113: VERBATIM TRUE (dedent/requote only) — the note's "quoted
   VERBATIM from plan §6 SQ.4" claim holds exactly.
 C-2 TRACK-COUNT (note ll. 12969–77) vs plan ll. 2914–21: VERBATIM TRUE.
The predecessor's 5 WATCH (A-W1..A-W5) ride unrepaired, as the record states.

## D. Own-construction numeric check (/tmp/usq_rev5_extend.py)

 D-1 The on-disk /tmp/usq_squeeze_check.py is the PRE-FIX artifact (wrong
   R(2) = (1/6,1/6,2/3)); running it reproduces the falsification — the SQ.3-chain
   assert fires at p = 2 (same violation the rev-4 report caught at the upper
   leg). Teeth re-demonstrated.
 D-2 R(2) = (1/3,1/3,1/3) re-derived INDEPENDENTLY (b-parity split: b odd →
   D ≡ 1−4c gives split/inert evenly, no ram; b even → D/4 uniform →
   (1/6,1/6,2/3); average (1/3,1/3,1/3)) — matches the predecessor's fix.
 D-3 Corrected runs: p = 2 (N ≤ 8), p = 3 (N ≤ 5), and NEW prime p = 5
   (R = (5/12,5/12,1/6), N ≤ 3): (BOX-N), upper leg, lower leg, |d−R| ≤ env
   ALL PASS at every (σ, N).
 D-4 (L-meas) RETYPING (SQ.5's rev-2 gate clause): the biconditional
   (d_σ ≥ R_σ − env_meas) ⟺ (Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ) holds at every (σ, N),
   all three primes — and is an arithmetic identity given (BOX-N) + checksum:
   d_σ = 1 − Σ_{τ≠σ}d_τ − env ≥ R_σ − env ⟺ Σ_{τ≠σ}d_τ ≤ 1 − R_σ. CONFIRMED.

## VERDICT

Both rev-5 clauses PRESENT and CORRECT at both sites; the both-ways failure
characterization matches §S S.4 as displayed; no identification language remains
on the statement-of-record. Fresh angle: both VERBATIM-quote claims (capstone
ledger, TRACK-COUNT) mechanically exact vs the plan. Numerics: all squeeze checks
pass at p = 2, 3, and the unprobed p = 5; the (L-meas) equivalence exact.
0 CRITICALS / 0 GAPS / 1 new WATCH (C-W6, coda-list echo) + 5 riding. CLEAN.
