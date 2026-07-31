# O1thr — the per-site read package — Phase-B attempt REV 3 (Fable, 2026-07-31)

Repair of the pass-2 hostile verification `O1thr_pass2_fable_verify.md` (verdict
SOUND-WITH-GAPS) of the rev-2 brief (`O1thr_phaseB_verifybrief_rev2.md`). Pass 2
CONFIRMED: Theorem 1 clause-by-clause (no run inspection), Lemmas
DEV/POS/R-LOC/NAT/CEIL, the SPAN ledger arithmetic and both equality routes,
2(b) Case 2, Theorem 3's cylinder/scaling/uniqueness arguments, the Eisenstein
guards by stated hypotheses, the (N4)/(R5) consumer audit, and no
∀-by-examples. It found one load-bearing gap (Finding 1) and five smaller ones.
This rev repairs ALL of them. The repaired self-contained brief is
`O1thr_phaseB_verifybrief_rev3.md`; the new falsifier is
`verification/openmath/o1thr_rev3_depth2_check.py` (run FIRST, 2026-07-31, this
machine: ALL PASS on the repaired machine; both prior suites re-run unchanged:
ALL PASS).

## 0. Pass-2 findings → dispositions (no silent drops)

| # | pass-2 finding (anchor) | class | disposition |
|---|---|---|---|
| F1 | "(M6a)'s [Definition of harvesting] tag covers substantive, f-dependent content" — (R1) beyond the window + no-phantom, hidden under a definitional tag; single-assumption headline falsified | GAP (load-bearing) | **DECLARED + PROVED** (brief §2.5): named condition **(M6c)** ((i) beyond-window (R1); (ii) no-phantom), threaded through its three consumers (SPAN roster totality; Theorem 2(b) Case 1 — where it turned out the consumer is really REAL≡/the definition of REALIZED; Theorem 3 (F1)/(F4)). PROOF: Lemma WGEO (+ ROOT-M/VAL1/KEY1/DIV1) — outright at root states and first transitions over degree-1 root keys; modulo two NAMED citation-grade inputs (V1)/(V2) (MacLane augmentation multiplicativity; GMN key-form/development/residual dictionary) at general states. The same lemmas DISCHARGE (M6b)(i) and the consumed (N4)-upper (Corollary VTX). The headline is corrected everywhere (§0/§2.4/§8): interface residue = (M6b)(iii) AUX + lower (N4) band + (V1)/(V2) beyond the displayed perimeter |
| F1′ | (consequence, surfaced by the proof attempt) | — | **THE ROUND'S HEADLINE** (§1 below): making (M6c) precise exposed that rev 2's §1.1 w-recursion and §1.4 window heights were NOT the OM composite — the depth-2 falsifier REFUTES the rev-2 literal (plain) reading (440 + 7,472 countermodels) and confirms the sloped MacLane composite (41,720 instances, 0 violations). §1.1/§1.3/§1.4 repaired (displayed, flagged in place) |
| F2 | "'realized' equivocates between two inequivalent notions"; §1.3 Note's "exactly" unproved; saturated-state extensions not excluded | GAP | **FIXED** (brief §1.3, §2.5): ONE notion **REALIZED** := READ ∧ LAWFUL ∧ no-proper-prefix-saturated (record-only third clause); every §5–6 use audited to it (§2 below); the execution identification is the displayed **Lemma REAL≡** (conditional on (M6a)+(M6b)+(M6c)), replacing the silent identification. The plain-reading falsifier even exhibits the audit's saturated-state worry concretely (a phantom face at a saturated state, T-F first plain3 instance) |
| F3 | Theorem 2(a)'s unconditional status conflicts with its hypothesis; "canonical" dangling | GAP | **FIXED** (brief §5, §0, §8): 2(a) restated with REALIZED — an unconditional (nearly tautological) restriction of Theorem 1 + record-only clause transfer; "canonical" purged from §0 and §5; the ledger row now says exactly this, with the execution reading priced separately (REAL≡) |
| F4 | σ-count formula uses undefined "decided-σ count"/"typemult" and an unproven exhaustion | GAP | **FIXED by scoping + an honest OPEN caveat** (brief §6): D_σ(N) DEFINED with the thr(T) ≤ N clause inside; the displayed equation is exactly what is proved; caveat **(E-N)** (can a level-N box fiber a thr > N tree?) stated OPEN, with the audit's own warning that the plausibility argument is not a proof; "typemult" → type(T) |
| F5 | root window's face confinement used but not stated | GAP (minor) | **FIXED** (brief §2.5 Lemma ROOT-M, displayed proof: w_0(B_m) = 0 from ord_φ̄(f̄) = m, faces confined to [0, m], beyond-window strict); cited in (W-ADD) and in §1.4's window display (which also replaces the "0..m-and-beyond" gloss) |
| F6 | garbled sentence in Theorem 3(a) | editorial | **FIXED** (brief §6): the instantiation displayed cleanly (N := t, M = M′ = N) |
| m1 | §0 gloss omits the ceiling | minor | **FIXED** (§0: "1 + the largest ⌈de-normalized intercept⌉") |
| m2 | integer-valuedness of w_i cited but never proved | minor | **FIXED** (§1.1: one-line induction displayed) |
| m3 | P_β^+, irrVerdict, IrrHalts/NsHalts undefined | minor | **FIXED** (§2.3: P_β^+ displayed; §1.4: IrrHalts/NsHalts/irrVerdict displayed) |

Everything pass 2 verified is carried byte-stable EXCEPT where a listed
disposition touches it; the two verified-section touches forced by F1′ are §1.1
(the w-recursion: develop in Φ_i with γ_{i+1} = e_i·w_i(Φ_i) + h_i, i.e. the
MacLane composite, in place of rev 2's Φ_{i+1}-development) and §1.3/§4 (the
(R1)/(R2) heights carry the explicit slot shear u^{(i)}_j = w_i(B_j) + j·γ̂_{i−1};
Theorem 1's bullets swap thresholds ℓ_i(j) → β_{i,j} = ℓ_i(j) − j·γ̂_{i−1} ≤ I_i
with one added shear-cancellation sentence — the proof's structure, (†), DEV,
POS, R-LOC uses are UNCHANGED, and POS's §2.2 text is verbatim-stable under the
new recursion). These are definition repairs to the machine, made in the open
with the machine countermodels displayed (§9 T-F); pass 3 should re-verify §4
against them.

## 1. THE ROUND'S HEADLINE — the (M6c) proof forced a convention pin, and the falsifier refuted the alternative

Chasing Finding 1 mathematically (the OM principal-part-length genre, as the
pass-2 report suggested) produced Lemma WGEO: with the window points read in
the SLOPED, SHEARED heights u_k = w_{i+1}(C_k) + k·γ̂_i (w_{i+1} the MacLane
composite, γ̂_i the key height), the full successor development satisfies
min_k u_k = γ (the parent side value), first attained EXACTLY at k = μ — via a
two-step argument from the package's own stock: a division/development identity
(DIV1, elementary at the displayed perimeter) plus an initial-form ord_ψ
argument (VAL1/KEY1: weighted Gauss lemma in 𝔽_p[x̄, p̄] + the degree block
ψ_hom ∤ in(C_k)). Everything else falls out by convexity: all window faces
strictly descend to the vertex (μ, γ); the full polygon's principal part IS the
window hull ((M6c)(ii)'s geometric content); beyond-window points sit strictly
above every face line ((M6c)(i)); C_μ ≠ 0 and the (N4)-upper follow free
(Corollary VTX), shrinking (M6b).

But rev 2's literal machine did NOT read windows this way: its recursion made
the order-≥1 heights effectively unsloped. Per the falsifier-first rule the new
depth-2 checker (`o1thr_rev3_depth2_check.py`) probes BOTH readings at every
depth-1 state of five configs ((p,n,M) = (2,3,4), (2,4,4), (3,3,4), (3,4,3),
(2,6,3); 41,720 (box, site) instances, 7,912 with beyond-window slots):

* **Sloped (the repaired machine): 0 violations** of T-F.1 (vertex law
  min u = γ first at μ), T-F.2 ((M6c)(i)), T-F.3 ((M6c)(ii)), T-F.4
  ((N4)-upper).
* **Plain (rev-2 literal): REFUTED** — 440 beyond-window support violations
  (first: f = X⁴+2X³+2X², p = 2 — the harvested face line meets slot 2, beyond
  the window, with equality) and 7,472 principal-part/window mismatches
  (phantom faces on beyond-window support; first: f = X³+2X², p = 2, at a
  SATURATED state — precisely the pass-2 saturation worry, machine-realized).
  The two readings harvest different depth-2 face data (e′, h′) in
  41,406/41,720 instances.

So (M6c) is FALSE for the rev-2 literal machine and PROVABLE for the OM
composite; the §1.1 pin is forced, not stylistic. The pass-2 remark that the
depth-1 falsifier is structurally blind to this content is confirmed in the
strongest way: the first depth-2 probe found a definitional defect that every
depth-1 test (T-A..T-E, 61,079 instances) had passed over.

## 2. The realized-audit table (Finding 2's §5–6 sweep)

| use (rev-2 wording) | rev-3 resolution |
|---|---|
| §1.3 Note "site-reading is exactly membership of the pruned run set" | true BY DEFINITION of REALIZED on the record side; execution side = Lemma REAL≡ |
| 2(a) "the canonical run realizes the site" | REALIZED(f_x, H·ν); unconditional; "canonical" purged |
| 2(b) statement "children realized on f_{x′}" | REALIZED children; roster equality via (F1) + 2(a) |
| 2(b) "(if o is saturated there are none... by (M6a))" | by REALIZED's prefix-non-saturation clause (definitional) |
| 2(b) Case 1 "realized children are harvested, and harvested records are lawful" | unnecessary: REALIZED ⊇ LAWFUL by definition; the harvested-record content moved to (M6c)(ii) where it is proved |
| SPAN "a candidate is READ-realized in full by (M6a)+(M6b)" | candidate ⟹ REALIZED via (M6a) + (M6c)(i) + (M6b)(i)/VTX (READ), displayed law list (LAWFUL), decided-tree prefixes (clause 3) |
| Thm 3 (F1) fwd/backward, (F2), (F4) | REALIZED throughout; non-ns-halt witnessed via (M6c)(ii) at (F1)-fwd and (F4) |

## 3. What the rev-3 brief now claims (delta to rev 2)

* Theorem 1 / 2(a): PROVED OUTRIGHT for the repaired machine, every policy,
  every box-free AUX (2(a) in the REALIZED form). §4's proof needs pass-3
  re-verification against the sheared clause displays (structure unchanged).
* Theorem 2(b) / 3: PROVED MODULO the reduced residue — (M6b)(iii) AUX at
  harvest + the lower (N4) band (consumed only by REAL≡) + (V1)/(V2) at states
  beyond root states and degree-1 first transitions. (M6c) and the (M6b)
  kernel are PROVED on that perimeter (§2.5). Theorem 3(c)'s count is scoped
  by the OPEN caveat (E-N).
* NEW displayed objects: u-heights/γ̂ (§1.1), REALIZED (§1.3), (M6c) + Lemmas
  ROOT-M/VAL1/KEY1/DIV1/WGEO + Corollary VTX + Lemma REAL≡ (§2.5), D_σ(N) and
  (E-N) (§6), IrrHalts/NsHalts/irrVerdict, P_β^+.

## 4. Files

* `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md` — the self-contained
  rev-3 brief (hand THIS to pass 3).
* `verification/openmath/o1thr_rev3_depth2_check.py` — NEW depth-2 falsifier
  (T-F; ALL PASS sloped; plain-reading refutation counts 440/7,472 reported).
* `verification/openmath/o1thr_rev2_checks.py`, `o1thr_persite_check.py` —
  UNCHANGED depth-1 suites (re-run 2026-07-31: ALL PASS; still valid for the
  repaired machine — root windows are unsheared, and read 0's (R5) uses w_0).
* Rev-1/rev-2 artifacts left in place for the audit trail.

## 5. Verification protocol note

PROVED-UNVERIFIED until fresh-context passes accept it. Suggested pass-3
charges beyond the standard: (i) re-verify Theorem 1's bullets against the
sheared (R1)/(R2) displays (the one verified section with a forced edit);
(ii) re-derive WGEO(b)'s ord argument and check the degree-block step; (iii)
audit that (V1)/(V2) are consumed EXACTLY where §2.5 says (nothing else leans
on multiplicativity); (iv) check REAL≡'s (N4)-lower consumption is the only
one; (v) the open items: (E-N), the (V1)/(V2) attributions (exact
MacLane/GMN numbers), general-d_0 first transitions (the KEY1/DIV1 bookkeeping
over K_0[T, p̄] is sketched in-context but deliberately left inside the
(V1)/(V2) bucket); a depth-3 falsifier (order-2 states, where (V1)/(V2) are
genuinely consumed) is the right next numeric investment.
