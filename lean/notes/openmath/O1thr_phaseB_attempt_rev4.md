# O1thr — the per-site read package — Phase-B attempt REV 4 (Fable, 2026-07-31)

Repair of the pass-3 hostile verification (V24, `V24_o1thr3.jsonl`; model-diverse
Codex verifier with literature access) of the rev-3 brief
(`O1thr_phaseB_verifybrief_rev3.md`). Pass-3 verdict: **UNSOUND** — 3 critical,
5 justification gaps. Crucially, pass 3 also RE-VERIFIED the parts rev 3 was
dispatched to check: "No new substantive failure appears in Theorem 1, POS, DEV,
or R-LOC"; the §4 sloped re-derivation (the sheared thresholds β_{i,j}, the
(†′) rederivation, DEV/POS/R-LOC at pulled-back heights) passed with one wording
gap; WGEO's graded-cancellation core was ruled "conditionally valid" with its
condition exactly the (V2) clauses. All three criticals are PACKAGING defects
(a circular quantifier guard, a policy over-claim, a mislabeled kernel), not
convention or transport failures. This rev repairs ALL findings. The repaired
self-contained brief is `O1thr_phaseB_verifybrief_rev4.md`. No falsifier change
was needed; all three suites re-run unchanged (2026-07-31, this machine):
T-A..T-E ALL PASS, T-F ALL PASS (41,720 instances, 0 sloped violations,
440 + 7,472 plain-reading refutations reproduced).

## 0. CHURN CHECK (the dispatched question) — the pin STANDS; not churn

Round 3 pinned the machine convention (sloped MacLane-composite window heights,
§1.1) after the depth-2 falsifier refuted the plain reading. The standing rule:
if pass 3 had found the PIN wrong again, that would be churn, forcing a rescope
to the depth-1+root perimeter. **Pass 3 did NOT find the pin wrong.** It
re-verified Theorem 1, POS, DEV, R-LOC and §4 against the sheared displays and
confirmed them; its WGEO analysis is conducted INSIDE the sloped convention and
validates the graded argument modulo (V2). The criticals are quantifier/scope
defects orthogonal to the convention. Verdict: REPAIR, no rescope. (Noting an
irony: the honest OUTRIGHT perimeter after repairing the policy finding lands
exactly on the depth-1+root, standard-lift slice — the same territory the churn
contingency named — but as the proved slice of a wider conditional package, not
as a retreat of the claims.)

## 1. Pass-3 findings → dispositions (no silent drops)

| # | pass-3 finding (anchor) | class | disposition |
|---|---|---|---|
| C1 | "(M6c) is quantified [at] REALIZED non-halted o … used … to establish that the parent is non-ns-halted … That is circular" (REAL≡ ⟸) | CRITICAL | **FIXED by requantification** (brief §2.5): the §2.5 setting and (M6c) drop the halting guard entirely — the state hypothesis is only "creating read satisfies (R1)-all-slots + (R2) on f" (root states: ROOT-M's ord_φ̄(f̄) = m); (ii)'s child hypothesis is WEAKENED to READ + (N1) (the proof never used more); ¬NsHalts becomes a displayed CONCLUSION of (ii). No proof in §2.5 ever used the guard — the fix is pure statement surgery. REAL≡'s ⟸ is rewritten non-circularly: prefix READ + (N1) → (M6c)(ii) → principal face → non-halted → (M6a) harvest. T-F had already enumerated ALL depth-1 states (saturated + ns-halted included; the checker applies T-F.2/3 unconditionally, and rev 3's first plain-reading countermodel was itself a saturated state), so the widened quantifier is exactly the falsifier-confirmed one — noted in §9 |
| C2 | the same circle at Theorem 3: (F1)-fwd pruning and (F4) cite (M6c)(ii) at states whose non-halt is being proved | CRITICAL | **FIXED** (brief §6): both legs rewritten against the requantified (M6c)(ii) — the tree child (REALIZED at x′ by 2(a)) carries READ + (N1); (M6c)(ii) with no halting hypothesis exhibits its side as a principal window face; NsHalts fails. Non-circular by construction |
| C3 | "Arbitrary-policy coverage is false as stated": policy = any monic lift of the right degree, but KEY1 assumes the standard lift; "mere monicity and degree are insufficient" for MacLane's Thm 4.2 | CRITICAL | **FIXED by honest scoping** (brief §0, §1.1, §2.5, §8 S-3): (V1)/(V2) are RESTATED as key-COMPLIANCE conditions on the policy's assigned keys (not facts about arbitrary lifts); Theorems 2(b)/3 are claimed for compliant policies only; the standard lift is a displayed HYPOTHESIS of KEY1, and VAL1/KEY1/DIV1 = the proof that standard-at-degree-1-root policies are compliant there; "existence of policies is trivial" is scoped (existence of COMPLIANT keys = the MacLane/GMN citation, not proved). Theorems 1/2(a) remain every-policy (pass 3 concurs 2(a) "remains valid"). T-E/T-F used exactly the standard lift, so the falsifier perimeter = the proved perimeter |
| G1 | root harvest kernel "reported as proved but only tested": ledgers claim PROVED at root states while Corollary VTX defers root children to T-E; SPAN consumes it | GAP (load-bearing) | **FIXED by PROVING it + relabeling** (brief §2.5 Corollary VTX): VTX recast at ANY harvest state o via WGEO at the child state o·ν′, whose hypotheses at a FRESH harvest are supplied by (M6a) window clauses + (M6c)(i)-at-o (= ROOT-M at root states); for root-harvested children over degree-1 root keys with the standard lift this runs entirely on VAL1/KEY1/DIV1 — PROVED OUTRIGHT, T-E demoted to corroboration. Simultaneously the one-level over-claim in rev 3's "outright at root states AND first transitions" is corrected: children harvested AT first-transition states have their vertex law at the ORDER-2 state — (V1)/(V2) territory. §2.4/§8 ledgers rewritten to the corrected perimeter |
| G2 | (V2a)'s "Φ_i-degree" undefined in gr(w_{i+1}); membership of in(C_k) unstated — "exactly what WGEO consumes" | GAP | **FIXED** (brief §2.5): (V2a) restated as the exact consumed block — in(Φ_{i+1}) = unit·ψ̂_hom and ψ̂_hom ∤ in(B) for every nonzero B of deg < deg Φ_{i+1}; KEY1 gains the bridge sentence (deg B < eg ⟹ in(B) has x̄-degree < eg ⟹ ψ_hom ∤ in(B)); WGEO(b) cites the restated form |
| G3 | WGEO(b) "attained at k = μ and at NO k < μ" is FIRST attainment; global-uniqueness readings unsupported | GAP | **FIXED by flagging** (brief §2.5 WGEO(b)): the statement now says FIRST attainment explicitly, notes u_k = γ at k > μ is neither excluded nor needed, and that (c)/(d) consume only first attainment (T-F checks exactly first attainment — `min(argmins) == mu`) |
| G4 | DIV1's "top reduction step subtracts a_d·X^{d−D}·Φ_1" not weight-graded for general Φ_0 = X − a | GAP | **FIXED** (brief §2.5 DIV1): the division is performed Φ_0-adically (b_d·Φ_0^{d−D}·Φ_1; at d_0 = 1 this IS the unique X-division), the displayed weight computation runs on Φ_0-monomials, top-slot cancellation noted (ψ̂_g = 1) |
| G5 | §4 transfers READ but "the machine reads" = REALIZED; the record-only prefix-non-saturation conjunct omitted | GAP | **FIXED** (brief §4 proof, one sentence): the third clause is record-only, hence shared; REALIZED reduces to READ on both sides |
| G6 | (V1)/(V2) citation status: (V1)'s cite should name Thm 4.2; (V2) "not citation-grade in its present bundled form" — no theorem numbers, no normalization dictionary | GAP | **FIXED by downgrade + loci** (brief §2.5 status bullet, §8 S-4, §10): (V1)/(V2) carry the verifier-checked loci (MacLane Def. 4.1/Thm. 4.2; GMN Prop. 2.10/Thm. 2.11 + §2.6 Theorem of the product) and an explicit statement that the translation into the package's (w_i, γ̂_i, Φ_i) normalization is an OWED open correspondence — they are consumed as named ASSUMPTIONS on the policy's keys, "citation-grade" retracted |
| G3′ | (verifier, §1) "unit-plus-multiple-of-ψ̂_hom bracket … imprecise: not divisible does not mean unit" (conclusion salvageable without primeness) | GAP | **FIXED** (brief §2.5 WGEO(b)): the bracket step replaced by the displayed factorization in(f) = ψ̂_hom^m·β with ψ̂_hom ∤ β and the two-sided ord pin via domain cancellation ((V1)) — no primeness, no unit status |
| F-SELF | (self-caught while rewriting the consumers) rev 3's "a prefix of a REALIZED pruned run is one" silently assumed AUX restricts to prefixes — AUX was "ANY predicate of the record chain" | GAP (self-reported) | **FIXED** (brief §1.2): AUX's parameter definition now requires PREFIX CLOSURE (true of the source machine's per-transition admissibility bundle by construction), flagged in place; consumed at Theorem 3 (F1)-backward and REAL≡'s walk-standing step, both now citing it |

Verifier-confirmed content carried byte-stable: Theorem 1's clause transfers and
(†)/(†′), POS/DEV/R-LOC, §4's shear cancellation, WGEO(a)/(c)/(d) and the (b)
skeleton, ROOT-M, VAL1, KEY1's proof body, SPAN's ledger arithmetic, Theorem
2(b)'s cases, Theorem 3's cylinder/scaling/uniqueness, §7, T-A..T-F rows. The
diff against rev 3 (39 hunks) touches only the listed repair sites.

## 2. What the rev-4 brief now claims (delta to rev 3)

* Theorem 1 / 2(a): unchanged — PROVED OUTRIGHT, every policy, every box-free
  (now: prefix-closed) AUX.
* Theorem 2(b) / 3: PROVED MODULO the residue for **compliant policies**:
  (M6b)(iii) AUX-at-harvest + the lower (N4) band + (V1)/(V2) key compliance
  beyond the proved slice. The claims are NARROWER than rev 3's ("every
  policy" retracted per C3) and more honest about (V1)/(V2) (assumptions with
  owed dictionary, not citation-grade).
* The proved slice, now correctly labeled: (M6c) at root states (any policy,
  any d_0); WGEO/(M6c) at degree-1 first-transition states and the vertex
  kernel for root-harvested children — both under the standard first key.
  NEW at rev 4: the root-harvest kernel is PROVED (was: machine-checked only);
  (M6c) carries no halting guard (was: circular at its consumers).
* Open, unchanged: (E-N); the (V1)/(V2) dictionary (now an explicit owed
  correspondence); general-d_0 first transitions; depth-3 falsifier.

## 3. Files

* `lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md` — the self-contained
  rev-4 brief (hand THIS to pass 4).
* `lean/notes/openmath/V24_o1thr3.jsonl` — the pass-3 report repaired against.
* `verification/openmath/o1thr_rev3_depth2_check.py`, `o1thr_rev2_checks.py`,
  `o1thr_persite_check.py` — UNCHANGED (re-run 2026-07-31: ALL PASS). No new
  numerics: every repair is statement/quantifier surgery on perimeters the
  suites already cover (T-F's no-filter state enumeration and standard lift
  are exactly the requantified/rescoped forms — brief §9 rev-4 note).
* Rev-1/2/3 artifacts left in place for the audit trail.

## 4. Verification protocol note

PROVED-UNVERIFIED until fresh-context passes accept it. Suggested pass-4
charges beyond the standard: (i) check the requantified (M6c) against every
consumer (REAL≡, Theorem 3 (F1)/(F4), SPAN roster totality) for any residual
non-halt presupposition; (ii) re-derive Corollary VTX's fresh-harvest
application of WGEO (does (M6a) + (M6c)(i)-at-o really supply WGEO's hypothesis
at o·ν′, including at the root?); (iii) audit the compliant-policy scoping for
completeness — is (V1)/(V2) compliance along T's chains SUFFICIENT everywhere
§2.5 is consumed, and is the standard-lift slice claimed nowhere wider than
VAL1/KEY1/DIV1 reach; (iv) the WGEO(b) domain-cancellation rewrite; (v) AUX
prefix closure: legitimate parameter restriction vs. smuggled strengthening
(the source machine's AUX is per-transition, so it restricts — but check the
claim is used only where cited). Open items as in rev 3 §5 plus: the root-track
binding inside REAL≡'s walk bookkeeping (which track of f̄ owns a READ chain's
root state) remains implicit in the walk definition, as at rev 3 — pass 3 did
not flag it; a pass-4 eye is welcome.
