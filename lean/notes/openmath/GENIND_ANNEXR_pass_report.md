# GENIND ANNEX R — scoped hostile pass (2026-08-10)

## VERDICT (filled at commit 2, from the artifacts)

PENDING AT SEAL — this skeleton commits the charge, the surfaces, and
the sealed fresh instrument (`verification/openmath/
genind_annexrpass_fresh.py`, preregistered P1–P5 + teeth T-P3/T-P5)
BEFORE the fresh run; the verdict and findings land in commit 2 from
the committed outputs.

## Charge and scope

GENIND (`GENIND_PROOF_2026-08-08.md`, the general two-species
induction) was ACCEPTED 2/2 at wave 14 (PE7 + PE8 clean; body
byte-frozen, lines 1–2464 md5 `14fa6afc`). The Codex ratification then
returned CHALLENGE (6/6 CONFIRMED, 0 CRITICAL;
`CODEX_GENINDRAT_2026-08-09.md`), and the wave-16 unit (killed
mid-storm by a server error after R1, resumed as wwb8dpzum) landed
**ANNEX R** — the repair queue R1–R6 + close + the GENHN
supplier-movement dated append, note lines 2552–3054 — which the
ledger records as "honestly disclosed NOT-hostile-passed (its scoped
pass queues behind the chain notes)". This pass is that queued item.

Scope: the annex stack ONLY (R1–R6, close, movement append). The
accepted body is frozen and 2-clean — re-litigated NOWHERE; checked
only for annex↔body contradiction. Surfaces: (1) each annex claim
re-derived against the note's own lemmas; (2) the annex↔body seam;
(3) sibling seams (gauge/wrap per 59c1966, ψ vs ψ^{(w)},
certificate-free attainment, stage-index conflation); (4) the machine
legs the annex cites (pins + isolated re-run); (5) one FRESH
out-of-battery route stressing the annex's newest claims
(ANNEX-LEMMA GENIND-C1 / ANNEX-THEOREM GENIND.C′ + the R4/R6
arithmetic). Protocol: quote-and-classify, fix nothing; charge bar =
nothing GAP-or-worse is CLEAN.

## Findings (filled at commit 2)

PENDING AT SEAL.

## Machine and freeze verifications (executed pre-seal; all pins as claimed)

* Body freeze: `head -c 158427` = `head -n 2548` = md5
  `eefcf6584bbb0917875e77c9fcab7a9e` at worktree HEAD ✓ (the annex
  header's 158,427-byte / 2,548-line claim exact); PE8 body freeze
  lines 1–2464 md5 `14fa6afc…` ✓.
* R1 slice: HEAD lines 2549–2745 byte-identical to a1525ea's ✓ (the
  close's claim; a1525ea's file ends at line 2745 — R1 was the
  casualty boundary).
* Supp leg: `genind_annexr_supp.py` md5 `42fd603e…` ✓, committed
  output md5 `d938ad82…` ✓ (commit f5271e4, 08-09 11:24); ISOLATED
  RE-RUN (fresh copy in /tmp, sympy venv): exit 0, output
  byte-identical to the committed artifact ✓.
* Sealed runner untouched: `genind_checks.py` md5 `e7ca150b…` ✓; the
  two CS4-F gate lines read verbatim `while 4 * k <= N - 1:` at
  EXACTLY lines 709 and 869 ✓ (R4.2's cite).
* PE8-report cite: the non-monotonicity sentence sits at exactly
  L176–178 of `GENIND_passPE8_report.md` ✓ (R6.1's "its L176–178").
* Codex-finding quotes: R1.0/R2.0/R3.0/R4.0/R5.0/R6.0 each checked
  against `CODEX_GENINDRAT_2026-08-09.md` — faithful (condensations
  only, no strengthening or weakening of any charge) ✓.
* Movement append pins: all 8 enumerated GENHN commits exist with the
  claimed content and timestamps (E1 bc1b996 / E2 961d0ff / E3
  46bf675 / box 58b1080 09:23–09:26; r2 d16869c/7650b20/438608a/
  9636b7e 11:44–11:48); `git log 850e77e..9636b7e --
  GENHN_PROOF_2026-08-08.md` = EXACTLY 8 commits ✓ (the "exactly the
  eight commits" record sentence is true as an enumerative claim);
  the n ≤ 7 sealed / n ≥ 8 adds [GENHN-TOW-1] split matches
  d16869c's own restated clause ✓.

## Re-derivations against the note's own lemmas (executed pre-seal)

* R1.1 m = 2 ground: the S5.2 recursion at m = 2 is
  u(N) = Q^{N−1} + Σ (Q−1)Q^{k·c(2)}u(N−2k) with c(2) = 1 (body L125
  defines c(m) := m(m−1)/2; body L906 displays the recursion) — the
  annex's coefficient (Q−1)Q^k is exact ✓. The telescope re-derived
  here: u(N) − Q·u(N−2) collapses the k ↦ k+1 re-indexed sum to
  Q^{N−1} − Q^{N−2} + (Q−1)Q·u(N−2), i.e.
  u(N) = Q^{N−1} − Q^{N−2} + Q²u(N−2) ✓ — the gloss "subtracting the
  k ↦ k+1 re-indexed sum" is literally correct. Closed forms checked
  by hand at N = 3, 4, 5 against BOTH the sum and the telescoped
  recursion ✓; both closed-form branches equal
  Q^{M−1} + ⌊(M−1)/2⌋(Q−1)Q^{M−2} ✓ (the HEX3.A R(M) tie).
* R1.2(i): D_l ≤ v(a₀) from the j = 0 term of min_j(v(a_j)+j·k_l) ✓;
  {v(a₀) ≥ D_l} pins π-levels 1..D_l−1 of a₀ (level 0 pinned in
  every state by ā_j = 0, per S1 read at R3's rider) = d(D_l−1)
  q-digits = relative mass Q^{−(D_l−1)} exactly ✓; leg E's three
  instances re-computed by hand: M6 (q−1)²q^{−11} ≤ q^{−3},
  PSTEEP3 2^{−7} ≤ 2^{−2}, PSTEEP4 2^{−11} ≤ 2^{−3} ✓.
* R1.2(ii)–(iv): union bound over the fibration product ✓ (standard;
  machine at r ≤ 3 in the supp leg, r = 4, 5 in the fresh leg);
  GROWING-regime exponent composition −(D_l−1)−(M_l−c) = −(N−c−1)
  from D_l + M_l = N ✓; BOUNDED regime carried by the prefactor
  alone ✓; genre count p̃(m)·N^m from partition types × one integer
  slope ≤ N−1 per side ✓.
* R1.3 (the annex's heaviest new derivation): the α-recomposition is
  EXACT — the α(k) relative-mass factor (Q−1)Q^{−k·m(m+1)/2} (body
  L137) times the child-total renormalization Q^{mk} equals
  (Q−1)Q^{−k·c(m)} because m(m+1)/2 − m = m(m−1)/2 = c(m) — the
  displayed Σ_k(Q−1)Q^{−k·c(m)} ≤ 1 for c(m) ≥ 1 is then the right
  condition, satisfied at every m ≥ 2, with EQUALITY at m = 2
  (c = 1): the ground case is genuinely sharp. (A first-read
  suspicion that the display dropped a Q^{mk} dissolved exactly
  here — the body's c(m) := m(m−1)/2 is what makes the display
  correct; verified symbolically in the fresh leg P3.)
  Lexicographic (degree, window) shape ✓: β-children descend in
  degree (GENIND-1(iii)), α descends in window at fixed degree;
  window-1 base = R3's rider ✓; the K-absorption polynomial
  inequality has positive leading coefficient m·B·N^{B−1} ✓.
* R2: pivot species enumerated against the body's own displays —
  binomial "triangular with unit diagonal" verbatim at body L321 ✓;
  monic-divisor long division has the divisor's lead (= 1) as pivot
  ✓; the non-unit-lead cofactor is an OUTPUT, never a divisor row ✓;
  Codex's toy (x+π)y mod π² is exactly the non-monic-multiplier
  shape ✓; M6's committed constant fibers q⁹/q⁷ (512/128 at q = 2)
  are the right no-collapse signature ✓.
* R3: at N = 1 the state count q^{dm·0} = 1, a_j = 0 forces
  v(a₀) ≥ 1 = N → DRAIN before any digit ✓; DRAIN locus law = 1 ✓;
  α needs mk ≤ 0 (none), polygon events need v(a₀) < N (none) —
  exactly one of five events inhabited ✓; u(2ℓ+1) at ℓ = 0 returns
  1 ✓ (coherent with the closed form).
* R4: floor 4k ≤ N−1 re-derived from the genre heights (4k,3k,2k,k)
  + DRAIN-first keying (v(a₀) = 4k must be ≤ N−1) — the same
  derivation species as the body's own CS4-E floor (PE1-M3) ✓;
  (2,2,1): display 2^{−6} non-integer vs true 0 ✓; (2,5,1): 2⁶ = 64
  ✓; fresh points in P5.
* R5: the degree-level parse re-checked at the three consuming sites
  named (S5.2 positive-density sentence, S6 conditionality
  geography, S7.4 finite enumerability) — none needs the stage-level
  parse ✓; the m = 4/5/6 instance list is coherent under the reading
  the annex itself fixes (an m-key cluster system whose OWN
  refinement opens CS: QRT at m = 4 "the 4-key system's own", S5.3
  embedded genres at m = 5, M6/SS6 at m = 6 — M6's locus law
  (q−1)²q^{6N−17} > 0 with the composite right side IS a CS event of
  the (q,6,1) system) ✓; the general-m stage-level statement stays
  explicitly unclaimed ✓ — this annex WEAKENS no accepted sentence,
  it fixes the parse Codex showed was the only supported one.
* R6: ∂/∂u₁(u₁T₂+T₁u₂−u₁u₂) = T₂−u₂ ≥ 0 on u₂ ≤ T₂ ✓ (the PE8
  sentence is false as quoted); ∂/∂u_i[ΠT−Π(T−u)] = Π_{j≠i}(T_j−u_j)
  ✓; identity-vs-bound separation consistent with the body's [r1]
  record (its two load-bearing sentences remain true) ✓.
* Sibling seams: gauge/wrap (erratum 59c1966), ψ vs ψ^{(w)},
  certificate-free attainment, stage-index conflation — grep over
  the full annex stack (lines 2552–3054): ZERO occurrences of the
  seam vocabulary; those seams live in the tower notes and have no
  contact surface here. The movement append keys conditionality on
  the DEGREE n (not a stage index) and touches no tower-key display.

## Fresh route + verdict: commit 2.
