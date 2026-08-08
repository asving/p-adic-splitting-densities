# SIGMALAW passPE3 — hostile verification report (THE ACCEPTING ATTEMPT)

**Target:** `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` at HEAD.
Byte-freeze verified first: md5 a50d3d5f09d06e8567a20de24d0cf799 at HEAD ==
the r1 commit 6b24942's blob exactly; the note has not changed since r1
(seal 8064ae3, verdict 59c1ff2, PE1 9b0117d, r1 6b24942, PE2 6e57e03,
PE2-adjudication a049d6c). **Charge:** fresh-context hostile pass 3 at full
acceptance rigor (counter 1/2 after PE2 clean-on-note; a second consecutive
clean pass ACCEPTS at 2/2); quote-and-classify; fix nothing; unmined veins =
(1) SL-L2's own proof re-derived line-by-line (both prior passes consumed
it), (2) the u_j closed form's THREE factors at a junction where all three
are simultaneously nontrivial (constructed), (3) the m = 1 base against the
ACCEPTED GRTW2's rk. 3 verbatim (byte-compare), (4) the §5 instrument-note
census (145 = 123 + 22, zero ξ₂ ≠ 1 ∧ g₂ ≥ 2) recounted from the committed
artifacts, (5) wild-card; machine re-run; fresh route differing from the
order-5 AND order-7 genres AND the algebraic λ-census.
**Verifier artifacts (not committed):** `/tmp/pe3sl/pe3_fresh.py`,
`/tmp/pe3sl/pe3_partC.py`, `/tmp/pe3sl/pe3_partDE.py` (own
A_q/χ/ξ/Σ/U/E/u_j/Λ implementations written from the note's §1/§3
displays; own walker; own battery recount; own F₂₇/ord-13 genre with own
Rabin/disc irreducibility instrument; own mutants), outputs
`partAB.json`, `partC.json`, `partD.json`, `partDE.json`,
`partC_out.txt`, `partDE_out.txt`; fresh machine re-run in
`/tmp/pe3sl/run/`.

## VERDICT: CLEAN — 0 CRITICAL + 0 GAPS + 0 minor. SECOND consecutive clean pass on the frozen note text; counter 2/2 — **THE Σ-LAW NOTE IS ACCEPTED**; fold owed to the orchestrator.

Every unmined vein was pressed and every claim it touched CONFIRMED: SL-L2
re-derived line-by-line and machine-keyed BY NAME for the first time (with
an off-perimeter Λ-control failing exactly where the ladder predicts); the
u_j three-factor composition constructed and green where all three factors
are simultaneously nontrivial (plus a 22-slot coverage census showing the
sealed battery already exercises it); the m = 1 base byte-compared clause-
by-clause against ACCEPTED GRTW2 (rk. 3, §3.4, §1.3/tex 1270, W2-L3) with
the r1 brackets verified byte-faithful against the seal blob and diff; the
§5 zero-sampling census recounted from spec-identical battery reproduction
to the digit; the §6R corrected figures re-derived leak-free by
construction; the machine leg bit-identical; a genuinely fresh F₂₇/ord-13
genre (new base field, new twist order, first prime g₁ > 4) green on all
laws with wrap tests and a three-factor slot at order 13; and a mutant
audit caught every seeded defect in the classes the sealed teeth do not
cover. The PE2 off-note finding's repair (GRTW2 tail erratum) is verified
landed and correct.

---

## §V1. VEIN 1 — SL-L2 re-derived line-by-line (the vein both passes consumed)

**Statement re-read:** Λ_q(w) := ε_q(w)·U_q(w)/Σ_q(ε_q(w)) = χ_q^{−w} for
every q ≥ 1, w in the level-q grid. Every step of the note's proof (lines
197–212) was re-derived independently:

* **Base q = 1:** ε₁U₁/Σ₁(ε₁) = ε₁·1/ε₁ = 1 = χ₁^{−w} (Σ₁ = id, χ₁ = 1). ✓
* **The reduction Λ_q = U_q·ξ_q^{−E}:** Σ_q(ε_q(w)) = ξ_q^{E(w)}ε_q(w)
  cancels ε_q — this is (SC-q) at y = 1, honestly deferred by the note to
  the REMARK/ladder (within-level order EC → SC → L2, PE2's §A.2 graph);
  consistent. ✓
* **The ε-exponent identity** ℓ′s − ℓu = (s − ℓw)/e: ℓ′s − ℓ(w − sh)/e =
  [s(ℓ′e + ℓh) − ℓw]/e = (s − ℓw)/e by ℓh + ℓ′e = 1 — re-proved, and
  machine-keyed against the engine's `eps` (expo = lp·s − l·u) on every
  weight of every Part-A sweep (assertion, 0 failures). ✓
* **z-part exponent:** U_q contributes −s(w)A_{q−1}; ξ_q^{−E} contributes
  +e_{q−1}A_{q−1}E = A_{q−1}(s(w) − ℓ_{q−1}w); total −A_{q−1}ℓ_{q−1}w —
  matches the note's display exactly. ✓
* **χ-part exponent:** −w₀(w) − γ_q·E(w) = [−w + s(w)γ_q − γ_q s(w) +
  γ_qℓ_{q−1}w]/e_{q−1} = w(ℓ_{q−1}γ_q − 1)/e_{q−1}; with γ_q =
  e_{q−1}w_{q−1}Φ_{q−1} + h_{q−1} and ℓh − 1 = −ℓ′e this is
  w(ℓ_{q−1}w_{q−1}Φ_{q−1} − ℓ′_{q−1}) — matches. ✓ Integrality of w₀
  (silently needed): w − s(w)γ_q ≡ w − ℓwh ≡ wℓ′e ≡ 0 (mod e_{q−1}) —
  holds for every integer w; re-proved. ✓
* **Collapse to the χ-recursion:** z_{q−1}^{−A'ℓw}·χ_{q−1}^{w(ℓwΦ−ℓ′)} =
  [χ_{q−1}^{ℓ′−ℓwΦ}z_{q−1}^{A'ℓ}]^{−w} = χ_q^{−w} — the §3.4 recursion
  falls out as an OUTPUT (the consumption note "no §3.4 theorem-content
  consumed" re-verified: only the χ/ξ definitions + Bézout + grid enter). ✓
* **Its (MATCH) consumption re-derived:** Λ_{q−1}(w_ν) = χ_{q−1}^{−w₀+νγ_q}
  makes the ν-part [z^{−eA'}·ξ_q^{−1}·χ_{q−1}^{γ_q}]^ν = 1 identically by
  the ξ_q definition, leaving exactly (U-REC) — re-derived, and (VD-q)'s
  per-ν comparison happens inside the faithful basis with ε_q(β) an exact
  common left factor and U_q(β) ∈ K_{q−1} a per-coordinate scalar (no wrap
  touched in (VD-q) itself; PE2's remark re-confirmed). ✓

**Machine key BY NAME (never run by any prior pass):** Λ_q(w) tested as an
element identity ε_q(w)U_q(w)/Σ_q(ε_q(w)) == χ_q^{−w} over weight sweeps,
own code: A-PB (F₉, ord-4 twist) q=2 0/46; A-SEPB (χ₂ = −1 live) q=2 0/22,
q=3 0/130; A-DBL-k1 (doubly-twisted perimeter) q=2 0/46, q=3 0/478 — ALL
GREEN on the perimeter. **Off-perimeter Λ-control (new):** the (2,1,2)-top
doubly-twisted chamber, where (EC-3) is infeasible for every k (my own
derivation: it needs ξ₃² = ξ₂, i.e. z₁^{2(2−2k)} = z₁², i.e. 4k ≡ 2 mod 8 —
no solution), fails Λ₃ on 708/946 weights while Λ₂ stays 0/46 — SL-L2's
perimeter scoping is real at the gauge-ratio level itself, exactly where
the ladder places it. VEIN 1: **CONFIRMED, no gap.**

## §V2. VEIN 2 — the u_j closed form with ALL THREE factors simultaneously nontrivial (constructed)

u_j = [z_m^{−k_jA_m}]·[ε_m(β_j)]·[U_m(β_j)]. Factor 1 needs a supported
slot j ≥ 1 at a twisted m ≥ 2 junction; the sealed SEPA/SEPB genres all
carry g = 1 top moduli, but my whole-battery factor census (§V4 walk)
finds **22 sealed walked slots** (B-genre interior-supported slots) where
all three factors are already simultaneously nontrivial — all green there.
Constructed here in addition (deg-2 NON-monomial tops over K₂ — outside
the sealed geometry): ℤ₃, (2,1,2)+(3,1,4)+(1,1,2), ψ₁ = y⁴+z₁^k,
ψ₂ = y² + a·y + b over K₂ = F₃^8 with a ≠ 0 (slot j = 1 supported).
Hand-arithmetic first: at k = 1, j = 1: A₂ = 52, γ₃ = 157, β₁ = 157;
factor 1 = z₂^{−e₂A₂} = z₂^{−52} ≠ 1 (z₂^{52} = z₁^{5k+4 mod 8} = z₁);
factor 2 = ε₂(β₁) = z₂^{E}, E = (1−157)/3 = −52 ≠ 0, = factor 1 ≠ 1;
factor 3 = U₂(β₁) = z₁^{−s·A₁} = z₁^{−2} ≠ 1 (s = 157 mod 3 = 1, A₁ = 2).
**Machine (own code): 14 walked rows, 21 slot samples, 7 slots with all
three factors simultaneously nontrivial, ledger identity + δ-law + phir
ALL GREEN (0 violations), c-tie exact, 7 separator slots, 7 non-involution
δ, 9 gap slots.** The three factors compose exactly as displayed at a
junction where each is individually falsifiable. VEIN 2: **CONFIRMED.**

## §V3. VEIN 3 — the m = 1 base vs ACCEPTED GRTW2 rk. 3, byte-compared

* **GRTW2 §3.4 rk. 3 (HEAD, lines 430–433):** "at m = 1 this is:
  c·z₁^{A₁e₁j} = 1 for every j ∈ supp(ψ_m) ∩ [0, g_m)". With GRTW2 §1.3's
  c = c₁^{e_mg_m}, c₁ = z_m^{−A_m} (tex 1270): c·z₁^{A₁e₁j} =
  z₁^{−A₁e₁(g₁−j)} = ξ₂^{g₁−j} (ξ₂ = χ₁^{γ₂}z₁^{−e₁A₁}, χ₁ = 1 — §3.4
  display lines 396–400). So rk. 3's byte law IS (EC-2) at Σ₁ = id, and the
  note's "(λ_j = 1 ⟺ θ^{g−j} = 1 at m = 1 — rk. 3 recovered)" is exact
  (θ = ξ₂^{−1}, and ξ^x = 1 ⟺ θ^x = 1). Support windows agree (both
  supp ∩ [0, g)). ✓
* **The r1 brackets quote the SEALED text byte-faithfully** (checked against
  the 8064ae3 blob and the 9b0117d→6b24942 diff): the removed REMARK really
  displayed "ξ_q^{g_{q−1}−i} = 1 on supp(ψ_{q−1})— EXACTLY the byte-share
  law of the junction below (GRTW2 §3.4 rk. 3 at level q−1…)"; the removed
  SL-C1 hedge really read "(SC)-type covariance when x is an
  ε-monomial-times-class (x = ε_m(β_j)^{−1}ψ_{m,j}, REALIZE R3), by the
  same wrap-invariance as §3's REMARK"; the removed consumption line really
  cited "the shared-below byte-share law". All three [r1] characterizations
  faithful. ✓
* **Statement freeze across r1:** every one of the 25 lines removed by r1
  is header/genre text, the §1 typo parenthetical, the REMARK display, the
  SL-C1 hedge, the consumption line, or §7 grade text — NO theorem
  statement display touched (diff-checked directly). ✓
* **W2-L3 = (VD-1) verbatim** (GRTW2 §2.4 display z₁^{τ₁(A)}R₁(A)(z₁) =
  ε₁(β)R₁v(A) vs P₁ = ε₁U₁Σ₁(H₁) with U₁ = 1, Σ₁ = id) and τ_q's form is
  W2-L3's τ₁ at level q, as §1 claims. Thm-phir constant cite (c₁, c,
  tex 1270) byte-consistent with GRTW2 §1.3, and my c-tie
  (c == z_M^{−A_M e_M g_M}) held at every walked junction of every genre
  this pass built. ✓ VEIN 3: **CONFIRMED.**

## §V4. VEIN 4 — the §5 instrument-note census + full §6R recount (own walk)

The ENTIRE sealed battery (OA `gen_battery()` + the runner's `gen_sepA`/
`gen_sepB`, spec-identical reproduction) was re-walked with MY OWN walker,
census code, and law checks (own χ/ξ/Σ/U/u_j/δ; engine
rres/read/actual_ratios/gap_scan as instrument) — 20 s, `partC.json`:

* **539 towers built, 0 rejects; 1,211 walked rows (539/527/145 by m) + 6
  SKIP** — §6R's row accounting exact. **0 LAW VIOLATIONS anywhere**
  (ledger identity both legs, δ-law, Thm-phir, c-tie — every walked slot).
* **Σ|supp| = 1,414** ⟹ the genuine per-family figures 2,828 (VDM both
  legs) / 1,414 (DELTA) / 1,414 (PHIR); **gap rows 317, gap slots 340** ⟹
  SL-GAP genuine 680 = 2×340; **SEP2 = 96, SEP3 = 27**; **INVREC = 218
  with ALL 218 on the OA geography** — my walk runs no teeth, so the
  no-leak census comes out at 218 directly: the r1 [r1] block's genuine
  decomposition (2,828/1,414/1,414/680, INVREC 218 exactly) is confirmed
  by construction, independent of PE1/PE2's leak arithmetic.
* **The §5 instrument-note census CONFIRMED TO THE DIGIT:** over all 145
  walked m = 3 rows, my own (ξ₂-trivial, g₂, ψ₂-Σ₂-fixed) census =
  {(True, 2, True): 123; (False, 1, False): 22} — the 22 all B3D (genre
  recount: ROSTER 2 + B3A 17 + B3B 50 + B3D 22 + SEPB 54 = 145, tied
  row-for-row to the committed JSON). **ZERO sealed rows with ξ₂ ≠ 1 ∧
  g₂ ≥ 2** — the zero-sampling disclosure is exact.
* **The §5 "acting characters were ±1" claim keyed row-wise (new):** on
  every OA-battery walked row carrying a δ ≠ 1 slot (179 rows = the 141
  m = 2 + 38 m = 3 of PE1's row census), ALL acting characters ξ_q
  (2 ≤ q ≤ m) satisfy ξ_q² = 1 — **179/179.** The involution-degeneracy
  explanation now rests on the characters themselves, not only on the
  Σ = σ′ coincidence census.

VEIN 4: **CONFIRMED.**

## §V5. WILD-CARDS

* **Mutant audit — the defect classes the sealed TEETH do NOT cover** (the
  teeth garble U, Σ-composite, and the print leg; nothing garbles the ε or
  z^{−k_jA} factors of u_j or the χ-correction inside ξ alone). With my
  own checker over constructed three-factor rows + SEPA/SEPB towers:
  MUT-dropeps (u_j without ε_m(β_j)): caught 10/10 visible slots;
  MUT-dropf1 (u_j without z_m^{−k_jA_m}): caught 1/1 visible slots;
  MUT-dropchi (ξ_q without the χ_{q−1}^{γ_q} correction, q ≥ 3): caught
  2/2 visible slots (SEPB m = 3). Every factor of the closed form and the
  χ-correction of the map is separately load-bearing — the note's u_j and
  Σ displays are not over-parameterized, and each ingredient is
  independently falsifiable against the engine.

* **PE2-finding disposition (acceptance diligence):** the a049d6c
  adjudication applied an ERRATUM to the GRTW2 tail; verified at HEAD: the
  erratum text now carries the GENUINE figures SL-VDM 2,828 / SL-DELTA
  1,414 / SL-PHIR 1,414 / SL-GAP 680 (= 2×340) with INVREC = 218 — the PE2
  transposition is cured, the erratum's own arithmetic is self-consistent,
  and the SIGMALAW note itself needed (and received) no edit. ✓
* **§5 hand-arithmetic re-verified** (the r1 instrument-note k = 1 tower:
  A₁ = 2, γ₂ = 13, w₂Φ₂ = 156, A₂ = 52, γ₃ = 157, χ₂ = z₁², z₂^{−52} =
  z₁^{3k+4 mod 8}, ξ₃ = z₁^{3k+6} = z₁^{6−5k mod 8}, ξ₃² = ξ₂ ⟺ k ≡ 1 mod
  4; SEP-B: A₁ = 1, χ₂ = −1, γ₃ = 41 odd, θ₃ = z₂^{20} = 1 while ξ₃ = −1)
  — all exact. ✓ The §7 [r1] arc-ledger pointer a00cf97 exists and is the
  PE1-recording commit. ✓

## §V6. MACHINE LEG

Runner `verification/openmath/sigmalaw_checks.py` at HEAD md5
92e7c22cb2c823909dc5ad6b03f61c32 == seal 8064ae3 byte-identical; committed
artifacts md5 a5daabf1…/70e5bd1d… == verdict 59c1ff2 byte-identical.
**Fresh full re-run (isolated copy, /tmp/pe3sl/run): exit 0, 18.4 s, 6,970
samples, ALL FAMILIES GREEN, SEP2 96 / SEP3 27; output byte-identical to
the committed artifact ex-timing lines; JSON identical except `elapsed_s`
(18.3 vs 18.5).** Committed-JSON direct recount ties §6R-as-corrected
exactly: 1,217 rows = 1,211 walked (539/527/145 by m) + 6 SKIP; Σ|supp| =
1,414; printed families 2,854/1,427/688/1,427 with 0 violations; gap rows
317 (37/197/83 by m), gap slots 340; SEP2 96, SEP3 27, INVREC 221/218-OA;
m = 3 rows by genre ROSTER 2 + B3A 17 + B3B 50 + B3D 22 + SEPB 54 = 145.

## §V7. FRESH ROUTE (differs from order-5, order-7, and the λ-census)

**F₂₇ territory, ord-13 invisible twist, first prime slot degree > 4** —
no battery and no prior pass used K₁ = F₂₇, a twist of order 13, or a
g₁ = 13 modulus (sealed = F₉/ord-4 and χ₂ = −1; PE1 fresh = F₁₆/ord-5;
PE2 fresh = F₈/ord-7). Chamber ℤ₃, ψ₀ = y³ − y + 1 (verified z₁ ord 26 —
primitive), reads (2,1,3)+(2,1,13), ψ₁ = y¹³ + z₁^k (k = 1,2,3; supp {0};
hand: A₁ = ℓ₀g₀γ₁ = 3, ξ₂ = z₁^{−6} of ORDER 13, machine-tied;
support-invisible since ξ₂¹³ = 1 ⟹ m = 1 junction byte-equal — (EC-2) at
a 13-order character); tops = 3 non-monomial deg-1 moduli over
K₂ = F₃^39 + ONE deg-2 modulus ψ₂ = y² + y + (1 − z₁) (irreducible by
disc = z₁ nonsquare: z₁^{(3³⁹−1)/2} = z₁¹³ = −1 — proved by hand,
exponent (3³⁹−1)/2 ≡ 13 mod 26). Because the committed `poly_irr` brute
force is infeasible at g = 13, tower validation used my own instrument
(deterministic Rabin test + the deg-2 disc criterion; disclosed;
unit-tested on known F₃ cases). Results (own Σ/u_j/δ code): **10 towers
built, 20 walked rows (10 at m = 2), 21 slot samples, 0 LAW VIOLATIONS
(ledger + δ-law + phir + c-tie); 9 separator slots (both bare-θ variants
fail, ξ-law holds); 9 non-involution δ; 7 gap slots; the deg-2 top's
j = 1 slot carries ALL THREE u_j factors nontrivially at ord-13
(hand-predicted: f1 = f2 = z₂^{−169} = −1 at k = 2, f3 = z₁^{−3});
(SC-2) wrap spot-tests 45/45 at E ∈ {1, 12, 13, 14, 26} on mixed
elements.** The ξ-law now has witnesses at twist orders 2, 4, 5, 7,
and 13.

## Remarks (non-findings)

1. **SL-C1 proof-body display artifact:** the sentence "δ_j =
   ρ_j·Σ_m(x/y) = ρ_j·Σ_m(ρ_j^{−1}·...)" (note §4) carries a dangling
   ellipsis and restarts mid-derivation; the complete chain that follows
   ((y/x)·Σ_m(x)/Σ_m(y) with Σ_m ∈ Aut) is correct and honest about its
   Aut consumption. Readability only; both prior passes read it without
   comment.
2. ξ₁ is still used implicitly as 1 (PE2's remark 1 stands; harmless,
   Σ₁ = id).
3. **Coverage fact (positive):** 22 sealed walked slots already carry all
   three u_j factors simultaneously nontrivially (B-genre interior
   slots) — the sealed battery was not blind to the triple composition,
   only the SEPA/SEPB separator genres were (g = 1 tops).
4. **Instrument note:** the F₂₇ genre required replacing `poly_irr`'s
   brute-force divisor scan (infeasible at g = 13) with a Rabin
   irreducibility test in MY OWN tower builder; the committed runner and
   artifacts are untouched. If a future unit wants deep prime-degree
   moduli in a sealed battery, the committed `poly_irr` will need the
   same upgrade.

## Disposition

Arc: seal 8064ae3 → verdict 59c1ff2 → PE1 0C+1G+2m (9b0117d) → r1
(6b24942) → PE2 CLEAN-on-note (6e57e03; counter 1/2 per a049d6c) →
**PE3 (this report): CLEAN — 0C + 0G + 0m — counter 2/2, SECOND
consecutive clean pass on the byte-frozen note text: THE Σ-LAW NOTE IS
ACCEPTED.** Owed to the orchestrator: the acceptance fold (grade box +
consumer notices — OPEN2ATTACK's pointer-annex and the GRTW2 tail annexes
already carry the corrected figures and the erratum; nothing further found
owing on those surfaces by this pass), and the standing Phase-2 items the
note itself lists as unchanged (the converse at every m, above-r₀ chain
claims, drainage/exhaustiveness). THEOREM SL-1 ((VD)+(EC)+(SC) ladder),
SL-C1 (δ = ρ^{1−Σ}), SL-C2/OPEN-2a-Σ's unconditional Σ-leg firing, and
the §5 separator corrections stand verified on every route three hostile
passes could construct.

— passPE3 verifier, 2026-08-08.
