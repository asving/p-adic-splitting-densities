# GENTOW4 passPE1 — HOSTILE VERIFIER REPORT (first pass; fresh context, no prior stake), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` at HEAD
(651b9e5; note last touched c43505d 2026-08-09 16:06, a disclosed
hash-display typo fix — diff verified display-only). Attempt grade
0/2, arc opens here. Protocol: quote-and-classify, fix nothing.

## VERDICT: **NOT CLEAN — 1 GAP (the gauge seam, four sites; refuted
## by this pass's fresh machine leg at an η ≠ 1, f₂ = 2 partial-side
## frame) + 2 MINOR. The core mechanism SURVIVES at the corrected
## key: bouquet + projection independently re-derived; sealed leg
## bit-identical isolated re-run 1,740/0; fresh route GREEN 93/0 at
## two out-of-battery frames (first gauge-live partial side; first
## TWO-BLOCK member anywhere in the tower batteries). Counter stays
## 0/2.**

Timeline fact driving F-1 (checked in git): the note was composed,
sealed and verdicted 2026-08-09 15:39–16:06 (c8da214 → 2aa5b16 →
c21b59e/c43505d). The GENHN gauge erratum 59c1966 landed 20:13, the
HETOW [r1] wrap-correction 5335ae3 at 20:12, GENTOW1's gauge annex
477b1b1 at 23:26 — all AFTER. GENTOW4 has received NO dated append
since: it is (with GENTOW6) the last sibling carrying the
gauge-naive displays uncorrected. 7 of 7 sibling first-passes have
now hit this seam.

---

## FINDINGS

### F-1 (GAP, CONFIRMED — the gauge seam: the note predates erratum 59c1966; four sites; machine-refuted at an η ≠ 1, f₂ = 2 partial side; battery structurally blind)

**Site (a) — S0 key display.** Quote (S0): "Composed key (same
formula as T(b)'): Phi2 := Phi'^{e2f2} − Sum_{t<f2}
chat_t·nhat(u2(f2−t))·Phi'^{e2t}". This is LEMMA GENHN-T(b)′'s
GAUGE-NAIVE display (plain lifts ĉ_t), corrected at source by
erratum 59c1966 to ĉ_t := lift(c_t·η^{W(t)}),
W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋. The naive and corrected keys coincide iff
every c_t·(η^{W(t)}−1) = 0 — in particular at η = 1, and
automatically at f₂ = 1 (W(0) = ⌊i(u₂)/e₁⌋ = 0 since i < e₁). They
DIFFER at η ≠ 1 frames with f₂ ≥ 2 — inside the note's stated scope
(S3(iii) "stated at any mu2*"; BOX-3 claims the S2–S4 proofs
"uniform" over f₂ per the S6 table's f₂ ∈ {1,2} with q ∈ {2,3};
f₁ = 1 does NOT force η = 1 — the erratum's own frame X is f₁ = 1,
η = 2).

**Site (b) — LEMMA GENTOW-4.1(c).** Quote: "HETOW-2 holds verbatim:
Phi2 = Psi_{kappa2,rtilde} − w with w = 0 or dv2(w) > T2". The
HETOW-2 the note audited at composition was the pre-[r1] gauge-naive
form, REFUTED at η ≠ 1, f₂ = 2 by HETOW passPE1 F-1 (frame X: naive
key σ {(4,1)} ≠ carrier {(2,2)}) and restated at 5335ae3 at the
wrap-corrected key. At the naive Φ₂ of site (a), clause (c) is FALSE
at such frames (the naive key is not a Ψ-family member up to a
> T₂ perturbation: this pass measured the discrepancy AT dv₂ = T₂
exactly — see the fresh leg). Everything (c) transports — HE6R1-2 +
RIDER, HE6R1-3, HE7.A/C/D, HE7-13′ "all hold with key Phi2" — and
therefore THEOREM GENTOW-4.A(ii)/(iii)/(v) and COR GENTOW-4.C, reads
onto the wrong polynomial there. Same for S3's label vocabulary
"rtilde_r = the pi-bar-normalized twist of r" (HETOW-1's [r1]
restatement re-scoped r̃ to minpoly(β) with the slot-residue clause
proved only at the corrected key).

**Site (c) — GENTOW4-BOX-3.** Quote: "The S2–S4 proofs are uniform
in all of these (S3(iii) is stated at any mu2*); the gap is
machine-side, named." The same uniformity sentence was withdrawn at
HETOW [r1] F-3 ("BOX-3 gains the eta-gauge axis; 'uniform in all of
these' withdrawn"). BOX-3 names q, e₂, f₁, depth, μ₂ axes but NOT
the η-gauge axis; the battery cannot see it (audited the sealed
runner: the only f₂ = 2 family is P2 at q = 2 where η = 1 forcibly;
the q = 3 families P3/P5 use Φ′ = x²−3, η = res(x²/3) = 1, and are
f₂ = 1 anyway).

**Site (d) — the S4 REMARK's scope sentence.** Quote: "(Δb is
forced even; the x- and pi-relations have residue 1 at f1 = 1)".
False as stated: the x-relation x^{e₁} = η·π^h·(1+small) has residue
η, and f₁ = 1 does not force η = 1 (frame X and this pass's FR-G
are f₁ = 1, η = 2). The coherent-digit formula
delta_j = r_j·eta2^{(b_j−B_j)/2} is derived, and correct, at η = 1
only: at η ≠ 1 the b-wrap Φ′^{e₂} → η₂·n̂(u₂) introduces x-exponents
i(u₂) whose own e₁-wraps contribute η-powers the display omits. The
honest scope of the S4 remark (and of the sealed coh()) is η = 1 —
which covers the entire battery but not the note's claim scope.

**Failure scenario (constructed and machine-executed this pass —
`gentow4_pe1_fresh.py`, frame FR-G):** p = 3, Φ′ = x²−6 (legal outer
genre (2,1,5), h = 1, η = 2), inner (e₂,f₂) = (1,2), u₂ = 3,
ψ₂ = Z²+Z+2, μ₂ = 2 on side [1,5] of slope 3 — PARTIAL (4 < μ₁ = 5),
sibling slope 4 length 1; members f = f_S·g with deg-8 blocks at the
corrected key and g = x²−15. Measured, PARI dual-route adjudicated:
* the note's displayed (naive) key Φ′²−6xΦ′−27 has σ = {(4,1)} ≠
  {(2,2)} = f₁f₂-carrier; the corrected key Φ′²−6xΦ′−54 has
  σ = {(2,2)} (site (b) refuted at a partial-side frame);
* the Φ₂^naive-development of BOTH members has an EMPTY >T₂ initial
  segment (naive pins hull (0,15)–(2,3), slopes = T₂ = 6 exactly):
  GENTOW-4.A(ii)'s display "the slope->T2 part of P2(f) ... spans
  [0, mu2*]" computes mu2* = 0 while deg f_S = 8 = D₂·2 — the
  displayed equation deg f_S = D₂·mu2* is FALSE at the naive key,
  and the tower class is INVISIBLE (a reader on the note's display
  refuses/undecides every member);
* GENTOW-1(d)'s field floor through the projection collapses at the
  naive key: nfeltval gives dv₂(Φ₂^naive) = E₂ EXACTLY on every
  class factor (2·6 = 6·2; 4·... row (4,2): 2·12 = 6·4), vs
  STRICTLY > E₂ at the corrected key (16, 14 > 12; 26 > 24);
* at the CORRECTED key both members read exactly per THEOREM
  GENTOW-4.A: μ₂* = 2, c_g = 3, floors cleared, trichotomy 2SIDED /
  RAM, σ = PARI {(2,1),(2,2),(2,2)} / {(2,1),(4,2)} both routes.

**Classification: GAP, not CRITICAL** — per the erratum's own scope
finding and the sibling precedent (GENTOW1 r1, GENTOW3 r1): the
proof MECHANISM (bouquet, projection, per-block decision) holds at
the corrected key — my fresh leg confirms it does at this very
frame — and the sealed battery + verdict are sound on their all-η=1
geography. What is owed is GENTOW4's dated gauge annex in the
sibling pattern: pin ĉ_t := lift(c_t·η^{W(t)}) at S0/4.1(c), re-read
r̃ per HETOW [r1], add the η-gauge axis to BOX-3, and re-scope the
S4 remark's "at f1 = 1" to "at η = 1". REPAIR RULE reminder: re-derive
from 59c1966 + HETOW_RECON [r1] §S2, not from this report's text.

### m-1 (MINOR — S2 "exactly THREE places" enumerates two)

Quote (S2): "consumes fullness in exactly THREE places: HETOW-1(a)'s
psi2(0) != 0 (...), HETOW-3 wholesale (f_S = f), and nothing else".
Two places are listed. The repairs (a)–(d) and THEOREM (ii) cover
both listed sites (plus the datum floor), so no content hinges on
the count; the sentence should read TWO (or name the third).

### m-2 (MINOR — T-2 NOCG's even-p₀ branch kills a representative, not a mutant run)

Sealed runner L871–878: when p₀ is even and (p₀−c_g) odd (true read
RAM), the "mutant sigma" is hand-assembled as INERT ("emit INERT as
the representative wrong sigma") rather than produced by running the
parity-mutant reader through the trichotomy. The kill (mut ≠ PARI)
is real and the odd-p₀ direction is a genuine mutant, so the tooth
stands; but the verdict sentence "49 parity flips, every one
PARI-killed" silently includes representative-assembled flips. Worth
one clause of disclosure at the next append.

---

## CLEAN CHARGES (verified, nothing at GAP-or-worse found)

* **Surface (1), the bouquet (GENTOW-4.A(i)) — independently
  re-derived.** Partition: each root has one label (letter's minimal
  polynomial; HE6-2″/HE6-4 realized-and-partition checked at
  source). Galois stability: v is Galois-invariant, Φ′ and the n₂
  monomials have g-fixed coefficients, so β₂,gρ = ḡ(β₂,ρ) and the
  minimal polynomial over F_Q is preserved — LEMMA HE7-11's
  computation verified to read only Φ′/normalizers/ι (its proof
  quoted at HE7_PROOF L776–785), correctly instantiable at every
  datum of GENTOW-4.1(b). Integrality + division: v(ρ) = h/e₁ > 0,
  Gauss + disc f ≠ 0 (LEMMA HE7-6's argument, quoted L688–699).
  Degree forcing D′ℓd_r | deg f_{κ,r}: LEMMA HE7-5 (L552–554) gives
  e₁ℓℓ₂ | e and f₁d_rd_{r₂} | f per root — covers the claim.
* **Surface (2), the block projection — statement-vs-use audit.**
  LEMMA HE6R1-2 (HE6R1_RECON §S3.4) verified to be stated at
  EXACTLY the proper-block configuration with the [r1′] Ψ ∤ f_S
  hypothesis and the [r1′] γ_g ∈ K₂^× scalar; GENTOW-4.A(ii)
  carries both (S2 peels; "up to the K2^x scalar gamma_g" +
  scale-invariant consumption per HE7 §S1). RIDER HE6R1-2R's
  evaluand-wider HE7-7′(b) consumed as displayed. The initial-
  segment/right-endpoint addition ((ii)'s proof) re-derived: hull
  drops strictly decrease left→right, P₂(f_S) spans [0, μ₂*] all
  sides > T₂ (HE7-9(a) + HE7.A(1)) with monic right endpoint
  (μ₂*, 0); support-function equality on (T₂,∞) forces the
  translate's breakpoints — sound. GENHN-2′ (T(b)′(ii), L1156–1167)
  verified side-blind in the evaluand (any A of deg < D₂ at
  tower-node points; the partial side's non-monic length-M
  development has all coefficient degrees < D₂ including the top).
  GENTOW-4.1(b)'s vertex-attainment argument re-derived (a lower-
  hull vertex of a finite integer point set is a point of the set;
  left endpoint of every side is a vertex; attained pin has unit
  quotient, nonzero digit) — genuinely side-blind and correctly
  fences what it does NOT claim (interior pins). GENTOW-4.2's
  pure-power tie re-derived from HE6-3(b) (n_λ = D′L_λ, quoted
  (SEP)-FREE at HE6_PROOF L271–278) + HE6-2′ excess ⟺ residual root
  + |S| = deg f_S; the mixed-side refusal (BOX-1) is honest and
  matches HE7-BOX-4's decline. COR GENTOW-4.C's floor transport
  checked against GENTOW-1's 𝒯 definition (GENTOW1_PROOF L142–148):
  f_S monic, deg D₂μ₂*, one side, monic pure-power residual — 𝒯
  member at (Q; e1,f1, e2f2·mu2*; h); floors apply. (At η ≠ 1 the
  coherent-residual normalization folds into F-1's annex.)
* **Surface (3), machine instruments.** Seal chain verified:
  runner md5 98cdd4a4e5a47f1434bdf8ca5a1c4b4c = HEAD = commit
  2aa5b16 (16:04:01) = artifact line 2; verdict commit c21b59e
  (16:05:54) artifact-only; c43505d display-only. **Isolated
  re-run** (/tmp copy, fresh env): output IDENTICAL to the committed
  artifact from line 2 onward (same 1,740/0, 71 c_g-odd, 49 NOCG,
  8 NOTWIST, GREEN; only the line-1 timestamp differs). Member
  census re-derived from the code: 25/24/22/22/24 = 117 ✓.
  **Tautology audit NEGATIVE:** read_member/composed_read compute σ
  from f alone (level-1 digits → classes → per-class keys →
  pins/trichotomy); family constants are used as parse GATES and as
  the ψ₂-derived keys (P2's F.PHI2 checked = the display's key for
  ψ₂ = Z²+Z+1; P3/P5 keys digit-derived at read time, equal to the
  family constants); PARI enters only at the comparison loop. Teeth
  semantics verified at source (T-1 dev-quotient ≠ [1]; T-4 status
  leak check; T-5 cross-key incl. PEEL corner; T-6 = coh() vs
  eta2=1 re-read, kills adjudicated by PARI). P-5's nodev6 keyed to
  the key ACTUALLY read (rd['tower'][0]['key']).
* **Sibling lesson (2) — ψ vs ψ^{(w)}:** GENTOW4 does not consume
  GENTOW2's twisted-residual displays; the f₂ = 2 refine lift in
  the runner is the per-flavor base re-solve consistent with
  GENTOW1's [r2] corrected lift display (4e81a57); η₂ ≠ 1 DBL rows
  machine-covered (P5, PARI-exact).
* **Sibling lesson (3) — attainment sentences:** P-4's parity-flip
  liveness is measured (71/46 split); PE2-P's "j = 1 EXACTLY at the
  node floor" carries its witness (re-verified by hand AND by the
  fresh leg: pins (28,16,5), c_g = 5, 11 = 11). No certificate-free
  attainment sentence found.
* **Sibling lesson (5) — stage-index conflation:** none found; all
  S3/S4 displays pair same-stage objects (checked (ii)'s pins/hull,
  (v)'s trichotomy, 4.C's floors, S4's N_j heights).
* **Sibling lesson (6) — supplier census vs ledger:** BOX-4's stack
  was accurate as-of-composition (HETOW 0/2, GENTOW-1 0/2, HE6R1
  post-r2 annex stack, HE7 2/2 + post-acceptance annex F-1
  disclosed, HE6 accepted, GENHN 2/2). Since then HETOW → 2/2 and
  GENTOW1 → 2/2 (in GENTOW4's favor), BOTH via gauge-corrected
  restatements — the stack line's next refresh belongs inside F-1's
  annex. ANNEX-LEMMA HE7-13′ existence + post-acceptance honesty
  label verified at HE7_PROOF L1603.
* S1/S5 hand tables INDEPENDENTLY recomputed (slot heights of
  C₀/C₁/C₂ by hand: 28/16/5; hull slopes 12/11; block pins 23/11/0;
  and by the fresh instrument's FR-W leg): exact, σ witness
  reproduced {(2,1),(4,1),(4,1)}.

## FRESH LEG (out-of-battery; `gentow4_pe1_fresh.py`, md5 5dc455dd…, output dac5110c…, committed): **GREEN 93 checks / 0 violations, dual PARI routes**

* **FR-G — the first gauge-live partial side anywhere** (η = 2,
  f₂ = 2, q = 3; no battery family has η ≠ 1): corrected-key reads
  PARI-exact on 2SIDED + RAM members; the three F-1 teeth above
  fired exactly as hand-derived (naive key σ {(4,1)}; naive μ₂* = 0
  class-invisible; naive field floor = E₂ collapse).
* **FR-M — the first TWO-BLOCK partial member in any tower battery**
  (q = 2, all gauges trivial — pure geometry stress): μ₁ = 9,
  n = 18, hull (0,28)–(1,24)–(5,10)–(9,0), TWO repeated classes
  (T+1)² on TWO sides (u₂ = 7 side [1,5]; u₂ = 5 side [5,9]) plus a
  slope-4 sibling; maximal partiality (event length 4 vs μ₁ = 9;
  battery max μ₁ = 7). All 3 label combos: both classes read
  through their own keys with μ₂* = 2 (GENTOW-4.2's tie at two
  pure-power sides SIMULTANEOUSLY — first exercise), c_g^A = 27 and
  c_g^B = 25 exactly as hand-derived (each class's c_g correctly
  absorbs the OTHER block's mass: 20 + 7, 20 + 5), floors cleared,
  per-class trichotomy = design, σ = PARI both routes
  (σ_A ∪ σ_B ∪ {(2,1)}), per-key nfeltval separator exact (class
  rows > E₂ strict, degree sums 8 = D₂μ₂* at BOTH keys per member).
  GENTOW-4.A(iv)'s "a repeated co-class is ITSELF a tower class,
  read by this same theorem" holds at first machine contact.

## GRADE LINE

**NOT CLEAN at passPE1: 1 GAP (F-1, CONFIRMED by construction +
fresh machine refutation) + 2 MINOR. Counter stays 0/2.** The owed
repair is the sibling-pattern dated gauge annex (sites a–d), after
which the theorem chain—whose mechanism this pass confirmed at the
corrected key on both fresh frames—can re-enter the arc. Sealed leg,
tautology audit, bouquet re-derivation, projection statement-vs-use
audit, and all six sibling lessons otherwise CLEAN.
