# WFRAME passPE1 — hostile verification report (first pass, RCT round 1)
## Target: WFRAME_NOTE_2026-08-10.md @ 940ee7f3 (grade 0/2) — 2026-08-10

**VERDICT: NOT CLEAN — 1 GAP, 3 MINOR. Counter stays 0/2.**
The note's mathematical spine held everywhere I attacked it: the four
definitions are symbol-identical to their sources, the five laws are
faithful quote-with-recaps at their pinned ledger rows/spans, the level
ladder matches GENTOW5 S11.2/S11.3 exactly, the machine leg's seal and
run verify bit-identically, and a FRESH frame (new key GF29, an 8th
prime) confirmed four laws live including the verdict-level naive-twin
kill. The one GAP is a record-fidelity error: §4's tower data misstates
LP1's Φ′ (GB's polynomial copied onto LP1), in the section whose charge
is to be the measurement record's single home.

---

## F-1 (GAP) — §4 tower data: LP1's Φ′ misstated as x²−2

Quote (§4, "Towers:"): "LP1 (Φ′ = x²−2; e₁ = 2, f₁ = 2, z₁ live with
z₁²+z₁+1 = 0; e₂ = 2, f₂ = 1, z₂ = 1; u₂ = 9, V₂ = 4, e(µ₂) = 4)".

The committed sources fix Φ′_LP1 = x⁴ + 2x² + 4:
* GENTOW2_PROOF_2026-08-09.md @ 33f86204, L1140: "Φ′_LP1 = x⁴ + 2x² +
  4, Φ₂_LP1 = Φ′² − 8x³, (e, f) = (4, 2)";
* gentow2_pe4_fresh.py L18: "PHIP = x^4 + 2x^2 + 4";
* gentow2_pe6_fresh.py header: "LP1: PHIP = x^4+2x^2+4, PHI2 =
  PHIP^2-8x^3".

x²−2 is GB's Φ′ (both towers listed in one breath; the GB copy
leaked). The error is internally detectable — e₁f₁ = 4 forces
deg Φ′ = 4 ≠ 2 — but false as written, and §4 is chartered as "the
owed w ≠ 1 as-of note['s] ... single home" (§8: future measurements
append HERE). Failure scenario: a consumer reconstructing the LP1
frame from this note alone (as the "single home" invites) builds an
inconsistent or wrong tower for rows R-1/R-2/R-5; every committed
numeric fact about LD1/LD3/LD2 (ladders 4x·Φ′, 512x, digit strings,
avatar z₁/z₁²) is pinned to the TRUE Φ′ and fails to reproduce.
Classification: GAP (single false datum in the enumerative record;
the rows' measured VALUES themselves re-verified correct against
PE6 §E / PE3 LEG W / the honesty box — see the verification log
below). One-line repair when folded.

## F-2 (MINOR) — §7 "all three residues independently recomputed":
## inside THIS instrument the IDY row is linearly entailed

The instrument computes the three residues from the same monomial
vectors: r_u0 = n̂₂(2u₃) − 2u₃·π₃, r_θ = n̂₂(2u₃) − 2n̂₂(u₃), r_w =
n̂₂(u₃) − u₃·π₃, so r_u0 = r_θ + 2·r_w IDENTICALLY as vectors, and the
split/letter maps are linear — the {f}.IDY rows cannot fail once the
three splits exist, for any frame data. The discriminating content is
real but sits elsewhere: the U0/TH0/WAVA rows compare each recomputed
letter against the PE6-MEASURED pins (three per-prime residues measured
independently at actual primes — that independence lives in the SOURCE
record, gentow2_pe6_fresh.py, which itself disclosed "the IDY row is
multiplicative residue arithmetic — ... consistency closure, not
independent physics"). §7's sentence transfers the source's
independence claim onto this instrument's recompute without the
source's own caveat. No check is wrong; the prose overstates what the
3 IDY rows of the 47 test. (Fresh-leg note: my GF29 measurement below
measured the three residues at an actual prime — the closure is live
physics there.)

## F-3 (MINOR) — as-of dating: [GENTOW5-W(i)] is now PROVED at
## attempt grade; §3/§5 OPEN-1 read correctly but are hours-dated

Commit order verified: WFRAME verdict 940ee7f3 (12:55) precedes the
RCT-W(i) verdict ec30256c (13:56), so §3's "i ≥ 3 — OPEN BEHIND
[GENTOW5-W(i)] ... reproduced nowhere" and OPEN-1 were TRUE at
composition and remain true OF THE ACCEPTED CORPUS (GENTOW5_WI is
0/2, its own hostile arc owed — not accepted; the note's
accepted-texts-only rule keeps it out correctly). As-of reading for
consumers: OPEN-1's item now has an attempt-grade supplier
(GENTOW5_WI_2026-08-10.md @ ec30256c), and that arc's LW3 frame also
RECORDED the first measured avatar ≠ w geography (level 3, gap unit
2, filed to OPEN-3's row-23 gate) — which post-hoc vindicates this
note's §2 W-E asymmetry caution and makes OPEN-3's gate load-bearing,
not pedantic. Nothing to fix in the note (its fences point exactly at
both events); the FOLD after this arc should date §5. Cross-arc
declaration check: the note consumes neither T1/S-1 (declared NOT
consumed, verified — sole mention is the declaration) nor the W(i)
arc (composed before it); no undeclared mutual consumption found.

## F-4 (MINOR) — §4 consequence (i) says "w ≡ 1 is dead at each of
## the 7 measured primes" where the measured object is the avatar

§4's preamble states the discipline exactly (measured object = the
w-AVATAR; interpretation avatar = w rides row 23, DESCRIPTIVE, "not
upgraded here"), and the table column is honestly headed "w-avatar".
But the consequences block then writes "w ≡ 1 is dead at each of the
7 measured primes" and the F19 rule "the measured w ≠ 1 instances" —
w-language at the two places a consumer will actually cite, with the
avatar qualification 20+ lines above. Strictly: avatar ≠ 1 is
measured; w ≠ 1 rides the disclosed descriptive leg. This mattered
within the hour: the W(i) arc measured an avatar ≠ w geography at
level 3 (F-3). At i = 2 no measured gap exists and the leg is
disclosed in-section, so MINOR — but the fold should re-key
consequence (i) and the F19 rule's subject to "avatar" or add the
leg's rider inline.

---

## VERIFICATION LOG (what was checked and held)

**Definitions (surface 1).** DEF W-1 display w_i = R_{i+1,κ̄_i}(n̂_i
(u_{i+1})), κ̄_i = u_{i+1}/e(µ_i): symbol-identical to LEMMA GENTOW2-B″
L729–730 ("w := u(κ̄) = R_{3,κ̄}(n̂₂(u₃))"), to ledger row #2's κ̄
parenthesis, and to GENTOW5_PROOF L788–790 at level i. DEF W-2 =
GENTOW5 L784–785 display verbatim; coefficientwise form is correct
one-line algebra (re-derived). DEF W-3 = GENTOW2-B row #2's ϑ(t)
display, index-generalized as declared. DEF W-4 is convention-only as
audited in §6(c). Nothing built in (w = 1 possible; letter-valuedness
kept out — checked against OPEN-3).

**Laws (surface 2).** W-A: the quoted parenthetical is verbatim in
ledger row #2 (md5-8 8a00bf44 verified against the baseline JSON);
factor-pattern generality is B″'s own consequence sentence ("with P's
irreducible-factor pattern for every value of w", row #4). W-B: (6)
verbatim at L732 with the stated κ̄. W-C: recap algebra re-derived
exactly (u(β_t)c_t = a_t w^{f₃−t}); iff clause matches row #2's final
sentence. W-D: quoted sentences located at row #1, row #4, GENTOW5
L816–819. W-E: matches the S5.2 γ-calculus paragraph L715–727
content-exactly; the ϑ-only scope + asymmetry caution present. All
four ledger md5-8s (5d1ae5f0/8a00bf44/bae471b0/d4c8b885) recomputed
from statement_ledger_baseline.json and matched; statement_ledger.py
--check GREEN at HEAD (166 baseline, 0 changed/deleted).

**Ladder (surface 3).** §3 i=2/i=1/i≥3 entries match GENTOW5 S11.2
(L1888–1933; [GENTOW5-W(i)] display byte-matched) and S11.3
(L1933–1964; ψ₂^{(u1)} display byte-matched, species sentence
faithful). OPEN-1's conditional/unconditional clause split matches
S11.2's fence-scope paragraph item-for-item. As-of status: F-3.

**Record (surface 4).** R-1..R-4 vs PE6 §E L245–295: avatars
z₁/z₁²/z₂²/z₂, 6 primes, both u₃-discrimination pairs, B″(6) closed at
3 slots, ϑ(0) decode/PE5 pins — all match. R-6 vs PE3 LEG W L270–292:
7th prime, first (8,4), w = z₂ ≠ 1, PSIW on the nose, NOSE tooth,
naive twin [16,16] — all match. R-5 vs the honesty box L384–396: LD2
digits (z₁,z₁²), split target, single (4,4) prime, realized y²+z₁y+1,
RED 62/9 seal 23def87, decode 14/0 — all match. Instrument seals as
cited (ade1727, 68/1→68/0; 48/2→48/0). Except: the LP1 Φ′ datum (F-1).

**Machine leg.** Seal verified: runner md5 at seal commit 2840d78c =
e9495dfcbf866baef09bea60f70d0dbc = working tree; output md5
470d157b1cff29f31e06cb27e22fe715; seal commit strictly precedes the
verdict commit and contains runner + §7 prose only. Isolated re-run
from /tmp: BIT-IDENTICAL output, exit 0 (47/0, teeth 4/4). Check count
47 re-derived from source (16 avatar + 10 ϑ + 9 IDY + 12 subst).
Hand re-verification of the arithmetic on my own route: lattice splits
at all 4 frames (e.g. GA3 u(β₀): (165,20,−82) → (−20,−41) → z₂), all
four F₄ twist pins, all four teeth re-derived as genuinely biting
(T-GAMMA: 86 ≠ 77 consistency break confirmed). Tautology audit:
SUBST/WAVA/TH0/U0 rows carry real content against committed pins;
IDY rows are entailed (F-2); LD3.THTRIV re-reads its own frame table
(1 of 47, no discriminating power — folded into F-2's audit, not
separately filed); no law could be false with the run green EXCEPT
W-D, which the instrument does not claim to test (checked: no tooth
or check touches consumer w-blindness; its verification is textual,
LAW W-D's quotes, verified above).

**Fresh route (machine, new geography).** Frame GF29 — NOT in any
committed record: the GB tower (Φ′ = x²−2, Φ₂ = Φ′⁴−4xΦ′²−32, u₂ = 5,
π₃ = Φ′/x²) with a NEW stage-3 key at u₃ = 29 (e₃ = 1, f₃ = 2;
κ₃ = 29 > e₂f₂u₂ = 20; no committed key uses u₃ = 29), target
ψ₃ = y²+y+z₂. Hand γ-calculus predictions derived fresh: n̂₂(29) =
64Φ′, n̂₂(58) = 2¹⁴x; w-avatar split (58,6,−28) → z₂ ≠ 1; ϑ(0) =
z₂²; u(β₀) split (117,14,−58) → z₂. Multiplicative key Φ₃ = Φ₂² −
64Φ′Φ₂ − (2¹⁴x + 2¹²Φ′²) [c₀ = ϑ(0)⁻¹a₀ = z₂², lift 1+z₂]; LAW
W-C/W-A predict realized residual ψ₃^{(z₂)} = y²+z₂y+1 (irreducible
/F₄) → ONE prime (4,4). Naive twin Φ₃ⁿ = Φ₂² − 64Φ′Φ₂ − 2¹²Φ′²
predicts y²+z₂y+z₂² = (y+1)(y+z₂²) → TWO primes (4,2): a
verdict-level discrimination. PARI leg (gp, dual routes factorpadic +
idealprimedec/nfmodpr): see wframe_pe1_fresh_output.txt — results
recorded in the addendum below after the run.

## GRADE LINE

Attempt grade for the arc: **0/2 stands; pass NOT CLEAN (1 GAP: F-1;
3 MINOR: F-2/F-3/F-4).** The GAP is a one-line data repair in §4, not
a law or ladder defect; no CRITICAL anywhere; the machine leg and the
fresh frame both GREEN on the note's laws.
