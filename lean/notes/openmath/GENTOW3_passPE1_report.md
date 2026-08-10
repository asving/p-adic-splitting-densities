# GENTOW3 passPE1 — FIRST HOSTILE PASS (2026-08-10)

**Target:** `lean/notes/openmath/GENTOW3_PROOF_2026-08-09.md` at HEAD
(verdict commit d90db6d, 2026-08-09 15:53; body md5 8664269e, byte-
untouched since). Subject: THEOREM GENTOW-3 (the faithfulness
threshold Θ_j = (μ₂−j)E₂ + δ), COR GENTOW-3.C (T(a)-as-theorem), the
S4 leaf-failure quantification, and the S5 machine leg.
**Protocol:** quote-and-classify, fix nothing. Fresh context, zero
prior stake.

## VERDICT: NOT CLEAN — 1 GAP + 3 MINOR. Counter stays 0/2.

The mathematical core SURVIVES this pass: the threshold derivation
re-derived independently and confirmed exact at three frames outside
the battery (μ₂ = 3; δ = 5; gauge-live η ≠ 1 — fresh route GREEN
485/0, dual-oracle); the sealed machine leg is bit-identical on
isolated re-run with a negative tautology audit. The GAP is the
gauge seam at the note's one value-live ĉ_t site (the x-free genre
definition), whose "equivalently" clause is false at f₁ ≥ 2 inside
the note's claimed uniformity scope; the note predates the GENHN
gauge erratum and carries no gauge annex.

---

## FINDINGS

### F-1 (GAP — the gauge seam at the x-free definition; the
### "equivalently" clause false at f₁ ≥ 2)

QUOTE (S2, X-FREE GENRES, L108–111): "call the genre x-free iff
every lift coefficient ĉ_t·n̂(u2(f2−t)) of Phi2 (t < f2, ĉ_t ≠ 0)
is an x-free monomial π^a — equivalently i(u2(f2−t)) = 0, i.e.
e1 | u2(f2−t)·h⁻¹-class"; and (GENTOW3-BOX-2): "The S2 proof is
uniform in (e1, f1, e2, f2, mu2, q, h)".

CLASSIFICATION: GAP. Two entangled defects, one cure (a dated gauge
annex, the GT1-r1 shape):

(a) The note's verdict commit (d90db6d, 08-09 15:53) PREDATES the
GENHN dated gauge erratum (59c1966, 08-09 20:13, ĉ_t :=
lift(c_t·η^{W(t)}), W(t) = ⌊(f2−t)·i(u2)/e1⌋) and the note carries
NO gauge pin anywhere (no η mention in the body). Its one
value-live ĉ_t site is exactly this definition: x-freeness of the
lift coefficient depends on the ĉ_t READING at f₁ ≥ 2, where
lift(c_t·η^{W(t)}) and lift(c_t) differ in x-content.

(b) Independently of gauge, the displayed "equivalently
i(u2(f2−t)) = 0" is FALSE at f₁ ≥ 2: ĉ_t is then a polynomial of
degree < D′ = e1f1 that is itself x-ful whenever c_t·η^{W(t)} ∉ F_Q
(lifts of K-elements outside F_Q carry x-exponents e1·r, r ≥ 1), so
i(m) = 0 does not make ĉ_t·n̂(m) an x-free monomial. The
equivalence holds at f₁ = 1 (ĉ_t constant) — every battery family
and every fresh frame of this pass sits at f₁ = 1.

FAILURE SCENARIO (concrete): genre with f₁ = 2, K = F₄, some
c_t·η^{W(t)} a generator of F₄, and all i(u2(f2−t)) = 0. The
"equivalent" test declares the genre x-free; a consumer then reads
clause (iii) (ShC_j = C_j identically, "the shadow IS the composed
read") and prices σ-strata through stage pins — while the actual
key has x-ful lift coefficients, the (iv) self-overflow machinery
is live, and the shadow can carry a fake digit at Θ_j: exactly the
PE1-shape mislabeling the theorem exists to prevent.

SCOPE OF DAMAGE (verified): clauses (i)/(ii) are weight-level and
wrap-immune (heights only — my independent re-derivation below
never touches ĉ_t values); clause (iii)'s PROOF is correct under
the PRIMARY definition ("every lift coefficient an x-free
monomial", any f₁); COR GENTOW-3.C is untouched (A_J degree < D′ +
band heights, value-blind). Only the "equivalently" reduction and
the f₁-uniformity claim for the GENRE CLASSIFICATION are wrong.
Also folded here: GENTOW3-BOX-2 cites "GENTOW-BOX-2's geography
verbatim" without the η = 1 battery-blindness reading that
GENTOW-BOX-2 gained at GT1-r1 — GENTOW3's battery is equally
η = 1-blind and says so nowhere. The fresh route below supplies
this note's first η ≠ 1 machine contact (frame FR-GL at the
corrected key: floor + attainment at BOTH coordinates, GREEN).

### m-1 (MINOR — "machine-checked" digit-value attribution)

QUOTE (S2 (iv)): "the per-genre CERTIFICATE, decided by one finite
computation (machine-checked: A5/A7/C touch j = 0 with digits
16Phi'/64Phi'/64Phi' at 21/31/43; B touches BOTH: ShC_1 = 4Phi' +
8x at 7, ShC_0 = 64Phi' + 64x at 13)."

The sealed instrument checks self-shadow PINS only (`want` lists
[21,None]/[31,None]/[13,7]/[43,None]); the digit VALUES appear
nowhere in the machine output. The values are all CORRECT — I
verified each by hand (independent division walks) and the fresh
instrument replicates them exactly (SELF rows: 16Φ′, 64Φ′, 64Φ′,
B-pair 64Φ′+64x / 4Φ′+8x, D drain) — so this is attribution-only:
pin-nonzeroness (which IS the certificate) was machine-checked;
the displayed digit values were hand-derived. MINOR.

### m-2 (MINOR — P-1 member-count sentence)

QUOTE (S5): "P-1 (FLOOR, 274): every discrepancy height on 110
members (nec + real + anchors, five families) clears Θ_j."

The FLOOR tally 274 = 2 coordinates × 137 member_check calls =
5 × (14 nec [10 bases + 4 deep-perturbation variants at i ≡ 0
mod 3] + 12 real + 1 anchor) + 2 A7-band rows. "110" counts only
nec-bases + real (50 + 60) and omits the 20 perturbation variants,
5 anchors, 2 band rows despite naming anchors. Conservative
direction (more was checked than claimed), but the record sentence
miscounts. MINOR.

### m-3 (MINOR — T-SHADOW-REG's σ-leg is dead code)

QUOTE (S5): "T-SHADOW-REG x1 (the shadow reproduces the refuted
stage pins and its priced σ differs from PARI on rows 1–2)."

In the instrument the σ-comparison branch is a literal `pass`
(gentow3_checks.py L398–399: `if i > 0 and rs[3] is not None and
rs[3] != [(8, 1)]: pass`); the tooth fires on pins+labels matching
wants alone. The σ-difference IS entailed by machine-checked facts
(shadow labels tINERT/t2SIDED force priced σ {(4,2)}/{(4,1)²} via
the accepted (iii) dictionary, against PARI-checked truth {(8,1)}
on the same rows), so nothing false is claimed about the world —
but the tooth's description overstates what the code compares.
MINOR. (Related observation, no finding: the ENTRY tally 274 is
logically entailed by FLOOR 274 given δ ≥ 1 — honest as COR 3.C's
"machine face", but it is not independent evidence.)

---

## CLEAN CHARGES (verified, nothing at GAP-or-worse found)

1. **Θ_j re-derived independently.** With wt(π^v x^{a′} Y^{b′}) =
   e1e2·v + a′e2h + b′u2: x-carry Phi′-branch costs exactly
   +δ = u2 − e2D′h per retained Φ′-factor; Φ′-carry and K2-division
   moves are weight-conserving; membership floors put F at
   wt ≥ μ₂E₂; any shadow/honest discrepancy carries ≥ 1
   Φ′-extraction, so total wt ≥ μ₂E₂ + δ, and slot height at
   coordinate j = wt − jE₂ ≥ Θ_j. Table values re-computed for all
   five families (E₂, δ, Θ₀, Θ₁, entry top — all match). The Step-2
   recarry arithmetic ((μ₂−j′)E₂ + kδ − (j−j′)E₂ ≥ Θ_j) checks out;
   the j-boundary is correctly scoped (j < μ₂ throughout; j = μ₂ is
   the monic top). I stress-tested the ledger's tightness on
   g = x·Φ₂ at FR-M3: the bare-monomial discrepancy lands at
   wt(g) + δ − jE₂ = 2 < Θ₁ — and confirmed this is NOT a
   counterexample because membership forces wt(g) ≥ μ₂E₂ + 1,
   pushing every member's discrepancy to ≥ Θ_j + 1 from g-content
   and = Θ_j only from the key power's own shadow. The floor is
   exactly attained where the theorem says and nowhere below (0
   violations across 210 fresh FLOOR checks + 274 sealed).
2. **T(b)′(iv) consumption faithful.** The annex's functoriality
   identification, the Φ₂-recarry remark, the discrepancy display
   Φ′(x₀)H_j at dv₂ ≥ u₂ + dv₂(H_j-class), the PE1 table (honest
   RAM(25)/RAM(21)/RAM(21) vs stage RAM(21)/INERT(28,14)/
   2SIDED(30,14), PARI {(8,1)}×3) and the u₂ = 7 supp row
   (stage-INERT(36) vs true RAM(31)) all read verbatim from
   GENHN_PROOF S8 [r2]; GENTOW3's S1/S4 anchors match. COR 3.C
   upgrades exactly the sentence (iv) leaves machine-verified, and
   its proof is sound: A_J deg < D′ (projection = identity) +
   event band ≤ (μ₂−j)E₂ = Θ_j − δ < Θ_j + theorem (ii).
3. **Supplier arc census.** GENHN ACCEPTED 2/2 at PE4 (adjudications
   L14350–52) including the S8 [r2] annex; GENTOW1 (LEMMA GENTOW-1
   + GENTOW-5 + Step 0) ACCEPTED 2/2 on 08-10 — the note's "at
   GENTOW-1's 0/2 grade" was accurate at composition and the stack
   has only improved; [r1] node floor inside accepted GENHN text.
   Import base gentow1_checks.py md5 6df4b213 = GENTOW1's sealed
   runner, byte-identical today. Nothing is consumed at theorem
   strength that is attempt-grade beyond the disclosed stack.
   ψ vs ψ^{(w)}: GENTOW3 is depth-2 (ψ₂ only, no ψ₃ consumption)
   — w-free per the accepted GENTOW2/GENTOW6 reading; no cross-note
   quantifier mismatch found. GENTOW-2 (the μ₂ ≥ 3-conditional
   lemma) is NOT consumed.
4. **S4 regimes.** δ = 1: Θ = node floor, no faithful leaf band
   (PE1 geography sharp); δ ≥ 2: band [(μ₂−j)E₂+1, Θ_j−1] of width
   δ−1 (A7: 29–30 faithful, 31 first violation — machine rows
   agree); x-free: no violation (FAM-D 12-member sweep). All
   re-checked; the δ = 5 fresh frame extends the band pattern to
   width 4 (four faithful heights 37–40, PARI-confirmed decided
   reads at 37/39/40).
5. **Honesty boxes accurate.** GENTOW3-BOX-1 correctly downgrades
   (iv)'s sharpness to a per-genre certificate (my FR-M3 frame
   shows the certificate genuinely CAN have slack — j = 0 shadow
   pin 12 > Θ₀ = 10 — so the box is load-bearing, not decorative);
   the entry-digit-driven overflow genre named as unwitnessed;
   scope honestly FULL-side; consumption path correctly deferred.

## MACHINE LEG (sealed battery, verified)

Seal chain: runner-only seal 5ac0d80 (docstring P-1..P-7 + 3 teeth
+ smoke disclosure BEFORE first run) → verdict 2b970ae (two-commit
discipline ✓). Runner md5 7cf3a7b8 and output md5 926cd05f match
the note; single-commit history = no post-seal edit. ISOLATED
RE-RUN (fresh scratch dir, runner + import base only): exit 0,
output BIT-IDENTICAL (md5 926cd05f), PARI leg live (6 jobs).
TAUTOLOGY AUDIT: NEGATIVE — shadow and honest reads are computed by
structurally different routes (two-variable K2-division with
mod-Φ′ reduction at every step vs direct Φ₂-division); Θ enters
only as preregistered constants; an accidentally-identity `xred`
would flip SHARP/PE1 rows RED (they demand divergence at exact
pins), so the instrument cannot pass with the theorem false in
either direction. Tally recomputed from code paths: 274+274+11+6+
3+2+3+6+3 = 582 ✓.

## FRESH ROUTE (gentow3_pe1_fresh.py — own primitives, frames
## outside the battery)

Three frames chosen to stress the threshold where the battery is
blind: **FR-M3** (μ₂ = 3 — battery is μ₂ = 2 only — with e2f2 = 1,
the instant-recarry corner never exercised anywhere), **FR-D5**
(δ = 5 — battery max 3; faithful band of width 4), **FR-GL** (the
first η ≠ 1 frame for this geography, at the corrected key Φ₂ =
Φ′² + 3xΦ′ + 108). Preregistered exact predictions, all
hand-derived first: FR-M3 self-shadow ShC = [64, 40x, 12], pins
[12, 7, 4] vs Θ [10, 7, 4] (attained at j = 1, 2; SLACK at j = 0 —
first measured slack instance); FR-D5 ShC₀ = 256Φ′ at 41 = Θ₀;
FR-GL ShC₀ = −486Φ′ + 2916x at 13 = Θ₀, ShC₁ = 9Φ′ − 27x at 7 = Θ₁
(both attained, two-flavored digits). Constructed interference
rows: **cancel41** (f = Φ₂² − 256Φ′: honest DECIDED tRAM(41), PARI
{(8,1)}, while the shadow j = 0 coordinate is IDENTICALLY ZERO —
the sharpest possible "shadow is not a function of the honest
data" witness); add41 (divergence exactly at Θ₀ = 41, shadow pin
displaced to 45); FR-M3 cancel7 (shadow blind to an honest pin AT
Θ₁); FR-GL anchor13 (divergence at Θ₀ with equal pins, different
digits, honest σ {(4,2)} PARI-exact at the gauge-live frame). Plus
90 random in-budget members (level-1 gate spot-checked), 3 PARI
carrier facts, and the battery digit replication of m-1.

RESULT: run 1 RED 485/1 KEPT (`gentow3_pe1_fresh_output_run1_RED
.txt`, md5 485946fc; the one miss = MY instrument literal — the
D5-B40 check demanded mindiff ≥ 41 at both coordinates where
coordinate 1's threshold is Θ₁ = 23; measured divergence 24 clears
it and the consulted pin 19 — theorem fine, literal over-strict;
one-literal repair disclosed in-file). Run 2 **GREEN — 485 checks,
0 violations, 3/3 teeth** (runner md5 35ad32aa, output md5
94160b22): tally SELF 33, GATE 9, FLOOR 210, ENTRY 210, BAND 6,
CANCEL 5, ADD 1, GP 8, TEETH 3. Teeth: T-F-UP ×10 (Θ+1 mutant
killed by ten attained pins across five frames incl. μ₂ = 3 and
η ≠ 1), T-F-DOWN (Θ−1 mutant refuted by the faithful (40,19)
2SIDED row + PARI), T-F-CANCEL (cancel41). Bonus datum: the B40
row's j = 1 divergence measured at exactly wt(g) + δ − E₂ = 24 —
the linear ledger is tight at a second coordinate.

## GRADE LINE

**passPE1: NOT CLEAN — 1 GAP (F-1) + 3 MINOR (m-1, m-2, m-3);
acceptance counter stays 0/2.** The theorem's mathematical core
(floor, band, attainment, T(a)-corollary) survived independent
re-derivation, an adversarial fresh route at three
out-of-battery frames (μ₂ = 3, δ = 5, η ≠ 1) with dual oracles,
and a negative tautology audit; the owed repair is a dated gauge
annex of the GT1-r1 shape (pin ĉ_t := lift(c_t·η^{W(t)}) at the
x-free site, fix or fence the "equivalently" clause at f₁ ≥ 2,
add the η = 1 battery-blindness reading to GENTOW3-BOX-2, and
optionally adopt FR-GL as the note's η ≠ 1 machine contact) plus
the three MINOR record corrections.
