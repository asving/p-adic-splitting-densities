# GENHN passPE1 — first hostile pass (2026-08-09)

**VERDICT: NOT CLEAN — 2 CRITICAL + 1 GAP + 2 MINOR (+4 remarks). The
clean count stays 0/2.** Headline: **LEMMA GENHN-T(b) (tower
composition) is REFUTED at the leaf level by constructed n = 8
counter-instances, PARI-confirmed on two independent oracle routes**
— the note-frame inner read (division in the stage algebra, Φ′ = 0)
predicts composed σ {(4,2)} and {(4,1),(4,1)} where the true fields
give {(8,1)}; the defect's mechanism is identified exactly (the
Φ′-classes of the composed slot basis, which the stage algebra kills,
undercut the stage-algebra pins), and a corrected read (the composed
key Φ₂'s development of f itself) matches PARI on all constructed
instances. Scope: n ≥ 8 towers only — P(5), the n ≤ 7 assembly, the
genre classification, GENHN.C at μ = 2, and GENHN-T(a)'s
event-level criterion all SURVIVE this pass, several now with
first-ever machine contact (the f₁ = 3 stage, the comp = 2 band
census, the F₈-letter refine transfer, the (1,3,2) σ-dictionary).

Target: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` at HEAD
d64b0a8 (850e77e body + [r1] + [e2] errata bc1b996/961d0ff/46bf675/
58b1080). Instrument: `verification/openmath/genhn_pe1_fresh.py`
(independent: no battery imports; own slot-min reader; PARI via
global factor + nfinit([g,[2]]) + idealprimedec — NO factorpadic),
artifact `genhn_pe1_fresh_output.txt`, GREEN as an instrument
(0 violations on its scored checks; the note-frame refutation is
recorded as a 4-instance tally, not an instrument failure).

---

## FINDINGS

### F1 — CRITICAL. LEMMA GENHN-T(b): the tower composition's inner
### read is unsound; composed σ refuted at constructed n = 8 members.

**Claim attacked** (S8, proof of (b)): "The inner opening happens
inside the (μ, K) stage system ... Apply THEOREM GENHN.CLASS +
GENHN.A TO THAT SYSTEM ... σ-dictionaries compose as
(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s). No new mechanism." Consumed by
THEOREM GENHN.B's "(CS-1) and (CS-2) hold ... towers included via
LEMMA GENHN-T" — load-bearing for every n ≥ 8 genre with a decided
inner leaf.

**Counter-instances** (outer genre (2,1,4) at n = 8, q = 2, h = 1 —
the note's own first-live tower geography, same entry shape as the
battery's P8 witness; f(x) = G(x²−2), so the outer stage state IS
G's coefficient tuple; disc ≠ 0 verified on each):

| G(Y) | note-frame inner read (stage algebra) | T(b) composed σ | PARI (both routes) |
|---|---|---|---|
| Y⁴+16Y+96 | pins (21,14), inner-RAM(21) | {(8,1)} | {(8,1)} — agrees, but see below |
| Y⁴+16Y³+32Y²+96 | pins (28,14), residual T²+T+1 irred/F₂ → inner-INERT | **{(4,2)}** | **{(8,1)}** |
| Y⁴+16Y³+32Y²+224 | pins (30,14) → inner-2SIDED(14,16) | **{(4,1),(4,1)}** | **{(8,1)}** |

(+ deep-perturbation variants of each: same refutations; 4 refuted
jobs total. Oracle route 1 = global nfinit/idealprimedec; route 2 =
factorpadic cross-check: each octic is LOCALLY IRREDUCIBLE with
e = 8, f = 1. Base-genre controls validate the verifier's semantics:
plain (2,1,2) INERT/2SIDED/RAM constructions give {(2,2)} /
{(2,1),(2,1)} / {(4,1)} exactly as GENH4's accepted dictionary.)

**The mechanism (exact, not a conjecture).** The composed coordinate
ring has FOUR slot classes per dv₂ = 4v ladder: {1, x, Φ′, xΦ′} at
classes {0, 2, 1, 3} mod 4 (x² = Φ′ + 2, x³ = xΦ′ + 2x). The note's
inner read develops the stage polynomial G(Y) over the stage ring
R = Ô[x]/(Φ′) — where Φ′ ≡ 0 — so it sees only the {1, x}-shadow.
But at an actual root x₀ of f, Φ′(x₀) = Y₀ ≠ 0 (dv₂(Y₀) = 5 here):
the R[Y]-division identity lifts to Ô[x][Y] only modulo
Φ′·H(x, Y), and evaluation injects the correction Y₀·H at dv₂ =
5 + dv₂(H). Concretely, the honest inner object — the development of
f ITSELF by the composed degree-4 key Φ₂ := Φ′² − 4x (division in
ℤ[x], no quotient) — carries Φ′-class terms the stage algebra
killed: for the second row, C₀ = 128 + 128x + **16Φ′** + 64xΦ′, and
16Φ′ sits at dv₂ = 21, UNDERCUTTING the stage-algebra pin u₂ = 28.
True pins (21, 14) → inner-RAM(21) → v(Φ₂(x₀)) = 21/8 → 8 | e →
{(8,1)} = PARI, on 3/3 instances (verified in the instrument:
`inner_read_true`, scored 6/6 jobs). Even the first row, where σ
agreed, has its LEAF LABEL wrong: stage-algebra RAM(21) vs true
RAM(25) (C₀ = 128 + 32Φ′; the 32Φ′ is the carry from 16x² = 32 +
16Φ′) — so tower COUNT laws priced through T(b) are also wrong, the
agreement was parity luck.

**What survives / what breaks.** GENHN-T(a) — the criterion (towers
⟺ μ ≥ 4 ⟺ n ≥ 8) and the EVENT-level witness — survives: in each
instance and in the battery's P8 witness the inner CS event's entry
data (hull (0,10)–(4,0), residual (y+1)²) sits strictly below the
correction floor (entry pins dv₂ ≤ 20 < 21), and the corrections are
key-term products landing strictly above the side. What breaks:
GENHN-T(b)'s proof AND its leaf-level content; S8(b)'s grade line
("inherits GENHN.A's clause grades at each level"); THEOREM GENHN.B's
tower clause, hence the display "P(n) for ALL n ... conditional
EXACTLY on {[GENHN-HE(μ ≥ 3)]} ∪ {S9 boxes} ∪ {arc stack}" — the word
EXACTLY is now false for n ≥ 8: an unlisted defect exists. P(5)/P(6)/
P(7) and the μ = 2 σ-theorem GENHN.C are tower-free and untouched.
The battery could not catch this: GENHN-BOX-3 honestly disclosed
"tower LAWS (witness only)".

**Failure scenario.** Any degree-≥ 8 density assembly that prices a
tower genre through T(b) at a decided inner leaf emits wrong σ
strata — e.g. it books an unramified-quadratic residue extension
{(4,2)} on a locus whose members are totally ramified octics
{(8,1)}; Σ_τ R_τ = 1 would silently misdistribute mass between τ's
at n = 8.

**Repair direction (from the data, not prescribed).** The corrected
inner state = the Φ₂-adic development of f in the composed slot
basis — i.e. genuine order-2 OM types (composed keys), which is
exactly the machinery the repo's classifier already implements at
Lean level. The multiplicative (e,f)-ladder/census composition ITSELF
may well survive under that frame (my corrected reads compose
multiplicatively and match PARI); what cannot survive is "no new
mechanism: this is GENHN.A applied to the stage system" — the stage
algebra is not evaluation-faithful at inner-leaf depth.
