# W12 passPE1 report — hostile verification pass 1 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD (composed
20dd400..2c2c6af, seal f669cb0, verdict c16c717); ledger adjudication 97122f2
read first; supplier notes read at their S9 pins. Per the effort directive
this note is the J-D block's complete-theorem target: FULL hostile bar (two
consecutive clean passes accept). This pass fixes nothing; it quotes and
classifies.

**VERDICT: NOT CLEAN — 1 CRITICAL (display-level: THEOREM W-12.A's count
formula as displayed is FALSE for every shape containing a simple branch;
the missing factor is Π_{i: m_i=1} q^{d_i(N−1)}; the S2 proof actually
establishes the corrected law, and no machine row or in-note consumer
exercises the false display) + 3 JUSTIFICATION GAPS + 2 minor. Clauses
(i)-at-the-instances, (ii), (iii) and both instance lemmas SURVIVE full
independent re-derivation. Machine leg: runner md5-identical to seal, re-run
exit 0 GREEN 3,232,506/0, every count == §S10, artifacts timing-only
(restored). Fresh route: own arithmetic on 3 cubic + 2 quartic rows, 0
mismatches, pointwise identical to the committed JSON. Counter: 0/2 (this
pass is not clean); r1 owed on the findings below.**

---

## 1. FINDINGS

### FINDING 1 — CRITICAL (statement display false; conclusion re-proved true)

**Quote (S1, THEOREM W-12.A display):**

> Then the window-N count of monic f realizing T is EXACTLY
>
>     #T(N) = C₀(q) · Π_{i: m_i≥2} [ (Π_S S_{λ_{i,S}}(q^{d_i})) · q^{d_i·B_i(N)} ],

and the companion cell clause in the same statement:

> counts factorizing cell by cell (every (configuration,
> residual-letter) cell has exactly Π q^{d_i B_i(N)} members)

**Classification: CRITICAL ERROR (display level).** The configuration
C = {(P̄_i, m_i)} has Σ m_i d_i = n, so it includes the simple branches
(m_i = 1), but the displayed product runs over {i : m_i ≥ 2} only. Each
simple branch contributes a volume factor q^{d_i(N−1)} (S2.1's own text:
"Simple branches (m_i = 1) are σ-decided at level 0 … count q^{d_i(N−1)}
each"), which the display omits. The formula as printed is therefore false
for EVERY shape with at least one simple branch, and only correct for
single-repeated-branch shapes (pure-power level-0 patterns).

*Counter-instances, checked against the note's own suppliers and its own
committed artifacts:*

* SEP-SPLIT at n = 2 (two simple branches, no repeated branch): display
  gives #T = C₀(q) = q(q−1)/2, an N-free number; W-11(ii) at pin 31506b3
  (which the same statement claims as an instance: "W-10(2,1,1) and every
  W-11 row are instances") gives ((q²−q)/2)·q^{2N−2}. Off by q^{2(N−1)}.
* DBL RAM(1) at n = 3 (pattern (x−c̄)²(x−d̄); repeated branch polygon
  (0,1)–(2,0), λ = (1); one simple linear branch): display gives
  C₀·(q−1)·q^{2N−3} = q(q−1)·(q−1)q^{2N−3} → at (Zp, q=2, N=5): 256.
  The committed artifact `w12_checks_results.json`, row (Zp,2,5),
  dbl_keys["('RAM', (1,), ())"] = 4096 = 256 × q^{N−1}. The missing factor
  is exactly the simple-branch fiber q^{N−1}, which the note's own LEMMA
  W12-L1(c) carries correctly ("= q^{N−1} × (the W12-L0 per-center
  count)").
* Internal inconsistency visible from the statement alone: with the
  displayed formula, dens_T := #T(N)/q^{nN} would be N-dependent for any
  shape with a simple branch, contradicting the same sentence's "dens_T
  … ∈ ℚ(q) is shape-only".

*Why everything downstream survives:* the S2.3 assembly line ("Combining
S2.1 (product over branches) × S2.2 (each branch) × the level-0 census
C₀(q)") proves the CORRECTED law #T(N) = C₀(q) · Π_{i: m_i=1} q^{d_i(N−1)}
· Π_{i: m_i≥2}[…] — S2.1 displays the simple-branch count explicitly. Every
in-note instance of W-12.A that is machine-checked is a single-branch shape
(the seven TRP families, the QRT quadruple-center rows); the DBL laws are
consumed through W12-L0/W12-L1, which carry the q^{N−1} fiber correctly; the
S3.4 n = 2 and n = 3 menus take their laws from W-11/W12-L0/L1 and the
per-center TRP table (all correct). The corrected dens_T = C₀(q)·
q^{−Σ_{m_i=1} d_i} · Π_{m_i≥2} S·q^{−d_i(Σ_j⌈P_i(j)⌉+L_i)} is N-free and
shape-only, so the theorem's CONCLUSIONS (one q-polynomial per shape,
ℚ(q)-membership, characteristic-blindness) all stand on the corrected
display.

*Materiality beyond the note:* §S8 consumer 2 names W-12.A as "the
transcription spec for order-1 menu entries AT EVERY DEGREE"; a Lean
transcription of the display as printed would be false at every mixed
(multi-branch) shape. The ledger fold (BRIDGE_ADJUDICATIONS @ 97122f2)
reproduces the same formula ("#T(N) = C₀(q)·Π[Π_S S_λ(q^d)·q^{d·B(N)}]",
index set not shown) and inherits the error. The battery cannot catch it:
no roster row checks a multi-branch shape through the W-12.A display route.

*Repair shape (one line):* product over ALL i, with the m_i = 1 convention
B_i(N) = N−1 and empty residual product — or an explicit
× Π_{i: m_i=1} q^{d_i(N−1)} factor; same fix in the cell clause.

### FINDING 2 — JUSTIFICATION GAP ([W12-H]'s "exactly" list omits the order-≥2 σ-decision input)

**Quote (S4.2):**

> The general clause (i) at orders ≥ 2 — shapes with repeated residual
> factors of degree ≥ 2, i.e. towers whose key polynomials have degree
> > d — is CONDITIONAL on, exactly:
> * **(H-a)** the JC composite-stage warrant …
> * **(H-b)** the JB membership faces …
> * **(H-c)** the J-D1 (H1) residue-structure package …
> * **(H-d)** the universal residual censuses OVER RESIDUE TOWERS …

**Classification: JUSTIFICATION GAP** (box-pricing only; no order-≥2 law is
claimed, so nothing proved is touched). A fifth obligation exists that none
of (H-a)–(H-d) names: the order-≥2 LEAF/DECIDEDNESS theorem — the
higher-order analogue of the Ore step that clause (i) itself uses at order 1
("σ(T) is read off by Ore's theorem", S2.3), i.e. the GMN order-r types
theorem giving σ and (A0)-well-posedness at separable composite-stage
residuals. S4.1's classical-inputs list is explicitly order-1 scoped
("Ore's theorem / GMN order-1 (S2.3)"), so this input is in neither the
classical list nor the box. (H-a) is a no-cancellation/level-detection
warrant and (H-c) a residual dictionary; neither, as quoted from their
sources, states the leaf theorem "separable order-r residual ⟹ decided
with (e, f) read off". If the composer's intent is that (H-c)'s FGMN-4.2
pairings carry it, that derivation is not displayed. Since W-12.D
consumption at n ≥ 4 needs (A0) at those shapes, the box's "exactly" is an
under-count by one named classical/weld input.

### FINDING 3 — JUSTIFICATION GAP (S1 taxonomy sentence contradicts S2.5's own frontier row)

**Quote (S1, conventions):**

> separable residuals decide (Ore leaves), repeated residual roots of
> degree 1 refine (recenter deeper), repeated residual factors of degree
> ≥ 2 open order-2 (composite) stages.

**Classification: JUSTIFICATION GAP** (definitional display; low blast
radius). The trichotomy is incomplete: a repeated residual root OF DEGREE 1
on a side with e ≥ 2 does NOT refine by recentering — it opens a key of
degree e·d > d, i.e. an order-≥2 stage. The note's own S2.5 row is exactly
this case and says so: "QRT-G2(h; (1²)) [NOT decided at order 1 — the
composite-stage frontier]: … members open a DEGREE-2 key (order 2)" — with
λ = (1²) a repeated residual root of degree 1 on the e = 2 side. As a
general-n convention the S1 sentence misclassifies this genre as
"recenter deeper". No harm at n = 3 (every e ≥ 2 side there has g = 1, so
no repeated residual can occur on one — verified in the completeness case
tree, and the runner's `assert e == 1` never fires); the theorem statement's
own fence ("ORDER 1 means: every key polynomial in the read has degree d")
is the correct one and is what S2.4/S2.5 actually use. Repair: add the
e ≥ 2 qualifier ("repeated residual roots of degree 1 ON AN e = 1 SIDE
refine; on an e ≥ 2 side they open an order-2 stage, S2.5").

### FINDING 4 — JUSTIFICATION GAP (the disc = 0 oracle bracket's cited warrant misses the exact-cube genre)

**Quote (S7, W12-ORACLE bullet):**

> exact integer disc == 0 ⟹ never decided (Python-exact
> disc, mixed bracket — proved for cubics via W-11's square-block
> case + the S3.2 species, see S3.2)

**Classification: JUSTIFICATION GAP** (machine-bracket warrant; the
operational check is unaffected). A monic cubic over ℤ with disc = 0 is
(x−a)²(x−b) with a ≠ b — covered by W-11's mixed-characteristic
perfect-square case through W12-L1(c) — or (x−a)³ exactly. The exact-cube
genre is covered by NEITHER cited lemma: its window member is not in the
S3.2 species (recentered at the read's center c, b₁ = 3(c−a)² can still be
window-visible at the read state where b₀ = (c−a)³ has left the window —
e.g. v(c−a) = m with 3m ≥ N > 2m), and S3.2's proof needs b₁ = b₀ = 0
in-window. The bracket is still operationally true (the conservative TRP
reader's refine chain on such a member ends at v(b₀) ≥ N ⟹ UNDECIDED, so
"reader never decides" holds), but that one-line argument — conservative
convention, not the cited pair — is the warrant that actually closes it.
Repair: one sentence replacing the cite for the cube genre.

### MINOR 1 — Step 1's closed form degenerates on zero-step progressions

**Quote (S3.4, Step 1):** "Σ_{x ∈ P_F} dens_F(x) = c_F(q)·q^{−m₀−Σm_ia_i}·
Π_i (1 − q^{−m_ib_i})^{−1} ∈ ℚ(q) by d_F iterated geometric series
(absolutely convergent: q ≥ 2, m_ib_i ≥ 1)". If some progression has step
b_i = 0 (a point coordinate — (A1)'s "arithmetic progressions" does not
exclude it), the displayed factor divides by zero while the sum is trivially
finite; and the integrality of ℓ_F's coefficients (needed for
q^{−m_ib_i} ∈ ℚ(q)) is implicit (it does follow from ℓ_F being
integer-valued on P_F). Cosmetic: point families are handled in the n = 2
instance as d_F = 0 families, and every in-note P_F has b_i = 1 or 2.

### MINOR 2 — P-6 verdict sentence lists non-shared rows inside the "identical across Zp/Fqt" display

**Quote (S10, P-6):** "the measured value is IDENTICAL across Zp/Fqt at
every shared (q, N) — (2,3…7): 32/144/608/2720/11328; (3,2…4): 27/243/2511;
(4,2/3): 64/1024; (5,2): 125; (8,2): 512; (9,2): 729". The (4,·), (8,2),
(9,2) values are Fqt-only rows (no Zp prime-power rows exist — BOX-6); the
list format invites reading them as cross-checked pairs. The claim is
correctly scoped by "shared" — artifact check: exactly 9 shared (q,N) pairs
exist and all 9 are equal across kinds (verified from the committed JSON
this pass) — so this is display hygiene only.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) THEOREM W-12.D re-derived in full from (A0)(A1)(A2).** Step 1: the
iterated geometric series and the shifted-product closed form re-computed
(exponent q^{−m₀−Σm_ia_i}, ratio q^{−m_ib_i}); inclusion–exclusion over
finite unions valid (coordinatewise AP∩AP = AP or empty); q-uniformity of
the resulting expression is carried by (A1)'s uniformity clause, as
displayed. Step 2: visible sets increase to P_F for any finite ν_F;
monotone partial sums of a positive convergent series. Step 3: definitional
given (A1)-disjointness; limit by (A2). Step 4 re-derived: lower bound needs
(A0) + disc-0-null (displayed, classical); upper bound needs the two-case
truncation argument with (A0) applied to F itself (displayed); openness by
Krasner (displayed, classical). **Hidden-hypothesis hunt: negative.** No
disjointness beyond (A1) is consumed (cross-type disjointness IS in (A1)'s
pairwise clause); window-uniformity is explicit in (A1)'s "for every window
N" quantifier with N-free data; the Haar tie consumes only the displayed
classical steps (measurability from openness; per-window finiteness of the
visible list is implicit but forced by (A1) itself — disjoint classes of
exact positive count in a finite space). The n = 2 firing was checked
against W-11's actual post-r2 displays at pin 31506b3: all six core-family
laws match W-11(ii) exactly (RAM (q−1)q^{2N−2k−1}, 2SIDED
(q−1)²q^{2N−3−w₁−w₂}, SPLITEQ ((q−1)(q−2)/2)q^{2N−2k−3}, INERTDEEP
((q−1)/2)q^{2N−2k−2}, SEP ((q²−q)/2)q^{2N−2}, per center × q where
applicable); disjointness+exactness are W-11(ii)(iii)'s partition; the
SPLIT-TAIL routing through (A2) is correct and necessary (its per-center
count (q−1)q^{N−2} is not dens·q^{2N}-shaped) and r(N) = q^N +
q⌊(N−1)/2⌋(q−1)q^{N−2} re-derived; all four series re-summed: R_split =
q³/(2q²(q+1)) = q/(2(q+1)), R_inert = q/(2(q+1)), R_ram = 1/(q+1), Σ = 1.
The n = 3 conditionality is exactly (hMenu-3)+(hExhaust-3) as displayed:
no composite stage can open at n = 3 (an e ≥ 2 side with g ≥ 2 needs side
length ≥ 4 > 3; a repeated residual factor of degree ≥ 2 needs g ≥ 4), so
[W12-H] is genuinely not needed; the deep-decided TRP mass (which would
otherwise poison (A2)) is supplied to (A1) by (hMenu-3), and the TRP tail
σ-certification lemma is explicitly assigned to the boxes in S3.1 ("These
three named lemmas are exactly (hMenu-3)/(hExhaust-3)'s distance"); (A0)
for the missing families folds into the menu hypothesis. Modulo FINDING 1
(which lives in W-12.A's display, not in W-12.D), clause (iii) is PROVED
as stated.

**(2) THEOREM W-12.A re-derived.** LEMMA W12-S2.1 (window Hensel product):
cardinality, minimal-divergence-level injectivity (the coprimality/degree
argument re-checked), surjectivity via O-level Hensel, σ/decidedness
transport — sound. S2.2 digit calculus re-derived: slot bookkeeping
B = mN − Σ⌈P(j)⌉ − L, the membership trichotomy (vertex/on-side
lattice/automatic ceiling), in-window pinning (all priced heights ≤ P(0) ≤
N−1), and the right-to-left census sweep S_T = Π_S S_{λ_S} (unit-normalized
residuals; the (q−1)² vs (q−1)³ cross-check against W-11's 2SIDED confirmed
— the quoted per-node form (q−1)²q^{2N−2−u−w₁} is the CORRECTED post-r1
W-11 text). Censuses re-derived from scratch: g = 2 row (Q−1)(Q−2)/2,
Q(Q−1)/2, Q−1 (sum Q(Q−1)); g = 3 row incl. S_{(3)} = (Q³−Q)/3,
S_{(1,1²)} = (Q−1)(Q−2) (sum Q²(Q−1); spot values at Q = 2, 3 as displayed).
Factorization re-derived at n = 2 (W-10 (2,1,1): B = 2N−3 ✓), at n = 3 for
all SEVEN TRP families including both wild strata (RAM3: ⌈2h/3⌉+⌈h/3⌉ =
h+1 for 3∤h checked at h = 1,2,4; LINRAM2/RAM2LIN parity+vertex conditions
2u₀ > 3u₁ / u₀ > 3t re-derived; all seven B-exponents and S_T factors match
the table; σ-assignments by Ore re-checked; depth-0 completeness case tree
re-built: one-side 3∤h xor 3|h, vertex-at-1 e = 2 xor e = 1, vertex-at-2
e = 2 xor e = 1, 3LIN — no missing case), and at n = 4 for QRT-G2(h;λ)
including the wild λ = (2) p = 2 stratum (heights sum 5h+1, L = 2,
B = 4N−5h−3 ✓; the (1²) row correctly priced as order-1 volume with
σ-resolution left to [W12-H]). **[W12-H] fifth-member hunt: FINDING 2**
(the order-≥2 leaf/σ-decision input). No sixth found: lift-convention
independence is correctly fenced OUT (BOX-5, statement scoped to the read's
own Φ); the Φ₂-adic development itself is elementary monic division; the
membership faces, carry warrant, dictionary, and tower censuses are (H-b),
(H-a), (H-c), (H-d).

**(3) THEOREM W-12.C + LEMMA W12-L1 re-derived.** L1(a) = two-branch
S2.1 ✓. L1(b): the expansion (a₂′, a₁′, a₀′) = (B₁−ρ̃, B₀−ρ̃B₁, −ρ̃B₀)
re-computed; all three polygon cases re-checked (2w < u: exact w-pin with
letter −ρ̄·digit; u odd RAM: v(a₁′) ≥ (u+1)/2 > u/2; u = 2k: digit_k(a₁′) =
−ρ̄c₁ since v(B₀) = 2k > k, residual R_f = −ρ̄·R_g a unit multiple — same
type, same refinement letter); refinement preserves the setup (ρ̄ survives
recentering, v(s) ≥ 1); tail exits transfer verbatim (B₀ = 0 ⟹ a₁′ = −ρ̃B₁
exactly). L1(c): disc F = disc(G)·res(G,L)² with res(G,L) a unit (Ḡ(d̄) =
(d̄−c̄)² ≠ 0), so disc≠0-lift σ-sets biject; fiber q^{N−1}; drainage
(q−1)q^{2N−1} = q(q−1)·q^{N−1}·q^{N−1} re-derived from W-11(iii) at pin.
W-12.C: the partition identity is S2.1-branchwise decidedness (separable
patterns decided at level 0). U₃ bounds: LEMMA W12-S3.2 re-derived in
full — both constructed lifts checked in both the B ≠ 0 and B = 0 genres
(F_A's quadratic factor polygon {(0,2K+1),(1,t),(2,0)} with 2t < 2K+1 gives
two unit-... two O-roots at distinct valuations resp. RAM(2K+1); F_B's
polygon {(0,L),(2,t),(3,0)} with L ≥ 3N > 3t gives the e = 2 block + simple
root resp. e = 3 at 3∤L; congruence mod π^N holds since every correction
sits at height ≥ N; disc ≠ 0 étale in every case; σ_A ≠ σ_B in all four
pairings); species count q·q^{N−1} = q^N; upper bound = stratum size
q^{3N−2}. All confirmed by the independent PARI witness leg (85/85) and by
my fresh route (species all-undecided, q^N per row).

**(4) Blueprint-divergence box + W-11 §S4.3 reconciliation: FAITHFUL.**
The blueprint's W-12 row quoted in S0 is byte-identical to
`docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S3.1 (line 302); the
(J-D1) block quoted in S5 is byte-identical to §S2.4 (lines 247–255); the
cited section numbers are correct; "execution-order step (8)" matches the
blueprint's S6 recommended order ("(8) W-12 as a composition display at the
(H1) row"). The divergence box is accurate: the blueprint row prices ONLY
the J-D1 composition display (S-priced), which §S5 delivers at that price
(nothing re-proved there; consumed-downstream framing preserved; (GR-B)
cited only inside §S5; DULEMMA correctly declared display-only), and the
assembly S1–S4 is honestly flagged as charge-directed extra content. The
W-11 §S4.3 reconciliation names (P1)/(P2)/(P3) exactly as W-11 states them
(incl. the owed inputs list: g ≥ 2 censuses, JA-GRID/JB-VTX + row-12
residue, JC warrant), and the claim that the census-owed input is
discharged AT THE ORDER-1 LAYER is correct as scoped (S2.2's explicit
polynomials, machine-checked at g = 2, 3 both characteristics).

**(5) Supplier pins: ALL VERIFIED against git log this session.** W-11 arc
7020ceb (seal) / cb05127 (verdict) / 8c87fa3 (r1) / 473a993 (PE2) / 31506b3
(r2 = the W-11 file's last commit — consumption is at post-r2 HEAD);
W-10 2e6fdd8/9506a55; J-D0 1642275/9387eb1; ledger fold 17d2a32; GRTJA
f131c53; GRTJB+GRTJC 83f47f4; GRTW2 adc6cf3; LIFTCORNER 08f61e9; WELDMASTER
66b3498; DULEMMA 048cf6d/f819f26; OPEN2ATTACK bd82766/4a970aa. Every commit
exists and its subject matches the role the note assigns it. **Stale-text
sweep: CLEAN.** W-12 consumes no pre-r1/pre-r2 W-11 display: the W12-L0
per-instance forms match W-11's post-r1 S2.5 window laws exactly (RAM
(q−1)q^{N−1−u}·q^{N−(u+1)/2}, 2SIDED (q−1)²q^{2N−2−u−w}, SPLITEQ/INERTDEEP
constants ((q−1)(q−2)/2, q(q−1)/2) with q^{2N−3k−2}, SPLIT-TAIL
(q−1)q^{N−1−w}, UNDECIDED q^{N−1−M}); the bracket 1+Σ(q−1)q^{s−1} = q^{k−1}
is W-11 S2.5's post-r1 text; the S2.2 cross-check quotes the CORRECTED
2SIDED per-node form; the r1-struck S2.4 per-node legs (q²X/X/qX) appear
nowhere in W-12; the r2-supplied telescoping ('whence') is not consumed
(BOX-8 declines the every-window symmetry at n ≥ 3, and the n = 2 split =
inert value in S3.4 is derived from the limit series, not the every-window
claim); the r2 mixed-2 pin is inherited with its correct scope ("the pin is
load-bearing only for p = 2 disc-spectrum displays, never for counts").

**(6) n = 2 → general-n fencing + BOX-7.** Every consuming surface checked:
S2.6 fenced ("Fix n = 2"); S2.7 transports by PROOF (L1(b)), not by fiat;
S3.3's use of W-11 at general n applies it only to the quadratic branch
factor through LEMMA W12-S2.1's branchwise decidedness (legitimate); S3.4's
unconditional firing is n = 2 only; BOX-8 declines the n ≥ 3 symmetry;
W-12.B correctly presents n = 2 as its only exact instance. **BOX-7 vs the
runner: EXACT MATCH.** `read_trp` exits UNDECIDED precisely when the current
recentered constant term leaves the window (`u0 = R.val(B0); if u0 is None:
return decided=False`) — certifying NO tail σ, exactly the disclosed
conservative convention; the DBL side inherits W-11's proved convention
including SPLIT-TAIL certification (`read_dbl`: `2*w + 1 <= R.N` ⟺
w ≤ (N−1)/2) and is cross-checked pointwise against the md5-pinned sealed
w11 classifier (W12-L1X). The runner's `assert e == 1` at repeated residual
roots encodes the (true) fact that no e ≥ 2 side at n = 3 carries a
repeated residual (cf. FINDING 3 — the assert is correct; the S1 sentence
is the defective surface).

---

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  7dc040d94fbbb1e8d20ac817b665d418 == `git show f669cb0:…` — byte-identical
  to the seal commit. All five frozen-import pins re-hashed and matching
  (w11 500aae15…, w10 a9c34244…, iterlawn cae45db2…, grt_jc 03811b69…,
  jd0 d3a5e13d…).
* **Re-run (single fresh run, this pass):** exit 0, **3,232,506 checks /
  0 violations, teeth 23/23/8/1273**, zero skips, 326.6 s. Every family
  count equals §S10 exactly: PIN 5, LVL0 138, SHAPE 164, QRT 27, L0HIST
  306, BLOCK 1,594,670, L1X 1,594,090, DRAIN3 1,183, ORACLE 41,923.
* **Artifacts:** diff vs committed = timing-only (6 per-row elapsed_s
  values + total 323.0→326.6; stdout same 6 timing lines); committed bytes
  restored, md5s re-verified (0557b15f… / 05776c9e…).
* **Bookkeeping re-derived from the roster (independent arithmetic):**
  7,105,774 = Σ q^{3N} over the 23 cubic rows ✓; 2,946,008 = Σ q^{3N−1} ✓;
  580,550 = Σ q^{4N−3} over 8 quartic rows ✓; 69,053 = Σ q^{2N} over 11
  L0HIST rows ✓; oracle 40,645 = Σ q^{3N} over the 5 Zp rows ✓; species
  85 = Σ q^N ✓; QRT oracle 1,516 = 32+512+972 ✓; decided cubics 38,874 =
  Σ (q^{3N} − (q−1)q^{2N−1} − U₃TRP_row) ✓; total 3,232,506 = Σ families ✓.
  §S10's spot values ALL re-derived from the closed forms (the (Zp,2,4)
  6-key table; 3LIN(3,2,1) = 512 at (2,7); (Fqt,9,2) RAM3(1) = 5832; the
  QRT triples 512/512/0, 729/243/486, 6144/3072/3072; DBL spots 128/5832/
  192); the 22-key (2,7) menu confirmed in the committed JSON (both kinds).

## 4. FRESH ROUTE (own arithmetic, no runner imports)

`/tmp/w12_fresh_route.py`, written from scratch this pass: own ring classes
(ℤ/p^N and F_p[t]/t^N), own cubic/quartic shift arithmetic, own hull code,
own recursive TRP reader (conservative tail), own direct DBL cubic reader
(L1(b) mechanics), own level-0 pattern classifier, own transcription of the
closed forms. Rows: cubic (Zp,2,4), (Zp,3,3), (Fqt,2,4) — 27,875 cubics
read; quartic (Zp,3,3), (Zp,2,4) — 27,875 stratum members. Results:
**0 mismatches** — every depth-0 decided TRP key equals its S2.4 closed
form both directions (6 keys at (2,4) incl. FULL(1,'12')=16/FULL(1,'3')=32;
3 keys at (3,3)); DBL undecided = (q−1)q^{2N−1} on all three rows
(128/486/128); species all-undecided at exactly q^N (16/27/16); QRT keys
exact including the (Zp,2,4) λ=(1,1) zero and the (3,3) triple 243/486/729.
Cross-check vs the committed `w12_checks_results.json`: per-key dicts,
dbl_undecided, and U3TRP **pointwise identical** on all matched rows. The
U3TRP characteristic-uniformity bonus observation was independently
confirmed from the artifacts: exactly 9 shared (q,N) pairs, measured value
equal across Zp/Fqt at all 9 (and my own Fqt(2,4) run reproduces 144 = the
Zp value by fresh eq-char arithmetic).

## 5. ARC / COUNTER

Composed at attempt 0/2; this is PE1, the arc's first hostile pass. PE1
outcome: **1 CRITICAL + 3 GAPS + 2 minor ⟹ NOT CLEAN; counter stays 0/2;
r1 owed** (F1 is a display strike-and-replace with zero blast radius on the
proofs; F2/F3/F4 are one-sentence box/convention repairs). Machine and
fresh-route legs are arc facts for the record: seal intact, battery GREEN
and reproducible, instance layer independently confirmed.

— passPE1 verifier, fresh context, 2026-08-08.
