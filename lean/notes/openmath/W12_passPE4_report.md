# W12 passPE4 report — hostile verification pass 4 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r3
(**b17238a**, the σ-pin). Read first: all three prior reports (PE1 2b47711,
PE2 1be15d2, PE3 c9c5c0e), all three repair diffs (r1 ba0d1a4, r2 99f1813,
r3 b17238a), both dated annexes, the r3 adjudication ledger entry (b8dfe62,
"~40 σ-surfaces classified"), the supplier notes W-11 and HEX3 (incl. HEX3's
own r3 = b6a1d69, landed in parallel). This pass fixes nothing; it quotes and
classifies. Fences/boxes/annexes/repair-records are read as part of the
statement. Charge-designated veins: (1) the r3 σ-pin's coherence (total? the
degenerate corner? faithfulness of the rejected-parse record; one divergence
row re-derived from HEX3.A); (2) spot-audit of 8 of the ~40 swept surfaces
across all three classes; (3) W-12.B's well-formedness at general n POST-pin;
(4) W-12.D's (A2)/(A0) consumption at the pinned definition — Steps 3–4
re-derived; (5) the HEX3-r3 race; (6) one unmined S2/S3 detail (chosen:
LEMMA W12-S3.2's constructed lift pair, characteristic by characteristic).
Draft kept at /tmp/w12_pe4_draft.md; fresh instrument /tmp/w12_pe4b_fresh.py.

**VERDICT: NOT CLEAN — 1 CRITICAL + 2 JUSTIFICATION GAPS + 2 minor
(+ 5 uncounted remarks).**

**The r3 σ-pin itself is COHERENT and TOTAL** (charge 1, the headline
check): the pinned predicate "the window digits force ONE σ across all
disc ≠ 0 O-lifts" is a well-defined condition on every window member, and
its apparent degenerate corner is EMPTY — every window class has a
disc ≠ 0 lift (disc is a nonzero polynomial in the coefficients and O is
infinite), and at order-1 decided shapes *every* lift is separable, so no
member is left without a σ-set to be a singleton of. The rejected-parse
record is faithful to PE3's finding and its arithmetic is independently
correct: I re-derived HEX3.A from the HEX3 note (not from the annex) and
reproduce the divergence table to the digit — 0.5000 (N=3) / 0.8579 (N=10)
/ 2.5333 (N=50) / **8.7833 (N=200)** — with mean slope exactly
(q−1)/(2q²(q+1)) = 1/24 at q = 2 (the per-step increments alternate
1/60, 1/15 with mean 1/24, confirmed at q = 2,3,5,7), and my own
transcription ties all 13 distinct committed U₃ values (23 rows).

**But the pin is INCOMPLETE at two load-bearing sites and the pass found a
CRITICAL in the vein the pin's own sweep does not cover:** (a) LEMMA
W12-S3.2's constructed witness pair is INSEPARABLE — disc = 0 — in equal
characteristic 2 (Lift 1) and equal characteristic 3 (Lift 2) on the
b₂ = 0 sub-species, so the proof's "both lifts have disc ≠ 0" is FALSE
there and W-12.C's stated lower bound q^N ≤ U₃^TRP is not established over
F_q[[t]] with p ∈ {2,3} (repair: one line — take B = π^N, never B = 0;
conclusion survives, nothing downstream moves); (b) THEOREM W-12.D's
hypotheses (A0)+(A1) never assert that core-family members ARE σ-DECIDED
nor that their forced σ equals the family label σ_F, and Step 4's lower
bound uses both — under the pin's own gloss (A0) reads as a tautology and a
one-family instance (F = all window-N monics, σ_F := split) satisfies
(A0)(A1)(A2) with R_split = 1 ≠ μ_split; (c) S10's P-6 bonus observation
still reads the conservative-measured U₃ sequence as "order q^{2N} as
W-12.B predicts" — false for that quantity by this note's own annexed
THEOREM HEX3.A (Θ(N·q^{2N})), and post-pin it is not W-12.B's quantity at
all. Two minors: W12-BOX-7 (the box the pin cites as its authority) still
assigns the conservative convention to the TRP side *definitionally*; and
S2.3's "in fact every lift" is false in equal characteristic at wild
decided shapes.

**Everything else checked CLEAN:** the 8 audited swept surfaces consume
what the sweep says (the battery's `dbl_undecided` verified
certification-inclusive from the runner source, not just from its output);
W-12.B is well-formed at general n under the pin (c_n unique by rational
interpolation; ring-dependence carried by the "independent of the
characteristic" clause); W-12.C's DBL term is exact *under the pin* —
verified at the supplier: W-11 proves BOTH directions (SPLIT-TAIL
certified; the residue genuinely lift-ambiguous "split and inert lifts BOTH
always exist"); Steps 1–4 of W-12.D re-derived, no step needs the rejected
parse. **Machine leg:** runner md5 == seal f669cb0, fresh full run exit 0
GREEN **3,232,506 / 0**, teeth 23/23/8/1273, every family count == §S10,
artifacts content-identical ex-timing, committed bytes restored.
**Fresh route (new to the whole arc):** W-12's own law suite run in TWO
ring types outside the note's S1 convention — a RAMIFIED mixed-char DVR
(ℤ₂[π]/(π²−2), v(2) = 2) and W(F₄) (mixed char, PRIME-POWER residue, the
gap W12-BOX-6 discloses) — **all laws exact, 0 mismatches, pointwise
identical to the committed JSON** on five (q,N) rows. **Counter stays 0/2;
r4 owed.**

---

## 1. FINDINGS

### FINDING 1 — CRITICAL: LEMMA W12-S3.2's constructed lifts are INSEPARABLE (disc = 0) in equal characteristic 2 and 3 on the b₂ = 0 sub-species; the proof's "both lifts have disc ≠ 0" is false there and W-12.C's lower bound is not established over F_q[[t]], p ∈ {2,3}

**Quotes (S3.2).** Statement: "Every TRP member with b₁ = b₀ = 0 over
O/π^N (after recentering; **b₂ ∈ πO/π^N free**) is σ-undecided:
U₃^TRP(q, N) ≥ q·q^{N−1} = q^N." Proof setup: "Let t = v(b₂) ∈ [1, N−1] ∪
{≥ N} and B a lift of b₂ to O, **chosen B = 0 when b₂ = 0**". The two
B = 0 branches: "**If B = 0: the quadratic is RAM(2K+1) (u odd):
σ_A = {(1,1),(2,1)}**" and "**If B = 0: choose 3∤L: one side, e = 3:
σ_B = {(3,1)}**". Closing warrant: "In every case F_A ≡ F_B ≡ the member
mod π^N …, **both lifts have disc ≠ 0 (distinct irreducible factors,
étale)**, and σ_A ≠ σ_B". Header: "*Proof (constructed lifts, **both
characteristics**, every q).*"

**Classification: CRITICAL** (a false step, for a nonempty case, in a
lemma graded PROVED and consumed as one of THEOREM W-12.C's two displayed
bounds). With B = 0:

* **Lift 1** is F_A = (x−c)³ + π^{2K+1}(x−c) = (x−c)·[(x−c)² + π^{2K+1}].
  In **equal characteristic 2** the quadratic factor is inseparable:
  disc(y² + c) = −4c = 0, i.e. y² + π^{2K+1} = (y + π^{(2K+1)/2})² over the
  algebraic closure. Hence disc F_A = 0 — F_A is NOT an étale lift, and the
  assigned σ_A = {(1,1),(2,1)} does not exist (the degree-2 piece is purely
  inseparable, e = 2 = p with the y¹ slot empty). Machine-visible
  structurally: F_A = y·(y²+π^{2K+1}) and F_A′ = y² + π^{2K+1} in char 2,
  so gcd(F_A, F_A′) = y² + π^{2K+1} ≠ 1.
* **Lift 2** is F_B = (x−c)³ + π^L with 3∤L. In **equal characteristic 3**
  F_B′ ≡ 0 (machine-checked this pass), disc(y³+c) = −27c² = 0, and
  F_B = (y + π^{L/3})³: disc F_B = 0, and σ_B = {(3,1)} does not exist
  (purely inseparable degree-3, e = 3 = p).

So in equal char 2 the "split-directed" witness dies, in equal char 3 the
"ramification-directed" witness dies — and both branches are needed
precisely for the one member per center with b₂ = 0 (the exact-cube
truncation), i.e. **q members of each row**. The affected rows are
squarely in the note's advertised scope: the twelve equal-characteristic
p ∈ {2,3} cubic census rows (Fqt 2,3–7; 4,2–3; 8,2; 3,2–4; 9,2), and
S2.4's table itself foregrounds these as the wild strata ("p = 3 / char 3",
"p = 2 / char 2"). Consequences, stated exactly:

1. LEMMA W12-S3.2 as displayed does not prove σ-ambiguity for those q
   members in equal char 2 or 3; the established bound there degrades to
   U₃^TRP ≥ q^N − q.
2. **THEOREM W-12.C's displayed bracket "q^N ≤ U₃^TRP(q,N)" is therefore
   not established over F_q[[t]] with p ∈ {2,3}**, nor is the HEX3 annex's
   inherited "q^N ≤ U₃^σ" there.
3. Everything else is untouched: the generic branch (b₂ ≠ 0 in-window,
   t ∈ [1,N−1]) is correct in every characteristic — I checked the
   separability that "distinct irreducible factors, étale" silently needs:
   char 2 Lift 1's quadratic has disc = B² ≠ 0; char 2 Lift 2 has
   F_B′ = y² with y ∤ F_B; char 3 Lift 2 has F_B′ = 2By with y ∤ F_B; and
   the e = 2 factor of Lift 2 is y²+ay+b with a = B + r ≠ 0 forced by the
   coefficient identities (b = ar, −br = π^L), so it is separable in char 2
   too.
4. **Why three passes and a GREEN battery missed it:** the ambiguity-witness
   leg (W12-ORACLE) builds F_A, F_B "exactly as above" **only on the Z_p
   oracle rows** (W12-BOX-6: "PARI legs are mixed-characteristic only"),
   and in mixed characteristic both B = 0 witnesses are fine
   (disc(y²+2^{2K+1}) = −4·2^{2K+1} ≠ 0; disc(y³+3^L) = −27·3^{2L} ≠ 0).
   The defect is invisible to the instrument by construction.

*Repair shape (one line, conclusion unchanged):* delete "chosen B = 0 when
b₂ = 0" and instead **lift b₂ = 0 to B = π^N** (any lift of valuation ≥ N),
setting t := N in the existing constraints (2K+1 ≥ 2t+2 = 2N+2; L ≥ 3N with
L − t odd). Then the member is handled by the generic branch verbatim:
F_A = y[y² + π^N y + π^{2K+1}] has three roots of valuations 0, N,
2K+1−N (σ_A = {(1,1)³}, disc ≠ 0 in every characteristic, quadratic
disc = π^{2N} ≠ 0 even in char 2); F_B = y³ + π^N y² + π^L keeps
σ_B = {(2,1),(1,1)} and is separable in char 2 (F′ = y², y ∤ F_B) and in
char 3 (F′ = 2π^N y, y ∤ F_B) — both verified this pass. The count q^{N−1}
free b₂ per center is unaffected (the witness choice is per member).

### FINDING 2 — JUSTIFICATION GAP: (A0)+(A1) never assert that core-family members are σ-DECIDED with forced σ = σ_F; THEOREM W-12.D's Step 4 lower bound uses both, and under the r3 pin (A0) degenerates to a tautology

**Quotes (S1, W-12.D).** "(A0) [lift well-posedness] every window-decided
member of a core family has ALL its disc ≠ 0 O-lifts of **the read's
type**;" — "(A1) … there is a FINITE list of core families F — each with **a
splitting type σ_F**, a parameter set … such that for every window N the
classes (F, x) with x visible … are PAIRWISE DISJOINT sets of window-N
polynomials, each of EXACT count dens_F(x)·q^{nN}" — Step 4: "Lower bound:
**the visible decided-τ classes** at window N are disjoint cylinder unions
**all of whose disc ≠ 0 lifts have type τ (A0)**: μ_τ ≥ D_τ(N)/q^{nN}",
with D_τ(N) := Σ_{σ_F = τ, x visible} count(F, x).

**Classification: JUSTIFICATION GAP** (hypothesis display of the note's
flagship PROVED clause; every instance the note actually fires satisfies the
missing strengthening, so no conclusion in the corpus moves). Two distinct
holes, both surfaced by the r3 pin:

* **(i) The label link is unstated.** (A1) attaches σ_F as *data*; nothing
  says the members of F have splitting type σ_F. The only candidate link is
  (A0)'s "the read's type" — but the r3 pin re-glossed exactly this phrase
  ("that σ is the read's output wherever the reader decides, and beyond the
  reader's window exit it is certified per stratum"), i.e. as the member's
  OWN forced σ. Read that way (A0) says "for every decided member, all
  disc ≠ 0 lifts have the σ they all have" — a tautology given
  decidedness — and the theorem is FALSE as literally stated. Counterexample
  (n = 2, any q): ONE family F = all window-N monic quadratics, d_F = 0,
  ℓ_F ≡ 0, ν_F ≡ 0, c_F = 1, σ_F := split. (A1) holds (single class, exact
  count q^{2N}, trivially disjoint, q-uniform); (A2) holds (r(N) ≡ 0);
  (A0) holds tautologously. Then R_split = 1 and R_inert = R_ram = 0, so
  Σ_τ R_τ = 1 ✓ but μ_split = q/(2(q+1)) ≠ 1 — the "it equals … the Haar
  splitting density μ_τ" clause fails. The intended reading ("the read's
  type" = σ_F) is recoverable from S2.3's instantiation ("the shape is
  σ-DECIDED with σ read off the shape alone, and (A0)-strongly (every
  disc ≠ 0 lift has **this** σ)"), which is why the proof is *morally* fine;
  the displayed hypothesis is not.
* **(ii) Decidedness of core members is assumed, not hypothesised.** Even
  under the σ_F reading, (A0) is conditioned on "every **window-decided**
  member", while Step 4 needs the conclusion for EVERY member of every
  visible core class (D_τ counts them all) and simply calls them "the
  visible decided-τ classes". An instance in which a positive-density part
  of a core family is σ-undecided satisfies (A0) vacuously there and breaks
  the lower bound; excluding it needs either (A1)-side decidedness or the
  vanishing of the undecided density — which is NOT among (A0)–(A2) (and at
  general n is exactly what W-12.B conjectures). Note the pin helps but does
  not close this: pinned-decided ⊇ reader-decided, so the pin *widens*
  (A0)'s reach (tail-certified members now count as decided) without making
  it total.

*Repair shape:* one clause — e.g. in (A1): "… each with a splitting type
σ_F such that EVERY member of every class (F, x) is σ-DECIDED (S1's pinned
sense) with forced σ = σ_F", after which (A0) becomes the (now redundant,
or retained-as-emphasis) well-posedness restatement and Step 4's lower
bound reads off directly. PE1's §2(1) "hidden-hypothesis hunt: negative"
covered Steps 1–3 and the Krasner/measurability side; this is the hole it
missed.

### FINDING 3 — JUSTIFICATION GAP: §S10 P-6's bonus observation still reads the conservative-measured U₃ sequence as corroborating W-12.B's q^{2N} order — false for that quantity by this note's own annexed THEOREM HEX3.A, and post-pin it is not W-12.B's quantity

**Quote (§S10, P-6).** "U₃^TRP recorded (EXPLORATORY, conservative
convention), bonus observation FROM the artifacts: the measured value is
IDENTICAL across Zp/Fqt at each of the NINE genuinely shared (q, N) pairs …
— characteristic-uniform raw data **consistent with W-12.B's q-uniformity**
(no law claimed; the q = 2 sequence 32/144/608/2720/11328 grows ≈ ×q² per
window step, **order q^{2N} as W-12.B predicts**)."

**Classification: JUSTIFICATION GAP** (a false inference; it is the note's
only empirical corroboration of W-12.B at n = 3, and it is fenced as
EXPLORATORY with "no law claimed", so no theorem depends on it). Two
independent reasons the closing clause does not hold:

1. **The measured quantity is Θ(N·q^{2N}), not Θ(q^{2N}).** By THEOREM
   HEX3.A — quoted verbatim in this note's own BOX-3 ANNEX —
   U₃^conv = q·u(q,N) with u carrying the R-tail family, so the normalized
   mass U₃^conv·q^{−2N} diverges linearly with mean slope
   (q−1)/(2q²(q+1)). W-12.B predicts undecided·q^{−2N} → c₃(q), i.e. no N
   factor. The committed numbers already show it: normalized, the q = 2
   sequence is 0.5000, 0.5625, 0.5938, 0.6641, 0.6914 — monotonically
   RISING, and each displayed ratio (4.50, 4.22, 4.47, 4.16) exceeds the
   "≈ ×q²" = 4 the sentence attributes to it. The excess IS the divergence,
   not noise.
2. **Post-pin the measured quantity is not W-12.B's.** After r3,
   undecided(3,q,N) is the lift-certification residue; the battery measures
   the conservative residue U₃^conv ⊇ U₃^σ. So even the *order* statement,
   if true, would corroborate a different quantity. Symmetrically the r3
   sweep classifies this very surface under "(c) disclosed-convention
   MEASUREMENT surfaces (the conservative reader named explicitly, **no
   σ-decidedness claim ridden**)" — accurate about σ-decidedness, but this
   surface rides a W-12.B *order* claim, which is the classification the
   sweep needed to catch. (Note what remains TRUE and valuable in the same
   sentence: the nine-shared-pair characteristic-uniformity, now explained
   by COROLLARY HEX3.C.)

*Repair shape:* one clause — "… characteristic-uniform raw data (explained
by COROLLARY HEX3.C); NOT a W-12.B corroboration: the conservative residue
is Θ(N·q^{2N}) by HEX3.A and is an upper count for the pinned σ-residue,
which this battery does not measure."

### MINOR 1 — W12-BOX-7, the box the r3 pin names as its authority, still assigns the rejected convention to the TRP side definitionally

**Quotes.** The pin (S1): "pinned [r3, PE3 F1: the σ-pin] to
**W12-BOX-7's LIFT-CERTIFICATION notion**". W12-BOX-7 (untouched by r3):
"Decided = certified on window digits for all disc ≠ 0 lifts; the DBL side
inherits W-11's proved convention (incl. its SPLIT-TAIL certification);
**the TRP side uses the BOX-3 conservative convention**. The two
conventions can disagree only on deep-tail TRP members".

**Classification: minor** (the pin names which clause of BOX-7 it takes, so
the intent is unambiguous; but the citation target still carries, as a
definitional sentence, the hybrid the r3 record rejects). Under the pin
there is exactly ONE definitional notion (lift certification) and the
conservative reader is a MEASUREMENT convention — which is how the r3
record itself re-reads the runner docstring ("its docstring discloses the
conservative convention as a MEASUREMENT convention, correct as sealed").
BOX-7's third clause says instead that the TRP *side* "uses" the
conservative convention, which for a TRP deep-tail member that IS
lift-certified asserts UNDECIDED (clause 3) and DECIDED (clause 1) at once.
*Repair shape:* one scope word — "the **battery's** TRP reader uses the
BOX-3 conservative convention (a measurement convention; the definitional
notion is clause 1 uniformly)".

### MINOR 2 — S2.3's parenthetical "in fact every lift" is false in equal characteristic at wild decided shapes

**Quote (S2.3).** "All the data the read consumes sit at heights ≤ N−1, so
every lift of the window class shares them: the shape is σ-DECIDED with σ
read off the shape alone, and (A0)-strongly (every disc ≠ 0 lift has this
σ — **in fact every lift**)."

**Classification: minor** (parenthetical over-claim; nothing consumes it —
(A0) and Step 4 quantify over disc ≠ 0 lifts only). Counter-instance in the
note's own family table: a TRP-RAM3(h) member with 3∤h whose b₁ and b₂
vanish in-window admits the lift F = y³ + b₀ with v(b₀) = h; in equal
characteristic 3 that lift is inseparable (F′ ≡ 0), so it has disc = 0 and
no σ at all. Same phenomenon at any wild side with e divisible by p and the
intermediate slots empty (LINRAM2 / RAM2LIN / QRT-G2 in char 2). The
correct claim is exactly the one used: every disc ≠ 0 lift has this σ.
(This is the same characteristic-blindness as FINDING 1 — "distinct
irreducible factors ⟹ étale" is a char-0 reflex; in char p an e = p side
can be purely inseparable. Two sites, one root cause.)

### Remarks (uncounted, no repair owed)

* **R-1 (the pin's degenerate corner — EMPTY, but unargued).** The pinned
  predicate quantifies over disc ≠ 0 lifts; if a member had none, "force ONE
  σ" would be FALSE while the retained head clause ("every O-lift with
  disc ≠ 0 has the read's σ") would be vacuously TRUE — the two would
  disagree. The corner is empty: disc of the generic monic degree-n
  polynomial is a nonzero polynomial in the coefficients (Π_{i<j}(x_i−x_j)²
  is nonzero over any field), the coefficient substitution a = f + π^N g is
  an invertible affine change, and a nonzero polynomial over the infinite
  ring O cannot vanish on O^n; so every window class has a disc ≠ 0 lift,
  in every characteristic. (Stronger at order-1 decided shapes: every lift
  factors into distinct SEPARABLE irreducibles — except in the wild
  equal-characteristic corner of MINOR 2 — which is also the mechanism
  behind the battery's "disc = 0 ⟹ never decided" leg.) One sentence would
  make the definition visibly total.
* **R-2 (the HEX3-r3 race — resolved, W-12's own leg unaffected, its cite
  now stale).** HEX3 r3 (b6a1d69) landed AFTER W-12 r3 (b17238a) and
  conditionalized §S8.2's W-12.B consistency clause. W-12's [r3] class-(a)
  entry describes that surface as an unconditional consumer of the pinned
  parse ("HEX3 §S8.2's downstream corroboration remark (it routes the
  N-linear conservative mass to (A2)'s boundary families — the pinned
  parse)") and vouches "all consistent" — i.e. it vouched, undated, for the
  clause HEX3's own PE4 verifier found to assert BOX-1's OPEN lemma as fact.
  At HEAD that clause reads "consistent with W-12.B IF this SPLIT-TAIL-type
  mass belongs to (A2)'s boundary-family (σ-certified) component", with the
  divergence price and a pin-robust route citing W-12 r3 by hash — so the
  two notes are now consistent, and W-12's own n = 3 (A2) leg never needed
  the split (S3.4's parenthetical "those are conv-UNDECIDED by
  construction, so no TRP tail leg is separately owed" is exactly the
  pin-robust argument, and I verified it: σ-undecided TRP ∪ tail-certified
  TRP ⊆ conv-undecided TRP ≤ N·q^{2N−1}). Only the cite is stale, in the
  safe direction.
* **R-3 (branchwise transport of the pinned notion — true, step not
  displayed).** LEMMA W12-S2.1's "f is σ-decided iff every f_i is" and
  W12-L1(c)'s "lift-σ-set(f) = lift-σ-set(g) ⊎ {(1,1)}" need, at the pin,
  that the disc ≠ 0 quantifier factorizes: disc(Π F_i) = Π disc(F_i)·Π
  res(F_i,F_j)² and the resultants are units (coprime reductions), so
  disc(Π F_i) ≠ 0 ⟺ every disc(F_i) ≠ 0. True and one line; not shown.
* **R-4 (P-7/S10 wording is reader-scoped, not σ-scoped).** "disc = 0 ⟹
  undecided" (P-7) and "0 disc-0-decided members" (§S10) are statements
  about the runner's verdicts; at the pin the same words would assert
  lift-ambiguity, which for the disc = 0 genres (ii)/(iii) is not proved
  (it is the TRP tail question). The note's genre analysis is explicitly
  reader-scoped ("In all three genres 'reader never decides' holds"), so
  this is a vocabulary-drift remark, not a finding.
* **R-5 (post-pin the note's n = 3 bracket is uninformative about c₃).**
  Under the pin, W-12.B's n = 3 quantity is U₃^σ with bracket
  q^N ≤ U₃^σ ≤ q·u(q,N): normalized by q^{−2N} the lower end → 0 and the
  upper end → ∞. So after r3 the note has no nontrivial evidence either way
  for c₃'s existence (pre-pin, the conv parse gave a determinate NO). That
  is honest given "GRADE: conjecture", and FINDING 3 is the one place the
  note says otherwise.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) The r3 σ-pin: coherence, totality, the degenerate corner, record
faithfulness, one divergence row re-derived.**

*Coherence/totality:* CLEAN, with R-1's one-sentence omission. The pinned
definiens is |{σ(F) : F an O-lift of f, disc F ≠ 0}| = 1 — decidable in
principle for each member, independent of any reader, and non-vacuous
because the lift set with disc ≠ 0 is always nonempty (R-1). The retained
head clause ("if every O-lift of f with disc ≠ 0 has the read's σ") differs
from the definiens exactly at members where the reader exits (where "the
read's σ" is undefined — PE3's point) and, vacuously, at the empty corner
(which does not occur); the pin's "pinned … to" makes the ⟺ clause
governing, and the [r3] record's explicit REJECTION of the read-anchored
parse removes residual ambiguity. The parenthetical "beyond the reader's
window exit it is certified per stratum — the DBL side by W-11's PROVED
SPLIT-TAIL leg" is coherent *scoped to decided members* (it says where a
decided tail member's σ comes from); read unscoped it would also cover the
DBL UNDECIDED stratum, where certification provably FAILS (W-11's q^{N−1}
per center) — worth a scope word but not a finding, since the sentence sits
inside the definition of σ-DECIDED.

*Record faithfulness:* CLEAN and slightly stronger than PE3. PE3 reported
"0.50 → 0.86 → 2.53 → 8.78, asymptotic slope 1/24" and "even THEOREM
W-12.C's displayed DBL constant would be wrong (the DBL SPLIT-TAIL mass
would inflate it)"; the [r3] record reproduces the table verbatim and
sharpens the second point to the exact inflation
⌊(N−1)/2⌋(q−1)²q^{2N−2} — which I verified is precisely the transported
SPLIT-TAIL mass (the members the rejected parse would call undecided).

*My own re-derivation (charge-mandated, one row = all four rows).* I
transcribed THEOREM HEX3.A from HEX3_PROOF §S2 (u(q,N) = q^{2N−2} +
(q−1)Σ_{k=1}^{⌊(N−1)/3⌋} q^{4k−1}(q^{N−3k}−1)R(N−3k), R(M) = q^{M−1} +
⌊(M−1)/2⌋(q−1)q^{M−2}, R(1) = 1), NOT from this note's annex. Results:
U₃^conv = q·u matches all 13 distinct committed U₃ values (23 rows:
(2,3..7) = 32/144/608/2720/11328, (3,2..4) = 27/243/2511, (5,2) = 125,
(4,2) = 64, (4,3) = 1024, (8,2) = 512, (9,2) = 729), 0 mismatches. The
normalized mass q·u·q^{−2N} at q = 2: **N = 3 → 0.5000, N = 10 → 0.8579,
N = 50 → 2.5333, N = 200 → 8.7833** — the record's 0.50/0.86/2.53/8.78 to
the digit. Slope: the per-step increment alternates 1/60 and 1/15 (the
⌊(M−1)/2⌋ parity), mean exactly 1/24 = (q−1)/(2q²(q+1)); average slope over
N = 200→400 and 1000→2000 equals 1/24 to machine precision, and the formula
(q−1)/(2q²(q+1)) reproduces the measured mean slope at q = 2, 3, 5, 7
(0.041667 / 0.027778 / 0.013333 / 0.007653). Also re-derived HEX3's
(2,7) k = 1 N-linear mass ⌊(N−4)/2⌋(q−1)²q^{2N−4}(1−q^{−(N−3)}) = 960 ✓.

**(2) Spot-audit of 8 swept surfaces (ledger: "~40 σ-surfaces classified,
NO consumer of the rejected parse").** Each audited by re-deriving what the
surface actually consumes, not by re-reading the sweep:

| # | surface | sweep class | audit verdict |
|---|---|---|---|
| 1 | THEOREM W-12.C's identity (DBL term exact) | (a) pinned | **CLEAN, verified at the supplier.** Under the pin the term must be the lift-ambiguous DBL count in BOTH directions. W-11 supplies both: SPLIT-TAIL is "σ = split certified" (so excluded), and the residue is "genuinely ambiguous … per MEMBER, split and inert lifts BOTH always exist (so σ-undecidedness itself is airtight member by member)" [W11 S2.4, r1 F6 text]. ⟹ q^{N−1}/center is exactly the pinned count; ×q^{N−1} fiber ×q(q−1) patterns = (q−1)q^{2N−1} ✓ |
| 2 | battery `dbl_undecided == (q−1)q^{2N−1}` | (a) pinned | **CLEAN, verified in the runner SOURCE** (not merely from the output): the DBL reader returns `('SPLIT-TAIL', (w,), H, ((1,1),)*3)` as a DECIDED key and `('UNDECIDED', (), H, None)` separately (w12_checks.py L346–347; predictor L594–595), i.e. certification-inclusive. Independent numeric confirmation: if SPLIT-TAIL were counted undecided the measured value would exceed the law by ⌊(N−1)/2⌋(q−1)²q^{2N−2} > 0 for N ≥ 3, and it does not |
| 3 | BOX-3 annex's bracket quantity U₃^σ | (a) pinned | **CLEAN**: the annex writes q^N ≤ U₃^σ ≤ q·u with U₃^conv = q·u exactly — the pinned quantity on the left, the measurement on the right; and q·u ≤ q^{3N−2} for all q ≥ 2, N ≥ 2, so it is a genuine sharpening of W-12.C's trivial upper bound. (Its LOWER end is the one FINDING 1 dents in equal char 2/3.) |
| 4 | LEMMA W12-S2.1 branchwise decidedness | (a) pinned | **CLEAN with R-3's undisplayed step**: at the pin, decided(f) ⟺ every branch decided requires disc(ΠF_i) ≠ 0 ⟺ ∀i disc(F_i) ≠ 0, which holds since the cross-resultants are units. The ⊎-product of singletons is a singleton ✓ |
| 5 | S2.3's decided shapes (Ore leaves) | (a) pinned | **CLEAN as the (A0) claim**; its parenthetical over-claims (MINOR 2) |
| 6 | S3.4's (A2) routing of the transported SPLIT-TAIL | (a) pinned | **CLEAN**: under the pin those members are σ-DECIDED split-certified, hence not in undecided(3,·), and being N-dependent they lie in no (A1) family — so (A2) is the only route, exactly as displayed; mass re-derived ⌊(N−1)/2⌋(q−1)²q^{2N−2} and cross-checked in my fresh instrument in two new rings (§4) |
| 7 | LEMMA W12-S3.2 + S3.3 lower bounds | (b) parse-robust | **Parse-robustness CLEAN** (both prove lift-DISAGREEMENT, valid under either notion) **but S3.2's proof is CRITICALLY defective in equal char 2/3 — FINDING 1**; S3.3 is clean and inherits only W-11's per-center law |
| 8 | U₃^TRP EXPLORATORY battery row | (c) measurement, "no claim ridden" | **NOT CLEAN as classified — FINDING 3**: §S10's P-6 text for this very row rides a W-12.B order claim |

The sweep's headline negative ("NO surface consumes the rejected
read-anchored parse") survives my audit: I found no surface whose validity
requires the reader to have printed σ. Its class-(c) rationale ("no
σ-decidedness claim ridden") is what fails, at one surface, in the weaker
form of a W-12.B corroboration claim (FINDING 3).

**(3) CONJECTURE W-12.B at general n, POST-pin: WELL-FORMED.** (a) The
pinned undecided(n,q,N) is a well-defined non-negative integer for each
(n, O, N) — R-1 gives totality of the predicate. (b) Ring dependence: for a
given prime power q the note's convention admits two rings (W(F_q) and
F_q[[t]]), so "undecided(n,q,N)" is a slight abuse; the conjecture's own
clause "independent of the characteristic" is exactly the hypothesis that
makes it well-posed (read: for each admitted ring the limit exists and is
the same c_n(q)). PE3's answer stands post-pin. (c) Uniqueness of c_n as an
element of ℚ(q): values at infinitely many prime powers determine a
rational function. (d) Positivity for the "equivalently" clause: S3.3
in-bullet gives c_n ≥ q^{−(n−1)}. (e) What the pin CHANGED: the quantity is
no longer the one the battery measures at n = 3, so the note's evidential
situation is R-5 (bracket → 0 below, → ∞ above) — well-formedness intact,
corroboration gone (FINDING 3).

**(4) W-12.D's (A0)/(A2) consumption at the pinned definition — Steps 3–4
re-derived; does any step secretly need the rejected parse? NO.**
Step 3 is definitional: Σ_τ D_τ(N) sums each family exactly once (every
family has a σ_F) and r(N) := q^{nN} − Σ_{F,x visible} count(F,x) closes the
identity; divide, take N → ∞ (finitely many τ, each net convergent by
Step 2), apply (A2) — **no σ-notion enters at all**, so Step 3 is
parse-invariant. Step 4: measurability/openness (Krasner) and disc = 0
being null are classical and displayed; the lower bound consumes (A0) (and
the two unstated strengthenings — FINDING 2); the upper bound's two-case
truncation consumes (A0) applied to F itself, which under the pin is
*better* behaved than under the rejected parse (pinned-decided ⊇
reader-decided, so the pin enlarges the set of members (A0) speaks about).
The n = 2 instance-check is parse-invariant where it matters: r(N) =
q^N + q⌊(N−1)/2⌋(q−1)q^{N−2} is a count of the complement of the six core
families (a combinatorial identity in W-11's classification), and the four
series re-summed this pass give R_split = R_inert = q/(2(q+1)),
R_ram = 1/(q+1), Σ = 1 ✓. **Conclusion: no step needs the rejected parse;
the parse-sensitive item is a hypothesis, not a step — FINDING 2.**

**(5) The HEX3 r3 race — RESOLVED, see R-2.** Timeline verified in git:
W-12 r3 b17238a (17:19:10Z) → HEX3 passPE4 report 34a946b (17:43) →
adjudication b8dfe62 (17:45:13) → HEX3 r3 b6a1d69 (after). HEX3 §S8.2 at
HEAD is conditionalized, cites W-12's pin by hash (b17238a), displays the
same divergence price (all-k slope (q−1)/(2q²(q+1)) = 1/24 at q = 2, under
S5.3's excess bound 1/(2q(q+1))) — arithmetic I independently reproduced
(§2(1)) — and states the pin-robust route (U₃^conv = σ-undecided TRP ∪
certified boundary tails, exactly). W-12's own record is stale only in
having vouched, undated, for the pre-r3 wording.

**(6) The chosen unmined detail: LEMMA W12-S3.2's constructed lift pair,
characteristic by characteristic.** This is FINDING 1 (equal char 2/3
inseparability at b₂ = 0) plus the positive half: in the generic branch
(b₂ ≠ 0 in-window) both lifts are separable in EVERY characteristic, which
required checking what "distinct irreducible factors, étale" does not
supply — the e = 2 factor of Lift 2 is y² + ay + b with a = B + r, and the
coefficient identities of F_B = (y²+ay+b)(y−r) (namely b = ar,
−br = π^L, a − r = B) force a ≠ 0, hence disc = a² ≠ 0 even in char 2; the
polygon of that quadratic is one side of slope (L−t)/2 with odd numerator,
so e = 2 and irreducible ✓; and the assigned σ_A, σ_B are then correct.
Prior passes covered S3.2's counting (PE1) and its parse-robustness (r3's
sweep); no pass had checked its separability, which is where it breaks.

*Also re-derived while here (no findings):* the seven S2.4 families
end-to-end from the digit calculus (heights, L = Σ_S g_S per side-degree
bookkeeping, vertex conditions 2u₀ > 3u₁ / u₀ > 3k / u₀ > 3t), S2.5's
quartic heights (2h, (3h+1)/2, h, (h+1)/2) summing 5h+1 with L = 2 ⟹
B = 4N−5h−3, S2.2's in-window claim (P(j) ≤ P(0) ≤ N−1 so every priced slot
is visible and N − ⌈P(j)⌉ ≥ 1), and the census-sweep identity S_T = Π_S
S_{λ_S}(q^d) with exactly L priced slots.

---

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  **7dc040d94fbbb1e8d20ac817b665d418** == `git show
  f669cb0:verification/openmath/w12_checks.py | md5sum` — byte-identical to
  the seal; committed artifacts at HEAD carry §S10's md5s (0557b15f… /
  05776c9e…).
* **Fresh full re-run (single run, this pass):** exit 0, **3,232,506 checks
  / 0 violations**, teeth **W12-T-SHAPE 23 / T-DRAIN 23 / T-CENSUS4 8 /
  T-SIGMA 1273**, zero skips, 346.1 s, verdict GREEN. Every §S10 family
  count reproduced EXACTLY: PIN 5, LVL0 138, SHAPE 164, QRT 27, L0HIST 306,
  BLOCK 1,594,670, L1X 1,594,090, DRAIN3 1,183, ORACLE 41,923 (sum
  3,232,506).
* **Artifacts:** fresh JSON content-identical to the committed one after
  stripping timing (programmatic compare == True); `w12_checks_output.txt`
  diff = 46 lines, all per-row elapsed times. Committed bytes RESTORED and
  md5s re-verified (0557b15fb08a6e6eb40bd2db7e62206b /
  05776c9e00071c5d7524abdfbe894442). No other file in
  `verification/openmath/` touched by this pass.

## 4. FRESH ROUTE — W-12's law suite in TWO ring types the arc has never run it in

`/tmp/w12_pe4b_fresh.py`, written from scratch this pass (own residue-field
tables with λ-labels distinguishing (1²) from (2) and (1³) from (3); own
lower-hull code; own depth-0 TRP classifier; own recursive conservative TRP
reader; own n = 2 block reader with refinement histories; own quartic
one-side classifier; no import of any repo runner). **Disclosed own-bug,
found and fixed before scoring:** my first λ encoding collapsed
multiplicity onto degree ((1²)≡(2), (1³)≡(3)), which made refine cases read
as decided — caught by the S2.4 laws and by HEX3.A, both of which then went
exact; and my quartic driver initially compared per-center counts against
whole-space predictions (factor q).

**Rings (both OUTSIDE the note's S1 convention pair {absolutely unramified
mixed char with v(p) = 1, F_q[[t]]}):**

* **E2 = ℤ₂[π]/(π²−2)** — RAMIFIED mixed characteristic, v(2) = 2, residue
  F₂. The note's laws are stated for its two pinned ring types; this row
  tests whether the digit calculus is genuinely ring-agnostic where even
  v(p) moves.
* **W4 = W(F₄) = ℤ₂[ω]/(ω²+ω+1)** — unramified mixed characteristic with
  **PRIME-POWER residue field q = 4**: exactly the gap W12-BOX-6 discloses
  ("no mixed-characteristic prime-power rows exist in the frozen kit") and
  that §S10 P-6's [r1 m2] scoping had to fence ("those are Fqt-ONLY rows …
  single-kind raw data, NOT cross-checked pairs").

**Results — 0 mismatches everywhere, and pointwise EQUAL to the committed
JSON at every shared (q,N):**

| ring | (q,N) | S2.4 depth-0 keys | U₃^conv | DBL term | committed row |
|---|---|---|---|---|---|
| E2 | (2,3) | 3 keys, all exact | 32 | 32 | == (Zp,2,3) / (Fqt,2,3) |
| E2 | (2,4) | 6 keys, all exact | 144 | 128 | == (Zp,2,4) |
| E2 | (2,5) | 10 keys, all exact | 608 | 512 | == (Zp,2,5) |
| W4 | (4,2) | 1 key, exact | 64 | 192 | == (Fqt,4,2) |
| W4 | (4,3) | 3 keys, all exact | 1024 | 3072 | == (Fqt,4,3) |

Detail (whole-space, = per-center × q): E2 (2,5) reproduces the committed
ten-key dictionary EXACTLY — FULL(1,'12') 128, FULL(1,'3') 256,
LINRAM2(2,1) 1024, (3,1) 512, (4,1) 256, RAM2LIN(4,1) 64, RAM3(1) 4096,
RAM3(2) 1024, RAM3(4) 64, VERT1(4,1,'2') 64 — plus deep-decided 96 and
species 32, all matching. W4 (4,3) reproduces LINRAM2(2,1) 2304,
RAM3(1) 12288, RAM3(2) 768, dbl_undecided 3072, species 64, U₃ 1024 —
**the first time a mixed-characteristic prime-power-q row has been put
against the note's prime-power Fqt rows**, which upgrades P-6's
"nine genuinely shared (q,N) pairs" to eleven in my own instrument (q = 4
at N = 2, 3 now cross-characteristic-checked, both equal).

Also exact in both rings: **W12-L0's history-resolved n = 2 laws** (every
(kind, params, history) key against (q−1)^t × the one-node closed form —
5/8/15 keys at E2 N=3/4/5, 2/6 keys at W4 N=2/3, 0 mismatches);
**W-11's drainage** q^{N−1} undecided blocks per center; **W12-L1(c)/
W-12.C's DBL σ-undecided term** (q−1)q^{2N−1}; the **transported SPLIT-TAIL
per-w aggregate** (q−1)²q^{2N−2} with w-range 1..⌊(N−1)/2⌋ and total
⌊(N−1)/2⌋(q−1)²q^{2N−2}; **S2.5's QRT-G2 laws** including the (1²)
composite-frontier volume (E2 (2,3)/(2,4): 16/16 and 256/256 per center;
W4 (4,3): '11' 768, '2' 1536, '1sq' 768 = S_λ(4)·4⁴ with S_{(1,1)}(4) = 3,
S_{(2)}(4) = 6, S_{(1²)}(4) = 3); and the **S3.2 species locus** (q^{N−1}
members per center, all reader-undecided). **THEOREM HEX3.A holds verbatim
in both rings**, including in the v(2) = 2 ring — evidence that the law is
insensitive not just to the characteristic but to the absolute ramification
(consistent with HEX3.A's own "independent … of which DVR realizes F_q").

Independent machine leg for FINDING 1: over F₃[t], F_B = y³ + t⁷ has
F_B′ ≡ 0 (inseparable, disc = 0); over F₂[t], F_A = y³ + t⁵y = y(y²+t⁵)
with F_A′ = y²+t⁵, so gcd(F_A, F_A′) = y²+t⁵ ≠ 1 (inseparable); the
repaired witnesses (B = π^N) have gcd = 1 in both characteristics.

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 1C+3G+2m (2b47711) → r1 (ba0d1a4) + BOX-3 annex
(8e535d2) → PE2 0C+3G+2m (1be15d2) → r2 + BOX-2 annex (99f1813) → PE3
0C+1G+1m (c9c5c0e) → r3 σ-pin (b17238a) → **PE4 (this pass): NOT CLEAN —
1 CRITICAL + 2 JUSTIFICATION GAPS + 2 minor; counter stays 0/2; r4 owed.**
The CRITICAL is a one-line witness change (S3.2's B = 0 branch) that leaves
the lemma's conclusion and every downstream count intact; the two gaps are
one-clause hypothesis/scope repairs ((A1)'s decidedness+label clause;
§S10 P-6's corroboration sentence); the minors are a scope word in BOX-7
and a parenthetical in S2.3. No annex is touched by any of them, and the
machine and fresh legs are arc facts for the record: seal intact, battery
GREEN and reproducible a FOURTH time at identical counts, and the note's
law suite now confirmed in two DVR types outside its own stated
convention — including the mixed-characteristic prime-power row its own
BOX-6 says does not exist anywhere in the kit.

— passPE4 verifier, fresh context, 2026-08-08.
