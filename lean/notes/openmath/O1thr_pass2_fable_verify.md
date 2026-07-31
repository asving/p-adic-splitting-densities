# Pass-2 hostile verification of O1thr_phaseB_verifybrief_rev2.md

*Verifier: Claude Fable 5, fresh context, model-diverse pass 2. Input: ONLY the brief
(`O1thr_phaseB_verifybrief_rev2.md`). Charge: quote each suspect passage; classify
CRITICAL ERROR vs JUSTIFICATION GAP; fix nothing. The pass-1 report was not seen.*

## Verdict

**SOUND-WITH-GAPS.** Theorem 1 (lawful-site locality) is verified sound as stated,
for the machine as defined, for every policy and every box-free AUX — and its proof
inspects no runs. Lemmas DEV/POS/R-LOC/NAT/CEIL are verified. The SPAN ledger, the
Case-2 deep-child contradiction, and Theorem 3's cylinder/scaling/disjointness
arguments are verified as arguments — but they rest on harvest-interface content
that the brief tags as *definitional* ((M6a)) while it is in fact substantive
(the OM principal-part-length fact), so the headline claim that (M6b) is the
package's SINGLE substantive interface assumption is not sustained. No ∀-claim is
settled by examples; the Eisenstein family is excluded by the stated hypotheses at
every theorem. Six findings below; the first is the package's main defect.

## Positive verifications (what was checked and held)

1. **Theorem 1 does not inspect runs.** Clause-by-clause: keys and valuations come
   from records + policy ((M4)); (†) arithmetic verified (⌈I_i/E_i⌉ ≤ L−1 ⟹
   I_i ≤ (L−1)E_i < L·E_i); the B_j = 0 vs B′_j ≠ 0 edge cases of (R1) verified,
   including forbidden-equality slots with ℓ_i(j) < 0 (vacuous both sides by POS);
   (R2) nonzero-transfer verified; (†′) is genuinely rederived (DEV/POS apply to
   the monic Φ_{i+1} with heights in w_i) and uses only (N4)'s upper bound. The
   lawful-site quantifier is honored: nothing presupposes realization.
2. **Lemma NAT.** γ ≥ (s0+wSide)·h ≥ wSide ≥ e (h ≥ 1, e ∣ wSide, wSide ≥ 1)
   gives I ≥ 1, L(H) ≥ 2. Verified; (N3) is exactly what makes p^L well-formed.
3. **Lemma CEIL.** (R1)/(R2) heights ≤ I_i since h > 0, j ≥ 0; ℓ < 0 vacuous by
   POS; (R5) height = vhtx ≤ I by (N4). Complete relative to (M1). Verified.
4. **Lemmas DEV/POS/R-LOC.** Division by a monic over ℤ_p commutes with mod-p^L
   reduction; the POS induction (γ_{i+1} ≥ 1 since w_i(Φ_{i+1}) ≥ 0, h_i ≥ 1;
   E_{i+1} = e_iE_i uniform in j) verified; R-LOC is definitional. Verified.
5. **SPAN ledger arithmetic.** Σ_ψ g_ψμ_ψ = deg R = wSide/e (pat(0) ≠ 0,
   pat(wSide/e) ≠ 0 by (N1)); wt(child) = degΦ_o·e·g·μ; per-face and all-faces
   sums; L-SAT via the key-degree identity (accE·accF = Dwidth ⟹ μ = 1 at
   saturation); the subtree induction and BOTH equality-forcing routes ((F6)
   per-track; (F3)+(F5)+(∗∗) global). Verified GIVEN the roster identification
   (Finding 1). SPAN(ii)'s pin bound I ≤ (L−1)E_o ≤ (t−1)E_o verified.
6. **Theorem 2(b) Case 2.** DEV+POS transport of the slot-0 pin (N·E_o > β_0),
   B′_0 ≠ 0 forced, ℓ′(0) ≤ β_0 ≤ (t−1)E_o, ⌈I(ν′)/E_o⌉ ≤ t−1, thr majorizes
   o's own reads, hence L(o·ν′) ≤ t ≤ N contradicting deepness. Verified,
   including the empty-history root case (L = 1 + ⌈I(ν′)/E_0⌉ ≤ t).
7. **Theorem 3.** (a)'s six clause transfers verified; the (F1)-backward walk is
   sound (the longest-prefix state o is automatically non-saturated because K is
   PRUNED — a halted proper prefix is excluded — so 2(b)'s "root state or interior
   chain" scope suffices); (b)'s p^{n(N−t)}-to-1 count and the cross-level
   instance (M = N, M′ = t, agreement level t) verified against (a)'s exact
   hypotheses; (c)'s uniqueness ((F1)/(F2)/(F3) determine T) and the
   at-most-p^{nN} finiteness at the common level verified. Modulo Finding 4.
8. **Eisenstein guard, by the stated hypotheses.** f_N = X^n + p^N has root-site
   intercept I = N, so L = N+1 and any tree recording the site has thr ≥ N+1.
   Theorem 1's hypothesis (agreement below L = N+1) fails for the pair
   (f_N, X^n) (they agree only below N). Theorem 2(b)/3 require fiber(T, x) with
   T decided ns-free: the zero box's run ns-halts (window polygon of X^n has a
   single finite point, no principal face), so it fibers nothing; f_N's own tree
   has thr ≥ N+1 > N, so the N-level comparison hypothesis N ≥ thr fails. The
   exclusion is by displayed hypotheses, not intent. Sharpness honestly reported
   (T-B: 112/115, the 3 exceptions disclosed).
9. **(N4)/(R5) consumer consistency.** Consumers of the recorded vertex height:
   Lemma CEIL, Theorem 1's (†′), (M6a)'s slot-μ read, (M6b)(ii), T-E's band
   check, §8 S-4. All consume β* ≤ vhtx ≤ I with only the UPPER bound doing
   work, as announced; no surviving consumer of the refuted vhtx = β* reading.
   The T-E countermodel arithmetic checks: f = X³ + 10X², face (2,1)–(3,0),
   γ = 3, I = 3, β* = 0, C_1 = f′(−2) = −28, w_0 = 2 ∈ [0, 3], ≠ β*.
10. **No ∀-by-examples.** Theorems 1–3 are argued generally; (M6b) is openly an
    ASSUMPTION with depth-1 corroboration, correctly not claimed proved. (But
    see Finding 1: a second substantive assumption is smuggled in as definition.)

## Findings

### Finding 1 — JUSTIFICATION GAP (load-bearing; the package's main defect):
**(M6a)'s [Definition of harvesting] tag covers substantive, f-dependent content
that (M6b) does not supply.**

Quotes (§2.4):
> "(M6a) Harvest, definitional half: at a realized non-saturated state, every
> (principal face, irreducible residual factor) pair yields a harvested node
> whose READ data are read off f by construction — (R1)/(R2) record f's own side
> data and digits, …"
> "… every realized child arises from a (face, ψ) pair. [Definition of harvesting.]"

READ's (R1) (§1.3) quantifies over EVERY slot j of the full Φ_i-adic development
("for every j with B^{(i)}_j ≠ 0"), but the window at a non-root state has width
μ_ν (§1.4) and harvesting inspects only the window polygon. At a non-root state
the development has slots beyond μ (e.g. n = 4, a depth-1 face with e = g = 1,
μ = 2: the successor development has 4 slots). Hence:

* (i) That a harvested child satisfies (R1) at slots BEYOND the window is not
  "by construction" — it is the OM principal-part-length theorem (the negative-
  slope part of the level-(i+1) polygon has length exactly ord_ψ(R_i)), nowhere
  stated in the brief and not contained in (M6b) (whose clauses are: vertex
  nonzero, (N4) band, AUX — and AUX is record-only, so it cannot express an
  f-dependent support condition).
* (ii) The converse ("every realized child arises from a (face, ψ) pair" — the
  no-phantom direction) is equally substantive under the brief's own §1.3
  definition of realization (READ ∧ LAWFUL): excluding a READ-realized side
  with slots beyond the window needs the same missing theorem (or an AUX
  window-fit clause s0 + wSide ≤ W, which the theorems, quantified over EVERY
  AUX, may not assume).

Where it bites: Lemma SPAN's roster totality ("a candidate is READ-realized in
full by (M6a)+(M6b)") and its ≤-direction (span ≤ W_o needs no-phantom);
Theorem 2(b) Case 1 (a realized child must satisfy FULL READ before Theorem 1
can transfer it); Theorem 3(a) (F1)-forward/backward and (F4)'s ¬NsHalts
witness. Assuming the missing coherence (true for genuine OM machines), all
downstream steps verify — hence GAP, not critical. But the headline claims

> "proved modulo exactly ONE substantive interface assumption, (M6b)" (§0)
> "(M6b) Harvest, substantive half — THE package's single substantive interface
> assumption" (§2.4)

are thereby MISSTATEMENTS: the package has (at least) a second substantive
interface assumption, currently hidden under a definitional tag. Note also that
the §9 falsifier is structurally blind to this content: at depth 1 the root
window is global ("root window = the full Newton polygon of f w.r.t. X"), so no
depth-1 test can probe beyond-window slots; T-E checks only the vertex clause.

### Finding 2 — JUSTIFICATION GAP: the §1.3 Note's "exactly" is unproved, and
"realized" equivocates between two inequivalent notions.

Quote (§1.3):
> "Note this includes realization of all PREFIX reads … and it witnesses
> non-halting of every proper prefix (each has a realized child, namely the next
> node), so site-reading is exactly membership of H·ν in the pruned run set."

The forward inclusion (READ ∧ LAWFUL ⟹ membership in the machine's pruned run
set) is asserted, not proved. Saturation halting is record-only ("the machine
has NO children at saturated states, by definition", §1.4), yet nothing in
READ ∧ LAWFUL prevents a READ-realizable extension of a saturated state (window
width 1 admits a face (0, β)–(1, β′)) unless AUX forbids it — and the theorems
quantify over every AUX. The "witnesses non-halting" clause covers ns-halts
only, not saturation halts. Downstream, "realized" is used sometimes as
READ ∧ LAWFUL (Theorem 1 transfers exactly this) and sometimes as
machine-execution/harvest (2(b)'s "(if o is saturated there are none, on either
side, by (M6a))"; Case 1's "realized children are harvested"). Each individual
use is repairable under one consistent reading plus Finding 1's coherence
bridge; as written the two notions are silently identified.

### Finding 3 — JUSTIFICATION GAP (conditionality-ledger inconsistency):
Theorem 2(a)'s unconditional status conflicts with its own hypothesis.

Quotes:
> "Theorem 2(a) … Let x be a box on whose decode the canonical run realizes the
> site (H, ν) … *Proof.* Immediate restriction of Theorem 1's quantifier to
> realized sites. ∎" (§5)
> "Proved outright … for every policy and every box-free AUX completion …
> Theorem 2(a)." (§8)
> "Consequently (induction along runs from the root) every realized pruned run
> is LAWFUL — used silently wherever Theorem 1 is applied to realized chains or
> children." (§2.4, inside (M6b))

Theorem 1 requires LAWFUL(H·ν). If "the canonical run realizes the site" means
execution-realization, lawfulness of the site is precisely the (M6b)-derived
consequence quoted above — so 2(a) is (M6b)-conditional, contradicting §8. If
it means §1.3's site-reading (READ ∧ LAWFUL), 2(a) is an unconditional but
tautological restriction, and the word "canonical" is dangling: "the canonical
run" / "canonical tree" (§0) are never defined, while seam S-3 disclaims
canonicity ("used NOWHERE in this brief"). One of the two readings must be
declared; as written the honesty ledger's row for 2(a) is not right.

### Finding 4 — JUSTIFICATION GAP: Theorem 3(c)'s σ-count formula uses an
undefined term and an unproven exhaustion.

Quote (§6):
> "so per splitting type σ the decided-σ count at level N is
> Σ_{T : typemult = σ, thr(T) ≤ N} mass(T)·p^{nN}."

"Decided-σ count at level N" (and "typemult") is defined nowhere in the brief.
For any reasonable reading (level-N boxes whose canonical tree is decided
ns-free with type σ), the formula additionally needs: every such box fibers a
tree with thr(T) ≤ N — i.e. no level-N box fibers a decided ns-free tree whose
threshold exceeds N. That is plausible (a level-N decode has no digits at or
above N to pin) but is neither stated nor proved; a box fibering a thr > N tree
would be counted by the left side and missed by the sum. Disjointness and
finiteness themselves are verified (item 7 above); only the displayed count
formula outruns what is proved.

### Finding 5 — JUSTIFICATION GAP (minor): the root window's face confinement
is used but not stated.

Quote (§1.4): "at a root state of a track with reduction factor φ̄^m (m ≥ 2 …
m = window width), the development of f in Φ_0 over slots 0..m-and-beyond with
the side constraint global over all slots".

(W-ADD) needs the recorded faces' spans to lie in [0, W_o] ("Σ over ALL
recorded children of wt = deg Φ_o · (total recorded span) ≤ wt(o)"). At a root
state the harvest polygon is global, so this needs: no principal face extends
past slot m. True — ord_{φ̄}(f̄) = m exactly gives w_0(B_m) = 0, and principal
faces cannot pass a height-0 point — but the brief neither states this fact nor
the "0..m-and-beyond" convention precisely enough to make span ≤ m displayed.

### Finding 6 — editorial (no classification): garbled sentence in Theorem 3(a).

Quote (§6): "any two level-N boxes in one level-t cylinder agree below t ≥ ...
apply the equivalence with N replaced by t (hypothesis N ≥ t ≥ t holds; …)".
The "t ≥ ..." fragment is broken text. The intended instantiation (statement's
N := t, M = M′ = N) is recoverable and correct.

### Minor notes (no classification)
* §0's modulus gloss "1 + the largest de-normalized side-line intercept" omits
  the ceiling function present in §3's L(H) = 1 + max⌈I_i/E_i⌉.
* Integer-valuedness of w_i on nonzero integral polynomials is cited "(§1.1)"
  at (N2) but never proved there (easy induction; motivational use only).
* P_β^+ (§2.3), "irrVerdict", "IrrHalts/NsHalts" (§6) are used without display;
  all are decodable from context, but a self-contained brief should define them.

## Charge-item summary

* **Read-machine totality/consistency:** total (READ is false rather than
  undefined at out-of-range records; μ-slot existence not needed for totality);
  the one genuine internal inconsistency is the realized-vs-site-read
  equivocation (Finding 2) plus the harvest/READ window mismatch (Finding 1).
* **Locality proof run-inspection:** none found (item 1).
* **SPAN ledger:** arithmetic verified; rests on Finding 1's roster bridge.
* **Cylinder exactness/scaling/disjointness:** verified; the σ-count formula is
  the only overreach (Finding 4).
* **(N4)/(R5) consistency across consumers:** verified (item 9).
* **Eisenstein guards by stated hypotheses:** verified (item 8).
* **∀-by-examples:** none; but the single-assumption headline is falsified by
  Finding 1's hidden second assumption.

**Verdict: SOUND-WITH-GAPS** — Theorem 1 and its lemma layer stand as proved;
Theorems 2(b)/3 stand modulo (M6b) PLUS the unstated harvest-coherence content
of Finding 1, and the conditionality ledger (§0/§2.4/§8) must be amended to say
so.
