# GRTW2 passPE2 report — hostile pass 2 on `GRTW2_PROOF_2026-08-08.md` (post-r1; the first acceptance attempt of the arc)

**Verifier:** Fable hostile pass PE2, fresh context, wallclock 2026-08-07.
**Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` at HEAD (last note
commit 8d5e3fa = the r1 repair round; working tree byte-clean). **Inputs read:**
the PE1 report (083adff), the full r1 diff (5463f2a → 8d5e3fa, note-only
+291/−25), the accepted [JB]/[JC]/WM/LIFTCORNER surfaces at their pins, the GMN
print `docs/references/HigherNewton.tex` at the cited tex anchors, the sealed
runner + committed artifacts. I fixed nothing.

## VERDICT

**0 CRITICAL ERRORS. 2 JUSTIFICATION GAPS (P1 moderate, P2 minor). 1 minor
precision defect (P3). NOT CLEAN — the counter stays 0/2** (this pass neither
starts nor advances the 2-clean count). The r1 re-scope is honest in intent
and its census is exactly right (independently recomputed, §A.4); the
four-route derivability adjudication HOLDS at source, and a deliberate
fifth-route hunt in the print found no supplier (§A.1). The machine leg
reproduces byte-for-byte (§B). The fresh leg confirms the (ξ,w) closed form by
an unused route: formula → committed ledger via from-scratch arithmetic, 16/16
at m = 1, plus full hand re-derivations at T3B/T3F r = 4 (§C). The two gaps:
the re-scoped grade's own boundary rides an unproven identification (P1), and
the [r1, F6] sign "fix" is unfaithful to the named print definition (P2).

---

## P1 — JUSTIFICATION GAP (moderate). The re-scope's warrant and W2-OPEN-2's premise both rest on the unproven identification "first recorded ξ ≠ 1 junction = first byte-divergence".

Quotes. §5.2 [r1, F1] block: "*junctions below r₀ recorded ξ = 1, so no
conjugation fired and **every key below r₀ is byte-equal to the harness key**;
the criterion AT r₀ is therefore evaluated over byte-shared lower keys and
clauses 1–2 apply*". W2-OPEN-2 premise: "*The chamber's keys φ_q^tw are
byte-equal to the harness keys Φ_q for q < r₀ and byte-DIFFERENT for
r₀ ≤ q < r*". Grade cap: "PROVED at attempt grade given clauses 1–2 UP TO AND
INCLUDING the first ξ ≠ 1 junction of each transported chamber".

The defect. "No conjugation fired" is definitional; but *raw print keys
byte-equal to harness keys below r₀* does NOT follow from "recorded ξ = 1
below r₀" by anything displayed. One direction is easy (recorded ξ ≠ 1 ⟹
byte-RED). The needed converse — recorded (ξ, w) trivial-ξ at a junction ⟹
the junction is byte-equal — is: (i) PROVABLE at m = 1 (I re-derived it: the
orbit equation at j = 0 forces w = 1, then z₁^{−A₁e₁j} = 1 on supp incl. the
top forces the §3.4-rk-3 byte condition c·z₁^{A₁e₁j} = 1 on supp ∩ [0, g₀));
(ii) OPEN at m ≥ 2 — the recorded pair sees only the top-layer reads while
the byte-law (§3.4 rk. 3) quantifies over EVERY node value of the recursion
tree, and a read-invisible byte divergence (a deeper node character invisible
on a sparse support — exactly the invisible-twist genre the note itself
exhibits at I4B) would give a byte-RED, recorded-ξ = 1 junction. In such a
chamber the transport never fires, no cure exists, and every junction between
the divergence and r₀ sits inside the note's "proved" scope with clauses 1–2
inapplicable. The failure would surface as a class-pin chamber, not on this
roster: I recomputed the equivalence from the committed JSON — **on all 22
walked junctions, recorded ξ ≠ 1 ⟺ byte-RED (0 exceptions), and every
junction below every chamber's r₀ is byte-GREEN** — so the 38/44 census and
all machine claims stand as instance evidence; only the GENERAL warrant is
gapped. Blast radius: the same identification is baked into W2-OPEN-2's
premise, so the box as stated does not cover the (hypothetical) invisible-
divergence chambers — "exactly what the live region needs" holds modulo this
identification. Repair: display the identification as its own scoped lemma
(m = 1 proved; machine 22/22; open at m ≥ 2 — one honest sentence in the
[r1, F1] block and one in the box premise), or re-key the proved-scope
boundary to "first byte-divergent junction" (coincides with r₀ on the roster).

## P2 — JUSTIFICATION GAP (minor; inside the review-owed §4.3 fence). The [r1, F6] sign repair is unfaithful to the print definition it names; the r0 sign was correct under tex 1431.

Quote (§4.3 at HEAD): "changes Def-`t(i)` by ~~t ↦ t − k·u_i~~ [r1, F6]
t ↦ t + k·u_i (direct computation: t(i) = (ℓu_i − s_i)/e_{r−2} with
s_i = ℓV mod e ℓ-shift-invariant — the r0 sign was flipped. The rescaling
display below and the 'T2A: h = 1, k = 2' instance are as-written correct
under k ↦ −k …)".

The defect. The print's literal Def-`t(i)` (tex 1431) is
t_{r−1}(a)_i = **(s_{r−1}(a) − ℓ_{r−1}·v_r(a·φ_r^i))/e_{r−1}** — the
(s − ℓu)/e arrangement, with u_i := v_r(a_iφ_r^i) the polygon ordinate (tex
1373) and s_{r−1}(a) the attained initial abscissa (ℓ-independent). Under
this definition ℓ ↦ ℓ + k·e gives **t ↦ t − k·u_i — the r0 sign** — and the
downstream rescaling display c_i ↦ z_{r−2}^{−k(u₀ − jh_{r−1})}·c_i (unchanged
since r0) is DIRECTLY consistent with it through Def-`rescoeff` (tex 1447,
c_i = z^{t(i)}·R(a_i)), with no k ↦ −k gloss needed. The bracket's premise
formula "(ℓu_i − s_i)/e" is a DIFFERENT print object — the Prop-`construct`
child twist exponent (tex 1201: y^{(ℓ_{r−2}u_j−𝔰_j)/e_{r−2}}), whose 𝔰 is the
ideal on-line initial abscissa, near-negative of Def-t(i). Root cause is an
r0 defect PE1 did not flag: W2-L2's parenthetical names its T = (ℓu − 𝔰)/e
"the print's Def-`t(i)`/Prop-`construct` twist exponent", conflating the two
opposite-signed exponents; PE1's F6 computed with the conflated alias and r1
implemented that wrong finding, so the repair made §4.3 worse against the
named source (a false "direct computation" attribution + a false "the r0 sign
was flipped" historical claim + a spurious reinterpretation of a display that
was already consistent). Mitigations, which cap this at minor: the section is
fenced CONVENTION ANALYSIS review-owed; the conclusions (orbit = ⟨z_m^{h_m}⟩
with coupled w; reachability iff gcd(h_m, ord z_m) divides the ξ-exponent)
quantify over all k ∈ ℤ and are sign-invariant under either convention (both
r0 and r1 say this, correctly); nothing downstream consumes the orbit
reading; W2-L2's actual identity is machine-keyed (CK-MM 4,396) and correct —
only its NAMING parenthetical is off. Repair: restore the r0 sign with tex
1431's formula displayed; split the W2-L2 parenthetical into its two print
referents (construct exponent tex 1201 = the note's T; Def-t(i) tex 1431 = its
near-negative); delete the k ↦ −k gloss.

## P3 — precision (minor; F5 genre). W2-OPEN-2's premise pairs the keys off by one against the note's own dictionary.

Quote: "The chamber's keys φ_q^tw are byte-equal to the harness keys **Φ_q**
for q < r₀". With q a GMN order (it is bounded by the GMN orders r₀, r, and
the box's display line uses GMN-indexed φ_{r−1}^tw), the note's own §1.2
dictionary (φ_i^GMN = Φ_{i−1}^har) and §1.3 perimeter (Φ_q^har = φ_{q+1}^cls)
make the comparanda φ_q^tw vs **Φ_{q−1}** — as written the pairs have
different degrees. One-token repair.

---

## §A. The charge's five items — what was checked and CONFIRMED

**A.1 The four-route adjudication (r1's centerpiece) — each route's failure
argument re-run at source; verdict HOLDS; no fifth route found.**
(1) [JC]: verified at `GRTJC_PROOF_2026-08-08.md` — TR-3′-GEN's closed scope
of record is {all order-2} ∪ {order-3 all-e_j = 1} with the units-only
phrasing "PERMANENTLY REFUTED on (ii)" (the discrepancy an explicit slot-keyed
character) [JC r3, G-6 block]; the ρ_λ = 𝑅_λ/a_λ invariance is proved for ONE
read operator in one gauge ("the whole ρ-calculus can be run in the R^{GMN}
gauge") with anchors a_λ = 𝑅_λ(φ_λ) from a fixed tower's harness data —
chamber-internal, as the W2 box says. (2) [JB]: JB-VTX is proved "on the
SHARED-KEY PERIMETER P<q … at the W2-C1 admissible representative" (single
chain); row 15's "8 chamber walks" carry evidence class **NONE** in JB's own
§0M — machine legs, not theorems; the Σ_q(S) transport is a polygon-frame
reparameterization, never a key-representative change. (3) Classical MacLane:
re-derived — equal augmented valuations with assigned value γ_r require
v_{r−1}(Φ − φ) ≥ γ_r; the recorded data give v_{r−1}(Φ − φ) = key weight
v_{r−1}(φ_r) generically (nontrivial slot-ratio characters put the difference
ON the key line), strictly below γ_r; so key-equivalence invariance does not
apply and the lemma is genuinely about the two canonical RECIPES. (4) GMN
print: all three anchors byte-verified (tex 1288 "we fix a representative …
without necessarily assuming that it has been constructed by the method of
Propositon construct"; tex 1719 fixes ty and a representative throughout;
tex 2053 "This set is not an intrinsic invariant of f(x) because it depends
on the choices of the representatives" — plus two more dependence flags at
tex 2141 and 2355 the note did not even cite). **Fifth-route hunt** (the
charge's highest-value target): the print's only two-φ comparison results are
Lemma `extension` (tex ~763, order 1) and Proposition `extensionr` (tex
~1890, order r) — both are unramified BASE-CHANGE statements whose mechanism
requires an exact factorization ρ_r = φ_r/φ′_r with ω′_r(ρ_r) = 0; in W2's
situation Φ^har and φ^tw differ ADDITIVELY (no factorization exists), so the
admissible-development step cannot be seeded. Lemma `admissible2` (tex 1612)
is the right tool GENRE, but applying it to the expansion of (φ^tw + D)^{e_mk}
requires exactly the binomial cross-term carry control that IS W2-OPEN-2's
key-carry sufficient form — the open content, not a supplier. Harness-side
corpus ([ILN]†, LIFTCORNER, WM): single-chain laws; none compares two
chambers' keys. **Adjudication verdict "NOT derivable from the accepted
corpus, RE-SCOPED not bridged" — CONFIRMED.**

**A.2 W2-OPEN-2's statement vs the live region.** The conclusion pair (a)+(b)
is exactly the TW-ADM (vok + onesided + orbit) and TW-STRICT content the 6
live junction-levels need for W2-C3 (i)/(ii) — (iii) follows with the PARI
leg — stated at class-pin generality as W2-C3 itself requires: no more, no
less at the conclusion level. The key-carry sufficient form is correctly
related to §5.4: same channel-(b) division-carry mechanism, honestly flagged
as run "for KEY objects rather than anchors" (an analogy, not a citation),
and it is genuinely sufficient (character-only cross-term corrections ⟹ no
weight drop/support split ⟹ (a); per-slot character corrections ⟹ residual
∼ ψ^tw ⟹ (b)). The alternative GMN-citation route is correctly fenced as a
NEW consumption. Two premise-level defects: the P1 identification is baked in,
and the P3 off-by-one. TW-STRICT's SAME-adjacent reclassification is correct
(re-checked in `orbit_scan`/`transport_leg`: given the orbit pair, the §5.1
conjugation makes strictness an identity in the final chamber).

**A.3 Consumer surfaces (all pin-protected; none needed edits — verified).**
WM's (M4) face quotes W2-C3 ("strict representative at every level … no
weight/support splits", WM line 233) under the [W2]@5463f2a as-of pin (WM line
88); consumption grade is "PROVED-BY-CITATION at the cited grades" (WM1) —
conditionality rides the citation, nothing falsified; the r1-recorded
fold annotation (re-point (M4) at proved-to-first-twist / measured-above /
W2-OPEN-2) is correctly billed to the orchestrator, and one more WM staleness
item will ride the same fold: WM line 88's "its only commit" is now outdated
(W2 has 8d5e3fa). JB §0M column (d) already consumes the REPAIRED pairing
("W2-C1a for the window object; W2-C3 for the transported chamber", JB line
261) — the [r1, F2] qualifier falsifies nothing; JB row 15's subordinate
"(representative reading; W2-C3 chamber off the byte perimeter)" cell verified
at HEAD, its fold annotation likewise orchestrator-owed. LIFTCORNER consumes
W2-OPEN-1, whose box statement r1 did not touch (only an appended [r1, F1]
cross-reference sentence at the §5.3 paragraph end). r1 is note-only: 1 file,
+291/−25, runner and both artifacts byte-frozen (verified, §B).

**A.4 The 38/44 census — independently recomputed from the committed
ξ-ledger.** Parsed `xi_ledger` (entries (r, ξ, w) per `transport_leg` line
630) with my own is-one test: first-twist census per chamber = T2A/C/D/G r₀=3,
T3A/C/D/E r₀=3, T3B/F r₀=4, I4B r₀=5, I4C r₀=3, T2B/E/F + I4A no twist.
Junction-levels above a first twist: **exactly 6 = T3A, T3C, T3D, T3E at r=4
and I4C at r=4,5** — the note's list verbatim. Total = 16 r=2 rows (7+6+3
towers × 1) + 28 r≥3 rows (7+12+9) = 44 = TW-ADM's loop (r ∈ [2, NR+1] per
tower, re-read from the runner); 44 − 6 = **38** ✓. The 6 above-twist rows
coincide with the 6 CK-SLOT SKIPs and are all byte-RED ✓. All three F3
corrections re-verified against the JSON: 22 walked (byte_walk_nodes present)
+ 6 SKIP = 28; walked split 12 RED/10 GREEN, +6 SKIP RED → 18/10 ✓.

**A.5 The rest of the r1 diff, line-by-line.** S-STATUS block: arc facts
correct (PE1 = 083adff, 0C+2G+5m; counter 0/2; 28 [r1] brackets — recounted
28 exactly, multiline-tolerant). Grade cap [r1, F2]/[r1, F1] rewrites:
faithful to the findings; the W2-C1a qualifier is the right fence (byte-shared
below, junction itself unconstrained — first-divergence junctions in scope;
harness-side line content level-unconditional; matches probe F2's 45
GREEN/6 RED split, 45+6 = 51 ✓). §3.5 F5 renaming verified INCLUDING the
bracket's claim that level-indexed ξ₄ = χ₃^{γ₄}z₃^{−e₃A₃} = 1 on I4B (hand:
e₂ = 1 ⟹ ℓ₂ = 0 ⟹ A₃ = 0; ℓ′₂ = 1 ⟹ χ₃ = χ₂ = z₁⁴ = 1). §6.1 F4
disclosure verified (docstring line 77 "PREDICT: 24/24"; executed family 12).
§5.4 F7 bracket verified (JSON t3e: T3E s₂ = {0}, 0 digit-diff pairs; T3A
s₂ = {0,1}, 16 ⊆ 24 exact). §5.1 step-1 bracket, §6.2/§6.3(d)/§6.4 rewrites,
§7 round block: accurate. The one r1 edit that is WRONG against its source is
[r1, F6] — finding P2.

---

## §B. Machine leg (re-run this pass)

* **Seals:** `grt_w2_checks.py` sha256 `71f8fc90…ba52` — byte-identical
  across working tree, 5463f2a, and HEAD; `grt_weld_probe.py` sha256
  `107c92b6…4ea9` — byte-identical to seal commit 55f7416; working tree clean
  before and after the re-run.
* **Re-run: exit 0.** stdout **byte-identical** to the committed
  `grt_w2_checks_output.txt`; results JSON **byte-identical** to the committed
  file (even elapsed_s = 3.2 reproduced). 6,403 samples, 0 violations, 17
  families GREEN, boundary junctions = 1, teeth MT-TW CAUGHT. Per-family
  counts match the §6.1 table exactly (CK-MM 4,396 · CK-HR1/VD1 156 · CK-REC
  55 · CK-SLOT 44/16 · CK-XI 22 · CK-BYTE 28 · TW-RATIO/ADM/STRICT 44 ·
  TW-F3/F3b 684 · TW-PARI 12 · TW-QO 7 · CK-T3E 2 · MT-TW 2).
* **Independent JSON recomputations:** the A.4 census; the ξ-triviality ⟺
  byte-verdict cross-tab (P1's roster leg: 22/22, no ξ-trivial byte-RED
  junction); shared_below flags consistent; I4B ledger [(3,(1,1)), (4,(1,1)),
  (5,(−1,−1))] re-read.

## §C. Fresh re-derivation of the closed form (charge item 5) — an unused route: formula → committed ledger through from-scratch arithmetic

No prior report evaluated §3.4's DISPLAY directly against the committed
ξ-ledger by independent computation (PE1 §A.5–6 derived the closed form
algebraically and trusted the runner's sim for instances). This pass built
the residue towers K₀, K₁ from scratch (own field arithmetic, no runner
imports; inputs = the tower spec DATA and the committed JSON only) and
evaluated ξ = z₁^{−e₁ℓ₀g₀h₀}, w = 1 at every m = 1 junction: **16/16 towers
match the committed r = 3 ledger pairs exactly** (all have full junction
support, so the orbit pair is unique and the match is forced, not
stabilizer-assisted). At m = 2, two full hand re-derivations at the two
first-twist-at-top junctions (neither used by PE1, whose instance was I4B):
**T3B r = 4**: γ = (1, 7, 29), A = (1, 7), χ₂ = z₁^{A₁ℓ₁} = z₁ = −1 ⟹
(ξ₃, w₃) = (χ₂^{γ₃}z₂^{−e₂A₂}, χ₂^{−g₂γ₃}) = (−1, −1) = the committed ledger
pair, with top-slot consistency w·ξ^{g₂} = 1 = c = c₁^{e₂g₂}, c₁ = z₂^{−7} =
−1 ✓. **T3F r = 4**: γ = (2, 13, 79), ℓ₀ = 0 (e₀ = 1) ⟹ A₁ = 0 ⟹ χ₂ = 1;
A₂ = 13, z₂ = −z₁ of order 4 ⟹ ξ₃ = z₂^{−26} = −1, w₃ = 1 = ledger ✓;
top-slot w·ξ = −1 = c = (z₂^{−13})² ✓. The closed form is CONFIRMED on a
fresh route; en route this also re-confirms PE1's derivation-level census
(the χ-recursion and the c₁ tie ground out numerically).

## Repair queue implied (for the composer; I fix nothing)

R-P1: one scoped lemma or boundary re-key for the first-twist =
first-byte-divergence identification (m = 1 proved, machine 22/22, open at
m ≥ 2) at the [r1, F1] block AND the W2-OPEN-2 premise. R-P2: restore §4.3's
r0 sign with tex 1431 displayed; disambiguate W2-L2's parenthetical (tex 1201
construct exponent ≠ tex 1431 Def-t(i)); drop the k ↦ −k gloss. R-P3:
Φ_q → Φ_{q−1} in the W2-OPEN-2 premise. Orchestrator (fold, unchanged from
r1's record): WM (M4) annotation + "its only commit" staleness; JB row 15
annotation.

— PE2, GRTW2 acceptance arc, 2026-08-07.
