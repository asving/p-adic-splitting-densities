# D-11 (MASS-ID) — hostile verification pass 1 ("D11V", 2026-07-31)

**Charge.** Fresh-context hostile verifier. Source read: ONLY
`lean/notes/openmath/D11_massid_phaseB_attempt.md`. Quote-and-classify; fix nothing.
Special-hostility items: (1) M1's unconditional claim vs the O-12 verified perimeter;
(2) the (O3) kernel's Markov/countable-additivity resummation; (3) the a.s.-termination
reread of the (r1) margins; (4) M2's seam count and uniqueness pivot; (5) whether M1′
undermines M1/M2. Classification per the workspace convention: **CRITICAL** (breaks the
logical chain / claim not proved as billed — dependents checked only conditionally) vs
**GAP** (assume the conclusion, keep verifying downstream) vs MINOR. Verification is
against the attempt's own §0 declarations; the O-12/O-1thr/O5triple briefs themselves
were not opened (fresh-context discipline), so citation-precision items are flagged
PLAUSIBLE rather than CONFIRMED.

**Verdict: NOT ACCEPTED as billed — 1 CRITICAL, 3 GAP, 2 MINOR.** The critical finding
is a conditionality mislabel, not (so far as this pass can see) a false mathematical
belief: M1(c)'s multi-block a.s.-termination consumes the open seam (S1) while the
honesty ledger bills all of M1(a)–(d) unconditional. What survives cleanly: M1(a) and
M1(b) and M1(d) unconditional over the declared base (modulo the PLAUSIBLE
citation-precision item F5); the (O3) resummation (charge 2) — airtight given L2/L3 in
the form §1 asserts; the per-block half of M1(c); the uniqueness-pivot mechanism for
the (O1)/(O3) legs of M2; Proposition M1′; §5's OL-O12-2 split at the (O3) booking.

---

## Finding F1 — CRITICAL (conditionality): M1(c)'s a.s.-termination consumes the OPEN seam (S1) while billed unconditional

Quote (M1(c)):

> "Moreover the process terminates almost surely: along every branch the block index
> strictly decreases at each hand-off [L4: μ < e], so an infinite run eventually loops
> within one block; by the Markov property (L2+L3, as in (a)), P(≥ L consecutive loops
> at a block state) = K_e(q₀)^L ≤ (1/4)^L → 0, and a countable union over finite
> prefixes of null events is null."

and (honesty ledger §7):

> "Proved here, unconditional over the VERIFIED O-12 §3 lemma base (+ ordinary measure
> theory): Theorem M1 (a)–(d)"

The per-block computation is fine: under the block-e state law, P(loop forever) =
lim (loop mass)^L = 0 by the L2/L3 Markov induction exactly as in (a). The failure is
the cross-block composition, "a countable union over finite prefixes of null events is
null". A "finite prefix" here includes hand-off steps. The null-ness needed is: *given*
the hand-off prefix, the conditional probability that the child loops forever at block
μ is 0. The K^L bound holds under the child block's STATE LAW; but the statement that
the child, conditioned on the hand-off stratum, is distributed per the state law
(Haar-C_μ over the base-changed field) is verbatim seam **(S1)**, which §3 declares:

> "OPEN for the cross-block legs: the pattern/polygon residual descent (the 'standard
> Montes/Okutsu residual descent' O-12 §2.2 expressly fences out) and the root split"

Without (S1) (or at minimum absolute continuity of the hand-off child law w.r.t. Haar
on C_μ — itself part of the fenced-out residual descent), the trajectory law of the
multi-block process is not even fully specified, so "terminates almost surely" is not
well-posed beyond one block, and the transfer from "Haar-null in C_μ" to "conditionally
null given the prefix" is unjustified from the cited base. (A conditional law given a
hand-off stratum need not be Haar-absolutely-continuous a priori; the {loop forever}
set is Haar-null but could in principle carry conditional mass.)

Blast radius: contained. M2 is the only consumer of the a.s.-termination clause ("[The
a.s. termination of M1(c) is what makes the one-step decomposition exhaustive...]") and
M2 assumes (S1) anyway, so M2's conditional correctness is unaffected. What is false as
written: the §7 "unconditional" billing of M1(c)'s second half, and §5 clause 3's
unqualified "**PROVED (M1(c))** ... a.s. termination composed from L4 + the Markov
property". The honest restatement is: per-block a.s. exit is unconditional; full-process
a.s. termination is conditional on (S1)'s child-law clause (its independence clause and
type-composition clause are not needed for termination — only the marginal law, or
absolute continuity).

## Finding F2 — GAP: the "termination probability" reread of the (r1) margins is wrong for the (O2)/(O2′) bookings; internally contradicted by M1′

Quote (M1(c)):

> "Per booking, the per-visit continuation mass is K_e(q₀) and the exit mass is
> 1 − K_e(q₀) = Φ_e(q₀) ≥ 3/4 (O1) · 7/8 (O2, O2′) · 6/7 (O3), — O-12 Theorem 3's (r1)
> margins (Corollary D), REREAD through (a) as termination probabilities"

Per M1(a), the (O2)/(O2′) kernel books only loop-0: "K_e(q₀) = q₀^{−E} = κ₀ =
P(loop-0 | C_e)". But the semantic descent process 𝒟_e also continues (rescale,
recenter, re-enter the state law) on the loop-c strata — the attempt's own M1′ says so
explicitly:

> "the recentering stratum (mass κ₁) re-enters the full state law (L3) and realizes
> EVERY verdict with positive probability."

So for (O2)/(O2′) the per-visit PROCESS-continuation mass is q₀^{1−E} (all loop
strata), not K_e(q₀) = q₀^{−E}, and the booked exit mass 1 − q₀^{−E} ≥ 7/8 is a
booked-row mass, NOT a termination probability — the booked "exit" includes a stratum
on which the process demonstrably does not terminate. The reread is valid for (O1)
(kernel = all loop strata, Φ = 1 − q₀^{1−E} ≥ 3/4 is genuine per-visit termination) and
for (O3) (the E_rec complement is, up to the null {loop-0 forever}, the scaled exits).
The a.s.-termination CONCLUSION is unaffected (the true loop mass q₀^{1−E} ≤ 2^{1−3}·2
... = q₀^{1−E} ≤ 1/4 for e ≥ 2, q₀ ≥ 2, since E = e(e+1)/2 ≥ 3), but the displayed
identity "P(≥ L consecutive loops at a block state) = K_e(q₀)^L" is false at (O2)/(O2′)
(should be (q₀^{1−E})^L), and §5 clause 3's "the margins ARE O-12's verified (r1)
margins ... reread as termination probabilities — PROVED" inherits the error at the 7/8
margin. Classification GAP: the mathematical content is repairable by restricting the
termination reread to (O1)/(O3) (the density-carrying bookings per M1′'s own
consequence paragraph), which the unit failed to do.

## Finding F3 — GAP: M2's balance-equation derivation does not cover the (O2′) leg it claims

Quote (M2 statement): "for the re-entrant bookings (O1)/(O2′)/(O3)". Quote (proof):

> "β*_e(σ) = P(loop)·P(type σ | loop) + Σ_{exit strata F} P(F)·P(type σ | F). On the
> loop stratum the transformed state is again the state law with the SAME type [L2+L3
> — proved, no seam], so P(type σ | loop) = β*_e(σ) ... the right-hand side is exactly
> the abstract row: β*_e satisfies x = K_e(q₀)·x + t(q₀)"

For (O1), P(loop) = K_e(q₀) (kernel = all loop strata) and every non-loop stratum
hands off to μ < e (L4), so t is x-free and the induction closes. For (O3) the attempt
defers to "O-12 §2.4 displays the equivalence: identical solved values" — acceptable
as a brief-internal display (see F6). But for (O2′), M1(a) fixes the kernel at κ₀ =
q₀^{−E} (loop-0 only), so the loop-c strata are neither in the kernel term K_e(q₀)·x
nor hand-offs to lower blocks — they re-enter block e itself with the same unknown
β*_e (M1′'s mechanism). As displayed, either t(q₀) contains x (and the equation
"x = K_e(q₀)x + t(q₀)" with the (O2′) kernel is not what β*_e satisfies), or the
(O2′) member's rows book loop-c through some resummation/self-referential form the
proof never displays. Nothing in §3 derives the (O2′) case; no analogue of the §2.4
equivalence is cited for it. The theorem's conclusion for (O2′) is therefore
unproved as written. Repair path is presumably the same resummation as (O3) (fold
P(σ|loop-c) = β*_e(σ) into the left side: x = (κ₀+κ₁)x + t_true, pivot
1 − q₀^{1−E} ≠ 0 by the (O1) margin) — but the verifier fixes nothing; the leg is a gap.

The uniqueness pivot itself (charge 4, second half) is complete where the equation is
established: scalar K, 1 − K_e(q₀) = Φ_e(q₀) ≠ 0 by (r1) at every prime power, so the
affine equation has a unique solution and the abstract solve t/(1−K) is one; (r2)
supplies definedness of every evaluated entry (both consumptions displayed in §3's
"where the pole-free theorem is consumed" paragraph). No circularity: β* is defined
semantically, the equation is derived from M1(a),(b),(d) + (S1) + (S2) + induction on
e (well-founded via L4), and (r1) enters only to invert. The base case (e = 1) and the
simultaneous-in-q₀ induction (needed because hand-offs move to q₀^{D_i}) are sound.

## Finding F4 — GAP (seam count): the projective assembly weight is a third unproved input to M2's top layer, not covered by (S1)/(S2)

Quote (M1(a), family (v)):

> "EXCEPT the projective assembly weight (q−1)/(q^{n+1}−1), whose mass reading lives at
> the root/projective assembly layer (the M1 bridge companion), consumed only by M2's
> top layer."

Quote (M2's seam preamble): "**The two seams (the ONLY unproved inputs; owners
named).**" The "M1 bridge companion" appears nowhere in §0's source list and no proof
of the projective weight's mass reading appears in this unit; (S1) covers hand-off
faithfulness and (S2) composition data — neither covers this weight. So either (i)
M2's scope is the monic ensemble only (its statement says "Haar-random monic degree-n
f over O", and its proof's root layer is the monic root read) — in which case the
family-(v) clause "consumed only by M2's top layer" is wrong and the projective
reading of M2's conclusion (which the N2 falsifier explicitly exercises: "monic +
projective") is out of theorem scope and should be said to be; or (ii) M2's top layer
does consume it — in which case "the ONLY unproved inputs" is false and there are
three seams, the third unowned. Answer to charge 4, first half: **as written, the seam
count is exactly two only for the monic reading; the projective reading has an
undisplayed third input.**

## Finding F5 — GAP, PLAUSIBLE (citation precision): the uniform-reduction and conditional-pushforward content attributed to L2+L3

M1(a) repeatedly consumes two precise statements: (i) conditioned on R_e, the
reduction h̄ is UNIFORM over the q₀^e monic degree-e residuals ("L3 for the reduction
partition: q₀ centers × q₀^{−e} each", and "L2 + L3's uniform reduction" at the
divisor-pattern rows — load-bearing wherever Fact F counts are converted to masses,
hence also for M1(d)'s Σ = 1); (ii) the step map conditioned on a loop stratum pushes
the conditional law to the state law ("conditioned on the stratum, ĥ is AGAIN the
state law", §1) — the Markov property driving the (O3) resummation, M1(c), and M2's
loop-term cancellation. §0's glosses of the verified lemmas are "L2 (rescale
self-similarity, measure-preserving), L3 (re-cluster, measure-preserving +
type-preserving)": consistent with (i)+(ii) but not verbatim containing them —
"measure-preserving" alone (e.g. preserving Haar globally) is strictly weaker than the
conditional-pushforward form used. This pass read only the attempt, so it cannot
confirm the verified L2/L3 statements have the needed strength; the next pass (or a
one-line quote from `O12_phaseB_verifybrief_rev4.md` §3 into the attempt) should pin
the exact lemma statements. If they do have that strength, F5 evaporates and — this is
the charge-2 verdict — **the (O3) resummation is measure-theoretically airtight**: the
E^{(L)} are measurable (finite intersections of stratum preimages under measurable
step maps), pairwise disjoint (first non-(loop-0) step differs — checked, and the exit
family (loop-0)^L∘F is likewise disjoint across L since F is disjoint from loop-0),
the induction P(E^{(L)}|C_e) = κ₀^{L−1}κ₁ is the conditional-pushforward identity
applied L−1 times, and κ₀ = q₀^{−E} < 1 makes the geometric series converge to
κ₁/(1−κ₀) = (q₀−1)/(q₀^E−1) — arithmetic verified, as were the (O1) identity
q₀·q₀^{−e}·q₀^{−(E−e)} = q₀^{1−E}, the exit scaling q₀^E/(q₀^E−1), the normalization
vol(C_e) = q₀^{−e}, and all three margin values at (e, q₀) = (2, 2).

## Finding F6 — MINOR (citation hygiene, two items)

(i) M1(c) cites "O-12 Theorem 3's (r1) margins (**Corollary D**)"; §0's enumeration of
the verified perimeter lists L1–L6′, L6e, Fact F, Theorems 1/3/4 — no Corollary D. If
Corollary D is the brief's margins-corollary of Theorem 3 this is cosmetic, but the
attempt's own discipline ("every cite is to a proved, verified O-12 §3 lemma") should
name only enumerated objects. (ii) M2's (O3) leg rests on "O-12 §2.4 displays the
equivalence: identical solved values" — a brief-internal algebraic display cited from
§2.4, which is claim-scope text rather than the §3 lemma base; presumably verified
with the brief, but it is an input the seam preamble does not mention.

## Charge-by-charge summary

1. **M1 unconditional vs perimeter.** M1(a), (b), (d): every cite is to L1–L4,
   L6a–L6e, L6′, Fact F + ordinary measure theory — inside the declared perimeter
   (modulo F5's precision item). M1(c) additionally consumes Theorem 3(r1)/"Corollary
   D" (perimeter per §0, naming quibble F6) AND — the critical finding — the (S1)
   child-law content for its multi-block half (F1), which is NOT in the perimeter and
   is declared open two sections later. The "unconditional" billing must be re-scoped.
2. **(O3) resummation.** Airtight conditional on L2/L3 having the
   conditional-pushforward strength the attempt asserts they have (F5); all
   disjointness, measurability, convergence, and arithmetic checks pass.
3. **A.s.-termination reread.** Two defects: the (S1) dependence (F1) and the
   (O2)/(O2′) misidentification of booked-exit mass with termination probability (F2).
   The (O1)/(O3) margin rereads are correct.
4. **M2 seams + pivot.** Two seams as displayed only for the monic reading; the
   projective assembly weight is an undisplayed third input (F4). Pivot mechanism
   complete for (O1)/(O3); the (O2′) leg's balance equation is not derived (F3).
5. **M1′ vs M1/M2.** M1′ does not undermine M1(a), (b), (d) (they claim masses of
   displayed events, not verdict-constancy) and not M2 (which excludes (O2); but see
   F3 for (O2′), whose kernel M1(a) makes identical to (O2)'s). It DOES contradict
   M1(c)'s termination reread at (O2)/(O2′) — that is F2, and the attempt states both
   sides without noticing. M1′'s consequence paragraph (density carriers = re-entrant
   bookings; (O2) = gate object) is sound and consistent with §5 clause 4.

## Required for pass 2

R1 (from F1): restate M1(c) as per-block unconditional + multi-block conditional on
(S1)'s child-law clause (name the minimal form used); fix §5 clause 3 and the §7
ledger. R2 (from F2): restrict the termination reread to (O1)/(O3); correct the
"P(≥ L consecutive loops) = K^L" display to the loop mass. R3 (from F3): derive the
(O2′) balance equation or drop (O2′) from M2's statement. R4 (from F4): either scope
M2 to monic and delete "consumed only by M2's top layer", or display the projective
weight as a named third seam with owner. R5 (from F5): quote the verified L2/L3
statements verbatim into §0 so the conditional-pushforward + uniform-reduction
strength is checkable. R6 (from F6): cite enumerated objects only; add §2.4 to the
(O3)-leg conditionality display.

*Verifier: Fable pass 1, fresh context, source = the attempt file only. Nothing fixed.*
