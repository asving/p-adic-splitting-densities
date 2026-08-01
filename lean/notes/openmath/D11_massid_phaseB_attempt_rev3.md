# D-11 (MASS-ID) — Phase-B attempt REV 3: the mass-identification theorem (Fable "D11", 2026-07-31)

> **[SUPERSEDED 2026-08-04.** This revision FAILED the owed hostile pass
> (`D11_owedpass_2026-08-03.md`, VERDICT CRITICAL — 6 CRITICAL + 3 GAP; the
> ROOT Phase-C acceptance was SUSPENDED on it). The current revision is
> **`D11_rev4_2026-08-04.md`** — the Unit-A repair executed per the accepted
> consolidated design `R11_REPAIR_DESIGN_V5_2026-08-04.md` (edit list L1–L11;
> pass-confirmed passages of this file carried byte-stable there). Nothing in
> this file is current; read the r4.**]**

Repair of the pass-2 hostile verification (`V31_d11r2.jsonl`, verdict UNSOUND —
2 CRITICAL, 4 GAP, 2 MINOR; rev-2's F2 core, F3, F5, F6 repairs CONFIRMED OK)
of the rev-2 attempt (`D11_massid_phaseB_attempt_rev2.md`; pass-1 record =
`D11_pass1_verify.md`, its dispositions = rev 2's §0-pre, on file there).
Produced by COPYING rev 2 and applying ONLY the edits listed below, so every
pass-2-confirmed passage — M1(a)'s (i)/(ii)/(iii) bullets, M1(c)'s corrected
booked-row/termination displays, M1(d), the (O2′) folded-pivot derivation, the
verbatim L2/L3 quotes, Proposition M1′, M3, §6's falsifier record — is
byte-stable (diff-checkable against rev 2: the delta is exactly this table's
eight dispositions).

## 0-pre. Pass-2 findings → dispositions (no silent drops)

| # | pass-2 finding (gist) | class | disposition |
|---|---|---|---|
| P1 | Lemma M2.0's written proof does not establish its advertised minimal dependence: conditioning on a revealed PREFIX is not licensed by the immediate-stratum marginal clause; the absolute-continuity transport step is asserted, not argued; and literal state-valued prefixes are uncountable | GAP | **FIXED (§3, Lemma M2.0 rewritten)**: the proof is re-based on countable SYMBOLIC ADDRESSES (finite (stratum, child-slot) words — the strata are countable, hand-off lists finite); the consumed clause is displayed as **(S1-m)** (the child pushforward under the CANONICAL parent law is ≪ Haar-C) together with the displayed structural premise **(DET)** (the §1 model is ONE Haar draw pushed through displayed measurable maps — each child is a measurable function of its parent's state); the ≪-transport is a displayed induction on address length whose kernel-null-set step is written out; no sibling/downstream conditioning ever occurs. HONEST WIDENING displayed in-lemma: under a genuinely stochastic hand-off reading, (S1-m) alone does NOT suffice and the billing widens to the prefix-conditional clause (S1-m+) |
| P2 | M1(a) is self-contradictory: its universal quantifier over families (i)/(ii)/(iii)/(v) includes the projective assembly weight that the same clause then disclaims; the §7 ledger compounds it by billing "Theorem M1 (a)–(d)" unconditional | CRITICAL (statement/billing) | **FIXED (§2 + §7)**: M1(a)'s quantifier RESCOPED to families (i)/(ii)/(iii); NEW clause **(a′)** gives family (v) its per-entry displayed readings (valuation-box masses; singleton-residual conditional masses; the (O3) scalings read only through (a)'s (O3) bullet — they are not masses), with the projective weight quantified over NOWHERE (→ (S3)); NEW clause **(a″)** puts ALL exclusions in the theorem statement itself; §7 re-billed per the verifier's own correctly-billed list — block-level unconditional, everything crossing a hand-off conditional |
| P3 | The package recommends "D-11 status → PROVED-UNVERIFIED" while §5 itself admits the actual-pack correspondence (clause 4) is unchecked — a completed-node overclaim ("finite"/"engineering" ≠ "proved") | CRITICAL (overclaim) | **FIXED (§5)**: the recommendation is WITHDRAWN; clause 4 restated **OPEN** = OL-O12-2's remaining DATA half (cited: `O12_phaseB_attempt_rev4.md` §3), displayed as the open clause it is; D-11's honest status = LAYERED (its M1/M2/M3 layers at their displayed conditionality; clause 4 open); the "zero mathematical content" gloss replaced — the pass is finite data comparison but it IS clause 4's content |
| P4 | M2's monic root layer is only asserted ("the same argument once more"); no root analogue of M1(b)/(d) is stated or proved; "a factor occurring in a mass formula is not thereby itself the mass of a displayed event" | GAP | **FIXED (§3 proof)**: the root layer is DISPLAYED — the root read **(R-read)** defined (pattern masses N_π·q^{−n} composed with the root composition datum); **(R-b/R-d)** proved unconditionally (exact unique-factorization partition; L3's uniform-reduction clause applied at degree n; normalization Σ_π N_π = q^n from Fact F(ii) counting a partition); **(R-balance)** derived conditional on (S1)'s root leg + (S2); the pack-rows-equal-(R-read) match EXCLUDED in-statement (→ clause 4) |
| P5 | The unit-charge billing "kernel/entry VALUES are masses" is broader than the proof: families (iv)-arbitrary-α/(vi)/(vii) are not covered, and the exclusions lived in a downstream caveat instead of the theorem statement | GAP | **FIXED (§2 (a″) + §5 + §7)**: the exclusions are moved INTO Theorem M1's statement; the coverage is restated at every summary layer as (i)–(iii) + (a′)'s per-entry readings + M1′'s concrete recorded row — and NOT beyond |
| P6 | M1(b) proves disjointness of the displayed strata and their multi-step compounds; the per-ROW disjointness of a concrete pack's combined/adjusted rows is entangled with the open transcription pass | GAP | **FIXED (§2 (b))**: scope sentence appended to (b) — the per-row reading for a concrete pack is clause-4/data-pass content (OPEN); (b) claims the displayed strata and their compounds only, plus M1′'s one concrete adjusted row |
| P7 | §5 clause 3 cites "L4 + the Markov property" for the per-block exit; L4 (decreasing block indices) is not what proves it — L2/L3 + the loop bound do | MINOR (citation) | **FIXED (§5)**: cite corrected to L2+L3 (the Markov property) + the loop-mass bound; L4's role confined to Lemma M2.0's branch-length argument |
| P8 | "Lemma M2.0 … is what makes the one-step decomposition exhaustive" is false — M1(b)/(d) already make it exhaustive; M2.0 is not consumed by the renewal equation or its unique solution | MINOR | **FIXED (§3 proof)**: the bracket is replaced — M2.0 is NOT consumed by the equation or the solve; its role is the OPERATIONAL a.s.-decidedness reading of the conclusion, billed on its own (S1-m)+(DET) ledger line |

Pass-2 CONFIRMED and carried byte-stable: the F2 core (booked-row vs
termination distinction + the corrected loop display (q₀^{1−E})^L), the F3
(O2′) folded-pivot derivation at its stated input perimeter, the F5 verbatim
L2/L3 quotes, F6's citation hygiene, M1(a)'s (i)/(ii)/(iii) bullets, M1′,
M3, §6.

**Unit charge (tree §D1.2 D-11 node + DELTA-2 §§D2.2/D2.7 pricing + CU_cluster §6.1
audit).** Prove that the abstract solve family 𝔅_n's kernel/entry VALUES are the Haar
masses of the continuation events at the intended instance — the identification through
which O-12's pole-free theorem (VERIFIED, leaf #2) gets to speak about the real
densities — composed from the displayed pieces; or the honest partial with the exact
seam. Sub-charge: close OL-O12-2's mathematical half. This unit is written on the
CU_cluster §6.1 audit's pricing (per-box lift uniformity = O5triple Theorem E + D-15;
NO ∼_OM/OB2 consumption) and constructively re-confirms it: no step below pools
OM-equivalent polynomials.

## 0. Sources and the status of every consumed piece

* `O12_phaseB_verifybrief_rev4.md` — **VERIFIED at honest scope** (V19 + Fable pass 2;
  ledger commit 95a46d2). **The scope subtlety this unit lives on:** the O-12 CLAIM is
  zeros/poles only ("VALUE correctness is also not part of the claim", §1), but the
  brief's §3 is a set of fully-proved SEMANTIC MASS lemmas — L1 (coefficient/root
  valuations), L2 (rescale self-similarity, measure-preserving), L3 (re-cluster,
  measure-preserving + type-preserving), L4 (hand-off bounds μ < e), L6a (polygon cell
  = displayed event, exact Haar volume), L6b (affine cone exponents c_j ≥ 1), L6c/L6d
  (residue independence + the joint count-rationality (JC)), L6′ ((g4) closure), L6e
  (exhaustion off the displayed null set Z_e, disjoint cells), Fact F (universal
  pattern counts), Theorem 1 (kernels/determinants; its clause (3) displays the four
  bookings' balance equations — the re-entrant three are all algebraically
  (1 − κ₀ − κ₁)x = s), Theorem 3 ((r1)+(r2) at every
  prime power, margins 3/4 · 7/8 · 6/7), **Corollary D** (the det channel: the brief's
  margins-corollary of Theorem 3 — D_{Φ_e}(q₀) ≠ 0, N_{Φ_e}(q₀) ≠ 0, and the displayed
  per-booking margins Φ^{(O1)} ≥ 3/4, Φ^{(O2)} = Φ^{(O2′)} ≥ 7/8, Φ^{(O3)} ≥ 6/7 at
  every prime power q₀ ≥ 2), Theorem 4 (substochastic robustness) — all
  inside the verified perimeter (the rev-1..rev-3 audit arc confirmed exactly these).
  Also consumed as brief-internal DISPLAYED inputs (claim-scope text verified with the
  brief, named here per pass-1 F6(ii)): the §2.4 booking displays — the four kernels,
  the balance-equation forms `(O2′) x = κ₀x + (κ₁x + s)` ("the κ₁ strata booked as
  exit legs that RE-FEED block e's own entrance") and the (O3) resummed equivalence
  (`(1 − κ₁/(1−κ₀))x = s/(1−κ₀)`, same solve after multiplying by 1 − κ₀ ≠ 0).
  Because M1 consumes L2/L3 in their full conditional-pushforward strength (pass-1
  F5), the two verified statements are quoted VERBATIM from the brief's §3:

  > **Lemma L2** (rescale self-similarity). Conditioned on R_e = {a_i ∈ π^iO ∀i},
  > the coefficients b_i := a_i/π^i of h(y) := g(πy)/π^e are independent Haar-
  > uniform on O, and g, h have equal splitting types.

  > **Lemma L3** (re-cluster). For Haar-uniform monic h of degree e: the reduction
  > h̄ is uniform on the q₀^e monic degree-e polynomials over F_{q₀}; for each
  > c ∈ F_{q₀}, the event {h̄ = (y − c)^e} has volume q₀^{-e}, and conditioned on
  > it, h(c̃ + y) is Haar conditioned on C_e (the block state law), with splitting
  > type equal to that of h.

  These contain exactly the two consumptions M1 makes: (i) the uniform-reduction
  clause (h̄ uniform over the q₀^e monic residuals — what converts Fact F counts to
  masses), and (ii) the conditional-pushforward clause (conditioned on a loop stratum,
  the transformed state is AGAIN the state law with equal type — the Markov property
  driving the (O3) resummation and M2's loop-term handling).
  MASS-ID consumes the LEMMAS as mass statements, which is what they are; it does NOT
  widen the O-12 claim retroactively — the composition below is NEW material with its
  own conditionality display.
* `O1thr_phaseB_verifybrief_rev3.md` §6 **Theorem 3 = D-15** (CYL + mass/count tie:
  decided ns-free verdict classes are exact finite unions of level-t cylinders;
  #Φ_N(T) = mass(T)·p^{nN}; per-box tree uniqueness/disjointness). CONDITIONAL-ON-PASS
  **P(O-1thr r4)** (rev-4 landed, fresh pass owed); caveat **(E-N)** OPEN (displayed
  where it bites).
* `O5triple_phaseB_verifybrief_rev3.md` §6 **Theorem E** (D-7c + O-5 ASSEMBLY: "any two
  monic separable lifts of x have equal splitting types"; the multiset is engine data,
  lift-independent). Conditional on interface (I-1)–(I-3) (served per CU-7's corrected
  attribution) + the five §2 flags; **P(O5t r3)**.
* `CU_cluster_phaseB.md` — CU-1/CU-2 (no-missing/no-phantom, per-f), CU-7 (interface
  discharge), §6.1 (the D2.7 audit: D-11 does NOT consume OB2), §0 pending-verdict
  registry (P(O-2a r5), P(O-1thr r4), P(O5t r3), P(CU-1 r2) = V29, P(GD23 r2) = V28).
* `docs/MATH_COMPLETION_TREE_2026-08-01.md` — the D-11 node text (§D1.2), T-3/T-6 node
  texts (§2.2), D2.2 GD table (GD-2/GD-3 rows), D2.6 path step 8.
* `O12_phaseB_attempt_rev4.md` §3 — OL-O12-2's own text ("dischargeable by a finite
  transcription-and-correspondence pass").
* Numerics of record: N6-regp (25/25 gates, 95/95 primes, 0 failures, min margin 6/7);
  N2-density-tie (24/24 configs + exact n = 2 census, width ~1e-5); O-12 §8 rev-2/4
  (L6a cell-law and L6e-trichotomy exact enumerations). NEW falsifier extension: §6.

**Standing perimeter carried:** monic separable; ns loci Haar-null (T-6 (ns-null),
VERIFIED-DUAL); the intended instance = the O-12 §2.1 semantic model verbatim: prime p,
δ ≥ 1, q₀ = p^δ, K₀/ℚ_p unramified of degree δ, O its integers, Haar on monic degree-e
polynomials via coefficient tuples O^e; E := E_e := e(e+1)/2.

## 1. The objects identified (definitions, all displayed)

**The descent process 𝒟_e (the semantic reading of block e).** State space: the
aligned size-e cluster law — Haar conditioned on C_e = {v(a_i) ≥ 1 ∀i} (O-12 §2.2).
One step = the O-12 §2.2 stratification of C_e:

    (loop-0)   R_e ∩ {h̄ = y^e}                      [rescale, recenter at 0]
    (loop-c)   R_e ∩ {h̄ = (y−c)^e}, c ∈ F_{q₀}^×    [rescale, recenter at c]
    (patt-π)   R_e ∩ {h̄ has pattern π}, π ≠ {(1,e)} [rescale, split; hand-offs
                                                      = the atoms (D, m), m ≥ 2]
    (poly-κρ⃗)  (C_e \ R_e) ∩ {polygon P of face-kind κ, w ∈ cone} ∩ {shapes ρ⃗}
                                                     [polygon exit; hand-offs
                                                      = the atoms of the ρ_j, m ≥ 2]

up to the displayed Haar-null set Z_e = (C_e\R_e) ∩ {a_e = 0} (L6e; Z_2 = ∅). On loop
strata the step map is g ↦ ĥ := h(c̃ + y), h = g(πy)/π^e; L2 + L3 say: conditioned on
the stratum, ĥ is AGAIN the state law (Haar on C_e), with the same splitting type. On
hand-off strata the booked children go to blocks μ < e (L4) at base change q ↦ q^D.

**Per-row continuation events.** For a row of a 𝔅_n member (a §2.3 family member), its
*continuation event* is the sub-event of the state law that the row books, with
multi-step rows read through the step maps: e.g. the (O3) kernel books

    E_rec := ⨆_{L ≥ 1} E^{(L)},   E^{(L)} := {first L−1 steps are (loop-0),
                                              step L is some (loop-c), c ≠ 0},

and the (O3)-scaled exit rows book ⨆_{L ≥ 0} {L steps of (loop-0), then the exit
stratum}. These are genuine measurable events: finite intersections of preimages of
the displayed strata under the (measurable, measure-preserving) step maps.

**The abstract side.** A 𝔅_n member's kernel K_e, entries E(e), determinant
Φ_e = det(1 − K_e), solved values β_e(σ) = u^{−1}t_σ — fixed elements of ℚ(q),
evaluated at q₀ (defined there by O-12 Theorem 3).

## 2. Theorem M1 (one-step mass identification — block-level, unconditional over the verified O-12 lemma base; scope displayed IN-STATEMENT)

**Theorem M1.** Fix n ≥ 2, a member of 𝔅_n, a prime power q₀ = p^δ ≥ 2, a block
e ∈ {2, …, n} (block 1 is trivial: K_1 = 0, immediate termination). Then, with all
masses CONDITIONAL on the state law C_e:

**(a) [values are masses — families (i)/(ii)/(iii); pass-2 P2 rescope].** Every §2.3
family-(i)/(ii)/(iii) entry, evaluated at q₀, IS the Haar mass of its displayed
continuation event:
  * kernel, (O1): K_e(q₀) = q₀^{1−E} = P(R_e ∩ {h̄ = (y−c)^e for some c} | C_e) — the
    mass of "descend at a rational e-fold center" [L1 for R_e = the descent event; L2
    for the rescale; L3 for the reduction partition: q₀ centers × q₀^{−e} each ×
    P(R_e|C_e) = q₀^{−(E−e)}].
  * kernel, (O2)/(O2′): K_e(q₀) = q₀^{−E} = κ₀ = P(loop-0 | C_e) [same cites, c = 0].
  * kernel, (O3): K_e(q₀) = (q₀−1)/(q₀^E−1) = P(E_rec | C_e). Proof of the resummed
    identity: by induction on L, P(E^{(L)} | C_e) = κ₀^{L−1}κ₁ — the base is L2+L3;
    the step is the Markov property (conditioned on (loop-0) the transformed state is
    again the state law, L2+L3, so the next step's stratum probabilities are again
    κ₀, κ₁, …). The E^{(L)} are pairwise disjoint (they differ at the first
    non-(loop-0) step), so countable additivity gives
    P(E_rec | C_e) = Σ_{L≥1} κ₀^{L−1}κ₁ = κ₁/(1−κ₀) = (q₀−1)/(q₀^E−1). The (O3) exit
    scaling likewise: P(⨆_{L≥0} (loop-0)^L ∘ F | C_e) = P(F|C_e)/(1−κ₀) =
    P(F|C_e)·q₀^E/(q₀^E−1).
  * divisor-pattern masses: m(π)(q₀) = q₀^{−(E−e)}·N_π(q₀)·q₀^{−e} = P(patt-π | C_e)
    [L2 + L3's uniform reduction + Fact F(ii): N_π(q₀) counts the monic h̄ of pattern
    π].
  * polygon-family masses: m(κ, ρ⃗)(q₀) = P(poly-κρ⃗ summed over the depth cone | C_e).
    Per cell: P(cell) = (1−q₀^{−1})^k·q₀^{−N(P)} [L6a, exact]; P(shapes ρ⃗ | cell) =
    ∏_j P_{ρ_j}(q₀)·(q₀^{d_j}−q₀^{d_j−1})^{−1} — ONE value uniform over every cell of
    the face-kind [L6d (JC)]; the cells of the cone are pairwise disjoint [L6e(i)], so
    countable additivity along L6b's affine cone (exponents c_j ≥ 1 give convergent
    geometric sums Σ_w q₀^{−N_min−Σc_jw_j}) reproduces exactly the displayed closed
    form of §2.3(iii) [the L6′ algebra], times the conditional normalization q₀^{+e}
    (= 1/vol(C_e)).
**(a′) [family (v) — per-entry displayed readings; pass-2 P2/P5: rev ≤ 2's blanket
"each is a displayed factor of a mass" reading is WITHDRAWN — a factor occurring in a
mass formula is not thereby itself the mass of a displayed event].** Family (v)'s four
sublists, each read at its occurrences in (a)'s closed forms and the §2.3(iv)/(O3)
adjustments:
  * q^{−b} (0 ≤ b ≤ E_n): each occurrence IS the Haar mass of the displayed valuation
    box it names there — e.g. vol(C_e) = q₀^{−e} (v(a_i) ≥ 1 ∀i), vol(R_e) = q₀^{−E}
    (v(a_i) ≥ i ∀i) [L1], the L6a cell factors q₀^{−N(P)};
  * (q^d − q^{d−1})^{−1}: the conditional mass of a displayed SINGLETON-residual
    event — by L6c/L6d the face-j residual is uniform over its q₀^d − q₀^{d−1}
    admissible values, so each occurrence is P(residual = one fixed value | cell);
  * q^{E_m}/(q^{E_m}−1) (the (O3) exit scalings Σ_{L≥0} κ₀^L): NOT masses (they
    exceed 1); their mass reading is exactly and only (a)'s (O3) bullet — the PRODUCT
    with an exit-stratum mass is the mass of the displayed resummed event
    ⨆_{L≥0} (loop-0)^L ∘ F;
  * (q−1)/(q^{n+1}−1), the projective assembly weight: EXCLUDED from this theorem —
    quantified over NOWHERE in (a)/(a′). Its mass reading lives at the projective
    assembly layer and is seam **(S3)** in §3 (owner: annex node A-1 of the
    completion tree, the monic → projective bridge = June lemma M1); it is consumed
    only by the PROJECTIVE reading of M2's conclusion.

**(a″) [in-statement exclusions — the exact perimeter of the "values are masses"
claim, displayed here rather than in a downstream caveat (pass-2 P5)].** NOT claimed
by (a)/(a′): family-(iv) verdict rows under ARBITRARY allocation data α_e — they need
not be masses at all (they can leave [0, 1]; Proposition M1′ below covers exactly the
recorded concrete α₂ at n = 2, and nothing more); families (vi)/(vii) — the β-legs
and solved entries carry no per-entry mass identity, their density reading being
Theorem M2's CONDITIONAL conclusion; and the projective assembly weight ((S3)). The
unit charge's "kernel/entry VALUES" is covered exactly at (i)–(iii) + (a′)'s
readings + M1′'s concrete row, and not beyond.

**(b) [rows pairwise disjoint].** The one-step strata are pairwise disjoint and
exhaust C_e up to the null set Z_e: R_e vs C_e\R_e is the L1 dichotomy; within R_e the
reduction h̄ partitions [L3]; within C_e\R_e (off Z_e) the polygon cells partition
[L6e(i)] and, per cell, the joint-shape events partition [L6d's consistency clause:
the (JC) values sum to 1 over shape vectors]. Multi-step events built from disjoint
strata by the step maps are disjoint at the first differing step. [Scope (pass-2
P6): (b) is a statement about the DISPLAYED strata and the multi-step events built
from them, plus — at n = 2 — M1′'s one concrete adjusted row. That every
combined/adjusted row of a CONCRETE pack books such a disjoint union is
actual-pack-correspondence content: §5 clause 4, OPEN (OL-O12-2's data half). It is
NOT claimed here.]

**(c) [positive per-visit termination margin at the density-carrying bookings +
per-block a.s. exit].** The true per-visit PROCESS-continuation mass is the same at
every booking: the loop strata carry κ₀ + κ₁ = q₀^{1−E} [by (a); M1′ — the loop-c
strata continue (rescale, recenter, re-enter the state law) whether or not the
booking's kernel books them]. The (r1) margins (Corollary D) are genuine per-visit
TERMINATION probabilities exactly at the re-entrant density-carrying bookings:

    (O1)  1 − K_e(q₀) = 1 − q₀^{1−E} = Φ^{(O1)}(q₀) ≥ 3/4   [kernel = ALL loop
          strata, so booked exit = true exit],
    (O3)  Φ^{(O3)}(q₀) ≥ 6/7   [kernel = E_rec; up to the null set
          {loop-0 forever}, the complement of E_rec is exactly the scaled exits,
          so the resummed step terminates with probability Φ^{(O3)}(q₀)],

— this restricted reread is the precise sense in which the pole-free theorem speaks
about the real process. At (O2)/(O2′) the booked exit mass 1 − q₀^{−E} ≥ 7/8 is a
BOOKED-ROW mass, NOT a termination probability: the loop-c strata (mass κ₁) sit
outside the κ₀ kernel yet the process demonstrably continues on them (M1′) — the
rev-1 reread at the 7/8 margin was wrong and is withdrawn (pass-1 F2).
Moreover, PER BLOCK the process a.s. exits: by the Markov property (L2+L3, as in
(a)), P(≥ L consecutive loops at a block-e state) = (q₀^{1−E})^L ≤ (1/4)^L → 0
(E = e(e+1)/2 ≥ 3 for e ≥ 2, q₀ ≥ 2), so under any single block's state law the
event "loop at this block forever" is Haar-null. [This is the UNCONDITIONAL half of
the rev-1 termination claim. A.s. termination of the FULL multi-block process needs,
in addition, the hand-off child law — verbatim seam-(S1) content — and is therefore
stated at M2's layer as Lemma M2.0 (§3), where (S1) is assumed: the pass-1 CRITICAL
repair.]

**(d) [Σ = 1].** For every block state, the one-step strata masses sum to 1: (b)'s
partition + countable additivity + L6e(ii) (Z_e null). [O-12 §8 checked this
symbolically for e ≤ 5 as a declared non-proof corroboration; here it is a theorem of
the same lemma base — the composition O-12's scope fence deliberately did not take.]

*Proof.* Assembled above, clause by clause; every cite is to a proved, verified O-12
§3 lemma, plus ordinary countable additivity and the two measure-preservation lemmas
L2/L3 for the step maps. No engine object, no box, no lift, no ∼_OM class appears. ∎

**Proposition M1′ (the (O2) verdict-row caveat — a finding, not a defect).** Under the
(O2) booking with the concrete allocation datum α₂ = (0, q−1) (the machine-checked
degree-2 table), the adjusted verdict row values ARE masses of displayed events — at
e = 2, the α-adjusted row 1/q − q^{−3} evaluates to q₀^{−1} − q₀^{−3} =
P(descend and not (loop-0) | C_2), the disjoint union of the two pattern strata
(π = {(1,1),(1,1)} and {(2,1)}, total mass q₀^{−1} − q₀^{−2} by Fact F) with the
recentering stratum (κ₁ = q₀^{−2} − q₀^{−3}) — but the booked event is NOT
verdict-constant:
the recentering stratum (mass κ₁) re-enters the full state law (L3) and realizes EVERY
verdict with positive probability. Hence the (O2) booking satisfies M1(a–d) while its
solved values differ from the true conditional densities — exactly the divergence O-12
§2.4 records. Consequence for D-11: the instance pin's target must be (and is) the
re-entrant bookings — the general-n engine is (O1), the sealed degree-3 tables are
(O3) (O-12 §1); the (O2) member is the coarsened n = 2 Lean GATE instance (so
recorded in the N6 harness), not a density carrier. For arbitrary allocation data
α_e ∈ ℚ[q] the adjusted rows need not be masses at all (they can leave [0, 1]); O-12's
theorem quantifies over all of them because its claim is poles/zeros only — MASS-ID
covers exactly the recorded concrete choice.

## 3. Theorem M2 (the solve identification — the abstract solved values ARE the real conditional densities; the exact seams displayed)

**The three seams (the ONLY unproved inputs; owners named; per-consumer scope
displayed).** [Also consumed, NOT a seam: the O-12 §2.4 booking displays / Theorem
1(3) balance-equation forms — brief-internal displayed algebra, verified with the
brief, named in §0 per pass-1 F6(ii); they enter the (O2′) and (O3) legs below.]
[Also displayed, NOT counted a seam: **(DET)**, Lemma M2.0's structural reading of
§1's model (ONE Haar draw pushed through displayed measurable maps) — a definitional
stance on the semantic model, not an unproved mathematical statement; its
honest-widening fallback under a stochastic reading is displayed in-lemma (pass-2
P1).]
* **(S1) Hand-off faithfulness.** Conditioned on a hand-off stratum F with hand-off
  list ((μ_1, D_1), …, (μ_r, D_r)): the r handed-off sub-objects are INDEPENDENT, the
  i-th distributed per block μ_i's state law over the base-changed field (Haar-C_{μ_i}
  over the degree-D_i unramified extension, residue field F_{q₀^{D_i}}), and the
  parent's splitting type is a function of the children's types (+ the terminal m = 1
  atoms' fixed data). Status: PROVED for the within-block legs — the loop hand-off IS
  L2+L3, so (O1)/(O2′)/(O3)'s kernels carry no seam; OPEN for the cross-block legs:
  the pattern/polygon residual descent (the "standard Montes/Okutsu residual descent"
  O-12 §2.2 expressly fences out) and the root split (HEN-LIFT + joint law of the
  Hensel factors). Owner: **GD-3 FULL form** (the value side; O-9 OL-B — "one proof
  should serve both") + LIT-3/(HEN-LIFT) at the root. Proved partials on file: M08
  Theorem 2 (level-1 census, 46 strata machine-checked); B-4/M6 empirical through OM
  order 4 (GD-3 row, tree §D2.2).
* **(S2) Composition-datum correctness.** The member's comp_F equals the TRUE type
  composition (types of coprime factors aggregate as multiset union; a child type over
  the degree-D unramified extension contributes through the fixed base-change law).
  Status: OPEN as a general statement; table data per member. Owner: **O-11** (value
  correctness; T-7s carries the concrete tables and their obligations ledger).
* **(S3) Projective assembly weight.** The mass reading of the family-(v) entry
  (q−1)/(q^{n+1}−1) at the root/projective assembly layer — that it is the correct
  projective normalization tying the monic root read to the projective ensemble.
  Status: OPEN in this unit (nothing here derives it). Owner: **annex node A-1**
  (the monic → projective bridge, June lemma M1; PROVED-UNVERIFIED at the tree,
  out of the critical path by standing directive). Scope: consumed ONLY by the
  projective reading of M2's conclusion — M2 as stated (monic ensemble) does not
  consume it; the N2 falsifier's projective configurations exercise it numerically.

**Lemma M2.0 (a.s. termination of the full process — conditional exactly on the
displayed clause (S1-m), under the displayed structural reading (DET)).** [Pass-2 P1
rewrite: rev 2's one-paragraph proof ASSERTED the prefix-conditioning and
≪-transport steps and took a union over uncountably many state-valued prefixes; all
three defects are repaired below.]

*The consumed inputs, displayed:*
* **(DET)** [the structural reading of §1's model — a premise, displayed, not
  hidden]: the semantic process is ONE Haar draw pushed through displayed measurable
  maps — the within-block step is the deterministic map g ↦ ĥ = h(c̃ + y) (§1), and
  each hand-off child is a measurable function T_{F,i} of the parent state on its
  stratum F (the child IS the displayed cluster/factor of the parent polynomial; the
  model carries no randomness beyond the initial draw). This is how §1 / O-12 §2.2
  define the model, and it is the reading under which L2/L3 are stated (they are
  distributional statements about exactly these deterministic maps).
* **(S1-m)** [of (S1), ONLY the child-marginal clause, read under the CANONICAL
  parent law]: for each block e′, each hand-off stratum F ⊆ C_{e′} with child list
  ((μ_1, D_1), …, (μ_r, D_r)), and each slot i, the pushforward under T_{F,i} of the
  normalized restriction of Haar-C_{e′} to F is Haar-C_{μ_i} over the degree-D_i base
  change — or merely ABSOLUTELY CONTINUOUS w.r.t. it, which is all the proof uses.
  [(S1)'s independence and type-composition clauses are NOT consumed.]
* M1(c)'s per-block clause; L4; measurability of the displayed strata and step maps
  (the L2/L3/L6 layer).

*Statement.* Under (DET) and (S1-m), the descent process from any block state (any
block, any prime power) terminates almost surely.

*Proof (four displayed steps).*
1. *(Addresses are countable.)* A node address is a finite word
   a = ((F_1, i_1), …, (F_k, i_k)) of (hand-off stratum, child slot) pairs. Each
   block's one-step strata form a COUNTABLE set — finitely many loop and pattern
   strata; per polygon face-kind, countably many depth cells w ∈ cone × finitely
   many shape vectors — and each hand-off list is finite, so the address set 𝔄 is
   countable. [Rev 2 unioned over "finite prefixes"; state-valued prefixes are
   uncountable (pass-2). Symbolic addresses are the correct countable index.]
2. *(Reduction to an eternal loop at a node.)* Block indices strictly decrease
   across hand-offs [L4: μ < e], so every branch of the descent tree makes finitely
   many hand-offs, and a non-terminating run reaches some node — at a finite address
   a ∈ 𝔄 — whose within-block trajectory never leaves the loop strata. Write
   x_a := the state at node a (where defined, a measurable function of the initial
   draw, by (DET)) and, per block μ, N_μ := {x ∈ C_μ : the within-block trajectory
   of x loops forever} = ⋂_L {first L within-block steps are loop strata} —
   measurable (preimages of displayed strata under the deterministic step maps), and
   null: for μ ≥ 2, Haar-C_μ(N_μ) ≤ (q^{1−E_μ})^L → 0 (E_μ ≥ 3) at every prime
   power q, including the base-changed q₀^{D_i} [M1(c)'s per-block clause]; block 1
   terminates immediately (§2: K_1 = 0), so N_1 = ∅. Then
       {non-termination} ⊆ ⋃_{a ∈ 𝔄} E_a,
       E_a := {node a reached} ∩ {x_a ∈ N_{μ(a)}}.
3. *(≪-transport along an address — the kernel-null-set step, displayed.)* Claim:
   for every a ∈ 𝔄 with P(node a reached) > 0, the law of x_a conditioned on
   {node a reached} is ≪ Haar-C_{μ(a)}. Induction on |a|. Base |a| = 0: that law IS
   the block state law. Step a = a′·(F, i): {node a reached} =
   {node a′ reached} ∩ {x_{a′} ∈ F}, and x_a = T_{F,i}(x_{a′}) [(DET)]. Let
   N ⊆ C_{μ(a)} be Haar-null. (S1-m) at (F, i) gives
   Haar-C_{μ(a′)}(F ∩ T_{F,i}^{−1}(N)) = 0 [the pushforward of normalized Haar|_F
   puts mass 0 on N]. By the inductive ≪, P(x_{a′} ∈ F ∩ T_{F,i}^{−1}(N) |
   node a′ reached) = 0; dividing by P(x_{a′} ∈ F | node a′ reached) > 0 gives
   P(x_a ∈ N | node a reached) = 0. [Why no illegitimate conditioning occurs — the
   pass-2 objection: under (DET), {node a reached} is itself a composed preimage of
   displayed strata under measurable functions of the ONE initial draw; the
   induction never conditions a child on sibling or downstream data — it only pushes
   null sets back through the maps. The parent's REACHED-conditioned law (not the
   canonical law) is what the inductive hypothesis controls, and that is exactly why
   (S1-m) under the canonical law + ≪-transport suffices.]
4. *(Conclusion.)* For every a ∈ 𝔄: P(E_a) ≤ P(node a reached) ·
   P(x_a ∈ N_{μ(a)} | node a reached) = 0 [step 3 + N_μ Haar-null; addresses with
   P(reached) = 0 contribute trivially]. A countable union [step 1] of null events
   is null. ∎

*Honest billing widening (displayed per the pass-2 charge: prove the minimal
dependence or widen).* The proof consumes (S1-m) AND the structural reading (DET).
If a future (S1) discharge realizes the hand-off as a genuinely STOCHASTIC kernel
(randomness beyond the parent state), (DET) fails, step 3's composed-preimage
reading fails with it, and — as pass 2 observed — the bare marginal clause no longer
suffices: a parent law ≪ Haar does not transport through an arbitrary kernel pinned
only in Haar-average. The billing then widens to **(S1-m+)**: the child's law
conditioned on the FULL revealed path to its birth is ≪ its block's Haar-C law —
prefix-conditional (S1) content (the seam's intended Markov reading), NOT derivable
from (S1-m) alone. Either way M2.0 consumes strictly less than full (S1); the
minimal displayed form is (S1-m) + (DET).

**Theorem M2.** Assume (S1) and (S2) for the member. Then for every prime power
q₀ = p^δ and every block e, for the re-entrant bookings (O1)/(O2′)/(O3):

    β_e(σ)(q₀) = P( splitting type = σ | the block-e state law at q₀ ),   ∀σ,

i.e. the abstract solved values ARE the real conditional densities; and the top-layer
assembly (root read + entrance weights) identifies the solved final densities with the
true unconditional splitting-type densities of Haar-random monic degree-n f over O.
[MONIC scope. The PROJECTIVE reading of this conclusion is additionally conditional
on (S3) — the projective assembly weight's mass reading, owner A-1.] [Top layer
(pass-2 P4): the identified object is the DISPLAYED root read (R-read) — proof, root
layer below. That a concrete pack's root/entrance rows equal (R-read) entry-for-entry
is actual-pack-correspondence content (§5 clause 4, OPEN) and is NOT claimed here.]

*Proof.* Induction on e (well-founded: hand-offs go to blocks μ < e by L4; base e = 1:
a linear factor, the type atom is forced, β_1 = 1 = the displayed E(1)). Let
β*_e(σ) := P(type = σ | C_e) — well-defined on the separable full-measure locus. One
step of 𝒟_e, using M1(b)'s partition and M1(d):

    β*_e(σ) = P(loop)·P(type σ | loop) + Σ_{exit strata F} P(F)·P(type σ | F).

On EVERY loop stratum — loop-0 AND each loop-c — the transformed state is again the
state law with the SAME type [L2+L3 — proved, no seam; L3's type-preservation is
what makes this hold at the recentering strata too], so P(type σ | loop-0) =
P(type σ | loop-c) = β*_e(σ) — the same unknown. On a genuine exit stratum F,
(S1)+(S2) give P(type σ | F) = Σ_{comp_F(σ⃗)=σ} ∏_i β*_{μ_i}(σ_i at
q₀^{D_i}); by the induction hypothesis each β*_{μ_i}(· at q₀^{D_i}) equals the
abstract β_{μ_i}(·)(q₀^{D_i}) — the (g5) β-legs of E(e). With M1(a) (each P(F) is the
abstract mass entry at q₀), the semantic one-step identity is therefore

    x = (κ₀ + κ₁)·x + s(q₀),      x := β*_e(σ) coordinate-wise,

with s the true exit row (x-free in block e: every genuine exit hands off to blocks
μ < e by L4, values supplied by the IH). This IS the member's balance equation at
each re-entrant booking [pass-1 F3 repair — the (O2′) leg now derived, not asserted]:
  * **(O1)**: kernel = κ₀ + κ₁, t = s — literally the display above.
  * **(O2′)**: kernel = κ₀ only, but the member's loop-c rows are BLOCK-e β-LEGS by
    construction [O-12 §2.4: "the κ₁ strata booked as exit legs that RE-FEED block
    e's own entrance", t = κ₁x + s], so the member's equation x = κ₀x + (κ₁x + s)
    is the same identity regrouped.
  * **(O3)**: the resummed form (1 − κ₁/(1−κ₀))x = s/(1−κ₀) [O-12 §2.4]; multiplying
    by 1 − κ₀ ≠ 0 recovers the display.
By O-12 Theorem 1(3), all three are algebraically (1 − κ₀ − κ₁)x = s, i.e.
(1 − q₀^{1−E})x = s(q₀); the folded pivot 1 − q₀^{1−E} = Φ^{(O1)}(q₀) ≥ 3/4 is
nonzero at every prime power [Corollary D / (r1)], so the equation has a UNIQUE
solution; the abstract common re-entrant solve β_e(q₀) = s(q₀)/(1 − q₀^{1−E}) is
one, hence β*_e = β_e(q₀). [Exhaustiveness of this conditioning needs only M1(b)/(d)
— the one-step strata partition C_e up to the displayed null sets — and NOT Lemma
M2.0: pass-2 P8 corrected rev 2's misattribution; the renewal equation and its
unique solution consume no termination statement. M2.0's role is the OPERATIONAL
reading of the conclusion — a.s. every draw's descent terminates, so the solved
densities describe an a.s.-decided process — billed on its own (S1-m)+(DET) line in
§7.]

**Root layer (pass-2 P4: displayed, replacing rev 2's one-sentence assertion).** The
top state is Haar on monic degree-n f — NO C-conditioning; the root read precedes
any descent. Define the DISPLAYED root read: for each divisor pattern π of total
degree n with atoms (D_j, m_j) (the m_j = 1 atoms decided and absorbed into the root
composition datum comp^root_π as fixed data, exactly as in §2.3(iv)),

    (R-read)   d(σ)(q) := Σ_π N_π(q)·q^{−n} ·
                  Σ_{comp^root_π(σ⃗)=σ} ∏_{j : m_j ≥ 2} β_{m_j}(σ_j)(q^{D_j})

— the root analogue of the §2.3(iv) rows with pattern mass N_π(q)·q^{−n} in place of
m(π) (no q^{−(E−e)} factor: nothing is conditioned at the top).
* **(R-b/R-d)** [the root analogue of M1(b)/(d) — unconditional over the same lemma
  base]: the events {f̄ has pattern π} PARTITION the top state space exactly (unique
  factorization over F_{q₀}: every monic residual has exactly one divisor pattern —
  at this layer not even a null set is excluded), with P(f̄ has pattern π) =
  N_π(q₀)·q₀^{−n} [L3's uniform-reduction clause applied at degree n — its verbatim
  statement (§0) is for Haar-uniform monic of arbitrary degree e, and the top state
  is exactly that at e := n — plus Fact F(ii) for the count], and
  Σ_π N_π(q₀)·q₀^{−n} = 1 [the N_π count a partition of the q₀^n monic residuals].
* **(R-balance)** [conditional on (S1)'s ROOT leg + (S2)]: on {pattern π}, the
  m_j ≥ 2 atoms' clusters are the root hand-offs; (S1)'s root leg (HEN-LIFT + the
  joint law of the Hensel factors) gives cluster j the block-m_j state law over the
  degree-D_j unramified extension, and (S2)'s root composition datum aggregates the
  cluster types (+ the decided atoms) to the type of f, so P(type σ | pattern π) =
  Σ_{comp^root_π(σ⃗)=σ} ∏_{j : m_j ≥ 2} β*_{m_j}(σ_j at q₀^{D_j}); the block theorem above
  supplies β*_{m_j}(· at q₀^{D_j}) = β_{m_j}(·)(q₀^{D_j}). Total probability over
  (R-b)'s partition: the true unconditional splitting-type density of Haar-random
  monic degree-n f equals (R-read) at q₀. ∎

[What the root layer does NOT settle — displayed, not hidden (pass-2 P3/P4): that a
CONCRETE pack's root/entrance rows equal (R-read) entry-for-entry is the actual-pack
correspondence — §5 clause 4, OPEN, OL-O12-2's data half. M2's top layer identifies
the DISPLAYED assembly with the true densities; it certifies no sealed table.]

**Where the pole-free theorem is consumed — the displayed answer to the unit charge:**
O-12's (r1) is the UNIQUENESS PIVOT (the folded re-entrant pivot 1 − q₀^{1−E} =
Φ^{(O1)}(q₀) ≠ 0 — Corollary D — pins the semantic density vector as THE solution of
the abstract equation, at every prime power including wild); O-12's margins are the
TERMINATION supply (M1(c) per-visit at (O1)/(O3) + per-block; Lemma M2.0 for the
multi-block composition, on (S1-m)+(DET)); O-12's (r2) is the definedness of every
evaluated entry the induction touches. That is the identification through which the
pole-free theorem "speaks about the real densities": without M1/M2 it is a theorem
about rational functions; with them it is a theorem about the descent process's
decided masses.

## 4. Theorem M3 (row labels are true types; the T-3/T-6 event tie — the audit-priced clause)

**(a) [per-box σ-constancy — what D-11 needs where verdicts meet boxes].** Let T be a
decided ns-free tree with threshold t = thr(T) fibered by a box x. Then the verdict
class is an EXACT finite union of level-t cylinders with the fiber scaling law and
per-box tree uniqueness [D-15 = O-1thr Theorem 3(a)–(c)], and every monic separable
lift g of x has true splitting type equal to the tree's verdict multiset typemult(T)
[O5triple Theorem E via CU-7's corrected attribution]. So the verdict σ labeling a
decided continuation/termination event is the true type of EVERY polynomial of the
event's cylinders — lift uniformity per box, exactly the σ-constancy D-11's row
labels need. Conditionality (inherited, displayed): P(O5t r3) + (I-1)–(I-3) as served
by CU-7 (hence P(O-2a r5), P(CU-1 r2) = V29 through CU-4's leg) + the five O5triple
flags (GD-1/GD-7/GD-8 duties) + P(O-1thr r4) + TB-CAP's D-12r perimeter + (E-N)
displayed OPEN (it touches which N a box may be counted at, not the constancy).
**Constructive re-confirmation of the CU_cluster §6.1 audit:** the clause consumed is
single-cylinder lift uniformity; no ∼_OM pooling, no OB2, no BNS object appears — the
O3design row "D-11 ← OB2" stays unwarranted.

**(b) [the classifier tie — M1's events ARE the T-3/T-6 continuation events].** M1/M2
identify table values with masses of SEMANTIC strata (root valuations, reductions of
rescales, Newton polygons, residual shapes). D-11's node text speaks of "the T-3/T-6
continuation events" — the branch-tree events of T_can(f) (T-3's per-shape-prefix
mass law; T-6's assembly/TB-CAP). The tie is the engine-read seam: the machine's
window polygon = the Newton polygon vertex-for-vertex and the emitted records are the
GMN data [GD-2], the residual reads are the residual shapes [GD-3-min], every emitted
record is its chain's GMN datum [CU-2 no-phantom] and every Cons_f chain is realized
[CU-1 no-missing]. Under this dictionary the semantic strata of §1 are read by the
engine as its continuation events, and M1's identities become D-11's literal clause
("kernel entries are the Haar volumes of the T-3/T-6 continuation events").
Conditionality: the GD-1..GD-6 residue per the CU §0 registry (heads GD23 = V28,
CU-1 = V29) + P(O-2a r5) + P(O-1thr r4). Nothing here is new mathematics — it is the
same composition CU-1/CU-2 already price; this clause only ATTACHES the mass
identities to the classifier vocabulary.

## 5. What this closes (the D-11 clause map + OL-O12-2's mathematical half)

The D-11 node's four clauses (tree §D1.2), with statuses after this unit:
1. *"kernel entries are the Haar volumes of the … continuation events at the intended
   instance"* — **PROVED unconditionally at the semantic events, AT M1's in-statement
   scope (pass-2 P2/P5)**: families (i)/(ii)/(iii) as masses (M1(a)), family (v) per
   entry per (a′), M1′'s concrete adjusted row — with (a″)'s displayed exclusions
   (arbitrary-α verdict rows; (vi)/(vii), whose density reading is M2's conditional
   conclusion; the (S3) weight); at the T-3/T-6 (classifier) reading, conditional
   exactly on the M3(b) dictionary (GD/CU conditionality, displayed).
2. *"the events per row pairwise disjoint"* — **PROVED (M1(b))**, up to the displayed
   null sets (Z_e; ns loci) — at the DISPLAYED strata and their multi-step compounds;
   the per-row reading for a concrete pack's combined/adjusted rows is clause-4
   content (the correspondence pass, OPEN — pass-2 P6).
3. *"with positive per-state termination margin"* — **PROVED (M1(c)) at the
   density-carrying bookings**: the margins ARE O-12's verified (r1) margins 3/4
   (O1) and 6/7 (O3), reread as per-visit termination probabilities; at (O2)/(O2′)
   the 7/8 margin is a booked-row mass, NOT a termination probability (M1′; pass-1
   F2), and the true per-visit loop mass is q₀^{1−E} ≤ 1/4 at every booking.
   A.s. termination: PER BLOCK unconditional (M1(c): L2+L3's Markov property + the
   loop-mass bound — pass-2 P7 cite fix; L4 plays no role there, its decreasing-index
   argument belonging to Lemma M2.0's branch-length step); the FULL multi-block
   process conditional exactly on (S1-m)+(DET) (Lemma M2.0, rewritten at pass-2 P1;
   billing widens to the displayed (S1-m+) under a stochastic hand-off reading).
4. *"the pack's block system IS 𝔅_n — or an organization covered by the robustness
   criterion"* — **OPEN (pass-2 P3: this clause is NOT closed by this unit, and D-11
   is therefore NOT a completed node)**. What stands: degree-2 = the (O2) member IN
   the O-12 claim (with M1′'s coarseness finding: it is a gate object, not a density
   carrier; its transcription is in the N6 harness of record); degree-3 sealed: the
   claim "is an (O3) member" is EXACTLY OL-O12-2, whose remaining DATA half — the
   finite transcription-and-correspondence pass — has NOT run (below); the GENERAL-n
   eventual pack = O-14d instance population, an engineering duty outside the math
   tree (D-10), guarded by the robustness backup (O-12 Theorem 4 + contingent
   OL-O12-1) if a future pack departs from 𝔅_n's organizations. Until the
   correspondence pass runs, M1/M2/M3 speak about 𝔅_n members and the displayed
   (R-read) assembly — not yet about the sealed tables.

**OL-O12-2, split and half-closed.** OL-O12-2 (O-12 attempt rev 4 §3): "the complete
sealed degree-3 tables — every stratum mass, kernel, junction row, and final density
on record — are, entry-for-entry, an (O3) member of 𝔅₃ with its recorded composition
datum. Dischargeable by a finite transcription-and-correspondence pass."
* Its MATHEMATICAL half — what the identification would MEAN, i.e. that matching an
  (O3) member makes the pole-free theorem's clauses statements about the true degree-3
  densities (masses, margins, uniqueness of the solved values) — is **CLOSED by M1 +
  M2 at n = 3, (O3) booking**, at the conditionality displayed there (M1 at its
  in-statement scope, unconditional; Lemma M2.0 on (S1-m)+(DET); M2 on (S1)/(S2),
  monic scope — projective reading additionally on (S3); M3 for the verdict/box
  reading). Nothing about the MEANING of the identification remains open.
* Its remaining half is the finite transcription-and-correspondence pass itself (map
  each sealed row to its §2.3 family (i)–(vii) member and check entry equality) —
  finite displayed-data comparison, no new mechanism, same execution class as O-14d —
  but it IS the content of clause 4 (pass-2 P3: "finite" and "engineering" do not
  mean "proved"): until it runs, the sealed tables are not established to be an (O3)
  member, the per-row readings ((a″), (b)'s scope note, (R-read)) are not ATTACHED
  to them, and D-11 is not a completed node. Numerics already tie it tightly (§6) —
  a falsifier, not a discharge. The (S1)/(S2) seams are NOT OL-O12-2 residue: they
  are GD-3-full/O-11 property, priced there.

**Recommended DELTA-3 lines (governance, sign-off owed — not executed here):**
(i) the CU §6.1 OB2 eviction, now constructively re-confirmed by M3(a); (ii) D-11
status → **LAYERED, NOT COMPLETE** (rev-2's PROVED-UNVERIFIED recommendation
WITHDRAWN — pass-2 P3): clauses 1–3 at their displayed layers (M1(a)/(a′)/(b)/(c)/(d)
+ M1′ + (R-b/R-d) unconditional over the verified O-12 lemma base, at the
in-statement scope; Lemma M2.0 on (S1-m)+(DET); M2 on (S1)/(S2), monic scope,
projective reading on (S3); M3 on the displayed CU/O5triple/D-15 conditionality);
clause 4 **OPEN** = the actual-pack correspondence, OL-O12-2's data half
(`O12_phaseB_attempt_rev4.md` §3); (iii) OL-O12-2 re-labeled "data-pass only —
and that data pass = D-11 clause 4's open content" per the split above.

## 6. Falsifier report (standing citations + the NEW extension, ran with this unit)

Standing (cited, not re-run):
* **N6-regp** (`verification/openmath/N6-regp_scan.py`, results JSON + tree §3 fleet
  table): the REAL tables — the sealed RESUM-n3 degree-3 solve transcribed verbatim +
  both n = 2 instances — pass all 25 symbolic/brute gates and the (r1)/(r2-def)/
  (r2-act) scan at ALL 95 primes < 500, faithful and superset pools, 0 failures; the
  minimum observed escape margin is 6/7 — EQUAL to Corollary D's (O3) bound at q₀ = 2,
  i.e. M1(c)'s margin is observed sharp at the real tables.
* **N2-density-tie** (exact + MC + report logs): the solved values equal the true Haar
  densities numerically — 24/24 (ensemble, n, p) configurations (n ≤ 5, p ∈ {2,3,5},
  all wild pairs, monic + projective), 0 cells beyond 4 SE, plus the float-free exact
  n = 2 census sandwich (width ~1.5e-5 / 5.7e-6 / 1.3e-5 at p = 2/3/5) — M2's
  conclusion observed exactly where it can be enumerated. [The projective
  configurations exercise the (S3)-conditional PROJECTIVE reading of M2's
  conclusion — numerical support for the seam, not a proof of it.]
* **O-12 §8 rev 2/4 exact enumerations**: L6a's cell law and L6e's trichotomy over
  (ℤ/p^M)^e lifts, five configs, zero exceptions — M1(a)'s per-cell mass identity
  checked exhaustively at small levels.

NEW (this unit; falsifier-first — the scan ran before this section was frozen):
* **N6-regp-ext2000** (`verification/openmath/N6-regp_scan_ext2000.py`, results
  `N6-regp_results_ext2000.json`, log `logs/N6-regp_ext2000.log`): the same real
  tables, primes extended 500 → 2000 (303 primes) and pools deepened δ ≤ 3 → δ ≤ 4
  (q₀ up to ≈ 1.6·10¹³). MASS-ID-relevant clauses: every entry defined with value in
  [0, 1] (necessary for M1(a)), every count polynomial a nonnegative integer (Fact F
  at large q₀), every det margin positive (M1(c)). RESULT (2026-07-31, this machine):
  **303/303 primes PASS at n = 2 AND n = 3; failing sets EMPTY at faithful AND
  superset pools; all 25 gates + brute ACT anchors PASS; minimum escape margin again
  exactly 6/7** (at n = 2, q₀ = 2, the (O3) kernel) — the M1(c) bound stays sharp and
  is never approached anywhere else in the scanned range.

A single failure — an entry outside [0, 1], a non-integer count, a vanishing
determinant, or an N2 density mismatch — would have refuted M1(a)/(c) or M2 at the
real tables.

## 7. Honesty ledger

**Proved here, unconditional over the VERIFIED O-12 §3 lemma base (+ ordinary measure
theory) — all BLOCK-LEVEL or root-partition statements; nothing in this class crosses
a hand-off (pass-2 P2 re-billing, per the verifier's own correctly-billed list):**
Theorem M1 at its REV-3 in-statement scope — (a) families (i)/(ii)/(iii) as masses;
(a′) the family-(v) per-entry readings (the (S3) weight quantified over nowhere);
(a″) the displayed exclusions; (b) at the displayed strata (per-row pack readings
excluded in-statement); (c) per-visit margins at the density-carrying bookings
(O1)/(O3) + the PER-BLOCK a.s. exit; (d) — Proposition M1′, and the root
partition/normalization (R-b/R-d). These are new COMPOSITIONS: O-12's claim
deliberately excluded value semantics; its lemmas do not — this unit is the place
where that composition is written down.
**Proved here, conditional exactly on the displayed seams — everything that crosses
a hand-off:** Lemma M2.0 (a.s. termination of the full process) [(S1-m), the
child-marginal clause under the canonical parent law — Haar absolute continuity
suffices — PLUS the structural reading (DET); widens to the displayed
prefix-conditional (S1-m+) under a stochastic hand-off reading — §3]; Theorem M2's
block induction, monic scope [(S1) GD-3 full / LIT-3 root leg; (S2) O-11 composition
data]; M2's top layer at the DISPLAYED root read (R-read) [(S1) root leg + (S2)] —
its PROJECTIVE reading additionally on [(S3) the projective assembly weight, owner
A-1]; Theorem M3(a) [P(O5t r3) +
(I-1)–(I-3) via CU-7 + five flags + P(O-1thr r4) + TB-CAP D-12r + (E-N) displayed];
M3(b) [the GD/CU dictionary, per the CU §0 registry].
**NOT proved here — the open clause displayed (pass-2 P3):** D-11 clause 4, the
ACTUAL-PACK CORRESPONDENCE (that the sealed tables ARE an (O3) member — OL-O12-2's
remaining data half, `O12_phaseB_attempt_rev4.md` §3) — so D-11 is NOT a completed
node; and the seams (S1)/(S2)/(S3) themselves. The unit charge's "kernel/entry
VALUES are masses" is covered exactly at (a)/(a′)/M1′ and not beyond ((a″));
arbitrary-allocation verdict rows are explicitly outside.
**Findings:** M1′ (the (O2) verdict-row coarseness pins the density-carrying packs to
the re-entrant bookings); the (r1)-as-uniqueness-pivot reading (§3) — the exact
mechanism by which O-12 speaks about real densities; the constructive OB2
re-confirmation (M3(a)).
**Not attempted:** discharging (S1)/(S2)/(S3) (owned by GD-3-full/O-9, O-11, and
annex A-1 respectively); the OL-O12-2
data pass (= clause 4's open content, above); the general-n pack population (O-14d);
Lean artifacts; any O5triple/O-1thr/CU pass.

**Files:** this record = `lean/notes/openmath/D11_massid_phaseB_attempt_rev3.md`
(rev 2 = `D11_massid_phaseB_attempt_rev2.md`, superseded; pass-1 report =
`D11_pass1_verify.md`; pass-2 report = `V31_d11r2.jsonl`); falsifier
extension = `verification/openmath/N6-regp_scan_ext2000.py` + results JSON + log
(UNCHANGED by this revision — every clause it tests survives rev 3 verbatim: entry
definedness/[0,1], count integrality, det margins; the rev-3 rescopes are
statement-perimeter and billing edits, not scanned quantities). No
other file touched; home-brief pointer updates (O-12's OL-O12-2 line may add "math
half closed at D11 unit") are their owners'.
