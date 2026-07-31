# D-11 (MASS-ID) — Phase-B attempt: the mass-identification theorem (Fable "D11", 2026-07-31)

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
  pattern counts), Theorem 1 (kernels/determinants), Theorem 3 ((r1)+(r2) at every
  prime power, margins 3/4 · 7/8 · 6/7), Theorem 4 (substochastic robustness) — all
  inside the verified perimeter (the rev-1..rev-3 audit arc confirmed exactly these).
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

## 2. Theorem M1 (one-step mass identification — unconditional over the verified O-12 lemma base)

**Theorem M1.** Fix n ≥ 2, a member of 𝔅_n, a prime power q₀ = p^δ ≥ 2, a block
e ∈ {2, …, n} (block 1 is trivial: K_1 = 0, immediate termination). Then, with all
masses CONDITIONAL on the state law C_e:

**(a) [values are masses].** Every §2.3 family-(i)/(ii)/(iii)/(v) entry, evaluated at
q₀, IS the Haar mass of its displayed continuation event:
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
  * entrance/shape weights (family (v)): each is a displayed factor of one of the
    above masses (cell volumes q^{−b}, shape normalizations (q^d − q^{d−1})^{−1}, the
    (O3) scalings) — same cites — EXCEPT the projective assembly weight
    (q−1)/(q^{n+1}−1), whose mass reading lives at the root/projective assembly layer
    (the M1 bridge companion), consumed only by M2's top layer.

**(b) [rows pairwise disjoint].** The one-step strata are pairwise disjoint and
exhaust C_e up to the null set Z_e: R_e vs C_e\R_e is the L1 dichotomy; within R_e the
reduction h̄ partitions [L3]; within C_e\R_e (off Z_e) the polygon cells partition
[L6e(i)] and, per cell, the joint-shape events partition [L6d's consistency clause:
the (JC) values sum to 1 over shape vectors]. Multi-step events built from disjoint
strata by the step maps are disjoint at the first differing step.

**(c) [positive per-state termination margin + a.s. termination].** Per booking, the
per-visit continuation mass is K_e(q₀) and the exit mass is

    1 − K_e(q₀) = Φ_e(q₀) ≥ 3/4 (O1) · 7/8 (O2, O2′) · 6/7 (O3),

— O-12 Theorem 3's (r1) margins (Corollary D), REREAD through (a) as termination
probabilities: this is the precise sense in which the pole-free theorem speaks about
the real process. Moreover the process terminates almost surely: along every branch
the block index strictly decreases at each hand-off [L4: μ < e], so an infinite run
eventually loops within one block; by the Markov property (L2+L3, as in (a)),
P(≥ L consecutive loops at a block state) = K_e(q₀)^L ≤ (1/4)^L → 0, and a countable
union over finite prefixes of null events is null.

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

**The two seams (the ONLY unproved inputs; owners named).**
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

**Theorem M2.** Assume (S1) and (S2) for the member. Then for every prime power
q₀ = p^δ and every block e, for the re-entrant bookings (O1)/(O2′)/(O3):

    β_e(σ)(q₀) = P( splitting type = σ | the block-e state law at q₀ ),   ∀σ,

i.e. the abstract solved values ARE the real conditional densities; and the top-layer
assembly (root read + entrance weights) identifies the solved final densities with the
true unconditional splitting-type densities of Haar-random monic degree-n f over O.

*Proof.* Induction on e (well-founded: hand-offs go to blocks μ < e by L4; base e = 1:
a linear factor, the type atom is forced, β_1 = 1 = the displayed E(1)). Let
β*_e(σ) := P(type = σ | C_e) — well-defined on the separable full-measure locus. One
step of 𝒟_e, using M1(b)'s partition and M1(d):

    β*_e(σ) = P(loop)·P(type σ | loop) + Σ_{exit strata F} P(F)·P(type σ | F).

On the loop stratum the transformed state is again the state law with the SAME type
[L2+L3 — proved, no seam], so P(type σ | loop) = β*_e(σ) — the same unknown. On an
exit stratum F, (S1)+(S2) give P(type σ | F) = Σ_{comp_F(σ⃗)=σ} ∏_i β*_{μ_i}(σ_i at
q₀^{D_i}); by the induction hypothesis each β*_{μ_i}(· at q₀^{D_i}) equals the
abstract β_{μ_i}(·)(q₀^{D_i}) — the (g5) β-legs of E(e). With M1(a) (each P(F) is the
abstract mass entry at q₀), the right-hand side is exactly the abstract row: β*_e
satisfies

    x = K_e(q₀)·x + t(q₀)

coordinate-wise — the member's balance equation, evaluated. By O-12 Theorem 3 (r1),
1 − K_e(q₀) = Φ_e(q₀) ≠ 0, so the equation has a UNIQUE solution; the abstract solve
β_e(q₀) = t(q₀)/(1 − K_e(q₀)) is one, hence β*_e = β_e(q₀). [The a.s. termination of
M1(c) is what makes the one-step decomposition exhaustive: the never-exiting event
carries zero mass, so no density leaks.] The (O3) form is the same equation resummed
(O-12 §2.4 displays the equivalence: identical solved values). The root layer is the
same argument once more at the top state (Haar on monic degree-n): the root strata are
the reduction patterns of f̄ (Fact F counts = the family-(v)/root-read entries), the
hand-offs are the root split's clusters — the (S1) root leg. ∎

**Where the pole-free theorem is consumed — the displayed answer to the unit charge:**
O-12's (r1) is the UNIQUENESS PIVOT (Φ_e(q₀) ≠ 0 pins the semantic density vector as
THE solution of the abstract equation, at every prime power including wild); O-12's
margins are the TERMINATION supply (M1(c)); O-12's (r2) is the definedness of every
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
   instance"* — **PROVED unconditionally at the semantic events (M1(a))**; at the
   T-3/T-6 (classifier) reading, conditional exactly on the M3(b) dictionary
   (GD/CU conditionality, displayed).
2. *"the events per row pairwise disjoint"* — **PROVED (M1(b))**, up to the displayed
   null sets (Z_e; ns loci).
3. *"with positive per-state termination margin"* — **PROVED (M1(c))**: the margins
   ARE O-12's verified (r1) margins 3/4 · 7/8 · 6/7, reread as termination
   probabilities; a.s. termination composed from L4 + the Markov property.
4. *"the pack's block system IS 𝔅_n — or an organization covered by the robustness
   criterion"* — for the CONCRETE packs: degree-2 = the (O2) member IN the O-12 claim
   (with M1′'s coarseness finding: it is a gate object, not a density carrier);
   degree-3 sealed = (O3) member up to OL-O12-2's residue (below); the GENERAL-n
   eventual pack = O-14d instance population, an engineering duty outside the math
   tree (D-10), guarded by the robustness backup (O-12 Theorem 4 + contingent
   OL-O12-1) if a future pack departs from 𝔅_n's organizations.

**OL-O12-2, split and half-closed.** OL-O12-2 (O-12 attempt rev 4 §3): "the complete
sealed degree-3 tables — every stratum mass, kernel, junction row, and final density
on record — are, entry-for-entry, an (O3) member of 𝔅₃ with its recorded composition
datum. Dischargeable by a finite transcription-and-correspondence pass."
* Its MATHEMATICAL half — what the identification would MEAN, i.e. that matching an
  (O3) member makes the pole-free theorem's clauses statements about the true degree-3
  densities (masses, margins, uniqueness of the solved values) — is **CLOSED by M1 +
  M2 at n = 3, (O3) booking**, at the conditionality displayed there (M1
  unconditional; M2 on (S1)/(S2); M3 for the verdict/box reading). Nothing about the
  MEANING of the identification remains open.
* Its remaining half is the finite transcription-and-correspondence pass itself (map
  each sealed row to its §2.3 family (i)–(vii) member and check entry equality) —
  pure displayed-data comparison, ZERO mathematical content, same status as O-14d.
  Numerics already tie it tightly (§6). The (S1)/(S2) seams are NOT OL-O12-2 residue:
  they are GD-3-full/O-11 property, priced there.

**Recommended DELTA-3 lines (governance, sign-off owed — not executed here):**
(i) the CU §6.1 OB2 eviction, now constructively re-confirmed by M3(a); (ii) D-11
status → PROVED-UNVERIFIED at this unit's displayed scope (M1(a–d)+M1′ unconditional
over the verified O-12 lemma base; M2 conditional on (S1)/(S2); M3 on the displayed
CU/O5triple/D-15 conditionality), hostile pass owed; (iii) OL-O12-2 re-labeled
"data-pass only" per the split above.

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
  conclusion observed exactly where it can be enumerated.
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
theory):** Theorem M1 (a)–(d); Proposition M1′. These are new COMPOSITIONS: O-12's
claim deliberately excluded value semantics; its lemmas do not — this unit is the
place where that composition is written down.
**Proved here, conditional exactly on the displayed seams:** Theorem M2 [(S1) GD-3
full / LIT-3 root leg; (S2) O-11 composition data]; Theorem M3(a) [P(O5t r3) +
(I-1)–(I-3) via CU-7 + five flags + P(O-1thr r4) + TB-CAP D-12r + (E-N) displayed];
M3(b) [the GD/CU dictionary, per the CU §0 registry].
**Findings:** M1′ (the (O2) verdict-row coarseness pins the density-carrying packs to
the re-entrant bookings); the (r1)-as-uniqueness-pivot reading (§3) — the exact
mechanism by which O-12 speaks about real densities; the constructive OB2
re-confirmation (M3(a)).
**Not attempted:** discharging (S1)/(S2) (owned by GD-3-full/O-9/O-11); the OL-O12-2
data pass (finite, engineering); the general-n pack population (O-14d); Lean
artifacts; any O5triple/O-1thr/CU pass.

**Files:** this record = `lean/notes/openmath/D11_massid_phaseB_attempt.md`; falsifier
extension = `verification/openmath/N6-regp_scan_ext2000.py` + results JSON + log. No
other file touched; home-brief pointer updates (O-12's OL-O12-2 line may add "math
half closed at D11 unit") are their owners'.
