# M10-w17ii — Attempt (Fable): resolution of the repaired W17ii clause (ii)

Companion to `M10-w17ii_brief.md` (notation, Lean quotes, and the repair spec
live there). Setting, in one paragraph: for a fixed shape Ŝ and pool q₀ we
have a height domain D ⊆ ℋ, per-height finite events E_h(N) inside a nonempty
finite level-N box of size b(N) ≥ 1, a finite visible set V(N) ⊆ ℋ, an
aggregate event E(N), real weights w(h) and a real value W, subject to the
census laws (L1)–(L6) and the repair fields (R1)–(R4) + guard (G) of the
brief. The obligation is `HasSum (fun h : ↥D => w h) W`.

## 0. Summary of results

The repaired form is resolved COMPLETELY, as a dichotomy in the guard:

- **Theorem A** (§3): clause (ii) is PROVED under the census fields
  (R1)–(R3) plus a *visible-exactness* law (VE) — a per-(Ŝ,q₀)-uniform
  threshold form of the per-height census on the visible set. (R4) is not
  needed. Works for infinite D.
- **Corollary A1** (§4): under guard **(G-fin)** (D finite), (VE) is derivable
  from the existing law (L2) + (R2); hence the (a′)-with-finiteness-tie
  repaired form is PROVED. This un-banks the sorry if E-1 rules (G-fin).
- **Corollary A2** (§4): (VE) also follows from a uniform-threshold
  strengthening of (L2); that variant is PROVED for infinite D.
- **Theorem B** (§5): under guard **(G-sum)** (bare summability tie), clause
  (ii) is FALSE even with ALL census fields (R1)–(R4) present: an explicit
  countermodel ("escaping mass at the visibility frontier") satisfies every
  law with Σ w = 1/2 while W = 1. It is realizable as a full ~30-field
  `RS4Chain` by a 6-field modification of the already-compiled quarantined
  countermodel. So the "summability tie" branch of the repair menu is DEAD
  as literally specced.
- **Finding** (§6): `shdom_no_stray` (R4) is not load-bearing for clause (ii)
  in any provable variant — it is census hygiene only.
- **Faithfulness** (§6): the intended deep instances have infinite semilinear
  height domains (geometric series), so (G-fin) is faithful only to the
  current gate-level corpus; (VE) is the recommended repair shape — it is
  provable at infinite domains and numerically confirmed on a real p-adic
  census (§7, test 2).

All results are (c) claimed new as statements (they are project-specific);
the proof technique of Theorem A is the standard monotone-net/least-upper-
bound argument for unconditional sums of nonnegative reals — no literature
statement matches the census formulation, so nothing here is
LITERATURE-AXIOM-ELIGIBLE.

## 1. Notation and hypotheses

Fix Ŝ ∈ 𝔉 and q₀ ∈ 𝒫 once and for all; suppress both. All thresholds below
may depend on (Ŝ, q₀). From the brief:

- (L1) ∀ N: E(N) = ⋃_{h ∈ V(N)} E_h(N); V(N) finite.
- (L2) ∀ h ∈ D: ∃ N₂(h), ∀ N ≥ N₂(h): w(h)·b(N) = #E_h(N).
- (L3) ∃ N₃, ∀ N ≥ N₃: W·b(N) = #E(N).
- (L4) W ∈ [0,1]. (Not used below; recorded for completeness.)
- (L5), (L6): realization / domain-nonemptiness. (Not used below.)
- (R1) ∀ N, ∀ h ≠ h′ ∈ V(N): E_h(N) ∩ E_{h′}(N) = ∅.
- (R2) ∃ N_v, ∀ N ≥ N_v: V(N) ⊆ D.
- (R3) ∀ h ∈ D: ∃ N₀(h), ∀ N ≥ N₀(h): h ∉ V(N) ⟹ E_h(N) = ∅.
- (R4) ∀ h ∈ D: ∃ N₄(h), ∀ N ≥ N₄(h): E_h(N) ≠ ∅.
- b(N) ≥ 1 for all N (box nonempty and finite).

If (R1) is landed with an eventual threshold instead of ∀N, every use below
is at large N, so nothing changes; same for (L1). Threshold sensitivity is
tracked per step.

Guard variants considered:

- **(G-fin)**: D is finite.
- **(G-sum)**: (w(h))_{h∈D} is summable (some unconditional sum exists).
- **(VE)** *(visible exactness; proposed)*: ∃ N_e, ∀ N ≥ N_e, ∀ h ∈ V(N):
  w(h)·b(N) = #E_h(N).

(VE) strengthens (L2) only in its threshold structure: the census of every
*visible* height is exact at one common level, rather than each height
stabilizing at its own level. It demands nothing of invisible heights.

## 2. Preliminaries

**Lemma 1 (nonnegativity).** For every h ∈ D: w(h) ≥ 0.

*Proof.* Take N := N₂(h). Then w(h) = #E_h(N)/b(N), a quotient of a
nonnegative integer by b(N) ≥ 1 > 0. ∎

**Lemma 2 (partition count).** For every N: #E(N) = Σ_{h ∈ V(N)} #E_h(N).

*Proof.* By (L1), E(N) is the union of the finite family
(E_h(N))_{h ∈ V(N)}; by (R1) the family is pairwise disjoint; the cardinality
of a finite disjoint union is the sum of the cardinalities. ∎
(Lean: `Finset.card_biUnion` with the disjointness hypothesis.)

## 3. Theorem A: visible exactness suffices (infinite D allowed)

**THEOREM A.** Assume (L1), (L2), (L3), (R1), (R2), (R3) and (VE). Then
HasSum (fun h : ↥D => w h) W.

*Proof.* By Lemma 1 the family is nonnegative on D, so the net
F ↦ S_F := Σ_{h∈F} w(h) (F ranging over finite subsets of D, directed by ⊆)
is monotone. For a monotone nonnegative net, HasSum to W is equivalent to:
W is the least upper bound of the set 𝒮 := {S_F : F ⊆ D finite}. We show W
is an upper bound of 𝒮 attained by a member of 𝒮; that is exactly
IsLUB 𝒮 W.

**Step 1 (upper bound: S_F ≤ W for every finite F ⊆ D).**
Fix F ⊆ D finite and choose
N ≥ max( N₃, N_e, max_{h∈F} N₂(h), max_{h∈F} N₀(h) )
(a finite maximum). Then, with every step justified:

  S_F · b(N) = Σ_{h∈F} w(h)·b(N)
             = Σ_{h∈F} #E_h(N)                    [(L2) at each h ∈ F]
             = Σ_{h ∈ F∩V(N)} #E_h(N)             [(R3): h ∈ F∖V(N) ⟹ E_h(N) = ∅]
             ≤ Σ_{h ∈ V(N)} #E_h(N)               [F∩V(N) ⊆ V(N); cards ≥ 0]
             = #E(N)                              [Lemma 2]
             = W · b(N).                          [(L3)]

Dividing by b(N) ≥ 1 > 0: S_F ≤ W. (Uses per-height thresholds only over the
finite F — no uniformity needed here; (VE) not yet used; (R2) not used here.)

**Step 2 (attainment: W ∈ 𝒮).**
Choose N* ≥ max(N₃, N_v, N_e). Then

  W · b(N*) = #E(N*)                              [(L3)]
            = Σ_{h ∈ V(N*)} #E_h(N*)              [Lemma 2]
            = Σ_{h ∈ V(N*)} w(h)·b(N*).           [(VE): all h ∈ V(N*) at once]

Dividing by b(N*) ≥ 1: W = Σ_{h ∈ V(N*)} w(h) = S_{V(N*)}, and by (R2)
V(N*) ⊆ D, so S_{V(N*)} ∈ 𝒮. (If V(N*) = ∅ this reads W = 0 = S_∅ ∈ 𝒮 —
the degenerate case is covered.) This is the ONLY place (VE) is used, and it
is used exactly where a per-height threshold cannot reach: the level N* must
be simultaneously past the stabilization threshold of *every* height V(N*)
declares visible. Theorem B shows this is not a proof artifact.

**Step 3 (conclusion).** By Step 1, W is an upper bound of 𝒮. By Step 2,
W ∈ 𝒮, so every upper bound of 𝒮 is ≥ W. Hence IsLUB 𝒮 W. For a
nonnegative family in ℝ, IsLUB of the finite partial sums at W implies
HasSum (w|_D) W (the monotone net converges to its supremum). ∎

Lean-facing notes (for the eventual TV-H3 unit, not part of the proof):
closing lemma `hasSum_of_isLUB_of_nonneg` (Mathlib,
`Topology/Algebra/InfiniteSum/Order`; verify exact name with
`lean_local_search` at build time); Lemma 2 is `Finset.card_biUnion`; the
finite-subsets-of-a-subtype bookkeeping (F : Finset ↥D vs finite F ⊆ D) is
the usual `Finset.map (Function.Embedding.subtype _)` transport; Step 1's
division is `le_div_iff`-free if stated multiplicatively throughout and
finished with `mul_le_mul_right` on b(N) > 0.

Threshold sensitivity: (R3) was used per-height (weakest form suffices);
(R2) and (VE) were used with per-(Ŝ,q₀) thresholds; (R1)/(L1) were used at
arbitrary large N, so eventual forms are fine. Nothing in the proof needs
thresholds uniform in Ŝ or q₀.

## 4. Corollaries: the provable guard readings

**COROLLARY A1 (the (a′)-finiteness repair: PROVED).** Assume (L1)–(L3),
(R1)–(R3), and (G-fin): D finite. Then HasSum (w|_D) W.

*Proof.* It suffices to derive (VE). Set N_e := max(N_v, max_{h∈D} N₂(h)) —
finite since D is finite. For N ≥ N_e and h ∈ V(N): V(N) ⊆ D by (R2), so
h ∈ D and N ≥ N₂(h), whence w(h)·b(N) = #E_h(N) by (L2). Apply Theorem A. ∎

Remark (Lean economy): with D finite one can bypass the net argument —
index ↥D is a Fintype, `hasSum_fintype` gives HasSum to the finite sum
Σ_{h∈D} w(h), and the Step-1/Step-2 computation at the single level
N := max(N₃, N_v, max_{h∈D} N₂(h), max_{h∈D} N₀(h)) gives
Σ_{h∈D} w(h)·b(N) = Σ_{h∈V(N)} #E_h(N) + 0 = W·b(N) directly
(split D into D∩V(N) and D∖V(N); (R3) kills the second part; (R2) shows the
first part is all of V(N)... more precisely Σ_{h∈D} #E_h(N)
= Σ_{h∈V(N)} #E_h(N) by `Finset.sum_subset` since V(N) ⊆ D and terms outside
V(N) vanish). Every law of the (a′) list except (R4) is load-bearing here:
(R1) for Lemma 2, (R2) for the subset direction, (R3) for the vanishing
direction, (L2)/(L3) as the censuses.

**COROLLARY A2 (uniform-threshold (L2): PROVED, D infinite allowed).**
Replace (L2) by (L2-u): ∃ N₂, ∀ h ∈ D, ∀ N ≥ N₂: w(h)·b(N) = #E_h(N).
Assume (L1), (L2-u), (L3), (R1)–(R3). Then HasSum (w|_D) W.

*Proof.* (VE) holds with N_e := max(N₂, N_v) by (R2). Apply Theorem A
(with (L2) a fortiori from (L2-u)). ∎

(But see §6: (L2-u) over an infinite D is likely NOT faithful to the
intended instances — stabilization levels genuinely grow with height — while
(VE) is; that is why Theorem A is stated from (VE).)

## 5. Theorem B: the bare summability guard is FALSE

**THEOREM B.** There is an instance of the FULL repaired structure — all of
(L1)–(L6), (R1)–(R4), clause (i), and every remaining `RS4Chain` field — in
which (w(h))_{h∈D} is summable (guard (G-sum) holds) and yet
HasSum (w|_D) W fails: the unconditional sum is 1/2 while W = 1.

**The census data.** Heights ℋ := ℕ; domain D := ℕ (all of it);
boxes Box(q₀, N) := Fin(2^N), so b(N) = 2^N ≥ 1; weights and value

  w(h) := 2^{−h−2},   W := 1,   V(N) := {0, 1, …, N}.

Per-height event cards (the events themselves: consecutive intervals in
Fin(2^N), in increasing order of h, so pairwise disjointness is by
construction):

  #E_h(N) =: c_h(N) = ⎧ 2^{N−h−2}   if h ≤ N−2      (the stabilized bulk)
                      ⎨ 2^{N−1}     if h = N−1      (frontier slot 1)
                      ⎪ 1           if h = N        (frontier slot 2)
                      ⎩ 0           if h > N        (invisible)

and E(N) := the full box Fin(2^N). The intervals tile the box exactly:

  Σ_{h=0}^{N} c_h(N) = (2^{N−1} − 1) + 2^{N−1} + 1 = 2^N     (N ≥ 2),

and for the degenerate levels: N = 0 gives c_0(0) = 1 = 2^0; N = 1 gives
c_0(1) = 2^0 = 1 (the h = N−1 slot) plus c_1(1) = 1 (the h = N slot),
total 2 = 2^1. So E(N) = ⋃_{h∈V(N)} E_h(N) exactly, at every N.

**Verification of every law** (machine-checked exactly for N ≤ 40, h ≤ 30;
§7 test 1):

- (L1) grouping: by the tiling above, ∀ N. ✓
- (R1) disjointness: consecutive intervals, ∀ N. ✓
- (L2): for N ≥ N₂(h) := h+2, w(h)·b(N) = 2^{−h−2}·2^N = 2^{N−h−2} = c_h(N). ✓
  (At N = h+1 the law demands nothing — the frontier slot 2^{N−1} ≠ w(h)·2^N
  sits below the threshold.)
- (L3): W·b(N) = 2^N = #E(N), ∀ N (threshold 0). ✓
- (L4): W = 1 ∈ [0,1]. ✓
- (L5): E(N) = full box ≠ ∅, ∀ N, every pool. ✓
- (L6): D = ℕ ≠ ∅. ✓
- (R2): V(N) ⊆ ℕ = D, ∀ N. ✓
- (R3): h > N ⟹ E_h(N) = ∅, ∀ N (stronger than eventual). ✓
- (R4): for N ≥ h+2, c_h(N) = 2^{N−h−2} ≥ 1. ✓
- (G-sum): Σ_{h∈ℕ} 2^{−h−2} = 1/2 (geometric). ✓

**The failure.** HasSum over ↥(Set.univ : Set ℕ) transports to HasSum over ℕ
(`Equiv.Set.univ`); by uniqueness of unconditional sums in ℝ, HasSum (w) W
would force W = 1/2, but W = 1. So clause (ii) fails at this instance. ∎

**Where the mass went.** At every level N, the two frontier heights
{N−1, N} — visible, but not yet past their (L2)-thresholds — carry census
mass (2^{N−1} + 1)/2^N → 1/2. The aggregate census (L3) counts this mass into
W at every level; the per-height censuses never get to keep it, because it
sits at ever-later heights. This is an interchange-of-limits failure
(lim_N Σ_h ≠ Σ_h lim_N), and no amount of per-height eventual laws excludes
it. Consistently with Theorem A, (VE) fails here: h = N ∈ V(N) has
#E_N(N) = 1 ≠ w(N)·2^N = 1/4.

**Realizability as a full `RS4Chain` (the countermodel is not just census
data).** The quarantined compiled countermodel of the unguarded form
(`lean/quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt`, built green
2026-07-30 over the `TV_H1a` carriers) discharges every non-census field of
the ~30-field chain over the degenerate carriers: n = 1, block state types
`Fin 0` (so every state-guarded law — all of the ledger, the measured-family
bundle, the per-pool escape hypotheses — is vacuous or subsingleton-trivial,
and every pool is all-active vacuously), one k = 0 shape, and the
rational-function side discharged FOR REAL (`Rsh = 1` at the unique verdict
multiset, `Rval ≡ 1`, `decidedTotal ≡ 1`). The present countermodel is that
build with exactly seven changes:

1. `negMS.Box := fun _ N => Fin (2^N)` instead of `Fin 1` (`Fintype` ✓,
   `Nonempty` ✓ since 2^N ≥ 1); every other `MeasuredSide` field unchanged.
2. the six shallow fields `shDom/shEvtH/visH/shEvt/shWeightH/WshVal` and
   their four laws replaced by the §5 data (with `WshVal ≡ 1` unchanged).

Box-independence of everything else was verified against the sources:
`PoolHyp` (Defs.lean:533–543), `RegP` (:618), `AVAgree`/`DetHyp` (:556–563),
`LegAgree`, `RS1Bundle`, `LedgerIV`, and `Rsh`/`shConv`/`PolyGeom` mention
states, matrices and rational functions only — never `M.Box`, `M.Hgt`, or the
six shallow carriers. The four shallow laws re-prove as in the table
(`shevt_grouping` from the tiling, `sh_realized` from E(N) = full box,
`shweight_card`/`wshval_card` with the displayed thresholds). Consequence:
once the item-4 census fields land, a (G-sum)-guarded clause (ii) would again
be refutable by a compiled chain of exactly this shape (a TV-H1b′); the
standing coexistence rule (compiled negation must never share a build root
with the sorried universal) would apply to it verbatim.

**Robustness.** The countermodel's weights are strictly positive, every
height is eventually realized, every pool behaves identically, and the
frontier mass 1/2 can be tuned to any σ ∈ (0,1) (scale the bulk slots to
w(h) = (1−σ)·2^{−h−1} and pad the frontier). So no additional hygiene law of
the no-stray/positivity/realization kind can rescue (G-sum); only a law that
constrains the *visible-but-not-yet-exact* census mass (the frontier) can —
(VE) is the minimal such law used by Theorem A, and a quantitative
frontier-domination law (Σ_{h ∈ V(N), N < N₂(h)} #E_h(N) = o(b(N))) would be
an equivalent analytic variant.

## 6. Faithfulness analysis and recommendation (for the E-1 adjudication)

The repair menu's two guard readings, against the corpus:

- **(G-fin) — PROVED (Corollary A1), and exactly matches the executable
  spec.** The blueprint's own provability claim ("clause (ii) then provable
  by the counting squeeze at a fixed pool IF shDom is also tied finite") is
  hereby confirmed, with the exact law inventory: (R1), (R2), (R3), (L2),
  (L3), box-positivity — and NOT (R4). Faithfulness: the n = 2 gate instance
  has D = {0}, and every repair field holds there at threshold 0 ((R1)
  vacuous on the singleton V(N) = {0}; (R2) {0} ⊆ {0}; (R3) premise false;
  (R4) events are the full box; (G-fin) trivially; (VE) at every N since
  w ≡ 1, E_h(N) = full box). So the gate re-discharge (TV-H4) is cheap under
  (G-fin). BUT: the intended deeper instances sum over semilinear height
  domains H(γ) ⊆ Π_i ℕ^{d_i} with geometric series values — genuinely
  infinite domains (the design note's "(XHD-s) SUMS" clause). A (G-fin)
  guard would make `W17ii` unsatisfiable-in-spirit for those instances: the
  field would have to be re-repaired at the first wild/deep instantiation.
- **(G-sum) — REFUTED (Theorem B).** The Q4-preferred "summability guard"
  reading is dead even WITH all four census fields — strictly stronger than
  the earlier finding (which only observed that a bare guard proves ∃-sum,
  not the value): no census field of the (a′) list closes the gap either.
- **(VE) — PROVED (Theorem A), infinite domains allowed; recommended.**
  (VE) is an instance-coherence burden: *a height may be declared visible at
  level N only if its census is already exact at level N.* The instance
  builder controls both `visH` and the census thresholds, so this is a
  design discipline, not an added mathematical assumption — one can always
  take visH(N) := a finite set of heights whose censuses have stabilized by
  N (and grouping/`shEvt` are instance-supplied too). Numerically, the real
  p-adic census this abstracts PASSES (VE) with margin: §7 test 2 shows the
  discriminant-valuation census of monic quadratics is exactly stable at
  every visible height (h ≤ N−1) for p ∈ {2,3,5}, with frontier mass
  p^{1−N}(1+o(1)) → 0 — against the countermodel's frontier mass 1/2, which
  is precisely what (VE) forbids.
- **(R4) `shdom_no_stray`** is not load-bearing for clause (ii) in any
  provable variant (Theorems A, A1, A2 never use it). It can land for census
  hygiene (it does exclude weight-0 junk heights in D), but if field economy
  matters it can be dropped from THIS repair without weakening clause (ii).

Bottom line for the concurrent item-4 execution: land (R1)+(R2)+(R3) as
specced; for the guard, EITHER (G-fin) (sound now, must be revisited for
deep instances) OR the (VE) threshold form (sound permanently); do NOT land
(G-sum) alone — it leaves the clause exactly as false as it is today.

## 7. NUMERIC-TESTS

Tests 1–2 were RUN (2026-07-31, python3, this machine); test 3 is proposed
for the numerics fleet.

**Test 1 (countermodel consistency; RUN — PASS).** Exact integer/Fraction
check of §5: for N ≤ 40, h ≤ 30: (i) Σ_{h≤N} c_h(N) = 2^N (tiling);
(ii) w(h)·2^N = c_h(N) for all h+2 ≤ N ≤ h+12 ((L2) at threshold h+2);
(iii) c_h(N) = 0 for h > N ((R3)); (iv) c_h(N) ≥ 1 for N ≥ h+2 ((R4));
(v) partial sums of w → 1/2 ≠ 1 = W; (vi) (VE) fails at h = N
(c_N(N) = 1 vs w(N)·2^N = 1/4). All PASSED. Refutation criterion: any
failure would invalidate Theorem B's data table.

**Test 2 (visible exactness in a real census; RUN — PASS).** For
p ∈ {2,3,5}, N up to {7,5,4}: enumerate all monic quadratics x²+bx+c over
ℤ/p^N (b(N) = p^{2N} boxes), census E_h(N) := #{(b,c) : v_p(b²−4c) = h}
for h < N, frontier := {v ≥ N}. Check per-height exact stability
(E_h(N+1) = p²·E_h(N), the (VE)/(L2) content with b(N) = p^{2N}) and the
frontier mass. RESULT: every visible height h ≤ N−1 is exactly stable at
every checked level and prime (e.g. p=3: stable h-lists [0], [0,1], [0,1,2],
[0,1,2,3] at N = 1→2, …, 4→5, no unstable heights); frontier mass =
p^{1−N}·(1+o(1)) (e.g. p=3, N=5: 243/59049 ≈ 0.004) → 0. Confirms (VE) is
faithful to a genuine splitting-relevant census and that real frontiers are
null — the countermodel's fat frontier is an artifact the repair must (and
under (VE) does) exclude. Refutation criterion: a visible height whose
census changes proportion between consecutive levels would refute the
(VE)-faithfulness claim.

**Test 3 (PROPOSED — height-decomposed splitting censuses, cubics/quartics).**
With cypari2 (`factorpadic`): for p ∈ {2,3,5,7}, n ∈ {3,4}, N ≤ 5 (n=4 only
p ∈ {2,3}, N ≤ 4 — cost p^{nN} · poly): enumerate monic degree-n f over
ℤ/p^N with a fixed splitting type σ (unramified split/inert/mixed and the
e > 1 types via factorpadic on lifts), height h := v_p(disc f) (and, for the
σ-conditioned refinement, the resolvent valuation). Compute
E_{σ,h}(N)/p^{nN}. CONFIRMS the repaired law shape if: (a) for every
visible h ≤ N − c(σ,p) (some constant margin) the proportion is exactly
stable level-to-level (rational with denominator p^{nN} matching
p^n-rescaling); (b) Σ_{h visible} proportion + frontier = 1 exactly at every
N ((L1)+(R1) partition); (c) partial sums over h approach the σ-density
R_σ(p) computed independently by `verification/quartic_oracle.py`, with
error ≍ frontier mass ≍ p^{−N+O(1)}. REFUTES (i.e. flags the abstraction as
unfaithful) if some visible height's proportion oscillates without
stabilizing (would mean real instances need per-height thresholds ABOVE
visibility — exactly the countermodel shape — and then clause (ii) needs a
frontier-domination law instead of (VE)).

## VERDICT

**PARTIAL — the repaired form is fully resolved as a guard dichotomy, with
the executable branch PROVED:** clause (ii) is PROVED under the (a′) census
fields with the finiteness tie (Corollary A1: (R1)+(R2)+(R3)+(L2)+(L3)+
box-positivity; (R4) unused), and PROVED at infinite height domains under
the visible-exactness threshold form (VE) (Theorem A); it is REFUTED under
the summability tie (Theorem B: explicit escaping-mass chain, all census
fields satisfied, Σw = 1/2 ≠ 1 = W, realizable as a compiled RS4Chain by a
7-field modification of the quarantined TV-H1b build). The E-1 adjudication
must pick (G-fin) or (VE); (G-sum) is dead. Verdict is PARTIAL rather than
PROVED only because the guard choice — hence THE repaired statement — is not
yet frozen at HEAD.
