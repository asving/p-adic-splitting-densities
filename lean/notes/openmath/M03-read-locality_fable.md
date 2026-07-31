# M03-read-locality — attempt (Fable prover, 2026-07-31)

Companion to `M03-read-locality_brief.md`; all notation from there. Target: the
CORRECTED row (queue item 7 form) — `chart_pin` as the exact digit-slot pin,
`child_local` with the added guard `N₀ ≤ N` — at the intended instance: the
canonical run-extension tree models (`canTreeModel` with decode `canDec`) over the
pinned tower (`BridgeReadLocality`: N₀ = 1, F = 𝔽_p, ∀-closed over trees).

**Headline.** `chart_pin` is definitionally true at the intended instance (not open
content). `child_local` is **FALSE at the intended instance** — I give an explicit
countermodel family, rigorous except for ONE witness-existence lemma (W_N) whose
content is the standard OM fact "an Eisenstein-type polynomial realizes its own
root read"; every other step is verified from the definitions. The failure is
structural (the site quantifier ranges over sites deeper than the cutoff), not an
off-by-one: no choice of tree-keyed threshold can repair the statement, because
for every cutoff N the classifier has realized sites reading digits at level N.
What is true — and suffices for every consumer — is a pair of site-threshold-keyed
statements (K1), (K2) given in §5; §6 sketches how they re-derive the note-faithful
consumer `TreeNStable`. §7: the row is not literature-axiom-eligible; the coarse
classical analogue (Krasner-type continuity of factorization) is recalled with its
per-polynomial (not per-tree-uniform) modulus, which is exactly the mathematical
reason the row fails as quantified.

Labels: the refutation is (c) claimed new (about this corpus's specific predicate);
the (K1)/(K2) mathematics is (a) known-in-substance OM theory (the note's own Thm
2.1/D4R.4/TB-CAP content), restated here at the corpus's carrier.

---

## 1. The chart face

At the dressed bridge tower the chart is DEFINED as `bridgeChartStd n M : b ↦ slot
b` (coefficient b's digit-0 slot in the standard layout). The corrected pin
`(χat M h b : ℕ) = b` is `rfl`-genre there, and the block bound `< n` is
`b.isLt` (already compiled: `bridgeChartStd_pin`). So the chart face carries no
open mathematics at the intended instance; the queue-7 repair only makes the row's
statement match the instance it will be discharged at. Nothing further below
concerns `chart_pin`.

## 2. The countermodel family for `child_local`

Fix p (any prime; p = 2 is the minimal case), F = 𝔽_p, n = 2, pol any policy whose
lift rule agrees at the witness node with the corpus's `polOM` realizer (see the
policy-seam remark, §3.4; the intended `canPolicy` is such a policy by design).
Tower: `Tat M := canTreeModelN p 2 M pol` dressed to the standard layout, chart =
`bridgeChartStd`, N₀ = 1 — i.e. the `BridgeReadLocality` instance.

### 2.1 The data

Let N ≥ 1 be arbitrary (this will be the cutoff). Set

    f_N  := X² + p^N          (Eisenstein for N = 1; v_p(a₀) = N, a₁ = 0)
    f'   := X²

and let M := N + 1. Define boxes x_N, x'_N at working level M (standard layout,
n·M = 2(N+1) slots):

    x_N  := digits of f_N :  digit N of coefficient 0 equals 1, all other slots 0;
    x'_N := the zero box   (decode: f').

Then x_N and x'_N agree on the level-<N block (slots c < 2N: all digits of both
coefficients at levels 0…N−1 are 0 in both boxes) — the `child_local` agreement
hypothesis at cutoff N, with M = M' = N + 1 ≥ N ≥ 1 = N₀. The added guard N₀ ≤ N
holds. Decodes: `canDec` reconstructs f_N from x_N and f' from x'_N exactly (§1.1
of the brief; a₀ = Σ_{k<M} digit_k p^k).

### 2.2 The tree

Take Tr := the **empty VTree** V∅: chains = ∅, henV = 0, leafV ≡ none, nsLeaf ≡
False. Every VTree field law holds (all quantifiers over chains are vacuous;
`hleaf` reads `False ↔ False`; checked against the structure fields at
MovesT/Defs.lean:487). Its threshold: thr(V∅, n) = max over the empty set joined
with 1 = **1 ≤ N**. Since `BridgeReadLocality` is ∀-closed over trees, refuting at
V∅ refutes it. (For a refutation at a nonempty realizable tree, see §2.5.)

### 2.3 The site

The site is (o, ν) := (none, ν*_N) — a candidate ROOT child — where ν*_N is the
node recording f_N's genuine root read. Its data (n = 2; two cases by the parity
of N; all Node record laws verified in §3.1):

* stage σ := the corpus's base (root) frame: key Φ = X (degree 1), w = the p-adic
  valuation on constants, K = the prime field, R = the base residual map;
* side: the unique lower-Newton-polygon side of f_N w.r.t. Φ = X, from (slot 0,
  height N) to (slot 2, height 0):
  - N odd: (e, h) = (2, N); N even: (e, h) = (1, N/2);
  - s0 = 0, wSide = 2, Dwidth = 1, u* = 0, γ = 2h (= e·N in both cases);
  - Bézout: N odd: (s, t) = ((1−N)/2, 1); N even: (s, t) = (1, 0);
  - anchor: e·a = s0 − t·γ gives a = −N (N odd), a = 0 (N even);
* pattern: pat 0 = 1, pat(wSide/e) = 1, interior pattern digits 0. Residual
  R_anch = 1 + z (N odd) or 1 + z² (N even);
* ψ := the irreducible factor of R_anch through the residue root: N odd:
  ψ = z + 1, g = 1, μ = 1; N even (p = 2): ψ = z + 1, g = 1, μ = 2 (over odd p,
  1 + z² may be irreducible — then ψ = 1 + z², g = 2, μ = 1; either way legal);
* z̄ := the root of ψ (= −1 for ψ = z + 1); lift := polOM.liftOf ν*_N (set by
  field choice; legal since a policy's lift rule never reads the lift field);
* species := root.

### 2.4 The refutation, given the witness lemma

**Lemma W_N (witness existence — the ONE open step).** With the data of §2.3,

    memCan 2 pol canDec (rootHist ν*_N) x_N,

i.e. `ReadsOf 2 f_N [ν*_N]` ∧ `Realizable [ν*_N]` ∧ `IsCanonPres pol [ν*_N]`.
(Status and clause-by-clause analysis in §3.)

**Theorem R (refutation).** Assume W_N. Then `child_local` (corrected form) fails
at the above instance: with Tr = V∅, cutoff N, levels M = M' = N + 1, site
(none, ν*_N), boxes (x_N, x'_N):

    child(none, ν*_N, x_N)  holds,   child(none, ν*_N, x'_N)  fails,

although x_N and x'_N agree on the first n·N coordinates. Hence
`ReadLocality Tat χat V∅` is false, hence `BridgeReadLocality n p` is false, for
every N-family member; N = 1 already suffices.

*Proof.* The positive leg is W_N through the canonical model's definitional child
display: child(none, ν, x) = ∃ (h : ν.species = root), memCan (rootHist ν h) x,
and ν*_N has root species.

Negative leg — rigorous from the definitions, no witness needed. Suppose
child(none, ν*_N, x'_N). Then ReadsOf 2 f' [ν*_N] holds, so at read i = 0 there
are B, Nd with `IsDevelopment X f' B Nd` and `SideReads ν*_N B Nd Φnext`.
IsDevelopment in the degree-1 key X forces each B_j to be a constant and
f' = Σ_{j<Nd} B_j X^j; comparing coefficient 0 gives **B_0 = C(f'.coeff 0) = 0**.
But SideReads clause (ii) at stride index k = 0 (legal: 0 ≤ wSide/e; pat 0 ≠ 0 is
the Node LAW `hpat0`) demands B_{s0 + e·0} = B_0 ≠ 0 — contradiction. ∎

Remarks. (1) The negative leg uses only: deg Φ = 1 with Φ = X, s0 = 0, and the
record law `hpat0`. (2) The failure survives every tree-keyed weakening of the
guard: the cutoff N was arbitrary, and thr is a function of Tr alone while the
site quantifier is unconstrained — for ANY Tr, taking N := max(thr(Tr,n), N₀) the
family member (ν*_N, x_N, x'_N) violates the row. (3) It equally kills the
on-disk (pre-repair) form, whose quantifiers are weaker only at N < N₀.

### 2.5 Realizable-tree variant (evidence-grade, not fully verified)

If one insists on a tree the tower realizes: at p = 2, n = 2 take Tr_inert :=
the one-chain tree of an inert quadratic (root read of slope-0 with irreducible
residual, immediate τ-irr halt) — the corpus's own non-vacuity witness node (U31)
is exactly this read. Its chain's side line has intercept 0, so Nshape = 1 and
siteLevel = 1, giving thr = 1; the same (ν*_1, x_1, x'_1) then violates the row at
N = 1. I have not machine-checked Nshape/siteLevel arithmetic for that chain; the
V∅ instance of §2.2 needs no such check and already refutes the ∀-closed target.

---

## 3. Status of Lemma W_N (clause-by-clause)

W_N asserts the three memCan conjuncts for the one-node history [ν*_N] at x_N
(f := f_N). Everything below §3.2 is verified rigorously here; §3.3 lists the
residue: four sub-checks internal to the corpus's base-stage bookkeeping, each a
finite computation of the U31-gate genre, plus one policy seam. Mathematically
each says "the base frame's residual apparatus reports the standard Newton-polygon
data of X² + p^N", i.e. standard OM facts; they are open only as corpus-internal
verifications.

### 3.1 Node record laws (rigorous)

he/hh: e, h ≥ 1 ✓. hcop: gcd(2, N) = 1 for N odd; gcd(1, N/2) = 1 ✓. hbez +
hbezCanon: as listed (§2.3), unique by 0 ≤ t < e ✓. hg, hμ ≥ 1 ✓. hEdvd: e ∣ 2 ✓.
hDwidth: Dwidth = 1 = deg X ✓. hψmonic/hψdeg/hψirr ✓ (degree-1, or the recorded
irreducible factor). hRanch: R_anch = Σ_{k≤wSide/e} pat(k) z^k matches §2.3 ✓.
hpat0/hpatTop: pat 0 = pat top = 1 ≠ 0 ✓. hAnchor: e·a = s0 − t·γ checked in §2.3
✓. hOrd: ord_ψ R_anch = μ ✓ (direct: ord_{z+1}(1+z) = 1; ord_{z+1}(1+z²) = 2 over
𝔽_2). hzbarRoot: ψ(z̄) = 0 ✓. hLineU: choose the line through
((s0+wSide)·Dwidth, u*) = (2, 0) with the slope pinned below ✓ (a Line value
exists for any pinned point and slope). Species root: hspecInc/hspecRec vacuous ✓.

### 3.2 History-level conjuncts (rigorous)

HistoryCoherent [ν*_N]: clause 1: deg Φ = 1 ✓. Clause 2 (slope law, i = 0,
STR₀ = 1): slope·(e·1·1) = h — pins slope = h/e, consistent with hLineU's point ✓.
Clause 3 (γ-tie): γ = e·(1·u*) + (s0+wSide)·h = 0 + 2h ✓ matches §2.3. Clause 4:
vacuous (one node). **Realizable [ν*_N]**: quantifies over adjacent pairs —
vacuous ✓. **IsCanonPres pol [ν*_N]**: lift = pol.liftOf ν*_N — holds by the field
choice IF pol.liftOf ν*_N = polOM.liftOf ν*_N (seam, §3.4); z̄ = canonRoot: ψ has
the single root −1, so the enumeration-least root is −1 = z̄ ✓.

ReadsOf's first three conjuncts: f_N monic, degree 2 ✓; coherence above ✓. The
development at read 0: B := the X-adic coefficients of f_N (B_0 = p^N, B_1 = 0,
B_2 = 1, Nd = 3) — IsDevelopment ✓. SideReads clause (i): nonzero slots {0, 2};
values e·w(B_j) + j·h: at j = 0: e·N = γ ✓ equality, and 0 = s0 + e·0 is a stride
slot with pat 0 ≠ 0 ✓; at j = 2: e·0 + 2h = γ ✓ equality at stride slot
2 = s0 + e·(wSide/e), pat top ≠ 0 ✓; no other nonzero slots, so "equality only at
recorded stride digits" ✓. Clause (ii) valuation pins: as just computed, both
exact ✓. Clause (iii) second half (ord_ψ R_anch = μ) ✓ = hOrd.

### 3.3 The open sub-checks (explicit open lemmas)

* **W-a (clause (ii), residual display).** The base residual of B_0 = p^N is the
  monomial unit with scalar pat 0 = 1 at the forced position, and likewise for
  B_2 = 1: R(p^N) = C(1)·T(−σ.t·wPrev(p^N)), R(1) = C(1)·T(0)-form. A finite
  normalization computation at the corpus's base stage (the same clause the U31
  inert gate discharged at its node).
* **W-b (clause (iii), anchor).** HasAnchorK (σ.R f_N) a R_anch at the recorded
  a — the frame residual of f_N is R_anch anchored at a. Same genre as W-a.
* **W-c (clause (iv), landing).** LandingKey ν*_N Φnext with the standard-lift
  witness tt_0 := p^N: Φnext = Φ^{e·g} + tt_0·Φ^0 requires w(tt_0) = h·(g−0) and
  the residual digit condition; for N odd this gives Φnext = X² + p^N = f_N
  itself (w(p^N) = N = h·g needs h = N, g = 1 ✓). For N even (e = 1, g per §2.3)
  the analogous lift exists; I did not push the arithmetic through both parities.
* **W-d (clause (vi), vertex read-off).** For every development Bh of f_N in
  Φnext: digPrime z̄ (Bh μ) = vtx(ν*_N). With Φnext = f_N (N odd) the development
  is Bh = (0, 1): the check is digPrime z̄ (1) = vtx — one evaluation of the
  corpus's D.8 vertex normalization at the recorded data.

Evidence that W-a…W-d are dischargeable: (α) the identical clause bundle is
PROVED in-corpus at the n = 2 inert root node (HC2 `gate_readsOf_inert2` — same
base stage, slope-0 side); (β) the ramified stage/transition apparatus at e = 2
is now constructed (MovesD/R7_ramifiedForge.lean, via the proved S9 transition
capstone); (γ) mathematically each says the base frame reports the textbook
polygon data of X² + p^N — if any failed for structural (not bookkeeping) reasons,
the base stage would misreport Eisenstein polynomials wholesale, contradicting
(α)'s calibration. I could not complete them here because they require unfolding
the base stage's R/wPrev/digPrime normalization conventions, which this unit did
not have the budget to re-derive; they are honest open sub-lemmas.

### 3.4 The policy seam (recorded, not a gap in the mathematics)

memCan at policy pol requires BOTH lift pins: SideReads (v) pins
lift = polOM.liftOf ν (the corpus's fixed realizer), IsCanon pins
lift = pol.liftOf ν. So memCan is satisfiable at ν only if the two policies agree
there. At pol := `canPolicy` (opaque in Lean) this is unverifiable today — which
also means **no compiled refutation of `BridgeReadLocality` is currently possible**
(consistent with the corpus's fence discipline on sorried universals); the
refutation is at the intended semantics, where canPolicy is a realizer of the same
lift specification as polOM (the blueprint's ratified deviation note: "every
spec-realizer produces identical graded data"). A compiled countermodel IS
available one level up, at `MovesT.ReadLocality` over the same canonical model
with pol := polOM itself (then IsCanon = clause (v), no seam) — W_N is the only
missing ingredient there too.

### 3.5 Robustness dichotomy

Even if W_N failed at the corpus's exact base stage for every choice of ν*_N's
free fields, the row would not be saved: then NO node is a realized root child at
x_N (every realized root node at f_N must have s0 = 0 and hence dies at x'_N by
the §2.4 argument — the forced-side computation: equality slots of any support
line on {(0,N), (2,0)} lie in {0, 2}, and s0 = 2 is excluded since it would force
the non-stride slot 0 to violate clause (i); width-0 monic-slot reads at s0 = 2
survive clause (i) only when e·N ≥ 2h, but they are children at BOTH boxes and so
neither witness nor obstruct). In that horn, the canonical tower fails its own
covering duty `KBTotTower.root_total` (MovesT/Defs.lean:941: a repeated factor of
the reduction — here X² — forces a root child) at x_N, so `treeN_stable`'s premise
row is uninstantiable at the intended tower and the ReadLocality row is moot for
its only consumer. Either horn ends the row as stated. (This dichotomy is
informal: `root_total`'s ∃ν is interface-level; the horn analysis pins its witness
only at the canonical model's semantics.)

---

## 4. Why the row was over-quantified (diagnosis)

The site quantifier "∀ (o, ν)" was chosen (recorded as TV-B2's "option α") because
the fiber-identity backward direction (`fiberAt` clause (i): every pruned member
at x' is a tree chain) mentions arbitrary histories. But at the canonical model,
membership of a DEEP history is genuinely not a level-N event — its run pins exact
valuations at heights ≥ N (§2). The note never claims option α: its threshold is a
bound on the data OF THE TREE'S OWN SITES ("per site … per branch … per leaf");
stray histories are to be excluded by a first-deviation argument (§6), not by
unbounded-site locality. So the corrected row still transcribes strictly more than
the note's Thm 2.1/D4R.4/TB-CAP inputs, and the excess is exactly what is false.

---

## 5. The repaired kernel pair (reduction — what should replace the row)

Both statements below are OPEN (they are the genuine Thm 2.1/D4R.4/TB-CAP
content); the reduction claim is that they are (i) true at the intended semantics,
(ii) sufficient for every current consumer (§6), and (iii) immune to §2's
countermodel because their thresholds are keyed to the SITE, not the tree.

Define the **read ceiling** of a history H, ceil(H) ∈ ℕ: the least bound such
that every recorded read's constrained heights lie strictly below it — concretely,
in corpus vocabulary, ceil(H) := (shapeOfH H n).Nshape ⊔ (shapeOfH H n).NPband n
(1 + the largest side-line intercept / constrained band level over H's reads; for
the chains of a tree Tr this is ≤ thr(Tr, n) by definition of thr).

**(K1) ReadsOfLocal — history-keyed run locality.** For every history H with
ceil(H) ≤ N, all levels M, M' ≥ max(N, N₀), and boxes x (level M), x' (level M')
agreeing on the level-<N block:

    ReadsOf n (canDec x) H  ↔  ReadsOf n (canDec x') H,

and hence memCan(H, x) ↔ memCan(H, x') (the other two conjuncts are box-free —
checked rigorously: `Realizable` and `IsCanonPres` read only H). Child form: for
sites (o, ν) with ceil(o ⌢ ν) ≤ N, child(o, ν, x) ↔ child(o, ν, x').

Why true (sketch, at the intended semantics): every box-dependent clause of
SideReads at read i constrains f's development coefficients B_j through (a) exact
valuation pins e·w(B_j) + j·h = γ at stride slots — heights (γ − j·h)/e ≤ the side
line's intercept < Nshape(H) ≤ N; (b) one-sided bounds γ ≤ e·w(B_j) + j·h — i.e.
"valuation ≥ β" with β below the same intercept bound; (c) residual-digit reads AT
those pinned heights (< N); (d) the anchor/vertex displays (iii)/(vi), which are
functions of the digits read in (a)–(c). Through the graded-presentation
dictionary ("a valuation clause w(B) ≥ β is the literal zero system of the tower
coordinates of height < β" — the corpus's `downsets_literal` seed law, i.e. the
note's C.1.5/LST layer, with its chart-coverage proviso "the box records every
constrained coordinate", which is exactly N ≥ ceil(H)), each clause is a finite
Boolean combination of conditions on box digits at levels < N. Two boxes agreeing
there satisfy the same combination. The open content is precisely the dictionary
step (c)—(d): the corpus's residual maps must be shown to read only the recorded
heights. This is the note's declared "per branch: D4R.4's exact level-N
realization" input, now stated at its natural carrier.

**(K2) Window closure at decided states (stray exclusion).** Let Tr be a VTree
with no ns-leaves, N ≥ max(thr(Tr, n), N₀), x a level-M box (M ≥ N) in Tr's fiber,
and x' =_{n·N} x. Then at every tree state o ∈ {none} ∪ {some H : H ∈ Tr.chains}:

    { ν : child(o, ν, x) } = { ν : child(o, ν, x') }.

(Deep candidate children are excluded at BOTH boxes, bounded ones transfer by
(K1).) Why true (sketch): since x fibers Tr and Tr is complete and decided, the
window polygon at each tree state closes at heights < thr(Tr, n): all its vertices
are pinned by level-<N digits (points of height < N are pinned exactly; points of
height ≥ N stay ≥ N at both boxes, hence above the closed hull). A child at x'
whose read data exceed level N would need a polygon vertex of the state's window
at height ≥ N, which the transferred hull excludes; children within level N
transfer by (K1). The open content: the same dictionary step as (K1), plus the
per-leaf cap ("TB-CAP's level-N_V cylinders") and the per-site joint-cell literal
system ("its B(iii) level") — the note's other two declared inputs.

Countermodel compatibility check: §2's witness site (none, ν*_N) has
ceil([ν*_N]) = N + 1 > N (its side line has intercept N), so (K1) does not apply
to it — and x_N is in NO decided fiber whose threshold is ≤ N with a root state
covering that window (its reduction X² opens a window whose sides live at height
N), so (K2) does not apply either. The repair is exactly the guard the
countermodel exploits.

## 6. (K1) + (K2) + chart ⇒ TreeNStable (derivation sketch)

Target (`TreeNStable`): Tr decided (no ns-leaves), N ≥ max(thr, N₀), M ≥ N,
x =_{n·N} x' at the SAME level M: fiberAt(x) ↔ fiberAt(x'). By symmetry assume
fiberAt(x); check the six fiber clauses at x'.

* Reduction data: redPoly χ x = redPoly χ x' (chart_pin: charts read level-0
  slots ⊆ the agreed block) — hence clause (iii) (hen payload) and the clause-(vi)
  track-degree identity transfer verbatim.
* Clause (i) forward (chains are pruned members at x'): for H ∈ Tr.chains,
  ceil(H) ≤ thr ≤ N, so memCan(H, x') by (K1); prefix non-halting: IrrHalts is
  box-free; ¬NsHalts(some H', x') for proper prefixes H' needs a child at x' —
  take H'’s tree child (Tr complete: a non-maximal chain has an immediate
  extension in Tr.chains), a child at x by fiberAt(x) + mem_snoc, transferred to
  x' by (K1) (its ceiling is ≤ thr).
* Clause (i) backward (no strays at x'): suppose PrunedMem(H, x') with H ∉
  Tr.chains. Walk H against Tr: let o be the last state along H that is a tree
  state ({none} ∪ chains — none qualifies, so o exists), ν the next node of H.
  child(o, ν, x') holds (mem of the prefix + mem_snoc/mem_single). By (K2) at o,
  child(o, ν, x); the prefix o ⌢ ν is a pruned member at x (its proper prefixes
  are prefixes of tree chains or of H, non-halted at x by fiberAt(x) resp. by
  (K2)/(K1) transfer of non-halting from x'); so o ⌢ ν ∈ Tr.chains by fiberAt(x)
  clause (i) — contradicting the choice of o. 
* Clause (ii) (leaf verdicts): irr legs are box-free; ns legs are excluded by
  decidedness. Clause (iv) (interior non-halting): as in (i) forward. Clause (v)
  (mass of typemult): box-free given (ii)/(iii).

Gaps in this sketch, stated: the walk in (i)-backward needs prefix-closure
bookkeeping (finiteness of H, existence of the last tree state) — routine; the
non-halting transfers invoke (K1)/(K2) at prefixes, which needs ceil ≤ thr for
tree prefixes — true by thr's definition. I consider the sketch sound at the
informal-rigorous level; it is the note's own architecture ("per site / per
branch / per leaf"), and it shows option-α locality was never needed.

## 7. Literature

* **Not literature-axiom-eligible.** The row as stated is false at its intended
  instance (§2), so no faithful citation can exist. Moreover even (K1)/(K2)
  quantify over the corpus's own run predicate (SideReads' six clauses, the
  canonical-presentation class, the recorded-data node carrier), which no
  published statement matches; a literature axiom here would be unfaithful.
* **The coarse classical analogue (known).** Krasner-type continuity of
  factorization: for monic separable f ∈ ℤ_p[X] of degree n with d := v_p(disc f),
  every monic g of degree n with g ≡ f mod p^{2d+1} has the same factorization
  type over ℚ_p (degree-matched bijection of irreducible factors, corresponding
  factors generating isomorphic extensions; via Krasner's lemma applied to the
  roots, ‖g − f‖ < p^{−2d} forcing root-wise proximity below the minimal root
  distance). Attribution: folklore corollary of Krasner's lemma; effective forms
  appear in the polynomial-factorization literature over local fields (e.g.
  Ford–Pauli–Roblot, J. Théor. Nombres Bordeaux 14 (2002); Pauli's factoring
  papers; and as "Okutsu equivalence"/type-stability statements in
  Guàrdia–Montes–Nart, Trans. AMS 364 (2012) — the project's pinned external, cf.
  docs/GMN_citations.md). **Exact theorem numbers not verified here — flagged for
  lookup before any citation-grade use.** Note the modulus 2d + 1 is
  PER-POLYNOMIAL and unbounded over any level cylinder — the precise classical
  reflection of why a tree-uniform threshold over all sites (option α) fails,
  and consistent with the per-tree threshold thr(Tr) sufficing once the sites are
  the tree's own (v_p(disc) is bounded on a decided fiber).

---

VERDICT: REFUTED (child_local face, corrected form, at the intended canonical
instance) — modulo the single explicitly-stated witness lemma W_N (§3; standard
OM content, four base-stage bookkeeping sub-checks W-a…W-d open, robustness
dichotomy §3.5); chart_pin face: true by construction at the intended instance
(no open content); honest content REDUCED to the site-keyed pair (K1) + (K2)
(§5), which re-derives the note-faithful consumer TreeNStable (§6).

## NUMERIC-TESTS

All runnable with sympy alone (1–2 uses cypari2 for cross-checks); each test
names its confirming/refuting output.

1. **Countermodel family — polygon-side discontinuity (sympy, minutes).**
   For p ∈ {2, 3, 5}, n ∈ {2, 3}, N ∈ {1, 2, 3, 4}: set f = X^n + p^N,
   f' = X^n, M = N + 1. (a) Assert the boxes agree at levels < N: compare the
   digit vectors of all coefficients mod p^N — expect equality. (b) Compute the
   lower Newton polygon of f w.r.t. the key X (points (j, v_p(coeff_j))): expect
   the single side (0, N)–(n, 0), i.e. recorded data e = n/gcd(n,N),
   h = N/gcd(n,N), s0 = 0, wSide = n, pat 0 ≠ 0. (c) For f': assert coeff_0 = 0,
   so the clause-(ii) slot-0 pin B_0 ≠ 0 fails. CONFIRMS the refutation's
   arithmetic core if (a)–(c) all hold for every tuple; any tuple violating (b)
   (e.g. a second side) REFUTES my side bookkeeping and the witness data of §2.3
   must be re-derived.
2. **No uniform threshold (cypari2, ~200 samples/prime).** For p ∈ {2, 3},
   n ∈ {2, 3}: for K = 1…6 sample pairs (f, g) with g ≡ f mod p^K but
   g ≠ f mod p^{K+1}, f random monic with v_p(disc f) ≥ K (e.g. f = X^n + p^a·u
   families): count pairs where `factorpadic(f)` and `factorpadic(g)` have
   different (e, f)-multisets. CONFIRMS if for every K there exist mismatching
   pairs (no level-K cylinder determines the type globally — the option-α failure
   at every cutoff); REFUTES (and would resurrect a uniform row) if mismatches
   stop above some K independent of the sample's disc valuation.
3. **Krasner bound sanity (cypari2).** Same samples: verify ZERO mismatches when
   additionally 2·v_p(disc f) < K. Confirms the per-polynomial modulus statement
   of §7 (and calibrates test 2's sampler).
4. **Site-keyed locality (K1) probe (sympy).** For p = 2, n = 2: take the
   Eisenstein site's data at N = 1 (side (0,1)–(2,0)); for 500 random f with
   v_2(f(0)) = 1 exactly and random digits at levels 2…8: assert the root read's
   realized side data (polygon side, residual pattern at the pinned heights) are
   invariant under changing digits at levels ≥ 2 (= ceil of the 1-node history).
   CONFIRMS (K1)'s guard placement at reads of ceiling 2; a dependence on level
   ≥ 2 digits would refute (K1) as guarded and demand a larger ceiling.
5. **Fiber stability with tree-keyed threshold (K2)/TreeNStable probe (cypari2,
   p = 2, n = 2, exhaustive to level 6 — 4096 boxes).** Group all monic X² + aX
   + b with a, b ranging over residues mod 2^6 by their splitting data
   (factorpadic: multiset of (e, f, deg)) and by d := v_2(disc). For the decided
   sub-family d ≤ 2: assert the splitting data are constant on level-(d+1)
   cylinders (proxy for thr). For the family with all a ≡ 0, b ≡ 0 mod 2^k:
   exhibit that splitting data are NOT constant on level-k cylinders. CONFIRMS
   the two-sided picture: per-tree threshold suffices on decided fibers, no
   global per-level threshold exists.
