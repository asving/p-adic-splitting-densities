# O4T pass 4 — ACCEPTANCE PASS over rev 4 (hostile, fresh context; Fable, 2026-07-31)

**Input read:** `lean/notes/openmath/O4T_phaseB_verifybrief_rev4.md` ONLY (standalone;
no prior pass reports consulted). **Charge:** the full acceptance audit — classifier
policy, certificate stability, order arithmetic at wild corners, both (CEIL) chains,
envelope with the unbounded hypothesis, the THREE-import external count, the corrected
(I1) criterion, the bracket forms — plus all 12 §7 attack charges, plus a full harness
re-run. Protocol: two-class (critical error / justification gap), quote-and-classify,
fix nothing.

**VERDICT: SOUND** (zero critical errors, zero justification gaps; three
observation-level notes, none touching any displayed statement or proof step).

Standalone-readability check first: the brief passes — every consumed hypothesis is
displayed in-document (I-TAIL, M05 Lemmas B/D as named quoted imports; the eleven
classical Facts with pins; (AGR) as an explicit displayed seam), and no §§1–3 step
required repository context to verify.

---

## 1. Line-by-line verification of the mathematical core

### §1 setting

* **(D)** `v_p(disc f) = 2·Σ_{i<j} v(α_i − α_j)`: correct for monic integral-root `f`
  from `disc = ∏_{i<j}(α_i − α_j)²` + `v`-additivity. PASS.
* **(K)** `U^K_N = {a : v_p(disc f_a) ≥ ⌈N/2⌉}`: re-derived from `c^K`'s definition
  alone — decided iff some lift has `2v+1 ≤ N`, i.e. `v ≤ ⌊(N−1)/2⌋`; undecided iff
  every lift has `v ≥ ⌊(N−1)/2⌋ + 1 = ⌈N/2⌉` (checked at both parities); the event is
  level-`⌈N/2⌉`-measurable (`disc mod p^m` is a `Z`-polynomial function of
  `a mod p^m`), so "some lift"/"every lift" agree. Confirms the rev-4 claim that the
  (K) identity needs NO external input (Lemma D underwrites only soundness and
  `U^sem ⊆ U^K`). PASS.

### §2 skeleton

* **Lemma A / TR-0 / FLOOR**: elementary and correct as displayed; the
  sufficiency-only direction discipline is honored (nothing downstream uses a
  converse). FLOOR's dependence on `c^sem` being a well-defined function (M05 Lemma B)
  is now correctly priced in the three-import count. PASS.
* **TR-Q with UNBOUNDEDNESS (§7 charge 7)**: `Γ⁻(N) := min{v : Γ(v) > N}` is
  well-defined exactly because `Γ(v) → ∞` makes the set nonempty; minimality gives
  `v < Γ⁻(N) ⇒ Γ(v) ≤ N` (no off-by-one: the contradiction step needs precisely
  `N ≥ Γ(v)`, which this supplies); divergence re-derived (`N ≥ Γ(v₀)` + monotonicity
  ⇒ `Γ⁻(N) > v₀`). The constant-`Γ` counterexample is excluded by the HYPOTHESIS, not
  by prose. Both consumers instantiate unbounded majorants: N3-ENV's `Γ(v) = v+1`
  (with `Γ⁻(N) = N`, re-checked), TR-OM's OL2 shape displays unboundedness. PASS.

### §3.2 policy + the (C1)-redundancy note (§7 charge 12(iii))

The pinned walk is well-posed: "resolved" (`y_i < k`) is decidable from digits `< k`
and then exact; all reads are class reads. The rev-4 note's content re-derived: every
resolved point has height `< k`, so `H_res(i) < k` by convexity, and any unresolved
point (height `≥ k`) is strictly above — (C1) can indeed never fail; the operative
gate is `x₀ ≤ 1` + (C2). Confirmed OBSERVATION-only: the policy text, (CEIL), and the
harness-tested walk are unchanged (the note is appended after the walk, policy
byte-stable as claimed). PASS.

A stronger fact, verified because CERT and the case-(b) shortcut lean on it: at EVERY
scan level (not just the certify level), the lower hull of the full `[x₀, n]` point
set equals `H_res` in every completion — unresolved points sit strictly above the
hull of the resolved subset, and adding points above a lower hull does not change it.
This closes both "is `s_r` the TRUE right-slope" questions below.

### §3.3 (I1) with the corrected `> 0` criterion (§7 charge 12(i))

`ᾱ = r ⟺ α − r ∈ 𝔪 ⟺ v(α − r) > 0` is correct (`𝔪` = the positive-valuation
ideal of the integral closure); the root count = multiplicity of `r` in `f̄`. The
retired `≥ 1` form is indeed false (the brief's own `x² − p` refutation checks:
`v(±√p − 0) = 1/2`). Grep-level audit of consumption: the case (a)/(b) chains use
only `b_2 > λ_prev`, sortedness, integrality of the roots (`b_j ≥ 0`), and
ultrametric identities — no step anywhere uses `b_j ≥ 1`. PASS.

### Lemma RES (§7 charge 5)

Both unique-minimality claims re-derived:
* `in_w(g_<) = x̄^{deg}`: coefficients of `g_<` satisfy `v(c_j) > (deg−j)·h` (roots of
  valuation `> h`), so every non-leading term has `w`-weight `> deg·h`.
* `in_w(g_>) = c̄₀·π̄^{v(c₀)}`: `v(c_0) = Σ v(roots)` exactly; for `j ≥ 1`,
  `v(c_j) > v(c_0) − jh` (any `j` omitted roots have total valuation `< jh`), so the
  constant term is the unique `w`-minimal one.
Multiplicativity of initial forms is Fact GRD (displayed, pinned). The on-line digits
of `g` are then the on-line digits of `g_h` up to one monomial (scalar + lattice
shift), which are the reduced coefficients of `G` — `R = c̄·Ḡ`, `c̄ ∈ F_p^×`. PASS.

### Corollary RES-0 and Lemma REC (§7 charge 3)

RES-0: side roots have `v(β/p^h) = 0` exactly, so `G(0) = ±∏(units)` is a unit (Fact
UCT), `Ḡ(0) ≠ 0`, `R(0) = c̄·Ḡ(0) ≠ 0`; the independent hull-vertex/no-cancellation
confirmation also checks. REC's three-case split re-verified with `z₀ ≠ 0` threaded:
`v(α−c) < h` (minimum uniquely attained below `h`); `v(α−c) = h`, other residual
class (`(α−c)/p^h − z₀` a unit); `v(α−c) > h` (steeper side — here `z₀ ≠ 0` is
load-bearing: `v(α−c′) = min(v(α−c), h) = h` uniquely attained). Cases exhaustive;
exactly the `m′` SIDE(ii) roots satisfy `v(α−c′) > h`; (I1) restored. PASS.

### Lemma SIDE

(i): denominator-`e` valuation forces `e | e(Q_p(β))` and `[Q_p(β):Q_p] ≥ e` (Fact
EF); the degree-`e` slope factor containing `β` is then its minimal polynomial —
irreducible, type `(e,1)`. (ii): Hensel bookkeeping via HRG re-checked, including
that a simple `ψ_i` gives an irreducible `G_i` with unramified degree-`d′` root field
and `Q_p(p^h u) = Q_p(u)` for `h ∈ Z`. (Fact HEN is stated for two coprime factors
and used for `∏ G_i` — routine iteration; see Note N2.) PASS.

### Lemma CERT (§7 charges 1 and 11(iii))

(i) The index-range reading closes: the proof uses ONLY the hull of the `[x₀, n]`
point set, true in every completion by the strictly-above argument (resolved values
persist and unresolved status persists under any completion of the read digits —
this is the certificate-STABILITY content, verified). Index 0 enters exclusively
through (C2)/(ii). PASS.
(ii) The completion quantifier attack: in every completion, `v(g_0) ≥ k > y_1 + s_r`,
so the full true hull has the vertex at `(1, y_1)` (left slope `v(g_0) − y_1 > s_r` =
right slope), the leftmost side has length 1 and integer slope (heights integral) —
including `g_0 = 0`, read as height `+∞` per Fact NP's convention, where the single
`v(β) > s_r` root is `β = 0 ∈ Q_p` itself; `s_r` computed from `H_res` IS the true
right-slope by the every-scan-level hull identity above. The one-root set is
Galois-stable (Galois preserves `v`, permutes the valuation class), so rational
(Fact DES). `k > y_1 + λ_prev` puts it in the current cluster. PASS.

### Theorem N3: both (CEIL) chains (§7 charges 2, 6) and wild corners

Order arithmetic re-derived from scratch, including the exactness inputs
`y(0) = Σ_j b_j` and `y(1) = Σ_{j≥2} b_j` at a `(1, y(1))`-vertex (elementary
symmetric functions; unique minimal term iff `b_1 > b_2`).

* **Case (a) `b_1 = b_2`** (all `b_j` finite — a `b_1 = ∞` forces case (b)): earliest
  possible fire is `k = y(0)+1` with `x₀ = 0` (index 0 resolves exactly there, Fact NP
  no-cancellation); the shortcut cannot pre-empt (firing needs `v(g_0) ≥ k` and
  CERT(ii) would force `b_1 > b_2`). Chain:
  `k − 1 = y(0) = b_1 + b_2 + Σ_{j≥3} b_j ≤ 2δ_{12} + Σ_{j≥3} δ_{2j} ≤ v` — each step
  checked (`δ_{12} ≥ min(b_1,b_2)`; `δ_{2j} ≥ min(b_2,b_j) = b_j` by sortedness; all
  `δ ≥ 0` by integrality; the `δ`'s are `c`-independent, so the bound holds at every
  recursion depth). PASS.
* **Case (b) `b_1 > b_2`**: length-1 leftmost side gives `b_1 ∈ Z ∪ {∞}`; the
  shortcut fires at `k = y(1) + ⌊b_2⌋ + 1`: index 1 resolved (`⌊b_2⌋ ≥ 0`), index 0
  unresolved (`y(0) = y(1) + b_1 ≥ k` since `b_1 ∈ Z, b_1 > b_2 ⇒ b_1 ≥ ⌊b_2⌋+1`;
  `b_1 = ∞`/`g_0 = 0` corner: never resolves — checked separately on the concrete
  instance `f = x³ − px`, where `b_2 = 1/2` is also the fractional corner: `k = 2`,
  verdict `(1,1)+(2,1)`, `k ≤ v+1` at `p = 2` and odd `p` both), `k > y_1 + s_r`
  (`⌊b_2⌋+1 > b_2 ≥ s_r`, with `s_r = b_2` by the true-hull identity — the fractional
  case `b_2 ∉ Z` requires `b_2 = b_3 > λ_prev`, i.e. `m = 3`, and the side of length
  ≥ 2 realizes slope `b_2` exactly), `k > y_1 + λ_prev` (`λ_prev ∈ Z`, `b_2 > λ_prev
  ⇒ ⌊b_2⌋ ≥ λ_prev`). Chain:
  `k − 1 = y(1) + ⌊b_2⌋ ≤ 2b_2 + Σ_{j≥3} b_j ≤ 2δ_{12} + Σ_{j≥3} δ_{2j} ≤ v`, with
  `δ_{12} = b_2` EXACT by strict ultrametric (also at `b_1 = ∞`, where `α_1 = c`).
  PASS.
* **`e·d ≥ 4` exclusion (§7 charge 4)**: a repeated residual needs residual degree
  `d ≥ 2`; with `e ≥ 2` the side length `e·d ≥ 4 > n` — impossible at `n ≤ 3`,
  including wild `p` and refined clusters (the argument is characteristic-free and
  `λ_prev`-independent). Recursion shifts always come from `e = 1` sides, so
  `λ_prev ∈ Z` throughout — consumed by case (b) above. PASS.
* **Wild corners probed by hand**: `x² − 2` (`k = 2 ≤ v+1 = 4`, `(2,1)`),
  `x² + 2x + 4` (case (a), `k = 3 = v+1` tight, `(1,2)`), `x² + 2x + 8` (case (b)
  shortcut, `k = 3 = v+1` tight, split — cross-checked `−7 ∈ (Q_2^×)²`),
  `x³ − 2x` at `p = 2` (fractional + infinite corner simultaneously). All conform.
  PASS.
* **Every-lift separability chain (§7 charge 11(ii))**: each certified factor is a
  monic irreducible factor of ANY completion `g` (the certificates quantify over
  completions); root groups pairwise disjoint ACROSS depths (distinct step-0
  residues / side valuations / residual classes / REC's refined-cluster count);
  degrees sum to `n` at every node of the recursion (NP side lengths = root counts
  with multiplicity; residual degrees partition side length); pairwise distinct
  irreducibles ⇒ coprime ⇒ their product is a monic degree-`n` divisor of `g`, hence
  `= g`; Fact SEP gives `n` distinct roots. No circularity: no certification step
  presupposes `g` separable (checked per lemma — SIDE(i) is a degree argument,
  SIDE(ii)/HRG and step 0 are Hensel bookkeeping, CERT(ii)'s side has length 1). PASS.
* Termination (`λ_prev ∈ Z` strictly increasing, bounded via each step's
  `k ≤ v+1`) and the `v = 0` base (`L = 1`) check. PASS.

### N3-ENV and N3-BRACKET (§7 charge 11(i); bracket forms)

* Count chain re-derived: undecided at `N` ⇒ every lift has `v ≥ N` (if some lift had
  `v < N`, that is level-`N` measurable, the lift is separable, and (CEIL) decides
  the class — contradiction); the middle set is level-`N` measurable with count
  `μ{v ≥ N}·p^{nN}`; `undec^K(2N−1) = μ{v ≥ ⌈(2N−1)/2⌉}·p^{n(2N−1)} =
  μ{v ≥ N}·p^{n(2N−1)}` — the displayed normalization identity
  `undec^K(2N−1) = p^{n(N−1)}·#{middle}` is EXACT, the terminal `≤` correct
  (equality iff `N = 1`), and the DENSITY-form terminal `=` is an identity. The
  8-vs-32 refutation instance recomputed from scratch (`n=2, p=2, N=2`:
  `v(a₁²−4a₀) ≥ 2 ⟺ v(a₁) ≥ 1`, `μ = 1/2`, counts `8` and `32`, ratio
  `4 = p^{n(N−1)}`). Downstream consumption audit: §4's rescope display and TR-OM
  consume only the inequality/density forms. PASS.
* N3-ENV: instantiation arithmetic `Γ⁻(N) = N` re-checked. PASS.

### §4 (§7 charges 8, 10)

* No line of §§2–3 consumes (AGR), CU-*, GD-≥2, GMN termination, or BNS: verified by
  walking every proof against the §3.1 inventory — the imports actually touched are
  exactly NP, SF, HEN, EXT, EF, D, GRD, UCT, HRG, SEP, DES (+ I-TAIL only through
  TR-Q). Fact GRD's in-project pin (GD23 order-≤1 layer) is distinct from the OPEN
  GD-≥2 items. PASS.
* Rescope note: the density-form refutation is the sound one (FLOOR at a common
  level + the §5 `n = 2` exactness leaves no room for a strict shifted density
  inequality of the charged shape), and N3-BRACKET is the faithful replacement;
  the raw cross-level count comparison indeed proves nothing either way (counts
  inflate by `p^n` per level). PASS.

### Three-import external count (§7 charge 12(ii))

Every external quote in the brief checked against the corrected sentence: I-TAIL
(consumed by TR-Q ⇒ N3-ENV, TR-OM — including its `μ{disc=0} = 0` clause), M05
Lemma B (exactly `c^sem` well-definedness ⇒ FLOOR ⇒ N3-BRACKET's left clause), M05
Lemma D (exactly `c^K` soundness + `U^sem_N ⊆ U^K_N`; NOT the (K) identity — see the
§1 re-derivation above, which needs only the definition + measurability). No fourth
import of this species found: Lemma A is re-proved in-document; "M05 Prop 5.1's
shape" and "BNS Thm 3.13" are comparisons, not consumptions; the §3.1 Facts are the
separately-inventoried classical layer (see Note N1). The scoped sub-claim (I-TAIL
the only external touched by §3's proofs) also checks. PASS.

## 2. Harness re-run (§7 charge 9)

Repository artifacts all present at the §5 paths. Runs executed this pass:

* `python3 O4T_transfer_check.py --quick` — selftest PASS; 3 reduced configs ALL PASS.
* `python3 O4T_transfer_check.py` (full, ~77 s) — five configs `(n=2: p=2 C=10,
  p=3 C=6, p=5 C=4; n=3: p=2 C=5, p=3 C=4)`, 2,534,851 classes (sum re-verified),
  P1/P2/P3/P4/P5(+mono)/P6 all 0 fails, **OVERALL: ALL PASS**.
* Diff against the committed sealed `results/O4T_transfer_results.json`: byte-identical
  except the two per-config `seconds` fields (1.9→1.8, 27.6→27.3) — the rev-4 header's
  "byte-exact modulo timing fields" reproduction claim confirmed independently.
* Preregistration: the docstring's P1–P6 match the brief's §5 list verbatim in content
  (P4 phrased `L ≤ 2v+1 for v ≥ 1, L = 1 at v = 0` ≡ the brief's `max(1, 2v+1)`).
* Headline tables: every number in the brief's §5 block matches the sealed JSON
  (n=2 `undec_OM = undec_sem_exact` at ALL probed levels and primes, 1,970,642
  classes; n=3 rows digit-for-digit incl. the depth-artifact zeros;
  `max_shift_L_minus_v_minus_1 = 0` in EVERY config — the sharpness claim). PASS.
* The sealed JSON was restored to its committed bytes after the re-run (the working
  tree is left clean; see Note N3).

## 3. Findings

**Critical errors: NONE. Justification gaps: NONE.**

Observation-level notes (no repair required; recorded for future editors):

* **N1 (prose, sub-gap).** The rev-4 sentence "The package's EXTERNAL,
  quoted-not-proved imports are THREE" is accurate under its evident scoping —
  external = imported from other PROJECT units carrying verification tags (M05
  lemmas, the Lean-proved I-TAIL count form) — which the sentence signals via "with
  named pins and verification tags" and the closing line separately accounting the
  classical Facts. A maximally literal reader could observe that Facts NP/HEN/EXT/
  EF/D/GRD are also quoted-not-proved (literature-classical, (a)-labeled, separately
  inventoried in §3.1 with per-fact consumption sites). Since both inventories are
  displayed and complete, and I verified no member of either is missing, this is a
  wording observation, not a gap: one adjective ("project-external") would
  future-proof it.
* **N2 (routine).** Fact HEN is displayed for a two-factor coprime lift; Lemma
  SIDE(ii) uses the multi-factor form `G = ∏ G_i` — the standard iteration, one line
  if anyone wants it displayed.
* **N3 (infrastructure, outside the brief).** `O4T_transfer_check.py --quick` writes
  to the SAME results path as the sealed full run (`results/O4T_transfer_results.json`)
  and will clobber the sealed artifact on a casual quick invocation (it did,
  transiently, during this pass; the committed file was restored). A `--quick`-suffixed
  output path would remove the hazard. No bearing on the brief's soundness — the
  sealed artifact is committed and the full run reproduces it.

## 4. Verdict

All twelve §7 charges PASS; the acceptance-charge items (policy, certificate
stability, wild-corner order arithmetic, both (CEIL) chains, envelope +
unboundedness, three-import count, corrected (I1), bracket forms) PASS; the harness
reproduces the sealed record byte-exact modulo timings. Rev 4's repairs are exactly
as advertised — prose/display-level, with the mathematical core byte-stable — and
the core itself survived this pass's independent re-derivation at every probed point.

**VERDICT: SOUND**

Per the adjudication quoted in the brief's status protocol ("the unit is one
confirming clean pass from acceptance"), this pass is that confirming clean pass.
