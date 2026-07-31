# O4T rev 2 — hostile verification pass 2 (Fable, fresh context, 2026-07-31)

**Charge.** Second verifier of the two-pass bar on
`O4T_phaseB_verifybrief_rev2.md`. Read ONLY that file (standalone; no repository
context, no prior reports consulted). Protocol: quote-and-classify (CRITICAL ERROR vs
JUSTIFICATION GAP), fix nothing. Audit targets per dispatch: the pinned §3.2 policy and
certificate stability under all lifts; the n≤3 cannot-leave-order-≤1 arithmetic at
every branch incl. wild p=2,3; both (CEIL) chains and the wild corners; the envelope
arithmetic incl. the Γ-unbounded hypothesis; the eight named classical imports and
their stated scopes; the bracket directions.

**Verdict: UNSOUND** — one CRITICAL error (a false displayed identity in Corollary
N3-BRACKET, a level-normalization error; localized, nothing downstream consumes the
false clause) plus four JUSTIFICATION GAPS. The mathematical core — Theorem N3 with
both (CEIL) chains and all probed corners, TR-0/FLOOR/TR-Q with the rev-2
unboundedness repair, Lemmas CERT/RES/RES-0/SIDE/REC, the `e·d ≥ 4` exclusion at every
branch including wild p — **survives line-by-line audit**. By this package's own bar
(rev 1 was UNSOUND for one false displayed claim inside an otherwise-sound core), the
same standard applies here.

---

## Finding 1 — CRITICAL ERROR: N3-BRACKET's terminal equality is false for N ≥ 2

**Quote (§3.4, Corollary N3-BRACKET):**

> `undec^sem(N) ≤ undec^can(N) ≤ #{level-N classes with v_p(disc) ≥ N on every lift}`
> `             = undec^K(2N−1)`

**Classification: CRITICAL ERROR** (false statement, not a missing justification).

§1 pins `undec^c(M)` = "the number of undecided level-M classes". The event
`{v_p(disc f_a) ≥ N}` is level-N measurable (disc mod p^N is a function of a mod p^N),
so:

- `#{level-N classes with v ≥ N} = μ{v ≥ N} · p^{nN}`;
- `undec^K(2N−1) = μ{v ≥ ⌈(2N−1)/2⌉} · p^{n(2N−1)} = μ{v ≥ N} · p^{n(2N−1)}`.

These differ by the factor `p^{n(N−1)}`: equal only at N = 1, false for every N ≥ 2.
Concrete instance from the brief's own §5 table (n=2, p=2, N=2): μ{v ≥ 2} = 1/2
(v(a₁²−4a₀) ≥ 2 ⟺ v(a₁) ≥ 1), so the middle count is 8 while `undec^K(3) = 32`.

What survives: the INEQUALITY `undec^can(N) ≤ undec^K(2N−1)` is true (the deeper-level
count only inflates, factor `p^{n(N−1)} ≥ 1`), and the density form
`env^can(N) ≤ env^K(2N−1)` is the faithful identity-bearing statement. The left
inequality and both directions are correct as V30 found. The §4 rescope note quotes
only the inequality form, so nothing downstream consumes the false "=" — but the
displayed corollary as stated is false, and its §0/§6 status is PROVED.

## Finding 2 — JUSTIFICATION GAP: the import inventory is still incomplete

**Quotes:** §3.1 rev-2 addendum displays SIX new facts (EXT/EF/D/GRD/UCT/HRG); the §0
table quotes V30 finding 6 as "**eight** further classical facts are consumed"; §7
charge 8 asserts §3 "must stand on the §3.1 named imports alone".

Independently of the count mismatch (six displayed vs eight quoted, unreconciled in
the brief), the line-by-line audit finds at least two classical facts consumed but
NOT in the inventory:

1. **Galois descent / fixed field** (`Q̄_p^{Gal} = Q_p`, and Galois-fixed integral
   elements lie in `Z_p`). Consumed at: Fact SF's proof ("the coefficients are
   Galois-fixed integral elements" — concluding they are IN `Z_p` is descent, not
   EXT's valuation-invariance); Lemma CERT(ii) ("a one-element Galois-stable root set
   is `Q_p`-rational").
2. **Char-0 separability of irreducibles** (an irreducible polynomial over `Q_p` has
   distinct roots). Consumed implicitly wherever a certified irreducible factor
   contributes distinct roots to the separability of a completion (see Finding 3).

Both are rigor-label (a) and true; the gap is inventory completeness, the exact defect
class V30 finding 6 already flagged once.

## Finding 3 — JUSTIFICATION GAP: separability of EVERY lift is used but never proved

**Quote (§1, soundness definition):** "It is *sound* if `c_N(x) = σ ≠ ⊥` implies:
every lift `a ∈ x` has `f_a` **separable** with `σ(f_a) = σ`."

**Quote (§3.4, Theorem N3 proof):** "the walk on any lift `g` … certifies the same
factors, and each certificate is TRUE OF `g`. The certified degrees sum to `n` … so
the output is the full type `σ(g)`."

`σ(g)` is only defined for separable `g`, and FLOOR (hence N3-BRACKET's left
inequality) consumes soundness in exactly the every-lift-separable form. The proof
never establishes that an arbitrary completion `g` of the read digits is separable
(squarefree). It IS true — the certificates hand `g` a partition of its `n` roots into
pairwise-disjoint groups (distinct step-0 residues / distinct valuations / distinct
residual classes), each group the root set of one irreducible (hence separable, char
0) factor, so `g` has `n` distinct roots — but this chain is nowhere displayed, and it
consumes Finding 2's unnamed import (2). Unclosed obligation; assume-and-continue
downstream verified.

## Finding 4 — JUSTIFICATION GAP (minor): CERT(i)'s hull claim is ambiguous at x₀ = 1

**Quote (Lemma CERT(i)):** "hence by (C1) the resolved hull is the true hull on
`[x₀, n]`."

Two readings when `x₀ = 1` (index 0 unresolved): (a) the true hull of the FULL point
set `{0,…,n}` restricted to `[1,n]` — for this the claim needs the vertex condition at
`(1, y_1)`, which (C1) does NOT supply (C1 only covers unresolved `i > x₀`; a low
point at index 0 could cut under `(1, y_1)`); it is supplied only by (C2) via
CERT(ii)'s `k > y_1 + s_r` argument. (b) the hull of the index-range-`[1,n]` points —
then (i) is correct as proved, and CERT(ii)'s proof ("The hull on `[1, n]` is true by
(i)", then the vertex condition displayed separately from `v(g_0) ≥ k > y_1 + s_r`)
is complete and correct under this reading. The logic closes under reading (b); the
sentence should say which hull it means. No completion escapes the certificate either
way — verified below — so this is classified a (minor) gap, not an error.

## Finding 5 — JUSTIFICATION GAP (minor): the §4 rescope note's refutation mixes the
same count/density normalization

**Quote (§4 rescope note):** "As literally written this is NOT the provable direction:
`undec_sem ≤ undec_OM` always (FLOOR)".

FLOOR compares counts at the SAME level; the charged inequality
`undecided_OM(N) ≤ undecided_sem(N + shift)` compares counts at DIFFERENT levels,
where raw counts inflate with depth (n=2, p=2: undec^sem counts 2, 4, 8, … by the §5
table) — so in raw-count form the charged inequality can hold trivially and FLOOR
alone does not refute it. The honest refutation is the density form plus the n=2
numeric observation `env^can(N) = env^sem(N)` (which the note does invoke). The
CONCLUSION (rescope to N3-BRACKET's inequality) is correct; the stated reason is
incomplete. Same root cause as Finding 1.

---

## Verification log (what was checked and UPHELD)

### §2 transfer skeleton

- **Lemma A / TR-0**: clopen cylinder bookkeeping, nesting from stability, continuity
  from above; `⋂_N U^c_N ⊆ {N(a) undefined or ∞}` null. Sufficiency-only discipline
  honored. UPHELD.
- **FLOOR**: sound ⇒ every lift separable of type σ ⇒ every SEPARABLE lift has type σ
  ⇒ `c^sem` decides; contrapositive. UPHELD (note: correctness of applying it to
  `c^can` rests on Finding 3's obligation).
- **TR-Q with the rev-2 unboundedness hypothesis**: `Γ⁻(N) = min{v : Γ(v) > N}`
  nonempty by unboundedness, so well-defined; `v < Γ⁻(N) ⇒ Γ(v) ≤ N` by minimality
  (no off-by-one: `N ≥ Γ(v)` is exactly the decision hypothesis's threshold);
  `U^c_N ⊆ {disc = 0} ∪ {v ≥ Γ⁻(N)}` correct; I-TAIL applied within its stated scope
  (`n ≥ 2`, `m = Γ⁻(N) ≥ 0`); divergence proof (fix `v₀`, take `N ≥ Γ(v₀)`, use
  monotonicity) correct. V30's constant-Γ counterexample is excluded by the displayed
  hypothesis itself, not prose. Both consumers instantiate unbounded majorants
  (`v + 1`; TR-OM's OL2 shape displays unboundedness). UPHELD.

### §3.1 imports, scope usage

NP (incl. the `g(0) = 0` finite-slope reading, used at the `b₁ = ∞` corner), SF, HEN
(iterated to multi-factor coprime splits in SIDE(ii) — a routine induction beyond the
two-factor statement, noted, not charged), EXT, EF (applied to `v(β) = h/e` in lowest
terms ⇒ `e | e(Q_p(β)/Q_p)` ⇒ `[Q_p(β):Q_p] ≥ e` — within scope), D (monic integral
roots ⇒ `δ_{ij} ≥ 0`, needed and available for both chains), GRD (used exactly as
stated in RES), UCT and HRG (proved in-line; proofs check). All used within stated
scopes. The inventory is nonetheless incomplete — Finding 2.

### §3.2 policy well-definedness

- All reads are class reads: digits of Z-polynomial values below level k are functions
  of a's digits below k (no downward carries); recursion centers `c + z₀p^h` are fixed
  integer lifts of residues computed from read digits. UPHELD.
- Resolved/unresolved is computable from digits < k; `y_n = 0` monic. UPHELD.
- Residual digits sit at heights ≤ y(x₀) < k (hull slopes ≥ 0 since it ends at (n,0)
  with all y ≥ 0, so heights decrease rightward): consumption ≤ k. UPHELD.
- Stability: deterministic walk on digits below L(f) ≤ N; refinements replay it. UPHELD.

### Lemma CERT — the certificate under ALL completions (charge 1)

- (i): unresolved i in (x₀, n) have y_i ≥ k > H_res(i) in EVERY completion; points on
  or above a lower hull never change it; resolved values exact by definition. UPHELD
  under the truncated-point-set reading (Finding 4 for the wording).
- (ii), the left-edge shortcut: once (1, y₁) is resolved and (C1) holds, H_res on
  [1,n] is the true hull there, so s_r is the true first slope (= b₂). The unresolved
  index 0 has v(g₀) ≥ k > y₁ + s_r in every completion, which is exactly the vertex
  condition at (1, y₁): the leftmost true side has length 1, slope v(g₀) − y₁ ∈ Z (or
  ∞ when g₀ = 0 — the corner is covered: the root is c itself, still the unique root
  with v(β) > s_r). A one-element Galois-stable root set is rational (Finding 2's
  unnamed descent fact), giving the (1,1) factor; `k > y₁ + λ_prev` puts its slope
  > λ_prev, i.e. in the current cluster. UPHELD.
- Spurious-fire check: if in truth b₁ = b₂, then with (C1) true s_r = b₁ and firing
  would need v(g₀) ≥ k > y₁ + s_r = y(0), a contradiction — the shortcut CANNOT fire
  when the left side has length ≥ 2, in any completion. UPHELD.

### Lemmas RES / RES-0 / SIDE / REC (charges 3, 5)

- RES monomial bookkeeping (charge 5): for g_< (roots of valuation > h), coefficient
  j has v(c_j) + jh ≥ (deg−j)h′ + jh with h′ > h — strictly above deg·h except at the
  leading term: unique minimum, in_w = x̄^deg. For g_> (roots of valuation < h),
  v(c_j) + jh ≥ [Σv(β) − (sum of the j largest v(β))] + jh > Σv(β) for j > 0 since
  each v(β) < h: unique minimum at the constant term. Both unique-minimality claims
  UPHELD; with Fact GRD the on-line digits of g are one monomial times those of g_h,
  i.e. R = c̄·Ḡ.
- RES-0: G monic with unit roots ⇒ G(0) unit (UCT) ⇒ R(0) = c̄Ḡ(0) ≠ 0; the
  independent vertex-digit confirmation (r₀ read at the exact left-endpoint valuation,
  no cancellation by NP) also checks. UPHELD — the z₀ = 0 corner is genuinely EMPTY.
- SIDE(i): denominator-e argument via EF; slope factor degree e contains β ⇒
  irreducible, type (e,1); prime-agnostic (wild included). UPHELD.
- SIDE(ii): Ḡ = c̄⁻¹R monic of degree d (right endpoint is a vertex ⇒ r_d ≠ 0);
  coprime-power Hensel split; simple ψ of degree d′ ⇒ unramified (1, d′) with
  Q_p(β) = Q_p(u) since h ∈ Z; repeated z₀ ⇒ exactly m′ roots with u ≡ z₀ (HRG), i.e.
  v(β − z₀p^h) > h; exclusivity of the group needs v(z₀p^h) = h exactly, supplied by
  RES-0. UPHELD.
- REC three-case split (charge 3): with z₀ ≠ 0, v(c′ − c) = h exactly; the cases
  v(α−c) < h / = h with different residue / > h each give v(α−c′) ≤ h with the
  ultrametric minimum uniquely attained where claimed; (I1) propagates with exactly m′
  roots. The rev-1 false "either way" sentence is gone. UPHELD.

### Theorem N3, both (CEIL) chains and corners (charges 2, 6)

- **(D) and pairwise bounds**: v(disc) = 2Σ_{i<j}δ_{ij} (D via EXT-additivity);
  δ_{ij} ≥ 0 (integral roots) licenses dropping unused pairs. UPHELD.
- **Case (a), b₁ = b₂ (< ∞ forced by separability)**: v(g₀) = Σb_j EXACTLY (a product
  — no cancellation possible at index 0); index 0 resolves at k = y(0)+1 and (C1)
  holds there (all hull heights ≤ y(0) < k); no earlier certification (x₀ ≥ 2 never
  certifies; shortcut blocked by the spurious-fire check above). Chain:
  b₁ + b₂ = 2b₂ ≤ 2δ₁₂ (δ₁₂ ≥ min = b₂), b_j ≤ min(b₂,b_j) ≤ δ₂ⱼ for j ≥ 3, and
  2δ₁₂ + Σδ₂ⱼ ≤ 2Σδ = v by δ ≥ 0. So k − 1 = y(0) ≤ v. Sharp at n = 2 (equality),
  matching §5 P3. UPHELD.
- **Case (b), b₁ > b₂ (charge 2)**: (1, y(1)) is a true vertex, y(1) = Σ_{j≥2}b_j ∈ Z
  exact (unique minimal term since b₁ > b₂; b₂ < ∞ by separability so y(1) < ∞);
  b₁ = y(0) − y(1) ∈ Z ∪ {∞} (length-1 side, integer coefficient valuations).
  Fractional-b₂ corner: k = y(1) + ⌊b₂⌋ + 1 > y(1) + b₂ holds STRICTLY for all b₂
  (⌊b₂⌋ + 1 > b₂), and s_r = b₂ once (C1) holds — checked that (C1) is automatic for
  k > y(1) (H_res(i) ≤ y(1) < k, heights decreasing), so the fire level is exactly as
  displayed. `x = 0` unresolved: b₁ ∈ Z, b₁ > b₂ ⇒ b₁ ≥ ⌊b₂⌋ + 1 ⇒ y(0) ≥ k; the
  b₁ = ∞ (g₀ = 0) corner is trivial (never resolves). k > y(1) + λ_prev from
  b₂ > λ_prev ∈ Z ⇒ ⌊b₂⌋ ≥ λ_prev. No earlier fire: x₀ = 0 needs k > y(0) ≥ k. Chain:
  δ₁₂ = b₂ EXACTLY (strict ultrametric; also correct at b₁ = ∞: δ₁₂ = v(c′−α₂) = b₂),
  k − 1 = y(1) + ⌊b₂⌋ ≤ 2b₂ + Σ_{j≥3}b_j ≤ 2δ₁₂ + Σδ₂ⱼ ≤ v. UPHELD.
- Consistency corner: a length-1 side cannot carry fractional b₂ — if b₂ ∉ Z its ≥ e
  conjugates share valuation b₂ > λ_prev (EXT), all cluster roots, so the b₂-side has
  length ≥ e ≥ 2; no contradiction anywhere in case (b)'s sub-processing. UPHELD.
- **Recursed steps**: the same two cases verbatim with c′ ∈ Z_p; δ's are absolute root
  differences, (D) global, so k ≤ v + 1 at EVERY cluster step. Termination: λ_prev
  strictly increases through integers ≤ δ₁₂ ≤ v/2 (2δ ≤ v for every pair); each scan
  halts at the computed k. Step 0 consumes 1 ≤ v + 1; v = 0 ⇒ f̄ separable ⇒ L = 1.
  UPHELD.
- **Wild spot-checks** (p = 2: x²+1, x²−2, x²+2x+4; p = 3: x³−3, x³−3x−3): walk output
  and L ≤ v+1 verified by hand, including the (2,1)/(3,1) wild certifications via
  SIDE(i) and a residual read (R = z²+z+1 at p=2, unramified (1,2)). All exact;
  x²+2x+4 attains L = v + 1 = 3. UPHELD.

### The `e·d ≥ 4` exclusion at every branch (charge 4)

At every cluster step the sides of slope > λ_prev carry exactly the m ≤ n ≤ 3 cluster
roots (I1), so every side has length ℓ = e·d ≤ 3: a d ≥ 2 residual forces e = 1, a
repeated residual factor of degree ≥ 2 would need d ≥ 4, and a repeated residual on an
e ≥ 2 side would need e·d ≥ 4 — all impossible at n ≤ 3, at every prime (the counting
is characteristic-free), at step 0 and at every refined cluster (m′ ≤ 3). The §4
never-leaves-order-≤1 claim's arithmetic is UPHELD. (e = 3, d = 1 — totally ramified
cubic — does occur and is handled by SIDE(i), not by order growth.)

### N3-ENV, envelope arithmetic (charge 7 consumer check)

Γ(v) = v + 1 is nondecreasing and unbounded; Γ⁻(N) = min{v : v + 1 > N} = N exactly;
the displayed envelope is TR-Q's bound verbatim with m = N, w = n·v_p(n); → 0 by TR-Q
divergence. Instantiation UPHELD.

### N3-BRACKET directions (charge 10) and §4

Left inequality (FLOOR + N3 soundness, same level N, count form): UPHELD modulo
Finding 3. Middle inequality: undecided at N ⇒ every separable lift has
L(f) ≤ v+1 impossible at N, so v ≥ N; inseparable lifts v = ∞; {v ≥ N} is level-N
measurable: UPHELD. Terminal EQUALITY: FALSE — Finding 1. The in-words gloss's
direction (rev-2 fix): correct as now written. §4's TR-OM conditional hygiene (TR-0
via a.e.-finiteness from (AGR) + null disc locus; FLOOR via quoted Lean soundness;
OL2-shape unboundedness threaded): internally consistent, nothing in §§2–3 consumes
(AGR)/CU-*/GD-≥2 (charge 8 — checked per proof line against the §3.1 list; the only
extra-inventory consumptions are Finding 2's two classical facts and the M05 Lemma B
pointer for c^sem nonvacuity, which is named inline). Rescope conclusion sound;
reasoning gap = Finding 5.

### §5 numerics (charge 9)

Out of scope for this standalone pass by construction (no repository reads permitted).
The internal consistency of the quoted tables with the claimed laws was spot-checked
(n=2 p=2 halving; K-lag pattern consistent with env^K(N) = μ{v ≥ ⌈N/2⌉}; the μ{v≥2} =
1/2 computation above); the sealed artifacts remain for repository-access verifiers.

---

## Attack-list disposition (§7)

1. CERT(ii) completion quantifier incl. g₀ = 0 and s_r: UPHELD (Finding 4 wording).
2. Case (b) read level, b₁ = ∞ and fractional b₂ corners: UPHELD.
3. REC / RES-0 and the three-case split: UPHELD.
4. e·d ≥ 4 exclusion incl. wild and refined clusters: UPHELD.
5. RES unique-minimality pair: UPHELD.
6. (D) + both chains' slack directions: UPHELD.
7. TR-Q Γ⁻ off-by-one + unboundedness + consumers: UPHELD.
8. No silent (AGR)/CU-*/GD-≥2 consumption; imports list: GAP — Finding 2 (inventory
   short of actual consumption; six displayed vs V30's quoted eight, unreconciled).
9. Harness rerun: out of scope (standalone).
10. Rescope direction: conclusion UPHELD; justification GAP — Finding 5.

**Bottom line.** The rev-2 repairs of all five V30 dispositions are genuine and
correctly executed; the core N3/TR-Q mathematics passes a full hostile line-by-line
audit including every charged corner. The package as stated nonetheless contains one
false displayed identity (N3-BRACKET's "= undec^K(2N−1)", Finding 1 — a
count-vs-density normalization error, repair one line) and an incomplete import
inventory plus an unclosed every-lift-separability obligation (Findings 2, 3).
Verdict: UNSOUND under the package's own acceptance bar; expected to be SOUND after a
rev 3 addressing Findings 1–3 (Findings 4–5 are wording-level).

*(Fable pass 2 of 2; fresh context; input = the rev-2 brief only.)*
