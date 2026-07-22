# WILD_WAVE6C_BLUEPRINT — faithfulness scope #5: every fiber of the full n=2 model
*(2026-07-22. Ground truth: `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (accepted) §§1–4, 7;
predecessor blueprints `WILD_WAVE56_BLUEPRINT_2026-07-22.md`, audit log Wave-6 entry. Status:
DRAFT pending Codex adversarial pass on §1/§3.)*

## §0. The gap being closed

Wave 6's capstone `SeriesAssembly.montes_unconditional_n2_full` certified the FULL per-type
n=2 densities (1/3 each at p=2, `hExhaust` discharged) — but its honest-limits block records:
the σ-keying of (i) the c=1 translate fibers and (ii) the depth-0 even-height inert/split
cluster leaves is DEFINITIONAL, outside axiom scope #4 (`om_leaf_faithful` over
`omMenu5 n D K σ` + `fiberOf5`). Until a faithfulness statement covers every fiber the model
counts, "complete per-type density" is not Montes-faithful in every fiber.

**Wave 6c goal.** A theorem `fullFiber_hasType`: every genuine monic quadratic `f : ℤ_[2][X]`
whose coefficient box lies in ANY decided fiber of `realMW6`'s per-type count
(`decidedCount6 σ N`) has a genuine ℚ_p-factorization certificate of the keyed type σ.
Footprint: Lean core + `om_leaf_faithful` exactly. Capstone statements and footprints
UNTOUCHED (this wave adds faithfulness companions; no counting change, no value change).

**Design headline (settled by reading the code, §3):**
1. The **c=1 translates need NO axiom content**: the fiber is definitionally the c=0 fiber of
   the translated polynomial (`TransChain c … a = ChainPair … (transMap c a)`), the
   box-level translate is matched by the genuine translate `g = f(x+1)` (a commutation lemma
   to prove), and the PROVED transport `QpTypeChain.qpType_translate_rescale` (any a≠0, any
   degree) carries g's certificate to f at `a = 1, c = 1`. Deriving rather than importing
   translate coverage continues the (P4d) discipline: the paper states no translation form,
   so none may enter the axiom.
2. The **depth-0 inert/split legs need a pure MENU widening**: `chainShapes` (ChainMenu.lean
   line ~1000) filters `ms ≠ []`; but `fiberOf5` on a chain-headed literal already dispatches
   to `ChainCell (decodeMs T) (decodeLeaf T)`, and `ChainPair [] leaf = LeafPair leaf` — the
   EXACT fiber the W6 model counts at depth 0. So scope #5 = admit `chainLit [] leaf` to the
   menu (a new emission `chainShapes6` without the filter); the fiber dispatch hypothesis is
   byte-identical. `om_leaf_faithful_w5` (the scope-#4 form) derives back by menu inclusion.
3. Every new keying payload gets an ALL-FIBER axiom-free machine guard (the masters, §1):
   split-keyed fibers' faithfulness is PROVED outright (no axiom at any depth/translate);
   ram/inert-keyed fibers get irreducibility + both-coordinate (e,f) forcing on every bundle
   — the axiom contributes only the `LocalFactorData` existence it has always carried
   (DVR-ness of the integral closure; Serre carrier, `GMN_citations.md` §§1–2).

No new CITED THEOREM enters: the depth-0 leaf reads are GMN Thm 1.15 / Thm 1.19 / Cor 1.20
instances already inside the (P4) pin, with the per-literal statement-map displayed in §3
(this display is mandatory — Codex pass-1 gap #4); hence no W5c-style blocking declaration
gate, but the §3 table IS the declaration-gate content for the new instances.

## §1. Math ground truth

Setting: p prime (all masters below are general-p unless marked p=2), `g = y² + b₁y + b₀`
monic quadratic over ℤ_p. Recall for degree 2: reducible over ℚ_p ⟺ has a root in ℚ_p, and a
root of a monic ℤ_p-polynomial is integral, so reducible ⟺ has a root in ℤ_p. Valuation v is
the normalized ℚ_p-valuation (v(p) = 1, ℤ-valued on ℚ_pˣ).

### 1.1 The five masters

**(R) Ram master.** *Hypotheses:* v(b₀) = H exactly with H odd, and v(b₁) ≥ (H+1)/2.
*Conclusions:* g is irreducible over ℚ_p, and every `LocalFactorData` bundle on g carries
(e,f) = (2,1).

*Proof.* Irreducibility: suppose g = (y−r₁)(y−r₂) with r₁, r₂ ∈ ℚ_p. Both roots are nonzero
(else v(b₀) = ∞) with v(rᵢ) ∈ ℤ and v(r₁) + v(r₂) = v(b₀) = H. H odd forces v(r₁) ≠ v(r₂)
(equality would give 2v(r₁) = H); say v(r₁) < v(r₂), so v(r₁) ≤ (H−1)/2 (integer below H/2).
Then v(b₁) = v(r₁ + r₂) = min(v(r₁), v(r₂)) = v(r₁) ≤ (H−1)/2 < (H+1)/2 ≤ v(b₁),
contradiction. (The ultrametric min-equality holds because the two valuations differ.)

(e,f) forcing — run INSIDE AN ARBITRARY BUNDLE (this is the quantifier the conclusion
carries): let D be any `LocalFactorData` on g, L := D.L (with finrank_ℚ_p L = 2 from
`D.finrank_eq` and deg g = 2), r ∈ O_L the bundle's root of g, and e·f = 2 the fundamental
identity (`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` on the bundle's pinned
integral closure — the landed pattern of `ef_of_inert_quadratic`/`ef_of_wildH3`). BOTH roots
of g lie in this same L by Vieta, no Galois theory: r' := −b₁ − r satisfies
g = (y − r)(y − r') (expand and match coefficients: sum −b₁, product r·(−b₁−r) =
−b₁r − r² = b₀ since g(r) = 0). Suppose e = 1 (so f = 2). Then L's value group equals
ℚ_p's, i.e. the normalized valuation v_L on L (in Lean: the ϖ-order apparatus of the landed
`ef_of_wildH3`, generalized from H = 3 to odd H) is ℤ-valued with v_L(p) = 1 and extends v.
Now v_L(r) + v_L(r') = v_L(b₀) = H odd forces v_L(r) ≠ v_L(r'); say v_L(r) < v_L(r'), so
2·v_L(r) < H, v_L(r) ≤ (H−1)/2 < (H+1)/2 ≤ v(b₁) = v_L(b₁) (if b₁ = 0 read
v_L(b₁) = ∞; the next step only needs v_L(r) < v_L(b₁)). Then
v_L(r') = v_L(−b₁ − r) = v_L(r) (ultrametric: the strictly smaller term wins; at b₁ = 0
directly v_L(−r) = v_L(r)) — contradicting v_L(r) < v_L(r'). So e = 2, f = 1, on EVERY
bundle. ∎

*(Lean route: generalizes the banked H=3 arguments — `QpTypeH3` "elementary two-root
irreducibility" and `ef_of_wildH3` ϖ-order parity — replacing the hard-coded 3 by odd H with
omega arithmetic. In the bundle formulation the "v_L" bookkeeping is the existing ϖ-order
apparatus; no new machinery.)*

**(I) Inert master.** *Hypotheses:* v(b₀) ≥ 2m, v(b₁) ≥ m, and the residual digit pair
(b₀/p^{2m} mod p, b₁/p^m mod p) ∈ `noRootPairs` (the residual quadratic
z² + (b₁/p^m)‾z + (b₀/p^{2m})‾ has no root in F_p). *Conclusions:* g is irreducible over
ℚ_p, and every bundle carries (e,f) = (1,2).

*Proof.* Set h(z) := g(p^m z)/p^{2m} = z² + w₁z + w₀ with w₁ = b₁/p^m, w₀ = b₀/p^{2m} ∈ ℤ_p.
Its reduction h̄ is root-free over F_p by hypothesis, hence irreducible (a monic quadratic
over a field with no root is irreducible; over F_p rootless quadratics are automatically
separable, but separability is not needed here). If g had a root y₀ ∈ ℤ_p then... note
y₀/p^m need not be integral a priori; argue on h directly: a root z₀ ∈ ℚ_p of h is integral
(h monic over ℤ_p), and its reduction roots h̄ — contradiction; so h is irreducible over ℚ_p.
Roots of g and h generate the same extension (y ↦ y/p^m is a ℚ_p-affine bijection between
root sets: g(y₀) = 0 ⟺ h(y₀/p^m) = 0 since g(y) = p^{2m}h(y/p^m)), so g has no ℚ_p-root
either: g irreducible. For the forcing, L = ℚ_p(root of h): e·f = 2, and f = 1 is refuted
because the root ρ of h lies in O_L with residue field F_p (if f = 1), so ρ̄ ∈ F_p roots h̄ —
contradiction. Hence f = 2, e = 1; the bundle transport along the affine identity
g(p^m z) = p^{2m}h(z) keeps (e,f) literally unchanged (L, O unchanged — the proved
`compData` transport of W5c). ∎

*(Lean route: `ef_of_inert_quadratic` (QpTypeChainLeaves Block: exists, stated on (w₀,w₁))
applied after a general-m rescale decode; the m=1 instance is the landed chainInert anchor.)*

**(S) Split master.** *Hypotheses:* v(b₁) = k exactly, v(b₀) ≥ 2k+1. *Conclusions:* there is
a genuine certificate: h(z) := g(p^k z)/p^{2k} = z² + w₁z + w₀ has w₁ = b₁/p^k a UNIT and
v(w₀) ≥ 1, so h̄ = z(z + w̄₁) has two DISTINCT simple roots 0 and −w̄₁ ≠ 0; Hensel lifts them
to r₁ ≠ r₂ ∈ ℤ_p with h = (z−r₁)(z−r₂); each linear factor carries the proved degree-1
bundle (`linearFactorData`, (e,f) = (1,1)); the proved transport along
g(y) = p^{2k}h(y/p^k) (i.e. g.comp(C p^k·X) = C p^{2k}·h read backwards — the relation used
is g's certificate FROM h's, `qpType_translate_rescale` at a = p^k, c = 0) yields
∃ F : QpFactorization g, qpType F = {(1,1),(1,1)}. Axiom-FREE. ∎

*(Lean route: the landed `chainSplit_hasType` machinery at general k — the k=1 instance is
the landed anchor. Simple-root hypothesis for Hensel: h̄'(0) = w̄₁ ≠ 0 and
h̄'(−w̄₁) = −w̄₁ ≠ 0, valid at ALL p including p = 2.)*

**(S0) Order-0 split master (p = 2).** *Hypotheses:* 2 ∣ a₀, 2 ∤ a₁ (the `SepSplitCell`
digit conditions on f = x² + a₁x + a₀). *Conclusions:* full certificate of type
{(1,1),(1,1)}, axiom-free. *Proof:* f̄ = x² + x = x(x+1) over F₂ has distinct simple roots
0, 1 (f̄' = 1 there since 2ā = 0... precisely f̄'(x) = 2x + ā₁ = ā₁ = 1 ≠ 0); Hensel as in
(S) with k = 0 — indeed (S0) IS the k = 0 boundary instance of the (S) argument minus the
exactness bookkeeping: w₁ = a₁ unit, w₀ = a₀ ∈ 2ℤ₂... note (S) required v(b₀) ≥ 2k+1 = 1 ✓.
So (S0) = (S) at k = 0 verbatim. ∎ *(Lean: state (S) for k ≥ 0; then (S0) is the k = 0
instance and needs no separate module code beyond the digit-condition glue
`SepSplitCell → hypotheses of (S) at k = 0`.)*

**(I0) Order-0 inert master (p = 2).** *Hypotheses:* 2 ∤ a₀, 2 ∤ a₁ (`SepInertCell`).
*Conclusions:* f irreducible, every bundle (1,2). *Proof:* (I) at m = 0: the residual pair
is (ā₀, ā₁) = (1, 1), and z² + z + 1 is root-free over F₂ (0 ↦ 1, 1 ↦ 1). So (I0) = (I) at
m = 0, PROVIDED (I) is stated for m ≥ 0 (nothing in the proof of (I) uses m ≥ 1) and the p=2
digit glue `SepInertCell → residual pair ∈ noRootPairs 2` is supplied (`noRootPairs 2 =
{(1,1)}` — decidable). ∎

### 1.2 The chain unwind (genuine decode at every depth)

**Lemma (step decode, general head m, TAIL-GENERIC).** Fix a tail list ms' and leaf. Let f
be a genuine monic quadratic (deg 2) whose box pair at staircase frame (L₀, L₁) with
2m ≤ L₀ and m ≤ L₁ AND L₀ ≤ L₁ satisfies `ChainPair (m :: ms') leaf L₀ L₁`. [ERRATUM
2026-07-22, caught at W6c-a implementation: L₀ ≤ L₁ is REQUIRED — the descendPair box match
reads the b₁-slot (known mod p^(L₁−m)) into the child b₀-slot at level L₀−2m, so
box_shift_cast needs L₀−2m ≤ L₁−m; counter-frame (L₀, m, L₁) = (10, 1, 1) refutes the
weaker form. It is the staircase invariant and available at every unwind call site.]
Then there are ĉ ∈ ℕ (the
value of the stratum's existential unit digit) and a genuine monic quadratic g of degree 2
with

  f.comp (C p^m·X + C (ĉ·p^m)) = C p^{2m}·g,     (step relation)
  toBoxPair_{(L₀−2m, L₁−m)} g = descendPair p m ĉ (toBoxPair_{(L₀,L₁)} f),   (box match)

hence — since `ChainPair ms' leaf (L₀−2m) (L₁−m)` is by DEFINITION a predicate of the
`descendPair` output — `ChainPair ms' leaf (L₀−2m) (L₁−m)` holds at toBoxPair g. The tail
(arbitrary ms', not just the leaf case) rides through the box match for free; this is the
statement the induction consumes, displayed here precisely because the landed m = 1 template
(`chainStep_decode`) states LESS: it hard-codes ms' = [], m = 1, and keeps the box match
(`hdesc`, its lines 165–181) and ĉ·p (line 158) internal to the proof. The general PROOF is
nonetheless the template's, with: `dvd_of_box_dvd` at shifts 2m ≤ L₀ and m ≤ L₁ (these are
the lemma's two frame hypotheses — StratumPair's (S1)∧(S2) provide the box divisibilities at
exactly those shifts), `box_shift_cast` at the same shifts, and the closing degree-2 `ring`
identity in p^m. ∎

**Frame availability along the induction.** The unwind hypothesizes the additive budget
2·Σms + leafNeed(leaf) ≤ L₀ ≤ L₁ (kept in ADDITIVE form; never rewrite into ℕ-subtraction
before omega). At the head step 2m ≤ 2·Σ(m::ms') ≤ L₀ − leafNeed < L₀ ✓ and
m ≤ 2m ≤ L₀ ≤ L₁ ✓; the child budget 2·Σms' + leafNeed ≤ L₀ − 2m and L₀ − 2m ≤ L₁ − m
(from L₀ ≤ L₁, m ≥ 0) re-establish the hypothesis. Below the budget the fiber is EMPTY
(`chainPair_empty`), so the dichotomy 'L₀ < 2·Σms + leafNeed (vacuous) OR budget ≤ L₀
(decode)' is exhaustive by ℕ-trichotomy.

**Proposition (unwind).** For every slope list ms (entries ≥ 1) and leaf, if toBoxPair f at
frame (L₀, L₁) with L₀ ≤ L₁ satisfies `ChainPair ms leaf L₀ L₁`, then EITHER
L₀ < 2·Σms + leafNeed(leaf) (in which case the fiber is empty — `chainPair_empty` — so the
statement is vacuous), OR there is a genuine monic quadratic g_leaf whose box pair at the
final frame (L₀ − 2Σms, L₁ − Σms) satisfies `LeafPair leaf`, together with a composed chain
of affine relations f → g_leaf each of the step-decode form. Consequently:
* any certificate of g_leaf transports UP to a certificate of f with the same qpType — per
  step by the proved `qpType_translate_rescale` (its stated direction: a certificate of the
  INNER polynomial g yields one of f along f.comp(C a·X + C c) = C a^{deg g}·g), composed;
* irreducibility transports DOWN-to-UP as well (a ℚ_p-root of f maps to a ℚ_p-root of
  g_leaf under the inverted affine maps, so g_leaf rootless ⟹ f rootless ⟹ f irreducible
  at degree 2 — equivalently the landed W5c affine `AlgEquiv` transfer, composed);
* every-bundle (e,f)-forcing transports by BUNDLE PULLBACK, which runs in the OPPOSITE
  direction to certificate transport and is supplied by the landed `compData` over ℚ_p at
  the INVERTED affine data: given an arbitrary bundle D on f, `compData α β γ` at
  α = (p^m)⁻¹, the matching β = −(ĉ·p^m)/(p^m)-shape data, γ = (p^{2m})⁻¹ produces a bundle
  on g with L, O literally unchanged and efOf UNCHANGED BY rfl (`efOf_compData`) — this is
  verbatim the pattern inside the landed depth-1 gate `chainGate_ef_forced`
  (`QpTypeChain.lean` lines ~740–750, there at m = 1), composed along the chain. The
  masters force (e,f) on every bundle of g_leaf; pulling back an arbitrary bundle of f
  yields a bundle of g_leaf with the SAME (e,f); hence the forcing descends to f.
*Proof:* induction on ms; base = the identity relation; step = the tail-generic step-decode
lemma. The frame arithmetic (L₀ − 2m) − 2·Σms' = L₀ − 2·Σ(m::ms') etc. is `omega` on the
additive-form budget (previous paragraph). ∎

**Corollary (per-leaf conclusions at every depth, c = 0).** ChainPair-fiber membership at a
sufficiently large frame gives, via the masters at the final frame:
* leaf = ram H (H odd ≥ 1): f irreducible, every bundle (2,1); [(R)]
* leaf = inert m (m ≥ 1): f irreducible, every bundle (1,2); [(I)]
* leaf = split k (k ≥ 1): ∃ certificate of type {(1,1),(1,1)} — axiom-free. [(S)]

Note the exactness decodes at the final frame need the digit positions inside the frame:
leafNeed(leaf) ≤ L₀ − 2Σms, which is exactly the non-emptiness threshold — below it the
fiber is empty and the claim vacuous. leafOK (H odd, parameters ≥ 1) is supplied by the menu
(`of_mem_chainLeaves`) or hypothesized directly.

### 1.3 The translate reduction (c = 1; no axiom content)

**Lemma (translate commutation).** For genuine monic quadratic f and ĉ ∈ ℕ:
toBoxPair(f.comp(X + C ĉ)) = transMap ĉ N (toBoxPair f), and f.comp(X + C ĉ) is monic of
degree 2. *Proof:* for f = x² + a₁x + a₀, f(x+ĉ) = x² + (a₁ + 2ĉ)x + (a₀ + ĉa₁ + ĉ²);
`transMap` = `affineEquiv` at (N, N) computes the same pair (its defining formulas,
cf. `transMap_one_fst`/`transMap_one_snd` at ĉ = 1); toZModPow is a ring hom. ∎

**Reduction.** `TransChain c ms leaf N (toBoxPair f)` unfolds to
`ChainPair ms leaf N N (transMap c N (toBoxPair f))` = `ChainPair ms leaf N N
(toBoxPair (f.comp(X + C c)))`. So with g := f.comp(X + C c): g is in the c=0 fiber; the
per-leaf conclusions of §1.2 apply to g; and they transport back to f:
* certificates via `qpType_translate_rescale` at a = 1, c = ĉ (relation
  f.comp(C 1·X + C ĉ) = C 1·g, i.e. 1^{deg g} = 1);
* irreducibility/forcing via the same affine transfer at a = 1.
At p = 2 only c ∈ {0, 1} occur (the model's residue points). ∎

### 1.4 σ-keying table (every fiber family of `decidedCount6 σ N`)

| family | fiber predicate | keyed σ | faithfulness route | axiom used |
|---|---|---|---|---|
| order-0 sep split | `SepSplitCell N` | {(1,1),(1,1)} | (S0) certificate | none |
| order-0 sep inert | `SepInertCell N` | {(1,2)} | (I0) forcing | existence only |
| chain, c ∈ {0,1}, ms, ram H | `TransChain c ms (ram H) N` | {(2,1)} | §1.2/§1.3 + (R) forcing | existence only |
| chain, c ∈ {0,1}, ms, inert m | `TransChain c ms (inert m) N` | {(1,2)} | §1.2/§1.3 + (I) forcing | existence only |
| chain, c ∈ {0,1}, ms, split k | `TransChain c ms (split k) N` | {(1,1),(1,1)} | §1.2/§1.3 + (S) certificate | none |

"Existence only" = the certificate itself comes from `om_leaf_faithful` (§3), whose
machine-guard is the corresponding all-fiber forcing theorem; wrong-keying mutations are
refuted by the forcing (probes, §4). GMN reading of the NEW menu legs (depth-0 inert/split),
inside the (P4) pin and the existing citation: inert m = single side (0,2m)–(2,0) of integer
slope −m in lowest terms −m/1 (e = 1), residual the root-free (hence irreducible, degree-2)
quadratic — Thm 1.19/Cor 1.20 give one leaf with (e,f) = (1,2); split k = two width-1 sides
(vertices (0, v(b₀)), (1, k), (2, 0), slopes distinct since v(b₀) − k > k... v(b₀) ≥ 2k+1 ⟹
v(b₀) − k ≥ k+1 > k) — Thm 1.15 gives two coprime degree-1 blocks, each (1,1). The GENUINE
reads match the masters' conclusions, which is the mutual-consistency check the guardian
audits (statement-map, both directions).

### 1.5 What remains axiom content (unchanged carrier)

Only `LocalFactorData` existence for IRREDUCIBLE quadratics (bundle = the finite extension L
with its DVR integer ring and (e,f) bookkeeping; mathlib at the pin cannot prove DVR-ness of
`integralClosure ℤ_[p] L` in general — the Serre carrier, exactly as declared since W2).
Nothing else: no uniformity, no measure, no density, no translation form, no uniqueness. The
menu widening (§3) adds INSTANCES (depth-0 legs), not content classes.

## §2. Lean wave plan

### W6c-a — `OM/QpTypeLeafMasters.lean` (axiom-free; new leaf module)
* `stepDecode_general` — §1.2 step decode at head m (template: `chainStep_decode`).
* `leafRam_master` — (R): from `LeafPair (ram H)` box membership at frame (L₀,L₁),
  H+1 ≤ L₀ ≤ L₁, H odd: irreducible + every-bundle (2,1) forcing (templates: `QpTypeH3`
  two-root irreducibility + `ef_of_wildH3` parity, H generalized).
* `leafInert_master` — (I) for m ≥ 0: rescale decode + `ef_of_inert_quadratic`.
* `leafSplit_master` — (S) for k ≥ 0: rescale decode + the `chainSplit_hasType` Hensel
  machinery at general k; conclusion `∃ F, qpType = splitType2`.
* `sepSplit_hasType` / `sepInert_master` — (S0)/(I0) as the k=0/m=0 instances + p=2 digit
  glue (`noRootPairs 2 = {(1,1)}` by `decide`).
* No `sorry`, no axiom; AxCheck block core-only.

### W6c-b — `OM/QpTypeChainAll.lean` (axiom-free; imports W6c-a)
* `chainUnwind` — §1.2 proposition (induction on ms; emptiness branch via
  `chainPair_empty`).
* `transBox_comp` — §1.3 commutation lemma; `transChain_iff_chainPair_translate`.
* Per-leaf all-depth all-translate conclusions:
  `chainAll_split_hasType` (certificate, axiom-free),
  `chainAll_ram_forced` / `chainAll_inert_forced` (irreducible + both-coordinate forcing on
  every bundle, axiom-free).
* No `sorry`, no axiom; AxCheck core-only.

### W6c-c — the re-scope + assembly (edits `OM/ChainMenu.lean` menu section OR a small new
`OM/ChainMenu6.lean`; edits `OM/OmLeafFaithful.lean`; new `OM/FullFaithful.lean`)
* `chainShapes6 n D K σ` := the `chainShapes` emission WITHOUT the `ms ≠ []` filter;
  `omMenu6 n D K σ := omMenu4 ∪ chainShapes6` (or `omMenu5 ∪ (chainLeaves K σ).image
  (chainLit [])` — implementer's choice, with `omMenu5 ⊆ omMenu6` and a
  `mem_omMenu6_cases` discriminator).
* `om_leaf_faithful` re-declared: `hT : T ∈ omMenu6 n D K σ`; `hfib` BYTE-IDENTICAL
  (`fiberOf5`). Docstring gains the W6c re-scope record + the §1.4 GMN reading of the
  depth-0 legs. Scope-#4 form derived back as `om_leaf_faithful_w5` (menu inclusion);
  all downstream consumers byte-unchanged.
* `OM/FullFaithful.lean`: family index `inductive W6Fiber` (sepSplit | sepInert |
  chain (c : Fin 2) (ms : List ℕ) (leaf : ChainLeaf)) with `fiberPred : W6Fiber → …`
  matching `decidedCount6`'s summands EXACTLY (definitional unfolding lemmas) and
  `keyedType : W6Fiber → FactorizationType`; the headline
  `fullFiber_hasType : … fiberPred F (toBoxPair f) → ∃ Fc : QpFactorization 2 f,
  qpType 2 Fc = keyedType F` (hypotheses: menu-side well-formedness ms ∈ msMenu N N,
  leaf ∈ chainLeaves N σ — exactly the index set `decidedCount6` sums over).
  Consumes: masters (a), unwind/translate (b), and `om_leaf_faithful` (existence at
  ram/inert). Plus the capstone companion `montes_n2_full_faithful` (docstring-level
  pairing of `montes_unconditional_n2_full` with `fullFiber_hasType` — statement TBD by
  implementer as a conjunction restatement, NO change to the capstone itself).
* Sep-inert existence: preferred route — `om_leaf_faithful` at the ORDER-0 menu shape via
  the banked order-0 fiber characterization (`Order0`/`ClassifierBridgeFiber2` glue:
  `SepInertCell` digit conditions ⟹ `B.classify = sepShape(inert)`); fallback — admit the
  m = 0 inert literal into `chainShapes6` (requires relaxing `leafOK (inert 0)`… NOT
  preferred: leafOK is consumed by W5 counting theorems; do not touch it — if the glue
  fails, extend `chainLeaves`-emission with a separate `inert0Lit` literal + its own
  dispatch branch in a NEW fiber function `fiberOf6` (then `fiberOf5` derives back). Flag
  whichever route lands for the guardian.

### W6c-d — witnesses, probes, census (extends the evidence blocks; new gates in
`OM/FullFaithfulGates.lean` or in-module)
* Nonempty witnesses: depth-0 inert `y² + 2y + 4` (disc −12 = 4·(−3), −3 ≡ 5 mod 8 ⟹
  unramified quadratic ✓); depth-0 split `y² + 2y + 8` (disc −28 = 4·(−7), −7 ≡ 1 mod 8 ⟹
  square ⟹ split ✓); c=1 translate of the W5 chain gate: `x² − 2x + 5` (then
  f(x+1) = x² + 4 = the landed `chainGatePoly` ✓); one general-m chain witness, e.g. head
  m = 2: `x² + 2⁵` (ChainPair [2] (ram 1): after the m=2 step at ĉ=… implementer verifies
  digits; any machine-checkable member of a `[m], m ≥ 2` fiber suffices).
* Mutation probes (scratch-derive False, record, delete — house pattern): wrong-type keying
  at the depth-0 inert gate (split keying refuted by `sepInert`-style forcing/irreducibility)
  and at the c=1 translate ram gate (split and (1,2) keyings refuted by transported forcing).
  Positive coherence gate per new family.
* Census: `lake env lean LeanUrat/AxChk_baseline.lean` — every capstone footprint
  UNCHANGED (core-only); `fullFiber_hasType` = core + `om_leaf_faithful` exactly; all
  W6c-a/b masters core-only. Full `lake build` green.

### W6c-e — guardian audit #6 + docs
* Codex fresh-context audit of the re-scoped axiom (triple test: statement-map both
  directions — in particular that the menu widening adds only Thm 1.15/1.19/Cor 1.20
  instances; mutation; non-vacuity of the new legs via the W6c-d witnesses).
* `PROJECT_STATE.md` §2 (W6 honest-scope line updated: keying now Montes-faithful in every
  fiber, modulo the one axiom), §5; `SEMANTIC_AUDIT_LOG.md` W6c entry; commit per milestone.

## §3. Scope #5 statement design (for the guardian)

* Menu delta: `omMenu6 ⊇ omMenu5`, new members exactly `{chainLit [] leaf : leaf ∈
  chainLeaves K σ}` (n = 2 only, σ-keyed, window K). These are formally NEW fiber
  predicates for the axiom (digit-form `LeafPair`, not `B.classify`), so their
  statement-map must be displayed PER LITERAL, not gestured at. Note the axiom's fiber
  hypothesis has been digit-form since W4c (`InCell`) and W5c (`ChainCell`); the map below
  is the same kind of reading, at depth 0:
  - **`chainLit [] (ram H)`** (H odd, leafOK): the `LeafPair` conditions v(b₀) = H EXACT
    (box dvd + nonzero digit at H, readable since leafNeed = H+1 ≤ L₀) and
    v(b₁) ≥ (H+1)/2 pin the principal Newton polygon of y² + b₁y + b₀ to the single side
    (0,H)–(2,0): the middle dot (1, v(b₁)) lies strictly above it since
    v(b₁) ≥ (H+1)/2 > H/2. Slope −H/2 with gcd(H,2) = 1 ⟹ d(S) = 1: **Cor 1.20** gives
    exactly one irreducible factor with (e,f) = (2,1). This is the same Cor-1.20 reading
    the W1/W3 window legs receive (there routed through the classify-fiber
    characterization; here directly from the digits) — same cited theorem, new instance
    form; guarded by (R) at ALL odd H (strictly stronger than the banked H ∈ {1,3}
    anchors).
  - **`chainLit [] (inert m)`** (m ≥ 1): v(b₀) = 2m exact (the root-free pair's first
    digit is nonzero — `noRootPairs_fst_ne_zero`), v(b₁) ≥ m: single side (0,2m)–(2,0) of
    slope −m = −m/1 in lowest terms ⟹ e = 1, side degree 2, residual = the digit
    quadratic z² + w̄₁z + w̄₀, root-free hence irreducible: **Thm 1.19 + Cor 1.20** give one
    leaf with (e,f) = (1,2). Guarded by (I).
  - **`chainLit [] (split k)`** (k ≥ 1): v(b₁) = k exact (with nonzero digit, so b₁ ≠ 0),
    v(b₀) ≥ 2k+1, readability gate 2k+1 ≤ L₀. Case b₀ ≠ 0: polygon vertices
    (0, v(b₀))–(1, k)–(2, 0) with DISTINCT slopes (left side slope −(v(b₀) − k) ≤ −(k+1)
    < −k = right side slope): **Thm 1.15** dissects into two coprime width-1 (hence
    linear) blocks, each (e,f) = (1,1). Case b₀ = 0 (ADMITTED by the fiber — Codex pass-2
    gap #1): g = y·(y + b₁) factors LITERALLY into two linear (hence (1,1)) factors — the
    GMN reading applies via the standard split-off of the x-power factor (the paper's
    f = x^{ord₀ f}·f′ convention) and the width-1 side (1,k)–(2,0) for f′; no finite point
    (0, v(b₀)) exists and none is needed. Both cases guarded by (S), whose proof uses only
    v(b₀) ≥ 2k+1 (w₀ = 0 allowed: h̄ = z(z + w̄₁) still has the two distinct simple roots)
    — indeed for split literals the certificate is PROVED outright and the axiom instance
    is redundant in consumers (kept in the menu for uniform emission).
  Ram/inert existence for the new literals rests on the axiom exactly as every
  irreducible-leaf leg has since W2 (the Serre `LocalFactorData` carrier); "no new
  citation" means: same cited theorems (Thm 1.15/1.19/Cor 1.20 + the carrier), new
  INSTANCES, statement-mapped above — the guardian audits this table against the paper
  text per literal.
* Fiber dispatch: byte-identical `fiberOf5`. NO translate parameter enters the axiom
  ((P4d) discipline: translate coverage is DERIVED — §1.3).
* Conclusion: byte-identical (∃ certificate, qpType = σ). No uniformity / rationality /
  measure / density / uniqueness terms — unchanged.
* Anti-vacuity: new legs nonempty at the W6c-d witnesses; small-frame emptiness
  (`chainPair_empty` covers ms = [] via `leafPair_empty`: leafNeed ≥ 1 > 0 = budget slack
  at L₀ < leafNeed).
* Faithfulness-table consistency: §1.4's GMN readings vs the masters' conclusions agree
  per leg (the audit's both-directions check).

## §4. Risks & fallbacks

1. **`ef_of_wildH3` generalization**: if the ϖ-order parity bookkeeping resists general odd
   H, fall back to declaring the master at the heights the menu emits (H = 2j−1 ≤ 2K−1,
   still all-H via induction on j) — the statement is the same; only the proof organization
   changes. Do NOT weaken the statement to specific H.
2. **Sep-inert glue** (`SepInertCell → B.classify = sepShape`): if the banked order-0
   characterization doesn't unfold cleanly at p=2, use the fiberOf6-with-inert0-literal
   fallback (§2 W6c-c) — an extra dispatch branch, guardian-flagged.
3. **Frame-arithmetic thrash in the unwind**: the (L₀ − 2Σms, L₁ − Σms) bookkeeping is
   ℕ-subtraction; keep every step's hypotheses in the `2·Σms + leafNeed ≤ L₀ ≤ L₁` form and
   discharge by omega; below threshold use emptiness, never partial decodes.
4. **Census regression**: any capstone footprint change is stop-the-line (house rule).

## §5. Definition of done

1. `lake build` green; zero `sorry` in scope (the banked Classifier sorry stays the only
   one).
2. Census: capstones core-only byte-unchanged; `fullFiber_hasType` = core +
   `om_leaf_faithful` exactly; W6c-a/b modules core-only.
3. Guardian audit #6 ACCEPT (flags closed or explicitly carried).
4. `PROJECT_STATE.md` + `SEMANTIC_AUDIT_LOG.md` updated; committed.
