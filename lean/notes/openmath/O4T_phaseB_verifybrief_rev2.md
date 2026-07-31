# O4T — the O-4 drainage transfer — Phase-B verify brief, REV 2 (Fable, 2026-07-31)

**Self-contained.** Everything needed to verify the claims is displayed here; external
inputs enter only as NAMED, quoted hypotheses with their statuses. Verifier charge: the
standard two-class protocol (critical error vs justification gap), plus the §7 attack
list. Every claim carries a rigor label (a) known / (b) new proof of known / (c) claimed
new.

(This is REVISION 2, repairing the V30 hostile audit (`V30_o4t.jsonl`; Codex, fresh
context, no-repository read of rev 1 `O4T_phaseB_verifybrief.md`: verdict UNSOUND —
"the core n = 2, 3 ceiling argument appears mathematically sound, including the wild
primes, but the package as stated contains one false unconditional theorem and several
unacknowledged classical dependencies"). V30 CONFIRMED, and rev 2 carries BYTE-STABLE:
the left-edge-shortcut certificate CERT(ii) with its completion quantifier ("the
mechanism is genuinely stable under all lifts"), the case-(b) read level
`k = y(1) + ⌊b₂⌋ + 1` with both corners (`b₁ = ∞`, fractional `b₂`), the `e·d ≥ 4`
order-≤1 exclusion at n = 2, 3, both (CEIL) inequality chains including the
wild/inseparable corners and the termination argument, N3-ENV's instantiation
arithmetic (`Γ⁻(N) = N`), the N3-BRACKET display's inequality DIRECTIONS, the §4
rescope ("the Krasner replacement is mathematically faithful"), and the scope audit
("Nothing in the mathematical N3 proof appears to consume AGR, CU-*, GD-≥2, GMN
termination, or BNS"). It found, and this rev repairs, the items below.)

## 0-pre. Rev-2 changelog (V30 findings → dispositions → repair sites)

| V30 finding | class | disposition | repair site |
|---|---|---|---|
| 5: TR-Q's "`Γ⁻(N) → ∞` since each `Γ(v)` is finite" is FALSE under the stated hypotheses (`Γ ≡ 1` is finite and nondecreasing, yet `{v : Γ(v) > N}` is EMPTY for `N ≥ 1`, so `Γ⁻(N)` is undefined) — the package's one false unconditional theorem | critical | REPAIRED — UNBOUNDEDNESS (`Γ(v) → ∞`) added as a displayed hypothesis of TR-Q; well-definedness of `Γ⁻` and its divergence now PROVED in-line; both consumers re-checked against the strengthened hypotheses (`Γ(v) = v + 1` is unbounded; TR-OM's OL2 shape now says unbounded) | §0 table; §2 TR-Q; §3.4 N3-ENV; §4 TR-OM; §7 charge 7 |
| 2: Lemma REC's `z₀ = 0` corner — "as written, that reasoning is invalid … contains a false 'either way' assertion" (if `z₀ = 0`, steeper-side roots would inflate the count) | justification gap | REPAIRED — the verifier-supplied rescue is adopted and DISPLAYED: new Corollary RES-0 (`R(0) ≠ 0`: the scaled slope factor `G` has unit roots, hence a unit constant term, so zero is NEVER a residual root); Lemma REC's proof is rewritten with `z₀ ≠ 0` throughout and the false "either way" sentence is DELETED | §3.1 Fact UCT; §3.3 Corollary RES-0 + Lemma REC |
| 6: "§3 must stand on Facts NP/SF/HEN alone" is inaccurate — eight further classical facts are consumed, several merely asserted inside RES/SIDE | justification gap / overstatement | REPAIRED — the FULL import inventory is now displayed as named citation-grade Facts EXT/EF/D/GRD/UCT/HRG with pinned sources and per-fact consumption sites; every "NP/SF/HEN alone" claim is replaced by the §3.1 list | §1 pointers; §3.1 rev-2 addendum; §3.3 cite tags; §6 ledger; §7 charge 8 |
| 3 (scope): the recurring "n ≤ 3" technically overstates Theorem N3, "which is written only for 2 ≤ n ≤ 3" (degree 1 trivial but not covered) | overstatement | REPAIRED — headline ranges pinned to 2 ≤ n ≤ 3; explicit n = 1 non-claim displayed (scope note below) | §0 scope note + table + non-claims; §3 header |
| 7 (prose): N3-BRACKET's "at least as fast as the semantic optimum" gloss is "backwards or, at best, misleading: the semantic classifier has no more undecided classes than the canonical one" | prose error | REPAIRED — the in-words gloss now states the floor direction correctly; the display itself (directions confirmed by V30) is byte-stable | §3.4 N3-BRACKET |
| 1, 3 (core), 4: the shortcut mechanism, the case-(b) read level, the `e·d ≥ 4` exclusion at n = 2, 3, both ceiling chains, wild corners, termination | UPHELD | byte-stable (finding 4's "subject to the REC gap" rider is closed by the finding-2 repair) | — |
| 7 (numerics): "the sealed numeric claims cannot be independently verified from this no-repository audit. They are not needed for the proof." | note | no change — the harness, rerun command, and sealed artifacts stand in §5 / §7 charge 9 for repository-access verifiers | — |

**Scope note (V30 finding 3).** Every "n ≤ 3" headline in this brief abbreviates the
proved range **2 ≤ n ≤ 3** of Theorem N3. Degree n = 1 is trivial (f = x + a₀ is always
split, of type (1,1), decided at level 0, with disc = 1 by the empty-product
convention) but it is NOT covered by the stated theorem and is NOT claimed.

Status protocol: rev 2 is PROVED-UNVERIFIED until hostile fresh-context passes accept
it (rev 1's verdict was UNSOUND, driven by the TR-Q critical above).

## 0. What is claimed (status table)

| # | claim | status |
|---|---|---|
| TR-0 | classifier drainage skeleton: an a.e.-finite decision-level function forces env(N) → 0 (measure form) | **PROVED here** (elementary; unconditional) |
| FLOOR | any sound stable classifier is bounded below by the semantic one: U^sem_N ⊆ U^c_N | **PROVED here** |
| TR-Q | quantitative transfer: a NONDECREASING, UNBOUNDED decision-level majorant N(f) ≤ Γ(v_p(disc f)) converts the discriminant tail bound into an explicit envelope for c | **PROVED here** (consumes I-TAIL, displayed; rev 2 — unboundedness is a REQUIRED displayed hypothesis, V30 finding 5) |
| N3 | the canonical order-≤1 classifier at 2 ≤ n ≤ 3: termination, soundness, stability, read ceiling **L(f) ≤ v_p(disc f) + 1** at every prime including wild, hence pointwise OL1 and drainage with explicit envelope | **PROVED here** ((c) as the assembled quantified statement; ingredients (a)/(b) classical — see §6) |
| TR-OM | the same conclusions for the project's AS-BUILT OM-tree classifier at general n | **CONDITIONAL** on the displayed seam (AGR), = tree node O-4's OL1-ii; OPEN (§4) |
| NUM | preregistered falsifier P1–P6, 5 exhaustive configs, 2,534,851 classes | **ALL PASS** (§5) |

Not claimed: anything about the as-built Lean engine's emitted records or acceptance
predicate; degree n = 1 (trivial; scope note above); n ≥ 4; OM order ≥ 2; any
consumption of Bauch–Nart–Stainsby (BNS).

## 1. Setting and definitions

Fix a prime `p` and `n ≥ 1`. `μ` = Haar probability on `Z_p^n`; a coefficient vector
`a = (a_0, …, a_{n−1})` names the monic `f_a = x^n + a_{n−1}x^{n−1} + … + a_0`. `v = v_p`
is the valuation with `v(p) = 1`, extended uniquely to `Q̄_p` (Q-valued on finite
extensions — Fact EXT, §3.1), `v(0) = ∞`. For separable monic `f`, `σ(f)` = its splitting type over
`Q_p`: the multiset of pairs `(e_i, f_i)` (ramification index, residue degree) of the
distinct irreducible factors, `Σ e_i f_i = n`. `disc f` = the discriminant; for monic
`f` with roots `α_1, …, α_n` (integral since `f` is monic over `Z_p`), Fact D (§3.1)
gives

    (D)   v_p(disc f) = 2 · Σ_{i<j} v(α_i − α_j).

**Classes and classifiers.** A level-`N` class is a coset of `(p^N Z_p)^n` in `Z_p^n`
(equivalently: `a mod p^N` coefficient-wise). A *classifier* `c` assigns to every
level-`N` class a splitting type or `⊥`, subject to *stability*: if `c_N(x) ≠ ⊥` and
`x'` refines `x` then `c_{N'}(x') = c_N(x)`. It is *sound* if `c_N(x) = σ ≠ ⊥` implies:
every lift `a ∈ x` has `f_a` separable with `σ(f_a) = σ`. Undecided set and density:

    U^c_N := { a : c_N(a mod p^N) = ⊥ },   env^c(N) := μ(U^c_N)
    (= undec^c(N)/p^{nN} with undec^c(N) the number of undecided level-N classes).

**The semantic classifier** `c^sem`: decide `x` with type `σ` iff every separable monic
lift of `x` has type `σ` (separable lifts always exist; M05 Lemma B). **The
Krasner/discriminant decider** `c^K`: decide `x` (with the common type) iff some lift
`f` of `x` has `2·v_p(disc f) + 1 ≤ N`. Its soundness at every prime is the Krasner–
Hensel local-constancy lemma [M05 Lemma D, hostile-verified: V2_m05_verify item "Lemma
D" upheld]: if `g ≡ f mod p^{2v(disc f)+1}` coefficient-wise, `f` separable, then `g` is
separable of the same type. Consequently `c^K`-decided ⇒ `c^sem`-decided, i.e.
`U^sem_N ⊆ U^K_N`, and

    (K)   U^K_N = { a : v_p(disc f_a) ≥ ⌈N/2⌉ }  (every lift; the event is class-
          measurable since ⌈N/2⌉ ≤ N)   [M05 Theorem E's contrapositive step].

**Displayed import I-TAIL** (verified: M05 Lemma C = V2 item "Lemma C's exponent
arithmetic is sound"; Lean-proved count form `MovesX.XF7.tailCountBound`): for `n ≥ 2`,
every prime, every `m ≥ 0`, with `w := n·v_p(n)`:

    (I-TAIL)   μ{ a : v_p(disc f_a) ≥ m }  ≤  (n−1)·p^{−max(0, ⌈(m−w)/(n−1)⌉)},
    and μ{disc f_a = 0} = 0.

## 2. The transfer skeleton (unconditional)

**Lemma A (cylinder mass; (b), = M05 Lemma A, re-proved here).** For any classifier `c`:
`U^c_N` is clopen, `env^c(N) = μ(U^c_N)`, stability gives `U^c_{N'} ⊆ U^c_N` for
`N ≤ N'`, and `env^c(N) ↓ μ(⋂_N U^c_N)`. *Proof.* `U^c_N` is a disjoint union of
`undec^c(N)` level-`N` cylinders of mass `p^{−nN}` each; stability is the contrapositive
of decidedness persisting; continuity from above for the finite measure `μ`. ∎

**Theorem TR-0 (drainage skeleton).** Let `c` be a stable classifier and suppose there
is a function `N(·)`, defined and finite for μ-a.e. `a`, with: `c` decides the level-`N`
class of `a` for every `N ≥ N(a)`. Then `env^c(N) → 0`. *Proof.* `⋂_N U^c_N ⊆ {a : N(a)`
undefined or `= ∞}`, a μ-null set; Lemma A. ∎ (Direction discipline: this is
SUFFICIENCY only. The a.e. statement does not imply a pointwise one — the V2 finding 1
correction is honored; nothing below uses an equivalence.)

**Proposition FLOOR.** If `c` is sound and stable, then `U^sem_N ⊆ U^c_N` for every `N`;
hence `env^sem(N) ≤ env^c(N)` and `undec^sem(N) ≤ undec^c(N)`. *Proof.* If
`c_N(x) = σ ≠ ⊥`, soundness makes every lift separable of type `σ`, which is the
definition of `c^sem_N(x) = σ ≠ ⊥`. Contrapositive. ∎

**Theorem TR-Q (quantitative transfer; rev 2 — Γ now nondecreasing AND UNBOUNDED, the
V30 critical repair).** Let `c` be stable and suppose there is a nondecreasing,
UNBOUNDED `Γ : Z_{≥0} → Z_{≥0}` (i.e. `Γ(v) → ∞` as `v → ∞`) with: for every separable
monic `f`, `c` decides the level-`N` class of `f` for every `N ≥ Γ(v_p(disc f))`. Then
for every `N`:

    env^c(N) ≤ μ{ a : disc f_a = 0 } + μ{ a : v_p(disc f_a) ≥ Γ⁻(N) }
             ≤ (n−1)·p^{−max(0, ⌈(Γ⁻(N)−w)/(n−1)⌉)},
    where Γ⁻(N) := min{ v : Γ(v) > N } — WELL-DEFINED because unboundedness makes the
    set nonempty; and v < Γ⁻(N) ⇒ Γ(v) ≤ N.

*Proof.* If `a ∈ U^c_N` and `f_a` is separable with `v := v_p(disc f_a) < Γ⁻(N)`, then
`Γ(v) ≤ N` and `c` decides `a`'s class at level `N` — contradiction. So
`U^c_N ⊆ {disc = 0} ∪ {v ≥ Γ⁻(N)}`; apply (I-TAIL). Divergence of `Γ⁻`: for any `v₀`,
once `N ≥ Γ(v₀)` monotonicity gives `Γ(v) ≤ Γ(v₀) ≤ N` for all `v ≤ v₀`, so
`Γ⁻(N) > v₀`; hence `Γ⁻(N) → ∞` and the envelope tends to 0. ∎

(Rev-2 note, V30 finding 5 — a CRITICAL error in rev 1, which asserted "`Γ⁻(N) → ∞`
since each `Γ(v)` is finite": finite-valued and nondecreasing does NOT imply unbounded
— for the constant `Γ ≡ 1`, `{v : Γ(v) > N}` is empty for `N ≥ 1` and `Γ⁻(N)` is
undefined. The repair is the displayed unboundedness hypothesis, which restores both
well-definedness and divergence, proved above. Both consumers instantiate unbounded
majorants: N3-ENV uses `Γ(v) = v + 1`; TR-OM's OL2 shape now displays unboundedness.)

## 3. The canonical order-≤1 classifier at 2 ≤ n ≤ 3, and Theorem N3

Throughout §3: `2 ≤ n ≤ 3`, `p` arbitrary (wild included), `f = f_a` monic of degree
`n`, roots `α_1, …, α_n ∈ Q̄_p` (integral).

### 3.1 Classical facts, displayed

**Fact NP (Newton polygon; (a), classical).** For monic `g ∈ Z_p[x]` of degree `n` with
`g(0) ≠ 0`, let `y_i := v(g_i)` (`g_i` the coefficients, `y_n = 0`) and let `H` be the
lower convex hull of `{(i, y_i)}`. Writing the side slopes as `s = (y_left −
y_right)/Δx` (so sides descend left to right and slopes decrease left to right), the
multiset of root valuations of `g` equals the multiset of side slopes with multiplicity
= horizontal length; at each vertex `(i, y)` of `H`, `v(g_i) = y` exactly (no
cancellation), and at non-vertex points `v(g_i) ≥ H(i)`. If `g(0) = 0`, the same holds
for the sides of finite slope, with `x = 0` read as height `+∞`.

**Fact SF (slope factorization; (a)).** Grouping the roots by valuation, `g = ∏_s g_s`
with `g_s := ∏_{v(β)=s}(x − β)`. Each `g_s ∈ Z_p[x]`: the root multiset with a fixed
valuation is `Gal(Q̄_p/Q_p)`-stable (Galois preserves `v`), so the coefficients are
Galois-fixed integral elements. `deg g_s` = the length of the slope-`s` side.

**Fact HEN (coprime Hensel lifting; (a)).** For monic `G ∈ Z_p[u]` with
`Ḡ = φ̄·ψ̄`, `gcd(φ̄, ψ̄) = 1` in `F_p[u]`, there is a unique monic factorization
`G = Φ·Ψ` lifting it. If `Ḡ` is irreducible then `G` is irreducible and `Q_p[u]/(G)` is
the unramified extension of degree `deg G`.

**Rev-2 addendum (V30 finding 6): the FULL import inventory.** Rev 1 claimed §3 stands
on NP/SF/HEN alone; V30 correctly listed further classical facts consumed inside the
§3.3 proofs ("standard classical facts, and none looks false, but they are not
consequences of NP/SF/HEN alone and several are merely asserted inside RES or SIDE").
They are now DISPLAYED as named citation-grade imports — all rigor label (a) classical
(or one-line consequences of the others, proved where so marked); consumption sites
named per fact; citation pins follow the repo's standing practice (chapter + section
certain; proposition numbers carried with the same confidence flags the repo's own
audits use — `M16-zf-serre_fable.md` §2, `docs/MATH_COMPLETION_TREE` LIT-2/LIT-3):

**Fact EXT (unique valuation extension; Galois invariance; (a)).** `v = v_p` extends
uniquely to a valuation on `Q̄_p`, Q-valued on each finite extension `L`
(`w = (1/[L:Q_p])·v∘N_{L/Q_p}`), and every `σ ∈ Gal(Q̄_p/Q_p)` preserves it (`w∘σ` is
another extension; apply uniqueness). [Neukirch, *Algebraic Number Theory*, Grundlehren
322 (1999), Thm. II.4.8 (high-confidence pin, repo precedent M16 §2); Serre, *Local
Fields* (GTM 67), Ch. II §2.] Consumed: the §1 setting line; Fact SF's Galois
stability; Fact UCT below.

**Fact EF (fundamental identity + denominator bound; (a)).** For finite `L/Q_p`:
`e(L/Q_p)·f(L/Q_p) = [L:Q_p]`; the value group of `w` on `L^×` is `(1/e)Z`, so for
`β ∈ L^×` the lowest-terms denominator of `w(β)` divides `e(L/Q_p)`, which divides —
in particular is at most — `[L:Q_p]`. [Serre, *Local Fields*, Ch. II §3 (complete
discretely valued case, `Σeᵢfᵢ = [L:K]` with one prime — the repo's LIT-2 pin);
Neukirch II §6 (Thm. 6.8-region; number flagged per the M16 audit).] Consumed: Lemma
SIDE(i)'s `e | e(Q_p(β)/Q_p)` and `[Q_p(β):Q_p] ≥ e`.

**Fact D (discriminant = root differences; (a)).** For monic `f` of degree `n` with
roots `α_i`: `disc f = (−1)^{n(n−1)/2}·Res(f, f′) = ∏_{i<j}(α_i − α_j)²`, whence the §1
display `(D)` by `v`-additivity (Fact EXT). [Lang, *Algebra*, rev. 3rd ed. (GTM 211),
Ch. IV §8 (resultant/discriminant; proposition number flagged for page verification);
Cohen, *A Course in Computational Algebraic Number Theory* (GTM 138), §3.3 — the
coefficient-side resultant form is also what the §5 harness computes.] Consumed: both
(CEIL) chains in Theorem N3; the class-measurability of `{v_p(disc f_a) ≥ m}`.

**Fact GRD (Gauss graded ring is a domain; initial forms multiply; (a)).** For `h ∈ Z`,
`w_h(Σ c_j x^j) := min_j (v(c_j) + j·h)` is a valuation on `Q_p[x]`; its associated
graded ring is `F_p[x̄][π̄^{±1}]` (a Laurent-polynomial ring over a field), a DOMAIN;
consequently initial forms are multiplicative: `in_w(FG) = in_w(F)·in_w(G)`.
[In-project: GD23 rev 2 §3, the order-≤1 GAUSS-g/VAL-g layer proved outright over an
arbitrary complete DVR — the layer V26 confirmed ("no critical error found");
literature: MacLane, Trans. AMS 40 (1936) / GMN, Trans. AMS 364 (2012) §1, pinned via
`docs/GMN_citations.md` + `LITUNIT_2026-08-01.md`.] Consumed: Lemma RES.

**Fact UCT (unit constant term; one line from EXT, proved here).** A monic `G ∈ Z_p[u]`
all of whose roots are units has `G(0) = ±∏(roots)` with `v(G(0)) = Σ 0 = 0` (EXT's
multiplicativity): a unit; so `Ḡ(0) ≠ 0`. Displayed because V30 identified it as
load-bearing and unstated. Consumed: Corollary RES-0, hence Lemma REC.

**Fact HRG (Hensel factors ↔ root groups; one line from HEN + EXT, proved here).** In
Fact HEN's factorization `G = Φ·Ψ`: the roots of `Φ` are EXACTLY the roots of `G` whose
residue is a root of `φ̄`, likewise `Ψ`/`ψ̄`. *Proof.* Roots of the monic integral `Φ`
are integral and reduce to roots of `Φ̄ = φ̄`; same for `Ψ`; coprimality makes the two
residue root sets disjoint; every root of `G` is a root of `Φ` or of `Ψ`. ∎ [Textbook
form: Neukirch II §4, Prop. 4.6-region — the repo's LIT-3 pin, numbers to confirm at
declaration.] Consumed: Lemma SIDE(ii)'s per-factor root bookkeeping.

(I-TAIL remains the one EXTERNAL named import, §1 — V30: "as acknowledged".)

### 3.2 The classifier (pinned policy — this definition IS the object of N3)

`c^can` is computed by the following walk on a representative, reading coefficient
digits; "level `k` consumed" means digits at indices `0 … k−1` were read. The verdict at
level `N` is the walk's output if the walk completes with all consumption `≤ N`, else
`⊥`. (Digits of any `Z`-polynomial value in `a` below level `k` are functions of the
digits of `a` below level `k`, so all reads are class reads.)

* **Step 0** (consumes level 1): factor `f̄ ∈ F_p[x]`. Each simple irreducible factor of
  degree `d`: certified factor `(1, d)` [Fact HEN applied to the coprime split of `f̄`].
  Each repeated root `r` (multiplicity `m ≥ 2`; at `n ≤ 3` repeated factors are linear):
  open a *cluster step* `(c := r, m, λ_prev := 0)`.
* **Cluster step `(c, m, λ_prev)`**: put `g := f(x + c)`, `y_i := v(g_i)`. Scan levels
  `k = λ_prev + 1, λ_prev + 2, …`; at scan level `k` call `i < n` *resolved* if
  `y_i < k` (then `y_i` is known exactly, from digits `< k`), else *unresolved*
  (knowledge: `y_i ≥ k`); `i = n` is always resolved (`y_n = 0`). Let `x₀` = least
  resolved index and `H_res` = the lower hull of the resolved points. **Certify** iff
  - (C1) every unresolved `i > x₀` has `k > H_res(i)` (strictly above the resolved
    hull), and
  - (C2) `x₀ = 0`; or `x₀ = 1` and `k > y_1 + s_r` and `k > y_1 + λ_prev`, where `s_r`
    = the slope of the first side of `H_res` (the *left-edge shortcut*; it certifies an
    extra factor `(1,1)`). `x₀ ≥ 2` never certifies.
  On certification, process the sides of `H_res` of slope `s > λ_prev`, `s = h/e` in
  lowest terms, length `ℓ = e·d`:
  - `d = 1`: certified factor `(e, 1)`.
  - `d ≥ 2` (then `e = 1`, since `e·d ≥ 4 > n` otherwise): read the *residual*
    `R(z) = Σ_j r_j z^j`, `r_j` = the digit of `g_{i₁+j}` at level `y₁ − j·h` when
    `(i₁+j, ·)` lies on the side line, else `0` (all these digits are below `k`).
    Factor `R` over `F_p`: each simple irreducible factor of degree `d′` certifies
    `(1, d′)`; each repeated root `z₀` of multiplicity `m′ ≥ 2` opens the cluster step
    `(c + z₀·p^h, m′, λ_prev := h)`.
  `L(f)` := the maximum certify-level `k` over all steps (`≥ 1` for step 0).

### 3.3 Correctness lemmas

Write `β_j := α_j − c` and `b_j := v(β_j)` at a given cluster step, sorted
`b_1 ≥ b_2 ≥ …`. **Invariant (I1)**: at every cluster step, the roots with
`v(α − c) > λ_prev` are exactly `m ≥ 2` in number, and `b_1 = ∞` is possible only for
one root (`f` separable). *Proof of (I1) at step 0*: the roots reducing to the repeated
residue `r` are exactly those with `v(α − r) ≥ 1 > 0`; multiplicity of `r` in `f̄` = the
count. *Propagation*: below (Lemma REC). ∎

**Lemma RES (residual = reduction of the scaled slope factor; (b) — the order-1
instance of the GD23-verified graded multiplicativity).** Let `s = h ∈ Z` (`e = 1`) be a
side of the true hull of `g`, of length `d`, `g_h` the slope factor (Fact SF),
`G(u) := p^{−hd}·g_h(p^h u) ∈ Z_p[u]` (monic; integral since its roots `β/p^h` are
units). Then the residual `R` of §3.2 equals `c̄·Ḡ` for a scalar `c̄ ∈ F_p^×`.
*Proof.* Let `w` be the Gauss valuation on `Q_p[x]` with `w(x) = h`:
`w(Σ c_j x^j) = min_j (v(c_j) + jh)`. Its graded ring is `F_p[x̄, π̄^{±1}]` (`π̄` the
image of `p`), a domain, so initial forms are multiplicative [Fact GRD, §3.1 — rev 2:
the step V30 flagged as a bare assertion is now a displayed import]: `in_w(g) = in_w(g_<) ·
in_w(g_h) · in_w(g_>)` where `g_<` (roots of valuation `> h`) has `in_w(g_<) = x̄^{deg}`
(the leading term is the unique `w`-minimal one: every other coefficient of `g_<` has
`v(c_j) > (deg−j)h`), and `g_>` (roots of valuation `< h`) has `in_w(g_>) = c̄₀ π̄^{v(c₀)}`
(the constant term is the unique minimal one). So along the slope-`h` line of `g`, the
on-line digits are, up to one monomial factor (a scalar and a shift of the lattice
window), the on-line digits of `g_h`; and those are precisely the reductions of the
coefficients of `G`. ∎

**Corollary RES-0 (zero is never a residual root; rev 2 — the V30-supplied rescue,
displayed).** In the setting of Lemma RES, `R(0) ≠ 0`; in particular no residual root
— simple or repeated — equals `0`, and every recursion shift satisfies
`v(z₀·p^h) = h` EXACTLY. *Proof.* `G` is monic with all roots `β/p^h` units (the
side's roots have `v(β) = h` exactly), so `G(0)` is a unit and `Ḡ(0) ≠ 0` [Fact UCT,
§3.1]; `R = c̄·Ḡ` with `c̄ ∈ F_p^×` (Lemma RES), so `R(0) = c̄·Ḡ(0) ≠ 0`. ∎
(Independent confirmation from the read itself: `r₀` is the digit of `g_{i₁}` at its
exact valuation `y₁` — the side's left endpoint is a hull vertex, where Fact NP gives
no cancellation — so `R(0) = r₀ ≠ 0` directly.)

**Lemma SIDE (side verdicts; (b), classical content).** With the true hull certified on
the relevant range (see Lemma CERT):
(i) a side of slope `h/e` in lowest terms with `d = 1` certifies one irreducible factor
of type `(e, 1)`;
(ii) on a side with `e = 1`, `d ≥ 2`: each simple irreducible factor `ψ` of `R` of
degree `d′` certifies one factor of type `(1, d′)`; the roots of `g` on the side whose
scaled reduction is a repeated root `z₀` of `R` of multiplicity `m′` are exactly `m′`
in number, and all satisfy `v(α − c − z₀p^h) > h`.
*Proof.* (i) The side's roots all have `v(β) = h/e` with denominator exactly `e`, so
`e | e(Q_p(β)/Q_p)` and `[Q_p(β):Q_p] ≥ e` [Fact EF, §3.1]; the slope factor
`g_{h/e} ∈ Z_p[x]` (Fact SF) has degree `e·1 = e` and contains `β`: it is irreducible
with `e = e`, `f = 1`.
(ii) By Lemma RES, `Ḡ = c̄⁻¹R`. Factor `R = ∏ ψ_i^{m_i}` into pairwise-coprime powers;
Fact HEN gives `G = ∏ G_i`, `Ḡ_i = (unit)·ψ_i^{m_i}`. For `m_i = 1`, `ψ_i` irreducible
of degree `d′`: `G_i` is irreducible with unramified root field of degree `d′`; its
roots `u` give roots `β = p^h u` of `g` with `Q_p(β) = Q_p(u)` (`h ∈ Z`), so the factor
has type `(1, d′)`. For a repeated root `z₀` (`ψ_i = z − z₀`, `m_i = m′ ≥ 2`): `G_i` is
monic of degree `m′` with `Ḡ_i = (unit)(u − z₀)^{m′}`, so its `m′` roots satisfy
`u ≡ z₀ (mod 𝔪)` [Fact HRG, §3.1], i.e. `v(β − z₀p^h) > h`; no other root of `g` does
(other sides have `v(β) ≠ h`; other residual classes reduce elsewhere). ∎

**Lemma REC (refinement invariant; rev 2 — the V30 `z₀ = 0` repair).** Opening
`(c′ = c + z₀p^h, m′, λ_prev = h)` from a repeated residual root restores (I1): exactly
the `m′` roots of Lemma SIDE(ii) satisfy `v(α − c′) > h`. *Proof.* Those `m′` roots do,
by SIDE(ii). By Corollary RES-0, `z₀ ≠ 0`, so `v(z₀p^h) = h` EXACTLY. Any other root
`α` falls in one of three exhaustive cases: if `v(α − c) < h`, then
`v(α − c′) = v(α − c) < h` (ultrametric; the minimum in `min(v(α−c), h)` is uniquely
attained); if `v(α − c) = h` with residual class `≠ z₀` (a slope-`h`-side root outside
SIDE(ii)'s group), then `(α − c)/p^h − z₀` is a unit — its reduction is the nonzero
residue difference — so `v(α − c′) = h`; if `v(α − c) > h` (a steeper-side root,
processed separately by the certificate), then `v(α − c′) = min(v(α − c), h) = h`,
again uniquely attained because `z₀ ≠ 0`. In every case `v(α − c′) ≤ h`, so no root
outside SIDE(ii)'s group enters. Each certified or recursed group is disjoint, and
degrees add to `m`. ∎

(Rev-2 note, V30 finding 2 — a justification gap in rev 1, whose proof reasoned about
a `z₀ = 0` corner and asserted "the count in SIDE(ii) is exact either way": V30
correctly rejected that reasoning as invalid ("if `z₀ = 0`, all roots on steeper sides
would also satisfy `v(α − c′) > h`, contradicting the claimed exact count"). The
repair is V30's own rescue, now displayed as Corollary RES-0: zero is never a residual
root, so the corner is EMPTY and the false sentence is deleted.)

**Lemma CERT (the certificate is sound).** At the certify level `k`:
(i) all unresolved `i` have TRUE `y_i ≥ k`; resolved values are true; hence by (C1) the
resolved hull is the true hull on `[x₀, n]`.
(ii) if (C2) fires with `x₀ = 1`: the true hull has a vertex at `(1, y_1)`, the leftmost
true side has length 1 and integer slope `v(g_0) − y_1 > max(s_r, λ_prev)` (or
`g_0 = 0`), so `g` has exactly one root with `v(β) > s_r`, Galois-fixed, hence in
`Q_p`: a certified `(1,1)` factor, belonging to the current cluster (`slope > λ_prev`).
*Proof.* (i) Unresolved means no nonzero digit below `k`. On `[x₀, n]` the hull heights
are `≤ max resolved y < k` and unresolved points are `≥ k`, strictly above, so they are
hull-irrelevant in every completion. (ii) The hull on `[1, n]` is true by (i). Slopes on
a lower hull ending at `(n, 0)` with all `y ≥ 0` are `≥ 0`, so `H_res(i) ≤ y_1` there.
The point `(0, v(g_0))` has `v(g_0) ≥ k > y_1 + s_r`, so in the full true hull the
vertex condition at `x = 1` holds: `v(g_0) − y_1 > s_r` = the slope on the right. A
length-1 side carries exactly one root, of valuation `v(g_0) − y_1` (integer, or `∞`
when `g_0 = 0`, i.e. the root `c` itself); a one-element Galois-stable root set is
`Q_p`-rational. `k > y_1 + λ_prev` makes its slope `> λ_prev`. ∎

### 3.4 Theorem N3

**Theorem N3.** Let `2 ≤ n ≤ 3`, `p` any prime, `f` monic separable of degree `n` over
`Z_p`, `v := v_p(disc f)`. Then the walk of §3.2 terminates, every digit it consumes
lies below level `L(f)`, its output is `σ(g)` for EVERY monic `g ≡ f mod p^{L(f)}`, and

    (CEIL)   L(f) ≤ v + 1.

Consequently `c^can` is a stable, sound classifier which decides the level-`N` class of
every separable `f` at every `N ≥ v_p(disc f) + 1` — pointwise OL1 with the LINEAR
majorant `Γ(v) = v + 1`.

*Proof.* **Stability and per-lift correctness.** All reads are digits below the
certify levels; the certificates and verdicts of §3.3 are statements about the true
hull and residuals of ANY completion of the read digits (Lemma CERT (i)/(ii) quantify
over completions), and Lemmas SIDE/REC certify factor types from exactly those data. So
the walk on any lift `g` of the level-`L(f)` class reads the same digits, certifies the
same factors, and each certificate is TRUE OF `g`. The certified degrees sum to `n`
(step 0 partitions `n` into simple factors + clusters; each cluster step partitions its
`m` by (I1) + SIDE + REC), so the output is the full type `σ(g)`.

**Ceiling.** Consider any cluster step, with `b_1 ≥ b_2 ≥ … ≥ b_n` as in §3.3 (the
`m ≥ 2` cluster roots are `b_1, …, b_m > λ_prev`; `b_2 < ∞` by separability). Note
`Σ_j b_j = v(g_0) = y(0)` and `Σ_{j≥2} b_j = y(1)` when `(1, y(1))` is a vertex.
*Case (a): `b_1 = b_2`.* The leftmost true side has length `≥ 2`, so (C2) requires
`x₀ = 0`: the scan certifies at `k = y(0) + 1` (the vertex `(0, y(0))` resolves exactly
there — Fact NP no-cancellation — and then (C1) holds since every unresolved point is
`≥ k > y(0) ≥ H(i)`; the left-edge shortcut cannot fire earlier: firing needs
`v(g_0) ≥ k`, and by CERT(ii) it would force `b_1 > b_2`). Bound, using (D) and
`v(α_i − α_j) ≥ min(b_i, b_j)` with equality when `b_i ≠ b_j` (ultrametric):
`b_1 + b_2 ≤ 2·v(α_1 − α_2)` and `b_j ≤ v(α_2 − α_j)` for `j ≥ 3`, so

    k − 1 = y(0) = b_1 + b_2 + Σ_{j≥3} b_j ≤ 2·δ_{12} + Σ_{j≥3} δ_{2j} ≤ 2·Σ_{i<j} δ_{ij} = v.

*Case (b): `b_1 > b_2`.* Then the leftmost true side has length 1, so `b_1 ∈ Z ∪ {∞}`
and `(1, y(1))` is a true vertex with `y(1) ∈ Z`; the first slope right of it is `b_2`.
The shortcut fires at `k = y(1) + ⌊b_2⌋ + 1` (then `k > y(1) + b_2 ≥ y(1) + s_r` — if
`b_2 ∉ Z` the resolved-hull slope `s_r` equals `b_2` once (C1) holds — and
`k > y(1) + λ_prev` since `b_2 > λ_prev`; `x = 0` stays unresolved up to that level
because `y(0) = y(1) + b_1 ≥ y(1) + ⌊b_2⌋ + 1 = k`, as `b_1 ∈ Z`, `b_1 > b_2` force
`b_1 ≥ ⌊b_2⌋ + 1`). Bound: `δ_{12} = b_2` exactly (strict ultrametric), `b_j ≤ δ_{2j}`
for `j ≥ 3`:

    k − 1 = y(1) + ⌊b_2⌋ ≤ 2·b_2 + Σ_{j≥3} b_j ≤ 2·δ_{12} + Σ_{j≥3} δ_{2j} ≤ v.

Residual digits lie at levels `≤ y(x₀) < k`. Step 0 consumes level `1 ≤ v + 1`. Every
step obeys `k ≤ v + 1`, so `L(f) = max k ≤ v + 1`, and in particular each scan halts;
recursion terminates because `λ_prev` strictly increases and stays `≤ δ_{12} ≤ v/2`.
Finally, `f̄` separable (`v = 0`) means no cluster opens: `L = 1 = v + 1`. ∎

**Corollary N3-ENV (drainage at 2 ≤ n ≤ 3, every prime, with envelope).** By TR-Q with
`Γ(v) = v+1` — nondecreasing AND unbounded, so the rev-2 TR-Q hypotheses hold, and
`Γ⁻(N) = min{v : v+1 > N} = N` — for `2 ≤ n ≤ 3`, every prime including wild:

    env^can(N) ≤ (n−1)·p^{−max(0, ⌈(N−w)/(n−1)⌉)},  w = n·v_p(n)  →  env^can(N) → 0.

**Corollary N3-BRACKET (the two-sided transfer display).** For `2 ≤ n ≤ 3`, every `N`:

    undec^sem(N) ≤ undec^can(N) ≤ #{level-N classes with v_p(disc) ≥ N on every lift}
                 = undec^K(2N−1),

(left: FLOOR + N3-soundness; right: N3 (CEIL) applied to every lift + (K)). In words
(rev 2 — the V30 direction fix): the SEMANTIC classifier is the FLOOR — it never has
MORE undecided classes than the canonical one — and the canonical classifier is at
most as slow as the Krasner decider run at DOUBLE the level; relative to Krasner the
transfer shift is multiplicative in the canonical classifier's favor, not an additive
lag. (Rev 1 glossed the left inequality as the canonical classifier being "at least as
fast as the semantic optimum is required to be" — backwards/misleading per V30 finding
7; the display itself was confirmed and is unchanged.)

## 4. The seam: transfer to the AS-BUILT classifier at general n (conditional)

The project's intended instance is not `c^can` but the as-built OM verdict-tree
classifier (Lean `ClassifierSpec` `canonical`; no executable extraction). The honest
transfer is:

**Theorem TR-OM (conditional).** Let `c^OM` be the as-built classifier (stable by its
Lean law `canonical_stable`; sound by `VPSound`). Assume the displayed seam:

> **(AGR)** For every prime `p` and every monic separable `f` of degree `n`, the
> canonical OM run on `f` terminates with a finite certificate: there is
> `N^OM(f) < ∞` such that `c^OM` decides the level-`N` class of `f` for every
> `N ≥ N^OM(f)`.

Then `env^OM(N) → 0` at every prime (TR-0 + (I-TAIL)'s null discriminant locus =
exactly M05 Prop 5.1's shape), and `undec^sem(N) ≤ undec^OM(N)` (FLOOR). If moreover
`N^OM(f) ≤ Γ(n, v_p(disc f))` with `Γ` nondecreasing AND unbounded in `v` (the OL2
shape; unboundedness required by the rev-2 TR-Q, V30 finding 5), TR-Q gives the
explicit envelope with `Γ⁻(N)` in the exponent.

**Status of (AGR) — OPEN; the exact decomposition on record (tree DELTA-2 consumer
walk):** `O-4 OL1-ii ← CU-2 + CU-4 + GMN Cor 4.19`, i.e.
* (S1) termination of the canonical run at finite order for separable `f` — GMN
  Trans. AMS 364 (2012), Cor 4.19 [LITERATURE, pinned in `docs/GMN_citations.md`; the
  "≤ ind(f) nontrivial steps" operational strengthening needs the charging argument —
  V2 item 4's caveat, consumed at GD-7/OL1-i];
* (S2) CU-2 (no-phantom: every emitted record of the run is the GMN datum of its
  chain) — OPEN over the GD-1..GD-6 residue; the GD layer is VERIFIED at order ≤ 1 +
  DEVID (V26 upheld exactly that) and REJECTED beyond it (V26: 3 criticals on the
  general-order composition);
* (S3) CU-4/F4-C (the built acceptance predicate accepts at `N ≥ N*(𝐇(f))`, the
  per-branch decision level with majorant property (N*-MAJ)) — OPEN; the CU-1 proof
  that would feed it was REJECTED at V27 (five defects, including the (N*-MAJ)
  prefix-monotonicity break in the IH invocation);
* (S4) the "finite run ⇒ finite stable certificate" step is a PROOF obligation, not an
  observation (V2 finding 3) — at `n ≤ 3` THIS IS EXACTLY WHAT §3 PROVES for the
  canonical run (the certificates of Lemma CERT are the finite stable certificates,
  perturbation-stable by construction).

**What N3 changes about the seam.** At `n ≤ 3` the canonical OM tree never leaves
order ≤ 1 (a repeated residual factor on a side with `e ≥ 2` needs side length
`e·d ≥ 4 > n`; repeated residuals with `e = 1` are handled by refinement) — i.e. the
run sits entirely inside the V26-verified GD23 perimeter, and §3 discharges the
MATHEMATICAL half of (AGR) there, with the sharp majorant `Γ(v) = v + 1`. The remaining
`n ≤ 3` residue is pure engine conformance (the as-built engine implements the §3.2
policy and its acceptance fires at the §3.2 certificate) — GD-4/GD-6/CU-4 territory, no
new mathematics. At `n ≥ 4` the mathematical half is also open (order-≥2 states; the
V26-rejected general-order composition is the missing layer).

**Rescope note (churn classification, under the standing authority).** The dispatch
charge displayed the target as `undecided_OM(N) ≤ undecided_sem(N + shift)`. As
literally written this is NOT the provable direction: `undec_sem ≤ undec_OM` always
(FLOOR — the semantic classifier is the floor), so an upper bound on `undec_OM` through
`undec_sem` can only pass through the computable Krasner SUPERSET of the semantic
undecided locus. The honest transfer inequality is N3-BRACKET:
`undec^can(N) ≤ undec^K(2N−1)` — Krasner level, factor-2 shift, in the classifier's
favor — and its general-`n` conditional analogue via TR-Q. The charge's inequality is
RESCOPED to this display; nothing else in the charge is affected. (At `n = 2` the
numerics show `undec^can(N) = undec^sem(N)` EXACTLY at every probed level and prime —
see §5 — so no inequality of the charged form with a nontrivial shift could be strict
there anyway.)

## 5. Numeric falsifier record (preregistered; run BEFORE this brief was written)

Harness: `verification/openmath/O4T_transfer_check.py` (new; imports the N1-exhaust
exact `n = 2` semantic law and the exact `padic_types` oracles). Sealed results:
`verification/openmath/results/O4T_transfer_results.json`; log
`verification/openmath/logs/O4T_transfer_20260731_155929.log`. Exhaustive exact-integer
scans, five configs, 2,534,851 depth-`C` classes total, wild cells included:

    n=2: (p=2, C=10) (p=3, C=6) (p=5, C=4);   n=3: (p=2, C=5) (p=3, C=4).

Preregistered predictions → results:
* **P1 SOUND** (walker verdict = exact oracle type, every decided class): 0 mismatches.
* **P2 FLOOR** (no class decided by the walker while semantically undecided; `n = 2`
  by the exact law, `n = 3` by certified lift-disagreement witnesses): 0 violations.
* **P3 CEIL** (`L ≤ v_p(disc)+1` per separable representative): 0 violations —
  AND max(L − v − 1) = 0 in EVERY config: the (CEIL) bound is attained, i.e. sharp.
* **P4 KRA** (`L ≤ max(1, 2v+1)`): 0 violations (implied by P3; independently checked).
* **P5 ENV** (N3-ENV envelope + monotonicity of `undec^can(N)`): 0 violations.
* **P6 LEAN2** (`n = 2`: `undec^can(N) ≤ (⌊N/2⌋+1)p^{−(N−1)}`, the K-12 hExhaustP
  envelope shape): 0 violations.

Headline tables (fractions of Haar mass; `sem` = exact at `n = 2`, certified lower
bound at `n = 3`):

    n=2 p=2:  N:      1     2      3      4       5        ...  10
              OM:   .5    .25   .125   .0625   .03125     ...  9.77e-4
              sem:  .5    .25   .125   .0625   .03125     ...  9.77e-4   (EQUAL)
              K:    .5    .5    .5     .5      .25        ...  .0625
    n=2 p=3:  OM = sem = .3333 .1111 .0370 .01235 .004115 .001372 ; K lags 1-2 levels
    n=2 p=5:  OM = sem = .2 .04 .008 .0016 ; K = .2 .2 .04 .04
    n=3 p=2:  OM: .5 .1875 .09375 .046875 .02148 ; sem-lower: .5 .1875 .09375 .04053 0*
    n=3 p=3:  OM: .3333 .08642 .02881 .009602 ; sem-lower: .3333 .08642 .02820 0*
        (* the exhaustive lower bound loses witnesses at the top levels N ~ C — a
           depth artifact, not a classifier gap; the P2 pointwise check is what binds.)

**Findings.** (i) The ceiling `L ≤ v+1` is exact — the same `δ+1` precision shape as
BNS Thm 3.13 (flagged consistency; BNS is NOT consumed). (ii) At `n = 2` the canonical
classifier is EXACTLY semantically optimal on all 1.97M probed classes (undec^can =
undec^sem level-by-level, p ∈ {2,3,5}) — recorded as an observation, NOT claimed as a
theorem. (iii) `undec^can` beats the Krasner decider by the predicted factor-2 level
shift throughout. (iv) At `n = 3` the walker's undecided mass tracks the certified
semantic lower bound to within the depth artifact.

## 6. Rigor labels and honesty ledger

* TR-0/FLOOR/TR-Q: (b) — elementary measure bookkeeping; the skeleton is M05 Lemma A
  re-proved (V2 upheld it) with the a.e./pointwise direction discipline honored.
* Facts NP/SF/HEN + (rev 2) EXT/EF/D/GRD/UCT/HRG: (a) classical, ALL displayed in
  §3.1 with sources and per-fact consumption sites. Rev 1's "NP/SF/HEN alone"
  undercounted the import surface (V30 finding 6); the §3.1 rev-2 addendum is the
  corrected inventory. Citation pins follow the repo's standing practice — chapter +
  section certain, proposition numbers carried with confidence flags where the repo's
  own audits flag them (M16 §2; `docs/MATH_COMPLETION_TREE` LIT-2/LIT-3).
* Lemma RES: (b) — the order-1 shadow of the GD23 unit's GAUSS-g/VAL-g/DEVID layer
  (V26-verified); proved here for `e = 1` on top of the displayed Fact GRD (rev 2:
  the graded-domain / initial-form-multiplicativity steps are NAMED imports, no
  longer bare assertions).
* Theorem N3 + corollaries: (c) AS AN ASSEMBLED, EXPLICITLY QUANTIFIED STATEMENT about
  the pinned §3.2 policy (the `v+1` ceiling with the left-edge-shortcut read policy,
  every prime, `2 ≤ n ≤ 3`); the mathematical substance is (a/b)-classical (order-1
  Ore–Montes + Hensel + Krasner-free direct arguments). The SHAPE (`δ+1` precision)
  matches BNS Thm 3.13, which remains LITERATURE-CANDIDATE, route-R-QNT, unconsumed.
* TR-OM: conditional; (AGR) OPEN with the §4 decomposition and statuses quoted from
  the record (V2, V26, V27) — nothing about CU-1/CU-2/CU-4/GD-≥2 is claimed here.
* NOT CLAIMED: as-built engine conformance at any `n`; `n ≥ 4` (any part); OM
  order ≥ 2; semantic OPTIMALITY of `c^can` (numeric observation only); any rate for
  `c^OM` at general `n`; any Lean artifact (no Lean edits in this unit).
* The walk is POLICY-PINNED: (CEIL) is a statement about the §3.2 scan policy. A
  different sound policy changes `L` by bounded amounts but the theorem is stated and
  tested only for the pinned one (harness flag F2).

## 7. Verification charges (attack list)

1. **Lemma CERT (ii)** — the left-edge shortcut. Attack the completion quantifier: does
   `k > y_1 + s_r` really force the vertex in EVERY completion, including `g_0 = 0`,
   and is `s_r` (computed from the RESOLVED hull) the true right-slope at that moment?
   (§3.3's proof: hull-on-`[1,n]` is true by (C1) + slopes `≥ 0`.)
2. **Case (b) of (CEIL)** — the claim `y(0) ≥ k` (i.e. `x = 0` still unresolved when
   the shortcut fires), which used `b_1 ∈ Z`, `b_1 > b_2 ⇒ b_1 ≥ ⌊b_2⌋ + 1`. Check the
   `b_1 = ∞` (`g_0 = 0`) corner and the fractional-`b_2` corner.
3. **Lemma REC** — the `z₀ = 0` corner and the exact-count claim (`m′` and no others);
   check against SIDE(ii)'s Hensel factor bookkeeping. (Rev 2: the corner is now
   excluded by Corollary RES-0 — attack RES-0 itself and the rewritten three-case
   split.)
4. **The `e·d ≥ 4` exclusion** — verify no `n ≤ 3` configuration reaches a repeated
   residual on an `e ≥ 2` side, including at `p = 2` (wild) and at refined clusters.
5. **Lemma RES** — the monomial-factor bookkeeping (`in_w(g_<) = x̄^{deg}`,
   `in_w(g_>) = c̄₀π̄^{v}`): check both unique-minimality claims.
6. **(D) and the pairwise bounds** — `v(disc) = 2Σδ_{ij}` for monic integral-root
   polynomials, and each `≤`-step in the two ceiling chains (any slack direction error
   breaks (CEIL)).
7. **TR-Q's `Γ⁻`** — off-by-one at the tail threshold (`v < Γ⁻(N) ⇒ Γ(v) ≤ N`), and
   the rev-2 UNBOUNDEDNESS hypothesis: is `Γ⁻` well-defined and divergent exactly as
   now displayed (V30 finding 5's constant-`Γ` counterexample must be excluded by the
   hypothesis itself, not by prose), and does every consumer instantiate an unbounded
   `Γ`?
8. **§4 (AGR)** — confirm nothing in §§2–3 silently consumes (AGR) or any CU-*/GD-≥2
   item; §3 must stand on the §3.1 named imports alone (NP/SF/HEN + the rev-2
   inventory EXT/EF/D/GRD/UCT/HRG — V30 finding 6 forced the enlargement; check each
   proof line against the list).
9. **§5** — re-run the harness (`python3 O4T_transfer_check.py`, ~80 s; `--quick`
   ~1 s); confirm the preregistration matches the docstring and the sealed JSON.
10. **The rescope note** — confirm the charged inequality direction is indeed
    unprovable as written (FLOOR) and that N3-BRACKET is the faithful replacement.
