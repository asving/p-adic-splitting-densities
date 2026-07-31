# M06-vp-sound — Attempt (Fable prover, 2026-07-31)

**Obligation**: discharge `BK.vp_sound : VPSound X`
(`lean/LeanUrat/MovesU/BridgeKernels.lean:235`) at the pinned instance
`X := bridgeClassifierSpec n p (bridgeCanonical n p boxEquivD) … bridgeZfType`
(BridgeMk intended wiring). See `M06-vp-sound_brief.md` for the full unfolding.

**Outcome in one paragraph.** The row as it would be discharged at the
AS-BUILT instance is **refuted**: the as-built classifier admits (τ-ns)
["no-side" / empty-Newton-window] leaves in its verdict trees
(`VTree.fiberAt` clause (ii), `lean/LeanUrat/MovesT/Defs.lean:521–524`), and
an ns verdict issued at finite level N is unsound — I exhibit an explicit
witness class ((x+p)² mod p^N, §2) whose lifts realize three different
splitting types (PARI-confirmed), while a legal carried ns-tree fibers at it.
This is an unfaithful transcription of the project's own note, whose partition
display routes ns-leaf fibers to the UNDECIDED side at every finite level
("(NS-d): ns-leaf fibers lie in Undec(N) at EVERY N", MOVES_2026-07-24.md
§SQ.1), and whose interface docstring (`MovesU/Defs.lean:54`) already says
verdict trees have "all leaves (τ-irr)/(τ-hen)". After the one-clause repair
(§3: restrict the classifier's existential to ns-free trees), the row REDUCES
(§4) to two literature statements — (HEN-LIFT), coprime Hensel + unramified
read-off, and (OM-SAT), the Ore–Montes irreducibility certificate =
Guàrdia–Montes–Nart Cor. 3.8/Def. 3.9, already pinned in
`docs/GMN_citations.md` — plus two genuinely project-internal open lemmas
(certified-level determinacy; tree-to-factorization assembly). The two
citation legs are literature-axiom-eligible with the faithfulness caveats of
§5; the row as a whole is NOT one literature axiom.

Caveat on refutation strength: `bridgeTm`'s realized-state/realized-child
semantics ride the R7 designer data (`MovesD.canPolicy`, sorried at HEAD), so
no countermodel can be *compiled* today. §2.4 shows the witness fires under
both natural completions of the semantics (visible-digit reads;
run-on-canonical-decode). Classification: refutation of the intended-instance
discharge, same genre as the compiled `BK.cl6` refutation (SynK2, row kept +
repair queued).

---

## 1. Decomposition of the instance statement

Write f for a level-N class (N ≥ 1), g for a monic degree-n lift in ℤ_p[x],
and type(g) for the multiset {(e(h), f(h)) : h monic ℚ_p-irreducible factor
of g, with multiplicity}. By `bridgeCanonical_pin` (proved) and
`zpReads_unique_of_lift` + `lift_exists` (proved / elementary), the row at
the instance is equivalent to:

> **(VPS)** For all N ≥ 1, f, σ: if some carried σ-tree T (σ-typed,
> self-realized `MovesT.VTree`) with thr(T) ≤ N satisfies
> `fiberAt (Tm N) (chart N) f`, then ∀ g ≡ f (mod p^N): type(g) = σ.

Natural decomposition (each piece named for §§4–6):

* **(LOC)** — certified-level determinacy: under (VPS)'s hypothesis with T
  ns-free, every lift g realizes the same complete halted tree: the OM run on
  g (infinite precision) produces exactly T's chains, halts at T's leaves by
  the same rules, with the same verdict data. [Open project lemma, §4.3.]
* **(LEAF)** — per-leaf soundness on the true object: at a (τ-hen) leaf the
  corresponding factor of g is irreducible unramified with (E,F) = (1, deg ψ)
  [(HEN-LIFT), §4.1]; at a (τ-irr) leaf (saturated branch) the certified
  cluster factor of g is irreducible with (e, f) = (accE, accF) [(OM-SAT),
  §4.2].
* **(ASSEMBLY)** — the leaves of the complete tree account for ALL of g:
  g = (∏ Hensel factors)·(∏ leaf cluster factors), so
  type(g) = typemult(T) = σ, the degree checksum Σ e·f = n riding fiberAt
  clause (v) and defectlessness of ℚ_p. [Open project lemma with a GMN
  backbone, §4.4.]

(VPS) restricted to ns-free trees = (LOC) + (LEAF) + (ASSEMBLY). The ns leaf
clause admitted by the as-built fiberAt breaks (LOC) — there is no finite
certification level for "the window is empty at ALL heights" — and with it
(VPS) itself:

---

## 2. Refutation of (VPS) at the as-built instance

### 2.1 The witness

Fix p odd (run below: p = 5), n = 2, and any N ≥ max(thr(T*), 3) (run below:
N = 6). Let

  f* := the class of (x + p)² = x² + 2p·x + p² in Box p 2 N.

Both coefficients 2p and p² are their own canonical representatives mod p^N
(nonnegative integers < p^N whose p-adic digits vanish at and above level N).

### 2.2 The carried ns-tree T*

Let ν₀ be the root-track window read of (x+p)²: reduction x̄² (one repeated
factor ψ₀ = x̄, multiplicity 2 ⇒ one track, window opened; no simple factors,
so Hensel payload ∅); Newton polygon of x² + 2px + p² w.r.t. x has vertices
(0,2), (1,1), (2,0): one side, slope −1, e = 1, h = 1, side length 2; residual
polynomial (y + 1)²: one repeated root of multiplicity μ = 2, residual degree
g = 1. The canonical recentering key at the Teichmüller policy is
φ₁ = x − ω(−1)·p = x + p (ω(−1) = −1 for p odd). Define T* :=
{chains = {[ν₀]}, henV = ∅, nsLeaf = {[ν₀]}, leafV [ν₀] = nsVerdictOf [ν₀] =
μ·{(accE, accF)} = 2·{(1,1)}}. Then typemult(T*) = {(1,1),(1,1)} =: σ₀, a
legal `SplittingType 2` (Σ e·f = 2). thr(T*) (`VTree.thr`) is a fixed finite
number computed from [ν₀]'s shape data alone — independent of N.

T* is a legal inhabitant of `bridgeTree 2 p σ₀`: the `VTree` structure fields
(finite, prefix-closed, nonempty node lists, hen payload law, leaf law) are
immediate, and `RealizedSelf` holds with witness the truncation of (x+p)² at
T*'s own working level (same fiber walk as §2.3 at that level).

### 2.3 T* fibers at f* (fiberAt clause walk)

At x = f*, level N, under the intended semantics (§2.4 for the caveat):

* (i) chains: [ν₀] is realized (its side/residual data are visible at level
  ≤ 2); it is τ-pruned (no proper nonempty prefix); no other nonempty history
  is realized — the reduction has a single repeated factor (one track, one
  side, one residual root), and after recentering at φ₁ the second window of
  f* is identically zero mod p^N ((x+p)² + p^N·(anything) ≡ φ₁² exactly at
  level N), so no depth-2 node's read datum is realized. Hence
  chains(x) = {[ν₀]} = T*.chains.
* (ii) [ν₀] is maximal. ¬IrrHalts([ν₀]): accE·accF = 1·1 = 1 ≠ 2 =
  childWidth·μ (no saturation — correct, the cluster has degree 2). NsHalts
  (Tm N) (some [ν₀]) f*: the state is realized and NO child read is realized
  at f* (all continuation slots vanish mod p^N). nsLeaf ✓, verdict =
  nsVerdictOf ✓. The second disjunct of clause (ii) holds.
* (iii) henV = henPayload = ∅ ✓ (x̄² has no multiplicity-1 factors).
* (iv) no non-maximal chain halts ✓ (vacuous beyond the empty prefix guard).
* (v) Σ over typemult of e·f = 2 = n ✓.
* (vi) heads = {[ν₀]}; trackDeg [ν₀] = deg of its leaf verdict = 2; the
  repeated-factor side: normalizedFactors(x̄²) = {x̄, x̄}, the multiplicity-≥2
  filter yields {x̄} with count·deg = 2·1 = 2. Multisets {2} = {2} ✓.

By `bridgeCanonical_pin` (+ the proved fibering-type uniqueness †7u), for
every N ≥ max(thr(T*), 3):

  **canonical N f* = some σ₀,  σ₀ = {(1,1),(1,1)}.**

### 2.4 The two candidate completions of the designer semantics

`bridgeTm`'s mem/child data ride the sorried `canPolicy` (R7), so §2.3 needs
one honesty clause. The two natural completions:

* **Visible-digit semantics** (the note's (z-2)/(z-3) capped-lump reading): a
  child read is realized at x iff its side/digit data are visible in x's
  level-N digits. Then §2.3 holds verbatim: f*'s recentered window is
  visibly empty, NsHalts fires.
* **Run-on-canonical-decode semantics** (`MovesD.canTreeModelN`'s
  run-extension reading over the coefficient decode `canDec`): mem/child are
  read off the OM run on the canonical lift canDec(x) ∈ ℤ_p[x]. By §2.1 the
  canonical lift of f* is (x+p)² EXACTLY, whose run genuinely ns-halts at
  [ν₀] (J((x+p)²) = ∅ at φ₁, all heights). Same conclusion.

Any completion on which NO ns-leaf tree ever fibers at any finite-level class
would dodge the witness — but then fiberAt's ns clause is dead code at every
instance point, i.e. the repair of §3 in disguise; it should then be made
explicit rather than left to unpinned designer data. (Note also `NsHalts` is
definitionally `mem ∧ ∀ ν, ¬ child` — for it to be everywhere-false at
realized states, `child` would have to be generous exactly where `mem` is,
which contradicts the chains-clause (i) finiteness for fibering trees:
a generous child relation pumps unboundedly many realized pruned histories
into chains(x), contradicting `hfin` for ANY fibering tree. So under every
completion, either ns trees fiber somewhere — the witness genre — or
`Decided` collapses far below the intended locus. This is why I classify the
finding as architectural, not designer-data-sensitive.)

### 2.5 trueType at the witness is `none` (machine-checked)

Monic degree-2 lifts of f* = (x+p)² mod p^N realize at least three splitting
types. PARI/GP run (p = 5, N = 6; factorpadic + per-factor (e,f) via
p-maximal `nfinit([h,[p]])` + `idealprimedec`; script in §NUMERIC-TESTS):

```
lift 1: g = (x+5)^2 - 5^13 : type [[2,1]]          (odd slope: ramified)
lift 2: g = (x+5)^2 - 5^12 : type [[1,1],[1,1]]    (split)
lift 3: g = (x+5)^2 - 2*5^12 : type [[1,2]]        (2 a nonresidue: unramified)
lift 4: g = (x+5)^2 + 5^6*x : type [[2,1]]
lift 5: g = (x+5)^2 + 5^7*x + 3*5^6 : type [[1,2]]
base  : g = (x+5)^2 itself  : type [[1,1],[1,1]]
```

All five lift-checks (g ≡ (x+5)² mod 5^6) pass. Hence `ZpReads … f* σ` fails
for every σ (any two lifts of different types kill every candidate), the
dite in `bridgeTrueType` takes its negative branch, and

  **trueType N f* = none ≠ some σ₀.**

With §2.3: **VPSound fails at (N, f*, σ₀)** at the as-built instance. ∎

### 2.6 Scope of the refutation

* It refutes the DISCHARGE of the as-built row, not the note's VP-SOUND: the
  note quantifies (τ-ns) soundness over "every f in the leaf's CELL", and the
  (τ-ns) cell is the exact-key-power pro-cylinder ∩_M L_M — on which the
  verdict is CORRECT ((x+p)² itself has type σ₀; PARI line "base"). The Lean
  transcription silently enlarged the cell to its level-N saturation L_{M(N)}
  (the fiberAt/NsHalts face), which strictly contains the pro-cylinder; the
  witness lives in the difference. The note's own TB-CAP(ns) refutation
  (§T.2) is precisely the statement that this enlargement is never exact at
  any finite level; its (NS-ROUTE)/(NS-d) display is the mandated routing that
  the bridge transcription dropped (the BP1 blueprint never mentions the ns
  route — checked 2026-07-31).
* It does NOT touch: `identification` (U11 — correct as proved, parametric),
  `bridgeCanonical_pin`, the trueType machinery (D9a/D10), or the other
  kernel rows. It DOES additionally threaten `seam.count_tie` (TREE-N) at
  ns-leaf trees — the note holds TREE-N verbatim only for ns-free trees
  (§T.2, consequence (ii)) — reinforcing the same repair.
* The mechanism is not n = 2-specific and not root-level-specific: the n = 4,
  p = 3 class of (x²+3)² mod 3^8 (deep ns leaf at the degree-2 key x²+3,
  verdict 2·{(2,1)}) shows the same three-way lift split — PARI run:
  base type [[2,1],[2,1]]; lifts realize [[2,2]], [[2,1],[2,1]], [[4,1]]
  (§NUMERIC-TESTS T0′).

---

## 3. The repair (adjudication item, not a prover move)

Implement the note's (NS-d) routing at the classifier: the verdict existential
must range over **ns-free** trees only. Minimal faithful options (either):

* **(R-a)** In `bridgeCanonical` (BridgeD7), replace the existential's tree
  range by `{T : bridgeTree n p σ // ∀ H, ¬ (bridgeVt n p σ T).nsLeaf H}`
  (equivalently add the conjunct `∀ H ∈ T.1.chains, ¬ T.1.nsLeaf H`). The
  `FiberSeries` carrier and the mass ledger are untouched (ns trees keep
  contributing their measure-zero fibers there, per the note's (ns-null)).
* **(R-b)** Equivalently, consume a variant of `fiberAt` whose leaf clause
  (ii) has only the (τ-irr) disjunct, keeping `henV` — i.e. decide only
  "all leaves (τ-irr)/(τ-hen)" trees, exactly the interface docstring
  (`MovesU/Defs.lean:54`) and the note's §SQ.1 clause (a).

Post-repair sanity (why nothing else breaks): the witness classes of §2
become UNDECIDED at every N, i.e. they ride the envelope `env(N)`; their
level-N mass is the ns-lump mass, which → 0 by the note's (ns-null) (the
Lean-side countable-union glue already exists: `ka4c_nsFiberUnion_null`,
`lean/LeanUrat/Kernels/KA4c.lean`), so `env_tendsto` (row M05) absorbs them —
this is exactly the note's accounting. `canonical_stable` survives (dropping
trees from the existential only shrinks the decided locus, and the transfer
row is per-tree). U11's sandwich is parametric — unaffected.

---

## 4. Post-repair reduction: (VPS, ns-free) = (LOC) + (LEAF) + (ASSEMBLY)

### 4.1 (HEN-LIFT) — literature; statement and citations

> **(HEN-LIFT).** Let f ∈ ℤ_p[x] be monic, f̄ = ψ·h̄ in F_p[x] with ψ monic
> irreducible and gcd(ψ, h̄) = 1. Then f = g·h with g, h ∈ ℤ_p[x] monic,
> ḡ = ψ, h̄ = h̄, and the pair (g, h) is unique. Moreover g is irreducible
> over ℚ_p, ℚ_p[x]/(g) is the unramified extension of degree deg ψ, and g's
> factor-pair is (e, f) = (1, deg ψ).

Status: **(a) known.** Part 1 is Hensel's lemma in coprime-factorization form
over a complete local ring / complete valued field: Neukirch, *Algebraic
Number Theory* (Springer 1999), Ch. II §4, Prop. 4.6; also Bourbaki, *Comm.
Algebra* Ch. III §4 (Hensel), Eisenbud *Comm. Algebra* Thm. 7.18 [exact
numbers to be confirmed at declaration time per the cite policy — the
mathematical statement above is the pinned content]. Part 2 is the standard
equivalence "monic with irreducible (hence separable, F_p finite) reduction ⇒
generates the unramified extension of that degree, e = 1, f = deg" — Serre,
*Local Fields* (GTM 67), Ch. I §6/Ch. III (unramified extensions); Neukirch
Ch. II §7 [numbers to confirm]. Valid at ALL p including wild — the
hypothesis is coprimality, not tameness. Note: before declaring this as an
axiom, probe Mathlib — `HenselianLocalRing` (ℤ_p instance exists) plus the
unramified-extension API may make (HEN-LIFT) fully Lean-provable; it is the
one leg of this row plausibly within reach of a direct formalization.

### 4.2 (OM-SAT) — literature; statement, citations, dictionary debt

> **(OM-SAT).** Let η be a realized branch of the canonical OM tree of a
> monic f ∈ ℤ_p[x], with reads ν₀, …, ν_k, accumulated invariants
> E = ∏ e_r and F = f₀·∏ g_r (f₀ the track's residual degree at level 0,
> g_r the read residual degrees), and cluster degree d at the last read. If
> E·F = d (equivalently: residual multiplicity μ = 1 at the last read), then
> the branch's certified cluster factor f_η ∈ ℤ_p[x] is irreducible over ℚ_p
> with e(f_η) = E and f(f_η) = F.

Status: **(a) known** = Guàrdia–Montes–Nart, *Newton polygons of higher order
in algebraic number theory*, Trans. AMS 364 (2012), no. 1, 361–416
(arXiv:0807.2620v2): **Corollary 3.8** (order-r leaf dichotomy: a
multiplicity-1 residual factor certifies an irreducible factor with
e = e₁⋯e_r, f = f₀f₁⋯f_r) together with **Definition 3.9** (f-complete type,
ω = 1); order-1 instance **Corollary 1.20**; length-1-side instance
**Corollary 3.3**. Labels verified against the arXiv v2 text in
`docs/GMN_citations.md` (standing caveat there: TAMS printed numbering to be
confirmed). GMN work over K finite over ℚ_p — here K = ℚ_p exactly, so none
of the scope over-claims flagged in `docs/AXIOM_FAITHFULNESS.md` (AX-GMN
audit) are needed.

**Dictionary debt (what the citation does NOT give).** Cor. 3.8 speaks of GMN
types (φ₁; λ₁, φ₂; …; ψ_r) with representatives; the project's chains carry
node data (e, h, g, μ, s0, wSide, recentering digits, …). The identification
"project chain ↔ GMN type of order r; saturation accE·accF = d ⇔ ω_t(f) = 1;
(accE, accF) = (e₁⋯e_r, f₀⋯f_r)" is a project-side lemma (deg f_t = m_r·ω_r,
m_r = f₀·∏_{i<r} e_i f_i — GMN Def. 2.3/Thm. 2.11 vocabulary). This is the
same open "ALIGN/GMN dictionary" already carried by census §4.3 item 16
(`KT.cl15_align`); it should be ONE shared lemma, not two.

### 4.3 (LOC) — open project lemma OL-1 (certified-level determinacy)

> **OL-1.** Let T be an ns-free carried σ-tree with thr(T) ≤ N and suppose
> `fiberAt (Tm N) f` holds. Then every monic degree-n g ∈ ℤ_p[x] with
> g ≡ f (mod p^N) realizes T exactly: the τ-pruned canonical OM run on g has
> chain set T.chains, halts at T's leaves by the same rules ((τ-hen)/(τ-irr))
> with the same verdicts.

Status: open at the Lean level; the note proves the two ingredient cap
statements — TB-CAP(hen) (cap N = 1) unconditionally and TB-CAP(irr) (the
verdict class of a saturated branch is an exact finite union of level-N(η)
cylinders, N(η) shape-computable) conditional on the accepted Newton-polygon
perimeter (MOVES §T.2). The Lean-proved carry-algebra spine (`CL12_ncl`
no-cancellation, `CL13_lvlDet` level detection, `lean/LeanUrat/HC1/`) supplies
the digit-level determinacy mechanics; the remaining distance is the
transport to the instance model (`bridgeTm`), which is the same seam as the
ReadLocality kernel (census row M03) — OL-1 should be stated over the pinned
model laws so the two rows share their transport. Numeric surrogate
(Krasner): type constancy across lifts at N = 2·v_p(disc f) + 1, tested 40/40
(§NUMERIC-TESTS TB). NOTE: OL-1 is FALSE if T may have an ns leaf (§2) — the
ns exclusion is not cosmetic.

### 4.4 (ASSEMBLY) — open project lemma OL-2 (tree accounts for all of g)

> **OL-2.** In OL-1's conclusion, the map {leaves of T} → {monic irreducible
> factors of g over ℚ_p} sending a (τ-hen) leaf to its Hensel factor and a
> (τ-irr) leaf to its certified cluster factor is a bijection onto the
> factors-with-multiplicity, and g is the product; consequently
> type(g) = typemult(T) = σ.

Status: open at the Lean level. Backbone: **(a) known** — GMN Def. 3.10 /
eq. (37) (Hensel + theorems of the polygon and of the residual polynomial in
orders 1…r give f = ∏ f_t over the type tree) + Cor. 4.19 (termination:
every type f-complete at some finite order), plus e·f = deg per irreducible
factor (ℚ_p complete discretely valued with perfect residue field is
defectless; standard, e.g. Serre *Local Fields* Ch. II [number to confirm]).
Project side: the accumulation/lift-independence content is accepted at note
level (§B2/D.11 ledger); the fiberAt clauses (v)/(vi) provide exactly the
degree checksums OL-2 needs to rule out orphan factors. The completeness
clause (fiberAt (i): chains = ALL realized pruned histories) is what makes
the leaf set exhaustive — this is where the proof must use it.

---

## 5. Faithfulness analysis (the LITERATURE-eligibility question)

**Does the Lean row state MORE than the citations? Yes, on four axes.**

1. **The ns clause**: as built, the row quantifies over verdict trees with
   (τ-ns) leaves, where it is FALSE (§2) — no citation covers it; it must be
   repaired away, not cited.
2. **Finite-level quantification (LOC)**: (HEN-LIFT)/(OM-SAT)/GMN are
   infinite-precision statements about a given f ∈ ℤ_p[x]; the row
   quantifies over ALL monic lifts of a level-N class. The gap is OL-1,
   project math (note-proved modulo perimeter), not literature.
3. **Assembly bookkeeping**: eq. (37) is per-polynomial; the row's σ is the
   tree's typemult — the gap is OL-2's bijection + checksum argument.
4. **Vocabulary**: the row is typed at the constructed carrier (fiberAt's six
   clauses, VTree node data); the citations know nothing of it — the gap is
   the shared ALIGN/GMN dictionary (OL-3 := the dictionary lemma of §4.2,
   shared with M15/cl15_align).

**Conclusion**: `BK.vp_sound` is NOT one literature axiom. The
literature-axiom-eligible units are the two standalone statements (HEN-LIFT)
and (OM-SAT) as displayed in §4.1/§4.2 (each with its own
AXIOM_FAITHFULNESS entry; (HEN-LIFT) should first get a Mathlib-provability
probe). The residue is: the (NS-d) repair (adjudication), OL-1, OL-2, OL-3.

---

## VERDICT

**REFUTED** (the as-built instance discharge): the (τ-ns) leaf clause admitted
by `VTree.fiberAt`/`bridgeCanonical` makes `VPSound` false at the pinned
instance — witness class (x+p)² mod p^N (n = 2; also (x²+p)² at n = 4),
lifts realize three distinct splitting types (PARI-confirmed), while a legal
carried ns-tree fibers; stated at the note's intended semantics, robust
across both natural completions of the R7 designer data (§2.4). The note
itself mandates the excluded routing ((NS-d)); the transcription dropped it.
**After the one-clause repair (§3): REDUCED** to (HEN-LIFT) + (OM-SAT)
[literature, §4.1–4.2, faithfulness caveats §5] + OL-1 (certified-level
determinacy) + OL-2 (assembly) + OL-3 (ALIGN/GMN dictionary, shared with
cl15_align) [open project lemmas].

---

## NUMERIC-TESTS

Tooling note (pitfall found today): per-factor (e, f) after `factorpadic`
must use the p-maximal order `nfinit([h, [p]])` before `idealprimedec(K, p)`
— plain `nfinit(h)` factors the full discriminant of lifted factors
(60-digit coefficients) and hangs. Helper used in all runs:

```
efof(h, p) = if(poldegree(h) == 1, [1,1],
  my(K = nfinit([h, [p]]), pr = idealprimedec(K,p)[1]); [pr.e, pr.f]);
localtype(g, p) = my(fp = factorpadic(g, p, 60), out = List(), h, m);
  for(i = 1, matsize(fp)[1], h = liftall(fp[i,1]); m = fp[i,2];
    my(ef = efof(h,p)); for(j=1,m, listput(out,ef))); vecsort(Vec(out));
```

* **T0 (the countermodel; RAN 2026-07-31, PASSES = refutes the row).**
  p = 5, N = 6, base (x+5)²: the five monic lifts of §2.5 all satisfy
  g ≡ base mod 5^6 and realize types [[2,1]], [[1,1],[1,1]], [[1,2]],
  [[2,1]], [[1,2]] — ≥ 2 distinct types ⇒ trueType = none. EXTEND: sweep
  p ∈ {3,5,7,11,13}, N ∈ {4,…,10}, base (x+cp)² for c ∈ {1,…,p−1}, 50 random
  monic lifts each: confirm ≥ 2 types ALWAYS occur (expected: the three types
  appear with the classical proportions among y² − u·p^{2N'}-shapes). If some
  (p, N, c) shows ALL sampled lifts of one class sharing one type, that class
  would be a candidate ns-decidable point — report it (it would weaken §2 and
  demand re-examination).
* **T0′ (deep-key variant; RAN 2026-07-31).** p = 3, N = 8, base (x²+3)²:
  lifts realize [[2,2]], [[2,1],[2,1]], [[4,1]] — same refutation one level
  down and at n = 4. EXTEND: bases φ^μ for Eisenstein φ of degree 2, 3,
  μ = 2, 3, p ∈ {2,3,5}, checking n = deg φ·μ ≤ 8.
* **TA (HEN-LIFT sampling; RAN 2026-07-31: 11 instances, 0 failures).** For
  fixed small (p, f) with f̄ having a simple irreducible factor ψ: assert
  factorpadic(f) has exactly one factor h with h̄ = ψ and efof(h) =
  (1, deg ψ). EXTEND: random monic f, p ∈ {2,3,5,7}, n ≤ 6, ≥ 500
  simple-factor instances. Any failure refutes (HEN-LIFT) (not expected —
  it is textbook).
* **TB (Krasner cap, OL-1 surrogate; RAN 2026-07-31: 40 lift-checks, 0
  failures).** For separable f with D = v_p(disc f): assert all monic lifts
  at level N = 2D+1 share type(f). EXTEND: p ∈ {2,3,5,7}, n ≤ 5, ≥ 200 base
  polynomials × 20 lifts; then probe SMALLER N to locate the sharp
  determinacy level and compare with the tree threshold thr(T) once the
  designer data lands (a class decided at thr but with lift-variation at
  thr would refute OL-1 as stated — the diagnostic to run post-R7).
* **TC (OM-SAT order-1/Ore sampling; RAN 2026-07-31: 5 instances, 0
  failures).** One-sided x-polygon of slope h/e, gcd(h,e) = 1, side length e
  (residual degree 1): assert type = [[e·(denominator bookkeeping), …]] —
  concretely x^e + c·p^h ⇒ [[e, 1]] when gcd(e, h) = 1. EXTEND to genuine
  order-2 certificates: f = φ² + c·p^{2v+1}·(unit) for φ Eisenstein deg 2
  (one-sided second-order polygon, residual degree 1): assert irreducible
  with (e, f) read from the accumulated invariants — this is the exact
  (OM-SAT) shape beyond Ore. Any failure refutes the GMN reading (not
  expected).
* **TD (post-repair regression, once (R-a/b) lands and R7 designer data is
  filled).** Enumerate the full level-N box at (n, p, N) = (2, 3, ≤ 5) and
  (2, 5, ≤ 4); run the Lean classifier (via `#eval` on a decidable fragment
  or an extracted reference implementation); assert (i) no decided class
  contains two lifts of distinct PARI types [= VPSound instance check], and
  (ii) every ns-lump class is undecided [(NS-d) check]. This is the
  machine-checkable acceptance test for the repaired row.

