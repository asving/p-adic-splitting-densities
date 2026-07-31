# M18-realization-complete — Problem brief: the realization-completeness row

**Target obligation:** the named open Prop `RealizationComplete` at
`lean/LeanUrat/MovesV/V2_valB.lean:272` — a field (`hRC`) of the hypothesis
ledger `CtsmLedger` (`lean/LeanUrat/MovesV/V7_ledger.lean:36`), currently
undischarged (Phase-B). Date: 2026-07-31.

This brief is self-contained. It re-expands every project-internal name; the
reader is assumed to know p-adic fields, Newton polygons, Okutsu–Montes
theory, and Igusa zeta functions, but nothing about this repository.

The questions to be settled (in decreasing order of value):

1. Is `RealizationComplete` TRUE at the intended concrete instance of the
   abstract structures (the p-adic factorization process described in §5)?
   Since that instance is not yet constructed in the repository (§6), an
   answer must make explicit which properties of the instance-to-be-built
   it uses, stated precisely enough to become named construction duties.
2. Exhibit an added hypothesis H on the abstract structures such that
   H ⟹ `RealizationComplete`, with a rigorous (ideally Lean-checkable)
   proof. H must have genuine content-separation value: it should be
   dischargeable at the intended instance by an argument visibly simpler or
   more local than the full statement.
3. Assess whether H is provable at the intended instance, or what exact
   construction choices make it so.

A machine-checked countermodel (§4.4) already shows the statement does NOT
follow from the axioms/laws of the abstract structures alone, so question 2
cannot be answered by "no hypothesis needed".

---

## 1. The Lean obligation (normative form)

```lean
def RealizationComplete {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) : Prop :=
  ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → Function.Surjective (TE.tmark γ x h)
```

(`lean/LeanUrat/MovesV/V2_valB.lean:272–274`.) All names are unfolded below.
Note the quantifier: ALL height points `h`, with no restriction to the
"realizable height domain" of §3.4.

---

## 2. Standard-mathematics translation of the ambient structures

Fix an integer n ≥ 1 (degree bound; it only enters through the label set of
§2.1). Two abstract structures carry the statement: a *step system* S (the
combinatorial/table side) and a *marked-event carrier* TE over it (the
process side).

### 2.1 The step system S (`StepSys n`, `lean/LeanUrat/MovesV/Defs.lean:81`)

- A finite nonempty set of **cells** (abstract states) — write A, elements
  α, β. Terminal exits carry **absorbing labels** v = (e, f), pairs of
  positive integers with e·f ≤ n (`VLabel n`).
- For each ordered pair (α, β) a finite set **Move(α, β)** of continuing
  move labels; for each (α, v) a finite set **MoveT(α, v)** of terminal
  move labels. Each move m carries a **dimension** d(m) ∈ ℕ; a *height
  point* of m is a tuple h ∈ ℕ^{d(m)} (`Hpt (dim m)`, where `Hpt D` is just
  `Fin D → ℕ`).
- A set **Pools ⊆ ℚ** of evaluation points: nonempty, every member a prime
  power p^k and > 1.
- For each q₀ ∈ ℚ and cell α, a type **Hist(q₀, α)** of *histories*
  (admissible ways of reaching a concrete state of α), nonempty at pools,
  with a predicate **zc** ⊆ Hist(q₀, α) ("realizable, normalized prefix" —
  intended semantics in §5), nonempty at pools.
- For each continuing m : α → β, history x ∈ Hist(q₀, α), and height point
  h ∈ ℕ^{d(m)}: a FINITE set **Assign(m, x, h)** of *fresh assignments*,
  and an extension map **ext(m, x, h, ·) : Assign(m, x, h) → Hist(q₀, β)**
  which preserves zc (`ext_zc`). For terminal m: a finite set
  **AssignT(m, x, h)**, no extension map.
- The one-step **count** is a definition, not data:
  cnt(m, x, h) := #Assign(m, x, h) (`StepSys.cntraw`), likewise cntT.
- Mass functions Assign → ℝ and a productivity law (`out_ne`) exist but do
  not enter this problem's statement.

### 2.2 Templates and the chain carrier

A **template** γ from cell α (`Template n S α`,
`lean/LeanUrat/MovesV/Defs.lean:977`) is a nonempty finite path, built from:
`last m` (one continuing step m : α → β), `lastT m` (one terminal step), and
`cons m γ'` (a continuing step m : α → β followed by a template γ' from β).
Its **dimension** D(γ) is the sum of its steps' dimensions; a height point
of γ is h ∈ ℕ^{D(γ)}, split at a `cons` into the head part h₁ ∈ ℕ^{d(m)}
(`Hpt.take h`) and the tail part (`Hpt.drop h`).

The **assignment-chain count** (`chainCount`, Defs.lean:989):

- T̂_{last m}(x, h) = #Assign(m, x, h);  T̂_{lastT m}(x, h) = #AssignT(m, x, h);
- T̂_{cons m γ'}(x, h) = Σ_{a ∈ Assign(m, x, h₁)} T̂_{γ'}(ext(x, a), h').

The **chain carrier** (`Chains`, Defs.lean:1000) is the type this counts:

- Chains(last m, x, h) = Assign(m, x, h); likewise lastT;
- Chains(cons m γ', x, h) = Σ_{a ∈ Assign(m, x, h₁)} Chains(γ', ext(x, a), h').

So a *chain* is a formally consistent sequence of fresh assignments, each
extending the history produced by its predecessors. It is proved
(`chains_card`, V1_chains.lean:21) that #Chains(γ, x, h) = T̂_γ(x, h), with
the evident Fintype structure (`chainsFintype`).

### 2.3 The marked-event carrier TE (`TmplEvents n S`, Defs.lean:1010)

Data:

- for each q₀ and level N ∈ ℕ, a finite type **Box(q₀, N)** (level-N
  residue data; intended semantics §5);
- for each (γ, x, h) and level N, two finite subsets of Box(q₀, N):
  **tevt(γ, x, h, N)** (the *event census* at level N) and
  **tinst(γ, x, h, N)** (the *instance/mark census* at level N);
- a **defining level** ℓ(γ) ∈ ℕ per template (`tmplLvl`);
- a **mark reading** — for each (γ, x, h) a function
  `tmark γ x h : tinst(γ, x, h, ℓ(γ)) → Chains(γ, x, h)`
  (each counted mark *reads off* the assignment chain it realizes).

Define **T_γ(x, h) := #tinst(γ, x, h, ℓ(γ))** (`Tgam`, Defs.lean:1044) — the
"realized count", the object the source note's exact-domain laws are keyed
to — and **TReal(γ, x, h)** := ∃ N₀, ∀ N ≥ N₀, tevt(γ, x, h, N) ≠ ∅
("eventual event nonemptiness").

Laws, all guarded by q₀ ∈ Pools and zc x:

- `tevt_last_iff` (+ terminal twin): at LENGTH-1 templates,
  TReal(last m, x, h) ⟺ 0 < #Assign(m, x, h);
- `real_marks`: TReal(γ, x, h) ⟹ 0 < T_γ(x, h);
- `marks_realize`: 0 < T_γ(x, h) ⟹ TReal(γ, x, h);
- `tmark_inj`: tmark γ x h is injective (distinct marks read to distinct
  chains);
- `tmark_last_surj` (+ terminal twin `tmark_lastT_surj`): at LENGTH-1
  templates, tmark is surjective — every single fresh assignment is
  realized by a mark.

NOTE the deliberate asymmetry: injectivity is a law at ALL templates,
surjectivity is a law ONLY at length 1. At composite templates the census
fields tevt/tinst are FREE data, tied to the step layer only through the
laws above. `RealizationComplete TE` is exactly the missing surjectivity at
all templates.

### 2.4 The domain package (`XHDd n S TE`, Defs.lean:1060)

For context (it appears in the surrounding proved results, not in the
obligation itself): an XHDd-structure assigns to each template γ an
explicitly listed, pairwise-disjoint finite union dom(γ) of *linear sets*
{h₀ + Σ_v n_v·v : n_v ∈ ℕ} ⊆ ℕ^{D(γ)}, with, over pools at zc histories:

- `no_orphan`: 0 < T_γ(x, h) ⟹ h ∈ dom(γ);
- `no_stray`: h ∈ dom(γ) ⟹ 0 < T_γ(x, h) (for EVERY zc x).

Note both are keyed to the realized count T_γ, not to T̂_γ.

---

## 3. What `RealizationComplete` says, unfolded

For every template γ, every pool element q₀, every zc history x at γ's
source cell, and EVERY height point h ∈ ℕ^{D(γ)}: the mark reading

  tmark γ x h : tinst(γ, x, h, ℓ(γ)) → Chains(γ, x, h)

is surjective — every formally consistent assignment chain is read off by
at least one counted mark. Together with the injectivity law this makes
tmark a bijection, hence (by `chains_card`) forces the counting tie

  T_γ(x, h) = T̂_γ(x, h)   for all γ, all h, over pools at zc histories.

In particular it forces: T̂_γ(x, h) > 0 ⟹ T_γ(x, h) > 0 (a nonempty set of
formal chains implies a nonempty mark census), which combined with
`no_orphan` gives T̂_γ(x, h) > 0 ⟹ h ∈ dom(γ).

---

## 4. What is already proved in the corpus

All in `lean/LeanUrat/MovesV/` (module V2_valB unless noted); everything
below is sorry-free and Lean-core (axioms {propext, Classical.choice,
Quot.sound}).

### 4.1 One-way bound and the length-1 tie

- `marks_chains` (V1_lastTie.lean:32): T_γ(x, h) ≤ T̂_γ(x, h) over pools at
  zc histories (from injectivity alone).
- `tgam_eq_cntraw` / terminal twin (V1_lastTie.lean): at length-1 templates
  T = T̂ (both directions of surjectivity available there).
- `tgam_eq_chains` (V1_chains.lean:43): T_γ(x, h) = #{c ∈ Chains :
  ∃ b, tmark b = c} — the realized count IS the count of realized chains.

### 4.2 The conditional bridge and its consumer

- `tgam_eq_chainCount_of_complete` (V2_valB.lean:278):
  `RealizationComplete TE` ⟹ T_γ(x, h) = T̂_γ(x, h) (pools, zc).
- `val_b` (V2_valB.lean:292): given the valuation laws for the one-step
  counts (`ValA`: each one-step count at in-domain base points equals a
  table polynomial evaluated at q₀), the uniformity laws (`XHDu`:
  representative-independence and height-rectangularity of the one-step
  counts), a domain-coherence tie (`MDomTie`), AND `RealizationComplete`:
  for h ∈ dom(γ), (T_γ(x, h) : ℚ) = C_γ(q₀), the product over γ's steps of
  their table polynomials (`pathProdPoly`).
- `val_b_table` (V2_valB.lean:251): the same conclusion for T̂_γ WITHOUT
  `RealizationComplete` — the unconditional table-side half.
- Consumption: the capstone conclusion record `CtsmConclusions.val_b_chain`
  (V7_ctsmDefs.lean:190, statement `ValB_Stmt` keyed to T_γ) is discharged
  in `ctsM` (V7_ctsm.lean:54) through the ledger field
  `hRC : RealizationComplete TE`. Downstream, the bridge-cluster seam
  TV_F2 (`seam_coherence_exists`, tg_val leg) needs the T_γ-keyed value law
  at the pinned instance, so the whole leg is blocked on this row.

### 4.3 Consistency (the statement is satisfiable)

The trivial process witness `witTE` (V1_witnessB.lean:103; all chain
carriers subsingletons, all censuses full) satisfies every TmplEvents law,
and its tmark is plainly surjective at all templates. So the laws + the
target statement are jointly satisfiable.

### 4.4 Non-derivability (the statement has content)

The census-coupled toy (`HmcToy`, V4_hmc.lean): one cell, one continuing
and one terminal move, all history/assignment carriers of size 2, zc ≡
true, pool {2}; the composite census is DECOUPLED from the step layer —
`census(cons …)(x, h) := if h = 0 then 0 else 1` while every one-step
census is full. Every TmplEvents law and both XHDd laws hold
(`HmcToy.TE`, `HmcToy.XD`). Machine-checked consequences:

- `coupling_signature` (V4_hmc.lean:380): there exist S, TE and a composite
  point with 0 < T̂ (= 4) and T = 0. By §3 this refutes any unconditional
  derivation of `RealizationComplete` from the standing laws.
- `hmc_false_witness` (V4_hmc.lean:369): the same toy witnesses ¬HMC (the
  height-domain Markov factorization fails there), so the toy is also the
  corpus' standing ¬HMC bracket.

### 4.5 A recorded structural diagnosis (adjacent, same root cause)

The docstring of `CompProduct` (V5_comphA.lean:85–97) records a failed
derivation attempt for the composite marked-event product law with the
diagnosis: "the corpus' tevt laws are nonemptiness ties only … and the
one-step census has no composite-template analogue, so the decomposition is
genuinely Phase-B … the instance's cevt is BUILT as the entrance-extended
biUnion, where the split is definitional". The same census-freedom at
composites is what blocks `RealizationComplete`.

---

## 5. The intended instance (source-note semantics)

From the source note (`lean/notes/MOVES_2026-07-24.md`, §V.0–V.2, §V.1(vi),
§D4-R.4) and the transcription blueprint
(`lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` §2.B, §2.G):

Fix a prime power q₀ = p^k in the pool. The process studied is the
canonical factorization tree T_can(f) of a monic degree-n polynomial f over
ℤ_p (an Okutsu–Montes/Newton-polygon tower: each node reads a Newton
polygon and a residual factorization, each continuing branch descends into
one residual factor, heights are the ℕ-valued slope/valuation parameters of
the reads). Intended readings:

- **Cells** α: p-independent syntactic states of one branch (skeleton +
  source-partition cell). **Histories** x ∈ Hist(q₀, α): admissible
  realized prefixes of one branch reaching a concrete state of α; zc = the
  note's normalization invariant (ZC) carried along realized prefixes
  ("(ZC)-satisfying realizable prefixes").
- **Assign(m, x, h)**: the fresh-assignment fiber — the set of fresh digit
  cells (new coefficient digits of f revealed at this read) that REALIZE
  the move species m at height h from the prefix x. `ext` = appending the
  chosen digit cell to the prefix. Per the note these are *realized*
  objects: each fresh assignment carries a positive conditional mass
  q₀^{−E(h)} (the note's XHD-w law), and extension preserves realizability
  (`ext_zc`).
- **Box(q₀, N)**: level-N residue data — pairs (f mod p^N, η) with η a
  marked branch prefix of T_can(f); the note's "mark-index family … finite
  per level" (V.1(vi)), with the finite-level census laws D4R.4-SUM/EV.
- **tinst(γ, x, h, ℓ(γ))**: the census, at the stabilization level ℓ(γ)
  (the note's N(P̂): the level at which every realizability equation of the
  shape is resolved, so each realized-prefix fiber is an exact union of
  level-N residue classes), of realized marked prefixes (f, η) following
  template γ at heights h from the prefix x.
- **tmark**: reading a counted mark (f, η) as the chain of fresh digit
  cells its branch actually consumed.

At this intended instance, `RealizationComplete` says: *every formally
consistent chain of realized fresh digit-cell choices along a template is
actually witnessed, at the stabilization level, by at least one p-adic
polynomial f and branch η consuming exactly those digit cells at those
heights.*

## 6. Status of the instance construction

No p-adic instance of `TmplEvents` exists in the repository yet: the only
instances of the structure are the two toys of §4.3–4.4. Building the real
instance is the recorded Phase-B duty (the fenced instantiation sorries
`ledgerIV_inst`, `ratBurdens_exists`, `scs_data_supply`; ratification
record `lean/notes/RATIFY_ROUND5_V_2026-08-01.md`). Consequently "provable
at the bridged instance" means: provable from properties the instance
builder can be charged to deliver, stated as precise named duties on the
carriers of §5 — not from anything already on disk.

## 7. What a solution must deliver

1. A verdict on question 1 of the header (truth at the intended instance),
   with every used instance property stated as an explicit lemma-level
   assumption on the §5 carriers — no appeal to "the construction will
   obviously satisfy this".
2. For question 2: the added hypothesis H stated in the exact vocabulary of
   §2 (so it can be typed against `StepSys`/`TmplEvents` verbatim), a
   rigorous proof of H ⟹ `RealizationComplete`, and a check of H against
   the §4.4 countermodel (the toy must violate H).
3. For question 3: either a proof sketch of H at the §5 semantics
   identifying the exact load-bearing facts (with their note citations), or
   a precise obstruction.
4. Statement fence: `RealizationComplete` itself must not be weakened or
   re-keyed; H is an ADDITIONAL row.
