# HDISCHARGE_H8 — discharge blueprint for (H8) = (K-CUT), the shallow-cut decomposition kernel

**Campaign**: the hypothesis-discharge swarm (Asvin directive 2026-08-05, ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` entry "ASVIN DIRECTIVE (2026-08-05)";
commit 5a624c3). **Lead**: H8 (this file). **Door**: Door 1 (tree combinatorics).
**Status**: BLUEPRINT (no Scaffold `.lean` files land in this unit; prover fan-outs
run separately). Every Lean statement in §4 was **compile-probed green against the
built corpus** on 2026-08-05 (probe files `/tmp/openmath/H8_probe{,2,3,4}.lean`,
`lake env lean` — sorry-warnings only, zero errors) BEFORE being written here
(the BP_IV/BP_VI lesson: ill-typed verbatim statements block whole waves).

---

## 0. Charter: the row, exactly, and where it is consumed

**The authoritative statement** (`docs/ROOT_ASSEMBLY_2026-08-02.md`, §3.1 row
"(H8) = (K-CUT)", NEW at REVISION 10/r11 from finding G-2 of the un-banked O-11
hostile pass `lean/notes/openmath/O11_owedpass_2026-08-03.md`; provenance
disambiguated at REVISION 12, finding VC13-4):

> **(K-CUT).** For every n ≥ 2, every prime p, and every splitting type σ of
> degree n, every complete type-σ canonical tree T admits EXACTLY ONE
> decomposition into a shallow shape Ŝ plus per-branch block derivations
> (D_1, …, D_r) — exhaustive-exclusive read ownership at the first-split cut —
> and the decomposition is weight-preserving,
>
> (†)   μ(fiber T) = W(Ŝ) · ∏_i weight(D_i),
>
> as M04 Lemma 3.3's hypothesis consumes it at Step 18's K1.

**The consumer's exact form** (M04 = `lean/notes/openmath/M04-series-tie_fable.md`
§5.4, Lemma 3.3's hypothesis — the shape (K-CUT) must supply):

> a countable shape family {Ŝ} with numeric weights W(Ŝ)(p) ∈ [0,∞), entrance
> lists ((e_i, τ_i, δ_i))_{i≤k(Ŝ)}, halted verdicts σ₀(Ŝ), and a
> WEIGHT-PRESERVING BIJECTION
>
> (‡)   {complete trees T of type σ} ≅ ⨆_Ŝ {(D_i)_{i≤k(Ŝ)} :
>            σ₀(Ŝ) ⊎ ⊎_i verdict(D_i) = σ},
>
> under which μ(fiber T) = W(Ŝ)·∏_i weight(D_i).

**Consumption sites** (ROOT (ROOT-C) attribution, exact): clause (R) at Step 18's
K1 regrouping (the Lemma-3.3 shallow-cut regroup inside `series_tie`'s reduction);
clause (UB) through the transported K1/K4 chain at q ↦ q^δ. NOT (0)/(SQ).

**Provenance and the named falsifiers** (finding G-2, verbatim targets): the O-11
r3 serving map "CUT-WD ← O-1thr Theorem 1 (= D-14, read locality) + CU-3 (= F3′
coherent nonempty locus)" is a correspondence CLAIM, not a demonstrated
implication — "a coherent nonempty read locus can still have **overlapping
ownership**, an **unowned read**, or **two different shallow decompositions** of
one tree. D-14 and CU-3, as described, exclude none of these." These three named
failure channels are the design targets of §4's partition theorems.

**Named retirement route on record** (the (H8) §3.1 row): O-11 §8 charge (vi) —
the adjudication of the serving map against T-6's §T-ASSEMBLY; if that
adjudication demonstrates the implication from on-file content, the row RETIRES
into the consuming leaves' [V] debts. §2.5 executes this route's spec; §2.5's
honest prediction: the D-14+CU-3 implication FAILS as displayed (G-2's own
analysis), but the MOVES §S.2 (CUT-WD) derivation IS on file — so the realistic
outcome is a RE-SCOPE, not a fiat retirement (§6).

**The honesty invariant, applied**: nothing below discharges (H8) by declaration.
The blueprint (i) PROVES in Lean the pure-combinatorics legs (unique first
entrance, exhaustive-exclusive ownership, the sum/product regrouping — exactly
G-2's three falsifier channels), (ii) reduces the remainder to a THREE-FIELD
residual hypothesis surface ((K-CUT-s)/(K-CUT-g)/(K-CUT-m), §1.3) each already
owned by an existing displayed row or fence, and (iii) specs the documentary
adjudication that decides whether the serving map can be re-pointed. (H8) stays
a §3.1 row until the ROOT ledger itself is revised on the strength of landed
artifacts — that revision is the orchestrator's, not this blueprint's.

---

## 1. The mathematical content, decomposed (member map)

(H8) is displayed as ONE row; it decomposes into four members with different
doors. Notation for the whole file: T = a complete finite realizable canonical
type-σ tree (the corpus carrier `MovesT.VTree`); its READ SITES are its chains
(TREE-EXP's site vocabulary — `Tr.chains`, prefix-closed, finite); E = the
ENTRANCE PREDICATE "this chain's last step is a block-entrance read" (MOVES
§S.2's predicate, CTS-M(i)/(iii) supply); Ŝ(T) = T's shallow layer; D_i = the
subtree hanging at the i-th first entrance.

* **(K-CUT-1) CUT WELL-DEFINEDNESS — "exactly one shallow decomposition".**
  GIVEN E: every chain of T either has no entrance among its proper prefixes
  (SHALLOW read) or has a UNIQUE FIRST entrance ε above it; ε is itself minimal
  (nested entrances are owned by the outermost block); the assignment
  T ↦ (Ŝ(T), (D_ε)_ε) is a choice-free FUNCTION of (T, E) — two different
  shallow decompositions of one tree cannot exist. [= MOVES §S.2 (CUT-1) +
  (CUT-3)'s choice-freeness; kills G-2 falsifier #3.]

* **(K-CUT-2) EXHAUSTIVE-EXCLUSIVE READ OWNERSHIP (with the (BDY) boundary
  rule).** The read sites of T partition EXACTLY as
  shallowReads(T) ⊔ ⨆_{ε ∈ minEnts(T)} blockReads(T, ε): no unowned read
  (exhaustive), no read owned twice (exclusive), and at the boundary the
  minimal entrance ε's OWN entering read is shallow-side while ε as a state
  index heads its block — MOVES §S.2's (BDY)/(CUT-2) display. [Kills G-2
  falsifiers #1 and #2.]

* **(K-CUT-3) THE WEIGHT-PRESERVING PRODUCT LAW (†).** GIVEN TREE-EXP's
  per-site product μ(fiber T) = ∏_{sites s} jvol(c_s | Σ_{<s}) — which is
  ITSELF conditional on (SIB)/(JC-multi), priced at their own ledger rows
  ((H7)'s K-LOC face, the `sibjc` rows), never re-priced here — the ownership
  partition of (K-CUT-2) regroups the product as
  (∏_{shallow}) · ∏_ε (∏_{block ε}), i.e. (†) with W(Ŝ) := the shallow-site
  factor and weight(D_ε) := the block-ε factor. The regrouping step is pure
  index algebra (`Finset.sum_biUnion` over a proved-disjoint family); the
  IDENTIFICATION of the block factor with the block-derivation grammar weight
  at the transported pool q^{δ_ε} is [2r] REL.2's dictionary — a residual leg
  ((K-CUT-m), §1.3).

* **(K-CUT-g) GRAFT COMPLETENESS (the surjectivity direction of (‡)).** Every
  verdict-compatible pair (Ŝ, (D_i)) IS the cut of exactly one complete
  realizable type-σ tree. This is NOT tree combinatorics: it is continuation
  memorylessness — a block derivation D from interface (e, τ, δ) must be
  realized below EVERY realized entrance carrying that interface, or the block
  totals B_{e,τ}(σ')(q^δ) (sums over ALL grammar derivations) overcount the
  right side of Lemma 3.3's conclusion. THIS is the leg the T-6 serving map
  (D-14 read locality + CU-3 coherent nonempty locus + REL.2) was actually
  being cited for; G-2 is exactly the finding that no on-file display derives
  it. It stays hypothesis-grade here ((K-CUT-g) field, §1.3).

**Why (‡) needs BOTH directions (displayed, so no verifier re-derives it):** the
cut direction (K-CUT-1/2/3) alone gives Σ_T μ(fiber T) ≤ Σ_Ŝ W(Ŝ)·Σ_compat ∏ B
(each tree hits one tuple, weights multiply); missing tuples would make the
inequality strict. Lemma 3.3's conclusion is an EQUALITY; (K-CUT-g) closes it.

### 1.1 Granularity adjudication (a G-2-class trap, settled by display)

Two readings of "shape Ŝ" circulate in the sources and are NOT interchangeable:

* **(full-data)** Ŝ = T's shallow LAYER with values and heights retained; W(Ŝ)
  = the measured mass of THAT layer. At this granularity the per-T identity (†)
  and the bijection (‡) are literally true-formable, and the family is
  countable, not finite.
* **(height-forgotten)** Ŝ = the finite-up-to-heights SHALLOW TREE SHAPE of
  RS.1-SH (MOVES §S.2 12026–12046; the Lean `MovesS.Shape T` with k/eOf/τOf/
  δOf/σ0), W_Ŝ ∈ ℚ(q) the RESUMMED shallow mass. At this granularity (‡) is
  FALSE as a bijection (many shallow layers per shape) and (†) is FALSE per-T
  (a fixed resummed W against T's own heights).

**Decision (binding on §4):** (K-CUT) = the **full-data** statement; that is what
the §3.1 row's per-T display "μ(fiber T) = W(Ŝ)·∏ weight(D_i)" can mean, and it
is all M04's Lemma 3.3 consumes (its {Ŝ} is only required countable-with-
weights). The passage full-data → height-forgotten (grouping shallow layers by
their forgotten shape and resumming W) is **CL-17 duty (ii)** = the height-sum
production law, ALREADY typed in the corpus as `MovesS.W17ii`'s clause (ii)
(`HasSum (fun h : shDom Ŝ => shWeightH Ŝ h q₀) (WshVal Ŝ q₀)`) and priced at
(H5)'s PACK row-laws (`wsh_ok`, PACK-iii) + the W17ii row — **NOT (H8) content**.
CUT-3's "values and heights forgotten, entrance and halt boundary data retained"
(MOVES 12091–12094) is the shape-of map Ŝ_full ↦ Ŝ_forgotten; its entrance lists
(e_i, τ_i, δ_i) and σ₀ are retained data, so the compatibility predicate in (‡)
is stable under the forgetting — the seam is displayed, never silently crossed.
[Translation risk closed: a unit that proved (†)/(‡) at the height-forgotten
granularity would prove something FALSE; a unit that consumed the full-data form
where Rsh's finite `ShapeFam` sum is needed would smuggle CL-17(ii). §4's units
name the granularity in every statement.]

### 1.2 What is already on file (the reuse inventory)

* **MOVES §S.2 (CUT-WD) derivation** (`lean/notes/MOVES_2026-07-24.md`
  12065–12094): (CUT-1) first-entrance uniqueness per branch, (CUT-2) node
  trichotomy + (BDY) boundary ownership + the no-reclassification fence
  (deep-recursion splits never re-classified shallow), (CUT-3) choice-freeness
  — DERIVED **given the fenced SUPPLY**: "the ENTRANCE PREDICATE — 'ν is a
  BLOCK-ENTRANCE node' — is CELL data … the predicate's computability per node
  rests on CTS-M(i)'s computed partition (CL-13) and the (iii) entrance-shape
  family — [1v]/[2b] territory, cited not proved." Part of T-8 (§S-RESUM),
  dual-accepted 2026-07-27/28 as a NOTE (its supply fence displayed).
* **T-6 (§T-ASSEMBLY = MOVES §T.4)**: TREE-EXP (the per-site product, proved
  GIVEN (SIB)+(JC-multi)), TREE-N, the first-split recursion. Dual-accepted;
  its own row lists CUT-WD as an OPEN KERNEL served by leaves O-1/O-3/O-10.
* **Lean, landed and green**: `MovesT.VTree` (chains, `hfin`, `hclosed`
  prefix-closure) + `History.IsPrefixOf` (nodewise list prefix,
  `MovesD/Defs.lean:614`) + `MovesT.vtree_pathOrder` (refl/trans/antisymm +
  ancestor totality — `D8_pathOrder.lean`, PROVED) + `MovesT.treeExp`
  (TREE-EXP count form, `E8_treeExp.lean`, PROVED under its displayed rows) +
  `MovesT.TreeIfaceCore` + `treeIfaceCore` (D13, the packed carrier core) +
  `MovesU.FiberSeries`/`seriesSum` (the [3t] series carrier, `MovesU/Defs.lean`)
  + `MovesS.Shape`/`ShapeFam`/`shConv`/`Rsh` (the height-forgotten symbolic
  side) + `MovesS.ReadOwner`/`bdyEdgeOwner`/`bdyNodeOwner` (the (BDY) index
  toys) + `MovesS.W17ii` (the resummation seam, §1.1).
* **The §W4-SYNC seam contract** (`lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md`
  §W4-SYNC, S-5): the R41-completed `W7_cutWD` pin design (TreeIface + CUT-1
  least-first-entrance + the typed no-reclassification fence + (CUT-3)'s
  entrance-boundary-data clause + σ₀ feed). NEVER built ("NOT LEAN UNITS. NOT
  BUILT AT E-PHASE"). §4 EXECUTES this design's mathematical content over the
  real carrier (`VTree` directly, via D8's order laws) instead of the abstract
  `TreeIface` — the S-5/S-11 re-keying charge said the pin is DONE only when
  re-keyed against the real corpora; going to `VTree` directly skips the
  double translation. The W7 clauses that are DATA conformance (shapeOf/σ₀/
  F.Sh-membership) surface in §4's `CutData`/seam fields, not as axioms.

### 1.3 The residual hypothesis surface (what stays open, by owner)

After §4's provable units land, (H8)'s open content is EXACTLY three fields
(the Lean surface `VTreeCutSeam`, unit H8-B2):

| field | content | owner of record (existing display) |
|---|---|---|
| (K-CUT-s) `supply_cell` | the entrance predicate E is CELL data, per-node decidable from the realized read (CTS-M(i) computed partition CL-13 + CTS-M(iii) entrance-shape family) | MOVES §S.2's fenced SUPPLY; [1v]/[2b]; surfaces of the (H1) dictionary group + the O-9/CL-13 census rows |
| (K-CUT-g) `graft_complete` | every verdict-compatible (Ŝ_full, (D_i)) tuple is the cut of exactly one complete realizable tree (continuation memorylessness at entrances, incl. the δ > 1 base-changed legs) | the T-6 serving arc: D-14 (read locality, PROVED) + CU-3 (coherent nonempty locus) + [2r] REL.2 (CL-8, open) — the arc G-2 found UNDEMONSTRATED; adjudication unit H8-R1 |
| (K-CUT-m) `mass_tie` | the cut factors are the MEASURED weights: shallow factor = W(Ŝ_full)(p), block-ε factor = the grammar weight of D_ε at pool p^{δ_ε} | TREE-EXP ((SIB)/(JC-multi) = (H7)/sibjc rows) + REL.2's pool dictionary ([2r], CL-8) + (K4) mass semantics (M02/count_tie — O-1/O-3) |

Discharging THESE fields is other rows' work (each cell names its row); (H8)'s
own contribution — everything G-2 actually named — is proved. That is the
honest shape of this discharge: **(H8) reduces to already-displayed rows plus
Lean-proved combinatorics; no new open content is created.**

---

## 2. Door adjudication, member by member

### 2.1 (K-CUT-1) cut well-definedness — door: **PROVE** (Lean, outright)

Argument (transcribing MOVES §S.2 (CUT-1)/(CUT-3) into the corpus vocabulary;
full section-by-section design in §3): the proper prefixes of a chain H are
linearly ordered by `IsPrefixOf` (list-prefix totality on common extensions —
`vtree_pathOrder` clause 4 / `List.prefix_or_prefix_of_prefix`), so among the
entrance proper prefixes of H there is at most one that is below all others
(antisymmetry) and, if any entrance proper prefix exists, a length-minimal one
IS below all others (minimality + totality) — existence and uniqueness of the
first entrance. Choice-freeness: `minEnts`/`blockReads`/`shallowReads` are
`Finset.filter`s of decidable-from-E predicates — FUNCTIONS of (T, E), so the
decomposition is unique by construction, and "two different shallow
decompositions of one tree" (G-2 falsifier #3) is structurally dead. No open
points: consumes only list combinatorics + `hclosed`. Honest note: this member
is stated GIVEN E as an abstract predicate; which E (the corpus entrance
predicate) is (K-CUT-s)'s business, quantified over in every §4 statement.

### 2.2 (K-CUT-2) exhaustive-exclusive ownership — door: **PROVE** (Lean, outright)

Argument: exhaustive — a chain is shallow or has a first entrance ((K-CUT-1)
existence), and that first entrance is ITSELF minimal (its proper prefixes are
proper prefixes of H by transitivity; an entrance among them would contradict
firstness) and a member of `Tr.chains` (`hclosed` + `History.nonempty`), so
every non-shallow read lands in `blockReads` of a genuine `minEnts` member.
Exclusive — shallow ∩ block = ∅ (a block member has an entrance proper prefix
by definition); block ε₁ ∩ block ε₂ = ∅ for ε₁ ≠ ε₂ ((K-CUT-1) uniqueness).
(BDY) display: a minimal entrance ε satisfies `ShallowRead E ε` by definition
of minimality — its OWN entering read is shallow-side — while every member of
`blockReads ε` has ε strictly above: the node-vs-edge ownership shift is a
THEOREM, not a convention to be trusted. G-2 falsifiers #1 (overlap) and #2
(unowned read) are the two halves. No open points. Nested-entrance semantics
(the no-reclassification fence, Codex#6-5 form): an entrance ε′ strictly
inside block ε has first entrance ε — owned by the OUTERMOST block; deep
splits are never re-classified shallow because ownership is by FIRST entrance,
which exists for them (they sit below their block root). The fence is thus a
COROLLARY of the partition, not an extra clause — displayed as
`firstEntAbove_shallowRead` + the partition.

### 2.3 (K-CUT-3) weight preservation (†) — door: **PROVE the regroup**, inputs priced elsewhere

Two layers, strictly separated:

* **(provable, Lean)** The REGROUPING: given the (K-CUT-2) partition,
  Σ_{H ∈ chains} siteExp H = Σ_shallow + Σ_{ε ∈ minEnts} Σ_{block ε}
  (`Finset.sum_union` + `sum_biUnion` over the proved disjointness), hence with
  `treeExp`'s count identity (its hypothesis rows carried VERBATIM),
  Nat.card(fiber T) · (p^{n+Σ_shallow} · ∏_ε p^{Σ_{block ε}}) = p^m — (†) in
  the corpus's level-exact count vocabulary, every site charged exactly once
  ACROSS THE CUT. On the [3t] series carrier the same regroup is the abstract
  Lemma-3.3 pair `seriesSum_cut`/`seriesSum_cut_conv` (ENNReal Tonelli; the
  second step is M04's "group tuples by their verdict tuple and factor").
* **(hypothesis, priced elsewhere)** the identification of the three factor
  families with the MEASURED semantic weights — (K-CUT-m), §1.3. In
  particular the p^{−siteExp} count factors equal conditional jvols only
  through TREE-EXP's own rows, and the block-ε factor is a grammar weight AT
  THE TRANSPORTED POOL q^{δ_ε} only through REL.2's dictionary; neither is
  re-proved nor re-assumed here beyond the named fields.

### 2.4 (K-CUT-g) graft completeness — door: **CONSTRUCTION-CONFORMANCE + the §2.5 adjudication**; stays hypothesis-grade in Lean

No abstract proof exists to spec: the content is semantic (realizability of
grafts). Lean-side it is the `cut` Equiv's surjectivity inside `CutData` (unit
H8-A3) — supplied at instantiation time by the `VTreeCutSeam.graft_complete`
field (unit H8-B2), NEVER by an axiom. Its serving arc (D-14 + CU-3 + REL.2)
is exactly what O-11 §8 charge (vi) adjudicates (§2.5). Falsifier intuition
for verifiers: if grafting could fail, some compatible (Ŝ, (D_i)) would be
unrealized and Σ_Ŝ W·Σ∏B would strictly exceed Σ_T μ(fiber T) — the numeric
gates (§5) bound this from both sides at n = 2, 3, which is evidence, not proof.

### 2.5 (K-CUT-R) the named retirement route — door: **documentary adjudication** (unit H8-R1)

O-11 §8 charge (vi), verbatim: "check the K1-a per-kernel serving map
((SIB-STEP) ← O-10 Thm 2 + D-b; CUT-WD ← D-14 + CU-3) against T-6's own
§T-ASSEMBLY text — the map is displayed reasoning from the tree's T-6 row +
O-10 §5.3, not T-6's own display." Execution spec (Codex, fresh context,
quote-and-classify): paste (a) the T-6 §T-ASSEMBLY text (MOVES §T.4), (b) the
MOVES §S.2 (CUT-WD) block 12057–12099 incl. the ROUTING law, (c) the D-14 and
CU-3 statements, (d) the (H8) row + (‡), and charge it to adjudicate TWO
separately-billed questions: (vi-a) does D-14 + CU-3 demonstrably imply
(K-CUT-1/2/g) as displayed? [G-2's analysis says NO — expected verdict FAIL];
(vi-b) does the §S.2 (CUT-1)/(CUT-2)/(CUT-3) derivation, GIVEN its fenced
supply, demonstrate (K-CUT-1)+(K-CUT-2) and the (BDY) rule at the level T-6's
consumers need [expected YES for the combinatorial legs — which §4's Lean
units then make machine-checked, superseding the prose], and does ANY on-file
display demonstrate (K-CUT-g) [expected NO — the honest residue]? DISPOSITION
RULE (pre-registered): only outcome (vi-a)=PASS retires the row into [V]
debts per the ROOT's named route; the expected outcome ((vi-a) FAIL,
(vi-b) split) yields the §6 RE-SCOPE display instead. Fiat discharge excluded:
this unit only ever RECORDS an adjudication of already-on-file content.

### 2.6 Literature door — **N/A, recorded**

M04's own literature adjudication (M04-series-tie_fable.md §6) covers this
row's neighborhood and concludes LITERATURE-AXIOM-ELIGIBLE: NO — the content
quantifies over project-internal carriers (canonical-policy trees, the chain's
grammar weights); the abstract core (incl. Lemma 3.3 itself) is "cheaper to
prove than to axiomatize" — and §4 proves it. The generic first-entrance-cut
combinatorics is folklore (prefix-closed forests; cf. stopping-time /
first-passage decompositions of branching processes, Harris 1963 Ch. II-style,
and the Kleene–Schützenberger block decompositions in Kuich's Handbook ch. 9
survey) — corroborative only, label (b) at best, no exact-statement match, no
axiom candidate. NO new literature axiom is proposed by this blueprint.

---

## 3. Proof design (section-by-section, for the prover fan-out)

Everything is stated over `History p F` lists and `VTree` (the real corpus
carrier); no new tree type is introduced (REUSE rule; and `TreeIfaceCore` lacks
`path_total`, which is free at the list level anyway).

**§3.0 Conventions.** E : History p F → Prop arbitrary (the abstract entrance
predicate; instantiation = (K-CUT-s)). All Finsets are filters of
`Tr.hfin.toFinset`. `ProperPrefix H' H := H'.IsPrefixOf H ∧ H' ≠ H`. Proper
prefixes of interest always have `H'.nodes ≠ []` (automatic: `History.nonempty`
is a structure field), so `hclosed` applies to them.

**§3.1 (H8-A1) First-entrance calculus.**
* `firstEntAbove_unique`: from `FirstEntAbove E ε₁ H` and `… ε₂ H`, clauses 3
  give ε₁ ≼ ε₂ and ε₂ ≼ ε₁; `List.IsPrefix` antisymmetry (via lengths +
  `history_ext`, exactly as `vtree_pathOrder`'s antisymm leg) gives ε₁ = ε₂.
* `firstEntAbove_exists`: the set {H' : E H' ∧ ProperPrefix H' H} is a set of
  prefixes of the LIST H.nodes — finitely many; take H₀ of minimal
  `nodes.length`; for any other entrance proper prefix H',
  `List.prefix_or_prefix_of_prefix` (both are prefixes of H.nodes) + length
  minimality forces H₀ ≼ H'. Implementation note: work with
  `Finset.filter … (Finset.range …)`-free formulation — extract the prefix
  list via `List.take`; the prover may instead induct on `H.nodes.length`.
* `firstEntAbove_shallowRead` (first entrances are minimal): a proper prefix
  H'' of ε is a proper prefix of H (trans + length <); if E H'' then clause 3
  of `FirstEntAbove … ε` gives ε ≼ H'' — contradicting H'' strictly shorter.
* `firstEntAbove_mem_chains`: `hclosed` at H ∈ chains with ε.IsPrefixOf H and
  `ε.nodes ≠ []` (= `ε.nonempty`).

**§3.2 (H8-A2) The ownership partition.**
* `read_cut_exhaustive` (⊆ direction of the union is the content): for
  H ∈ chains, classical case split on `ShallowRead E H`; in the non-shallow
  case take ε := the A1 first entrance; membership of ε in `minEnts` is A1's
  minimality + `firstEntAbove_mem_chains`; H ∈ blockReads ε by construction.
  Reverse inclusion: filters of `Tr.hfin.toFinset` are subsets.
* `shallow_block_disjoint`: a member of `blockReads ε` has the entrance ε as a
  proper prefix — refuting `ShallowRead`.
* `block_block_disjoint`: two `FirstEntAbove` witnesses at the same H —
  `firstEntAbove_unique`.
* `bdy_display`: ε ∈ shallowReads is `minEnts`' second filter conjunct;
  the block clause is `FirstEntAbove`'s second conjunct.
* Optional corollary (cheap, aids consumers): `read_cut_partition` packaging
  the three as `Finset.SupIndep`-style or a `Finset.disjiUnion` equality.

**§3.3 (H8-B1) The regroup + count-form (†).**
* `siteExp_cut`: rewrite by `read_cut_exhaustive`;
  `Finset.sum_union` (disjointness: shallow vs biUnion via
  `shallow_block_disjoint` lifted through `Finset.disjoint_biUnion_right`) +
  `Finset.sum_biUnion` (pairwise disjointness `block_block_disjoint`).
* `fiber_count_cut`: `treeExp` (verbatim hypothesis list) + `siteExp_cut` +
  `pow_add`/`Finset.prod_pow_eq_pow_sum` — mirror of E8's own composition
  step. The statement carries treeExp's FULL row list unchanged (statement-
  fence hygiene: (H8) must not silently strengthen or weaken TREE-EXP's
  conditionality).

**§3.4 (H8-A3) Abstract Lemma 3.3 over `FiberSeries` (the M04 consumer form).**
* `CutData` (the (‡)+(†) package at full-data granularity; §4 for the verbatim
  probed form): verdict monoid V abstract (corpus instance:
  `Multiset (ℕ × ℕ)` via `VTree.typemult`; `SplittingType n → V` the `vOf`
  map) — keeping V abstract avoids importing the σ-vocabulary into the
  abstract layer and lets the toy gate use ℕ.
* `seriesSum_cut`: `Equiv.tsum_eq` along `cut σ` + `ENNReal.tsum_sigma` +
  `ENNReal.tsum_mul_left` + `mass_eq` pointwise.
* `seriesSum_cut_conv`: for fixed Ŝ, regroup the compatible-tuple tsum by the
  verdict tuple (sigma-equiv on the subtype) and factor the finite product of
  countable tsums: ∑'_{g : Π i, D_i} ∏_i w(g i) = ∏_i ∑'_{d} w d — prove by
  induction on `Fin (k Ŝ)` (`Fin.cases`/`Fintype.prod_congr`, ENNReal Tonelli
  `ENNReal.tsum_mul_left/right`, `tsum_prod'`); then restrict to the
  compatibility fiber. This is the file's one genuinely fiddly proof (tagged
  HARD); its statement is probed green.
* `blockTotal` is the B of M04's Lemma 3.3 conclusion; NO claim here that it
  equals `blockSolve`'s evaluation (that is M04 K3/(H5)-territory).

**§3.5 (H8-B2) The corpus seam.** `VTreeCutSeam` (three Prop fields, §1.3,
BP_VI `RootHyps` convention: named visible fields, True-instantiable, never
axioms, no self-supply) + doc-level map field-by-field to owners. NO theorem in
this unit claims to discharge a field.

**§3.6 (H8-G1) The toy positive gate.** Non-vacuity discipline (the corpus's
standing gate pattern, cf. `HK23_twoNodeGatePos`): a concrete ≥ 3-chain VTree
at p = 2 (REUSE `MovesT/G1_toyGate.lean`'s `toyModel` node stock where
importable) + a one-entrance E; `decide`/`native_decide`-free explicit
computation that `minEnts` = the marked chain, `shallowReads` = the two
shallow chains (incl. the entrance itself — the (BDY) check), `blockReads` =
the strictly-below chain, and `read_cut_exhaustive` instantiates non-trivially.
Guards against: vacuously-true partition theorems (empty chains), E ≡ False
degeneracy, and the (BDY) off-by-one (the G-2-adjacent failure a wrong
`ProperPrefix` vs `IsPrefixOf` choice would cause — the gate FAILS if the
entrance's own read lands block-side).

---

## 4. LEAN UNIT SPECS (verbatim, compile-probed; target dir `lean/LeanUrat/Scaffold/HDischarge/H8/`)

Ground rules (inherited): namespace `LeanUrat.Scaffold.HDischarge.H8`; new files
only under the target dir; NO new axioms; no fenced statement touched; parked
items 22–29 untouched; statement-fence applies after E-phase sign-off — provers
may adjust implicit binders/instance arguments, never mathematical content.
Common prelude for every file (probed):

```lean
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D8_pathOrder
import LeanUrat.MovesT.E8_treeExp   -- H8-B1 only
import LeanUrat.MovesU.Defs         -- H8-A3/B2 only
namespace LeanUrat.Scaffold.HDischarge.H8
open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open scoped ENNReal                  -- H8-A3/B2 only
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
```

### Wave 0 — H8-D0 `CutDefs.lean` [EASY-MED; blocks everything]

```lean
/-- Proper prefix among histories (nodewise list prefix, strict). -/
def ProperPrefix (H' H : History p F) : Prop := H'.IsPrefixOf H ∧ H' ≠ H

/-- SHALLOW READ (the (BDY)-shifted ownership): no PROPER prefix of `H` is an
entrance — `H`'s own entering read is charged to the shallow layer. -/
def ShallowRead (E : History p F → Prop) (H : History p F) : Prop :=
  ∀ H', ProperPrefix H' H → ¬ E H'

/-- `ε` is THE FIRST ENTRANCE strictly above `H`. -/
def FirstEntAbove (E : History p F → Prop) (ε H : History p F) : Prop :=
  E ε ∧ ProperPrefix ε H ∧ ∀ H', E H' → ProperPrefix H' H → ε.IsPrefixOf H'

/-- MINIMAL (first) entrances of the tree — the block roots of the shallow cut. -/
noncomputable def minEnts (Tr : VTree p F) (E : History p F → Prop) :
    Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (fun ε => E ε ∧ ShallowRead E ε)

/-- The shallow-owned read sites. -/
noncomputable def shallowReads (Tr : VTree p F) (E : History p F → Prop) :
    Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (ShallowRead E)

/-- The block-`ε`-owned read sites. -/
noncomputable def blockReads (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) : Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (FirstEntAbove E ε)
```

plus definitional simp lemmas (`mem_minEnts`, `mem_shallowReads`,
`mem_blockReads` unfolding the filters — prover's discretion, no content).
Difficulty: the defs are landed-as-written; lemmas EASY.

### Wave 1 (parallel; each depends on D0 only)

**H8-A1 `CutFirst.lean` [MED] — (CUT-1), the first-entrance calculus.**

```lean
theorem firstEntAbove_unique (E : History p F → Prop) {ε₁ ε₂ H : History p F}
    (h1 : FirstEntAbove E ε₁ H) (h2 : FirstEntAbove E ε₂ H) : ε₁ = ε₂

theorem firstEntAbove_exists (E : History p F → Prop) {H : History p F}
    (h : ¬ ShallowRead E H) : ∃ ε, FirstEntAbove E ε H

theorem firstEntAbove_shallowRead (E : History p F → Prop) {ε H : History p F}
    (h : FirstEntAbove E ε H) : E ε ∧ ShallowRead E ε

theorem firstEntAbove_mem_chains (Tr : VTree p F) (E : History p F → Prop)
    {ε H : History p F} (hH : H ∈ Tr.chains) (h : FirstEntAbove E ε H) :
    ε ∈ Tr.chains
```

Proof stock: §3.1. `firstEntAbove_exists` needs classical choice on the
minimal-length entrance prefix (no decidability of E assumed — statements are
∀-E; `by_contra`/`Classical.byContradiction` freely).

**H8-A2 `CutPartition.lean` [MED-HARD] — (CUT-2) + (BDY).**

```lean
open Classical in
theorem read_cut_exhaustive (Tr : VTree p F) (E : History p F → Prop) :
    Tr.hfin.toFinset
      = shallowReads Tr E ∪ (minEnts Tr E).biUnion (blockReads Tr E)

theorem shallow_block_disjoint (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    Disjoint (shallowReads Tr E) (blockReads Tr E ε)

theorem block_block_disjoint (Tr : VTree p F) (E : History p F → Prop)
    {ε₁ ε₂ : History p F} (h : ε₁ ≠ ε₂) :
    Disjoint (blockReads Tr E ε₁) (blockReads Tr E ε₂)

theorem bdy_display (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    ε ∈ shallowReads Tr E ∧ ∀ H ∈ blockReads Tr E ε, ProperPrefix ε H
```

(`shallow_block_disjoint` in fact holds without `hε`; keep the binder — it is
the consumption shape and costs nothing. Prover may add the hε-free variant.)

**H8-A3 `Lemma33.lean` [MED for CutData+seriesSum_cut; HARD for _conv] — the
abstract M04 Lemma 3.3 over the [3t] carrier.** Verbatim (probed):

```lean
/-- THE (K-CUT) SEAM DATA over the [3t] series carrier: a countable FULL-DATA
shallow-layer family, per-slot block-derivation types, and the weight-preserving
cut equivalence — M04 Lemma 3.3's hypothesis, typed.  `V` is the verdict monoid
(corpus instance: `Multiset (ℕ × ℕ)` via `VTree.typemult`).  GRANULARITY: §1.1
(full-data; the height-forgotten resummation is CL-17(ii)/W17ii, NOT here). -/
structure CutData {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) (V : Type*) [AddCommMonoid V] where
  vOf : LeanUrat.MovesU.SplittingType n → V
  ShL : Type
  ctblS : Countable ShL
  k : ShL → ℕ
  W : ShL → ℝ≥0∞
  σ0 : ShL → V
  Deriv : (Ŝ : ShL) → Fin (k Ŝ) → Type
  ctblD : ∀ Ŝ i, Countable (Deriv Ŝ i)
  dverdict : ∀ Ŝ i, Deriv Ŝ i → V
  weight : ∀ Ŝ i, Deriv Ŝ i → ℝ≥0∞
  /-- the EXACTLY-ONE decomposition, BOTH directions (an `Equiv`: cut ∘ graft =
  id ∧ graft ∘ cut = id), verdict-compatible fibers only. -/
  cut : ∀ σ, Fb.Tree σ ≃
    {x : Σ Ŝ : ShL, ∀ i : Fin (k Ŝ), Deriv Ŝ i //
      σ0 x.1 + ∑ i, dverdict x.1 i (x.2 i) = vOf σ}
  /-- weight preservation μ(fiber T) = W(Ŝ)·∏ᵢ weight(Dᵢ) — the row's (†). -/
  mass_eq : ∀ σ (T : Fb.Tree σ),
    Fb.mass σ T = W ((cut σ T).1.1) * ∏ i, weight _ i (((cut σ T).1.2) i)

/-- The per-slot block total B_{e_i,τ_i}(v) := Σ_{D : verdict D = v} weight D. -/
noncomputable def CutData.blockTotal {n p : ℕ}
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    (CD : CutData Fb V) (Ŝ : CD.ShL) (i : Fin (CD.k Ŝ)) (v : V) : ℝ≥0∞ :=
  ∑' D : {D : CD.Deriv Ŝ i // CD.dverdict Ŝ i D = v}, CD.weight Ŝ i D.1

/-- M04 LEMMA 3.3, Lean form, step 1: regroup the fiber series along the cut. -/
theorem seriesSum_cut {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    (CD : CutData Fb V) (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : CD.ShL, CD.W Ŝ *
          ∑' g : {g : ∀ i : Fin (CD.k Ŝ), CD.Deriv Ŝ i //
              CD.σ0 Ŝ + ∑ i, CD.dverdict Ŝ i (g i) = CD.vOf σ},
            ∏ i, CD.weight Ŝ i (g.1 i)

/-- M04 LEMMA 3.3, Lean form, step 2: group by verdict tuple + Tonelli-factor —
the SHALLOW CONVOLUTION of the block totals (the K1 regroup Step 18 consumes). -/
theorem seriesSum_cut_conv {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {V : Type*} [AddCommMonoid V]
    [DecidableEq V] (CD : CutData Fb V) (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : CD.ShL, CD.W Ŝ *
          ∑' vt : {vt : Fin (CD.k Ŝ) → V //
              CD.σ0 Ŝ + ∑ i, vt i = CD.vOf σ},
            ∏ i, CD.blockTotal Ŝ i (vt.1 i)
```

NOTE (probed): `∑' g : {…}` over the sigma-subtype needs no extra instances in
ENNReal (`ENNReal.summable`); countability instances ride `ctblS`/`ctblD` — the
prover should `haveI := CD.ctblS` etc. locally as needed.

### Wave 2 (after wave 1)

**H8-B1 `SiteExpCut.lean` [MED; needs A2 + E8_treeExp] — the count-form (†).**

```lean
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem siteExp_cut (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CD : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CD χ) (E : History p F → Prop) :
    ∑ H ∈ Tr.hfin.toFinset, L.siteExp H
      = (∑ H ∈ shallowReads Tr E, L.siteExp H)
        + ∑ ε ∈ minEnts Tr E, ∑ H ∈ blockReads Tr E ε, L.siteExp H

theorem fiber_count_cut (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA.toCellData χ)
    (sc : TreeScaffold Tr T CA.toCellData χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g)
    (E : History p F → Prop) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * ((p ^ (n + ∑ H ∈ shallowReads Tr E, L.siteExp H))
          * ∏ ε ∈ minEnts Tr E, p ^ (∑ H ∈ blockReads Tr E ε, L.siteExp H))
      = p ^ m
```

The hypothesis block is `treeExp`'s VERBATIM row list (statement-fence hygiene:
(H8) must not silently re-price TREE-EXP's conditionality); the proof is
`treeExp` + `siteExp_cut` + exponent algebra.

**H8-B2 `CutSeam.lean` [EASY-MED; needs A3] — the residual surface + reduction.**

```lean
/-- (K-CUT)'s residual hypothesis surface at the [3t] carrier (BP_VI `RootHyps`
convention: named Prop FIELDS, True-instantiable, never axioms, no self-supply).
Field-by-owner map: blueprint §1.3. -/
structure VTreeCutSeam (n p : ℕ) {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) where
  /-- (K-CUT-s): the entrance predicate is CELL data (CTS-M(i)/(iii) supply;
  MOVES §S.2's fenced SUPPLY — owner [1v]/[2b], CL-13). -/
  supply_cell : Prop
  /-- (K-CUT-g): GRAFT COMPLETENESS — every verdict-compatible (Ŝ,(Dᵢ)) tuple is
  the cut of exactly one complete realizable type-σ tree (continuation
  memorylessness; the D-14 + CU-3 + REL.2 serving face — G-2's open channel). -/
  graft_complete : Prop
  /-- (K-CUT-m): the measured shallow mass / block weights equal the cut factors
  (TREE-EXP-conditional; (SIB)/(JC-multi)/[2r] priced at their own rows). -/
  mass_tie : Prop

/-- All three residual legs (the row's honest remainder after waves 0–2). -/
def VTreeCutSeam.holds {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} (S : VTreeCutSeam n p Fb) : Prop :=
  S.supply_cell ∧ S.graft_complete ∧ S.mass_tie
```

plus the module docstring carrying the §1.3 owner table and the explicit
anti-vacuity note (the fields are consumed as named assumptions by BP_V-side
units; a `trivialSeam` True-instantiation may exist ONLY next to the honesty
gate comment, mirroring `Hypotheses.lean`'s `trivialRootHyps` pattern).

**H8-G1 `ToyGate.lean` [MED; needs D0, A2] — the positive gate.** Spec §3.6/§5.
No verbatim statement pinned (gate units are constructions); MUST end with a
`#guard`-style or `example : minEnts toyTr toyE = {toyEps} := by decide/rfl`
family plus the (BDY) check `toyEps ∈ shallowReads toyTr toyE`. If
`G1_toyGate`'s stock proves too entangled to import, build a fresh 3-chain
`VTree 2 (ZMod 2)` from `Node` literals (D13's `oneNode` pattern) — new toy
data is not duplication.

### Wave 3 (after wave 2; optional consumers, LOW priority)

**H8-C1 `KCutReduce.lean` [MED]** — the display theorem tying the waves
together for BP_V/BP_VI consumption: GIVEN a `VTreeCutSeam` whose fields hold
and the wave-1/2 theorems, a `CutData` instance exists for the intended
carrier, hence `seriesSum_cut_conv`'s conclusion — the exact regroup Step 18's
K1 consumes, with the residual conditionality displayed as the three fields.
Statement to be E-phased against BP_V's `SolveSeam`/`series_tie` wiring when
BP_V unfreezes (it holds until BP_II/III land — division-order note); do NOT
guess its final binder list now. ALSO: the one-line `RootHyps` extension
(`h8_kcut : Prop` field) is a SHARED edit owned by the orchestrator across all
nine leads — flagged here, not landed by any H8 unit.

### Unit/wave summary

| unit | file | content | deps | difficulty |
|---|---|---|---|---|
| H8-D0 | `CutDefs.lean` | ProperPrefix/ShallowRead/FirstEntAbove/minEnts/shallowReads/blockReads + simp lemmas | — | EASY-MED |
| H8-A1 | `CutFirst.lean` | first-entrance exists/unique/minimal/in-chains | D0 | MED |
| H8-A2 | `CutPartition.lean` | exhaustive + 2 disjointness + (BDY) | D0, A1 | MED-HARD |
| H8-A3 | `Lemma33.lean` | CutData + blockTotal + seriesSum_cut(+_conv) | D0 (nominal) | MED / HARD(_conv) |
| H8-B1 | `SiteExpCut.lean` | siteExp_cut + fiber_count_cut | A2, E8 | MED |
| H8-B2 | `CutSeam.lean` | VTreeCutSeam + holds + owner map | A3 | EASY-MED |
| H8-G1 | `ToyGate.lean` | 3-chain positive gate + (BDY) check | D0, A2 | MED |
| H8-C1 | `KCutReduce.lean` | seam→CutData reduction display | B1, B2, BP_V | MED (E-phase later) |
| H8-R1 | (documentary) | O-11 §8 charge (vi) adjudication | — | Codex run |
| H8-R2 | (documentary) | ROOT (H8)-row re-scope spec | R1 + waves | orchestrator |

Parallelism: A1/A2/A3 run concurrently after D0 (A2 may consume A1's theorems —
if scheduled truly parallel, A2's prover re-proves locally or waits; preferred:
D0 → {A1, A3} → {A2} → {B1, B2, G1} → C1). 7 Lean units + 2 documentary.

---

## 5. Falsifier / numeric gates

* **G-2 channel coverage (design-level):** overlapping ownership ↔
  `shallow_block_disjoint`/`block_block_disjoint`; unowned read ↔
  `read_cut_exhaustive`; two decompositions ↔ `firstEntAbove_unique` +
  filter-functionality. Each Lean theorem names its channel in its docstring.
* **H8-G1 toy gate (positive, Lean):** §3.6 — fails if (BDY) is mis-shifted,
  if E ≡ False degenerates the partition, or if the entrance's own read lands
  block-side.
* **Numeric evidence (standing, cited not re-run):** the RESUM-n3 65/65 exact
  pipeline (T-8 gate) and O-11's falsifier logs (37/37, run 4 of record)
  already exercise the shallow convolution end-to-end at n = 3 — consistent
  with (K-CUT) + (K-CUT-g); they are EVIDENCE for the graft leg, never proof
  (G-3's scope caution applies: only the displayed identities are proved by
  those runs). No new numerics required for waves 0–2 (their content is
  machine-checked outright); optional: a `verification/openmath/h8_cut_check.py`
  enumerating cut decompositions on the n = 3 catalogue trees and asserting
  bijectivity against the RESUM-n3 shape list — LOW priority, spec on request.

---

## 6. What lands where (the discharge display; ROOT sync spec for H8-R2)

After waves 0–2 land green and H8-R1 records its adjudication, the honest
(H8) row state, for the orchestrator's ROOT revision (NOT executed here):

> (H8) = (K-CUT), REDUCED (blueprint `lean/blueprints/HDISCHARGE_H8.md`):
> members (K-CUT-1)/(K-CUT-2) and the (†)-regroup of (K-CUT-3) are PROVED
> Lean-core (`Scaffold/HDischarge/H8/` — first-entrance uniqueness,
> exhaustive-exclusive read ownership with the (BDY) boundary law, the
> count-form and series-form regroupings incl. M04 Lemma 3.3 as
> `seriesSum_cut_conv`), killing exactly the G-2 falsifier channels; the row's
> remaining content is the THREE-field seam `VTreeCutSeam`:
> (K-CUT-s) entrance-predicate cell-data supply [owner: CTS-M(i)/(iii)/CL-13,
> (H1)-adjacent census rows], (K-CUT-g) graft completeness [owner: the
> D-14 + CU-3 + REL.2 arc; charge-(vi) record at H8-R1], (K-CUT-m) measured
> mass tie [owners: (H7)/sibjc TREE-EXP rows + [2r]/CL-8 + O-1/O-3 count-tie].
> Consumption sites unchanged (Step 18 K1, clause (R); clause (UB) at q ↦ q^δ).

Retirement condition (unchanged from the row): full retirement into [V] debts
ONLY if charge (vi-a) PASSES (§2.5's disposition rule); otherwise the row
persists at the reduced scope above. Either way the ROOT edit is a ledgered
revision with its own VC pass — the standing acceptance-counter discipline
applies (a text change resets the counter; this blueprint does not touch ROOT).

