# MovesT LEAN BLUEPRINT (2026-07-28) — §T-ASSEMBLY: the branch-to-tree mass assembly

CORPUS: `lean/LeanUrat/MovesT/` (namespace `LeanUrat.MovesT`). WAVE 4.
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` §T-ASSEMBLY, **rev 7** (body lines
6970–7761, repairs in place), DUAL-ACCEPTED 2026-07-27 (Codex pass 8 = 0/0
`TASM_PASS8_2026-07-27.md` + Fable confirm 0/0 `FABLE_CONFIRM_TASM_REV7_2026-07-27.md`
on identical text; acceptance record MOVES 9215–9227). A Lean statement is faithful
iff it says what a rev-7 display says (campaign §0).

CONSUMES (all built, sorry-free cores):
* `LeanUrat.MovesD` — `Box`, `topLocus`, `ShapeRead`/`ShapePrefix`/`ShapeWF`/`Shape`,
  `CanonPolicy`, `PrefSet`/`PrefIdx`/`reprOf`, `Presented` (`fiber`/`event`/`mult`),
  `Threshold`, `TreeModel` (STRUCTURAL fields only), the pinned Props `D4R_CYL`,
  `ClassFiberWelldef`, `History.snoc`/`History.IsPrefixOf`, the mass laws
  (D10 `D4R1_SUM` style: division-free `Nat.card · * p^A = p^(nN)` identities),
  SW1 `ShapeWF_of_matches`, the D4R.4/L12 threshold apparatus (`Nshape`, `NPband`,
  `Shape.NP`, D4R4all).
* `LeanUrat.MovesSp` — `Species`, `StageLaws`, `Coherent` (G1–G6), `CatalogueWord`
  (confirming-letter convention W = 1), `CanTreeModel` (typing only).
* `LeanUrat.MovesC` — `History`/`Node`/`JetSetup`/`Locus`/`AdmissibleZ`/`SHZ`/
  `totalPins`/`boxMass`; `C4_conditionalMass` (the single-step conditional count law),
  `C6_thmC_b` (Theorem C(b)), `HistoryCoherent`, `Realizable`.

FORMAT: campaign master plan §2 unit specs (id/file/statement/moves_ref/deps/sketch/
difficulty/hypothesis_fields). DOCTRINE carried (campaign ledger, wave-3+ prompts): a
faithful interface must be FALSE for instances the note would reject; obligations may
be open, but their TYPES must pin their content; hypotheses neither weakened nor
silently strengthened.

---

## §0 Conditionality ledger — the note's §T.5 perimeter, typed

Every entry below is a NAMED HYPOTHESIS (ours ⇒ never an axiom, campaign §4). Each
rides as an explicit premise/field on exactly the units listed; no unit consumes one
silently, none is strengthened.

| name | note display | Lean form | status / rider sites |
|---|---|---|---|
| **(SIB)** | §T.3 display 7292: μ(⋂ Sj │ Σc) = ∏ μ(Sj │ Σc); COUNT FACE 7293–7295 | `SibCount` (Defs §2.6) — the count face, the finite-level statement this corpus prices with | OPEN KERNEL (CL-10; gate 32/32 = support not closure). Hypothesis `hsib` on T-E5/E7/E8/E10/E11/E13-corollaries |
| **(SIB-STEP)** | 7382–7388 stacked-vector form | `SibStep` (Defs §2.6), def only | OPEN; the (SIB-STEP)⟹(SIB) filtration lemma (7388–7391) is a recorded wave-5 obligation, NOT a unit (the note itself lists it inside the open kernel, §T.5(1)) |
| **(JC-multi)** | 7473–7483: multi-side joint cell = side product | `JCmulti` (Defs §2.5), def only | OPEN, census-untested; hypothesis `hjcm` at multi-side sites only (T-E7/E8/E10/E11) |
| **(HEN-LIFT)** | 7254–7261 declared statement | `HenLift` named Prop (Defs §2.7) | VP-SOUND citation obligation; discharge should PREFER Mathlib's Hensel (campaign §4) — until then a hypothesis field, never consumed by a mass unit |
| **(OM-SAT)** | 7262–7273 declared statement | `OmSat` named Prop (Defs §2.7) | VP-SOUND citation obligation (GMN/Montes cite; axiomatization would need the faithfulness-entry process). Hypothesis field only |
| **X.3 / CL-4** | 7041–7048: density form of (TGT) only | NOT typed here | this corpus states ONLY finite/normalized-count forms (TREE-EXP/TREE-N are X.3-FREE, 7046–7048); no unit consumes X.3 |
| **XRB, [2r] REL.2(a)/(b)/(d), PCI** | §T.5(5) 7644–7652; PCI 7406–7413 | `PCI` def only; REL.2 legs stay owner-tagged Props in the MovesS packages | proved nowhere here (the note: "this note states the interface and proves nothing about it") |
| **KB-TOT** | (c2) covering 7112–7119 consumes Theorem B totality (D4R.0-K(a)+(b), note-DISCHARGED) | `BranchDichotomy` (Defs §2.4) | Lean owner HC-2/D4R0K; hypothesis on T-V6, T-D3 |
| **RUN-KEY / ETA-LOC / CHAIN-LOC** | the HC-2 bridge surface (per-history locus ↔ tree membership) | named Props at §5 (W4-3 discharge) | hypothesis fields on T-D5/T-D6; owner HC-2 |
| **Q1/Q2 fence** | PROJECT_STATE 28j queue | §6 | DESIGNED here, NOT BUILT until Asvin's sign-off (task #44) |

Two REFUTATION RECORDS carried from the note (never re-claim):
* TB-CAP(ns) **literal duty FAILS** (7189–7202): the (τ-ns) class is a pro-cylinder,
  at NO finite cap a finite cylinder union. The corpus encodes ONLY the amendment
  pair (ns-lump)+(ns-null); no unit states a cap for (ns); TREE-N's hypothesis
  excludes (ns) leaves by type (T-E11's `hdet`).
* Raw-count limit **FALSE** (7237–7240): only NORMALIZED (ns) bounds are stated
  (T-C8, T-E12); no unit claims the raw count tends to 0.

---

## §1 What this corpus is (the note's §T.0, in one paragraph)

The FAM/RESUM layer (MovesD) prices MARKED-BRANCH masses μ̂ (per-branch, D4R.1-SUM);
Theorem U prices PER-f events. §T-ASSEMBLY supplies the conversion: the verdict pin VP
making the halted tree T_can^τ(f) a total choice-free function of f (§T.1–T.2), the
joint sibling kernel (SIB) pricing a tree as the product of its branches (§T.3), and
the first-split recursion TREE-EXP assembling per-f tree-fiber masses from explicit
root/joint-cell charges + §C single-branch chains + (SIB), shared prefixes charged
ONCE (§T.4). MovesT is the SOLE marked→per-f conversion site (7036–7039): no consumer
may equate a μ̂ quantity with an f-event mass except through TREE-EXP — the corpus
exports `treeExp`/`treeN`/`oneF`/the pre-halt dictionary and NOTHING that shortcuts
them. This note proves NO termination, NO exhaustion, NO rationality (7663).

---

## §2 Defs skeleton — `lean/LeanUrat/MovesT/Defs.lean` (definitions only)

Imports: `Mathlib`, `LeanUrat.MovesD.Defs`, `LeanUrat.MovesSp.Defs` (MovesC comes
through MovesD). Opens: `Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD`.
Standing binders: `{p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]`
`{n N m : ℕ} {pol : CanonPolicy p F}`. E-phase elaboration deviations go to
`MANIFEST.json` ("deviations"), exactly as in MovesD.

### 2.1 (VP-1) — the verdict alphabet

```lean
/-- (VP-1) VERDICT ALPHABET: "V := { finite multisets v of pairs (E, F) ∈ ℕ_{≥1}² }"
(MOVES 7061–7063). -/
def VerdictOK (v : Multiset (ℕ × ℕ)) : Prop := ∀ ef ∈ v, 1 ≤ ef.1 ∧ 1 ≤ ef.2

abbrev Vd : Type := {v : Multiset (ℕ × ℕ) // VerdictOK v}

/-- Σ_{(E,F) ∈ v} E·F — a τ-halted leaf of a degree-d cluster carries v with deg = d
(7062–7063; "Theorem U's σ is the whole-f instance, d = n"). -/
def Vd.deg (v : Vd) : ℕ := (v.1.map fun ef => ef.1 * ef.2).sum

/-- the degree-d slice (the finite alphabet actually carried by degree-d clusters). -/
abbrev VdAt (d : ℕ) : Type := {v : Vd // v.deg = d}

/-- (τ-hen) verdict: v = {(1, g)} (7072–7073). -/
def henVerdict (g : ℕ) (hg : 1 ≤ g) : Vd := ⟨{(1, g)}, by simpa [VerdictOK] using hg⟩

/-- (τ-irr) verdict: v = {(E, F)} at the branch's accumulated invariants (7074–7077). -/
def irrVerdict (E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) : Vd :=
  ⟨{(E, F)}, by simpa [VerdictOK] using ⟨hE, hF⟩⟩

/-- (τ-ns) verdict: v = μ·{(E(Φ̂), F(Φ̂))} (7083). -/
def nsVerdict (μ E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) : Vd :=
  ⟨Multiset.replicate μ (E, F), by
    intro ef hef; rw [Multiset.eq_of_mem_replicate hef]; exact ⟨hE, hF⟩⟩
```

### 2.2 accumulated invariants and the τ-irr firing datum

```lean
/-- E := ∏_r e_r over the branch's reads (7075). -/
def accE (H : History p F) : ℕ := (H.nodes.map fun ν => ν.e).prod
/-- F := ∏_r g_r over the branch's reads (7075). -/
def accF (H : History p F) : ℕ := (H.nodes.map fun ν => ν.g).prod

/-- (τ-irr) FIRES: ≥ 1 read, and the latest read saturates — "Saturation is equivalent
to μ = 1 at the branch's latest read" (7078–7080). Pure node/cell data: no box input,
no f. -/
def IrrHalts (H : History p F) : Prop :=
  H.nodes ≠ [] ∧ (H.nodes.getLast?).elim False (fun ν => ν.μ = 1)

/-- the (τ-irr) leaf's verdict — total via junk 1s off the realizable domain
(realizable nodes have e, g ≥ 1 through `ShapeRead.Matches`; unit T-V8). -/
noncomputable def irrVerdictOf (H : History p F) : Vd :=
  irrVerdict (max (accE H) 1) (max (accF H) 1) (le_max_right _ _) (le_max_right _ _)
```
[E-phase note: on Shape-matched coherent histories `max … 1` is the identity — the
junk guard is the same idiom as MovesD's `poolProj`; the guard is NEVER load-bearing
on `PrefSet` members.]

### 2.3 the root reduction datum and (τ-hen)

```lean
/-- the level-0 reduction f̄ of a box member, through an injective level-0 chart χ:
monic degree-n over F_p = ZMod p ("the root read is the reduction split f̄", 7069–7071;
(JC-root)'s "ONE digit layer, the n coefficient digits pinned", 7464–7466). -/
noncomputable def redPoly (χ : Fin n → Fin m) (x : Box p m) : Polynomial (ZMod p) :=
  Polynomial.X ^ n + ∑ b : Fin n, Polynomial.C (x (χ b)) * Polynomial.X ^ (b : ℕ)

/-- the level-0 cell {f : f̄ = g} ((JC-root), 7464). -/
def rootCell (χ : Fin n → Fin m) (g : Fin n → ZMod p) : Set (Box p m) :=
  {x | ∀ b : Fin n, x (χ b) = g b}

/-- the Hensel-track degrees of x: degrees of the SIMPLE (multiplicity-1) monic
irreducible factors of f̄ — "A track with m_i = 1 … halts with NO window read ever
opened: v = {(1, g)}" (7071–7073). -/
noncomputable def henDegrees (χ : Fin n → Fin m) (x : Box p m) : Multiset ℕ :=
  ((UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)).toFinset.filter
    (fun ψ => Multiset.count ψ
      (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)) = 1)).val.map
    Polynomial.natDegree

/-- the (τ-hen) verdict payload of x. -/
noncomputable def henPayload (χ : Fin n → Fin m) (x : Box p m) : Multiset Vd :=
  (henDegrees χ x).map (fun g => henVerdict (max g 1) (le_max_right _ _))
```
[E-phase: `max g 1` guard — irreducible factors have degree ≥ 1, the guard is dead;
keep the def total.]

### 2.4 τ over the model, pruning, decidedness

```lean
/-- (τ-ns) FIRES at (o, x): the state is realized and its branch set at x is EMPTY —
"CELLS whose window admits no side (J(f) = ∅)" (7081–7083). Cell data through the
model's child predicate. -/
def NsHalts (T : TreeModel p F n N m pol) (o : Option (History p F)) (x : Box p m) :
    Prop :=
  T.mem o x ∧ ∀ ν : Node p F, ¬ T.child o ν x

/-- KB-TOT (hypothesis carrier — Theorem B's structural totality, D4R.0-K(a)+(b),
note-DISCHARGED, consumed by (c2)'s covering 7112–7119): at a realized nonempty-chain
state, either some child exists and every child-branch either saturates (IrrHalts of
the extension) or continues, or the no-side status holds. Lean owner: HC-2/D4R0K. -/
def BranchDichotomy (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    (∃ ν, T.child (some H) ν x) ∨ NsHalts T (some H) x

/-- τ-PRUNED membership: H ∈ T_can^τ(x) — realized, and NO proper nonempty prefix
τ-halts ("The engine's below-halt continuations exist syntactically but are NOT
walked", 7086–7088). (τ-hen) never applies to chains (its domain is level-0 tracks,
7069). -/
def PrunedMem (T : TreeModel p F n N m pol) (H : History p F) (x : Box p m) : Prop :=
  T.mem (some H) x ∧
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H →
    ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x
```

### 2.5 finite pruned trees, fibers, read sites, thresholds

```lean
/-- A COMPLETE FINITE (canonical, τ-pruned) TREE — the (TGT) summation object
(7017–7024): chains = realized value-prefixes; `henV` = the root cell's Hensel-track
verdicts (level-0 tracks carry NO chain — VP-2 (τ-hen)); `leafV` = the (τ-irr)/(τ-ns)
verdicts at maximal chains. `nsLeaf` marks which leaves are (ns) — TREE-EXP's product
form EXCLUDES trees with any (7457–7461). -/
structure VTree (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  chains : Set (History p F)
  hfin : chains.Finite
  hne_nodes : ∀ H ∈ chains, H.nodes ≠ []
  hclosed : ∀ H ∈ chains, ∀ H' : History p F,
    H'.IsPrefixOf H → H'.nodes ≠ [] → H' ∈ chains
  henV : Multiset Vd
  hhen : ∀ v ∈ henV, ∃ g : ℕ, 1 ≤ g ∧ v.1 = {(1, g)}
  leafV : History p F → Option Vd
  hleaf : ∀ H, (leafV H).isSome ↔ (H ∈ chains ∧ IsMaximalIn chains H)
  nsLeaf : History p F → Prop

/-- maximality in a chain set (leaf = no strict extension present). -/
def IsMaximalIn (S : Set (History p F)) (H : History p F) : Prop :=
  ∀ H' ∈ S, H.IsPrefixOf H' → H' = H

/-- typemult(T) := ⊎_{leaves ℓ} v(ℓ), hen tracks included (7024–7025). -/
noncomputable def VTree.typemult (T : VTree p F) : Multiset (ℕ × ℕ) := …
  -- Σ over hfin.toFinset-restricted leaves of (leafV H).elim 0 (·.1), + Σ over henV
  -- [E-phase fixes the Finset plumbing; the VALUE is the display's ⊎.]

/-- THE TREE FIBER {x : T_can^τ(x) = T}, graph-equality form — "one f, ONE tree"
(7025–7029): (i) chains are EXACTLY the pruned realized prefixes; (ii) every leaf
τ-halts at x with the recorded verdict, (ns) leaves exactly at NsHalts; (iii) the
hen payload matches x's root datum; (iv) non-leaves do not halt. -/
def VTree.fiberAt (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  (∀ H : History p F, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)) ∧
  (∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →
    ((IrrHalts H ∧ ¬ Tr.nsLeaf H ∧ Tr.leafV H = some (irrVerdictOf H)) ∨
     (NsHalts T (some H) x ∧ Tr.nsLeaf H))) ∧
  Tr.henV = henPayload χ x ∧
  (∀ H ∈ Tr.chains, ¬ IsMaximalIn Tr.chains H →
    ¬ IrrHalts H ∧ ¬ NsHalts T (some H) x)
```
[E-phase: the (ns) leaf's verdict VALUE (nsVerdict μ E F) is recorded through `leafV`
with the same shape law as `hhen`; exact clause fixed at E-phase against 7083. The
graph-equality form is the DESIGN: disjointness (T-E9) and ONE-F (T-F1) fall out of
functionality, exactly the note's "T_can^τ is a function … distinct trees have
disjoint preimages" (7026–7028).]

```lean
/-- DECIDED at x := some complete finite tree fibers x — (TGT)'s decided set, the
domain ONE-F partitions (7580, 7586–7589). The undecided complement is [5]'s (X.3);
NOT priced here. -/
def Decided (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  ∃ Tr : VTree p F, Tr.fiberAt T χ x

/-- READ SITES of T (7441–7448): the root site plus every chain of T; each site's
JOINT CELL is the full realized stratum datum of that read. Site list =
`none :: (chains as some ·)`; the per-site joint-cell EVENT is `SiteCell` below. -/
def VTree.sites (Tr : VTree p F) : Set (Option (History p F)) :=
  insert none (some '' Tr.chains)

/-- the joint-cell event of a site, given the state event above it: at the root, the
level-0 cell (JC-root); at a window read, the read's full stratum — the event that x
realizes EXACTLY this chain's last read from its parent state (7443–7448). -/
def SiteCell (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    Option (History p F) → Set (Box p m)
  | none => Set.univ  -- the root's AMBIENT state; its cells are `rootCell χ g`
  | some H => {x | T.mem (some H) x}
```
[Design note, load-bearing: TREE-EXP is stated DIVISION-FREE in the D10 house style —
"jvol(c_s │ Σ) = p^{−k_s}" becomes `Nat.card ↥(cell ∩ Σ) * p ^ k_s = Nat.card ↥Σ`,
and the site product becomes one exponent sum. No ℚ, no measure API; the profinite μ
statements of the note are consumed at their finite-level faces, which is what the
note's own TREE-N/count displays provide (7568–7574).]

```lean
/-- thr(T) (7562–7566): the max over T's branches of the §D4-R L12/D4R.4 thresholds
N(η,⊤), joined with TB-CAP caps of the halted leaves and the joint-cell levels
(level 1 at the root). All shape/height data. -/
noncomputable def VTree.thr (Tr : VTree p F) (n : ℕ) : ℕ := …
  -- max over hfin.toFinset of (shapeOfH H).Nshape ⊔ 1  [E-phase: exact join per
  -- 7562–7566; `shapeOfH` below]

/-- the retained ShapeRead of a node (the L3 dictionary, node → shape side). -/
noncomputable def readOf (ν : Node p F) (r : ℕ) (n : ℕ) : ShapeRead := …
  -- componentwise: species/e/h/g/μ/a/s0/wSide/Dwidth/ustar/gam from ν's fields;
  -- w := (Nat.card ↥ν.σ.K).factorization p; monicTop := decide (r = 0 ∧ s0+wSide = n)
/-- the shape of a history (unit T-V8 proves MatchesHist + ShapeWF via SW1). -/
noncomputable def shapeOfH (H : History p F) (n : ℕ) : ShapePrefix :=
  ⟨(List.range H.nodes.length).map fun r => (H.nodes[r]?).elim default
    (fun ν => readOf ν r n)⟩
```

### 2.6 (SIB) — the joint sibling kernel, COUNT FACE (hypothesis, NEVER proved here)

```lean
/-- the event that branch (o, ν)'s continuation realizes the PRESCRIBED finite
subtree — (SIB)'s S_j quantifier ("S_j determined by b_j's own continuation reads",
7287–7290): the prescribed chains are exactly the pruned realized extensions of
o·ν, with the subtree's leaf/halt clauses as in `fiberAt`. -/
def ContFiber (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (Tsub : Set (History p F)) (leafSpec : History p F → Option Vd)
    (x : Box p m) : Prop := …
  -- [E-phase: the rooted analogue of fiberAt clauses (i)/(ii)/(iv), root = o·ν;
  --  no hen clause (hen is level-0 only); shape law as in fiberAt.]

/-- **(SIB), COUNT FACE, tree-indexed** — the note's display 7292 at finite level
("COUNT FACE (same statement at finite level): the joint fresh-assignment counts
multiply", 7293–7295), SIBLING INDEXING binding (7415–7423: member-indexed Finset,
no ordering, no symmetry factor). THE CENTRAL HYPOTHESIS of this corpus: OPEN
(CL-10), gate-supported (SIB 32/32, T-n3 21/21), consumed by TREE-EXP at every
branching cell, NEVER proved. The base-changed O_δ reading of each S_j is [2r]
REL.2(a)/(b)/(d)'s identification — cited in the packages (§5 S-9), not needed to
STATE the count face. -/
def SibCount (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
  ∀ (o : Option (History p F)) (Σc : Set (Box p m)) (B : Finset (Node p F))
    (S : Node p F → Set (Box p m)),
    2 ≤ B.card →
    (∀ x ∈ Σc, T.mem o x ∧ ∀ ν ∈ B, T.child o ν x) →
    (∀ ν ∈ B, ∃ Tsub leafSpec, S ν = {x | ContFiber T o ν Tsub leafSpec x}) →
    Nat.card ↥(Σc ∩ ⋂ ν ∈ B, S ν) * (Nat.card ↥Σc) ^ (B.card - 1)
      = ∏ ν ∈ B, Nat.card ↥(Σc ∩ S ν)

/-- (SIB-STEP), stacked-vector form (7382–7388) — def ONLY; its ⟹(SIB) filtration
lemma is the note's own open remainder (§T.5(1)), a wave-5 obligation. Typed so the
kernel's CONTENT is pinned: joint uniformity of the stacked next-read vector on the
PRODUCT alphabet, conditionally on the entire joint past — "not a conjunction of
marginals" (7387). -/
def SibStep (T : TreeModel p F n N m pol) : Prop := …
  -- [E-phase: stacked one-step uniform-fiber statement over the interleaved
  --  filtration's stage events; NOT consumed by any wave-4 unit.]

/-- PCI (parent-context independence) — "named interface, NOT part of (SIB)"
(7406–7413); stated, proved nowhere, consumed by nothing in MovesT (REV 13 struck
PCI from TREE-EXP's inputs, 7650–7652). A PCI failure adjudicates as R2's
lumpability channel, never as a (SIB) failure. -/
def PCI : Prop := …  -- [owner-tagged; field value for the MovesS packages, §5 S-9]
```

### 2.7 VP-SOUND's two declared citations (typed, hypothesis-only)

```lean
/-- (HEN-LIFT) (7254–7261): coprime-factor Hensel over ℤ_p — a simple irreducible
factor ψ of f̄ lifts uniquely to a monic irreducible unramified g │ f, (E,F) =
(1, deg ψ). Valid at ALL primes incl. wild (coprimality, not tameness). Discharge
route: Mathlib Hensel (campaign §4 prefers the library); until then a named Prop. -/
def HenLift (p : ℕ) [Fact p.Prime] : Prop := …
  -- [E-phase types it against Polynomial ℤ_[p]; NO mass unit consumes it — it backs
  --  VP-SOUND's read-off, which this corpus does not price.]

/-- (OM-SAT) (7262–7273): the Ore–Montes certificate — a saturated branch's cluster
factor is irreducible with e = E, f = F. CONSUMED as a cite (GMN/Montes), "not
derived from §B2-DEF" (7267–7270). Named Prop; axiomatization would need the
faithfulness-entry + guardian process. -/
def OmSat (p : ℕ) [Fact p.Prime] : Prop := …
```
VP-SOUND status (7274–7279) transcribed: a CITATION obligation with two declared
statements, NOT a gap in the mechanism; the PARI-oracle layers are the standing
refuters; D4R.0-K(c)'s remainder = exactly {VP-SOUND's cites} (7634–7635).

### 2.8 pre-halt marks and the dictionary carriers (ONE-F)

```lean
/-- PRE-HALT (7595–7598): none of η's PROPER prefixes τ-halts — "a property of η's
OWN cell data". Box-free for the IrrHalts clause; the (ns) clause needs the model. -/
def PreHaltPfx (T : TreeModel p F n N m pol) (H : History p F) (x : Box p m) : Prop :=
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H →
    ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x

/-- the length-ℓ chains of a tree T of shape P̂ (the dictionary's per-tree count,
7601–7603). -/
noncomputable def VTree.chainCount (Tr : VTree p F) (n : ℕ) (P : Shape n) : ℕ :=
  Nat.card {H : History p F // H ∈ Tr.chains ∧ (P : ShapePrefix).MatchesHist H}
```

### 2.9 the seam-discharge carriers (consumed at §5; see units T-D1…T-D13)

```lean
/-- the joint-cell assignment — MovesT's cell vocabulary (the W4-1/W4-2 re-keying
target): a cell datum per (state, box) with (a) finiteness, (b) locality at the
CELL'S OWN LEVEL (a per-state level from shape/height data — NOT the withdrawn
uniform cap envelope; §5 W4-2), (c) the branch set read off the cell. -/
structure CellAssign (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (T : TreeModel p F n N m pol) where
  Cell : Type
  hCellFin : Finite Cell
  cellOf : Option (History p F) → Box p m → Cell
  cellLevel : Option (History p F) → ℕ
  levelOf : Fin m → ℕ
  cell_local : ∀ (o : Option (History p F)) (x x' : Box p m),
    (∀ c : Fin m, levelOf c < cellLevel o → x c = x' c) → cellOf o x = cellOf o x'
  branchSetOf : Cell → Finset (Node p F)
  child_cell : ∀ (o : Option (History p F)) (ν : Node p F) (x : Box p m),
    T.mem o x → (T.child o ν x ↔ ν ∈ branchSetOf (cellOf o x))

/-- W4-1's re-keyed `eligible` — a DEFINED predicate over the cell/branch-set
vocabulary (MovesD §2.5 W4-1(c) verbatim: "`eligible` becomes a DEFINED predicate
over MovesT's cell/branch-set vocabulary"). -/
def eligibleT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) : Prop :=
  ν ∈ CA.branchSetOf (CA.cellOf o x)
```

---

## §3 The unit DAG — 51 units (12 easy / 29 medium / 10 hard)

### Layer V — VP: the verdict pin (§T.1) [8 units]

**T-V1 `MovesT.vd_deg_hen` · `V1_vdDeg.lean` · easy**
```lean
theorem vd_deg_hen (g : ℕ) (hg : 1 ≤ g) : (henVerdict g hg).deg = g
```
moves_ref: 7072–7073 "halts with NO window read ever opened: v = {(1, g)}" + 7062
"Σ E·F = d". deps: Defs. sketch: `simp [Vd.deg, henVerdict]`; one-element multiset,
1·g = g. hypothesis_fields: none.

**T-V2 `MovesT.vd_deg_ns` · `V2_vdDegNs.lean` · easy**
```lean
theorem vd_deg_ns (μ E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) :
    (nsVerdict μ E F hE hF).deg = μ * (E * F)
```
moves_ref: 7083 "v = μ · {(E(Φ̂), F(Φ̂))}"; degree = cluster degree μ·deg Φ̂.
deps: Defs. sketch: `Multiset.map_replicate` + `Multiset.sum_replicate`.
hypothesis_fields: none.

**T-V3 `MovesT.accEF_keyDeg` · `V3_accKeyDeg.lean` · medium**
```lean
theorem accEF_keyDeg {n : ℕ} (l : List MovesSp.Species) (hne : l ≠ [])
    (hroot : ∀ s, l.head? = some s → MovesSp.RootStage n s)
    (hchain : l.Chain' MovesSp.StageLaws) (s : MovesSp.Species)
    (hlast : l.getLast? = some s) (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    ((l.map fun t => t.e).prod * g) * ((l.map fun t => ?g_of t).prod) = s.e * g * s.D
```
[E-phase fixes the exact product bookkeeping: the accumulated ∏e·∏g through the last
selection equals the CHILD key degree D′ = e·g·D, whence child cluster degree =
D′·μ = (E·F)·μ.] moves_ref: 7078–7080 "cluster degree = key degree · μ = E·F·μ".
deps: MovesSp.Defs (StageLaws, RootStage). sketch: list induction along `Chain'
StageLaws`: D_{r+1} = e_r·g_r·D_r with D_0 = 1 (RootStage) telescopes to
∏ e·∏ g = D′; multiply by μ. difficulty: medium. hypothesis_fields: none (pure
species bookkeeping; the g-projection needs each letter's selection — E-phase
threads the selections as a list, per the sketch).

**T-V4 `MovesT.sat_iff_confirming` · `V4_satW1.lean` · medium**
```lean
theorem sat_iff_confirming {n : ℕ} (s s' : MovesSp.Species)
    (hstep : MovesSp.StageLaws s s') (hcoh : MovesSp.Coherent s')
    (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    (μ = 1) ↔ (s'.W = 1)
```
and the (G6) face `(μ = 1) ↔ s'.sel = none`. moves_ref: 7078–7080 saturation ⟺
μ = 1; MovesSp (G6) "selection = ⊥ iff W = 1"; the τ-irr halt = MovesSp's confirming
W = 1 letter (CatalogueWord.hLast). deps: MovesSp.Defs. sketch: StageLaws gives
s'.W = μ; (G6) from `hcoh` converts. Ties VP-2 (τ-irr) to the ALREADY-BUILT
catalogue convention — the two corpora's halt notions provably agree.
hypothesis_fields: none.

**T-V5 `MovesT.tau_disjoint` · `V5_tauDisjoint.lean` · medium**
```lean
theorem tau_disjoint (T : TreeModel p F n N m pol) (H : History p F) (x : Box p m)
    (hmem : T.mem (some H) x) : ¬ (IrrHalts H ∧ NsHalts T (some H) x) ∨ True
```
STATEMENT DUTY [E-phase final form]: the three domains pairwise disjoint —
(τ-hen) fires only at level-0 tracks (no chain: disjoint from both by TYPE — hen
lives in `henPayload`, never on `chains`); (τ-irr) needs a NONEMPTY branch set
member saturating vs (τ-ns)'s EMPTY branch set: state as
`IrrHaltsAsChild T o ν x → ¬ NsHalts T o x` where IrrHaltsAsChild names the halted
branch as a member of o's branch set. moves_ref: 7104–7111 "MUTUAL EXCLUSIVITY, by
domain stratification … disjoint by depth … disjoint by case". deps: Defs.
sketch: the hen/chain split is definitional (carrier separation); irr-vs-ns: the
halting branch is a child (T.child o ν x), contradicting NsHalts's ∀ ν ¬child.
difficulty: medium. hypothesis_fields: none.

**T-V6 `MovesT.tau_total` · `V6_tauTotal.lean` · medium**
```lean
theorem tau_total (T : TreeModel p F n N m pol) (hdi : BranchDichotomy T)
    (H : History p F) (x : Box p m) (hmem : T.mem (some H) x) :
    (∃ ν, T.child (some H) ν x) ∨ NsHalts T (some H) x
```
plus the leaf reading: a chain with no children τ-halts one way (ns) or extends into
halted children (irr at the extension) — no orphan, none twice (with T-V5).
moves_ref: 7112–7119 "COVERING, the case analysis (no orphan)". deps: Defs, T-V5.
sketch: literal from `BranchDichotomy` — the content IS the hypothesis (Theorem B
totality, note-DISCHARGED at D4R0K (a)/(b)); this unit is the honest typed rider,
consumed by T-D3's halt_iff. hypothesis_fields: `hdi : BranchDichotomy T` (KB-TOT,
owner HC-2/D4R0K — NEVER proved here).

**T-V7 `MovesT.vdAt_finite` · `V7_vdFin.lean` · medium**
```lean
instance vdAt_finite (d : ℕ) : Finite (VdAt d)
```
moves_ref: 7061–7063 (V's degree-d slice is what a degree-d cluster carries) —
needed so W4-2's `hVfin` is INSTANTIABLE at V := VdAt n (§5 W4-2). deps: Defs.
sketch: a verdict of deg d has ≤ d pairs, each in [1,d]²; inject into
`Multiset.replicate`-bounded multisets / `Sym`-type on Fin (d+1) × Fin (d+1);
finiteness by cardinality embedding (MovesSp SP2's encoding idiom).
hypothesis_fields: none.

**T-V8 `MovesT.shapeOfH_matches` · `V8_shapeOf.lean` · medium**
```lean
theorem shapeOfH_matches (H : History p F) (n : ℕ) (hcoh : HistoryCoherent H)
    (hbox : InBox n H) :
    (shapeOfH H n).MatchesHist H ∧ ShapeWF n (shapeOfH H n)
```
moves_ref: §D4-R L3 dictionary (the corpus's shape-of-a-branch tie; TB-CAP(irr) and
thr(T) read thresholds off it, 7562–7566). deps: Defs, MovesD.SW1_shapeWF.
sketch: componentwise Matches is definitional (readOf copies ν's fields; the w
field's card identity from ν.σ.K's card = p^w — E-phase may need the coherence
clause carrying it); ShapeWF via MovesD's `ShapeWF_of_matches` (SW1, built).
hypothesis_fields: none beyond coherence (already the L3 setting).

### Layer C — TB-CAP per clause + the (ns) pair (§T.2) [8 units]

**T-C1 `MovesT.tbcap_hen` · `C1_capHen.lean` · medium**
```lean
theorem tbcap_hen (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (x x' : Box p m) (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    henPayload χ x = henPayload χ x'
```
plus the partition face: the verdict class {x │ henPayload χ x = v₀} is a UNION of
level-0 cells `rootCell χ g` (finitely many g : Fin n → ZMod p), i.e. membership
depends on x only through x ∘ χ. CAP N_V = 1, uniform per class. moves_ref:
7155–7159 "TB-CAP(hen): PROVED (cap N_V = 1) … a union of level-1 cells (finitely
many …), each a level-1 cylinder." deps: Defs. sketch: `redPoly χ x` is a function
of x ∘ χ (definitional); henDegrees/henPayload factor through it; the class is a
preimage under x ↦ x ∘ χ, whose fibers are the level-0 cells — union + finiteness
free. hypothesis_fields: none. PROVED-IN-NOTE status: unconditional.

**T-C2 `MovesT.tbcap_irr` · `C2_capIrr.lean` · medium**
```lean
theorem tbcap_irr {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P)
    (hirr : IrrHalts (reprOf i)) (hstab : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx c < (P : ShapePrefix).NPband n → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i)
```
[levelIdx = the chart's level projection; E-phase keys it to the presented jets'
`coordOf` per MovesD's chart tie.] moves_ref: 7161–7182 "the verdict class at this
leaf is EXACTLY the extended single-branch event S(η′,⊤) … §C C.2 (Z = ∅) cuts
S(η′,⊤) at level N(η′,⊤) … So N_V := N(η′,⊤) works." + the quantifier honesty
7183–7187 (per REALIZED halting branch-read; NO cap uniform over all cells claimed —
the statement above is per (P, i), never joined). deps: Defs, MovesD (Presented,
NPband, D4R.4 apparatus/D8 band shape). sketch: the class IS S(η′,⊤) by definition
of fiber (the extended history is the enumerated class member); the finite-level cut
is MovesD's D4R.4/L12 exact-realization at stabilized levels, restated as
digit-locality below NPband. difficulty: medium. hypothesis_fields: `S.jet` (the
Presented family — HC-2's PRESENT-EXIST supplies instances); the NP-ID pin is NOT
consumed (locality is stated at NPband, the corpus-native cutoff — no max_η claim).

**T-C3 `MovesT.ns_lump` · `C3_nsLump.lean` · medium**
```lean
def nsClass (T : TreeModel p F n N m pol) (H : History p F) : Set (Box p m) :=
  {x | NsHalts T (some H) x}
def lump (L : ℕ → Set (Box p m)) : Prop := Antitone L   -- the capped lumps L_M
theorem ns_lump (T : TreeModel p F n N m pol) (H : History p F)
    (L : ℕ → Set (Box p m)) (hL : IsNsLumpFamily T H L) :
    (∀ M M', M ≤ M' → L M' ⊆ L M) ∧ nsClass T H = ⋂ M, L M
```
where `IsNsLumpFamily` pins L M := {all window-slot digits vanish up to height M}
against the model's child predicate [E-phase: the family enters as data with its
defining property — B(iii)'s capped format — because the slot/height vocabulary is
MovesC's jet chart; the property ties L to `NsHalts` exactly]. moves_ref: 7203–7209
"(ns-lump) CAP-APPROXIMABILITY … the level-N saturation … is the SINGLE level-N
cylinder L_{M(N)} … monotone in N with the class as the intersection. PROVED (a
re-reading of B(iii), no new content)." deps: Defs. sketch: monotonicity + the
intersection identity are the defining clauses of the family, given "no side at
every height ⟺ vanishing at all heights" (the IsNsLumpFamily tie). difficulty:
medium. hypothesis_fields: `hL` (the B(iii) lump identification — owner D4R0K
Theorem B(iii), note-standing-perimeter; typed, not re-proved).

**T-C4 `MovesT.ns_ladder` · `C4_nsLadder.lean` · medium**
```lean
theorem ns_ladder (M₀ : ℕ) (Zcard : ℕ → ℕ) (hlad : ∀ M, M₀ ≤ M → M - M₀ ≤ Zcard M) :
    Filter.Tendsto (fun M => (p : ℝ) ^ (-(Zcard M : ℤ))) Filter.atTop (nhds 0)
```
moves_ref: 7227–7229 "(iii) |Z_M| → ∞: slot 0's block b₀ … one coordinate per level,
heights unit-spaced, so |Z_M| ≥ ⌊M − M₀⌋." deps: none beyond Mathlib. sketch:
|Z_M| ≥ M − M₀ → ∞, p ≥ 2, zpow-antitone squeeze. The LADDER INPUT (one fresh
coordinate per level at the interior block b₀ — "the window interior is never
empty") is T-C5's output `hlad`. difficulty: medium. hypothesis_fields: none (pure
analysis; `hlad` discharged by T-C5 at consumption in T-C7).

**T-C5 `MovesT.nsZ_free` · `C5_nsFree.lean` · hard**
```lean
theorem nsZ_free {H : History p F} (J : JetSetup H n N m) (M : ℕ) (hM : M₀ J ≤ M) :
    ∃ Z : Locus p m, AdmissibleZ (J.Sigma H.nodes.length) Z ∧
      IsLumpLocus J M Z ∧ M - M₀ J ≤ pinCount Z
```
[`IsLumpLocus J M Z` := Z's equations are EXACTLY the fresh clauses of L_M —
interior blocks (base index < μ·D), F(b) < ht ≤ M; `M₀ J` := the entrance
resolution; `pinCount` := the number of fresh equations. E-phase types these three
against MovesC's Locus/floor vocabulary (`History.floorH`, the (ZC) fields of J).]
moves_ref: 7216–7229 "(i) Z_M is finite and ADMISSIBLE in C.2's rev-9 sense — each
equation solves for its own coordinate, FREE on Σ: interior indices are determined
iff ht ≤ F(b) ((ZC-a) …), and DIG_k's leads sit at rim indices, base ≥ μ·D ((ZC-b)),
never interior." deps: Defs, MovesC (AdmissibleZ, the ZC carriers), MovesD
(floorS/bandS mirrors for the shape-side reading). sketch: construct Z_M explicitly
from the block/height grid; freeness: an interior coordinate at height > F(b) is
unpinned on Σ by (ZC-a)'s inclusive top; rim leads never interior by (ZC-b)'s base
≥ μ·D; the ladder count from slot 0's unit-spaced heights. THE ONE SUBSTANTIVE NEW
PROOF of the corpus's C-layer — the note's rev-2 (ns-null) mechanism, verified clean
FOUR times (9222–9223). difficulty: hard (pre-approved split: C5a the locus
construction + count; C5b admissibility/freeness). hypothesis_fields: the (ZC)
package carried by J (MovesC's accepted induction — standing perimeter, 7232–7233).

**T-C6 `MovesT.ns_price` · `C6_nsPrice.lean` · medium**
```lean
theorem ns_price {H : History p F} (J : JetSetup H n N m) (M : ℕ) (hM : M₀ J ≤ M)
    (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z)
    (hlump : IsLumpLocus J M Z) :
    Nat.card ↥(J.SHZ Z) * p ^ pinCount Z = Nat.card ↥(J.SHZ (topLocus p m))
```
moves_ref: 7225–7227 "(ii) Theorem C(b) with Z = Z_M prices the lump exactly:
μ(S(H, Z_M)) = μ(S(H, ⊤))·p^{−|Z_M|}." deps: MovesC.C6_thmC_b, T-C5. sketch:
two C6_thmC_b instances (at Z and at ⊤) share boxMass; divide the pin counts —
division-free: cross-multiply the two `Nat.card · * p^· = boxMass` identities.
difficulty: medium. hypothesis_fields: J (the jet — HC-2 territory), hZ/hlump from
T-C5.

**T-C7 `MovesT.ns_null` · `C7_nsNull.lean` · medium**
```lean
theorem ns_null {H : History p F}
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N'))
    (hlumps : …)  -- the L_M family realized as IsLumpLocus at each level (T-C3/T-C5)
    :
    Filter.Tendsto
      (fun M => (Nat.card ↥(nsTrunc Jat M) : ℝ) / (Nat.card ↥(stateTrunc Jat M)))
      Filter.atTop (nhds 0)
```
[`nsTrunc`/`stateTrunc` := the level-M(N) truncated lump ∩ state and state counts —
the finite-level face of μ((τ-ns) class │ Σ); E-phase fixes the level-threading via
the Scale map exactly as 7205–7207.] moves_ref: 7210–7231 "(ns-null) NULLITY:
μ((τ-ns) class │ Σ) = 0 — PROVED … μ(Σ ∩ L_M) → 0, and the class = ∩_M (Σ ∩ L_M)
((ns-lump)) gives μ((τ-ns) class │ Σ) = lim_M = 0 by continuity from above."
deps: T-C4, T-C5, T-C6, T-C3. sketch: per M, T-C6 gives ratio = p^{−|Z_M|}; T-C5's
count + T-C4's limit squeeze it to 0. Continuity-from-above is REPLACED at finite
level by stating the limit over the truncations themselves (the corpus's only limit
statement; the profinite class never enters). difficulty: medium.
hypothesis_fields: the jet family (HC-2's PRESENT-EXIST face) + the lump
identification (T-C3's hL).

**T-C8 `MovesT.ns_tree_bound` · `C8_nsTreeBound.lean` · medium**
```lean
theorem ns_tree_bound (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (H : History p F) (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) :
    {x | Tr.fiberAt T χ x} ⊆ nsClass T H
```
+ the normalized corollary: the fiber's truncated counts are dominated by T-C7's
vanishing ratios — NEVER a raw-count claim. moves_ref: 7240–7247 "(i) an (ns)-leaf
tree's fiber is contained in a null class … (ii) … the one-sided NORMALIZED bound
p^{−nN}·#{…} ≤ μ(L_{M(N)} ∩ …) → 0 … NO claim that the raw count tends to 0."
deps: Defs, T-C7. sketch: fiberAt's leaf clause at H gives NsHalts at every fiber
member — inclusion is one line; monotonicity of counts under ⊆ gives the bound.
difficulty: medium. hypothesis_fields: inherited from T-C7 at the corollary only.

### Layer S — (SIB) as hypothesis (§T.3) [3 units]

**T-S1 `MovesT.sib_defs_wf` · `S1_sibDefs.lean` · easy**
```lean
theorem sibCount_mono (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (h : SibCount T χ) : True  -- compile witness; plus:
theorem sibCount_pair_form (T …) (h : SibCount T χ) (o Σc b₁ b₂ S₁ S₂ …) :
    Nat.card ↥(Σc ∩ (S₁ ∩ S₂)) * Nat.card ↥Σc
      = Nat.card ↥(Σc ∩ S₁) * Nat.card ↥(Σc ∩ S₂)
```
moves_ref: 7292 the display; 7523–7525 "P3's censused identity 78,125² =
15,625·390,625 is exactly (SIB) at this site" — the m = 2 specialization IS the
gate-checked shape. deps: Defs §2.6. sketch: instantiate B = {b₁, b₂}
(SIBLING INDEXING: a two-member Finset, DecidableEq via classical), card 2,
exponent 1. hypothesis_fields: `h : SibCount T χ` (the kernel — this unit only
RESHAPES it). Purpose: the consumers (T-E5/E7) call this form.

**T-S2 `MovesT.sib_falsifier` · `S2_sibFalse.lean` · medium**
```lean
theorem sib_falsifier : ∃ (T : TreeModel 2 (ZMod 2) 2 1 2 polTriv) (χ : _),
    ¬ SibCount T χ
```
moves_ref: doctrine (campaign ledger): "a faithful interface must be FALSE for
instances the note would reject" — (SIB) is a CONTENTFUL law (the note calls a
surviving failure "the campaign's named structural wall", 7397–7400), so the Prop
must be falsifiable. deps: Defs. sketch: a toy 2-element-box model with two
children whose continuation events are IDENTICAL (the note's own warning shape,
7379–7381: "two contemporaneous reads can each be uniform yet identical") — the
joint count then fails the product; `decide`-scale. difficulty: medium.
hypothesis_fields: none. [`polTriv` := the constant-lift policy on the toy — Gates
layer supplies it.]

**T-S3 `MovesT.sib_root_instance` · `S3_sibRoot.lean` · easy**
```lean
theorem sib_root_instance (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (h : SibCount T χ) :
    ∀ (Σc B S …), (o = none case of SibCount) …
```
moves_ref: 7298–7304 "DEPTH-0 INSTANCE: (SIB) at η = ∅ is the root read's
cross-cluster product … the root product's citation authority is the Montes-L1
cite (D4R0K O4's scope note) … the clause stays under the (SIB) tag." deps: Defs.
sketch: specialize o := none. RECORD (do not encode): JOINT-D1 is single-cluster
EVIDENCE, not the theorem — the root clause carries NO separate hypothesis; it
rides the same `hsib` tag (the rev-6 Fable repair, 9196–9201). hypothesis_fields:
`h : SibCount T χ`.

### Layer E — TREE-EXP: the first-split recursion (§T.4) [13 units]

**T-E1 `MovesT.jcRoot_partition` · `E1_jcRootPart.lean` · easy**
```lean
theorem jcRoot_partition (χ : Fin n → Fin m) :
    (Set.univ : Set (Box p m)) = ⋃ g : Fin n → ZMod p, rootCell χ g ∧
    Pairwise (Function.onFun Disjoint (rootCell χ))
```
moves_ref: 7464–7466 "(JC-root) PROVED, unconditional: … the level-0 cells
partition the box." deps: Defs. sketch: cells are fibers of x ↦ x ∘ χ; fibers of a
function partition. hypothesis_fields: none.

**T-E2 `MovesT.jcRoot_card` · `E2_jcRootCard.lean` · easy**
```lean
theorem jcRoot_card (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (g : Fin n → ZMod p) :
    Nat.card ↥(rootCell χ g) * p ^ n = p ^ m
```
moves_ref: 7464–7468 "ONE digit layer, the n coefficient digits pinned: jvol =
p^{−n} exactly … (The degree-1 Hensel tree … now has μ(fiber) = p^{−1} —
pass-1 finding 8's base case, formerly an empty product = 1.)" deps: Defs.
sketch: coordinate-splitting equivalence (MovesC C4's `putOn` idiom): pin n of m
coordinates, count the rest. The degree-1 base case (n = 1) is this statement at
n = 1 — record in docstring. hypothesis_fields: none.

**T-E3 `MovesT.jc_single` · `E3_jcSingle.lean` · medium**
```lean
theorem jc_single (Sigma : Locus p m) (fd : FreshData p m)
    (hfree : ∀ cl ∈ fd.clauses, ∀ c ∈ cl.support, Sigma.pinned c = false) :
    Nat.card {x : Box p m // Sigma.IsSolution x ∧ fd.sat x} * p ^ fd.mstar
      = Sigma.mass
```
moves_ref: 7469–7472 "(JC-single) PROVED (= C.1.5(1) verbatim): at a site whose
window hull has ONE side, the joint cell IS a single §C read stratum with its
values: jvol(c_s │ Σ) = vol_nom(E_fresh(ν_s))." deps: MovesC.C4_conditionalMass.
sketch: this IS `C4_conditionalMass` re-exported at MovesT's site typing — the
unit's work is the SITE-CELL BRIDGE: `SiteCell` at a one-side site is a
{IsSolution ∧ fd.sat} event (definitional unfold at the jet's transported system).
difficulty: medium. hypothesis_fields: the jet carrying the site's system (HC-2
face); no new strength — the note marks this clause PROVED via C.1.5(1) and the
Lean C.1.5(1) is BUILT (MovesC).

**T-E4 `MovesT.jcMulti_def_and_branching` · `E4_jcMultiBranch.lean` · medium**
```lean
def JCmulti (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
  ∀ (o : Option (History p F)) (Σc cell : Set (Box p m)) (k : ℕ) (sides : Fin k → …),
    2 ≤ k → IsMultiSideSite T o cell sides →
    Nat.card ↥(cell ∩ Σc) * p ^ (∑ j, freshExp (sides j)) = Nat.card ↥Σc

theorem jcMulti_branching (T …) (CA : CellAssign …) (o cell sides …)
    (h : IsMultiSideSite T o cell sides) (hk : 2 ≤ k) :
    2 ≤ (CA.branchSetOf …).card
```
moves_ref: 7473–7483 "(JC-multi) OPEN, displayed … the CLAIMED mass is the side
product … an OPEN obligation on this note's record, census-untested … A multi-side
site is always a BRANCHING site (k sides ⟹ ≥ k branches), so unbranched segments
never consume (JC-multi)." deps: Defs, §2.9. sketch: the DEF is the unit's main
deliverable (the open obligation TYPED, side product form); the theorem is the
displayed k-sides⟹branching consequence — each side contributes ≥ 1 eligible
factor to the branch set (via CellAssign's read-off). difficulty: medium.
hypothesis_fields: `JCmulti` itself is NEVER proved — hypothesis `hjcm` downstream.

**T-E5 `MovesT.fiber_root_split` · `E5_rootSplit.lean` · hard**
```lean
theorem fiber_root_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (hsib : SibCount T χ) (g : Fin n → ZMod p) (htracks : RootSplitData Tr g) :
    Nat.card ↥{x | Tr.fiberAt T χ x} * (Nat.card ↥(rootCell χ g)) ^ (numTracks htracks - 1)
      * p ^ n
      = p ^ m * ∏ i ∈ trackIdx htracks,
          Nat.card ↥(rootCell χ g ∩ trackEvent Tr T χ i)
```
[`RootSplitData` := the root reduction g with its track decomposition of Tr (each
track's subtree; τ-hen tracks are leaf factors 1 — they constrain only through g);
E-phase fixes the exact packaging.] moves_ref: 7485–7495 "ROOT CLAUSE: μ(fiber T) =
jvol({f̄ = g}) · ∏_{tracks i} μ(S_{T_i} │ the reduction cell) = p^{−n} ·
∏_i μ(S_{T_i} │ Σ_0) — the level-0 cells partition ((JC-root)), and the cross-track
factorization is (SIB) at η = ∅." deps: T-E1, T-E2, T-S1/T-S3. sketch: fiberAt
decomposes as (x ∈ rootCell χ g) ∧ ⋂ tracks' continuation events ∧ hen payload
(determined by g); apply SibCount at o = none over the track branch set; multiply
by T-E2's root charge. The LEDGER CHECK (7491–7495: F1's 14-pin split
5^{−4}·5^{−10}) is the Gates layer's job (T-G1's toy analogue). difficulty: hard.
hypothesis_fields: `hsib` (SIB — OPEN); the Montes-L1 root authority is the SAME
tag (T-S3's record).

**T-E6 `MovesT.fiber_seg_step` · `E6_segStep.lean` · medium**
```lean
theorem fiber_seg_step (T : TreeModel p F n N m pol) (H : History p F)
    (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root)
    (hone : OneSideSite T (some H) …) (E : Set (Box p m)) …:
    Nat.card ↥{x | T.mem (some (H.snoc ν hν)) x ∧ x ∈ E} * p ^ freshExp ν
      = Nat.card ↥{x | T.mem (some H) x ∧ x ∈ E}
```
moves_ref: 7496–7499 "UNBRANCHED SEGMENT: along a maximal single-branch run, each
site is one-side/one-factor, so (JC-single) applies: C.1.5(1)+(2) multiply the
running mass by jvol(c_s │ Σ) = vol_nom(E_fresh(ν_s)) at each site." deps: T-E3,
MovesD (TreeModel.mem_snoc). sketch: mem_snoc splits the event; the child clause
at a one-side site is T-E3's conditional count with mstar = freshExp ν; E rides as
a spectator (locality: E must be a below-site event — E-phase adds the standard
level-separation premise). difficulty: medium. hypothesis_fields: the site's jet
(as T-E3).

**T-E7 `MovesT.fiber_first_split` · `E7_firstSplit.lean` · hard**
```lean
theorem fiber_first_split (Tr …) (T …) (χ …) (hsib : SibCount T χ)
    (hjcm : JCmulti T χ) (c : SplitSiteData Tr) :
    Nat.card ↥(fiber Tr ∩ Σ_{<c}) * (Nat.card ↥(Σc c)) ^ (numChildren c - 1)
      * p ^ (jointExp c)
      = Nat.card ↥(Σ_{<c}) ^ ? * ∏ j ∈ children c, Nat.card ↥(Σc c ∩ childEvent j)
```
[E-phase settles the exact division-free exponent bookkeeping; the CONTENT is
pinned: charge jvol(c │ Σ) — "the FORMERLY MISSING FACTOR, now explicit" — via
(JC-single) or (JC-multi), then (SIB) at c over the member-indexed children;
τ-halted children are leaf factors 1.] moves_ref: 7503–7515 "FIRST SPLIT: …
Charge jvol(c │ Σ) — … supplied by (JC-single) or (JC-multi) — then by (SIB) at c
… μ(fiber T │ Σ) = jvol(c │ Σ) · ∏_{j=1}^m μ( S_{T_j} │ Σ_c )." deps: T-E3, T-E4,
T-S1. sketch: split fiber at the first branching site; one jvol charge (E3 or the
hjcm hypothesis by side count); SibCount over the branch set; child factors are
ContFiber events. The REL.2 identification of children as smaller-degree theory
(7511–7513) is NOT consumed — the Lean recursion is on node count alone (the note's
own well-foundedness display (a), 7529–7530). difficulty: hard. hypothesis_fields:
`hsib`, `hjcm` (at multi-side sites only — single-side sites never touch hjcm).

**T-E8 `MovesT.treeExp` · `E8_treeExp.lean` · hard**
```lean
theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (hsib : SibCount T χ) (hjcm : JCmulti T χ)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)   -- ALL leaves (τ-irr)/(τ-hen)
    (hsites : SiteLedger Tr T χ) :             -- per-site jvol data (jets)
    Nat.card ↥{x | Tr.fiberAt T χ x} * p ^ (n + ∑ s ∈ windowSites Tr, siteExp s)
      = p ^ m
```
moves_ref: 7449–7456 "(TREE-EXP) μ{ f : T_can^τ(f) = T } = ∏_{read sites s of T}
jvol(c_s │ Σ_{<s}), every site charged exactly once — the ROOT INCLUDED"; the (NS)
clause 7457–7461 is EXCLUDED BY `hdet` ("the product formula is NOT asserted for
such T" — T-C8 owns those trees). deps: T-E5, T-E6, T-E7, T-E2. sketch: strong
induction on Tr.chains' card (hfin) via the first-split decomposition: root clause
(E5), unbranched runs (E6), terminal leaves (factor 1 — the verdict is cell data of
the last site, TB-CAP exhibits the class: T-C1/T-C2), first split (E7). Every site
in exactly one recursion frame ⇒ the exponent sum charges each site once.
difficulty: hard (the corpus centerpiece). hypothesis_fields: `hsib` (SIB),
`hjcm` (JC-multi, multi-side sites only), `hsites` (the per-site jet/system ledger
— HC-2's presented faces), `hdet` (the (ns) exclusion, BY TYPE).

**T-E9 `MovesT.tree_fiber_disjoint` · `E9_fiberDisjoint.lean` · medium**
```lean
theorem tree_fiber_disjoint (Tr Tr' : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m)
    (h : Tr.fiberAt T χ x) (h' : Tr'.fiberAt T χ x) :
    Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
    ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H)
```
moves_ref: 7025–7029 "The tree FIBERS … are pairwise DISJOINT — one f, ONE tree:
T_can^τ is a function (L2 + VP-2's τ a function of cell data) … a genuine PARTITION
of the decided set, in exact contrast to the shape events S(P̂,⊤)" (the
multiplicity-weighted COVER, MovesD L6). deps: Defs. sketch: fiberAt clause (i) is
a graph equality — both chain sets equal the pruned set of x (Set.ext); clauses
(ii)/(iii) pin henV/leafV/nsLeaf from x's data. difficulty: medium.
hypothesis_fields: none — this is the CHOICE-FREENESS payoff, unconditional.

**T-E10 `MovesT.perShape_law` · `E10_perShape.lean` · hard**
```lean
theorem perShape_law (T̂ : TreeShape n) (T : TreeModel p F n N m pol) …
    (hsib : SibCount T χ) (hjcm : JCmulti T χ) (hsites : …) :
    (∑ᶠ Tr : {Tr : VTree p F // TreeShapeOf Tr = T̂ ∧ realizes …},
      Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x}) * p ^ (Ashape T̂)
      = CofShape T̂ * p ^ m
```
[`TreeShape`/`TreeShapeOf` := chains projected through `shapeOfH` with the tree
structure retained; `Ashape T̂` := n + Σ window-site shape exponents;
`CofShape T̂` := Nat.card of the realized value-trees of shape T̂ — E-phase fixes
the finite enumeration via MovesD's PrefIdx machinery per chain.] moves_ref:
7537–7545 "Each site's jvol is shape-determined … Σ_{T of shape T̂} μ(fiber T) =
C_T̂(p) · p^{−A(T̂)}, with NO multiplicity weights — the tree fibers are genuinely
disjoint." deps: T-E8, T-E9, T-V8, MovesD (shape exponents). sketch: sum T-E8's
constant over the shape's value-trees (D10's sum-the-constant idiom); disjointness
never needed for the SUM (same as D10: "NO disjointness consumed") but IS the
no-multiplicity-weights content — cite T-E9 in the docstring. MULTINOMIAL SCOPE
(7548–7557): the m!/(∏ mⱼ!) factorization is NOT claimed — per-node exchangeability
is [1v]'s burden; record verbatim in the docstring. difficulty: hard.
hypothesis_fields: `hsib`, `hjcm`, `hsites` (inherited from T-E8).

**T-E11 `MovesT.treeN` · `E11_treeN.lean` · hard**
```lean
theorem treeN (Tr : VTree p F) … (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hthr : Tr.thr n ≤ N) (hsib : SibCount T χ) (hjcm : JCmulti T χ) (hsites : …) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr
      = p ^ (n * N)
```
moves_ref: 7559–7574 "TREE-N (finite-level stability …): … for every N ≥ thr(T):
#{ f mod p^N : T_can^τ(f) = T } = p^{nN} · μ(fiber T) — the fiber is a FINITE
intersection of finite-level digit-cell conditions … hence an exact union of
level-N residue classes." deps: T-E8, T-C1, T-C2, T-V8 (thr via shapeOfH), MovesD
D4R4all (exact level realization). sketch: T-E8 gives the exponent identity at the
working level; thr joins the branch thresholds (MovesD), the leaf caps (T-C1/T-C2),
and the site levels — above it every condition is an exact residue-class union, so
the count is level-stable. X.3-FREE (7047–7048); GIVEN (SIB) + (JC-multi at
multi-side sites) "for the mass value" (7576–7577). difficulty: hard.
hypothesis_fields: `hsib`, `hjcm`, `hsites`, `hdet` (verbatim: TREE-N "holds
VERBATIM for trees ALL of whose leaves are (τ-irr)/(τ-hen)", 7241–7243).

**T-E12 `MovesT.treeN_ns` · `E12_treeNns.lean` · medium**
```lean
theorem treeN_ns (Tr : VTree p F) … (H : History p F)
    (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) (…C7/C8 inputs…) :
    Filter.Tendsto (fun N => (Nat.card ↥(fiberTrunc Tr N) : ℝ) / (p : ℝ) ^ (n * N))
      Filter.atTop (nhds 0)
```
moves_ref: 7574–7576 "For (ns)-leaf trees the identity is REPLACED by the
NORMALIZED capped bound of §T.2 (p^{−nN}·count ≤ μ(lump ∩ …) → 0; the raw count
need NOT tend to 0)." deps: T-C7, T-C8. sketch: T-C8's inclusion + T-C7's vanishing
ratio; squeeze. difficulty: medium. hypothesis_fields: T-C7's (jet family, lump
identification).

**T-E13 `MovesT.tgt_finadd` · `E13_tgtFinAdd.lean` · easy**
```lean
theorem tgt_finadd (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol) (χ : _)
    (hd : ∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, Tr ≠ Tr' → Disjoint {x | fiberAt …} {x | fiberAt …}) :
    Nat.card ↥(⋃ Tr ∈ 𝒯, {x | Tr.fiberAt T χ x})
      = ∑ Tr ∈ 𝒯, Nat.card ↥{x | Tr.fiberAt T χ x}
```
moves_ref: 7017–7030 (TGT)'s regrouping license at finite level ("The series is
positive and ≤ 1; all regroupings … licit (Tonelli)" — at finite level: finite
additivity over the disjoint fibers). The DENSITY form stays X.3-tagged and
UNSTATED (§0). deps: T-E9. sketch: Nat.card of finite disjoint unions; hd from
T-E9 pointwise. hypothesis_fields: none.

### Layer F — ONE-F: the once-per-f normalization [4 units]

**T-F1 `MovesT.oneF` · `F1_oneF.lean` · easy**
```lean
theorem oneF (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃! TrE : VTreeExt p F, TrE.val.fiberAt T χ x
```
[`VTreeExt` := VTree quotiented/bundled to extensional equality of (chains, henV,
leafV, nsLeaf) — T-E9's tuple; E-phase picks bundling vs Setoid.] moves_ref:
7579–7589 "(ONE-F) Σ_{T̂} 1_{shape(T_can^τ(f)) = T̂} = 1 — immediate from totality +
choice-freeness … f HAS exactly one tree, the tree exactly one shape … No
reciprocal/Möbius weights w(f, η) exist or are needed." INDEPENDENT of TREE-EXP
(7580–7581: "it neither uses nor certifies the recursion"). deps: T-E9. sketch:
existence = Decided's witness; uniqueness = T-E9. NOTE the independence: no hsib,
no hjcm — totality + choice-freeness alone. hypothesis_fields: none.

**T-F2 `MovesT.preHalt_dict_ptwise` · `F2_dictPtwise.lean` · hard**
```lean
theorem preHalt_dict_ptwise {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (Tr : VTree p F) (x : Box p m) (hfib : Tr.fiberAt T χ x) :
    Nat.card {i : PrefIdx n pol P //
        x ∈ S.fiber i ∧ PreHaltPfx T (reprOf i) x}
      = Tr.chainCount n P
```
moves_ref: 7590–7603 "THE DICTIONARY …, RESTRICTED TO PRE-HALT MARKS: … Pref^τ(P̂)
:= the pre-halt members of Pref(P̂) is shape/value-computable. Then, on the decided
set …: Σ_{η ∈ Pref^τ(P̂)} μ(S(η,⊤)) = Σ_T (# length-ℓ chains of T of shape P̂) ·
μ{f : T_can^τ(f) = T}." deps: Defs §2.8, MovesD (D4R_CYL, ClassFiberWelldef pinned
Props — consumed AS HYPOTHESES exactly as MovesD's D15 was specced), T-E9. sketch:
hcyl converts "x ∈ S.fiber i" to "reprOf i ∈ T_can(x)"; PreHaltPfx cuts to the
pruned tree = Tr.chains (fiberAt clause (i)); the count bijection i ↦ its chain,
injective by hwd + PresentNorm uniqueness (class ↔ chain). difficulty: hard.
hypothesis_fields: `hcyl : D4R_CYL S T`, `hwd : ClassFiberWelldef …` — the W4-3
pins, HERE consumed; their PROOF for the canonical model is T-D5/T-D6.

**T-F3 `MovesT.preHalt_dict_sum` · `F3_dictSum.lean` · medium**
```lean
theorem preHalt_dict_sum {P : Shape n} (S : …) (T : …) (χ : …) (hcyl …) (hwd …)
    (𝒯 : Finset (VTree p F)) (hpart : PartitionsDecided 𝒯 T χ) :
    ∑ᶠ i : PrefIdx n pol P, Nat.card ↥{x | x ∈ S.fiber i ∧ PreHaltPfx T (reprOf i) x}
      = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x}
```
moves_ref: 7601–7606 "the PRE-HALT marked total is the pruned-tree-fiber sum
weighted by PER-TREE mark counts; it exceeds the event mass exactly where mult > 1
(D4R.1-EV)." deps: T-F2, T-E13, T-F1. sketch: double count {(i, x)} both ways
(Finset.sum exchange); per-x the inner count is T-F2's identity at x's unique tree
(T-F1). difficulty: medium. hypothesis_fields: hcyl/hwd (via T-F2); `hpart` (the
finite family covering the decided slice under count — at fixed level, the decided
set IS a finite union; E-phase derives it from T-E11's stability or takes the
finite-level slice as the summation domain).

**T-F4 `MovesT.belowHalt_excess` · `F4_belowHalt.lean` · easy**
```lean
theorem belowHalt_excess {P : Shape n} (S : Presented p F n N m pol P) (T : …) (χ …)
    (x : Box p m) :
    Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ PreHaltPfx T (reprOf i) x}
      ≤ S.mult x
```
moves_ref: 7606–7611 "The unrestricted total … is ≥ this, with excess exactly the
below-halt marks — §D4-R bookkeeping that NO consumer may convert to a per-f
quantity without first restricting to Pref^τ. Conversion then runs through
TREE-EXP's fiber expansion ONLY." deps: Defs, MovesD (Presented.mult). sketch:
subtype inclusion; `Nat.card` monotone. THE FENCE rides in the docstring: the
conversion ban (the pass-8 critical-1 channel, closed by display).
hypothesis_fields: none.

### Layer D — the seam-discharge units [13 units]

**T-D1 `MovesT.eligibleT_apparatus` · `D1_eligible.lean` · medium**
Deliverable: the `CellAssign` structure + `eligibleT` def (§2.9 — already in Defs;
this unit proves the two coherence lemmas):
```lean
theorem eligibleT_iff_child (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) (hmem : T.mem o x) : T.child o ν x ↔ eligibleT T CA o ν x
theorem eligibleT_cell_data (T …) (CA …) (o ν x x')
    (h : CA.cellOf o x = CA.cellOf o x') : eligibleT T CA o ν x ↔ eligibleT T CA o ν x'
```
moves_ref: MovesD §2.5 W4-1(c) "`eligible` becomes a DEFINED predicate over MovesT's
cell/branch-set vocabulary (T_can^τ, VP's (c2)); `child_iff` then a THEOREM-
obligation of HC-2" + §T.1 (c1) 7093–7100 (verdicts/branches attach at the two cell
levels). deps: Defs §2.9. sketch: first lemma = `CA.child_cell` verbatim (the
re-keyed `child_iff`, DISCHARGED against any CellAssign; producing a CellAssign for
the canonical model is HC-2's — see §5 W4-1); second is cellOf-factoring, one line.
difficulty: medium. hypothesis_fields: `CA` (the cell assignment — its canonical
instance is HC-2's SideReads surface, fenced through §6 Q1/Q2).

**T-D2 `MovesT.eligible_nonvacuity` · `D2_eligGate.lean` · medium**
```lean
theorem eligible_nonvacuity : ∃ (T : TreeModel …toy…) (CA : CellAssign …)
    (o ν x), eligibleT T CA o ν x ∧ ¬ (∀ ν' x', ¬ eligibleT T CA o ν' x')
    ∧ RejectsRootOnlyChildless T CA
```
[`RejectsRootOnlyChildless` := on the toy realizable input, the root-only childless
tree FAILS `fiberAt` — the W4-1 tie-demand union's named vacuity.] moves_ref:
MovesD §2.5 W4-1(b) "NO `eligible := child` vacuity (Codex#7 c.5 — the root-only
childless tree must not satisfy the law for realizable inputs); eligibility is CELL
data, never f-data (L5)." deps: T-D1, Gates layer toy model. sketch: the toy model
(T-G1) has a realized child; decide. difficulty: medium. hypothesis_fields: none
(concrete instance).

**T-D3 `MovesT.verdictModel_inst` · `D3_verdictModel.lean` · hard**
```lean
noncomputable def vModelOf (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (hdi : BranchDichotomy T) (…caps…) :
    VerdictModelT T   -- MovesT's REBUILT structure, see below
```
THE RE-KEY (W4-2(c): "the whole structure is re-derived from §T-ASSEMBLY's
VP-1/VP-2 + TB-CAP; MovesD's form is the negotiating position, not the buildable
spec"): `VerdictModelT` is DECLARED IN THIS CORPUS with the frozen rev-8 fields
EXCEPT: (i) `V := VdAt n` (concrete, T-V7's finiteness; hVne by `⟨henVerdict n …⟩`;
NO degenerate singleton — VP-1's alphabet); (ii) `vdict := tauVdict` DEFINED (the
τ emission: some (irrVerdictOf H) on IrrHalts, some (ns value) on NsHalts, none
else); (iii) `halt_iff` PROVED from T-V5/T-V6 (GIVEN hdi); (iv) the WITHDRAWN
`cell_local` is REPLACED by `CellAssign.cell_local` at the PER-STATE level
`cellLevel o` — the both-directions fix: no cap-envelope over-factoring (kernel-(b)
cells keyed to their OWN level, not the verdict cap), no `Cell := Box` degeneracy
(hCellFin + a proper `cellLevel < N` premise); (v) `cap`/`cap_law` per clause from
TB-CAP: cap(hen) = 1 (T-C1), cap(irr v) = the leaf's NPband datum (T-C2), NO cap
field for ns — the ns clause enters `vdict` only through `NsHalts`, and its classes
are NEVER claimed cylindrical (§0 refutation record; the rev-8 uniform cap_law is
NOT reproduced for ns — this is the ADMITTED amendment, MovesD §2.5 W4-2(b)(ii)).
moves_ref: MovesD §2.5 W4-2 entire; §T.1 (c1)/(c2) 7093–7120; §T.2 per-clause
statuses. deps: T-V5, T-V6, T-V7, T-C1, T-C2, T-C3, Defs §2.9. sketch: assemble;
every field either defined, proved from the layer-V/C units, or an explicit
structure PARAMETER (the caps' shape-data functions). difficulty: hard
(pre-approved split: D3a the structure + vdict/halt_iff; D3b the cap fields).
hypothesis_fields: `hdi` (KB-TOT), `CA`, the per-leaf cap data (T-C2's Presented
faces). NON-DEGENERACY GATE: T-G1's toy instantiates vModelOf and `decide`s a
non-constant vdict — the W4-2(b)(i) demand made a build-time check.

**T-D4 `MovesT.cellLevel_local` · `D4_cellLevel.lean` · medium**
```lean
theorem cellLevel_local_sound (T …) (CA : CellAssign …) (o : Option (History p F))
    (hlev : CA.cellLevel o = siteLevel o)   -- the site's OWN B(iii) level
    (x x' : Box p m) (hagree : ∀ c, CA.levelOf c < siteLevel o → x c = x' c) :
    CA.cellOf o x = CA.cellOf o x'
```
+ the FALSIFIER: the cap-envelope version (rev-8 `cell_local`) FAILS on a two-level
toy where the cell datum reads a coordinate above the verdict cap:
`theorem capEnvelope_cellLocal_false : ∃ …, ¬ CapEnvelopeCellLocal …`.
moves_ref: MovesD §2.5 W4-2(b)(ii) "rev 8's `cell_local` SILENTLY STRENGTHENS: L5's
full polygon/digit outcome cell is kernel-(b) data and is NOT determined by the
verdict-cap prefix (kernel-(c)) — … the correct strength is the owner's
(§T-ASSEMBLY/MovesT) to fix." deps: Defs §2.9, Gates toy. sketch: soundness is
CA.cell_local rewritten; the falsifier is a 2-coordinate decide witness — the
(b)/(c) conflation exhibited, closing the Codex#7 c.6 demand BOTH directions.
difficulty: medium. hypothesis_fields: none.

**T-D5 `MovesT.d4rcyl_canonical` · `D5_d4rcyl.lean` · medium**
```lean
theorem d4rcyl_canonical {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol)
    (hkey : ∀ (H : History p F) (hH : H ∈ PrefSet n pol P) (x : Box p m),
      (∀ J : JetSetup H n N m, x ∈ J.SHZ (topLocus p m)) ↔ T.mem (some H) x) :
    D4R_CYL S T
```
moves_ref: MovesD's pinned Prop docstring "S(η,⊤) = {f : η ∈ T_can(f)} … Lean proof
EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus" + W4-3(c) "D4R_CYL … become[s a]
wave-4 THEOREM over the MovesT tree." deps: MovesD.Defs (D4R_CYL, Presented.fiber),
HC-2 (the hypothesis's discharge). sketch: unfold D4R_CYL; at i, apply hkey at
reprOf i (∈ PrefSet by choice-spec); the ∀-J face needs jet-independence of the
locus — supplied INSIDE hkey's ∀-J quantifier (deliberately: the hypothesis is the
HONEST HC-2 surface — per-history run-key faithfulness, RUN-KEY in §0). difficulty:
medium. hypothesis_fields: `hkey` (RUN-KEY — HC-2's ReadsOf↔locus bridge at finite
level; owner HC-2, fenced through Q1/Q2 for the steep legs, §6).

**T-D6 `MovesT.cfw_canonical` · `D6_cfw.lean` · hard**
```lean
theorem cfw_canonical {P : Shape n}
    (T : TreeModel p F n N m pol)
    (hkey : … as T-D5 …)
    (heta : ∀ H H', H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' →
      ∀ x, T.mem (some H) x ↔ T.mem (some H') x) :
    ClassFiberWelldef p F n N m pol P
```
moves_ref: MovesD ClassFiberWelldef docstring "one η-class, one classifier locus,
over ALL representatives and ALL jets (§C L4's semantic content). Deferred to the
wave-4/HC-2 tree corpus together with D4R_CYL" + W4-3(c). deps: MovesD.Defs, T-D5's
hkey. sketch: J.SHZ ⊤ = tree membership (hkey both ways) and tree membership is
η-class-invariant (heta) ⇒ loci equal. `heta` is the ETA-LOC face (§0): the tree
reads only cell data, and equal η-data means equal cell reads — its discharge is
HC-2's PresentNorm/Galois content, NOT provable here (honestly a hypothesis).
difficulty: hard (the bridge plumbing around JetSetup binders). hypothesis_fields:
`hkey` (RUN-KEY), `heta` (ETA-LOC) — both owner HC-2, both named in §0.

**T-D7 `MovesT.np_id` · `D7_npid.lean` · hard [pre-approved split D7a/D7b]**
```lean
theorem np_id {P : Shape n} (S : Presented p F n N m pol P) (i : PrefIdx n pol P)
    (J : JetSetup (reprOf i) n N m) (hJ : J = S.jet i) :
    (transportedLevels J (topLocus p m)) = bandLevels (P : ShapePrefix) n
```
[`transportedLevels` := the level set of J's pinned equations at Z = ⊤;
`bandLevels` := the levels below NPband where `bandS` fires — E-phase types both
Finsets against MovesC's `totalPins` support and MovesD's `bandS`.] moves_ref:
MovesD §2.5 W4-4(a) "every transported-system equation level is a band level and
conversely (the §C C.2 cutoff of each η equals NPband)"; (c) "NP-ID becomes a
wave-4 theorem from mstar_eq + fresh_band/fresh_cover + D8/D4b over the
MovesT-presented classes." deps: MovesD.D8_bandShape, MovesD.D4b_chartCount,
MovesC (mstar/fresh apparatus), T-V8. sketch: D7a (⊆): every pinned equation sits
in a fresh band at its read (fresh_band/mstar_eq); D7b (⊇): every band level is hit
by a pinned equation (fresh_cover + D8's band shape). Until proved, MovesD's
D4R4_all keeps its conditionality pointer (their manifest row) — landing this unit
DELETES that pointer. difficulty: hard. hypothesis_fields: `S.jet` (presented
family).

**T-D8 `MovesT.vtree_pathOrder` · `D8_pathOrder.lean` · medium**
```lean
theorem vtree_pathOrder (Tr : VTree p F) :
    IsPartialOrder … (fun H H' => H.IsPrefixOf H') ∧
    ∀ H₁ H₂ H, H₁ ∈ Tr.chains → H₂ ∈ Tr.chains → H ∈ Tr.chains →
      H₁.IsPrefixOf H → H₂.IsPrefixOf H → (H₁.IsPrefixOf H₂ ∨ H₂.IsPrefixOf H₁)
```
moves_ref: MovesS §W4-SYNC TreeIface's ROOT-PATH ORDER LAWS (path_refl/trans/
antisymm/total: "ancestors of a node are comparable"). deps: Defs §2.5. sketch:
list-prefix order facts (`List.IsPrefix` refl/trans/antisymm; two prefixes of one
list are comparable — Mathlib `List.IsPrefix` lemmas). This makes `VTree` a lawful
TreeIface CARRIER; the entrance/deep-split/blockOf semantics are [1v]/MovesV
vocabulary and stay THERE (§5 S-5). difficulty: medium. hypothesis_fields: none.

**T-D9 `MovesT.shape_countable` · `D9_shapeCtbl.lean` · easy**
```lean
instance : Countable ShapePrefix
instance (n : ℕ) : Countable (Shape n)
```
moves_ref: (infrastructure for S-7's `ctbl` demand — TREE-N fibers countably
indexed.) deps: MovesD.Defs. sketch: `ShapeRead` is a finite tuple of
ℕ/ℤ/ℚ/Bool/Finset ℕ data (all countable) + Props; lists of countables countable;
subtype inherits. hypothesis_fields: none.

**T-D10 `MovesT.classTree_countable` · `D10_classTreeCtbl.lean` · medium**
```lean
def ClassTree (n : ℕ) (pol : CanonPolicy p F) : Type _ := …
  -- finite prefix-closed trees whose chains are (P, i : PrefIdx n pol P) class
  -- addresses with leaf verdicts in VdAt-slices
instance : Countable (ClassTree n pol)
```
moves_ref: MovesS §W4-SYNC S-7 "`Fib` must MAP to canonical-tree fibers (TREE-N's
complete finite subtrees; disjointness; the ONE-F partition) … `ctbl`." deps: T-D9,
T-V7, MovesD (PrefIdx finiteness via the E-layer encodings). sketch: a ClassTree is
a finite set of class addresses; countable-of-finite fibers over countable Shape
lists; PrefIdx finiteness from MovesD's E9/E10 encoding bound. difficulty: medium.
hypothesis_fields: none.

**T-D11 `MovesT.fibOf_keying` · `D11_fibOf.lean` · medium**
```lean
noncomputable def fibOf (ct : ClassTree n pol) : VTree p F := …  -- reprOf per chain
theorem fibOf_fiber_disjoint … -- distinct ClassTrees, disjoint fibers (via T-E9 +
theorem fibOf_partition …      -- ClassFiberWelldef), and the ONE-F partition face
```
moves_ref: S-7's keying demand (fibOf : Fib → Tree; "βmeas = 0 must not trivialize
(fiber nonemptiness where βmeas > 0)" — the nonemptiness face is MovesS's
consumption, stated there; here the map + disjointness + partition). deps: T-D10,
T-E9, T-F1, T-D6. sketch: chains := reprOf-images; disjointness from T-E9 once
class-distinctness gives tree-distinctness (hwd/ClassFiberWelldef — T-D6's
hypothesis chain rides). difficulty: medium. hypothesis_fields: `hwd` (via T-D6's
conclusion or directly as the MovesD pinned Prop).

**T-D12 `MovesT.packages_rekey` · `D12_packages.lean` · easy**
```lean
def rs1GivenOfMovesT (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    RS1GivenPackageValues := {
  tree_exp_fin := ∀ Tr …, (T-E8's statement) ,
  tree_exp_ns  := ∀ Tr …, (T-E12's statement) ,
  tree_n       := ∀ Tr …, (T-E11's statement) ,
  one_f        := ∀ x …, (T-F1's statement) ,
  sib          := SibCount T χ ,
  tb_cap       := (T-C1 ∧ T-C2 statements) ∧ NsAmendedPair … ,
  vp           := VPPinned T … ,   -- (c1)/(c2)/(c3-a) discharged + VP-SOUND's two
                                   -- cites as the REMAINDER (7634–7635)
  pci          := PCI }
def xrbOfMovesT … : XRBPackageValues := { sib := SibCount T χ,
  jc_multi := JCmulti T χ, tb_cap := …, vp := …, ns_null := (T-C7's statement), … }
```
moves_ref: MovesS §W4-SYNC S-9 "every abstract Prop field in XRBPackage/
RS1GivenPackage/Wsh17Package is a NAME AWAITING RE-KEYING — the contract's whole
point" + the [3t] owner tags on tree_exp_*/tree_n/one_f/sib/tb_cap/vp/pci/ns_null/
jc_multi. deps: all layer statements (as PROPS — the field values quote statements,
they do not require the proofs). sketch: definitional record; the [2b]/[2r]/[1v]
fields (xhd_*, jc_inv, rel2_*) are NOT touched — they keep their owner tags
(MovesV/MovesR territory). Also supplies Wsh17Package.sib_count := (SIB)'s COUNT
face across shallow splits — literally `SibCount` restricted to depth-0/shallow
sites. difficulty: easy. hypothesis_fields: none (defs of Props).

**T-D13 `MovesT.treeIface_carrier` · `D13_ifaceGate.lean` · medium [PARTIAL — see §5 S-11]**
```lean
noncomputable def treeIfaceCore (𝒯 : Finset (VTree p F)) (h𝒯 : 𝒯.Nonempty) :
    TreeIfaceCore …  -- Tree := ↥𝒯, Node := chains+root, onPath := prefix order,
                     -- order laws := T-D8; finN from hfin; node_ne from root
```
moves_ref: MovesS §W4-SYNC S-11 "`n2_treeiface` (ex-U-29d6): the gate's TreeIface
instance + W7 check, built when TreeIface is re-keyed." deps: T-D8. sketch: pack
the carrier + order laws. HONEST SCOPE: `isEntrance`/`isDeepSplit`/`blockOf`/
`entδ`/`shapeOf`-into-F.Sh are CTS/[1v] vocabulary — MovesV's; this unit delivers
the CARRIER CORE only, and S-11's full instance waits on MovesV (recorded at §5).
difficulty: medium. hypothesis_fields: none.

### Layer G — sealed-number gates (the T-n3 discipline at Lean scale) [2 units]

**T-G1 `MovesT.toy_treeExp_gate` · `G1_toyGate.lean` · medium**
```lean
def toyModel : TreeModel 2 (ZMod 2) … := …   -- a 2-adic, ≤ 8-coordinate box model
theorem toy_gate : (Nat.card ↥{x | toyTree.fiberAt toyModel toyχ x}) * 2 ^ toyA
    = 2 ^ toyM := by decide
theorem toy_sib : SibCount toyModel toyχ := by decide   -- (provable ON THE TOY)
theorem toy_vdict_nonconstant : ∃ x y, toyVdict x ≠ toyVdict y := by decide
```
moves_ref: §T.6's gate DISCIPLINE (the F1/T-n3 integers 7516–7528 are p = 5 census
scale — out of `decide` range; the Fable-confirm's own p = 2 census "N(fiber) = 8 =
2^{9−6}, 0/10,000 stability" (9208–9209) is the Lean-scale target: the toy encodes
a 2-adic depth-1 split with the SAME ledger shape). deps: Defs, T-E8's statement
(gate checks the STATEMENT's instance, not via the theorem). sketch: hand-build a
tiny TreeModel with 2 children + explicit fibers; decide the count identity, the
Sib instance, the vdict non-constancy (T-D3's gate). PASS ≠ closing (SIB) — scope
recorded verbatim (7699–7700). difficulty: medium. hypothesis_fields: none.

**T-G2 `MovesT.toy_oneF_gate` · `G2_toyOneF.lean` · easy**
```lean
theorem toy_oneF : ∀ x, ToyDecided x → ∃! t ∈ toyTrees, toyFiber t x := by decide
```
moves_ref: T-n3 Layer C's ONE-F face 7745–7752 ("marked 64 / per-f 58 / gap 6" at
census scale; the Lean toy checks the ∃!-partition shape + a below-halt excess
instance > 0, so the dictionary gap is EXHIBITED, not just typed). deps: T-G1 defs.
sketch: decide. hypothesis_fields: none.

---

## §4 THE Q-FENCE — Q1/Q2 discharge DESIGN (fenced on Asvin's sign-off; task #44)

PROJECT_STATE 28j's queue items Q1/Q2 touch the FROZEN MovesC interface, so per the
statement fence NOTHING here builds until the sign-off. This section is the DESIGN
the charge asked for — what MovesT's vocabulary does for them, written so the
post-sign-off build is mechanical.

**Q1 — the HistoryCoherent child re-key at the regraded value + the 2-node ReadsOf
gate (the V10 inconsistency finding: the `e·g ≥ 2` steep-read legs of the K1 kernel
are vacuous-by-inconsistency under the current child keying).**
DESIGN: MovesT's `CellAssign.child_cell` (§2.9) is written against `T.child`, NOT
against `HistoryCoherent`'s child clause — so the corpus is INSENSITIVE to the
re-key's exact constant: when HistoryCoherent's child keying moves to the regraded
value, only HC-2's CellAssign INSTANCE changes; every MovesT unit (T-D1…T-D6, the
E-layer) is stated over the abstract CA and survives verbatim. The 2-NODE READSOF
GATE becomes, in this vocabulary, a Layer-G unit spec (pre-written, NOT built):
`G3_q1Gate.lean` — a two-node history (root + one steep e·g ≥ 2 read) with a
concrete box member, `decide`-checking `T.mem (some H₂) x` through the re-keyed
instance — the non-vacuity witness for the steep leg that V10 showed is currently
inconsistent. FENCE: G3 is in the manifest as `status: "fenced-Q1"`; building it
before the sign-off is a statement-fence event.

**Q2 — U21's RunVertexPin (the D.7(v)-warranted `child_dig_frame` pin).**
DESIGN: `eligibleT`'s semantic content enters through `CA.branchSetOf ∘ CA.cellOf`;
the vertex pin is exactly the clause that makes `cellOf`'s digit frame at a child
read WELL-DEFINED (which frame the recorded digit tuple is read in). MovesT
reserves the NAMED conjunct slot: `CellAssign` gains (post-sign-off) a field
`vertex_pin : ∀ o ν x, …` transcribing D.7(v)'s warrant (the HC-1 V10/V9 kernel
family is PROVED — the pin's mathematical content is machine-checked; what awaits
sign-off is its INTERFACE placement on the frozen MovesC types). Until then:
`CellAssign` as in §2.9 (no vertex field), and HC-2's canonical instance carries
the pin internally — no MovesT statement names it. FENCE: adding the field is
additive but touches the negotiating position — flagged `fenced-Q2` in the
manifest, sign-off required.

---

## §5 SEAM-DISCHARGE — every consumed contract entry → its discharging unit

**(A) MovesD blueprint §2.5 (the §W4-SYNC contract, 4 entries):**

| entry | tie-demand honored | discharging unit(s) | residual owner |
|---|---|---|---|
| **W4-1** TreeModel `eligible`/`child_iff` | eligible = DEFINED over cell/branch-set vocabulary; CELL data never f-data; no `eligible := child` vacuity | Defs §2.9 (`CellAssign`, `eligibleT`) + T-D1 (`child_iff` re-key against CA) + T-D2 (vacuity gate) | the CANONICAL CellAssign instance = HC-2's SideReads surface (Wall A); steep legs fenced Q1/Q2 (§4) |
| **W4-2** VerdictModel ENTIRE, both directions | (i) no degenerate satisfiability: V := VdAt n concrete + T-G1's non-constant-vdict gate; (ii) no over-factoring: `cell_local` REBUILT at the per-state `cellLevel` (T-D4 sound + falsifier); cross-level cap uniformity typed per clause from TB-CAP (hen = 1, irr = per-leaf NPband; NO ns cap — the refutation record) | T-D3 (`vModelOf`) + T-D4 + T-V5/V6/V7 + T-C1/C2 | `hdi` (KB-TOT, HC-2/D4R0K); the ns clause stays cap-FREE by design |
| **W4-3** D15's `D4R_CYL` + `ClassFiberWelldef` | become wave-4 theorems over the MovesT tree | T-D5 (`d4rcyl_canonical`) + T-D6 (`cfw_canonical`); consumed downstream by T-F2/F3 (the dictionary) and T-D11 | hypotheses RUN-KEY + ETA-LOC, owner HC-2 (§0); MovesD's D15 builds once HC-2 lands them |
| **W4-4** NP-ID | named typed pin → theorem from mstar_eq + fresh_band/fresh_cover + D8/D4b | T-D7 (`np_id`, split D7a/D7b) | none new; landing deletes D4R4_all's conditionality pointer |

**(B) MovesS blueprint §W4-SYNC (11 entries + the 2 ratification addenda):**

| entry | MovesT's deliverable | discharging unit(s) | stays with owner |
|---|---|---|---|
| **S-1** W1_RS1SH (+S-1e, S-1m) | the [3t] premise row's REAL statements (tree_exp_fin/ns, tree_n, one_f, sib, tb_cap, vp, pci) | T-D12 (`rs1GivenOfMovesT` — field values := the layer-E/F/C/S statements) | the RS.1-SH/equates/marked CONCLUSIONS and their derivation: MovesS wave 5 |
| — **addendum (W1 circularity)** | the fix is STRUCTURAL here: MovesT exports TREE-EXP/TREE-N/ONE-F as separate theorems (T-E8/E11/F1), so MovesS's re-key can DERIVE RS.1-SH from the tree assembly instead of restating it — the derivation inputs now exist as named non-circular statements | T-E8, T-E11, T-F1 + T-D12 | the derivation itself: MovesS |
| — **addendum (W1m nine-input ledger)** | the [3t] premises W1m must carry are typed by T-D12's record; the nine-input LedgerIV itself is MovesS's real object | T-D12 | MovesS carries all nine as typed premises at its re-key |
| **S-2** W2_xrb | [3t] fields of XRBPackage re-keyed: sib/jc_multi/tb_cap/vp/ns_null := MovesT statements | T-D12 (`xrbOfMovesT`) | xhd_* / jc_inv ([2b], MovesV), rel2_* ([2r]) |
| **S-3** W3_recursion | consumes S-1/S-2's re-keyed fields; MovesT adds nothing beyond them | T-D12 | the recursion equality: MovesS |
| **S-4** W4_x3 | NOTHING (consumed-item pin, [5]'s package) — recorded: MovesT is X.3-free (§0) | — | [5]/MovesX |
| **S-5** W7_cutWD + TreeIface | the CARRIER: VTree + prefix order laws (refl/trans/antisymm/total = "ancestors comparable") | T-D8, T-D13 | isEntrance/isDeepSplit/blockOf/entδ/σ₀-feed: CTS/[1v] vocabulary → MovesV |
| **S-6** W8_bdy + ReadLedger | the per-entered-path READ list exists as a VTree chain with its site exponents (SiteLedger) — the `charge` carrier | Defs §2.5 (sites/siteExp) | the W/β charge SPLIT (fe, the entrance split): MovesV/[1v] |
| **S-7** W10_convergence + FiberIface | fibOf keying to TREE-N fibers; countability; disjointness; the ONE-F partition | T-D9, T-D10, T-D11 (+T-E9, T-F1) | fibMass/βmeas HasSum: MovesS consuming T-E11 |
| **S-8** W17ii + Wsh17Package | the `sib_count` face := (SIB)'s COUNT face across shallow splits = `SibCount` at depth-0/shallow sites | T-D12 (+T-S3's root form) | c15_volumes (§C/MovesC cite), cts_counts ([1v]/MovesV), the menu-nonemptiness premise |
| **S-9** packages-as-registries | every [3t]-owned Prop field now has a REAL named statement to point at | T-D12 | non-[3t] fields keep their owner tags |
| **S-10** RS4Chain provenance | the DISCHARGE provenance objects exist: TREE-EXP (T-E8), ONE-F (T-F1); device instances replaceable by production statements | T-E8, T-F1 | CUT-WD leg → MovesV (S-5 residual); the actual field re-keying: MovesS |
| **S-11** n2_treeiface | the carrier-core instance constructor | T-D13 | the FULL gate instance (entrance semantics + W7 check): after MovesV re-keys TreeIface |

**(C) HC-2 Wall A / Wall B seam notes:**

| seam note | MovesT's side | unit(s) |
|---|---|---|
| **Wall A** (engine → History; `ReadsOf` is "deliberately the SAME semantic surface as MovesD's W4-1 `eligible`"; "HC-2 owns the definition; MovesT re-keys `eligible` to it in wave 4") | re-key EXECUTED at the interface level: `eligibleT` is defined over `CellAssign`, and the reconciliation obligation is pinned as: HC-2's canonical CellAssign has `branchSetOf (cellOf o x)` = the per-read SideReads clause bundle (incl. clause (vi)'s vertex read-off — the HC2 §7.6 note "the wave-4 reconciliation copies clause (vi) into the re-key") | Defs §2.9 + T-D1; the instance: HC-2 (fenced Q1/Q2, §4) |
| **Wall B** (SEED-EXIST / PresentSeed — HC-1's graded hypothesis) | NOT MovesT's to discharge (recorded so nobody silently widens scope — the HC2 blueprint's own "NOT HC-2's to deliver" list assigns the MovesT tree corpus ONLY the D4R_CYL side, handled at W4-3). MovesT consumes Presented/jets ONLY as hypothesis fields (`S.jet`, `hsites`), exactly MovesD's pattern | riders on T-C2/C6/C7, T-E3/E6/E8/E10/E11, T-D7 |

**(D) PROJECT_STATE 28j queue:**

| item | disposition |
|---|---|
| **Q1** HistoryCoherent child re-key + 2-node ReadsOf gate | discharge DESIGNED at §4 (CA-abstraction makes MovesT re-key-invariant; gate spec G3 pre-written, `fenced-Q1`) — NOT BUILT pending sign-off |
| **Q2** RunVertexPin (child_dig_frame) | discharge DESIGNED at §4 (named additive `vertex_pin` field slot on CellAssign, `fenced-Q2`) — NOT BUILT pending sign-off |

COUNT: 4 (MovesD) + 11 + 2 addenda (MovesS) + 2 (HC-2 walls) + 2 (Q1/Q2) = **19
distinct seam entries mapped** (the addenda are handled inside S-1's row but are
counted, per the wave-4 charge, as their own ratification demands).

---

## §6 Process, census, and honest perimeter

BUILD ORDER (hardest-hole-first inside each phase; E-phase = statements compile
with sorry bodies, then the prover fleet):
1. `Defs.lean` (§2) — then T-G1's toy SKELETON immediately (the day-one non-vacuity
   gate: if `fiberAt`/`SibCount` over-strengthen, the toy dies first — the U31
   lesson from HC-2 rev 2).
2. Layer V + T-E1/E2/E9 + T-F1 (the unconditional core: the pin, the partition).
3. Layer C (T-C5 first — the one substantive new proof; its failure mode feeds
   back into the Defs of `IsLumpLocus`).
4. Layer E (E3 → E6 → E5/E7 → E8 → E10/E11) + F2–F4.
5. Layer D (D1/D2/D4/D8/D9/D10/D12 early — they unblock other corpora's wave-5
   work; D3/D5/D6/D7/D11/D13 after their deps).
6. Gates T-G1/T-G2 full; §4's G3 stays fenced.

CENSUS TARGETS: 51 units = 12 easy / 29 medium / 10 hard (hard: T-C5, T-E5, T-E7,
T-E8, T-E10, T-E11, T-F2, T-D3, T-D6, T-D7 — escalation-risk set pre-declared;
pre-approved splits: C5a/C5b, D3a/D3b, D7a/D7b). Zero axioms; zero `sorry` in the
accepted scope; every hypothesis field named in §0 or §5. `#print axioms` per
proved unit = Lean core only.

WHAT THIS CORPUS DOES **NOT** CLAIM (the note's §T.5/§T.0, restated as the
manifest's honesty block):
* no (SIB) proof, no (SIB-STEP)⟹(SIB) filtration lemma (open remainder, wave 5+);
* no (JC-multi) proof (open, census-untested);
* no X.3/density form — finite/normalized counts only;
* no VP-SOUND discharge — (HEN-LIFT)/(OM-SAT) stay named Props (D4R.0-K(c)'s
  remainder = exactly {VP-SOUND's cites}, 7634–7635);
* no TB-CAP for (ns) — refuted; only (ns-lump)+(ns-null) as displayed;
* no termination, no exhaustion, no rationality (7663);
* no marked→per-f conversion outside TREE-EXP (T-F4's fence);
* no multinomial factorization of C_T̂ (exchangeability is [1v]'s burden).

AUDIT CHARGE for the wave-4 pass (per campaign §3): faithfulness of every
`statement` against the quoted rev-7 display; non-vacuity (each hypothesis Prop
must be falsifiable — T-S2/T-D4's falsifiers are the in-corpus witnesses; the toy
gate is the day-one instance); quantifier exactness (esp. TB-CAP(irr)'s
per-realized-leaf scope 7183–7187 — NO cap uniform over all cells may appear; and
SIBLING INDEXING — no ordering/symmetry factor in any product); hypothesis-field
completeness against §0's ledger.

