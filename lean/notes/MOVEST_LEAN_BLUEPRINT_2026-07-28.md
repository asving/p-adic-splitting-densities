# MovesT LEAN BLUEPRINT (2026-07-28) — §T-ASSEMBLY: the branch-to-tree mass assembly — **REV 2**

CORPUS: `lean/LeanUrat/MovesT/` (namespace `LeanUrat.MovesT`). WAVE 4.
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` §T-ASSEMBLY, **rev 7** (body lines
6970–7761, repairs in place), DUAL-ACCEPTED 2026-07-27 (Codex pass 8 = 0/0
`TASM_PASS8_2026-07-27.md` + Fable confirm 0/0 `FABLE_CONFIRM_TASM_REV7_2026-07-27.md`
on identical text; acceptance record MOVES 9215–9227). A Lean statement is faithful
iff it says what a rev-7 display says (campaign §0).

REV RECORD: **rev 1 was DUAL-REJECTED** — Codex 35 crit / 10 gap
(`MOVEST_AUDIT_CODEX_2026-07-28.md`) + Fable 5 crit / 8 gap
(`MOVEST_AUDIT_FABLE_2026-07-28.md`), both recommending a full rev 2. THIS REVISION
repairs the UNION of both verdicts; the finding-by-finding disposition table is §7.
The two structural changes every reader should load first:
 (i) **the conditioning event is now PINNED** — `SibCount` and the joint-cell law
   are typed on the note's cell event Σ_c (the `CellAssign` fiber), never on an
   arbitrary subset (Fable CRIT-1/CRIT-2, computationally refuted at the F1 cell);
 (ii) **§5 is now an ACCOUNTING, not a claim** — every seam row states what MovesT
   proves (statement = the contracted obligation over consumed corpus objects),
   what is REDUCED to a named typed bridge Prop, and what stays with its owner BY
   THE CONTRACT'S OWN TEXT; the headline count is corrected (19 seam entries + 2
   fenced queue designs = 21 rows; rev 1 miscounted 19 = 4+11+2+2+2 — Codex 35,
   Fable GAP-1).

CONSUMES (all built, sorry-free cores):
* `LeanUrat.MovesD` — `Box`, `topLocus`, `ShapeRead`/`ShapePrefix`/`ShapeWF`/`Shape`,
  `CanonPolicy`, `PrefSet`/`PrefIdx`/`reprOf`, `Presented` (`fiber`/`event`/`mult`),
  `Threshold`, `TreeModel` (STRUCTURAL fields only: mem/child/root_mem/mem_single/
  mem_snoc/mem_realizable), the pinned Props `D4R_CYL`, `ClassFiberWelldef`,
  `History.snoc`/`History.IsPrefixOf`, the mass laws (D10 `D4R1_SUM` style:
  division-free `Nat.card · * p^A = p^(nN)` identities), SW1 `ShapeWF_of_matches`,
  the D4R.4/L12 threshold apparatus (`Nshape`, `NPband`, `Shape.NP`, D4R4all).
* `LeanUrat.MovesSp` — `Species`, `StageLaws`, `Coherent` (G1–G6), `CatalogueWord`
  (confirming-letter convention W = 1), `CanTreeModel` (typing only).
* `LeanUrat.MovesC` — `History`/`Node`/`JetSetup`/`Locus`/`AdmissibleZ`/`SHZ`/
  `totalPins`/`boxMass`; `C4_conditionalMass` (the single-step conditional count law,
  signature `Nat.card {x // Sigma.IsSolution x ∧ fd.sat x} * p ^ fd.mstar =
  Sigma.mass`), `C6_thmC_b` (Theorem C(b)), `HistoryCoherent`, `Realizable`, `InBox`.

FORMAT: campaign master plan §2 unit specs (id/file/statement/moves_ref/deps/sketch/
difficulty/hypothesis_fields). DOCTRINE carried (campaign ledger, wave-3+ prompts): a
faithful interface must be FALSE for instances the note would reject; obligations may
be open, but their TYPES must pin their content; hypotheses neither weakened nor
silently strengthened. REV-2 ADDITION (the CRIT-1/CRIT-2 lesson): a hypothesis Prop
whose conditioning event is a FREE variable is silently strengthened into
unsatisfiability — every conditional law below names its conditioning event as a
DEFINED object (cell event / state event), never a bare `Set` binder.

---

## §0 Conditionality ledger — the note's §T.5 perimeter, typed

Every entry below is a NAMED HYPOTHESIS (ours ⇒ never an axiom, campaign §4). Each
rides as an explicit premise/field on exactly the units listed; no unit consumes one
silently, none is strengthened.

| name | note display | Lean form | status / rider sites |
|---|---|---|---|
| **(SIB)** | §T.3 display 7292 (quoted verbatim at §2.6): μ(⋂ Sj │ Σ_c) = ∏ μ(Sj │ Σ_c), Σ_c THE cell event; COUNT FACE 7293–7295 | `SibCount T CA` (Defs §2.6) — the count face AT THE CELL EVENTS of the cell assignment (rev 2: Σc is no longer a free `Set` binder — Fable CRIT-1) | OPEN KERNEL (CL-10; gate 32/32 = support not closure). Hypothesis `hsib` on T-E5/E7/E8/E10/E11 (+ reshapes T-S1/S3) |
| **(SIB-STEP)** | 7382–7388 stacked-vector form | `SibStep` (Defs §2.6), def only, typed over `JointStage` | OPEN; the (SIB-STEP)⟹(SIB) filtration lemma (7388–7391) is a recorded wave-5 obligation, NOT a unit (the note itself lists it inside the open kernel, §T.5(1)) |
| **(JC-multi)** | 7473–7483: multi-side joint cell = side product, priced AT THE ENTRANCE STATE | `JCmultiAt T CA o c ss` (Defs §2.5) — PER-SITE, tied to the site's cell/state events (rev 2: Fable CRIT-2) | OPEN, census-untested; hypothesis `hjcm` quantified over the TREE'S OWN multi-side sites ONLY (rev 2: Codex 12–13 — single-side trees consume nothing) on T-E7/E8/E10/E11 |
| **(HEN-LIFT)** | 7254–7261 declared statement | `HenLift` (Defs §2.7, now fully typed) | VP-SOUND citation obligation; discharge should PREFER Mathlib's Hensel (campaign §4) — until then a hypothesis field, never consumed by a mass unit |
| **(OM-SAT)** | 7262–7273 declared statement | `OmSat` (Defs §2.7, typed over a named factor-assignment carrier) | VP-SOUND citation obligation (GMN/Montes cite; axiomatization would need the faithfulness-entry process). Hypothesis field only |
| **X.3 / CL-4** | 7041–7048: density form of (TGT) only | NOT typed here | this corpus states ONLY finite/normalized-count forms (TREE-EXP/TREE-N are X.3-FREE, 7046–7048); no unit consumes X.3 |
| **XRB, [2r] REL.2(a)/(b)/(d), PCI** | §T.5(5) 7644–7652; PCI 7406–7413 | `PCI` typed (Defs §2.6); REL.2 legs stay owner-tagged Prop PARAMETERS in the §5 packages | proved nowhere here (the note: "this note states the interface and proves nothing about it") |
| **KB-TOT** | (c2) covering 7112–7119 consumes Theorem B totality (D4R.0-K(a)+(b), note-DISCHARGED) | `BranchDichotomy` (Defs §2.4) — REV 2: restated as the per-child SATURATE-OR-CONTINUE law (μ=1 halt vs μ≥2 realized continuation), no longer the classical branch-set tautology (Codex 1/8) | Lean owner HC-2/D4R0K; hypothesis `hdi` on T-V6, T-D3 |
| **RUN-KEY** | the HC-2 bridge surface: per-history jet-locus ↔ tree membership, per jet | `RunKey T P` — NAMED typed Prop (Defs §2.9; rev 2: no longer an inline unnamed premise, and the ∀-jet quantifier sits OUTSIDE the iff — Fable CRIT-4/Codex 22) | hypothesis on T-D5/T-D6; owner HC-2 |
| **ETA-LOC** | tree membership is η-class data (§C L4 semantic content) | `EtaLoc T P` — NAMED typed Prop (Defs §2.9) | hypothesis on T-D6, T-F2 (rev 2: Fable GAP-5); owner HC-2 |
| **CHAIN-LOC / InBox** | realized chains carry in-box reads (the L3 setting) | `InBoxOfMem T n` (Defs §2.9) | hypothesis on T-F2 (rev 2: Fable GAP-5); owner HC-2 |
| **B(iii) lump tie** | 7203–7209: no side at every height ⟺ vanishing at all heights | `NsLumpFamily.tie` (Defs §2.5a) — rev 2: the family's defining fields are DISPLAYED so T-C3 is non-circular (Codex 38) | field on T-C3/C7/E12; owner D4R0K Theorem B(iii), standing perimeter |
| **Node-data lawfulness** | realizable reads have e,g,μ ≥ 1, K-card a p-power (L3/§B2-DEF ledger data) | `NodeDataLawful` (Defs §2.2) — REV 2: replaces `HistoryCoherent` as T-V8's premise; carries NO child-keying clause, hence Q1-INSENSITIVE (Codex 9's fence violation removed) | hypothesis on T-V8; owner HC-2 (implied by `HistoryCoherent` off the steep legs today, on all legs post-Q1) |
| **Q1/Q2 fence** | PROJECT_STATE 28j queue | §4 | DESIGNED here, NOT BUILT until Asvin's sign-off (task #44). NO unit premises `HistoryCoherent` any more (rev 2) |

Two REFUTATION RECORDS carried from the note (never re-claim):
* TB-CAP(ns) **literal duty FAILS** (7189–7202): the (τ-ns) class is a pro-cylinder,
  at NO finite cap a finite cylinder union. The corpus encodes ONLY the amendment
  pair (ns-lump)+(ns-null); no unit states a cap for (ns); TREE-N's hypothesis
  excludes (ns) leaves by type (T-E11's `hdet`).
* Raw-count limit **FALSE** (7237–7240): only NORMALIZED (ns) bounds are stated
  (T-C8, T-E12); no unit claims the raw count tends to 0.

THREE REV-2 IN-CORPUS REFUTATION RECORDS (the audit round's computational finds,
carried so the E-phase never regresses):
* rev 1's `SibCount` (free Σc) is FALSE for every intended model — at the note's own
  F1 cell, Σc := (S₁ Δ S₂) ∩ cell gives 0 ≠ 62,500² (Fable CRIT-1). The rev-2 form
  pins Σc := the cell event.
* rev 1's `JCmulti` (free Σc) is unsatisfiable at any multi-side site with positive
  fresh exponent (Σc := {x₀} gives p^E = 1 — Fable CRIT-2). The rev-2 form prices
  the cell event against the entrance state event.
* rev 1's T-E5 exponent `numTracks − 1` fails the note's committed integers
  (5^{10} = 5^{28} at F1; 64 = 4096 at the p=2 census — Fable CRIT-3). The rev-2
  exponent is `numTracks`.

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
`MANIFEST.json` ("deviations"), exactly as in MovesD. REV-2 RULE (Codex 37): every
load-bearing definition is DISPLAYED IN FULL below; `…` survives only inside
E-phase plumbing notes (Finset coercions, snoc-proof arguments), never as the body
of a consumed definition.

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

### 2.2 accumulated invariants, the τ-irr firing datum, node-data lawfulness

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

/-- REV 2 (Codex 9, the Q1-fence repair): the per-node lawfulness the verdict layer
actually consumes — each read has e, g, μ ≥ 1 and its K-carrier card a p-power.
STRICTLY WEAKER than `HistoryCoherent`: NO child-keying clause, so it is Q1-INSENSITIVE
(the steep-leg inconsistency V10 found lives in the child-keying clause, which nothing
in this corpus premises any more). `HistoryCoherent` implies it wherever both are
stated; its own discharge is HC-2's node-ledger content. -/
def NodeDataLawful (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) : Prop :=
  ∀ ν ∈ H.nodes, 1 ≤ ν.e ∧ 1 ≤ ν.g ∧ 1 ≤ ν.μ ∧
    Nat.card ↥ν.σ.K = p ^ ((Nat.card ↥ν.σ.K).factorization p)

/-- the (τ-irr) leaf's verdict — total via junk 1s off the lawful domain. REV 2
(Codex 4): the guards are no longer merely ASSERTED inactive — T-V8's `acc_pos`
conjunct PROVES `max (accE H) 1 = accE H ∧ max (accF H) 1 = accF H` under
`NodeDataLawful`, a statement-surface fact consumers can discharge. -/
noncomputable def irrVerdictOf (H : History p F) : Vd :=
  irrVerdict (max (accE H) 1) (max (accF H) 1) (le_max_right _ _) (le_max_right _ _)

/-- REV 2 (Codex 3): the (τ-ns) leaf's verdict VALUE — v = μ·{(E(Φ̂), F(Φ̂))} (7083):
μ is the LAST read's multiplicity (the (z-3) exact key power Φ̂^μ), and (E(Φ̂), F(Φ̂))
are the key's accumulated invariants — the key's own chain is H's read chain, so
E(Φ̂) = accE H, F(Φ̂) = accF H. [E-phase: if D4R0K's (z-3) accessor for μ differs
from `getLast?.μ`, the deviation goes to MANIFEST with the (z-3) cite.] -/
noncomputable def nsVerdictOf (H : History p F) : Vd :=
  nsVerdict ((H.nodes.getLast?).elim 1 fun ν => ν.μ)
    (max (accE H) 1) (max (accF H) 1) (le_max_right _ _) (le_max_right _ _)
```

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
note-DISCHARGED, consumed by (c2)'s covering 7112–7119). REV 2 (Codex 1/8): rev 1's
form was the classical tautology `∃ child ∨ ∀ ν ¬child`; the ACTUAL content of the
covering display is PER-CHILD: "each branch of the branch set then either saturates
(μ = 1: τ-irr halt) or has μ ≥ 2 and CONTINUES, the continuation existing by L1
totality" (7114–7118). That is what is typed: every realized child either saturates
(its extension IrrHalts) or is a realized continuation — a law a degenerate model
can FAIL (a model with a realized μ ≥ 2 child and no realized extension violates
it; a model with a μ = 1 child whose extension does not IrrHalt violates it). The
branch-set dichotomy itself (some child ∨ no child = τ-ns) is classical and carries
no content — recorded, not typed. Lean owner: HC-2/D4R0K. -/
def BranchDichotomy (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    ∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      (ν.μ = 1 ∧ IrrHalts (H.snoc ν hν)) ∨
      (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)
-- [`NodeExtends H ν` := the snoc side condition MovesC's `History.snoc` carries
--  (well-formed extension datum); E-phase binds it to the actual snoc signature.]

/-- τ-PRUNED membership: H ∈ T_can^τ(x) — realized, and NO proper NONEMPTY prefix
τ-halts ("The engine's below-halt continuations exist syntactically but are NOT
walked", 7086–7088). REV 2 (Codex 2): the `H'.nodes ≠ []` guard is now IN the
quantifier — rev 1 let the EMPTY prefix carry an arbitrary `NsHalts` value at the
junk state `some ⟨[]⟩` and prune every nonempty history. (τ-hen) never applies to
chains (its domain is level-0 tracks, 7069); the root state is `none`, never
`some ⟨[]⟩`. -/
def PrunedMem (T : TreeModel p F n N m pol) (H : History p F) (x : Box p m) : Prop :=
  T.mem (some H) x ∧
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H → H'.nodes ≠ [] →
    ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x
```

### 2.5 finite pruned trees, fibers, sites, the site vocabulary, thresholds

REV 2: this section now DEFINES the entire site-exponent family rev 1 left undefined
(`stateEvent`/`cellEvent`, `SitePresents`, `SpectatorFor`, `SideSplit`+`sideExp`,
`IsMultiSideSite`, `JCmultiAt`, `SiteLedger`+`siteExp`+`freshCoords`, `windowSites`,
`AofTr`, `siteLevel`) — Fable GAP-2 (seam row S-6 promised them), Codex 42. Rev 1's
bare name `freshExp` is SUBSUMED: per-side exponents are `SideSplit.sideExp`,
per-site exponents are `SiteLedger.siteExp` (rename recorded in §7).

```lean
/-- maximality in a chain set (leaf = no strict extension present).
[REV 2, Fable GAP-8(iv): declared BEFORE `VTree`, which uses it.] -/
def IsMaximalIn (S : Set (History p F)) (H : History p F) : Prop :=
  ∀ H' ∈ S, H.IsPrefixOf H' → H' = H

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
  hns_leaf : ∀ H, nsLeaf H → H ∈ chains ∧ IsMaximalIn chains H

/-- typemult(T) := ⊎_{leaves ℓ} v(ℓ) ⊎ henV (7024–7025). REV 2 (Codex 37): full body
— non-leaves contribute 0 through `leafV`'s `none`. -/
noncomputable def VTree.typemult (Tr : VTree p F) : Multiset (ℕ × ℕ) :=
  (Tr.henV.map Subtype.val).sum
    + ∑ H ∈ Tr.hfin.toFinset, ((Tr.leafV H).elim 0 Subtype.val)

/-- THE TREE FIBER {x : T_can^τ(x) = T}, graph-equality form — "one f, ONE tree"
(7025–7029): (i) chains are EXACTLY the pruned realized prefixes; (ii) every leaf
τ-halts at x with the RECORDED VERDICT VALUE — REV 2 (Codex 3): the (ns) leaf's
value is now PINNED to `nsVerdictOf` (the note's v = μ·{(E(Φ̂),F(Φ̂))}, 7083), so
two trees differing only in an ns-leaf verdict can no longer fiber the same x
(this restores T-E9/T-F1 — Codex 14/15); (iii) the hen payload matches x's root
datum; (iv) non-leaves do not halt. -/
def VTree.fiberAt (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  (∀ H : History p F, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)) ∧
  (∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →
    ((IrrHalts H ∧ ¬ Tr.nsLeaf H ∧ Tr.leafV H = some (irrVerdictOf H)) ∨
     (NsHalts T (some H) x ∧ ¬ IrrHalts H ∧ Tr.nsLeaf H ∧
       Tr.leafV H = some (nsVerdictOf H)))) ∧
  Tr.henV = henPayload χ x ∧
  (∀ H ∈ Tr.chains, ¬ IsMaximalIn Tr.chains H →
    ¬ IrrHalts H ∧ ¬ NsHalts T (some H) x)

/-- DECIDED at x := some complete finite tree fibers x — (TGT)'s decided set, the
domain ONE-F partitions (7580, 7586–7589). The undecided complement is [5]'s (X.3);
NOT priced here. -/
def Decided (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  ∃ Tr : VTree p F, Tr.fiberAt T χ x

/-- READ SITES of T (7441–7448): the root site plus every chain of T. -/
def VTree.sites (Tr : VTree p F) : Set (Option (History p F)) :=
  insert none (some '' Tr.chains)

/-- the WINDOW sites (every site but the root); TREE-EXP's exponent sum runs here,
the root's charge is the fixed n ((JC-root)). -/
def VTree.windowSites (Tr : VTree p F) : Set (Option (History p F)) :=
  some '' Tr.chains

/-- the STATE EVENT of a site — the event that x realizes the site's entrance state.
At the root this is the ambient box (`TreeModel.root_mem` makes it `univ`). Replaces
rev 1's `SiteCell` (same values, one uniform definition). -/
def stateEvent (T : TreeModel p F n N m pol) (o : Option (History p F)) :
    Set (Box p m) := {x | T.mem o x}
```

[Design note, load-bearing, carried from rev 1: TREE-EXP is stated DIVISION-FREE in
the D10 house style — "jvol(c_s │ Σ) = p^{−k_s}" becomes
`Nat.card ↥(cell ∩ Σ) * p ^ k_s = Nat.card ↥Σ`, and the site product becomes one
exponent sum. No ℚ, no measure API; the profinite μ statements of the note are
consumed at their finite-level faces, which is what the note's own TREE-N/count
displays provide (7568–7574).]

```lean
/-- REV 2 (Fable GAP-8/Codex 41): the jet-site tie, NAMED — the site's cell event IS
the transported system's stratum. This is the bridge T-E3's rev-1 sketch promised but
kept out of the statement; it is now a hypothesis object the statements consume.
Owner of instances: HC-2 (the presented faces). -/
def SitePresents (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m) : Prop :=
  cellEvent T CA o c = {x | Sigma.IsSolution x ∧ fd.sat x}
  ∧ stateEvent T o = {x | Sigma.IsSolution x}

/-- REV 2 (Fable GAP-3/Codex 43): the level-separation premise for spectator events,
EXPLICIT — E is invariant under changes of the given (fresh) coordinates. -/
def SpectatorFor (fresh : Finset (Fin m)) (E : Set (Box p m)) : Prop :=
  ∀ x x' : Box p m, (∀ i : Fin m, i ∉ fresh → x i = x' i) → (x ∈ E ↔ x' ∈ E)

/-- REV 2 (Codex 42/Fable GAP-2): the SIDE DECOMPOSITION of a cell's branch set —
the window polygon's sides, each carrying ≥ 1 eligible branch, with per-side fresh
exponents (E_fresh of the side's system). Cell data. -/
structure SideSplit (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (c : CA.Cell) where
  k : ℕ
  sideOf : Node p F → Fin k
  side_ne : ∀ j : Fin k, ∃ ν ∈ CA.branchSetOf c, sideOf ν = j
  sideExp : Fin k → ℕ

/-- a MULTI-SIDE site: its window hull has ≥ 2 sides (7473–7483). -/
def IsMultiSideSite (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (c : CA.Cell) (ss : SideSplit T CA c) : Prop := 2 ≤ ss.k

/-- **(JC-multi), PER-SITE — REV 2 (Fable CRIT-2 + Codex 12–13).** The note's display
7473–7483 prices the joint cell AT THE ENTRANCE STATE: "the CLAIMED mass is the side
product jvol(c_s │ Σ) = ∏_{sides} vol_nom(E_fresh(ν_side))". Division-free, with the
cell event and state event as the DEFINED conditioning objects (no free `Set`
binder): the cell's count times p^(side-exponent sum) recovers the state's count.
OPEN obligation (census-untested); NEVER proved here. -/
def JCmultiAt (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) (ss : SideSplit T CA c) : Prop :=
  Nat.card ↥(cellEvent T CA o c) * p ^ (∑ j : Fin ss.k, ss.sideExp j)
    = Nat.card ↥(stateEvent T o)

/-- the per-site B(iii)/Scale level (T-D4's `hlev`, T-E11's threshold joins): level 1
at the root (7564), the shape-side band level at a window site. -/
noncomputable def siteLevel (n : ℕ) : Option (History p F) → ℕ
  | none => 1
  | some H => (shapeOfH H n).NPband n

/-- REV 2 (Fable GAP-2 — seam row S-6's promised deliverable): the SITE LEDGER — the
typed carrier of the per-site jet/system data (HC-2's presented faces). Fields pin
the content: each window site of Tr carries a transported system, the jet-site tie
(`SitePresents`), C4's freeness, and its fresh coordinate support; `siteExp` is
DEFINED from the ledger (the system's mstar), never free data — so the per-site
charge identities are THEOREMS (T-E3/E6 from C4), not ledger axioms. -/
structure SiteLedger (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) where
  sys : History p F → Locus p m × FreshData p m
  cellAt : History p F → CA.Cell            -- the joint cell of the site's last read
  parentSt : History p F → Option (History p F)   -- the entrance state above the read
  hparent : ∀ H ∈ Tr.chains, (parentSt H).elim True
    (fun H' => H'.IsPrefixOf H ∧ H' ≠ H ∧ H' ∈ Tr.chains)
  presents : ∀ H ∈ Tr.chains,
    SitePresents T CA (parentSt H) (cellAt H) (sys H).1 (sys H).2
  free : ∀ H ∈ Tr.chains, ∀ cl ∈ (sys H).2.clauses, ∀ cIdx ∈ cl.support,
    (sys H).1.pinned cIdx = false
  freshCoords : History p F → Finset (Fin m)
  hfresh : ∀ H ∈ Tr.chains, ∀ cl ∈ (sys H).2.clauses, ∀ cIdx ∈ cl.support,
    cIdx ∈ freshCoords H
  hcard : ∀ H ∈ Tr.chains, (freshCoords H).card = (sys H).2.mstar

/-- the per-site fresh exponent, off the ledger. -/
def SiteLedger.siteExp {Tr : VTree p F} {T : TreeModel p F n N m pol}
    {CA : CellAssign p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F) : ℕ := (L.sys H).2.mstar

/-- A(T) as an exponent (T-E11's `AofTr`, now DEFINED — Fable GAP-2): the root's n
plus the window sites' fresh exponents (7540: "A(T̂) := n + Σ_{window sites} A(s)"). -/
noncomputable def AofTr (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellAssign p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) : ℕ :=
  n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H

/-- thr(T) (7562–7566), full body (REV 2, Codex 37): the join over T's chains of the
§D4-R L12/D4R.4 thresholds N(η,⊤) (`Nshape` of the chain's shape — a LEAF chain
includes its halting read, so the leaf caps N(η′,⊤) of TB-CAP(irr) are the same
join), with the joint-cell levels (`siteLevel`: B(iii) heights → base levels via
C.1.5's Scale, all shape data), and 1 (the root's level). -/
noncomputable def VTree.thr (Tr : VTree p F) (n : ℕ) : ℕ :=
  Tr.hfin.toFinset.sup
    (fun H => (shapeOfH H n).Nshape ⊔ siteLevel n (some H)) ⊔ 1

/-- the retained ShapeRead of a node (the L3 dictionary, node → shape side),
componentwise: species/e/h/g/μ/a/s0/wSide/Dwidth/ustar/gam copy ν's like-named
fields; `w := (Nat.card ↥ν.σ.K).factorization p`;
`monicTop := decide (r = 0 ∧ ν.s0 + ν.wSide = n)`. [REV 2, Codex 37: the mapping is
displayed; the structure-literal field ROSTER is bound at E-phase to
`MovesD.ShapeRead`'s actual field names — any mismatch is a MANIFEST deviation, the
VALUES above are the spec.] -/
noncomputable def readOf (ν : Node p F) (r : ℕ) (n : ℕ) : ShapeRead :=
  { species := ν.species, e := ν.e, h := ν.h, g := ν.g, μ := ν.μ, a := ν.a,
    s0 := ν.s0, wSide := ν.wSide, Dwidth := ν.Dwidth, ustar := ν.ustar,
    gam := ν.gam, w := (Nat.card ↥ν.σ.K).factorization p,
    monicTop := decide (r = 0 ∧ ν.s0 + ν.wSide = n) }

/-- the shape of a history (unit T-V8 proves MatchesHist + ShapeWF via SW1). -/
noncomputable def shapeOfH (H : History p F) (n : ℕ) : ShapePrefix :=
  ⟨(List.range H.nodes.length).map fun r => (H.nodes[r]?).elim default
    (fun ν => readOf ν r n)⟩
```

### 2.5a the (ns) lump family (REV 2, Codex 38/39 — the B(iii) carrier, non-circular)

```lean
/-- the capped lumps L_M of a no-side track, AS DATA WITH THEIR DEFINING SHAPE
(7203–7209, 7216–7224). REV 2: rev 1's `IsNsLumpFamily` was an undisplayed name that
could have assumed T-C3's conclusion; the fields below pin the content so T-C3 can
PROVE antitonicity and the intersection identity: `vanish` says L M is the
digit-vanishing event of the window-interior blocks up to height M in J's chart
((ZC) vocabulary: interior = base index < μ·D, fresh heights F(b) < ht ≤ M);
`tie` is B(iii)'s reading "no side at every height ⟺ vanishing at all heights" —
the standing-perimeter hypothesis (owner D4R0K Theorem B(iii)), carried as a FIELD,
never re-proved. -/
structure NsLumpFamily (T : TreeModel p F n N m pol) {H : History p F}
    (J : JetSetup H n N m) where
  L : ℕ → Set (Box p m)
  vanish : ∀ (M : ℕ) (x : Box p m),
    x ∈ L M ↔ ∀ bl ∈ interiorFreshIdx J M, digitAt x bl = 0
  interior_mono : ∀ M M', M ≤ M' → interiorFreshIdx J M ⊆ interiorFreshIdx J M'
  tie : ∀ x : Box p m, T.mem (some H) x →
    ((∀ ν : Node p F, ¬ T.child (some H) ν x) ↔ ∀ M, x ∈ L M)
-- [`interiorFreshIdx J M : Finset (coordinate index)` and `digitAt` are the jet
--  chart's accessors — E-phase types them against MovesC's (ZC) fields (`floorH`,
--  block base indices, the Scale map); their DEFINING CLAUSES are the display
--  7217–7224 quoted in T-C5. The Finset is what T-C5's `Z_M` pins.]
```

DECLARATION ORDER — NORMATIVE (the §2.x display order is thematic; the FILE hoists):
(1) §2.1–2.4; (2) `readOf`/`shapeOfH` (§2.5 tail); (3) §2.9's `CellAssign`/
`cellEvent`/`eligibleT`/`RootCellsOf` (consumed by §2.5's site vocabulary and §2.6);
(4) the rest of §2.5 + §2.5a; (5) §2.6–2.8; (6) the remainder of §2.9 (VerdictModelT,
RunKey/EtaLoc/InBoxOfMem/WallAReconciled). [Fable GAP-8(iv) generalized: no forward
reference survives in the file.]

### 2.6 (SIB) — the joint sibling kernel, COUNT FACE (hypothesis, NEVER proved here)

The note's display, quoted (7290–7292) — the conditioning event is THE CELL EVENT:

> "Then, conditionally on the cell event Σ_c:
>   (SIB)   μ( ⋂_{j=1}^m S_j │ Σ_c ) = ∏_{j=1}^m μ( S_j │ Σ_c )."

REV 2 (Fable CRIT-1, computationally refuted at F1; Codex 5): rev 1 quantified Σc
over ARBITRARY subsets of the cell — demanding independence after arbitrary further
conditioning, FALSE for every model with one genuine branching cell (F1 witness:
Σc := (S₁ Δ S₂) ∩ cell gives 0 ≠ 62,500²). The rev-2 kernel is typed AT the cell
event of the cell assignment — exactly the display's Σ_c — and the branch set B is
the CELL'S branch set, not a free Finset (Codex 5's second face).

```lean
/-- the event that branch (o, ν)'s continuation realizes the PRESCRIBED finite
subtree — (SIB)'s S_j quantifier ("S_j determined by b_j's own continuation reads",
7287–7290). REV 2 (Codex 37): full body — the rooted analogue of `fiberAt`'s clauses
(i)/(ii)/(iv), root = o·ν; no hen clause (hen is level-0 only, 7069); prefix duties
scoped STRICTLY ABOVE the child root (the entrance state's own realization is the
conditioning event's business). -/
def ContFiber (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (hν : ChildRoot o ν) (Tsub : Set (History p F))
    (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop)
    (x : Box p m) : Prop :=
  (∀ H' : History p F, H' ∈ Tsub ↔
      ((childHist o ν hν).IsPrefixOf H' ∧ T.mem (some H') x ∧
        ∀ H'' : History p F, (childHist o ν hν).IsPrefixOf H'' →
          H''.IsPrefixOf H' → H'' ≠ H' → ¬ IrrHalts H'' ∧ ¬ NsHalts T (some H'') x)) ∧
  (∀ H' ∈ Tsub, IsMaximalIn Tsub H' →
    ((IrrHalts H' ∧ ¬ nsSpec H' ∧ leafSpec H' = some (irrVerdictOf H')) ∨
     (NsHalts T (some H') x ∧ ¬ IrrHalts H' ∧ nsSpec H' ∧
       leafSpec H' = some (nsVerdictOf H')))) ∧
  (∀ H' ∈ Tsub, ¬ IsMaximalIn Tsub H' → ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x)
-- [`ChildRoot o ν` / `childHist o ν hν` := the child history of the site: at
--  o = some H it is `H.snoc ν _`; at o = none it is the one-node history of the
--  track's first window read. E-phase binds the snoc side conditions.]

/-- **(SIB), COUNT FACE, tree-indexed — REV 2.** The display above at finite level
("COUNT FACE (same statement at finite level): the joint fresh-assignment counts
multiply", 7293–7295), SIBLING INDEXING binding (7415–7423: member-indexed Finset =
the cell's own branch set, no ordering, no symmetry factor). A halted child's event
is the SURE event given the cell (7509: "a leaf child has S_{T_j} = the sure event
given c, factor 1") — hence the `∨ S ν = Set.univ` leg. THE CENTRAL HYPOTHESIS of
this corpus: OPEN (CL-10), gate-supported (SIB 32/32, T-n3 21/21), consumed by
TREE-EXP at every branching cell, NEVER proved. The base-changed O_δ reading of each
S_j is [2r] REL.2(a)/(b)/(d)'s identification — cited in the packages (§5 S-9), not
needed to STATE the count face. -/
def SibCount (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T) : Prop :=
  ∀ (o : Option (History p F)) (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T o ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEvent T CA o c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEvent T CA o c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEvent T CA o c ∩ S ν)

/-- (SIB)'s COUNT face ACROSS SHALLOW SPLITS — the Wsh17Package.sib_count field's
value (§5 S-8): the same kernel restricted to root-state sites (o = none). -/
def SibCountShallow (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) : Prop :=
  ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEvent T CA none c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEvent T CA none c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEvent T CA none c ∩ S ν)

/-- (SIB-STEP), stacked-vector form (7382–7388) — def ONLY; its ⟹(SIB) filtration
lemma is the note's own open remainder (§T.5(1)), a wave-5 obligation. REV 2
(Codex 37): typed over an explicit stage carrier. `StageRealized` (the clause that
`past` is a realized-reads event and `nextW` the actual next-fresh-read digit forms
of the active siblings — §C vocabulary) is the ONE deliberately-open carrier Prop
here: consumed by NOTHING in wave 4; its clauses are 7383–7387's and the wave-5
filtration lemma owns its final form. -/
structure JointStage (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) where
  active : Finset (Node p F)
  hactive : active ⊆ CA.branchSetOf c
  past : Set (Box p m)
  hpast : past ⊆ cellEvent T CA o c
  nextW : Node p F → Box p m → ℕ
  alpha : Node p F → ℕ
  halpha : ∀ ν ∈ active, 1 ≤ alpha ν

def SibStep (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T) : Prop :=
  ∀ (o : Option (History p F)) (c : CA.Cell) (st : JointStage T CA o c),
    StageRealized T CA st →
    ∀ a a' : Node p F → ℕ,
      (∀ ν ∈ st.active, a ν < st.alpha ν) → (∀ ν ∈ st.active, a' ν < st.alpha ν) →
      Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a ν}
        = Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a' ν}

/-- PCI (parent-context independence — "named interface, NOT part of (SIB)",
7406–7413); stated, proved nowhere, consumed by nothing in MovesT (REV 13 struck PCI
from TREE-EXP's inputs, 7650–7652). REV 2 (Codex 37): typed — the conditional
continuation law of a child depends only on the child's own data, never on unused
parent/sibling cell data: the SAME individuated child in two branch sets prices its
transported subtree events equally (division-free cross-multiplied form). The
subtree transport `TsubAt` (same prescribed subtree read at the two entrances — the
child-CTS-state identification) is the [2r]/CTS-M(iv)-REP face, flagged E-phase.
A PCI failure adjudicates as R2's lumpability channel, never as a (SIB) failure. -/
def PCI (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T) : Prop :=
  ∀ (o o' : Option (History p F)) (c c' : CA.Cell) (ν : Node p F),
    ν ∈ CA.branchSetOf c → ν ∈ CA.branchSetOf c' →
    ∀ (hν : ChildRoot o ν) (hν' : ChildRoot o' ν)
      (TsubAt : Option (History p F) → Set (History p F))
      (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop),
      SubtreeTransport TsubAt o o' ν →
      Nat.card ↥(cellEvent T CA o c ∩
          {x | ContFiber T o ν hν (TsubAt o) leafSpec nsSpec x})
        * Nat.card ↥(cellEvent T CA o' c')
      = Nat.card ↥(cellEvent T CA o' c' ∩
          {x | ContFiber T o' ν hν' (TsubAt o') leafSpec nsSpec x})
        * Nat.card ↥(cellEvent T CA o c)
```

### 2.7 VP-SOUND's two declared citations (typed, hypothesis-only)

```lean
/-- (HEN-LIFT) (7254–7261): coprime-factor Hensel over ℤ_p. REV 2 (Codex 37): full
statement — a monic f whose reduction splits as ψ·h̄ with ψ monic irreducible and
coprime to h̄ factors UNIQUELY as g·h (monic, reducing to ψ·h̄), g irreducible; the
unramified read-off (E,F) = (1, deg ψ) is the final conjunct, typed against the
local-field API [E-phase: Mathlib's Hensel + `IsUnramified` vocabulary; campaign §4
PREFERS the library discharge]. Valid at ALL primes incl. wild (coprimality, not
tameness). NO mass unit consumes it. -/
def HenLift (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : Polynomial ℤ_[p], f.Monic →
    ∀ ψ hb : Polynomial (ZMod p), ψ.Monic → Irreducible ψ → IsCoprime ψ hb →
      f.map (PadicInt.toZMod) = ψ * hb →
      ∃! gh : Polynomial ℤ_[p] × Polynomial ℤ_[p],
        gh.1.Monic ∧ gh.2.Monic ∧ f = gh.1 * gh.2 ∧
        gh.1.map PadicInt.toZMod = ψ ∧ gh.2.map PadicInt.toZMod = hb ∧
        Irreducible gh.1 ∧ UnramifiedOfDeg gh.1 ψ.natDegree
-- [`UnramifiedOfDeg g d` := ℚ_p[x]/(g) is unramified of residue degree d, i.e.
--  (E, F) = (1, d) — E-phase types it against Mathlib's extension API.]

/-- (OM-SAT) (7262–7273): the Ore–Montes certificate — a saturated branch's cluster
factor is irreducible with e = E, f = F. REV 2 (Codex 37): typed over a named
factor-assignment carrier: `ClusterFactorOf H fη` (the track factor H's chain
certifies — the D.11/TRANS accumulation vocabulary), `ramIdx`/`resDeg` (the
extension invariants). CONSUMED as a cite (GMN/Montes), "not derived from §B2-DEF"
(7267–7270); axiomatization would need the faithfulness-entry + guardian process. -/
def OmSat (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (H : History p F) (fη : Polynomial ℤ_[p]),
    ClusterFactorOf H fη → IrrHalts H →
    Irreducible fη ∧ ramIdx fη = accE H ∧ resDeg fη = accF H
```
VP-SOUND status (7274–7279) transcribed: a CITATION obligation with two declared
statements, NOT a gap in the mechanism; the PARI-oracle layers are the standing
refuters; D4R.0-K(c)'s remainder = exactly {VP-SOUND's cites} (7634–7635).

### 2.8 pre-halt marks and the dictionary carriers (ONE-F)

```lean
/-- PRE-HALT (7595–7598) — REV 2 (Codex 17): BOX-FREE, "a property of η's OWN cell
data" as the note says. Rev 1's `PreHaltPfx` read the box through the (ns) clause;
but at a PROPER prefix H' of η, η's own next node is a member of H''s branch set,
so (τ-ns) is refuted BY η's OWN DATA at every proper prefix — only the (τ-irr)
clause survives, and it is node data. Unit T-F0 proves the equivalence with the
model-side pruning predicate on realized inputs. -/
def PreHalt (H : History p F) : Prop :=
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H → H'.nodes ≠ [] → ¬ IrrHalts H'

/-- the length-ℓ chains of a tree T of shape P̂ (the dictionary's per-tree count,
7601–7603). -/
noncomputable def VTree.chainCount (Tr : VTree p F) (n : ℕ) (P : Shape n) : ℕ :=
  Nat.card {H : History p F // H ∈ Tr.chains ∧ (P : ShapePrefix).MatchesHist H}
```

### 2.9 the seam-discharge carriers (consumed at §5; see units T-D1…T-D14)

```lean
/-- the joint-cell assignment — MovesT's cell vocabulary (the W4-1/W4-2 re-keying
target): a cell datum per (state, box) with (a) finiteness, (b) locality at the
CELL'S OWN LEVEL (a per-state level from shape/height data — NOT the withdrawn
uniform cap envelope; §5 W4-2), (c) the branch set read off the cell. NOTE (Codex
20): `child_cell` already REJECTS the degenerate constant-`cellOf` models on any T
with a genuine branch distinction — T-D2's `cellOf_nonconstant` displays this as a
theorem, not a hope. -/
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

/-- THE CELL EVENT Σ_c — the note's conditioning object (7290–7292), DEFINED:
the site's realized state cut to one cell value. Every conditional law of this
corpus conditions HERE (REV 2, Fable CRIT-1/CRIT-2). -/
def cellEvent (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) : Set (Box p m) :=
  {x | T.mem o x ∧ CA.cellOf o x = c}

/-- W4-1's re-keyed `eligible` — a DEFINED predicate over the cell/branch-set
vocabulary (MovesD §2.5 W4-1(c) verbatim). Cell data BY CONSTRUCTION (it factors
through `cellOf` — T-D1's second lemma displays this). -/
def eligibleT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) : Prop :=
  ν ∈ CA.branchSetOf (CA.cellOf o x)

/-- the root-cell tie: the root state's cell datum IS the reduction f̄ read through
χ ((JC-root) 7464–7466). A LAW the canonical CellAssign must satisfy; hypothesis
field `hrc` on T-E5/E8/T-S3/T-G1. -/
def RootCellsOf (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ x y : Box p m, CA.cellOf none x = CA.cellOf none y ↔ ∀ b : Fin n, x (χ b) = y (χ b)

/-- RUN-KEY, NAMED (REV 2 — Fable CRIT-4 + Codex 22): the HC-2 bridge surface — for
every class representative and EVERY jet, the jet's top stratum is exactly tree
membership. THE ∀-JET QUANTIFIER SITS OUTSIDE THE IFF: rev 1's `(∀ J, x ∈ SHZ) ↔
mem` form could not discharge D4R_CYL (the ⇒ leg needed ∀-J from ONE J — precisely
the jet-independence CFW leaves open; counter-model on record in the Fable audit).
This per-jet form is the honest HC-2 surface (ReadsOf↔locus at finite level). -/
def RunKey (T : TreeModel p F n N m pol) (P : Shape n) : Prop :=
  ∀ (H : History p F), H ∈ PrefSet n pol P →
    ∀ (x : Box p m) (J : JetSetup H n N m),
      x ∈ J.SHZ (topLocus p m) ↔ T.mem (some H) x

/-- ETA-LOC, NAMED: tree membership is η-CLASS data — every PrefSet member of class
i realizes the same membership event as the class representative. [E-phase keys
`SameClass` to MovesD's PrefIdx class map.] Owner HC-2 (PresentNorm/Galois). -/
def EtaLoc (T : TreeModel p F n N m pol) (P : Shape n) : Prop :=
  ∀ (i : PrefIdx n pol P) (H : History p F), H ∈ PrefSet n pol P → SameClass i H →
    ∀ x : Box p m, T.mem (some H) x ↔ T.mem (some (reprOf i)) x

/-- CHAIN-LOC's box face (REV 2, Fable GAP-5): realized chains are in-box — the L3
setting's missing supply (`mem_realizable` does not give `InBox`). Owner HC-2. -/
def InBoxOfMem (T : TreeModel p F n N m pol) (n : ℕ) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x → InBox n H

/-- Wall A reconciliation, TYPED (REV 2, Codex 34): the canonical CellAssign's
branch sets ARE HC-2's per-frame run predicate — branch membership iff `ReadsOf`
holds of the extended history ("HC-2 owns the definition; MovesT re-keys `eligible`
to it in wave 4"; clause (vi)'s vertex read-off is INSIDE ReadsOf per HC2 §7.6).
`ReadsOf` enters as a parameter until HC-2's name lands; the canonical instance
must satisfy this pin. Owner of the instance: HC-2 (fenced Q1/Q2, §4). -/
def WallAReconciled (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (ReadsOf : Box p m → History p F → Prop) : Prop :=
  ∀ (H : History p F) (ν : Node p F) (hν : NodeExtends H ν) (x : Box p m),
    T.mem (some H) x →
    (ν ∈ CA.branchSetOf (CA.cellOf (some H) x) ↔ ReadsOf x (H.snoc ν hν))
```

**`VerdictModelT` — W4-2's re-derivation, ALL fields (REV 2, Codex 20/21).** The
structure is DECLARED IN THIS CORPUS from VP-1/VP-2 + TB-CAP ("MovesD's form is the
negotiating position, not the buildable spec" — W4-2(c)):

```lean
structure VerdictModelT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) where
  vdict : Option (History p F) → Box p m → Option Vd
  halt_iff : ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    ((vdict (some H) x).isSome ↔ (IrrHalts H ∨ NsHalts T (some H) x))
  vdict_irr : ∀ H x, T.mem (some H) x → IrrHalts H →
    vdict (some H) x = some (irrVerdictOf H)
  vdict_ns : ∀ H x, T.mem (some H) x → ¬ IrrHalts H → NsHalts T (some H) x →
    vdict (some H) x = some (nsVerdictOf H)
  vdict_cell : ∀ o x x', T.mem o x → T.mem o x' →
    CA.cellOf o x = CA.cellOf o x' → vdict o x = vdict o x'
  rootVdict : Box p m → Multiset Vd
  rootVdict_law : ∀ x, rootVdict x = henPayload χ x
  rootVdict_cell : ∀ x x', (∀ b, x (χ b) = x' (χ b)) → rootVdict x = rootVdict x'
  capHen : ℕ
  capHen_law : capHen = 1 ∧
    ∀ x x' : Box p m, (∀ b : Fin n, x (χ b) = x' (χ b)) → rootVdict x = rootVdict x'
    -- the hen class is level-1 data through the chart (T-C1's locality face; the
    -- finite-union-of-cells face is T-C1's second conjunct, referenced not
    -- duplicated)
  capIrr : ∀ {P : Shape n}, PrefIdx n pol P → ℕ
  capIrr_law : CapIrrLaw T CA capIrr   -- := T-C2's statement (the per-class,
                                        -- N-FREE cap law; see T-C2)
  -- NO ns cap field: the (ns) clause enters `vdict` only through `NsHalts`; its
  -- classes are NEVER claimed cylindrical (§0 refutation record — the ADMITTED
  -- amendment, MovesD §2.5 W4-2(b)(ii)).
```

FIELD CROSSWALK against MovesD rev-8 `VerdictModel` (W4-2(a)'s full roster — the
"ENTIRE" audit, Codex 20): `V/hVfin/hVne` → CONCRETE `Vd`/`VdAt n` (T-V7 proves
finiteness AND `1 < Nat.card (VdAt n)` for n ≥ 2 — no singleton degeneracy;
hVne := `⟨henVerdict n _⟩`); `vdict` → field, VALUE PINNED by `vdict_irr`/`vdict_ns`
(not just isSome — the rev-1 gap); `halt_iff` → field, proved by T-D3 from
T-V5/V6; `rootVdict/rootHalt_iff` → `rootVdict`+`rootVdict_law` (hen is total at
level 0 — halt_iff trivial there, recorded); `levelOf/levelOf_lt/hlevel` →
`CA.levelOf` + `CA.cellLevel` (the per-state level, T-D4); `cap/capBound/hcapU/
hcapB/cap_law` → the PER-CLAUSE pair `capHen`/`capIrr` with laws := T-C1/T-C2's
statements — CROSS-LEVEL UNIFORM by type: `capIrr` takes NO `N` argument (one cap
per class across all presented N — W4-2(b)'s addendum demand, Codex 21);
`vdict_local` → `vdict_cell` (τ is cell data — VP-2's typing); `Cell/cellOf/
hCellFin/cell_local` → `CellAssign` (the per-state-level `cell_local`, the
WITHDRAWN cap-envelope form replaced — T-D4 sound + falsifier); `vdict_cell/
rootVdict_cell` → fields above. Every rev-8 field is accounted: defined, proved,
replaced-with-warrant, or refuted-with-record (ns cap).

---

## §3 The unit DAG — 53 units (13 easy / 30 medium / 10 hard)

REV 2: two units added (T-F0 the box-free pre-halt bridge; T-D14 the S-6 chain-charge
carrier); every restated unit carries its rev-2 change inline.

### Layer V — VP: the verdict pin (§T.1) [8 units]

**T-V1 `MovesT.vd_deg_hen` · `V1_vdDeg.lean` · easy**
```lean
theorem vd_deg_hen (g : ℕ) (hg : 1 ≤ g) : (henVerdict g hg).deg = g
```
moves_ref: 7072–7073 + 7062 "Σ E·F = d". deps: Defs. sketch: `simp [Vd.deg,
henVerdict]`; one-element multiset, 1·g = g. hypothesis_fields: none.

**T-V2 `MovesT.vd_deg_ns` · `V2_vdDegNs.lean` · easy**
```lean
theorem vd_deg_ns (μ E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) :
    (nsVerdict μ E F hE hF).deg = μ * (E * F)
```
moves_ref: 7083; degree = cluster degree μ·deg Φ̂. deps: Defs. sketch:
`Multiset.map_replicate` + `Multiset.sum_replicate`. hypothesis_fields: none.

**T-V3 `MovesT.accEF_keyDeg` · `V3_accKeyDeg.lean` · medium — REV 2 (Codex 6, Fable
GAP-8(i)): the `?g_of` metavariable is GONE (selections threaded as a zipped list)
and the conclusion now displays BOTH equalities of "cluster degree = key degree · μ
= E·F·μ" (7078–7080).**
```lean
theorem accEF_keyDeg {n : ℕ} (l : List MovesSp.Species) (sels : List (ℕ × ℕ))
    (hzip : l.length = sels.length ∧
      ∀ r s gm, l[r]? = some s → sels[r]? = some gm → s.sel = some gm)
    (hne : l ≠ []) (hroot : ∀ s, l.head? = some s → MovesSp.RootStage n s)
    (hchain : l.Chain' MovesSp.StageLaws)
    (s : MovesSp.Species) (hlast : l.getLast? = some s)
    (g μ : ℕ) (hsel : sels.getLast? = some (g, μ) ∧ s.sel = some (g, μ)) :
    (l.map fun t => t.e).prod * (sels.map Prod.fst).prod = s.e * g * s.D
    ∧ ((l.map fun t => t.e).prod * (sels.map Prod.fst).prod) * μ
        = (s.e * g * s.D) * μ
```
moves_ref: 7078–7080 "cluster degree = key degree · μ = E·F·μ" — first conjunct:
E·F = the CHILD key degree D′ = e·g·D; second: cluster degree = D′·μ = E·F·μ (the μ
display rev 1 dropped). deps: MovesSp.Defs (StageLaws, RootStage). sketch: list
induction along `Chain' StageLaws`: D_{r+1} = e_r·g_r·D_r with D₀ = 1 (RootStage)
telescopes to ∏e·∏g = D′; multiply by μ. hypothesis_fields: none (pure species
bookkeeping).

**T-V4 `MovesT.sat_iff_confirming` · `V4_satW1.lean` · medium — REV 2 (Codex 36):
split into its two exactly-warranted legs; nothing unfrozen is bundled.**
```lean
theorem sat_iff_W1 {n : ℕ} (s s' : MovesSp.Species)
    (hstep : MovesSp.StageLaws s s') (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    (μ = 1) ↔ (s'.W = 1)          -- warrant: StageLaws's W-law (s'.W = μ)
theorem sat_iff_selNone {n : ℕ} (s s' : MovesSp.Species)
    (hstep : MovesSp.StageLaws s s') (hcoh : MovesSp.Coherent s')
    (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    (μ = 1) ↔ s'.sel = none      -- warrant: (G6) "selection = ⊥ iff W = 1"
```
moves_ref: 7078–7080 saturation ⟺ μ = 1. DOCSTRING DUTY: these are CORPUS-TIE
lemmas (VP-2's τ-irr = MovesSp's confirming W = 1 letter, `CatalogueWord.hLast`),
not note-display transcriptions — each leg cites its exact MovesSp warrant and
claims nothing further. deps: MovesSp.Defs. hypothesis_fields: none.

**T-V5 `MovesT.tau_disjoint` · `V5_tauDisjoint.lean` · medium — REV 2 (Codex 7,
Fable CRIT-5): the `∨ True` literal is DEAD; the prose duty is now the statement,
over the new named carrier.**
```lean
def IrrHaltsAsChild (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (x : Box p m) : Prop :=
  T.mem o x ∧ T.child o ν x ∧ ν.μ = 1

theorem tau_disjoint (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (x : Box p m) (h : IrrHaltsAsChild T o ν x) :
    ¬ NsHalts T o x
```
moves_ref: 7104–7111 "MUTUAL EXCLUSIVITY, by domain stratification … disjoint by
depth … disjoint by case": (τ-irr) verdicts attach to members of a NONEMPTY branch
set; (τ-ns) demands the branch set EMPTY. The hen/chain disjointness is BY TYPE
(hen lives in `henV`/`henPayload`, never on `chains`) — recorded in the docstring,
no theorem needed. deps: Defs. sketch: `h.2.1` contradicts `NsHalts`'s
`∀ ν, ¬ child`. hypothesis_fields: none.

**T-V6 `MovesT.tau_total` · `V6_tauTotal.lean` · medium — REV 2 (Codex 8): no longer
the branch-set tautology; states the PER-CHILD covering + exactly-one content.**
```lean
theorem tau_total (T : TreeModel p F n N m pol) (hdi : BranchDichotomy T)
    (H : History p F) (x : Box p m) (hmem : T.mem (some H) x) :
    (∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      ((ν.μ = 1 ∧ IrrHalts (H.snoc ν hν) ∧ ¬ T.mem (some (H.snoc ν hν)) x → True) ∨
        (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)) ∧
      ¬ (ν.μ = 1 ∧ 2 ≤ ν.μ)) ∧
    ((∀ ν : Node p F, ¬ T.child (some H) ν x) → NsHalts T (some H) x)
```
STATEMENT DUTY [E-phase final form; the display above is the shape]: (i) every
realized child receives EXACTLY ONE disposition — saturate-and-halt (μ = 1, the
extension IrrHalts) or continue (μ ≥ 2, the extension realized) — from `hdi`, with
exclusivity by μ-arithmetic; (ii) a childless realized state IS the (ns) status
(definitional from `NsHalts`). HONESTY NOTE (docstring duty): the branch-set-level
"some child ∨ no child" split is CLASSICAL and carries no content — the covering's
Lean content is exactly (i), i.e. `hdi`; this unit is the honest typed rider,
consumed by T-D3's halt_iff. moves_ref: 7112–7119 "COVERING, the case analysis (no
orphan)". deps: Defs, T-V5. hypothesis_fields: `hdi : BranchDichotomy T` (KB-TOT,
owner HC-2/D4R0K — NEVER proved here).

**T-V7 `MovesT.vdAt_finite` · `V7_vdFin.lean` · medium — REV 2 (Codex 20's
degeneracy leg): gains the non-singleton lemma.**
```lean
instance vdAt_finite (d : ℕ) : Finite (VdAt d)
theorem vdAt_nontrivial (d : ℕ) (hd : 2 ≤ d) : 1 < Nat.card (VdAt d)
```
moves_ref: 7061–7063 — needed so W4-2's `hVfin` is INSTANTIABLE at V := VdAt n AND
the singleton-V degeneracy is REJECTED (W4-2(b)(i)): at d ≥ 2, {(1,d)} ≠ {(d,1)}
are both degree-d verdicts. deps: Defs. sketch: a verdict of deg d has ≤ d pairs,
each in [1,d]²; inject into Sym-type on Fin (d+1) × Fin (d+1) (MovesSp SP2's
encoding idiom); the two displayed witnesses for nontriviality.
hypothesis_fields: none.

**T-V8 `MovesT.shapeOfH_matches` · `V8_shapeOf.lean` · medium — REV 2 (Codex 9: the
Q1-fence violation REMOVED — `HistoryCoherent` no longer appears; Codex 4: the
junk-guard discharge is now a conclusion).**
```lean
theorem shapeOfH_matches (H : History p F) (n : ℕ) (hlaw : NodeDataLawful p H)
    (hbox : InBox n H) :
    (shapeOfH H n).MatchesHist H ∧ ShapeWF n (shapeOfH H n)
theorem acc_pos (H : History p F) (hlaw : NodeDataLawful p H) :
    max (accE H) 1 = accE H ∧ max (accF H) 1 = accF H
```
moves_ref: §D4-R L3 dictionary (TB-CAP(irr) and thr(T) read thresholds off it,
7562–7566). deps: Defs, MovesD.SW1_shapeWF. sketch: componentwise Matches is
definitional (readOf copies ν's fields; the w-card identity is `NodeDataLawful`'s
p-power clause); ShapeWF via SW1; acc_pos: products of ≥-1 factors. FENCE NOTE:
`NodeDataLawful` carries NO child-keying clause — the V10/Q1 steep-leg
inconsistency cannot make this unit vacuous; no unit of this corpus premises
`HistoryCoherent` (rev-2 sweep). hypothesis_fields: `hlaw` (owner HC-2, §0).

### Layer C — TB-CAP per clause + the (ns) pair (§T.2) [8 units]

**T-C1 `MovesT.tbcap_hen` · `C1_capHen.lean` · medium**
```lean
theorem tbcap_hen (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (x x' : Box p m) (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    henPayload χ x = henPayload χ x'
```
plus the partition face: the verdict class {x │ henPayload χ x = v₀} is a UNION of
level-0 cells `rootCell χ g` (finitely many g), i.e. membership depends on x only
through x ∘ χ. CAP N_V = 1, uniform per class. moves_ref: 7155–7159. deps: Defs.
sketch: `redPoly χ x` is a function of x ∘ χ (definitional); henDegrees/henPayload
factor through it. hypothesis_fields: none. PROVED-IN-NOTE status: unconditional.

**T-C2 `MovesT.tbcap_irr` · `C2_capIrr.lean` · medium — REV 2 (Codex 10/21, Fable
GAP-8(v)): the cap is now the CONTRACT'S cap N(η′,⊤) — the jet's own C.2 cutoff —
NOT the silently-substituted NPband; and it is N-FREE BY TYPE (cross-level
uniformity). The NPband form survives only as a corollary that EXPLICITLY consumes
T-D7a (the ⊆ half of NP-ID).**
```lean
noncomputable def capIrrOf {P : Shape n} {H : History p F}
    (J : JetSetup H n N m) : ℕ := jetTopLevel J
-- [`jetTopLevel J` := 1 + the largest base level among J's pinned equations at
--  Z = ⊤ — "N(η′,⊤) = 1 + the largest base level among T(η′,⊤)'s finitely many
--  equations" (7178–7180); E-phase types it off MovesC's `totalPins` support.
--  SHAPE DATA ONLY: no N in its value (u* ∈ P̂ makes heights shape data, 7181).]

theorem tbcap_irr {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx c < capIrrOf (S.jet i) → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i)

theorem tbcap_irr_npband {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (hnp : transportedLevels (S.jet i) (topLocus p m) ⊆ bandLevels (P : ShapePrefix) n)
    -- ^ T-D7a's conclusion, HERE an explicit premise — the NP-ID ⊆ half; rev 1
    --   consumed it silently (Codex 10)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx c < (P : ShapePrefix).NPband n → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i)
```
moves_ref: 7161–7182 "the verdict class at this leaf is EXACTLY the extended
single-branch event S(η′,⊤) … §C C.2 (Z = ∅) cuts S(η′,⊤) at level N(η′,⊤) … So
N_V := N(η′,⊤) works" + the quantifier honesty 7183–7187 (per REALIZED halting
branch-read; per (P, i), never joined). CROSS-LEVEL (Codex 21): `capIrrOf` takes no
N — one cap per class across all presented N, the addendum's uniform demand made a
TYPE fact; the ∀-N face is stated at consumption (T-D3's `capIrr_law` quantifies
over the presented family). deps: Defs, MovesD (Presented, D4R.4/L12 apparatus);
T-D7a for the corollary ONLY. sketch: the class IS S(η′,⊤) by definition of fiber;
the finite-level cut is MovesD's D4R.4/L12 exact-realization, restated as
digit-locality below the jet's own cutoff. hypothesis_fields: `S.jet` (HC-2's
PRESENT-EXIST supplies instances); `hnp` on the corollary only.

**T-C3 `MovesT.ns_lump` · `C3_nsLump.lean` · medium — REV 2 (Codex 38): stated over
the DISPLAYED `NsLumpFamily` (§2.5a) — non-circular: antitonicity and the
intersection identity are PROVED from `vanish`+`interior_mono`+`tie`, not assumed.**
```lean
def nsClass (T : TreeModel p F n N m pol) (H : History p F) : Set (Box p m) :=
  {x | NsHalts T (some H) x}

theorem ns_lump (T : TreeModel p F n N m pol) {H : History p F}
    (J : JetSetup H n N m) (Lf : NsLumpFamily T J) :
    (∀ M M', M ≤ M' → Lf.L M' ⊆ Lf.L M) ∧
    nsClass T H = {x | T.mem (some H) x} ∩ ⋂ M, Lf.L M
```
moves_ref: 7203–7209 "(ns-lump) CAP-APPROXIMABILITY … monotone in N with the class
as the intersection. PROVED (a re-reading of B(iii), no new content)." deps: Defs
§2.5a. sketch: antitone from `vanish` + `interior_mono` (more heights = more
equations = smaller event); the identity from `tie` + `NsHalts`'s two conjuncts.
hypothesis_fields: `Lf` (the B(iii) lump family — its `tie` field is the
note-standing-perimeter identification, owner D4R0K; typed, not re-proved).

**T-C4 `MovesT.ns_ladder` · `C4_nsLadder.lean` · medium**
```lean
theorem ns_ladder (M₀ : ℕ) (Zcard : ℕ → ℕ) (hlad : ∀ M, M₀ ≤ M → M - M₀ ≤ Zcard M) :
    Filter.Tendsto (fun M => (p : ℝ) ^ (-(Zcard M : ℤ))) Filter.atTop (nhds 0)
```
moves_ref: 7227–7229. deps: Mathlib only. sketch: |Z_M| ≥ M − M₀ → ∞, p ≥ 2,
zpow-antitone squeeze. hypothesis_fields: none (`hlad` discharged by T-C5 at
consumption in T-C7).

**T-C5 `MovesT.nsZ_free` · `C5_nsFree.lean` · hard [pre-approved split C5a/C5b]**
```lean
theorem nsZ_free {H : History p F} (J : JetSetup H n N m) (M : ℕ) (hM : M₀ J ≤ M) :
    ∃ Z : Locus p m, AdmissibleZ (J.Sigma H.nodes.length) Z ∧
      IsLumpLocus J M Z ∧ M - M₀ J ≤ pinCount Z
```
[`IsLumpLocus J M Z` := Z's equations are EXACTLY the fresh clauses of L_M — the
`interiorFreshIdx J M` set of §2.5a (interior blocks, base index < μ·D, F(b) < ht
≤ M); `M₀ J` := the entrance resolution; `pinCount` := the number of fresh
equations. E-phase types these against MovesC's Locus/floor vocabulary
(`History.floorH`, the (ZC) fields of J) — same accessors as §2.5a's carrier.]
moves_ref: 7216–7229 (i)/(iii). deps: Defs §2.5a, MovesC (AdmissibleZ, ZC), MovesD
(floorS/bandS mirrors). sketch: construct Z_M explicitly from the block/height
grid; freeness: interior coordinate at height > F(b) unpinned on Σ by (ZC-a)'s
inclusive top; rim leads never interior by (ZC-b)'s base ≥ μ·D; the ladder count
from slot 0's unit-spaced heights. THE ONE SUBSTANTIVE NEW PROOF of the C-layer —
the note's rev-2 (ns-null) mechanism, verified clean FOUR times (9222–9223).
hypothesis_fields: the (ZC) package carried by J (standing perimeter, 7232–7233).

**T-C6 `MovesT.ns_price` · `C6_nsPrice.lean` · medium**
```lean
theorem ns_price {H : History p F} (J : JetSetup H n N m) (M : ℕ) (hM : M₀ J ≤ M)
    (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z)
    (hlump : IsLumpLocus J M Z) :
    Nat.card ↥(J.SHZ Z) * p ^ pinCount Z = Nat.card ↥(J.SHZ (topLocus p m))
```
moves_ref: 7225–7227 "(ii) Theorem C(b) with Z = Z_M prices the lump exactly."
deps: MovesC.C6_thmC_b, T-C5. sketch: two C6_thmC_b instances share boxMass;
cross-multiply. hypothesis_fields: J (HC-2 territory), hZ/hlump from T-C5.

**T-C7 `MovesT.ns_null` · `C7_nsNull.lean` · medium — REV 2 (Codex 39, Fable GAP-4
tail): the hypothesis row and the truncation carriers are now DISPLAYED; no bare
ellipsis premise.**
```lean
def Mlev (J : JetSetup H n N m) (N' : ℕ) : ℕ := scaleTop J N'
-- [M(N) := the largest window height with base level < N — C.1.5's Scale map read
--  off J's chart (7205–7207); E-phase binds `scaleTop` to the Scale accessor.]

theorem ns_null {H : History p F} (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N') :
    Filter.Tendsto
      (fun N' => (Nat.card ↥(nsTruncAt Jat Lat N') : ℝ)
        / (Nat.card ↥(stateTruncAt Jat N')))
      Filter.atTop (nhds 0)

def stateTruncAt (Jat : …) (N' : ℕ) : Set (Box p (n * N')) :=
  (Jat N' _).SHZ (topLocus p (n * N'))          -- the truncated state count
def nsTruncAt (Jat : …) (Lat : …) (N' : ℕ) : Set (Box p (n * N')) :=
  stateTruncAt Jat N' ∩ (Lat N' _).L (Mlev (Jat N' _) N')   -- state ∩ lump L_{M(N)}
```
moves_ref: 7210–7231 — THE FINITE-LEVEL FACE: "μ(Σ ∩ L_M) → 0, and the class =
∩_M (Σ ∩ L_M) gives μ((τ-ns) class │ Σ) = 0 by continuity from above." SCOPE RIDER
(REV 2, Fable GAP-4 — binding on every consumer, quoted in T-D12's S-2 row): this
corpus states ONLY the truncated-ratio limit; continuity-from-above and the
profinite class NEVER enter; any consumer reading the note's measure-zero claim off
this field must add its own finite→profinite bridge. deps: T-C3, T-C4, T-C5, T-C6.
sketch: per level, T-C6 gives ratio = p^{−|Z_M|}; T-C5's count + T-C4's limit
squeeze. hypothesis_fields: the jet family `Jat` (HC-2's PRESENT-EXIST face) + the
lump families `Lat` (§2.5a; B(iii) tie, owner D4R0K).

**T-C8 `MovesT.ns_tree_bound` · `C8_nsTreeBound.lean` · medium**
```lean
theorem ns_tree_bound (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (H : History p F) (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) :
    {x | Tr.fiberAt T χ x} ⊆ nsClass T H
```
+ the normalized corollary: the fiber's truncated counts are dominated by T-C7's
vanishing ratios — NEVER a raw-count claim (§0 refutation record). moves_ref:
7240–7247. deps: Defs, T-C7. sketch: fiberAt's leaf clause at H gives NsHalts at
every fiber member. hypothesis_fields: inherited from T-C7 at the corollary only.

### Layer S — (SIB) as hypothesis (§T.3) [3 units]

**T-S1 `MovesT.sib_pair_form` · `S1_sibDefs.lean` · easy — REV 2: over the pinned
cell events; the rev-1 `True` compile witness is dropped.**
```lean
theorem sibCount_pair_form (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (h : SibCount T CA)
    (o : Option (History p F)) (c : CA.Cell)
    (hcard : (CA.branchSetOf c).card = 2) (S : Node p F → Set (Box p m))
    (hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
      S ν = {x | ContFiber T o ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) :
    Nat.card ↥(cellEvent T CA o c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * Nat.card ↥(cellEvent T CA o c)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEvent T CA o c ∩ S ν)
```
moves_ref: 7292 the display; 7523–7525 "P3's censused identity 78,125² =
15,625·390,625 is exactly (SIB) at this site" — the m = 2 specialization IS the
gate-checked shape. deps: Defs §2.6. sketch: instantiate; card 2, exponent 1.
hypothesis_fields: `h : SibCount T CA` (the kernel — this unit only RESHAPES it).

**T-S2 `MovesT.sib_falsifier` · `S2_sibFalse.lean` · medium — REV 2 (Fable GAP-6):
the falsifier's decide surface is the FINITE SURROGATE; the bridge to the real Prop
is a hand lemma (see Layer G's gate architecture).**
```lean
theorem sib_falsifier : ∃ (T : TreeModel 2 (ZMod 2) 2 1 2 polTriv)
    (CA : CellAssign 2 (ZMod 2) 2 1 2 polTriv T), ¬ SibCount T CA
```
moves_ref: doctrine (campaign ledger): a faithful interface must be FALSE for
instances the note would reject — (SIB) is a CONTENTFUL law (7397–7400). deps:
Defs, Gates layer. sketch: a toy model with two children whose continuation events
are IDENTICAL (the note's own warning shape, 7379–7381); the joint count fails the
product AT THE CELL EVENT (the pinned Σ_c — the falsifier survives the rev-2
re-typing because the failure is at the cell event itself, not at a pathological
subset). Negation = one explicit instance: exhibit o/c/S, compute both sides on the
enumerated toy roster (`decide` on the surrogate kernel, hand bridge to the Set
form). hypothesis_fields: none. [`polTriv` := the constant-lift policy on the toy —
Gates layer supplies it.]

**T-S3 `MovesT.sib_root_instance` · `S3_sibRoot.lean` · easy**
```lean
theorem sib_root_instance (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hrc : RootCellsOf T CA χ) (h : SibCount T CA) :
    ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
      2 ≤ (CA.branchSetOf c).card →
      (∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
      Nat.card ↥(cellEvent T CA none c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
          * (Nat.card ↥(cellEvent T CA none c)) ^ ((CA.branchSetOf c).card - 1)
        = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEvent T CA none c ∩ S ν)
```
moves_ref: 7298–7304 "DEPTH-0 INSTANCE: (SIB) at η = ∅ is the root read's
cross-cluster product … the root product's citation authority is the Montes-L1 cite
(D4R0K O4's scope note) … the clause stays under the (SIB) tag." deps: Defs.
sketch: specialize o := none (= `SibCountShallow`'s clause, derived not re-assumed).
RECORD (do not encode): JOINT-D1 is single-cluster EVIDENCE, not the theorem — the
root clause carries NO separate hypothesis; it rides the same `hsib` tag (the rev-6
Fable repair, 9196–9201). hypothesis_fields: `h : SibCount T CA`, `hrc`.

### Layer E — TREE-EXP: the first-split recursion (§T.4) [13 units]

**T-E1 `MovesT.jcRoot_partition` · `E1_jcRootPart.lean` · easy — REV 2 (Codex 40,
Fable GAP-8(ii)): bracketing fixed — the partition conjunction no longer nests under
the union.**
```lean
theorem jcRoot_partition (χ : Fin n → Fin m) :
    ((Set.univ : Set (Box p m)) = ⋃ g : Fin n → ZMod p, rootCell χ g) ∧
    Pairwise (Function.onFun Disjoint (rootCell χ))
```
moves_ref: 7464–7466 "(JC-root) PROVED, unconditional". deps: Defs. sketch: cells
are fibers of x ↦ x ∘ χ. hypothesis_fields: none.

**T-E2 `MovesT.jcRoot_card` · `E2_jcRootCard.lean` · easy**
```lean
theorem jcRoot_card (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (g : Fin n → ZMod p) :
    Nat.card ↥(rootCell χ g) * p ^ n = p ^ m
```
moves_ref: 7464–7468 (incl. the degree-1 base case, recorded in docstring). deps:
Defs. sketch: coordinate-splitting equivalence (MovesC C4's `putOn` idiom).
hypothesis_fields: none.

**T-E3 `MovesT.jc_single` · `E3_jcSingle.lean` · medium — REV 2 (Codex 41): the
site-cell bridge is IN the statement (via `SitePresents`), not a sketch promise.**
```lean
theorem jc_single (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m)
    (hpres : SitePresents T CA o c Sigma fd)
    (hfree : ∀ cl ∈ fd.clauses, ∀ cIdx ∈ cl.support, Sigma.pinned cIdx = false) :
    Nat.card ↥(cellEvent T CA o c) * p ^ fd.mstar = Nat.card ↥(stateEvent T o)
```
moves_ref: 7469–7472 "(JC-single) PROVED (= C.1.5(1) verbatim): at a site whose
window hull has ONE side, the joint cell IS a single §C read stratum with its
values." deps: MovesC.C4_conditionalMass, Defs §2.5. sketch: rewrite both events by
`hpres`; the conclusion is `C4_conditionalMass`'s identity verbatim (`Sigma.mass` =
the state count through hpres's second conjunct). hypothesis_fields: `hpres` (the
jet-site tie — HC-2 face); no new strength (the note marks this clause PROVED via
C.1.5(1), BUILT in MovesC).

**T-E4 `MovesT.jcMulti_branching` · `E4_jcMultiBranch.lean` · medium — REV 2 (Fable
CRIT-2 fixed at §2.5's `JCmultiAt`; Fable GAP-7: the branching corollary now
concludes k ≤ card, the display's "k sides ⟹ ≥ k branches").**
```lean
theorem jcMulti_branching (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (c : CA.Cell) (ss : SideSplit T CA c) :
    ss.k ≤ (CA.branchSetOf c).card
```
moves_ref: 7473–7483 "(JC-multi) OPEN, displayed … A multi-side site is always a
BRANCHING site (k sides ⟹ ≥ k branches), so unbranched segments never consume
(JC-multi)." deps: Defs §2.5. sketch: j ↦ (side_ne j).choose is injective into the
branch set (sideOf is a function); `Finset.card_le_card_of_injOn`. The DEF
deliverable (`JCmultiAt`, the open obligation typed at the site) moved to §2.5;
this unit proves the displayed consequence. hypothesis_fields: `JCmultiAt` is NEVER
proved — hypothesis `hjcm` downstream, PER-SITE only.

**T-E5 `MovesT.fiber_root_split` · `E5_rootSplit.lean` · hard — REV 2 (Fable
CRIT-3, Codex 11): the sibling power is `numTracks`, NOT `numTracks − 1`. Check at
t = 1 (F1, B22): 5⁶·5⁴·5¹⁸ = 5²⁸ = 5²²·5⁶ ✓; p = 2 census: 8·2³·2⁶ = 2¹² … per-level
instance recorded in T-G1. Rev 1's form forced 5¹⁰ = 5²⁸ — refuted by the note's own
committed integers.**
```lean
structure RootSplitData (Tr : VTree p F) (g : Fin n → ZMod p) where
  t : ℕ                                        -- the CONTINUING tracks
  trackChains : Fin t → Set (History p F)      -- head-node partition of Tr.chains
  hpart : (⋃ i, trackChains i) = Tr.chains ∧
    Pairwise (Function.onFun Disjoint trackChains)
  hhead : ∀ i, ∃ ν₀ : Node p F, ∀ H ∈ trackChains i, H.nodes.head? = some ν₀
  hne : ∀ i, (trackChains i).Nonempty
-- τ-hen tracks carry NO chain (7069): they constrain only through g — leaf
-- factors 1, absent from the product (7490–7491).

def trackEvent (Tr : VTree p F) (T : TreeModel p F n N m pol) {g : Fin n → ZMod p}
    (htracks : RootSplitData Tr g) (i : Fin htracks.t) : Set (Box p m) :=
  {x | SubFiber T (htracks.trackChains i) Tr.leafV Tr.nsLeaf x}
-- [`SubFiber` := ContFiber's three clauses over a designated chain subset (§2.6's
--  body with Tsub := trackChains i and the child root = the track's head read).]

theorem fiber_root_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hsib : SibCount T CA) (g : Fin n → ZMod p) (htracks : RootSplitData Tr g)
    (hfib : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * (Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n
      = p ^ m * ∏ i : Fin htracks.t, Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i)
```
moves_ref: 7485–7495 "ROOT CLAUSE: μ(fiber T) = jvol({f̄ = g}) · ∏_{tracks i}
μ(S_{T_i} │ Σ₀) = p^{−n} · ∏_i μ(S_{T_i} │ Σ₀)" — division-free with
card(Σ₀)·p^n = p^m: card(fiber)·card(Σ₀)^t·p^n = p^m·∏ᵢ card(Σ₀ ∩ Sᵢ), exponent
t = numTracks (the rev-2 arithmetic, verified against F1 AND the p=2 census above).
deps: T-E1, T-E2, T-S1/T-S3. sketch: fiberAt decomposes as (x ∈ rootCell χ g) ∧
⋂ track events ∧ hen payload (determined by g); SibCount at o = none over the root
cell's branch set (hrc identifies the root cell event with `rootCell χ g`); T-E2's
root charge converts card(Σ₀)·p^n = p^m. t = 1 needs no SIB (single factor —
docstring). LEDGER CHECK (7491–7495: F1's 14-pin split) = Gates layer (T-G1).
difficulty: hard. hypothesis_fields: `hsib` (SIB — OPEN); `hrc`; the Montes-L1 root
authority is the SAME tag (T-S3's record).

**T-E6 `MovesT.fiber_seg_step` · `E6_segStep.lean` · medium — REV 2 (Codex 43,
Fable GAP-3): the level-separation premise is IN the statement (`SpectatorFor`).**
```lean
theorem fiber_seg_step (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (Tr : VTree p F) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : (L.sys H).2.oneSide)   -- one-side site [E-phase: the hull-side count
                                    -- datum of the transported system]
    (E : Set (Box p m)) (hspec : SpectatorFor (L.freshCoords H) E) :
    Nat.card ↥(stateEvent T (some H) ∩ E) * p ^ L.siteExp H
      = Nat.card ↥(stateEvent T (L.parentSt H) ∩ E)
```
moves_ref: 7496–7499 "UNBRANCHED SEGMENT: along a maximal single-branch run, each
site is one-side/one-factor, so (JC-single) applies … multiply the running mass by
jvol(c_s │ Σ) = vol_nom(E_fresh(ν_s)) at each site." deps: T-E3, MovesD
(TreeModel.mem_snoc), Defs §2.5. sketch: L.presents rewrites both events into the
stratum form; C4's count law relativizes to E by `hspec` (the fresh coordinates are
free of E — the standard C.1.5 spectator step). hypothesis_fields: the ledger `L`
(the site's jet — HC-2 face); `hspec` (explicit, rev 2).

**T-E7 `MovesT.fiber_first_split` · `E7_firstSplit.lean` · hard — REV 2: the `?`
exponent is GONE (Fable GAP-8(iii)) — the SIB shape and the jvol charge are now TWO
displayed conjuncts, each exact; and (JC-multi) enters PER-SITE (Codex 12–13).**
```lean
structure SplitSiteData (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) where
  o : Option (History p F)               -- the split site's entrance state
  c : CA.Cell                            -- its joint cell
  hbr : 2 ≤ (CA.branchSetOf c).card
  S : Node p F → Set (Box p m)           -- the member-indexed child events
  hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
    S ν = {x | ContFiber T o ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ
  hdecomp : {x | Tr.fiberAt T χ x} ∩ stateEvent T o
    = cellEvent T CA o c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν
  -- the first-split fiber identification at this site (proved in E8's recursion
  -- from fiberAt's clauses; a FIELD here so E7 states one recursion frame)

theorem fiber_first_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hsib : SibCount T CA) (d : SplitSiteData Tr T CA χ)
    (hcharge : Nat.card ↥(cellEvent T CA d.o d.c) * p ^ jointExpOf d
      = Nat.card ↥(stateEvent T d.o)) :
    -- (SIB) at c, the member-indexed product (7510):
    Nat.card ↥({x | Tr.fiberAt T χ x} ∩ stateEvent T d.o)
        * (Nat.card ↥(cellEvent T CA d.o d.c)) ^ ((CA.branchSetOf d.c).card - 1)
      = ∏ ν ∈ CA.branchSetOf d.c,
          Nat.card ↥(cellEvent T CA d.o d.c ∩ d.S ν)
-- [`jointExpOf d` := the site's exponent — the single side's mstar (one-side) or
--  the SideSplit sum (multi-side); `hcharge` is DISCHARGED by T-E3 at one-side
--  sites and rides as `JCmultiAt` (the hjcm tag) at multi-side sites — the
--  PER-SITE consumption the note prescribes (7506–7508, 7451–7452).]
```
moves_ref: 7503–7515 "FIRST SPLIT: … Charge jvol(c │ Σ) — the FORMERLY MISSING
FACTOR, now explicit — supplied by (JC-single) or (JC-multi) — then by (SIB) at c
… μ(fiber T │ Σ) = jvol(c │ Σ) · ∏_{j=1}^m μ(S_{T_j} │ Σ_c)"; halted children =
`Set.univ` legs (factor = full cell — 7509). deps: T-E3, §2.5 (JCmultiAt), T-S1.
sketch: rewrite by hdecomp; apply hsib at (o, c); the charge conjunct is the
hypothesis. The REL.2 identification of children as smaller-degree theory
(7511–7513) is NOT consumed — the Lean recursion is on node count alone (7529–7530).
hypothesis_fields: `hsib`; `hcharge` per site (T-E3-discharged or hjcm-tagged).

**T-E8 `MovesT.treeExp` · `E8_treeExp.lean` · hard — REV 2: `hjcm` is PER-SITE
(quantified over the TREE'S OWN multi-side sites only — Codex 12–13); the exponent
statement is UNCHANGED from rev 1 (verified correct against both censuses — Fable
CRIT-3's scope note: the defect was E5-local).**
```lean
def multiSites (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) : Set (History p F) :=
  {H | H ∈ Tr.chains ∧ ¬ (L.sys H).2.oneSide}

theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hsib : SibCount T CA) (L : SiteLedger Tr T CA χ)
    (hjcm : ∀ H ∈ multiSites Tr T CA χ L, ∀ ss : SideSplit T CA (L.cellAt H),
      IsMultiSideSite T CA (L.cellAt H) ss →
      JCmultiAt T CA (L.parentSt H) (L.cellAt H) ss)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) :  -- ALL leaves (τ-irr)/(τ-hen)
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m
```
moves_ref: 7449–7456 "(TREE-EXP) μ{f : T_can^τ(f) = T} = ∏_{read sites s of T}
jvol(c_s │ Σ_{<s}), every site charged exactly once — the ROOT INCLUDED"; the (NS)
clause 7457–7461 EXCLUDED BY `hdet`. deps: T-E5, T-E6, T-E7, T-E2. sketch: strong
induction on Tr.chains' card via the first-split decomposition: root clause (E5),
unbranched runs (E6), terminal leaves (factor 1 — verdict is cell data of the last
site, TB-CAP exhibits the class: T-C1/T-C2), first split (E7 with hcharge from E3
or hjcm BY SIDE COUNT — single-side trees never touch hjcm, rev 2). Every site in
exactly one recursion frame ⇒ each site charged once. difficulty: hard (the corpus
centerpiece). hypothesis_fields: `hsib` (SIB), `hjcm` (JC-multi, THIS tree's
multi-side sites only), `L` (the per-site jet ledger — HC-2's presented faces),
`hdet`, `hrc`.

**T-E9 `MovesT.tree_fiber_disjoint` · `E9_fiberDisjoint.lean` · medium — REV 2
(Codex 14): TRUE under the repaired `fiberAt` — the ns-leaf verdict VALUE is now
pinned by the fiber clauses, so the rev-1 counterexample (two trees differing only
in an ns verdict, both fibering x) dies.**
```lean
theorem tree_fiber_disjoint (Tr Tr' : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m)
    (h : Tr.fiberAt T χ x) (h' : Tr'.fiberAt T χ x) :
    Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
    ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H)
```
moves_ref: 7025–7029 "one f, ONE tree … a genuine PARTITION of the decided set".
deps: Defs. sketch: clause (i) is a graph equality (Set.ext); clause (ii) now pins
leafV on BOTH legs (irr value = irrVerdictOf H, ns value = nsVerdictOf H — both
functions of H alone) and nsLeaf (the ns leg carries ¬IrrHalts, the irr leg
¬nsLeaf, and the τ-disjunction at x decides which leg both trees are on); clause
(iii) pins henV. hypothesis_fields: none — the CHOICE-FREENESS payoff,
unconditional.

**T-E10 `MovesT.perShape_law` · `E10_perShape.lean` · hard — REV 2 (Codex 16): the
summation domain now EXCLUDES ns-leaf trees (`NsFree`), matching the note's denial
of the product law there.**
```lean
def NsFree (Tr : VTree p F) : Prop := ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H

theorem perShape_law (T̂ : TreeShape n) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) (hχ : …) (hrc : …)
    (hsib : SibCount T CA) (hjcm : ∀ Tr …, (T-E8's per-site quantifier at each
      summand tree)) (Lat : ∀ Tr …, SiteLedger Tr T CA χ) :
    (∑ᶠ Tr : {Tr : VTree p F // TreeShapeOf Tr n = T̂ ∧ NsFree Tr},
      Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x}) * p ^ (Ashape T̂)
      = CofShape T̂ * p ^ m
```
[`TreeShape`/`TreeShapeOf` := chains projected through `shapeOfH` with tree
structure retained; `Ashape T̂` := n + Σ window-site shape exponents (=`AofTr`
through the ledger, shape-determined per 7537–7540); `CofShape T̂` := Nat.card of
the realized ns-free value-trees of shape T̂ — E-phase fixes the finite enumeration
via MovesD's PrefIdx machinery per chain.] moves_ref: 7537–7545 "Σ_{T of shape T̂}
μ(fiber T) = C_T̂(p) · p^{−A(T̂)}, with NO multiplicity weights — the tree fibers
are genuinely disjoint" — stated for TREE-EXP's domain (all leaves (τ-irr)/(τ-hen),
7449–7451; the (ns) trees are 7457–7461's separate clause, NOT summed here). deps:
T-E8, T-E9, T-V8, MovesD (shape exponents). sketch: sum T-E8's constant over the
shape's value-trees (D10's sum-the-constant idiom); disjointness never needed for
the SUM but IS the no-multiplicity-weights content — cite T-E9 in the docstring.
MULTINOMIAL SCOPE (7548–7557): the m!/(∏ mⱼ!) factorization is NOT claimed — record
verbatim in the docstring. difficulty: hard. hypothesis_fields: `hsib`, `hjcm`
(per-site, per summand tree), `Lat` (ledgers).

**T-E11 `MovesT.treeN` · `E11_treeN.lean` · hard — REV 2: `AofTr` is now DEFINED
(§2.5) and `hjcm` per-site; the exponent form is UNCHANGED (census-verified).**
```lean
theorem treeN (Tr : VTree p F) (T : TreeModel p F n (n * N) pol) -- m := n·N level
    (CA : …) (χ : …) (hχ : …) (hrc : …)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hthr : Tr.thr n ≤ N) (hsib : SibCount T CA)
    (hjcm : (T-E8's per-site quantifier)) (L : SiteLedger Tr T CA χ) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N)
```
moves_ref: 7559–7574 "TREE-N (finite-level stability): for every N ≥ thr(T):
#{f mod p^N : T_can^τ(f) = T} = p^{nN} · μ(fiber T) — the fiber is a FINITE
intersection of finite-level digit-cell conditions … an exact union of level-N
residue classes." deps: T-E8, T-C1, T-C2, T-V8 (thr via shapeOfH), MovesD D4R4all.
sketch: T-E8 at the working level; thr joins the branch thresholds, the leaf caps
(T-C1/T-C2 — `capIrrOf` is N-free, so ONE cap serves all levels: the rev-2 T-C2),
and the site levels (`siteLevel`); above it every condition is an exact
residue-class union. X.3-FREE (7047–7048); GIVEN (SIB) + (JC-multi at multi-side
sites) "for the mass value" (7576–7577). hypothesis_fields: `hsib`, `hjcm`
(per-site), `L`, `hdet` (verbatim 7241–7243), `hrc`.

**T-E12 `MovesT.treeN_ns` · `E12_treeNns.lean` · medium — REV 2 (Codex 44): a
complete statement — the truncation carriers and the domination hypothesis are
displayed; same level-family threading as T-C7.**
```lean
theorem treeN_ns (Tr : VTree p F) (H : History p F)
    (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hdom : ∀ N' h, {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N') x}
      ⊆ nsTruncAt Jat Lat N') :
    Filter.Tendsto
      (fun N' => (Nat.card ↥{x : Box p (n * N') |
          Tr.fiberAt (Tat N' _) (χat N') x} : ℝ) / (p : ℝ) ^ (n * N'))
      Filter.atTop (nhds 0)
```
moves_ref: 7574–7576 "For (ns)-leaf trees the identity is REPLACED by the
NORMALIZED capped bound of §T.2 (p^{−nN}·count ≤ μ(lump ∩ …) → 0; the raw count
need NOT tend to 0)." deps: T-C7, T-C8 (hdom is T-C8's inclusion cut to the
truncated lump at each level — E-phase derives it there). sketch: domination +
T-C7's vanishing ratio; squeeze (state counts ≤ p^{nN}). hypothesis_fields: T-C7's
(jet family, lump families).

**T-E13 `MovesT.tgt_finadd` · `E13_tgtFinAdd.lean` · easy**
```lean
theorem tgt_finadd (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m)
    (hd : ∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, Tr ≠ Tr' →
      Disjoint {x | VTree.fiberAt Tr T χ x} {x | VTree.fiberAt Tr' T χ x}) :
    Nat.card ↥(⋃ Tr ∈ 𝒯, {x | VTree.fiberAt Tr T χ x})
      = ∑ Tr ∈ 𝒯, Nat.card ↥{x | VTree.fiberAt Tr T χ x}
```
moves_ref: 7017–7030 (TGT)'s regrouping license AT FINITE LEVEL; the DENSITY form
stays X.3-tagged and UNSTATED (§0). deps: T-E9. sketch: Nat.card of finite disjoint
unions; hd from T-E9 pointwise (`≠` between EXTENSIONALLY distinct trees — E-phase
notes the VTreeExt quotient tie, T-F1). hypothesis_fields: none.

### Layer F — ONE-F: the once-per-f normalization [5 units]

**T-F0 `MovesT.preHalt_prunedMem` · `F0_preHalt.lean` · easy — NEW at REV 2
(Codex 17): the box-free pre-halt IS the model-side pruning on realized inputs.**
```lean
theorem preHalt_prunedMem (T : TreeModel p F n N m pol) (H : History p F)
    (hne : H.nodes ≠ []) (x : Box p m) (hmem : T.mem (some H) x) :
    PrunedMem T H x ↔ PreHalt H
```
moves_ref: 7595–7598 "Call a value-prefix η PRE-HALT if none of its proper prefixes
τ-halts — a property of η's OWN cell data … Pref^τ(P̂) … is shape/value-computable."
deps: Defs §2.4/2.8, MovesD (mem_snoc). sketch: (⇐) the ¬IrrHalts leg is PreHalt;
the ¬NsHalts leg: a proper nonempty prefix H' of H extends inside H by H's own next
node ν', and `mem_snoc` at x gives `T.child (some H') ν' x` — refuting NsHalts at
H'. (⇒) restriction. THE PAYOFF: `PreHalt` is box-free, so Pref^τ is
shape/value-computable exactly as the note says. hypothesis_fields: none.

**T-F1 `MovesT.oneF` · `F1_oneF.lean` · easy — REV 2 (Codex 15): true again under
the repaired `fiberAt` (the ns-verdict pin restores uniqueness).**
```lean
theorem oneF (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃! TrE : VTreeExt p F, TrE.val.fiberAt T χ x
```
[`VTreeExt` := VTree bundled to extensional equality of (chains, henV, leafV,
nsLeaf) — T-E9's tuple; E-phase picks bundling vs Setoid.] moves_ref: 7579–7589
"(ONE-F) … f HAS exactly one tree, the tree exactly one shape … No
reciprocal/Möbius weights w(f, η) exist or are needed." INDEPENDENT of TREE-EXP
(7580–7581). deps: T-E9. sketch: existence = Decided's witness; uniqueness = T-E9.
NO hsib, NO hjcm — totality + choice-freeness alone. hypothesis_fields: none.

**T-F2 `MovesT.preHalt_dict_ptwise` · `F2_dictPtwise.lean` · hard — REV 2 (Fable
GAP-5): the missing hypothesis fields are IN — `heta` (ETA-LOC) and `hib` (InBox
supply); the count's surjectivity leg is now provable.**
```lean
theorem preHalt_dict_ptwise {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (Tr : VTree p F) (x : Box p m) (hfib : Tr.fiberAt T χ x) :
    Nat.card {i : PrefIdx n pol P //
        x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = Tr.chainCount n P
```
moves_ref: 7590–7603 "THE DICTIONARY, RESTRICTED TO PRE-HALT MARKS: …
Σ_{η ∈ Pref^τ(P̂)} μ(S(η,⊤)) = Σ_T (# length-ℓ chains of T of shape P̂) · μ{f}."
deps: Defs §2.8, T-F0, T-E9, MovesD (D4R_CYL, ClassFiberWelldef AS HYPOTHESES —
their proof for the canonical model is T-D5/T-D6). sketch: hcyl converts
"x ∈ S.fiber i" to tree membership at reprOf i; T-F0 + PreHalt cut to the pruned
tree = Tr.chains (fiberAt clause (i)); the bijection i ↦ its chain — injective by
hwd, SURJECTIVE by heta + hib (a chain H of Tr matching P̂ lies in PrefSet — hib
supplies InBox — and heta carries membership to the class representative, so its
class i has x ∈ S.fiber i: the leg rev 1 could not close). hypothesis_fields:
`hcyl`, `hwd` (the W4-3 pins, HERE consumed), `heta`, `hib` (HC-2-owned, §0).

**T-F3 `MovesT.preHalt_dict_sum` · `F3_dictSum.lean` · medium**
```lean
theorem preHalt_dict_sum {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (𝒯 : Finset (VTree p F)) (hpart : PartitionsDecided 𝒯 T χ) :
    ∑ᶠ i : PrefIdx n pol P,
        Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x}
```
moves_ref: 7601–7606. deps: T-F2, T-E13, T-F1. sketch: double count {(i, x)} both
ways; per-x the inner count is T-F2 at x's unique tree (T-F1). hypothesis_fields:
hcyl/hwd/heta/hib (via T-F2); `hpart` (the finite family covering the decided slice
at fixed level — E-phase derives from T-E11's stability or takes the finite-level
slice as the summation domain).

**T-F4 `MovesT.belowHalt_decomp` · `F4_belowHalt.lean` · easy — REV 2 (Codex 18):
the note's EXACT below-halt decomposition, not an inequality.**
```lean
theorem belowHalt_decomp {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m) :
    S.mult x
      = Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      + Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ ¬ PreHalt (reprOf i)}
```
+ the ≤ corollary (rev 1's form) kept as `belowHalt_excess`. moves_ref: 7606–7611
"The unrestricted total … is ≥ this, WITH EXCESS EXACTLY THE BELOW-HALT MARKS —
§D4-R bookkeeping that NO consumer may convert to a per-f quantity without first
restricting to Pref^τ. Conversion then runs through TREE-EXP's fiber expansion
ONLY." deps: Defs §2.8, MovesD (Presented.mult = the mark count). sketch: classical
partition of the finite index subtype by `PreHalt (reprOf i)`. THE FENCE rides in
the docstring: the conversion ban (the pass-8 critical-1 channel, closed by
display). hypothesis_fields: none.

### Layer D — the seam-discharge units [14 units]

**T-D1 `MovesT.eligibleT_apparatus` · `D1_eligible.lean` · medium**
```lean
theorem eligibleT_iff_child (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) (hmem : T.mem o x) : T.child o ν x ↔ eligibleT T CA o ν x
theorem eligibleT_cell_data (T : TreeModel p F n N m pol) (CA : …) (o ν x x')
    (h : CA.cellOf o x = CA.cellOf o x') :
    eligibleT T CA o ν x ↔ eligibleT T CA o ν x'
```
moves_ref: MovesD §2.5 W4-1(c) "`eligible` becomes a DEFINED predicate over MovesT's
cell/branch-set vocabulary; `child_iff` then a THEOREM-obligation of HC-2" + §T.1
(c1) 7093–7100. deps: Defs §2.9. sketch: first = `CA.child_cell` verbatim; second =
cellOf-factoring. HONEST SCOPE (rev 2, Codex 19): these theorems hold over ANY
CellAssign — the definitional leg of W4-1; the CANONICAL instance is HC-2's BY THE
CONTRACT'S OWN (c) CLAUSE (see §5's status column). hypothesis_fields: `CA` (the
canonical instance: HC-2's SideReads surface via `WallAReconciled`, fenced Q1/Q2).

**T-D2 `MovesT.eligible_nonvacuity` · `D2_eligGate.lean` · medium — REV 2
(Codex 19/20): the GENERAL rejection theorems join the toy gate — the interface
itself, not just the toy, rejects the degenerate readings.**
```lean
theorem no_childless_vacuity (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (h : ∃ o ν x, T.mem o x ∧ T.child o ν x) :
    ∃ o ν x, eligibleT T CA o ν x
theorem cellOf_nonconstant (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (h : ∃ o ν x x', T.mem o x ∧ T.mem o x' ∧ T.child o ν x ∧ ¬ T.child o ν x') :
    ∃ o x x', CA.cellOf o x ≠ CA.cellOf o x'
theorem eligible_nonvacuity_toy : ∃ (T : TreeModel …toy…) (CA : CellAssign …)
    (o ν x), eligibleT T CA o ν x ∧ RejectsRootOnlyChildless T CA
```
[`RejectsRootOnlyChildless` := on the toy realizable input, the root-only childless
tree FAILS `fiberAt`.] moves_ref: MovesD §2.5 W4-1(b) "NO `eligible := child`
vacuity (Codex#7 c.5) … eligibility is CELL data, never f-data (L5)." deps: T-D1,
Gates layer. sketch: first from child_cell; second: cells equal would force equal
branch sets, contradicting the child split — so `CellAssign`'s TYPE rejects
constant-cellOf on any T with a genuine branch distinction (the Codex-20 degeneracy,
now a theorem); toy leg via the gate architecture (surrogate + bridge). SCOPED
PUSH-BACK, recorded: the ALL-(ns) childless model (every realized state no-side) is
NOT rejectable — it is a lawful τ-ns configuration, not a degeneracy; what the
demands exclude is `eligible := child`-style vacuity and constant cells, both
handled above. hypothesis_fields: none (concrete instances).

**T-D3 `MovesT.verdictModel_inst` · `D3_verdictModel.lean` · hard [split D3a/D3b]**
```lean
noncomputable def vModelOf (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hdi : BranchDichotomy T) (hvc : VdictCellData T CA) (capData : …) :
    VerdictModelT T CA χ
```
THE RE-KEY (W4-2(c)): `VerdictModelT` is §2.9's DISPLAYED structure — every rev-8
field accounted by the §2.9 crosswalk (Codex 20's repair). vdict := the τ emission
(some (irrVerdictOf H) on IrrHalts; some (nsVerdictOf H) on NsHalts; none else);
halt_iff from T-V5/T-V6 (GIVEN hdi); vdict_cell from `hvc` (τ reads cell data —
the (c1) typing, an HC-2-owned supply over the canonical CA); rootVdict :=
henPayload χ with T-C1 discharging rootVdict_cell; capHen := 1 (T-C1); capIrr :=
capIrrOf ∘ S.jet (T-C2 — N-FREE, the cross-level demand); NO ns cap (§0 refutation
record — the ADMITTED amendment, W4-2(b)(ii)). moves_ref: MovesD §2.5 W4-2 entire;
§T.1 (c1)/(c2) 7093–7120; §T.2 per-clause statuses. deps: T-V5, T-V6, T-V7, T-C1,
T-C2, Defs §2.9. difficulty: hard (D3a structure + vdict/halt_iff; D3b caps).
hypothesis_fields: `hdi` (KB-TOT), `CA`, `hvc`, per-leaf cap data (T-C2's Presented
faces). NON-DEGENERACY GATE: T-G1 instantiates vModelOf on the toy and checks a
non-constant vdict (surrogate + bridge — the W4-2(b)(i) demand as a build-time
check, with T-V7's `vdAt_nontrivial` the type-level face).

**T-D4 `MovesT.cellLevel_local` · `D4_cellLevel.lean` · medium**
```lean
theorem cellLevel_local_sound (T : TreeModel p F n N m pol) (CA : …)
    (o : Option (History p F)) (hlev : CA.cellLevel o = siteLevel n o)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, CA.levelOf c < siteLevel n o → x c = x' c) :
    CA.cellOf o x = CA.cellOf o x'
theorem capEnvelope_cellLocal_false : ∃ …, ¬ CapEnvelopeCellLocal …
```
moves_ref: MovesD §2.5 W4-2(b)(ii) — the withdrawn cap-envelope `cell_local`
replaced at the per-state level (`siteLevel` NOW DEFINED, §2.5 — rev 2, Fable
GAP-2). deps: Defs §2.5/2.9, Gates toy. sketch: soundness is CA.cell_local
rewritten; the falsifier is a 2-coordinate toy witness (surrogate + bridge) — the
(b)/(c) conflation exhibited, closing Codex#7 c.6 BOTH directions.
hypothesis_fields: none.

**T-D5 `MovesT.d4rcyl_canonical` · `D5_d4rcyl.lean` · medium — REV 2 (Fable CRIT-4,
Codex 22): the hypothesis is the NAMED `RunKey` with the ∀-jet OUTSIDE the iff; the
rev-1 quantifier error (∀-J-inside cannot yield the per-jet ⇒ leg) is dead.**
```lean
theorem d4rcyl_canonical {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (hkey : RunKey T P) :
    D4R_CYL S T
```
moves_ref: MovesD's pinned Prop docstring "S(η,⊤) = {f : η ∈ T_can(f)} … Lean proof
EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus" + W4-3(c). deps: MovesD.Defs,
Defs §2.9 (RunKey). sketch: unfold D4R_CYL; at class i, `hkey` at reprOf i
(∈ PrefSet) and J := S.jet i gives the iff DIRECTLY — both legs per jet, no
jet-independence needed (that was rev 1's circularity; jet-independence of the
locus now FALLS OUT: any two jets' top strata equal the same membership event).
hypothesis_fields: `hkey : RunKey` (RUN-KEY — the typed HC-2 surface, §0; NAMED
package per the typed-package discipline, Codex 22).

**T-D6 `MovesT.cfw_canonical` · `D6_cfw.lean` · hard**
```lean
theorem cfw_canonical {P : Shape n} (T : TreeModel p F n N m pol)
    (hkey : RunKey T P) (heta : EtaLoc T P) :
    ClassFiberWelldef p F n N m pol P
```
moves_ref: MovesD ClassFiberWelldef docstring "one η-class, one classifier locus,
over ALL representatives and ALL jets (§C L4's semantic content)" + W4-3(c). deps:
MovesD.Defs, Defs §2.9. sketch: hkey (per representative, per jet) equates every
jet's top stratum with the representative's membership event; heta equates the
membership events across one class; hence all loci of one class agree — the
same-H face AND the cross-representative face both from the two named Props (rev
1's "hkey both ways per J" circularity gone). hypothesis_fields: `hkey` (RUN-KEY),
`heta` (ETA-LOC) — both owner HC-2, both named in §0.

**T-D7 `MovesT.np_id` · `D7_npid.lean` · hard [pre-approved split D7a/D7b] — REV 2
(Codex 24): the ∀-jet quantifier is the CONTRACT'S — no `hJ : J = S.jet i`
weakening.**
```lean
theorem np_id {P : Shape n} (i : PrefIdx n pol P)
    (J : JetSetup (reprOf i) n N m) :
    transportedLevels J (topLocus p m) = bandLevels (P : ShapePrefix) n
```
[`transportedLevels` := the level set of J's pinned equations at Z = ⊤;
`bandLevels` := the levels below NPband where `bandS` fires — E-phase types both
Finsets against MovesC's `totalPins` support and MovesD's `bandS`. The statement is
W4-4(a) VERBATIM: "∀ (i : PrefIdx n pol P) (J : JetSetup (reprOf i) n N m), (the
level set of J's pinned equations at Z = ⊤) = (the bandS levels below NPband)".]
moves_ref: MovesD §2.5 W4-4(a)/(c) "NP-ID becomes a wave-4 theorem from mstar_eq +
fresh_band/fresh_cover + D8/D4b over the MovesT-presented classes." deps:
MovesD.D8_bandShape, MovesD.D4b_chartCount, MovesC (mstar/fresh apparatus), T-V8.
sketch: D7a (⊆): every pinned equation sits in a fresh band at its read
(fresh_band/mstar_eq — per-J theorems, so the ∀-J form is the natural strength);
D7b (⊇): every band level is hit (fresh_cover + D8). Landing this unit DELETES
D4R4_all's conditionality pointer (their manifest row); T-C2's NPband corollary
consumes D7a EXPLICITLY (rev 2). hypothesis_fields: none beyond the class binders
(the jet is UNIVERSALLY quantified — the contract's own strength).

**T-D8 `MovesT.vtree_pathOrder` · `D8_pathOrder.lean` · medium**
```lean
theorem vtree_pathOrder (Tr : VTree p F) :
    (∀ H, H.IsPrefixOf H) ∧
    (∀ H₁ H₂ H₃, H₁.IsPrefixOf H₂ → H₂.IsPrefixOf H₃ → H₁.IsPrefixOf H₃) ∧
    (∀ H₁ H₂, H₁.IsPrefixOf H₂ → H₂.IsPrefixOf H₁ → H₁ = H₂) ∧
    (∀ H₁ H₂ H, H₁ ∈ Tr.chains → H₂ ∈ Tr.chains → H ∈ Tr.chains →
      H₁.IsPrefixOf H → H₂.IsPrefixOf H → (H₁.IsPrefixOf H₂ ∨ H₂.IsPrefixOf H₁))
```
moves_ref: MovesS §W4-SYNC TreeIface's ROOT-PATH ORDER LAWS (path_refl/trans/
antisymm/total). deps: Defs §2.5. sketch: `List.IsPrefix` facts. This makes `VTree`
a lawful TreeIface CARRIER; entrance/deep-split/blockOf semantics are [1v]/MovesV
vocabulary and stay THERE (§5 S-5, honest status). hypothesis_fields: none.

**T-D9 `MovesT.shape_countable` · `D9_shapeCtbl.lean` · easy**
```lean
instance : Countable ShapePrefix
instance (n : ℕ) : Countable (Shape n)
```
moves_ref: infrastructure for S-7's `ctbl`. deps: MovesD.Defs. sketch: finite
tuples of countable data; lists; subtype. hypothesis_fields: none.

**T-D10 `MovesT.classTree_countable` · `D10_classTreeCtbl.lean` · medium**
```lean
def ClassTree (n : ℕ) (pol : CanonPolicy p F) : Type _ :=
  {ct : Finset (Σ P : Shape n, PrefIdx n pol P) × (… leaf verdict data in VdAt …) //
    PrefixClosed ct}   -- finite prefix-closed class-address trees [E-phase: the
                        -- verdict-data component per leaf address]
instance : Countable (ClassTree n pol)
```
moves_ref: MovesS §W4-SYNC S-7. deps: T-D9, T-V7, MovesD (PrefIdx finiteness via
the E-layer encodings). sketch: countable-of-finite fibers over countable Shape
data. hypothesis_fields: none.

**T-D11 `MovesT.fibOf_keying` · `D11_fibOf.lean` · medium — REV 2 (Codex 32): the
nonemptiness CARRIER is typed here so S-7's non-vacuity demand has a MovesT-side
object; the toy witness is T-G1's.**
```lean
noncomputable def fibOf (ct : ClassTree n pol) : VTree p F   -- reprOf per address
def Realizes (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (Tr : VTree p F) : Prop := ∃ x, Tr.fiberAt T χ x
theorem fibOf_fiber_disjoint …   -- distinct ClassTrees, disjoint fibers (T-E9 + hwd)
theorem fibOf_partition …        -- the ONE-F partition face over `Realizes` trees
```
moves_ref: S-7's keying demand + "βmeas = 0 must not trivialize (fiber nonemptiness
where βmeas > 0)" — the LAW is MovesS's consumption over presented instances; the
CARRIER (`Realizes`) and the keying are here; the toy nonemptiness witness is
T-G1's `toy_fiber_ne`. deps: T-D10, T-E9, T-F1, T-D6. hypothesis_fields: `hwd` (via
T-D6's conclusion or directly as the MovesD pinned Prop).

**T-D12 `MovesT.packages_rekey` · `D12_packages.lean` · easy — REV 2 (Codex 25/28,
Fable GAP-4): the ACTUAL contract structures are DECLARED VERBATIM (field names and
order from MovesS §W4-SYNC's displays — no parallel "Values" carriers), instantiated
with [3t] fields := MovesT statements and non-[3t] fields as PARAMETERS; the W1m
premise row is a typed display; the ns_null finite-face rider is quoted.**
```lean
-- DECLARED VERBATIM from MovesS §W4-SYNC (the contract's own field rosters; MovesS
-- wave 5 re-points its contract here or moves the declaration — a PROCESS note in
-- both corpora's manifests):
structure XRBPackage where
  xhd_w : Prop ; xhd_u : Prop ; xhd_d : Prop ; xhd_s : Prop
  jc_inv : Prop
  sib : Prop ; jc_multi : Prop
  tb_cap : Prop ; vp : Prop
  rel2_a : Prop ; rel2_b : Prop ; rel2_d : Prop
  ns_null : Prop
structure RS1GivenPackage where
  tree_exp_fin : Prop ; tree_exp_ns : Prop ; tree_n : Prop ; one_f : Prop
  sib : Prop ; tb_cap : Prop ; vp : Prop ; pci : Prop
  rel2_a : Prop ; rel2_b : Prop ; rel2_c : Prop ; rel2_d : Prop ; rel2_e : Prop
structure Wsh17Package where
  c15_volumes : Prop ; cts_counts : Prop ; sib_count : Prop

def rs1GivenOfMovesT (T : TreeModel p F n N m pol) (CA : …) (χ : …)
    (rel2_a rel2_b rel2_c rel2_d rel2_e : Prop) : RS1GivenPackage := {
  tree_exp_fin := (T-E8's statement Prop), tree_exp_ns := (T-E12's),
  tree_n := (T-E11's), one_f := (T-F1's), sib := SibCount T CA,
  tb_cap := (T-C1 ∧ T-C2 statements) ∧ NsAmendedPair …,
  vp := VPPinned T …,     -- (c1)/(c2)/(c3-a) discharged + VP-SOUND's two cites as
                           -- the REMAINDER (7634–7635)
  pci := PCI T CA, rel2_a := rel2_a, … }
def xrbOfMovesT (T : …) (CA : …) (χ : …) (xhd_w xhd_u xhd_d xhd_s jc_inv
    rel2_a rel2_b rel2_d : Prop) : XRBPackage := {
  sib := SibCount T CA, jc_multi := (T-E8's per-site hjcm Prop, ∀-trees form),
  tb_cap := …, vp := …, ns_null := (T-C7's statement Prop), xhd_w := xhd_w, … }
def wsh17OfMovesT (T : …) (CA : …) (c15 cts : Prop) : Wsh17Package :=
  { c15_volumes := c15, cts_counts := cts, sib_count := SibCountShallow T CA }

/-- the W1m addendum's premise row, TYPED (rev 2, Codex 28): RS.1-MARKED's
re-keying must carry the S.2 GIVEN list AND the nine-input ledger; the ledger slot
is a Prop parameter here (its REAL object is MovesS's `LedgerIV`, typed in MovesS's
core — bound at MovesS's re-key; owner-tagged). -/
def w1mObligation (Π' : RS1GivenPackage) (ledger_iv : Prop)
    (concl : Prop) : Prop :=
  (Π'.tree_exp_fin ∧ Π'.tree_exp_ns ∧ Π'.tree_n ∧ Π'.one_f ∧ Π'.sib ∧
   Π'.tb_cap ∧ Π'.vp ∧ Π'.pci ∧
   Π'.rel2_a ∧ Π'.rel2_b ∧ Π'.rel2_c ∧ Π'.rel2_d ∧ Π'.rel2_e) →
  ledger_iv → concl
```
NS_NULL RIDER (Fable GAP-4, quoted wherever `ns_null` is consumed): the field's
value is T-C7's FINITE-LEVEL truncated-ratio statement; the note's profinite
μ-claim is NOT stated in Lean — MovesS's re-audit consumes the finite face or adds
its own bridge; the S-2 row (§5) carries this rider verbatim. moves_ref: MovesS
§W4-SYNC S-9 + the [3t] owner tags + both RATIFICATION ADDENDA. deps: layer
statements AS PROPS. hypothesis_fields: none (defs of Props; non-[3t] fields are
parameters keeping their owner tags — [2b]/[2r]/[1v]).

**T-D13 `MovesT.treeIface_carrier` · `D13_ifaceGate.lean` · medium [PARTIAL — §5 S-11]**
```lean
noncomputable def treeIfaceCore (𝒯 : Finset (VTree p F)) (h𝒯 : 𝒯.Nonempty) :
    TreeIfaceCore …  -- Tree := ↥𝒯, Node := chains+root, onPath := prefix order,
                     -- order laws := T-D8; finN from hfin; node_ne from root
```
moves_ref: MovesS §W4-SYNC S-11. deps: T-D8. sketch: pack carrier + order laws.
HONEST SCOPE: `isEntrance`/`isDeepSplit`/`blockOf`/`entδ`/`shapeOf`-into-F.Sh are
CTS/[1v] vocabulary — MovesV's; the CARRIER CORE only; S-11's full instance + W7
check wait on MovesV (§5 status: PARTIAL). hypothesis_fields: none.

**T-D14 `MovesT.chain_charge_ledger` · `D14_chainCharges.lean` · medium — NEW at
REV 2 (Codex 31): the S-6 deliverable made real — the per-entered-path read list
with its charge identities.**
```lean
noncomputable def chainReads (Tr : VTree p F) (H : History p F) :
    List (History p F) :=
  (List.range H.nodes.length).filterMap fun r =>
    (prefixAt H (r+1)).filter (· ∈ Tr.chains)   -- the nonempty prefixes = the
                                                 -- reads along H [E-phase plumbing]
theorem chain_charge (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : …) (χ : …) (L : SiteLedger Tr T CA χ) (H : History p F)
    (hH : H ∈ Tr.chains)
    (hone : ∀ H' ∈ chainReads Tr H, (L.sys H').2.oneSide) :
    Nat.card ↥(stateEvent T (some H))
        * p ^ ((chainReads Tr H).map (L.siteExp ·)).sum
      = Nat.card ↥(stateEvent T none)
```
moves_ref: MovesS §W4-SYNC S-6 "tie ReadLedger to the tree — a per-entered-path
assignment RL with charges = the tree's read masses" — the MovesT half: the read
list (`chainReads`) and the per-read charges (`L.siteExp`) with the chained mass
identity (Theorem C(b)'s closed form along a run = T-E6 iterated). THE (BDY) SPLIT
(Wcharge/βcharge at the first-entrance index fe) is NOT here — it needs
`isEntrance` (MovesV vocabulary); §5 S-6 status PARTIAL, the residual quoted.
deps: T-E6, Defs §2.5. sketch: induction along the chain, T-E6 at each step with
E := univ. hypothesis_fields: `L`; `hone` (branching chains route through T-E7/E8
instead — recorded).

### Layer G — sealed-number gates (the T-n3 discipline at Lean scale) [2 units]

GATE ARCHITECTURE (REV 2, Fable GAP-6 — binding on every `decide` below): the real
Props quantify over `Set (Box p m)`, `History p F`, `Node p F` — types carrying
`Polynomial ℤ_[p]` data, NOT decidable. Every gate therefore ships as a PAIR:
 (a) a FINITE SURROGATE — the same identity over an ENUMERATED roster (the toy's
   realized states/cells/events as explicit `Finset`s over a `DecidableEq` toy
   carrier) — closed `by decide`;
 (b) a HAND BRIDGE — a classification lemma (the toy's realized states/ContFiber
   events are exactly the enumerated ones) transporting (a) to the real Prop.
No `by decide` is claimed on a statement with a `Set`/`History` quantifier.

**T-G1 `MovesT.toy_treeExp_gate` · `G1_toyGate.lean` · medium [pre-approved split
G1a surrogate-decide / G1b classification bridge]**
```lean
def toyModel : TreeModel 2 (ZMod 2) … := …   -- a 2-adic, ≤ 8-coordinate box model
def toyCA : CellAssign 2 (ZMod 2) … toyModel := …
theorem toy_gate : (Nat.card ↥{x | toyTree.fiberAt toyModel toyχ x}) * 2 ^ toyA
    = 2 ^ toyM                                -- via G1a decide + G1b bridge
theorem toy_sib : SibCount toyModel toyCA     -- provable ON THE TOY: the rev-2
  -- kernel quantifies over the toy's FINITELY MANY cell events (not all subsets —
  -- the rev-1 form was FALSE on every branching toy, Fable CRIT-1's tail)
theorem toy_vdict_nonconstant : ∃ x y, toyVdict x ≠ toyVdict y
theorem toy_fiber_ne : ∃ x, toyTree.fiberAt toyModel toyχ x   -- S-7's witness
theorem toy_e5_instance : …   -- the rev-2 E5 exponent shape at t = 1 on the toy
  -- (the CRIT-3 regression gate: numTracks, not numTracks − 1)
```
moves_ref: §T.6's gate DISCIPLINE; the Fable-confirm p = 2 census "N(fiber) = 8 =
2^{9−6}, 0/10,000 stability" (9208–9209) is the Lean-scale target — the toy encodes
a 2-adic depth-1 split with the SAME ledger shape. deps: Defs, T-E8's statement
(gate checks the STATEMENT's instance, not via the theorem). sketch: hand-build the
toy + enumerate; G1a decides the surrogate identities (incl. the SibCount kernel at
each of the toy's cell events); G1b classifies. PASS ≠ closing (SIB) — scope
recorded verbatim (7699–7700). DAY-ONE DUTY (build order §6): if
`fiberAt`/`SibCount` over-strengthen, the toy dies first — the U31 lesson.
hypothesis_fields: none.

**T-G2 `MovesT.toy_oneF_gate` · `G2_toyOneF.lean` · easy**
```lean
theorem toy_oneF : ∀ x, ToyDecided x → ∃! t ∈ toyTrees, toyFiber t x
theorem toy_belowHalt_pos : ∃ x, 0 < toyBelowHaltExcess x   -- the dictionary gap
```
moves_ref: T-n3 Layer C's ONE-F face 7745–7752 ("marked 64 / per-f 58 / gap 6" at
census scale; the Lean toy checks the ∃!-partition shape + a below-halt excess
instance > 0 — the gap EXHIBITED, not just typed). deps: T-G1 defs (surrogate +
bridge). sketch: decide on the surrogate; bridge. hypothesis_fields: none.

---

## §4 THE Q-FENCE — Q1/Q2 discharge DESIGN (fenced on Asvin's sign-off; task #44)

PROJECT_STATE 28j's queue items Q1/Q2 touch the FROZEN MovesC interface, so per the
statement fence NOTHING here builds until the sign-off. This section is the DESIGN
the charge asked for. REV 2 NOTE: these two rows are QUEUE-ITEM DESIGNS, NOT seam
entries — they do not count toward §5's discharge tally (Codex 35, Fable GAP-1) —
and the corpus-side fence is now TOTAL: after T-V8's restatement onto
`NodeDataLawful`, NO unit of this corpus premises `HistoryCoherent` (rev 1's T-V8
did, unfenced — the Codex-9 violation; removed).

**Q1 — the HistoryCoherent child re-key at the regraded value + the 2-node ReadsOf
gate.** DESIGN: `CellAssign.child_cell` (§2.9) is written against `T.child`, NOT
against `HistoryCoherent`'s child clause — the corpus is INSENSITIVE to the re-key's
exact constant: when the child keying moves to the regraded value, only HC-2's
CellAssign INSTANCE changes; every MovesT unit is stated over the abstract CA and
survives verbatim. The 2-NODE READSOF GATE becomes a Layer-G unit spec (pre-written,
NOT built): `G3_q1Gate.lean` — a two-node history (root + one steep e·g ≥ 2 read)
with a concrete box member, checking `T.mem (some H₂) x` through the re-keyed
instance (surrogate + bridge, per the gate architecture) — the non-vacuity witness
for the steep leg V10 showed is currently inconsistent. FENCE: G3 is in the manifest
as `status: "fenced-Q1"`; building it before sign-off is a statement-fence event.

**Q2 — U21's RunVertexPin (the D.7(v)-warranted `child_dig_frame` pin).** DESIGN:
`eligibleT`'s semantic content enters through `CA.branchSetOf ∘ CA.cellOf`; the
vertex pin is exactly the clause making `cellOf`'s digit frame at a child read
WELL-DEFINED. MovesT reserves the NAMED conjunct slot: `CellAssign` gains
(post-sign-off) a field `vertex_pin : ∀ o ν x, …` transcribing D.7(v)'s warrant
(the HC-1 V10/V9 kernel family is PROVED — the pin's mathematical content is
machine-checked; what awaits sign-off is its INTERFACE placement on the frozen
MovesC types). Until then: `CellAssign` as in §2.9 (no vertex field); HC-2's
canonical instance carries the pin internally; `WallAReconciled` (§2.9) is where
clause (vi)'s read-off meets the re-key. FENCE: adding the field is flagged
`fenced-Q2` in the manifest, sign-off required.

---

## §5 SEAM ACCOUNTING — every consumed contract entry, rebuilt entry-by-entry
## against the contract texts (REV 2 — Codex 19–35, Fable GAP-1)

REV-2 SEMANTICS (replacing rev 1's "discharging" claim): a row is **DISCHARGED**
only where a unit's STATEMENT is the contracted obligation over the consumed corpus
objects and the unit is in-corpus provable; **REDUCED** where the obligation is
derived from a NAMED typed bridge Prop whose instance has a recorded owner;
**SUPPLIED** where MovesT's side of a shared entry is delivered but the entry's own
DONE criterion ("re-keyed against the real corpora and re-audited" — MovesS
§W4-SYNC preamble) sits with the owner; **NOT-OURS** where the contract's own text
assigns the leg elsewhere (quoted per row). NO row counts as done that isn't.

COUNT (corrected — Codex 35, Fable GAP-1): **19 seam entries** = 4 (MovesD W4-1…4)
+ 11 (MovesS S-1…S-11) + 2 (MovesS ratification addenda) + 2 (HC-2 Walls A/B);
PLUS 2 fenced Q1/Q2 queue-item DESIGNS (§4 — not seam entries, not discharge
targets). Total rows below: 21. Status tally over the 19:
**2 DISCHARGED (W4-4, S-9/[3t] leg) · 3 REDUCED (W4-1, W4-2, W4-3) · 12 SUPPLIED/
PARTIAL (S-1, both addenda, S-2, S-5, S-6, S-7, S-8, S-10, S-11, Wall A — plus
S-4's recorded fence) · 2 NOT-OURS (S-3, Wall B).**

**(A) MovesD blueprint §2.5 (4 entries):**

| entry | contract text honored | MovesT units | status + residual (owner per the contract's own clause) |
|---|---|---|---|
| **W4-1** `eligible`/`child_iff` | (c): "`eligible` becomes a DEFINED predicate over MovesT's cell/branch-set vocabulary; `child_iff` then a THEOREM-obligation of HC-2"; (b): no `eligible := child` vacuity, cell data never f-data | Defs §2.9 (`CellAssign`, `eligibleT`, `WallAReconciled`) + T-D1 + T-D2 (incl. the GENERAL `no_childless_vacuity`/`cellOf_nonconstant` rejection theorems — rev 2) | **REDUCED**: the definitional leg + the (b)-demands are theorems here; `child_iff` for the CANONICAL instance is HC-2's by (c)'s own text (pin: `WallAReconciled`; steep legs fenced Q1/Q2). Scoped push-back on record (T-D2): the all-(ns) childless model is lawful τ-ns, not a rejectable degeneracy |
| **W4-2** VerdictModel ENTIRE | (a)'s FULL field roster → §2.9's `VerdictModelT` + crosswalk (every rev-8 field accounted — rev 2, Codex 20); (b)(i) no degenerate satisfiability → `vdAt_nontrivial` (T-V7) + `cellOf_nonconstant` (T-D2) + toy gates; (b)(ii) `cell_local` replaced at the per-state level (T-D4 sound + falsifier); cross-level cap uniformity → `capIrrOf` N-FREE BY TYPE (T-C2, Codex 21); (c) re-derived from VP-1/VP-2 + TB-CAP | T-D3 (`vModelOf`) + T-D4 + T-V5/V6/V7 + T-C1/C2 | **REDUCED**: structure, vdict values, halt_iff, both caps, both locality laws are in-corpus theorems/defs; residuals NAMED: `hdi` (KB-TOT — HC-2/D4R0K), `hvc` (τ-cell-data over the canonical CA — HC-2), the canonical CA itself (HC-2); ns stays cap-FREE (the ADMITTED (b)(ii) amendment, refutation record §0) |
| **W4-3** D15's `D4R_CYL` + `ClassFiberWelldef` | (b): "its proof needs kernel (a)/(b) apparatus + Thm C(a) — wave-4"; (c): "become wave-4 THEOREMS over the MovesT tree; D15 builds then" | T-D5 + T-D6, from the NAMED `RunKey`/`EtaLoc` (rev 2: ∀-jet outside the iff — the rev-1 quantifier error is dead); consumed downstream by T-F2/F3, T-D11 | **REDUCED**: both Props are theorems here FROM RunKey + EtaLoc; those two bridge Props are HC-2's Wall-A surface (owner recorded, §0). D15 builds once HC-2 lands them |
| **W4-4** NP-ID | (a)'s typed form stated VERBATIM (∀ i, ∀ J — rev 2, Codex 24: no `S.jet` weakening); (c): "becomes a wave-4 theorem from mstar_eq + fresh_band/fresh_cover + D8/D4b" | T-D7 (`np_id`, split D7a/D7b) | **DISCHARGED** (statement = the contract's (a), in-corpus provable from the built MovesD/MovesC apparatus); landing deletes D4R4_all's conditionality pointer; T-C2's NPband corollary consumes D7a explicitly |

**(B) MovesS blueprint §W4-SYNC (11 entries + 2 addenda).** The DONE criterion is
the contract's own: "a seam entry is DONE only when re-keyed against the real
corpora and re-audited" — accordingly NO row below claims DONE; the column records
MovesT's side vs the owner's remainder.

| entry | MovesT's side (delivered) | units | status + owner remainder |
|---|---|---|---|
| **S-1** W1_RS1SH (+S-1e, S-1m) | the [3t] premise row's REAL statements; the ACTUAL `RS1GivenPackage` declared verbatim + instantiated (rev 2, Codex 25) | T-D12 | **SUPPLIED**: fields re-keyed; the RS.1 derivations + the re-audit are MovesS wave 5 (Codex 26 honored: NOT counted done) |
| — **addendum (W1 circularity)** | the enabling half: TREE-EXP/TREE-N/ONE-F exported as SEPARATE named theorems (T-E8/E11/F1) — non-circular derivation inputs now exist | T-E8, T-E11, T-F1 + T-D12 | **SUPPLIED / OPEN-AT-OWNER**: the addendum's demand — "the re-keying must DERIVE RS.1-SH from the MovesT tree assembly, not restate it" — is an act of MovesS's re-key; unrepairable from this side (Codex 27 recorded, not claimed fixed) |
| — **addendum (W1m nine-input ledger)** | the premise row TYPED incl. the ledger slot: `w1mObligation` (rev 2, Codex 28) | T-D12 | **SUPPLIED**: the slot binds to MovesS's real `LedgerIV` at its re-key (owner-tagged) |
| **S-2** W2_xrb | XRBPackage declared verbatim; [3t] fields := MovesT statements — **with the ns_null FINITE-FACE RIDER quoted at the field** (rev 2, Fable GAP-4): T-C7 is the truncated-ratio limit, NOT the profinite μ-claim; MovesS's re-audit must consume the finite face or add its own bridge | T-D12 | **SUPPLIED**: xhd_*/jc_inv ([2b], MovesV), rel2_* ([2r]) stay parameters with owner tags |
| **S-3** W3_recursion | nothing beyond S-1/S-2's fields — and honestly so | — | **NOT-OURS** (rev 2, Codex 29 re-statused): the demanded re-keyed premise `hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …` is stated over MovesS's `RS1Meas.βmeas` — not stateable in this corpus; the contract's re-key charge sits with MovesS ("re-keyed form: (hxrb : …) → …") |
| **S-4** W4_x3 | recorded posture only: MovesT is X.3-free (§0) | — | **NOT-OURS** ([5]/MovesX's package; consumed-item pin unchanged) |
| **S-5** W7_cutWD + TreeIface | the CARRIER: VTree + the four order laws (refl/trans/antisymm/total) | T-D8, T-D13 | **PARTIAL** (rev 2, Codex 30): the load-bearing re-keyed clause — "∀ t ν, TI.isDeepSplit t ν → ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν" — needs `isEntrance`/`isDeepSplit` (CTS/[1v] vocabulary, MovesV); quoted so the residual is checkable |
| **S-6** W8_bdy + ReadLedger | the tree-tied charge carrier IS NOW BUILT (rev 2, Codex 31): `SiteLedger` (§2.5) + `chainReads`/`chain_charge` (T-D14) — per-entered-path read list, per-read exponents, the chained mass identity | Defs §2.5 + T-D14 | **PARTIAL**: the (BDY) SPLIT (Wcharge = reads ≤ fe, βcharge = reads > fe) needs the first-entrance index (MovesV's `isEntrance`); the WshVal/βmeas feeds are MovesS's consumption |
| **S-7** W10_convergence + FiberIface | fibOf keying, countability, disjointness, ONE-F partition + the NONEMPTINESS CARRIER `Realizes` and the toy witness `toy_fiber_ne` (rev 2, Codex 32) | T-D9, T-D10, T-D11 (+T-E9, T-F1, T-G1) | **PARTIAL**: "βmeas = 0 must not trivialize (fiber nonemptiness where βmeas > 0)" is a LAW over MovesS's measured side — consumed there against `Realizes`; general realizability is genuinely open (no fake theorem) |
| **S-8** W17ii + Wsh17Package | the actual `Wsh17Package` declared; `sib_count := SibCountShallow T CA` — a DEFINED statement (§2.6), not a name | T-D12 | **PARTIAL** (Codex 33): the empty-menu exclusion (`F.Sh.Nonempty`) and the xhd_s face are MovesS/[2b]-side tie-demands — quoted, owners recorded; c15_volumes (§C/MovesC cite) and cts_counts ([1v]) stay parameters |
| **S-9** packages as registries | every [3t]-owned Prop field now has a REAL named statement AND the registry structures exist as declared types (rev 2) | T-D12 | **DISCHARGED for the [3t] leg** (the contract's whole point, per its own text); non-[3t] fields keep owner tags as parameters |
| **S-10** RS4Chain provenance | the DISCHARGE provenance objects exist as named theorems: TREE-EXP (T-E8), ONE-F (T-F1) | T-E8, T-F1 | **PARTIAL** (Codex 33): "RE-KEYING REPLACES (R46) the device-satisfied instances … by production-derived ones" — the replacement ACT is MovesS's; the CUT-WD leg is S-5's residual (MovesV) |
| **S-11** n2_treeiface | the carrier-core constructor | T-D13 | **PARTIAL** (Codex 30): "the gate's TreeIface instance + W7 check, built when TreeIface is re-keyed" — the full instance + W7 check wait on MovesV's entrance semantics |

**(C) HC-2 Wall A / Wall B seam notes (2 entries):**

| seam note | MovesT's side | units | status |
|---|---|---|---|
| **Wall A** ("deliberately the SAME semantic surface as MovesD's W4-1 `eligible`; HC-2 owns the definition; MovesT re-keys `eligible` to it in wave 4") | the re-key is executed at interface level (`eligibleT` over `CellAssign`) AND the reconciliation is now a TYPED PIN (rev 2, Codex 34): `WallAReconciled T CA ReadsOf` — branch membership ↔ the run predicate at the extended history, clause (vi)'s vertex read-off inside `ReadsOf` per HC2 §7.6 | Defs §2.9 + T-D1 | **SUPPLIED**: the pin is typed here; the canonical instance satisfying it is HC-2's (fenced Q1/Q2, §4) |
| **Wall B** (SEED-EXIST / PresentSeed) | NOT MovesT's to discharge (HC2's own "NOT HC-2's to deliver" list assigns this corpus ONLY the D4R_CYL side → W4-3). QUANTIFIER TRACE (rev 2, Codex 45): SEED-EXIST is `∀ i N, P.NP ≤ N → ∃ keys, KeysLawful (reprOf i) keys ∧ Nonempty (PresentSeed …)`; MovesT's riders consume ONLY downstream VALUES of it — `S.jet i` (a Presented family member, arising via PRESENT-EXIST = SEED-EXIST + U15), the `SiteLedger` fields (finite-level faces of `J.SHZ` counts through C4/C6 at seeded jets), and T-C7's `Jat` family. No MovesT statement quantifies over keys or strengthens the ∃-keys/`KeysLawful` shape: each rider takes the jet/family AS GIVEN DATA — the hypothesis-not-axiom pattern MovesD set | riders on T-C2/C6/C7, T-E3/E6/E8/E10/E11, T-D7 | **NOT-OURS** (recorded fence; trace supplied) |

**(D) PROJECT_STATE 28j queue (2 fenced DESIGN rows — not seam entries):**

| item | disposition |
|---|---|
| **Q1** HistoryCoherent child re-key + 2-node ReadsOf gate | discharge DESIGNED at §4 (CA-abstraction makes MovesT re-key-invariant; gate spec G3 pre-written, `fenced-Q1`); corpus-side fence now TOTAL (no `HistoryCoherent` premise anywhere — rev 2) — NOT BUILT pending sign-off |
| **Q2** RunVertexPin (child_dig_frame) | discharge DESIGNED at §4 (named additive `vertex_pin` field slot, `fenced-Q2`) — NOT BUILT pending sign-off |

---

## §6 Process, census, and honest perimeter

BUILD ORDER (hardest-hole-first inside each phase; E-phase = statements compile
with sorry bodies, then the prover fleet):
1. `Defs.lean` (§2) — then T-G1's toy SKELETON immediately (the day-one
   non-vacuity gate: if `fiberAt`/`SibCount` over-strengthen, the toy dies first —
   the U31 lesson; the rev-2 `toy_sib` is the regression gate for CRIT-1's class).
2. Layer V + T-E1/E2/E9 + T-F0/T-F1 (the unconditional core: the pin, the
   partition).
3. Layer C (T-C5 first — the one substantive new proof; its failure mode feeds
   back into the Defs of `IsLumpLocus`/`NsLumpFamily`).
4. Layer E (E3 → E6 → E4 → E5/E7 → E8 → E10/E11 → E12) + F2–F4.
5. Layer D (D1/D2/D4/D8/D9/D10/D12/D14 early — they unblock other corpora's
   wave-5 work; D3/D5/D6/D7/D11/D13 after their deps).
6. Gates T-G1/T-G2 full (surrogate + bridge); §4's G3 stays fenced.

CENSUS TARGETS: **53 units = 13 easy / 30 medium / 10 hard** (hard: T-C5, T-E5,
T-E7, T-E8, T-E10, T-E11, T-F2, T-D3, T-D6, T-D7 — escalation-risk set
pre-declared; pre-approved splits: C5a/C5b, D3a/D3b, D7a/D7b, G1a/G1b). REV-2
DELTA: +T-F0, +T-D14; T-F4 renamed `belowHalt_decomp` (exact identity). Zero
axioms; zero `sorry` in the accepted scope; every hypothesis field named in §0 or
§5. `#print axioms` per proved unit = Lean core only.

WHAT THIS CORPUS DOES **NOT** CLAIM (the note's §T.5/§T.0, restated as the
manifest's honesty block):
* no (SIB) proof, no (SIB-STEP)⟹(SIB) filtration lemma (open remainder, wave 5+);
* no (JC-multi) proof (open, census-untested; consumed PER-SITE only);
* no X.3/density form — finite/normalized counts only;
* no VP-SOUND discharge — (HEN-LIFT)/(OM-SAT) stay named Props (D4R.0-K(c)'s
  remainder = exactly {VP-SOUND's cites}, 7634–7635);
* no TB-CAP for (ns) — refuted; only (ns-lump)+(ns-null) as displayed, and
  (ns-null) ONLY at its finite-level truncated-ratio face (the T-C7/S-2 rider);
* no termination, no exhaustion, no rationality (7663);
* no marked→per-f conversion outside TREE-EXP (T-F4's fence);
* no multinomial factorization of C_T̂ (exchangeability is [1v]'s burden);
* no seam entry claimed DONE whose DONE criterion sits with an owner (§5's
  statuses are the claim's whole extent).

AUDIT CHARGE for the wave-4 re-pass (per campaign §3): faithfulness of every
`statement` against the quoted rev-7 display; non-vacuity (each hypothesis Prop
falsifiable — T-S2/T-D4's falsifiers; the toy gate day-one); quantifier exactness
(TB-CAP(irr) per (P,i) — NO cap uniform over all cells; SIBLING INDEXING — no
ordering/symmetry factor; CONDITIONING EVENTS PINNED — no free `Set` binder in any
conditional law, the rev-2 doctrine line); hypothesis-field completeness against
§0's ledger; §5's status semantics (DISCHARGED rows must have statement =
obligation; SUPPLIED/PARTIAL rows must quote their residual verbatim).

---

## §7 REV-2 DISPOSITION TABLE (the full union of both rev-1 verdicts)

Legend: **F** = fixed (statement-level repair) · **R** = redesigned (structural
rebuild) · **PB** = pushed back (scoped, with reason on record). Cross-references
where the two audits found the same defect.

**Codex criticals 1–35:**

| # | finding (short) | disp. | where |
|---|---|---|---|
| 1 | BranchDichotomy a classical tautology | **R** | §2.4 per-child saturate-or-continue law |
| 2 | PrunedMem halt test on the empty prefix | **F** | §2.4 `H'.nodes ≠ []` guard |
| 3 | fiberAt's ns leaf value unpinned | **F** | §2.2 `nsVerdictOf` + fiberAt clause (ii) |
| 4 | irrVerdictOf junk guards only asserted | **F** | T-V8 `acc_pos` conclusion |
| 5 | SibCount over arbitrary Σc/B (= Fable CRIT-1) | **R** | §2.6 pinned to `cellEvent`, B := the cell's branch set |
| 6 | T-V3 omits cluster degree/μ; `?g_of` | **F** | T-V3 restated (zipped selections; both equalities) |
| 7 | T-V5 `∨ True` (= Fable CRIT-5) | **F** | `IrrHaltsAsChild` + real duty |
| 8 | T-V6 tautology, (c2) content dropped | **R** | T-V6 per-child covering + exactly-one |
| 9 | T-V8 unfenced HistoryCoherent (Q1 violation) | **F** | `NodeDataLawful` (no child-keying clause); corpus-wide sweep clean |
| 10 | T-C2 NPband substitution IS NP-ID | **F** | cap := `capIrrOf` (jet's own N(η′,⊤)); NPband corollary consumes T-D7a explicitly |
| 11 | T-E5 off by one |rootCell| (= Fable CRIT-3) | **F** | exponent `numTracks`; E8/E11 untouched (census-verified) |
| 12–13 | JCmulti global on E7/E8/E11 (= Fable CRIT-2's scope face) | **R** | `JCmultiAt` per-site; `hjcm` over the tree's own multi-side sites |
| 14 | T-E9 false under rev-1 fiberAt | **F** | consequence of #3's repair |
| 15 | T-F1 ∃! fails | **F** | consequence of #3's repair |
| 16 | T-E10 exact law on ns-leaf trees | **F** | `NsFree` summation domain |
| 17 | PreHaltPfx box-dependent | **R** | §2.8 `PreHalt` box-free + T-F0 bridge |
| 18 | T-F4 inequality vs exact identity | **F** | `belowHalt_decomp` (exact) |
| 19 | W4-1: arbitrary CA; toy-only rejection | **F**(+scoped PB) | T-D2 general rejection theorems; all-(ns) childless model recorded NOT rejectable (lawful τ-ns); canonical instance HC-2 per W4-1(c)'s own text |
| 20 | W4-2 fields omitted; degenerate CA admitted | **R** | §2.9 `VerdictModelT` full + crosswalk; `vdAt_nontrivial` + `cellOf_nonconstant` |
| 21 | cross-level cap demand dropped | **F** | `capIrrOf` N-free BY TYPE (T-C2) |
| 22 | T-D5 hkey unnamed repackaging (= Fable CRIT-4) | **F** | NAMED `RunKey`, ∀-jet outside the iff |
| 23 | T-D6 circular on CFW | **F** | from RunKey + EtaLoc (both named) |
| 24 | T-D7 weakened to S.jet i | **F** | contract's ∀-J form verbatim |
| 25 | T-D12 parallel Values carriers | **F** | actual structures declared verbatim + instances |
| 26 | S-1 counted done | **R** | §5 status SUPPLIED; DONE criterion quoted |
| 27 | W1-circularity addendum unrepaired | **R** | §5: enabling half here; derivation OPEN-AT-OWNER (MovesS) — recorded, not claimed |
| 28 | W1m ledger omitted | **F** | `w1mObligation` typed premise row incl. ledger slot |
| 29 | S-3 hxrb premise unsupplied | **PB** | βmeas is MovesS's object — not stateable here; row re-statused NOT-OURS with the contract's re-key charge quoted |
| 30 | S-5/S-11 load-bearing clauses absent | **R** | statuses PARTIAL; missing clauses quoted verbatim with owners (MovesV) |
| 31 | S-6 ReadLedger not built | **F** | `SiteLedger` + T-D14 `chain_charge`; (BDY) fe-split residual quoted |
| 32 | S-7 non-vacuity dropped | **F** | `Realizes` carrier + `toy_fiber_ne`; the βmeas law stays MovesS's (quoted) |
| 33 | S-8/S-10 tie-demands unmet | **R** | statuses PARTIAL; each demand quoted with owner |
| 34 | Wall A unreconciled with ReadsOf | **F** | `WallAReconciled` typed pin (clause (vi) noted) |
| 35 | tally 19 ≠ 4+11+2+2+2 (= Fable GAP-1) | **F** | 19 entries + 2 fenced designs = 21 rows; tally line rewritten |

**Codex gaps 36–45:**

| # | finding | disp. | where |
|---|---|---|---|
| 36 | T-V4 bundles unfrozen equivalences | **F** | split legs, per-leg warrants |
| 37 | load-bearing Defs as `…` | **F** | typemult/ContFiber/SibStep/PCI/HenLift/OmSat/thr/readOf displayed in full (§2) |
| 38 | IsNsLumpFamily possibly circular | **F** | `NsLumpFamily` fields displayed (§2.5a); T-C3 proves, not assumes |
| 39 | T-C7 hypotheses unspecified | **F** | Jat/Lat/hM₀ + `Mlev`/`nsTruncAt`/`stateTruncAt` displayed |
| 40 | T-E1 bracketing | **F** | partition conjunction hoisted |
| 41 | T-E3 bridge absent from statement | **F** | `SitePresents` premise + cellEvent conclusion |
| 42 | IsMultiSideSite undefined | **F** | `SideSplit`/`IsMultiSideSite` (§2.5) |
| 43 | T-E6 locality premise (= Fable GAP-3) | **F** | `SpectatorFor` in the statement |
| 44 | T-E12 incomplete | **F** | full statement, carriers displayed |
| 45 | Wall B quantifier untraced | **F** | trace paragraph in §5(C) |

**Fable criticals & gaps:**

| # | finding | disp. | where |
|---|---|---|---|
| C-1 | SibCount FALSE for intended models (F1 refutation) | **R** | = Codex 5; §0 in-corpus refutation record added; toy_sib is the regression gate |
| C-2 | JCmulti unsatisfiable (free Σc) | **R** | `JCmultiAt` at cell/state events (§2.5) |
| C-3 | T-E5 exponent refuted by F1 + p=2 census | **F** | `numTracks`; E8/E11 NOT touched (per the audit's own verification); `toy_e5_instance` regression gate |
| C-4 | T-D5/D6 hkey quantifier error | **F** | = Codex 22/23 |
| C-5 | T-V5 vacuous | **F** | = Codex 7 |
| G-1 | seam count inconsistent | **F** | = Codex 35 |
| G-2 | site vocabulary undefined | **F** | §2.5 in full; `freshExp` SUBSUMED (per-side `SideSplit.sideExp`, per-site `SiteLedger.siteExp` — rename recorded here) |
| G-3 | T-E6 premise missing | **F** | = Codex 43 |
| G-4 | ns_null finite-face rider | **F** | rider at T-C7 + T-D12 + §5 S-2 (+ `hlumps` ellipsis replaced by typed Lat) |
| G-5 | T-F2 hypotheses insufficient | **F** | `heta` (EtaLoc) + `hib` (InBoxOfMem) added; surjectivity leg's proof sketched through them |
| G-6 | decide gates not typing-plausible | **R** | Layer-G gate architecture: finite surrogate `by decide` + hand classification bridge; no decide on Set/History quantifiers |
| G-7 | T-E4 corollary weaker than display | **F** | `ss.k ≤ card` |
| G-8 | precision sweep (i)–(v) | **F** | (i) V3 `?g_of` gone; (ii) E1 brackets; (iii) E7's `?` exponent eliminated (two exact conjuncts); (iv) IsMaximalIn declared first + normative order note; (v) T-C2/T-D7a dep explicit |

DISPOSITION TALLY: 57 union entries → **43 fixed** (one carrying a scoped
push-back note, Codex 19) · **13 redesigned** · **1 pushed back** (Codex 29 —
with the contract's own text as the reason). No finding is left unaddressed; no
statement was weakened to make an obligation provable (the statement-fence: every
restatement is toward the note's display or the contract's typed form, both quoted
at the unit).
