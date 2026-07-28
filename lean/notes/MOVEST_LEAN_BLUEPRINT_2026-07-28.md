# MovesT LEAN BLUEPRINT (2026-07-28) — §T-ASSEMBLY: the branch-to-tree mass assembly — **REV 3**

CORPUS: `lean/LeanUrat/MovesT/` (namespace `LeanUrat.MovesT`). WAVE 4.
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` §T-ASSEMBLY, **rev 7** (body lines
6970–7761, repairs in place), DUAL-ACCEPTED 2026-07-27 (Codex pass 8 = 0/0
`TASM_PASS8_2026-07-27.md` + Fable confirm 0/0 `FABLE_CONFIRM_TASM_REV7_2026-07-27.md`
on identical text; acceptance record MOVES 9215–9227). A Lean statement is faithful
iff it says what a rev-7 display says (campaign §0).

REV RECORD: **rev 1 DUAL-REJECTED** — Codex 35/10 (`MOVEST_AUDIT_CODEX_2026-07-28.md`)
+ Fable 5/8 (`MOVEST_AUDIT_FABLE_2026-07-28.md`). **Rev 2 DUAL-REJECTED** — Codex
21 crit / 4 gap (`MOVEST_AUDIT_CODEX2_2026-07-28.md`) + Fable 3 crit / 4 gap
(`MOVEST_AUDIT_FABLE2_2026-07-28.md`). THIS REVISION (rev 3) repairs the UNION of the
round-2 verdicts; the finding-by-finding disposition table is §7 (round-2 union; the
rev-1→rev-2 table is retired to the rev-2 file history). The structural changes every
reader should load first:
 (i) **the REALIZABLE qualifier is restored** — TREE-EXP/its root clause/TREE-N take
   the display's own "realizable canonical tree" as the hypothesis `hreal : Realizes
   T χ Tr` (Fable-2 CRIT-1: the henV-emptied flip of the toy tree refuted rev 2's
   E5/E8/E11; the flip now fails `hreal`, and a Layer-G regression gate pins it);
 (ii) **the lawfulness fragment replaces `NodeDataLawful` as T-V8's premise** —
   `HistLawful`, the CHILD-KEYING-FREE fragment of history lawfulness, an EXPLICIT
   fenced premise whose discharge is queued on Q1 (Fable-2 CRIT-2: rev 2's premise
   could not source the real `ShapeWF`/SW1; honest conditionality, not a weaker
   substitute — a factored SW1 variant is queued on the MovesD side);
 (iii) **the state↔cell tie is a typed hypothesis** — the `SiteLedger` field
   `state_cell` (Fable-2 CRIT-3: E6/D14/E8 silently assumed it; it sits exactly at
   the fenced Q2 vertex pin's semantic content, owner HC-2, §0 row), and the
   entrance-state carrier `EntSt` now REPRESENTS the root-conditioned entrance
   (Codex-2 #8: `parentSt = none` could not carry "conditioned on the reduction
   cell");
 (iv) **the seam map is round-3 re-keyed on VALUES** — every DISCHARGED/SUPPLIED
   row now binds a typed statement over the consumed objects (the §2.10 value
   defs), the S-3 pushback is REVERSED per the contract's own preamble (the `hxrb`
   premise is stated over the IMPORTED `MovesS.RS1Meas.βmeas` — MovesS is BUILT),
   and the status tally is row-faithful (Codex-2 #25, Fable-2 GAP-1).

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
  Sigma.mass`), `C6_thmC_b` (Theorem C(b)), `HistoryCoherent`, `Realizable`, `InBox`,
  `Node.childWidth`.
* `LeanUrat.MovesS` — NEW at REV 3 (the S-3 re-key): `TableShape`/`MeasuredSide`/
  `RS1Meas` (with `βmeas`, Interfaces.lean 35–46)/`RatBurdens`/`DegCons`/`evalRe`
  (EvalReDef.lean) — BUILT, imported by §2.10/T-D15 only.
* `LeanUrat.HC2` — NEW at REV 3 (the Wall-A pin): `ReadsOf` (Defs.lean 283) —
  BUILT, referenced by `WallAReconciled` only (spec-level; fence note at §2.9).

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
| **(SIB)** | §T.3 display 7292 (quoted verbatim at §2.6): μ(⋂ Sj │ Σ_c) = ∏ μ(Sj │ Σ_c), Σ_c THE cell event; COUNT FACE 7293–7295 | `SibCount T CA χ` (Defs §2.6; rev 3: entrance-carrier sites, Codex-2 #8) — the count face AT THE CELL EVENTS of the cell assignment (rev 2: Σc is no longer a free `Set` binder — Fable CRIT-1) | OPEN KERNEL (CL-10; gate 32/32 = support not closure). Hypothesis `hsib` on T-E5/E7/E8/E10/E11 (+ reshapes T-S1/S3) |
| **(SIB-STEP)** | 7382–7388 stacked-vector form | `SibStep` (Defs §2.6), def only, typed over `JointStage` | OPEN; the (SIB-STEP)⟹(SIB) filtration lemma (7388–7391) is a recorded wave-5 obligation, NOT a unit (the note itself lists it inside the open kernel, §T.5(1)) |
| **(JC-multi)** | 7473–7483: multi-side joint cell = side product, priced AT THE ENTRANCE STATE | `JCmultiAt T CA χ es c ss` (Defs §2.5) — PER-SITE, tied to the site's cell/ENTRANCE events (rev 2: Fable CRIT-2; rev 3: the entrance carrier + the clause-partitioned `sideExp`, Codex-2 #8/#9) | OPEN, census-untested; hypothesis `hjcm` quantified over the TREE'S OWN multi-side sites ONLY (rev 2: Codex 12–13 — single-side trees consume nothing) on T-E7/E8/E10/E11 |
| **(HEN-LIFT)** | 7254–7261 declared statement | `HenLift` (Defs §2.7, now fully typed) | VP-SOUND citation obligation; discharge should PREFER Mathlib's Hensel (campaign §4) — until then a hypothesis field, never consumed by a mass unit |
| **(OM-SAT)** | 7262–7273 declared statement | `OmSat` (Defs §2.7, typed over a named factor-assignment carrier) | VP-SOUND citation obligation (GMN/Montes cite; axiomatization would need the faithfulness-entry process). Hypothesis field only |
| **X.3 / CL-4** | 7041–7048: density form of (TGT) only | NOT typed here | this corpus states ONLY finite/normalized-count forms (TREE-EXP/TREE-N are X.3-FREE, 7046–7048); no unit consumes X.3 |
| **XRB, [2r] REL.2(a)/(b)/(d), PCI** | §T.5(5) 7644–7652; PCI 7406–7413 | `PCI` typed (Defs §2.6); REL.2 legs stay owner-tagged Prop PARAMETERS in the §5 packages | proved nowhere here (the note: "this note states the interface and proves nothing about it") |
| **KB-TOT** | (c2) covering 7112–7119 consumes Theorem B totality (D4R.0-K(a)+(b), note-DISCHARGED) | `KBTot` (Defs §2.4) — REV 3 (Codex-2 #2): the per-child SATURATE-OR-CONTINUE law (rev 2's `BranchDichotomy`, kept as the (a)-leg) PLUS the (b)-leg `ns_lumps`: every realized state carries a B(iii) lump family with the slot-0 ladder — childlessness is Theorem-B no-side DATA, so the mem-everywhere/child-nowhere degeneracy FAILS the bundle (falsifier displayed at §2.4) | Lean owner HC-2/D4R0K; hypothesis `hdi : KBTot T` on T-V6, T-D3 |
| **RUN-KEY** | the HC-2 bridge surface: per-history jet-locus ↔ tree membership, per jet | `RunKey T P` — NAMED typed Prop (Defs §2.9; rev 2: no longer an inline unnamed premise, and the ∀-jet quantifier sits OUTSIDE the iff — Fable CRIT-4/Codex 22) | hypothesis on T-D5/T-D6; owner HC-2 |
| **ETA-LOC** | tree membership is η-class data (§C L4 semantic content) | `EtaLoc T P` — NAMED typed Prop (Defs §2.9) | hypothesis on T-D6, T-F2 (rev 2: Fable GAP-5); owner HC-2 |
| **CHAIN-LOC / InBox** | realized chains carry in-box reads (the L3 setting) | `InBoxOfMem T n` (Defs §2.9) | hypothesis on T-F2 (rev 2: Fable GAP-5); owner HC-2 |
| **B(iii) lump tie** | 7203–7209: no side at every height ⟺ vanishing at all heights | `NsLumpFamily.tie` (Defs §2.5a) — rev 2: the family's defining fields are DISPLAYED so T-C3 is non-circular (Codex 38) | field on T-C3/C7/E12; owner D4R0K Theorem B(iii), standing perimeter |
| **Node-data lawfulness** | realizable reads have e,g,μ ≥ 1, K-card a p-power (L3/§B2-DEF ledger data) | `NodeDataLawful` (Defs §2.2) — per-node only; conjunct of `IrrHalts` (REV 3, Codex-2 #1) | owner HC-2 (node-ledger content) |
| **History lawfulness fragment** | the L3-dictionary laws of a realizable history — per-node data + the slope/γ/anchor ties + width/window/w-chains + w₀ (card K₀ = p EXACTLY) — the CHILD-KEYING-FREE fragment | `HistLawful` (Defs §2.2) — REV 3 (Fable-2 CRIT-2): T-V8's premise. Q1-INSENSITIVE (Q1's target is solely the 4th-conjunct child-keying constants, which this fragment omits). HONESTY (replacing rev 2's false row claim): `HistoryCoherent` alone does NOT imply it (no HC clause forces μ ≥ 1, the K-card p-power, or card K₀ = p); the intended discharge is HistoryCoherent-at-the-regraded-value + the node/root ledger data, QUEUED ON Q1 — until then an explicit fenced premise | hypothesis `hlaw` on T-V8, T-V9; owner HC-2, discharge fenced-Q1 (§4) |
| **State↔cell tie** | the recursion's "each conditional on the state left by the recursion above it" (7454–7456): the state a read leaves IS the read's presented cell at its entrance | `SiteLedger.state_cell` (Defs §2.5) — REV 3 (Fable-2 CRIT-3): a FIELD, never derived in-corpus; its semantic content is exactly the fenced Q2 vertex pin's ("the clause making cellOf's digit frame at a child read WELL-DEFINED", §4) | field on `SiteLedger`, consumed by T-E6/T-E8/T-D14; owner HC-2 (canonical instance post-Q2 sign-off) |
| **Pre-halt class data** | τ is cell data (7595–7598) ⟹ pre-halt is η-CLASS data; distinct chains of one realized tree lie in distinct classes (L4/L6 semantic content) | `PreHaltClassData P` + the chain-class separation premise `hsep` (T-F2, displayed there) — REV 3 (Codex-2 #15) | hypotheses on T-F2/T-F3; owner HC-2 (PresentNorm/Galois, beside ETA-LOC) |
| **Q1/Q2 fence** | PROJECT_STATE 28j queue | §4 | DESIGNED here, NOT BUILT until Asvin's sign-off (task #44). NO unit premises `HistoryCoherent`; `HistLawful`'s discharge and `state_cell`'s canonical instance are the two fenced-queue consumers (rev 3) |

Two REFUTATION RECORDS carried from the note (never re-claim):
* TB-CAP(ns) **literal duty FAILS** (7189–7202): the (τ-ns) class is a pro-cylinder,
  at NO finite cap a finite cylinder union. The corpus encodes ONLY the amendment
  pair (ns-lump)+(ns-null); no unit states a cap for (ns); TREE-N's hypothesis
  excludes (ns) leaves by type (T-E11's `hdet`).
* Raw-count limit **FALSE** (7237–7240): only NORMALIZED (ns) bounds are stated
  (T-C8, T-E12); no unit claims the raw count tends to 0.

SIX IN-CORPUS REFUTATION RECORDS (both audit rounds' constructive finds, carried so
the E-phase never regresses; each has a Layer-G regression gate):
* rev 1's `SibCount` (free Σc) is FALSE for every intended model — at the note's own
  F1 cell, Σc := (S₁ Δ S₂) ∩ cell gives 0 ≠ 62,500² (Fable CRIT-1). The rev-2 form
  pins Σc := the cell event.
* rev 1's `JCmulti` (free Σc) is unsatisfiable at any multi-side site with positive
  fresh exponent (Σc := {x₀} gives p^E = 1 — Fable CRIT-2). The rev-2 form prices
  the cell event against the entrance state event.
* rev 1's T-E5 exponent `numTracks − 1` fails the note's committed integers
  (5^{10} = 5^{28} at F1; 64 = 4096 at the p=2 census — Fable CRIT-3). The rev-2
  exponent is `numTracks`.
* rev 2's T-E5/E8/E11 without the REALIZABLE qualifier are FALSE on the corpus's own
  toy: Tr' := the T-G1 toy tree with henV := ∅ satisfies every rev-2 hypothesis
  (the ledger reuses verbatim) yet fiber(Tr') = ∅, so E8 concluded 0·2⁶ = 2⁹
  (Fable-2 CRIT-1). The rev-3 forms carry `hreal : Realizes T χ Tr` — the display's
  own quantifier (7449–7451) — and fiberAt's new degree-conservation clause (v).
* rev 2's T-V8 premise (`NodeDataLawful` alone) cannot source `ShapeWF`: a two-node
  H with all e = g = μ = 1, K-cards p-powers, but node₁.Dwidth ≠ node₀.childWidth
  satisfies the premise while `ShapeWF n (shapeOfH H n)` FAILS `dchain`; and the real
  `ShapeWF_of_matches` demands `HistoryCoherent` + card K₀ = p (Fable-2 CRIT-2). The
  rev-3 premise is `HistLawful` (the fragment), with the factored SW1 variant queued.
* rev 2's T-E6 is refutable through the real `mem_single`/`child_cell`: the same
  lawful node in TWO branch sets makes `stateEvent T (some H)` a UNION of cell
  events — at m = 2, Cell = Bool the displayed conclusion computes 8 ≠ 4 (Fable-2
  CRIT-3). The rev-3 form consumes the `state_cell` ledger field.

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

/-- per-node lawfulness — each read has e, g, μ ≥ 1 and its K-carrier card a p-power
(L3/§B2-DEF ledger data). Owner HC-2 (node-ledger content). -/
def NodeDataLawful (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) : Prop :=
  ∀ ν ∈ H.nodes, 1 ≤ ν.e ∧ 1 ≤ ν.g ∧ 1 ≤ ν.μ ∧
    Nat.card ↥ν.σ.K = p ^ ((Nat.card ↥ν.σ.K).factorization p)

/-- REV 3 (Fable-2 CRIT-2): **the CHILD-KEYING-FREE FRAGMENT of history lawfulness** —
T-V8's premise, strong enough to source the REAL `ShapeWF` (all clauses:
dchain/window/gamTie/anchorTie/edvd/gmu/w0/wchain — rev 2's per-node-only premise
provably could not, §0 refutation record #5). Clauses = `HistoryCoherent`'s conjuncts
1–3 VERBATIM (root key degree 1; the slope tie; the γ-tie) + the 4th conjunct's
NON-KEYING sub-clauses (window `s0'+w' ≤ μ`, the Dwidth chain, slope increase) —
the keying sub-clauses (IsRecenteringCore/IsNodeLift/TransitionCoreL, the σ.s/σ.t
ties) are OMITTED, which is exactly what makes it Q1-INSENSITIVE — + `NodeDataLawful`
+ the two SW1 side conditions (card K₀ = p EXACTLY; the read-0 monic tie), + the
per-node anchor/edvd/gmu ledger clauses [E-phase: each bound to its MovesC `Node`
accessor; the roster below is NORMATIVE — a clause SW1's factored variant does not
consume is dropped at E-phase with a MANIFEST deviation, never silently added]. -/
def HistLawful (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (H : History p F) : Prop :=
  NodeDataLawful p H ∧
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
  (∀ hj : 0 < H.nodes.length, Nat.card ↥((H.nodes[0]'hj).σ.K) = p) ∧      -- w₀ = 1
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- slope tie
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- γ-tie
    (((H.nodes[i]'hi).gam : ℤ) : ℚ)
      = ((H.nodes[i]'hi).e : ℚ) * ((H.strFrame i : ℚ) * (H.nodes[i]'hi).ustar)
        + ((((H.nodes[i]'hi).s0 + (H.nodes[i]'hi).wSide) : ℕ) : ℚ) * ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- anchor/edvd/gmu
    ((H.nodes[i]'hi).e : ℤ) * (H.nodes[i]'hi).a
        = ((H.nodes[i]'hi).s0 : ℤ) - bezT (H.nodes[i]'hi).e (H.nodes[i]'hi).h * (H.nodes[i]'hi).gam ∧
      (H.nodes[i]'hi).e ∣ (H.nodes[i]'hi).wSide ∧
      (H.nodes[i]'hi).g * (H.nodes[i]'hi).μ ≤ (H.nodes[i]'hi).len) ∧
  (∀ (i : ℕ) (hi : i + 1 < H.nodes.length),                                -- non-keying chain
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope)) ∧
  (∀ h0 : 0 < H.nodes.length, ((H.nodes[0]'h0).s0 + (H.nodes[0]'h0).wSide ≤ n))
-- FENCED CONDITIONALITY (§0 row): `HistoryCoherent` alone does NOT imply this (no HC
-- clause forces μ ≥ 1, K-card p-powers, or card K₀ = p); the discharge from the
-- re-keyed HistoryCoherent + node/root ledger data is QUEUED ON Q1 (§4). Until then
-- `hlaw : HistLawful p n H` is an explicit hypothesis — honest conditionality.

/-- (τ-irr) FIRES: ≥ 1 LAWFUL read, and the latest read saturates — "Saturation is
equivalent to μ = 1 at the branch's latest read" (7078–7080). REV 3 (Codex-2 #1): the
lawfulness conjunct is IN — a junk history ending in μ = 1 no longer halts, so
`fiberAt`/`ContFiber`/`PreHalt`/the verdict model cannot halt histories the note would
not; the saturation display's degree content "E·F = d(cluster)" is the THEOREM PAIR
T-V9 (accE·accF = the last read's childWidth under the chain fragment; saturation ⟺
μ = 1), not a silent claim. Pure node/cell data: no box input, no f. -/
def IrrHalts (H : History p F) : Prop :=
  H.nodes ≠ [] ∧ NodeDataLawful p H ∧ (H.nodes.getLast?).elim False (fun ν => ν.μ = 1)

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
model's child predicate. DEFINITIONAL FACE ONLY (rev 3, Codex-2 #2): its Theorem-B
faithfulness — childlessness IS the (z-3) no-side status, never a modeling artifact —
is `KBTot.ns_lumps` below, consumed where that content is load-bearing (T-V6's
covering, T-D3's halt_iff, T-C3's lump identification). -/
def NsHalts (T : TreeModel p F n N m pol) (o : Option (History p F)) (x : Box p m) :
    Prop :=
  T.mem o x ∧ ∀ ν : Node p F, ¬ T.child o ν x

/-- the per-child SATURATE-OR-CONTINUE law (the (a)-leg of KB-TOT, carried from rev 2):
"each branch of the branch set then either saturates (μ = 1: τ-irr halt) or has μ ≥ 2
and CONTINUES, the continuation existing by L1 totality" (7114–7118). -/
def BranchDichotomy (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    ∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      (ν.μ = 1 ∧ IrrHalts (H.snoc ν hν)) ∨
      (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)
-- [`NodeExtends H ν` := the snoc side condition MovesC's `History.snoc` carries
--  (well-formed extension datum); E-phase binds it to the actual snoc signature.]

/-- **KB-TOT, the full hypothesis bundle** — REV 3 (Codex-2 #2, the recommended
single threading point): Theorem B's structural totality (D4R.0-K(a)+(b)),
consumed by (c2)'s covering 7112–7119. Leg (a) = `BranchDichotomy`. Leg (b) =
`ns_lumps`, the NO-SIDE FAITHFULNESS: every realized state carries a B(iii) lump
family at a jet of the state (§2.5a) WITH the slot-0 ladder — so childlessness at a
realized state is pinned by `NsLumpFamily.tie` to the all-heights digit-vanishing
datum of the state's OWN window, and the note's (τ-ns) = "J(f) = ∅, the exact key
power" (7081–7083), never arbitrary absence of children. FALSIFIER (the rev-1/rev-2
degeneracy dies): a model with `mem` everywhere and `child` nowhere forces, at any
state, ∀ x ∈ box, ∀ M, x ∈ L M — but T-C6's count face gives
card(SHZ Z_M)·p^{|Z_M|} = card(SHZ ⊤) with |Z_M| ≥ M − M₀ → ∞ (the ladder field),
incompatible with a full-box lump; so `ns_lumps` FAILS on it. Owner HC-2/D4R0K;
NEVER proved here. -/
structure KBTot (T : TreeModel p F n N m pol) : Prop where
  dichotomy : BranchDichotomy T
  ns_lumps : ∀ (H : History p F), (∃ x, T.mem (some H) x) →
    ∃ J : JetSetup H n N m, Nonempty (NsLumpFamily T J)
    -- the family's `tie` + `slot0` fields (§2.5a) carry the content; the ∃ is the
    -- realized-state supply (HC-2's presented faces / D4R0K B(iii))

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
per-site exponents are `SiteLedger.siteExp` (rename recorded in §7). REV 3: the
ENTRANCE-STATE carrier `EntSt` joins the vocabulary (Codex-2 #8) and threads through
`SitePresents`/`JCmultiAt`/`SiteLedger`/`SibCount`/`PCI`; the tree layer gains
`Realizes` (hoisted), `VTree.ext`, `ShapeEquiv`, and fiberAt's degree clause (v);
`SideSplit` is re-tied to the presented system's clause partition (Codex-2 #9); the
ledger gains `sides`/`splitAt`/`state_cell` (Fable-2 CRIT-3).

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
value is PINNED to `nsVerdictOf` (the note's v = μ·{(E(Φ̂),F(Φ̂))}, 7083), so
two trees differing only in an ns-leaf verdict can no longer fiber the same x
(this restores T-E9/T-F1 — Codex 14/15); (iii) the hen payload matches x's root
datum; (iv) non-leaves do not halt; (v) — NEW at REV 3 (Codex-2 #3, the VTree
completeness face) — DEGREE CONSERVATION: the tree's whole type multiset saturates
the box degree, "a τ-halted leaf of a degree-d cluster carries v with Σ E·F = d …
d = n" (7062–7063) summed over the complete tree's leaves + hen tracks. Clause (v)
REJECTS the silently-track-dropping trees rev 2 admitted: an empty-chain tree on a
repeated-factor reduction has typemult = henV (simple factors only), degree < n —
its fiber is now EMPTY BY TYPE (T-D2's general rejection theorem displays this). -/
def VTree.fiberAt (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  (∀ H : History p F, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)) ∧
  (∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →
    ((IrrHalts H ∧ ¬ Tr.nsLeaf H ∧ Tr.leafV H = some (irrVerdictOf H)) ∨
     (NsHalts T (some H) x ∧ ¬ IrrHalts H ∧ Tr.nsLeaf H ∧
       Tr.leafV H = some (nsVerdictOf H)))) ∧
  Tr.henV = henPayload χ x ∧
  (∀ H ∈ Tr.chains, ¬ IsMaximalIn Tr.chains H →
    ¬ IrrHalts H ∧ ¬ NsHalts T (some H) x) ∧
  ((Tr.typemult.map fun ef => ef.1 * ef.2).sum = n)

/-- DECIDED at x := some complete finite tree fibers x — (TGT)'s decided set, the
domain ONE-F partitions (7580, 7586–7589). The undecided complement is [5]'s (X.3);
NOT priced here. -/
def Decided (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  ∃ Tr : VTree p F, Tr.fiberAt T χ x

/-- REALIZABILITY of a tree — the display's own qualifier: "for every complete finite
REALIZABLE canonical tree T" (7449–7451). REV 3 (Fable-2 CRIT-1): HOISTED from T-D11
and threaded as the hypothesis `hreal` on T-E5/E8/E11 and into T-E10's summation
domain — the henV-emptied flip of a lawful tree (fiber ∅) now fails a hypothesis
instead of falsifying the identities. -/
def Realizes (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (Tr : VTree p F) : Prop := ∃ x, Tr.fiberAt T χ x

/-- EXTENSIONAL EQUALITY of trees — the (chains, henV, leafV, nsLeaf) tuple. REV 3
(Codex-2 #24): DISPLAYED (rev 2 deferred the quotient bridge to prose). This IS an
equivalence relation: off `chains`, `hleaf` forces `leafV = none` and `hns_leaf`
forces `¬ nsLeaf`, so the on-chain clauses determine both functions globally. -/
def VTree.ext (Tr Tr' : VTree p F) : Prop :=
  Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
  ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H)

/-- the tree-shape equivalence (REV 3, Codex-2 #14 — replaces rev 2's undisplayed
`TreeShape`/`TreeShapeOf`/`Ashape`/`CofShape` quartet): a prefix-order isomorphism of
chain sets matching per-chain shapes and the hen payload. Two equal-shape sibling
chains (F1's z−1/z−2) are NOT collapsed — the bijection is on chains, not on shape
values. T-E10 sums over an `ShapeEquiv`-class of a REPRESENTATIVE tree; its constant
exponent and class count are then `AofTr` of the representative and the class's own
`Nat.card` — no separate shape carrier type. -/
def ShapeEquiv (n : ℕ) (Tr Tr' : VTree p F) : Prop :=
  Tr.henV = Tr'.henV ∧
  ∃ φ : {H // H ∈ Tr.chains} → {H // H ∈ Tr'.chains}, Function.Bijective φ ∧
    (∀ H H', H.1.IsPrefixOf H'.1 ↔ (φ H).1.IsPrefixOf (φ H').1) ∧
    (∀ H, shapeOfH (φ H).1 n = shapeOfH H.1 n) ∧
    (∀ H, (Tr.nsLeaf H.1 ↔ Tr'.nsLeaf (φ H).1))

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

/-- **the ENTRANCE-STATE carrier** — NEW at REV 3 (Codex-2 #8): rev 2's
`Option (History p F)` could not represent "the root state conditioned on the
reduction cell g" — the entrance state of a track's FIRST window read (the note's
Σ₀, the state the ROOT read leaves, 7485–7491) — invalidating the first window step
and T-D14. Three constructors: the ambient box (the root read's own entrance), a
REDUCTION CELL (a track's entrance — keyed by the canonical level-0 datum g, not by
`CA.Cell`, so the carrier is CellAssign-free), a realized chain state. -/
inductive EntSt (p : ℕ) (F : Type*) (n : ℕ) where
  | amb : EntSt p F n
  | red (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p)) : EntSt p F n
    -- the reduction cell {f̄ = g}, WITH the track selected by its reduction factor ψ
    -- (several tracks share one reduction cell; the entrance EVENT is the cell, the
    -- cell FUNCTION at this entrance is per-track — the ψ datum individuates it)
  | st (H : History p F) : EntSt p F n

/-- the entrance EVENT: what a site's charge law conditions on. -/
def entEvent (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    EntSt p F n → Set (Box p m)
  | .amb => Set.univ
  | .red g _ => rootCell χ g
  | .st H => stateEvent T (some H)

/-- the Option-state embedding (the rev-2 vocabulary is the .amb/.st sub-family). -/
def embE : Option (History p F) → EntSt p F n
  | none => .amb
  | some H => .st H
```

[Design note, load-bearing, carried from rev 1: TREE-EXP is stated DIVISION-FREE in
the D10 house style — "jvol(c_s │ Σ) = p^{−k_s}" becomes
`Nat.card ↥(cell ∩ Σ) * p ^ k_s = Nat.card ↥Σ`, and the site product becomes one
exponent sum. No ℚ, no measure API; the profinite μ statements of the note are
consumed at their finite-level faces, which is what the note's own TREE-N/count
displays provide (7568–7574).]

```lean
/-- REV 2 (Fable GAP-8/Codex 41): the jet-site tie, NAMED — the site's cell event IS
the transported system's stratum. REV 3 (Codex-2 #8): stated over the ENTRANCE
carrier, so a track's first window read presents FROM its reduction cell. This is
the bridge T-E3's rev-1 sketch promised but kept out of the statement; a hypothesis
object the statements consume. Owner of instances: HC-2 (the presented faces). -/
def SitePresents (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m) : Prop :=
  cellEventE T CA χ es c = {x | Sigma.IsSolution x ∧ fd.sat x}
  ∧ entEvent T χ es = {x | Sigma.IsSolution x}

/-- REV 2 (Fable GAP-3/Codex 43): the level-separation premise for spectator events,
EXPLICIT — E is invariant under changes of the given (fresh) coordinates. -/
def SpectatorFor (fresh : Finset (Fin m)) (E : Set (Box p m)) : Prop :=
  ∀ x x' : Box p m, (∀ i : Fin m, i ∉ fresh → x i = x' i) → (x ∈ E ↔ x' ∈ E)

/-- REV 3 (Codex-2 #9 — rev 2's `sideExp` was FREE data, so one cell could carry
incompatible exponent assignments): the SIDE DECOMPOSITION of a presented cell — the
window polygon's sides, each carrying ≥ 1 eligible branch, with the per-side systems
a PARTITION of the presented system's OWN clauses and the per-side exponents DEFINED
as the side sub-systems' equation counts. `sideExp` is no longer a field: it is
`(clausesOf j).card` [E-phase: mstar of the side subsystem], and the partition clause
forces Σ_j sideExp j = fd.mstar — one exponent budget per cell, no mislabeling. -/
structure SideSplit (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (c : CA.Cell) (fd : FreshData p m) where
  k : ℕ
  sideOf : Node p F → Fin k
  side_ne : ∀ j : Fin k, ∃ ν ∈ CA.branchSetOf c, sideOf ν = j
  clausesOf : Fin k → Finset (FreshClause p m)     -- the side's own system [E-phase:
                                                    --  the clause carrier of FreshData]
  hpartition : (⋃ j : Fin k, (clausesOf j : Set _)) = (fd.clauses : Set _) ∧
    Pairwise (Function.onFun Disjoint clausesOf)
def SideSplit.sideExp {T CA c fd} (ss : SideSplit T CA c fd) (j : Fin ss.k) : ℕ :=
  (ss.clausesOf j).card    -- [E-phase: the side subsystem's mstar]

/-- a MULTI-SIDE site: its window hull has ≥ 2 sides (7473–7483). -/
def IsMultiSideSite (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (c : CA.Cell) {fd : FreshData p m} (ss : SideSplit T CA c fd) : Prop := 2 ≤ ss.k

/-- **(JC-multi), PER-SITE — REV 2 (Fable CRIT-2 + Codex 12–13); REV 3: over the
entrance carrier, exponents off the clause partition.** The note's display 7473–7483
prices the joint cell AT THE ENTRANCE STATE: "the CLAIMED mass is the side product
jvol(c_s │ Σ) = ∏_{sides} vol_nom(E_fresh(ν_side))". Division-free, with the cell
event and entrance event as the DEFINED conditioning objects (no free `Set` binder).
OPEN obligation (census-untested — the union system is exactly what no accepted
lemma covers); NEVER proved here. -/
def JCmultiAt (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell)
    {fd : FreshData p m} (ss : SideSplit T CA c fd) : Prop :=
  Nat.card ↥(cellEventE T CA χ es c) * p ^ (∑ j : Fin ss.k, ss.sideExp j)
    = Nat.card ↥(entEvent T χ es)

/-- the per-site B(iii)/Scale level (T-D4's `hlev`, T-E11's threshold joins): level 1
at the root (7564), the shape-side band level at a window site. -/
noncomputable def siteLevel (n : ℕ) : Option (History p F) → ℕ
  | none => 1
  | some H => (shapeOfH H n).NPband n

/-- REV 2 (Fable GAP-2 — seam row S-6's promised deliverable): the SITE LEDGER — the
typed carrier of the per-site jet/system data (HC-2's presented faces). REV 3
changes: (a) `parentSt` lands in the ENTRANCE carrier (Codex-2 #8) — head chains
enter from their reduction cell, never from the ambient root; (b) `state_cell`, the
STATE↔CELL TIE, is a FIELD (Fable-2 CRIT-3 — the fence-compatible one-hypothesis
shape: E6/D14/E8 consumed it silently and were refutable through the real
`mem_single`/`child_cell`; its semantic content is exactly the fenced Q2 vertex
pin's, §4, owner HC-2, §0 row); (c) the hull-side COUNT is a field with the one-side
tie (Codex-2 #9 — rev 2's `fd.oneSide` label was untied and could evade `hjcm` by
mislabeling): a multi-side site must EXHIBIT its clause-partitioned `SideSplit`.
`siteExp` stays DEFINED from the ledger (the system's mstar), never free data — the
per-site charge identities are THEOREMS (T-E3/E6 from C4), not ledger axioms. -/
structure SiteLedger (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) where
  sys : History p F → Locus p m × FreshData p m
  cellAt : History p F → CA.Cell            -- the joint cell of the site's read
  parentSt : History p F → EntSt p F n      -- the entrance state of the read (REV 3)
  hparent : ∀ H ∈ Tr.chains, match parentSt H with
    | .amb => False                          -- window sites never enter from the ambient box
    | .red _ _ => H.nodes.length = 1         -- a track's FIRST window read: entrance = Σ₀
    | .st H' => H'.IsPrefixOf H ∧ H' ≠ H ∧ H' ∈ Tr.chains
  presents : ∀ H ∈ Tr.chains,
    SitePresents T CA χ (parentSt H) (cellAt H) (sys H).1 (sys H).2
  sides : History p F → ℕ                    -- the hull side count of the site's
  hsides : ∀ H ∈ Tr.chains, 1 ≤ sides H      --   own window (REV 3, Codex-2 #9)
  state_cell : ∀ H ∈ Tr.chains, sides H = 1 →   -- THE TIE (REV 3, Fable-2 CRIT-3):
    stateEvent T (some H)                       -- at a ONE-SIDE window, the state a
      = cellEventE T CA χ (parentSt H) (cellAt H)   -- read leaves IS its presented
    -- cell at its entrance (one side ⟹ any branch selection pins ALL on-line
    -- digits). Fable-2's two-branch-sets counter-instance dies HERE: it forced
    -- state(some H) = a UNION of two cell events, contradicting this equality. At
    -- multi-side windows the state is strictly coarser (other sides' digits free);
    -- those sites route through T-E7's `hdecomp` + (SIB), never through this field.
  splitAt : ∀ H ∈ Tr.chains, 2 ≤ sides H → SideSplit T CA (cellAt H) (sys H).2
    -- a multi-side site EXHIBITS its side decomposition of its OWN system; the
    -- one-side tie: sides H = 1 means (sys H).2 is a single-side system, C4-eligible
    -- [E-phase: the hull datum of the transported system — owner HC-2's instance]
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
  slot0 : ∀ M, M₀ J ≤ M → M - M₀ J ≤ (interiorFreshIdx J M).card
    -- REV 3 (Codex-2 #2's falsifier leg): the slot-0 LADDER — "the window interior
    -- is never empty … one coordinate per level, heights unit-spaced" (7227–7229).
    -- As a FIELD it makes the family non-degenerate (an empty-interior junk jet
    -- cannot trivialize `tie`); T-C5 PROVES it for the real jets, so the field is
    -- discharged at every presented instance.
-- [`interiorFreshIdx J M : Finset (coordinate index)` and `digitAt` are the jet
--  chart's accessors — E-phase types them against MovesC's (ZC) fields (`floorH`,
--  block base indices, the Scale map); their DEFINING CLAUSES are the display
--  7217–7224 quoted in T-C5. The Finset is what T-C5's `Z_M` pins.]

/-- the (ZC) hypothesis package of a jet — REV 3 (Codex-2 #6): T-C5 formerly
quantified over EVERY `JetSetup` while its sketch consumed the note's (ZC) setting;
the setting is now an explicit displayed premise. Clauses = the display 7216–7224:
(a) INCLUSIVE TOP — an interior coordinate is Σ-determined iff its height ≤ the
floor at its block ((ZC-a)); (b) RIM SEPARATION — DIG's lead indices sit at base
index ≥ μ·D, never interior ((ZC-b)); (c) SLOT-0 — block b₀ at base index 0 < μ·D
with one coordinate per level, unit-spaced heights (the ladder's engine); (d) the
window-interior/floor data are carried by J's chart. [E-phase: each clause bound to
MovesC's (ZC) fields — `floorH`, block bases, Scale; standing perimeter 7232–7233.] -/
structure ZCPack {H : History p F} (J : JetSetup H n N m) : Prop where
  inclusive_top : ∀ bl, bl ∈ interiorIdx J →
    (pinnedOnState J bl ↔ heightOf J bl ≤ floorAt J bl)
  rim_sep : ∀ bl, digLead J bl → interiorBase J bl = false
  slot0_grid : ∀ ht, M₀ J ≤ ht → ∃ bl, bl ∈ interiorIdx J ∧ heightOf J bl = ht ∧
    baseOf J bl = 0
-- [`interiorIdx/pinnedOnState/heightOf/floorAt/digLead/interiorBase/baseOf` — J's
--  chart accessors, E-phase-bound as above; the STRUCTURE's clause roster is
--  normative, the accessor names are not.]
```

DECLARATION ORDER — NORMATIVE (the §2.x display order is thematic; the FILE hoists):
(1) §2.1–2.3 + §2.4's `NsHalts`/`BranchDichotomy`/`PrunedMem`; (2) `readOf`/
`shapeOfH` (§2.5 tail); (3) §2.5's `EntSt`/`entEvent`/`embE` + §2.9's `CellAssign`/
`cellEvent`/`cellEventE`/`eligibleT`/`RootCellsOf` (consumed by §2.5's site
vocabulary and §2.6); (4) the rest of §2.5 + §2.5a; (5) §2.4's `KBTot` (consumes
§2.5a's `NsLumpFamily`); (6) §2.6–2.8; (7) the remainder of §2.9 (VerdictModelT,
`levelIdx`/`CapIrrLaw`/`CapData`, RunKey/EtaLoc/InBoxOfMem/WallAReconciled);
(8) the structural carriers displayed at their units (`RootSplitData`/`trackEvent`
(T-E5), `SplitSiteData` (T-E7), `TreeScaffold`/`multiSites` (T-E8), `JetTower`/
`Mlev`/truncation carriers (T-C7), `ReadLedgerT`/`readLedgerOf` (T-D14),
`nsClass` (T-C3), `NsFree`/`shapeClass` (T-E10), `IrrHaltsAsChild` (T-V5),
`capIrrOf` (T-C2), `ClassTree`/`fibOf` (T-D10/11)) — ALL HOIST into `Defs.lean`
ahead of (9) §2.10 (the seam-value defs, which consume them — land last).
[Fable GAP-8(iv) generalized: no forward reference survives in the file.]

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

/-- `SubFiber` — REV 3 (Codex-2 #23: displayed; rev 2 left it a bracket note):
ContFiber's three clauses over a DESIGNATED chain subset headed at a root child —
T-E5's per-track event body. (i) the subset is exactly the realized non-halting-
prefixed extensions of its head; (ii) maximal members halt with the recorded
verdict values; (iii) non-maximal members do not halt. -/
def SubFiber (T : TreeModel p F n N m pol) (chainSet : Set (History p F))
    (ν₀ : Node p F) (hν : ChildRoot none ν₀)
    (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop)
    (x : Box p m) : Prop :=
  (∀ H' : History p F, H' ∈ chainSet ↔
      ((childHist none ν₀ hν).IsPrefixOf H' ∧ T.mem (some H') x ∧
        ∀ H'' : History p F, (childHist none ν₀ hν).IsPrefixOf H'' →
          H''.IsPrefixOf H' → H'' ≠ H' → ¬ IrrHalts H'' ∧ ¬ NsHalts T (some H'') x)) ∧
  (∀ H' ∈ chainSet, IsMaximalIn chainSet H' →
    ((IrrHalts H' ∧ ¬ nsSpec H' ∧ leafSpec H' = some (irrVerdictOf H')) ∨
     (NsHalts T (some H') x ∧ ¬ IrrHalts H' ∧ nsSpec H' ∧
       leafSpec H' = some (nsVerdictOf H')))) ∧
  (∀ H' ∈ chainSet, ¬ IsMaximalIn chainSet H' → ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x)

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
def stOf : EntSt p F n → Option (History p F)
  | .st H => some H
  | _ => none      -- .amb and .red entrances root their children at the model's
                    -- root state (first window reads are `T.child none` children)

def SibCount (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (es : EntSt p F n) (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEventE T CA χ es c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)
-- REV 3 (Codex-2 #8's kernel face): the site quantifier is the ENTRANCE carrier —
-- the note's own gate cell (F1's 14-pin Σ_c = reduction cell + window data) is a
-- `.red`-entrance cell, which rev 2's Option-state quantifier could not reach
-- (RootCellsOf forces the none-state cells to be EXACTLY the reduction cells).

/-- (SIB)'s COUNT face ACROSS SHALLOW SPLITS — the Wsh17Package.sib_count field's
value (§5 S-8): the same kernel restricted to the SHALLOW entrances (.amb — the
root cross-track split — and .red — the depth-1 window splits; never .st). -/
def SibCountShallow (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) : Prop :=
  ∀ (es : EntSt p F n), (∀ H, es ≠ .st H) →
    ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEventE T CA χ es c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)

/-- (SIB-STEP), stacked-vector form (7382–7388) — def ONLY; its ⟹(SIB) filtration
lemma is the note's own open remainder (§T.5(1)), a wave-5 obligation. REV 2
(Codex 37): typed over an explicit stage carrier. -/
structure JointStage (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) where
  active : Finset (Node p F)
  hactive : active ⊆ CA.branchSetOf c
  past : Set (Box p m)
  hpast : past ⊆ cellEvent T CA o c
  nextW : Node p F → Box p m → ℕ
  alpha : Node p F → ℕ
  halpha : ∀ ν ∈ active, 1 ≤ alpha ν

/-- `StageRealized` — REV 3 (Codex-2 #23/Fable-2 GAP-2: no longer an undisplayed
name; the TYPE pins the content, the wave-5 filtration lemma owns the final
refinement, recorded as an E-phase-adjustable spec). Two clauses (7383–7387):
(i) `past` IS a realized-reads stage event — the cell event cut by the active
siblings' realized read prefixes through the stage; (ii) the stacked `nextW` forms
are alphabet-valued on it. Consumed by NOTHING in wave 4. -/
def StageRealized (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    {o : Option (History p F)} {c : CA.Cell} (st : JointStage T CA o c) : Prop :=
  (∃ rd : Node p F → Set (History p F),
    (∀ ν ∈ st.active, ∀ H' ∈ rd ν, ∃ hν : ChildRoot o ν,
      (childHist o ν hν).IsPrefixOf H') ∧
    st.past = cellEvent T CA o c ∩ ⋂ ν ∈ st.active, ⋂ H' ∈ rd ν,
      stateEvent T (some H')) ∧
  (∀ ν ∈ st.active, ∀ x ∈ st.past, st.nextW ν x < st.alpha ν)

def SibStep (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T) : Prop :=
  ∀ (o : Option (History p F)) (c : CA.Cell) (st : JointStage T CA o c),
    StageRealized T CA st →
    ∀ a a' : Node p F → ℕ,
      (∀ ν ∈ st.active, a ν < st.alpha ν) → (∀ ν ∈ st.active, a' ν < st.alpha ν) →
      Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a ν}
        = Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a' ν}
-- [REV 3 note: JointStage/SibStep stay Option-keyed at wave 4 — they are def-only,
--  consumed by NOTHING here; the wave-5 filtration lemma re-keys them over `EntSt`
--  alongside its own final form (recorded so the reachability repair is not lost).]

/-- PCI (parent-context independence — "named interface, NOT part of (SIB)",
7406–7413); stated, proved nowhere, consumed by nothing in MovesT (REV 13 struck PCI
from TREE-EXP's inputs, 7650–7652). REV 2 (Codex 37): typed — the conditional
continuation law of a child depends only on the child's own data, never on unused
parent/sibling cell data: the SAME individuated child in two branch sets prices its
transported subtree events equally (division-free cross-multiplied form). The
subtree transport `TsubAt` (same prescribed subtree read at the two entrances — the
child-CTS-state identification) is the [2r]/CTS-M(iv)-REP face, flagged E-phase.
A PCI failure adjudicates as R2's lumpability channel, never as a (SIB) failure. -/
def PCI (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (es es' : EntSt p F n) (c c' : CA.Cell) (ν : Node p F),
    ν ∈ CA.branchSetOf c → ν ∈ CA.branchSetOf c' →
    ∀ (hν : ChildRoot (stOf es) ν) (hν' : ChildRoot (stOf es') ν)
      (TsubAt : EntSt p F n → Set (History p F))
      (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop),
      SubtreeTransport TsubAt es es' ν →
      Nat.card ↥(cellEventE T CA χ es c ∩
          {x | ContFiber T (stOf es) ν hν (TsubAt es) leafSpec nsSpec x})
        * Nat.card ↥(cellEventE T CA χ es' c')
      = Nat.card ↥(cellEventE T CA χ es' c' ∩
          {x | ContFiber T (stOf es') ν hν' (TsubAt es') leafSpec nsSpec x})
        * Nat.card ↥(cellEventE T CA χ es c)
-- REV 3: entrance-carrier sites, same reachability repair as SibCount (Codex-2 #8)
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
  cellOf : EntSt p F n → Box p m → Cell       -- REV 3 (Codex-2 #8): the cell datum is
    -- keyed by the ENTRANCE carrier — at `.red g ψ` it is the joint cell of x's
    -- track-ψ window read (the datum rev 2's Option-state could not carry)
  cellLevel : EntSt p F n → ℕ
  levelOf : Fin m → ℕ
  cell_local : ∀ (es : EntSt p F n) (x x' : Box p m),
    (∀ c : Fin m, levelOf c < cellLevel es → x c = x' c) → cellOf es x = cellOf es x'
  branchSetOf : Cell → Finset (Node p F)
  child_cell : ∀ (o : Option (History p F)) (ν : Node p F) (x : Box p m),
    T.mem o x → (T.child o ν x ↔ ν ∈ branchSetOf (cellOf (embE o) x))
  child_cell_red : ∀ (χ : Fin n → Fin m) (g : Fin n → ZMod p)
      (ψ : Polynomial (ZMod p)) (ν : Node p F) (x : Box p m),
    x ∈ rootCell χ g → ν ∈ branchSetOf (cellOf (.red g ψ) x) → T.child none ν x
    -- the ⊆ face: cells at a reduction-cell entrance select among the root's
    -- realized children; the per-track ⊇ face (the cell's branch set is EXACTLY the
    -- track-ψ window's eligible branches) is the CANONICAL instance's law — HC-2's,
    -- through `WallAReconciled` (fenced Q1/Q2)

/-- THE CELL EVENT Σ_c — the note's conditioning object (7290–7292), DEFINED:
the site's realized state cut to one cell value. Every conditional law of this
corpus conditions HERE (REV 2, Fable CRIT-1/CRIT-2). The Option form is the
.amb/.st sub-family (`embE`); the ENTRANCE form `cellEventE` (REV 3) additionally
serves the reduction-cell entrances. -/
def cellEvent (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) : Set (Box p m) :=
  {x | T.mem o x ∧ CA.cellOf (embE o) x = c}

def cellEventE (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell) : Set (Box p m) :=
  {x | x ∈ entEvent T χ es ∧ CA.cellOf es x = c}

/-- W4-1's re-keyed `eligible` — a DEFINED predicate over the cell/branch-set
vocabulary (MovesD §2.5 W4-1(c) verbatim). Cell data BY CONSTRUCTION (it factors
through `cellOf` — T-D1's second lemma displays this). -/
def eligibleT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) : Prop :=
  ν ∈ CA.branchSetOf (CA.cellOf (embE o) x)

/-- the root-cell tie: the root state's cell datum IS the reduction f̄ read through
χ ((JC-root) 7464–7466). A LAW the canonical CellAssign must satisfy; hypothesis
field `hrc` on T-E5/E8/T-S3/T-G1. -/
def RootCellsOf (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ x y : Box p m, CA.cellOf .amb x = CA.cellOf .amb y ↔ ∀ b : Fin n, x (χ b) = y (χ b)

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

/-- Wall A reconciliation, pinned at the REAL predicate — REV 3 (Codex-2 #19: rev 2's
`ReadsOf`-as-parameter supplied "neither the real predicate nor an inhabited
canonical CellAssign", so the row overclaimed SUPPLIED). **`HC2.ReadsOf` is BUILT**
(`lean/LeanUrat/HC2/Defs.lean` line 283: `ReadsOf p F n f H` — monic degree-n f,
`HistoryCoherent H`, per-read development realization incl. clause (vi)'s vertex
read-off) and is consumed here BY NAME. Its argument is a profinite f while the box
is level-N digit data, so the pin takes HC-2's chart section `dec` (the decode
Box → ℤ_p[x] — HC-2 instance data) as its ONE remaining parameter: branch membership
iff the decoded member's run realizes the extended history. Status accordingly
REDUCED (never SUPPLIED): the named residue = {`dec`, the canonical CA, the instance
proof} — all HC-2's, fenced Q1/Q2 (§4). -/
def WallAReconciled (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (dec : Box p m → Polynomial ℤ_[p]) : Prop :=
  ∀ (H : History p F) (ν : Node p F) (hν : NodeExtends H ν) (x : Box p m),
    T.mem (some H) x →
    (ν ∈ CA.branchSetOf (CA.cellOf (embE (some H)) x) ↔
      LeanUrat.HC2.ReadsOf p F n (dec x) (H.snoc ν hν))
-- FENCE NOTE: spec-only — NO mass unit premises this Prop. `ReadsOf` internally
-- carries `HistoryCoherent`; that is the fenced Q1 surface itself, referenced as
-- the reconciliation TARGET, never consumed as a unit premise (fence intact; the
-- corpus-wide no-HistoryCoherent-premise sweep still passes).
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
    CA.cellOf (embE o) x = CA.cellOf (embE o) x' → vdict o x = vdict o x'
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
  capIrr_law : CapIrrLaw p F n m pol capIrr   -- DISPLAYED below (REV 3, Codex-2
                                               -- #17/Fable-2 GAP-2 — no longer a name)
  -- NO ns cap field: the (ns) clause enters `vdict` only through `NsHalts`; its
  -- classes are NEVER claimed cylindrical (§0 refutation record — the ADMITTED
  -- amendment, MovesD §2.5 W4-2(b)(ii)).

/-- the digit level of a box coordinate under the standard layout (m = n·N: n
coefficient digits per level): coordinate c sits at level ⌊c/n⌋ + 1. REV 3 (Fable-2
GAP-2: previously unbracketed and undefined). [E-phase: bound to MovesD's Box layout
accessor; the VALUE is the spec.] -/
def levelIdx {n : ℕ} (c : Fin m) : ℕ := (c : ℕ) / n + 1

/-- **the cross-level per-class cap LAW** — REV 3 (Codex-2 #5/#17): the contract's
"one cap per class across ALL presented N" (W4-2(b)'s addendum), now QUANTIFIED over
the presented family — rev 2's form was locality for ONE fixed `Presented` object.
The cap function takes no N (uniformity by type); the law demands it works at every
presented level. -/
def CapIrrLaw (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n m : ℕ) (pol : CanonPolicy p F)
    (cap : ∀ {P : Shape n}, PrefIdx n pol P → ℕ) : Prop :=
  ∀ {P : Shape n} (i : PrefIdx n pol P), IrrHalts (reprOf i) →
    ∀ (N' : ℕ) (S : Presented p F n N' m pol P) (x x' : Box p m),
      (∀ c : Fin m, levelIdx c < cap i → x c = x' c) →
      (x ∈ S.fiber i ↔ x' ∈ S.fiber i)

/-- the cap DATA package T-D3 consumes — REV 3 (Codex-2 #17: rev 2's `capData : …`
was an undisplayed future package). -/
structure CapData (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) where
  capIrrOf : ∀ {P : Shape n}, PrefIdx n pol P → ℕ
  cap_law : CapIrrLaw p F n m pol capIrrOf     -- discharged by T-C2's family theorem
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

### 2.10 THE SEAM-VALUE DEFS — every package field a TYPED STATEMENT (REV 3)

Round 2's structural seam finding (Codex-2 #18, echoing rev 1's diagnosis): the §5
rows kept supplying "a name for a future value, not the value". This section is the
repair — every [3t]-owned field of the S-9 packages, and every carrier §5 cites, is
a DEF with a displayed body over the consumed corpus objects. DECLARATION-SITE
WARRANT (replacing rev 2's "MovesS re-points later" prose): the MovesS contract's
own preamble assigns the re-key here — "The typed forms below (carried from REV 9)
are each entry's CURRENT PIN — the contract MovesT/MovesV re-key when their
vocabulary exists" and "The former file plan (`MovesS/Interfaces.lean`) is retired
for these declarations" (MovesS blueprint §W4-SYNC preamble, verbatim). MovesS
wave 5 consumes these by import; no re-pointing act remains.

```lean
-- ===== the [3t] field values (the ∀-closures of the §3 unit statements) =====

/-- TREE-EXP (finite face), ∀-closed — the value of `RS1GivenPackage.tree_exp_fin`
and `XRBPackage`'s TREE-EXP consumption. Body = T-E8's statement, all hypotheses in
the premise row (nothing dropped, nothing strengthened). -/
def TreeExpFin (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (Tr : VTree p F) (L : SiteLedger Tr T CA χ), Function.Injective χ →
    RootCellsOf T CA χ → SibCount T CA χ → Realizes T χ Tr →
    ∀ (sc : TreeScaffold Tr T CA χ L),
    (∀ H ∈ Tr.chains, ∀ h2 : 2 ≤ L.sides H,
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H ‹_› h2)) →
    (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ m

/-- TREE-N, ∀-closed (`RS1GivenPackage.tree_n`) — T-E11's statement. -/
def TreeNStmt (pol : CanonPolicy p F) : Prop :=
  ∀ (N' : ℕ) (T : TreeModel p F n N' (n * N') pol) (CA : CellAssign _ _ _ _ _ _ T)
    (χ : Fin n → Fin (n * N')) (Tr : VTree p F) (L : SiteLedger Tr T CA χ)
    (sc : TreeScaffold Tr T CA χ L), Function.Injective χ → RootCellsOf T CA χ →
    SibCount T CA χ → Realizes T χ Tr → (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    (∀ H ∈ Tr.chains, ∀ h2 : 2 ≤ L.sides H,
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H ‹_› h2)) →
    Tr.thr n ≤ N' →
    Nat.card ↥{x : Box p (n * N') | Tr.fiberAt T χ x} * p ^ AofTr Tr L = p ^ (n * N')

/-- TREE-EXP's (ns) face, ∀-closed (`tree_exp_ns`) — T-E12's statement, WITH the
finite-face rider riding in the docstring at every consumption (§5 S-2). -/
def TreeExpNs (pol : CanonPolicy p F) : Prop :=
  ∀ (Tr : VTree p F) (H : History p F), (H ∈ Tr.chains ∧ Tr.nsLeaf H) →
    ∀ (N₀ : ℕ) (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
      (χat : ∀ N', Fin n → Fin (n * N'))
      (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
      (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)), JetTower Jat →
      (∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N') →
      Filter.Tendsto (fun N' => Mlev (Jat N'.1 N'.2) N'.1) Filter.atTop Filter.atTop →
      (∀ N' h, (stateTruncAt Jat N').Nonempty) →
      (∀ N' h, {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N') x}
        ⊆ nsTruncAt Jat Lat N') →
      Filter.Tendsto (fun N' : {k // N₀ ≤ k} =>
          (Nat.card ↥{x : Box p (n * N'.1) | Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x} : ℝ)
            / (p : ℝ) ^ (n * N'.1))
        Filter.atTop (nhds 0)

/-- ONE-F, ∀-closed (`one_f`) — T-F1's statement over the extensional quotient. -/
def OneFStmt (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
  ∀ x : Box p m, Decided T χ x →
    ∃ Tr : VTree p F, Tr.fiberAt T χ x ∧
      ∀ Tr' : VTree p F, Tr'.fiberAt T χ x → Tr.ext Tr'

/-- TB-CAP as amended, pinned (`tb_cap`): the (hen) cap-1 law + its finite-union
face (T-C1) and the (irr) per-class cross-level cap law (T-C2). NO (ns) leg — the
refutation record (§0). -/
def TBCapPinned (pol : CanonPolicy p F) (m : ℕ) : Prop :=
  (∀ (χ : Fin n → Fin m), Function.Injective χ → ∀ x x' : Box p m,
    (∀ b : Fin n, x (χ b) = x' (χ b)) → henPayload χ x = henPayload χ x') ∧
  (∀ (χ : Fin n → Fin m), Function.Injective χ → ∀ v₀ : Multiset Vd,
    ∃ G : Finset (Fin n → ZMod p),
      {x : Box p m | henPayload χ x = v₀} = ⋃ g ∈ G, rootCell χ g) ∧
  (∃ cap : ∀ {P : Shape n}, PrefIdx n pol P → ℕ, CapIrrLaw p F n m pol cap)

/-- the (ns) amendment pair, pinned (`ns_null`'s value together with (ns-lump)):
leg 1 = T-C3's conclusion ∀-closed (a THEOREM here); leg 2 = T-C7's truncated-ratio
statement ∀-closed. FINITE-FACE RIDER (binding, quoted at every consumption): leg 2
is the finite-level face ONLY; the profinite μ-claim is NOT stated in Lean. -/
def NsAmendedPair (pol : CanonPolicy p F) : Prop :=
  (∀ (N' m' : ℕ) (T : TreeModel p F n N' m' pol) (H : History p F)
    (J : JetSetup H n N' m') (Lf : NsLumpFamily T J),
    (∀ M M', M ≤ M' → Lf.L M' ⊆ Lf.L M) ∧
    nsClass T H = {x | T.mem (some H) x} ∩ ⋂ M, Lf.L M) ∧
  (∀ (H : History p F) (N₀ : ℕ) (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)), JetTower Jat →
    (∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N') →
    Filter.Tendsto (fun N' => Mlev (Jat N'.1 N'.2) N'.1) Filter.atTop Filter.atTop →
    (∀ N' h, (stateTruncAt Jat N').Nonempty) →
    Filter.Tendsto (fun N' : {k // N₀ ≤ k} =>
        (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ) / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0))

/-- VP pinned (`vp`): (c1)/(c3-a) = an inhabited cell-data verdict model; (c2) = the
KB-TOT bundle; VP-SOUND's two cites as the REMAINDER — exactly D4R.0-K(c)'s residual
"{VP-SOUND's cites}" (7634–7635). A structure of four named legs, not a name. -/
structure VPPinned (T : TreeModel p F n N m pol) (CA : CellAssign p F n N m pol T)
    (χ : Fin n → Fin m) : Prop where
  model : Nonempty (VerdictModelT T CA χ)
  covering : KBTot T
  hen_lift : HenLift p
  om_sat : OmSat p F

-- ===== the F/D-layer carriers §5 cites (REV 3 displays) =====

/-- the finite decided-slice partition premise (T-F3) — displayed (Fable-2 GAP-2). -/
def PartitionsDecided (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : Prop :=
  (∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, ¬ VTree.ext Tr Tr' →
    Disjoint {x | VTree.fiberAt Tr T χ x} {x | VTree.fiberAt Tr' T χ x}) ∧
  (∀ x : Box p m, Decided T χ x → ∃ Tr ∈ 𝒯, VTree.fiberAt Tr T χ x)

/-- pre-halt is η-CLASS data (T-F2's `hph`; §0 row) — owner HC-2. -/
def PreHaltClassData {P : Shape n} (pol : CanonPolicy p F) : Prop :=
  ∀ (i : PrefIdx n pol P) (H : History p F), H ∈ PrefSet n pol P → SameClass i H →
    (PreHalt H ↔ PreHalt (reprOf i))

/-- prefix-coherent representative choice (T-D11's premise) — owner HC-2
(PresentNorm). [`ClassPrefixOf` — the class-level prefix relation; E-phase keys it
to MovesD's PrefIdx class maps.] -/
def PrefixCoherentRepr (n : ℕ) (pol : CanonPolicy p F) : Prop :=
  ∀ {P P' : Shape n} (i : PrefIdx n pol P) (i' : PrefIdx n pol P'),
    ClassPrefixOf i' i → (reprOf i').IsPrefixOf (reprOf i)

-- ===== S-3's re-keyed premise, over the IMPORTED MovesS objects (REV 3) =====
-- imports: `LeanUrat.MovesS.Interfaces` (BUILT — `RS1Meas`, `βmeas`, `evalRe`)

/-- XRB's CONCLUSION equality — the `hxrb` premise the S-3 contract prescribes,
stated over the REAL imported `MovesS.RS1Meas.βmeas` (h-independence at pools). -/
def hxrbStmt {n' : ℕ} (T' : MovesS.TableShape n') (M : MovesS.MeasuredSide T')
    (B₀ : MovesS.RS1Meas T' M) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n') (h h' : ℕ) (τ : T'.State e)
    (σ' : Multiset T'.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    B₀.βmeas e he h τ σ' q₀ = B₀.βmeas e he h' τ σ' q₀

/-- W3_recursion, RE-KEYED per the S-3 demand ("assume XRB's CONCLUSION … re-keyed
form: `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`"): the premise row is the GIVEN
list + the ledger + `hxrbStmt` — never the bare `W2_xrb` implication. -/
def w3Rekeyed {n' : ℕ} {T' : MovesS.TableShape n'} {M : MovesS.MeasuredSide T'}
    (RB : MovesS.RatBurdens T' M) (hdc : MovesS.DegCons T')
    (given : Prop)               -- := `RS1GivenHolds Π'` (T-D12's premise row)
    (ledger_iv : Prop)           -- := `MovesS.LedgerIV T' M` at MovesS's re-key
    (B₀ : MovesS.RS1Meas T' M) : Prop :=
  given → ledger_iv → hxrbStmt T' M B₀ →
  ∀ e (he : e ∈ Finset.Icc 1 n') (τ : T'.State e) (σ' : Multiset T'.VType)
    (q₀ : ℚ) (hq : q₀ ∈ M.Pools), M.activeState q₀ e τ →
    ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
      = MovesS.evalRe T' M RB hdc e he τ σ' q₀ (fun e' he' => B₀.βmeas e' he' h_ent)
```

---

## §3 The unit DAG — 55 units (14 easy / 31 medium / 10 hard)

REV 2: two units added (T-F0 the box-free pre-halt bridge; T-D14 the S-6 chain-charge
carrier); every restated unit carries its rev-2 change inline.

### Layer V — VP: the verdict pin (§T.1) [9 units]

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

**T-V3 `MovesT.accEF_keyDeg` · `V3_accKeyDeg.lean` · medium — REV 3 (Fable-2 GAP-3:
rev 2's "second equality" was the first conjunct times μ, contentless). HONEST
SCOPE, recorded: `MovesSp.Species` carries NO independent cluster-degree field
(roster re-checked: tag/D/w/W/e/s0/ell/a/d/slots/lam/sel/flanks), so in SPECIES
vocabulary only the E·F = D′ leg is stateable — this unit states exactly that leg.
The display's genuine second identity "cluster degree = key degree·μ" IS stateable
in NODE vocabulary, where the degree datum exists (`Node.childWidth`, MovesC/Defs
465) — that is the NEW unit T-V9's second theorem; the pair covers 7078–7080 with
no contentless conjunct.**
```lean
theorem accEF_keyDeg {n : ℕ} (l : List MovesSp.Species) (sels : List (ℕ × ℕ))
    (hzip : l.length = sels.length ∧
      ∀ r s gm, l[r]? = some s → sels[r]? = some gm → s.sel = some gm)
    (hne : l ≠ []) (hroot : ∀ s, l.head? = some s → MovesSp.RootStage n s)
    (hchain : l.Chain' MovesSp.StageLaws)
    (s : MovesSp.Species) (hlast : l.getLast? = some s)
    (g μ : ℕ) (hsel : sels.getLast? = some (g, μ) ∧ s.sel = some (g, μ)) :
    (l.map fun t => t.e).prod * (sels.map Prod.fst).prod = s.e * g * s.D
```
moves_ref: 7078–7080, the E·F = key-degree leg: E·F = the CHILD key degree
D′ = e·g·D. deps: MovesSp.Defs (StageLaws, RootStage). sketch: list induction along
`Chain' StageLaws`: D_{r+1} = e_r·g_r·D_r with D₀ = 1 (RootStage) telescopes to
∏e·∏g = D′. hypothesis_fields: none (pure species bookkeeping). DOCSTRING DUTY: the
cluster-degree·μ leg lives at T-V9 (node side) — cite it, claim nothing here.

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

**T-V6 `MovesT.tau_total` · `V6_tauTotal.lean` · medium — REV 3 (Codex-2 #4: rev 2's
first disjunct was `… → True`, always true — the unit proved NO disposition. The
`→ True` literal is DEAD; both disjuncts now carry their full content, and the ns
leg consumes `KBTot.ns_lumps` so childlessness is the Theorem-B status, not a
definitional echo).**
```lean
theorem tau_total (T : TreeModel p F n N m pol) (hdi : KBTot T)
    (H : History p F) (x : Box p m) (hmem : T.mem (some H) x) :
    (∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      ((ν.μ = 1 ∧ IrrHalts (H.snoc ν hν)) ∨
        (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)) ∧
      ¬ (ν.μ = 1 ∧ 2 ≤ ν.μ)) ∧
    ((∀ ν : Node p F, ¬ T.child (some H) ν x) →
      NsHalts T (some H) x ∧
      ∃ (J : JetSetup H n N m) (Lf : NsLumpFamily T J), ∀ M, x ∈ Lf.L M)
```
STATEMENT DUTY: (i) every realized child receives EXACTLY ONE disposition —
saturate-and-halt (μ = 1, the extension IrrHalts) or continue (μ ≥ 2, the extension
realized) — from `hdi.dichotomy`, exclusivity by μ-arithmetic; (ii) a childless
realized state IS the (ns) status AND carries B(iii)'s all-heights vanishing datum
— from `hdi.ns_lumps` + the family's `tie` (the leg rev 2 left definitional; the
covering display's "no orphan" case analysis now has both halves typed).
moves_ref: 7112–7119 "COVERING, the case analysis (no orphan)". deps: Defs, T-V5.
hypothesis_fields: `hdi : KBTot T` (KB-TOT, owner HC-2/D4R0K — NEVER proved here).

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

**T-V8 `MovesT.shapeOfH_matches` · `V8_shapeOf.lean` · medium — REV 3 (Fable-2
CRIT-2: rev 2's premise `NodeDataLawful` could not source `ShapeWF`'s cross-node
clauses — dchain/window/gamTie/anchorTie/edvd/gmu/w0/wchain — and the only cited
route, the REAL `ShapeWF_of_matches` (MovesD/SW1_shapeWF.lean 67–72), DEMANDS
`HistoryCoherent` + card K₀ = p; counter-instance in §0's refutation record #5. The
rev-3 premise is `HistLawful` (§2.2) — the fence-compatible ONE-hypothesis shape:
strong enough for a FACTORED SW1 variant, still child-keying-free hence
Q1-insensitive, its own discharge queued on Q1 as an EXPLICIT fenced conditionality
(§0 row) — never a weaker substitute).**
```lean
theorem shapeOfH_matches (H : History p F) (n : ℕ) (hlaw : HistLawful p n H) :
    (shapeOfH H n).MatchesHist H ∧ ShapeWF n (shapeOfH H n)
theorem acc_pos (H : History p F) (hlaw : NodeDataLawful p H) :
    max (accE H) 1 = accE H ∧ max (accF H) 1 = accF H
```
moves_ref: §D4-R L3 dictionary (TB-CAP(irr) and thr(T) read thresholds off it,
7562–7566). deps: Defs, MovesD (NEW QUEUED UNIT on the MovesD side, additive-only:
`SW1b ShapeWF_of_lawful` — the SW1 proof refactored to consume exactly the
child-keying-free fragment; NO statement change to the existing `ShapeWF_of_matches`;
recorded in MovesD's manifest as a wave-4 companion). sketch: componentwise Matches
is definitional (readOf copies ν's fields; the w-card identity is the fragment's
p-power clause); ShapeWF via SW1b — each ShapeWF clause named to its `HistLawful`
source: dchain ← the Dwidth chain; window ← the window clause; gamTie ← the γ-tie;
anchorTie ← the anchor clause; edvd/gmu ← the per-node ledger clauses; w0 ← card
K₀ = p; wchain ← w-multiplicativity through MatchesHist + the K-card p-powers
[E-phase: wchain's node-side source is bound at SW1b's construction — any clause
SW1b needs beyond the §2.2 roster is ADDED to `HistLawful` with a MANIFEST
deviation, never silently assumed]; acc_pos: products of ≥-1 factors, from the
per-node face alone. FENCE NOTE: `HistLawful` carries NO child-keying clause — the
V10/Q1 steep-leg inconsistency cannot make this unit vacuous; no unit of this
corpus premises `HistoryCoherent` (rev-3 sweep; `WallAReconciled` references it
inside the BUILT `HC2.ReadsOf` as spec-only reconciliation target, §2.9 fence
note). InBox is subsumed: `HistLawful`'s root-box clause carries the L3 bound.
hypothesis_fields: `hlaw : HistLawful` (owner HC-2, discharge fenced-Q1 — §0).

**T-V9 `MovesT.irr_saturation` · `V9_irrSat.lean` · medium — NEW at REV 3
(Codex-2 #1's degree face + Fable-2 GAP-3's honest home): the τ-irr display's
degree content, in NODE vocabulary where the cluster-degree datum EXISTS.**
```lean
theorem acc_childWidth (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (hne : H.nodes ≠ []) :
    accE H * accF H = (H.nodes.getLast?).elim 1 (fun ν => ν.childWidth)
theorem irr_saturates (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (ν : Node p F) (hν : H.nodes.getLast? = some ν) :
    (accE H * accF H = accE H * accF H * ν.μ) ↔ ν.μ = 1
```
moves_ref: 7078–7080 "E := ∏e_r, F := ∏g_r … SATURATE the cluster degree —
E·F = d(cluster) … Saturation is equivalent to μ = 1 at the branch's latest read
(cluster degree = key degree·μ = E·F·μ)". The key degree at the latest read is the
node datum `ν.childWidth` (= e·g·Dwidth, MovesC/Defs 465); the Dwidth chain in
`HistLawful` telescopes it to accE·accF; the cluster degree is childWidth·μ, and
saturation ⟺ μ = 1 via accEF ≥ 1 (per-node lawfulness). Together with T-V3's
species leg this displays BOTH equalities of the note line with no contentless
conjunct (the rev-2 T-V3 defect). deps: Defs §2.2. sketch: list telescope on the
Dwidth chain; Nat.le arithmetic for the iff. hypothesis_fields: `hlaw` (§0).

### Layer C — TB-CAP per clause + the (ns) pair (§T.2) [8 units]

**T-C1 `MovesT.tbcap_hen` · `C1_capHen.lean` · medium — REV 3 (Codex-2 #22): the
finite-union face is a DISPLAYED second theorem, not prose.**
```lean
theorem tbcap_hen (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (x x' : Box p m) (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    henPayload χ x = henPayload χ x'
theorem tbcap_hen_cells (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (v₀ : Multiset Vd) :
    ∃ G : Finset (Fin n → ZMod p),
      {x : Box p m | henPayload χ x = v₀} = ⋃ g ∈ G, rootCell χ g
```
CAP N_V = 1, uniform per class — the class IS a finite union of level-0 cells, the
duty's literal shape. moves_ref: 7155–7159. deps: Defs. sketch: `redPoly χ x` is a
function of x ∘ χ (definitional); henDegrees/henPayload factor through it; G := the
finitely many g whose payload is v₀ (Fintype on Fin n → ZMod p).
hypothesis_fields: none. PROVED-IN-NOTE status: unconditional.

**T-C2 `MovesT.tbcap_irr` · `C2_capIrr.lean` · medium — REV 3 (Codex-2 #5: rev 2's
form was locality for ONE fixed `Presented` object with a cap read off an
N-dependent jet, no compatible family quantified). RESOLVED PER THE DISPLAY: the
cap is the display's own N(η′,⊤) = the jet cutoff `jetTopLevel` (7178–7180); its
CROSS-LEVEL CONSTANCY is now an explicit theorem consuming T-D7 (both jets' level
sets equal the SAME shape-side `bandLevels` — "u* ∈ P̂ makes the heights shape
data", 7181 — so the display's shape-computability claim is a THEOREM, and the
NP-ID consumption is EXPLICIT, never silent — the rev-1 sin does not recur); the
family law is then quantified over ALL presented N.**
```lean
noncomputable def capIrrOf {P : Shape n} {H : History p F}
    (J : JetSetup H n N m) : ℕ := jetTopLevel J
-- [`jetTopLevel J` := 1 + the largest base level among J's pinned equations at
--  Z = ⊤ — "N(η′,⊤) = 1 + the largest base level among T(η′,⊤)'s finitely many
--  equations" (7178–7180); E-phase types it off MovesC's `totalPins` support.]

theorem capIrr_uniform {P : Shape n} (i : PrefIdx n pol P)
    {N N' m m' : ℕ} (J : JetSetup (reprOf i) n N m) (J' : JetSetup (reprOf i) n N' m') :
    capIrrOf J = capIrrOf J'
-- the cross-level constancy: via T-D7 (NP-ID, in-corpus provable), each side's
-- pinned-equation level set = `bandLevels (P : ShapePrefix) n` — shape data.

theorem tbcap_irr {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx c < capIrrOf (S.jet i) → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i)

theorem tbcap_irr_family {P : Shape n} (i : PrefIdx n pol P)
    (hirr : IrrHalts (reprOf i))
    (J₀ : JetSetup (reprOf i) n N m) :     -- ONE reference jet fixes the ONE cap
    ∀ (N' : ℕ) (S : Presented p F n N' m pol P) (x x' : Box p m),
      (∀ c : Fin m, levelIdx c < capIrrOf J₀ → x c = x' c) →
      (x ∈ S.fiber i ↔ x' ∈ S.fiber i)
-- the COMPATIBLE FAMILY across all presented N (Codex-2 #5's demand): one cap per
-- class across the family — from `tbcap_irr` + `capIrr_uniform`. This theorem is
-- what discharges `CapIrrLaw` (§2.9) at cap := capIrrOf J₀, i.e. T-D3's cap datum.

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
N_V := N(η′,⊤) works … the level a function of η′'s shape/height data" + the
quantifier honesty 7183–7187 (per REALIZED halting branch-read; per (P, i), never
joined). deps: Defs, MovesD (Presented, D4R.4/L12 apparatus); T-D7 for
`capIrr_uniform` and the corollary — EXPLICIT dep. sketch: the class IS S(η′,⊤) by
definition of fiber; the finite-level cut is MovesD's D4R.4/L12 exact-realization,
restated as digit-locality below the jet's own cutoff; uniformity via D7a+D7b.
hypothesis_fields: `S.jet`/`J₀` (HC-2's PRESENT-EXIST supplies instances); `hnp` on
the corollary only.

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

**T-C5 `MovesT.nsZ_free` · `C5_nsFree.lean` · hard [pre-approved split C5a/C5b] —
REV 3 (Codex-2 #6: rev 2 quantified over EVERY `JetSetup` while the note fixes the
(ZC) setting — window interior, rim separation, slot-0 ladder; the setting is now
the explicit displayed premise `hzc : ZCPack J`, §2.5a).**
```lean
theorem nsZ_free {H : History p F} (J : JetSetup H n N m) (hzc : ZCPack J)
    (M : ℕ) (hM : M₀ J ≤ M) :
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
grid; freeness: interior coordinate at height > F(b) unpinned on Σ by
`hzc.inclusive_top`; rim leads never interior by `hzc.rim_sep`; the ladder count
from `hzc.slot0_grid`'s unit-spaced heights. THE ONE SUBSTANTIVE NEW PROOF of the
C-layer — the note's rev-2 (ns-null) mechanism, verified clean FOUR times
(9222–9223). This theorem also DISCHARGES `NsLumpFamily.slot0` at every presented
instance (the ladder is the same count). hypothesis_fields: `hzc : ZCPack J` (the
(ZC) package — standing perimeter, 7232–7233, now displayed §2.5a).

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

**T-C7 `MovesT.ns_null` · `C7_nsNull.lean` · medium — REV 3 (Codex-2 #7, all five
faces): (a) the function is total on the subtype {N' // N₀ ≤ N'} — nothing ill-typed
below N₀; (b) the jet family is a compatible TOWER (`JetTower`, displayed); (c) the
frozen-Mlev degeneracy is excluded by the explicit growth premise `hMgrow` (the
Scale map is unbounded along the tower — C.1.5, owner HC-2's instance); (d) the
denominator is nonempty by `hne` (realized states have members at every level);
(e) the profinite bridge stays EXCLUDED by the finite-face rider (unchanged — that
part of rev 2 was honest and stays).**
```lean
def Mlev (J : JetSetup H n N m) (N' : ℕ) : ℕ := scaleTop J N'
-- [M(N) := the largest window height with base level < N — C.1.5's Scale map read
--  off J's chart (7205–7207); E-phase binds `scaleTop` to the Scale accessor.]

/-- the jet family is a LEVEL TOWER: the deeper jet's pinned system truncates to the
shallower jet's (same state, same chart, more levels). REV 3 (Codex-2 #7(b)).
[E-phase: the truncation map bound to MovesC's level-restriction of `totalPins`.] -/
def JetTower {H : History p F} {N₀ : ℕ}
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N')) : Prop :=
  ∀ (N' N'' : ℕ) (h' : N₀ ≤ N') (h'' : N₀ ≤ N''), N' ≤ N'' →
    SystemTruncatesTo (Jat N'' h'') (Jat N' h')
-- [`SystemTruncatesTo J₂ J₁` := J₂'s pinned equations at levels ≤ N' are exactly
--  J₁'s, under the coordinate embedding Box p (n·N') ↪ Box p (n·N'') — E-phase.]

def stateTruncAt (Jat : …) (N' : ℕ) : Set (Box p (n * N')) :=
  (Jat N' _).SHZ (topLocus p (n * N'))          -- the truncated state count
def nsTruncAt (Jat : …) (Lat : …) (N' : ℕ) : Set (Box p (n * N')) :=
  stateTruncAt Jat N' ∩ (Lat N' _).L (Mlev (Jat N' _) N')   -- state ∩ lump L_{M(N)}

theorem ns_null {H : History p F} (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1)
      Filter.atTop Filter.atTop)
    (hne : ∀ N' h, (stateTruncAt Jat N').Nonempty) :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ)
        / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0)
```
moves_ref: 7210–7231 — THE FINITE-LEVEL FACE: "μ(Σ ∩ L_M) → 0, and the class =
∩_M (Σ ∩ L_M) gives μ((τ-ns) class │ Σ) = 0 by continuity from above." SCOPE RIDER
(carried, binding on every consumer, quoted in T-D12's S-2 row): this corpus states
ONLY the truncated-ratio limit; continuity-from-above and the profinite class NEVER
enter; any consumer reading the note's measure-zero claim off this field must add
its own finite→profinite bridge. deps: T-C3, T-C4, T-C5, T-C6. sketch: per level,
T-C6 gives ratio = p^{−|Z_{M(N')}|} (denominator > 0 by `hne`); T-C5's ladder count
+ `hMgrow` + T-C4's limit squeeze (`htw` aligns the per-level systems so the counts
compare). hypothesis_fields: the jet family `Jat` + `htw`/`hMgrow`/`hne` (HC-2's
PRESENT-EXIST faces) + the lump families `Lat` (§2.5a; B(iii) tie, owner D4R0K).

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
cell events; REV 3: over the ENTRANCE carrier (the F1 gate site is a `.red` cell —
Codex-2 #8's kernel face).**
```lean
theorem sibCount_pair_form (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) (h : SibCount T CA χ)
    (es : EntSt p F n) (c : CA.Cell)
    (hcard : (CA.branchSetOf c).card = 2) (S : Node p F → Set (Box p m))
    (hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
      S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) :
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * Nat.card ↥(cellEventE T CA χ es c)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)
```
moves_ref: 7292 the display; 7523–7525 "P3's censused identity 78,125² =
15,625·390,625 is exactly (SIB) at this site" — the m = 2 specialization IS the
gate-checked shape, and the F1 site (14-pin Σ_c = reduction cell + window data) is
the `.red`-entrance instance — reachable by the rev-3 kernel, unreachable by rev
2's Option-state quantifier. deps: Defs §2.6. sketch: instantiate; card 2,
exponent 1. hypothesis_fields: `h : SibCount T CA χ` (the kernel — this unit only
RESHAPES it).

**T-S2 `MovesT.sib_falsifier` · `S2_sibFalse.lean` · medium — REV 2 (Fable GAP-6):
the falsifier's decide surface is the FINITE SURROGATE; the bridge to the real Prop
is a hand lemma (see Layer G's gate architecture).**
```lean
theorem sib_falsifier : ∃ (T : TreeModel 2 (ZMod 2) 2 1 2 polTriv)
    (CA : CellAssign 2 (ZMod 2) 2 1 2 polTriv T), ¬ SibCount T CA toyχ
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
    (hrc : RootCellsOf T CA χ) (h : SibCount T CA χ) :
    ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
      2 ≤ (CA.branchSetOf c).card →
      (∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
      Nat.card ↥(cellEventE T CA χ .amb c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
          * (Nat.card ↥(cellEventE T CA χ .amb c)) ^ ((CA.branchSetOf c).card - 1)
        = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ .amb c ∩ S ν)
```
moves_ref: 7298–7304 "DEPTH-0 INSTANCE: (SIB) at η = ∅ is the root read's
cross-cluster product … the root product's citation authority is the Montes-L1 cite
(D4R0K O4's scope note) … the clause stays under the (SIB) tag." deps: Defs.
sketch: specialize es := .amb (⊆ `SibCountShallow`'s clause, derived not re-assumed).
RECORD (do not encode): JOINT-D1 is single-cluster EVIDENCE, not the theorem — the
root clause carries NO separate hypothesis; it rides the same `hsib` tag (the rev-6
Fable repair, 9196–9201). hypothesis_fields: `h : SibCount T CA χ`, `hrc`.

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
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m)
    (hpres : SitePresents T CA χ es c Sigma fd)
    (hfree : ∀ cl ∈ fd.clauses, ∀ cIdx ∈ cl.support, Sigma.pinned cIdx = false) :
    Nat.card ↥(cellEventE T CA χ es c) * p ^ fd.mstar = Nat.card ↥(entEvent T χ es)
```
moves_ref: 7469–7472 "(JC-single) PROVED (= C.1.5(1) verbatim): at a site whose
window hull has ONE side, the joint cell IS a single §C read stratum with its
values." REV 3: over the entrance carrier — a track's first window read now charges
against its REDUCTION CELL (Codex-2 #8). deps: MovesC.C4_conditionalMass, Defs §2.5.
sketch: rewrite both events by `hpres`; the conclusion is `C4_conditionalMass`'s
identity verbatim (`Sigma.mass` = the entrance count through hpres's second
conjunct). hypothesis_fields: `hpres` (the jet-site tie — HC-2 face); no new
strength (the note marks this clause PROVED via C.1.5(1), BUILT in MovesC).

**T-E4 `MovesT.jcMulti_branching` · `E4_jcMultiBranch.lean` · medium — REV 2 (Fable
CRIT-2 fixed at §2.5's `JCmultiAt`; Fable GAP-7: the branching corollary now
concludes k ≤ card, the display's "k sides ⟹ ≥ k branches").**
```lean
theorem jcMulti_branching (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (c : CA.Cell) {fd : FreshData p m}
    (ss : SideSplit T CA c fd) :
    ss.k ≤ (CA.branchSetOf c).card
```
moves_ref: 7473–7483 "(JC-multi) OPEN, displayed … A multi-side site is always a
BRANCHING site (k sides ⟹ ≥ k branches), so unbranched segments never consume
(JC-multi)." deps: Defs §2.5. sketch: j ↦ (side_ne j).choose is injective into the
branch set (sideOf is a function); `Finset.card_le_card_of_injOn`. The DEF
deliverable (`JCmultiAt`, the open obligation typed at the site) moved to §2.5;
this unit proves the displayed consequence. hypothesis_fields: `JCmultiAt` is NEVER
proved — hypothesis `hjcm` downstream, PER-SITE only.

**T-E5 `MovesT.fiber_root_split` · `E5_rootSplit.lean` · hard — REV 3 (Fable-2
CRIT-1 + Codex-2 #10): (a) `hreal` restored — the display quantifies over REALIZABLE
trees (7449–7451), and the henV-emptied flip (fiber ∅, RHS > 0) now fails a
hypothesis (§0 refutation record #4); (b) the ROOT DECOMPOSITION is supplied —
`RootSplitData` gains the constructive head roster (`headOf`, injective) so the
`Fin t` tracks are IDENTIFIED with the tree's own head chains, and the sketch names
the branch-set bridge (heads = the root cell's branch set on fiber members, via
fiberAt (i) + `mem_single` + `child_cell` + `hrc`) — nothing at t = 0 concludes a
positive count any more (`hreal` forces the fiber inhabited, and fiberAt's degree
clause (v) kills the track-dropping trees). Exponent `numTracks` (rev-2 arithmetic,
census-verified: t = 1 F1: 5⁶·5⁴·5¹⁸ = 5²⁸ = 5²²·5⁶ ✓; p = 2: 8·2³·2⁶ = 2¹² ✓).**
```lean
structure RootSplitData (Tr : VTree p F) (g : Fin n → ZMod p) where
  t : ℕ                                        -- the window-opening tracks
  trackChains : Fin t → Set (History p F)      -- head-node partition of Tr.chains
  hpart : (⋃ i, trackChains i) = Tr.chains ∧
    Pairwise (Function.onFun Disjoint trackChains)
  headOf : Fin t → Node p F                    -- REV 3: the CONSTRUCTIVE head roster
  hhead : ∀ i, ∀ H ∈ trackChains i, H.nodes.head? = some (headOf i)
  hinj : Function.Injective headOf             -- distinct tracks, distinct heads
  hne : ∀ i, (trackChains i).Nonempty
  hcov : ∀ i, oneNode (headOf i) ∈ Tr.chains   -- each head IS a chain of Tr
-- [`oneNode ν` := the one-node history ⟨[ν]⟩.] τ-hen tracks carry NO chain (7069):
-- they constrain only through g — leaf factors 1, absent from the product
-- (7490–7491). With `hpart` (∪ = chains) every chain of Tr lies over exactly one
-- head: the roster EXHAUSTS the tree's tracks — no omission, no duplication.

def trackEvent (Tr : VTree p F) (T : TreeModel p F n N m pol) {g : Fin n → ZMod p}
    (htracks : RootSplitData Tr g) (i : Fin htracks.t)
    (hcr : ChildRoot none (htracks.headOf i)) : Set (Box p m) :=
  {x | SubFiber T (htracks.trackChains i) (htracks.headOf i) hcr Tr.leafV Tr.nsLeaf x}

theorem fiber_root_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hsib : SibCount T CA χ) (hreal : Realizes T χ Tr)
    (g : Fin n → ZMod p) (htracks : RootSplitData Tr g)
    (hcr : ∀ i, ChildRoot none (htracks.headOf i))
    (hfib : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * (Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n
      = p ^ m * ∏ i : Fin htracks.t,
          Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i))
```
moves_ref: 7485–7495 "ROOT CLAUSE: μ(fiber T) = jvol({f̄ = g}) · ∏_{tracks i}
μ(S_{T_i} │ Σ₀) = p^{−n} · ∏_i μ(S_{T_i} │ Σ₀)" — division-free with
card(Σ₀)·p^n = p^m: card(fiber)·card(Σ₀)^t·p^n = p^m·∏ᵢ card(Σ₀ ∩ Sᵢ), exponent
t = numTracks. deps: T-E1, T-E2, T-S1/T-S3. sketch — THE DECOMPOSITION CHAIN
(Codex-2 #10, each step named): (1) on any fiber member x, fiberAt (i) +
`mem_single` give: heads of Tr.chains = the realized root children of x; (2)
`child_cell` at o = none + `hrc` identify those with the g-cell's branch set —
`headOf` enumerates it (injectivity `hinj`, coverage `hcov`+`hpart`); (3) fiberAt
therefore decomposes: fiber = rootCell χ g ∩ ⋂ᵢ trackEvent i, with the hen payload
determined by g (T-C1) and the degree clause (v) securing that NO realized track is
missing from the roster; (4) SibCount at es = .amb over the g-cell's branch set (the
S-function: S (headOf i) := trackEvent i, halted members' events are their own
one-chain SubFibers — every branch member IS a head by (2)); (5) T-E2 converts
card(Σ₀)·p^n = p^m. t = 1 needs no SIB (single factor); t = 0 (all-Hensel trees):
the product is empty and the identity is exact for fully-split g — `hreal` +
clause (v) exclude the repeated-factor degeneracy Codex-2 #10 exhibited. LEDGER
CHECK (7491–7495: F1's 14-pin split) = Gates layer (T-G1). difficulty: hard.
hypothesis_fields: `hsib` (SIB — OPEN); `hrc`; `hreal` (the display's qualifier);
the Montes-L1 root authority is the SAME tag (T-S3's record).

**T-E6 `MovesT.fiber_seg_step` · `E6_segStep.lean` · medium — REV 3 (Fable-2 CRIT-3
+ Codex-2 #11): the state↔cell tie is CONSUMED AS THE LEDGER FIELD `state_cell` —
rev 2 derived nothing from `L.presents` alone (the child state was a UNION of cell
events; §0 refutation record #6) — and the entrance is the CARRIER value
(`L.parentSt H : EntSt`), so the head-read step conditions on the reduction cell
(Codex-2 #8's first-window-step defect).**
```lean
theorem fiber_seg_step (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (Tr : VTree p F) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : L.sides H = 1)          -- one-side site (the ledger's hull datum, §2.5)
    (E : Set (Box p m)) (hspec : SpectatorFor (L.freshCoords H) E) :
    Nat.card ↥(stateEvent T (some H) ∩ E) * p ^ L.siteExp H
      = Nat.card ↥(entEvent T χ (L.parentSt H) ∩ E)
```
moves_ref: 7496–7499 "UNBRANCHED SEGMENT: along a maximal single-branch run, each
site is one-side/one-factor, so (JC-single) applies … multiply the running mass by
jvol(c_s │ Σ) = vol_nom(E_fresh(ν_s)) at each site." deps: T-E3, MovesD
(TreeModel.mem_snoc), Defs §2.5. sketch: `L.state_cell hH hone` rewrites the LHS
state event into the presented cell event (the tie — a FIELD, never re-derived);
`L.presents` rewrites both sides into the stratum form; C4's count law relativizes
to E by `hspec` (the fresh coordinates are free of E — the standard C.1.5 spectator
step). hypothesis_fields: the ledger `L` incl. `state_cell` (owner HC-2, §0 —
Q2-adjacent) ; `hspec` (explicit, rev 2).

**T-E7 `MovesT.fiber_first_split` · `E7_firstSplit.lean` · hard — REV 3 (Fable-2
GAP-4: rev 2 PROMISED "two displayed conjuncts" but displayed one, with `hcharge`
assumed and unused; Codex-2 #12: the jvol factor was absent from the conclusion).
The conclusion is now the CONJUNCTION: (A) the SIB product at the cell event; (B)
the CHARGE-COMPOSED first-split display — the note's
μ(fiber│Σ) = jvol(c│Σ)·∏ μ(S_j│Σ_c) cross-multiplied division-free, with `hcharge`
CONSUMED. The entrance is the carrier value (deep splits at .st states, root-track
splits at .red entrances).**
```lean
structure SplitSiteData (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m) where
  es : EntSt p F n                       -- the split site's entrance state (REV 3)
  c : CA.Cell                            -- its joint cell
  hbr : 2 ≤ (CA.branchSetOf c).card
  jointExp : ℕ                           -- the site's charge exponent (REV 3:
    -- DISPLAYED datum — one-side: fd.mstar; multi-side: the SideSplit sum, which
    -- the §2.5 clause-partition ties to the same mstar)
  S : Node p F → Set (Box p m)           -- the member-indexed child events
  hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec,
    S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ
  -- [`stOf es` := the Option-state under the child events: .st H ↦ some H;
  --  .red g ψ / .amb ↦ none — E-phase plumbing]
  hdecomp : {x | Tr.fiberAt T χ x} ∩ entEvent T χ es
    = cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν
  -- the first-split fiber identification at this site — a FIELD here so E7 states
  -- one recursion frame; E8 receives the per-site family through its SCAFFOLD
  -- hypothesis (REV 3, Codex-2 #13 — no longer "proved in E8" by promise)

theorem fiber_first_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hsib : SibCount T CA χ) (d : SplitSiteData Tr T CA χ)
    (hcharge : Nat.card ↥(cellEventE T CA χ d.es d.c) * p ^ d.jointExp
      = Nat.card ↥(entEvent T χ d.es)) :
    -- (A) (SIB) at c, the member-indexed product (7510), through hdecomp:
    (Nat.card ↥({x | Tr.fiberAt T χ x} ∩ entEvent T χ d.es)
        * (Nat.card ↥(cellEventE T CA χ d.es d.c)) ^ ((CA.branchSetOf d.c).card - 1)
      = ∏ ν ∈ CA.branchSetOf d.c,
          Nat.card ↥(cellEventE T CA χ d.es d.c ∩ d.S ν)) ∧
    -- (B) the composed display WITH the jvol charge (hcharge CONSUMED):
    -- μ(fiber│Σ) = jvol(c│Σ)·∏ μ(S_j│Σ_c), division-free:
    (Nat.card ↥({x | Tr.fiberAt T χ x} ∩ entEvent T χ d.es) * p ^ d.jointExp
        * (Nat.card ↥(cellEventE T CA χ d.es d.c)) ^ (CA.branchSetOf d.c).card
      = Nat.card ↥(entEvent T χ d.es)
        * ∏ ν ∈ CA.branchSetOf d.c,
            Nat.card ↥(cellEventE T CA χ d.es d.c ∩ d.S ν))
```
moves_ref: 7503–7515 "FIRST SPLIT: … Charge jvol(c │ Σ) — the FORMERLY MISSING
FACTOR, now explicit — supplied by (JC-single) or (JC-multi) — then by (SIB) at c
… μ(fiber T │ Σ) = jvol(c │ Σ) · ∏_{j=1}^m μ(S_{T_j} │ Σ_c)"; halted children =
`Set.univ` legs (factor = full cell — 7509). deps: T-E3, §2.5 (JCmultiAt), T-S1.
sketch: (A) rewrite by hdecomp; apply hsib at (es, c). (B) multiply (A) by
card(cellEvent) and substitute hcharge — check: (A)·C, then C·p^k = card(Σ) gives
card(f∩Σ)·p^k·C^m = card(Σ)·∏ — the display verbatim. `hcharge` is DISCHARGED by
T-E3 at one-side sites and rides as `JCmultiAt` (the hjcm tag) at multi-side sites
— the PER-SITE consumption the note prescribes (7506–7508, 7451–7452). The REL.2
identification of children as smaller-degree theory (7511–7513) is NOT consumed —
the Lean recursion is on node count alone (7529–7530). hypothesis_fields: `hsib`;
`hcharge` per site (T-E3-discharged or hjcm-tagged).

**T-E8 `MovesT.treeExp` · `E8_treeExp.lean` · hard — REV 3 (Fable-2 CRIT-1: `hreal`
restored — the henV-flip refutation, §0 record #4; Codex-2 #13: the recursion's
structural data are now the EXPLICIT scaffold hypothesis `sc`, not sketch
promises).**
```lean
def multiSites (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) : Set (History p F) :=
  {H | H ∈ Tr.chains ∧ 2 ≤ L.sides H}    -- REV 3: off the ledger's hull datum
                                          -- (rev 2's fd.oneSide label retired)

/-- the RECURSION SCAFFOLD — REV 3 (Codex-2 #13): everything T-E8's induction
consumes beyond the ledger, as TYPED per-tree data: the root decomposition, the
per-branching-site split frames (each with its `hdecomp` identification), and the
child-subtree partition above each split. Owner of instances: HC-2's presented
faces (with T-E5's bridge steps (1)–(3) discharging `root`'s roster on fiber
members). "Ledger sites = the tree's read sites" is BY CONSTRUCTION (both are keyed
by `Tr.chains`, which fiberAt (i) makes the realized read sites). -/
structure TreeScaffold (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) where
  g : Fin n → ZMod p                            -- the fiber's root datum
  hg : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g
  root : RootSplitData Tr g
  hcr : ∀ i, ChildRoot none (root.headOf i)
  splitFrame : ∀ H ∈ Tr.chains, 2 ≤ (CA.branchSetOf (L.cellAt H)).card →
    SplitSiteData Tr T CA χ                     -- one recursion frame per split,
  hframe : ∀ H hH h2, (splitFrame H hH h2).es = L.parentSt H ∧
    (splitFrame H hH h2).c = L.cellAt H         -- keyed to the ledger's site data
  subtree_part : ∀ H hH h2, ∀ ν ∈ CA.branchSetOf (L.cellAt H),
    ∃ Cν : Set (History p F), Cν ⊆ Tr.chains ∧
      (∀ H' ∈ Cν, H.IsPrefixOf H') ∧
      ((splitFrame H hH h2).S ν = Set.univ ∨
        (splitFrame H hH h2).S ν
          = {x | ∃ hν Tsub leafSpec nsSpec, ContFiber T (some H) ν hν Tsub
              leafSpec nsSpec x ∧ Tsub = Cν})
    -- the child-subtree partition: each branch member's event is carried by its
    -- own chain subset above the split [E-phase: the ∃-packaging is bound to
    -- ContFiber's actual argument order]

theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hsib : SibCount T CA χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L)
    (hjcm : ∀ H ∈ multiSites Tr T CA χ L, ∀ h2 : 2 ≤ L.sides H,
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H ‹H ∈ Tr.chains› h2))
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) :  -- ALL leaves (τ-irr)/(τ-hen)
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m
```
moves_ref: 7449–7456 "(TREE-EXP) … for every complete finite REALIZABLE canonical
tree T ALL of whose leaves are (τ-irr)/(τ-hen) … μ{f : T_can^τ(f) = T} =
∏_{read sites s of T} jvol(c_s │ Σ_{<s}), every site charged exactly once — the
ROOT INCLUDED" — `hreal` is that quantifier's Lean face; the (NS) clause 7457–7461
EXCLUDED BY `hdet`. deps: T-E5, T-E6, T-E7, T-E2. sketch: strong induction on
Tr.chains' card via the first-split decomposition: root clause (E5 with sc.root),
unbranched runs (E6 via `state_cell`, spectator events carrying the other sides'
pins across sub-recursions), terminal leaves (factor 1 — verdict is cell data of
the last site, TB-CAP exhibits the class: T-C1/T-C2), first split (E7 at
sc.splitFrame, hcharge from E3 or hjcm BY SIDE COUNT — single-side trees never
touch hjcm; sc.subtree_part hands each factor to the strictly smaller subtree).
Every site in exactly one recursion frame ⇒ each site charged once. difficulty:
hard (the corpus centerpiece). hypothesis_fields: `hsib` (SIB), `hjcm` (JC-multi,
THIS tree's multi-side sites only), `L` (incl. `state_cell` — §0), `sc` (HC-2's
presented faces), `hdet`, `hrc`, `hreal`.

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
-- REV 3 note: the conclusion IS `VTree.ext Tr Tr'` (§2.5) definitionally — the
-- quotient bridge T-F1/T-E13 consume, in-statement (Codex-2 #24).
```
moves_ref: 7025–7029 "one f, ONE tree … a genuine PARTITION of the decided set".
deps: Defs. sketch: clause (i) is a graph equality (Set.ext); clause (ii) now pins
leafV on BOTH legs (irr value = irrVerdictOf H, ns value = nsVerdictOf H — both
functions of H alone) and nsLeaf (the ns leg carries ¬IrrHalts, the irr leg
¬nsLeaf, and the τ-disjunction at x decides which leg both trees are on); clause
(iii) pins henV. hypothesis_fields: none — the CHOICE-FREENESS payoff,
unconditional.

**T-E10 `MovesT.perShape_law` · `E10_perShape.lean` · hard — REV 3 (Codex-2 #14,
all four faces): (a) the undisplayed `TreeShape`/`TreeShapeOf`/`Ashape`/`CofShape`
quartet is RETIRED — the summation domain is the `ShapeEquiv`-class (§2.5,
displayed) of a REPRESENTATIVE tree, so the class count IS the cardinality of
exactly the summation domain (definitional, no separate carrier); (b) the per-shape
exponent constancy is the EXPLICIT premise `hA` (the note's shape-determination
7537–7540, an owner-supplied law, no longer implicit); (c) finiteness is the
explicit premise `hfin` — no unguarded infinite ∑ᶠ; (d) the domain carries
`Realizes` (Fable-2's CofShape note: the "realized" bracket typed against the SAME
realization predicate as E5/E8/E11).**
```lean
def NsFree (Tr : VTree p F) : Prop := ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H

def shapeClass (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : Set (VTree p F) :=
  {Tr | ShapeEquiv n Tr Tr₀ ∧ NsFree Tr ∧ Realizes T χ Tr}

theorem perShape_law (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hsib : SibCount T CA χ)
    (hfin : (shapeClass Tr₀ T χ).Finite)
    (L₀ : SiteLedger Tr₀ T CA χ)
    (Lat : ∀ Tr ∈ shapeClass Tr₀ T χ, SiteLedger Tr T CA χ)
    (scat : ∀ Tr h, TreeScaffold Tr T CA χ (Lat Tr h))
    (hjcm : ∀ Tr h, (T-E8's per-site hjcm row at (Tr, Lat Tr h)))
    (hA : ∀ Tr h, AofTr Tr (Lat Tr h) = AofTr Tr₀ L₀) :
    (∑ Tr ∈ hfin.toFinset, Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x})
        * p ^ (AofTr Tr₀ L₀)
      = Nat.card ↥(shapeClass Tr₀ T χ) * p ^ m
```
moves_ref: 7537–7545 "Σ_{T of shape T̂} μ(fiber T) = C_T̂(p) · p^{−A(T̂)}, with NO
multiplicity weights — the tree fibers are genuinely disjoint" — stated for
TREE-EXP's domain (all leaves (τ-irr)/(τ-hen), REALIZABLE, 7449–7451; the (ns)
trees are 7457–7461's separate clause, NOT summed here). C_T̂ := the class's own
`Nat.card` — "counted directly on individuated members" (7542); A(T̂) := the
representative's `AofTr` with `hA` the shape-determination law ("(JC-single): §C
C.3 with u* ∈ P̂ per §D4-R L3; (JC-multi): shape-determined GIVEN its side-product
form" — owner: the shape-side theory through T-V8's dictionary; an explicit
premise, not a silent constancy). deps: T-E8, T-E9, T-V8, MovesD (shape
exponents). sketch: every summand tree is realizable + ns-free, so T-E8 applies
with the SAME exponent by `hA`; sum the constant (D10's idiom); disjointness never
needed for the SUM but IS the no-multiplicity-weights content — cite T-E9 in the
docstring. MULTINOMIAL SCOPE (7548–7557): the m!/(∏ mⱼ!) factorization is NOT
claimed — record verbatim in the docstring. difficulty: hard. hypothesis_fields:
`hsib`, `hjcm` (per-site, per summand tree), `Lat`/`scat` (ledgers + scaffolds),
`hA`, `hfin`.

**T-E11 `MovesT.treeN` · `E11_treeN.lean` · hard — REV 3 (Fable-2 CRIT-1: `hreal`
restored — "complete finite REALIZABLE with all leaves (τ-irr)/(τ-hen)" is the
display's own hypothesis row, 7559–7561; rev 2's `thr` read no henV and the
henV-flip satisfied everything); scaffold threaded as at T-E8.**
```lean
theorem treeN (Tr : VTree p F) (T : TreeModel p F n N (n * N) pol) -- m := n·N level
    (CA : CellAssign p F n N (n * N) pol T) (χ : Fin n → Fin (n * N))
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (hreal : Realizes T χ Tr)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hthr : Tr.thr n ≤ N) (hsib : SibCount T CA χ)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L)
    (hjcm : (T-E8's per-site hjcm row)) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N)
```
moves_ref: 7559–7574 "TREE-N (finite-level stability): let T be complete finite
realizable with all leaves (τ-irr)/(τ-hen) … for every N ≥ thr(T):
#{f mod p^N : T_can^τ(f) = T} = p^{nN} · μ(fiber T) — the fiber is a FINITE
intersection of finite-level digit-cell conditions … an exact union of level-N
residue classes." deps: T-E8, T-C1, T-C2, T-V8 (thr via shapeOfH), MovesD D4R4all.
sketch: T-E8 at the working level; thr joins the branch thresholds, the leaf caps
(T-C1/T-C2 — `capIrrOf` is cross-level constant by `capIrr_uniform`, so ONE cap
serves all levels), and the site levels (`siteLevel`); above it every condition is
an exact residue-class union. X.3-FREE (7047–7048); GIVEN (SIB) + (JC-multi at
multi-side sites) "for the mass value" (7576–7577). hypothesis_fields: `hsib`,
`hjcm` (per-site), `L`, `sc`, `hdet` (verbatim 7241–7243), `hrc`, `hreal`.

**T-E12 `MovesT.treeN_ns` · `E12_treeNns.lean` · medium — REV 3: the T-C7 rev-3
premise row threaded verbatim (JetTower, Mlev growth, nonempty denominators,
subtype domain — Codex-2 #7's faces apply here identically).**
```lean
theorem treeN_ns (Tr : VTree p F) (H : History p F)
    (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1)
      Filter.atTop Filter.atTop)
    (hne : ∀ N' h, (stateTruncAt Jat N').Nonempty)
    (hdom : ∀ N' h, {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N') x}
      ⊆ nsTruncAt Jat Lat N') :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥{x : Box p (n * N'.1) |
          Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x} : ℝ) / (p : ℝ) ^ (n * N'.1))
      Filter.atTop (nhds 0)
```
moves_ref: 7574–7576 "For (ns)-leaf trees the identity is REPLACED by the
NORMALIZED capped bound of §T.2 (p^{−nN}·count ≤ μ(lump ∩ …) → 0; the raw count
need NOT tend to 0)." deps: T-C7, T-C8 (hdom is T-C8's inclusion cut to the
truncated lump at each level — E-phase derives it there). sketch: domination +
T-C7's vanishing ratio; squeeze (state counts ≤ p^{nN}). hypothesis_fields: T-C7's
(jet family, lump families).

**T-E13 `MovesT.tgt_finadd` · `E13_tgtFinAdd.lean` · easy — REV 3 (Codex-2 #24):
disjointness is DERIVED from T-E9 through the DISPLAYED `VTree.ext` (§2.5) — the
premise is extensional distinctness of the family, never an assumed disjointness
over raw structure values; the quotient bridge is in-statement, not prose.**
```lean
theorem tgt_finadd (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m)
    (hpair : ∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, Tr ≠ Tr' → ¬ VTree.ext Tr Tr') :
    Nat.card ↥(⋃ Tr ∈ 𝒯, {x | VTree.fiberAt Tr T χ x})
      = ∑ Tr ∈ 𝒯, Nat.card ↥{x | VTree.fiberAt Tr T χ x}
```
moves_ref: 7017–7030 (TGT)'s regrouping license AT FINITE LEVEL; the DENSITY form
stays X.3-tagged and UNSTATED (§0). deps: T-E9. sketch: pointwise, a shared fiber
member of Tr ≠ Tr' would give `VTree.ext Tr Tr'` BY T-E9 (its conclusion tuple IS
`ext`), contradicting `hpair` — disjointness derived, then Nat.card of finite
disjoint unions. hypothesis_fields: none (hpair is the family's ext-distinctness —
T-F3's `PartitionsDecided` supplies it, same ¬ext form).

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

**T-F1 `MovesT.oneF` · `F1_oneF.lean` · easy — REV 3 (Codex-2 #24's quotient face):
stated through the DISPLAYED `VTree.ext` (§2.5) — no undisplayed `VTreeExt`
carrier; uniqueness IS uniqueness-up-to-ext, which T-E9's tuple delivers verbatim.**
```lean
theorem oneF (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃ Tr : VTree p F, Tr.fiberAt T χ x ∧
      ∀ Tr' : VTree p F, Tr'.fiberAt T χ x → VTree.ext Tr Tr'
```
moves_ref: 7579–7589 "(ONE-F) … f HAS exactly one tree, the tree exactly one shape
… No reciprocal/Möbius weights w(f, η) exist or are needed." INDEPENDENT of
TREE-EXP (7580–7581). deps: T-E9. sketch: existence = Decided's witness; the
up-to-ext clause = T-E9 (its conclusion IS `ext`). NO hsib, NO hjcm — totality +
choice-freeness alone. hypothesis_fields: none. This is `OneFStmt` (§2.10)
pointwise — the package field's value.

**T-F2 `MovesT.preHalt_dict_ptwise` · `F2_dictPtwise.lean` · hard — REV 3
(Codex-2 #15: the class↔chain bijection was asserted without its two legs). The
LHS counts CLASSES through one representative, the RHS raw CHAINS; the bijection's
missing warrants are now EXPLICIT premises: `hph` (PreHalt is η-class data — rev 2
silently transported `PreHalt (reprOf i)` across the class) and `hsep` (distinct
chains of ONE realized tree lie in distinct classes — without it two chains could
share a class and the counts differ). Both §0-rowed, owner HC-2.**
```lean
theorem preHalt_dict_ptwise {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (Tr : VTree p F) (x : Box p m) (hfib : Tr.fiberAt T χ x)
    (hsep : ∀ H H', H ∈ Tr.chains → H' ∈ Tr.chains →
      H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      (∃ i : PrefIdx n pol P, SameClass i H ∧ SameClass i H') → H = H') :
    Nat.card {i : PrefIdx n pol P //
        x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = Tr.chainCount n P
```
moves_ref: 7590–7603 "THE DICTIONARY, RESTRICTED TO PRE-HALT MARKS: …
Σ_{η ∈ Pref^τ(P̂)} μ(S(η,⊤)) = Σ_T (# length-ℓ chains of T of shape P̂) · μ{f}."
deps: Defs §2.8/§2.10, T-F0, T-E9, MovesD (D4R_CYL, ClassFiberWelldef AS
HYPOTHESES — their proof for the canonical model is T-D5/T-D6). sketch — the
bijection with EVERY leg warranted: i ↦ the chain of Tr in i's class at x. Well-
defined + injective: hcyl converts "x ∈ S.fiber i" to membership at reprOf i, T-F0
+ `hph` transport PreHalt across the class, fiberAt (i) lands the class's realized
member in Tr.chains, and `hsep` pins ONE chain per class. Surjective: a chain H of
Tr matching P̂ lies in PrefSet (`hib` supplies InBox), `heta` carries membership to
the class representative, so its class i has x ∈ S.fiber i, and `hph` gives
PreHalt (reprOf i) from T-F0 at H. hypothesis_fields: `hcyl`, `hwd` (the W4-3
pins, HERE consumed), `heta`, `hib`, `hph`, `hsep` (HC-2-owned, §0 — `hsep` is the
per-tree face of `hwd` over the canonical model, recorded beside ETA-LOC).

**T-F3 `MovesT.preHalt_dict_sum` · `F3_dictSum.lean` · medium**
```lean
theorem preHalt_dict_sum {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (hsep : ∀ Tr ∈ 𝒯, (T-F2's per-tree hsep row at Tr))
    (𝒯 : Finset (VTree p F)) (hpart : PartitionsDecided 𝒯 T χ) :
    ∑ᶠ i : PrefIdx n pol P,
        Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x}
```
moves_ref: 7601–7606. deps: T-F2, T-E13, T-F1. sketch: double count {(i, x)} both
ways; per-x the inner count is T-F2 at x's unique-up-to-ext tree (T-F1; chainCount
is ext-invariant — one-line lemma). hypothesis_fields: hcyl/hwd/heta/hib/hph/hsep
(via T-F2); `hpart` (§2.10, DISPLAYED — the finite family covering the decided
slice at fixed level; E-phase derives it from T-E11's stability or takes the
finite-level slice as the summation domain).

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

### Layer D — the seam-discharge units [15 units]

**T-D1 `MovesT.eligibleT_apparatus` · `D1_eligible.lean` · medium**
```lean
theorem eligibleT_iff_child (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) (hmem : T.mem o x) : T.child o ν x ↔ eligibleT T CA o ν x
theorem eligibleT_cell_data (T : TreeModel p F n N m pol) (CA : …) (o ν x x')
    (h : CA.cellOf (embE o) x = CA.cellOf (embE o) x') :
    eligibleT T CA o ν x ↔ eligibleT T CA o ν x'
```
moves_ref: MovesD §2.5 W4-1(c) "`eligible` becomes a DEFINED predicate over MovesT's
cell/branch-set vocabulary; `child_iff` then a THEOREM-obligation of HC-2" + §T.1
(c1) 7093–7100. deps: Defs §2.9. sketch: first = `CA.child_cell` verbatim; second =
cellOf-factoring. HONEST SCOPE (rev 2, Codex 19): these theorems hold over ANY
CellAssign — the definitional leg of W4-1; the CANONICAL instance is HC-2's BY THE
CONTRACT'S OWN (c) CLAUSE (see §5's status column). hypothesis_fields: `CA` (the
canonical instance: HC-2's SideReads surface via `WallAReconciled`, fenced Q1/Q2).

**T-D2 `MovesT.eligible_nonvacuity` · `D2_eligGate.lean` · medium — REV 3
(Codex-2 #16: rev 2 "only proves a model already known to have a child has an
eligible child" — the contract's actual (b)-demand, "the ROOT-ONLY CHILDLESS TREE
must not satisfy the law for REALIZABLE inputs", is now a GENERAL in-corpus
theorem: on any input whose reduction opens a window, the childless tree's fiber
is EMPTY — through fiberAt's degree clause (v), no toy needed).**
```lean
theorem rootOnly_childless_rejected (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (hχ : Function.Injective χ) (x : Box p m)
    (hrep : ∃ ψ, ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) ∧
      2 ≤ Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)))
    (Tr : VTree p F) (hchains : Tr.chains = ∅) : ¬ Tr.fiberAt T χ x
-- a REPEATED reduction factor = a window-opening track (m_i ≥ 2). The childless
-- tree's typemult = henV = the SIMPLE factors' payload — degree < n — so fiberAt's
-- clause (v) fails: the interface ITSELF rejects the degeneracy on every such
-- input, for EVERY model and EVERY CellAssign. (The contract's "realizable input"
-- is any box member; window-opening is the case where childlessness would lie.)
theorem no_childless_vacuity (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (h : ∃ o ν x, T.mem o x ∧ T.child o ν x) :
    ∃ o ν x, eligibleT T CA o ν x
theorem cellOf_nonconstant (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T)
    (h : ∃ o ν x x', T.mem o x ∧ T.mem o x' ∧ T.child o ν x ∧ ¬ T.child o ν x') :
    ∃ es x x', CA.cellOf es x ≠ CA.cellOf es x'
theorem eligible_nonvacuity_toy : ∃ (T : TreeModel …toy…) (CA : CellAssign …)
    (o ν x), eligibleT T CA o ν x ∧ RejectsRootOnlyChildless T CA
```
[`RejectsRootOnlyChildless` := on the toy realizable input, the root-only childless
tree FAILS `fiberAt` — now a corollary of the GENERAL first theorem at the toy's
repeated-factor input.] moves_ref: MovesD §2.5 W4-1(b) "NO `eligible := child`
vacuity (Codex#7 c.5 — the root-only childless tree must not satisfy the law for
realizable inputs) … eligibility is CELL data, never f-data (L5)." deps: T-D1,
Defs §2.5 (fiberAt (v)), Gates layer. sketch: first: henPayload's degree = Σ over
SIMPLE factors of deg ψ < n when a repeated factor exists (normalizedFactors sums
to n); clause (v) forces typemult degree = n; chains = ∅ makes typemult = henV
sum — contradiction. second from child_cell; third: cells equal would force equal
branch sets, contradicting the child split; toy leg via the gate architecture.
SCOPED PUSH-BACK, narrowed (rev 3): the all-(ns) childless model at states BELOW
genuine reads remains lawful τ-ns — but it is now REJECTABLE at the ledger level
through `KBTot.ns_lumps` (the B(iii) tie + slot-0 ladder, §2.4), so the record
claims only: not rejectable by fiberAt ALONE. hypothesis_fields: none (concrete
instances).

**T-D3 `MovesT.verdictModel_inst` · `D3_verdictModel.lean` · hard [split D3a/D3b] —
REV 3 (Codex-2 #17): the two undisplayed packages are GONE — `hvc` is DELETED (τ's
cell-data locality is an in-corpus LEMMA `vdict_cell_of_child_cell`: IrrHalts reads
the state H alone, NsHalts reads children, and `CA.child_cell` transports children
across a shared cell — no owner supply needed); `capData` is the DISPLAYED §2.9
`CapData`, discharged by T-C2's `tbcap_irr_family`.**
```lean
theorem vdict_cell_of_child_cell (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (o : Option (History p F)) (x x' : Box p m)
    (hx : T.mem o x) (hx' : T.mem o x')
    (hc : CA.cellOf (embE o) x = CA.cellOf (embE o) x') :
    ∀ ν, T.child o ν x ↔ T.child o ν x'
noncomputable def vModelOf (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (hdi : KBTot T) (capData : CapData T CA χ) :
    VerdictModelT T CA χ
```
THE RE-KEY (W4-2(c)): `VerdictModelT` is §2.9's DISPLAYED structure — every rev-8
field accounted by the §2.9 crosswalk (Codex 20's repair). vdict := the τ emission
(some (irrVerdictOf H) on IrrHalts; some (nsVerdictOf H) on NsHalts; none else);
halt_iff from T-V5/T-V6 (GIVEN hdi — now the full `KBTot` bundle, so the ns leg
carries Theorem-B content); vdict_cell from `vdict_cell_of_child_cell` (IN-CORPUS —
the rev-2 `hvc` owner-row is retired); rootVdict := henPayload χ with T-C1
discharging rootVdict_cell; capHen := 1 (T-C1); capIrr := capData.capIrrOf with
capIrr_law := capData.cap_law (discharged by T-C2's `tbcap_irr_family` at the
presented instances); NO ns cap (§0 refutation record — the ADMITTED amendment,
W4-2(b)(ii)). moves_ref: MovesD §2.5 W4-2 entire; §T.1 (c1)/(c2) 7093–7120; §T.2
per-clause statuses. deps: T-V5, T-V6, T-V7, T-C1, T-C2, Defs §2.9. difficulty:
hard (D3a structure + vdict/halt_iff; D3b caps). hypothesis_fields: `hdi : KBTot`
(KB-TOT, §0), `CA`, `capData` (T-C2's Presented faces). NON-DEGENERACY GATE: T-G1
instantiates vModelOf on the toy and checks a non-constant vdict (surrogate +
bridge — the W4-2(b)(i) demand as a build-time check, with T-V7's
`vdAt_nontrivial` the type-level face).

**T-D4 `MovesT.cellLevel_local` · `D4_cellLevel.lean` · medium**
```lean
theorem cellLevel_local_sound (T : TreeModel p F n N m pol) (CA : …)
    (o : Option (History p F)) (hlev : CA.cellLevel (embE o) = siteLevel n o)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, CA.levelOf c < siteLevel n o → x c = x' c) :
    CA.cellOf (embE o) x = CA.cellOf (embE o) x'
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
  {ct : Finset (Σ P : Shape n, PrefIdx n pol P)
        × List ((Σ P : Shape n, PrefIdx n pol P) × Vd) //
    PrefixClosed ct.1 ∧ ∀ av ∈ ct.2, av.1 ∈ ct.1}
-- REV 3 (Fable-2 GAP-2: the ellipsis component displayed): finite prefix-closed
-- class-address sets, with the leaf-verdict data an ASSOCIATION LIST address ↦ Vd
-- over the address set [E-phase: `PrefixClosed` keys to MovesD's class-level
-- prefix relation `ClassPrefixOf` — same accessor as §2.10's PrefixCoherentRepr].
instance : Countable (ClassTree n pol)
```
moves_ref: MovesS §W4-SYNC S-7. deps: T-D9, T-V7, MovesD (PrefIdx finiteness via
the E-layer encodings). sketch: countable-of-finite fibers over countable Shape
data. hypothesis_fields: none.

**T-D11 `MovesT.fibOf_keying` · `D11_fibOf.lean` · medium — REV 3 (Codex-2 #23:
`fibOf`'s body displayed; the representative-coherence it NEEDS is the explicit
premise `hrep : PrefixCoherentRepr` (§2.10) — without it reprOf-per-address need
not produce prefix-closed chains, and rev 2's bare name hid that).**
```lean
noncomputable def fibOf (hrep : PrefixCoherentRepr n pol)
    (ct : ClassTree n pol) : VTree p F where
  chains := {H | ∃ a ∈ ct.1.1, H = reprOf a.2}   -- the per-address representatives
  hfin := (finite image of the finite address set)
  hne_nodes := (PrefSet members are nonempty histories — MovesD)
  hclosed := (from `hrep`: a class-prefix's representative IS a history prefix,
              and ct.1.1 is PrefixClosed)
  henV := (ct's root payload component)   -- [E-phase: carried on ct.2's root row
                                           --  or a third component; MANIFEST notes
                                           --  the packaging choice]
  hhen := (payload wellformedness from Vd's carrier)
  leafV := fun H => (the ct.2 association-list lookup at H's address)
  hleaf := (maximal address ↔ maximal representative, via `hrep`)
  nsLeaf := fun H => (the looked-up verdict is a replicate — nsVerdict-shaped)
  hns_leaf := (lookup only at maximal addresses)
theorem fibOf_fiber_disjoint …   -- distinct ClassTrees, ¬ext trees (T-E9 + hwd)
theorem fibOf_partition …        -- the ONE-F partition face over `Realizes` trees
```
[`Realizes` HOISTED to §2.5 at rev 3 (Fable-2 CRIT-1's fix consumes it corpus-wide);
this unit keeps the KEYING.] moves_ref: S-7's keying demand + "βmeas = 0 must not
trivialize (fiber nonemptiness where βmeas > 0)" — the LAW is MovesS's consumption
over presented instances; the CARRIER (`Realizes`) and the keying are here; the toy
nonemptiness witness is T-G1's `toy_fiber_ne`. deps: T-D10, T-E9, T-F1, T-D6.
hypothesis_fields: `hwd` (via T-D6's conclusion or directly as the MovesD pinned
Prop); `hrep : PrefixCoherentRepr n pol` (owner HC-2/PresentNorm, §2.10).

**T-D12 `MovesT.packages_rekey` · `D12_packages.lean` · easy — REV 3 (Codex-2 #18:
every [3t] field value is now a NAMED §2.10 DEF with a displayed body — no prose
placeholder, no undefined Prop; and the declaration-site question is settled by the
CONTRACT'S OWN PREAMBLE, quoted in §2.10: "the contract MovesT/MovesV re-key when
their vocabulary exists" + "The former file plan (`MovesS/Interfaces.lean`) is
retired for these declarations" — the re-keying corpus IS the declaration site;
MovesS wave 5 consumes by import, no re-pointing act remains).**
```lean
-- DECLARED VERBATIM from MovesS §W4-SYNC (the contract's own field rosters):
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

def rs1GivenOfMovesT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (rel2_a rel2_b rel2_c rel2_d rel2_e : Prop) : RS1GivenPackage := {
  tree_exp_fin := TreeExpFin T CA χ,        -- §2.10, displayed
  tree_exp_ns := TreeExpNs pol,             -- §2.10, displayed (finite-face rider)
  tree_n := TreeNStmt pol,                  -- §2.10, displayed
  one_f := OneFStmt T χ,                    -- §2.10, displayed
  sib := SibCount T CA χ,                     -- §2.6, displayed
  tb_cap := TBCapPinned pol m ∧ NsAmendedPair pol,   -- §2.10, both displayed
  vp := VPPinned T CA χ,                    -- §2.10, four named legs
  pci := PCI T CA χ,                          -- §2.6, displayed
  rel2_a := rel2_a, rel2_b := rel2_b, rel2_c := rel2_c,
  rel2_d := rel2_d, rel2_e := rel2_e }      -- [2r] owner-tagged parameters
def RS1GivenHolds (Π' : RS1GivenPackage) : Prop :=   -- the contract's premise row
  Π'.tree_exp_fin ∧ Π'.tree_exp_ns ∧ Π'.tree_n ∧ Π'.one_f ∧ Π'.sib ∧
  Π'.tb_cap ∧ Π'.vp ∧ Π'.pci ∧
  Π'.rel2_a ∧ Π'.rel2_b ∧ Π'.rel2_c ∧ Π'.rel2_d ∧ Π'.rel2_e
def xrbOfMovesT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (xhd_w xhd_u xhd_d xhd_s jc_inv rel2_a rel2_b rel2_d : Prop) : XRBPackage := {
  sib := SibCount T CA χ,
  jc_multi := (∀ (Tr : VTree p F) (L : SiteLedger Tr T CA χ),
    ∀ H ∈ multiSites Tr T CA χ L, ∀ h2 : 2 ≤ L.sides H,
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H ‹_› h2)),
  tb_cap := TBCapPinned pol m ∧ NsAmendedPair pol,
  vp := VPPinned T CA χ,
  ns_null := NsAmendedPair pol,             -- the (ns) pair; FINITE FACE ONLY
  xhd_w := xhd_w, xhd_u := xhd_u, xhd_d := xhd_d, xhd_s := xhd_s,
  jc_inv := jc_inv, rel2_a := rel2_a, rel2_b := rel2_b, rel2_d := rel2_d }
def wsh17OfMovesT (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (c15 cts : Prop) : Wsh17Package :=
  { c15_volumes := c15, cts_counts := cts, sib_count := SibCountShallow T CA χ }

/-- the W1m addendum's premise row, TYPED (rev 2, Codex 28): RS.1-MARKED's
re-keying must carry the S.2 GIVEN list AND the nine-input ledger; the ledger slot
binds to MovesS's REAL `LedgerIV T M` (a Prop structure, importable) at MovesS's
consumption — here a Prop parameter with that binding recorded. -/
def w1mObligation (Π' : RS1GivenPackage) (ledger_iv : Prop)
    (concl : Prop) : Prop :=
  RS1GivenHolds Π' → ledger_iv → concl
```
NS_NULL RIDER (Fable GAP-4, quoted wherever `ns_null` is consumed): the field's
value is the FINITE-LEVEL truncated-ratio statement (`NsAmendedPair`'s second leg);
the note's profinite μ-claim is NOT stated in Lean — MovesS's re-audit consumes the
finite face or adds its own bridge; the S-2 row (§5) carries this rider verbatim.
moves_ref: MovesS §W4-SYNC S-9 + the [3t] owner tags + both RATIFICATION ADDENDA.
deps: Defs §2.10. hypothesis_fields: none (defs of Props; non-[3t] fields are
parameters keeping their owner tags — [2b]/[2r]/[1v], per the contract's own
roster).

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

**T-D14 `MovesT.chain_charge_ledger` · `D14_chainCharges.lean` · medium — REV 3
(Codex-2 #21 + #8: rev 2's charge started from `stateEvent none` — it could not
represent the root reduction cell — and no ReadLedger-shaped object was
constructed). Now: (a) the chain telescopes to the chain's ROOT-CELL entrance
(EntSt.red — the note's Σ₀), consuming `state_cell` at each step; (b) the
contract's `ReadLedger` carrier is DECLARED VERBATIM and a ledger value is
CONSTRUCTED from (Tr, L, H, fe), its (BDY)-split identities THEOREMS by
construction — `fe` itself stays the one owner-supplied datum (MovesV's
`isEntrance`), quoted as the S-6 residual.**
```lean
noncomputable def chainReads (Tr : VTree p F) (H : History p F) :
    List (History p F) :=
  (List.range H.nodes.length).filterMap fun r =>
    (prefixAt H (r+1)).filter (· ∈ Tr.chains)   -- the nonempty prefixes = the
                                                 -- reads along H [E-phase plumbing]
theorem chain_charge (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellAssign p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : ∀ H' ∈ chainReads Tr H, L.sides H' = 1)
    (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p))
    (hent : ∀ H₁ ∈ chainReads Tr H, H₁.nodes.length = 1 → L.parentSt H₁ = .red g ψ) :
    Nat.card ↥(stateEvent T (some H))
        * p ^ ((chainReads Tr H).map (L.siteExp ·)).sum
      = Nat.card ↥(rootCell χ g)
-- the telescope now ENDS AT the reduction cell Σ₀ — the entrance of the chain's
-- head read (Codex-2 #8's carrier at work); Theorem C(b)'s closed form along a run
-- = T-E6 iterated through `state_cell`.

-- the contract's carrier, DECLARED VERBATIM (MovesS §W4-SYNC ReadLedger roster):
structure ReadLedgerT where
  L fe : ℕ ; hfe : fe ≤ L
  charge : ℕ → ℝ
  Wcharge βcharge : ℝ
/-- the CONSTRUCTED per-entered-path ledger (the S-6 value): per-read charges =
the tree's read masses p^{−siteExp}; the totals DEFINED as the (BDY) sums. -/
noncomputable def readLedgerOf (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellAssign p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F)
    (fe : ℕ) (hfe : fe ≤ (chainReads Tr H).length) : ReadLedgerT :=
  { L := (chainReads Tr H).length, fe := fe, hfe := hfe,
    charge := fun r => ((chainReads Tr H)[r]?).elim 0
      (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹),
    Wcharge := ∑ r ∈ Finset.Icc 0 fe, ((chainReads Tr H)[r]?).elim 0
      (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹),
    βcharge := ∑ r ∈ Finset.Icc (fe + 1) (chainReads Tr H).length,
      ((chainReads Tr H)[r]?).elim 0 (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹) }
theorem readLedgerOf_bdy (Tr : VTree p F) … (fe hfe) :
    (readLedgerOf Tr L H fe hfe).Wcharge
        = ∑ r ∈ Finset.Icc 0 fe, (readLedgerOf Tr L H fe hfe).charge r ∧
    (readLedgerOf Tr L H fe hfe).βcharge
        = ∑ r ∈ Finset.Icc (fe + 1) (readLedgerOf Tr L H fe hfe).L,
            (readLedgerOf Tr L H fe hfe).charge r
-- = the contract's `W8_bdy RL` conjunction AT the constructed value — by rfl-level
-- unfolding; the charges = the tree's read masses is `chain_charge` above.
```
moves_ref: MovesS §W4-SYNC S-6 "tie ReadLedger to the tree — a per-entered-path
assignment `RL : (t, first-entrance ν) → ReadLedger` with charges = the tree's read
masses, Wcharge feeding WshVal, βcharge feeding βmeas." MovesT's half is now a
CONSTRUCTED VALUE + two theorems; the residual (quoted, owner recorded): the
first-entrance INDEX fe's semantic pin needs `isEntrance` (MovesV/[1v]), and the
WshVal/βmeas feeds are MovesS's consumption. Branching chains: the per-read charge
at a multi-side read is the same `siteExp` (the §2.5 clause-partition ties the
side sum to mstar); the mass identity for them rides T-E7/E8, tagged hjcm —
recorded, not hidden. deps: T-E6, Defs §2.5. sketch: induction along the chain,
T-E6 at each step with E := univ; the base case is the head read's charge into
`rootCell χ g`. hypothesis_fields: `L` (incl. `state_cell`); `hone`; `fe` (MovesV).

**T-D15 `MovesT.w3_rekey` · `D15_w3Rekey.lean` · easy — NEW at REV 3 (Codex-2 #20,
the S-3 pushback REVERSED): the contract's re-keyed W3 obligation, stated over the
IMPORTED MovesS objects (MovesS is BUILT — `RS1Meas.βmeas`/`evalRe` importable from
`LeanUrat.MovesS.Interfaces`/`EvalReDef`).**
```lean
-- §2.10's `hxrbStmt` + `w3Rekeyed` are the defs; this unit binds them to T-D12's
-- premise row and records the consumption shape MovesS wave 5 derives:
theorem w3_rekey_typed {n' : ℕ} (T' : MovesS.TableShape n')
    (M : MovesS.MeasuredSide T') (RB : MovesS.RatBurdens T' M)
    (hdc : MovesS.DegCons T') (Π' : RS1GivenPackage) (ledger_iv : Prop)
    (B₀ : MovesS.RS1Meas T' M) :
    w3Rekeyed RB hdc (RS1GivenHolds Π') ledger_iv B₀
      = (RS1GivenHolds Π' → ledger_iv → hxrbStmt T' M B₀ →
          ∀ e (he : e ∈ Finset.Icc 1 n') (τ : T'.State e) (σ' : Multiset T'.VType)
            (q₀ : ℚ) (hq : q₀ ∈ M.Pools), M.activeState q₀ e τ →
            ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
              = MovesS.evalRe T' M RB hdc e he τ σ' q₀
                  (fun e' he' => B₀.βmeas e' he' h_ent))
```
moves_ref: MovesS §W4-SYNC S-3 — the demand VERBATIM: "assume XRB's CONCLUSION (the
invariance equality, or the thirteen premises + W2), not the bare implication;
re-keyed form: `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`" — and the preamble's
assignment: "the contract MovesT/MovesV re-key when their vocabulary exists."
STATUS HONESTY: this unit STATES the re-keyed obligation (an rfl-level identity
pinning its shape — the premise now the equality, never `W2_xrb`); DERIVING its
conclusion (the recursion itself) is MovesS wave-5's RS.1 work, quoted in §5's S-3
row as the owner remainder. deps: Defs §2.10, `LeanUrat.MovesS.Interfaces`.
sketch: `rfl` after unfolding. hypothesis_fields: none (a shape pin).

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
theorem toy_sib : SibCount toyModel toyCA toyχ     -- provable ON THE TOY: the rev-2
  -- kernel quantifies over the toy's FINITELY MANY cell events (not all subsets —
  -- the rev-1 form was FALSE on every branching toy, Fable CRIT-1's tail)
theorem toy_vdict_nonconstant : ∃ x y, toyVdict x ≠ toyVdict y
theorem toy_fiber_ne : ∃ x, toyTree.fiberAt toyModel toyχ x   -- S-7's witness
theorem toy_e5_instance : …   -- the rev-2 E5 exponent shape at t = 1 on the toy
  -- (the CRIT-3 regression gate: numTracks, not numTracks − 1)
theorem toy_henflip_unrealizable :                             -- NEW at REV 3: the
    ¬ Realizes toyModel toyχ (toyTree.withHenV ∅)              -- Fable-2 CRIT-1
  -- regression gate — the henV-emptied flip of the toy tree has EMPTY fiber (its
  -- typemult loses the hen degree, clause (v); its payload mismatches clause
  -- (iii)), so E5/E8/E11's `hreal` hypothesis correctly excludes it FOREVER.
  -- [`withHenV` := the record-update; surrogate + bridge per the architecture.]
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
survives verbatim. REV-3 ADDITION: `HistLawful`'s DISCHARGE (T-V8/T-V9's premise,
§0) is queued HERE — the intended source is the re-keyed HistoryCoherent + the
node/root ledger data, and declaring that implication before the re-key lands would
assert lawfulness through the currently-inconsistent steep child keying; until
sign-off the premise stays explicit (honest conditionality, Fable-2 CRIT-2's
shape). The 2-NODE READSOF GATE becomes a Layer-G unit spec (pre-written, NOT
built): `G3_q1Gate.lean` — a two-node history (root + one steep e·g ≥ 2 read) with
a concrete box member, checking `T.mem (some H₂) x` through the re-keyed instance
(surrogate + bridge, per the gate architecture) — the non-vacuity witness for the
steep leg V10 showed is currently inconsistent. FENCE: G3 is in the manifest as
`status: "fenced-Q1"`; building it before sign-off is a statement-fence event.

**Q2 — U21's RunVertexPin (the D.7(v)-warranted `child_dig_frame` pin).** DESIGN:
`eligibleT`'s semantic content enters through `CA.branchSetOf ∘ CA.cellOf`; the
vertex pin is exactly the clause making `cellOf`'s digit frame at a child read
WELL-DEFINED. MovesT reserves the NAMED conjunct slot: `CellAssign` gains
(post-sign-off) a field `vertex_pin : ∀ es ν x, …` transcribing D.7(v)'s warrant
(the HC-1 V10/V9 kernel family is PROVED — the pin's mathematical content is
machine-checked; what awaits sign-off is its INTERFACE placement on the frozen
MovesC types). REV-3 ADDITION (Fable-2 CRIT-3): the pin's TYPED CONSEQUENCE at the
one-side sites is the `SiteLedger.state_cell` field (§2.5) — the state↔cell tie the
E-layer consumes as DATA; HC-2's canonical instance discharges the field FROM the
pin post-sign-off, and no MovesT unit derives it in-corpus (the fence-compatible
carrier). Until then: `CellAssign` as in §2.9 (no vertex field); HC-2's canonical
instance carries the pin internally; `WallAReconciled` (§2.9) is where clause
(vi)'s read-off meets the re-key. FENCE: adding the field is flagged `fenced-Q2`
in the manifest, sign-off required.

---

## §5 SEAM ACCOUNTING — every consumed contract entry, rebuilt entry-by-entry
## against the contract texts (REV 3 — Codex-2 #16–21/#25, Fable-2 GAP-1)

STATUS SEMANTICS (carried from rev 2): a row is **DISCHARGED** only where a unit's
STATEMENT is the contracted obligation over the consumed corpus objects and the
unit is in-corpus provable; **REDUCED** where the obligation is derived from a
NAMED typed bridge Prop whose instance has a recorded owner; **SUPPLIED** where
MovesT's side of a shared entry is a delivered TYPED VALUE (a §2.10-grade
statement, never a bare name — the rev-3 tightening) but the entry's own DONE
criterion ("re-keyed against the real corpora and re-audited" — MovesS §W4-SYNC
preamble) sits with the owner; **NOT-OURS** where the contract's own text assigns
the leg elsewhere (quoted per row). NO row counts as done that isn't.

COUNT: **19 seam entries** = 4 (MovesD W4-1…4) + 11 (MovesS S-1…S-11) + 2 (MovesS
ratification addenda) + 2 (HC-2 Walls A/B); PLUS 2 fenced Q1/Q2 queue-item DESIGNS
(§4 — not seam entries, not discharge targets). Total rows below: 21. Status tally
over the 19 — ROW-FAITHFUL (REV 3, Codex-2 #25/Fable-2 GAP-1: rev 2's tally line
contradicted its own table on S-4 and the NOT-OURS count):
**1 DISCHARGED (W4-4) · 4 REDUCED (W4-1, W4-2, W4-3, Wall A) · 12 SUPPLIED/PARTIAL
(S-1, both addenda, S-2, S-3, S-5, S-6, S-7, S-8, S-9, S-10, S-11) · 2 NOT-OURS
(S-4, Wall B).** Check: 1+4+12+2 = 19 ✓ (re-counted from the rows below).
REV-3 STATUS MOVES, each with its reason: S-9 DISCHARGED→SUPPLIED (Codex-2 #18 —
values now in-corpus, but the DONE criterion's re-audit is the owner's); Wall A
SUPPLIED→REDUCED (Codex-2 #19 — the pin now binds the BUILT `HC2.ReadsOf`, the
instance residue is HC-2's); S-3 NOT-OURS→SUPPLIED (Codex-2 #20, pushback REVERSED
— the `hxrb` premise is stated over the imported real `βmeas`, §2.10/T-D15); S-4
counted NOT-OURS as its own row always said.

**(A) MovesD blueprint §2.5 (4 entries):**

| entry | contract text honored | MovesT units | status + residual (owner per the contract's own clause) |
|---|---|---|---|
| **W4-1** `eligible`/`child_iff` | (c): "`eligible` becomes a DEFINED predicate over MovesT's cell/branch-set vocabulary; `child_iff` then a THEOREM-obligation of HC-2"; (b): "NO `eligible := child` vacuity … the root-only childless tree must not satisfy the law for realizable inputs", cell data never f-data | Defs §2.9 (`CellAssign`, `eligibleT`, `WallAReconciled`) + T-D1 + T-D2 — REV 3 (Codex-2 #16): the (b)-demand is now the GENERAL theorem `rootOnly_childless_rejected` (every window-opening input, every model, every CA — through fiberAt's degree clause (v)), no longer a toy-only witness | **REDUCED**: the definitional leg + BOTH (b)-demands are in-corpus theorems; `child_iff` for the CANONICAL instance is HC-2's by (c)'s own text (pin: `WallAReconciled` at the BUILT `HC2.ReadsOf`; steep legs fenced Q1/Q2). The rev-2 push-back is NARROWED (T-D2): all-(ns)-below-reads models are rejectable at the LEDGER level via `KBTot.ns_lumps`, so only "not rejectable by fiberAt alone" is recorded |
| **W4-2** VerdictModel ENTIRE | (a)'s FULL field roster → §2.9's `VerdictModelT` + crosswalk (every rev-8 field accounted); (b)(i) no degenerate satisfiability → `vdAt_nontrivial` (T-V7) + `cellOf_nonconstant` (T-D2) + toy gates; (b)(ii) `cell_local` replaced at the per-state level (T-D4 sound + falsifier); cross-level cap uniformity → `CapIrrLaw` quantified over ALL presented N (§2.9, DISPLAYED) discharged by T-C2's `tbcap_irr_family` via `capIrr_uniform` (Codex-2 #5 closed); (c) re-derived from VP-1/VP-2 + TB-CAP | T-D3 (`vModelOf` + the in-corpus `vdict_cell_of_child_cell`) + T-D4 + T-V5/V6/V7 + T-C1/C2 — REV 3 (Codex-2 #17): the three undisplayed packages are GONE — `VdictCellData` retired (an in-corpus LEMMA), `CapIrrLaw`/`CapData` displayed §2.9, `KBTot` displayed §2.4 with its falsifier | **REDUCED**: structure, vdict values, halt_iff, both caps, both locality laws are in-corpus theorems/defs over DISPLAYED types; residuals NAMED and typed: `hdi : KBTot` (HC-2/D4R0K), the canonical CA itself (HC-2); ns stays cap-FREE (the ADMITTED (b)(ii) amendment, refutation record §0) |
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
| **S-3** W3_recursion | the RE-KEYED W3 obligation with the `hxrb` premise as the contract prescribes | §2.10 (`hxrbStmt`, `w3Rekeyed`) + T-D15 | **SUPPLIED** — REV 3, the rev-2 pushback REVERSED (Codex-2 #20 ruling accepted, sided with the text): the preamble assigns the re-key HERE ("the contract MovesT/MovesV re-key when their vocabulary exists") and S-3 prescribes the premise shape ("re-keyed form: `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`"); rev 2's "βmeas is not stateable in this corpus" was FALSE — MovesS is BUILT and `RS1Meas.βmeas`/`evalRe` import (`LeanUrat/MovesS/Interfaces.lean` 35–46, `EvalReDef.lean`); `hxrbStmt` states the equality over the imported objects, `w3Rekeyed` the full obligation. Owner remainder (quoted honestly): DERIVING the recursion conclusion is MovesS wave-5's RS.1 work |
| **S-4** W4_x3 | recorded posture only: MovesT is X.3-free (§0) | — | **NOT-OURS** ([5]/MovesX's package; consumed-item pin unchanged) |
| **S-5** W7_cutWD + TreeIface | the CARRIER: VTree + the four order laws (refl/trans/antisymm/total) | T-D8, T-D13 | **PARTIAL** (rev 2, Codex 30): the load-bearing re-keyed clause — "∀ t ν, TI.isDeepSplit t ν → ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν" — needs `isEntrance`/`isDeepSplit` (CTS/[1v] vocabulary, MovesV); quoted so the residual is checkable |
| **S-6** W8_bdy + ReadLedger | the contract's carrier DECLARED VERBATIM (`ReadLedgerT`), a ledger VALUE CONSTRUCTED from the tree (`readLedgerOf` — charges := the tree's read masses p^{−siteExp}), its (BDY)-split identities THEOREMS at the constructed value (`readLedgerOf_bdy` = the contract's `W8_bdy` conjunction), and the chained mass identity telescoping to the ROOT CELL entrance (`chain_charge`, rev-3 EntSt form) | Defs §2.5 + T-D14 | **PARTIAL** — REV 3 (Codex-2 #21: rev 2 supplied a conditional carrier, no instance, and a root-blind charge; all three fixed). Residuals quoted with owners: the first-entrance INDEX fe's semantic pin needs `isEntrance` (MovesV/[1v]); the WshVal/βmeas feeds are MovesS's consumption; multi-side chains' mass identities ride T-E7/E8 under the hjcm tag |
| **S-7** W10_convergence + FiberIface | fibOf keying, countability, disjointness, ONE-F partition + the NONEMPTINESS CARRIER `Realizes` and the toy witness `toy_fiber_ne` (rev 2, Codex 32) | T-D9, T-D10, T-D11 (+T-E9, T-F1, T-G1) | **PARTIAL**: "βmeas = 0 must not trivialize (fiber nonemptiness where βmeas > 0)" is a LAW over MovesS's measured side — consumed there against `Realizes`; general realizability is genuinely open (no fake theorem) |
| **S-8** W17ii + Wsh17Package | the actual `Wsh17Package` declared; `sib_count := SibCountShallow T CA χ` — a DEFINED statement (§2.6), not a name | T-D12 | **PARTIAL** (Codex 33): the empty-menu exclusion (`F.Sh.Nonempty`) and the xhd_s face are MovesS/[2b]-side tie-demands — quoted, owners recorded; c15_volumes (§C/MovesC cite) and cts_counts ([1v]) stay parameters |
| **S-9** packages as registries | every [3t]-owned Prop field is a §2.10 DEF with a DISPLAYED BODY over consumed corpus objects (`TreeExpFin`/`TreeExpNs`/`TreeNStmt`/`OneFStmt`/`TBCapPinned`/`NsAmendedPair`/`VPPinned`/`SibCount`/`PCI`/`SibCountShallow`) — no prose placeholder, no undefined Prop (Codex-2 #18 closed); declaration site warranted by the preamble quotes (§2.10) | Defs §2.10 + T-D12 | **SUPPLIED** — REV 3 re-tag (down from rev 2's DISCHARGED, per Codex-2 #18's DONE-criterion point): the values are in-corpus, but "re-keyed against the real corpora AND RE-AUDITED" is the contract's DONE bar, and the re-audit of MovesS's consumption is wave-5/owner-side; non-[3t] fields keep owner tags as parameters (the contract's own roster) |
| **S-10** RS4Chain provenance | the DISCHARGE provenance objects exist as named theorems: TREE-EXP (T-E8), ONE-F (T-F1) | T-E8, T-F1 | **PARTIAL** (Codex 33): "RE-KEYING REPLACES (R46) the device-satisfied instances … by production-derived ones" — the replacement ACT is MovesS's; the CUT-WD leg is S-5's residual (MovesV) |
| **S-11** n2_treeiface | the carrier-core constructor | T-D13 | **PARTIAL** (Codex 30): "the gate's TreeIface instance + W7 check, built when TreeIface is re-keyed" — the full instance + W7 check wait on MovesV's entrance semantics |

**(C) HC-2 Wall A / Wall B seam notes (2 entries):**

| seam note | MovesT's side | units | status |
|---|---|---|---|
| **Wall A** ("deliberately the SAME semantic surface as MovesD's W4-1 `eligible`; HC-2 owns the definition; MovesT re-keys `eligible` to it in wave 4") | the re-key is executed at interface level (`eligibleT` over `CellAssign`) AND the pin now binds the REAL BUILT predicate (REV 3, Codex-2 #19): `WallAReconciled T CA dec` consumes `HC2.ReadsOf` BY NAME (`lean/LeanUrat/HC2/Defs.lean` 283 — clause (vi)'s vertex read-off inside it per HC2 §7.6); the sole remaining parameter is HC-2's chart section `dec : Box → ℤ_p[x]` | Defs §2.9 + T-D1 | **REDUCED** — REV 3 re-tag (down from rev 2's SUPPLIED, per Codex-2 #19: a pin with the predicate itself a parameter was at most a name). The named residue = {`dec`, the canonical CA, the instance proof} — all HC-2's (fenced Q1/Q2, §4); nothing else remains on this side |
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

CENSUS TARGETS: **55 units = 14 easy / 31 medium / 10 hard** (hard: T-C5, T-E5,
T-E7, T-E8, T-E10, T-E11, T-F2, T-D3, T-D6, T-D7 — escalation-risk set
pre-declared; pre-approved splits: C5a/C5b, D3a/D3b, D7a/D7b, G1a/G1b). REV-3
DELTA: +T-V9 (medium — the node-side saturation pair) and +T-D15 (easy — the S-3
re-key shape pin); one queued MovesD-side companion (SW1b `ShapeWF_of_lawful`,
additive-only, counted in MovesD's census not here); layer counts 9V + 8C + 3S +
13E + 5F + 15D + 2G = 55. Zero axioms; zero `sorry` in the accepted scope; every
hypothesis field named in §0 or §5. `#print axioms` per proved unit = Lean core
only.

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
  statuses are the claim's whole extent);
* no realizability proof — `hreal : Realizes T χ Tr` is the display's own
  qualifier, carried as a hypothesis (general tree realizability is genuinely
  open; the toy witnesses are gates, not theorems);
* no `HistLawful` discharge (explicit fenced premise, queued on Q1 — §0/§4) and
  no in-corpus `state_cell` derivation (a ledger FIELD, owner HC-2, Q2-adjacent).

AUDIT CHARGE for the wave-4 re-pass (per campaign §3): faithfulness of every
`statement` against the quoted rev-7 display; non-vacuity (each hypothesis Prop
falsifiable — T-S2/T-D4's falsifiers; the toy gate day-one); quantifier exactness
(TB-CAP(irr) per (P,i) — NO cap uniform over all cells; SIBLING INDEXING — no
ordering/symmetry factor; CONDITIONING EVENTS PINNED — no free `Set` binder in any
conditional law, the rev-2 doctrine line); hypothesis-field completeness against
§0's ledger; §5's status semantics (DISCHARGED rows must have statement =
obligation; SUPPLIED/PARTIAL rows must quote their residual verbatim). REV-3
ADDITIONS: the REALIZABLE qualifier present on every identity the display
quantifies over realizable trees (E5/E8/E11 + E10's domain); no unit consumes the
state↔cell tie except through the `state_cell` field; the §5 tally re-counted from
the rows; every §2.10 value def's body checked against its unit's display (no
name-for-value regressions).

---

## §7 REV-3 DISPOSITION TABLE (the full union of both round-2 verdicts)

Legend: **F** = fixed (statement-level repair) · **R** = redesigned (structural
rebuild) · **PB** = pushed back (scoped, with reason on record). The rev-1→rev-2
table is retired with the rev-2 text (its two overstated rows — Codex-1 #9 "F" and
#6 "F" — are corrected by this round's CRIT-2/GAP-3 entries below). Cross-references
where the two audits found the same defect.

**Codex-2 criticals 1–21:**

| # | finding (short) | disp. | where |
|---|---|---|---|
| 1 | IrrHalts encodes no saturation (no lawfulness, no degree) | **R** | §2.2: `NodeDataLawful` conjunct IN `IrrHalts`; the E·F = d(cluster) display = NEW T-V9 pair (node-side, `childWidth` the real datum) |
| 2 | NsHalts/BranchDichotomy admit the childless degeneracy | **R** | §2.4 `KBTot` bundle: dichotomy + `ns_lumps` (B(iii) tie + slot-0 ladder field) — mem-everywhere/child-nowhere FAILS it; falsifier displayed; threaded once (T-V6/T-D3), not per-consumer |
| 3 | VTree/fiberAt not a complete tree (empty chains, dropped tracks, no degree fact) | **R** | fiberAt clause (v) DEGREE CONSERVATION; heads = realized children via clause (i)+mem_single (recorded); T-D2's general rejection theorem is the corollary |
| 4 | T-V6 vacuous (`… → True`) | **F** | the literal is DEAD; both dispositions full; ns leg carries the B(iii) datum via `hdi.ns_lumps` |
| 5 | T-C2 not the cross-level cap (one fixed Presented; N-dependent jet) | **R** | `capIrr_uniform` (via T-D7, explicit) + `tbcap_irr_family` (∀ presented N) + `CapIrrLaw` displayed §2.9 — resolved per the display's own shape-computability claim |
| 6 | T-C5 strengthened beyond the (ns) setting | **F** | `hzc : ZCPack J` (§2.5a, clauses displayed) |
| 7 | T-C7 incoherent (ill-typed below N₀, no tower, frozen Mlev, empty denominator) | **R** | subtype domain + `JetTower` + `hMgrow` + `hne`; profinite rider kept |
| 8 | no carrier for the root-conditioned entrance state | **R** | `EntSt`/`entEvent`/`embE` (§2.5); `CellAssign.cellOf` re-keyed over it; SitePresents/JCmultiAt/E3/E6/E7/D14 restated; `.red g ψ` carries the track datum |
| 9 | SideSplit contradictory (free sideExp; oneSide mislabeling) | **R** | §2.5: `sideExp` DEFINED from a clause PARTITION of the presented system (Σ = mstar forced); ledger `sides` field + one-side tie; `multiSites` off the hull datum |
| 10 | T-E5 lacks the root (SIB) decomposition; t = 0 false | **F** | `RootSplitData` + `headOf`/`hinj`/`hcov`; the 5-step decomposition chain named in the sketch; `hreal` + clause (v) kill the t = 0 leak |
| 11 | T-E6 does not follow from `presents` (missing history→cell bridge) | **F** | = Fable-2 CRIT-3: the `state_cell` ledger FIELD, consumed not derived |
| 12 | T-E7 omits the joint-cell charge from its conclusion | **F** | conjunct (B): the composed display with `hcharge` CONSUMED (= Fable-2 GAP-4) |
| 13 | T-E8 asserts TREE-EXP without its structural hypotheses | **R** | `TreeScaffold` (root data + per-split frames with hdecomp + subtree partition); sites=chains by construction; `hreal`; degenerate trees dead via (v)+hreal |
| 14 | T-E10 lacks constancy/canonicity/domain-cardinality/finiteness | **R** | restated over `ShapeEquiv` classes: `hA` explicit, count := the domain's own Nat.card (definitional), `hfin` premise, `Realizes` in the domain |
| 15 | T-F2 equates class indices with raw chains, no bijection | **F** | `hph : PreHaltClassData` + `hsep` (chain-class separation) — both §0-rowed, owner HC-2; bijection legs named in the sketch |
| 16 | T-D2 proves nothing about the prohibited childless model | **F** | `rootOnly_childless_rejected` — GENERAL, in-corpus, every window-opening input; push-back narrowed |
| 17 | W4-2 reduced to undisplayed future packages | **F** | `VdictCellData` retired (in-corpus lemma via child_cell); `CapIrrLaw`/`CapData` displayed; `KBTot` displayed; T-C2 family theorem |
| 18 | T-D12/S-9 parallel declarations, prose placeholder values | **R** | §2.10 value defs (TreeExpFin/TreeExpNs/TreeNStmt/OneFStmt/TBCapPinned/NsAmendedPair/VPPinned) — displayed bodies; declaration site warranted by the preamble QUOTES; S-9 re-tagged SUPPLIED |
| 19 | Wall A "SUPPLIED" on a parameterized future Prop | **F** | pin binds the BUILT `HC2.ReadsOf` by name; residue = {dec, CA, proof} named; row re-tagged REDUCED |
| 20 | S-3 pushback contrary to the contract preamble | **F** (pushback REVERSED) | §2.10 `hxrbStmt`/`w3Rekeyed` over the IMPORTED `MovesS.RS1Meas.βmeas` + T-D15; row re-tagged SUPPLIED; both contract sentences quoted at the row |
| 21 | S-6 a conditional carrier, no instance, root-blind charge | **F** | T-D14: `ReadLedgerT` declared verbatim + `readLedgerOf` CONSTRUCTED + `readLedgerOf_bdy` theorems; `chain_charge` telescopes to the rootCell entrance; fe residual quoted |

**Codex-2 gaps 22–25:**

| # | finding | disp. | where |
|---|---|---|---|
| 22 | T-C1's finite-union face prose-only | **F** | `tbcap_hen_cells` displayed |
| 23 | undisplayed load-bearing names (CapIrrLaw, StageRealized, ClusterFactorOf, UnramifiedOfDeg, jointExpOf, SubFiber, PartitionsDecided, TreeShape quartet, fibOf, E8's Prop, VPPinned, NsAmendedPair) | **F** | CapIrrLaw/CapData §2.9; StageRealized §2.6 (typed clauses); SubFiber §2.6; PartitionsDecided/VPPinned/NsAmendedPair/TreeExpFin-family §2.10; TreeShape quartet RETIRED for `ShapeEquiv` (§2.5); fibOf body + `PrefixCoherentRepr` premise (T-D11); jointExp a displayed SplitSiteData field; ClassTree ellipsis replaced (T-D10). RESIDUAL, disclosed: `ClusterFactorOf`/`UnramifiedOfDeg` (OmSat/HenLift vocabulary, consumed by NOTHING) keep one E-phase-bound clause each — pointer-pinned, weakest case, flagged |
| 24 | T-E13 assumes disjointness for raw values; VTreeExt deferred to prose | **F** | `VTree.ext` displayed (§2.5, an equivalence BY the structure laws); E13's premise = ¬ext-distinctness, disjointness DERIVED from T-E9; T-F1 restated up-to-ext |
| 25 | §5 tally ≠ table; §7 rows overstate | **F** | row-faithful tally (1/4/12/2, re-counted); the two overstated rev-2 rows corrected via this round's entries (see legend note) |

**Fable-2 criticals & gaps:**

| # | finding | disp. | where |
|---|---|---|---|
| C-1 | REALIZABLE qualifier dropped — henV-flip refutes E5/E8/E11 | **F** | `hreal : Realizes T χ Tr` threaded (E5/E8/E11 + E10's domain + CofShape-successor); fiberAt clause (v); §0 refutation record #4; `toy_henflip_unrealizable` regression gate |
| C-2 | T-V8's premise cannot source ShapeWF; SW1 demands HistoryCoherent + card K₀ = p | **R** | `HistLawful` (the child-keying-free fragment, §2.2 displayed) as the ONE explicit fenced premise; SW1b factored variant queued MovesD-side (additive-only); §0 row's implication claim restated honestly; discharge queued on Q1 (§4) |
| C-3 | state↔cell tie silently assumed at E6/D14/E8 | **F** | `SiteLedger.state_cell` FIELD (one-side-scoped equality — the multi-side face routes through E7's hdecomp), owner HC-2, §0 row, placed at the Q2 pin per §4; Codex-2 #11 same fix |
| G-1 | §5 tally contradicts its own table on S-4 | **F** | = Codex-2 #25 |
| G-2 | undisplayed consumed names under a DISCHARGED claim | **F** | = Codex-2 #23 (the T-D12 instances now bind §2.10 defs; `VdictCellData`/`levelIdx`/`CapIrrLaw` displayed; `ClassTree` ellipsis replaced) |
| G-3 | T-V3's second equality contentless; cluster degree absent | **F** | T-V3 keeps the honest species leg ONLY (Species roster re-checked: no degree field — recorded); the genuine second identity = T-V9 in node vocabulary (`childWidth`) |
| G-4 | T-E7 promised two conjuncts, displayed one; hcharge unused | **F** | = Codex-2 #12: conjuncts (A)+(B), hcharge consumed by (B) |

DISPOSITION TALLY: 32 round-2 union entries → **21 fixed** (Codex-2 #4/6/10/11/12/
15/16/17/19/20/21/22/23/24/25 + Fable-2 C-1/C-3/G-1/G-2/G-3/G-4) · **11
redesigned** (Codex-2 #1/2/3/5/7/8/9/13/14/18 + Fable-2 C-2) · **0 pushed back**
(the one candidate pushback, S-3, is REVERSED — the round-2 ruling accepted with
the contract text quoted). No finding is left unaddressed; no
statement was weakened to make an obligation provable (the statement-fence: every
restatement is toward the note's display or the contract's typed form, both quoted
at the unit; the two hypothesis ADDITIONS — `hreal`, `hzc` — are the displays' own
quantifiers restored, and every other new premise is a §0-rowed owner-tagged
supply, never a convenience).
