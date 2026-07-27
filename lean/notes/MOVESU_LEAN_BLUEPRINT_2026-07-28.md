# MovesU — Lean blueprint for §U-SQUEEZE (Theorem U, conditional form)
# REV 6 (post-Codex-FINAL#2: cl10_vpsound added to FinStack; nothing else) — 2026-07-28

*REV 6 (Codex FINAL#2 `MOVESU_AUDIT_CODEX_FINAL2_2026-07-28.md`: REJECT 3c/0g, one
root cause): `FinStack` carried cl10's three conjuncts but OMITTED `cl10_vpsound`,
one field thinner than the note's CL-10 citation. VERIFIED against the note: the
(U-n) upper side cites "the [3t] package (CL-10)" WHOLE — CL-10's own entry ends
"…and VP-SOUND (a citation obligation…)", and SQ.1 says "CL-10's tags ride every
consumption". So `cl10_vpsound : VPSound X` is now a `FinStack` field; the
projection updated. Nothing else changed.*

*REV 5 (Codex FINAL `MOVESU_AUDIT_CODEX_FINAL_2026-07-28.md`: REJECT 3c/0g, all three
= OVER-hypothesization — U3/U4/U6 took the full `CapstoneLedger` where the note's
displays cite only slices): three Prop SUB-BUNDLES added in DefsLedger — `FinStack`
(CL-7 + CL-10 + the TREE-N identity; U3's exact stack), `SolveStack` (the (U-n)
upper-side citation list CL-1/5/6/8/9/11/13–16/17/18/19 + the operative
identification; with FinStack = U4's exact stack), `LowerStack` (RS.4's inherited
checksum + the CL-4 slot; U6-lower's addition) — as FIELD-SELECTIONS with projection
defs `CapstoneLedger.finStack/solveStack/lowerStack`, so `CapstoneLedger` itself is
untouched and U10 fires the earlier units without re-packing. CL-2/CL-3 now appear in
NO unit except U10's full ledger: the rate form they attach to is gate SQUEEZE-n3, a
census artifact, not a Lean unit (no U6b needed). D12 records the slice discipline.*

*REV 4 (Fable audit `MOVESU_AUDIT_FABLE_2026-07-28.md`: REJECT 2c/4g, spine verified):
KsubM1C1 rebound to same-size CONTINUATIONS (same-size halts exempt — F3-C1); the full
CTS-M(i) tag restored (`ctsmSyntax` slot reinstated beside the typed face) and `M`/`K`
moved to the p-UNIFORM layer before ∀ p, making p-independence expressible (F3-C2,
F3-G4); menus pinned by `menuCount` equations + a not-all-empty law (F3-G1);
`cellCount_pos`/`shapeCount_pos` DROPPED as note-unsupported — cardinality equations
stay, positivity was over-strong vs (K-TRI)'s minimal blocks (F3-G3); §7 audit-trail
misstatements corrected (F3-G2). No spine unit touched.*

*Audit trail: rev 1 REJECT 10c/3g (`MOVESU_AUDIT_CODEX_2026-07-28.md`, repaired at
REV 2); rev 2 REJECT 4c/3g (`MOVESU_AUDIT_CODEX_REV2_2026-07-28.md`, repaired HERE per
the orchestrator ruling (A)–(E)). Findings→repairs table: §7 (extended). REV 3
architecture: (A) the polynomial space is CONCRETE (`Box` + `toPoly` — monic degree-n
polynomials over ZMod (p^N); all counts over THIS space); (B) U10's conclusion SPLITS as
the note does — clause (i) the classifier-keyed density, clause (ii) the identification
corollary under VP-SOUND, now a TYPED ledger field over the concrete box (new unit U11);
(C) RegData de-vacuified: every entry family index-typed with cardinality equations
pinned to block/table data; (D) (REG-p) gains the explicit R_σ-evaluability clause;
(E) menus concrete (`MenuData`), the O3 Teichmüller pin a field, the
Defs/U0b/DefsLedger circularity fixed, `DecidableEq (Tree σ)` added.*

*Blueprint-writer deliverable (campaign wave 1, `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`).
Source of truth: the DUAL-ACCEPTED §U-SQUEEZE rev 7 (`lean/notes/MOVES_2026-07-24.md`,
lines ~12879–13629; Codex passes 8+9 + Fable confirm CLEAN on identical text). TARGET
(master plan §0): Theorem U machine-checked in its CONDITIONAL form — the open kernels as
NAMED HYPOTHESES, never axioms. Upstream objects (MovesS's solve, MovesX's envelope,
MovesD's trees) enter as HYPOTHESIS STRUCTURES: self-contained now, instantiable later.
Protocol L: verbatim names, statements re-bound at use, explicit DAG.*

Discipline: NO new axioms; the statement-fence holds; every structure field is a trust
surface flagged for the Codex semantic audit (§4). `sorry`-free ≠ non-vacuous.

---

## 0. What §U-SQUEEZE is, in one paragraph

The level-N monic coefficient box (p^{nN} classes) is partitioned by the choice-free
canonical-tree verdict into decided-of-type-σ and undecided; (BOX-N) is the exact count
identity. The decided count is bracketed two-sidedly against §S-RESUM's fixed rational
R_σ ∈ ℚ(q): decided_σ(N) ≤ R_σ(p)·p^{nN} (SQ.2 — partial sum of a positive series
dominated by its fixpoint) and decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN} (SQ.3 — pure
arithmetic from (BOX-N) + SQ.2-at-every-other-τ + RS.4's checksum). env(N) → 0 then
forces ρ_σ(p) = lim decided_σ(N)/p^{nN} = R_σ(p) at every prime p satisfying the named
regularity schema (REG-p). Nothing substantive is unconditional: the note's exactly FOUR
tag-free steps are (BOX-N); SQ.3's bracket arithmetic AS arithmetic; Tonelli's
extended-value existence in [0, ∞]; and the env(N) → 0 ⟹ limit forcing. Everything
density-typed rides the capstone ledger CL-1…CL-19.

## 1. Design decisions (D1–D9)

**D1 — Splitting types are CONCRETE (F11).** `SplittingType n := {σ : Multiset (ℕ × ℕ) //
(∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧ (σ.map fun x => x.1 * x.2).sum = n}` — literally the
note's "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n". A Fintype instance is unit
U0b (entries bounded by n). No abstract label type anywhere; `hn : 2 ≤ n` now has
semantic force (the type is the real one).

**D2 — The polynomial space is CONCRETE; the verdict is the classifier interface
(ruling (A); rev-2 criticals 1/2's space objection).** `Box p n N := Fin n →
ZMod (p ^ N)` with `Box.toPoly f := X^n + Σ_i C (f i) * X^i : Polynomial (ZMod (p^N))`
— a REAL Fintype of monic degree-n polynomials mod p^N, no interface. ALL counts
(`decided`/`undec`/`trueCount`) are `Nat.card` counts over THIS space. `ClassifierSpec
n p` (owner MovesD + HC-2, the MovesC-`JetSetup` precedent) carries: `canonical N f`
(T_can^τ's verdict-type map — "a CHOICE-FREE function of f", [1] L2 + VP + ONE-F);
`trueType N f` (the true-factorization-type FIELD, constrained by soundness laws ON
THE CONCRETE SPACE — see D10; its fidelity to real ℤ_p factorization is HC-2's
declared bridge, NOT defined from scratch here, per the ruling); `canonical_stable`
(a level-N decision persists to N' ≥ N along `ZMod.castHom` reduction — TREE-N's join
/ Thm 2.1); `baseSection` (the pinned base digit section, an enum FIELD — the O3
TEICHMÜLLER declaration, gap 6; the ledger pins `= .teichmuller`). `canonical_sound`
is REMOVED as a structure field: verdict soundness is VP-SOUND, an OPEN kernel — it
becomes a TYPED LEDGER FIELD `VPSound X` over the concrete box (D10), never a baked-in
interface law and never a bare Prop slot. `decided`/`undec`/`env`/`dmass`/`trueCount`/
`trueDmass` are DEFINED from the fields. (BOX-N) stays a tag-free count identity.

**D3 — Tonelli is typed in ℝ≥0∞** (unchanged). `seriesSum σ := ∑' T, mass σ T` exists
UNCONDITIONALLY (`ENNReal.summable`); partial sums are dominated (`ENNReal.sum_le_tsum`,
`ENNReal.tsum_eq_iSup_sum`). Rev 2's retyped SQ.2 clause verbatim: existence tag-free;
FINITENESS and IDENTIFICATION with R_σ(p) are ledger fields.

**D4 — FiberSeries is tied to the actual tree family (F2).** `FiberSeries` now carries
`thr : ∀ σ, Tree σ → ℕ` (each tree's decision threshold — "a finite threshold EXISTS",
(NS-a)) with the CHARACTERIZATION `mem_slice_iff : T ∈ thrSlice σ N ↔ thr σ T ≤ N` (the
slice IS the thr ≤ N slice; `slice_mono` becomes derivable and is dropped), plus
`slice_exhausts : ∀ T, T ∈ thrSlice σ (thr σ T)` (definitional corollary, kept explicit
for the audit). The tie to the CLASSIFIER is the ledger's `finiteness_stack` IDENTITY
(TREE-N): decided_σ(N) = p^{nN}·Σ_{thr≤N} mass — so `Tree σ` can be empty ONLY when the
canonical classifier never emits σ at any level (decided ≡ 0 is then forced, not
smuggled). The Finset type of `thrSlice` is still CL-7's finiteness riding the
instantiation (TRACK-COUNT + D(n) + genuine-increment, OPEN — named in KernelStatements,
D7). REV 3 (gap 7): `instTreeDeq : ∀ σ, DecidableEq (Tree σ)` added as a field (the
instantiation needs it to build the Finsets; no classical smuggling at the interface).

**D5 — (REG-p) is a Prop schema over the FULL displayed entry bundle (F4/F10).**
`RegData p` now carries: `depthSet : Finset ℕ` with `one_mem_depthSet : 1 ∈ depthSet`
(the base-change depths of RS.1-SH's assembly, owner MovesS; δ = 1 always arises) and
`pool_eq : Pool = depthSet.image (p ^ ·)` — Q(p) is EXACTLY the pool set, nonempty by
construction (p ∈ Pool), never an arbitrary Finset; `Block` with `instNe : Nonempty
Block` (the top block exists); the matrices `K`; AND ALL remaining displayed entry
families as data. REV 3 (ruling (C), rev-2 critical 3): every family is INDEX-TYPED
with a CARDINALITY EQUATION pinned to block/table count data — never `Nonempty` alone,
never a free Finset that could be empty: `instBiNe : ∀ e, Nonempty (bidx e)` +
`bidx_card : Fintype.card (bidx e) = blockDim e`, `blockDim_pos` (kills the
empty-matrix det = 1 dodge); `Jcell : JIdx e → RatFunc ℚ` with `JIdx_card :
Fintype.card (JIdx e) = cellCount e` (|Jcell| = the branching-cell count of the
block's table, CL-18); `Wcoef : WIdx → RatFunc ℚ` with `WIdx_card = shapeCount` (one
coefficient per shallow shape Ŝ, CL-17). REV 4 (F3-G3): the J/W/leg families are
pinned BY EQUATION ONLY — no positivity: (K-TRI)'s well-foundedness ("every b_e^split
leg has e_j < e") means MINIMAL blocks have no split legs and plausibly no branching
cells, so `cellCount_pos`/`shapeCount_pos`/`legCount_pos` would be over-strong
(truthful-instantiability risk, the dual vacuity trap); `instBiNe`/`blockDim_pos`
stay (every block's table has rows — audited safe);
`betaLeg : legIdx e → ℕ → RatFunc ℚ` with `legIdx_card = legCount e` — β entries are
functions of (leg, depth δ), and `entryList` unions their images over EVERY
δ ∈ depthSet (the display's "at every pool of Q(p)"). The count DATA (`blockDim`,
`cellCount`, `shapeCount`, `legCount`) is the owner tables'; its VALUES' fidelity is
MovesS/[1v]'s declared instantiation pin (D9). `entryList e` stays a DEFINITION (the
union of all families), so (r2) quantifies over the whole display. RULING (D) (rev-2
critical 4): `RegP` becomes `RegP S D` and gains the note's EVALUABILITY clause —
`∀ σ, DefinedAt (S.R σ) (p : ℚ)` — "UNDER (REG-p), the literal evaluation R_σ(p) …
is DEFINED"; U4/U10's `evalℝ` is thereby guarded, never junk. `act` stays abstract
(CTS-M(ii), owner [1v]); (REG-p) stays the rev-5 SEPARATE hypothesis.

**D6 — Literal evaluation.** `evalℝ S σ p := ((S.R σ).eval (RingHom.id ℚ) (p:ℚ) : ℝ)`
(Mathlib `RatFunc.eval`, junk-valued at poles). The theorem NEVER consumes `evalℝ` except
under `RegP S D`, where the ledger's solve-stack field asserts the identification (and
REV 3's evaluability clause asserts definedness, ruling (D)) — so the
junk case is never load-bearing. The WILD-p/ACT reading is carried by (r2)'s agreement
clause inside `RegP`, exactly the note's "the two readings coincide, so ρ_σ(p) = R_σ(p)
is well-typed".

**D7 — The kernel ledger: a `KernelStatements` pack + per-CL assertion fields
(F5/F6/F7).** The open kernels are STATEMENTS owned upstream; MovesU cannot re-state
their content, but it CAN carry them as named Prop-valued parameters. `KernelStatements`
is a structure of `Prop` slots — one per open kernel/obligation of the capstone ledger
(escapeE0, weightCharge, progressX2 with the (X2-*) family, the CL-5 nine, ivPoly,
trackCount/dnDuty/genuineIncrement, the six CL-8 REL legs, rs0LumpBisim,
sib/jcMulti/treeExpTreeN, noEqualEFeedback/degCons, m1m5, x1aDict, m4bConstancy,
rs1Assembly, jRat, jcInv) — filled with the REAL statements at instantiation (owners
per slot). REV 3/4 (rev-2 gap 5; Fable F3-C1/C2/G1/G4): `vpSound` is DELETED from the
pack and becomes the TYPED ledger field `cl10_vpsound : VPSound X` over the concrete
box (D10). `ksubM1C1` is DELETED and becomes the typed `KsubM1C1 M` in `cl11` —
REV 4: rebound to same-size CONTINUATIONS only (`o.c ≠ 0 →`), since the note's clause
is "equal-e CONTINUATION rides exclusively in the (c = 1, m = 1) rows" and same-size
HALTS (c = 0, the b_e^{term,fin} leaves) are generic — the faithful catalogue now
satisfies it (F3-C1). `ctsmSyntax` is REINSTATED as a full-statement slot (F3-C2: the
typed face `MenuWF M` — m ≥ 1, c ≤ m, PER-ENTRY TARGET TOTALITY (labeled honestly;
global compatibility is NOT this), empty menu = halt — is strictly weaker than CL-13's
"ONE fixed finite p-independent state set with DISPLAYED cell predicates and globally
compatible target-cell maps", and the ledger may not drop an open tag): `cl13 :
K.ctsmSyntax ∧ MenuWF M`. `MenuData` is PINNED (F3-G1): `menuCount` per-state outcome
counts with `menu_card` equations + `menu_not_all_empty` (kills the all-∅ dodge; a
single state MAY have an empty menu — that is the halt convention). p-INDEPENDENCE
made expressible (F3-C2/G4): `M` and `K` move OUT of the per-prime `UInstance` to the
p-UNIFORM layer — `theoremU` binds ONE `M` and ONE `K` BEFORE ∀ p, the same ∃-before-∀
discipline as `S`.
`CapstoneLedger` keeps a field PER CL ITEM (CL-2/CL-3 included, F6) PLUS the operative
consumption fields (`finiteness_stack`, `solve_stack` with explicit positivity,
`rs4_checksum`/`rs4_eval`, `cl4_env_tendsto`) PLUS the O3 pin `o3_teichmuller :
X.baseSection = .teichmuller` (gap 6). (REG-p) is NOT a ledger field: the ONE explicit
hypothesis.

**D8 — NO-CLAIM failure semantics = the restricted quantifier, no Lean artifact.** The
theorem's conclusion is `∀ p, p.Prime → RegP S D → (...)`. At a p failing (REG-p) the
implication is vacuously satisfied — Lean asserts NOTHING there: no equality, no bound,
no non-existence (the removable-auxiliary-zero case needs no encoding). This is the
note's failure semantics EXACTLY, for free. Design note only; no unit.

**D9 — The intended instantiation chain, and the non-vacuity boundary (F13).** The
interfaces are pinned to named upstream objects with owners: `ClassifierSpec` ←
MovesD's T_can trees + the OM engine's factorization types (HC-2 — `trueType` is the
semantic anchor; instantiating it with anything but the true ℤ_p factorization type is
an instantiation-fidelity violation adjudicated at the HC-2 audit, exactly like
MovesC's `JetSetup`); `FiberSeries` ← MovesD/[3t]'s complete finite realizable trees
with TREE-N thresholds; `SolveData`/`RegData` ← MovesS's block solve ([3]);
`KernelStatements` ← the owner notes per field ([3], [5], [2b], [2r], [1v], [3t], [4]).
What the abstract corpus CAN pin, it now does (the concrete polynomial space and
counts, stability, the slice characterization, the index-typed entry families with
pinned cardinalities, concrete SplittingType, concrete menus, the O3 pin). THE HONEST
NON-VACUITY STATEMENT (ruling (B), superseding REV 2's refuted "fake instance is dead"
claim): for U10's CLAUSE (i) — the classifier-keyed density — the degenerate-instance
objection DIES, because the clause asserts a real limit of real `Nat.card` counts over
the concrete box; a degenerate `canonical` merely makes clause (i) a true statement
about a different (unfaithful) classifier, which is exactly the conditionality the
note itself has ("keyed to ClassifierSpec verdicts"). For CLAUSE (ii) — the true-type
density — the objection MOVES INTO VP-SOUND's faithfulness: `cl10_vpsound : VPSound X`
is typed over the concrete box, and the residual pin (that `trueType` denotes real
ℤ_p factorization types, that the kernel slots carry the real statements) is DECLARED,
owner-audited at instantiation — the MovesC `JetSetup` precedent, not a hidden hole.

**D10 — U10's conclusion splits exactly as the note does (ruling (B); rev-2 criticals
1/2).** Clause (i): ∀ σ, `dmass σ N → R_σ(p)` — the classifier-keyed density, what
Theorem U literally concludes ("decided_σ(N)" IS T_can^τ-keyed in the note's own
notation). Clause (ii), the IDENTIFICATION COROLLARY (new unit U11): with
`VPSound X : ∀ N f σ, canonical N f = some σ → trueType N f = some σ` (typed over the
concrete box) and env → 0, the TRUE-type counts `trueCount σ N := Nat.card {f //
trueType N f = some σ}` obey `decided ≤ trueCount ≤ decided + undec` (soundness gives
the left inclusion; a true-σ class is decided-σ or undecided, since a decided-τ class
is true-τ by soundness and trueType is single-valued), so `trueDmass σ N → R_σ(p)` by
a second squeeze — "ρ_σ(p) IS the splitting density … the undecided complement has
mass 0 and the classifier verdicts are the true factorization types", at exactly the
note's granularity. Clause (iii): env → 0 re-emitted. The ℤ_p-Haar reading of the
limit of `trueDmass` is HC-2's declared bridge (D9), not re-derived here.

**D12 — The slice discipline (Codex-FINAL, REV 5): a unit's hypothesis is EXACTLY the
display's citation list.** In Lean, `(L : CapstoneLedger …)` assumes EVERY field —
projecting one field in the proof does not weaken the premise. So each intermediate
unit consumes a Prop SUB-BUNDLE matching its display's cited stack verbatim: U3 ←
`FinStack` (the (U-n) upper side's "finiteness stack {SQ.0's budgets … (CL-7); the
[3t] package (CL-10)}" — CL-10 WHOLE, `cl10_vpsound` included per REV 6 — + the
operative TREE-N identity); U4 ← `FinStack` +
`SolveStack` (the upper side's "solve stack {E0 (CL-1); the CL-5 nine; CL-6; the CL-8
(e1)–(e5) legs; CL-9 …; CL-11; CL-13…CL-16's table inputs; CL-17; CL-18; CL-19}" +
the operative RegP-guarded identification); U6 ← those + `LowerStack` ("the LOWER
side additionally GIVEN RS.4's inherited set (X.3/CL-4 included)"). CL-2/CL-3 attach
ONLY to the RATE form ("the RATE form … additionally inherits CL-2/CL-3 + the (X2-*)
family") = gate SQUEEZE-n3, not a Lean unit — so they appear in NO unit's premise
except U10's full `CapstoneLedger`, which IS the note's Theorem U consumption. The
sub-bundles are field-selections (projection defs), so the ledger structure and the
verified spine are untouched.

**D11 — File split kills the Defs circularity (gap 7).** `Defs.lean` (SplittingType,
Box/toPoly, ClassifierSpec + counts, SolveData, RegData/RegP, FiberSeries, MenuData +
KsubM1C1/MenuWF — NO ledger) ← `U0b_splitTypeFintype.lean` (the `Fintype
(SplittingType n)` + `Nonempty` instances) ← `DefsLedger.lean` (KernelStatements,
CapstoneLedger — its `∑ σ` now has its instance in scope — UInstance). All
ledger-consuming units import `DefsLedger`.

**The four TAG-FREE units** (= the note's re-audited unconditional perimeter, and the
only units proved without ledger fields): `U1_boxN`, `U2_tonelli`, `U5_sq3_arith`,
`U7_squeeze`. Everything else consumes hypothesis-structure fields and says so.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesU/Defs.lean` (inline; elaboration-phase target)

THREE-FILE ORDER (D11, gap 7): `Defs.lean` (below, NO ledger) ← `U0b_splitTypeFintype.lean`
← `DefsLedger.lean` (§2b).

```lean
import Mathlib
namespace LeanUrat.MovesU
open Filter Topology ENNReal Polynomial

/-- A splitting type of degree n: "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n"
    (SQ.4, verbatim; entries ≥ 1). CONCRETE — F11's repair. Fintype: unit U0b. -/
def SplittingType (n : ℕ) : Type :=
  {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n}

/-- The level-N box, CONCRETE (ruling (A)): the n free coefficients of a monic
    degree-n polynomial mod p^N (p^{nN} classes; a real Fintype). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- The monic polynomial a box point denotes: X^n + Σ_i C (f i) · X^i — THE
    polynomial space behind every count (rev-2 criticals 1/2's space objection). -/
noncomputable def Box.toPoly {p n N : ℕ} (f : Box p n N) : Polynomial (ZMod (p ^ N)) :=
  X ^ n + ∑ i : Fin n, C (f i) * X ^ (i : ℕ)

/-- The level reduction Box p n N' → Box p n N for N ≤ N' (`ZMod.castHom`, p^N ∣ p^N'). -/
noncomputable def boxProj (p n : ℕ) {N N' : ℕ} (h : N ≤ N') : Box p n N' → Box p n N :=
  fun f i => ZMod.castHom (pow_dvd_pow p h) _ (f i)

/-- The base digit section policy (D4R0K S1.4 (B4)/O3 — gap 6). -/
inductive BaseSection | teichmuller | unspecified
  deriving DecidableEq

/-- THE CLASSIFIER INTERFACE (rulings (A)/(B); replaces Census). HYPOTHESIS
    STRUCTURE, owner MovesD + HC-2 — the MovesC `JetSetup` precedent.
    `canonical`: T_can^τ's verdict-type map — "T_can^τ is a CHOICE-FREE function of f"
    ([1] L2 + VP; [3t] ONE-F); `some σ` = complete finite realizable tree, all leaves
    (τ-irr)/(τ-hen), certified at level N (thr ≤ N). `trueType`: the
    true-factorization-type field of the level-N class — constrained on the concrete
    box by `VPSound` (a LEDGER field, D10), its ℤ_p fidelity HC-2's declared bridge
    (D9); NOT a baked-in soundness law (rev-2 critical 1: soundness is an OPEN
    kernel, so it is a hypothesis, never an interface axiom). `canonical_stable`:
    TREE-N's join / Thm 2.1 decision stability. `baseSection`: the O3 pin datum
    (the ledger requires `= .teichmuller`). -/
structure ClassifierSpec (n p : ℕ) where
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  trueType : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ
  baseSection : BaseSection

variable {n p : ℕ}

/-- VP-SOUND at interface strength, TYPED over the concrete box (ruling (B); never a
    bare Prop slot): every decided-σ class has true factorization type σ. An OPEN
    kernel (CL-10's VP + VP-SOUND citation duty) — consumed as a ledger field. -/
def VPSound (X : ClassifierSpec n p) : Prop :=
  ∀ N (f : Box p n N) σ, X.canonical N f = some σ → X.trueType N f = some σ

/-- decided_σ(N) — DEFINED from the canonical map (never a free field). -/
noncomputable def ClassifierSpec.decided (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = some σ}
/-- undec(N) := #Undec(N). -/
noncomputable def ClassifierSpec.undec (X : ClassifierSpec n p) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = none}
/-- env(N) := undec(N)/p^{nN} (the measured envelope). -/
noncomputable def ClassifierSpec.env (X : ClassifierSpec n p) (N : ℕ) : ℝ :=
  (X.undec N : ℝ) / (p : ℝ) ^ (n * N)
/-- d_σ(N) := decided_σ(N)/p^{nN}. -/
noncomputable def ClassifierSpec.dmass (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℝ :=
  (X.decided σ N : ℝ) / (p : ℝ) ^ (n * N)
/-- The TRUE-type count (clause (ii)'s object, D10): #{f : trueType N f = some σ}. -/
noncomputable def ClassifierSpec.trueCount (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.trueType N f = some σ}
/-- The true-type mass trueCount_σ(N)/p^{nN}. -/
noncomputable def ClassifierSpec.trueDmass (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℝ :=
  (X.trueCount σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- HYPOTHESIS STRUCTURE (MovesS interface): the fixed p-independent rational output.
    R_σ := RS.1-SH's object — "the ONLY density-typed output of the solve" (§S type
    fence: no μ̂-typed marked total appears anywhere in MovesU). -/
structure SolveData (n : ℕ) where
  R : SplittingType n → RatFunc ℚ

/-- Literal evaluation of R_σ at q = p (Mathlib `RatFunc.eval`; junk 0 at poles —
    consumed ONLY under RegP, D6). -/
noncomputable def evalℝ (S : SolveData n) (σ : SplittingType n) (p : ℕ) : ℝ :=
  ((S.R σ).eval (RingHom.id ℚ) (p : ℚ) : ℚ)

/-- "The fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED (q₀ not a pole)". -/
def DefinedAt (g : RatFunc ℚ) (q₀ : ℚ) : Prop := g.denom.eval q₀ ≠ 0

/-- HYPOTHESIS STRUCTURE (MovesS/§S S.4 interface; F4/F10 repair): the (REG-p) bundle.
    Q(p) = EXACTLY the image of the base-change depths (δ = 1 required — nonempty, never
    an arbitrary Finset); Block nonempty; K_e as literal matrices; ALL SEVEN displayed
    entry families as data (b_e BOTH components, per-cell J (CL-18), ι_e, W_Ŝ, every
    β_{e,τ} leg); ACT abstract (CTS-M(ii), owner [1v]). -/
structure RegData (p : ℕ) where
  depthSet : Finset ℕ                          -- base-change depths δ of RS.1-SH
  one_mem_depthSet : 1 ∈ depthSet              -- δ = 1 (the shallow pool) always arises
  Pool : Finset ℕ                              -- Q(p)
  pool_eq : Pool = depthSet.image (p ^ ·)      -- Q(p) IS the depth image
  Block : Type
  instB : Fintype Block
  instNe : Nonempty Block                      -- the top block exists
  -- per-block state indices: size PINNED to the table's row count (ruling (C))
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  instBiNe : ∀ e, Nonempty (bidx e)            -- kills the empty-det = 1 dodge
  blockDim : Block → ℕ                         -- the block table's row count (owner [1v]/[3])
  blockDim_pos : ∀ e, 0 < blockDim e
  bidx_card : ∀ e, Fintype.card (bidx e) = blockDim e
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)   -- {each entry of K_e}
  bterm : ∀ e : Block, bidx e → RatFunc ℚ      -- b_e^{term,fin}
  bsplit : ∀ e : Block, bidx e → RatFunc ℚ     -- b_e^split
  iota : ∀ e : Block, bidx e → RatFunc ℚ       -- {each entry of ι_e}
  -- per-cell J entries (CL-18): |Jcell e| = the table's branching-cell count.
  -- REV 4 (F3-G3): EQUATION pin only, NO positivity — (K-TRI) minimal blocks may
  -- have zero branching cells; positivity would risk truthful uninstantiability.
  cellCount : Block → ℕ
  JIdx : Block → Type
  instJ : ∀ e, Fintype (JIdx e)
  JIdx_card : ∀ e, Fintype.card (JIdx e) = cellCount e
  Jcell : ∀ e : Block, JIdx e → RatFunc ℚ
  -- W_Ŝ coefficients (CL-17): one per shallow shape (equation pin only, F3-G3)
  shapeCount : ℕ
  WIdx : Type
  instW : Fintype WIdx
  WIdx_card : Fintype.card WIdx = shapeCount
  Wcoef : WIdx → RatFunc ℚ
  -- β legs: per (leg, depth δ); entryList covers EVERY δ ∈ depthSet (per-pool coverage)
  legCount : Block → ℕ
  legIdx : Block → Type
  instL : ∀ e, Fintype (legIdx e)
  legIdx_card : ∀ e, Fintype.card (legIdx e) = legCount e
  betaLeg : ∀ e : Block, legIdx e → ℕ → RatFunc ℚ
  act : RatFunc ℚ → ℕ → ℚ                      -- ACT active value at a pool

/-- E(e) — a DEFINITION, verbatim the union SQ.4 displays; every family index-typed
    and cardinality-pinned (ruling (C)), the β images taken at EVERY depth of
    `depthSet`. (Classical DecidableEq on RatFunc ℚ for the images.) -/
noncomputable def RegData.entryList {p : ℕ} (D : RegData p) (e : D.Block) :
    Finset (RatFunc ℚ) :=
  letI := Classical.decEq (RatFunc ℚ)
  letI := D.instBi e; letI := D.instBd e; letI := D.instJ e
  letI := D.instW; letI := D.instL e
  (Finset.univ.image fun ij : D.bidx e × D.bidx e => D.K e ij.1 ij.2)
    ∪ (Finset.univ.image (D.bterm e)) ∪ (Finset.univ.image (D.bsplit e))
    ∪ (Finset.univ.image (D.Jcell e)) ∪ (Finset.univ.image (D.iota e))
    ∪ (Finset.univ.image D.Wcoef)
    ∪ D.depthSet.biUnion (fun δ => Finset.univ.image (fun l => D.betaLeg e l δ))

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every member of the DEFINED E(e)
    (all seven displayed families, cardinality-pinned) defined at q₀ AND literal =
    ACT active value ((ii-c) agreement); PLUS the EVALUABILITY clause (ruling (D),
    rev-2 critical 4): the literal R_σ(p) is DEFINED — "UNDER (REG-p), the literal
    evaluation R_σ(p) of the fixed element of ℚ(q) is DEFINED and IS the active
    value". Neither implies nor is implied by E0/CL-1 or ACT/CL-5 (D5). Never
    vacuous: Pool ∋ p^1, Block nonempty, every index family nonempty-pinned. -/
def RegP {n p : ℕ} (S : SolveData n) (D : RegData p) : Prop :=
  (∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀) ∧
  (∀ σ : SplittingType n, DefinedAt (S.R σ) (p : ℚ))

/-- HYPOTHESIS STRUCTURE (MovesD/[3t] interface; F2 repair): the tree-fiber series.
    `Tree σ` = the complete finite realizable canonical trees of verdict-type σ (owner
    MovesD); `thr` = TREE-N's decision threshold; `mem_slice_iff` CHARACTERIZES the
    slice as the thr ≤ N slice (no arbitrary Finset family). The Finset TYPE of
    `thrSlice` is CL-7's finiteness riding the instantiation (D4 — TRACK-COUNT + D(n)
    + genuine-increment, OPEN upstream, named in KernelStatements). The tie to the
    classifier's counts is the ledger's `finiteness_stack` IDENTITY (TREE-N):
    an empty `Tree σ` forces decided_σ ≡ 0 — nothing degenerate satisfiable (D4). -/
structure FiberSeries (n p : ℕ) (X : ClassifierSpec n p) where
  Tree : SplittingType n → Type
  instTreeDeq : ∀ σ, DecidableEq (Tree σ)       -- gap 7: needed to build the Finsets
  mass : ∀ σ, Tree σ → ℝ≥0∞                     -- μ(fiber T): RS.1's positive series
  thr : ∀ σ, Tree σ → ℕ                         -- TREE-N's threshold
  thrSlice : ∀ σ : SplittingType n, ℕ → Finset (Tree σ)
  mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ thr σ T ≤ N
  slice_exhausts : ∀ σ (T : Tree σ), T ∈ thrSlice σ (thr σ T)   -- kept explicit (F2)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (σ : SplittingType n) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

/-- One menu outcome, minimal concrete vocabulary (ruling (E), rev-2 gap 5):
    m members, c continuations, whether it stays at equal block size, and its
    target state (`none` = halt — the (BDY)/empty-continuation reading). -/
structure MenuEntry (State : Type) where
  m : ℕ
  c : ℕ
  sameSize : Bool
  target : Option State
  deriving DecidableEq

/-- The move-menu vocabulary (CL-13/CL-11's MovesU-visible face; owner [1v]/[2a]):
    the ONE fixed finite state set with per-state outcome menus AS FINSETS — bound at
    the p-UNIFORM layer (before ∀ p; F3-C2/G4). REV 4 pin (F3-G1): per-state outcome
    counts are catalogue DATA with a card equation, and menus are not ALL empty
    (a single empty menu = the halt convention and stays allowed). -/
structure MenuData where
  State : Type
  instState : Fintype State
  instStateDeq : DecidableEq State
  instStateNe : Nonempty State
  menu : State → Finset (MenuEntry State)
  menuCount : State → ℕ                       -- the catalogue's per-state outcome count
  menu_card : ∀ s, (menu s).card = menuCount s
  menu_not_all_empty : ∃ s, menuCount s ≠ 0   -- kills the all-∅ vacuity dodge (F3-G1)

/-- The (K-SUB) m = 1 classification as a REAL Prop over menus. REV 4 (F3-C1):
    binds same-size CONTINUATIONS ONLY — "equal-e CONTINUATION rides EXCLUSIVELY in
    K_e's (c = 1, m = 1) rows" (the same-size single-child direction). Same-size
    HALTS (c = 0, the b_e^{term,fin} leaves) are generic and EXEMPT: without the
    `o.c ≠ 0` guard the faithful catalogue would falsify the Prop. -/
def KsubM1C1 (M : MenuData) : Prop :=
  ∀ s, ∀ o ∈ M.menu s, o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1

/-- CL-13's menu well-formedness FACE (the typed trace, asserted BESIDE the
    full-statement slot `ctsmSyntax` in `cl13` — F3-C2): every outcome has ≥ 1
    member, ≤ m continuations, and PER-ENTRY TARGET TOTALITY on continuing outcomes
    (honest label — this is NOT the global compatibility of the target-cell maps,
    which lives in the `ctsmSyntax` slot with the cell predicates and
    p-independence); the empty menu is the halt convention. -/
def MenuWF (M : MenuData) : Prop :=
  ∀ s, ∀ o ∈ M.menu s, 1 ≤ o.m ∧ o.c ≤ o.m ∧ (o.c ≠ 0 → o.target.isSome)

end LeanUrat.MovesU
```

## 2b. The kernel pack + capstone ledger — `MovesU/DefsLedger.lean` (imports U0b, D11)

```lean
import LeanUrat.MovesU.U0b_splitTypeFintype  -- Fintype (SplittingType n) IN SCOPE (gap 7)
/-- THE KERNEL STATEMENT PACK (F5/F6/F7): one named Prop slot per open
    kernel/obligation of the capstone ledger. Filled with the REAL upstream statements
    at instantiation (owner per slot); filling a slot with `True` is an
    instantiation-fidelity violation adjudicated at the owner's audit (D9). -/
structure KernelStatements where
  escapeE0 : Prop         -- CL-1 [3]: per-pool ESCAPE(E0) active-block solvability
  weightCharge : Prop     -- CL-2 [5]: X.1b WEIGHT-CHARGE via X.2's env constants (F6)
  progressX2 : Prop       -- CL-3 [5]+[2b]: PROGRESS — (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/
                          --   (X2-TAILS) with constants c₃(n), c₄(n), s(n) (F6)
  x3Termination : Prop    -- CL-4 [5]: X.3 termination a.e. (statement slot; its
                          --   operative trace is the `cl4_env_tendsto` field below)
  xhdM4aX : Prop          -- CL-5(i) [2b]: XHD = M4a-X (+ (ENT-U))
  d4r0 : Prop             -- CL-5(ii) [1]: D4R.0 — CLOSED upstream; ledger-echo slot
  ctsmIvPart : Prop       -- CL-5(iii) [1v]: CTS-M(iv)-PART
  ctsmIvRep : Prop        -- CL-5(iv) [1v]: CTS-M(iv)-REP = M2(ii)
  ctsmIvMeas : Prop       -- CL-5(v) [1v]: CTS-M(iv)-MEAS
  ctsmVHmc : Prop         -- CL-5(vi) [1v]: CTS-M(v) HMC
  ctsmIiAct : Prop        -- CL-5(vii) [1v]: CTS-M(ii) ACT + (ii-c) — RELATED to (r2),
                          --   SEPARATE (rev 6: neither implies the other)
  ctsmIiiInit : Prop      -- CL-5(viii) [1v]: CTS-M(iii) INIT + ENT-COUNT (ENT-AGG/INIT-RAT)
  ctsmViComp : Prop       -- CL-5(ix) [1v]: CTS-M(vi) COMP-typing
  ctsmIvPoly : Prop       -- CL-6 [1v]: (iv)-POLY — without it R_σ ∈ ℚ(q) unfounded
  trackCount : Prop       -- CL-7a [4]: TRACK-COUNT + explicit L(n)
  dnDuty : Prop           -- CL-7b [4]: the D(n) duty (candidate n!, underived)
  genuineIncrement : Prop -- CL-7c [4]: the positive genuine-increment sub-claim
  rel1 : Prop             -- CL-8 [2r]: REL.1 re-scoped
  rel2a : Prop            -- CL-8 [2r]: REL.2(a)
  rel2b : Prop            -- CL-8 [2r]: REL.2(b)
  rel2d : Prop            -- CL-8 [2r]: REL.2(d)
  rel2e : Prop            -- CL-8 [2r]: REL.2(e), the β-typing (e1)–(e5) leg
  rel3 : Prop             -- CL-8 [2r]: REL.3 over O_δ
  rs0LumpBisim : Prop     -- CL-9 [3]: RS.0 (α) lumpability + (β) bisimulation = XRB
  sib : Prop              -- CL-10 [3t]: (SIB)/(SIB-STEP), measure-level joint form
  jcMulti : Prop          -- CL-10 [3t]: (JC-multi)
  treeExpTreeN : Prop     -- CL-10 [3t]: TREE-EXP(-fin/-ns) + TREE-N, (NS-ROUTE)-scoped
  -- (vpSound: DELETED as a slot at REV 3 — now the TYPED ledger field
  --  `cl10_vpsound : VPSound X`, ruling (B); rev-2 gap 5)
  noEqualEFeedback : Prop -- CL-11 [4]/[1v]: no-equal-e-feedback + DEG-CONS full roster
  -- (ksubM1C1: typed-only since REV 3 — `KsubM1C1 M` in cl11; its content is fully
  --  expressible over MenuData, so no bare slot is needed)
  ctsmSyntax : Prop       -- CL-13 [1v], REINSTATED at REV 4 (F3-C2): the FULL
                          --   CTS-M(i) statement — the ONE fixed finite p-independent
                          --   state set with DISPLAYED cell predicates and GLOBALLY
                          --   COMPATIBLE target-cell maps ("without it no path
                          --   product or kernel index type-checks"); the typed face
                          --   MenuWF M rides beside it in cl13, replacing NOTHING
  m1m5 : Prop             -- CL-14 [2a]: M1 + M5 — CLOSED upstream; ledger-echo slot
  x1aDict : Prop          -- CL-15 [5]: the per-species GMN index dictionary
  m4bConstancy : Prop     -- CL-16 [1v]/[2b]: M4b constancy + M4b-T equivariance (π_v)
  rs1Assembly : Prop      -- CL-17 [3]: RS.1-SH + routing + unique shallow cut + W_Ŝ
  jRat : Prop             -- CL-18 [1v]/[2b]: (J-RAT) per-cell rational tables
  jcInv : Prop            -- CL-19 [2b]: (JC-INV) joint digit-cell law

/-- THE CAPSTONE LEDGER (SQ.4's CL-1…CL-19, REV 16 extent) as ONE Prop structure:
    a field PER CL ITEM asserting its kernel slot (F5; CL-2/CL-3 included, F6) PLUS
    the operative consumption fields. "Neither this display nor any acceptance record
    may drop a tag while any cited CL-item is open." (REG-p) is NOT a field: the ONE
    explicit hypothesis. CL-12 is CLOSED ("NOTHING at CL-12 is open") — no slot. -/
structure CapstoneLedger (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (S : SolveData n) (D : RegData p) (M : MenuData) (K : KernelStatements) : Prop where
  cl1 : K.escapeE0
  cl2 : K.weightCharge
  cl3 : K.progressX2
  cl4 : K.x3Termination
  cl5 : K.xhdM4aX ∧ K.d4r0 ∧ K.ctsmIvPart ∧ K.ctsmIvRep ∧ K.ctsmIvMeas ∧
        K.ctsmVHmc ∧ K.ctsmIiAct ∧ K.ctsmIiiInit ∧ K.ctsmViComp
  cl6 : K.ctsmIvPoly
  cl7 : K.trackCount ∧ K.dnDuty ∧ K.genuineIncrement
  cl8 : K.rel1 ∧ K.rel2a ∧ K.rel2b ∧ K.rel2d ∧ K.rel2e ∧ K.rel3
  cl9 : K.rs0LumpBisim
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN
  /-- CL-10's VP-SOUND leg, TYPED over the concrete box (ruling (B)): decided-σ ⟹
      true type σ. The identification corollary (U11, clause (ii)) consumes it. -/
  cl10_vpsound : VPSound X
  cl11 : K.noEqualEFeedback ∧ KsubM1C1 M
  /-- CL-13 in FULL (F3-C2): the reinstated full-statement slot AND the typed menu
      face — no open tag dropped (SQ.4's acceptance-record rule binds this form). -/
  cl13 : K.ctsmSyntax ∧ MenuWF M
  /-- The O3 BASE-PIN DECLARATION (SQ.4's display duty, gap 6): the pinned base digit
      section is TEICHMÜLLER (D4R0K S1.4 (B4)/O3) — "declared once, as the definitive
      write-up must". -/
  o3_teichmuller : X.baseSection = BaseSection.teichmuller
  cl14 : K.m1m5
  cl15 : K.x1aDict
  cl16 : K.m4bConstancy
  cl17 : K.rs1Assembly
  cl18 : K.jRat
  cl19 : K.jcInv
  /-- OPERATIVE, the finiteness stack's consumed form (CL-7 + CL-10): TREE-N's exact
      fiber count summed over the thr ≤ N slice —
      "decided_σ(N) = Σ_{T : typemult(T) = σ, thr(T) ≤ N} #fiber(T) is a FINITE sum
      (SQ.0/CL-7) of exact fiber counts (TREE-N/CL-10)". This identity is also the
      series' tie to the classifier (D4, F2). -/
  finiteness_stack : ∀ σ N,
    (X.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T
  /-- OPERATIVE, the solve stack's consumed form (CL-1, CL-5, CL-6, CL-8, CL-9, CL-11,
      CL-13…CL-17, CL-18, CL-19 — the slots asserted above): UNDER (REG-p) the
      extended-value sum is finite, IS the literal R_σ(p), AND R_σ(p) ≥ 0 — "RS.3's
      positivity ((I − A(q₀))^{−1} ≥ 0) and R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN
      E0 + the CL-5 mass identification" (F8's repair: positivity is a conjunct, not
      an inference from `ofReal`). -/
  solve_stack : RegP S D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
    0 ≤ evalℝ S σ p
  /-- RS.4's checksum (§S S.5) WITH its full inherited set riding verbatim: "E0, the
      CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain incl.
      (J-RAT)/CL-18". The ℚ(q) identity — Theorem U's checksum conjunct.
      (Needs U0b's `Fintype (SplittingType n)`.) -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) — the form SQ.3's arithmetic consumes. Same
      inherited set. (E-phase note: derivable from `rs4_checksum` + (r2)-definedness
      via RatFunc eval-hom side conditions; carried as a field until that unit lands.) -/
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1
  /-- OPERATIVE trace of CL-4 = X.3 (QUALITATIVE form — "the limit consumes no
      envelope constant"; the statement slot is `cl4` above; discharges only at [5]'s
      EVENT): env(N) → 0. The quantitative rate form (CL-2/CL-3's constants) is
      asserted via the `cl2`/`cl3` slots but not consumed by any MovesU proof — gate
      SQUEEZE-n3 is a census artifact, not a Lean unit. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)

/-- THE PER-p INSTANTIATION BUNDLE (for U10's quantifier shape): everything Theorem U
    needs at one prime, over the FIXED p-uniform data (S, M, K — F3-C2/G4: one menu
    vocabulary and one kernel pack for ALL primes, so CL-13's p-independence and the
    slots' p-uniform referents are expressible). -/
structure UInstance (n : ℕ) (S : SolveData n) (M : MenuData) (K : KernelStatements)
    (p : ℕ) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  L : CapstoneLedger n p X F S D M K

/-- SQ.2-partial's EXACT stack (D12): the finiteness stack {CL-7; CL-10} + the
    operative TREE-N identity — nothing else (Codex-FINAL 1). -/
structure FinStack (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (K : KernelStatements) : Prop where
  cl7 : K.trackCount ∧ K.dnDuty ∧ K.genuineIncrement
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN
  /-- REV 6 (Codex-FINAL#2): CL-10 is cited WHOLE by the (U-n) upper side ("the [3t]
      package (CL-10)"), and VP-SOUND is part of CL-10's own entry — so the typed
      VP-SOUND field belongs to THIS slice, not only to the capstone. -/
  cl10_vpsound : VPSound X
  finiteness_stack : ∀ σ N,
    (X.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T

/-- SQ.2-upper's EXACT solve stack (D12): the (U-n) upper-side citation list —
    CL-1, CL-5, CL-6, CL-8, CL-9, CL-11, CL-13…CL-16, CL-17, CL-18, CL-19 — + the
    operative RegP-guarded identification. NO CL-2/CL-3/CL-4, NO RS.4, NO VP-SOUND,
    NO O3 (Codex-FINAL 2). -/
structure SolveStack (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (S : SolveData n) (D : RegData p) (M : MenuData) (K : KernelStatements) : Prop where
  cl1 : K.escapeE0
  cl5 : K.xhdM4aX ∧ K.d4r0 ∧ K.ctsmIvPart ∧ K.ctsmIvRep ∧ K.ctsmIvMeas ∧
        K.ctsmVHmc ∧ K.ctsmIiAct ∧ K.ctsmIiiInit ∧ K.ctsmViComp
  cl6 : K.ctsmIvPoly
  cl8 : K.rel1 ∧ K.rel2a ∧ K.rel2b ∧ K.rel2d ∧ K.rel2e ∧ K.rel3
  cl9 : K.rs0LumpBisim
  cl11 : K.noEqualEFeedback ∧ KsubM1C1 M
  cl13 : K.ctsmSyntax ∧ MenuWF M
  cl14 : K.m1m5
  cl15 : K.x1aDict
  cl16 : K.m4bConstancy
  cl17 : K.rs1Assembly
  cl18 : K.jRat
  cl19 : K.jcInv
  solve_stack : RegP S D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
    0 ≤ evalℝ S σ p

/-- (U-n)-LOWER's ADDITIONAL slice (D12): RS.4's checksum with its inherited set —
    the CL-4 slot ("X.3/CL-4 included") + both checksum forms. CL-2/CL-3 attach ONLY
    to the rate form = gate SQUEEZE-n3, not a Lean unit (Codex-FINAL 3). -/
structure LowerStack (n p : ℕ) (S : SolveData n) (D : RegData p)
    (K : KernelStatements) : Prop where
  cl4 : K.x3Termination
  rs4_checksum : ∑ σ, S.R σ = 1
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1

/-- Field-selection projections: U10 fires the earlier units without re-packing. -/
def CapstoneLedger.finStack (L : CapstoneLedger n p X F S D M K) :
    FinStack n p X F K := ⟨L.cl7, L.cl10, L.cl10_vpsound, L.finiteness_stack⟩
def CapstoneLedger.solveStack (L : CapstoneLedger n p X F S D M K) :
    SolveStack n p X F S D M K :=
  ⟨L.cl1, L.cl5, L.cl6, L.cl8, L.cl9, L.cl11, L.cl13, L.cl14, L.cl15, L.cl16,
   L.cl17, L.cl18, L.cl19, L.solve_stack⟩
def CapstoneLedger.lowerStack (L : CapstoneLedger n p X F S D M K) :
    LowerStack n p S D K := ⟨L.cl4, L.rs4_checksum, L.rs4_eval⟩
```

Greppable audit: every CL-1 … CL-19 item is now a REAL hypothesis field (F5) — the
`cl1`…`cl19` assertions over named `KernelStatements` slots — with CL-2/CL-3 present
(F6) and CL-12 correctly absent (CLOSED — "NOTHING at CL-12 is open"; its O3 base-pin
display duty is a write-up sentence, out of Lean scope).

---

## 3. The unit DAG — 13 units, one file each: `lean/LeanUrat/MovesU/<id>.lean`

Layers: L0 Defs+counting (U0, U0b, U1) → L1 series (U2–U4) → L2 bracket (U5–U6) →
L3 limit (U7) → L4 schema/aux (U8–U9) → L5 capstone (U10, U11). TAG-FREE = proved with
no ledger/structure hypothesis fields beyond definitions. Import order per D11:
Defs ← U0b ← DefsLedger ← every ledger-consuming unit (U3, U4, U6, U10, U11).

### U0b `MovesU.U0b_splitTypeFintype` — splitting types are a nonempty Fintype  [support]
- **file**: `MovesU/U0b_splitTypeFintype.lean` (imports Defs ONLY; imported BY
  DefsLedger — the gap-7 circularity fix, D11)  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement**: `instance : Fintype (SplittingType n)` and
  `theorem splittingType_nonempty (hn : 1 ≤ n) : Nonempty (SplittingType n)`
- **moves_ref**: "For each splitting type σ of degree n (a multiset of pairs (e_i, f_i)
  with Σ e_i·f_i = n)" (SQ.4)
- **sketch**: entries (e,f) have e·f ≤ n so e,f ≤ n and card σ ≤ n: embed into the
  multisets over `(Finset.range (n+1) ×ˢ Finset.range (n+1))` of card ≤ n
  (`Multiset.finite...`/`Set.Finite.fintype` route, classical OK); nonempty via
  ⟨{(n,1)}⟩. Needed by every `∑ σ` (rs4_checksum, (BOX-N), U10).
- **hypothesis_fields**: none.

### U0 `MovesU.U0_boxCard` — the box cardinality  [support, tag-free]
- **file**: `MovesU/U0_boxCard.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem boxCard (p n N : ℕ) [NeZero p] : Nat.card (Box p n N) = p ^ (n * N)`
- **moves_ref**: "the monic degree-n coefficient box mod p^N (p^{nN} residue classes)"
- **sketch**: `Nat.card (Fin n → ZMod (p^N)) = (p^N)^n = p^(n*N)`; `Nat.card_fun`/
  `Nat.card_eq_fintype_card`, `ZMod.card` (needs `NeZero (p^N)` from `NeZero p`), `pow_mul` (commuted).
- **hypothesis_fields**: none.

### U1 `MovesU.U1_boxN` — (BOX-N), the count identity  [TAG-FREE step 1]
- **file**: `MovesU/U1_boxN.lean`  ·  **difficulty**: medium  ·  **deps**: U0, U0b
- **statement**: `theorem boxN (X : ClassifierSpec n p) [NeZero p] (N : ℕ) :`
  `(∑ σ : SplittingType n, X.decided σ N) + X.undec N = p ^ (n * N)`
- **moves_ref**: "(BOX-N) p^{nN} = Σ_τ decided_τ(N) + undec(N) — the box partition,
  EXACT and tag-free as an identity of counts"
- **sketch**: partition the Fintype `Box p n N` by the value of `X.canonical N` in
  `Option (SplittingType n)`: `Finset.card_eq_sum_card_fiberwise` (Mathlib
  `Algebra/BigOperators/Group/Finset/Basic.lean`) over `Finset.univ`; fibers of
  `some σ` are `decided`, fiber of `none` is `undec` (`Nat.card_eq_fintype_card` +
  subtype/filter card transfer); close with U0. Tag-free BECAUSE it is a count
  identity for the interface's canonical map — the map's fidelity Props
  (`canonical_stable`; VP-SOUND as the ledger's `cl10_vpsound`) are carried
  elsewhere, not consumed here.
- **hypothesis_fields**: none consumed (F1's repair: the verdict is now the pinned
  classifier interface, D2; no arbitrary labeling is an instance).

### U2 `MovesU.U2_tonelli` — extended-value existence + partial-sum domination  [TAG-FREE step 3]
- **file**: `MovesU/U2_tonelli.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem tonelli_partial_le {X : ClassifierSpec n p}`
  `(F : FiberSeries n p X) (σ : SplittingType n) (N : ℕ) :`
  `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`
- **moves_ref**: "the positive series has a well-defined EXTENDED-VALUE sum in [0, ∞]
  unconditionally (nonnegative terms) … FINITENESS … and IDENTIFICATION … are NOT
  Tonelli's" (rev 2, pass-1 critical 7)
- **sketch**: `ENNReal.sum_le_tsum` (`Topology/Algebra/InfiniteSum/ENNReal.lean`);
  existence is the totality of `∑'` in ℝ≥0∞ (`ENNReal.summable`,
  `ENNReal.tsum_eq_iSup_sum` — cite in a doc comment; no separate lemma needed).
- **hypothesis_fields**: none (the FiberSeries DATA is used, no Prop field).

### U3 `MovesU.U3_sq2_partial` — decided mass IS the thr ≤ N partial sum  [conditional]
- **file**: `MovesU/U3_sq2_partial.lean`  ·  **difficulty**: easy  ·  **deps**: U2
- **statement** (F3's repair — the IDENTITY is the claim; REV 5/Codex-FINAL 1: the
  premise is the SLICE, never the full ledger):
  `theorem sq2_partial (FS : FinStack n p X F K) (σ N) :`
  `(X.decided σ N : ℝ≥0∞) = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T`
  and `theorem sq2_partial_le … : (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ`
- **moves_ref**: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
  positive tree-fiber series for type σ" (SQ.2 ROUTE); tags "(SQ.0/CL-7) … (TREE-N/CL-10)"
- **sketch**: the identity IS `FS.finiteness_stack σ N` (re-exposed as the unit's named
  statement so the exact claim is auditable, not hidden — F3); the corollary rewrites
  by it and applies U2 + `mul_le_mul_left'`.
- **hypothesis_fields**: EXACTLY `FinStack` (CL-7 + CL-10 + the TREE-N identity, D12).

### U4 `MovesU.U4_sq2_upper` — SQ.2, the fixpoint upper bound  [conditional]
- **file**: `MovesU/U4_sq2_upper.lean`  ·  **difficulty**: medium  ·  **deps**: U3
- **statement** (REV 5/Codex-FINAL 2 — the premise is FinStack + SolveStack, the
  (U-n) upper side's two cited stacks and NOTHING else):
  `theorem sq2_upper (FS : FinStack n p X F K) (SS : SolveStack n p X F S D M K)`
  `(hreg : RegP S D) (hp : p.Prime) (σ N) :`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` (F9: `p.Prime`, never
  `1 < p`; ruling (D): `hreg` also gives `DefinedAt (S.R σ) p`, so `evalℝ` is the
  genuine literal value, never junk)
- **moves_ref**: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
  "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 + the CL-5 mass
  identification"
- **sketch** (F8's repair): `SS.solve_stack hreg σ` GIVES `0 ≤ evalℝ S σ p` as its
  third conjunct — no bogus case split. Transfer ℝ≥0∞ → ℝ from U3's corollary (fired
  on `FS`): `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since the RHS is finite),
  `ENNReal.toReal_mul`, `ENNReal.toReal_ofReal` (nonnegativity = the positivity
  conjunct).
- **hypothesis_fields**: EXACTLY `FinStack` + `SolveStack` (the (U-n) upper side's
  displayed citation list, D12 — NO CL-2/CL-3/CL-4, NO RS.4, NO O3; VP-SOUND rides
  IN FinStack via `cl10_vpsound`, per the whole-CL-10 citation [rev-7 gloss fix —
  the F4-G1 stale phrase]); explicit `RegP S D`, `p.Prime`.

### U5 `MovesU.U5_sq3_arith` — SQ.3's bracket arithmetic AS arithmetic  [TAG-FREE step 2]
- **file**: `MovesU/U5_sq3_arith.lean`  ·  **difficulty**: medium  ·  **deps**: U1
- **statement** (every tagged input an EXPLICIT argument — the tag-free content is the
  implication): `theorem sq3_arith (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)`
  `(R : SplittingType n → ℝ) (σ : SplittingType n) (N : ℕ)`
  `(hupper : ∀ τ, τ ≠ σ → (X.decided τ N : ℝ) ≤ R τ * (p : ℝ) ^ (n * N))`
  `(hsum : ∑ τ, R τ = 1) :`
  `(R σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ)`
  (`1 < p` here is ARITHMETIC SCAFFOLDING — p^{nN} ≠ 0 — not the note's quantifier;
  the note's display is asserted only through U6/U10, at primes)
- **moves_ref**: "decided_σ(N) = p^{nN} − Σ_{τ≠σ} decided_τ(N) − undec(N) ≥
  p^{nN}·(1 − Σ_{τ≠σ} R_τ(p) − env(N)) = (R_σ(p) − env(N))·p^{nN}" (SQ.3)
- **sketch**: cast U1's (BOX-N) to ℝ; `Finset.sum_erase_add`/`sub` bookkeeping;
  `env` unfolds to `undec/p^{nN}` with `div_mul_cancel₀` (`p^{nN} ≠ 0` from `hp`);
  finish by `linarith` over the τ ≠ σ sum of `hupper` + `hsum`. Pure ℝ arithmetic:
  no ledger, no RegP — the inputs carry the tags, as the note's re-audit says.
- **hypothesis_fields**: none (tag-free as an implication; instantiated at U6 with
  tagged inputs).

### U6 `MovesU.U6_un_bracket` — (U-n), the two-sided bracket  [conditional; the note's product]
- **file**: `MovesU/U6_un_bracket.lean`  ·  **difficulty**: easy  ·  **deps**: U4, U5
- **statement** (REV 5/Codex-FINAL 3 — the NON-RATE bracket, on exactly its displayed
  stacks: upper = FinStack + SolveStack, lower additionally LowerStack; CL-2/CL-3
  appear NOWHERE — they attach only to the rate form, which is gate SQUEEZE-n3 and
  not a Lean unit, so no U6b exists):
  `theorem un_bracket (FS : FinStack n p X F K) (SS : SolveStack n p X F S D M K)`
  `(LS : LowerStack n p S D K) (hreg : RegP S D) (hp : p.Prime) (σ N) :`
  `(evalℝ S σ p - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` — `p.Prime` per F9
  (`NeZero p`/`1 < p` derived from `hp` inside)
- **moves_ref**: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
  every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing (REG-p) neither
  inequality is asserted" (the rev-3 qualifier = the `hreg` argument, D8)
- **sketch**: right leg = U4 (on FS, SS); left leg = U5 applied with `R := fun τ =>
  evalℝ S τ p`, `hupper` from U4 at each τ ≠ σ, `hsum := LS.rs4_eval hreg`.
- **hypothesis_fields**: EXACTLY `FinStack` + `SolveStack` + `LowerStack` (the lower
  side's "additionally GIVEN RS.4's inherited set (X.3/CL-4 included)", D12);
  explicit `RegP S D`.

### U7 `MovesU.U7_squeeze` — the limit forcing  [TAG-FREE step 4]
- **file**: `MovesU/U7_squeeze.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement** (bracket + env-limit as EXPLICIT arguments; `1 < p` = arithmetic
  scaffolding, as at U5): `theorem squeeze_limit`
  `(X : ClassifierSpec n p) (hp : 1 < p) (r : ℝ) (σ : SplittingType n)`
  `(hbr : ∀ N, (r - X.env N) * (p:ℝ)^(n*N) ≤ (X.decided σ N : ℝ) ∧`
  `           (X.decided σ N : ℝ) ≤ r * (p:ℝ)^(n*N))`
  `(henv : Tendsto X.env atTop (𝓝 0)) :`
  `Tendsto (X.dmass σ) atTop (𝓝 r)`
- **moves_ref**: "With env(N) → 0 (X.3/CL-4, the QUALITATIVE form …):
  ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN} EXISTS and = R_σ(p)"
- **sketch**: divide `hbr` by `p^{nN} > 0` (`div_le_div_of_nonneg_right` forms) to get
  `r − env N ≤ dmass σ N ≤ r`; squeeze with Mathlib's
  `tendsto_of_tendsto_of_tendsto_of_le_of_le` (`Topology/Order/Basic.lean`; the `'`
  eventually-variant if convenient); lower leg `r − env N → r − 0 = r` by
  `Filter.Tendsto.const_sub` (`Topology/Algebra/Group/Basic.lean`, the `to_additive`
  of `Tendsto.const_div'`) + `sub_zero`; upper leg `tendsto_const_nhds`.
- **hypothesis_fields**: none (tag-free forcing; the tagged bracket/limit enter as
  arguments, instantiated at U10 from U6 + `cl4_env_tendsto`).

### U8 `MovesU.U8_regP_access` — (REG-p) accessors over the FULL entry list  [definitional]
- **file**: `MovesU/U8_regP_access.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement** (the generic accessor + one corollary PER displayed family + (r1) +
  nonemptiness + REV 3's evaluability accessor):
  `theorem RegP.entry_agree {S : SolveData n} {D : RegData p} (h : RegP S D)`
  `  (hq : q₀ ∈ D.Pool) (e) {g} (hg : g ∈ D.entryList e) :`
  `  DefinedAt g q₀ ∧ g.eval (RingHom.id ℚ) q₀ = D.act g q₀`
  — with corollaries `K_agree`, `bterm_agree`, `bsplit_agree`, `Jcell_agree` (∀ j :
  JIdx e), `iota_agree`, `Wcoef_agree` (∀ w : WIdx), `betaLeg_agree` (∀ leg, ∀ δ ∈
  depthSet — the per-pool coverage now provable BECAUSE entryList unions over
  depthSet, ruling (C)); `theorem RegP.det_ne_zero … (h : RegP S D) …`;
  `theorem RegP.R_defined {S D} (h : RegP S D) (σ) : DefinedAt (S.R σ) (p : ℚ)`
  (ruling (D)); `theorem RegData.pool_self_mem (D : RegData p) : p ∈ D.Pool`.
- **moves_ref**: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
  ENTRY LIST E(e) := { each entry of K_e } ∪ { each entry of b_e — BOTH components …
  per-cell J … } ∪ { each entry of ι_e } ∪ { each W_Ŝ coefficient } ∪ { each entry of
  every β_{e,τ} … }" (SQ.4's rev-3 schema, now covered in full)
- **sketch**: unfold `RegP` + `RegData.entryList` (Finset union membership per family).
  The API the MovesS instantiation consumes; no content beyond the schema.
- **hypothesis_fields**: explicit `RegP S D` only.

### U9 `MovesU.U9_lmeas` — (L-meas)'s retype: equivalence + IMPLIED-BY  [conditional on `rs4_eval` only]
- **file**: `MovesU/U9_lmeas.lean`  ·  **difficulty**: medium  ·  **deps**: U1, U4
- **statement** (two lemmas, fixed σ, N; `X : ClassifierSpec n p`,
  `R : SplittingType n → ℝ`; `1 < p` scaffolding as at U5):
  `theorem lmeas_equiv [NeZero p] (hp : 1 < p) (hsum : ∑ τ, R τ = 1) :`
  `((R σ - X.env N) * (p:ℝ)^(n*N) ≤ (X.decided σ N : ℝ)) ↔`
  `(∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ)` — and
  `theorem lmeas_implied (hupper : ∀ τ, τ ≠ σ → X.dmass τ N ≤ R τ) :`
  `∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ`
- **moves_ref**: "(L-meas) … by (BOX-N), for fixed σ this leg is EQUIVALENT to the
  AGGREGATE inequality Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p) … It is IMPLIED BY — not
  equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's checksum" (rev 2,
  pass-1 critical 5)
- **sketch**: `lmeas_equiv`: divide U1 by `p^{nN}` and rearrange (`Finset.add_sum_erase`,
  `hsum`); `lmeas_implied`: `Finset.sum_le_sum` — ONE direction only, faithfully: no
  converse is stated anywhere (per-τ violations can cancel; the note's honesty).
- **hypothesis_fields**: none as stated (`R : SplittingType n → ℝ` abstract, `hsum` explicit);
  at consumption `R := evalℝ`, `hsum := rs4_eval` — the gate-layer reading, recorded
  for SQUEEZE-n3's (L-meas) leg semantics only (the gate itself is NOT a Lean unit).

### U10 `MovesU.U10_theoremU` — THEOREM U, the ONE structure-carrying theorem  [capstone]
- **file**: `MovesU/U10_theoremU.lean`  ·  **difficulty**: medium  ·  **deps**: U6, U7
- **statement** (verbatim target; the campaign's statement-of-record):
```lean
/-- THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger, carried per prime by
    `UInstance`; SQ.4). "For each splitting type σ of degree n … there is ONE fixed
    rational function R_σ ∈ ℚ(q)" — the ∃ binds ONE family BEFORE the prime
    quantifier (F11); witness: S.R, so the fixed family is the solve's. At EVERY
    prime p satisfying (REG-p): ρ_σ(p) exists and equals the literal R_σ(p); the
    undecided complement has vanishing mass; the classifier verdicts ARE the true
    factorization types (F12). Σ_σ R_σ = 1 identically in ℚ(q). At a p failing
    (REG-p): NO CLAIM (D8). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (S : SolveData n)
    (M : MenuData) (K : KernelStatements)   -- p-UNIFORM (F3-C2/G4): one M, one K, ∀ p
    (inst : ∀ p : ℕ, p.Prime → UInstance n S M K p) :
    ∃ R : SplittingType n → RatFunc ℚ,
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP S (inst p hp).D →
        -- (i) the classifier-keyed density (the note's ρ_σ(p) = R_σ(p), T_can-keyed)
        (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii) the identification corollary (U11; via cl10_vpsound : VPSound X):
        --     the TRUE-type density is the same limit — "ρ_σ(p) IS the splitting
        --     density of type σ"
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.trueDmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (iii) the undecided complement has mass 0
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0)
```
- **moves_ref**: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
  prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and ρ_σ(p) IS the
  splitting density of type σ over ℤ_p — the undecided complement has mass 0 and the
  classifier verdicts are the true factorization types … Σ_σ R_σ = 1 identically in q
  (RS.4). … The quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
- **sketch**: witness `R := S.R`. Checksum: `(inst 2 Nat.prime_two).L.rs4_checksum`
  (p-independent, any prime's ledger). Per p: clause (i) = U7 with `r := evalℝ S σ p`,
  bracket from U6 fired on the ledger's PROJECTIONS `L.finStack`/`L.solveStack`/
  `L.lowerStack` (D12 — no re-packing; `hp` supplies `NeZero p`, `1 < p`); clause
  (ii) = U11 applied to clause (i) + `L.cl10_vpsound` + `L.cl4_env_tendsto`; clause
  (iii) = `L.cl4_env_tendsto`. The conclusion split is the note's own (D10, ruling (B)):
  (i) is what Theorem U literally concludes (T_can-keyed); (ii) is "ρ_σ(p) IS the
  splitting density" at the note's granularity, conditional on VP-SOUND exactly as
  the note's parenthetical "(X.3/CL-4 + [3t] VP, with VP-SOUND's citation duty)"
  says; the ℤ_p reading of `trueType` is HC-2's declared pin (D9). ≤ 25 lines.
- **hypothesis_fields**: the COMPLETE ledger — all cl-fields incl. the typed
  `cl10_vpsound`/`cl11`/`cl13`/`o3_teichmuller` + the operative fields — via
  `UInstance.L` at every prime, + explicit `RegP S` per adjudicated p. Nothing else.

### U11 `MovesU.U11_identification` — clause (ii): the true-type density  [derived; inputs explicit]
- **file**: `MovesU/U11_identification.lean`  ·  **difficulty**: medium  ·  **deps**: U7 (DefsLedger for `VPSound`)
- **statement** (the second squeeze; all inputs EXPLICIT arguments):
  `theorem identification (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)`
  `(r : ℝ) (σ : SplittingType n) (hvs : VPSound X)`
  `(hd : Tendsto (X.dmass σ) atTop (𝓝 r))`
  `(henv : Tendsto X.env atTop (𝓝 0)) :`
  `Tendsto (X.trueDmass σ) atTop (𝓝 r)`
- **moves_ref**: "and ρ_σ(p) IS the splitting density of type σ over ℤ_p — the
  undecided complement has mass 0 and the classifier verdicts are the true
  factorization types (X.3/CL-4 + [3t] VP, with VP-SOUND's citation duty)"
- **sketch**: sandwich `decided σ N ≤ trueCount σ N ≤ decided σ N + undec N`. Left:
  `hvs` injects {f // canonical = some σ} ⊆ {f // trueType = some σ}
  (`Nat.card_le_card_of_injective` on subtype inclusion). Right: a true-σ class is
  decided-σ or undecided — if `canonical N f = some τ` then `hvs` gives `trueType =
  some τ = some σ`, so `τ = σ` (`Option.some.inj`; trueType is single-valued);
  else `canonical N f = none` (undec). So {true-σ} ⊆ {decided-σ} ⊎ {undec}, card ≤.
  Divide by p^{nN}: `dmass ≤ trueDmass ≤ dmass + env`; squeeze
  (`tendsto_of_tendsto_of_tendsto_of_le_of_le`, upper leg `hd.add henv` + `add_zero`).
- **hypothesis_fields**: none as stated (`VPSound X` explicit — instantiated at U10
  from `cl10_vpsound`); the derivation itself is unconditional arithmetic + counting,
  NOT a fifth tag-free note-step (the note carries this clause inside Theorem U's
  conditional sentence, and it rides VP-SOUND/CL-4's tags at U10).

---

## 4. Semantic-guardian flags (the trust surface, for the Codex audit)

- **G1 `ClassifierSpec.trueType`/`canonical`**: the semantic pins (D9). Soundness is
  NOT baked in (REV 3): it is the typed ledger hypothesis `cl10_vpsound : VPSound X`.
  U10's clause (i) is NON-VACUOUS (a real limit of real counts over the concrete box)
  but remains SATISFIABLE by an unfaithful classifier — D9's declared boundary, not
  "degenerate-proof" (F3-G2); clause (ii)'s meaning rests on `trueType`/VP-SOUND
  fidelity — the HC-2/MovesD owner-audited pin. Say so in any progress claim.
- **G2 `evalℝ` junk values**: Mathlib `RatFunc.eval` returns 0 at poles. Audit that no
  unit consumes `evalℝ` outside a `RegP`-guarded context except as the LIMIT TARGET in
  U10, where `solve_stack`/`rs4_eval` (both RegP-guarded) give it content.
- **G3 `FiberSeries.thrSlice : Finset`**: finiteness-as-data = CL-7 riding the
  instantiation (D4); `mem_slice_iff` pins the slice to `thr`. Audit TRACK-COUNT +
  D(n) + genuine-increment stay named OPEN (`KernelStatements` slots + docstrings).
- **G4 the kernel slots**: every CL-1 … CL-19 item is an ASSERTED field (grep the
  `cl`-fields); vpSound/ksubM1C1 are typed (`cl10_vpsound : VPSound X`, `KsubM1C1 M`);
  cl13 asserts BOTH the reinstated full-statement `K.ctsmSyntax` slot AND the typed
  face `MenuWF M` (F3-C2 — audit that neither conjunct is dropped). `M`/`K` are
  p-UNIFORM theorem parameters (F3-G4). Remaining bare slots are `Prop` parameters —
  a `True`-filled slot is an instantiation-fidelity violation (D9), flag any instance
  unit that fills one.
  `solve_stack` MUST carry the explicit `0 ≤ evalℝ` conjunct (RS.3's clause, F8);
  the ledger MUST carry `o3_teichmuller` (gap 6) — check neither drops in
  elaboration.
- **G9 the slice discipline (REV 5)**: no unit below U10 may take `L :
  CapstoneLedger` — audit that U3/U4/U6 consume exactly `FinStack`/`SolveStack`/
  `LowerStack` per D12, that the three sub-bundles' fields stay LITERAL copies of the
  ledger's (the projections must be `⟨…⟩` re-bundlings, no strengthening or
  weakening), and that CL-2/CL-3 occur in no premise outside `CapstoneLedger`.
- **G8 the count data (`blockDim`/`cellCount`/`shapeCount`/`legCount`/`menuCount`)**:
  the cardinality equations pin the index families to these ℕ fields (ruling (C);
  menus via `menu_card` + `menu_not_all_empty`, F3-G1), but the VALUES are owner data
  (MovesS/[1v]/[2a] tables) — audit any instantiation against the sealed tables; a
  fabricated count is a fidelity violation, not satisfiable slack. REV 4 (F3-G3):
  J/W/leg counts carry NO positivity — owner-table confirmation of which blocks have
  zero branching cells/legs is OWED BEFORE E-PHASE if any positivity is ever wanted;
  `instBiNe`/`blockDim_pos` are the only positivity pins, audited safe.
- **G5 `RegData.act` abstract**: (r2)'s ACT agreement is against an UNINTERPRETED
  `act`; the CTS-M(ii) semantics arrive at instantiation. (REG-p) stays the rev-5
  SEPARATE hypothesis — audit that no unit derives RegP from, or uses it to derive,
  any E0/ACT-shaped statement (the `ctsmIiAct` slot is a DIFFERENT obligation).
- **G6 statement-fence**: U5/U7 take their tagged inputs as EXPLICIT arguments with
  `1 < p` as declared arithmetic scaffolding; audit that the note's displays are
  asserted ONLY through U4/U6/U10 at `p.Prime` + `RegP` (F9), and that U6/U10
  re-supply the tagged arguments ONLY from ledger fields + RegP.
- **G7 `entryList` as definition**: (r2)'s domain is the DEFINED seven-family union —
  audit no family is dropped and none is quietly narrowed at instantiation (the β-legs
  Finset must contain EVERY base-changed leg at EVERY pool, per the display).

## 5. Verified Mathlib inventory (names checked against the pinned mathlib, 2026-07-28)

- `tendsto_of_tendsto_of_tendsto_of_le_of_le`, `...'` — `Mathlib/Topology/Order/Basic.lean` (the squeeze, U7).
- `Filter.Tendsto.const_sub` — `to_additive` of `Filter.Tendsto.const_div'`,
  `Mathlib/Topology/Algebra/Group/Basic.lean` (U7's lower leg); `tendsto_const_nhds`, `sub_zero`.
- `ENNReal.summable` (every ℝ≥0∞ family), `ENNReal.tsum_eq_iSup_sum`,
  `ENNReal.sum_le_tsum` — `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` (U2).
- `ENNReal.toReal_le_toReal`, `ENNReal.toReal_mul`, `ENNReal.toReal_ofReal`,
  `ENNReal.summable_toReal` — same area (U4's transfer).
- `RatFunc.eval` — `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`; `RatFunc.denom`,
  `RatFunc.denom_ne_zero` — `RatFunc/Basic.lean` (D5, `DefinedAt`).
- `Finset.card_eq_sum_card_fiberwise` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (U1).
- `ZMod.card`, `Nat.card_eq_fintype_card`, `pow_mul` (U0); `Finset.add_sum_erase`/
  `Finset.sum_erase_add`, `Finset.sum_le_sum`, `div_mul_cancel₀` (U5/U9).
- `ZMod.castHom` + `pow_dvd_pow` (`boxProj`, D2); `Set.Finite.fintype`/classical
  finiteness for `SplittingType n` (U0b — E-phase may swap in a cleaner
  `Multiset`-bounded construction; the instance's EXISTENCE is not in doubt).
- `Polynomial.X`, `Polynomial.C` (`Box.toPoly`, ruling (A));
  `Nat.card_le_card_of_injective` (or `Set.ncard`/`Fintype.card_le_of_injective`
  route) + `Option.some.injEq` for U11's sandwich; `Filter.Tendsto.add` + `add_zero`
  for U11's upper leg; `Finset.biUnion` membership lemmas for `entryList`'s β
  coverage (U8's `betaLeg_agree`).
- E-phase check (flagged, not assumed): eval-additivity side-condition lemmas for
  deriving `rs4_eval` from `rs4_checksum` (`RatFunc.eval_add`'s hypotheses) — if absent
  or awkward, `rs4_eval` stays a field (already the blueprint default).

## 6. Status and counts (REV 6)

REV 5 delta: three Prop sub-bundles (`FinStack`/`SolveStack`/`LowerStack`) + three
projection defs in DefsLedger; U3/U4/U6 premises re-sliced per D12; CL-2/CL-3
confined to `CapstoneLedger` (U10). REV 6 delta: `cl10_vpsound` added to `FinStack`
(whole-CL-10 citation verified against the note; projection updated) — one field,
nothing else. Unit count, difficulties, tag-free perimeter, and everything below
unchanged from REV 4.

13 units (U0, U0b, U1–U11) over THREE Defs files (Defs ← U0b ← DefsLedger, D11):
4 TAG-FREE/unconditional (U1 (BOX-N), U2 Tonelli existence, U5 SQ.3-as-arithmetic,
U7 limit forcing — exactly the note's re-audited tag-free perimeter; U11 is derived
arithmetic with explicit inputs, NOT a fifth) + 2 support (U0, U0b) + 7
conditional/definitional/derived, every hypothesis a named structure field, typed
kernel field, kernel slot, or explicit `RegP S`. Difficulty: 5 easy, 8 medium,
0 hard. No new axiom; no `sorry` planned. The rev-3 Fable audit VERIFIED the spine
(Box/counts, U1–U11's statements, the RegP pins, the second squeeze, ∃R-∀p, the four
tag-free units); REV 4 repaired its menu-layer findings only. p-uniform layer:
S, M, K bound before ∀ p. Instantiation hooks per D9: `ClassifierSpec`/`FiberSeries`
← MovesD/HC-2/[3t], `SolveData`/`RegData` ← MovesS, `MenuData` ← [2a]/[1v],
`KernelStatements` ← owner notes. OWED BEFORE E-PHASE (F3-G3): owner-table
confirmation on zero-cell/zero-shape blocks (G8). Next gate: the in-flight fresh-Fable
confirm on rev 4 (its findings fold into this rev if any) + Codex re-verdict on REV 5;
charge = §4's flags + the 29-finding disposition table (§7).

## 7. Findings→repairs table (Codex audit 2026-07-28, REJECT 10c/3g → REV 2)

| # | class | finding (short) | repair in REV 2 |
|---|---|---|---|
| 1 | crit | `Census` = arbitrary labeling, not the classifier | REDESIGNED: `ClassifierSpec` with `trueType`/`canonical`/`canonical_sound`/`canonical_stable` (D2, D9); decided/undec DEFINED from it |
| 2 | crit | `FiberSeries` empty/unrelated tree families | FIXED: `thr` + `mem_slice_iff` + `slice_exhausts`; tie = `finiteness_stack` identity (D4) |
| 3 | crit | U3 weakened "is the partial sum" to ≤ | FIXED: U3 states the exact identity; domination is the named corollary |
| 4 | crit | (REG-p) vacuous; entry list = K only | FIXED: `pool_eq` (Q(p) = depth image, ∋ p), `Nonempty Block`, all seven entry families, `entryList` a DEFINED union (D5) |
| 5 | gap | kernels are docstrings, not fields | FIXED: `KernelStatements` pack + per-CL `cl1`…`cl19` assertion fields (D7) |
| 6 | gap | CL-2/CL-3 omitted | FIXED: `weightCharge`/`progressX2` slots + `cl2`/`cl3` fields |
| 7 | gap | menus, m = 1, (BDY) absent | FIXED: `ksubM1C1` + `ctsmSyntax` slots carry them, named (D7) |
| 8 | crit | U4 positivity underivable from `ofReal` | FIXED: `solve_stack` gains explicit `0 ≤ evalℝ` (RS.3's clause, stated by the note) |
| 9 | crit | U4/U6 asserted at composite p > 1 | FIXED: `p.Prime` at U4/U6/U10; `1 < p` survives only as declared scaffolding in tag-free arithmetic units (U5/U7/U9, G6) |
| 10 | crit | U8 exposes only K-entries | FIXED: generic `entry_agree` + seven per-family corollaries + `pool_self_mem` |
| 11 | crit | U10: arbitrary σTy, no ∃-R, hn inert | FIXED: concrete `SplittingType n` (Σ eᵢfᵢ = n as data, U0b Fintype); conclusion `∃ R …` binding ONE fixed family before ∀ p |
| 12 | crit | U10 drops the density-identification clause | FIXED: conjuncts env → 0 + verdict-truth (`canonical_sound`) added; interface-strength caveat at G1 |
| 13 | crit | capstone satisfiable by fake instance | REDESIGNED: D9's non-vacuity boundary — pinned interfaces (soundness/stability, nonempty pools/blocks, defined entry list, concrete types); residual pin = `trueType`/kernel-slot fidelity, declared owner-audited (MovesC precedent) |

**Rev-2 re-audit (REJECT 4c/3g → REV 3, per the orchestrator ruling (A)–(E)):**

| # | class | finding (short) | repair in REV 3 |
|---|---|---|---|
| R2-1 | crit | U10 still satisfiable by degenerate instance (constant verdict + trueType, True slots) | REDESIGNED per ruling (A)/(B): concrete polynomial space (`Box.toPoly`, real counts) makes clause (i) NON-VACUOUS — still satisfiable by an unfaithful instance, per D9's declared boundary (wording corrected at REV 4, F3-G2); clause (ii)'s residue moves into typed `VPSound X` fidelity, DECLARED owner-audited |
| R2-2 | crit | no identification with the actual ℤ_p splitting density | REDESIGNED per ruling (B): conclusion splits — clause (ii) `trueDmass σ → R_σ(p)` via new unit U11 (second squeeze: decided ≤ trueCount ≤ decided + undec under VP-SOUND); ℤ_p-Haar reading = HC-2's declared bridge, not re-derived |
| R2-3 | crit | (REG-p) families could be empty (empty `bidx` ⟹ det = 1; free Finsets) | FIXED per ruling (C): every family index-typed with cardinality EQUATIONS pinned to count data (`bidx_card`/`JIdx_card`/`WIdx_card`/`legIdx_card`), `instBiNe` + `blockDim_pos` (the only positivity pins — REV 4/F3-G2 correction: no `legCount_pos` exists, and REV 4 dropped `cellCount_pos`/`shapeCount_pos` per F3-G3); β entries functions of (leg, δ) with `entryList` unioning over EVERY δ ∈ depthSet |
| R2-4 | crit | literal R_σ(p) never asserted DEFINED | FIXED per ruling (D): `RegP S D` gains `∀ σ, DefinedAt (S.R σ) p`; accessor `RegP.R_defined` (U8); U4/U10 consume `evalℝ` only under it |
| R2-5 | gap | ksubM1C1/ctsmSyntax/vpSound bare Prop slots | FIXED per ruling (E): slots DELETED; `MenuData` (menus as Finsets of (m, c, sameSize, target)) with `KsubM1C1 M` and `MenuWF M` as real Props (cl11/cl13); `cl10_vpsound : VPSound X` typed over the concrete box |
| R2-6 | gap | O3 Teichmüller pin absent | FIXED: `BaseSection` enum + `ClassifierSpec.baseSection` field + ledger field `o3_teichmuller : X.baseSection = .teichmuller` |
| R2-7 | gap | Defs circularity (Fintype before U0b); missing `DecidableEq (Tree σ)` | FIXED per ruling (E)/D11: three-file order Defs ← U0b ← DefsLedger (the `∑ σ` fields live in DefsLedger); `instTreeDeq` field added to `FiberSeries` |

**Rev-3 Fable audit (REJECT 2c/4g, spine verified → REV 4, surgical):**

| # | class | finding (short) | repair in REV 4 |
|---|---|---|---|
| F3-C1 | crit | `KsubM1C1` bound same-size HALTS (c = 0, the b_e^{term,fin} leaves) — stronger than the note's continuation-only clause; faithful catalogue would falsify it | FIXED: `o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1` — same-size continuations only, halts exempt |
| F3-C2 | crit | `cl13 : MenuWF M` strictly weaker than CL-13 (cell predicates absent, target-totality mislabeled as global compatibility, p-independence inexpressible with per-prime M); full-statement slot deleted = dropped open tag | FIXED: `ctsmSyntax : Prop` slot REINSTATED (full CTS-M(i) content in its docstring); `cl13 : K.ctsmSyntax ∧ MenuWF M`; `MenuWF`'s docstring relabeled (per-entry target totality, honestly); `M` moved to the p-uniform layer so "the ONE fixed p-independent state set" is expressible |
| F3-G1 | gap | all-empty menus satisfy both typed faces vacuously | FIXED: `menuCount` catalogue data + `menu_card` equations + `menu_not_all_empty` (single-state empty menu = halt convention, still allowed) |
| F3-G2 | gap | §7 misstatements: "all `_pos`" (no `legCount_pos` exists), "degenerate-proof" shorthand | FIXED: R2-1/R2-3 rows corrected in place; G1 flag reworded (non-vacuous ≠ degenerate-proof) |
| F3-G3 | gap | `cellCount_pos`/`shapeCount_pos` note-unsupported — (K-TRI) minimal blocks may have zero branching cells/shapes; truthful-instantiability risk | FIXED: both DROPPED; equation pins stay; owner-table confirmation owed before E-phase recorded at G8; `instBiNe`/`blockDim_pos` kept (audited safe) |
| F3-G4 | gap | `KernelStatements` per-prime though referents are p-uniform | FIXED: `K` (with `M`) moved out of `UInstance` to `theoremU` parameters before ∀ p — one pack, audited once |

**Rev-4 Codex FINAL (REJECT 3c/0g, all over-hypothesization → REV 5, surgical):**

| # | class | finding (short) | repair in REV 5 |
|---|---|---|---|
| CF-1 | crit | U3 takes the full `CapstoneLedger` — assumes every field (CL-1–19, VP-SOUND, O3, RS.4, env → 0) where the display cites only the finiteness stack | FIXED: `FinStack` sub-bundle (CL-7 + CL-10 slots + the TREE-N identity); U3's premise is exactly it (D12) |
| CF-2 | crit | U4 likewise — SQ.2's upper display cites the finiteness + solve stacks only, not CL-2/CL-3/CL-4, RS.4, VP-SOUND, O3 | FIXED: `SolveStack` sub-bundle (the (U-n) upper citation list CL-1/5/6/8/9/11/13–16/17/18/19 + the operative identification); U4 = FinStack + SolveStack + RegP + p.Prime |
| CF-3 | crit | U6 requires CL-2/CL-3 (rate-form-only per the note) and other capstone-only fields for the non-rate bracket | FIXED: U6 = FinStack + SolveStack + `LowerStack` (RS.4's inherited set, CL-4 included); CL-2/CL-3 in NO unit premise — the rate form is gate SQUEEZE-n3, not a Lean unit, so no U6b; `CapstoneLedger` (with CL-2/CL-3) remains U10's full consumption with projection defs `finStack`/`solveStack`/`lowerStack` |

**Rev-5 Codex FINAL#2 (REJECT 3c/0g, one root cause → REV 6, one field):**

| # | class | finding (short) | repair in REV 6 |
|---|---|---|---|
| CF2-1..3 | crit | `FinStack` omitted `cl10_vpsound : VPSound X` — U3/U4/U6's premises one field THINNER than the note's CL-10 citation | FIXED: `cl10_vpsound` added to `FinStack`; projection updated to `⟨L.cl7, L.cl10, L.cl10_vpsound, L.finiteness_stack⟩`. VERIFIED the citation is WHOLE-CL-10: the (U-n) display reads "the UPPER side GIVEN the finiteness stack {SQ.0's budgets with TRACK-COUNT + D(n) + the genuine-increment sub-claim (CL-7); the [3t] package (CL-10)}" (MOVES 13140–13143) — no display cites a VP-SOUND-free half: CL-10's entry itself ends "and VP-SOUND (a citation obligation …)" (13281–13284) and SQ.1 rules "CL-10's tags ride every consumption" (13033). So the field belongs in FinStack, not in a finer split |

