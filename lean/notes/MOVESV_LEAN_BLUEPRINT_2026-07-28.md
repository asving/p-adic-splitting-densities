# MOVESV LEAN BLUEPRINT — REV 3 (wave 4)

*(2026-07-28, Fable blueprint writer. GROUND TRUTH: the frozen dual-accepted
§V-TABLES text, `lean/notes/MOVES_2026-07-24.md` lines 7829–9054 (rev 7 —
Codex passes 6+7 + Fable pass, all CLEAN on identical text; V-n3 gate PASSED
178/178). A Lean statement below is faithful iff it says what that text's
display says. Campaign doctrine per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`
§2/§3 + the wave-2 ledger doctrine: "a faithful interface must be FALSE for
instances the note would reject; obligations may be open, but their TYPES must
pin their content".)*

**REVISION RECORD.** REV 1 was REJECTED by both round-1 auditors on identical
text: Codex 23 crit / 6 gap (`MOVESV_AUDIT_CODEX_2026-07-28.md`, findings C1–C29)
and Fable fresh-instance 2 crit / 5 gap (`MOVESV_AUDIT_FABLE_2026-07-28.md`,
findings A-1–A-7). REV 2 repairs the UNION; the full disposition table is §6.
The five structural repairs, named once here:
1. **The A2 arithmetic catch (C3, verified first):** `(3(h₀+h₂)−1)/2` has
   half-integral coefficients in (h₀,h₂), so it cannot inhabit the
   natural-coefficient `AffineE`. REPAIR: note-faithful reparameterization —
   `A2dom` and `EA2` are now DECLARED in the (t,u) chart where the coefficients
   ARE natural (E = 6t+3u+1 — OUR derived chart form; the note displays
   E = (3(h₀+h₂)−1)/2 plus the substitution h₂ = t ≥ 1, h₀ = 3t+2u+1, and the
   string "6t+3u+1" appears nowhere in it — attribution corrected at REV 3,
   G-1), and the coordinate change `A2chart` is a DEFINITION;
   V0-4/V6-2a/V6-2b re-keyed (§2.I, §3).
2. **The doctrine core (C1, C2):** `StepSys` gains non-vacuity laws (`cell_ne`,
   `out_ne`, `zc_ne`) where the note realizes them; `cntraw` is now a DEF
   (`Fintype.card (Assign …)` — tied to Assign cardinality BY DEFINITION);
   the chain count is the DEF `chainCount` (the note's T_γ definition encoded
   as the recursion through the new history-extension field `StepSys.ext`),
   so XHDd's exactness laws quantify over the real count, and the cell-event
   tie rides `CtsMeasured.evtOf` (§2.B, §2.F, §2.G).
3. **The wiring core (A-1, A-2, C7, C24):** the entrance-side carrier is now
   TEMPLATE×COMPONENT-keyed (`EntIx`, finite; `ιDom = the listed component`;
   `ιshH` the per-instantiation mass; per-component PolyGeoms exposed), which
   is the granularity `MovesS.MeasuredSide`/`RatBurdens.ιP` actually types;
   `StepSys.ext` is the history-extension carrier the chain recursion needs.
4. **The J/measured retyping (C8, C23, C24):** digit cells are OUTCOME-keyed
   (`DCellO`), so J tables exist per (τ, o) including split outcomes; the
   measured ℝ-fields (gwt/μcell/rowVal/kstep/ιshH/ιsh/ιval) are no longer free
   data — V7-4 DEFINES them from the typed XHD package over the counting
   carriers, which is exactly the tie set C24 demanded.
5. **Census upgraded (C20, A-4):** DefsGate gains explicit table-based finite
   fields `F4/F8/F9`, so V6-1c/V6-3b now decide the census at ALL NINE sealed
   prime-power points in-kernel; the multiplicity sketch is re-keyed to
   char-free divisibility (no f″ — the p = 2 trap is out).

**REVISION RECORD — REV 3.** REV 2 was REJECTED by both round-2 auditors:
Codex 16 crit / 4 gap (`MOVESV_AUDIT_CODEX2_2026-07-28.md`, findings 1–20) and
Fable fresh-instance 6 crit / 4 gap (`MOVESV_AUDIT_FABLE2_2026-07-28.md`,
F-1–F-6, G-1–G-4). The A2 chart, the doctrine core, the EntIx carrier itself,
the V6 gate layer, and the unit DAG outside the measured-wiring region were
VERIFIED CLEAN by both passes and are UNTOUCHED here. REV 3 repairs the union;
the round-2 disposition table is §6.2. The five structural repairs:
1. **THE MEASURED-WIRING CLUSTER (F-1..F-6; Codex 7–11, 16):** the INSTANCE
   CENSUS is now a carrier distinct from the box events — `CtsMeasured.entInst`
   (D4R.4's marked-prefix census, box-realized at the defining level) with the
   TYPED counting law `ent_card` (card(entEvt at N)·q^A = census·q^{nN});
   `ιshH` := census·q^{−A} (the F-1 slip is out — gate B: card at N = 3 is
   128 and ιshH·|Box(3)| = (1/4)·512 = 128, never 8192); `entCount` := the
   census (the ent-degree ledger is jointly satisfiable: gate degree 2 ≤
   Went = 3); `XHDsC`/`XHDsEnt` re-keyed WEIGHT-ONLY (the [2b] height-sum
   faces proper — counts enter only through the typed [1v] burdens
   CellPolyPack/ENT-COUNT, so INIT-RAT/(J-RAT) are never decided by a
   hypothesis field and nothing double-counts); `cell_refine` is a DERIVED
   UNIT (V5-8) with the count factor DISPLAYED (Σ_c P_c·ΣGcell = T·ΣGc —
   the (q−1)² adversary dies); `kstep` carries its ∏T path-product factor;
   `cellP` REVERTED to the rev-1 sizeP wiring (state-census fields
   stLvl/stInst/stInst_card added — the frozen cellP_deg bound and the m_H3
   q = 2 falsifier both pass again); J re-keyed to the ROUTE classification
   (ALL cells of a split-route outcome, EACH ONCE — the gate Jval is nonzero).
2. **THE COUNTING-TIE TYPES (F-3; Codex 10):** `evt_card` (per-assignment
   card = mass·|Box| eventually), `box_card` (|Box(N)| = q^{nN}), ONE
   heterogeneous disjointness law over the assignment-step Σ-carrier `AStep`
   (cross-move, cross-height, cross-assignment, terminal included), and the
   cell d-face `XHDdC` (cdom exact against cntc) — the
   meas_card/no_stray/no_orphan/d4r0 suite is now derivable field-by-field.
3. **THE STEPSYS/TERMINAL CORE (Codex 1, 2):** `out_ne` re-keyed to
   realized-history PRODUCTIVITY (empty syntactic menus are allowed, as the
   note demands; a globally unrealized model now violates the law at the
   zc_ne witness); TERMINAL-FINAL TWINS typed throughout (XHDu, C15Pack,
   CtsMeasured, XHDsC/XHDdC, CellPolyPack, Refinement) via the displayed
   substitution table.
4. **FORCING + CLOSED DISPLAYS (Codex 3–6, 12–18, 20; G-2, G-3):** the rel
   generator's partition FACTORS THROUGH its polynomial by type; `moveOf`'s
   target is ENFORCED by `tcell` BY TYPE; `ValA.tbl_count` base-point-keyed
   (says something at zero counts, smuggles no height-uniformity) +
   `ent_supported` (V4-1's missing premise); σ_sel pinned as the L11
   `selRank` data (E8_rankInj semantics); the V3-3(d) reconstruction bridge +
   the u*-slot zigzag/gamTie encoding (G-3); `XHDdEnt.lands_of_realizable`;
   V2-7's three cells corrected (nonzero coordinates); `Refinement` fully
   typed (`assign_cover`); V4-12 RESTORED to the note's IF AND ONLY IF at the
   ∀-weight-system quantifier (both directions now stated, the ⟸ leg proved,
   the ⟹ leg the generating-series separation — HARD); every named
   placeholder displayed closed (CoprimeLiftPack, CtsmConclusions,
   writeHeights, MoveData/TermData/dataOf, emult, F4/F8/F9 with the Conway
   claim corrected, Hpt.take/drop); `Wsh17PackageV` displayed AS A TYPE +
   seam flag SF-2; the general SCSData/KmatHyp supply typed
   (`StageLawBurden`, a CtsmLedger field).
5. **ONE-DISPLAY SPLITS + ATTRIBUTIONS (Codex 19; G-1, G-4):** V1-8, V7-2,
   V7-3, V7-4, V7-6 split into one-display units (census now 82 = 33/43/6);
   the two E = 6t+3u+1 attributions corrected (our derived chart form — the
   note never displays that string); V3-6(c) re-pointed to the EXPORTED
   `D4R1_SUM`/`D0b_thmCtop`.

## §0 Charge, status, and the conditionality banner

**WHAT THIS CORPUS IS.** §V-TABLES = assembly note [1v]-COND: ONE fixed
p-independent state space of syntactic branch-cells (V.2), one polynomial table
family T counting per-cell fresh-assignment transitions (V.2), and ONE measured
theorem — CTS-M (V.1) — typing how counts (T), fixed-height weights (g),
resummed weights (G), entrance masses (ι), and marked masses (μ̂) compose,
EACH CLAUSE GIVEN EXACTLY its V.1-ledger hypothesis set. Every left-hand side
is a MARKED-BRANCH mass μ̂ (μ̂(E) := Σ_η μ({f : (f,η) ∈ E}) — a sum over marks
BY DEFINITION), never an f-event mass and never a density.

**THE CONDITIONALITY BANNER (binding on every unit and on the corpus record).**
- XHD (XHD-w/-d/-s) + (XHD-u) + (ENT-U): OPEN, owner [2b] §H-DOMAINS (its six
  H.6 fences block [1v]-FULL). In Lean they are the §2.B/§2.G typed hypothesis
  structures; NO unit proves them; the discharge is the separate recorded
  event [1v]-FULL (V1-5's `IsFullDischarge` — bookkeeping, no mathematics).
- (v) HMC: OPEN KERNEL (probe specced-and-pinned at V.4, RUN status per the
  note: NOT run at freeze). Typed at §2.G; (HMC-AUG) a SEPARATE named Prop
  (body now DISPLAYED, §2.G).
- ENT-COUNT, (ENT-U), INIT-RAT: named burdens of clause (iii) — statements
  typed, INIT-RAT a theorem-under-hypotheses unit (V3-9c).
- (J-RAT)/CL-18: owner [1v] (with [2b] on the height-sum face) — THE PLAN-SYNC
  deliverable this corpus records on the owner side: the per-cell tables
  J_{τ,o} ∈ ℚ(q) ENTRYWISE, beyond PART-1's total (layer V5, units V5-7*).
- (ii-c) ACTIVE-VALUE: a finite per-(n, q₀) check (MovesS's AVAgree shape),
  recorded, never a blanket det ≠ 0 claim.
- Inherited: §C (via MovesC/HC-2 — the C.1.5(1)/TYP(b) faces ride as the typed
  `C15Pack`, owner tag §C/HC-2), §D4-R (MovesD — PROVED core consumed),
  [2a] §M-SPECIES (MovesSp — PROVED, so the note's "[2a] pending" inheritance
  is DISCHARGED against the Lean corpus at n = 3; recorded as an upgrade,
  not a deviation: the note's conditionality only shrinks).
- ESCAPE(E0): [3]'s duty (MovesS.EscapeE0); cited only inside (vi)'s
  conditional solve sentence, never claimed here.
- [3t] fence: VP, TB-CAP, TREE-EXP/ONE-F, tree pruning are NOT in this corpus;
  terminal outcome labels are consumed as ABSORBING COLUMN LABELS only
  (`VLabel`, §2.A). Equating any μ̂ object of this corpus with an f-event mass
  is a TYPE ERROR except through [3t]'s displayed conversion (MovesT, wave 4).

**WHAT IS PROVED OUTRIGHT HERE (no hypothesis fields)** — SCOPED PER UNIT
(A-6 repair; the banner sentence carries the same scope its units do): (U-A)
as the note proves it (V1-6, GIVEN only the typed §C-supply pack — the note's
own GIVEN); the clause-(i) meet lemma (V2-3); the entrance-template
finiteness (V3-4, now intrinsic — see C12); ENT-AGG's finite half (V3-7);
(ii-a)/(ii-b) given ValA's count semantics (V4-1/2); PART-2's n = 3 surplus
≡ 0 over the gate rosters + the general lemma GIVEN the displayed
continuing-size-≥-2 premise (V4-8); the (v)-naming EQUIVALENCE at the
displayed ∀-weight-system quantifier — HMC ⟺ the factorization identity for
EVERY positive-affine monomial weight system (V4-12, both directions of the
note's IF AND ONLY IF, GIVEN only the XHDd data argument; the single-system
failure witness rides as its non-vacuity fence); and the V.6 gate layer
**EXCEPT V6-4c** (V6-1a..V6-4b:
closed forms, PART-1 count faces, DEG-CONS rosters, domain normal form, the
gate-B dyadic arithmetic and two-history discipline; the census units V6-1c/
V6-3b at all nine sealed prime-power points via `F4/F8/F9`) — decide/ring/
norm_num-native. V6-4c is NOT in this list: its threshold derivation carries
the typed `hensel : CoprimeLiftPack` premise (fields displayed at §2.I).

## §1 Consumption map (all PROVED corpora; owner tags for open vocabulary)

| consumed | what | where used |
|---|---|---|
| `MovesSp` (PROVED, dual-accepted rev 5) | `Species` (SP.1 datum, heights forgotten BY TYPE), `InCatalogue`/`SnRaw`, `Succ`/`Out`/`SuccStep` (SP-OUT syntactic menus, NO field evaluated), `Verdict` (bare labels), `EntranceShape` (the species-word entrance carrier with height SLOTS — now the V3-3 bridge TARGET), `CollapsedWalk`/`collapseRuns` + the `rankNat` DAG idiom (SP4_dagWords), SP2 finiteness (`SP2_finThm`), the 53-catalogue + SP6 menu roster (kernel-decided) | §2.C skeletons + (D1) menus; V2-1; the (iii) template layer §2.D/V3-3/V3-4 (EntTemplate's WF fields mirror `EntranceShape.hMem/hChain/hEntry` — the A-3 tie); V4-8's roster; clause (i)'s [2a] discharge |
| `MovesD` (PROVED core, rev 9 seam split) | `Shape n`/`ShapePrefix`/`ShapeRead` (L3 rev 9: retains per-read (h, u*) — fields `h`, `ustar`; per-read `(g, μ)` — fields `g`, `μ`), `Presented`/`PrefIdx`/`Presented.fiber`/`mult`, `Box`, `D4R1_SUM` (D10), `D0b_thmCtop`, `mult_sum` (D11a), `D4R4_all`, `ShapePrefix.A`/`A'`/`W`, `ShapeRead.len`/`.mbar`, the L5/L11 eligibility apparatus BY NAME: `EligibleImage`, `selRank` (L11's s_r), `eligible_card_le` (E6), `E5_gmuLe`, `E8_rankInj`/`E9_encInj`, `ShapePrefix.gamTie` (the u*-determinacy law) | §2.D entrance shapes ε (P̂ concrete WITH heights; entry-read/eligibility WF ties); ι's counting-native def; A(ε) = A(P̂), W_ent(ε) = W(P̂); the marked-event census V5-1 |
| `MovesS` core (E-phase built) | `Qq`, `PolyGeom`, `OKat`/`evalAt`, `MuHat`, `TableShape`, `MeasuredSide`, `RatBurdens`, `LedgerIV`, `DegCons`, `KmatHyp`, `SCSData`, `EscapeE0`, `AVAgree` | §4 SEAM-SUPPLY: layer V7 instantiates; §2 reuses the ℚ(q) plumbing verbatim (NO re-derivation) |
| `MovesC` (PROVED) — owner tag §C/HC-2 | Theorem C(b) engine; C.1.5(1)/TYP(b) have NO standalone Lean form yet | the `C15Pack` typed supply for (U-A) (§2.B); each field cites its §C display; discharge = HC-2 territory |
| owner [2b] §H-DOMAINS | XHD-w/-u/-d/-s (incl. the cell and shallow/entrance faces), (ENT-U), (JC-INV) | typed hypothesis structures §2.B/§2.G; NEVER proved here |
| owner [3t] → MovesT | VP/TB-CAP/TREE-EXP/ONE-F/(SIB) | absent; absorbing labels only (`VLabel`) |
| owner [3] MovesS | ESCAPE(E0), the solve | cited in (vi)'s solve sentence via `MovesS.EscapeE0`/`DetHyp` |

Ownership fence, restated binding: this corpus does NOT own and nowhere
re-derives VP, TB-CAP, TREE-EXP/ONE-F (the SOLE marked→per-f conversion), the
nine-input ledger's probabilistic reading (CL-5, [3] RS.PRE), or exhaustion
([5]). K_e's construction as a MATRIX is MovesS's (`Kmat`); this corpus
supplies its ENTRY tables and their laws.

DAG position: MovesV consumes MovesSp + MovesD + MovesS-core (+ MovesC via the
typed pack); it is consumed by MovesS's wave-4 seam (§W4-SYNC) and MovesT.
Import direction `MovesV → MovesS.Defs/Interfaces` is ACYCLIC: MovesS's core
never imports MovesV (its intended-instance comments become real here).

## §2 The Defs layer — `MovesV/Defs.lean` (+ `DefsGate.lean` for V.6 data)

Declaration order below is normative AND Lean-plausible (C4 repair: `VLabel`
precedes `StepSys`; the `XHD` bundle follows XHDd/XHDs in §2.G; no invalid sum
types remain). Defs are sorry-free; every law with content is a UNIT, not a
Defs field, EXCEPT hypothesis-package fields (obligations by design, per the
doctrine) and the displayed data-tie fields marked [tie]. `open LeanUrat.MovesS
(Qq PolyGeom OKat evalAt MuHat)` — the ℚ(q) plumbing is reused, never rebuilt.
NO placeholder survives this revision: §2.J is the checklist (C29 repair).

### 2.A The height apparatus (V.0's ambient objects, "defined here so the package is CLOSED and refutable")

```lean
namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq PolyGeom OKat evalAt MuHat)

/-- A height point in D ℕ-slots (V.0: "the tuple of its reads' ℕ-height
parameters (the parameters [2a] SP.1 forgets; d_i height slots at step i)"). -/
abbrev Hpt (D : ℕ) := Fin D → ℕ

/-- concatenation of height points (used by templates and HMC). -/
def Hpt.append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) : Hpt (D₁ + D₂) :=
  Fin.append h₁ h₂

/-- the Fin-append splitters (Codex-18: displayed, closed — no longer a
"defs in the E-phase file" pointer). -/
def Hpt.take {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₁ :=
  fun i => h (Fin.castAdd D₂ i)
def Hpt.drop {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₂ :=
  fun j => h (Fin.natAdd D₁ j)

/-- prime-power evaluation points (was dangling in rev 1 — A-7 repair). -/
def IsPP (q₀ : ℚ) : Prop := ∃ (p k : ℕ), p.Prime ∧ 0 < k ∧ q₀ = (p : ℚ) ^ k

/-- (XHD-w)'s exponent: "E affine in h with positive weights". The weights are
DATA with a typed positivity law — a weight-0 (h-degenerate) instance is
UNSATISFIABLE, per the wave-2 doctrine. CHART CONVENTION (C3 repair, binding):
every `AffineE` of this corpus is declared IN COORDINATES WHERE ITS
COEFFICIENTS ARE NATURAL; where the note displays an exponent in other
coordinates (the A2 (h₀,h₂) display), the coordinate change is a DEFINITION
(`A2chart`, §2.I) and the display is re-derived THROUGH it (V6-2b) —
division-free, note-faithful. -/
structure AffineE (D : ℕ) where
  const : ℕ
  coeff : Fin D → ℕ
  pos   : ∀ i, 1 ≤ coeff i

def AffineE.eval {D : ℕ} (E : AffineE D) (h : Hpt D) : ℕ :=
  E.const + ∑ i, E.coeff i * h i

/-- V.0: "a LINEAR SET in ℕ^D is L(h₀; P) := {h₀ + Σ_{v∈P} n_v·v : n_v ∈ ℕ}
with base h₀ ∈ ℕ^D and a FINITE period list P" — bases and periods EXPLICITLY
LISTED (the "congruence-class translates" gloss is struck). -/
structure LinSet (D : ℕ) where
  base    : Hpt D
  periods : List (Hpt D)

def LinSet.Mem {D : ℕ} (L : LinSet D) (h : Hpt D) : Prop :=
  ∃ c : Fin L.periods.length → ℕ,
    h = fun i => L.base i + ∑ j, c j * (L.periods.get j) i

/-- THE DISJOINT-COMPONENT CONVENTION (rev 3, pass-2 finding 1), AS A TYPE:
every semilinear domain this corpus consumes is a LISTED PARTITION — the
listed linear sets pairwise disjoint. Overlapping lists are UNSATISFIABLE. -/
structure SemilinPart (D : ℕ) where
  comps : List (LinSet D)
  disj  : comps.Pairwise (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h))

def SemilinPart.Mem {D : ℕ} (S : SemilinPart D) (h : Hpt D) : Prop :=
  ∃ L ∈ S.comps, L.Mem h

/-- Absorbing column labels: (e, f) with e·f ≤ n — verdict SEMANTICS is [3t]
VP's, "consumed here only as absorbing column labels"; this carrier is also
MovesS's R20 pin verbatim (TableShape.vEquiv will be `Equiv.refl`-keyed).
Declared HERE so `StepSys.MoveT` can reference it (C4 declaration-order fix). -/
abbrev VLabel (n : ℕ) := {ef : ℕ+ × ℕ+ // (ef.1 : ℕ) * (ef.2 : ℕ) ≤ n}
```

### 2.B The step system, the (U-A) supply pack, and the first two XHD faces (V.0; owner tags per package)

XHD is stated over the STEP SYSTEM `StepSys` (§2.C defines its intended
instance; the structures are parameterized so [2b]'s eventual discharge
re-keys once). The RAW primitives are HISTORY-INDEXED — without that, (u-R)
and (U-A) would be contentless (the pass-1/2 lumpability findings). REV-2
CHANGES (C1/C2/A-2/A-5 repairs), REV-3 AMENDMENTS (Codex-1/2: `out_ne`
re-keyed to productivity; terminal twins throughout): non-vacuity laws
`cell_ne`/`out_ne`/`zc_ne` typed in; the history-extension operation `ext`
added (the carrier the chain
recursion requires — the normative-Defs amendment A-2 named); `cntraw` is now
a DEF, tied to `Assign` cardinality by definition; the rev-1 `inv` stub is
DELETED (design-freedom slot (1) resolved: `C15Pack` already carries the
pinned inventory carrier — nothing in the note demands a slot on `StepSys`).

```lean
/-- The index vocabulary + measured primitives XHD quantifies over (V.0:
"for every step datum (m, o) with source cell α and target cell β, and every
height point h"). `Hist α` = admissible histories/representatives reaching a
concrete state of α (x AND its history — (u-R)'s quantifier); `Assign` = the
fresh-assignment fiber realizing (m, o, β) at h from x; `massOf` = the
per-assignment C.1.5 conditional mass carrier; `ext` = history extension by
one realized assignment (V.0's chain vocabulary: "fresh-assignment CHAINS
from x" — a chain IS iterated extension). NON-VACUITY (C1, re-keyed at REV 3
per Codex-1): the note's 𝒞_n is nonempty (the root skeleton); every cell has
a (ZC)-realizable history (post-deletion cells are realized states — V.2's
deletion convention); and every (ZC) history is PRODUCTIVE (PART-1's mass 1
forces a realized continuing or terminal fresh assignment — `out_ne` below,
AFTER the Assign fields it constrains). The empty model violates `cell_ne`;
the all-empty-fibers model violates `out_ne`.
TERMINAL TWIN CONVENTION (REV 3, Codex-2): every per-move law of §2.B–§2.H
has a terminal-final twin under the SUBSTITUTION TABLE
  Move ↦ MoveT · dim ↦ dimT · Assign ↦ AssignT · finA ↦ finAT ·
  cntraw ↦ cntrawT · massOf ↦ massOfT · moveOf ↦ moveOfT · dataOf ↦ dataOfT ·
  evtOf ↦ evtOfT · stabLvl ↦ stabLvlT · cellOfA ↦ cellOfAT · cdom ↦ cdomT ·
  cntc ↦ cntcT · Gcell ↦ GcellT (targets: the absorbing label v, no ext, no
  target cell) —
twins are DISPLAYED fields (suffix T), written out in full where short and
marked [+T] where the substitution is verbatim. -/
structure StepSys (n : ℕ) where
  Cell  : Type                        -- 𝒞_n, symbolic, p-independent BY TYPE
  finC  : Fintype Cell
  cell_ne : Nonempty Cell                              -- [C1 non-vacuity]
  Move  : Cell → Cell → Type          -- continuing step data (m, o) : α → β
  MoveT : Cell → VLabel n → Type      -- terminal-final step data (rev-4 exit
  finM  : ∀ α β, Fintype (Move α β)   --   objects; β_k := absorbing label)
  finMT : ∀ α v, Fintype (MoveT α v)
  dim   : ∀ {α β}, Move α β → ℕ       -- the step's height-slot count d_i
  dimT  : ∀ {α v}, MoveT α v → ℕ
  Pools : Set ℚ
  pools_pp : ∀ q₀ ∈ Pools, IsPP q₀
  pools_gt_one : ∀ q₀ ∈ Pools, (1 : ℚ) < q₀
  Hist  : Cell → Type
  hist_ne : ∀ α, Nonempty (Hist α)
  zc    : ∀ {α}, Hist α → Prop        -- (ZC)-satisfying realizable prefixes
  zc_ne : ∀ α, ∃ x : Hist α, zc x                      -- [C1 non-vacuity]
  Assign : ∀ {α β} (m : Move α β), Hist α → Hpt (dim m) → Type
  finA   : ∀ {α β} (m : Move α β) x h, Fintype (Assign m x h)
  AssignT : ∀ {α v} (m : MoveT α v), Hist α → Hpt (dimT m) → Type
  finAT  : ∀ {α v} (m : MoveT α v) x h, Fintype (AssignT m x h)
  ext : ∀ {α β} (m : Move α β) (x : Hist α) (h : Hpt (dim m)),
    Assign m x h → Hist β             -- [A-2: the history-extension carrier]
  ext_zc : ∀ {α β} (m : Move α β) (x : Hist α) (h) (a : Assign m x h),
    zc x → zc (ext m x h a)           -- extension preserves realizability
  massOf : ∀ {α β} (m : Move α β) (x : Hist α) (h : Hpt (dim m)),
    Assign m x h → ℚ → ℝ              -- the C.1.5 fresh-volume ratio, per cell
  massOfT : ∀ {α v} (m : MoveT α v) (x : Hist α) (h : Hpt (dimT m)),
    AssignT m x h → ℚ → ℝ
  out_ne : ∀ α (x : Hist α), zc x →
    (∃ β (m : Move α β) (h : Hpt (dim m)), Nonempty (Assign m x h)) ∨
    (∃ v (m : MoveT α v) (h : Hpt (dimT m)), Nonempty (AssignT m x h))
    -- [RE-KEYED at REV 3 (Codex-1's both horns): PRODUCTIVITY at realized
    -- histories, not menu-nonemptiness. The note does NOT assert every
    -- syntactic menu nonempty (empty menus matter at the seam; "a species
    -- inadmissible at a particular p keeps its label and contributes empty
    -- landing sets") — so no ∀-menu claim survives. What the note DOES
    -- realize: PART-1's mass 1 at every (ZC) history forces at least one
    -- realized fresh assignment (continuing or terminal) from it. The
    -- all-empty-Assign adversary now violates out_ne at the zc_ne witness.]

/-- T(h) from x — a DEF, not data (C2 repair: the count IS the Assign
cardinality; nothing to tie). -/
def StepSys.cntraw {n} (S : StepSys n) {α β} (m : S.Move α β)
    (x : S.Hist α) (h : Hpt (S.dim m)) : ℕ :=
  @Fintype.card (S.Assign m x h) (S.finA m x h)
def StepSys.cntrawT {n} (S : StepSys n) {α v} (m : S.MoveT α v)
    (x : S.Hist α) (h : Hpt (S.dimT m)) : ℕ :=
  @Fintype.card (S.AssignT m x h) (S.finAT m x h)

/-- (U-A)'s §C supply, TYPED (V.0 "WHAT §C ACTUALLY SUPPLIES, displayed"):
C.1.5(1) gives per fresh assignment vol_nom(E_fresh) = q^{−#(strip pins)} ·
∏_slots (alphabet size)^{−1}, and BOTH factors are functions of the read's
NOMINAL DIGIT INVENTORY (C.1(ii)) — never of which values the cell pins.
Owner §C/HC-2; each field cites its display. -/
structure C15Pack (n : ℕ) (S : StepSys n) where
  Inv   : Type
  invOf : ∀ {α β} (m : S.Move α β), S.Hist α → Hpt (S.dim m) → Inv
  invOfT : ∀ {α v} (m : S.MoveT α v), S.Hist α → Hpt (S.dimT m) → Inv  -- [+T]
  F     : Inv → ℚ → ℝ                 -- the common conditional-mass functional
  mass_factors : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (q₀ : ℚ), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a q₀ = F (invOf m x h) q₀
  mass_factorsT : ∀ {α v} (m : S.MoveT α v) (x : S.Hist α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h) (q₀ : ℚ), q₀ ∈ S.Pools → S.zc x →
    S.massOfT m x h a q₀ = F (invOfT m x h) q₀
    -- [+T, Codex-2: the note's (U-A)/C.1.5(1) covers the final terminal read
    -- exactly as it covers continuing reads — same inventory functional F]
  -- [C.1.5(1) + TYP(b): the mass is q^{−pins(inv)}·∏ alph(inv)⁻¹; the
  -- factored NUMERIC form is a second field the E-designer adds if a unit
  -- needs it; `mass_factors` alone carries (U-A)'s derivation.]

/-- (XHD-w) WEIGHTS, typed: per step datum a monomial g = q^{−E(h)}, E affine
positive, EQUAL to the per-assignment C.1.5 ratio at h — "the conditional
mass, given the source cylinder at ANY representative of α under ANY
admissible history reaching it, of one fresh assignment realizing (m, o, β)
at h". Indexed by SOURCE AND TARGET cells (pass-6 concern 1). Owner [2b]. -/
structure XHDw (n : ℕ) (S : StepSys n) where
  E : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  w_eq : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOf m x h a q₀ = (q₀ : ℝ) ^ (-((E m).eval h : ℤ))
  wT_eq : ∀ {α v} (m : S.MoveT α v) (x : S.Hist α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOfT m x h a q₀ = (q₀ : ℝ) ^ (-((ET m).eval h : ℤ))

/-- the derived one-step weight (a def, not a field): g^{α,β}_{m,o}(h)(q₀). -/
noncomputable def XHDw.g {n} {S : StepSys n} (X : XHDw n S) {α β}
    (m : S.Move α β) (h : Hpt (S.dim m)) (q₀ : ℚ) : ℝ :=
  (q₀ : ℝ) ^ (-((X.E m).eval h : ℤ))

/-- (XHD-u) UNIFORMITY (rev 2, findings 2–3), typed. (u-R): ratio and count
depend on x and its history ONLY through (α, β, m, o, h). (u-T): the count is
one h-independent value per step ON the one-step domain; the RAW field below
demands it where both heights are realized, and the domain-conditional form
is DERIVED (V1-3's exactness + XHDd.no_stray) — no named `u_T_dom` object
exists or is pointed to (A-7 repair). Owner [2b]; NOT §C-derivable (V.0's
honest split — the fence unit V1-7 exhibits a C15Pack model violating u_R). -/
structure XHDu (n : ℕ) (S : StepSys n) where
  u_R_mass : ∀ {α β} (m : S.Move α β) (x x' : S.Hist α) (h : Hpt (S.dim m))
    (a : S.Assign m x h) (a' : S.Assign m x' h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOf m x h a q₀ = S.massOf m x' h a' q₀
  u_R_cnt : ∀ {α β} (m : S.Move α β) (x x' : S.Hist α) (h : Hpt (S.dim m)),
    S.cntraw m x h = S.cntraw m x' h
  u_T : ∀ {α β} (m : S.Move α β) (x : S.Hist α) (h h' : Hpt (S.dim m)),
    0 < S.cntraw m x h → 0 < S.cntraw m x h' →
    S.cntraw m x h = S.cntraw m x h'
  -- terminal twins (Codex-2: XHD-u covers the final terminal read):
  u_R_massT : ∀ {α v} (m : S.MoveT α v) (x x' : S.Hist α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h) (a' : S.AssignT m x' h) (q₀ : ℚ), q₀ ∈ S.Pools →
    S.massOfT m x h a q₀ = S.massOfT m x' h a' q₀
  u_R_cntT : ∀ {α v} (m : S.MoveT α v) (x x' : S.Hist α) (h : Hpt (S.dimT m)),
    S.cntrawT m x h = S.cntrawT m x' h
  u_TT : ∀ {α v} (m : S.MoveT α v) (x : S.Hist α) (h h' : Hpt (S.dimT m)),
    0 < S.cntrawT m x h → 0 < S.cntrawT m x h' →
    S.cntrawT m x h = S.cntrawT m x h'
```

`Template`/`XHDd`/`XHDs` (and their cell/entrance faces) need the path and
state-space vocabulary; they follow in §2.G, and THE `XHD` BUNDLE IS DECLARED
THERE, after its components (C4 declaration-order fix) — keeping V.0's own
order (the package is stated at V.0 but quantifies over templates constructed
at V.2).

### 2.C The state space 𝒞_n (CTS-S) and the computed-partition deliverable (D1)–(D4)

```lean
/-- A SKELETON s (V.2 CTS-S): "the [2a] SP.1 stage/side/residual-shape fields
of the CURRENT node, values and heights forgotten" — EXACTLY MovesSp.Species
(which forgets heights BY TYPE), catalogue-membered. p-INDEPENDENCE BY TYPING:
no field mentions a prime. -/
structure Skeleton (n : ℕ) where
  sp  : MovesSp.Species
  mem : MovesSp.InCatalogue n sp

/-- (D2) generator KIND — a proper inductive (C4/C5 repair; the rev-1
`(twist : ℤ) ⊕ (relName : String)` is struck): (a) an anchor-twisted VAL.1
generator with its twist exponent DISPLAYED; (b) a relational stratum WITH ITS
POLYNOMIAL (the note: "each relation named WITH its polynomial and its
exceptional-characteristic convention") — `relPoly` is a FIELD, not a comment;
the exceptional-characteristic convention IS the per-q₀ assignment map itself
(`part` below), as the note displays it. -/
inductive GenKind where
  | anchor (a_eff : ℤ)
  | rel (relPoly : Polynomial ℤ)

def GenKind.twistExp : GenKind → ℤ
  | .anchor a => a
  | .rel _ => 0

/-- ONE (D2) GENERATOR over the per-prime concrete-state carrier: a UNIFORM
finite partition — one fixed label set, a total per-q₀ cell assignment.
ANCHOR ALIGNMENT AS A TYPE (C10 repair): the generator carries the fixed-frame
map `base`, the anchor action `twistOf`, and the LAW `part_eq`: the partition
map IS base∘twist at the generator's twist exponent — at a_eff ≠ 0 cells apply
to the TWISTED target BY CONSTRUCTION and never directly to the fixed frame;
at a_eff = 0 `twist0` collapses part = base (V2-8 states both as lemmas). -/
structure GenSpec (Carrier : ℚ → Type) where
  idx    : Type
  finI   : Fintype idx
  kind   : GenKind
  base   : ∀ q₀, Carrier q₀ → idx        -- the fixed-frame cell map
  twistOf : ∀ q₀, ℤ → Carrier q₀ → Carrier q₀   -- the anchor action α^{−a}·(−)
  twist0 : ∀ q₀, twistOf q₀ 0 = id
  twist_add : ∀ q₀ a b, twistOf q₀ (a + b) = twistOf q₀ a ∘ twistOf q₀ b
    -- [REV 3, Codex-3/C10 residue: `twistOf` is a ℤ-ACTION by type — junk
    -- non-action data is out. WHICH action (α^{−a}·(−)) is the (D2) display
    -- duty at each computed skeleton, exactly where the note places it; the
    -- gate blocks display it concretely (V6 layer).]
  part   : ∀ q₀, Carrier q₀ → idx        -- total ⟹ a partition, typed
  part_eq : ∀ q₀ x, part q₀ x = base q₀ (twistOf q₀ kind.twistExp x)
  -- (D2) REL FORCING (REV 3, Codex-3: rev 2's `relPoly` was decorative —
  -- nothing relates `part` to it). The relational generator carries the
  -- observable it evaluates, a value carrier with a ring structure to
  -- evaluate the ℤ-polynomial in, and the LAW that its fixed-frame partition
  -- FACTORS THROUGH the polynomial's value at that observable — cells can
  -- depend on x only through relPoly(obs x). For anchor generators these
  -- fields are inert (rel_eq's premise is false).
  Val    : ℚ → Type
  ringV  : ∀ q₀, CommRing (Val q₀)
  relObs : ∀ q₀, Carrier q₀ → Val q₀
  stratOf : ∀ q₀, Val q₀ → idx
  rel_eq : ∀ (P : Polynomial ℤ), kind = .rel P → ∀ q₀ x,
    base q₀ x = stratOf q₀ ((P.map (Int.castRingHom (Val q₀))).eval (relObs q₀ x))

/-- (D1)–(D4) for ONE skeleton — CL-13's COMPUTED-PARTITION DELIVERABLE, one
typed record (V.2: "the meet symbol is a construction RECIPE; the clause-(i)
deliverable is the DISPLAYED LIST"). The MEET CELLS are the fibers of the
product of generator maps — "explicit cell predicates as boolean combinations
of (D2)'s generators" is DEFINITIONAL here. REV 2 adds `evalObs`: the letters'
evaluation-map carrier, so (iv)-REP's per-species proviso `ObsCheck` (§2.G)
has a typed referent (C29 repair). -/
structure BlockData (n : ℕ) (s : Skeleton n) where
  Carrier : ℚ → Type                       -- concrete states over F_{q₀}
  finCar : ∀ q₀, Fintype (Carrier q₀)
  -- (D1) the menu: [2a] SP-OUT letters from s, membership TYPED:
  Letter : Type
  finL   : Fintype Letter
  letterSp : Letter → MovesSp.Species ⊕ MovesSp.Verdict
  letter_menu : ∀ m, letterSp m ∈ MovesSp.Out n s.sp
  -- the letters' evaluation-map carrier ((D1)-level data; ObsCheck's referent):
  Obs     : Letter → ℚ → Type
  evalObs : ∀ (m : Letter) (q₀ : ℚ), Carrier q₀ → Obs m q₀
  -- (D2) the generator list:
  Gen  : Type
  finG : Fintype Gen
  gen  : Gen → GenSpec Carrier
  -- (D3) the meet list: labels = the product of generator labels; size
  -- polynomials with the SPLIT degree bound (W_state(s), never any W_loc):
  Wstate : ℕ
  sizeP  : (∀ g : Gen, (gen g).idx) → Polynomial ℚ
  size_deg : ∀ a, (sizeP a).natDegree ≤ Wstate
  size_count : ∀ (a) (q₀ : ℚ), IsPP q₀ →
    ((sizeP a).eval q₀ : ℚ)
      = (Finset.univ.filter (fun x : Carrier q₀ => ∀ g, (gen g).part q₀ x = a g)).card
  -- (D4) the target-cell map per CONTINUING letter, landing in the TARGET
  -- block's cells "under the SAME global definition" (typed by codomain):
  cont : Letter → Prop
  decCont : DecidablePred cont
  tgtSk : ∀ m, cont m → Skeleton n
  tgt_menu : ∀ m (h : cont m), (letterSp m).isLeft   -- continuing ⟹ species side
```

`BlockData.CellIdx := {a : ∀ g, (gen g).idx // sizeP a ≠ 0}` after zero-size
deletion (V.2: "cells with IDENTICALLY-zero size polynomial are deleted once,
symbolically"). THE TARGET-CELL MAP's cell-level component is a field of the
GLOBAL family record `CtsFamily`, since its codomain needs the target
skeleton's own BlockData — matrix indices type-check BY CONSTRUCTION, "no
species-relative cell ever appears as an index".

```lean
/-- The target index of a letter: continuing ⟹ a target-block cell; terminal
⟹ the absorbing column label. DISPLAYED as the two-constructor inductive it
is (C29 repair; rev 1's prose intent made real). -/
inductive TargetIx (n : ℕ) {s : Skeleton n} (B : BlockData n s)
    (B' : ∀ s', BlockData n s') (m : B.Letter) where
  | cell (h : B.cont m) (β : (B' (B.tgtSk m h)).CellIdx)
  | term (v : VLabel n)

/-- THE TABLE FAMILY over one n: per-skeleton BlockData + the globally-typed
(D4) cell maps + the per-entry count tables (CTS-T). THIS is the record the
SEAM instantiates into MovesS.TableShape (unit V7-3a). -/
structure CtsFamily (n : ℕ) where
  bd : ∀ s : Skeleton n, BlockData n s
  tcell : ∀ (s : Skeleton n) (m : (bd s).Letter) (h : (bd s).cont m),
    (bd s).CellIdx → (bd ((bd s).tgtSk m h)).CellIdx
  -- (CTS-T) the tables, with Theorem VAL(a)'s per-entry content as TYPE:
  -- one polynomial, degree ≤ W_loc(m); the COUNT SEMANTICS is ValA's field
  -- content (§2.F note + V2-4 — the rev-1 `tbl_count` field moved there,
  -- resolving design-freedom slot (3)):
  Wloc : ∀ (s : Skeleton n), (bd s).Letter → ℕ
  Outc : ∀ (s : Skeleton n), (bd s).Letter → Type   -- full outcome labels o
  finO : ∀ s m, Fintype (Outc s m)
  T : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : Outc s m)
    (α : (bd s).CellIdx) (β : TargetIx n (bd s) bd m), Polynomial ℚ
  T_deg : ∀ s m o α β, (T s m o α β).natDegree ≤ Wloc s m
  -- terminal outcome labels (REV 3: TermData's typed referent — the outcome's
  -- absorbing column label, displayed as a field):
  vlabOf : ∀ (s) (m) (o : Outc s m), ¬ (bd s).cont m → VLabel n
```

**The (D4)-typed step data (REV 3, Codex-3/Codex-18: displayed closed; the
target of a continuing datum is ENFORCED by `tcell` BY TYPE — the global D4
map can no longer be decorative, since `S.Move αc βc` will be empty unless βc
is a tcell-image, per `moveOf_bij` in §2.F):**
```lean
structure MoveData (n : ℕ) (C : CtsFamily n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : C.Outc s m
  hc : (C.bd s).cont m
  α  : (C.bd s).CellIdx

/-- the datum's source and its tcell-ENFORCED target. -/
def MoveData.src {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx := ⟨d.s, d.α⟩
def MoveData.tgt {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx :=
  ⟨(C.bd d.s).tgtSk d.m d.hc, C.tcell d.s d.m d.hc d.α⟩

structure TermData (n : ℕ) (C : CtsFamily n) (v : VLabel n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : C.Outc s m
  ht : ¬ (C.bd s).cont m
  hv : C.vlabOf s m o ht = v          -- the absorbing label, enforced
  α  : (C.bd s).CellIdx
```

[The OUTCOME label o carries "next-node data + all hinge-value cells +
collision pattern, or a terminal label — the [2a] L5-case letters"; its Lean
carrier is the abstract `Outc` with the V.6 gate instances pinning concrete
rosters (V6 layer), and the FULL per-skeleton roster is the TABLE-BUILD
deliverable — [1v]-COND's CL-13 burden, which this corpus types but does not
globally compute (exactly the note's own perimeter: "executed in this note
ONLY for the three V.6 gate blocks").]

### 2.D Entrance shapes ε (V.1(iii), rev-4 unified typing) — REV 2: the WF ties (C6/C12/A-3)

```lean
/-- V.1(iii)'s ENTRANCE SHAPE — "the TRIPLE ε := (P̂, b, σ_sel) of a shallow
CONCRETE §D4-R shape-prefix P̂ — which RETAINS its per-node heights h_r and
its per-read side heights u*_r (§D4-R L3, rev 9) — a designated continuing
branch b entering the size-e block landing in cell β₀, and the
branch-selection record σ_sel (L11's encoding data, lifted into the label)".
P̂ IS MovesD.Shape n (its ShapeRead fields `h`, `ustar` are the retained
heights — the rev-4 F1 unification is BY TYPE: no independent height
parameter exists). REV 2 (C6 repair): the triple's components are now TIED —
(gsel, musel) is the ENTRY READ's designated continuing selection (`hentry`,
mirroring MovesSp.EntranceShape.hEntry), L5-ELIGIBLE at that read (`helig`,
keyed to MovesD's eligible-(g,μ) menu — the E6 carrier), and σ_sel carries
ONE record entry per shallow branching cell passed (`hlen`) with each entry
in that cell's finite branch menu (`hmenu`). Degenerate/fictitious entrances
now violate a field. The LANDING (block e, cell β₀) is NOT a field of ε: it
is the measured side's landing data (`CtsMeasured.entLands`, §2.F) — the
note's β₀ always appears as the pairing index (ε, β₀). Entrances are
POST-SPLIT objects: siblings differ in s_r, hence carry DISTINCT ε. -/
structure EntShapeV (n : ℕ) where
  Phat   : MovesD.Shape n
  hne    : (Phat : MovesD.ShapePrefix).reads ≠ []
  gsel   : ℕ                       -- the designated branch's selection (g, μ)
  musel  : ℕ                       --   at the entry read (b's datum)
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hentry : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    R.g = gsel ∧ R.μ = musel       -- b IS the entry read's designated branch
  helig  : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    EligPair R gsel musel          -- L5 eligibility (MovesD E6 menu; def below)
  selRec : List ℕ                  -- σ_sel: s_r at every shallow branching
                                   --   cell passed — THE L11 RANKS (below)
  hlen   : selRec.length =
    ((Phat : MovesD.ShapePrefix).reads.filter IsBranchingRead).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < branchMenuCard n Phat i
```

**σ_sel's SEMANTIC PIN (REV 3, Codex-5: rev 2's entries were "unrelated
bounded naturals").** The i-th entry of `selRec` IS the L11 rank s_r —
`MovesD.selRank` — of the continuation selected at the i-th branching read:
the note's "σ_sel = (s_r at every shallow branching cell passed — L11's
encoding data, LIFTED INTO THE LABEL)" makes the rank the label datum ITSELF,
so at the label layer the tie is DEFINITIONAL (the selection is identified BY
its rank in the shared enumeration), and the identification of ranks with
actual ψ-selections is MovesD's PROVED injectivity `E8_rankInj`/`E9_encInj` —
cited at the instance layer (V3-1(b), V5-1), never re-derived. The entrance
events and the instance census (§2.F) take the FULL label ε (selRec included)
as their key, so distinct selections cut distinct events by construction.
The displayed defs (closed, keyed to NAMED MovesD declarations — Codex-18):
```lean
/-- shape-level eligibility of a (g, μ) pair at a read: the L5 budget
(E5_gmuLe is MovesD's law that every realized node's own pair satisfies it). -/
def EligPair (R : MovesD.ShapeRead) (g μ : ℕ) : Prop :=
  1 ≤ g ∧ 1 ≤ μ ∧ g * μ ≤ R.len

/-- a branching read: its same-shape eligible menu has ≥ 2 slots — the
shape-level menu card is m̄ = ⌊len/(g·μ)⌋ (`ShapeRead.mbar`; MovesD's
`eligible_card_le` bounds the value-level census by it). -/
def IsBranchingRead (R : MovesD.ShapeRead) : Prop := 2 ≤ R.mbar

def branchMenuCard (n : ℕ) (P : MovesD.Shape n) (i : ℕ) : ℕ :=
  (((P : MovesD.ShapePrefix).reads.filter IsBranchingRead).getD i default).mbar
```

```lean
/-- HEIGHT PROJECTION (rev 4): h_ent(ε) := the tuple of ε's RETAINED height
data — the (h_r, u*_r) pair vector over P̂'s reads. A FUNCTION of ε,
displayed; "one concrete ε FIXES its entrance heights". -/
def EntShapeV.hent {n : ℕ} (ε : EntShapeV n) : List (ℕ × ℚ) :=
  (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))

/-- ledger exponent A(ε) := §D4-R's A(P̂) — "a function of ε since u*_r ∈ P̂";
pool dimension W_ent(ε) := §D4-R's W(P̂) — "height-free, L3 rev 9". -/
noncomputable def EntShapeV.A (ε : EntShapeV n) : ℕ :=
  (ε.Phat : MovesD.ShapePrefix).A' n
def EntShapeV.Went (ε : EntShapeV n) : ℕ := (ε.Phat : MovesD.ShapePrefix).W

/-- The height-forgetting TEMPLATE ε̊ — "SP.1 applied to P̂, selection data
kept". REV 2 (C12/A-3 repair): the boundedness is INTRINSIC, not an external
[3t] premise — the word is a CATALOGUE-membered, SuccStep-linked,
RUN-COLLAPSED species word (MovesSp's `CollapsedWalk`: self-loop runs are
struck into the depth direction, exactly [2a]'s collapse convention), the
entry law mirrors `MovesSp.EntranceShape.hEntry`, and σ_sel is menu-bounded
per branching letter. V3-4 proves the family FINITE OUTRIGHT from these
fields ([2a]/M1: `rankNat` strictly increases along collapsed SuccStep edges
— the SP4_dagWords idiom — over the finite SP2 catalogue; L5's finite menus
bound selRec). No `WordBounded` premise exists any more. -/
structure EntTemplate (n : ℕ) where
  word   : List MovesSp.Species
  hne    : word ≠ []
  hMem   : ∀ s ∈ word, MovesSp.InCatalogue n s
  hWalk  : word.Chain' (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s')
  gsel musel : ℕ
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hEntry : ∀ s, word.getLast? = some s → s.sel = some (gsel, musel)
  selRec : List ℕ
  hlen   : selRec.length = (word.filter (IsBranchingLetter n)).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < letterMenuCard n word i

def EntShapeV.template {n : ℕ} (ε : EntShapeV n) : EntTemplate n :=
  { word := MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix)),
    gsel := ε.gsel, musel := ε.musel, selRec := ε.selRec,
    hne := …, hMem := …, hWalk := …, hEntry := …, hlen := …, hmenu := … }
    -- the six WF anonymous fields are PROOF TERMS (not data), each the named
    -- V3-3(b) bridge law (spWord lands in the catalogue, SuccStep-linked;
    -- collapse strikes the runs; selection/menu ties preserved) — E-phase
    -- fills them from that unit; no data freedom hides here.

/-- the instantiation dimension of a template: two ℕ-slots (h_r, the u*-code
u°_r — encoding below) per letter + one depth slot per (collapsed) self-loop
letter — the h-vector H(ε̊) ranges over (V3-5's chart;
MovesSp.EntranceShape's slot layout). -/
def EntTemplate.entDim {n : ℕ} (ε̊ : EntTemplate n) : ℕ :=
  2 * ε̊.word.length + (ε̊.word.filter (SelfLoopLetter n)).length
```

**THE u\*-SLOT ENCODING, PINNED (REV 3, G-3: `MovesD.ShapeRead.ustar : ℚ`
vs the ℕ-slot).** The second slot per letter carries NOT u\*_r but the ℕ-code
of the read's ℤ-datum γ_r (`ShapeRead.gam`); u\*_r is then the DISPLAYED
inversion of MovesD's own WF law `ShapePrefix.gamTie`
(γ = e·(STR·u\*) + (s0 + wSide)·h, an exact ℚ-identity), which DETERMINES
u\* from (γ, h, e, s0, wSide, STR):
```lean
abbrev zig : ℤ ≃ ℕ := (Denumerable.eqv ℤ)   -- the standard zigzag code

-- inside readOfLetter (V3-3(d)): given the letter's reconstructed
-- (e, s0, wSide) data, the prefix-so-far's STR value, the h-slot value h,
-- and the u*-slot value k:
--   ustar := ((zig.symm k : ℚ) − ((s0 + wSide) : ℚ) * h) / (e * STR)
-- gamTie makes the roundtrip EXACT (V3-5(c)'s computation law); if MovesD's
-- WF is later found to constrain gam's range, the code tightens THERE —
-- recorded, never silent.
```
So the note's "H(ε̊) ⊆ ∏ ℕ^{d_i}" typing is honored with a displayed,
invertible encoding; V3-5's bijection horns lean on `gamTie`, a PROVED law.

**THE INSTANTIATION MAP, DISPLAYED (Codex-18: `writeHeights` was prose).**
```lean
/-- write the height/depth point into the template's slots: re-expand the
collapsed self-loop letters by the depth slots, then fold `readOfLetter`
(V3-3(d)'s reconstruction: species letter + (h-slot, u*-code slot) + the
prefix-so-far ↦ the unique WF ShapeRead with those data — ustar via the
zig/gamTie inversion above) along the expanded word; selection data carried
verbatim; the EntShapeV WF fields are V3-3(d)'s proof terms. -/
def writeHeights {n : ℕ} (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) :
    EntShapeV n :=
  { Phat := shapeOfSlots n (expandRuns ε̊.word (depthSlots ε̊ h)) (pairSlots ε̊ h),
    gsel := ε̊.gsel, musel := ε̊.musel, selRec := ε̊.selRec,
    hne := …, hentry := …, helig := …, hlen := …, hmenu := … }
-- shapeOfSlots := List.foldl (readOfLetter n) emptyPrefix; expandRuns /
-- depthSlots / pairSlots are the three Fin-arithmetic slot projections of
-- 2.A's take/drop idiom (closed defs in this file). The anonymous fields are
-- V3-3(d) proof terms.
```

The template family's FINITENESS is unit V3-4 (hypothesis-free). The
bijection of `writeHeights` onto {concrete realizable ε with template ε̊} is
unit V3-5 (theorem-under-hypotheses: GIVEN the entrance-layer exactness
`XHDdEnt` supplying H(ε̊) — §2.G — and V3-3(d)'s reconstruction laws).
V3-3's bridge additionally constructs the `MovesSp.EntranceShape n gsel musel`
behind (ε̊, h) — the consumption-map tie A-3 demanded (word + hMem + hChain +
hEntry transported; heights into the slot functions). ESCALATION HATCH
(recorded, Codex-6): IF V3-3(d) finds a ShapeRead datum genuinely NOT
determined by (species letter, slots, WF ties), the template gains that
datum as a field THEN, with a fresh audit pass — never silently.

### 2.E The marked space and μ̂ (keying to MovesD; the [3t] fence)

```lean
/-- ι_{e,ε,β₀}'s counting-native carrier: the ε-REFINED ENTRANCE INDEX — the
sub-family of Pref(P̂) (MovesD.PrefIdx, D4R.1-SUM's index) cut by the
landing-cell condition on the designated continuing branch (cell data, §D4-R
L5). `lands` is a PARAMETER field with its (D4)-tie: the cut is a CELL
condition, never a height condition (heights ride IN ε). -/
structure EntranceCut (n : ℕ) (ε : EntShapeV n) (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (pol : MovesD.CanonPolicy p F) where
  lands : MovesD.PrefIdx n pol ε.Phat → Prop
  decL  : DecidablePred lands

/-- The MARKED entrance mass at level N, division-free (the MovesC/MovesD
counting idiom): ι·p^{nN} = Σ over the refined index of fiber cards. Each
member is one realized branch prefix η with its Theorem C(b) mass — "ι is
their SUM — a D4R.1-SUM sub-sum, hence a μ̂-object; an f entering twice
carries two marks". The ℝ-valued ι of the seam is DEFINED at V7-4b from this
count and the entrance census/events (§2.F) — tied, not parallel. -/
noncomputable def iotaCount {n : ℕ} (ε : EntShapeV n) {p F pol}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) : ℕ :=
  ∑ᶠ i ∈ {i | cut.lands i}, Nat.card ↥(S.fiber i)
```

μ̂ FENCE (binding, from MovesS): every aggregate of `iotaCount`-type objects
that leaves this corpus is wrapped in `MovesS.MuHat` (no Add, no coercion) —
"the pairing ι_e^T β_e is the μ̂-typed MARKED-entrance total … NEVER a clause
of the density R_σ". No unit of this corpus states a per-f density.

### 2.F The counting carrier `CtsMeasured` (the `MeasuredSide` producer's data half)

REV 2 REDESIGN (C7/C24/A-1 repair) + REV 3 RE-WIRING (F-1/F-2/F-3/F-5,
Codex-7/10/15/16). `CtsMeasured` carries ONLY counting data: boxes,
per-assignment events, digit-cell classifiers, listed height domains,
entrance events and landing data — and, NEW at REV 3, the two INSTANCE-CENSUS
carriers the round-2 audit showed are NOT box events (their cards scale
differently in N — the F-1/F-2 conflation): the ε-instance census `entInst`
(D4R.4's marked-prefix census, box-realized at the defining level) and the
state-instance census `stInst` (the G4 pattern; cellP's rev-1 sizeP wiring).
Each census is tied to its box events by a TYPED division-free counting law
(`ent_card`, `evt_card` + `box_card`) — the fields Fable's adjudication hints
named, making the LedgerIV suite derivable (V7-6a). Digit cells are
OUTCOME-KEYED (`DCellO` — C8). The entrance side is TEMPLATE×COMPONENT-keyed
(A-1). Terminal twins per the §2.B substitution table.

```lean
structure CtsMeasured (n : ℕ) (C : CtsFamily n) (S : StepSys n) where
  toStepCells : S.Cell ≃ Σ s : Skeleton n, (C.bd s).CellIdx
    -- 𝒞_n := {(s, α)} — the StepSys index IS the state space, typed once
  Pools : Set ℚ
  pools_sub : Pools ⊆ S.Pools
  pools_pp : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite      -- [C7: the MeasuredSide pool laws]
  Box  : ℚ → ℕ → Type                  -- level-N residue boxes (MovesD.Box keyed)
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  box_card : ∀ q₀ ∈ Pools, ∀ N, ((Fintype.card (Box q₀ N) : ℚ)) = q₀ ^ (n * N)
    -- [tie: MovesD.Box's card law at the real instance — the F-1/F-3 counting
    --  laws read |Box(N)| = q^{nN}; gate B: |Box(3)| = 2⁹ = 512]
  -- THE MOVE EMBEDDING, target tcell-ENFORCED BY TYPE (Codex-3; §2.C data):
  moveOf : ∀ d : MoveData n C,
    S.Move (toStepCells.symm d.src) (toStepCells.symm d.tgt)
  moveOf_bij : ∀ αc : S.Cell, Function.Bijective
    (fun d : {d : MoveData n C // toStepCells.symm d.src = αc} =>
      (⟨toStepCells.symm d.1.tgt, d.2 ▸ moveOf d.1⟩ : Σ βc, S.Move αc βc))
    -- S.Move αc βc is EMPTY unless βc is a tcell-image: the displayed (D4)
    -- target-cell map is load-bearing BY TYPE (Codex-3's second horn)
  moveOfT : ∀ {v : VLabel n} (d : TermData n C v),
    S.MoveT (toStepCells.symm ⟨d.s, d.α⟩) v
  moveOfT_bij : ∀ (αc : S.Cell) (v : VLabel n), Function.Bijective
    (fun d : {d : TermData n C v // toStepCells.symm ⟨d.1.s, d.1.α⟩ = αc} =>
      d.2 ▸ moveOfT d.1)                                            -- [+T]
  -- OUTCOME-KEYED digit cells (C8) + the classifiers (C2's tie):
  DCellO : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : C.Outc s m),
    (C.bd s).CellIdx → Type
  finDO : ∀ s m o α, Fintype (DCellO s m o α)
  cellOfA : ∀ (d : MoveData n C) (x : S.Hist (toStepCells.symm d.src))
    (h : Hpt (S.dim (moveOf d))),
    S.Assign (moveOf d) x h → DCellO d.s d.m d.o d.α
    -- every fresh assignment lies in EXACTLY ONE digit cell — D4R.0 totality
    -- at the assignment level, BY TYPE (a function, not a relation)
  cellOfAT : ∀ {v} (d : TermData n C v) (x) (h : Hpt (S.dimT (moveOfT d))),
    S.AssignT (moveOfT d) x h → DCellO d.s d.m d.o d.α              -- [+T]
  emult : ∀ {s m o α}, DCellO s m o α → ℕ
    -- the cell's eligible continuing-mark count (Codex-18: was prose) — L5
    -- data at the real instance (MovesD EligibleImage census); V4-7's surplus
    -- and §2.H consume it
  -- per-assignment box events; cell/entrance events are DEFINED from them:
  evtOf : ∀ {αc βc} (mv : S.Move αc βc) (x : S.Hist αc) (h : Hpt (S.dim mv)),
    S.Assign mv x h → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  evtOfT : ∀ {αc v} (mv : S.MoveT αc v) (x : S.Hist αc) (h : Hpt (S.dimT mv)),
    S.AssignT mv x h → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)        -- [+T]
  -- ONE heterogeneous disjointness law over the assignment-step carrier
  -- (REV 3, F-3/Codex-10: rev 2's evt_disj was same-(mv,h)-only; LedgerIV.d4r0
  -- needs cross-cell, cross-HEIGHT, cross-move, terminal included):
  evt_disj : ∀ {αc} (x : S.Hist αc) (p p' : AStep S αc x) (q₀ : ℚ) (N : ℕ),
    p ≠ p' → Disjoint (evtOfStep p q₀ N) (evtOfStep p' q₀ N)
    -- AStep S αc x := (Σ β (mv : S.Move αc β) (h : Hpt (S.dim mv)),
    --   S.Assign mv x h) ⊕ (Σ v (mv : S.MoveT αc v) (h : Hpt (S.dimT mv)),
    --   S.AssignT mv x h) — a closed def of this file; evtOfStep unpacks to
    -- evtOf/evtOfT. [tie]
  -- THE PER-ASSIGNMENT COUNTING LAW (REV 3, F-3/Codex-10: the field that
  -- exists in no rev-2 structure — "evtOf card at stabilized levels" is now
  -- a TYPE; C.1.5's counting semantics, discharged by MovesC/MovesD at the
  -- real instance):
  stabLvl : ∀ {αc βc}, S.Move αc βc → ℕ
  stabLvlT : ∀ {αc v}, S.MoveT αc v → ℕ                              -- [+T]
  evt_card : ∀ {αc βc} (mv : S.Move αc βc) (x) (h) (a : S.Assign mv x h)
    (q₀ : ℚ), q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvl mv,
    ((evtOf mv x h a q₀ N).card : ℝ)
      = S.massOf mv x h a q₀ * (Fintype.card (Box q₀ N) : ℝ)  -- [tie]
  evt_cardT : ∀ {αc v} (mv : S.MoveT αc v) (x) (h) (a) (q₀ : ℚ),
    q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvlT mv,
    ((evtOfT mv x h a q₀ N).card : ℝ)
      = S.massOfT mv x h a q₀ * (Fintype.card (Box q₀ N) : ℝ)  -- [tie, +T]
  -- listed height domains, AS DATA (the [2b] packages assert their EXACTNESS
  -- — XHDd at template level, XHDdC at cell level (§2.G, NEW at REV 3);
  -- the lists themselves are this corpus's constructed data):
  cdom : ∀ (d : MoveData n C), DCellO d.s d.m d.o d.α → SemilinPart (S.dim (moveOf d))
  cdomT : ∀ {v} (d : TermData n C v), DCellO d.s d.m d.o d.α
    → SemilinPart (S.dimT (moveOfT d))                               -- [+T]
  mdom : ∀ (d : MoveData n C), SemilinPart (S.dim (moveOf d))
  mdomT : ∀ {v} (d : TermData n C v), SemilinPart (S.dimT (moveOfT d))
    -- the MOVE-level listed one-step domains (ValA.tbl_count's base-point
    -- keys, REV 3 Codex-4; exactness = XHDd at the length-1 template)
  -- activity:
  activeState : ℚ → S.Cell → Prop     -- |α|(q₀) > 0 (Act_{q₀}'s predicate)
  act_size : ∀ q₀ ∈ Pools, ∀ c : S.Cell, activeState q₀ c ↔
    ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀ ≠ 0
  -- THE STATE-INSTANCE CENSUS (REV 3, F-5's revert + Codex-16: cellP's
  -- rev-1 sizeP wiring needs the state-census carriers; the G4 pattern
  -- "instance events whose card IS the cell size"):
  stLvl : S.Cell → ℕ
  stInst : S.Cell → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  stInst_card : ∀ (c : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ((stInst c q₀ (stLvl c)).card : ℚ)
      = ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀  -- [tie]
  -- ENTRANCE SIDE, template×component-keyed (A-1):
  entDom : ∀ ε̊ : EntTemplate n, SemilinPart ε̊.entDim   -- H(ε̊), LISTED (data)
  entLands : EntTemplate n → S.Cell → Prop   -- "entering the size-e block
  decLands : ∀ ε̊, DecidablePred (entLands ε̊) -- landing in cell β₀" (the
                                             -- ε-triple's landing datum)
  entEvt : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)                  -- concrete-ε entrance BOX events
  entLvl : EntTemplate n → ℕ           -- the stabilization level per template
  -- THE ε-INSTANCE CENSUS (REV 3, F-1/F-2/Codex-7: the carrier the round-2
  -- audit demanded — D4R.4's finite marked-prefix census, box-realized at
  -- the defining level; NOT the box event entEvt, whose card scales as
  -- q^{nN−A}):
  entInst : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)
  -- THE ENTRANCE COUNTING LAW, division-free (F-1's typed repair; discharged
  -- by the EXPORTED MovesD.D4R1_SUM/D0b_thmCtop at the real instance — G-4):
  ent_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ∀ N ≥ entLvl ε.template,
    ((entEvt ε β₀ q₀ N).card : ℚ) * q₀ ^ (ε.A : ℕ)
      = ((entInst ε β₀ q₀ (entLvl ε.template)).card : ℚ) * q₀ ^ (n * N)
    -- [tie] gate B (q₀ = 2, n = 3, A = 3, N = 3): 128·2³ = 2·2⁹ ✓ — the
    -- event card is I^ent·q^{nN−A} = 128, and the census is I^ent(2) = 2:
    -- F-1's 128-not-8192 acceptance number
```

Derived defs (displayed here; no free data behind them):
```lean
/-- fixed-height CELL events := the union of the cell's assignments' events
(C2's demanded tie: cellEvt ↔ Assign ↔ cntraw, definitional). -/
noncomputable def CtsMeasured.cellEvt (V : CtsMeasured n C S)
    (d : MoveData n C) (x : S.Hist _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (q₀ : ℚ) (N : ℕ) : Finset (V.Box q₀ N) :=
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).biUnion (fun a => V.evtOf (V.moveOf d) x h a q₀ N)
-- cellEvtT : the [+T] twin over cellOfAT/evtOfT, same shape.

/-- the cell-refined count T_c(h) from x — again a def. -/
def CtsMeasured.cntc (V : CtsMeasured n C S) (d : MoveData n C)
    (x : S.Hist _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) : ℕ :=
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).card
-- cntcT : the [+T] twin.

/-- THE ε-INSTANCE COUNT — a DEF (card of the census at the defining level):
I^ent_{ε,β₀}(q₀), the note's marked-prefix count. NOT an event card at a
box level (F-2's repair): its q₀-dependence is the polynomial ENT-COUNT
burden (deg ≤ W_ent), never a q^{nN−A} scaling. -/
noncomputable def CtsMeasured.entCensus (V : CtsMeasured n C S)
    (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  (V.entInst ε β₀ q₀ (V.entLvl ε.template)).card

/-- THE ENTRANCE INDEX (A-1's carrier, DECLARED): template × listed component,
landing at β₀ — FINITE (V3-4 × list length), the type `MovesS.MeasuredSide.
EntShape e τ` instantiates. -/
def CtsMeasured.EntIx (V : CtsMeasured n C S) (β₀ : S.Cell) : Type :=
  {p : Σ ε̊ : EntTemplate n, Fin (V.entDom ε̊).comps.length // V.entLands p.1 β₀}

/-- entrance count per EntIx member := the CENSUS at the component's base
instantiation (F-2/Codex-7 repair: the census, never the box-event card; the
polynomial across the WHOLE component being this same value is exactly
(ENT-U) — V3-9b — cited where consumed, never baked in). Gate B: entCount =
I^ent(q₀) = q₀(q₀−1), degree 2 ≤ Went = 3 — the ent-degree ledger
(ι_degT/degT_le vs Went) is jointly satisfiable again. -/
noncomputable def CtsMeasured.entCount (V : CtsMeasured n C S) {β₀}
    (i : V.EntIx β₀) (q₀ : ℚ) : ℕ :=
  V.entCensus (writeHeights i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base) β₀ q₀
```

The rev-1 fields `tbl_count`, `μcell`, `ιval`, `entCount`(free), `DCell`
(move-keyed), and the loose "from 2.E" pointers are GONE: the table-count
semantics is `ValA`'s field content (V2-4 — VAL(a)'s burden, where the note
itself places it: "alternative discharge: the table build proves
representative-uniform count rows per species"); the measured ℝ-objects are
V7-4a/b/c definitions; A-7's pointer hygiene is moot (each object has one
home).

### 2.G Templates, the chain count, XHD-d/-s (all faces), the bundle, HMC, and the COMP typing (V.1(iv)–(vi), V.4)

```lean
/-- A finite path template γ in block e (V.1(vi)): β₀ →^{m₁,o₁} β₁ → … → β_k,
length ≥ 1, with the rev-4 TERMINAL-FINAL EXTENSION: the final step may carry
a terminal outcome — "there β_k := the absorbing column label [o_k] — an EXIT
OBJECT … the label consumed only as a column index", heights/weight/count
typed as for any read, NO target-cell map consumed. -/
inductive Template (n : ℕ) (S : StepSys n) : S.Cell → Type
  | last  {α β} (m : S.Move α β)  : Template n S α
  | lastT {α v} (m : S.MoveT α v) : Template n S α
  | cons  {α β} (m : S.Move α β) (γ : Template n S β) : Template n S α

def Template.D {n S} : ∀ {α}, Template n S α → ℕ    -- total height dimension
  | _, .last m => S.dim m | _, .lastT m => S.dimT m
  | _, .cons m γ => S.dim m + γ.D

/-- THE CHAIN COUNT T_γ(x, h) — A DEF, BY THE NOTE'S OWN DEFINITION (C2/C9/
A-2 repair; design-freedom slot (2) RESOLVED: V.0 "T_γ(x, h) := #{fresh-
assignment chains from x realizing (γ, h)}" is a DEFINITION, so Lean encodes
it as the recursion through `StepSys.ext` — no free `chain` field, no tie
field to forget; XHDd's exactness laws below quantify over THIS count, so a
degenerate XHDd with junk domains violates them). -/
def chainCount {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α), S.Hist α → Hpt γ.D → ℕ
  | _, .last m,  x, h => S.cntraw m x h
  | _, .lastT m, x, h => S.cntrawT m x h
  | _, .cons m γ, x, h =>
      ∑ a : S.Assign m x (Hpt.take h), chainCount S γ (S.ext m x _ a) (Hpt.drop h)
-- (Hpt.take/drop: the Fin-append splitters, defs in 2.A's E-phase file.)

/-- (XHD-d) DOMAINS, typed: per template an EXPLICITLY LISTED pairwise-
disjoint semilinear PARTITION of the EXACT realizable height domain, exact
two-sidedly against the chain count T_γ(x, h) — which is now the DEF above:
(no orphan) count > 0 at some representative ⟹ h ∈ H(γ);
(no stray)  h ∈ H(γ) ⟹ count > 0 at EVERY representative. Owner [2b]. -/
structure XHDd (n : ℕ) (S : StepSys n) where
  dom : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  no_orphan : ∀ {α} (γ : Template n S α) (x : S.Hist α) (h : Hpt γ.D),
    0 < chainCount S γ x h → (dom γ).Mem h
  no_stray : ∀ {α} (γ : Template n S α) (h : Hpt γ.D),
    (dom γ).Mem h → ∀ x : S.Hist α, 0 < chainCount S γ x h

/-- ∏ᵢ g_i(h_i): the fixed-height template weight (a def over XHDw, by
recursion on γ with Hpt.take/drop). -/
noncomputable def gProd {n S} (W : XHDw n S) :
  ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ := …

/-- (XHD-s) SUMS, template face, typed: per LISTED linear set, the height sum
of the weight product is ONE ℚ(q) element in the note's geometric-denominator
class (denominators ∣ X^b·∏(1 − X^a)), convergent at every pool evaluation.
"By XHD-d's disjointness the finitely many component sums ADD EXACTLY to the
H(γ)-sum" is unit V0-3 + V5-4's consumption, not a field. Owner [2b]. -/
structure XHDs (n : ℕ) (S : StepSys n) (W : XHDw n S) (D : XHDd n S) where
  Gc : ∀ {α} (γ : Template n S α), Fin (D.dom γ).comps.length → Qq
  Gc_denom : ∀ {α} (γ : Template n S α) (j), ∃ b (as : Finset ℕ+),
    (Gc γ j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))
  Gc_ok : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
    Gc γ j ∈ OKat q₀
  Gc_hasSum : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((D.dom γ).comps.get j).Mem h} =>
        gProd W γ h.1 q₀)
      ((evalAt q₀ ⟨Gc γ j, Gc_ok γ j q₀ hq⟩ : ℚ) : ℝ)

/-- THE CELL D-FACE (NEW at REV 3 — F-3's missing face: the XHD bundle had a
d-face for templates and entrances and NONE for digit cells): per digit cell,
the listed `cdom` is exact two-sidedly against the cell-refined count —
h ∈ cdom(c) ⟺ cntc(c, h) > 0. Supplies LedgerIV.xhd_no_stray/no_orphan
through the evt_card nonemptiness tie (V7-6a). Owner [2b]. -/
structure XHDdC (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  no_orphanC : ∀ (d : MoveData n C) (x : S.Hist _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))), 0 < V.cntc d x c h → (V.cdom d c).Mem h
  no_strayC : ∀ (d : MoveData n C) (c) (h),
    (V.cdom d c).Mem h → ∀ x, 0 < V.cntc d x c h
  no_orphanCT : ∀ {v} (d : TermData n C v) (x) (c) (h),
    0 < V.cntcT d x c h → (V.cdomT d c).Mem h                       -- [+T]
  no_strayCT : ∀ {v} (d : TermData n C v) (c) (h),
    (V.cdomT d c).Mem h → ∀ x, 0 < V.cntcT d x c h                  -- [+T]

/-- (XHD-s) CELL FACE — RE-KEYED WEIGHT-ONLY at REV 3 (F-4/Codex-9: the rev-2
count-bearing `Gcell` with `cell_refine : Σ Gcell = Σ Gc` forced T ≡ 1 — the
(q−1)² adversary — AND, count-bearing, it decided (J-RAT)'s ℚ(q)-membership
by hypothesis). The [2b] height-sum face proper carries the WEIGHT g alone
per (cell, listed component); the COUNT factor enters only through the typed
[1v] burden `CellPolyPack` at the definition sites (V7-4c's gwt/μcell), and
the count-bearing refinement identity Σ_c P_c·ΣGcell = T·ΣGc is the DERIVED
unit V5-8 — count factor displayed, nothing collapsed, nothing decided.
Owner [2b]. -/
structure XHDsC (n : ℕ) (S : StepSys n) (W : XHDw n S) (D : XHDd n S)
    {C : CtsFamily n} (V : CtsMeasured n C S) (Xs : XHDs n S W D) where
  Gcell : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length), Qq
  Gcell_denom : ∀ d c j, ∃ b (as : Finset ℕ+),
    (Gcell d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gcell_ok : ∀ d c j (q₀ : ℚ), q₀ ∈ S.Pools → Gcell d c j ∈ OKat q₀
  Gcell_hasSum : ∀ (d) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
        W.g (V.moveOf d) h.1 q₀)
      ((evalAt q₀ ⟨Gcell d c j, Gcell_ok d c j q₀ hq⟩ : ℚ) : ℝ)
    -- WEIGHT-ONLY: no cntc factor, no x quantifier — the count polynomial
    -- multiplies OUTSIDE (V7-4c), where CellPolyPack types it
  GcellT : ∀ {v} (d : TermData n C v) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdomT d c).comps.length), Qq                        -- [+T]
  GcellT_denom : ∀ {v} (d : TermData n C v) c j, ∃ b (as : Finset ℕ+),
    (GcellT d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  GcellT_ok : ∀ {v} (d : TermData n C v) c j (q₀ : ℚ),
    q₀ ∈ S.Pools → GcellT d c j ∈ OKat q₀
  GcellT_hasSum : ∀ {v} (d : TermData n C v) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdomT d c).comps.get j).Mem h} =>
        (q₀ : ℝ) ^ (-((W.ET (V.moveOfT d)).eval h.1 : ℤ)))
      ((evalAt q₀ ⟨GcellT d c j, GcellT_ok d c j q₀ hq⟩ : ℚ) : ℝ)   -- [+T]

/-- (XHD-s) ENTRANCE FACE — RE-KEYED WEIGHT-ONLY at REV 3 (Codex-8: the rev-2
face summed the full count·weight mass ιshH, which (i) double-counted against
V3-9c's countT×geom PolyGeom and (ii) silently DECIDED the INIT-RAT burden.
The note's own split: "the note's XHD-s shallow face supplies the geometric
sum of WEIGHTS; (ENT-U) and ENT-COUNT are then needed to extract a constant
count polynomial"). Per entrance-index member (template ε̊, listed component
j of H(ε̊)): the height sum of the C(b) WEIGHT q^{−A(ε̊[h])} alone is one
ℚ(q) element of the class, convergent at pools. Owner [2b]. -/
structure XHDsEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  Gent : ∀ (β₀ : S.Cell) (i : V.EntIx β₀), Qq
  Gent_denom : ∀ β₀ i, ∃ b (as : Finset ℕ+),
    (Gent β₀ i).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gent_ok : ∀ β₀ i (q₀ : ℚ), q₀ ∈ V.Pools → Gent β₀ i ∈ OKat q₀
  Gent_hasSum : ∀ β₀ (i : V.EntIx β₀) (q₀) (hq : q₀ ∈ V.Pools),
    HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        (q₀ : ℝ) ^ (-(((writeHeights i.1.1 h.1).A : ℕ) : ℤ)))
      ((evalAt q₀ ⟨Gent β₀ i, Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)
    -- WEIGHT-ONLY: the count I^ent multiplies OUTSIDE, through ENT-COUNT +
    -- (ENT-U) at V3-9c/V7-4b — the burdens stay burdens

/-- (XHD-d) ENTRANCE FACE: exactness of the LISTED H(ε̊) against concrete-ε
realizability (V3-5's hypothesis; `Realizable` DISPLAYED — C29), PLUS the
REV-3 landing law (Codex-6's second horn: rev 2's no_orphanE concluded only
domain membership, so a realizable entrance could be excluded from EntIx and
V3-8 could omit genuine entrances). Owner [2b]. -/
structure XHDdEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  no_orphanE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    Realizable V (writeHeights ε̊ h) β₀ → (V.entDom ε̊).Mem h
  no_strayE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    V.entLands ε̊ β₀ → (V.entDom ε̊).Mem h → Realizable V (writeHeights ε̊ h) β₀
  lands_of_realizable : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    Realizable V (writeHeights ε̊ h) β₀ → V.entLands ε̊ β₀
    -- [REV 3: no realizable entrance falls outside the EntIx carrier]

def Realizable {n C S} (V : CtsMeasured n C S) (ε : EntShapeV n)
    (β₀ : S.Cell) : Prop :=
  ∀ q₀ ∈ V.Pools, ∃ N₀, ∀ N ≥ N₀, (V.entEvt ε β₀ q₀ N).Nonempty

/-- the per-instantiation ℝ-valued entrance mass — A DEF, RE-KEYED at REV 3
(F-1, THE q-POWER SLIP: rev 2's body read the BOX-EVENT card, which is
I^ent·q^{n·entLvl−A}, so the def computed ι·q^{n·entLvl−A}, not ι — refuted
by the blueprint's own gate numbers). The census carrier is the fix:
ιshH(ε̊, h, β₀) := I^ent(ε̊[h])(q₀) · q₀^{−A(ε̊[h])}, I^ent := the ε-INSTANCE
CENSUS (V.entCensus — the D4R.4 marked-prefix count, NOT an event card).
GATE CHECK (F-1's acceptance): q₀ = 2, A = 3, entLvl = 3 —
ιshH = 2·2⁻³ = 1/4; ιshH·|Box(3)| = (1/4)·512 = 128 = card(entEvt at 3)
per `ent_card` (128, never 8192): `LedgerIV.init_count` is TRUE at the
intended instance. -/
noncomputable def ιshH {n C S} (V : CtsMeasured n C S) (ε̊ : EntTemplate n)
    (h : Hpt ε̊.entDim) (β₀ : S.Cell) (q₀ : ℚ) : ℝ :=
  (V.entCensus (writeHeights ε̊ h) β₀ q₀ : ℝ)
    * (q₀ : ℝ) ^ (-(((writeHeights ε̊ h).A : ℕ) : ℤ))

/-- THE XHD PACKAGE (V.0), one record — DECLARED AFTER ITS COMPONENTS (C4):
w + u + d (template, CELL — new at REV 3 — and entrance faces) + s (template,
cell, entrance faces) + the entrance exactness. [1v]-FULL is V1-5's
`IsFullDischarge`; until it is instantiated every measured unit takes the
package (or the exact sub-package its V.1 ledger line names) as an explicit
argument — the tag displayed at its site. -/
structure XHD (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  w : XHDw n S
  u : XHDu n S
  d : XHDd n S
  dC : XHDdC n S V          -- [REV 3: the cell d-face — F-3]
  s : XHDs n S w d
  sC : XHDsC n S w d V s
  sEnt : XHDsEnt n S V
  dEnt : XHDdEnt n S V

/-- (v) HMC — THE OPEN KERNEL, typed exactly as displayed: "the whole-template
exact domain FACTORS stepwise, each factor depending ONLY on the retained
state β_{i−1} and the step data — never on earlier height choices". Stated as
membership-factorization over the flattening; templates INCLUDE terminal-final
ones (they are `Template` constructors — the rev-4 signature is BY TYPE).
NEVER proved in this corpus; consumed by (COMP-Σ)/V5-5 and V4-12. -/
def HMC {n : ℕ} (S : StepSys n) (D : XHDd n S) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (h₁ : Hpt (S.dim m))
    (h₂ : Hpt γ.D),
    (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂

/-- (HMC-AUG)'s refinement carrier — FULLY TYPED at REV 3 (Codex-13: the
rev-2 count_proj was an inequality with a loose ∃m and count_cover was
schematic, so an UNRELATED HMC-satisfying system could witness the
existential). Now: moves PROJECT (moveProj, dimension-preserving), heights
identify along dim_eq, assignments EMBED (assignOf, mass-preserving), and
the refined assignments over each coarse move PARTITION its fiber
(assign_cover, a displayed Σ-bijection) — so S' is keyed to S move-by-move,
height-by-height, count-by-count; count_proj/count_cover are now LEMMAS
(cards of a partitioned Σ-type), not fields. "One round of 𝒞_n refinement
by finitely-valued boundary/gap data"; never assumed in this corpus
(ledgered V.5(2)). -/
structure Refinement (n : ℕ) (S : StepSys n) where
  B : S.Cell → Type                       -- the finitely-valued refinement data
  finB : ∀ α, Fintype (B α)
  S' : StepSys n
  cellEq : S'.Cell ≃ Σ α : S.Cell, B α    -- refined cells fiber over 𝒞_n
  histOf : ∀ α' : S'.Cell, S'.Hist α' → S.Hist (cellEq α').1
  moveProj : ∀ {α' β'}, S'.Move α' β' → S.Move (cellEq α').1 (cellEq β').1
  dim_eq : ∀ {α' β'} (m' : S'.Move α' β'), S'.dim m' = S.dim (moveProj m')
  assignOf : ∀ {α' β'} (m' : S'.Move α' β') (x' : S'.Hist α')
    (h : Hpt (S'.dim m')),
    S'.Assign m' x' h → S.Assign (moveProj m') (histOf α' x') (dim_eq m' ▸ h)
  mass_eq : ∀ {α' β'} (m' : S'.Move α' β') (x') (h) (a') (q₀ : ℚ),
    S'.massOf m' x' h a' q₀
      = S.massOf (moveProj m') (histOf α' x') (dim_eq m' ▸ h) (assignOf m' x' h a')
  assign_cover : ∀ {α β} (m : S.Move α β) (α' : S'.Cell)
    (hα : (cellEq α').1 = α) (x' : S'.Hist α') (h : Hpt (S.dim m)),
    Function.Bijective
      (fun p : Σ (β' : {β' : S'.Cell // (cellEq β').1 = β})
          (m' : {m' : S'.Move α' β'.1 // castMove hα β'.2 (moveProj m') = m}),
          S'.Assign m'.1 x' (castHpt m'.2 (dim_eq m'.1) h) =>
        castAssign hα β'.2 (assignOf p.2.1.1 x' _ p.2.2))
    -- the refined assignments over (α', x') PARTITION the coarse fiber
    -- S.Assign m (histOf α' x') h. `castMove`/`castHpt`/`castAssign` are the
    -- three ▸-transport helpers along hα/β'.2/dim_eq — closed defs of this
    -- file (Eq.mpr wrappers, displayed at E-phase in one line each); the
    -- Σ-domain and the target fiber are otherwise verbatim as shown.
  -- terminal twins [+T]: moveProjT / dimT_eq / assignOfT / massT_eq /
  -- assign_coverT, by the §2.B substitution table (targets: the SAME
  -- absorbing label v on both sides — VLabel does not refine).

def HMCAug {n : ℕ} (S : StepSys n) (D : XHDd n S) : Prop :=
  ∃ (R : Refinement n S) (D' : XHDd n R.S'), HMC R.S' D'
  -- an unrelated witness is now impossible: D' is exact against S'.counts
  -- (XHDd quantifies over chainCount, a def), and S'.counts partition S's
  -- through assign_cover — the refinement is keyed to S by construction

/-- (ENT-U)'s affine-A face (M4a), DISPLAYED (C29): A(ε̊[h]) is affine in h
across instantiations of one template (dependent codomain — the rev-2 `_`
made explicit). -/
structure AffEnt (n : ℕ) where
  AE : ∀ ε̊ : EntTemplate n, AffineE ε̊.entDim
  A_eq : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim),
    (writeHeights ε̊ h).A = (AE ε̊).eval h

/-- (iv)-REP's per-species proviso, DISPLAYED (C29): "the species' evaluation
maps mention no observable outside the (a)/(b) generator list" — the letters'
evaluation maps factor through the generator meet. A PER-SPECIES CHECK
(table-build burden; executed at the gate blocks — V6-3b's (D2)-EMPTY). -/
def ObsCheck {n : ℕ} {s : Skeleton n} (B : BlockData n s) : Prop :=
  ∀ (m : B.Letter) (q₀ : ℚ) (x x' : B.Carrier q₀),
    (∀ g, (B.gen g).part q₀ x = (B.gen g).part q₀ x') →
    B.evalObs m q₀ x = B.evalObs m q₀ x'

/-- cofinite activity (V7-5 leg (c)'s premise carrier, DISPLAYED — C29):
at every state, only finitely many pools are inactive. -/
def CofinAct {n C S} (V : CtsMeasured n C S) : Prop :=
  ∀ c : S.Cell, {q₀ ∈ V.Pools | ¬ V.activeState q₀ c}.Finite
```

### 2.H The J tables ((J-RAT)/CL-18's carrier — the PLAN-SYNC deliverable) — REV 3: ROUTE-keyed (F-6)

```lean
/-- the (K-SUB) route classification of an outcome — the (m, c) row datum. -/
inductive RouteTag | kcol | split | term
  deriving DecidableEq

/-- THE J-CELL ROSTER — RE-KEYED at REV 3 (F-6, THE ROSTER BUG: rev 2 kept
only cells with ≥ 2 CONTINUING marks, but the note's bracket "[o branching :=
the (c ≥ 1, m ≥ 2) row of (K-SUB)'s (m, c) CLASSIFICATION]" classifies the
OUTCOME, not a sub-roster of its cells — and (K-SUB)'s arithmetic
Σ_β K + Σ b^term + Σ_o J_{τ,o} = 1 = PART-1's total over ALL cells forces
J_{τ,o} = the FULL cell mass of every split-route outcome. At n = 3 the rev-2
roster was EMPTY everywhere (V4-8's emult ≤ 1 census) while the note's J at
the root's m_2+1 outcome (m = 2, c = 1, T = q(q−1)) is nonzero.) J sums ALL
cells of a split-route outcome, EACH CELL ONCE — PART-1's partition index,
NEVER the marked per-continuing-branch T·G. -/
-- (Declaration order in the E-file: RouteTag → JCells → CellPolyPack → Jval
--  — Jval consumes the pack; displayed here in reading order.)
structure JCells (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  route : ∀ (s : Skeleton n) (m : (C.bd s).Letter), C.Outc s m → RouteTag
    -- the (K-SUB) classification datum; V7-3a carries the compatibility law
    -- `route_eq` tying it to MovesS's routeOf ∘ odata at the seam instance
  bcells : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : C.Outc s m)
    (α : (C.bd s).CellIdx), Finset (V.DCellO s m o α)
  roster_tie : ∀ s m o α (c : V.DCellO s m o α),
    c ∈ bcells s m o α ↔ route s m o = .split
    -- ALL cells iff the outcome is split-route; ∅ otherwise. The rev-2
    -- emult ≥ 2 tie is STRUCK; emult stays V4-7's surplus datum only.

/-- J_{τ,o}(q₀) as a MEASURED value: Σ over ALL cells of the split-route
(τ, o), EACH ONCE, of the XHD-resummed conditional cell mass — REV 3: the
cell mass is count-polynomial × weight-sum (the [1v]×[2b] split; XHDsC is
weight-only, so no factor is dropped and none is squared):
μcellVal cp XsC c q₀ := (cp.P … c).eval q₀ · Σ_j evalAt (XsC.Gcell … c j).
The ℚ(q) membership — (J-RAT) — is unit V5-7b; its PolyGeom presentation
supplies `MovesS.RatBurdens.jP`. GATE (F-6's acceptance): at the root's
m_2+1 split outcome, Jval = T·G-mass of its one cell = q(q−1)-count mass
≠ 0 — the n = 3 roster is NONEMPTY and Jval is nonzero. -/
noncomputable def Jval {n C S} {V : CtsMeasured n C S} (J : JCells n C S V)
    (cp : CellPolyPack n C S V) (XsC : XHDsC n S _ _ V _)
    (d : MoveData n C) (q₀ : ℚ) : ℝ :=
  ∑ c ∈ J.bcells d.s d.m d.o d.α, μcellVal cp XsC d c q₀
-- μcellVal cp XsC d c q₀ :=
--   ((cp.P d.s d.m d.o d.α c).eval q₀ : ℝ)
--     * ∑ j, ((evalAt q₀ ⟨XsC.Gcell d c j, _⟩ : ℚ) : ℝ)
-- (+T twin JvalT over TermData/GcellT for terminal split bookkeeping rows.)

/-- the per-cell count-polynomial pack ((J-RAT)'s [1v] face) — CLOSED at
REV 3 (Codex-16/18: no `V.moveOf …` ellipses; CtsMeasured now HAS the domain
carriers). One polynomial per digit cell, degree ≤ W_loc, valued at the
cell-refined count ON THE LISTED CELL DOMAIN (domain-keyed, unguarded — it
says something wherever the domain does; cdom exactness is XHDdC's face).
ADJUDICATION (recorded): keying the valuation across the whole listed domain
bakes CELL-LEVEL height-constancy into this [1v] burden — that is the note's
OWN (J-RAT) split ("cell-level counts polynomial per the (iv)-POLY pattern"
= one polynomial per cell), unlike VAL(a), where the note explicitly assigns
height-uniformity to (XHD-u) and V2-4 therefore keys tbl_count to base
points. A burden may be strong when the note's burden is. -/
structure CellPolyPack (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  P : ∀ (s) (m) (o : C.Outc s m) (α), V.DCellO s m o α → Polynomial ℚ
  deg : ∀ s m o α c, (P s m o α c).natDegree ≤ C.Wloc s m
  count : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (x : S.Hist _) (hzc : S.zc x) (q₀ : ℚ), q₀ ∈ V.Pools →
    ∀ h, (V.cdom d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntc d x c h
  countT : ∀ {v} (d : TermData n C v) (c) (x) (hzc : S.zc x) (q₀ : ℚ),
    q₀ ∈ V.Pools → ∀ h, (V.cdomT d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntcT d x c h           -- [+T]
```

### 2.I `DefsGate.lean` — the V.6 sealed data (concrete, decide-native) — REV 2: the A2 chart + the nine-point fields (C3, C20, C21)

Concrete data only (no laws): the root roster (five letters with their five
closed-form polynomials `TH3 = C(1/6)·X·(X−1)·(X−2)`, `TH12 = C(1/2)·X²·(X−1)`,
`TH3c = C(1/3)·(X³−X)`, `T21 = X·(X−1)`, `T3 = X`); the s_blk2 roster
(`Tsplit = C(1/2)·(X−1)·(X−2)`, `Tinert = C(1/2)·X·(X−1)`, `Tdbl = X−1`,
`Tw2 = X−1`, `Tvv = (X−1)²`); the gate-B constants (A(ε) = 3, W_ent = 3,
`Ient = X·(X−1)`, ι = 1/4, T = 1, g = 1/8, μ̂ = 1/32, shadow = 2, N₀ = 3);
the census q-list `censusQ := [2,3,4,5,7,8,9,11,13]` (ALL NINE, in-kernel —
C20 repair; `censusP` deleted).

**The A2 entry, note-faithfully reparameterized (C3 — THE ARITHMETIC CATCH):**
```lean
/-- the (t,u) chart: t = h₂ ≥ 1, u ≥ 0; chart (t,u) = (h₀, h₂) =
(3t + 2u + 1, t). A DEFINITION — the coordinate change itself. -/
def A2chart (h : Hpt 2) : Hpt 2 := ![3 * h 0 + 2 * h 1 + 1, h 0]

/-- the A2 height domain IN (t,u) COORDINATES: L((1,0); {(1,0),(0,1)})
(t ≥ 1, u ≥ 0 — one linear set; the (h₀,h₂)-image is V6-2a's lemma). -/
def A2dom : LinSet 2 := ⟨![1, 0], [![1, 0], ![0, 1]]⟩

/-- the A2 weight IN (t,u) COORDINATES — coefficients NATURAL: const 1,
coeff (6, 3), i.e. E = 6t + 3u + 1. ATTRIBUTION (REV 3, G-1): this (t,u)
form is OURS, derived; the note displays E = (3(h₀+h₂)−1)/2 and the domain
substitution "h₂ = t ≥ 1, h₀ = 3t + 2u + 1" (MOVES 8844) — the string
"6t+3u+1" appears nowhere in the frozen note. Both round-2 auditors
re-derived it independently (3(4t+2u+1)−1 = 2(6t+3u+1) ✓). The (h₀,h₂)
display is RE-DERIVED through A2chart as the division-free identity
2·E = 3(h₀+h₂) − 1 (V6-2b). -/
def EA2 : AffineE 2 := ⟨1, ![6, 3], by decide⟩

def TA2 : Polynomial ℚ := (Polynomial.X - 1) ^ 2
```
Sealed census height point: (h₀,h₂) = (4,1) = A2chart ![1,0], E = EA2.eval
![1,0] = 7 ✓ (the seal's value).

**The three prime-power fields (C20 repair; tables DISPLAYED at REV 3 —
Codex-18; provenance corrected — G-2):** explicit table-based instances over
`Fin` carriers, laws discharged by `decide`:
```lean
def F4 : Type := Fin 4          -- 0,1,x,x+1 over F₂[x]/(x²+x+1)
def f4mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (([[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]].get a).get b)
def f4add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (([[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]].get a).get b)
instance : Field F4 :=
  { add := f4add, mul := f4mul, zero := 0, one := 1, neg := id, …laws := by decide }
-- F8 := Fin 8 over F₂[x]/(x³+x+1); F9 := Fin 9 over F₃[x]/(x²+1) — same
-- pattern, the 8×8 / 9×9 tables generated once and PASTED as literals (the
-- E-file displays them in full; decide checks the field laws in-kernel).
```
PROVENANCE (G-2, corrected): x²+x+1 and x³+x+1 ARE the Conway polynomials
C_{2,2}/C_{2,3}; x²+1 over F₃ is NOT the Conway polynomial (C_{3,2} =
x²+2x+2) — it is simply AN irreducible (−1 a non-square mod 3), which is all
the census needs; the rev-2 "standard Conway-polynomial tables" claim is
struck. These make V6-1c/V6-3b decide-native at q = 4, 8, 9 — the census is
the note's NINE points in-kernel, and the char-2/char-3 finite-field behavior
(not polynomial interpolation) is what is checked, as the seal demands.

**`CoprimeLiftPack` — CLOSED at REV 3 (Codex-18: rev 2's `…`/`monic …`/
`reduce`/`hOf` were unspecified). It states EXACTLY unique coprime lifting +
coefficient determinacy, nothing stronger; determinacy of `hOf` is now BY
TYPE (it consumes only f mod 2^k):**
```lean
/-- reduction mod 2 of a mod-2^k polynomial (the one cast this pack uses). -/
def reduce2 (k : ℕ) (hk : 1 ≤ k) :
    Polynomial (ZMod (2 ^ k)) →+* Polynomial (ZMod 2) :=
  Polynomial.mapRingHom (ZMod.castHom (dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hk)) (ZMod 2))

structure CoprimeLiftPack where
  hOf : ∀ (k : ℕ), Polynomial (ZMod (2 ^ k)) → Polynomial (ZMod (2 ^ k))
    -- the designated lifted factor; a FUNCTION of f mod 2^k BY TYPE —
    -- rev 2's separate `determined` field is subsumed (recorded)
  lift_unique : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ū h̄ : Polynomial (ZMod 2)) (hcop : IsCoprime ū h̄)
    (hmh : h̄.Monic) (hfac : reduce2 k hk f = ū * h̄),
    ∃! uh : Polynomial (ZMod (2 ^ k)) × Polynomial (ZMod (2 ^ k)),
      uh.1 * uh.2 = f ∧ uh.2.Monic ∧
      reduce2 k hk uh.1 = ū ∧ reduce2 k hk uh.2 = h̄
  hOf_spec : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ū h̄ : Polynomial (ZMod 2)) (hcop : IsCoprime ū h̄)
    (hmh : h̄.Monic) (hfac : reduce2 k hk f = ū * h̄),
    (∃ u, u * hOf k f = f) ∧ (hOf k f).Monic ∧ reduce2 k hk (hOf k f) = h̄
    -- hOf picks THE unique monic factor over h̄ whenever one exists
```
Mathlib-first (`Polynomial.hensel`-adjacent archaeology at E-phase); if the
exact form is missing it becomes a DECLARED published-axiom candidate per
campaign §4 — flag at E-phase, do NOT silently strengthen; it remains a typed
premise of V6-4c either way (never an unconditional Lean axiom).

### 2.J The no-placeholder checklist (C29/Codex-18 closure, REV 3)

Every carrier either round named as a placeholder now has a displayed CLOSED
home: `inv` DELETED (§2.B note) · `TargetIx` §2.C (inductive) ·
`MoveData`/`TermData` §2.C (structures; `src`/`tgt` defs — tcell-enforced) ·
`dataOf`/`dataOfT` (the inverses of `moveOf_bij`/`moveOfT_bij`, derived
noncomputable defs — one line each at V7-4a) · `HMCAug` §2.G (body +
`Refinement` fully typed: moveProj/dim_eq/assignOf/mass_eq/assign_cover;
`count_proj`/`count_cover` are now LEMMAS) · `XHDdSh` → `XHDdEnt` §2.G (+
`lands_of_realizable`) · `XHDdC` §2.G (new) · `AffEnt` §2.G (dependent
codomain explicit) · `CellPolyPack` §2.H (closed, domain-keyed, no
ellipses) · `ObsCheck` §2.G (over `BlockData.evalObs`) · `CofinAct` §2.G ·
`moveOf`/`moveOfT` §2.F (fields + bijection laws, targets enforced) ·
`Realizable` §2.G · `CtsmConclusions` V7-2a (a CLOSED structure declaration,
one `*_Stmt`-typed field per deliverable) · `EligPair`/`IsBranchingRead`/
`branchMenuCard` §2.D (closed defs keyed to NAMED MovesD declarations:
`ShapeRead.len`/`.mbar`, `E5_gmuLe`, `eligible_card_le`, `selRank`,
`E8_rankInj`) · `writeHeights` §2.D (displayed fold via `readOfLetter`;
slots/zig/gamTie encoding pinned) · `Hpt.take/drop/append` §2.A (closed
defs) · `IsPP` §2.A · `CoprimeLiftPack` §2.I (closed; `reduce2` displayed;
determinacy BY TYPE) · `F4/F8/F9` §2.I (tables displayed; Conway claim
corrected) · `emult` §2.F (a CtsMeasured FIELD — rev 2 called it a def over
data the carrier did not have) · `AStep`/`evtOfStep` §2.F (closed Σ-carrier
defs) · `zig` §2.D (Mathlib's `Denumerable.eqv ℤ`) · `StageLawBurden` V7-3d ·
`Wsh17PackageV` V7-7 (a displayed TYPE). Residual E-phase freedom: NONE
declared — the `castMove/castHpt/castAssign` transport helpers (§2.G) and
the F8/F9 table literals are mechanical one-liners with zero design content.

## §3 The unit DAG — 82 units (33 easy / 43 medium / 6 hard)

Format per campaign §2: id `MovesV.<name>` · file · statement (against §2
Defs) · moves_ref (V-TABLES display, ≤ 3 lines) · deps · sketch · difficulty ·
hypothesis_fields (which open kernels ride — NEVER silently strengthened or
dropped). FORMAT AMENDMENT (C28 repair): a unit is ONE FILE with an
ENUMERATED LEMMA ROSTER (≤ 4 lemmas; each lemma one display); units whose
rev-1 spec concealed several declarations now display their rosters (V0-2,
V2-1, V2-2, V6-4a). Pre-approved splits are marked ⌿.

### Layer V0 — height apparatus [4]

**V0-1 `affine_pos` · `V0_affine.lean` · easy.**
`theorem affine_strictMono {D} (E : AffineE D) (h : Hpt D) (i : Fin D) :
StrictMono (fun t => E.eval (Function.update h i t))` + `theorem
affine_ge_const (E : AffineE D) (h : Hpt D) : E.const ≤ E.eval h` (h now
BOUND — A-7 repair). moves_ref: "E affine in h with positive weights" (XHD-w).
deps: Defs. sketch: sum manipulation; `Finset.sum_le_sum`. hyp_fields: none.

**V0-2 `linset_mem_iff` · `V0_linset.lean` · easy.**
ROSTER (3 — C28): (a) `linset_mem_iff` normal-form membership; (b)
`linset_base_mem : L.Mem L.base` (c := 0); (c) `linset_add_period` closure
under adding one period. moves_ref: "L(h₀; P) := {h₀ + Σ n_v·v}".
deps: Defs. sketch: definitional; `Fin.sum` lemmas. hyp_fields: none.

**V0-3 `semilin_sum_exact` · `V0_partition.lean` · medium.**
For `S : SemilinPart D`, `f : Hpt D → ℝ` with `0 ≤ f`, and per-component
`HasSum (f ∘ incl_j) (v j)`: `HasSum (f ∘ incl_{S.Mem}) (Σ_j v j)`.
moves_ref: "the finitely many component sums ADD EXACTLY to the H(γ)-sum —
no overlap terms exist (rev 3)". deps: V0-2.
sketch: induction on comps; `HasSum` over a disjoint union of subtypes
(`hasSum_subtype_iff` + disjointness field); nonneg gives summability
transfer. hyp_fields: none (the disjointness is a TYPE field of SemilinPart).

**V0-4 `xhds_instance_A2` · `V0_xhds_witness.lean` · medium ⌿ — RE-KEYED (C3).**
THE NON-DEGENERACY WITNESS for the XHD-s format (doctrine: packages must be
non-degenerately instantiable), now stated IN THE (t,u) CHART where `EA2`
lives: `HasSum (fun h : {h // A2dom.Mem h} => (q₀:ℝ)^(-(EA2.eval h.1 : ℤ)))
((evalAt q₀ ⟨GA2, _⟩ : ℚ) : ℝ)` for every prime power q₀ > 1, where
`GA2 : Qq` = the cleared form `X²/((X⁶−1)(X³−1))` — denominators in the
PolyGeom class. Base value: EA2.eval ![1,0] = 7 (the seal's E at (4,1)).
moves_ref: "HEIGHT DOMAIN … the ONE linear set L((4,1); {(3,1), (2,0)}) …
E = (3(h₀+h₂)−1)/2 — affine, positive weights" + "h₂ = t ≥ 1, h₀ = 3t+2u+1"
(V.6.2; the (t,u) form E = 6t+3u+1 is OUR derivation — G-1: never spliced
into the quotation again).
deps: V0-2, DefsGate (EA2/A2dom are (t,u)-native, so no V6 dependency — the
V0 layer stays before V6 in the build order; the (h₀,h₂) display is
V6-2a/b's downstream theorem). sketch: E = 6t+3u+1 over
t = 1+a, u = b: q^{−7}·Σ q^{−6a}·Σ q^{−3b}; product of two geometric series
(`tsum_geometric_of_lt_one`, `HasSum.mul`); match the cleared rational form
at eval. ⌿ split: (a) the double geometric sum; (b) the Qq clearing identity.
hyp_fields: none — a PROVED instance. [No half-integral arithmetic exists
anywhere in this unit: the (h₀,h₂) display is V6-2a/b's chart theorem.]

### Layer V1 — the XHD packages + (U-A) [10]

**V1-1 `xhdw_range` · `V1_xhdw.lean` · easy.**
`theorem xhdw_pos (X : XHDw n S) … : 0 < X.g m h q₀` and `X.g m h q₀ ≤ 1`
at pools (q₀ > 1, E ≥ const… state `0 <` and `≤ q₀^(−E.const)`).
moves_ref: "a FIXED-HEIGHT weight monomial g = q^{−E(h)}".
deps: Defs, V0-1. sketch: `zpow` monotonicity. hyp_fields: consumes XHDw as
an ARGUMENT (owner [2b]); proves only its numeric range.

**V1-2 `xhdu_rect_sum` · `V1_xhdu.lean` · easy.**
ROSTER (2): (a) GIVEN (u-T)'s constant count:
`∑ h ∈ Hfin, (cnt h : ℝ) * g h = (T:ℝ) * ∑ h ∈ Hfin, g h` when
`∀ h ∈ Hfin, cnt h = T`; (b) `xhdu_rect_false`, the "else false in general"
witness: a concrete `cnt` non-constant on a two-point H with
`Σ cnt·g ≠ cnt(h₀)·Σ g` (norm_num instance).
moves_ref: "Σ_h T(h)·g(h) = T·Σ_h g(h) is EXACTLY (u-T), else false in
general" ((iv) STEP). deps: Defs. sketch: `Finset.sum_congr` + `mul_sum`;
norm_num. hyp_fields: none (the premise is the (u-T) instance, explicit).

**V1-3 `xhdd_exact_supp` · `V1_xhdd.lean` · easy.**
GIVEN XHDd: `(D.dom γ).Mem h ↔ ∀ x, 0 < chainCount S γ x h` at inhabited
`Hist α` (both directions from no_orphan/no_stray + `hist_ne`) — now over
the DEFINED count (C2). moves_ref: "(no orphan) … ⟹ h ∈ H(γ); (no stray)
h ∈ H(γ) ⟹ … EVERY representative". deps: Defs. sketch: unfold;
`Nonempty.elim`. hyp_fields: XHDd argument (owner [2b]).

**V1-4 `xhds_eval_nonneg` · `V1_xhds.lean` · easy.**
GIVEN XHDw/XHDd/XHDs: each `Gc γ j` evaluates ≥ 0 at pools (limit of a
nonneg-term sum via `Gc_hasSum` + V1-1). moves_ref: "convergent at every
prime power evaluation (positive weights)". deps: V1-1.
sketch: `HasSum.nonneg`. hyp_fields: XHDw/XHDd/XHDs arguments.

**V1-5 `xhd_discharge` · `V1_discharge.lean` · easy.**
`def IsFullDischarge (n S C V) : Prop := Nonempty (XHD n S V)` + the RECORD
lemma `theorem cond_of_discharge : IsFullDischarge … → ∀ {P : XHD … → Prop},
(∀ X, P X) → ∃ X, P X` — the [1v]-FULL bookkeeping shape: discharge =
INHABITATION of the package, "no new mathematics"; every measured unit keeps
its explicit `XHD` argument. moves_ref: "[1v]-FULL := the RECORDED DISCHARGE
of the XHD hypotheses upon [2b]'s acceptance — a bookkeeping event" (V.0).
deps: Defs. sketch: trivial. hyp_fields: none (typing unit). [Deliberately
NOT `True`-valued; no unit may replace its XHD argument by this Prop.]

**V1-6 `UA_fixed_history` · `V1_UA.lean` · medium.**
(U-A) AS THE NOTE PROVES IT — this corpus's ONE §C-derivable clause:
`theorem UA (P : C15Pack n S) {α β} (m : S.Move α β) (x : S.Hist α)
(hzc : S.zc x) (h : Hpt (S.dim m)) (a a' : S.Assign m x h) (q₀ ∈ S.Pools) :
S.massOf m x h a q₀ = S.massOf m x h a' q₀`.
moves_ref: "Fix ONE realizable prefix satisfying (ZC) … BOTH factors are
functions of the read's NOMINAL DIGIT INVENTORY … Hence all fresh assignments
realizing (m, o, β) at h FROM THAT PREFIX carry one common conditional
mass. ∎" (V.0 (U-A)). deps: Defs (C15Pack).
sketch: two `mass_factors` rewrites; both sides = `F (invOf m x h) q₀`.
hyp_fields: `C15Pack` (owner §C/HC-2 — the typed C.1.5(1)+TYP(b) supply; the
PROOF is unconditional given the pack, exactly the note's GIVEN).

**V1-7 `ua_split_fence` · `V1_fence.lean` · medium.**
THE HONEST-SPLIT WITNESS, display Prop-corrected (A-7): `theorem ua_fence :
∃ S : StepSys n, ∃ _P : C15Pack n S, ¬ (∀ {α β} (m : S.Move α β) x x' h a a'
(q₀ …), S.massOf m x h a q₀ = S.massOf m x' h a' q₀)` — nested existentials,
no Type-as-conjunct. moves_ref: "NOT §C-derivable, HYPOTHESIZED in (XHD-u)
(they are lumpability assertions about histories §C never compares)" (V.0).
deps: Defs. sketch: two-history toy model, F distinguishing inventories;
norm_num. hyp_fields: none — a machine-checked record that (XHD-u) is not a
consequence of the pack (the inverse-defect discipline).

**V1-8a `stepsys_realized` · `V1_witnessA.lean` · medium — SPLIT (Codex-19).**
THE STEP-SYSTEM WITNESS: ONE concrete finite `StepSys` instance (two cells,
one continuing move with dim 1 + one terminal move, listed one-component
domain, `Assign x h := Fin 1` on the domain and `Empty` off it, `ext` the
evident map) which INHABITS, non-degenerately, `StepSys` (all non-vacuity
fields incl. the REV-3 productivity `out_ne`), a `C15Pack` (incl. the T-twin
fields), an `XHDw` (E = h + 1), an `XHDu` (incl. T-twins). moves_ref: the
V.0 package displays (each quantifier realized at a true instance).
deps: Defs. sketch: decide/norm_num. hyp_fields: none — a PROVED instance.

**V1-8b `xhdds_realized` · `V1_witnessB.lean` · medium — SPLIT (Codex-19).**
Over V1-8a's instance: an `XHDd` (exactness holds BY the count def) and an
`XHDs` (one geometric sum — the V0-4 pattern at dim 1). moves_ref: (XHD-d)/
(XHD-s) displays. deps: V1-8a, V0-4's pattern. sketch: one geometric series.
hyp_fields: none — a PROVED instance.

**V1-8c `measured_faces_realized` · `V1_witnessC.lean` · medium — SPLIT
(Codex-19).** Over a one-cell/one-template `CtsMeasured` toy on the same
system (incl. the REV-3 census/tie fields: entInst/ent_card/box_card/
evt_card/stInst_card realized by explicit finite data): the faces
`XHDdC`/`XHDsC`/`XHDsEnt`/`XHDdEnt`, hence the FULL bundle `XHD`.
moves_ref: the V.0 package + V.1(iii)/(iv) faces. deps: V1-8b, Defs 2.F/2.G.
sketch: decide + one geometric series; the census data is a literal.
hyp_fields: none — a PROVED instance; together with V1-7's failure witness
V1-8a/b/c bracket the packages (satisfiable, not vacuous; not §C-implied).

### Layer V2 — state space + tables [10]

**V2-1 `skeleton_menu` · `V2_skeleton.lean` · easy.**
ROSTER (2 — C28): (a) `letter_menu_out (B : BlockData n s) (m) :
B.letterSp m ∈ MovesSp.Out n s.sp` (projection); (b) `skeleton3_finite :
Set.Finite {s : Skeleton 3 | True}` via `SnRaw` finiteness (SP2/SP6, the
53-catalogue). moves_ref: "Out(s) := the finite p-INDEPENDENT SYNTACTIC menu
… ([2a] SP-OUT + M1 bookkeeping ALONE, evaluated over NO residue field)"
(CTS-S). deps: MovesSp.SP2_finThm, Defs. sketch: image of a finite set.
hyp_fields: none — the note's "[2a] pending" inheritance is DISCHARGED
against the PROVED MovesSp (recorded upgrade, §0).

**V2-2 `cellidx_delete` · `V2_cells.lean` · easy.**
ROSTER (3 — C28): (a) `def BlockData.CellIdx (B) := {a : ∀ g, (B.gen g).idx
// B.sizeP a ≠ 0}`; (b) `instance : Fintype B.CellIdx`; (c) `deleted_empty`:
deleted cells have empty fibers at every prime power (`size_count` + eval 0
⟹ card 0). moves_ref: "cells with IDENTICALLY-zero size polynomial are
deleted from 𝒞_n once, symbolically" (CTS-S). deps: Defs.
sketch: subtype Fintype; card = 0 from ℚ-cast. hyp_fields: none.

**V2-3 `meet_finite_uniform` · `V2_meet.lean` · medium.**
Clause (i)'s proved core: the product-of-generators cell map
`x ↦ (fun g => (B.gen g).part q₀ x)` induces a finite partition of
`Carrier q₀` with p-independent label set `∀ g, idx g`; fibers are pairwise
disjoint and exhaustive; refines EVERY generator.
moves_ref: "the meet of finitely many finite uniform partitions is finite and
uniform, and labels are fixed by (D2)/(D3)'s conventions" (V.3(i)).
deps: V2-2. sketch: fibers of a total map partition the domain; `Fintype.pi`.
hyp_fields: none. [The note's conditionality of clause (i) on the UNCOMPUTED
skeletons is the `BlockData`-per-skeleton ARGUMENT — clause (i) at full depth
is `∀ s, BlockData n s → …`, never "proved by construction" bare.]

**V2-4 `val_a_burden` · `V2_valA.lean` · easy (statement-shape unit) —
RE-KEYED (Codex-4: rev 2's `tbl_count` was BOTH too weak — guarded by
`0 < cntraw`, silent at zero-count entries — AND too strong — realized-height
equality smuggled (u-T), which the note assigns to (XHD-u), into VAL(a)).**
`structure ValA (n) (C : CtsFamily n) (S) (V : CtsMeasured n C S) : Prop`
with fields: (a) `tbl_count : ∀ (d : MoveData n C) (β) (x : S.Hist _)
(hzc : S.zc x) (q₀ ∈ V.Pools) (j : Fin (V.mdom d).comps.length),
((C.T d.s d.m d.o d.α β).eval q₀ : ℚ) = S.cntraw (V.moveOf d) x
(((V.mdom d).comps.get j).base)` — the polynomial valued at the count AT THE
LISTED BASE POINTS of the one-step domain, ∀ representatives, UNGUARDED:
· at an entry inadmissible at q₀ the base counts are 0, so the law FORCES
  T.eval q₀ = 0 (horn (i) closed — it says something at zero counts);
· NO height-uniformity is entailed: the polynomial is pinned only at base
  points; its validity across each component is EXACTLY (u-T)'s content,
  cited where consumed (V4-5, V2-5) — horn (ii) closed. Representative-
  uniformity stays (the note's own alternative discharge: "the table build
  proves representative-uniform count rows per species").
(+ `tbl_countT`, the [+T] twin over mdomT/cntrawT);
(b) the size ties (`size_deg`/`size_count`-keyed, already TYPE);
(c) `tgt_supported : ∀ …, ¬ V.activeState q₀ β → S.cntraw (V.moveOf d) x h
= 0` — "a landing forces a concrete target state", the count-level landing
tie; (d) NEW at REV 3 (Codex-15): `ent_supported : ∀ (ε : EntShapeV n) (β₀)
(q₀ ∈ V.Pools), ¬ V.activeState q₀ β₀ → V.entCensus ε β₀ q₀ = 0` — the SAME
landing sentence at the entrance layer ("… and ι of (iii) is supported on
Act_{q₀}", V.1(ii-a)) — V4-1's iota_supp is now derivable, not free.
+ `theorem valA_gate : ValA 3 gateFam gateMeas` DEFERRED to V6.
moves_ref: "(a) LOCAL: every entry T_{m,o}^{α,β} is ONE polynomial in ℚ[q] of
degree ≤ W_loc(m), and every cell size |α| ONE polynomial of degree ≤
W_state(s), each valued correctly at every prime power q" (Thm VAL) +
"(ii-a) NO-ENTRY … and ι of (iii) is supported on Act_{q₀}" (V.1(ii)).
deps: Defs. sketch: structure decl + gate pointer. hyp_fields: the count ties
are per-skeleton TABLE-BUILD burdens (CL-13/V.5(4)) — open beyond the V.6
blocks, stated as the structure.

**V2-5 `val_b_chain` · `V2_valB.lean` · medium — RESTATED (C2/C9).**
Theorem VAL(b) GIVEN (XHD-u)'s count face, over the DEFINED `chainCount`
(no free chain data, no missing tie field — the recursion is definitional):
ROSTER (3): (a) `chain_resolved (U : XHDu n S) {α} (γ) (x) (h) :
chainCount S γ x h = hProd γ h` where `hProd γ h := ∏ᵢ cnt_i(hᵢ)` with each
factor state-only (well-defined by u_R_cnt) — pure induction on γ through
`ext` (base = cntraw def; cons = `Fintype.sum_const` after IH + u_R_cnt at
the extended histories); (b) `valB (hVA : ValA n C S V) (U : XHDu) (D : XHDd)
(hzc : S.zc x) (q₀ ∈ V.Pools) (hmem : (D.dom γ).Mem h) :
(chainCount S γ x h : ℚ) = (pathProdPoly C γ).eval q₀` — REV 3 (Codex-4's
V2-5 leg): the path product is now THE TABLE POLYNOMIALS' product,
`pathProdPoly C γ := ∏ᵢ C.T (step-i data of γ) (its TargetIx)` (a displayed
def of this file over `dataOf`), CONNECTED to ValA and evaluated at q₀ —
from (a), replace each realized cnt_i(hᵢ) by the common value via u_T
(realized-ness from no_stray's positivity, projected per step along the
witnessing chain), then value each step by `tbl_count` at its base point
(u_T carries base ↔ hᵢ); terminal factor via the [+T] twins;
(c) `pathProd_deg : (pathProdPoly C γ).natDegree ≤ W γ` —
the degree bound RE-SCOPED (C9): it is a POLYNOMIAL-degree statement about
C_γ(q) = ∏ T given ValA's `T_deg` (Σ W_loc arithmetic), NOT a counting
inequality with no hypotheses. moves_ref: "(b) CHAIN — GIVEN (XHD-u)'s COUNT
FACE …: the PER-REPRESENTATIVE linked count from one fixed source
representative EQUALS the PATH PRODUCT C_γ(q) = ∏ T" (Thm VAL).
deps: Defs, V1-2, V2-4 (for (c)). sketch: as per roster.
hyp_fields: XHDu + XHDd (owner [2b]); "never proved here" — the unit derives
the equality FROM them, matching "hypothesized in (XHD-u), never proved here
(alternative discharge: the table build proves representative-uniform count
rows per species)".

**V2-6 `exp_audit_pow` · `V2_audit.lean` · medium.**
The EXPONENT-MAP AUDIT's worked law: for a finite field F with `|Fˣ| = m`,
the image of `t ↦ t^a` on `Fˣ` has cardinality `m / gcd a m`.
moves_ref: "e.g. the image size of t ↦ t^a on F_{q^g}ˣ is
(q^g − 1)/gcd(a, q^g − 1)" (EXPONENT-MAP AUDIT).
deps: none (Mathlib: `IsCyclic`, `powMonoidHom`, index/range card).
sketch: cyclic Fˣ; image of power map = unique subgroup of order m/gcd.
hyp_fields: none. [The AUDIT as a duty — "each such factor either cancels
against a displayed cell-size factor or splits the cell" — is a FIELD of the
table-build structure `AuditedEntry` in this file: per entry, a proof term
`cancels ⊕ splits`, consumed by V2-4's gate instances.]

**V2-7 `val1_worked` · `V2_val1.lean` · medium — CELLS CORRECTED (Codex-12:
rev 2's FL = {y = 0} and FS = {x = 0} both contained (0,0) and overlapped —
not the displayed disjoint strata).** The VAL.1 worked instance, stated
generically: F a field, `V : Fˣ × Fˣ → F × F`, `V (A, B) = (A, B)` in the
basis coordinates (the note's V(A,B) = Aα + B read in the basis {α, 1}).
ROSTER (2): (a) the THREE cells AS THE NOTE DISPLAYS THEM —
FG = {x ≠ 0 ∧ y ≠ 0}, FL = {x ≠ 0 ∧ y = 0} (= F_qˣ·α: the nonzero
coordinate REQUIRED), FS = {x = 0 ∧ y ≠ 0} (= F_qˣ) — are pairwise disjoint
and partition the NONZERO target (F×F) \ {(0,0)} (the target t = xα + y of
a value map into F_{q²}; the origin is no cell's member and carries fiber
count 0 — stated as its own lemma, outside the three-cell partition);
(b) the fiber count is 1 on FG, 0 on FL, 0 on FS — c_V constant per cell.
moves_ref: "Worked instance (V(A,B) = Aα + B …): THREE cells — FG =
{x ≠ 0, y ≠ 0}, c_V = 1; FL = F_qˣ·α (y = 0), c_V = 0 (B = 0 prohibited);
FS = F_qˣ (x = 0), c_V = 0 (A = 0 prohibited)" (VAL.1).
deps: none. sketch: coordinates are literal; fiber = {(x,y)} iff both
nonzero, else empty (A = 0/B = 0 prohibited by Fˣ). hyp_fields: none.

**V2-8 `anchor_twist_fence` · `V2_anchor.lean` · easy — RESTATED (C10).**
ANCHOR ALIGNMENT, now STRUCTURAL (the type does the fencing): ROSTER (2):
(a) `anchor_twisted (G : GenSpec Carrier) (ha : G.kind = .anchor a_eff) :
∀ q₀ x, G.part q₀ x = G.base q₀ (G.twistOf q₀ a_eff x)` — at a_eff ≠ 0 the
cells apply to the TWISTED target and NEVER directly to the fixed frame
(the partition map factors through the twist BY the `part_eq` field; there
is no un-twisted access to `part`); (b) `anchor_zero : G.kind = .anchor 0 →
G.part = G.base` (via `twist0`) — the a_eff = 0 collapse, now a corollary
not the content. moves_ref: "at anchor exponent a_eff ≠ 0 the cells apply to
the TWISTED target α^{−a_eff}·t, never to t in the fixed frame — fixed-frame
cell counts are PROVABLY char-dependent (the value probe …)" (VAL.1).
deps: Defs 2.C. sketch: field projections. hyp_fields: none. [The
char-dependence refutation itself is the Python probe's, cited as evidence —
no Lean claim.]

**V2-9 `deg_cons_gate` · `V2_degcons.lean` · easy.**
DEG-CONS at the computed rosters: for the V.6 gate family's outcome rosters,
every m ≥ 2 outcome has per-member sizes e_j ≥ 1 with Σ e_j ≤ e — by
`decide` over the DefsGate lists; PLUS the shape lemma producing
`MovesS.DegCons gateTS` for V7-3b. moves_ref: "DEG-CONS … m ≥ 2 children,
each child cluster size e_j ≥ 1, Σ_j e_j ≤ e — per member … The check runs
over the FULL roster of each computed table block" (V.2).
deps: DefsGate. sketch: decide. hyp_fields: none at the gate blocks; the
full-roster check at other skeletons is CL-11's burden (typed as the ValA-
style structure field, open).

**V2-10 `wloc_wstate_split` · `V2_bounds.lean` · easy — RESTATED (C11).**
The SPLIT-bound fence, examples now matching the claims: ROSTER (2):
(a) `gate_bounds`: the gate data's actual values RECORDED with their true
directions — root: Wstate = 0 < Wloc = 3; s_blk2: Wstate = 1 < Wloc = 2
(norm_num; these illustrate sizes and table degrees living on DIFFERENT
keys); (b) `wstate_gt_wloc_consistent`: an explicit SYNTHETIC `CtsFamily`
instance (one skeleton, sizeP = X so Wstate = 1; one letter with constant
entry T = 1 so Wloc = 0) witnessing `Wstate s > Wloc s m` — the note's "may
exceed some W_loc(m)" possibility, now witnessed in the CORRECT direction
(rev 1 cited two gate examples that both satisfy the opposite inequality).
moves_ref: "(SPLIT bounds — a source-cell size belongs to (s, α), not to any
outgoing m, and may exceed some W_loc(m))" ((iv)-POLY). deps: DefsGate.
sketch: norm_num + a two-line instance. hyp_fields: none.

### Layer V3 — entrance shapes + clause (iii) [11]

**V3-1 `entshape_postsplit` · `V3_eps.lean` · easy — RE-SCOPED (Codex-5:
rev 2's (b) claimed a derivation the fields cannot give).**
POST-SPLIT TYPING: ROSTER (2): (a) injectivity of the label in the σ_sel
coordinate (two `EntShapeV` differing in `selRec` are ≠ — trivial, but it is
what the LABEL layer owns); (b) the SEMANTIC LEG, correctly keyed: σ_sel's
entries ARE the L11 ranks (`MovesD.selRank` — the §2.D semantic pin), and
DISTINCT designated ψ-selections at a branching read have DISTINCT ranks by
MovesD's PROVED `E8_rankInj` — stated as the instance-layer lemma "two
entrance CUTS (2.E) induced by different selections at read i produce labels
with different selRec i-entries", citing E8_rankInj, never re-deriving it.
The note's "siblings … differ in s_r" is the CONJUNCTION (a) + (b).
moves_ref: "siblings at a shallow split differ in s_r, hence carry DISTINCT
ε — ι never aggregates a pre-split f-event or a joint-sibling locus"
(V.3(iii)) + "σ_sel = (s_r … — L11's encoding data, lifted into the label)".
deps: Defs 2.D/2.E, MovesD.E8_rankInj. sketch: structure injectivity +
rank-injectivity transport. hyp_fields: none.

**V3-2 `hent_proj` · `V3_hent.lean` · easy.**
h_ent is a PROJECTION: `hent` is a function of ε (definitional), determined
by `Phat` alone; + the non-degeneracy law: two ε with same template but
different read-heights have different `hent` (heights are RETAINED, not
quotiented). moves_ref: "h_ent(ε) := the tuple of ε's RETAINED height data —
… a FUNCTION of ε, displayed, no free height variable anywhere" (V.1(iii)).
deps: Defs. sketch: `List.map` congruence + a two-read discriminating
instance. hyp_fields: none.

**V3-3 `spword_bridge` · `V3_spword.lean` · HARD — EXTENDED (A-3; + REV 3
leg (d), the Codex-6 reconstruction bridge; ⌿ pre-approved split by leg).**
ROSTER (4): (a) `def spWord (n) (P : MovesD.ShapePrefix) : List
MovesSp.Species` (fold of the stage laws along `P.reads`) + its law:
consecutive outputs satisfy `MovesSp.SuccStep` when the reads satisfy
MovesD's `ShapeWF` stage clauses; (b) the COLLAPSE law: `EntShapeV.template`
lands in `EntTemplate` (the collapsed word is a `CollapsedWalk`; entry/menu
WF fields transported from ε's §2.D ties); (c) the ENTRANCE-SHAPE BRIDGE:
from (ε̊, h) construct the `MovesSp.EntranceShape n gsel musel` behind it
(word + hMem + hChain + hEntry from ε̊'s fields; heights h into the slot
functions) — the §1 consumption tie A-3 demanded; (d) RECONSTRUCTION
(NEW — Codex-6's lossiness horn + G-3): `readOfLetter` (species letter +
(h-slot, u*-code slot) + the WF prefix-so-far ↦ the unique WF `ShapeRead`
with those data — e/g/μ/s0/wSide/Dwidth/w from the letter's stage fields and
the WF chains (width chain, wchain), ustar via zig + `gamTie`'s inversion,
a/gam via `anchorTie`/`gamTie`) and `spWord_faithful`: two shallow WF
prefixes with equal collapsed spWord, equal height/depth/u*-code slots are
EQUAL — i.e. SP.1 genuinely forgets ONLY heights, realized as a THEOREM from
the two corpora's WF laws. THIS is the load-bearing leg of V3-5's bijection;
ESCALATION HATCH recorded at §2.D (if a datum is genuinely lost, the
template gains it as a field, with a fresh audit — never silently).
moves_ref: "ε̊ := ε's height-forgetting TEMPLATE (SP.1 applied to P̂,
selection data kept)" (V.1(iii)) + L3 rev 9 (retained (h, u*)).
deps: MovesD.Defs (gamTie/anchorTie/wchain), MovesSp.Defs.
sketch: structural recursion over reads; match `ShapeRead` fields (e, g, μ,
species tags) to `Species` stage fields via the D.5/D.7/D.8 output laws both
corpora carry; (d) inverts the same laws. hyp_fields: the ShapeWF
certificate (MovesD's, PROVED apparatus) — no open kernel.

**V3-4 `template_finite` · `V3_tfin.lean` · medium — RESTATED (C12/A-3).**
The template family is FINITE, OUTRIGHT AND UNCONDITIONALLY (no `WordBounded`
premise exists — the boundedness is §2.D's intrinsic WF fields):
`theorem template_finite (n) : Finite (EntTemplate n)` (n = 3 build target;
stated for the n the corpus fixes). moves_ref: "the family {ε̊} is FINITE
([2a]/M1 for the P̂-templates; L5's finite eligible-continuation menus for
the σ_sel's)" (V.1(iii)). deps: V3-3, MovesSp.SP2_finThm.
sketch: `hWalk` words are collapsed SuccStep walks over the finite SP2
catalogue; `rankNat` strictly increases along collapsed edges (the
SP4_dagWords idiom — at n = 3 decidable over the 53-catalogue), bounding
word length; words of bounded length over a finite alphabet are finite;
`hlen`/`hmenu` bound selRec (length by the word, entries by the L5 menus);
(gsel, musel) bounded via `hEntry` + the catalogue's finite sel field.
hyp_fields: NONE (this was C12's silent-weakening finding: the note asserts
finiteness from [2a]/M1 + L5, and the Lean statement now proves exactly
that, quantifier unmoved).

**V3-5 `inst_bijection` · `V3_instbij.lean` · HARD.**
The rev-4 INSTANTIATION BIJECTION, GIVEN the entrance exactness face:
`theorem inst_bij (DE : XHDdEnt n S V) (ε̊ : EntTemplate n) (β₀)
(hl : V.entLands ε̊ β₀) : ∃ e : {h // (V.entDom ε̊).Mem h} ≃
{ε : EntShapeV n // ε.template = ε̊ ∧ Realizable V ε β₀},
∀ h, (e h).1 = writeHeights ε̊ h.1` — "write the heights h into the
template's retained slots" (`writeHeights`, the §2.D def) is a BIJECTION
from H(ε̊) onto the concrete realizable ε with that template.
moves_ref: "the INSTANTIATION MAP h ↦ ε̊[h] … is a BIJECTION from H(ε̊) onto
{concrete ε with template ε̊} — D4R.1-SUM is cited ONLY at concrete ε"
(V.1(iii), pass-3 F1's two horns). deps: V3-3, V3-4, Defs 2.D/2.G.
sketch: injectivity = V3-3(d)'s `spWord_faithful` (heights + u*-codes
determine the reads given the template — the REV-3 reconstruction leg, no
longer hand-waved); surjectivity = no_strayE realizability +
template-matching through readOfLetter; `Realizable` is the DISPLAYED §2.G
def (entrance-event nonemptiness at stabilized levels); membership in EntIx
via `lands_of_realizable` (the REV-3 XHDdEnt field — Codex-6's landing
horn). ⌿ pre-approved split: (a) injectivity; (b) surjectivity; (c) the
writeHeights-computation law (incl. the zig/gamTie roundtrip).
deps += V3-3(d). hyp_fields: XHDdEnt (owner [2b] — the shallow-layer XHD-d
face, now with the landing law).

**V3-6 `iota_muhat` · `V3_iota.lean` · medium — RESTATED (C13).**
ι's typing laws, the FALSE IFF STRUCK: ROSTER (3): (a) `iota_le_total`:
`iotaCount ε cut S ≤ Σᶠ i, Nat.card (S.fiber i)` (a SUB-SUM of D4R.1-SUM's
index); (b) `iota_eq_of_total`: IF `lands` is total THEN equality — ONE
direction only (rev 1's converse is FALSE: excluded indices may have empty
fibers; C13); (c) `iota_d10_tie`: the D4R.1-SUM tie at stabilized levels —
each summand's fiber card × p^{A'} = p^{nN}, via the EXPORTED
`MovesD.D4R1_SUM` + `MovesD.D0b_thmCtop` (G-4 repair: rev 2 cited "D10's
`key`", a proof-internal `have` in `D10_sumLaw.lean`, not a consumable).
This tie is also what discharges `CtsMeasured.ent_card` at the real
instance. moves_ref: "ι_{e,ε,β₀}(p) := the D4R.1-SUM MARKED mass μ̂ of the
entrance family refined by ε (each summand Theorem C(b); an f entering twice
carries two marks — a μ̂-object, never an f-event mass)" (V.1(iii)).
deps: MovesD.D10_sumLaw, Defs 2.E. sketch: `finsum` over a subset ≤ total;
per-summand D10.key. hyp_fields: `S.jet` (MovesD's presented-jet field, as in
D10); the `lands` cut (§D4-R L5 cell data — a parameter with its (D4)-tie).

**V3-7 `ent_agg_finite` · `V3_aggfin.lean` · medium.**
ENT-AGG's hypothesis-free half: for FINITELY many pairwise-distinct concrete
ε (distinct marked pairs), the refined counts ADD:
`iotaCount` over a disjoint union of cuts = Σ of `iotaCount`s
(μ̂-additivity over disjoint mark families).
moves_ref: "The primitives and every FINITE partial sum are hypothesis-free
(μ̂-additivity over disjoint mark families — distinct concrete ε give
distinct marked pairs)" (V.1(iii)). deps: V3-6, V3-1.
sketch: `finsum_mem_union` on disjoint index sets. hyp_fields: none.

**V3-8 `ent_agg_full` · `V3_aggfull.lean` · medium — RE-KEYED at REV 3
(F-1/Codex-8: the summand is the CORRECTED ιshH — census·q^{−A} — and the
package face is weight-only, so the count constancy that resummation uses
is now the DISPLAYED (ENT-U) premise, not a hypothesis-field freebie).**
The FULL aggregate over the DECLARED carrier (EntIx = template × listed
component; ιval/ιsh are V7-4b's DEFS: ιsh i q₀ := entCount i q₀ ·
evalAt (XsEnt.Gent β₀ i), ιval := Σ_i ιsh):
`theorem ent_agg_full (XsEnt : XHDsEnt n S V) (DE : XHDdEnt …) (hEU : EntU V)
(β₀) (q₀ ∈ Pools) : HasSum (fun p : Σ i : V.EntIx β₀, {h // comp-Mem i h} =>
ιshH V p.1.1.1 p.2.1 β₀ q₀) (ιval β₀ q₀)` — entrance heights summed HERE and
nowhere else; each concrete realizable ε hit EXACTLY ONCE (V3-5's bijection
composed with the disjoint component listing + lands_of_realizable — no
realizable entrance omitted); per component: the census is CONSTANT at q₀
by (ENT-U), factor it out (HasSum.mul_left) of XHDsEnt's weight-only
Gent_hasSum; the outer sum is FINITE (V3-4 × list length).
ADJUDICATION (recorded): the note's ledger line names "GIVEN XHD-s
(shallow)" alone; the per-component count constancy the factoring uses is
(ENT-U)'s content, so the Lean statement displays BOTH — conditionality made
explicit, never silently absorbed into a package field (Codex-8's charge).
moves_ref: "ι_{e,β₀} := Σ_{ε̊} Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} … CONVERGENCE of
the full aggregate … is GIVEN XHD-s on the shallow layer" (ENT-AGG).
deps: V3-5, V3-7, V3-9b, V0-3. sketch: reindex by the bijection;
per-component weight HasSum × constant census; finite outer sum.
hyp_fields: XHD-s shallow + XHD-d shallow (owner [2b]) + (ENT-U) (owner [2b]
M4b — displayed); (iv)-REP invoked NOWHERE (the note: "never for the sum's
definition").

**V3-9a `ent_count_stmt` · `V3_entcount.lean` · easy (statement unit) —
RE-KEYED at REV 3 (F-2 + Codex-7: PER CONCRETE ε, against the CENSUS —
never the base-point collapse, never a box-event card).**
ENT-COUNT as the NAMED BURDEN, at the note's own granularity:
`def EntCount (V : CtsMeasured …) : Prop := ∀ (ε : EntShapeV n) (β₀ : S.Cell),
Realizable V ε β₀ → ∃ P : Polynomial ℚ, P.natDegree ≤ ε.Went ∧
∀ q₀ ∈ V.Pools, (P.eval q₀ : ℚ) = V.entCensus ε β₀ q₀` — "each I^ent_{ε,β₀}
is one polynomial", ε concrete; the collapse of the family {ε̊[h] : h ∈ c}
to ONE polynomial is (ENT-U)'s separate content (V3-9b), NEVER assumed here
(Codex-7's carrier-collapse horn closed). Degree ledger at gate B: census
polynomial q(q−1), degree 2 ≤ Went = 3 ✓ (F-2's joint-satisfiability
acceptance). + the displayed FENCE lemma: `I^ent = |β₀|` is NOT assumed (no
field ties them; the gate exhibits I^ent = q·|β₀| ≠ |β₀| — V6-4a).
moves_ref: "ENT-COUNT (named burden): each I^ent_{ε,β₀} is one polynomial
in q of degree ≤ W_ent(ε) … I^ent = |β₀| is NOT general — a per-family
theorem, displayed wherever used" (V.1(iii)).
deps: Defs 2.F. sketch: def + gate pointer. hyp_fields: ENT-COUNT itself
(owner [1v], open — THIS corpus's burden, V.5(3)).

**V3-9b `ent_u_stmt` · `V3_entu.lean` · easy (statement unit) — RE-KEYED
(over the census).**
(ENT-U), typed: over each listed component c of H(ε̊), the per-concrete-ε
census polynomial is ONE polynomial CONSTANT across the instantiations:
`def EntU (V) : Prop := ∀ β₀ (i : V.EntIx β₀), ∃ P : Polynomial ℚ,
P.natDegree ≤ Went i ∧ ∀ h, comp-Mem i h → ∀ q₀ ∈ V.Pools,
(P.eval q₀ : ℚ) = V.entCensus (writeHeights i.1.1 h) β₀ q₀`.
(EntU ⟹ the common P also witnesses EntCount at every ε̊[h] on c — a
one-line corollary in this file.)
moves_ref: "(ENT-U) …: over each listed linear set c of H(ε̊) …, I^ent,
viewed across the instantiations ε̊[h] with h ∈ c, is ONE polynomial CONSTANT
in h on c — [2b] M4b's h_ent-constancy clause, never assumed here" (V.3(iii)).
deps: Defs, V3-5. sketch: def. hyp_fields: (ENT-U) (owner [2b] M4b).

**V3-9c `init_rat` · `V3_initrat.lean` · medium — RESTATED (C23/A-1(3));
DOUBLE-COUNT KILLED at REV 3 (Codex-8/F-2: countT interpolates the CENSUS
polynomial and geom is the WEIGHT-ONLY Gent — the count enters exactly
once, and INIT-RAT is a THEOREM under its displayed burdens, no longer
pre-decided by a count-bearing package field).** ROSTER (2):
(a) `initRat_comp (XsEnt : XHDsEnt …) (hEU : EntU …) (hEC : EntCount …)
(hA : AffEnt n) : ∀ β₀ (i : V.EntIx β₀), ∃ P : PolyGeom,
P.countT = the (ENT-U) common census polynomial of i (degree ≤ Went i) ∧
P.countS = 1 ∧ P.geom = XsEnt.Gent β₀ i (the WEIGHT-ONLY component height
sum, denominators in class) ∧ ∀ q₀ ∈ Pools,
((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ) = ιsh i q₀` — per (template, component):
I^ent_c(q) × Σ_{h∈c} q^{−A(ε̊[h])}, the inner sum geometric (AffEnt's
affine A + XHDsEnt's weight face), the count constant by (ENT-U) — EXACTLY
the fields `RatBurdens.ιP/ι_interp/ι_count/ι_countS_one/ι_degT/ι_degS`
demand, jointly satisfiable (ι_count: countT.eval = entCount = the census
at base ✓ since base ∈ c; ι_degT = Went with natDegree ≤ Went ✓ — gate B:
degree 2 ≤ 3); (b) `initRat_agg`: the displayed aggregate
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c} I^ent_c(q)·Σ_{h∈c} q^{−A(ε̊[h])} ∈ ℚ(q) — finite
sum of (a)'s values (PolyGeom closure mini-lemmas, local to this corpus —
design-freedom slot (5) resolved: the closure route, no MovesS edit).
moves_ref: "INIT-RAT (BURDEN, GIVEN XHD on the shallow layer + (ENT-U)):
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c ⊆ H(ε̊)} I^ent_c(q)·Σ_{h∈c} p^{−A(ε̊[h])} … hence
∈ ℚ(q); CITED by RS.2" (V.3(iii)).
deps: V3-8, V3-9a, V3-9b, V0-3, V0-4 (the witness pattern).
sketch: per component: constant I^ent_c times the XHDsEnt geometric value;
finitely many components and templates. hyp_fields: XHD-s shallow + (ENT-U)
+ ENT-COUNT + M4a's affine-A face (`AffEnt`) — EXACTLY the V.1 ledger line
"INIT-RAT GIVEN XHD (shallow) + (ENT-U)"; supplies `RatBurdens.ιP/ι_interp`.

### Layer V4 — clauses (ii), (iv), (v) [12]

**V4-1 `act_no_entry` · `V4_act.lean` · medium — GUARD RESTORED (C15).**
(ii-a) NO-ENTRY, GIVEN ValA (whose `tbl_count`/`tgt_supported` fields carry
(iv)-POLY's correct valuation + the landing tie), WITH the note's
active-source guard: `theorem no_entry (hVA : ValA …) … (hact :
V.activeState q₀ αc) (hin : ¬ V.activeState q₀ βc) :
(C.T s m o α β).eval q₀ = 0` — zero is claimed ONLY for active sources
(rev 1 demanded zero from inactive rows too — strictly stronger than the
note, which treats those rows as formal junk; struck);
+ `theorem iota_supp (hVA : ValA …) : ¬ V.activeState q₀ β₀ → ιval β₀ q₀ = 0`
(the entrance side has no source guard: ι is supported on Act by its
target) — DERIVABLE at REV 3 (Codex-15's under-hypothesization closed):
ιval = Σ_i entCount·evalAt Gent, and `ValA.ent_supported` (the V2-4(d)
field, the note's own "landing forces a concrete target state" at the
entrance layer) kills every census at the inactive β₀.
moves_ref: "(ii-a) NO-ENTRY — for every source active at q₀, every
table/kernel entry INTO a target inactive at q₀ evaluates to 0 there (a
landing forces a concrete target state), and ι of (iii) is supported on
Act_{q₀}" (V.1(ii)). deps: V2-4 (ValA), Defs 2.F.
sketch: at active source pick a realized (x, h) (zc_ne + act_size);
tgt_supported kills the count; tbl_count casts the zero to the polynomial
value. hyp_fields: ValA ((iv)-POLY's table-build burden beyond the gate
blocks) — the unit is GIVEN it per the V.1 ledger "(ii-a/b) GIVEN (iv)-POLY's
correct valuation".

**V4-2 `act_triangular` · `V4_tri.lean` · medium.**
(ii-b): ordering states active-first, the evaluated kernel matrix at q₀ is
block-triangular `[[A, 0], [C, D]]` — every active-source → inactive-target
entry vanishes (V4-1): stated on `MovesS.Kmat` at evaluation, matching
`MovesS.PoolHyp.inactive_vanish`'s shape. NO stochastic-chain reading: rows
are marked offspring rows ("chain" struck at rev 2) — the lemma is about
matrix zeros only. moves_ref: "(ii-b) DELETION COMPATIBILITY — ordering
states active-first, K_e(q₀) is block-triangular [[A, 0],[C, D]]: the
realized system at q₀ IS the A-block" (V.1(ii)). deps: V4-1, MovesS.Defs.
sketch: entry-wise from V4-1 through Kmat's dite sum. hyp_fields: same as
V4-1.

**V4-3 `act_agreement_stmt` · `V4_agree.lean` · easy (statement unit).**
(ii-c) ACTIVE-VALUE as the typed per-(n, q₀) check — the Prop this corpus
RECORDS, never proves: `def ActiveValueAgree … : Prop := ∀ q₀ ∈ finitely
many empty-cell pools, AVAgree-shaped agreement after cancellation` — stated
via `MovesS.AVAgree` at the instantiated PoolHyp; removability of
det(I − D)(q₀) = 0 carried as the OKat membership hypothesis (MovesS's
"(ii-c) PASS" gate shape, verbatim consumption). moves_ref: "(ii-c)
ACTIVE-VALUE — … the burden is AGREEMENT: at the finitely many q₀ with empty
cells, the symbolic ℚ(q)-solution's value component, after cancellation,
EVALUATES to the active-subsystem value" (V.1(ii)).
deps: MovesS.Interfaces, V7-4c. sketch: def only. hyp_fields: (ii-c) itself —
"a finite per-(n, q₀) verification duty … exercised by RESUM-n3's wild-p
layer ([3]'s gate), recorded here as the clause's standing check, never a
blanket det ≠ 0 claim" (V.3(ii), finding 8: NO general theorem claimed).

**V4-4 `kernel_row_hfree` · `V4_krow.lean` · easy.**
K_e's entrance-height-freeness BY TYPE + the no-division fence: the entry def
`Σ_{m,o} T·G` consumes no `hent` argument (a definitional lemma: the entry
function factors through (α, β) only) and no source-mass denominator (its Qq
numerator is a product, never a quotient by |α| — checked on the def's
shape). moves_ref: "K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_o T·G — NO
source-mass division … K_e is entrance-height-FREE: entrance heights ride in
ε (retained data, rev 4), hence in ι alone" (V.1(iv)).
deps: Defs, MovesS.Kmat. sketch: definitional. hyp_fields: none.

**V4-5 `step_row_eq` · `V4_step.lean` · medium — SIGNATURE FIXED (C16).**
The (iv) STEP display, GIVEN XHD-w + (U-A) + (XHD-u) + XHD-d/s — the XHDw
argument now EXPLICIT (rev 1 used `X.g` with no `X`; and (U-A) alone does
NOT identify the common mass with q^{−E(h)} — that identification is
XHDw.w_eq's): `theorem step_row (P : C15Pack) (X : XHDw) (U : XHDu)
(D : XHDd) (Xs : XHDs) {αc βc} (mv) (x) (hzc : S.zc x) (q₀ ∈ Pools) (j) :
HasSum (fun h : {h // comp-Mem j h} => (S.cntraw mv x h.1 : ℝ) *
X.g mv h.1 q₀) ((T : ℝ) * G_j)` — the height-resolved row Σ T(h)·g(h)
equals T·G: w_eq + (U-A) make g the common per-assignment mass at the fixed
history, (u-R) makes mass and count state-only, (u-T) makes T(h) = T; each
g-summand ALREADY conditional (no re-division — no |α| factor exists).
moves_ref: "UNIFORMITY CONSUMPTION, displayed at the product (rev 2 —
findings 2–3: T·G is NOT licit from XHD-w/d alone): the height-resolved row
is Σ_{h} T(h)·g(h) … = T·Σ_h g(h) is EXACTLY (u-T)" (V.1(iv)).
deps: V1-6, V1-2, V1-1, Defs. sketch: pointwise congr to constant count;
`HasSum.mul_left`; G := the length-1 XHD-s component value.
hyp_fields: XHD-w + (U-A)'s pack + XHD-u + XHD-d/s — VERBATIM the ledger
"(iv) measured faces GIVEN XHD-w + (U-A) + (XHD-u); resummed forms also
GIVEN XHD-d/s".

**V4-6 `part1_route` · `V4_part1.lean` · HARD — FULL SIGNATURE DISPLAYED (C17).**
PART-1 by the rev-3 countable route; ALL premises now in the displayed
signature (rev 1 left (U-A)/XHD-d/s to the prose):
`theorem part1 (P : C15Pack) (X : XHDw) (D : XHDd) (Xs : XHDs)
(leg_a : Totality …) (leg_b : CtblAdd …) (leg_c : NullRem …)
(leg_d : FixedHeightExact …) : ∀ τ x q₀ ∈ Pools, V.activeState q₀ τ →
HasSum (fun ch : Σ c : DCellAll τ, {h // (cdom c)-Mem h} => μcellH …) 1`
— legs: (a) TOTALITY: outside the no-finite-height locus every source point
lies in exactly ONE digit cell (D4R.0 — keyed to MovesD's d4r0 apparatus;
`cellOfA` gives the assignment-level function, the leg lifts it to the
box level); (b) COUNTABLE ADDITIVITY of the conditional measure over this
countable partition; (c) NULL REMAINDER: the no-finite-height locus lies in
the decreasing intersection of height-≥-H strip cylinders with conditional
masses → 0 (typed: `Tendsto (stripMass H) atTop (nhds 0)`); (d) each
fixed-height block sums by C.1.5(1)'s conditional exactness. The four legs
are DISPLAYED structures in this file (Totality/CtblAdd/NullRem/
FixedHeightExact — typed field-by-field over §2.F's carriers).
moves_ref: "PART-1's route, displayed: (a) TOTALITY … (b) COUNTABLE
ADDITIVITY … (c) NULL REMAINDER … (d) each fixed-height block sums by
C.1.5(1)'s conditional exactness — together, the per-cell ratios over the
whole partition sum to 1" (V.3(iv), pass-2 finding 4: "mass 1 is NOT a
finite-pool identity"). deps: Defs, V0-3.
sketch: (d) gives per-(c,h) masses; (a)+(b) give the countable HasSum to the
total minus remainder; (c) kills the remainder; assemble by monotone limits
on nonneg terms. ⌿ pre-approved split: (i) the countable-partition HasSum
from legs a/b/d; (ii) the remainder-null limit from leg c; (iii) assembly.
hyp_fields: the four legs VERBATIM (the ledger: "PART-1 additionally GIVEN
D4R.0 totality + countable additivity + the null no-finite-height remainder"
+ XHD-w's (U-A) face at fixed history + XHD-d/s) — every one in the
signature; leg (a)'s D4R.0 cite keys to MovesD (PROVED core) at the shape
layer but stays a premise HERE because the CTS digit-cell carrier is
abstract until V7-4a.

**V4-7 `part2_row` · `V4_part2.lean` · medium.**
PART-2, the marked offspring row: GIVEN PART-1's conclusion + the mark-count
data (each cell's eligible continuing marks, `emult` — the §2.H def over the
L5 eligibility data): `Σ_{m,o,β} T·G + terminal = 1 + surplus` with
`surplus := Σ_cells (emult c − 1)⁺·mass c ≥ 0` — the marked row counts each
branching cell once PER eligible continuing mark; NO substochasticity of THIS
row is stated anywhere (the lemma's conclusion is the equality, and a
separate lemma `part2_ge`: row sum ≥ 1 − terminal).
moves_ref: "(PART-2, the marked offspring row) the kernel row Σ T·G counts
each branching cell once PER eligible continuing mark, so Σ T·G + (terminal)
= 1 + (branch surplus) … possibly > 1: NO substochasticity is claimed"
(V.1(iv)). deps: V4-6, Defs 2.H. sketch: regroup the marked sum by cells;
emult-weighted count vs once-per-cell count. hyp_fields: PART-1's set +
the emult roster tie (§D4-R L5's multi-eligible cells — MovesD-keyed field).

**V4-8 `part2_n3_zero` · `V4_n3surplus.lean` · easy — PREMISE DISPLAYED (C18).**
At n = 3 the surplus vanishes IDENTICALLY: ROSTER (2): (a) the gate census:
`∀ cells in the V.6 rosters, emult ≤ 1` by `decide`; (b) the GENERAL lemma
WITH ITS TRUE PREMISE DISPLAYED: `theorem surplus_zero (hDC : DegCons T)
(h2 : ContTwo T) : ∀ …, emult c ≤ 1` where `ContTwo T : Prop := ∀ e τ o,
∀ μ ∈ (T.odata e τ o).mem, μ.continuing → 2 ≤ μ.size` — the note's own
argument premise ("two continuing clusters need sizes ≥ 2 + 2 > 3": a
CONTINUING cluster has size ≥ 2; DegCons's size_pos alone gives only ≥ 1 —
C18's finding); then omega (2 + 2 > 3). ContTwo at the gate rosters: decide.
moves_ref: "(At n = 3 the surplus vanishes identically — two continuing
clusters need sizes ≥ 2 + 2 > 3 … first possible surplus at n = 4. Verified
over the V.6 rosters.)" (V.1(iv)). deps: V2-9, DefsGate.
sketch: decide + omega. hyp_fields: ContTwo (a table-build roster law,
decide at gates; displayed premise generally — nothing silently claimed).

**V4-9 `rep_indep` · `V4_rep.lean` · medium.**
(iv)-REP GIVEN (U-A) + (u-R), as the checkable row-level clause:
`theorem rep_row (P : C15Pack) (U : XHDu) (hobs : ObsCheck (C.bd s)) :
∀ (x x' : reps of α) …, measuredRow x = measuredRow x'` — the WEIGHTED
(T·G)-row, not the cardinality row; `ObsCheck` is now the DISPLAYED §2.G def
over `BlockData.evalObs` (the per-species proviso "the species' evaluation
maps mention no observable outside the (a)/(b) generator list"), executed at
the gate blocks (V6-3b's (D2)-EMPTY check) and OPEN elsewhere.
moves_ref: "(iv)-REP … the measured row from x ∈ α is a function of (a) x's
twisted VAL.1 cell data and (b) x's relational strata … the row is
cell-constant PROVIDED the species' evaluation maps mention no observable
outside the (a)/(b) generator list. That proviso is a PER-SPECIES CHECK"
(V.3(iv)). deps: V4-5, V1-6. sketch: row entries via u_R_mass/u_R_cnt +
ObsCheck's factoring. hyp_fields: (U-A) pack + (XHD-u)(u-R) + ObsCheck (the
table-build per-species check; refuter JOINT-probe is Python evidence,
cited not claimed).

**V4-10 `meas_marked` · `V4_meas.lean` · medium.**
(iv)-MEAS in the RETYPED (rev 3) marked-space form: each (m, o, β,
height-class) summand is a finite-level digit-cell union WITH the
continuation mark ADJOINED — a fiber of a finite-level map ON the marked
space; summands pairwise disjoint IN THE MARKED SPACE; as f-events only the
DIGIT CELLS are disjoint (and two summands' f-projections CAN be equal —
stated as: disjointness is claimed on Σ-marked carriers only, plus an
explicit two-continuation instance where f-projections coincide, keyed to
D4-R L5). moves_ref: "the summands are pairwise disjoint IN THE MARKED
SPACE; as f-events only the DIGIT CELLS are disjoint. No ordinary-source
disjointness is claimed anywhere" (V.1(iv), pass-2 finding 2).
deps: Defs 2.E/2.F, MovesD (L12/D4R.4 finite-level realization).
sketch: the marked event's carrier is `Σ (cell × mark)`; disjointness from
the mark coordinate (evt_disj + cellOfA); the equal-projection witness from
L5's two eligible (side, ψ) continuations. hyp_fields: XHD-d (height classes
listed); the L5 eligibility roster (MovesD-keyed field).

**V4-11 `hmc_typing` · `V4_hmc.lean` · easy (typing unit).**
The HMC/HMCAug Prop shapes compile against a NON-degenerate instance: a toy
StepSys with a 2-step template where `HMC` is FALSE (a coupled domain) and a
refined one where it holds — the kernel is a real hypothesis, not a
tautology; + the terminal-final signature check: `Template.lastT` instances
type against `HMC`'s quantifier (the probe's step 2 is a literal instance BY
TYPE). moves_ref: "(v) HMC — … OPEN KERNEL, displayed hypothesis … TERMINAL-
FINAL EXTENSION (rev 4 …): templates INCLUDE those whose FINAL step carries a
terminal outcome" (V.1(v)). deps: Defs 2.G. sketch: two decide-scale toy
models. hyp_fields: none proved ABOUT the CTS instance; HMC itself OPEN
(V.5(2)) — "until HMC closes, K_e(p)^k is NOT a theorem about the process".

**V4-12 `comp_naming` · `V4_naming.lean` · HARD — THE IFF RESTORED at REV 3
(Codex-14: rev 2's adjudication DROPPED the note's "IF AND ONLY IF"; rev 1's
version was false at a FIXED weight system (round-1 C19). The two verdicts
are jointly satisfiable at the right quantifier: the note's g's range over
ALL positive-affine monomial systems, and at THAT quantifier both directions
are true).** ROSTER (3):
(a) `comp_upgrade (hHMC : HMC S D) (X : XHDw) (Xs : XHDs) … :
FactorizesAll S D` where `FactorizesAll S D : Prop := ∀ (E-family :
∀ step, AffineE (dim step)) {α β} (m : S.Move α β) (γ : Template n S β)
(q₀ ∈ S.Pools), (Σ_{h∈H(cons m γ)} ∏ q₀^{−E_i(h_i)}) = (Σ_{h₁∈H(.last m)}
q₀^{−E_m(h₁)})·(Σ_{h₂∈H(γ)} ∏ q₀^{−E_i(h₂,i)})` — HMC ⟹ the factorization
identity for EVERY positive-affine monomial weight system (Fubini /
`HasSum.mul_eq` over the product decomposition HMC provides);
(b) `comp_upgrade_conv : FactorizesAll S D → HMC S D` — THE ⟸-TO-⟹
COMPLETION (the round-1 falsifier evaporates at the ∀-E quantifier): the
three sums are multivariate generating functions of the 0/1-coefficient
membership series of H(cons m γ) vs H(.last m) × H(γ), evaluated at
x_i = q₀^{−e_i} for all positive-affine exponent choices and all pool q₀;
agreement at all such points forces coefficient-wise equality (extract
minimal points by sending selected coefficients → ∞ along pool powers —
pools are infinite and closed under powers), and equality of 0/1 series IS
the membership factorization = HMC. ⌿ pre-approved split: (b-i) the
point-separation lemma for 0/1 multivariate series over pool evaluations;
(b-ii) the assembly.
(c) `comp_upgrade_fails`: the MACHINE-CHECKED FENCE — at V4-11's false-HMC
toy instance, ONE DISPLAYED weight system where the identity FAILS
(norm_num): the ∀-E quantifier in (a)/(b) is NOT removable (a single-system
iff would be false — round-1 C19's content, kept as the fence).
moves_ref: "The right side factors into ∏(T·G), i.e. (COMP-hΣ) upgrades to
(COMP-Σ), IF AND ONLY IF the whole-template domain factors stepwise with
state-only dependence — exactly (v) HMC" (V.4) — carried as the BICONDITIONAL
(a) + (b) at the weight-system-quantified reading, the only reading on which
the sentence is true; (c) records why.
deps: V0-3, V1-1, V4-11, Defs 2.G. sketch: product of HasSums over the
HMC-factored domain; series separation; the toy witness. hyp_fields:
XHD-w/-d/-s data + HMC in (a)'s premise slot (owner [2b] / open kernel) —
hypotheses of the lemma, displayed; (b) consumes only the XHDd data.

### Layer V5 — COMP + the J tables [10]

**V5-1 `marked_event_census` · `V5_event.lean` · medium.**
The (vi) marked event, typed over 2.E/2.F: its MARK-INDEX family is FINITE
per level and its level-N residue census is finite (keyed to MovesD.D4R4_all
at the entrance layer + the finite step data); the f-fibers are boxes,
GENERALLY INFINITE — typed by the carrier: the event is a Finset of
(box-point, mark) pairs at each level, NEVER a Finset of f's; + the census
lemma: card = Σ over marks of fiber cards.
moves_ref: "its MARK-INDEX family (the realized histories η) is FINITE per
level and its level-N residue census is finite (D4R.4); the f-fibers are
p-adic boxes, generally INFINITE (rev 2, finding 13 — never 'finitely many
f')" (V.1(vi)). deps: Defs 2.E/2.F, MovesD.D4R4all_wrapper, V3-6.
sketch: Fintype instances + double counting (MovesD.mult_sum's idiom).
hyp_fields: none beyond MovesD's proved apparatus.

**V5-2 `comp_h` · `V5_comph.lean` · HARD.**
(COMP-h), GIVEN (U-A)'s pack + (XHD-u), ε concrete and h FIXED:
`theorem comp_h … : μ̂N (markedEvent ε γ h) q₀ N
= ιN ε β₀ q₀ N * ∏ i, (T_i * g_i(h_i))` — in the counting-native form:
`(markedEvent …).card * (normalization) = iotaCount … * ∏ (cnt · q₀^{−E})`
(exact at stabilized levels, the MovesC idiom). The chain grouping now rides
the DEFINED `chainCount`/`ext` (no free chain data — A-2/C2 repaired
upstream; the induction has its carrier).
moves_ref: "(COMP-h) at every concrete ε and fixed h ∈ H(γ): μ̂(marked event
of (ε, γ, h) at p) = ι_{e,ε,β₀}(p) · ∏_{i=1}^k [T·g](p)" + the V.4 route
"Group the marked event by its entrance prefix … Per entrance mark, the
continuation mass along γ at h is the C.1.5 conditional chain".
deps: V5-1, V1-6, V4-5, V3-6. sketch: group by entrance mark (V5-1's census);
per mark, induct along γ through `ext`: each step contributes cnt·g by (U-A)
at the fixed history + (u-R) across the histories reaching βᵢ; multiply out.
⌿ pre-approved split: (a) the one-step case; (b) the induction step; (c) the
grouping identity. hyp_fields: (U-A) pack (§C/HC-2) + (XHD-u) (owner [2b]) —
VERBATIM V.4's GIVEN; "at a FIXED path height point AND one fixed entrance
history, the identity consumes only (U-A)'s §C-derivable content" is the
V6-4 gate's per-history face.

**V5-3 `comp_h_count` · `V5_shadow.lean` · medium.**
The COUNT SHADOW: `Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q)` at the same concrete
ε — the same grouping at the count layer, GIVEN VAL(b)'s (XHD-u) count face +
ENT-COUNT; degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ); + the FENCES as typed
non-lemmas: never |β₀| without the displayed per-family theorem, never summed
raw across ε with different A(ε) (the aggregation lemma V5-6 takes masses
ONLY). moves_ref: "the FULL realization count is PER (concrete) ENTRANCE
SHAPE: Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q) (same (XHD-u) tag, plus
ENT-COUNT), degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ) — the entrance factor never
omitted" (Thm VAL(b)). deps: V2-5, V3-9a, V5-2's grouping.
sketch: count-layer replay of V5-2. hyp_fields: (XHD-u) + ENT-COUNT.

**V5-4 `comp_hsum` · `V5_comphs.lean` · medium.**
(COMP-hΣ), GIVEN XHD-d/s, NO HMC: `HasSum (fun h : {h // (dom γ).Mem h} =>
μ̂(ε, γ, h) q₀) (ι_{e,ε,β₀} q₀ * Σ_{h∈H(γ)} ∏ (T·g(h_i)))` — the unfactored
per-template series, well-defined via V0-3 over the listed disjoint
components. moves_ref: "(COMP-hΣ) GIVEN XHD-d/s, NO HMC (rev 2, finding 11
— the unfactored height sum carries its OWN name)" (V.1(vi)).
deps: V5-2, V0-3, V1-4. sketch: sum V5-2 over h; `HasSum.mul_left`.
hyp_fields: XHD-d/s + V5-2's set.

**V5-5 `comp_sigma` · `V5_compsig.lean` · easy.**
(COMP-Σ), GIVEN additionally HMC: the V5-4 value factors to
`ι · ∏ (T·G)_i` — by V4-12(a)'s upgrade direction. moves_ref: "(COMP-Σ)
GIVEN additionally (v) HMC — the factored form" (V.1(vi)).
deps: V5-4, V4-12. sketch: rewrite. hyp_fields: + HMC (OPEN kernel; the tag
rides — every consumer of this unit carries `hHMC`).

**V5-6 `comp_agg` · `V5_compagg.lean` · medium.**
(COMP-AGG), GIVEN (COMP-Σ) + (iii) + (iv)-REP: summing over instantiations
ε̊[h] (the V3-5 bijection) then templates (V3-4 finite):
`Σ_{ε̊} Σ_{h∈H(ε̊)} (COMP-Σ at ε̊[h]) = ι_{e,β₀} · ∏ (T·G)` — entrance
heights EXACTLY ONCE; the common continuation factor pulled out by (iv)-REP
(the ONLY site invoking it, per ENT-AGG's fence); counts do NOT aggregate
(no count analogue stated — distinct A(ε)).
moves_ref: "(COMP-AGG) summing (COMP-Σ) over entrance heights (via the
instantiation bijection) then over templates ε̊ via ENT-AGG (licit by
(iv)-REP): … = ι_{e,β₀} · ∏ (T·G) — masses aggregate, counts do NOT"
(V.1(vi)). deps: V5-5, V3-8, V4-9, V3-5.
sketch: factor the constant continuation out of the double sum; ENT-AGG.
hyp_fields: HMC + XHD set + (iv)-REP's set (union of the deps' ledgers —
displayed in the theorem's signature, nothing implicit).

**V5-7a `jcells_once` · `V5_jdef.lean` · easy — ROUTE-KEYED (F-6; C8's
outcome keying kept).**
J's defining laws over the §2.H REV-3 carrier: `Jval` sums EACH CELL ONCE
(a `Finset.sum` over `bcells s m o α`, no mark index — definitional lemma:
`Jval` factors through the cell SET); the roster tie `bcells = ALL cells iff
route = split, ∅ otherwise` is a FIELD (roster_tie — the (K-SUB) OUTCOME
classification, F-6's repair); at the n = 3 gate rosters the route instance
is `decide` AND the gate NONZERO check is a named lemma: the root's m_2+1
outcome is split-route with a nonempty roster and Jval ≠ 0 there (norm_num
over the gate data — F-6's acceptance test). moves_ref: "J_{τ,o}(q) := the
CELL-LEVEL resummed branching mass — the sum, over the branching digit
CELLS of outcome class o at state τ, of the XHD-resummed conditional cell
mass …, EACH CELL ONCE. [o branching := the (c ≥ 1, m ≥ 2) row of (K-SUB)'s
(m, c) CLASSIFICATION]" (§S-RESUM S.0, the CL-18 display; owner-side record
per the PLAN-SYNC flag). deps: Defs 2.H, DefsGate. sketch: definitional +
decide + norm_num. hyp_fields: none (def-layer).

**V5-7b `j_rat` · `V5_jrat.lean` · medium — PER-(τ,o) (C8).**
(J-RAT) = CL-18, the deliverable, now quantified over EVERY outcome
INCLUDING split-route ones (the §2.H carrier is (s, m, o, α)-keyed; split
outcomes are ordinary index values, not missing single-target moves):
`theorem jRat (XsC : XHDsC …) (hcell : CellPolyPack …) : ∀ (d : MoveData …
with route = split), ∃ P : MovesS.PolyGeom, P.degBoundT = Wloc ∧
P.degBoundS = Wstate ∧ ∀ q₀ ∈ Pools, ((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ)
= Jval J hcell XsC d q₀` — J_{τ,o} ∈ ℚ(q) ENTRYWISE, "a deliverable BEYOND
PART-1's TOTAL cell-partition mass"; supplies `RatBurdens.jP/j_ok/j_interp/
j_degT/j_degS` at MovesS's ∀ (e, τ, o) quantifier through V7-3a's roster
equivalence. NO DOUBLE COUNT (Codex-9's second horn closed): Jval's cell
mass is ALREADY count-polynomial × weight-only-Gcell (§2.H's μcellVal), so
jRat multiplies nothing again — P.countT collects the cells' count
polynomials, P.geom the weight sums; and (J-RAT) is a genuine theorem-under-
burdens, not decided by a count-bearing package field (Codex-8's pattern,
avoided at the cell layer too). moves_ref: "its ℚ(q)-membership is the NEW
NAMED burden (J-RAT) (owner [1v]/[2b]: cell-level counts polynomial per the
(iv)-POLY pattern, XHD-s height sums)" (S.0/CL-18).
deps: V5-7a, V0-3, V1-4. sketch: per cell: count polynomial (CellPolyPack) ×
the weight-only XHDsC value; finite cell sum; PolyGeom closure (V3-9c's
mini-lemmas). hyp_fields: XHD-s cell face ([2b]'s height-sum face) +
`CellPolyPack` (the per-cell count polynomials — [1v]'s own OPEN face beyond
the gate blocks; at the gate blocks discharged by V6 data).

**V5-7c `j_not_marked_tg` · `V5_jfence.lean` · easy — ALGEBRA RE-KEYED
(F-6's tail: the "(J + surplus = marked row)" identity holds only for the
ALL-CELLS-ONCE J, which the REV-3 carrier now is).**
THE J-FENCE, machine-checked: on any split-route roster whose cells each
carry ≥ 1 continuing mark (the (c ≥ 1) classification's cell-level face — a
DISPLAYED roster premise), marked row Σ T·G = J + surplus with surplus =
Σ (emult − 1)⁺·mass; with a multi-eligible cell (emult c = 2) the marked row
STRICTLY EXCEEDS the once-per-cell J-sum; at the n = 3 gate rosters they
coincide (surplus ≡ 0, V4-8, and the roster premise holds by decide) — BOTH
directions stated, so no consumer can conflate the objects. moves_ref: "This
is NOT the marked per-continuing-branch T·G (rev 2, pass-1 finding 1: … a
T·G-sum would multiply-count the cell)" (S.0). deps: V5-7a, V4-7, V4-8.
sketch: toy 2-mark cell instance + the n = 3 decide. hyp_fields: the
displayed roster premise (gate: decide; general: the (K-SUB) cell-level
face, a table-build item).

**V5-8 `cell_refine` · `V5_cellrefine.lean` · medium — NEW at REV 3 (F-4 +
Codex-9: rev 2 carried this as an XHDsC FIELD equating count-bearing cell
sums with the count-free template sum — forcing T ≡ 1, the (q−1)²
adversary. It is neither a field nor false: with the counts displayed it is
a DERIVED identity).** `theorem cell_refine (hVA : ValA …) (U : XHDu)
(DC : XHDdC …) (Xs : XHDs) (XsC : XHDsC …) (hcell : CellPolyPack …)
(d : MoveData n C) (x) (hzc : S.zc x) (q₀ ∈ Pools) :
∑ c, ((hcell.P d.s d.m d.o d.α c).eval q₀ : ℝ) *
  ∑ j, evalAt (XsC.Gcell d c j)
= ((C.T d.s d.m d.o d.α (its TargetIx)).eval q₀ : ℝ) *
  ∑ j', evalAt (Xs.Gc (.last (V.moveOf d)) j')` — the COUNT FACTOR ON BOTH
SIDES, displayed: cell count polynomials on the left, the table entry on the
right. ADVERSARY CHECK (F-4's acceptance): A2's one digit cell with count
(q−1)²: LHS = (q−1)²·G = TA2·G = RHS ✓ — no collapse. [+T twin over
GcellT/mdomT.] moves_ref: "by XHD-d's disjointness the finitely many
component sums ADD EXACTLY to the H(γ)-sum" (XHD-s) + the (iv)-STEP row
"Σ_h T(h)·g(h) … = T·Σ_h g(h) is EXACTLY (u-T)" (V.1(iv)).
deps: V2-4, V0-3, V1-2, Defs 2.F/2.G/2.H. sketch: Fubini the double
(c, h)-sum over nonneg terms (HasSum rearrangement); pointwise
Σ_{c ∋ h} P_c.eval = Σ_c cntc = cntraw (CellPolyPack.count on the domain +
XHDdC exactness + the cntc/cntraw partition identity, definitional); then
cntraw(h) = T.eval across the domain by u_T + no_stray + tbl_count at base.
hyp_fields: ValA + (XHD-u) + XHDdC + XHD-s (template + cell faces) +
CellPolyPack — all displayed; supplies LedgerIV.kstep_one through V7-6b.

### Layer V6 — gate V-n3, decide-native (the seal's displays re-derived) [10]

**V6-1a `rootTable_identities` · `V6_a1poly.lean` · easy.**
The five root closed forms + PART-1 count face AS POLYNOMIALS:
`TH3 + TH12 + TH3c + T21 + T3 = X^3` in ℚ[X] (`ring`), + each degree ≤ 3.
moves_ref: "PART-1 count face, displayed: (q³−3q²+2q)/6 + (3q³−3q²)/6 +
(2q³−2q)/6 + (6q²−6q)/6 + 6q/6 = q³ = pool. ✓" (V.6.1).
deps: DefsGate. sketch: ring/decide on coefficients. hyp_fields: none.

**V6-1b `rootTable_evals` · `V6_a1eval.lean` · easy.**
The PREDICTED EVALUATIONS table at the nine census q — all 45 entries + the
Σ = q³ row, `norm_num`/`decide` (values from V.6.1's table: m_H3 row
0,1,4,10,35,56,84,165,286; …; m_3 row = q). Includes the m_H3 = 0 at q = 2
falsifier as its own named lemma. moves_ref: the V.6.1 evaluation table +
"the m_H3 zero at q = 2 (a genuine falsifier)" (V.6.5).
deps: V6-1a. sketch: norm_num. hyp_fields: none.

**V6-1c `rootTable_census` · `V6_a1census.lean` · medium — NINE POINTS,
CHAR-FREE SKETCH (C20, A-4).**
THE COUNT SEMANTICS at ALL NINE census points: over each F ∈ {ZMod 2, ZMod 3,
F4, ZMod 5, ZMod 7, F8, F9, ZMod 11, ZMod 13} (the §2.I table fields for the
prime powers), classifying monic cubics z³+az²+bz+c by (root count, max
multiplicity): the five class counts equal the closed forms' values —
`decide` per point. MULTIPLICITY PREDICATE, char-free (A-4 repair — the
rev-1 `f″` test is FALSE at p = 2, where f″ ≡ 6x + 2a ≡ 0 marks every double
root as triple, at the m_H3 falsifier's own point): multiplicity of a root
r := the largest k ≤ 3 with `(z − r)^k ∣ f`, decided by direct coefficient
arithmetic (three explicit divisibility tests) — no derivative, no
discriminant, exactly the note's char-free root block.
moves_ref: "(A-side …) exhaustive enumeration over F_q at the nine census q
of all fresh assignments … CHECKED EXACTLY, zero tolerance" (V.6.5).
deps: DefsGate (incl. F4/F8/F9). sketch: decide over F³ per point with the
divisibility multiplicity. hyp_fields: none. [The rev-1 honest-scope split
(six primes in Lean, prime powers Python-sealed) is RETIRED: all nine points
are now in-kernel; the Python seal remains the historical record.]

**V6-2a `a2_domain_chart` · `V6_a2dom.lean` · medium — RE-KEYED (C3).**
The A2 height-domain normal form THROUGH THE CHART: ROSTER (3):
(a) `A2chart_image : A2chart '' {h | A2dom.Mem h} = {(h₀,h₂) : 1 ≤ h₂ ∧
3·h₂ < h₀ ∧ Odd (h₀ − h₂)}` — the note's realizability set IS the chart
image of the (t,u) linear set (omega both directions; parity via 2u+1);
(b) `A2chart_inj : Set.InjOn A2chart {h | A2dom.Mem h}`;
(c) one-component ⟹ the disjointness convention holds VACUOUSLY (a
`Pairwise` on a singleton list — stated). moves_ref: "realizability =
{h₂ ≥ 1 (vertex), h₀ > 3h₂ (hull strictness), h₀ − h₂ odd}; with h₂ = t ≥ 1,
h₀ = 3t + 2u + 1 (u ≥ 0) this is the ONE linear set L((4,1); {(3,1), (2,0)})"
(V.6.2). deps: Defs 2.A, DefsGate. sketch: omega. hyp_fields: none — the
gate "FIXES its heights and consumes no domain hypothesis" (an ILLUSTRATION
of XHD-d's format, exactly as displayed).

**V6-2b `a2_weight_table` · `V6_a2wt.lean` · easy — RE-KEYED (C3).**
The A2 weight, natural-coefficient form + the note's display re-derived:
ROSTER (3): (a) `EA2.eval ![t, u] = 6*t + 3*u + 1` (rfl-level; the
declaration IS in the chart) and the sealed point: `A2chart ![1,0] = ![4,1]`
∧ `EA2.eval ![1,0] = 7`; (b) THE DISPLAY IDENTITY, division-free:
`∀ h, 2 * EA2.eval h = 3 * ((A2chart h 0) + (A2chart h 1)) − 1` — the note's
"E = (3(h₀+h₂)−1)/2" re-derived THROUGH the chart as an ℕ-identity (omega);
no half-integral coefficient exists anywhere; (c) `TA2 = (X−1)²` with the
nine evaluations 1,4,9,16,36,49,64,100,144 and PART-1 `(q−1)² = pool` (one
letter). moves_ref: "g(h₀,h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 — affine,
positive weights. Sealed census height point: (4, 1): E = 7" + "= 6t+3u+1"
+ the T = (q−1)² table (V.6.2). deps: DefsGate, V6-2a. sketch: omega/
norm_num. hyp_fields: none.

**V6-3a `blk2_table` · `V6_bpoly.lean` · easy.**
s_blk2 closed forms + PART-1: `Tsplit + Tinert + Tdbl = X·(X−1)` (ring);
char-2 recount equalities as polynomial identities ((q−1)(q/2 − 1) form =
Tsplit, (q−1)·q/2 = Tinert — the displayed convention: "the closed forms
below are the SAME polynomials under both"); degrees ≤ 2; Tw2 = X−1,
Tvv = (X−1)². moves_ref: "PART-1 count face: (q−1)(q−2)/2 + q(q−1)/2 +
(q−1) = q(q−1) ✓" + "(D2) … DISPLAYED exceptional-char convention; the
closed forms below are the SAME polynomials under both" (V.6.3).
deps: DefsGate. sketch: ring. hyp_fields: none.

**V6-3b `blk2_census` · `V6_bcensus.lean` · medium — NINE POINTS (C20).**
The m₂ outcome census at ALL NINE census points (ZMod primes + F4/F8/F9):
quadratics y² + wy + u with (u, w) ∈ Fˣ × F classified split/inert/double by
root count + multiplicity (the V6-1c divisibility predicate): counts =
(q−1)(q−2)/2, q(q−1)/2, q−1 — decide per point (char-2 points 2, 4, 8
exercise the exceptional-char convention IN THE FIELD, not by
interpolation); + the (iv)-REP count face: the classification is independent
of the source state t ∈ F_qˣ BY CONSTRUCTION in the Lean carrier (the count
sets don't mention t — the (D2)-EMPTY executed check, stated as a
definitional lemma), with the two-representative census duty recorded as
discharged-by-typing. moves_ref: "the s_blk2 rows identical at both
representatives ((iv)-REP)" (gate record) + "(D2) source generators: EMPTY —
none of the three letters' displayed evaluation maps reads t" (V.6.3).
deps: DefsGate. sketch: decide + rfl-lemma. hyp_fields: none.

**V6-4a `gateB_numbers` · `V6_gateB.lean` · easy — ROSTER ENUMERATED (C28).**
Gate B's dyadic arithmetic, every number displayed; ROSTER (4, each one
display): (a) `gateB_mass`: ι = 2·2⁻³ = 1/4, T_{o_double}(2) = 1, g = 2⁻³,
μ̂ = ι·T·g = 2⁻⁵ = 1/32; (b) `gateB_shadow`: count shadow I^ent(2)·T(2) =
2·1 = 2 + marked pairs 2^{3N−5}: N = 3 ↦ 16, N = 4 ↦ 128; (c)
`gateB_ledger`: A(ε) = 3, W_ent(ε) = 3, degree facts; (d) `gateB_ient_ne`:
I^ent = q(q−1) = q·|β₀| ≠ |β₀| (the displayed NOT-general instance, q ≥ 2 —
V3-9a's fence witness). moves_ref: "SEALED EXACT PREDICTIONS: μ̂(marked
event) = ι·T·g = (1/4)·1·(1/8) = 2⁻⁵ = 1/32 …; count shadow = 2·1 = 2" +
"note I^ent = q·|β₀| ≠ |β₀|" (V.6.4). deps: DefsGate. sketch: norm_num.
hyp_fields: none.

**V6-4b `gateB_two_histories` · `V6_gate2h.lean` · medium.**
The TWO-HISTORY DISCIPLINE, concrete at p = 2: the two marked entrance
histories (f̄ = z²(z+1) and f̄ = (z+1)²z over ZMod 2) BOTH land at the
same β₀ state (t = β̄ − ᾱ: 1 and −1 = 1 in ZMod 2), and their step reads
carry the SAME nominal inventory (E = 3λ as a function of the window shape
alone — stated as: the inventory function of DefsGate does not read the
recentering shift; evaluated equal for both histories) — hence T = 1 and
g = 2⁻³ per history BY DISPLAY, aggregate 2·2⁻³·(step factor); NO (XHD-u)
content consumed (the theorem's hypotheses list contains only the C15-shape
inventory data — auditable from the signature).
moves_ref: "(U-A) is applied PER HISTORY, separately … Both land at the SAME
β₀ state (t = 1 for z²(z+1); t = −1 = 1 at p = 2 …) and in EACH history's
branch frame the step read carries the SAME nominal digit inventory …
the commonality is DERIVED, not assumed" (V.6.4). deps: DefsGate, V1-6.
sketch: ZMod 2 arithmetic + inventory-function evaluation; decide/norm_num.
hyp_fields: the concrete inventory data (DefsGate) — no open kernel.

**V6-4c `gateB_threshold` · `V6_gateN.lean` · medium — PREMISE NOW AUDITABLE (C21).**
THRESHOLD N = 3, the derivation typed: GIVEN the coprime-factorization lift
(the typed premise `hensel : CoprimeLiftPack` — fields DISPLAYED at §2.I:
unique coprime lifting + coefficient determinacy, NOTHING stronger), level-3
data determine every event datum: h₀ ≡ 4 mod 8 (v(h₀) = 2 + unit digit at
level 3) and h₁ ≡ 0 mod 4 (v(h₁) ≥ 2) are level-3 predicates; box-precision
2^{3N−5} follows for all N ≥ 3 with ZERO event-word changes (the multiplier
lemma: each level adds exactly 2³ free digits). moves_ref: "THRESHOLD
N := 3, with the derivation displayed: … the coprime (Hensel) factorization
f = u·h lifts uniquely with h mod 2^k determined by f mod 2^k for EVERY k …
So level 3 determines every event datum" (V.6.4). deps: DefsGate, V6-4a.
sketch: mod-arithmetic on box coordinates; the lift pack supplies
determinacy; counting the free digits. hyp_fields: `CoprimeLiftPack`
(Mathlib-backed; if the exact form is missing, it becomes a DECLARED
published-axiom candidate per campaign §4 — flag at E-phase, do NOT silently
strengthen; NEVER an unconditional Lean axiom).

### Layer V7 — CTS-M assembly + the seam instances [15] (Codex-19 splits: every former multi-lemma unit is now one display per unit)

**V7-1 `ctsm_ledger` · `V7_ledger.lean` · easy (typing unit).**
THE PER-CLAUSE HYPOTHESIS LEDGER as ONE record (V.1's rev-2 finding-7 list,
verbatim — "each clause is asserted GIVEN exactly its listed set, nothing
less"): `structure CtsmLedger …` with one field per clause line: (i) the
BlockData family + computed lists at consumed skeletons; (ii) (ii-a/b) ←
ValA's (iv)-POLY ties, (ii-c) ← ActiveValueAgree; (iii) primitives free;
ENT-AGG ← XHD-s/-d shallow; ENT-COUNT named; INIT-RAT ← XHD shallow +
(ENT-U) + AffEnt; (iv) ← computed tables / + (XHD-u) / + PART-1's four legs /
measured ← XHD-w + (U-A) + (XHD-u) / resummed ← XHD-d/s (+ cell face); (v)
OPEN + (HMC-AUG) separate; (vi) ← per-identity sets + the solve sentence's
ESCAPE(E0)/(ii-c)/ENT-COUNT/INIT-RAT. REV-3 additions: the (J-RAT) cell
pack (`CellPolyPack`) and (ENT-U) ride as their own ledger fields (they are
consumed by the REV-3 defs, V7-4b/c), and the general table-build law supply
is the TYPED field `stage_laws : StageLawBurden n C` (V7-3d — Codex-20's
missing closed structure). Every field TYPED to the §3 unit statements (no
Prop-placeholder fields for in-corpus content; owner-tagged packages for
[2b]/[3t]). moves_ref: "PER-CLAUSE HYPOTHESIS LEDGER (rev 2 — finding 7 …)"
(V.1). deps: all statement layers. sketch: record decl.
hyp_fields: the ledger IS the hypothesis inventory — nothing new.

**V7-2a `ctsm_conclusions_decl` · `V7_ctsmDefs.lean` · easy (Defs-layer
unit) — SPLIT (Codex-19) + CLOSED (Codex-18/C22).**
`structure CtsmConclusions (L : CtsmLedger …) : Prop` DECLARED CLOSED: one
field per ledgered deliverable, each field's type a named `*_Stmt` def of
this file, and each `*_Stmt` def is the VERBATIM ∀-closure of the named
unit's displayed conclusion (zero new content; the transcription rule is
normative). Fields (24): `syntax_partition : Part_Stmt L` (V2-3 at every
listed skeleton) · `val_a : ValA_Stmt L` · `val_b_chain : ValB_Stmt L`
(V2-5(b)) · `no_entry : NoEntry_Stmt L` + `triangular : Tri_Stmt L`
(V4-1/2) · `iota_supp : IotaSupp_Stmt L` · `active_value_recorded :
AVRec_Stmt L` (the (ii-c) Prop CARRIED, never concluded) · `ent_typing` +
`ent_agg_fin` + `ent_agg_full` (V3-1/2, V3-7, V3-8) · `ent_count_named`
(the Prop carried) · `init_rat` (V3-9c under its ledger set) · `step_row`
(V4-5) · `part1` (V4-6) · `part2` + `surplus_n3` (V4-7/8) · `rep` (V4-9) ·
`meas` (V4-10) · `comp_h` + `count_shadow` + `comp_hsum` + `comp_sigma` +
`comp_agg` (V5-2/3/4/5/6) · `solve_conditional` (the (vi) solve sentence as
the displayed implication with ESCAPE(E0)/(ii-c)/ENT-COUNT/INIT-RAT
premises, MovesS-typed) — (v) has NO conclusion field (it remains a LEDGER
field — open kernel). Representative `*_Stmt` displays for three fields
(part1/step_row/comp_agg) are in this unit's roster; the rest follow the
same rule. moves_ref: the V.1 clause list. deps: statement layers.
sketch: structure decl + Stmt defs. hyp_fields: none (typing unit).

**V7-2b `ctsm_given` · `V7_ctsm.lean` · medium — SPLIT (Codex-19).**
THEOREM CTS-M assembled: `theorem ctsM (L : CtsmLedger …) :
CtsmConclusions L` — apply each cited unit; assemble. The [1v]-COND capstone
of this corpus. moves_ref: "This note proves CTS-M's clauses EACH GIVEN
EXACTLY the hypothesis set displayed in V.1's per-clause ledger" (header).
deps: V7-1, V7-2a + cited units. sketch: apply; assemble.
hyp_fields: = V7-1's ledger, displayed in the signature.

**V7-3a `tableShape_inst` · `V7_ts.lean` · medium — SPLIT (Codex-19).**
The `MovesS.TableShape n` instance from `CtsFamily`: State e := block-e CTS
cells (s, α) (via `toStepCells` and the block-size datum); VType := `VLabel
n` with `vEquiv := Equiv.refl`-keyed and `vdeg_spec` by rfl; Out/odata from
the letter+outcome rosters with member data from DEG-CONS's tuples;
Wloc/Wstate transported; PLUS `route_eq` (the §2.H compatibility law):
JCells.route s m o = MovesS.routeOf (odata …) under the roster wiring —
F-6's classification is the seam's own. moves_ref: "Downstream discipline
(plan REV 6): M2's τ, RS.0, RS.PRE, SQ.2 condition on CTS cells and on
NOTHING finer or coarser" (V.0) — the seam's one carrier.
deps: V2-*, V7-1, MovesSp. sketch: structure wiring; Fintype instances.
hyp_fields: the roster-coverage burden (CL-13) rides as the
BlockData-family argument.

**V7-3b `degcons_kmat_gate` · `V7_tsGate.lean` · easy — SPLIT (Codex-19).**
(a) `MovesS.DegCons` for the instance (V2-9 at the gate family; the general
instance GIVEN the CL-11 burden field); (b) `KmatHyp` AT THE GATE INSTANCE
by `decide` (a PROP about the roster — C25's correction stands).
moves_ref: DEG-CONS/CL-11 + the kcol column convention. deps: V7-3a, V2-9,
DefsGate. sketch: decide. hyp_fields: CL-11 beyond gates (in V7-3d's
StageLawBurden).

**V7-3c `scs_data_supply` · `V7_scsData.lean` · medium — SPLIT (Codex-19).**
The `SCSData` DATA supply: W/D/ℓ/g/μsel/W'/D'/flankCount/flankWidth/
resFactors/selIdx/memberOf from the MovesSp species stage fields (s.D, s.w,
s.W, s.sel, s.lam) through the roster wiring; the twelve LAWS decided AT THE
GATE ROSTERS (decide). moves_ref: the SP.2 stage laws (consumed).
deps: V7-3a, MovesSp, DefsGate. sketch: wiring + decide.
hyp_fields: none at gates; general = V7-3d.

**V7-3d `stage_law_burden` · `V7_stageLaw.lean` · medium — NEW TYPE
(Codex-20: the general SCSData/KmatHyp supply was an untyped prose burden).**
```lean
structure StageLawBurden (n : ℕ) (C : CtsFamily n) : Prop where
  kmat_all : ∀ e, MovesS.KmatHyp (tableShapeOf C) e
  degcons_all : MovesS.DegCons (tableShapeOf C)          -- CL-11, full roster
  ℓpos : …          -- the twelve SCSData laws, one field each, quantified
  window_comp : …   -- over ALL skeletons (verbatim MovesS field statements
  flank_zero : …    -- at the V7-3c data): ℓpos/window_comp/flank_zero/
  sel_mem : …       -- sel_mem/res_sum/memberOf_inj/memberOf_ne_sel/
  res_sum : …       -- sel_continuing/stage_D/stage_W/cluster_parent/
  memberOf_inj : …  -- cluster_child — each `…` is the MovesS law's statement
  memberOf_ne_sel : …  -- with V7-3c's data substituted (a mechanical
  sel_continuing : …   -- transcription; the FIELD LIST is the closed type,
  stage_D : …          -- and no law is missing or renamed)
  stage_W : …
  cluster_parent : …
  cluster_child : …
```
+ `theorem stage_law_gate : StageLawBurden-restricted-to-gates` by decide.
A FIELD of `CtsmLedger` (V7-1); at gates discharged by V7-3b/c; beyond them
the [2a]-SP.2 stage-law burden, now a TYPE, not prose. moves_ref: the (i)
ledger line + CL-13. deps: V7-3a/b/c. sketch: structure decl + gate decide.
hyp_fields: itself (the typed open burden).

**V7-4a `measured_cells_inst` · `V7_msA.lean` · medium — SPLIT (Codex-19);
the `MovesS.MeasuredSide` instance is a theorem-under-data across
V7-4a/b/c: GIVEN V : CtsMeasured, X : XHD, cp : CellPolyPack (the [2b]
package + the [1v] cell-count face as EXPLICIT data — conditional exactly
as [1v]-COND is).** Cells/boxes/state half:
- pools: `Pools`/`pools_prime_pow`/`pools_closed`/`pools_infinite` ← V (C7);
- `Box/finB/boxpos` ← V; `State e` := block-e CTS cells;
- `Cell e τ := Σ o : Out e τ, DCellO (dataOf τ o)` (outcome-cell fibers;
  `cellOut` := the Σ-projection); `Rep e τ := {x // S.zc x}` (rep_ne ← zc_ne);
- `dataOf/dataOfT` := the inverses of moveOf_bij/moveOfT_bij (one-line
  noncomputable defs, displayed here — Codex-18);
- `Hgt := Σ D : ℕ, Hpt D`; `HDom c` := the Σ-embedded listed `cdom`/`cdomT`;
- `cellLvl e τ c := V.stLvl (state of τ)`; `cellInst e τ c := V.stInst …` —
  THE F-5 REVERT: the STATE-instance census (the G4 pattern; rev 2's
  "stabilized level + cellEvt" line named fields that did not exist —
  Codex-16 — and the cell-instance keying broke cellP_deg/act_iff at both
  gates — F-5);
- `activeState` ← V.activeState (act laws ← act_size);
- `cellEvt x c h` := the §2.F biUnion def.
moves_ref: MovesS.Defs §2.B's intended-instance note: "the CTS cell space
over the level-N residue boxes of the O_δ theory (the MovesC counting
idiom), wave 4". deps: V7-3a, Defs 2.F, MovesD. sketch: field defs +
Fintype/Nonempty instances. hyp_fields: as in the header (data args).

**V7-4b `measured_entrance_inst` · `V7_msB.lean` · medium — SPLIT
(Codex-19); ENTRANCE SIDE at A-1's granularity, REV-3 census wiring.**
- `EntShape e τ := V.EntIx (cellOf τ)` — FINITE (`finE` ← V3-4 × list
  length); `Went i` := W(P̂) via the template (height-free, L3 rev 9);
- `entEvtH i h := V.entEvt (writeHeights i.1.1 h) β₀ …`; `ιDom i` := the
  Σ-embedded component; `ιshH i h` := the §2.G DEF (CENSUS·q^{−A} — F-1's
  corrected body); `ιsh i q₀ := (V.entCount i q₀ : ℝ) · evalAt
  (X.sEnt.Gent β₀ i)` (count × WEIGHT-ONLY sum — Codex-8's split);
  `ιval τ q₀ := Σ_{i : EntIx} ιsh i q₀`;
- `entCount i` := the §2.F CENSUS def (F-2); `entLvl i := V.entLvl i.1.1`;
  `entInst i q₀ N := V.entInst (writeHeights base) β₀ q₀ N` — so
  `LedgerIV.ent_count_card` is rfl-level AGAINST THE CENSUS (the ledger
  comment "the counting tie ι_count's polynomial now means the full count"
  is honored: ι_count's polynomial = the census polynomial, degree ≤ Went);
- `hent i := Σ_k ((V.entDom i.1.1).comps.get i.1.2).base k` — ADJUDICATION
  RETAINED AND RE-RECORDED (A-1(2); round-2 DISAGREEMENT on file: Codex-7
  called the scalar unfaithful, Fable's fresh pass source-verified that NO
  law in MovesS Defs/Interfaces reads `hent` and endorsed SF-1 as the right
  record. Disposition: the field is semantically INERT in the frozen seam;
  the instance supplies the component's base-height total as a canonical ℕ
  datum; SEAM FLAG SF-1 stands — MovesT's wave-4 re-keying of βmeas's h_ent
  argument must bind to the Hgt-indexed carriers (ιDom/ιshH/entEvtH), never
  to `hent`. Any future MovesS law reading `hent` re-opens this line item);
- `markedVal` := the μ̂ totals (MuHat-wrapped at exit).
moves_ref: V.1(iii) + the A-1 granularity record. deps: V7-4a, Defs 2.D/2.F,
V3-4. sketch: field defs. hyp_fields: as in the V7-4a header.

**V7-4c `measured_values_inst` · `V7_msC.lean` · medium — SPLIT (Codex-19);
the measured ℝ-values, REV-3 count-polynomial wiring (F-4/F-5).**
- `gwt c h q₀ := ((cp.P … c).eval q₀ : ℝ) * X.w.g (moveOf …) h q₀` — count
  POLYNOMIAL × weight (x-FREE by construction, as MovesS's gwt signature
  demands; the count factor is the [1v] pack, the weight the [2b] monomial);
- `μcell x c q₀ := ((cp.P … c).eval q₀ : ℝ) * Σ_j evalAt (X.sC.Gcell … c j)`
  (x-free; count × weight-only component sums);
- `rowVal o q₀ := Σ_{c ∈ cells o} μcell c q₀` (for split routes this IS the
  J cell-sum — MovesS's own comment — via §2.H's roster_tie);
- `kstep k τ β q₀ := Σ_{γ : length-k kcol templates τ→β}
  ((pathProdPoly C γ).eval q₀ : ℝ) · Σ_j evalAt (X.s.Gc γ j)` — THE COUNT
  FACTOR RESTORED (F-4/Codex-11: rev 2 dropped ∏T; kstep_one then demanded
  T ≡ 1). THE ANTI-SMUGGLE PIN STANDS: kstep is the measured k-step
  TEMPLATE mass (∏T × the unfactored template height sum), NOT the
  matrix-power recursion — LedgerIV.hmc stays V5-5's conditional content.
moves_ref: "K_e(q)_{(s,α),(s′,β)} := Σ Σ T·G" (V.1(iv)) + S.0's kstep row.
deps: V7-4a/b, V2-5 (pathProdPoly), Defs 2.G/2.H. sketch: field defs.
hyp_fields: as in the V7-4a header (X, cp explicit).

**V7-5 `ratBurdens_inst` · `V7_rb.lean` · HARD — LEGS RE-KEYED (C23); leg
(d) REVERTED at REV 3 (F-5).**
`MovesS.RatBurdens T M`, theorem-under-hypotheses — GIVEN the open faces,
the burdens structure is inhabited: `theorem ratBurdens_exists
(hVA : ValA …) (X : XHD …) (hcell : CellPolyPack …) (hEU : EntU …)
(hEC : EntCount …) (hA : AffEnt n) :
Nonempty (MovesS.RatBurdens T M)` with the legs:
(a) `tgP` := ValA's count polynomials × the XHDs/XHDsC geometric values —
the G-BEARING FACE IS A PREMISE (C23), and via V5-8's cell_refine the
count-polynomial form matches V7-4c's rowVal;
(b) `jP` ← V5-7b (weight-only XsC × CellPolyPack — no re-multiplication,
Codex-9's second horn; per-(τ,o) incl. split routes via V7-3a's route_eq);
(c) `ιP` ← V3-9c(a)'s PER-COMPONENT PolyGeoms — same type as
`RatBurdens.ιP : ∀ e τ, EntShape e τ → PolyGeom` under V7-4b's EntIx keying
(the C23 aggregate-vs-per-shape mismatch is gone); ι_count = the CENSUS tie
(countT.eval = entCount, TRUE at degree ≤ Went under the F-2 re-key — gate:
deg 2 ≤ 3), ι_countS_one, ι_degT/ι_degS from V3-9c(a)'s clauses;
(d) `cellP` — REVERTED TO THE REV-1 sizeP WIRING (F-5: rev 2's
"CellPolyPack granularity fix" was a REGRESSION — digit-cell COUNT
polynomials violate the frozen `cellP_deg ≤ Wstate` at BOTH gate blocks
(Wloc 3 > Wstate 0 at the root; 2 > 1 at s_blk2) and make `act_iff` FALSE
at q₀ = 2 through the m_H3 empty cell, the blueprint's own falsifier;
round-1 C23 never named cellP): `cellP e τ c := sizeP (state of τ)` —
constant across the state's digit cells — satisfying all four frozen laws:
`cellP_deg` ≤ Wstate ✓ (sizeP's bound); `cellP_nonzero` ✓ (post-deletion
CellIdx); `cellP_count` ✓ ← `V.stInst_card` (the state-census card at stLvl
IS sizeP.eval — the G4 pattern; cellInst/cellLvl wired at V7-4a);
`act_iff` ✓ ← `act_size` (activity IS state-size nonvanishing; with cellP
constant in c the ∀-c iff collapses to act_size — and at q₀ = 2 the root
stays active while the m_H3 DIGIT cell is empty, contradicting NOTHING).
The rev-2 `ActIff` premise is DELETED (subsumed by act_size); CofinAct
rides where MovesS's R45/R50 keying needs it.
⌿ split: (a) tgP/jP legs; (b) ιP leg; (c) cellP + act_iff. moves_ref: the
V.0 downstream line "[3] RESUM consumes K_e and ι_e from this note's clauses
only" + CL-6/CL-18/INIT-RAT ownership rows + MovesS R45/R50 ("EACH CELL SIZE
one polynomial of degree ≤ W_state(s)"; cellInst = "instance events whose
card IS the cell size"). deps: V2-4, V5-7b, V5-8, V3-9c, V7-4a/b/c.
sketch: assemble PolyGeoms; interp fields from the units' eval conclusions.
hyp_fields: (iv)-POLY beyond gate blocks (CL-13/CL-6) + (J-RAT)'s cell pack +
INIT-RAT's set — the STATED premises; nothing discharged silently.

**V7-6a `ledgerIV_counting` · `V7_livA.lean` · medium — SPLIT (Codex-19);
THE COUNTING SUITE, now derivable from typed fields (F-3/Codex-10's four
refuted legs, each with its REV-3 supplier):**
GIVEN V + X (with the dC face) + cp:
- `meas_card` (gwt·|Box| = |cellEvt| eventually): gwt = P_c·g by V7-4c's
  DEF; |cellEvt| = Σ_a |evtOf a| (V.evt_disj over AStep → card of the
  biUnion); each |evtOf a| = massOf·|Box| eventually (V.evt_card — the
  typed field that rev 2 lacked); massOf = g (X.w.w_eq); P_c.eval = cntc on
  the domain (cp.count + X.dC.no_strayC realizedness) — assemble;
- `xhd_no_stray`: h ∈ HDom → cntc > 0 (X.dC.no_strayC) → cellEvt nonempty
  for N ≥ stabLvl (evt_card with massOf = g > 0);
- `xhd_no_orphan`: h ∉ HDom → cntc = 0 (X.dC.no_orphanC contrapositive) →
  the filter is empty → cellEvt = ∅ at EVERY N (definitional);
- `d4r0` (cross-(c,h) disjointness incl. h ≠ h′): V.evt_disj over AStep —
  cross-assignment (same h, different cells: cellOfA discriminates),
  cross-HEIGHT, cross-move, and terminal cases are ALL instances of the one
  Σ-carrier law (rev 2's same-(mv,h) evt_disj could not reach h ≠ h′);
- `init_count` (ιshH·|Box| = |entEvtH| eventually): V.ent_card + V.box_card
  + the §2.G ιshH DEF — gate B: (1/4)·512 = 128 ✓ (F-1's number);
- `ent_count_card` ← rfl (entCount IS the census card BY DEF, §2.F).
moves_ref: the CL-5 nine-input ledger's counting faces (S.0). deps: Defs
2.F/2.G, V7-4a/b/c. sketch: as listed, field by field. hyp_fields: XHD
(w + dC faces) + CellPolyPack — displayed.

**V7-6b `ledgerIV_sums` · `V7_livB.lean` · medium — SPLIT (Codex-19); THE
SUM/VALUE SUITE:** GIVEN V + X + cp + (ENT-U):
- `xhd_sum` ← X.sC.Gcell_hasSum (weight-only) ×-scaled by P_c.eval
  (HasSum.mul_left) through V0-3 — μcell IS the count×component-sum value
  by V7-4c's DEF (the C24(1) tie, now with the count factor VISIBLE);
- `kstep_one` ← V5-8's cell_refine (the count-bearing refinement — the
  C24(3) supplier, no longer a false package field) summed over the kcol
  outcomes landing at β (V7-4c's kstep carries ∏T, so the length-1 case is
  T·ΣGc = Σ_c P_c·ΣGcell = rowVal — the F-4 acceptance identity);
- `comp_once` ← X.sEnt.Gent_hasSum ×-scaled by the constant census
  ((ENT-U) at q₀ — the entrance-height sum, once; ιsh/ιDom/ιshH are the
  §2.F/2.G objects);
- `init_agg` ← V7-4b's ιval DEF (a finite sum over EntIx — rfl-level).
moves_ref: ledger faces (1)/(6)/(8)/(9). deps: V5-8, V0-3, V3-9b, V7-4b/c.
sketch: HasSum algebra. hyp_fields: XHD (s faces) + CellPolyPack + (ENT-U)
— displayed.

**V7-6c `ledgerIV_inst` · `V7_livC.lean` · medium — SPLIT (Codex-19); THE
ASSEMBLY:** `MovesS.LedgerIV T M`, theorem-under-hypotheses: GIVEN the XHD
bundle (the SAME X as V7-4's instance) + cp + hVA + HMC + the PART-1 legs +
ENT-COUNT + (ENT-U), every LedgerIV field is supplied: the V7-6a/b suites +
- `part1` ← V4-6; `rep_indep` ← V4-9 (rowVal is x-free BY DEF; the law is
  exactly (iv)-REP's content);
- `hmc` ← V5-5's (COMP-Σ) factorization GIVEN the open kernel (hHMC
  explicit — no unconditional instance until (v) closes);
- `act_target` ← V4-1 (through hVA's tbl_count/tgt_supported at base
  points + u_T across the domain).
moves_ref: the CL-5 nine-input ledger's [1v] faces (S.0, cited; each face's
home display quoted at its field). deps: V7-6a/b, V4-*, V3-*, V7-4a/b/c.
sketch: assemble. hyp_fields: XHD + CellPolyPack + ValA + HMC + PART-1
legs + ENT-COUNT + (ENT-U) — the ledger's own tags, verbatim, nothing
silent.

**V7-7 `seam_rekey_stmts` · `V7_seam.lean` · easy (statement units) —
ONE COHERENT PACKAGE (C26/C27).**
The §W4-SYNC re-keyed statements this corpus OWNS, as named defs consumable
by MovesS's contract: `def xhdStmt : Prop := Nonempty (XHD n S_cts V_cts)` —
ONE Prop, the FULL bundle at the V7-4 instance. THE RE-KEYING (C27 repair):
ALL FOUR of `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` are re-keyed to THIS ONE
Prop (each field := `xhdStmt`) — any single field then yields one COHERENT
package (same weights, same domains, same sums; the s-face bound to the
SAME w/d BY THE BUNDLE'S TYPE), and four independent incompatible witnesses
are impossible by construction. Four unrelated `Nonempty` fragments no
longer exist. `def cts_counts_stmt : Prop := ValA … ∧ EntCount …` (re-keying
`Wsh17Package.cts_counts` — S-8's [1v] leg); PLUS the S-8 DEMANDS honored AS
A TYPE (Codex-17: rev 2 asserted "the re-keyed Wsh17Package gains it"
without displaying any type — a standalone Prop is not a package premise):
```lean
/-- the re-keyed Wsh17 package, DISPLAYED (the seam-contract pin's REV-3
form; field names verbatim from MovesS's Wsh17Package, plus the demanded
xhd_s face): -/
structure Wsh17PackageV : Prop where
  cts_counts : cts_counts_stmt          -- S-8's [1v] leg (ValA ∧ EntCount)
  wsh_xhd_s  : xhdStmt                  -- the DEMANDED xhd_s face, a FIELD
  -- (the package's remaining fields are [3t]/[3]-owned pins, carried by
  --  NAME from MovesS's Wsh17Package — tree/shape vocabulary MovesV does
  --  not restate; the re-keying instruction in §4.3 binds them.)
```
THE EMPTY-MENU LEG, HONESTLY SCOPED (Codex-17's second horn: rev 2 routed
`F.Sh.Nonempty` "through S-5" while listing S-5 as NOT re-keyed — a
contradiction, and the owner-side `W7_cutWD` still carries the obsolete
`isDeepSplit → ¬ isEntrance` clause): REV 3 does NOT claim the vacuity
fence closed. SEAM FLAG SF-2 (new, recorded in §4.3): W17ii's
nonemptiness leg awaits [3t]'s `tree_ne` + the W7_cutWD
first-entrance-ancestor retype — OWNER-SIDE OPEN; MovesV delivers exactly
its two legs (cts_counts, wsh_xhd_s) as fields of the DISPLAYED
`Wsh17PackageV` and flags the rest. moves_ref: MovesS §W4-SYNC S-2/S-8/S-9 +
this note's V.0 package. deps: V7-4a/b/c, V2-4, V3-9a.
sketch: defs + one structure. hyp_fields: none (names for open obligations —
their TYPES pin their content, per doctrine; inhabitation stays with the
owners).

## §4 SEAM-SUPPLY — every MovesS interface field, mapped to its supplying unit

This section is the wave-4 answer to MovesS's §W4-SYNC contract and to the
intended-instance notes in `MovesS/Defs.lean`. Legend: **[MovesV: unit]** =
supplied by this corpus; **[owner]** = NOT this corpus's (named owner; MovesV
neither states nor strengthens it). REV-2 pointer hygiene (A-7): entrance
carriers live in §2.F (EntIx/entDom/entEvt) and §2.D (hent/Went projections);
no "from 2.E" pointers remain.

### 4.1 `MovesS/Defs.lean` instantiation targets (the W-11 process gate)

| MovesS object | supplier |
|---|---|
| `TableShape n` (State/VType/vEquiv/Out/odata/Wloc/Wstate) | [MovesV: V7-3a from `CtsFamily` (§2.C); vEquiv via `VLabel` = the R20 pin verbatim; + route_eq (F-6's classification tie)] |
| `DegCons T` | [MovesV: V2-9 (gate rosters, decide) + the CL-11 full-roster burden field for uncomputed skeletons — carried, not discharged] |
| `KmatHyp T e` (a PROP: kcol members size e) | [MovesV: V7-3b PROVES it at the gate instance by decide; general = the TYPED `StageLawBurden.kmat_all` (V7-3d — Codex-20; no prose burden). (C25 repair stands: it is a proposition, and no MovesS theorem derives it.)] |
| `SCSData T` (W/D/ℓ/g/μsel/W'/D'/flankCount/flankWidth/resFactors/selIdx/memberOf + 12 laws) | [SPLIT (C25 repair): DATA fields ← V7-3c from MovesSp species stage fields (s.D, s.w, s.W, s.sel, s.lam) through the roster wiring; LAWS decided at the gate rosters (V7-3c) AND, beyond them, carried as the TYPED `StageLawBurden` (V7-3d — Codex-20: a closed hypothesis structure with all twelve law fields + kmat_all + degcons_all, a `CtsmLedger` field; no prose burden survives)] |
| `MeasuredSide T` (all fields) | [MovesV: V7-4a/b/c from `CtsMeasured` (§2.F) + the XHD package + `CellPolyPack` as data + MovesD boxes; `Hgt` carrier = Σ D, Hpt D ("MovesV instantiates the carrier at wave 4" — DONE here); entrance side = EntIx with the CENSUS wiring (entCount/entInst = the ε-instance census, ιshH = census·q^{−A} — F-1/F-2); cellLvl/cellInst = the STATE census stLvl/stInst (F-5); gwt/μcell/rowVal/kstep = count-polynomial × weight-only sums, kstep with ∏T (F-4); `hent` per the RECORDED adjudication + seam flag SF-1 (V7-4b — round-2 disagreement on file, resolved on Fable's source verification)] |
| `RatBurdens T M`: `tgP/tg_ok/tg_interp/tg_degT/tg_degS` | [MovesV: V7-5(a) from ValA (V2-4) × the XHDs/XHDsC geometric faces — CL-6 (iv)-POLY, GIVEN the table-build coverage AND the [2b] height-sum face (C23: rowVal is resummed; counts alone cannot interpolate it)] |
| `RatBurdens.jP/j_ok/j_interp/j_degT/j_degS` | [MovesV: V7-5(b) from V5-7b — **(J-RAT)/CL-18, THE PLAN-SYNC DELIVERABLE recorded owner-side**; per-(τ,o) incl. split routes (C8); height-sum face tagged [2b]] |
| `RatBurdens.ιP/ι_ok/ι_interp/ι_countS_one/ι_count/ι_degT/ι_degS` | [MovesV: V7-5(c) from V3-9c(a)'s PER-COMPONENT PolyGeoms (the C23 type fix) + V3-9a (ENT-COUNT); GIVEN XHD-shallow + (ENT-U) + AffEnt] |
| `RatBurdens.cellP/cellP_deg/cellP_nonzero/cellP_count/act_iff` | [MovesV: V7-5(d), the REV-3 REVERT to the rev-1 sizeP wiring (F-5): cellP = the state-size polynomial; cellP_count ← `stInst_card` (the state census, G4 pattern); act_iff ← `act_size`; the rev-2 CellPolyPack keying and its ActIff premise are STRUCK (they violated cellP_deg at both gates and act_iff at q₀ = 2)] |
| `LedgerIV T M` (all nine inputs) | [MovesV: V7-6a/b/c, CONDITIONALLY — the field-by-field map with the REV-3 TYPED TIES (meas_card ← evt_card + w_eq + cp.count + XHDdC; no_stray/no_orphan ← XHDdC + evt_card; d4r0 ← the AStep disjointness law; xhd_sum ← weight-only Gcell sums × P_c; kstep_one ← V5-8's DERIVED cell_refine; init_count ← ent_card + box_card + the census ιshH (gate: 128 ✓); ent_count_card ← rfl against the census; comp_once ← Gent_hasSum × (ENT-U); hmc ← hHMC explicit — no unconditional instance until (v) closes)] |
| `EscapeE0`, `PoolHyp`, `DetHyp`, `RegP` | [owner [3] MovesS — CL-1; MovesV only supplies the entries' OKat memberships through RatBurdens] |

### 4.2 `MovesS/Interfaces.lean` fields

| field | supplier |
|---|---|
| `RS1Meas.βmeas/β_bdd/βfull` | [owner [3t] → MovesT: measured subtree values; MovesV supplies NO per-f or subtree object — the [3t] fence; h_ent binding per seam flag SF-1] |
| `RS1Bundle.xrb` (W-2) | [owner [3]: the S.1 theorem; its `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` premise fields RE-KEYED to the ONE coherent `xhdStmt` — V7-7 (C27)] |
| `RS1Bundle.recursion_meas` (W-3) | [owner [3t]/[3]: the RS1GivenPackage route; MovesV contributes the PCI leg's (iv)-REP statement (V4-9) as the re-key target for `pci`'s REP conjunct] |
| `RS1Bundle.nsNull/rexact` | [owner [3t] §T.2 — CLOSED there; tag displayed] |
| `RS4Chain.L` | [MovesV: V7-6c (conditional instance)] |
| `RS4Chain.B/hns/PrimePools/prime_*/Sigmas/sig_exact` | [owner: wave-4 assembly (MovesT + MovesS gate)] |
| `RS4Chain.pools_e0/legs_reg` | [owner [3] — CL-1 E0; consumes MovesV's RatBurdens entries] |
| `RS4Chain.WshP/wsh_ok/WshVal/wsh_interp/wshval_bdd` | [owner [3t]/[3] — CL-17(ii) production; MovesV supplies the `cts_counts` leg: V7-7's `cts_counts_stmt` (ValA ∧ EntCount) + the demanded `xhd_s` face `wsh_xhd_s_stmt` (seam S-8, C26)] |
| `RS4Chain.wsh17_pin` | [owner [3]: instantiated with W17ii's statement at wave 4; the [1v] ingredients = V7-7; the empty-menu exclusion = [3t] tree_ne through S-5 (routed, C26)] |
| `RS4Chain.shDom/shEvtH/visH/shEvt/shWeightH/shevt_grouping/shDom_ne/sh_realized/shweight_card/wshval_card` | [SPLIT: the per-ε̊ shallow ingredients (entrance domains entDom/H(ε̊), entrance events entEvt/entEvtH, ιshH weights — §2.F/§2.G) are MovesV's, at V7-4b's entrance side; the per-SHAPE Ŝ assembly over trees is MovesT's (shapes are [3t] vocabulary). The re-keying REPLACES MovesS's device fields by production objects only when BOTH halves exist — per S-8/S-10's re-keying charge] |
| `RS4Chain.Rval/r_bdd/decidedTotal/x3_total/rs1_equates/rsh_interp` | [owners [3t]/[5]/[3] — W-1/W-4 pins; μ̂/density fence: nothing here is MovesV's to state] |
| `ReadOffBundle.pkg` | [owner [3] — E0 packages] |
| `ReadOffBundle.read` (AVAgree) | [MovesV: V4-3 states the (ii-c) duty in MovesS's own AVAgree shape; the CHECK is RESUM-n3's ([3]'s gate) — recorded, never a blanket claim] |

### 4.3 The seam entries RE-KEYED by this blueprint (count: 6)

1. **S-2 (`W2_xrb` package fields)** — the four `xhd_*` Prop placeholders in
   `XRBPackage` re-keyed to THE ONE Prop `xhdStmt := Nonempty (XHD n S V)`
   at the V7-4 instance (V7-7; C27: one coherent package — same weights,
   domains, sums — never four unrelated existentials).
   `jc_inv`/`sib`/`tb_cap`/`vp`/`rel2_*` stay with their owners
   ([2b]/[3t]/[2r]).
2. **S-8 (`W17ii` + `Wsh17Package`)** — the `cts_counts` field re-keyed to
   `cts_counts_stmt := ValA ∧ EntCount` (V7-7); the DEMANDED `xhd_s` face is
   DELIVERED as a FIELD of the DISPLAYED `Wsh17PackageV` (V7-7 — Codex-17:
   a type, not a floating Prop). THE EMPTY-MENU LEG IS **OWNER-SIDE OPEN**
   (SEAM FLAG SF-2, replacing rev 2's contradictory S-5 routing claim):
   W17ii's vacuity fence stays open until [3t] types `TreeIface.tree_ne` AND
   retypes `W7_cutWD`'s obsolete `isDeepSplit → ¬ isEntrance` clause to the
   first-entrance-ancestor form; MovesV claims only its two delivered legs.
3. **S-9 (packages as registries)** — the [1v]/[2b]-XHD names in the
   registries now point at ONE typed bundle with content-pinning fields
   (doctrine satisfied: degenerate instances violate typed laws — chainCount
   definitional, non-vacuity fields, exactness over real counts).
4. **W-6 (wild-pool read-off, AVAgree)** — cited per consumption site: V4-3
   is the [1v]-side citation form.
5. **W-11 (instantiation of every §2 structure by the REAL CTS objects)** —
   the process gate is now the concrete unit list V7-3a/b/c/d, V7-4a/b/c,
   V7-5, V7-6a/b/c (+ V2-9); DONE when those build. The SCSData/KmatHyp rows
   are part of this gate (C25/Codex-20).
6. **CL-18 (J-RAT) owner-side record** — the PLAN-SYNC flag's demand ("the
   owner notes' NEXT revision rounds must record these deliverables on their
   side") is discharged FOR THE LEAN CORPUS by §2.H + V5-7a/b/c: the
   per-cell tables are typed PER (τ, o) INCLUDING split routes (C8), their
   ℚ(q)-membership stated in the (iv)-POLY pattern, the not-the-marked-T·G
   fence machine-checked. (The NOTE text itself is accepted and unedited —
   this is the Lean-side record, exactly as the flag prescribes cross-note
   binding through the ledger.)

NOT re-keyed here (recorded): MovesS seam entries S-1/S-1e/S-1m, S-3, S-4,
S-5, S-6, S-7, S-10, S-11 (MovesT's vocabulary — trees, fibers, read
ledgers, RS.1); MovesD's §2.5 entries W4-1..W4-4 (TreeModel semantics,
VerdictModel, D4R_CYL consumer, NP-ID — MovesT/HC-2's). (JC-INV)/CL-19 is
[2b]'s and appears in NO MovesV statement. SEAM FLAG SF-1 (V7-4b): MovesT's
h_ent binding must use the Hgt-indexed entrance carriers, not
`MeasuredSide.hent` (retained at REV 3 over Codex-7's objection, on Fable's
round-2 source verification that no MovesS law reads the field — the
disagreement and its resolution are on the record at V7-4b). SEAM FLAG SF-2
(new, V7-7/S-8): W17ii's empty-menu vacuity fence is OWNER-SIDE OPEN — [3t]
owes `tree_ne` + the W7_cutWD first-entrance-ancestor retype; MovesV's S-8
delivery is exactly the two `Wsh17PackageV` fields.

## §5 Build order, process, and the census

**Build order (E-phase):** Defs → DefsGate → V0 → V1 → {V2, V6} (parallel;
V6 depends only on DefsGate + 2.A) → V3 → V4 → V5 → V7. The gate layer V6
is deliberately early-buildable: it is the corpus's non-vacuity anchor (the
sealed numbers re-derived in-kernel before any measured clause elaborates).

**Difficulty census: 82 units = 33 easy / 43 medium / 6 hard.**
Per layer: V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m] V3[11: 4e/5m/2h]
V4[12: 4e/6m/2h] V5[10: 3e/6m/1h] V6[10: 5e/5m] V7[15: 4e/10m/1h].
Delta vs rev 2 (71 = 31/35/5), all Codex-19/REV-3 driven: V1-8 → V1-8a/b/c
(3 medium); V7-2 → V7-2a (easy) + V7-2b (medium); V7-3 → V7-3a/c/d (medium)
+ V7-3b (easy); V7-4 (hard) → V7-4a/b/c (3 medium — the split de-escalates:
the wiring is now fully specified); V7-6 → V7-6a/b/c (3 medium); NEW V5-8
(`cell_refine`, medium — the derived count-bearing refinement); V3-3
re-graded medium → HARD (the (d) reconstruction bridge is the corpus's real
E-phase risk, hatch recorded); V4-12 re-graded medium → HARD (the restored
⟹ leg's generating-series separation).
HARD (escalation-risk set, pre-declared): V3-3 (reconstruction; split by
leg), V3-5 (instantiation bijection; split (a)/(b)/(c)), V4-6 (PART-1's
countable route; split (i)/(ii)/(iii)), V4-12 (the iff's ⟹ leg; split
(b-i)/(b-ii)), V5-2 (COMP-h grouping induction; split (a)/(b)/(c)), V7-5
(RatBurdens assembly; split (a)/(b)/(c)). WATCH (medium with known teeth):
V0-4 (double geometric sum in Qq), V2-6 (cyclic power-image cardinality),
V5-8 (the Fubini rearrangement over the (c,h) double sum), V6-1c/V6-3b
(the F4/F8/F9 table fields — decide feasibility over 9³·9 tuples is fine,
but the Field-instance decides need `Decidable` instances written with
care), V6-4c (the CoprimeLiftPack — Mathlib Hensel archaeology;
published-axiom fallback per campaign §4, flag before declaring).

**THE DESIGN-FREEDOM INVENTORY — COMPLETE, ALL FIVE SLOTS, ALL RESOLVED
(A-5 repair; per campaign §3(ii) each resolution is recorded WITH the audit
round, and no slot remains open into E-phase):**
1. `StepSys.inv` (rev-1 stub) → RESOLVED: DELETED. `C15Pack` already carries
   the pinned inventory carrier (`Inv`/`invOf`/`F`/`mass_factors` — the
   note's C.1(ii) role); nothing in the note demands a slot on `StepSys`
   (adjudicated at A-5, adopted here).
2. `XHDd.chain`'s recursion tie (rev-1 "field the E-designer adds") →
   RESOLVED: NO FREEDOM EXISTS. The note DEFINES T_γ; Lean encodes the
   definition (`chainCount` by recursion through `StepSys.ext`, §2.G); the
   exactness laws quantify over the defined count (C2/C9/A-2).
3. `moveOf` + the fixed-h form of `tbl_count` → RESOLVED: `moveOf` is a
   DISPLAYED CtsMeasured field with its bijection law (§2.F); the count
   semantics is `ValA.tbl_count`, stated representative- and height-uniformly
   at realized heights (V2-4 — VAL(a)'s burden, the note's own
   "alternative discharge" framing).
4. V4-1's `lands_in` → RESOLVED: the count-level landing tie is the ValA
   field `tgt_supported` (V2-4; "a landing forces a concrete target state"),
   consumed by V4-1 under the restored active-source guard (C15).
5. V3-9c's PolyGeom-closure vs OKat-landing route → RESOLVED: the CLOSURE
   route — PolyGeom add/scalar mini-lemmas local to MovesV (no MovesS edit);
   V3-9c(b)/V5-7b consume them.
6. (NEW at REV 3) the u*-slot ℕ-encoding (G-3) → RESOLVED: the slot carries
   zig(gam_r) (`Denumerable.eqv ℤ`); u* is the DISPLAYED gamTie inversion
   (§2.D); recorded with its tighten-at-MovesD hatch.
7. (NEW at REV 3) the instance-census box realization → RESOLVED: `entInst`/
   `stInst` are carrier DATA (box-embedded censuses at the defining levels)
   with the typed counting ties `ent_card`/`stInst_card`/`evt_card`/
   `box_card` pinning their semantics ([tie] fields; discharged by
   MovesD/MovesC at the real instance — D4R1_SUM/D0b_thmCtop, G4).
8. (NEW at REV 3) the `castMove/castHpt/castAssign` transport helpers
   (Refinement's assign_cover) → RESOLVED: mechanical ▸-wrappers, zero
   design content, one line each at E-phase (recorded so the inventory
   stays COMPLETE).

**Statement-fence inventory (changes needing sign-off):** none — every
structure above is new (additive); MovesS/MovesSp/MovesD are imported, never
edited. (The §4.3 re-keyings amend the SEAM CONTRACT's pins, which is that
contract's stated purpose — "NOT LEAN UNITS; re-keyed when the vocabulary
exists"; no frozen statement changes.)

**Non-vacuity anchors (the wave-2 doctrine, per package):** StepSys:
`cell_ne`/`zc_ne` + the REV-3 PRODUCTIVITY `out_ne` (the all-empty-fibers
adversary dies at the zc_ne witness — Codex-1) + the V1-8a realized
instance; XHD-w: positive weights are typed data (V0-1) + range lemma V1-1 +
V1-8a's witness; XHD-u (incl. T-twins): the rectangularity FALSITY witness
(V1-2(b)) + the (U-A)-does-not-imply-(u-R) fence V1-7 + V1-8a; XHD-d/XHD-dC:
two-sided exactness against the DEFINED counts (V1-3; degenerate domains
violate no_stray outright) + listed partition BY TYPE (2.A) + V1-8b/c;
XHD-s (all three faces, WEIGHT-ONLY): the PROVED A2-format witness V0-4 +
V1-8b/c — and the count factors live in the [1v] burdens, so no package
field can silently decide INIT-RAT/(J-RAT) (Codex-8/9); the counting ties:
realized by V1-8c's literal census data (ent_card/evt_card/box_card/
stInst_card all checked on the toy); HMC: the false-instance/true-instance
pair V4-11 + V4-12(c)'s single-system factorization-failure fence;
templates: terminal-final BY CONSTRUCTOR (+ the T-twin fields throughout —
Codex-2); J: route-keyed roster with the GATE-NONZERO lemma (V5-7a — the
F-6 emptiness adversary dies) + the not-marked-T·G fence V5-7c; ε:
post-split distinctness V3-1 (selRank semantics, E8_rankInj) + WF
entry/eligibility/menu ties (C6), heights-retained discrimination V3-2;
ε̊: intrinsic finiteness V3-4; cell_refine: DERIVED with the count displayed
(V5-8 — the (q−1)² collapse adversary dies); gate: 100+ sealed numbers
re-derived (V6-1a..V6-4a) including the m_H3 = 0 falsifier, at all nine
census points, + the F-1 counting check 128 = (1/4)·512 (ent_card at gate
B).

**Honest-perimeter recap (what a corpus record may claim when all 82 build):**
CTS-M's clauses machine-checked EACH GIVEN EXACTLY its V.1-ledger set
(V7-2b, conclusions displayed at V7-2a); (U-A) proved given the typed §C
pack; the V-n3 displays re-derived in-kernel at all nine census points
(V6-4c's threshold conditional on the typed CoprimeLiftPack premise); the
MovesS seam supplied per §4 — with XHD (all faces incl. dC)/(XHD-u)/
(ENT-U)/HMC/ENT-COUNT/INIT-RAT-premises/(J-RAT)-cell-pack/(ii-c)/
CL-13-coverage/ContTwo/StageLawBurden all OPEN, riding as typed arguments —
and the W17ii vacuity fence OWNER-SIDE OPEN (SF-2). NOTHING here is "the
density R_σ": every mass is μ̂-typed or counting-native; the marked→per-f
conversion stays [3t]'s.

## §6 DISPOSITION TABLES

### §6.1 Round 1 → REV 2 (historical; the round-2 audits re-adjudicated
several of these rows — where a rev-2 "REPAIRED" was refuted, the governing
row is now in §6.2: C24 → F-1/F-3/F-4, C23's cellP leg → F-5, C8's roster →
F-6, C1/C2/C5/C6/C7/C9/C14/C15/C19/C21/C22/C25/C26/C28/C29 → Codex-round-2
1–20)

Codex findings C1–C29 (`MOVESV_AUDIT_CODEX_2026-07-28.md`), Fable findings
A-1–A-7 (`MOVESV_AUDIT_FABLE_2026-07-28.md`). "Fixed at" names the governing
section/unit of REV 2.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| C1 | XHD packages vacuously inhabitable | REPAIRED: cell_ne/out_ne/zc_ne fields + per-structure witness unit | §2.B, V1-8, §5 anchors |
| C2 | cntraw/chain/cellEvt untied | REPAIRED: cntraw + chainCount are DEFS; cellEvt = assignment biUnion | §2.B, §2.G, §2.F |
| C3 | A2 exponent ∉ natural AffineE | REPAIRED: (t,u) declaration + chart-as-definition; display identity 2E = 3(h₀+h₂)−1 | §2.A convention, §2.I, V0-4, V6-2a/b |
| C4 | declaration order / invalid types | REPAIRED: VLabel→2.A; XHD bundle→2.G; GenKind inductive | §2.A/2.C/2.G |
| C5 | (D2) weakened to a String | REPAIRED: GenKind.rel carries relPoly; part_eq forces the twist | §2.C |
| C6 | EntShapeV triple untyped | REPAIRED: hentry/helig/hlen/hmenu WF fields; sibling law V3-1(b) | §2.D, V3-1 |
| C7 | V7-4 cannot produce MeasuredSide | REPAIRED: pool laws added; all fields defined from V + XHD; Cell granularity = outcome fibers; finE from V3-4 | §2.F, V7-4 |
| C8 | J tables not per-(τ,o) | REPAIRED: DCellO outcome-keyed; JCells/Jval/V5-7b per (s,m,o,α) incl. split | §2.F/2.H, V5-7a/b |
| C9 | V2-5 false as stated | REPAIRED: chainCount definitional; valB via u_R/u_T route; degree bound re-scoped to the path-product polynomial | V2-5 |
| C10 | V2-8 proves only zero-twist | REPAIRED: part_eq structural (twisted BY TYPE at a_eff ≠ 0); zero case a corollary | §2.C, V2-8 |
| C11 | V2-10 witness contradicts examples | REPAIRED: gate values recorded with true directions; synthetic Wstate > Wloc witness | V2-10 |
| C12 | V3-4 weakens finiteness | REPAIRED: intrinsic WF fields; finiteness proved OUTRIGHT, no premise | §2.D, V3-4 |
| C13 | V3-6 false iff | REPAIRED: iff struck; ≤ + one-directional equality + D10 tie | V3-6 |
| C14 | V3-8 underivable from XHDs | REPAIRED: XHDsEnt entrance face (sums of the DEFINED ιshH) + XHDdEnt | §2.G, V3-8 |
| C15 | V4-1 drops active-source guard | REPAIRED: guard restored; zero claimed only from active sources | V4-1 |
| C16 | V4-5 omits XHDw | REPAIRED: X : XHDw explicit; w_eq supplies the q^{−E} identification | V4-5 |
| C17 | V4-6 hypotheses undisplayed | REPAIRED: full signature displayed (pack + XHDw/d/s + four typed legs) | V4-6 |
| C18 | V4-8 gate fragment only | REPAIRED: ContTwo premise displayed (continuing size ≥ 2); gate decide + general lemma | V4-8 |
| C19 | V4-12 iff invalid | REPAIRED: extensional ⟹ STRUCK; ⟸ + machine-checked failure fence; adjudication recorded | V4-12 |
| C20 | census weakened to six primes | REPAIRED: F4/F8/F9 table fields; all nine points in-kernel | §2.I, V6-1c, V6-3b |
| C21 | CoprimeLiftPack unauditable | REPAIRED: fields displayed (unique coprime lift + determinacy, nothing stronger) | §2.I |
| C22 | CtsmConclusions opaque | REPAIRED: field list displayed incl. VAL(b), INIT-RAT, ACTIVE-VALUE record, count shadow, solve sentence | V7-2 |
| C23 | V7-5 legs type-wrong | REPAIRED: tgP gains the G-bearing face; ιP per-component (V3-9c(a)); cellP re-keyed to CellPolyPack | V7-5, V3-9c |
| C24 | V7-6 fields unsupplied | REPAIRED: μcell/gwt/rowVal/kstep DEFINED from XHD; cell_refine; init_count/comp_once re-keyed | §2.F/2.G, V7-4, V7-6 |
| C25 | SCSData dropped; KmatHyp misattributed | REPAIRED: SCSData row field-by-field (data ← species fields; laws ← gate decide + [2a] burden); KmatHyp = Prop, proved at gates | §4.1, V7-3 |
| C26 | S-8 vacuous; xhd_s missing | REPAIRED: wsh_xhd_s_stmt delivered; Sh-nonemptiness routed to [3t] tree_ne via S-5 | V7-7, §4.3 |
| C27 | XHD re-keyed as unrelated fragments | REPAIRED: ONE xhdStmt = Nonempty (full bundle); all four fields re-keyed to it | V7-7, §4.3 |
| C28 | units conceal multiple declarations | REPAIRED: lemma-roster format amendment; rosters displayed at V0-2/V2-1/V2-2/V6-4a (+ others) | §3 preamble |
| C29 | placeholders unauditable | REPAIRED: every named carrier displayed; checklist | §2.J |
| A-1 | entrance carrier granularity broken | REPAIRED: EntIx (template × component); ιDom/ιshH/ιsh/ιval defined; hent ADJUDICATED + seam flag SF-1; per-component PolyGeoms exposed; init_count re-keyed | §2.F/2.G, V3-8/9c, V7-4/6 |
| A-2 | chain recursion has no carrier | REPAIRED: StepSys.ext (normative Defs amendment); chainCount definitional | §2.B/2.G |
| A-3 | WordBounded under-pinned; EntranceShape unused | REPAIRED: intrinsic WF fields incl. menu bounds; V3-3(c) constructs the MovesSp.EntranceShape | §2.D, V3-3, V3-4 |
| A-4 | V6-1c f″ sketch false at p = 2 | REPAIRED: char-free divisibility multiplicity | V6-1c |
| A-5 | design-freedom inventory incomplete | REPAIRED: all five slots listed AND resolved | §5 inventory |
| A-6 | §0 banner overstates V6 | REPAIRED: V6-4c scoped out by name; census scope stated | §0 |
| A-7 | dangling-display cluster | REPAIRED: u_T_dom pointer removed; HMCAug displayed; V1-7 ∃-nested; V0-1 binds h; IsPP defined; eligibility ties added; §4.2 pointers fixed | §2.A/2.B/2.G, V0-1, V1-7, §4 |

### §6.2 DISPOSITION TABLE (round 2 → REV 3)

Codex round-2 findings 1–20 (`MOVESV_AUDIT_CODEX2_2026-07-28.md`; cited as
X-1..X-20), Fable round-2 findings F-1–F-6 / G-1–G-4
(`MOVESV_AUDIT_FABLE2_2026-07-28.md`). "Fixed at" names the governing
section/unit of THIS revision. The gate numbers the audits supplied are the
acceptance tests and are checked at the named sites.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| F-1 | ιshH body = ι·q^{n·entLvl−A} (event card, not census; gate 8192 ≠ 128) | REPAIRED: entInst census carrier + ent_card counting law; ιshH := census·q^{−A}; gate check 128 = (1/4)·512 displayed | §2.F (entInst/ent_card/box_card), §2.G ιshH, V7-6a |
| F-2 | entCount = box-event card; ι_count+ι_degT+degT_le jointly unsatisfiable | REPAIRED: entCount := the census (deg 2 ≤ Went 3 at gate); EntCount per CONCRETE ε against entCensus; EntU over the census | §2.F entCount, V3-9a/b, V7-4b |
| F-3 | meas_card/no_stray/no_orphan/d4r0 have no derivation AS TYPES | REPAIRED: evt_card + box_card [tie fields]; XHDdC cell d-face; ONE AStep disjointness law (cross-move/height/assignment/terminal) — suite derivable field-by-field | §2.F, §2.G XHDdC, V7-6a |
| F-4 | cell_refine forces T ≡ 1 ((q−1)² adversary); kstep drops ∏T | REPAIRED: XHDsC weight-only; cell_refine a DERIVED unit with the count displayed (Σ P_c·ΣGcell = T·ΣGc); kstep := Σ (pathProdPoly).eval·ΣGc | §2.G XHDsC, V5-8, V7-4c |
| F-5 | cellP ← CellPolyPack regression (cellP_deg broken at both gates; act_iff false at q₀ = 2) | REPAIRED: REVERTED to the rev-1 sizeP wiring; stLvl/stInst/stInst_card state-census fields added; ActIff premise deleted (act_size suffices) | §2.F, V7-4a, V7-5(d) |
| F-6 | roster_tie (emult ≥ 2) empties every n = 3 roster; Jval ≡ 0 | REPAIRED: route-keyed bcells (ALL cells of a split-route outcome, once); gate-nonzero lemma; V5-7c's algebra re-keyed with its roster premise displayed | §2.H, V5-7a/c, V7-3a (route_eq) |
| X-1 | out_ne forbids empty menus yet admits all-empty Assign models | REPAIRED: out_ne re-keyed to realized-history PRODUCTIVITY (menus may be empty; unrealized models violate it at zc_ne's witness) | §2.B |
| X-2 | terminal-final steps missing from XHDu/C15Pack/events/cells | REPAIRED: T-twins typed throughout via the displayed substitution table (XHDu ×3, C15Pack ×2, CtsMeasured events/domains/classifiers, XHDsC GcellT, XHDdC, CellPolyPack.countT, ValA.tbl_countT, Refinement twins) | §2.B convention + per-structure fields |
| X-3 | relPoly decorative; tcell not forced on moveOf | REPAIRED: GenSpec.rel_eq (partition factors through the polynomial) + twist_add (ℤ-action); moveOf target = d.tgt BY TYPE with moveOf_bij over MoveData | §2.C, §2.F |
| X-4 | tbl_count weak at zeros + smuggles (u-T); V2-5 unconnected to C.T | REPAIRED: base-point-keyed unguarded tbl_count; valB restated against (pathProdPoly C γ).eval q₀ with ValA+u_T route | V2-4, V2-5 |
| X-5 | selRec entries unrelated to actual selections | REPAIRED: σ_sel pinned as the L11 selRank data (definitional at the label; E8_rankInj at instances); V3-1(b) re-scoped; EligPair/IsBranchingRead/branchMenuCard closed over named MovesD decls | §2.D, V3-1 |
| X-6 | template lossy (bijection false); no_orphanE lacks landing | REPAIRED: V3-3(d) readOfLetter + spWord_faithful (reconstruction as a THEOREM, hatch recorded); writeHeights displayed; XHDdEnt.lands_of_realizable | §2.D, §2.G, V3-3/V3-5 |
| X-7 | EntIx collapses ENT-COUNT to base point; hent scalar | REPAIRED at the count: EntCount per concrete ε (census); base-collapse only in entCount's DEF with (ENT-U) cited at consumption. hent: ADJUDICATED-RETAINED (round-2 auditor disagreement resolved on Fable's source verification; SF-1 stands, re-opened iff a MovesS law ever reads hent) | V3-9a, §2.F, V7-4b |
| X-8 | XHDsEnt assumes INIT-RAT + double count in V3-9c | REPAIRED: Gent weight-only; counts enter via EntCount/(ENT-U); V3-9c countT×geom now counts once; V3-8 displays the (ENT-U) premise (adjudication recorded) | §2.G, V3-8, V3-9c |
| X-9 | cell_refine arithmetic wrong; V5-7b count-squared | REPAIRED: = F-4 + jRat over weight-only Gcell × CellPolyPack (no re-multiplication) | §2.G, V5-8, V5-7b |
| X-10 | events untied to LedgerIV (no card law; evt_disj same-h only; cdom unexact) | REPAIRED: = F-3 (evt_card/AStep disjointness/XHDdC) | §2.F/2.G, V7-6a |
| X-11 | kstep omits transition counts | REPAIRED: kstep carries (pathProdPoly).eval — kstep_one = V5-8's identity | V7-4c, V7-6b |
| X-12 | V2-7 cells overlap at (0,0) | REPAIRED: FL/FS with nonzero coordinate; partition of the nonzero target; origin lemma separate | V2-7 |
| X-13 | HMCAug satisfiable by an unrelated refinement | REPAIRED: Refinement fully typed (moveProj/dim_eq/assignOf/mass_eq/assign_cover Σ-bijection + T-twins); count laws now lemmas | §2.G |
| X-14 | V4-12 weakens the frozen IF AND ONLY IF | REPAIRED: the iff RESTORED at the ∀-weight-system quantifier — ⟸ proved, ⟹ = the generating-series separation (HARD, split); single-system fence retained as (c) | V4-12, §0 banner |
| X-15 | iota_supp under-hypothesized | REPAIRED: ValA.ent_supported (the note's own landing sentence); iota_supp derivable | V2-4(d), V4-1 |
| X-16 | cellP unsuppliable from CellPolyPack; no cellLvl/cellInst | REPAIRED: = F-5 (sizeP revert + stLvl/stInst/stInst_card); CellPolyPack retained ONLY for (J-RAT)/V5-8, closed and domain-keyed | §2.F/2.H, V7-5(d) |
| X-17 | Wsh17 xhd_s not expressed as a type; S-5 routing contradictory | REPAIRED: Wsh17PackageV displayed AS A STRUCTURE (wsh_xhd_s a field); the empty-menu leg re-scoped to SEAM FLAG SF-2 (owner-side OPEN — no closure claimed) | V7-7, §4.3 |
| X-18 | placeholder checklist not closed (7 named clusters) | REPAIRED: every named item displayed closed — Refinement (no `…`), CellPolyPack, CtsmConclusions (V7-2a structure), CoprimeLiftPack (reduce2; determinacy by type), MoveData/TermData/dataOf, writeHeights, Hpt.take/drop, emult (a field), moveOfT_bij, F4/F8/F9 tables, EligPair-cluster named-keyed | §2.J (the audit trail) |
| X-19 | V1-8/V7-2/V7-3(d)/V7-4/V7-6 conceal multi-lemma constructions | REPAIRED: split into V1-8a/b/c, V7-2a/b, V7-3a/b/c/d, V7-4a/b/c, V7-6a/b/c — census 82 = 33/43/6 | §3, §5 |
| X-20 | general SCSData/KmatHyp supply untyped | REPAIRED: StageLawBurden (closed structure, all twelve laws + kmat_all + degcons_all), a CtsmLedger field; gate restriction by decide | V7-3d, V7-1, §4.1 |
| G-1 | E = 6t+3u+1 misattributed to the note (×2 + moves_ref splice) | REPAIRED: both sites + V0-4's moves_ref corrected — ours, derived; note displays (3(h₀+h₂)−1)/2 + the substitution | §0, §2.I, V0-4 |
| G-2 | x²+1 over F₃ called a Conway polynomial | REPAIRED: provenance corrected (C_{3,2} = x²+2x+2; ours is merely irreducible) | §2.I |
| G-3 | u*-slot ℚ/ℕ encoding unpinned | REPAIRED: zig(gam) slot code + gamTie inversion, displayed; hatch recorded; V3-5(c) checks the roundtrip | §2.D, V3-3(d)/V3-5 |
| G-4 | V3-6(c) cites a proof-internal `key` | REPAIRED: re-pointed to exported D4R1_SUM/D0b_thmCtop (also ent_card's discharge cite) | V3-6, §1, §2.F |

VERIFIED-CLEAN CORES (both round-2 audits) LEFT UNTOUCHED, as charged: the
A2 chart complex (§2.I/V0-4/V6-2a/V6-2b — re-derived independently by both
auditors), the doctrine core (cell_ne/zc_ne/cntraw/chainCount/ext), the
EntIx carrier TYPE itself, the V6 gate layer (V6-1a..V6-4c incl. censusQ,
the m_H3 falsifier, the two-history discipline, the A-4 char-free
multiplicity), and the §4 field lists verified verbatim against the built
MovesS sources.

*(End of MOVESV blueprint REV 3. Next per campaign §3: Codex/Fable semantic
audit of this revision + Defs; REJECT loops until ACCEPT; then E-phase.)*
