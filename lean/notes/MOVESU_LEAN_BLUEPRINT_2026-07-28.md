# MovesU — Lean blueprint for §U-SQUEEZE (Theorem U, conditional form)
# REV 2 (post-Codex-audit, 13 findings repaired) — 2026-07-28

*Codex audit `MOVESU_AUDIT_CODEX_2026-07-28.md`: REJECT (10 crit / 3 gap). REV 2 repairs
ALL 13 in one batch; the findings→repairs table is §7. Architecture changes: `Census`
REPLACED by `ClassifierSpec` (the verdict IS the interface's canonical classifier map,
with characterizing Props — F1/F13); `SplittingType n` concrete (F11); `RegData` carries
the FULL displayed entry list + nonemptiness (F4/F10); the kernel ledger is a
`KernelStatements` pack asserted per-CL by `CapstoneLedger` (F5/F6/F7); U10 gains the
∃-ONE-fixed-R form + the density-identification conjuncts (F11/F12); exact partial-sum
identity (F3); positivity (F8); primality (F9).*

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

**D2 — The box is concrete; the verdict is THE CLASSIFIER INTERFACE (F1/F13).**
`Box p n N := Fin n → ZMod (p ^ N)` (`Nat.card = p^(n*N)`). `Census` is DELETED. In its
place `ClassifierSpec n p` — the MovesC-precedent interface structure (cf. MovesD's
`PrefFamily` carrying jet/enc/hist_inj), owner MovesD + HC-2 (the OM engine) — carries:
`trueType N f` (the GROUND-TRUTH factorization type of the level-N class, abstract here,
the ONE semantic pin; owner HC-2); `canonical N f` (T_can^τ's verdict-type map — "a
CHOICE-FREE function of f", [1] L2 + VP + ONE-F); `canonical_sound` (a decided verdict
AGREES with `trueType` — VP/VP-SOUND at interface strength); `canonical_stable` (a
level-N decision persists to every N' ≥ N along `ZMod.castHom` reduction — TREE-N's
thr ≤ N join / Thm 2.1 decision stability). `decided`/`undec`/`env`/`dmass` are DEFINED
from `canonical` — an arbitrary labeling is no longer an instance: the verdict function
is pinned to the named upstream object with its characterizing Props. (BOX-N) stays a
tag-free count identity (it holds for the interface's canonical map by counting alone).

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
D7).

**D5 — (REG-p) is a Prop schema over the FULL displayed entry bundle (F4/F10).**
`RegData p` now carries: `depthSet : Finset ℕ` with `one_mem_depthSet : 1 ∈ depthSet`
(the base-change depths of RS.1-SH's assembly, owner MovesS; δ = 1 always arises) and
`pool_eq : Pool = depthSet.image (p ^ ·)` — Q(p) is EXACTLY the pool set, nonempty by
construction (p ∈ Pool), never an arbitrary Finset; `Block` with `instNe : Nonempty
Block` (the top block exists); the matrices `K`; AND ALL remaining displayed entry
families as data: `bterm`/`bsplit` (both b_e components), `Jcell` (the per-cell J
entries, CL-18), `iota` (ι_e), `Wcoef` (the W_Ŝ coefficients), `betaLegs` (every
β_{e,τ} entry, all base-changed legs). `entryList e` is a DEFINITION — the union of the
seven families, exactly SQ.4's displayed E(e) — not a free field, so (r2) quantifies
over the whole display and nothing can be silently dropped. `act` stays abstract
(CTS-M(ii)'s semantics, owner [1v]); RegP stays the rev-5 SEPARATE hypothesis.

**D2 — Tonelli is typed in ℝ≥0∞.** The tree-fiber series (RS.1's positive series) lives
in `ℝ≥0∞`: `seriesSum σ := ∑' T, mass σ T` exists UNCONDITIONALLY (`ENNReal.summable` —
every ℝ≥0∞ family is summable), and every finite partial sum is dominated by the tsum
(`ENNReal.sum_le_tsum`, `ENNReal.tsum_eq_iSup_sum`). This is rev 2's retyped SQ.2 clause
verbatim: existence tag-free; FINITENESS (`seriesSum σ ≠ ⊤`) and IDENTIFICATION with
R_σ(p) are ledger fields (the tagged stack), never Tonelli's.

**D3 — Finiteness of the decided family is DATA-level.** `FiberSeries.thrSlice σ N :
Finset (Tree σ)` — the thr ≤ N slice is Finset-typed, so SQ.0/CL-7's finiteness
(TRACK-COUNT + D(n) + the genuine-increment sub-claim) rides the INSTANTIATION: whoever
builds a `FiberSeries` from MovesD trees must produce the Finset, which is exactly CL-7's
open duty. Flagged in the docstring; no silent strengthening — the abstract corpus never
proves finiteness, it consumes it.

**D6 — Literal evaluation.** `evalℝ S σ p := ((S.R σ).eval (RingHom.id ℚ) (p:ℚ) : ℝ)`
(Mathlib `RatFunc.eval`, junk-valued at poles). The theorem NEVER consumes `evalℝ` except
under `RegP D`, where the ledger's solve-stack field asserts the identification — so the
junk case is never load-bearing. The WILD-p/ACT reading is carried by (r2)'s agreement
clause inside `RegP`, exactly the note's "the two readings coincide, so ρ_σ(p) = R_σ(p)
is well-typed".

**D7 — The kernel ledger: a `KernelStatements` pack + per-CL assertion fields
(F5/F6/F7).** The open kernels are STATEMENTS owned upstream; MovesU cannot re-state
their content, but it CAN carry them as named Prop-valued parameters. `KernelStatements`
is a structure of ~30 `Prop` fields — one named slot per open kernel/obligation of the
capstone ledger (escapeE0, weightCharge, progressX2 with the (X2-*) family, the CL-5
nine individually, ivPoly, trackCount/dnDuty/genuineIncrement, the six CL-8 REL legs,
rs0LumpBisim, sib/sibStep/jcMulti/treeExpNs/vpSound, noEqualEFeedback/degCons,
ctsmSyntax (the move menus, empty-menu/(BDY) conventions, target-cell maps — F7),
ksubM1C1 (the (m,c) classification incl. the equal-e m = 1, c = 1 rows — F7), m1m5,
x1aDict, m4bConstancy, rs1Assembly, jRat, jcInv) — filled with the REAL statements at
instantiation (owners named per field). `CapstoneLedger` then has a field PER CL ITEM
(`cl1_escapeE0 : K.escapeE0`, …, `cl19_jcInv : K.jcInv` — CL-2/CL-3 INCLUDED even though
the qualitative limit never uses their constants: the frozen theorem is conditional on
the COMPLETE ledger, F6) PLUS the four operative consumption fields (`finiteness_stack`,
`solve_stack` — now with EXPLICIT positivity, F8 —, `rs4_checksum`/`rs4_eval`,
`cl4_env_tendsto`), each operative docstring naming the CL items whose consequence it
is. Every kernel is now a REAL hypothesis field, not a docstring (F5). (REG-p) is NOT a
ledger field: the ONE explicit hypothesis (rev 3, pass-2 critical 2).

**D8 — NO-CLAIM failure semantics = the restricted quantifier, no Lean artifact.** The
theorem's conclusion is `∀ p, p.Prime → RegP D → (...)`. At a p failing (REG-p) the
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
What the abstract corpus CAN pin, it now does (canonical soundness + stability, the
slice characterization, the full entry list, pool/block nonemptiness, concrete
SplittingType); what it CANNOT pin (that `trueType`/`canonical`/the kernel Props are the
real ones) is exactly the conditional-over-interface boundary of the MovesC precedent,
declared here and at every consuming unit. The audit's fake instance is dead: constant
verdicts now contradict `canonical_sound` against any faithful `trueType`, `RegP` is
never vacuous (Pool ∋ p, Block nonempty), and `K.trackCount := True` etc. is a
fidelity violation caught at instantiation review, not a satisfiable reading of THIS
corpus's claims.

**The four TAG-FREE units** (= the note's re-audited unconditional perimeter, and the
only units proved without ledger fields): `U1_boxN`, `U2_tonelli`, `U5_sq3_arith`,
`U7_squeeze`. Everything else consumes hypothesis-structure fields and says so.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesU/Defs.lean` (inline; elaboration-phase target)

```lean
import Mathlib
namespace LeanUrat.MovesU
open Filter Topology ENNReal

/-- A splitting type of degree n: "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n"
    (SQ.4, verbatim; entries ≥ 1). CONCRETE — F11's repair. Fintype: unit U0b. -/
def SplittingType (n : ℕ) : Type :=
  {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n}

/-- The level-N monic coefficient box: n free coefficients mod p^N (p^{nN} classes). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- The level reduction Box p n N' → Box p n N for N ≤ N' (`ZMod.castHom`, p^N ∣ p^N'). -/
noncomputable def boxProj (p n : ℕ) {N N' : ℕ} (h : N ≤ N') : Box p n N' → Box p n N :=
  fun f i => ZMod.castHom (pow_dvd_pow p h) _ (f i)

/-- THE CLASSIFIER INTERFACE (F1/F13 repair; replaces Census). HYPOTHESIS STRUCTURE,
    owner MovesD + HC-2 (the OM engine) — the MovesC `JetSetup` precedent.
    `trueType`: the GROUND-TRUTH factorization type of the level-N class (abstract; the
    semantic anchor, D9). `canonical`: T_can^τ's verdict-type map — "T_can^τ is a
    CHOICE-FREE function of f" ([1] L2 + VP; [3t] ONE-F); `some σ` = complete finite
    realizable tree, all leaves (τ-irr)/(τ-hen), certified at level N (thr ≤ N).
    `canonical_sound`: "the classifier verdicts are the true factorization types"
    (VP + VP-SOUND's citation duty, at interface strength). `canonical_stable`:
    TREE-N's join / Thm 2.1 decision stability — a decision persists upward. -/
structure ClassifierSpec (n p : ℕ) where
  trueType : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_sound : ∀ N f σ, canonical N f = some σ → trueType N f = some σ
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ

variable {n p : ℕ}

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
  pool_eq : Pool = depthSet.image (p ^ ·)      -- Q(p) IS the depth image (F4)
  Block : Type
  instB : Fintype Block
  instNe : Nonempty Block                      -- the top block exists (F4)
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)   -- {each entry of K_e}
  bterm : ∀ e : Block, bidx e → RatFunc ℚ      -- b_e^{term,fin}
  bsplit : ∀ e : Block, bidx e → RatFunc ℚ     -- b_e^split
  Jcell : Block → Finset (RatFunc ℚ)           -- every per-cell J entry (CL-18)
  iota : ∀ e : Block, bidx e → RatFunc ℚ       -- {each entry of ι_e}
  Wcoef : Finset (RatFunc ℚ)                   -- {each W_Ŝ coefficient}
  betaLegs : Block → Finset (RatFunc ℚ)        -- every β_{e,τ} entry, all pools' legs
  act : RatFunc ℚ → ℕ → ℚ                      -- ACT active value at a pool

/-- E(e) — a DEFINITION, verbatim the union SQ.4 displays (nothing droppable; F4/F10).
    (Classical DecidableEq on RatFunc ℚ for the images.) -/
noncomputable def RegData.entryList {p : ℕ} (D : RegData p) (e : D.Block) :
    Finset (RatFunc ℚ) :=
  letI := Classical.decEq (RatFunc ℚ); letI := D.instBi e; letI := D.instBd e
  (Finset.univ.image fun ij : D.bidx e × D.bidx e => D.K e ij.1 ij.2)
    ∪ (Finset.univ.image (D.bterm e)) ∪ (Finset.univ.image (D.bsplit e))
    ∪ D.Jcell e ∪ (Finset.univ.image (D.iota e)) ∪ D.Wcoef ∪ D.betaLegs e

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every member of the DEFINED E(e)
    (all seven displayed families, F10) defined at q₀ AND literal = ACT active value
    ((ii-c) agreement). Neither implies nor is implied by E0/CL-1 or ACT/CL-5 (D5).
    Never vacuous: Pool ∋ p^1, Block nonempty (F4). -/
def RegP {p : ℕ} (D : RegData p) : Prop :=
  ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀

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
  mass : ∀ σ, Tree σ → ℝ≥0∞                     -- μ(fiber T): RS.1's positive series
  thr : ∀ σ, Tree σ → ℕ                         -- TREE-N's threshold
  thrSlice : ∀ σ : SplittingType n, ℕ → Finset (Tree σ)
  mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ thr σ T ≤ N
  slice_exhausts : ∀ σ (T : Tree σ), T ∈ thrSlice σ (thr σ T)   -- kept explicit (F2)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (σ : SplittingType n) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

end LeanUrat.MovesU
```

## 2b. The kernel pack + capstone ledger (Defs, continued) — THE trust surface

```lean
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
  vpSound : Prop          -- CL-10 [3t]: VP (TB-CAP per clause) + VP-SOUND's two cites
  noEqualEFeedback : Prop -- CL-11 [4]/[1v]: no-equal-e-feedback + DEG-CONS full roster
  ksubM1C1 : Prop         -- CL-11/CL-13 face (F7): (K-SUB)'s (m,c) classification —
                          --   equal-e continuation EXCLUSIVELY in m = 1, c = 1 rows;
                          --   the empty-menu/(BDY) conventions ride here
  ctsmSyntax : Prop       -- CL-13 [1v]: CTS-M(i) SYNTAX — the ONE fixed finite state
                          --   set, move menus, cell predicates, target-cell maps (F7)
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
    (S : SolveData n) (D : RegData p) (K : KernelStatements) : Prop where
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
  cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN ∧ K.vpSound
  cl11 : K.noEqualEFeedback ∧ K.ksubM1C1
  cl13 : K.ctsmSyntax
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
  solve_stack : RegP D → ∀ σ,
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
  rs4_eval : RegP D → ∑ σ, evalℝ S σ p = 1
  /-- OPERATIVE trace of CL-4 = X.3 (QUALITATIVE form — "the limit consumes no
      envelope constant"; the statement slot is `cl4` above; discharges only at [5]'s
      EVENT): env(N) → 0. The quantitative rate form (CL-2/CL-3's constants) is
      asserted via the `cl2`/`cl3` slots but not consumed by any MovesU proof — gate
      SQUEEZE-n3 is a census artifact, not a Lean unit. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)

/-- THE PER-p INSTANTIATION BUNDLE (for U10's quantifier shape): everything Theorem U
    needs at one prime, over the FIXED SolveData. -/
structure UInstance (n : ℕ) (S : SolveData n) (p : ℕ) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  K : KernelStatements
  L : CapstoneLedger n p X F S D K
```

Greppable audit: every CL-1 … CL-19 item is now a REAL hypothesis field (F5) — the
`cl1`…`cl19` assertions over named `KernelStatements` slots — with CL-2/CL-3 present
(F6) and CL-12 correctly absent (CLOSED — "NOTHING at CL-12 is open"; its O3 base-pin
display duty is a write-up sentence, out of Lean scope).

---

## 3. The unit DAG — 12 units, one file each: `lean/LeanUrat/MovesU/<id>.lean`

Layers: L0 Defs+counting (U0, U0b, U1) → L1 series (U2–U4) → L2 bracket (U5–U6) →
L3 limit (U7) → L4 schema/aux (U8–U9) → L5 capstone (U10). TAG-FREE = proved with no
ledger/structure hypothesis fields beyond definitions.

### U0b `MovesU.U0b_splitTypeFintype` — splitting types are a nonempty Fintype  [support]
- **file**: `MovesU/U0b_splitTypeFintype.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
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
  (`canonical_sound`/`_stable`) are carried by the structure, not consumed here.
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
- **statement** (F3's repair — the IDENTITY is the claim; domination is the corollary):
  `theorem sq2_partial (L : CapstoneLedger n p X F S D K) (σ N) :`
  `(X.decided σ N : ℝ≥0∞) = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T`
  and `theorem sq2_partial_le … : (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ`
- **moves_ref**: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
  positive tree-fiber series for type σ" (SQ.2 ROUTE)
- **sketch**: the identity IS `L.finiteness_stack σ N` (re-exposed as the unit's named
  statement so the exact claim is auditable, not hidden — F3); the corollary rewrites
  by it and applies U2 + `mul_le_mul_left'`.
- **hypothesis_fields**: `finiteness_stack` (CL-7 + CL-10).

### U4 `MovesU.U4_sq2_upper` — SQ.2, the fixpoint upper bound  [conditional]
- **file**: `MovesU/U4_sq2_upper.lean`  ·  **difficulty**: medium  ·  **deps**: U3
- **statement**: `theorem sq2_upper (L : CapstoneLedger n p X F S D K)`
  `(hreg : RegP D) (hp : p.Prime) (σ N) :`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` (F9's repair: `p.Prime`,
  never `1 < p` — the note asserts SQ.2 only at primes satisfying (REG-p);
  composite p is NOT claimed)
- **moves_ref**: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
  "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 + the CL-5 mass
  identification"
- **sketch** (F8's repair): `L.solve_stack hreg σ` now GIVES `0 ≤ evalℝ S σ p` as its
  third conjunct — no bogus case split. Transfer ℝ≥0∞ → ℝ from U3's corollary:
  `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since the RHS is finite), `ENNReal.toReal_mul`,
  `ENNReal.toReal_ofReal` (its nonnegativity input = the positivity conjunct).
- **hypothesis_fields**: `finiteness_stack`, `solve_stack` (incl. the explicit
  positivity conjunct = RS.3's clause; the full solve stack CL-1, CL-5, CL-6, CL-8,
  CL-9, CL-11, CL-13…CL-19 rides the ledger's cl-slots); explicit `RegP D`, `p.Prime`.

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
- **statement**: `theorem un_bracket (L : CapstoneLedger n p X F S D K)`
  `(hreg : RegP D) (hp : p.Prime) (σ N) :`
  `(evalℝ S σ p - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧`
  `(X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)` — `p.Prime` per F9
  (`NeZero p`/`1 < p` derived from `hp` inside)
- **moves_ref**: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
  every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing (REG-p) neither
  inequality is asserted" (the rev-3 qualifier = the `hreg` argument, D8)
- **sketch**: right leg = U4; left leg = U5 applied with `R := fun τ => evalℝ S τ p`,
  `hupper` from U4 at each τ ≠ σ, `hsum := L.rs4_eval hreg`.
- **hypothesis_fields**: `finiteness_stack`, `solve_stack`, `rs4_eval` (RS.4's full
  inherited set incl. X.3/CL-4); explicit `RegP D`.

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
- **statement** (F10's repair — the generic accessor + one corollary PER displayed
  family + (r1) + nonemptiness):
  `theorem RegP.entry_agree {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e)`
  `  {g} (hg : g ∈ D.entryList e) : DefinedAt g q₀ ∧ g.eval (RingHom.id ℚ) q₀ = D.act g q₀`
  — with corollaries `K_agree`, `bterm_agree`, `bsplit_agree`, `Jcell_agree`,
  `iota_agree`, `Wcoef_agree`, `betaLegs_agree` (membership in the `entryList` union,
  one per family — so ALL of (r2)'s displayed E(e) is exposed, not just K);
  `theorem RegP.det_ne_zero {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e) :`
  `  (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) q₀ ≠ 0`;
  `theorem RegData.pool_self_mem (D : RegData p) : p ∈ D.Pool` (from `pool_eq` +
  `one_mem_depthSet`, `pow_one` — RegP is never pool-vacuous, F4).
- **moves_ref**: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
  ENTRY LIST E(e) := { each entry of K_e } ∪ { each entry of b_e — BOTH components …
  per-cell J … } ∪ { each entry of ι_e } ∪ { each W_Ŝ coefficient } ∪ { each entry of
  every β_{e,τ} … }" (SQ.4's rev-3 schema, now covered in full)
- **sketch**: unfold `RegP` + `RegData.entryList` (Finset union membership per family).
  The API the MovesS instantiation consumes; no content beyond the schema.
- **hypothesis_fields**: explicit `RegP D` only.

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
    (inst : ∀ p : ℕ, p.Prime → UInstance n S p) :
    ∃ R : SplittingType n → RatFunc ℚ,
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
        (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0)
        ∧ (∀ N f σ, (inst p hp).X.canonical N f = some σ →
            (inst p hp).X.trueType N f = some σ)
```
- **moves_ref**: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
  prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and ρ_σ(p) IS the
  splitting density of type σ over ℤ_p — the undecided complement has mass 0 and the
  classifier verdicts are the true factorization types … Σ_σ R_σ = 1 identically in q
  (RS.4). … The quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
- **sketch**: witness `R := S.R`. Checksum: `(inst 2 Nat.prime_two).L.rs4_checksum`
  (p-independent, any prime's ledger). Per p: limit = U7 with `r := evalℝ S σ p`,
  bracket from U6 (`hp` supplies `NeZero p`, `1 < p`), env-limit = `L.cl4_env_tendsto`
  (also the second conjunct verbatim); third conjunct = `X.canonical_sound`. The three
  density-identification conjuncts TOGETHER are the note's "ρ_σ(p) IS the splitting
  density" AT INTERFACE STRENGTH (F12): limit + vanishing undecided + verdict truth,
  with `trueType`'s fidelity the declared HC-2 instantiation pin (D9). ≤ 20 lines.
- **hypothesis_fields**: the COMPLETE ledger — all 19 cl-slots + the operative fields —
  via `UInstance.L` at every prime, + explicit `RegP` per adjudicated p. Nothing else.

---

## 4. Semantic-guardian flags (the trust surface, for the Codex audit)

- **G1 `ClassifierSpec.trueType`/`canonical`**: the ONE semantic pin (D9). The
  interface now CARRIES soundness + stability, but that the instantiated `trueType`
  is the real ℤ_p factorization type (and `canonical` the real T_can^τ) is the
  HC-2/MovesD instantiation-fidelity duty. U10's density-identification conjuncts are
  interface-strength; say so in any progress claim.
- **G2 `evalℝ` junk values**: Mathlib `RatFunc.eval` returns 0 at poles. Audit that no
  unit consumes `evalℝ` outside a `RegP`-guarded context except as the LIMIT TARGET in
  U10, where `solve_stack`/`rs4_eval` (both RegP-guarded) give it content.
- **G3 `FiberSeries.thrSlice : Finset`**: finiteness-as-data = CL-7 riding the
  instantiation (D4); `mem_slice_iff` pins the slice to `thr`. Audit TRACK-COUNT +
  D(n) + genuine-increment stay named OPEN (`KernelStatements` slots + docstrings).
- **G4 the kernel slots**: every CL-1 … CL-19 item is an ASSERTED field (grep the
  `cl1`…`cl19` fields); `KernelStatements` slots are `Prop`-typed parameters — a
  `True`-filled slot is an instantiation-fidelity violation (D9), flag any instance
  unit that fills one. `solve_stack` MUST carry the explicit `0 ≤ evalℝ` conjunct
  (RS.3's clause, F8) — check it is not dropped in elaboration.
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
- E-phase check (flagged, not assumed): eval-additivity side-condition lemmas for
  deriving `rs4_eval` from `rs4_checksum` (`RatFunc.eval_add`'s hypotheses) — if absent
  or awkward, `rs4_eval` stays a field (already the blueprint default).

## 6. Status and counts (REV 2)

12 units (U0, U0b, U1–U10): 4 TAG-FREE/unconditional (U1 (BOX-N), U2 Tonelli
existence, U5 SQ.3-as-arithmetic, U7 limit forcing — exactly the note's re-audited
tag-free perimeter) + 2 support (U0, U0b) + 6 conditional/definitional, every
hypothesis a named structure field, kernel slot, or explicit `RegP`. Difficulty:
5 easy, 7 medium, 0 hard. No new axiom; no `sorry` planned (conditional content =
hypothesis structures). Self-contained per the master plan; instantiation hooks per
D9: `ClassifierSpec` ← MovesD/HC-2, `FiberSeries` ← MovesD/[3t], `SolveData`/
`RegData`/`KernelStatements` ← MovesS + owner notes. Next gate: Codex re-audit
(one shot), charge = §4's guardian flags + the 13-finding disposition table (§7).

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

