/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.U0b_splitTypeFintype
import LeanUrat.MovesU.DefsCarriers
import LeanUrat.MovesU.U8_regP_access
import LeanUrat.MovesS.BlockSolveSpec
import LeanUrat.MovesX.Defs
import LeanUrat.MovesRBase.Defs
import LeanUrat.MovesT.Defs
import LeanUrat.MovesV.V7_ctsmDefs

/-!
# MovesU/DefsLedger — THE TYPED CAPSTONE LEDGER (ROUND-2 RETYPE, 2026-07-29,
commit 3728b00 — date corrected 2026-07-30; original record mis-dated 2026-07-31)

STATEMENT-CHANGE WARRANT: the round-2 ratification verdict — durable archive
`notes/MOVESU_RATIFICATION_ROUNDS_2026-07-30.md` ROUND 2 (verbatim copy of
`/tmp/leanratify_u2/verdict.txt`; REJECT 6 CRITICAL / 1 GAP, 2026-07-29). Every
change below quotes its finding:

* CRITICAL 1 ("the claimed residual typed ledger is literally 15 bare `Prop`
  slots… One may instantiate every field with `True`"): `UpstreamKernelStatements`
  is RETIRED. The rows are typed over the BUILT owner corpora —
  CL-2/CL-3/CL-15 over `MovesX` (`X3aRouteP`, the five X.2 Props, `X1aAlignP`);
  CL-7's mechanics over the `MovesX.XFamily` carriers (`Cl7Kernel`, with the
  p-UNIFORM explicit L(n)/D(n)/w*/T(n,N) data — CRITICAL 6 killed jointly);
  CL-8's typed face over `MovesRBase` (`EQ2law` at carried `AlphabetData`);
  CL-10's (SIB)/(JC-multi) over `MovesT` AT THE PINNED INSTANCE (`SibJcRows`
  through `TreePin`); CL-13's syntax face over `MovesV` (`Part_Stmt` at a carried
  `CtsmLedger` tied to THE table). The genuinely vocabulary-less rows are NO
  LONGER bundled: each is an EXPLICIT named `Prop` PARAMETER of `theoremU`
  (visible in the signature) — see U10's docstring for the list and owners.
* CRITICAL 2 ("canonical trees and the classifier remain abstract surrogates"):
  `TreePin` — the typed seam (the `r_is_solve` analogue): `F.Tree σ` is carried
  INTO the built `MovesT.VTree` corpus (`vt`, injective, typemult = σ, thr
  identified), `X.canonical` is pinned to fibering at a carried realizable tree
  within threshold (`canonical_pin`), `seam.treeOf` reads THE fibering tree
  (`treeOf_pin`), and the level-N box is pinned to the MovesT digit box by the
  base-p digit law (`boxeq_digits`). Discharge candidate: `MovesT.treeN` (E11).
* CRITICAL 3 ("`RegPin` does not pin the complete operative roster"): `RegPin`
  gains `act_pin` (ACT = the post-cancellation `evalAt` semantics on its defined
  locus — `AVAgree`'s own reading), `bsplit_pin`/`betaLeg_pin` (to the real
  `MovesS.bSplit`/`blockSolve`(`powSubst`) objects), and `bterm_pin` LOSES the
  per-row ∃σ' freedom (the designated assembled entry over `verdictImage`). The
  toy-menu channel is closed by RETIRING `MenuData`: (K-SUB)/CL-13's WF face are
  restated over THE table (`KsubM1C1T`/`MenuWFT`, DefsCarriers).
* CRITICAL 4 ("`RegP` is still stronger than the note's named schema"): `RegP` is
  restated as (r1) ∧ (r2) EXACTLY (MovesU/Defs); the former carried
  definedness/agreement conjuncts for `S.R` are DERIVED (`SolveSeam.R_defined`/
  `SolveSeam.R_agree`) from the typed assembly (detHyp transport + `r_is_solve` +
  `rsh_interp` + `act_pin`).
* CRITICAL 5 ("`ZpBridge` does not encode the (e,f) splitting type"): `zf_factor`
  now pins each read pair to THE valuation-theoretic invariants — the MovesT
  REV-9 closed defs `ramIdx`/`resDeg` at the monic factor (ℤ_p coefficients;
  ℚ_p-irreducible). Remaining HC-2 residue stated at the structure.
* GAP 1 ("the evaluated checksum is still assumed"): `rs4_eval` is DERIVED
  (`SolveSeam.rs4_eval`) from `rs4_checksum` + derived definedness via the
  `evalAt` ring hom; the ledger field and `LowerStack` are retired.

ROUND-3 REPAIRS (executed 2026-07-29, commit 00b03aa; warrant: durable archive
`notes/MOVESU_RATIFICATION_ROUNDS_2026-07-30.md` ROUND 3, verbatim copy of
`/tmp/finalratify_u/verdict.txt`, REJECT 4 CRITICAL / 0 GAP). Every change
quotes its finding:

* CRITICAL 1 ("`chart : ∀ N : ℕ, Fin n → Fin (n * N)` … For `N = 0`, this
  demands `Fin n → Fin 0` … no `TreePin` can exist, hence no `UInstance` can
  exist, hence `inst` is an inconsistent premise"): `chart` is RESTRICTED TO
  POSITIVE LEVELS (`∀ N, 0 < N → Fin n → Fin (n * N)`); the guard threads
  through every consumer (`chart_inj`/`vt_real`/`vt_surj`/`canonical_pin`/
  `treeOf_pin`/all three `SibJcRows` rows). Non-vacuity of the repaired slice is
  PROVED (`chartWitness`/`chartWitness_inj`: the digit chart i ↦ (i, 0)).
  RECORDED RESIDUE: the pin says nothing at N = 0 (there the level-0 box is the
  single class and TREE-N's working level m = n·N degenerates to 0).
* CRITICAL 3 ("There is no converse completeness/surjectivity statement saying
  that every complete finite realizable canonical `MovesT.VTree` of type `σ` is
  represented by some `T : F.Tree σ` … an instance may choose a proper
  subfamily"): `TreePin.vt_surj` — the COMPLETENESS direction: every
  `MovesT.VTree` (complete finite canonical by construction) of typemult σ.1,
  threshold ≤ N, REALIZED at the pinned level-N model/chart, is in `vt σ`'s
  image. With `canonical_pin`, `X.canonical` now recognizes the COMPLETE
  realizable corpus — the selected-subfamily bypass dies, and `seam.count_tie`
  is a claim about the full family.
* CRITICAL 4 ("Nothing makes `legSt` injective, surjective, or keyed to the
  actual source outcome/member/continuation roster … duplication can remove
  required real β-values from `(r2)`"): `LegRoster` — THE real consumed β-leg
  roster type (state × split outcome × continuing member position, exactly the
  population `leg_pin` counts) with `legTarget` reading each member's REAL
  (e', τ') (size ∈ [1, n] by the carried DEG-CONS); `RegPin.legEquiv` (a
  BIJECTION of the abstract labels onto the roster — injectivity + coverage)
  and `RegPin.legSt_pin` (`legSt` IS the real target through it). The
  duplication/omission bypass dies.
* CRITICAL 2 is ADJUDICATED, record only (see U10's docstring): the 13 explicit
  `Prop` parameters are the WAVE-4 BOUNDARY — UNPINNED (True-instantiable)
  pending the wave-D carriers.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology ENNReal LeanUrat

/-! ## The p-uniform kernel carriers (CRITICAL 1's substrate) -/

/-- THE UPSTREAM KERNEL CARRIER PACK (p-UNIFORM): the built owner corpora the
    retyped rows are stated over — never instance-invented vocabulary.
    `XF`/`XK`: the §X-EXHAUST family and its n-only constants (owner [5], built
    `MovesX`); `VC`: the §V-TABLES CTS family (owner [1v], built `MovesV`) — the
    carrier slice CL-13's syntax law `Part_Stmt` reads. FOOTPRINT NOTE (recorded):
    the FULL `MovesV.CtsmLedger` cannot be carried here — its `hEU : EntU` field
    type flows the V corpus's Phase-B `sorryAx` (the V3_spwordD
    `writeHeights_total_unscoped` shim) into every statement mentioning the
    ledger, and the capstone footprint must stay Lean-core; the syntax row is
    therefore stated at the clean `CtsFamily` carrier (`CtsmSyntaxRow` below,
    definitionally `Part_Stmt`'s body — `ctsmSyntaxRow_iff_part`), and the
    V-ledger's own T-seam tie is the recorded residue of that fence.
    `Sp`/`AD`: the [2r] species syntax and per-p alphabet carriers (built
    `MovesRBase`) for CL-8's typed (EQ-2) face. -/
structure KernelCarriers (n : ℕ) (C : UCarriers n) where
  XF : MovesX.XFamily n
  XK : MovesX.XConsts n
  VC : MovesV.CtsFamily n
  Sp : MovesRBase.SpeciesSyntax
  AD : ∀ (p : ℕ) [Fact p.Prime], MovesRBase.AlphabetData p Sp

/-- CL-13's CTS-M(i) SYNTAX law at the `CtsFamily` carrier: every box point of
    every skeleton's displayed cell-predicate family has a UNIQUE joint address,
    and the address space is finite — VERBATIM `MovesV.Part_Stmt`'s body (the
    `CtsmLedger` projection it reads), restated over the clean slice (see the
    `KernelCarriers` footprint note). -/
def CtsmSyntaxRow {n : ℕ} (CF : MovesV.CtsFamily n) : Prop :=
  ∀ (s : MovesV.Skeleton n) (q₀ : ℚ), MovesV.IsPP q₀ →
    (∀ x : (CF.bd s).Carrier q₀,
      ∃! a : ∀ g : (CF.bd s).Gen, ((CF.bd s).gen g).idx,
        ∀ g, ((CF.bd s).gen g).part q₀ x = a g) ∧
    Finite (∀ g : (CF.bd s).Gen, ((CF.bd s).gen g).idx)

/-- The definitional tie: at a V ledger, `CtsmSyntaxRow` IS `Part_Stmt` (the row
    quotes the built statement verbatim; only the carrier binder is slimmed). -/
theorem ctsmSyntaxRow_iff_part {n : ℕ} (L : MovesV.CtsmLedger n) :
    CtsmSyntaxRow L.C ↔ MovesV.Part_Stmt L :=
  Iff.rfl

/-- THE TYPED UPSTREAM ROWS (p-UNIFORM; replaces the corresponding retired bare
    slots — CRITICAL 1). Each row is the BUILT owner Prop at the carried corpus:
    * `cl2_route` — CL-2, X.1b WEIGHT-CHARGE in its X.3(a) route form
      (`X1aAlignP ∧ WeightChargeT4P`) ∨ (`X1aAlignP(inc) ∧ WeightChargeFullP`)
      — the XC3/XC4 discharge carriers' exact hypothesis surface;
    * `cl3_*` — CL-3, X.2 PROGRESS: (X2-AFF)/(X2-CAP)/the coercivity
      dichotomy/(X2-TAILS)/(X2-BRIDGE), the XD2–XD4 carriers' Props verbatim;
    * `cl8_eq2` — CL-8's TYPED [2r] face: the (EQ-2) alphabet law (F_δ-linearity
      + a_δ = δ·a on δ-stable positions) at the carried `AlphabetData`, per prime.
      The six REL rows themselves (REL.1, REL.2(a)/(b)/(d)/(e), REL.3) have NO
      built Lean statements — they ride as `theoremU`'s explicit bare parameters;
    * `cl13_syntax` — CL-13's CTS-M(i) SYNTAX face: `Part_Stmt`'s law (the
      displayed-cell-predicate partition with finite address space) at the
      carried `CtsFamily` (`CtsmSyntaxRow`; `ctsmSyntaxRow_iff_part` is the
      verbatim tie). The target-cell maps ride the V corpus's own typed carriers;
    * `cl15_align` — CL-15's operative ALIGN layer at the certified-increment
      state (the per-species GMN index dictionary itself is a bare parameter). -/
structure UpstreamTyped (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C) : Prop where
  cl2_route : MovesX.X3aRouteP n KC.XF KC.XK
  cl3_aff : MovesX.X2AffP n KC.XF KC.XK
  cl3_cap : MovesX.X2CapP n KC.XF KC.XK
  cl3_progress : MovesX.X2ProgressP n KC.XF KC.XK
  cl3_tails : MovesX.X2TailsP n KC.XF KC.XK
  cl3_bridge : MovesX.X2BridgeP n KC.XF
  cl8_eq2 : ∀ (p : ℕ) [Fact p.Prime], MovesRBase.EQ2law p (KC.AD p)
  cl13_syntax : CtsmSyntaxRow KC.VC
  cl15_align : MovesX.X1aAlignP n KC.XF ⟨true, false⟩

/-- CL-7's TYPED KERNEL over the real §X carriers (CRITICAL 1 + CRITICAL 6: "its
    witness `B` may also depend on `p`, `X`, and `F`… the real CL-7 mechanics
    remain only the three bare tags"). ALL DATA HERE IS p-UNIFORM — bound BEFORE
    any prime (binder order enforces the note's "L(n) explicit … uniformly in p,
    N, and depth" and kills the automatic per-p finite max: one `Tbound` must
    serve EVERY prime's slice family simultaneously, which no per-instance
    maximum supplies).
    * `L`/`Dden`/`wstar`/`Tbound` — TRACK-COUNT's L(n), the D(n) common
      denominator, the derived key-weight budget w*(N), and SQ.0's conclusion
      bound T(n, N) (consumed per-p at `UInstance.cl7_slice`);
    * `track_restarts` — (TRK-RULE)'s (t3) face over the X vocabulary: the
      ladder-restart (recentering) events of every stratum history number ≤ L.
      The (t1)/(t2) key/branch recognitions and the (c1) assignment MAP have no
      X carrier — they ride `theoremU`'s bare `trackRule` parameter;
    * `zero_gain` — SQ.0(c)'s displayed bound d_zero(H) ≤ L(n)·D(n)·w*(N) on
      threshold-≤-N branches (d_zero = continuing non-genuine-increment nodes);
      the weight-lattice duty (all key weights in (1/D(n))·ℤ, candidate D(n) | n!)
      has no key-weight carrier — bare `dnLattice` parameter;
    * `genuine_bound` — SQ.0(d)'s genuine-increment CONSEQUENCE: ≤ n·N genuine
      (T1/T2-increment) nodes on threshold-≤-N branches (the per-node
      strict-ledger-increment sub-claim itself is part of `dnLattice`'s owner
      residue, disclosed at U10). -/
structure Cl7Kernel (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C) where
  L : ℕ
  Dden : ℕ
  wstar : ℕ → ℕ
  Tbound : ℕ → ℕ
  hL : 1 ≤ L
  hD : 1 ≤ Dden
  track_restarts : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (H : MovesX.XHistory n), f ∉ MovesX.discZero n p →
    (KC.XF.gmn p).inStratum f H →
    MovesX.countPop H MovesX.Pop.recT1 + MovesX.countPop H MovesX.Pop.t4 ≤ L
  zero_gain : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f) (N : ℕ), (KC.XF.ctx p).threshold b ≤ N →
    MovesX.dTotal ((KC.XF.ctx p).hist b)
        - MovesX.countPop ((KC.XF.ctx p).hist b) MovesX.Pop.incT12
      ≤ L * Dden * wstar N
  genuine_bound : ∀ (p : ℕ) [Fact p.Prime] (f : MovesX.MonicBox n p)
    (b : (KC.XF.ctx p).Branch f) (N : ℕ), (KC.XF.ctx p).threshold b ≤ N →
    MovesX.countPop ((KC.XF.ctx p).hist b) MovesX.Pop.incT12 ≤ n * N

/-! ## The TREE-N seam (CL-7/CL-10's operative content, typed) -/

/-- THE TREE-N SEAM (typed rows replacing the ASSUMED `finiteness_stack` field —
    round-1 CRITICAL 2). The note's own open premises, named:
    `treeOf` — the canonical-tree assignment of every decided-σ class (T_can^τ's
    verdict-tree read at level N); `thr_le` — decided at N means threshold ≤ N
    (decision stability's read); `count_tie` — TREE-N's EXACT per-tree fiber count:
    μ(fiber T)·p^{nN} = #{decided-σ classes whose canonical tree is T} (the [3t]
    discharge candidate is `MovesT.treeN` — E8's `treeExp` at m = n·N — per the C9
    map; its instantiation at the real classifier is the remaining [3t] seam,
    now PINNED by `TreePin` below — round-2 CRITICAL 2).
    From THESE the partition identity is DERIVED (`finiteness_stack` below). -/
structure TreeSeam (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X) where
  treeOf : ∀ (σ : SplittingType n) (N : ℕ)
    (f : {f : Box p n N // X.canonical N f = some σ}), F.Tree σ
  thr_le : ∀ σ N f, F.thr σ (treeOf σ N f) ≤ N
  count_tie : ∀ (σ : SplittingType n) (N : ℕ) (T : F.Tree σ), F.thr σ T ≤ N →
    F.mass σ T * (p : ℝ≥0∞) ^ (n * N)
      = (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
          treeOf σ N f = T} : ℝ≥0∞)

/-- The finiteness stack, DERIVED (was an assumed field — round-1 CRITICAL 2):
    decided_σ(N) = p^{nN} · Σ_{thr(T) ≤ N} μ(fiber T), by partitioning the decided-σ
    classes along `treeOf` and summing `count_tie` over the slice. -/
theorem TreeSeam.finiteness_stack {n p : ℕ} [NeZero p] {X : ClassifierSpec n p}
    {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞)
      = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T := by
  classical
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (NeZero.ne p)⟩
  letI : Fintype {f : Box p n N // X.canonical N f = some σ} :=
    Fintype.ofFinite _
  -- ℕ-level partition of the decided-σ classes along the canonical-tree assignment.
  have hpart : X.decided σ N = ∑ T ∈ F.thrSlice σ N,
      Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
        seam.treeOf σ N f = T} := by
    have h1 : X.decided σ N
        = (Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).card := by
      rw [ClassifierSpec.decided, Nat.card_eq_fintype_card, Finset.card_univ]
    have h2 : (Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).card
        = ∑ T ∈ F.thrSlice σ N,
            ((Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).filter
              fun f => seam.treeOf σ N f = T).card :=
      Finset.card_eq_sum_card_fiberwise fun f _ =>
        (F.mem_slice_iff σ N _).mpr (seam.thr_le σ N f)
    have h3 : ∀ T : F.Tree σ,
        Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
            seam.treeOf σ N f = T}
          = ((Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).filter
              fun f => seam.treeOf σ N f = T).card := by
      intro T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, h2]
    exact Finset.sum_congr rfl fun T _ => (h3 T).symm
  calc (X.decided σ N : ℝ≥0∞)
      = ∑ T ∈ F.thrSlice σ N,
          (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
            seam.treeOf σ N f = T} : ℝ≥0∞) := by
        rw [hpart]; push_cast; rfl
    _ = ∑ T ∈ F.thrSlice σ N, F.mass σ T * (p : ℝ≥0∞) ^ (n * N) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [seam.count_tie σ N T ((F.mem_slice_iff σ N T).mp hT)]
    _ = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T := by
        rw [← Finset.sum_mul, mul_comm]

/-! ## The tree/classifier pin (round-2 CRITICAL 2) -/

/-- The digit slot (i, k) ↦ i·N + k of the level-N chart (the base-p digit
    positions of coefficient i). -/
def digitIdx (n N : ℕ) (i : Fin n) (k : Fin N) : Fin (n * N) :=
  ⟨(i : ℕ) * N + (k : ℕ), by
    have h1 : (i : ℕ) + 1 ≤ n := i.isLt
    calc (i : ℕ) * N + (k : ℕ) < (i : ℕ) * N + N := Nat.add_lt_add_left k.isLt _
      _ = ((i : ℕ) + 1) * N := by ring
      _ ≤ n * N := Nat.mul_le_mul_right N h1⟩

/-- NON-VACUITY WITNESS for the guarded chart slice (round-3 CRITICAL 1: "no
    `TreePin` can exist"): at every POSITIVE level the digit chart i ↦ (i, 0)
    inhabits `chart`'s repaired type. -/
def chartWitness (n N : ℕ) (hN : 0 < N) : Fin n → Fin (n * N) :=
  fun i => digitIdx n N i ⟨0, hN⟩

/-- …and injectively (`chart_inj`'s slice is inhabitable too). -/
theorem chartWitness_inj (n N : ℕ) (hN : 0 < N) :
    Function.Injective (chartWitness n N hN) := by
  intro i j hij
  have h : (i : ℕ) * N + 0 = (j : ℕ) * N + 0 := congrArg Fin.val hij
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hN (by simpa using h))

section TreePinSection
variable (n p : ℕ) [Fact p.Prime]

/-- THE TREE/CLASSIFIER PIN (round-2 CRITICAL 2: "Nothing in its type identifies
    `F.Tree σ` with the owner corpus's complete finite realizable canonical trees,
    or `treeOf` with T_can^τ … `canonical` remains an abstract classifier"). The
    typed seam in the `r_is_solve` pattern, carried as the NAMED premise
    (`UInstance.Tpin`): the abstract tree/classifier vocabulary is identified with
    the BUILT `MovesT` canonical-tree corpus.
    * `pol`/`Tm`/`chart` — the canonical policy, the per-level tree model at the
      working level m = n·N (TREE-N's own level), and the coefficient chart. THE
      CHART IS GUARDED TO POSITIVE LEVELS (round-3 CRITICAL 1: "For `N = 0`,
      this demands `Fin n → Fin 0` … no `TreePin` can exist"); non-vacuity of
      the guarded slice is PROVED at `chartWitness`/`chartWitness_inj`, and the
      pin is silent at N = 0 (recorded residue: the level-0 box is one class);
    * `boxeq`+`boxeq_digits` — the level-N coefficient box IS the MovesT digit box,
      pinned by the base-p digit expansion (no free relabeling survives the law);
    * `vt` (INJECTIVE) — every abstract tree IS a `MovesT.VTree` (a complete
      finite canonical tree), of verdict type σ (`vt_typemult`), with the SAME
      threshold (`vt_thr`), REALIZABLE at every level ≥ its threshold (`vt_real`);
    * `vt_surj` — THE COMPLETENESS DIRECTION (round-3 CRITICAL 3: "no converse
      completeness/surjectivity statement saying that every complete finite
      realizable canonical `MovesT.VTree` of type `σ` is represented by some
      `T : F.Tree σ`"): every `MovesT.VTree` (complete finite canonical BY
      CONSTRUCTION — its `chains`/`hfin`/`hclosed`/`hleaf` fields) of typemult
      σ.1 and threshold ≤ N that is REALIZED at the pinned level-N model/chart
      lies in `vt σ`'s image — no proper-subfamily instance survives, so
      `canonical_pin` + `seam.count_tie` speak about the COMPLETE corpus;
    * `canonical_pin` — T_can^τ's verdict read: `canonical N f = some σ` IFF the
      digit class fibers at a carried σ-tree within threshold (`VTree.fiberAt`,
      the graph-equality fiber of the built corpus);
    * `treeOf_pin` — the seam's canonical-tree assignment reads THE fibering tree.
    Discharge candidate for the seam's `count_tie` through this pin:
    `MovesT.treeN` (T-E11) at `Tm N`/`chart N hN`, whose (SIB)/(JC-multi)
    hypothesis rows are typed at THIS instance by `SibJcRows` below. -/
structure TreePin (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (seam : TreeSeam n p X F) where
  pol : MovesD.CanonPolicy p (ZMod p)
  Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol
  chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N)
  chart_inj : ∀ (N : ℕ) (hN : 0 < N), Function.Injective (chart N hN)
  boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N)
  boxeq_digits : ∀ (N : ℕ) (f : Box p n N) (i : Fin n),
    f i = ∑ k : Fin N,
      ((boxeq N f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ)
  vt : ∀ σ : SplittingType n, F.Tree σ → MovesT.VTree p (ZMod p)
  vt_inj : ∀ σ, Function.Injective (vt σ)
  vt_typemult : ∀ (σ : SplittingType n) (T : F.Tree σ), (vt σ T).typemult = σ.1
  vt_thr : ∀ (σ : SplittingType n) (T : F.Tree σ), F.thr σ T = (vt σ T).thr n
  vt_real : ∀ (σ : SplittingType n) (T : F.Tree σ) (N : ℕ) (hN : 0 < N),
    F.thr σ T ≤ N → MovesT.Realizes (Tm N) (chart N hN) (vt σ T)
  vt_surj : ∀ (σ : SplittingType n) (V : MovesT.VTree p (ZMod p)) (N : ℕ)
    (hN : 0 < N), V.typemult = σ.1 → V.thr n ≤ N →
    MovesT.Realizes (Tm N) (chart N hN) V →
    ∃ T : F.Tree σ, vt σ T = V
  canonical_pin : ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n),
    X.canonical N f = some σ ↔
      ∃ T : F.Tree σ, F.thr σ T ≤ N ∧
        (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f)
  treeOf_pin : ∀ (σ : SplittingType n) (N : ℕ) (hN : 0 < N)
    (f : {f : Box p n N // X.canonical N f = some σ}),
    (vt σ (seam.treeOf σ N f)).fiberAt (Tm N) (chart N hN) (boxeq N f.1)

/-- CL-10's (SIB)/(JC-multi) ROWS AT THE PINNED INSTANCE (round-2 CRITICAL 1's
    `sibJcMulti` home: "the built MovesT SibCount/JCmultiAt statements
    at-instance"). Exactly the hypothesis rows `MovesT.treeN` consumes, asserted
    at the PINNED tree models `TP.Tm N`/`TP.chart N` (never a free model):
    * `sib` — (SIB)'s COUNT face (`MovesT.SibCount`), the central CL-10 kernel;
    * `sib_at` — (SIB) at a realized site (`MovesT.SibCountAt`, the SITE-ENTRANCE
      keying of 2026-07-29, commit 00b03aa (date corrected 2026-07-30; original
      record mis-dated 2026-08-01): entrance es, the site's own branch node ν,
      ONE site cell c — conditioning and roster; the earlier same-day c/cSplit
      two-keying (commit 3728b00; record mis-dated 2026-07-31) is retired per
      the re-ratification verdict), guarded exactly as `SibCount`
      guards its prescribed-subtree events (each conditioning set a finite
      `ContFiber` at the entrance's child root, or ⊤);
    * `jc_multi` — (JC-multi) at multi-side sites (`MovesT.JCmultiAt`, same
      re-keyed form: the side split's own cell under the site's own read map
      prices the event). -/
structure SibJcRows {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {seam : TreeSeam n p X F} (TP : TreePin n p X F seam) : Prop where
  sib : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf),
    MovesT.SibCount (TP.Tm N) CA.toCellData (TP.chart N hN)
  sib_at : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf)
    (es : MovesT.EntSt p (ZMod p) n) (ν₀ : MovesC.Node p (ZMod p))
    (c : CA.toCellData.Cell)
    (S : MovesC.Node p (ZMod p) → Set (MovesD.Box p (n * N))),
    2 ≤ (CA.toCellData.branchSetOf c).card →
    (∀ ν ∈ CA.toCellData.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | MovesT.ContFiber (TP.Tm N) (MovesT.stOf es) ν hν Tsub leafSpec nsSpec x}) ∨
      S ν = Set.univ) →
    MovesT.SibCountAt (TP.Tm N) CA.toCellData (TP.chart N hN) es ν₀ c S
  jc_multi : ∀ (N : ℕ) (hN : 0 < N) (trackOf : MovesC.Node p (ZMod p) → Polynomial (ZMod p))
    (CA : MovesT.CellAssign p (ZMod p) n N (n * N) TP.pol (TP.Tm N) (TP.chart N hN) trackOf)
    (es : MovesT.EntSt p (ZMod p) n) (ν₀ : MovesC.Node p (ZMod p))
    (c : CA.toCellData.Cell) (fd : MovesC.FreshData p (n * N))
    (ss : MovesT.SideSplit (TP.Tm N) CA.toCellData c fd),
    MovesT.IsMultiSideSite (TP.Tm N) CA.toCellData c ss →
    MovesT.JCmultiAt (TP.Tm N) CA.toCellData (TP.chart N hN) es ν₀ ss

end TreePinSection

/-! ## The RegData re-key (round-2 CRITICAL 3) -/

/-- THE REAL CONSUMED β-LEG ROSTER of block e (round-3 CRITICAL 4: "Nothing makes
    `legSt` injective, surjective, or keyed to the actual source
    outcome/member/continuation roster"): one label per CONTINUING MEMBER of each
    SPLIT outcome of each state of the block — EXACTLY the population `leg_pin`
    counts (`Outcome.c` continuing members per split row). -/
def LegRoster {n : ℕ} (T : MovesS.TableShape n) (e : ℕ) : Type :=
  Σ (τ : T.State e) (o : {o : T.Out e τ // o ∈ MovesS.splitOuts T e τ}),
    {i : Fin (T.odata e τ o.1).mem.length // ((T.odata e τ o.1).mem.get i).continuing}

/-- The REAL target (e', τ') of a roster leg: the continuing member's size and
    state (`Member.size`/`Member.status`). Membership e' ∈ [1, n] rides the
    carried DEG-CONS (`size_pos` + `size_sum` at the source block). -/
noncomputable def legTarget {n : ℕ} (C : UCarriers n) (e : ℕ)
    (he : e ∈ Finset.Icc 1 n) (l : LegRoster C.T e) :
    (e' : {e' : ℕ // e' ∈ Finset.Icc 1 n}) × C.T.State e'.1 :=
  let μ := (C.T.odata e l.1 l.2.1.1).mem.get l.2.2.1
  ⟨⟨μ.size, by
      have hmem : μ ∈ (C.T.odata e l.1 l.2.1.1).mem := List.get_mem _ _
      have h1 : 1 ≤ μ.size := C.hdc.size_pos e l.1 l.2.1.1 μ hmem
      have h2 : μ.size ≤ ((C.T.odata e l.1 l.2.1.1).mem.map MovesS.Member.size).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hmem)
      exact Finset.mem_Icc.mpr
        ⟨h1, le_trans (le_trans h2 (C.hdc.size_sum e he l.1 l.2.1.1))
          (Finset.mem_Icc.mp he).2⟩⟩,
    μ.status.getRight l.2.2.2⟩

/-- THE ROSTER PIN (round-1 CRITICAL 4 + round-2 CRITICAL 3): every `RegData`
    index family, count, AND OPERATION is EQUATED to the real §S block system.
    `blk`/`st` identify the blocks with the working degrees e ∈ [1, n] and the
    per-block states with the REAL table states; `depth_pin` pins the depth set to
    the consumed-deltas closure; `K_pin`/`iota_pin` pin the matrix and ι entries to
    the REAL `Kmat`/ι tables; `Jcell_pin`/`W_pin` pin the per-cell J and W_Ŝ entry
    IMAGES to the real per-cell tables and shape presentation values; the counts
    (`blockDim_pin`/`cell_pin`/`shape_pin`/`leg_pin`) equate to the real tables'
    cardinalities. ROUND-2 ADDITIONS (each quoting the verdict):
    * `act_pin` ("the active-value operation remains free data … never related to
      the real CTS-M active semantics"): on its DEFINED locus (post-cancellation
      OKat membership — exactly `AVAgree`'s reading, "the evaluated object's
      q₀-value (after cancellation)"), `D.act` IS the real `evalAt` semantics;
    * `bterm_pin` ("permits an instance-selected σ' for every row"): the ∃σ' is
      KILLED — each row is THE designated assembled entry, the σ'-sum over the
      roster's own displayed support `verdictImage` (b^{term,fin}'s docstring:
      "any σ'; supported on `verdictImage`");
    * `bsplit_pin` ("no bsplit_pin"): each split row is pinned to the REAL
      `MovesS.bSplit` with the REAL `blockSolveLt` legs (the solve's own βlt slot,
      `blockSolve_spec`), assembled over the chain's EXACT σ-index `Sigmas`.
      RECORDED RESIDUE: the σ'-RESOLVED per-entry display of the split family
      (one abstract entry per (state, σ') rather than the Sigmas-assembled row)
      exceeds the abstract roster's per-state shape — [1v]'s display duty;
    * `legSt`+`betaLeg_pin` ("no betaLeg_pin"): each β leg is pinned to the real
      β_{e',τ'}(q^δ) object — `powSubst δ` of the real `blockSolve` at a carried
      (block, state) label, over `Sigmas`. Same recorded σ'-resolution residue.
    ROUND-3 ADDITION (CRITICAL 4: "`leg_pin` fixes only the number of abstract
    labels … Multiple abstract labels may map to the same real block/state while
    another consumed β-leg is omitted"): `legEquiv` — the abstract leg labels
    BIJECT onto the REAL consumed roster `LegRoster` (injectivity + coverage:
    every continuing member of every split outcome carries exactly one label) —
    and `legSt_pin` — `legSt` reads each label's REAL (e', τ') target through
    `legTarget`. With `betaLeg_pin`, every real consumed β value now rides
    `entryList`, hence `(r2)`; the surrogate-roster bypass dies.
    The former `MenuData` pins are CLOSED BY RETIREMENT: (K-SUB)/WF are restated
    over `C.T` itself (`KsubM1C1T`/`MenuWFT`, DefsCarriers). -/
structure RegPin {n : ℕ} (C : UCarriers n) {p : ℕ} (D : RegData p) where
  blk : D.Block ≃ {e : ℕ // e ∈ Finset.Icc 1 n}
  st : ∀ b : D.Block, D.bidx b ≃ C.T.State (blk b).1
  depth_pin : D.depthSet
    = (MovesS.consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))
  K_pin : ∀ (b : D.Block) (i j : D.bidx b),
    D.K b i j
      = MovesS.Kmat C.T C.RB (blk b).1 (C.hK (blk b).1 (blk b).2) (st b i) (st b j)
  iota_pin : ∀ (b : D.Block) (i : D.bidx b),
    D.iota b i = C.RB.ι (blk b).1 (st b i)
  act_pin : ∀ (g : RatFunc ℚ) (q₀ : ℕ) (hok : g ∈ MovesS.OKat (q₀ : ℚ)),
    D.act g q₀ = MovesS.evalAt (q₀ : ℚ) ⟨g, hok⟩
  bterm_pin : ∀ (b : D.Block) (i : D.bidx b),
    D.bterm b i
      = ∑ σ' ∈ MovesS.verdictImage C.T (blk b).1 (st b i),
          MovesS.bTerm C.T C.RB (blk b).1 σ' (st b i)
  bsplit_pin : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK) (b : D.Block) (i : D.bidx b),
    D.bsplit b i
      = ∑ σ' ∈ C.chain.Sigmas,
          MovesS.bSplit C.T C.RB C.hdc (blk b).1 (blk b).2
            (MovesS.blockSolveLt C.RB C.hdc C.hK hdet (blk b).1) σ' (st b i)
  legSt : ∀ b : D.Block,
    D.legIdx b → (e' : {e' : ℕ // e' ∈ Finset.Icc 1 n}) × C.T.State e'.1
  legEquiv : ∀ b : D.Block, D.legIdx b ≃ LegRoster C.T (blk b).1
  legSt_pin : ∀ (b : D.Block) (l : D.legIdx b),
    legSt b l = legTarget C (blk b).1 (blk b).2 (legEquiv b l)
  betaLeg_pin : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK) (b : D.Block)
    (l : D.legIdx b) (δ : ℕ) (hδ : 0 < δ), δ ∈ D.depthSet →
    D.betaLeg b l δ
      = MovesS.powSubst ⟨δ, hδ⟩
          (∑ σ' ∈ C.chain.Sigmas,
            MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
              (legSt b l).1.1 (legSt b l).1.2 (legSt b l).2 σ')
  blockDim_pin : ∀ b, D.blockDim b = Fintype.card (C.T.State (blk b).1)
  cell_pin : ∀ b, D.cellCount b
    = ∑ τ : C.T.State (blk b).1, ∑ o ∈ MovesS.splitOuts C.T (blk b).1 τ,
        (C.MS.cells (blk b).1 τ o).card
  Jcell_pin : ∀ b,
    (letI := D.instJ b; letI := Classical.decEq (RatFunc ℚ)
     Finset.univ.image (D.Jcell b))
      = (letI := Classical.decEq (RatFunc ℚ)
         (Finset.univ : Finset (C.T.State (blk b).1)).biUnion fun τ =>
           (MovesS.splitOuts C.T (blk b).1 τ).biUnion fun o =>
             (C.MS.cells (blk b).1 τ o).image fun c =>
               (C.RB.jPCell (blk b).1 τ c).val)
  shape_pin : D.shapeCount = C.Fam.Sh.card
  W_pin : (letI := D.instW; letI := Classical.decEq (RatFunc ℚ)
      Finset.univ.image D.Wcoef)
    = (letI := Classical.decEq (RatFunc ℚ)
       C.Fam.Sh.image fun Ŝ => (C.chain.WshP Ŝ).val)
  leg_pin : ∀ b, D.legCount b
    = ∑ τ : C.T.State (blk b).1, ∑ o ∈ MovesS.splitOuts C.T (blk b).1 τ,
        MovesS.Outcome.c (C.T.odata (blk b).1 τ o)

/-- The determinant gate TRANSPORTS through the pin: (REG-p)'s (r1) — the full
    determinant nonzero at the pool value p — forces the REAL symbolic determinant
    hypothesis `MovesS.DetHyp` (a zero rational function evaluates to zero). -/
theorem RegPin.detHyp {n : ℕ} {C : UCarriers n} {p : ℕ}
    {D : RegData p} (P : RegPin C D) (hreg : RegP D) :
    MovesS.DetHyp C.T C.RB C.hK := by
  have key : ∀ b : D.Block,
      (1 - MovesS.Kmat C.T C.RB (P.blk b).1
        (C.hK (P.blk b).1 (P.blk b).2)).det ≠ 0 := by
    intro b
    letI := D.instBi b; letI := D.instBd b
    have hpool : p ∈ D.Pool := D.pool_self_mem
    have h1 := (hreg p hpool b).1.2
    have hmat : (1 - D.K b)
        = (1 - MovesS.Kmat C.T C.RB (P.blk b).1
            (C.hK (P.blk b).1 (P.blk b).2)).submatrix (P.st b) (P.st b) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply,
        P.K_pin b i j, EmbeddingLike.apply_eq_iff_eq]
    have hdet : (Matrix.det (1 - D.K b))
        = (1 - MovesS.Kmat C.T C.RB (P.blk b).1
            (C.hK (P.blk b).1 (P.blk b).2)).det := by
      rw [hmat, Matrix.det_submatrix_equiv_self]
    intro h0
    rw [hdet, h0] at h1
    simp at h1
  intro e he
  have h := key (P.blk.symm ⟨e, he⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-! ## The solve seam + the DERIVED evaluability/agreement/checksum layer -/

/-- THE SOLVE SEAM (round-1 CRITICAL 2/3): `r_is_solve` pins `S.R` to THE real
    solve output `MovesS.Rsh` (RS.1-SH's shallow convolution over the blockSolve =
    the Cramer/adjugate route — a typed equation); `series_tie` pins the
    tree-fiber series sum to the chain's MEASURED per-σ value `Rval` — the named
    open [3t] premise (Haar mass of the canonical fibers vs the measured chain). -/
structure SolveSeam (n p : ℕ) (C : UCarriers n) {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (S : SolveData n) : Prop where
  series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
  r_is_solve : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK) (σ : SplittingType n),
    S.R σ = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ)

/-- Ruling (D), now DERIVED (round-2 CRITICAL 4: the former `RegP` conjunct
    `∀ σ, DefinedAt (S.R σ) p` was "the honest explicitly-carried strengthening";
    it is KILLED — definedness follows from the typed assembly): (r1) transports
    to `DetHyp` through the pin, `r_is_solve` pins `S.R σ` to the real `Rsh`, and
    the chain's `rsh_interp` supplies its `OKat` membership at the prime pool. -/
theorem SolveSeam.R_defined {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP D) (hp : p.Prime)
    (σ : SplittingType n) : DefinedAt (S.R σ) (p : ℚ) := by
  have hdet : MovesS.DetHyp C.T C.RB C.hK := P.detHyp hreg
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  obtain ⟨hok, -⟩ :=
    C.chain.rsh_interp (vmap C.T σ) (C.vmap_mem_Sigmas σ) (p : ℚ) hpP hdet
  rw [DefinedAt, ss.r_is_solve hdet σ]
  exact MovesS.mem_OKat_iff.mp hok

/-- The SQ.4 ACTIVE-VALUE AGREEMENT for `S.R`, now DERIVED (round-2 CRITICAL 4's
    second conjunct: "because `D.act` is unpinned, the added agreement is not yet
    agreement with the note's active value" — `act_pin` pins it, and the agreement
    follows): the literal evaluation IS the ACT active value at p. -/
theorem SolveSeam.R_agree {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP D) (hp : p.Prime)
    (σ : SplittingType n) :
    (S.R σ).eval (RingHom.id ℚ) (p : ℚ) = D.act (S.R σ) p := by
  have hok : S.R σ ∈ MovesS.OKat ((p : ℚ)) :=
    MovesS.mem_OKat_iff.mpr (ss.R_defined P hreg hp σ)
  rw [P.act_pin (S.R σ) p hok]
  rfl

/-- RS.4 EVALUATED, now DERIVED (round-2 GAP 1: "the evaluated checksum is still
    assumed… should be derived from `rs4_checksum` plus defined evaluation"): from
    the ℚ(q) checksum and the DERIVED definedness, through the `evalAt` ring hom
    on the regular subring at p. The former ledger field and `LowerStack` are
    retired. -/
theorem SolveSeam.rs4_eval {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP D) (hp : p.Prime)
    (hchk : ∑ σ, S.R σ = 1) :
    ∑ σ, evalℝ S σ p = 1 := by
  classical
  have hok : ∀ σ : SplittingType n, S.R σ ∈ MovesS.OKat ((p : ℚ)) :=
    fun σ => MovesS.mem_OKat_iff.mpr (ss.R_defined P hreg hp σ)
  have hsub : (∑ σ : SplittingType n, (⟨S.R σ, hok σ⟩ : MovesS.OKat ((p : ℚ))))
      = 1 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using hchk
  have hval : (∑ σ : SplittingType n,
      MovesS.evalAt ((p : ℚ)) ⟨S.R σ, hok σ⟩) = 1 := by
    rw [← map_sum, hsub, map_one]
  calc ∑ σ : SplittingType n, evalℝ S σ p
      = ((∑ σ : SplittingType n, MovesS.evalAt ((p : ℚ)) ⟨S.R σ, hok σ⟩ : ℚ) : ℝ) := by
        rw [Rat.cast_sum]
        exact Finset.sum_congr rfl fun σ _ => rfl
    _ = 1 := by rw [hval]; norm_num

/-- Under (REG-p), the literal evaluation equals the chain's measured value:
    `evalℝ S σ p = Rval (vmap σ) p` — through `r_is_solve` + `rsh_interp`. -/
theorem SolveSeam.evalℝ_eq_Rval {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP D) (hp : p.Prime)
    (σ : SplittingType n) :
    evalℝ S σ p = C.chain.Rval (vmap C.T σ) (p : ℚ) := by
  have hdet : MovesS.DetHyp C.T C.RB C.hK := P.detHyp hreg
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  obtain ⟨hok, heval⟩ :=
    C.chain.rsh_interp (vmap C.T σ) (C.vmap_mem_Sigmas σ) (p : ℚ) hpP hdet
  rw [show evalℝ S σ p
      = ((MovesS.evalAt (p : ℚ)
          ⟨MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ),
           hok⟩ : ℚ) : ℝ) from ?_]
  · exact heval
  · unfold evalℝ
    rw [ss.r_is_solve hdet σ]
    rfl

/-- The solve stack, DERIVED (round-1 CRITICAL 2): under (REG-p) the
    extended-value series sum is finite, IS the literal R_σ(p), and R_σ(p) ≥ 0
    (RS.3's positivity through the chain's `r_bdd`). The reach is the REAL MovesS
    solve laws (`rsh_interp` at the prime pool) through the RegPin determinant
    transport. -/
theorem SolveSeam.solve_stack {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP D) (hp : p.Prime) :
    ∀ σ : SplittingType n,
      F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
      0 ≤ evalℝ S σ p := by
  intro σ
  have heq := ss.evalℝ_eq_Rval P hreg hp σ
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  have hbdd := C.chain.r_bdd (vmap C.T σ) (p : ℚ) (C.chain.prime_sub hpP)
  refine ⟨?_, ?_, ?_⟩
  · rw [ss.series_tie σ]; exact ENNReal.ofReal_ne_top
  · rw [ss.series_tie σ, heq]
  · rw [heq]; exact hbdd.1

/-! ## The ℤ_p bridge (round-2 CRITICAL 5) -/

section ZpBridgeSection
variable (n p : ℕ) [Fact p.Prime]

/-- The ℤ_p reading predicate: the level-N class `f` reads σ iff EVERY monic
    degree-n ℤ_p lift of `f` (through `PadicInt.toZModPow`) has ℤ_p factorization
    type σ under the bridge's reading `zf`. -/
def ZpReads (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ)
    (f : Box p n N) (σ : SplittingType n) : Prop :=
  ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    g.map (PadicInt.toZModPow N) = f.toPoly → zf g = σ.1

/-- THE NAMED HC-2 ℤ_p BRIDGE — RETYPED at round 2 (CRITICAL 5: "it determines
    only the multiset of products e·f … It does not require either coordinate to
    be the actual ramification index or residue degree… `(1,6)`, `(2,3)`, `(3,2)`,
    `(6,1)` are indistinguishable"). `zf_factor` now pins BOTH coordinates of
    every read pair to THE valuation-theoretic invariants: each entry is
    `(ramIdx h, resDeg h)` at the corresponding monic factor `h` (ℤ_p
    coefficients, irreducible over ℚ_p) — the MovesT REV-9 CLOSED defs reading
    `Ideal.ramificationIdx`/`Ideal.inertiaDeg` of the maximal ideals through
    `AdjoinRoot h`. The degree accounting is retained as `zf_factor`'s final conjunct.
    REMAINING HC-2 RESIDUE (exact statement): (i) the INSTANCE obligation itself —
    supplying `lift_exists`/`lift_true`/`zf_factor` at the real classifier (the
    classifier ↔ ℤ_p-factorization seam); (ii) the §9 IP-1 instance plumbing —
    `ramIdx`/`resDeg` read their values through `IsLocalRing (AdjoinRoot h)`
    (junk 0 off it), so the bridge's (e,f) are the true invariants exactly on the
    locus where IP-1 (`IsLocalRing (AdjoinRoot h)` for monic ℚ_p-irreducible
    `h` over ℤ_p) holds — an owed instance, no longer an untyped invariant;
    (iii) `zf_pos` and `zf_factor`'s degree conjunct are carried as bridge laws
    (true theorems of local field theory, not yet Lean-derived). SCOPE NOTE
    (2026-07-30 verify-2 fold-in): the CARRIED degree conjunct is only the
    MULTISET-AGGREGATE identity `(zfType g).map (fun ef => ef.1 * ef.2) =
    factors.map Polynomial.natDegree` — with conjunct 3 this equates
    `factors.map (ramIdx·resDeg)` and `factors.map natDegree` AS MULTISETS,
    which does NOT pin the pointwise law `ramIdx h * resDeg h = h.natDegree`
    per factor (a two-factor permutation mismatch, e.g. products {2,3} against
    degrees {3,2}, satisfies the aggregate). The exact per-factor e·f = deg law
    is therefore part of the residue to be Lean-derived, NOT what the structure
    carries; a pointwise retype (∀ h ∈ factors, ramIdx h * resDeg h =
    h.natDegree) would need a fresh statement-change sign-off (queued in
    notes/GOLF_CAMPAIGN_2026-07-30.md). Premise-side, so the weaker carried
    law only broadens the admissible instance class — no soundness break. -/
structure ZpBridge (X : ClassifierSpec n p) where
  zfType : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)
  zf_pos : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∀ ef ∈ zfType g, 1 ≤ ef.1 ∧ 1 ≤ ef.2
  zf_factor : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∃ factors : Multiset (Polynomial ℤ_[p]),
      g.map (PadicInt.Coe.ringHom)
          = (factors.map (Polynomial.map PadicInt.Coe.ringHom)).prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible (h.map PadicInt.Coe.ringHom)) ∧
      zfType g = factors.map (fun h => (MovesT.ramIdx h, MovesT.resDeg h)) ∧
      (zfType g).map (fun ef => ef.1 * ef.2) = factors.map Polynomial.natDegree
  lift_exists : ∀ (N : ℕ) (f : Box p n N), ∃ g : Polynomial ℤ_[p],
    g.Monic ∧ g.natDegree = n ∧ g.map (PadicInt.toZModPow N) = f.toPoly
  lift_true : ∀ (N : ℕ) (f : Box p n N) (σ : SplittingType n),
    X.trueType N f = some σ ↔ ZpReads n p zfType N f σ

variable {n p} {X : ClassifierSpec n p}

/-- The ℤ_p-read count: #{level-N classes every monic lift of which reads σ}. -/
noncomputable def ZpBridge.zpCount (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // ZpReads n p B.zfType N f σ}

/-- The ℤ_p-read density at level N. -/
noncomputable def ZpBridge.zpDmass (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : ℝ :=
  (B.zpCount σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- Under the bridge, the ℤ_p-read count IS the classifier's true-type count. -/
theorem ZpBridge.zpCount_eq_trueCount (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : B.zpCount σ N = X.trueCount σ N :=
  Nat.card_congr (Equiv.subtypeEquivRight fun f => (B.lift_true N f σ).symm)

/-- Under the bridge, the ℤ_p-read density IS the true-type density. -/
theorem ZpBridge.zpDmass_eq_trueDmass (B : ZpBridge n p X) (σ : SplittingType n) :
    B.zpDmass σ = X.trueDmass σ := by
  funext N
  rw [ZpBridge.zpDmass, ZpBridge.zpCount_eq_trueCount]
  rfl

end ZpBridgeSection

/-! ## The capstone ledger (round-2 retype) -/

/-- THE CAPSTONE LEDGER (ROUND-2 RETYPE): the per-p typed rows over the real
    carriers + the seams. The p-UNIFORM rows now live at `UpstreamTyped`/
    `Cl7Kernel` (CRITICAL 1); the residual vocabulary-less rows are `theoremU`'s
    explicit parameters — NO bare-`Prop` pack rides here. CL-1/CL-5/CL-9(β)/
    (ii-c)/CL-18 are carried TYPED by `C : UCarriers n`; CL-11's DEG-CONS is
    `C.hdc` and its (K-SUB) face is `cl11_ksub` OVER THE REAL ROSTER; the CL-13
    WF face is DISCHARGED (`menuWFT_holds`), not carried. (REG-p) is NOT a field
    (the ONE explicit hypothesis, D5/D8). `rs4_eval` is DERIVED
    (`SolveSeam.rs4_eval`), no longer a field (GAP 1).

    PARAMETER NOTE (2026-07-30 verify-2 fold-in): the parameter `D : RegData p`
    is NOT mentioned by any field below (the fields use only X/C/F/S) — it is
    an INDEXING parameter, not a constraint: it ties the ledger's type to the
    same roster that `UInstance` supplies to both its `L` and `Dpin` fields, so
    a `CapstoneLedger` and its `RegPin` are keyed to one `RegData`. Do NOT read
    the ledger as imposing anything on `D`. Dropping the dead parameter is a
    statement change (queued in notes/GOLF_CAMPAIGN_2026-07-30.md). -/
structure CapstoneLedger (n p : ℕ) (C : UCarriers n) (X : ClassifierSpec n p)
    (F : FiberSeries n p X) (S : SolveData n) (D : RegData p) where
  /-- CL-4, TYPED (qualitative form — the note's own operative trace; the a.e.
      ℤ_p reading rides the bridge): env(N) → 0. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)
  /-- CL-6, TYPED: the (iv)-POLY value+degree law package over the real carriers
      (`tcount_val`/`scount_val`/`tcount_deg`/`scount_deg`). -/
  cl6 : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)
  /-- CL-10's VP-SOUND leg, TYPED over the concrete box (ruling (B)). -/
  cl10_vpsound : VPSound X
  /-- CL-11's (K-SUB) m = 1 classification, TYPED OVER THE REAL ROSTER (round-2
      CRITICAL 3's menu finding; DEG-CONS is `C.hdc`, carried). -/
  cl11_ksub : KsubM1C1T C.T
  /-- CL-17's production burden, TYPED as the chain's OPEN projection (W17ii at the
      chain's own carriers — never instance-suppliable data). -/
  cl17 : C.chain.wsh17_pin
  /-- CL-19's representative-invariance FACE, TYPED over the real measured carrier:
      the per-cell conditional mass is ONE function of the retained state —
      invariant across representatives (the history/h_ent face is the explicit
      `jcInvHist` parameter of U10). -/
  cl19_rep : ∀ e (τ : C.T.State e) (x x' : C.MS.Rep e τ) (c : C.MS.Cell e τ)
    (q₀ : ℚ), q₀ ∈ C.MS.Pools → C.MS.activeState q₀ e τ →
    C.MS.μcell e τ x c q₀ = C.MS.μcell e τ x' c q₀
  /-- The O3 BASE-PIN DECLARATION (SQ.4's display duty): Teichmüller. -/
  o3_teichmuller : X.baseSection = BaseSection.teichmuller
  /-- THE TREE-N SEAM (round-1 CRITICAL 2; its tree/classifier identification is
      the carried `UInstance.Tpin` — round-2 CRITICAL 2). -/
  seam : TreeSeam n p X F
  /-- THE SOLVE SEAM (round-1 CRITICAL 2/3). -/
  ssrc : SolveSeam n p C F S
  /-- RS.4's checksum (§S S.5), the ℚ(q) identity — with `ssrc.r_is_solve` this is
      a claim about THE real solve family; its evaluated form is DERIVED
      (`SolveSeam.rs4_eval` — round-2 GAP 1). -/
  rs4_checksum : ∑ σ, S.R σ = 1

/-- The derived finiteness stack, at the ledger (projection to `TreeSeam`'s). -/
theorem CapstoneLedger.finiteness_stack {n p : ℕ} [NeZero p] {C : UCarriers n}
    {X : ClassifierSpec n p} {F : FiberSeries n p X} {S : SolveData n}
    {D : RegData p} (L : CapstoneLedger n p C X F S D)
    (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞)
      = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T :=
  L.seam.finiteness_stack σ N

/-- THE PER-p INSTANTIATION BUNDLE (U10's quantifier shape) over the FIXED
    p-uniform data (C, KC, K7, S). ROUND-2 FIELDS: `Tpin` — the tree/classifier
    identification (CRITICAL 2), the named premise; `sibjc` — CL-10's
    (SIB)/(JC-multi) rows AT the pinned instance (CRITICAL 1); `cl7_slice` — the
    decided-family cardinality bound at the p-UNIFORM `K7.Tbound` (CRITICAL 6: the
    same T(n, N) serves every prime, so no per-instance finite max realizes it). -/
structure UInstance (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n) (p : ℕ) (hp : p.Prime) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  L : CapstoneLedger n p C X F S D
  Dpin : RegPin C D
  bridge : @ZpBridge n p ⟨hp⟩ X
  Tpin : @TreePin n p ⟨hp⟩ X F L.seam
  sibjc : @SibJcRows n p ⟨hp⟩ X F L.seam Tpin
  cl7_slice : ∀ (σ : SplittingType n) (N : ℕ),
    (F.thrSlice σ N).card ≤ K7.Tbound N

end LeanUrat.MovesU
