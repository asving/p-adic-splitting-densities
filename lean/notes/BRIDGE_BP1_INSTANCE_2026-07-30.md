# BRIDGE BLUEPRINT BP1 — THE INSTANCE BRIDGE (2026-07-30)

AREA: constructing the per-prime `UInstance` bundles for `LeanUrat.MovesU.theoremU`
at general degree n, from the built corpora + the OM classifier, and formulating the
thirteen reserved capstone slots (the wave-4 boundary parameters of U10).
AUTHOR: blueprint-architect agent (bridge campaign, task #69).
GROUND TRUTH: `lean/notes/MOVES_2026-07-24.md` (frozen dual-accepted; §U-SQUEEZE
~12879–13629, ledger display 13224–13361, SQ.0/TRACK-COUNT 12925–13018);
as-built statements verified TODAY against the files named in §2 (never memory).
DISCIPLINES BINDING EVERY UNIT: statement fence (named warranted hypotheses only,
flagged for ratification); countermodel-first (§5 units run BEFORE their provers);
honest sorries (unprovable-as-stated → repair adjudication); Lean 4.31.0 + Mathlib;
green records from `lake build` only (methodology rule #2).

---------------------------------------------------------------------------
## 1. GOAL

`theoremU` (LeanUrat/MovesU/U10_theoremU.lean:104) consumes, beyond its p-uniform
packs and thirteen bare `Prop` parameters, ONE per-prime premise:

    inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp

This area delivers, in a new file family `lean/LeanUrat/MovesU/Bridge*.lean`:

(G1) **The constructions.** For every prime p, genuine (non-surrogate) instances of
     every per-prime field of `UInstance` (DefsLedger.lean:832): a classifier
     `X : ClassifierSpec n p` and fiber series `F : FiberSeries n p X` built over the
     RATIFIED MovesT `VTree` corpus; the tautological roster `D : RegData p` built
     from the carried §S corpus `C : UCarriers n` with its `RegPin` holding by
     definitional pins; the solve family `S : SolveData n` pinned to `MovesS.Rsh`;
     the `ZpBridge` built from genuine ℤ_p[X] factorization; the `TreePin`; the
     `TreeSeam` assignment `treeOf`; the assembled `CapstoneLedger`.

(G2) **The kernel pack.** Two hypothesis structures, `BridgePre n C` (p-uniform,
     bound before any construction) and `BridgeKernels n C p …` (over the
     constructed X/F/seam/Tpin), whose fields are EXACTLY the named open kernels the
     note leaves open — each typed over built vocabulary, never True-instantiable
     (the wave-2 doctrine: false for instances the note would reject). Everything
     not in the packs is PROVED outright.

(G3) **The firing theorem.**

    theorem mkUInstance (n) (hn : 2 ≤ n) (C : UCarriers n) (KC : KernelCarriers n C)
        (K7 : Cl7Kernel n KC) (BP : BridgePre n C) (p : ℕ) (hp : p.Prime)
        (BK : BridgeKernels n C KC K7 BP p hp) :
        UInstance n C KC K7 (bridgeSolve C BP.hdet) p hp

    theorem theoremU_fired … : (theoremU's conclusion at the constructed instance)

     so that Theorem U's remaining conditionality = the p-uniform packs (other
     areas) + `BridgePre`/`BridgeKernels` rows (each a named open kernel) + the
     thirteen slots + per-p (REG-p).

(G4) **The thirteen slots.** A `MovesU/Slots.lean` family: one NAMED typed Prop per
     reserved parameter of `theoremU` (rel1 rel2a rel2b rel2d rel2e rel3, rs0Lump,
     trackRule, dnLattice, m1m5Echo, x1aDict, m4bConst, jcInvHist — U10 docstring
     lines 63–85), stated over built or newly-designed carrier vocabulary, with a
     non-vacuity audit and the consumption theorem `theoremU_bridged` that
     instantiates the 13 signature parameters with these Props. The parameters
     STAY in theoremU's signature (statement fence); instantiation is call-site.

NON-GOALS (owned elsewhere, consumed as parameters here): constructing
`C : UCarriers n` (the §S instantiation area; worked n = 2 precedent
`MovesS/N2Shape.lean`), `KC : KernelCarriers`, `K7 : Cl7Kernel`,
`KT : UpstreamTyped` (the §X/§V/§R-base area), proving any of the open kernels
themselves (E0, HMC, X.3, TRACK-COUNT, hExhaust-general-n — permanently fenced,
`notes/UNIFORMITY_COMPLETION_BLUEPRINT_2026-07-30.md`). See §6 Q4.

---------------------------------------------------------------------------
## 2. OBJECT INVENTORY (verified by reading, 2026-07-30)

### 2.1 Consumed — MovesU interface (all in lean/LeanUrat/MovesU/)
| object | file:line | status |
|---|---|---|
| `SplittingType n` (subtype of Multiset (ℕ×ℕ), entries ≥ 1, Σe·f = n) | Defs.lean:30 | built, Fintype at U0b |
| `Box p n N := Fin n → ZMod (p^N)`, `Box.toPoly`, `boxProj` | Defs.lean:36–45 | built |
| `ClassifierSpec n p` (canonical/trueType/canonical_stable/baseSection) | Defs.lean:62 | hypothesis structure — INSTANTIATE |
| `VPSound X` | Defs.lean:72 | Prop — kernel row |
| `SolveData n` (R : SplittingType n → RatFunc ℚ) | Defs.lean:106 | INSTANTIATE |
| `RegData p` (24 fields: depthSet/Pool/Block/bidx/K/bterm/bsplit/iota/JIdx/Jcell/WIdx/Wcoef/legIdx/betaLeg/act + cards + instances) | Defs.lean:124 | INSTANTIATE |
| `RegP D` = (r1) ∧ (r2) | Defs.lean:209 | per-p hypothesis of theoremU — NOT constructed; partial transport §3.3 |
| `FiberSeries n p X` (Tree/mass/thr/thrSlice/mem_slice_iff/slice_exhausts) | Defs.lean:227 | INSTANTIATE |
| `vmap`, `vmap_deg_sum`, `UCarriers` (T/MS/RB/hdc/hK/Fam/chain), `UCarriers.cl1`, `KsubM1C1T`, `MenuWFT`+`menuWFT_holds` | DefsCarriers.lean:35–137 | built |
| `KernelCarriers`, `CtsmSyntaxRow`, `UpstreamTyped`, `Cl7Kernel` | DefsLedger.lean:124–217 | p-uniform packs — consumed as parameters |
| `TreeSeam` (treeOf/thr_le/count_tie) + derived `finiteness_stack` | DefsLedger.lean:231–283 | INSTANTIATE (count_tie = kernel row) |
| `digitIdx`, `chartWitness`(+`_inj`), `TreePin` (13 fields incl. vt_surj, canonical_pin, boxeq_digits) | DefsLedger.lean:289–371 | INSTANTIATE |
| `SibJcRows` (sib/sib_at/jc_multi at the pinned models) | DefsLedger.lean:389 | kernel rows (CL-10, open) |
| `LegRoster`, `legTarget` | DefsLedger.lean:422–441 | built — the tautological legIdx |
| `RegPin` (17 pins) + `RegPin.detHyp` | DefsLedger.lean:479–562 | INSTANTIATE (pins definitional at the tautological roster) |
| `SolveSeam` (series_tie/r_is_solve) + derived R_defined/R_agree/rs4_eval/evalℝ_eq_Rval/solve_stack | DefsLedger.lean:571–676 | INSTANTIATE (series_tie = kernel row [3t]) |
| `ZpReads`, `ZpBridge` (zfType/zf_pos/zf_factor/lift_exists/lift_true) + zpCount/zpDmass laws | DefsLedger.lean:686–759 | INSTANTIATE — see RISK R1 (COUNTERMODEL FIRST) |
| `CapstoneLedger` (10 fields) | DefsLedger.lean:782 | ASSEMBLE |
| `UInstance` (X/F/D/L/Dpin/bridge/Tpin/sibjc/cl7_slice) | DefsLedger.lean:832 | ASSEMBLE |
| `theoremU` (13 bare Props + hn + inst) | U10_theoremU.lean:104 | built; consumption target |
| `RegData.pool_self_mem` | U8_regP_access.lean | built (used by detHyp) |

### 2.2 Consumed — MovesS (owner of the S-side vocabulary)
| object | file | status |
|---|---|---|
| `TableShape` (State/fin/deq/VType/vdeg/vEquiv/vdeg_spec/Out/finO/odata) | Defs.lean:66 | built; NOTE: NO `Nonempty (State e)` field — see Q3 |
| `Outcome.m/.c/.verdicts`, `routeOf`, `Member.continuing` (= status.isRight) | Defs.lean:40–58,37 | built |
| `verdictImage`, `splitOuts`, `Kmat`, `bTerm`, `consumedDeltas` (iterate from {1}), `MovesS.RegP`, `OKat`, `evalAt`, `DetHyp`, `DegCons` | Defs.lean | built |
| `bSplit` (BSplitDef), `blockSolve` (BlockSolve), `blockSolveLt`+`blockSolve_spec` (BlockSolveSpec), `powSubst` (PowSubst), `Rsh` (RshDef) | per-file | built |
| `MeasuredSide` (Pools/Box/Cell/cells/Rep/μcell/activeState …), `RatBurdens` (ι/jPCell), `ShapeFam` (Sh/δOf), `KmatHyp`, `PoolHyp` | Defs/Interfaces | built |
| `RS4Chain` (L/B/PrimePools/prime_base/legs_reg/legs_read/Sigmas/sig_exact/WshP/Rval/r_bdd/decidedTotal/x3_total/rs1_equates/rsh_interp/wsh17_pin) | Interfaces.lean:129 | built |
| n = 2 worked precedent `n2T : TableShape 2` | N2Shape.lean:63 | built |

### 2.3 Consumed — MovesT / MovesD / MovesSp (the tree corpus)
| object | file | status |
|---|---|---|
| `VTree p F` (chains/hfin/hclosed/hleaf …), `VTree.typemult`, `VTree.thr n`, `VTree.fiberAt` | MovesT/Defs.lean:487,502,734,518 | built, ratified round 4 |
| `Realizes T χ Tr` | MovesT/Defs.lean:543 | built |
| `vtree_eq_of_fiberAt` (fibering-tree uniqueness) | MovesT/F3_dictSum.lean:45 | PROVED Lean-core |
| `treeN` (mass identity, threshold-free) / `TreeNStable`+`treeN_stable` | MovesT/E11_treeN.lean:42,90 | treeN PROVED; treeN_stable = FENCED sorry (named open row, owner HC-2/D4R0K) |
| `ramIdx`/`resDeg` (junk-dispatch through IsLocalRing (AdjoinRoot g)) | MovesT/Defs.lean:1107,1116 | built — RISK R1: reads the ORDER's invariants, not the field's |
| `CellAssign`/`CellData`/`SiteLedger`/`TreeScaffold`/`SibCount(At)`/`JCmultiAt` | MovesT/Defs.lean | built (consumed via SibJcRows rows) |
| `MovesD.CanonPolicy p F`, `MovesD.TreeModel p F n N m pol`, `MovesD.Box p m` | MovesD/Defs.lean:356,630 | built |
| SP8 `CanTreeModel` (real-TreeModel instantiation, n = 2 witness) | MovesSp/SP8* | built — VERIFY generality in IB-D1 |

### 2.4 Consumed — OM engine (the classifier side)
| object | file | status |
|---|---|---|
| `classify p n : (N : ℕ) → monicBox p N n → ClusterShape` (DEF B.3, f-dependent root) | OM/Classifier.lean:652 | built, general (p, n) |
| decoders `typeOf5/typeOf7/typeOfW/…` (ClusterShape → Option FactorizationType, per-menu) | OM/ChainMenu*.lean, WildMenu*.lean | built, menu-scoped |
| `FactorizationType` (data : Multiset (ℕ×ℕ); NO positivity) + `.degree` | Interface.lean:152–158 | built |
| n = 2 all-primes precedent: `UniformModelN2` (decidedCountP, cluster_coveringP), `UniformCapstone` (fixed numR/denR…, `hExhaustP`, M7 p, gates p=2/p=3) | OM/UniformModelN2.lean, OM/UniformCapstone.lean | built, Lean-core |
| `RealInstanceV2` (realM2/realD2/realF2, montes_unconditional) — the CountingModel-spine capstone | OM/RealInstanceV2.lean | built; DIFFERENT spine from theoremU — enrichment target only |

STATUS NOTE: the OM chain certifies its density ties on the `CountingModel`/
`MontesDataV2` spine, NOT on `ClassifierSpec`. The bridge does not import OM modules
on the mkUInstance path in the default architecture (§3.4, Q1); OM enters through
the optional agreement/enrichment units (IB-F7, IB-D19).

---------------------------------------------------------------------------
## 3. THE MATHEMATICS

### 3.1 The vocabulary dictionary (SplittingType ↔ VType-multisets ↔ FactorizationType)

Three σ-vocabularies coexist: MovesU's `SplittingType n` (entries ≥ 1, Σe·f = n),
the chain's σ-index `Multiset C.T.VType` with membership `Sigmas` (`sig_exact`:
Σ vdeg = n), and OM's `FactorizationType` (no positivity). The load-bearing new fact:

(†1)  `vmap C.T : SplittingType n → Multiset C.T.VType` is a BIJECTION onto
      `{s // s ∈ C.chain.Sigmas}`.

Injectivity: post-compose with `fun v => (((T.vEquiv v).1.1 : ℕ), ((T.vEquiv v).1.2 : ℕ))`.
Key identity (the roundtrip): for x ∈ σ.1 the vmap entry is
`vEquiv.symm ⟨(⟨x.1, _⟩, ⟨x.2, _⟩), _⟩`, so `Equiv.apply_symm_apply` recovers the pair;
`Multiset.map_map` + `attach_map_val` collapse the attach (the same three-step dance
already executed in `vmap_deg_sum`, DefsCarriers.lean:47–69 — reuse its hcongr/hattach
pattern verbatim). Surjectivity onto Sigmas: given s with (s.map vdeg).sum = n, set
σ.1 := s.map (fun v => (((vEquiv v).1.1 : ℕ), ((vEquiv v).1.2 : ℕ))); positivity from
ℕ+; degree sum by `vdeg_spec`; then `vmap C.T σ = s` by the reverse roundtrip
(map over attach of a map — the only genuinely fiddly multiset computation in the
area). Corollary (†1c): sum transport — for any commutative-monoid-valued f,
`∑ σ : SplittingType n, f (vmap C.T σ) = ∑ s ∈ C.chain.Sigmas, f s`
(Fintype sum ↔ Finset sum through the equivalence; `Finset.sum_nbij'`).

The OM dictionary (needed only for enrichment units): `sigmaToFT σ := ⟨σ.1⟩` with
`degree = n`; partial inverse under positivity. Trivial; isolated so OM-side units
never touch the capstone path.

### 3.2 The level-N boxes and the digit pin

Three boxes: `MovesU.Box p n N = Fin n → ZMod (p^N)` (coefficients),
`QuotientBox.monicBox p N n` (monic polynomials — OM side), `MovesD.Box p (n·N)`
(digits — MovesT side).

(†2)  For 0 < N: `boxPolyEquiv : Box p n N ≃ monicBox p N n`, f ↦ `Box.toPoly f`.
      AT N = 0 THE EQUIV IS FALSE: `ZMod (p^0) = ZMod 1` is trivial, every polynomial
      is 0 with natDegree 0 ≠ n, so `monicBox p 0 n` is EMPTY while `Box p n 0` is a
      singleton (this is exactly `RealInstanceV2.stratumCount_level0`'s mechanism).
      Every unit touching the poly side carries the `0 < N` guard — same guard
      discipline as `TreePin.chart` (round-3 CRITICAL 1).

Injectivity: coefficient extraction (`Polynomial.coeff_add`, coeff of X^n, finset-sum
coeff — i < n cases). Surjectivity: g monic natDegree n ↦ fun i => g.coeff i; the
reconstruction `g = X^n + Σ C (g.coeff i) X^i` is `Polynomial.ext` + monic leading
coefficient. Nontriviality of `ZMod (p^N)` from p prime, N ≥ 1 (p^N > 1).

(†3)  `boxEquivD : Box p n N ≃ MovesD.Box p (n * N)` for 0 < N, by base-p digits:
      forward `f ↦ fun j => digit (j / N) of f (j % N)`… stated cleanly through
      `digitIdx n N i k = ⟨i·N + k, _⟩` (DefsLedger.lean:289): the (i,k) slot carries
      the k-th base-p digit of `(f i).val`. Inverse: `f i := Σ_k (d (digitIdx i k)) · p^k`
      in ZMod (p^N). The equivalence is the standard finite base-p positional system:
      `Nat.digits`-free formulation via ZMod.val div/mod — the two composites reduce to
      (a) Σ_k ((v / p^k) % p) p^k = v for v < p^N (strong induction on N or
      `Nat.sub_mod_eq_zero`-style telescoping; Mathlib `Nat.sum_range_succ` +
      `Nat.div_add_mod`), and (b) digit extraction of the sum.
      LAW (†3b) `boxeq_digits` (TreePin's field, DefsLedger.lean:351):
      `f i = Σ_k ((boxeq N f (digitIdx n N i k)).val : ZMod (p^N)) * p^k` — this IS
      composite (a) read in ZMod, `push_cast` after the ℕ-level identity.

Compatibility (†3c): `boxProj` (level reduction) corresponds to digit truncation and
to `Polynomial.map (ZMod.castHom …)` under (†2) — needed by the canonical_stable
plumbing (IB-D8) and by nothing else.

### 3.3 The tautological roster: RegData/RegPin from the carrier pack

DESIGN PRINCIPLE (the r_is_solve pattern): `RegData` is free data + `RegPin` equates
it to the real §S objects. Constructing D FROM those objects makes every pin
`rfl`/`Equiv.refl`/proof-irrelevance — the pins cost nothing and can never drift.

    noncomputable def bridgeRegData (C : UCarriers n) (hne : BlockStatesNe C)
        (p : ℕ) : RegData p where
      depthSet := (consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))
      one_mem_depthSet := …           -- (†4a)
      Pool := _.image (p ^ ·); pool_eq := rfl
      Block := {e : ℕ // e ∈ Finset.Icc 1 n}      -- instNe: 1 ∈ Icc 1 n from 2 ≤ n
      bidx e := C.T.State e.1                      -- instBiNe: hne — see (†4b)
      blockDim e := Fintype.card (C.T.State e.1); bidx_card := rfl
      K e := Kmat C.T C.RB e.1 (C.hK e.1 e.2)
      bterm e i := ∑ σ' ∈ verdictImage C.T e.1 i, bTerm C.T C.RB e.1 σ' i
      bsplit e i := if hdet : DetHyp C.T C.RB C.hK
        then ∑ σ' ∈ C.chain.Sigmas, bSplit … (blockSolveLt C.RB C.hdc C.hK hdet e.1) σ' i
        else 0
      iota e i := C.RB.ι e.1 i
      JIdx e := Σ (τ : C.T.State e.1) (o : {o // o ∈ splitOuts C.T e.1 τ}),
                  {c // c ∈ (C.MS.cells e.1 τ o.1).?}   -- exact carrier per MeasuredSide.cells
      Jcell e j := (C.RB.jPCell e.1 j.1 j.2.2).val
      cellCount e := ∑ τ, ∑ o ∈ splitOuts …, (C.MS.cells e.1 τ o).card
      WIdx := {Ŝ // Ŝ ∈ C.Fam.Sh}; shapeCount := C.Fam.Sh.card
      Wcoef Ŝ := (C.chain.WshP Ŝ.1).val
      legIdx e := LegRoster C.T e.1
      legCount e := ∑ τ, ∑ o ∈ splitOuts …, Outcome.c (C.T.odata e.1 τ o)
      betaLeg e l δ := if h : 0 < δ ∧ DetHyp C.T C.RB C.hK
        then powSubst ⟨δ, h.1⟩ (∑ σ' ∈ C.chain.Sigmas,
               blockSolve C.T C.RB C.hdc C.hK h.2
                 (legTarget C e.1 e.2 l).1.1 (legTarget C e.1 e.2 l).1.2
                 (legTarget C e.1 e.2 l).2 σ')
        else 0
      act g q₀ := if h : g ∈ OKat (q₀ : ℚ) then evalAt (q₀ : ℚ) ⟨g, h⟩ else 0

    def bridgeRegPin … : RegPin C (bridgeRegData C hne p)
      -- blk := Equiv.refl; st := fun _ => Equiv.refl; every *_pin := rfl or
      -- dif_pos + Subsingleton.elim (DetHyp proofs are proof-irrelevant);
      -- legEquiv := fun _ => Equiv.refl; legSt := legTarget …; legSt_pin := rfl

The four NON-rfl obligations:

(†4a) `1 ∈ consumedDeltas C.T C.Fam`. `consumedDeltas = (step)^[n] {1}` with
      `step s = s ∪ image₂ (·*·) …` (MovesS/Defs.lean:613). Since s ⊆ step s, the
      seed {1} survives every iterate: induction on the iterate,
      `Function.iterate_succ_apply'` + `Finset.subset_union_left`. Routine.
      (If it were false the whole `RegData` type is uninstantiable — it is not.)

(†4b) `instBiNe : Nonempty (C.T.State e)` and `blockDim_pos`. `TableShape` carries
      Fintype but NO nonemptiness (verified §2.2). NOT derivable from the pack:
      `MeasuredSide.rep_ne` gives `Nonempty (Rep e τ)` only GIVEN a τ. Resolution:
      the p-uniform pack `BridgePre` carries the NAMED warranted hypothesis
      `hStateNe : ∀ e ∈ Finset.Icc 1 n, Nonempty (C.T.State e)`
      (warrant: the note's block table always contains the entrance state of block e
      — §S-RESUM's roster is per-block nonempty by construction; MOVES ledger rows
      CL-5/CL-1 quantify over it). STATEMENT-FENCE FLAG: new named hypothesis,
      needs orchestrator ratification (Q3). Countermodel-first does not apply (it
      is a premise, not a universal claim), but IB-B2 must first attempt derivation
      from `C.chain` (e.g. through `LedgerIV`/`RS1Bundle` fields, read before
      giving up) and report which route closed.

(†4c) The two Finset-image pins `Jcell_pin`/`W_pin` (DefsLedger.lean:516–528):
      LHS `Finset.univ.image (D.Jcell b)` over the sigma/subtype carrier vs RHS
      biUnion/image over the same data — both sides enumerate the same value set;
      proof by `Finset.ext` + `Finset.mem_image`/`mem_biUnion` unfolding + the
      sigma-carrier's `Fintype` enumeration (`Finset.mem_univ` trivial). Medium:
      the subtype-of-Finset ↔ Finset-membership plumbing (`Finset.attach` on cells
      is the cleanest carrier choice — pick `JIdx` to make this proof shortest).

(†4d) The three cardinality pins `cell_pin`(=JIdx_card)/`leg_pin`(=legIdx_card):
      `Fintype.card` of a sigma = Σ of Σ of fiber cards (`Fintype.card_sigma`), then
      per-(τ,o): `Fintype.card {i : Fin mem.length // (mem.get i).continuing}
      = (mem.filter (fun μ => μ.status.isRight)).length = Outcome.c` — the count
      of continuing positions equals the filter length: `Fintype.card_subtype` +
      `List.length_filter` as `countP`, with `Member.continuing μ ↔ μ.status.isRight
      = true` (`Member.continuing` def MovesS/Defs.lean:37; mind the Prop/Bool
      coercion — `decide`-free route via `List.countP_eq_length_filter` and
      `List.count_eq_card_fin` style lemmas; expect Mathlib archaeology).

(†4e) `RegP` (the per-p gate) is NOT constructed — it stays theoremU's explicit
      hypothesis (D8: at a p failing (REG-p), no claim). PARTIAL TRANSPORT (IB-B15):
      from `C.chain` (legs_reg → `UCarriers.cl1`, pools_e0, rsh_interp) derive as
      much of `RegP (bridgeRegData …)` as is true at ALL-ACTIVE pools. The FULL
      transport is FALSE by design: the note's junk-block discipline (MOVES
      12208–12210) records junk-block determinants without requiring them nonzero,
      while (r1) demands EVERY block's det ≠ 0 at EVERY pool. IB-B16 documents this
      gap as a machine-readable comment + the note citation (no compiled
      countermodel possible without a concrete C; the unit produces the exact
      quantifier diff instead).

### 3.4 The classifier, the fiber series, the seam, and the pins

ARCHITECTURE (Q1 — RECOMMENDED OPTION B, "the classifier IS the tree-fibering
verdict"): define `canonical` THROUGH the ratified MovesT corpus, so that
`TreePin.canonical_pin` holds by construction and the OM engine ties in later as an
agreement enrichment. Option A (canonical := OM `classify` + decode) leaves
canonical_pin as an unprovable seam at general n (the classifier ↔ VTree
identification is HC-2-flavored open content) — it would re-create the exact
round-2 CRITICAL 2 defect as a permanent row. Option B makes it definitional and
concentrates ALL open content into four named rows (transfer, count_tie, vp_sound,
env_tendsto). The n = 2 OM results then discharge rows AT n = 2 through IB-F7
instead of blocking the general construction.

Fixed once per (n, p): a canonical policy and per-level models

    pol : MovesD.CanonPolicy p (ZMod p)         -- wire from MovesSp SP8's real
    Tm N : MovesD.TreeModel p (ZMod p) n N (n*N) pol   -- CanTreeModel; VERIFY
    chart N hN := chartWitness n N hN            -- the digit chart i ↦ (i,0)

(IB-D1/D2 are VERIFY-AND-WIRE adjudication units: SP8's `CanTreeModel` was built as
the real-TreeModel instantiation with an n = 2 non-vacuity witness — confirm it is
(n, N)-generic; if n = 2-specific, the unit reports the exact generalization needed
and the area re-plans. The chart choice must match `Realizes`'s read semantics —
the chart tells the model which digit coordinates carry the coefficients' leading
digits; `chartWitness` is the digit-0 chart, consistent with (†3)'s slot layout.)

(†5)  THE TREE CARRIER.  `Tree σ := {V : MovesT.VTree p (ZMod p) //
      V.typemult = σ.1 ∧ RealizedSelf V}` where
      `RealizedSelf V := Realizes (Tm (lvl V)) (chart (lvl V) _) V` at
      `lvl V := max (V.thr n) 1`  — σ-typed, complete finite canonical BY
      CONSTRUCTION (VTree's own fields), realizable at its own threshold level.
      `vt := Subtype.val` (injective), `vt_typemult`/`vt_thr` := rfl.
      REALIZABILITY MUST BE IN THE CARRIER: with all σ-typed VTrees, `vt_real`
      (every carried tree realizes at every level ≥ thr) is expected FALSE —
      junk trees no polynomial realizes (RISK R3, countermodel unit runs first).

(†6)  THE TRANSFER ROW (the ONE stability kernel, consumed four times):
      `realizes_transfer : ∀ (V : VTree p (ZMod p)) (N N' : ℕ) (hN : 0 < N)
         (hN' : 0 < N'), V.thr n ≤ N → V.thr n ≤ N' →
         Realizes (Tm N) (chart N hN) V → Realizes (Tm N') (chart N' hN') V`
      — TREE-N's decision/realization stability across levels (the note's Thm 2.1
      face; the Lean-side open row `MovesT.treeN_stable` is its fenced sibling —
      cite both, do NOT consume the sorried treeN_stable). Consumers: vt_real
      (IB-D15), vt_surj (IB-D16), canonical_stable (IB-D8), treeOf coherence.
      Also needs the FIBER-side transfer face for canonical_stable:
      `fiber_transfer : … fiberAt (Tm N) (chart N _) (boxeq N (boxProj … f)) →
         fiberAt (Tm N') …(boxeq N' f)` for N ≤ N' — stated jointly in the row
      structure `TransferRow n p` (two fields). Owner: HC-2/D4R0K + TREE-N.

(†7)  THE CLASSIFIER.
      `canonical N f := if hN : 0 < N then
         (if h : ∃ (σ : SplittingType n) (T : Tree σ), thr σ T ≤ N ∧
              (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f)
          then some h.choose else none) else none`  (open Classical).
      WELL-DEFINEDNESS of the emitted σ (needed for `canonical_pin`'s forward
      direction): if trees T, T' of types σ, σ' both fiber at f, then
      `vt σ T = vt σ' T'` by `MovesT.vtree_eq_of_fiberAt` (F3_dictSum.lean:45,
      PROVED), hence σ.1 = σ'.1 by typemult, hence σ = σ' by `Subtype.ext`.
      `canonical_pin` then holds by if-unfolding + this uniqueness (†7u).
      `canonical_stable`: from the ∃-witness at level N and `TransferRow`
      (thr ≤ N ≤ N'; fiber transfers along boxProj) — N = 0 source case is
      vacuous (canonical 0 _ = none ≠ some σ).
      `baseSection := .teichmuller` — `o3_teichmuller := rfl`.

(†8)  THE TRUE TYPE. Defined THROUGH ZpReads so that `lift_true` is definitional:
      `trueType N f := if h : ∃ σ, ZpReads n p zfType N f σ
         then some h.choose else none`.
      Uniqueness (†8u): for N arbitrary, IF a monic degree-n lift exists
      (`lift_exists`, (†10d)) then two σ's satisfying ZpReads agree on that lift:
      σ.1 = zfType g = σ'.1 ⇒ σ = σ'. So choose is the unique witness and
      `lift_true : trueType N f = some σ ↔ ZpReads … σ` follows by cases. At N = 0
      every g lifts f (trivial ring), so ZpReads pins ALL degree-n types at once —
      no σ (n ≥ 2 gives ≥ 2 types with distinct multisets, witnessed by X^n and an
      Eisenstein X^n − p… lift-independent argument), trueType 0 = none; the unit
      proves this edge or, if painful, notes trueType 0's value is irrelevant
      (no ledger row reads it at N = 0 — verify) and keeps the dichotomy silent.
      `VPSound X` (canonical ⇒ trueType) is the identification KERNEL ROW
      (CL-10's VP + VP-SOUND citation duty, U10's clause (ii) engine) — open.

(†9)  MASS, SLICE, SEAM.
      `mass σ T := (Nat.card {f : Box p n (lvl T) // canonical (lvl T) f = some σ
          ∧ treeOf-agrees…}) / p^(n · lvl T)` — cleanest equivalent: define mass
      AT THE TREE'S OWN LEVEL as the normalized fiber count of `(vt σ T).fiberAt`:
      `mass σ T := (Nat.card {x : MovesD.Box p (n * lvl T) //
          (vt σ T).fiberAt (Tm (lvl T)) (chart _ _) x} : ℝ≥0∞) / p^(n · lvl T)`.
      `count_tie` (TreeSeam field) then says: this normalized count is LEVEL-
      CONSTANT and matches the treeOf-partition at every N ≥ thr — THE [3t]/TREE-N
      kernel row (`count_tie_row`), discharge candidate `MovesT.treeN` at
      (Tm N, chart N) whose hypothesis rows are exactly the `SibJcRows` pack rows
      + per-instance CellAssign/SiteLedger/TreeScaffold suppliers (HC-2 data).
      The blueprint keeps the row bare and specifies the OPTIONAL discharge chain
      as gated units (IB-D20/D21, adjudication; see Q7).
      `thrSlice σ N := (slice_finite σ N).toFinset` from the row
      `slice_finite : ∀ σ N, {T : Tree σ // thr σ T ≤ N}.Finite` (CL-7's
      finiteness — the typed face of TRACK-COUNT at the instance; p-uniform bound
      is separate: `slice_card_le : (thrSlice σ N).card ≤ K7.Tbound N` = the
      `cl7_slice` row). `mem_slice_iff`/`slice_exhausts` follow definitionally.
      `treeOf σ N f := (canonical_pin ⇒ ∃ T…).choose` with `thr_le`/`treeOf_pin`
      from choose_spec; single-valuedness by (†7u).
      `TreeSeam.finiteness_stack` is ALREADY DERIVED (DefsLedger.lean:243) — free.

### 3.5 The solve family and the checksum transport

(†10a) `bridgeSolve C hdet : SolveData n` with
       `R σ := Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ)`.
       `hdet : DetHyp C.T C.RB C.hK` is p-INDEPENDENT (a symbolic ℚ(q) determinant
       nonvanishing) and is carried in `BridgePre` as a NAMED warranted hypothesis
       (warrant: it is (r1)'s symbolic face — `RegPin.detHyp` DERIVES it from
       (REG-p) at any single prime, DefsLedger.lean:536; carrying it p-uniformly
       merely asserts (REG-p) holds somewhere, which theoremU's consumer supplies
       anyway. STATEMENT-FENCE FLAG, Q3). With hdet fixed, `r_is_solve` is `rfl`
       (no dite needed — cleaner than the junk-branch alternative, and it kills
       RISK R5 by construction).

(†10b) THE CHECKSUM TRANSPORT (the area's prettiest theorem):
       `rs4_checksum : ∑ σ : SplittingType n, bridgeSolve.R σ = 1` in ℚ(q).
       Proof: (i) by (†1c) the sum is `∑ s ∈ C.chain.Sigmas, Rsh … s`;
       (ii) for EVERY prime p: `(p:ℚ) ∈ C.chain.PrimePools` (`prime_base`), and
       `rsh_interp` + `rs1_equates` + `x3_total` give
       `evalAt p (∑ s ∈ Sigmas, Rsh s) = ∑ Rval s p = decidedTotal p = 1`
       (evalAt is a ring hom on OKat p; each Rsh s ∈ OKat p by rsh_interp);
       (iii) hence the fixed rational function g := (∑ σ R σ) − 1 lies in OKat p
       and evaluates to 0 at every prime ⇒ its numerator polynomial has infinitely
       many roots (`Set.Infinite` of primes in ℚ via `Nat.infinite_setOf_prime` +
       cast injectivity) ⇒ numerator = 0 (`Polynomial.eq_zero_of_infinite_isRoot`)
       ⇒ g = 0 (`RatFunc.num_eq_zero_iff`). The denominators never vanish at the
       evaluated primes on the OKat locus — the evaluation-to-num/den translation
       is the only fiddly step (`RatFunc.eval` vs `evalAt`'s subring presentation;
       reuse the `SolveSeam.rs4_eval` calc block's cast patterns in reverse).

(†10c) `SolveSeam` assembly: `r_is_solve := fun _ σ => rfl` (proof irrelevance for
       the hdet binder); `series_tie` is the KERNEL ROW
       `series_tie_row : ∀ σ, F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) p)`
       — the [3t] Haar-mass-vs-measured-chain seam, the note's named open premise.
       All five derived lemmas (R_defined/R_agree/rs4_eval/evalℝ_eq_Rval/
       solve_stack) come free from DefsLedger.

### 3.6 The ℤ_p bridge — REAL local field theory, with a live countermodel

The intended instance: `zfType g := (monicFactors g).map (fun h => (ramIdx h, resDeg h))`
where `monicFactors g` is the multiset of monic ℤ_p-polynomial irreducible factors.

(†11a) FACTORIZATION. ℤ_p is a DVR (Mathlib instance on `PadicInt`), hence
       `ℤ_p[X]` is a UFD. For monic g, extract `monicFactors g` from
       `UniqueFactorizationMonoid.factors` by scaling each factor monic (units of
       ℤ_p[X] = units of ℤ_p; each factor of a monic polynomial over a domain has
       unit-leading-coefficient — leadingCoeff multiplicativity), with
       `(monicFactors g).prod = g` (the unit product telescopes to 1 by comparing
       leading coefficients). Each factor is irreducible in ℤ_p[X].
(†11b) GAUSS TRANSFER: a MONIC irreducible of ℤ_p[X] with positive degree is
       irreducible over ℚ_p — `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`
       needs `IsFractionRing ℤ_[p] ℚ_[p]`: VERIFY the Mathlib instance
       (`PadicInt` API; if absent, prove via `IsDVR` + field-of-fractions
       characterization — an archaeology unit). Degree-0 factors cannot occur in
       a monic factorization (they'd be units).
(†11c) IP-1: `IsLocalRing (AdjoinRoot h)` for h monic, ℚ_p-irreducible, over ℤ_p.
       `AdjoinRoot h = ℤ_p[X]/(h)` is a finite ℤ_p-algebra and a DOMAIN (h prime in
       the UFD by Gauss). Route: ℤ_p is complete local hence HENSELIAN
       (`HenselianLocalRing` instance — VERIFY on the pinned Mathlib; else via
       `IsAdicComplete`); a finite algebra over a henselian local ring is a product
       of local rings; a domain has no nontrivial idempotents ⇒ local. If the
       product decomposition is not in the pinned Mathlib, the fallback direct
       proof: nonunits closed under addition via the norm/integrality argument
       (every x ∈ AdjoinRoot h is integral over ℤ_p; x is a unit iff its ℤ_p-norm
       is — hard-fable, budget accordingly).
(†11d) `lift_exists`: for f : Box p n N take
       `g := X^n + Σ_i C ((f i).val : ℤ_[p]) X^i` — monic (leading 1), natDegree n,
       and `g.map (toZModPow N) = f.toPoly` coefficientwise
       (`PadicInt.toZModPow` of a nat-cast is the ZMod cast of `.val`, then
       `ZMod.natCast_val`/`ZMod.cast_id'` — routine cast plumbing).
(†11e) `zf_pos`: on the local domain (†11c), `ramIdx h ≥ 1` (the maximal ideal of
       AdjoinRoot h contains p's image: p is a nonunit; ramificationIdx ≥ 1 iff
       map ≤ P — sSup membership) and `resDeg h ≥ 1` (inertiaDeg = finrank of a
       nonzero field extension ≥ 1 — `Ideal.inertiaDeg_pos`-style; VERIFY name).

(†11f) **THE DEGREE CONJUNCT IS FALSE AS TYPED — countermodel (RISK R1, runs
       FIRST).** `zf_factor`'s conjuncts 3+4 jointly force
       `(factors.map (ramIdx·resDeg)) = factors.map natDegree` (as multisets) for
       THE monic irreducible factors (the factorization is unique: monic ℚ_p-
       factorizations are unique and monic ℤ_p-polys are determined by their ℚ_p
       images — so the ∃ gives no freedom). Take p odd, c a non-square unit,
       `h := X² − p²·c` (monic, ℤ_p coefficients, irreducible over ℚ_p — its roots
       ±p√c ∉ ℚ_p). Then `AdjoinRoot h = ℤ_p[π], π² = p²c` IS local (m = (p, π),
       R/m = F_p, complement of m = units by the norm a² − b²p²c), so the junk
       dispatch does NOT fire, and: inertiaDeg = [F_p : F_p] = 1; ramificationIdx:
       pR ≤ m but pR ⊄ m² = (p², pπ) (else 1 = pa + πb ∈ m) ⇒ ramIdx = 1.
       So (ramIdx h)·(resDeg h) = 1 ≠ 2 = natDegree h, while the TRUE invariants
       of ℚ_p(√c)/ℚ_p are (e,f) = (1,2): **ℤ_p[π] is a NON-MAXIMAL ORDER and
       MovesT.ramIdx/resDeg read the order's invariants, not the field's.**
       At g := h itself (n = 2) the aggregate conjunct fails: {1} ≠ {2}.
       CONSEQUENCE: NO ZpBridge instance exists at odd p as currently typed (at
       p = 2 pick c with c mod 8 a non-square unit class — same argument).
       This blueprint therefore front-loads IB-E0 (compile the countermodel or
       refute this analysis) and gates ALL ZpBridge proving units on Q2's repair:
       re-point `ramIdx`/`resDeg` at the integral closure / the valuation ring of
       `AdjoinRoot (h.map Coe.ringHom)` (the field), where
       `Ideal.sum_ramification_inertia` (Dedekind, finite extension; one prime by
       locality) yields the pointwise `ramIdx h · resDeg h = h.natDegree` (†11g)
       and hence the aggregate. The GOLF campaign note already queues the
       pointwise-retype sign-off — this countermodel converts "queued nicety"
       into "blocking repair". MovesT Defs + MovesU DefsLedger are RATIFIED:
       the repair is a statement-change adjudication (Q2), never a silent edit.

### 3.7 The kernel packs and the assembly

    structure BridgePre (n : ℕ) (C : UCarriers n) : Prop-free data pack
      hdet     : MovesS.DetHyp C.T C.RB C.hK                     -- (†10a)
      hStateNe : ∀ e ∈ Finset.Icc 1 n, Nonempty (C.T.State e)    -- (†4b)

    structure BridgeKernels (n C KC K7 BP) (p) (hp) — over the CONSTRUCTED
        X := bridgeClassifier …, F := bridgeFibers …, seam, Tpin:
      transfer     : TransferRow n p                              -- (†6)
      slice_finite : ∀ σ N, {T : Tree σ // thr σ T ≤ N}.Finite    -- CL-7 face
      slice_bound  : ∀ σ N, (thrSlice σ N).card ≤ K7.Tbound N     -- cl7_slice
      count_tie    : (TreeSeam count_tie at the constructed treeOf) -- [3t]/TREE-N
      series_tie   : ∀ σ, F.seriesSum σ = ofReal (Rval (vmap σ) p) -- [3t]
      env_tendsto  : Tendsto X.env atTop (𝓝 0)                    -- hExhaust-n (FENCED math)
      vp_sound     : VPSound X                                     -- CL-10 VP cites
      sibjc        : SibJcRows n p Tpin                            -- CL-10 (SIB)/(JC-multi)
      cl6          : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)  -- CL-6 (Q6)
      cl11_ksub    : KsubM1C1T C.T                                 -- (K-SUB) m=1 (Q6)
      cl17         : C.chain.wsh17_pin                             -- W17ii (open by design)
      cl19_rep     : (CapstoneLedger.cl19_rep's statement over C)  -- CL-19 face (Q6)
      zp           : (post-Q2) the ZpBridge input laws not proved outright

    ORDERING CONSTRAINT: `slice_finite` is consumed by the DEFINITION of thrSlice
    (†9), so F's construction takes it as an argument — the pack splits internally:
    fields above the line feed constructions, fields below feed the ledger. The
    E-phase writer fixes the exact dependency order; the blueprint's invariant is
    only: NO field mentions an object constructed after it.

    CapstoneLedger assembly: cl4 := env_tendsto; cl6/cl10_vpsound/cl11_ksub/cl17/
    cl19_rep := rows; o3_teichmuller := rfl; seam := ⟨treeOf, thr_le, count_tie⟩;
    ssrc := ⟨series_tie, r_is_solve⟩; rs4_checksum := (†10b) PROVED.
    UInstance assembly: X/F/D/L/Dpin/bridge/Tpin/sibjc/cl7_slice := slice_bound.

    theoremU_fired: apply theoremU at (C, KC, K7, bridgeSolve, KT, 13 slots,
    fun p hp => mkUInstance …). Conclusion verbatim theoremU's.

### 3.8 The thirteen reserved slots (U10 docstring lines 63–85, verbatim owners)

Wave-D discharges these by BUILDING carriers; this area FORMULATES each slot as a
named typed Prop `Slot_<name> : Prop` (with parameters over built vocabulary where
it exists) + records the owner + the note display. The consumption theorem
`theoremU_bridged` instantiates theoremU's 13 Prop parameters at these Props —
callers then owe their PROOFS (or carry them as visible hypotheses), and the
True-instantiation escape documented in the wave-4 boundary record dies at the
bridged capstone while theoremU itself stays untouched (statement fence).

Per-slot notes (formulation targets, each its own unit; difficulty reflects the
wave-2 lesson that these were left bare precisely because faithful self-contained
typing FAILED once — MovesR adjudication #1):

| slot | row | owner | formulation vocabulary + trap |
|---|---|---|---|
| rel1 | CL-8 REL.1 | [2r] | base-change ledger clause at δ: parameterize by the MovesR re-architecture's CInterface carrier (raw material: the parked CStatements/GradedCarrier draft + `MovesRBase.SpeciesSyntax/AlphabetData`); TRAP: the jet-additivity typing refuted once (p^N-torsion — campaign ledger, MovesR FABLE leg); re-type per the recorded resumption charge (level-set digits → graded-piece composite) |
| rel2a/b/d/e | CL-8 REL.2(a)(b)(d)(e) | [2r] | same carrier; four clause slots |
| rel3 | CL-8 REL.3 | [2r] | the note says NO satisfiable self-contained statement exists (round-1 audit rejected an invented one); disposition unit: either a CInterface-relative typing or the honest record that rel3 stays a bare parameter with the note citation |
| rs0Lump | CL-9(α) RS.0 lumpability | [3] | the fiber-process lumpability over MovesD/MovesT strata: the kernel `kstep`-aggregation invariance of `C.MS` rows vs the tree strata; candidate vocabulary exists (MeasuredSide.kstep, RS4Chain.L) |
| trackRule | CL-7a (t1)/(t2)+(c1) | [4] | over MovesX: key/branch recognition predicates on `XHistory` + a `trackOf` assignment map compatible with `K7.track_restarts`'s (t3) face |
| dnLattice | CL-7b lattice + strict increment | [4] | key weights ∈ (1/K7.Dden)·ℤ, Dden ∣ n!, per-node strict ledger increment — over MovesX Pop/dTotal vocabulary |
| m1m5Echo | CL-14 M1+M5 echo | [2a] | the MovesSp catalogue ↔ M1 seam (notes/M1_bridge.md is the recorded raw material); closed upstream — the slot types the INSTANCE TIE |
| x1aDict | CL-15 dictionary beyond ALIGN | [5] | per-species GMN index dictionary: ties `KT.cl15_align`'s `X1aAlignP` to the DECLARED GMN axiom's index — the ONLY slot allowed to reference the trusted axiom (cite AXIOM_FAITHFULNESS entry) |
| m4bConst | CL-16 M4b constancy + M4b-T equivariance | [1v]/[2b] | over MovesV height/translation carriers (`CtsFamily`, writeHeights vocabulary — mind the Order0Perimeter fence: do NOT consume the quarantined shim) |
| jcInvHist | CL-19 h_ent/history residue | [2b] | over MovesT entrance vocabulary (`EntSt`, histories): the cl19_rep-complement — invariance in the HISTORY argument |

Non-vacuity audit (IB-G11): every formulated Prop must be FALSE for a degenerate
instance the note would reject (the wave-2 doctrine) — one compiled falsifier or
inline `example : ¬ Slot_x degenerate…` per slot. Closure manifest (IB-G12): every
identifier in each displayed Prop → its built decl path, grep-verified (the
standing CLOSURE MANIFEST rule from wave-4 round 7).

<!-- STAGE-4 CONTINUES -->
