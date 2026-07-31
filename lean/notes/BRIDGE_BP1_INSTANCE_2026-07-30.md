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

    noncomputable def bridgeRegData (hn : 2 ≤ n) (C : UCarriers n)
        (hne : ∀ e ∈ Finset.Icc 1 n, Nonempty (C.T.State e))  -- = BridgePre.hStateNe
        (p : ℕ) : RegData p where
      depthSet := (consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))
      one_mem_depthSet := …           -- (†4a)
      Pool := _.image (p ^ ·); pool_eq := rfl
      Block := {e : ℕ // e ∈ Finset.Icc 1 n}      -- instNe := ⟨⟨1, by omega⟩⟩ from hn;
                                                  -- at n = 0 Block is EMPTY and hne is
                                                  -- vacuous — hn is LOAD-BEARING (Codex f.2)
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

    def bridgeRegPin … : RegPin C (bridgeRegData hn C hne p)
      -- blk := Equiv.refl; st := fun _ => Equiv.refl; every *_pin := rfl or
      -- dif_pos + Subsingleton.elim (DetHyp proofs are proof-irrelevant);
      -- legEquiv := fun _ => Equiv.refl; legSt := legTarget …; legSt_pin := rfl

    ASSEMBLY ORDER (post-Codex findings 3+4): a structure literal cannot postpone
    required fields. The two dite fields are STANDALONE defs `bridgeBsplit`/
    `bridgeBetaLeg` (unit IB-B9, which now runs BEFORE the record unit IB-B8;
    the record literal above consumes them). Likewise `bridgeRegPin` (IB-B10) is
    assembled only AFTER the standalone pin lemmas exist (IB-B11 Jcell, IB-B12 W,
    IB-B13 bsplit/betaLeg) — the pin units are LEMMAS over bridgeRegData, and
    B10 is the final record literal wiring them in.

The four NON-rfl obligations:

(†4a) `1 ∈ consumedDeltas C.T C.Fam`. `consumedDeltas = (step)^[n] {1}` with
      `step s = s ∪ image₂ (·*·) …` (MovesS/Defs.lean:613). Since s ⊆ step s, the
      seed {1} survives every iterate: induction on the iterate,
      `Function.iterate_succ_apply'` + `Finset.subset_union_left`. Routine.
      (If it were false the whole `RegData` type is uninstantiable — it is not.)

(†4b) `instBiNe : Nonempty (C.T.State e)` and `blockDim_pos`. (Separately,
      `instNe : Nonempty Block` rides `hn : 2 ≤ n` — mkUInstance's EXISTING binder,
      threaded into bridgeRegData's signature post-Codex finding 2; no new premise.)
      `TableShape` carries
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
      hypothesis (D8: at a p failing (REG-p), no claim). TYPED PARTIAL TRANSPORT
      (retyped post-Codex finding 8 — the locus vocabulary is now a unit, IB-B17):
        `RegPAt D q₀ e : Prop` := the (q₀, e)-clause of `RegP` factored out, with
          the decomposition lemma `RegP D ↔ ∀ q₀ ∈ D.Pool, ∀ e, RegPAt D q₀ e`
          (definitional re-grouping of Defs.lean:209's ∀∀-body);
        `bridgeActiveLocus C p : Finset ℕ` := (bridgeRegData …).Pool.filter
          (fun q₀ => (q₀ : ℚ) ∈ MovesS.allActivePools C.MS) (Classical
          decidability) — EXACTLY `pools_e0`'s all-active locus
          (MovesS/Interfaces.lean:138) read on the roster's pool.
      IB-B15a proves the (r2) conjunct of `RegPAt (bridgeRegData …) q₀ e` for
      every q₀ ∈ bridgeActiveLocus (from cl1/legs_reg + rsh_interp + B3's
      bridgeAct_ok); IB-B15b proves the (r1) conjunct at the CHAIN-COVERED pairs
      — primary route q₀ = p^1, where `UCarriers.cl1` (= legs_reg at the base
      prime, DefsCarriers.lean:98) supplies `MovesS.RegP`, transported through
      the K_pin submatrix-determinant identity (RegPin.detHyp's calc,
      DefsLedger.lean:536ff, run in reverse); secondary probe: pools_e0's
      PoolHyp packages at deeper all-active pools. Each unit RETURNS its typed
      residual (Pool \ bridgeActiveLocus; the uncovered (q₀, e) pairs). The FULL
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
      (`lift_exists`, (†11d)) then two σ's satisfying ZpReads agree on that lift:
      σ.1 = zfType g = σ'.1 ⇒ σ = σ'. So choose is the unique witness and
      `lift_true : trueType N f = some σ ↔ ZpReads … σ` follows by cases. At N = 0
      every g lifts f (trivial ring), so ZpReads pins ALL degree-n types at once —
      no σ (n ≥ 2 gives ≥ 2 types with distinct multisets, witnessed by X^n and an
      Eisenstein X^n − p… lift-independent argument), trueType 0 = none.
      ORDERING + FALLBACK CORRECTED (post-Codex finding 6): the N = 0 probe
      (IB-D10) runs BEFORE the lift_true prover (IB-D9b), per the binding
      cross-area countermodel-first rule. The old fallback ("verify no consumer
      reads trueType 0") is DELETED — it could not discharge lift_true's ∀-N
      obligation, which is a ZpBridge FIELD one must prove at N = 0 too. The
      accurate dependence, verified against the as-built source 2026-07-30:
      `ZpReads` is the ∀-lift predicate (DefsLedger.lean:686–689), so (†8u)'s
      uniqueness rides ONE lift — supplied by `lift_exists` at EVERY N including
      0 (at N = 0 the map-to-trivial-ring condition is automatic) — and
      lift_true's N = 0 instance holds by the same case split whether or not the
      "trueType 0 = none" edge is settled. D10 therefore gates D9b procedurally
      (rule compliance; it would also surface any ∃-read misreading of ZpReads)
      but a painful edge does NOT block D9b: the corrected pre-approved fallback
      is "record the edge OPEN + display the single-lift uniqueness derivation
      that D9b actually consumes".
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

    NO `zp` CATCH-ALL ROW (deleted post-Codex finding 5): G1 promises the
    ZpBridge built from genuine ℤ_p[X] factorization and G2 forbids un-named
    conditionality — a catch-all row would hide exactly what G2 bans. Group E
    (post-Q2 repair) proves ALL FIVE ZpBridge fields outright: zfType (IB-E11,
    def), zf_pos (E5), zf_factor (E6/E7), lift_exists (E8), lift_true (D9b);
    assembly IB-E9. If a specific law stalls, the prover returns a
    blocked-report and the ORCHESTRATOR adjudicates adding it as a NAMED typed
    row with owner + note display (a new-named-row fence event: campaign ledger
    + Asvin digest) — never a silent catch-all.

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
| rel3 | CL-8 REL.3 | [2r] | the note says NO satisfiable self-contained statement exists (round-1 audit rejected an invented one); typing unit (rescoped post-Codex finding 10): the CInterface-RELATIVE typed Prop is the REQUIRED deliverable (the round-1 rejection was of a SELF-CONTAINED invention; carrier-relative is untried); the bare-parameter record is DEMOTED to a BLOCKED outcome requiring adjudication — it fails G4 and voids the G11a falsifier |
| rs0Lump | CL-9(α) RS.0 lumpability | [3] | the fiber-process lumpability over MovesD/MovesT strata: the kernel `kstep`-aggregation invariance of `C.MS` rows vs the tree strata; candidate vocabulary exists (MeasuredSide.kstep, RS4Chain.L) |
| trackRule | CL-7a (t1)/(t2)+(c1) | [4] | over MovesX: key/branch recognition predicates on `XHistory` + a `trackOf` assignment map compatible with `K7.track_restarts`'s (t3) face |
| dnLattice | CL-7b lattice + strict increment | [4] | key weights ∈ (1/K7.Dden)·ℤ, Dden ∣ n!, per-node strict ledger increment — over MovesX Pop/dTotal vocabulary |
| m1m5Echo | CL-14 M1+M5 echo | [2a] | the MovesSp catalogue ↔ M1 seam (notes/M1_bridge.md is the recorded raw material); closed upstream — the slot types the INSTANCE TIE |
| x1aDict | CL-15 dictionary beyond ALIGN | [5] | per-species GMN index dictionary: ties `KT.cl15_align`'s `X1aAlignP` to the DECLARED GMN axiom's index — the ONLY slot allowed to reference the trusted axiom (cite AXIOM_FAITHFULNESS entry) |
| m4bConst | CL-16 M4b constancy + M4b-T equivariance | [1v]/[2b] | over MovesV height/translation carriers (`CtsFamily`, writeHeights vocabulary — mind the Order0Perimeter fence: do NOT consume the quarantined shim) |
| jcInvHist | CL-19 h_ent/history residue | [2b] | over MovesT entrance vocabulary (`EntSt`, histories): the cl19_rep-complement — invariance in the HISTORY argument |

Non-vacuity audit (IB-G11a/b/c, split per family post-Codex finding 11): every
formulated Prop must be FALSE for a degenerate
instance the note would reject (the wave-2 doctrine) — one compiled falsifier or
inline `example : ¬ Slot_x degenerate…` per slot. Closure manifest (IB-G12): every
identifier in each displayed Prop → its built decl path, grep-verified (the
standing CLOSURE MANIFEST rule from wave-4 round 7).

---------------------------------------------------------------------------
## 4. UNIT SPLIT (92 units on the default path, recounted at REVISION 2: IB-A*
dictionary 12 · IB-B* roster 18 (B15→B15a/B15b, +B17) · IB-C* solve 7 (C3→C3a/C3b)
· IB-D* classifier/fibers 20 (D9→D9a/D9b; +2 gated: D20/D21) · IB-E* ZpBridge 13
(E0–E12) · IB-F* pack/assembly 7 · IB-G* slots 15 (G11→G11a/b/c); pre-approved
splits inside A9/A11/B5/E0/E1/E4 absorb overruns without new ids). Difficulty: R = routine-opus, H = hard-fable, ADJ = adjudication.
Sizes are expected LINES OF PROOF (statements excluded); anything that grows past
~40 splits per the standing rule. New files: MovesU/BridgeDict.lean (A),
BridgeRoster.lean (B), BridgeSolve.lean (C), BridgeTrees.lean + BridgeClassifier.lean
(D), BridgeZp.lean (E), BridgeKernels.lean + BridgeMk.lean (F), Slots*.lean (G).
Deps on OTHER AREAS: none on the construction path (C/KC/K7 are binders).

### Group A — dictionaries (†1–†3)
- **IB-A1** `sigmaToFT`/`ftToSigma` + degree laws + roundtrips. Deps: —. Sketch:
  Subtype.ext, Multiset.map_id tricks. R, ~15.
- **IB-A2** `vmap_roundtrip` : (vmap C.T σ).map (fun v => ((vEquiv v).1.1, (vEquiv v).1.2))
  = σ.1 (ℕ-valued pairs). Deps: —. Sketch: replay vmap_deg_sum's hcongr/hattach
  (DefsCarriers.lean:51–69) with the pair-valued reader. H, ~30.
- **IB-A3** `vmap_injective`. Deps: A2. Sketch: congrArg the roundtrip. R, ~8.
- **IB-A4** `sigmaOfSigs` : s ∈ C.chain.Sigmas → SplittingType n (data + membership).
  Deps: —. Sketch: map through vEquiv; positivity ℕ+; degree via vdeg_spec +
  sig_exact. R, ~20.
- **IB-A5** `vmap_sigmaOfSigs` : vmap C.T (sigmaOfSigs s hs) = s. Deps: A4. Sketch:
  the reverse roundtrip; attach-of-map collapse (Multiset.attach_map_val +
  map_congr; induction-free). H, ~35.
- **IB-A6** `vmapEquiv : SplittingType n ≃ {s // s ∈ C.chain.Sigmas}` +
  `vmap_mem` reuse. Deps: A3, A5. R, ~12.
- **IB-A7** `sum_vmap_eq_sum_Sigmas` (†1c), CommMonoid-valued. Deps: A6. Sketch:
  Finset.sum_nbij' univ→Sigmas. R, ~15.
- **IB-A8** `monicBox_empty_of_level0` (n ≥ 1) + `box0_unique`. Deps: —. Sketch:
  trivial-ring polynomial ext (replay RealInstanceV2.stratumCount_level0's core).
  R, ~15.
- **IB-A9** `boxPolyEquiv` (0 < N) (†2). Deps: A8 (edge doc only). Sketch: toFun
  Box.toPoly with Monic/natDegree proofs (nontrivial ring); invFun coeff-read;
  two ext lemmas. H, ~40 — pre-approved split: A9a (toPoly lands in monicBox),
  A9b (the equiv laws).
- **IB-A10** digit-sum identity (†3a, ℕ-level): v < p^N → Σ_{k<N} ((v/p^k)%p)·p^k = v.
  Deps: —. Sketch: induction on N with div_add_mod telescoping. H, ~35.
- **IB-A11** `boxEquivD` (0 < N) + `boxeq_digits` law (†3b). Deps: A10. Sketch: val
  digits through digitIdx layout; ZMod cast of A10; extraction direction by
  val-uniqueness < p^N. H, ~40 — split A11a equiv, A11b law if needed.
- **IB-A12** `boxProj`-compat (†3c): boxProj ↔ Polynomial.map castHom under (†2);
  digit truncation under (†3). Deps: A9, A11. R, ~25.

### Group B — the tautological roster (†4)
- **IB-B1** `one_mem_consumedDeltas` (†4a). Deps: —. Sketch: iterate-monotone seed
  membership. R, ~12.
- **IB-B2** `hStateNe` DERIVATION ATTEMPT (†4b): read RS1Bundle/LedgerIV for any
  field forcing Nonempty (State e); if found, prove; else RETURN the exact missing
  statement for the BridgePre row. ADJ, report-unit.
- **IB-B3** `bridgeAct` + `bridgeAct_ok : g ∈ OKat q₀ → bridgeAct g q₀ = evalAt …`.
  Deps: —. R, ~8.
- **IB-B4** `Fintype (LegRoster C.T e)` + DecidableEq (Classical). Deps: —. Sketch:
  Sigma-Fintype over instances; `Finset.attach` for the splitOuts subtype;
  decidable continuing via Bool isRight. R, ~20.
- **IB-B5** `card_legRoster` (†4d leg case): Fintype.card (LegRoster C.T e) =
  Σ τ, Σ o ∈ splitOuts, Outcome.c. Deps: B4. Sketch: card_sigma twice + the
  continuing-positions count = filter length (countP route). H, ~40.
- **IB-B6** JIdx carrier def + Fintype + `card_JIdx` = Σ Σ card cells. Deps: —.
  Sketch: same shape as B5, one level simpler. R, ~25.
- **IB-B7** WIdx = Finset-coe Fintype + card = Sh.card. Deps: —. R, ~6.
- **IB-B9** `bridgeBsplit`/`bridgeBetaLeg` — the two dite fields as STANDALONE
  defs (re-scoped post-Codex finding 3: they must exist BEFORE the record) +
  well-definedness lemmas (value independent of the hdet proof — proof
  irrelevance is definitional for Prop binders; the lemma is `dif_pos`
  rewriting). Deps: —. R, ~15. RUNS BEFORE B8.
- **IB-B8** `bridgeRegData hn C hne p` — the FULL record assembly in ONE literal
  (re-scoped post-Codex finding 3: no postponed fields; bsplit/betaLeg := B9's
  defs). `hn : 2 ≤ n` feeds `instNe` (post-Codex finding 2; supplied at use
  sites by mkUInstance's existing binder), `hne` (= BridgePre.hStateNe) feeds
  instBiNe/blockDim_pos. Deps: B1, B2/BridgePre, B3, B4, B6, B7, B9. Sketch:
  §3.3 display; instances wired. R, ~35 (mostly `where` lines).
- **IB-B11** `bridge_Jcell_pin` — STANDALONE image-equality LEMMA (†4c) over
  bridgeRegData (re-scoped post-Codex finding 4: not a RegPin field proof).
  Deps: B6, B8. Sketch: Finset.ext + mem_image/mem_biUnion chase. H, ~35.
- **IB-B12** `bridge_W_pin` — STANDALONE image-equality LEMMA. Deps: B7, B8.
  Sketch: univ.image over coe = Finset.image on Sh (`Finset.image_coe_univ`-
  style; attach). R, ~15.
- **IB-B13** `bridge_bsplit_pin`/`bridge_betaLeg_pin` — STANDALONE LEMMAS.
  Deps: B8, B9. Sketch: dif_pos + rfl. R, ~15.
- **IB-B10** `bridgeRegPin` — the record assembly, LAST of the pin units
  (re-ordered post-Codex finding 4): the rfl-pins inline (blk/st/depth/K/iota/
  bterm/act/legSt/legEquiv/legSt_pin/blockDim/shape/cell/leg) + the standalone
  lemmas wired in (Jcell_pin := B11, W_pin := B12, bsplit_pin/betaLeg_pin :=
  B13, card pins := B5/B6). Deps: B5, B6, B8, B9, B11, B12, B13. Sketch:
  Equiv.refl + rfl + the lemma wiring. R, ~30.
- **IB-B14** `bridgeRegData_pool_mem` sanity: p^1 ∈ Pool; RegP's binding shape at
  the roster (non-vacuity display: entryList ≠ ∅). Deps: B8. R, ~15.
- **IB-B17** RegP-transport VOCABULARY (new unit, post-Codex finding 8):
  `RegPAt D q₀ e : Prop` (the (q₀, e)-clause of RegP) + the decomposition lemma
  `RegP D ↔ ∀ q₀ ∈ D.Pool, ∀ e, RegPAt D q₀ e` (definitional re-grouping of
  Defs.lean:209) + `bridgeActiveLocus C p : Finset ℕ` (Pool filtered by
  `(· : ℚ) ∈ MovesS.allActivePools C.MS`, Classical decidability) — pools_e0's
  locus (MovesS/Interfaces.lean:138) on the roster's pool. Deps: B8. R, ~20.
- **IB-B15a** (r2)-transport ON THE ACTIVE LOCUS (split of B15, post-Codex
  findings 8+11): typed theorem `∀ q₀ ∈ bridgeActiveLocus C p, ∀ e,
  (r2 conjunct of RegPAt (bridgeRegData …) q₀ e)` from cl1/legs_reg +
  rsh_interp + B3's bridgeAct_ok. Deps: B17, C1. H, ~35.
- **IB-B15b** (r1)-transport AT CHAIN-COVERED PAIRS (split of B15): primary
  route q₀ = p^1 via `UCarriers.cl1` (= legs_reg at the base prime,
  DefsCarriers.lean:98) transported through the K_pin submatrix-determinant
  identity (RegPin.detHyp's calc, DefsLedger.lean:536ff, reversed); secondary
  probe at pools_e0's deeper all-active pools; RETURN the residual quantifier
  gap as a TYPED record (Pool \ bridgeActiveLocus; uncovered (q₀, e) pairs).
  Deps: B17, B10. H, ~35 — expected PARTIAL by design; deliverable is proof +
  typed gap spec.
- **IB-B16** the junk-block gap RECORD (†4e): machine-readable docstring unit — the
  precise sublocus where full (r1) exceeds the note (MOVES 12208–12210 cite), no
  proof obligations; now also indexes B15a/B15b's typed residuals. R, doc-only.

### Group C — solve + checksum (†10)
- **IB-C1** `bridgeSolve C hdet` + `r_is_solve` (rfl) + `bridgeSolve_ok`
  (OKat membership at primes via rsh_interp). Deps: A6. R, ~15.
- **IB-C2** per-prime evaluation-1 (†10b ii): ∀ p prime,
  evalAt p (Σ s ∈ Sigmas, Rsh s) = 1. Deps: C1. Sketch: map_sum on OKat +
  rsh_interp/rs1_equates/x3_total; ℝ-cast down to ℚ (Rval is ℝ-valued —
  the cast-back needs rsh_interp's ℚ→ℝ equality read injectively). H, ~35.
- **IB-C3a** the OKat→num/den translation (split of C3, post-Codex finding 11):
  for g ∈ OKat q₀, evalAt q₀ ⟨g,_⟩ = g.num.eval q₀ / g.denom.eval q₀ with
  g.denom.eval q₀ ≠ 0; corollary: evalAt q₀ ⟨g,_⟩ = 0 → g.num.eval q₀ = 0.
  Deps: —. H, ~25 (the archaeology lives here: RatFunc.num/denom eval API vs
  the OKat subring presentation).
- **IB-C3b** infinite-roots vanishing (split of C3): g : RatFunc ℚ,
  (∀ p prime, g ∈ OKat p ∧ evalAt p g = 0) → g = 0. Deps: C3a. Sketch:
  num.eval = 0 at infinitely many cast-primes (`Nat.infinite_setOf_prime` +
  cast injectivity); `Polynomial.eq_zero_of_infinite_isRoot`;
  `RatFunc.num_eq_zero_iff`. R, ~20.
- **IB-C4** `rs4_checksum_bridge` (†10b): Σ σ, bridgeSolve.R σ = 1. Deps: A7, C2,
  C3b. Sketch: apply C3b to (Σ R) − 1. R, ~20.
- **IB-C5** `bridgeSolveSeam` assembly given `series_tie` row. Deps: C1. R, ~8.
- **IB-C6** consistency display (optional gate): at n = 2 the bridgeSolve values at
  q' = 2, 3 match the OM UniformCapstone gates (1/3,1/3,1/3; 1/4,3/8,3/8) — a
  `decide`/norm_num seal ONCE an n = 2 UCarriers instance exists. ADJ (gated on
  the S-area's n = 2 pack), ~20.

### Group D — classifier, fibers, seam, pins (†5–†9)
- **IB-D1** VERIFY-AND-WIRE `pol`/`Tm` from MovesSp SP8 CanTreeModel: confirm
  (n, N)-genericity; export `bridgePol p`, `bridgeTm p n N`. ADJ, report+~15.
- **IB-D2** chart semantics check: `chartWitness` vs `Realizes`'s read positions
  (does the model read coefficient i's digits at slots digitIdx i k?); pin the
  choice; document against (†3)'s layout. ADJ, report+~10.
- **IB-D3** `Tree σ` carrier def (†5) + DecidableEq (Classical) + `lvl`. R, ~12.
- **IB-D4** `vt`/`vt_inj`/`vt_typemult`/`vt_thr` (all rfl-level). Deps: D3. R, ~10.
- **IB-D5** `TransferRow n p` STRUCTURE DEF (†6) — statement-only unit; fields
  realizes_transfer + fiber_transfer; docstring cites TREE-N/Thm 2.1 +
  MovesT.treeN_stable (fenced sibling; NOT consumed). ADJ (statement fence:
  new named row), statement-only.
- **IB-D6** fibering σ-uniqueness (†7u): two typed trees fibering at (N, f) have
  equal vt hence equal σ. Deps: D3, D4. Sketch: vtree_eq_of_fiberAt +
  typemult + Subtype.ext. R, ~15.
- **IB-D7** `bridgeCanonical` def (†7) + `canonical_pin` (both directions). Deps:
  D3, D6, A11. Sketch: dif unfolding; forward = choose + uniqueness; backward =
  ∃-intro. H, ~40.
- **IB-D8** `canonical_stable` from TransferRow. Deps: D7, D5, A12. Sketch: unpack
  witness at N, transfer fiber + thr through N ≤ N'; N = 0 vacuous. H, ~30.
- **IB-D9a** `bridgeTrueType` DEF only (†8; split of D9, post-Codex finding 1):
  the dite-choose display over ZpReads. Deps: E11 (zfType DEF unit — group E;
  the assembly E9 is NOT a dependency). R, ~8.
- **IB-D10** trueType N = 0 edge PROBE (†8 tail) — re-scoped and RE-ORDERED
  BEFORE D9b (post-Codex finding 6): attempt to settle `bridgeTrueType 0 = none`
  via the two-witness argument (X^n vs Eisenstein zfType distinctness), and
  re-verify by direct read that ZpReads is the ∀-lift predicate
  (DefsLedger.lean:686–689 — an ∃-read would sink D9b's uniqueness route).
  Corrected fallback if the edge is painful: record it OPEN + display the
  single-lift uniqueness derivation D9b consumes (the old "no consumer reads
  it" fallback is DELETED — it discharged nothing of lift_true's ∀-N burden).
  Deps: D9a. ADJ, ~20.
- **IB-D9b** uniqueness (†8u) + `lift_true` at ALL N (N = 0 included via the
  single-lift route — see the corrected †8 tail). Deps: D9a, D10 (gate), E8,
  E10. Sketch: dif + choose; uniqueness via ONE lift. H, ~25.
- **IB-D11** `bridgeClassifierSpec` assembly (canonical/trueType/stable/
  teichmuller) + `o3_teichmuller` rfl. Deps: D7, D8, D9a/D9b, D10. R, ~10.
- **IB-D12** `mass` def (†9) + `mass_ne_top`-style sanity + lvl edge (thr = 0).
  Deps: D3. R, ~15.
- **IB-D13** `thrSlice` from `slice_finite` row + `mem_slice_iff`/`slice_exhausts`.
  Deps: D3. Sketch: Set.Finite.toFinset spec. R, ~12.
- **IB-D14** `bridgeFibers : FiberSeries n p X` assembly. Deps: D11–D13. R, ~10.
- **IB-D15** `vt_real` from TransferRow (carrier realizability at lvl → any N ≥ thr,
  0 < N). Deps: D3, D5. Sketch: transfer from lvl T. R, ~15.
- **IB-D16** `vt_surj` (†5): realized V of typemult σ.1, thr ≤ N → carrier
  membership (transfer DOWN to lvl V) → preimage. Deps: D5. R, ~20.
- **IB-D17** `bridgeTreeOf`/`thr_le`/`treeOf_pin` via canonical_pin choice. Deps:
  D7. R, ~20.
- **IB-D18** `bridgeTreePin` assembly (pol/Tm/chart/chart_inj := chartWitness_inj/
  boxeq := A11/boxeq_digits/vt*/canonical_pin/treeOf_pin). Deps: D1–D17. R, ~15.
- **IB-D19** OPTIONAL ENRICHMENT (gated, Q1; re-scoped post-Codex finding 9 —
  the inventory has NO general-degree decoder, §2.4: decoders are per-menu):
  the agreement statement is PARAMETRIC in a SUPPLIED decoder —
  `omClassify_agree (dec : ClusterShape → Option FactorizationType)
     (hcov : (covering hypothesis: dec decodes OM.classify's range at (n, p)))
     : ∀ N f (hN : 0 < N), (bridgeCanonical N f).isSome →
       (agreement of dec ∘ OM.classify p n N (boxPolyEquiv f) with
        bridgeCanonical through sigmaToFT)`
  — decoder + covering proof are BINDERS, never an assumed global interface.
  The n = 2 sanity instance supplies dec from the built menu decoders with
  `UniformModelN2.cluster_coveringP` discharging hcov. ADJ, statement-only +
  n = 2 instance.
- **IB-D20/D21** OPTIONAL count_tie DISCHARGE CHAIN (gated, Q7): D20 = the
  instance-data pack (CellAssign/SiteLedger/TreeScaffold suppliers at (Tm, chart))
  as a typed structure; D21 = count_tie from MovesT.treeN + sibjc rows + D20.
  ADJ then H; NOT on the default path.

### Group E — ZpBridge (†11) — E0 AND E12 (the gates) RUN FIRST; E5–E7 GATED ON Q2
- **IB-E0** THE COUNTERMODEL (†11f), FIRST: compile h := X² − p²c at p = 3, c = a
  non-square unit (e.g. −1 when p ≡ 3 mod 4); prove IsLocalRing (AdjoinRoot h),
  ramIdx h = 1, resDeg h = 1, natDegree = 2; conclude ¬∃ (the zf_factor conjuncts
  3∧4 at g := h) — OR refute this blueprint's analysis with the exact Mathlib
  computation. Deliverable either way is a compiled artifact + adjudication
  memo. H, ~60 (own file, quarantine-adjacent; split E0a locality, E0b ramIdx,
  E0c resDeg, E0d assembly if needed).
- **IB-E1** ℤ_p[X] UFD wiring + `monicFactors` def + `monicFactors_prod` (†11a).
  Deps: —. H, ~40 — split E1a (def + factor monic), E1b (prod law).
- **IB-E2** factors irreducible in ℤ_p[X] + degree-positive. Deps: E1. R, ~15.
- **IB-E3** Gauss transfer (†11b) + `IsFractionRing ℤ_[p] ℚ_[p]` VERIFY. Deps: E2.
  H, ~30 (archaeology; if the instance is absent this unit's deliverable is the
  instance).
- **IB-E12** IP-1 BOUNDARY GATE (new unit, post-Codex finding 7) — RUNS BEFORE
  E4: a genuine falsification attempt at IP-1's universal (h monic +
  ℚ_p-irreducible ⇒ IsLocalRing (AdjoinRoot h)). Deliverables: (a) the compiled
  NEAR-MISS showing irreducibility is load-bearing — at odd p,
  `¬ IsLocalRing (AdjoinRoot (X² − 1 : ℤ_p[X]))` (CRT split: X−1, X+1 coprime
  since 2 is a unit ⇒ a nontrivial idempotent); (b) the stress check that E0's
  NON-MAXIMAL order X² − p²c still satisfies IP-1 (locality ≠ maximality —
  wired from E0a's proof, positive evidence kept SEPARATE from the gate); (c) a
  memo enumerating any candidate failure class (none expected: domain + finite
  over henselian local). If a genuine countermodel to IP-1 itself lands,
  E4 is blocked → adjudication. Deps: E0 (locality-machinery reuse). H, ~30.
- **IB-E4** IP-1 (†11c): IsLocalRing (AdjoinRoot h). Deps: E3, E12 (gate). H,
  ~40 — split E4a (henselian route probe: which Mathlib instances exist), E4b
  (proof; pre-approved internal split per Codex finding 11: E4b1 the
  finite-algebra-over-henselian-local product decomposition, E4b2 the
  domain-has-no-nontrivial-idempotents collapse; the norm/integrality fallback
  is its own re-scope event, not an inline continuation). This discharges the
  ZpBridge residue item (ii) of DefsLedger's docstring.
- **IB-E5** `zf_pos` (†11e) [GATED Q2 if the repair changes ramIdx]. Deps: E4.
  H, ~30.
- **IB-E6** pointwise e·f = deg (†11g) AT THE REPAIRED DEFS [GATED Q2]. Sketch:
  sum_ramification_inertia at the field's valuation ring; locality collapses the
  sum. H, ~40; ADJ first (the repair's exact statement).
- **IB-E7** `zf_factor` assembly [GATED Q2]. Deps: E1–E6. R, ~25.
- **IB-E8** `lift_exists` (†11d). Deps: —. R, ~25.
- **IB-E11** `zfType` DEF only (new unit, post-Codex finding 1 — split out of E9
  to break the D9/E9/E10 cycle): `zfType g := (monicFactors g).map (fun h =>
  (MovesT.ramIdx h, MovesT.resDeg h))`. Textually Q2-stable (it reads whatever
  ramIdx/resDeg the repair lands); its LAWS stay Q2-gated (E5–E7). Deps: E1.
  R, ~5.
- **IB-E10** the (†8u)-feeding lemma: for a monic lift g, zfType g determines σ
  uniquely (Subtype.ext transport). Deps: E11, E8. R, ~10.
- **IB-E9** `bridgeZpBridge` ASSEMBLY (zfType := E11; zf_pos := E5; zf_factor :=
  E7; lift_exists := E8; lift_true := D9b) + the zpDmass laws come free
  (DefsLedger). Deps: E5–E8, E11, D9b. R, ~10.
  EXECUTABLE ORDER (finding 1 resolved): E1 → E11 → D9a → D10 → (E8, E10) →
  D9b → E9 — no cycle.

### Group F — packs + assembly
- **IB-F1** `BridgePre` structure (hdet, hStateNe) — statement-only + the two
  warrant docstrings + ratification flags. ADJ.
- **IB-F2** `BridgeKernels` structure (†3.7 rows; exact dependency order fixed
  here) — statement-only; every row's docstring cites its note display + owner +
  fenced status. ADJ (this is the area's honesty ledger — Codex-audit magnet).
- **IB-F3** `bridgeCapstoneLedger` assembly. Deps: C4, C5, D14, D17, F2. R, ~20.
- **IB-F4** `mkUInstance` (G3). Deps: ALL construction units. R, ~20.
- **IB-F5** `theoremU_fired`. Deps: F4. R, ~15.
- **IB-F6** cl7_slice wiring (slice_bound row → UInstance field). Deps: F2. R, ~5.
- **IB-F7** OPTIONAL n = 2 enrichment: discharge env_tendsto at n = 2 from OM
  `hExhaustP` through the D19 agreement seam. ADJ; NOT on the default path.

### Group G — the thirteen slots (§3.8)
- **IB-G1** CInterface-carrier skeleton for the REL family (from the parked MovesR
  draft; statement-only). ADJ.
- **IB-G2** Slot_rel1 + Slot_rel2a/b/d/e formulations over G1. ADJ→H,
  statement-only (5 displayed Props; the p^N-torsion trap documented).
- **IB-G3** Slot_rel3 TYPING (§3.8 trap; re-scoped post-Codex finding 10): the
  REQUIRED deliverable is a CInterface-RELATIVE typed Prop `Slot_rel3 (CI : …)`
  over G1's carrier (the round-1 rejection was of a SELF-CONTAINED invention;
  carrier-relative is the untried route) + its G11a falsifier. The
  bare-parameter record is NO LONGER a pre-approved disposition — it fails G4,
  voids the G11a falsifier, and leaves the True-instantiation escape alive at
  G13. If the CI-relative typing ALSO fails faithfulness, the unit returns
  BLOCKED and the fallback shape is ESCALATED to the orchestrator (see
  REVISION 2 — not decidable at this altitude). ADJ→H.
- **IB-G4** Slot_rs0Lump. ADJ→H, statement-only.
- **IB-G5** Slot_trackRule (MovesX vocabulary; must be CONSISTENT with
  K7.track_restarts's (t3) — same Pop counters). ADJ→H.
- **IB-G6** Slot_dnLattice (K7.Dden-keyed). ADJ→H.
- **IB-G7** Slot_m1m5Echo (M1_bridge.md raw material). ADJ→H.
- **IB-G8** Slot_x1aDict (GMN-axiom-citing; faithfulness entry cross-ref). ADJ→H.
- **IB-G9** Slot_m4bConst (MovesV; Order0Perimeter fence respected). ADJ→H.
- **IB-G10** Slot_jcInvHist (complement of cl19_rep; no overlap — the two
  statements' conjunction must equal CL-19's display). ADJ→H.
- **IB-G11a** non-vacuity audit, REL family (rel1, rel2a/b/d/e, rel3) — split of
  G11 post-Codex finding 11: one compiled falsifier
  (`example : ¬ Slot_x degenerate…`) per slot. Deps: G2, G3. H, ~20.
- **IB-G11b** non-vacuity audit, mechanics family (rs0Lump, trackRule,
  dnLattice). Deps: G4, G5, G6. H, ~15.
- **IB-G11c** non-vacuity audit, seam family (m1m5Echo, x1aDict, m4bConst,
  jcInvHist). Deps: G7, G8, G9, G10. H, ~15.
- **IB-G12** closure manifest (identifier → decl table, grep-verified). R, doc.
- **IB-G13** `theoremU_bridged` (consume theoremU at the 13 Slot_* Props — ALL
  THIRTEEN typed, per G4; if G3 returns BLOCKED this unit WAITS on the
  escalated rel3 adjudication rather than shipping a 12-slot variant). Deps:
  G2–G10, G11a–c. R, ~15.

---------------------------------------------------------------------------
## 5. RISKS (countermodel-first ledger — each runs BEFORE its group's provers)

- **R1 (CRITICAL, blueprint-level finding): `ZpBridge` is likely UNINSTANTIABLE as
  typed.** zf_factor's conjuncts 3+4 force the (ramIdx, resDeg) aggregate to match
  factor degrees, but `MovesT.ramIdx/resDeg` read `Ideal.ramificationIdx/inertiaDeg`
  AT `AdjoinRoot h` — a possibly NON-MAXIMAL order. Countermodel §3.6 (†11f):
  h = X² − p²c, AdjoinRoot local with (ramIdx, resDeg) = (1,1) ≠ (1,2) = true
  invariants, aggregate {1} ≠ {2}. Unit IB-E0 (FIRST). If confirmed: Q2 repair
  (statement change on RATIFIED files) before ANY ZpBridge prover runs. If refuted:
  the memo shows which Mathlib convention saves it and E5–E7 un-gate.
- **R2: `vt_real` false over the naive all-VTrees carrier** — unrealizable junk
  trees of correct typemult. Mitigated by (†5) carrier design; residual check:
  IB-D3's docstring must display the failure mode; no countermodel unit needed
  once realizability is IN the carrier (vt_real reduces to the transfer row).
  If a prover finds even the carrier version false → the TransferRow is
  mis-scoped (report, adjudication).
- **R3: full RegP transport is FALSE** (junk-block dets at wild pools; MOVES
  12208–12210). Pre-refuted by note read; IB-B15a/B15b are scoped PARTIAL from
  birth (typed loci via IB-B17) and
  IB-B16 records the gap. Failure mode guarded: a prover "fixing" B15a/b by weakening
  RegP would violate the statement fence — RegP is Defs.lean:209, untouchable.
- **R4: the checksum transport's cast chain** (†10b): rsh_interp equates ℚ-cast-ℝ
  values; recovering the ℚ-level 1 needs Rat.cast injectivity — if the chain's ℝ
  detour blocks, the repair is an added ℚ-level field… NO: derive
  `(evalAt p Σ : ℚ) = 1` from `((… : ℚ) : ℝ) = 1` by exact_mod_cast — safe. Risk
  retired at blueprint time; noted for the prover.
- **R5: sigma-uniqueness edge at N = 0 for trueType** (†8): the "no σ at N = 0"
  proof needs two lifts with distinct types — needs n ≥ 2 (hn binder) and an
  explicit pair (X^n vs Eisenstein). REVISED post-Codex finding 6: IB-D10 (the
  probe) now runs BEFORE the prover D9b; the old consumer-audit fallback is
  DELETED; the corrected fallback is record-the-edge-open + display the
  single-lift uniqueness D9b consumes (sound at all N because ZpReads is the
  ∀-lift predicate — DefsLedger.lean:686–689, verified 2026-07-30).
- **R6: slice_finite could be false even over the realizable carrier** if
  infinitely many realizable trees share thr ≤ N (they'd have distinct fibers in a
  finite box only if fibers are nonempty and disjoint — realizability gives
  nonempty; disjointness across DISTINCT trees is vtree_eq_of_fiberAt's
  contrapositive ⇒ ≤ p^{nN} trees: **slice_finite may be PROVABLE outright!**).
  Pre-prover probe unit (add to IB-D13): attempt the pigeonhole proof
  (inj Tree → nonempty disjoint fibers → card ≤ box) BEFORE wiring the row; if it
  lands, slice_finite LEAVES BridgeKernels and slice_bound's row shrinks to the
  p-uniformity claim. Upside risk — worth one fable-day.
- **R7: SP8 CanTreeModel may be n = 2-specific** (IB-D1). If so, the general Tm is
  a designer round (MovesD owns TreeModel; the constructor may need the MovesD
  policy machinery at general n) — schedule slack; D-group statements are Tm-
  parametric so only D1 blocks.
- **R8: multiset attach-map lemmas (A2/A5)** are the classic Lean quagmire;
  pre-approved fallback: restate via `Multiset.pmap` or induction on the
  underlying list with Quot.induction. Bounded-repair rule applies (≤3 attempts,
  then re-sketch).
- **R9: the thirteen-slot formulations repeating the MovesR failure** (round-1:
  15/6 → parked). Mitigation baked in: G-units are statement-only, CInterface-
  parametric, each with the closure manifest + non-vacuity falsifier + Codex
  audit BEFORE any consumer lands; rel3 explicitly allowed to remain bare (G3).

## 6. ORCHESTRATOR QUESTIONS (decisions this blueprint cannot make)

- **Q1 (interface, binds D-group):** ratify ARCHITECTURE B — `canonical` defined
  as the VTree-fibering verdict (canonical_pin definitional, OM engine tied in via
  optional agreement units D19/F7) — over A (OM classify + decode with
  canonical_pin as a permanent open row). Recommendation: B (§3.4 rationale).
  Affects the OM-tie area if one exists.
- **Q2 (statement fence, blocks E5–E7):** upon IB-E0 confirming R1: sign off the
  repair path for `MovesT.ramIdx/resDeg` (re-point to the integral closure /
  valuation-ring invariants) + the corresponding `ZpBridge.zf_factor` re-read.
  Both files are RATIFIED; the GOLF note already queues the pointwise retype.
  Alternatives: (a) repair defs (recommended — fixes the semantics everywhere),
  (b) rescope zf_factor to the maximal-order locus (weakens the ℤ_p clause of
  theoremU — bad), (c) keep bridge uninstantiated (kills the area).
- **Q3 (named premises, F1):** ratify the two BridgePre rows — `hdet`
  (symbolic DetHyp; = (r1)'s symbolic face, derivable from (REG-p) at any one
  prime) and `hStateNe` (pending IB-B2's derivation attempt). Both are
  statement-gaining-named-hypothesis events under the campaign's scoping
  authority; flagged here for ratification.
- **Q4 (area boundary):** confirm that UCarriers/KernelCarriers/Cl7Kernel/
  UpstreamTyped construction (incl. the n = 2 real pack over N2Shape) belongs to
  the sibling S/X-area blueprints, and that `SolveData` construction (IB-C1) is
  OWNED HERE. Also: who owns `KT : UpstreamTyped`'s discharge — it is not
  consumed by mkUInstance but is a theoremU binder.
- **Q5 (sequencing):** should the thirteen-slot formulations (G-group) wait for
  wave-D / MovesR unparking (the REL family's carrier), or proceed now with the
  CInterface-parametric shape? Recommendation: proceed statement-only now (they
  gate nothing on the construction path), Codex-audit before any proof units.
- **Q6 (row ownership):** cl6 (PolyGeomLaws), cl11_ksub (KsubM1C1T), cl19_rep —
  carried as BridgeKernels rows here, but they are S-corpus-shaped claims; if the
  S-area can PROVE any at the real pack (cl11_ksub is a finite roster check at
  n = 2), the row moves out of the pack. Decide per-row after the S-area
  blueprint lands.
- **Q7 (scope):** pursue the count_tie discharge chain (IB-D20/D21 — needs
  HC-2-flavored CellAssign/SiteLedger/TreeScaffold instance data) THIS campaign,
  or keep count_tie a named row? Recommendation: keep the row; spec D20's
  structure statement-only so wave-D can land it.
- **Q8 (unit budget):** IB-E0's outcome may add 2–4 repair units (the def
  re-point + downstream re-proof of UnramifiedOfDeg/HenLift consumers in MovesT)
  — pre-authorize the overflow or re-scope.

## 7. EXECUTION NOTES (for the prover fleet)

Wave order within the area: [E0, E12, B2, D1, D2, R6-probe] (adjudication/probe
front-runners; D10 runs at the head of its D-subchain, before D9b) → A-group ∥
B-group (internal order: B9 → B8; B11/B12/B13 → B10; B17 → B15a/B15b) ∥
C-group → D-group → E-group (post-Q2; E11 is def-only and may land early) →
F-group → G-group (anytime, statement-only). Every unit prompt carries: the
statement-fence rule, the 64k staged-write discipline, `lake build` (never
`lake env lean`) for green records, `#print axioms` per landed theorem
(Lean-core expected everywhere in this area — no declared axiom is consumed on
the construction path), and the standing rule that comments are unverified claims.
File-level acceptance: BridgeMk.lean compiles with mkUInstance + theoremU_fired
sorry-free, footprint Lean-core; the packs' rows are the ONLY hypotheses beyond
theoremU's own; MANIFEST.json gains a BRIDGE section mirroring §4's ids.

---------------------------------------------------------------------------
## REVISION 2 (2026-07-30, post-Codex) — finding-by-finding disposition

Codex adversarial review: REVISE (0 CRITICAL / 10 GAP + 1 NOTE). All findings
verified against the as-built sources before disposition (RegData/RegP
Defs.lean:124/209; ZpReads/ZpBridge DefsLedger.lean:686–735; RegPin
DefsLedger.lean:479ff; allActivePools/pools_e0 MovesS/Interfaces.lean:138).
Unit ids stable except where logged; new ids: B15a, B15b, B17, C3a, C3b, D9a,
D9b, E11, E12, G11a, G11b, G11c (retired as single units: B15, C3, D9, G11).
Default-path unit count 84 → 92.

1. APPLIED (circular D9/E9/E10 dependency): E9 was carrying both the zfType DEF
   and the ZpBridge ASSEMBLY. Split: new IB-E11 = zfType def (deps E1 only);
   IB-E10 re-keyed to deps E11+E8; IB-D9 split into D9a (trueType def, deps
   E11) and D9b (lift_true, deps D9a/D10/E8/E10); IB-E9 = assembly only (deps
   E5–E8, E11, D9b). Executable order displayed in Group E: E1 → E11 → D9a →
   D10 → (E8, E10) → D9b → E9.
2. APPLIED (bridgeRegData missing 2 ≤ n): `hn : 2 ≤ n` threaded into the §3.3
   display signature (feeds `instNe : Nonempty Block`, Defs.lean:136 — at
   n = 0 Block is empty and hne vacuous, exactly as the finding says); supplied
   at use sites by mkUInstance's EXISTING binder — no new premise, no fence
   event. The undefined placeholder name `BlockStatesNe C` in the old display
   was also replaced by the actual hStateNe statement.
3. APPLIED (record with postponed fields impossible): IB-B9 re-scoped to
   STANDALONE defs `bridgeBsplit`/`bridgeBetaLeg` and re-ordered BEFORE IB-B8;
   IB-B8 now assembles the FULL record in one literal, deps + B9. Assembly-order
   note added to §3.3.
4. APPLIED (bridgeRegPin assembled before its field proofs): IB-B11/B12/B13
   re-scoped to STANDALONE lemmas over bridgeRegData; IB-B10 re-ordered LAST
   with deps B5, B6, B8, B9, B11, B12, B13 (the missing B9 dep the finding
   flagged is now explicit).
5. APPLIED (the `zp` catch-all row hid conditionality, defeating G1/G2): the
   row is DELETED from BridgeKernels (§3.7). Group E proves all five ZpBridge
   fields outright (zfType E11 / zf_pos E5 / zf_factor E6–E7 / lift_exists E8 /
   lift_true D9b), post-Q2. A stall on any specific law returns a blocked-report
   and adding it as a NAMED typed row is an orchestrator adjudication (fence
   event: campaign ledger + digest) — pre-flagged, not decided here.
6. APPLIED WITH PARTIAL REBUTTAL (D10 after its prover): the ordering violation
   is real and fixed — D10 now runs BEFORE D9b (D9 split makes this possible:
   the def D9a precedes the probe). The finding's second claim ("the fallback
   does not validate D9's all-N lift_true") is CORRECT against the OLD
   consumer-audit fallback, which is deleted; but the N = 0 edge itself is NOT
   load-bearing for lift_true: ZpReads is the ∀-lift predicate
   (DefsLedger.lean:686–689, verified today), so (†8u)'s uniqueness needs only
   ONE lift, which lift_exists supplies at every N including 0 — lift_true's
   N = 0 instance holds regardless of whether "trueType 0 = none" is settled.
   Corrected fallback recorded in (†8)/R5/D10.
7. APPLIED (no countermodel gate for IP-1): new unit IB-E12, runs before E4 —
   compiled boundary near-miss ¬IsLocalRing (AdjoinRoot (X² − 1)) at odd p
   (irreducibility load-bearing), E0's non-maximal order as separate positive
   stress, failure-class memo. E4 deps gain E12.
8. APPLIED (B15 had no typed statement): new vocabulary unit IB-B17 (`RegPAt`
   clause decomposition of Defs.lean:209 + `bridgeActiveLocus` := Pool filtered
   by MovesS.allActivePools — pools_e0's locus, Interfaces.lean:138); B15 split
   into B15a ((r2) on the active locus) and B15b ((r1) at chain-covered pairs
   via UCarriers.cl1 + the K_pin submatrix-det transport), each returning a
   TYPED residual. §3.3 (†4e) retyped accordingly.
9. APPLIED (D19 assumed a nonexistent general decoder): D19's agreement
   statement re-scoped PARAMETRIC in a supplied decoder + covering-proof binder;
   the n = 2 instance discharges them from the built menus +
   UniformModelN2.cluster_coveringP. No general ClusterShape decoder is assumed
   anywhere.
10. APPLIED + ESCALATED (rel3 bare-parameter disposition fails G4): IB-G3
    re-scoped — the CInterface-relative typed Prop is now the REQUIRED
    deliverable (the round-1 rejection was of a self-contained invention;
    carrier-relative is untried) with a G11a falsifier; the bare-parameter
    record is DEMOTED from pre-approved disposition to BLOCKED-outcome.
    ESCALATION (not decided here): if the CI-relative typing also fails
    faithfulness, the fallback shape of theoremU_bridged (12 slots instantiated
    + rel3 as a visible named binder, vs. G4's all-thirteen requirement) is a
    goal-level decision not covered by Q5 — orchestrator adjudication required
    before G13 lands in that branch.
11. APPLIED (oversized units): C3 → C3a (OKat→num/den archaeology) + C3b
    (infinite-roots); B15 → B17 + B15a + B15b (see 8); G11 → G11a/G11b/G11c
    (REL / mechanics / seam families); E4 keeps E4a/E4b with a pre-approved
    internal split of E4b (product decomposition / idempotent collapse) and the
    norm/integrality fallback marked as its own re-scope event.

Editorial (no finding): the (†8u) cross-ref typo "(†10d)" corrected to
"(†11d)"; §5 R3 and §7 wave order updated to the new ids; §4 header recounted.

ESCALATIONS QUEUED FOR THE ORCHESTRATOR (from this revision): (a) the rel3
fallback shape (finding 10 above); (b) pre-flag: any Group-E stall converting a
ZpBridge law into a new NAMED kernel row is a fence event needing adjudication
(finding 5 above). No finding contradicted an existing adjudication (Q1–Q8
stand); no new statement-fence event was surfaced (finding 2's hn is an
existing binder; all other fixes are blueprint-internal).

---------------------------------------------------------------------------
## DESIGN ADDENDUM D-TM (2026-07-30) — the general TreeModel construction
### (MovesD designer round; resolves R7 / the IB-D1 finding)

CHARGE (BridgeD1_treeModelWire.lean, IB-D1 verdict): "no (n, N)-generic real
(pol, Tm) exists in-corpus — the only concrete `MovesD.TreeModel`s are n = 2
toys over `polTriv`, with toy-semantic mem/child; the general constructor is a
MovesD designer round". This addendum IS that round: the construction at unit
granularity + the landed E-phase skeleton `lean/LeanUrat/MovesD/TreeCan.lean`
(new module, builds green, 13 honest sorries keyed to the unit ids below).
UNIT IDS: IB-D20/D21 stay RESERVED for the count_tie discharge chain (§4, Q7 —
no collision); the designer round is IB-D22..IB-D30.

### D-TM.1 The construction (three factors, each residue NAMED)

(†12) **THE CANONICAL DECODE** `canDec p n N : MovesD.Box p (n·N) → ℤ_p[X]`,
      `X^n + Σ_{i<n} C(canCoeff i)·X^i` with `canCoeff i = Σ_{k<N} digit(i·N+k)·p^k`
      — slot i·N + k carries coefficient i's k-th base-p digit: the
      COEFFICIENT-MAJOR `digitIdx` layout ((†3), DefsLedger.lean:289), so the
      level-0 slot chart `canChart n N hN : i ↦ i·N` IS `chartWitness`'s shape and
      `canDec_red` ties the mod-p reduction to `MovesT.redPoly (canChart …) x`
      (stated import-free in MovesD; the redPoly re-key is one line at the D27
      wire). CONSEQUENCE: IB-D2's chart-semantics question is answered BY
      CONSTRUCTION — the model reads coefficient i's digits at slots digitIdx i k
      because `canDec` is DEFINED that way. Laws: `canDec_monic`,
      `canDec_natDegree` (unconditional — n = 0 degenerates to the monic 1),
      `canDec_red` (0 < N). Same layout as `lift_exists`'s display (†11d).

(†13) **T_can MEMBERSHIP** `memCan n pol dec H x :=
      MovesJ.ReadsOf p F n (dec x) H ∧ Realizable H ∧ pol.IsCanonPres H`.
      The clause roster (THE central design decision, flagged Q9):
      * `ReadsOf` (HC2/Defs:285, the f-explicit Wall-A run predicate) supplies
        Monic/degree-n of the lift, `HistoryCoherent` (its 3rd conjunct), and the
        per-read development/`SideReads` chain — "H is a run of the classifier on
        dec x".
      * `Realizable` (transition admissibility) + `pol.IsCanonPres` (L1 canonical
        lifts + canonical residue roots) make the tree the CANONICAL-presentation
        tree — matching `PrefSet`'s roster minus `MatchesHist` (shape-keying is
        Pref's job, not the tree's) and minus `InBox`.
      * `InBox` is NOT baked in: IB-D25a PROBES its derivation from the run's
        root development on the degree-n lift; a blocked probe re-adjudicates the
        roster (add the conjunct) — derivation-over-fiat, per countermodel-first.
      * `mem none := True` (the full box) — L2's root law, forced by `root_mem`.

(†14) **THE MODEL** `canTreeModel p F n N m pol dec : TreeModel p F n N m pol`:
      mem = (†13) on some-chains, True at none; child DEFINED as run-extension —
      `child none ν x := ∃ h : ν.species = root, memCan (rootHist ν h) x`,
      `child (some H) ν x := ∃ hν : ν.species ≠ root, memCan (H.snoc ν hν) x`.
      Law provability (all checked at design time):
      * `root_mem` — definitional (match reduces to True).
      * `mem_single` — the field's `⟨[ν], h1.1, h1.2⟩` equals `rootHist ν h` by
        DEFINITIONAL proof irrelevance of History's Prop fields; h1.2-at-0 gives
        the species leg. (IB-D24a)
      * `mem_snoc` — backward: proof-irrelevant projection of the ∃; forward: the
        ONE load-bearing law `memCan_snoc_mono` (IB-D23). (IB-D24b)
      * `mem_realizable` — projection: HistoryCoherent off ReadsOf's 3rd conjunct
        + the two carried conjuncts. (IB-D24c)
      SEAM REVERSAL (design consequence, record for the W4-1 ledger row): at this
      model the all-and-only face is DEFINITIONAL — `canTreeModel_child_some_iff`
      is the `WallAReconciled`-genre display with `dec := canDec` — while the
      COVERING duties (`W41ChildCover`/`ChildCover`, the (c2) row) become genuine
      ReadsOf-TOTALITY claims (a window-opening x admits a realized root run),
      owner HC-2/D4R.0-K exactly as the ledger already assigns. Nothing moves
      ownership; the definitional side just stops being open.

(†15) **THE POL-PIN POLICY** `canPolicy p : CanonPolicy p (ZMod p)` +
      `canPolicy_pin p : OffsetPPin (canPolicy p)` — the note's ONE (S6b)
      OFFSET-P-LIFT rule (note 4646–4651; W4-5). HONEST DATA SORRIES, owner
      HC-1/§B2-DEF (PolPin.lean: the (S6b′) formula needs the lower-stage
      realizer vocabulary MovesC/MovesD do not export). ACCEPTANCE RULE: a filled
      `canPolicy` WITHOUT `canPolicy_pin` is not acceptance — the pin is what
      excludes the under-typed instantiations (`not_realizes_bare_ne_zero`, the
      bypass kills). The model being (pol, dec)-PARAMETRIC confines this residue:
      every policy-quantified MovesT consumer is unaffected; only canonicity-
      demanding consumers block.

(†16) **THE WIRE** (IB-D27, a MovesU edit — outside the designer round's
      new-modules-only scope): `bridgePol p := canPolicy p`;
      `bridgeTm p n N := canTreeModelN p n N (canPolicy p)`
      (`canTreeModelN` = the m := n·N, dec := canDec specialization, landed).
      This kills BridgeD1's `bridgeTm` sorry outright and re-keys its `bridgePol`
      sorry to the pin-carrying (†15) pair — the residual conditionality of the
      whole Tm chain is then EXACTLY {canPolicy, canPolicy_pin} + the IB-D22/23/24
      unit proofs, each named.

### D-TM.2 Unit split (IB-D22..IB-D30; skeleton statements landed in TreeCan.lean)

- **IB-D22** `canChart`/`canCoeff`/`canDec` defs [LANDED, real] + `canDec_monic`/
  `canDec_natDegree`/`canDec_red` [sorried]. Deps: —. Sketch: leading-coeff of
  X^n + (deg < n) sum; map through C/X; `PadicInt.toZMod` kills p^k (k ≥ 1) and
  roundtrips digit 0 (`ZMod.natCast_val`). R, ~30.
- **IB-D23** `memCan_snoc_mono` [sorried]. Deps: —. Sketch: snoc-nodes =
  nodes ++ [ν]; `Realizable`/`IsCanonPres` restrict via `getElem_append_left`;
  `HistoryCoherent` restricts with `strFrame` take-stability; ReadsOf's per-read
  witnesses (B, Nd, Φnext) REUSED VERBATIM — truncation only vacates the
  `∀ hi1 : i+1 < len` Φnext guard at the new last read. COUNTERMODEL GATE: none
  (restriction + reuse); a non-prefix-stable clause ⇒ BLOCKED report ⇒
  adjudicated fallback = explicit prefix-closure scoping of memCan (fence event,
  Q9 — memCan is NEW, no ratified file changes). H, ~40.
- **IB-D24** the three field discharges (D24a mem_single / D24b mem_snoc /
  D24c mem_realizable) [sorried in the landed `canTreeModel`]. Deps: D23.
  Sketch: (†14)'s roster; D24a needs only `hist_ext`-style proof irrelevance
  (T1a's private lemma — hoist or replay). R, ~30 total.
- **IB-D25** (a) `canTreeModel_inBox` PROBE [sorried]: derive `InBoxOfMem`'s
  statement from the run's root development (`SideReads` root clause on the
  degree-n lift); BLOCKED ⇒ Q9 re-adjudication (add InBox to the roster), never
  a weakened statement. (b) display gates [sorried]: `child_some_iff` /
  `child_root_iff` / `child_none_not_root` (+ `mem_some_iff`, ALREADY PROVED
  `Iff.rfl` at the skeleton — the defeq pin holds). ADJ/R, ~25.
- **IB-D26** `canPolicy` + `canPolicy_pin` [sorried data, owner HC-1] — see
  (†15). NOT dischargeable this campaign; tracked as the named policy residue.
  The unit's only in-campaign duty: keep the pair adjacent so no consumer takes
  the policy without the pin.
- **IB-D27** the MovesU wire (†16): re-point `bridgePol`/`bridgeTm` in
  BridgeD1_treeModelWire.lean + the one-line `canDec_red` ↔ `redPoly` re-key.
  Deps: D22, D24, D26 (data only — the wire compiles against the sorried defs).
  R, ~10.
- **IB-D28** LAYOUT ADJUDICATION (memo unit): the corpus carries TWO digit
  layouts — coefficient-major `digitIdx` (slot i·N+k; (†3), chartWitness,
  boxeq_digits, and now canDec) vs level-major `MovesT.levelIdx` (level(c) =
  ⌊c/n⌋+1; MovesT/Defs:1250 — consumed by `CapIrrLaw` and by `TreeNStable`'s
  "the level-<N block is the first n·N coordinates" reading). Under
  coefficient-major, the level-<N block is NOT an initial segment. Deliverable:
  consumer enumeration + either (i) confirmation that every levelIdx consumer is
  chart-mediated at the bridge (expected: CapIrrLaw/TreeNStable are open rows
  whose bridge instances are stated through TransferRow, not raw levelIdx), or
  (ii) the reconciliation permutation of Fin (n·N) as a typed statement for
  adjudication (Q10). ADJ, memo+~10.
- **IB-D29** `CanTreeInhab` NON-VACUITY ROW (statement-only): ∃ x H,
  `(canTreeModelN p n N pol).mem (some H) x` at a designated small instance —
  needs a genuine ReadsOf run witness (HC2 run vocabulary, `keys_exist_of_run`
  genre). OWNER HC-2. This is the wave-2-doctrine gate for every D-group unit
  that consumes `Realizes` at the bridge model: without it the model could be
  some-empty and the D-group vacuous — the row makes that visible, not silent.
  ADJ, statement-only.
- **IB-D30** the Wall-A display `canTreeModel_child_some_iff` [sorried]: child =
  run-extension, the `WallAReconciled` face definitional at the canonical model.
  Deps: D24 (proof-irrelevance collapse only). R, ~10.

### D-TM.3 Risk-ledger updates

- **R7 → RESOLVED-BY-DESIGN**: the general constructor exists (landed skeleton);
  residual = the IB-D22/23/24 proofs + the NAMED policy pair (IB-D26, HC-1).
  IB-D1's `bridgeTm` data sorry dies at the D27 wire.
- **R10 (new)**: a `ReadsOf` clause could fail prefix-stability ⇒ IB-D23 BLOCKED
  ⇒ mem_snoc unprovable as constructed. Design-time check says no (restriction +
  witness reuse — D-TM.2's sketch); fallback pre-scoped: prefix-closure guard on
  memCan (fence event on a NEW def only).
- **R11 (new)**: the two-layout tension (IB-D28). Bites only levelIdx-keyed open
  rows at the bridge model; no construction-path unit reads levelIdx.
- **R12 (new)**: policy-sorry leakage — a prover "discharging" a canonicity-
  demanding unit by unfolding the sorried `canPolicy` would be vacuous-by-sorry.
  Guard: units needing THE policy must take `OffsetPPin pol` as a BINDER (the
  W4-5 consumption pattern, `CD_canonical`'s shape), never unfold `canPolicy`.

### D-TM.4 Orchestrator questions (this addendum's fence events)

- **Q9 (memCan roster — THE design ratification):** ratify (†13): mem none :=
  True; some-clause = ReadsOf(dec x) ∧ Realizable ∧ IsCanonPres; InBox by
  derivation probe (IB-D25a) with add-the-conjunct as the pre-approved blocked
  fallback; MatchesHist deliberately absent (shape-keying stays in PrefSet).
- **Q10 (layout):** ratify coefficient-major `digitIdx` as THE bridge layout
  (already forced by the ratified TreePin.boxeq_digits + chartWitness); IB-D28's
  memo to confirm no ratified levelIdx consumer breaks at the bridge model.
- **Q11 (policy placement):** the (†15) sorries live in MovesD/TreeCan.lean
  (adjacent to their pin obligation); when HC-1 exports the (S6b′) realizer
  vocabulary, does the filled policy land HERE or in an HC1 module re-exported?
  Also: does the D27 wire land NOW (against sorried defs — compiles, kills the
  bridgeTm sorry, keeps the policy pair visible) or after D22–D24 prove out?
  Recommendation: wire now — conditionality strictly shrinks and stays named.

FILE MAP: `lean/LeanUrat/MovesD/TreeCan.lean` (NEW module; `lake build
LeanUrat.MovesD.TreeCan` green 2026-07-30, "Build completed successfully
(8569 jobs)", 13 sorries = the census in its header — 11 declarations).
No existing file touched; MovesD/MANIFEST.json entry + the D27 wire are
follow-on edits (Q11).


---------------------------------------------------------------------------
## DESIGN ADDENDUM D-SC (2026-07-31) — the REL SITE-CARRIER LAYER
### (the thirteen-slot carrier design; resolves the SlotsG2/SlotsG3 BLOCKED escalations)

CHARGE (the compiled failure records, verbatim dispositions): SlotsG2_relFamily.lean
— "the site-carrier layer (or a ratified alternative closure) is an orchestrator
adjudication — surfaced, never improvised"; SlotsG3_rel3.lean — "the genuinely
missing ingredient is the [4]-side SQ.0–SQ.2 display carriers (unbuilt; their Lean
shape is exactly what must not be invented here)".  This addendum IS the dispatched
design round: the minimal structure family (sites, condMass carriers, Θ transports,
table/consumed-display carriers) that states each blocked slot faithfully, at unit
granularity, with the landed E-phase skeletons (new files only; the G2/G3 BLOCKED
records and every ratified file UNTOUCHED — 2026-07-31 boundary decision honored).
GROUND TRUTH read for this round: the G2/G3 records; the U10 docstring; §3.8 +
REVISION 2 finding 10; MOVES_2026-07-24.md 9421–9660 (REL.2 (a)–(e), (SIB-Oδ),
REL.3), 9293–9330 (the obligation ledger); the parked draft
MOVESR_LEAN_BLUEPRINT_2026-07-28.md (Setting/SettingsFamily/REL2a1–a6/REL2d/REL2e
with CF1/CF10–CF14 folded); the landed SlotsG1/G2/G4–G10 as-built.

### D-SC.1 The three design principles (each compiled-lesson-backed)

* **P1 — SUPPLIED CARRIERS, NEVER CLOSED QUANTIFIERS.** The G2 record proves both
  closures of site data inside a CI-only Prop fail (∀ false at every CI via the
  junk Dirac site; ∃ True-instantiable via the identity site).  Resolution: site,
  data pack, target interface, and exports are PARAMETERS of the slot Props —
  the same epistemic footing as theoremU's own `C : UCarriers n`.  The junk site
  converts from ∀-closure killer into the IB-G19a falsifier witness; the identity
  site converts from ∃-escape into the caller's VISIBLE liability at a named
  binder (falsifiable, recorded — the supplied-carrier discipline the capstone
  already lives under).
* **P2 — LAW/DATA SPLIT.** The parked draft carried note obligations as law
  FIELDS (its consumers hypothesized Props directly).  Fed to theoremU's slot
  parameters, law-fields collapse each slot to `Nonempty (pack)` — the ∃-trap
  again.  Resolution: carriers carry DATA + structural wellformedness only
  (nonemptiness, event-algebra closure, measure axioms — BoxVol's G1 precedent);
  every note OBLIGATION is a slot-Prop conjunct.  Consequence, by design:
  degenerate packs are constructible (falsifiers live), and NO consumer may take
  a raw pack without its law slot (the D-TM R12 policy-without-pin guard,
  restated here as R15).
* **P3 — DERIVED, NOT FREE (the rel3 repair).** The G3 record's junk-pack
  countermodels rode the display pack's FREE value/event fields.  Resolution:
  `ConsumedDisplayPack` carries ONLY the consumption KEY (site, first index,
  prescribed subtree); the leg's value is DERIVED as the site's β-table read
  and its event as the realization event — the q ↦ q^δ substitution is excluded
  STRUCTURALLY (no field to ride in), which is the note's own fixed discipline
  ("an input theorem about vol_{O_δ}, never the formal substitution").  Round 1's
  sin (inventing SQ.0–SQ.2 content) is not committed: the pack types only the
  keying the note fixes; its faithful POPULATION is [4]'s wave-D drafting event.

### D-SC.2 The structure family (landed E-phase skeletons; all builds green)

(†17) **`RelSite p` / `RelSiteFamily p`** (SlotsG14_relSite.lean, real, 0 sorry):
      the parked `Setting`/`SettingsFamily` re-homed (R-5), p phantom (R-6),
      realized-measure laws kept as wellformedness (R-7), CF1's `mem_pos` family
      scope (R-8); derived `δabs`/`dRel`/`βarg` (ABSOLUTE indices, (e2) pinned).
(†18) **the seven per-site data packs + `SiteData` bundle** (SlotsG15_siteData.lean,
      real, 0 sorry): `SiteDom` (a1-data), `SiteEmbed` (a3-data), `SiteTheta`
      (a4 = Θ itself), `SiteFrames` (a5-data, target transports; R-10 thinning),
      `SiteDict` (a6-data, per-read field readers + `resDict`), `SiteTrees`
      (d-data: square vertices, `nodeCorr`, word/read/verdict readers, `posOf`,
      `TgtSub`/`subtreeCorr`/`TgtRealizes`), `SiteBeta` (e-data: `stateDict`,
      read rosters, [3]'s β table in [3]'s keying, `entryFirst`).  CF13/CF14
      carried: `tableConv`/`consumed` are NOT fields (R-11).
(†19) **the four sited law slots** (SlotsG16_sitedLaws.lean, 4 E-phase sorries):
      `SitedSlot_rel2a (S) (SD)`, `SitedSlot_rel2b (S) (SD) (CI)`,
      `SitedSlot_rel2d (S) (SD)`, `SitedSlot_rel2e (S) (SD) (tableConv)
      (consumed) (CI)` — full displayed targets in the file header, REL.1
      conditionality displayed per site as a `Slot_rel1 CI` conjunct (the
      draft's `_linked`/FF6 shape); target vol = the supplied CI's OWN
      cylinder-pinned BoxVol.
(†20) **`RelAssignment` + `ConsumedDisplayPack` + `SitedSlot_rel3`**
      (SlotsG17_rel3Display.lean, 1 E-phase sorry): the per-family data/target/
      export assignment; the [4]-display pack per P3; the rel3 target =
      per-leg certification + keying (`first l = entryFirst`, `tableConv`) +
      consumption tie (`presc l ∈ consumed`).  Empty-pack caveat recorded
      (vacuous-faithfully until [4] drafts; falsifier = one-leg junk pack).
(†21) **`RelCarrierPack` + the six closure rows** (SlotsG18_relPack.lean, 6
      E-phase sorries): the p-uniform bundle (Sp p-free per EQ-1; per-prime
      AD/fam/assign/display) and `RelRow_rel1/_rel2a/_rel2b/_rel2d/_rel2e/_rel3`
      — the Props IB-G13′ feeds to theoremU's six REL parameters; ∀-closures
      range over the SUPPLIED family only.
(†22) **the elaboration probe** (SlotsG19b_targetElab.lean, 0 sorry): every †19/†20
      displayed target compiled as an anonymous `example : Prop` — the
      well-typedness half of the hygiene gate, consumable by nothing.

### D-SC.3 Per-slot design table (all thirteen)

| slot | carriers (fields) | faithful statement | falsifier (non-vacuity) | countermodel gate | deps | difficulty |
|---|---|---|---|---|---|---|
| rel1 | `CInterface` (G1: counting pack, jets, towers, frames, pins, ZC, LST/TYP carriers, blockEdge) | FILLED (G2 `Slot_rel1`: §A/§B1/§B2-DEF/ThmC(a)(b)/C.0.5/C.1/C.1.5/LST/TYP/DOM, r-F3-1/2/3) | degenerate CI breaking C.1 pricing or the r-F3-2 span (G11a, pending) | p^N-torsion trap — passed (r-F3-1) | G1 | done; audit pending |
| rel2b | `RelSite`+`SiteDom`+`SiteTheta`+CI_tgt | `Slot_rel1 CI` ∧ (0<μ(Σ_c) → Θ-pullbacks in the algebra ∧ condMass = CI.C.V.vol) | the G2 Dirac-site countermodel INVERTED (two disjoint cylinders vs a two-valued condMass) | G19b (elab landed; hygiene pending) | G14,G15,G1,G2 | fill R (~10) |
| rel2a | + `SiteEmbed`,`SiteFrames`,`SiteDict` | (a1)∧(a2)∧(a3 teich_pin)∧(a5 anchors+commutation)∧(a6 dictionary laws) | finite `freeCoords` (a1 fails); letter-collapsing `readDict` (a6 fails) | G19b | G14,G15 | fill R (~25) |
| rel2d | + `SiteTrees` | square ∧ word/read/verdict preservation ∧ posOf_letter (CF12) | constant `tgtTcan` vs non-constant `nodeCorr ∘ ambTcan` | G19b | G14,G15 | fill R (~12) |
| rel2e | + `SiteBeta`; params `tableConv`,`consumed` ([3]) | (e1)∧(e4 tableConv only, CF13)∧(e5)∧(e3 MASS=ENTRY at CI vol, `Slot_rel1` displayed) | β ≡ 2 (vol ≤ 1); two-element `consumed` | G19b | G14,G15,G1,G2 | fill R (~15) |
| rel3 | `RelSiteFamily`+`RelAssignment`+`ConsumedDisplayPack` | per-leg: certification (DERIVED value/event) ∧ keying ∧ consumption tie | one-leg junk pack with β ≡ 2 | G19b + empty-pack caveat | G14–G17 | fill R (~15); residue = [4] population (E-3) |
| rs0Lump | `UCarriers` (built; stratum = `verdictImage` pin) | FILLED (G4) | non-lumpable 2-state row (G11b) | — | — | done |
| trackRule | `KernelCarriers`+`Cl7Kernel` (∃-bound keyRec/trackOf, K7.L-priced) | FILLED (G5) | branch with > K7.L non-designated siblings (G11b) | — | — | done |
| dnLattice | same + ∃-bound w/trk/A ledger | FILLED (G6) | K7 with Dden ∤ n! (G11b) | — | — | done |
| m1m5Echo | `UCarriers`+MovesSp catalogue (∃-bound letterOf) | FILLED (G7) | member δ beyond catalogue budget (G11c) | — | — | done |
| x1aDict | `KernelCarriers` (gmn, Sp.shape; ∃-bound letterOf/share) | FILLED (G8; AX-INDEX cite statement-side) | gmn ≡ 0 with a certified charge (G11c) | — | — | done |
| m4bConst | MovesV `CtsMeasured` (+Order0Perimeter fence) | FILLED (G9) | census jump inside one listed component (G11c) | — | — | done |
| jcInvHist | MovesT/MovesD (TreeModel/CellData/entEvent)+`NodeRetainedKeyEq` | FILLED (G10) | key-equal entrances with unequal joint laws (G11c) | — | — | done |
NOTE on the ∃s inside G5–G8's filled bodies: P1 governs where junk data can
DISCHARGE a row; those ∃s are budget-priced/pinned (K7.L, Dden, catalogue, gmn)
so junk witnesses cannot discharge — reviewed at their fills, not re-opened here.

### D-SC.4 Unit split + build record

- **IB-G14** RelSite/RelSiteFamily + δabs/dRel/βarg [LANDED real]. R.
- **IB-G15** seven data packs + SiteData [LANDED real]. R.
- **IB-G16** SitedSlot_rel2a/b/d/e [LANDED, 4 sorries]; H-phase fill ADJ→R
  (targets pre-elaborated at †22), behind the Q5 audit + G19b.
- **IB-G17** RelAssignment + ConsumedDisplayPack + SitedSlot_rel3 [LANDED,
  1 sorry]; same gates.
- **IB-G18** RelCarrierPack + six RelRow_* [LANDED, 6 sorries]; row targets in
  header; same gates.
- **IB-G19b** hygiene gate: half 1 (well-typedness probe) LANDED; half 2 (the
  closure re-analysis at the new signatures + degenerate-falseness spot checks)
  runs BEFORE any G16/G17/G18 fill. H.
- **IB-G19a** compiled falsifier family for the six sited/row Props (extends
  G11a; runs AFTER the fills — falsifiers need bodies). H, ~30 total.
- **IB-G20** closure-manifest extension for G14–G18 identifiers (G12 pattern).
  R, doc.
- **IB-G13′** theoremU_bridged′ (ALL THIRTEEN: G4–G10 Props + the six RelRow_*
  at a `RelCarrierPack` binder). WAITS on Q12/Q13 + Q5 audits + G19a/b.
BUILD RECORD: `lake build` green 2026-07-31 through SlotsG19b ("Build completed
successfully (8571 jobs)"); new-sorry census = 11, all E-phase Prop bodies
(G16: 4, G17: 1, G18: 6); G14/G15/G19b sorry-free; nothing imports the new
modules (capstone path + footprints untouched); MovesU/MANIFEST.json entry =
follow-on edit (D-TM precedent).

### D-SC.5 The thirteen ordered by carrier reuse (discharge order)

1. rel1 (the CInterface anchor every REL slot's conditionality displays) →
2. rel2b (site kernel: RelSite+SiteDom+SiteTheta+CI — the pricing every later
   mass claim rides) → 3. rel2a (completes the six-item bundle: +Embed/Frames/
   Dict) → 4. rel2d (+SiteTrees, reuses Θ+dict) → 5. rel2e (+SiteBeta+[3]
   exports, reuses trees+CI vol) → 6. rel3 (adds ONLY the display pack; reuses
   the entire family+assignment) → 7./8. trackRule, dnLattice (pair: same
   XHistory/Pop keying; the ledger reuses the track handle) → 9./10. rs0Lump,
   m1m5Echo (pair: UCarriers roster/verdictImage keying) → 11. x1aDict (KC +
   the GMN cite, isolated) → 12. m4bConst (MovesV, isolated) → 13. jcInvHist
   (MovesT/MovesD, isolated; the Tpin seam caveat recorded at G10).

### D-SC.6 Risk-ledger updates

- **R9 → HALF-RETIRED**: the REL-family half (the "thirteen-slot formulations
  repeating the MovesR failure") is resolved-by-design at the supplied-carrier
  signature; residual = the H-phase fills behind Q5 + G19a/b.  The mechanics/
  seam half was already landed (G4–G10).
- **R13 (new)**: caller-supplied degenerate `RelCarrierPack` at G13′ —
  visible-liability status (named binder in the conditionality record),
  falsifiable (G19a), semantically pinned only by wave-D's instance, exactly
  like `C : UCarriers n`.  Any stronger pinning claim is FORBIDDEN in records.
- **R14 (new)**: carrier drift if MovesR un-parks — two homes for
  Setting-shaped vocabulary.  G14/G15 are the canonical home (R-5); un-parking
  must re-key onto them or supersede by adjudication, never fork.
- **R15 (new; = D-TM R12's pattern)**: pack-without-law leakage — a consumer
  taking a raw `SiteData`/`SiteEmbed` without its `SitedSlot_*` law would ride
  unpinned data (e.g. `teich` without the (a3) pin).  Guard: consumers take the
  law slot as a binder; G20's manifest flags raw-pack consumers.

### D-SC.7 Orchestrator questions / escalations (this addendum's fence events)

- **Q12 (design ratification):** ratify P1–P3 + the G14–G18 vocabulary as THE
  resolution of the G2/G3 BLOCKED escalations (mechanism: the Q5 Codex audit
  over this addendum + the six new files; then G19b half 2).  Until then the
  new Props gate nothing and nothing consumes them.
- **Q13 (= the queued rel3-fallback adjudication, E-1):** G13′ ships ALL
  THIRTEEN via the `RelCarrierPack` binder — the 12-slot fallback (rel3 as a
  visible bare binder) is SUPERSEDED if Q12 lands.  Goal-level conditionality
  surface: the bridged capstone's honesty record gains the pack binder + the
  eleven H-phase-filled law Props.  Flagged for the AUTHORITY-UPDATE decision
  rule; G13′ is a NEW declaration (no ratified statement touched), but its
  capstone role warrants the named sign-off queue.
- **Q14 (disposition of the BLOCKED records):** once Q12 lands, the five
  sorried `Slot_rel2a/b/d/e`/`Slot_rel3` in SlotsG2/G3 are dead vocabulary
  wearing live names — quarantine-with-record vs keep-in-place.  Fence event;
  NOT executed under the 2026-07-31 boundary decision.
- **Q15 (cross-area export duties, E-3):** ledger entries owed — [3]/MovesS
  exports `tableConv`/`consumed` (CF13/CF14's suppliers); [4] populates
  `ConsumedDisplayPack` when SQ.0–SQ.2 are drafted (the note's own REL.3
  acceptance criterion); wave-D inhabits `SiteData`/`RelAssignment`/
  `RelCarrierPack`; HC-1's GradedCarrier deliverable unchanged.

FILE MAP (all NEW; no existing file touched): lean/LeanUrat/MovesU/
SlotsG14_relSite.lean · SlotsG15_siteData.lean · SlotsG16_sitedLaws.lean ·
SlotsG17_rel3Display.lean · SlotsG18_relPack.lean · SlotsG19b_targetElab.lean.

### D-SC.8 Mid-round scope fold-in (item-9 adjudication, 2026-07-31)

The item-9 FORM ADJUDICATION (wf_b933dcd7-877; BRIDGE_ADJUDICATIONS sign-off
item 9(iv), committed 02498f7 mid-round) routed one addition into this design's
scope: "the base-change seam (REL.2(d), e_j ambient-vs-rebased) is note-side
OPEN — the (e4) 'owed' first-index definition joins the carrier-layer design
scope."  DISPOSITION (landed, IB-G15b = SlotsG15b_e4Seam.lean, real, 0 sorry):
the design already carries (e4) per CF13 — `entryFirst` free data + `tableConv`
as the ONLY obligation — which is exactly compatible with the seam being open;
G15b makes the seam VISIBLE as vocabulary by naming BOTH candidate readings
(`SiteBeta.firstIdxCandidateRebased` : entryFirst = S.dRel, the note's own
candidate; `SiteBeta.firstIdxCandidateAmbient` : entryFirst = (S.d : ℕ), the
seam's other face) under the CF13 consumption fence (named candidates ONLY; no
consumer, no SitedSlot law, may hypothesize either; IB-G20 flags violators).
The future (e)-pass resolves the seam by PROVING one reading from [3]'s tables
— never by a silent keying choice.  FILE MAP + build record updated: seven new
files total, `lake build … SlotsG15b_e4Seam` green ("Build completed
successfully (8567 jobs)", 2026-07-31).
