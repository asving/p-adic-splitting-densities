/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeB8_regData

/-!
# BridgeRosterPins — the roster pins + the RegP transport (bridge campaign BP1, cluster BP1-c5)

E-phase skeletons per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3
(†4c)/(†4d)/(†4e) / §4 group B, under
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q3: `hdet`/`hStateNe`
ratified as named premises).  Units in this file, in internal dependency order
(the §7 wave order: B11/B12/B13 → B10; B17 → B15a/B15b):

* IB-B17  `RegPAt` clause vocabulary + `bridgeActiveLocus`/`bridgeResidualPool`
* IB-B11  `bridge_Jcell_pin` — the (†4c) J-image equality at the roster
* IB-B12  `bridge_W_pin` — the (†4c) W-image equality at the roster
* IB-B13  `bridge_bsplit_pin`/`bridge_betaLeg_pin` — the dite-field pins
* IB-B10  `bridgeRegPin` — the `RegPin` record assembly (LAST of the pin units)
* IB-B14  `bridgeRegData_pool_mem` + `bridgeRegData_entryList_nonempty` sanity
* IB-B15a `bridge_r2_on_activeLocus` — (r2)-transport on the active locus
* IB-B15b `bridge_r1_on_activeLocus` — (r1)-transport at the chain-covered pairs
* IB-B16  the junk-block gap RECORD (three named display Props, doc-only)

FILE-NAME RESOLUTION (recorded): the blueprint's §4 prescribes ONE group-B file
`BridgeRoster.lean`, but group B is split across two clusters; the sibling
cluster (IB-B1…B9) landed per-unit files `BridgeB*.lean`, and the E-phase
no-edit rule forbids sharing a file, so THIS cluster's nine units land here.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
1. IB-B17's blueprint display names one Prop `RegPAt D q₀ e` while IB-B15a/b
   consume "the (r1)/(r2) conjunct of `RegPAt`"; the two conjuncts are
   therefore factored as the NAMED defs `RegPAtR1`/`RegPAtR2` with
   `RegPAt := RegPAtR1 ∧ RegPAtR2` — a definitional re-grouping of
   `RegP`'s body (`MovesU/Defs.lean:209`), nothing added or dropped.
2. `bridgeActiveLocus` is displayed in the blueprint as `bridgeActiveLocus C p`;
   it reads `(bridgeRegData …).Pool`, so it carries `bridgeRegData`'s own
   `hn : 2 ≤ n` and `hne : HStateNe n C` binders (IB-B8's as-built signature —
   no new premise: both are mkUInstance's existing binders per Q3/finding 2).
3. IB-B15a/IB-B15b carry `hp : p.Prime`: the blueprint's transport route rides
   `UCarriers.cl1 hp` (= `chain.legs_reg` at the base prime) and
   `chain.pools_e0` (PrimePools-scoped), neither of which binds at composite p.
   theoremU's per-p frame supplies `hp` at every use site.
4. IB-B15b's "(r1) AT CHAIN-COVERED PAIRS" is transcribed as the ∀ over
   `bridgeActiveLocus` — the locus whose complement (†4e) names as BOTH units'
   typed residual ("Pool \ bridgeActiveLocus; the uncovered (q₀, e) pairs").
   The docstring pins the primary route (q₀ = p^1) and the secondary probe
   (deeper all-active pools); if the deep-pool legs stall, the prover returns
   the typed uncovered-pair spec (bounded repair → adjudication), NEVER a
   weakened statement (statement fence; RISK R3).
   AS-BUILT DISCREPANCY (recorded): the blueprint's secondary probe cites
   "pools_e0's deeper all-active pools", but the as-built
   `RS4Chain.pools_e0` (MovesS/Interfaces.lean:138) is scoped to
   `PrimePools ∩ allActivePools` — BASE pools only; the deeper (δ > 1)
   packages actually come from `cl1`'s `MovesS.RegP` quantifier
   (∀ δ ∈ consumedDeltas, `PoolHyp` at (p:ℚ)^δ — MovesS/Defs.lean:618).
5. IB-B16 ("machine-readable docstring unit … no proof obligations") is
   realized as three NAMED display Props (burden / covered / residual gap) so
   the quantifier diff is compiled vocabulary, not prose; no theorem is stated.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-! ## IB-B17 — the RegP-transport vocabulary (†4e, post-Codex finding 8) -/

/-- IB-B17 (def): the (r1) conjunct of the (q₀, e)-clause of `RegP`
    (`MovesU/Defs.lean:209`, first conjunct verbatim): the FULL block
    determinant — junk blocks included — is defined and ≠ 0 at the pool value.
    Deps: — (Defs vocabulary only).  Consumers: IB-B15b, IB-B16. -/
def RegPAtR1 {p : ℕ} (D : RegData p) (q₀ : ℕ) (e : D.Block) : Prop :=
  letI := D.instBi e; letI := D.instBd e
  DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
    (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0

/-- IB-B17 (def): the (r2) conjunct of the (q₀, e)-clause of `RegP`
    (`MovesU/Defs.lean:209`, second conjunct verbatim): every member of the
    DEFINED entry list E(e) is defined at the pool value and agrees with the
    ACT active value.  Deps: —.  Consumers: IB-B15a, IB-B16. -/
def RegPAtR2 {p : ℕ} (D : RegData p) (q₀ : ℕ) (e : D.Block) : Prop :=
  ∀ g ∈ D.entryList e,
    DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀

/-- IB-B17 (def): the (q₀, e)-clause of `RegP`, factored (blueprint (†4e):
    "`RegPAt D q₀ e : Prop` := the (q₀, e)-clause of `RegP` factored out") —
    the conjunction of the two named conjuncts (header resolution 1). -/
def RegPAt {p : ℕ} (D : RegData p) (q₀ : ℕ) (e : D.Block) : Prop :=
  RegPAtR1 D q₀ e ∧ RegPAtR2 D q₀ e

/-- IB-B17 (decomposition law): `RegP` IS the ∀∀-closure of its factored
    clause — a definitional re-grouping of `MovesU/Defs.lean:209`'s body.
    Sketch: `Iff.rfl` (both sides unfold to the same term; the letI grouping
    of `RegPAtR1` matches `RegP`'s first-conjunct parenthesization). -/
theorem regP_iff_regPAt {p : ℕ} (D : RegData p) :
    RegP D ↔ ∀ q₀ ∈ D.Pool, ∀ e : D.Block, RegPAt D q₀ e :=
  Iff.rfl

open scoped Classical in
/-- IB-B17 (def): THE ACTIVE LOCUS of the tautological roster — the roster's
    pool filtered by membership of the ℚ-cast in `MovesS.allActivePools C.MS`
    (the DEFINED all-active locus, MovesS/Defs.lean:197) — EXACTLY `pools_e0`'s
    all-active locus (MovesS/Interfaces.lean:138) read on the roster's pool.
    Classical decidability on the Set membership.  Binders per header
    resolution 2.  Deps: IB-B8.  Consumers: IB-B15a, IB-B15b, IB-B16. -/
noncomputable def bridgeActiveLocus {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : Finset ℕ :=
  (bridgeRegData hn C hne p).Pool.filter
    fun q₀ => (q₀ : ℚ) ∈ MovesS.allActivePools C.MS

/-- IB-B17 (def): THE TYPED RESIDUAL of the (†4e) transport — the pool slice
    NOT covered by IB-B15a/IB-B15b ("Pool \ bridgeActiveLocus"), the index of
    the uncovered (q₀, e) pairs both units return and IB-B16 records. -/
noncomputable def bridgeResidualPool {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : Finset ℕ :=
  (bridgeRegData hn C hne p).Pool \ bridgeActiveLocus hn C hne p

/-! ## IB-B11 — the J-image pin at the roster (†4c) -/

/-- IB-B11: `bridge_Jcell_pin` — the STANDALONE image-equality LEMMA (†4c) over
    `bridgeRegData` (post-Codex finding 4: a lemma, not a `RegPin` field
    proof): the univ-image of the roster's per-cell J row equals the real
    per-cell table's value set (biUnion over states/split outcomes/cells of
    `jPCell`).  This is `RegPin.Jcell_pin`'s sentence (DefsLedger.lean:516)
    at `D := bridgeRegData`, `blk := Equiv.refl`.  Both sides enumerate the
    same value set: LHS over the IB-B6 attach carrier, RHS over the cells
    themselves.  Deps: IB-B6, IB-B8.  Consumer: IB-B10 (`Jcell_pin := `this).
    Sketch (H, ~35): `Finset.ext` + `Finset.mem_image`/`mem_biUnion` unfolding
    + the sigma/attach carrier's enumeration (`Finset.mem_univ` trivial,
    `Finset.mem_attach` for the cell coordinate). -/
theorem bridge_Jcell_pin {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (b : {e : ℕ // e ∈ Finset.Icc 1 n}) :
    (letI := (bridgeRegData hn C hne p).instJ b
     letI := Classical.decEq (RatFunc ℚ)
     Finset.univ.image ((bridgeRegData hn C hne p).Jcell b))
      = (letI := Classical.decEq (RatFunc ℚ)
         (Finset.univ : Finset (C.T.State b.1)).biUnion fun τ =>
           (MovesS.splitOuts C.T b.1 τ).biUnion fun o =>
             (C.MS.cells b.1 τ o).image fun c =>
               (C.RB.jPCell b.1 τ c).val) :=
  sorry

/-! ## IB-B12 — the W-image pin at the roster (†4c) -/

/-- IB-B12: `bridge_W_pin` — the STANDALONE image-equality LEMMA over
    `bridgeRegData`: the univ-image of the roster's W row (over the IB-B7
    attach carrier `BridgeWIdx C = {Ŝ // Ŝ ∈ C.Fam.Sh}`) equals the real
    shape-presentation image `C.Fam.Sh.image (fun Ŝ => (WshP Ŝ).val)`.
    `RegPin.W_pin`'s sentence (DefsLedger.lean:525) at the roster.
    Deps: IB-B7, IB-B8.  Consumer: IB-B10 (`W_pin := `this).
    Sketch (R, ~15): univ-image over the Finset-coe subtype = image over the
    Finset (`Finset.image_coe_univ`-style; `Finset.attach_image_val`). -/
theorem bridge_W_pin {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) :
    (letI := (bridgeRegData hn C hne p).instW
     letI := Classical.decEq (RatFunc ℚ)
     Finset.univ.image (bridgeRegData hn C hne p).Wcoef)
      = (letI := Classical.decEq (RatFunc ℚ)
         C.Fam.Sh.image fun Ŝ => (C.chain.WshP Ŝ).val) :=
  sorry

/-! ## IB-B13 — the dite-field pins at the roster (†4c tail) -/

/-- IB-B13 (bsplit half): `bridge_bsplit_pin` — the STANDALONE LEMMA equating
    the roster's split-exit row (IB-B9's `bridgeBsplit`, wired by IB-B8) to
    `RegPin.bsplit_pin`'s RHS (DefsLedger.lean:495) at `blk/st := Equiv.refl`:
    the real `MovesS.bSplit` with the real `blockSolveLt` legs, over the
    chain's exact σ-index `Sigmas`, at any supplied `hdet`.
    Deps: IB-B8, IB-B9 (this IS `bridgeBsplit_eq_of_detHyp` read at the
    record).  Consumer: IB-B10 (`bsplit_pin := `this).
    Sketch (R, ~15): `dif_pos` + proof irrelevance of the `DetHyp` witness. -/
theorem bridge_bsplit_pin {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (b : {e : ℕ // e ∈ Finset.Icc 1 n}) (i : C.T.State b.1) :
    (bridgeRegData hn C hne p).bsplit b i
      = ∑ σ' ∈ C.chain.Sigmas,
          MovesS.bSplit C.T C.RB C.hdc b.1 b.2
            (MovesS.blockSolveLt C.RB C.hdc C.hK hdet b.1) σ' i :=
  bridgeBsplit_eq_of_detHyp C hdet b i

/-- IB-B13 (betaLeg half): `bridge_betaLeg_pin` — the STANDALONE LEMMA equating
    the roster's β-leg row (IB-B9's `bridgeBetaLeg`, wired by IB-B8) to
    `RegPin.betaLeg_pin`'s RHS (DefsLedger.lean:505) at the tautological
    `legSt = legTarget` reading: `powSubst δ` of the real `blockSolve` at the
    leg's real (block, state) target, over `Sigmas`, at every positive depth of
    the pinned depth set.  Deps: IB-B8, IB-B9 (= `bridgeBetaLeg_eq_of_pos`
    read at the record; the `δ ∈ depthSet` hypothesis mirrors the pin field's
    shape and is unused by the underlying dite law).  Consumer: IB-B10
    (`betaLeg_pin := `this).  Sketch (R, ~15): `dif_pos ⟨hδ, hdet⟩` + proof
    irrelevance of the conjunction witness. -/
theorem bridge_betaLeg_pin {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (b : {e : ℕ // e ∈ Finset.Icc 1 n}) (l : LegRoster C.T b.1)
    (δ : ℕ) (hδ : 0 < δ) (hmem : δ ∈ (bridgeRegData hn C hne p).depthSet) :
    (bridgeRegData hn C hne p).betaLeg b l δ
      = MovesS.powSubst ⟨δ, hδ⟩
          (∑ σ' ∈ C.chain.Sigmas,
            MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
              (legTarget C b.1 b.2 l).1.1 (legTarget C b.1 b.2 l).1.2
              (legTarget C b.1 b.2 l).2 σ') :=
  bridgeBetaLeg_eq_of_pos C hdet b l δ hδ

/-! ## IB-B10 — the RegPin record assembly (LAST of the pin units) -/

/-- IB-B10: `bridgeRegPin` — THE ROSTER PIN at the tautological roster
    (†4, the r_is_solve pattern: constructing D FROM the real §S objects makes
    every pin `rfl`/`Equiv.refl`/proof-irrelevance).  Re-ordered LAST of the
    pin units (post-Codex finding 4): the data fields are supplied here
    (`blk`/`st`/`legEquiv` := `Equiv.refl`, `legSt` := the real `legTarget`),
    the rfl-pins (depth/K/iota/bterm/blockDim/cell/shape/leg/legSt) are
    one-line `rfl`s at the record literal, and the four non-rfl pins wire in
    the standalone lemmas: `Jcell_pin := bridge_Jcell_pin` (IB-B11),
    `W_pin := bridge_W_pin` (IB-B12), `bsplit_pin`/`betaLeg_pin` :=
    IB-B13's lemmas, `act_pin := bridgeAct_ok` (IB-B3).
    Deps: IB-B5, IB-B6, IB-B8, IB-B9, IB-B11, IB-B12, IB-B13.
    Consumers: IB-B15b, IB-F4 (`mkUInstance.Dpin`).
    Sketch (R, ~30): `Equiv.refl` + `rfl` + the lemma wiring; every `sorry`
    below is one of those three shapes. -/
noncomputable def bridgeRegPin {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) :
    RegPin C (bridgeRegData hn C hne p) where
  blk := Equiv.refl _
  st := fun _ => Equiv.refl _
  depth_pin := rfl
  K_pin := fun _ _ _ => rfl
  iota_pin := fun _ _ => rfl
  act_pin := fun g q₀ hok => bridgeAct_ok g q₀ hok
  bterm_pin := fun _ _ => rfl
  bsplit_pin := fun hdet b i => bridge_bsplit_pin hn C hne p hdet b i
  legSt := fun b l => legTarget C b.1 b.2 l
  legEquiv := fun _ => Equiv.refl _
  legSt_pin := fun _ _ => rfl
  betaLeg_pin := fun hdet b l δ hδ hmem =>
    bridge_betaLeg_pin hn C hne p hdet b l δ hδ hmem
  blockDim_pin := fun _ => rfl
  cell_pin := fun _ => rfl
  Jcell_pin := fun b => bridge_Jcell_pin hn C hne p b
  shape_pin := rfl
  W_pin := bridge_W_pin hn C hne p
  leg_pin := fun _ => rfl

/-! ## IB-B14 — roster sanity (non-vacuity display) -/

/-- IB-B14 (pool half): p = p^1 is in the roster's pool — `RegData.pool_self_mem`
    (U8) at the roster (`one_mem_depthSet` + `pool_eq`), so `RegP`'s binding is
    never vacuous in q₀.  Deps: IB-B8.  Sketch (R): apply `pool_self_mem`. -/
theorem bridgeRegData_pool_mem {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) :
    p ∈ (bridgeRegData hn C hne p).Pool :=
  (bridgeRegData hn C hne p).pool_self_mem

/-- IB-B14 (entry half): the roster's entry list is nonempty at every block —
    the non-vacuity display of `RegP`'s (r2) binding shape (`MovesU/Defs.lean`
    RegP docstring: the K-entry family rides the always-nonempty per-block
    state index `instBiNe` = `hne`).  Deps: IB-B8.  Sketch (R, ~10): exhibit
    `K b i₀ i₀` with `i₀ := (hne b.1 b.2).some`; membership by the first
    `Finset.mem_union` disjunct + `mem_image` of `(i₀, i₀)`. -/
theorem bridgeRegData_entryList_nonempty {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (b : {e : ℕ // e ∈ Finset.Icc 1 n}) :
    ((bridgeRegData hn C hne p).entryList b).Nonempty :=
  sorry

/-! ## IB-B15a — (r2)-transport on the active locus (†4e) -/

/-- IB-B15a: the (r2) conjunct of `RegPAt (bridgeRegData …) q₀ e` holds for
    EVERY pool value on the active locus and every block — the typed partial
    transport of (REG-p)'s entry-family clause from the carried chain.
    EXPECTED PARTIAL BY DESIGN at the unit level: the deliverable is proof +
    typed gap spec; the residual index is `bridgeResidualPool` (IB-B17), the
    record IB-B16.  Deps: IB-B17, IB-C1 (proof-time: `bridgeSolve_ok`'s OKat
    route), IB-B3 (`bridgeAct_ok`).  `hp` per header resolution 3.
    Sketch (H, ~35): q₀ = p^δ with δ ∈ consumedDeltas (pool_eq); `UCarriers.cl1
    hp` (= `legs_reg` at the base prime, DefsCarriers.lean:98) supplies the
    `PoolHyp` package at every consumed pool; on the ALL-ACTIVE locus the
    entry families are pole-free (`jcell_ok`/`wsh_ok`/the chain's per-family
    OKat laws), so each `g ∈ entryList` is `DefinedAt` and
    `bridgeAct_ok` (IB-B3) closes the agreement conjunct
    (`D.act g q₀ = evalAt q₀ ⟨g, _⟩ = g.eval …` — the eval/evalAt tie is the
    `SolveSeam.R_agree` cast pattern, DefsLedger.lean:599, in miniature). -/
theorem bridge_r2_on_activeLocus {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (hp : p.Prime) :
    ∀ q₀ ∈ bridgeActiveLocus hn C hne p,
      ∀ b : {e : ℕ // e ∈ Finset.Icc 1 n},
        RegPAtR2 (bridgeRegData hn C hne p) q₀ b :=
  sorry

/-! ## IB-B15b — (r1)-transport at the chain-covered pairs (†4e) -/

/-- IB-B15b: the (r1) conjunct of `RegPAt (bridgeRegData …) q₀ e` at the
    CHAIN-COVERED pairs, transcribed as the ∀ over the active locus (header
    resolution 4).  PRIMARY ROUTE: q₀ = p^1 (∈ the locus whenever (p : ℚ) is
    all-active), where `UCarriers.cl1 hp` supplies `MovesS.RegP`'s `PoolHyp`
    packages, transported through the K_pin submatrix-determinant identity —
    `RegPin.detHyp`'s calc (DefsLedger.lean:536ff) run in REVERSE at
    `bridgeRegPin`'s `blk/st = Equiv.refl` (the roster's `det (1 - K e)` IS
    the real block determinant, `Matrix.det_submatrix_equiv_self`).
    SECONDARY PROBE: the deeper all-active pools p^δ, δ ∈ consumedDeltas —
    packages from `cl1`'s own ∀δ quantifier (as-built discrepancy note,
    header resolution 4).  EXPECTED PARTIAL BY DESIGN: on the junk-block
    sublocus the full (r1) EXCEEDS the note (MOVES 12208–12210; RISK R3) —
    if a leg stalls, RETURN the typed uncovered-pair spec (indexed by
    `bridgeResidualPool` + the failing (q₀, b) pairs), never weaken `RegP`
    (statement fence: Defs.lean:209 untouchable).
    Deps: IB-B17, IB-B10.  `hp` per header resolution 3.  Sketch: H, ~35. -/
theorem bridge_r1_on_activeLocus {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) (hp : p.Prime) :
    ∀ q₀ ∈ bridgeActiveLocus hn C hne p,
      ∀ b : {e : ℕ // e ∈ Finset.Icc 1 n},
        RegPAtR1 (bridgeRegData hn C hne p) q₀ b :=
  sorry

/-! ## IB-B16 — the junk-block gap RECORD (†4e; doc-only, NO proof obligations)

THE GAP, MACHINE-READABLE (blueprint (†4e) + RISK R3, pre-refuted by note
read): `theoremU`'s per-p premise is `RegP (bridgeRegData …)` — the FULL
∀-closure `bridgeRegPBurden` below, whose (r1) face demands EVERY block's
determinant (junk blocks included) defined and ≠ 0 at EVERY pool value.  The
note's own discipline is STRICTLY WEAKER on the wild (non-all-active) pools:
"the junk-block determinants det(I − D_{q₀}) are RECORDED (a zero is a
FINDING, not by itself a FAIL; a blanket det(I − D_{q₀}) ≠ 0 is NOT
required)" (MOVES 12208–12210, quoted verbatim at `MovesS.LegAgree`'s
docstring, Interfaces.lean:82–85); the note's wild-pool agreement burden is
the PER-POOL weakened (ii-c) gate `chain.legs_read`, which carries NO
determinant clause for the inactive blocks.  The quantifier diff, in this
file's compiled vocabulary:

  `bridgeRegPBurden  ↔  bridgeRegPCovered ∧ bridgeRegPResidualGap`

(Pool splits as `bridgeActiveLocus ∪ bridgeResidualPool`, disjointly — a
filter and its sdiff; the decomposition rides `regP_iff_regPAt`).  IB-B15a/b
target `bridgeRegPCovered` (their typed residuals index the uncovered pairs);
`bridgeRegPResidualGap` — (r1)+(r2) on `bridgeResidualPool`, i.e. at the
wild pools — is the sublocus where the burden EXCEEDS the note: NO prover may
be assigned to it without a NEW mechanism (it is not a lemma the note
warrants; a per-C counterexample is expected once a concrete `UCarriers`
pack with a genuinely wild pool lands — no compiled countermodel is possible
without one, so this record produces the exact quantifier diff instead).
Consequence for the capstone: (REG-p) stays `theoremU`'s explicit per-p
hypothesis (D8: at a p failing (REG-p), no claim); the bridge does NOT
discharge it, and any future discharge claim must name this record.
NO THEOREM IS STATED HERE (doc-only unit): the three defs below are display
vocabulary, and the ↔ above is recorded prose, deliberately unproved. -/

/-- IB-B16 (display 1/3): THE BURDEN — theoremU's per-p (REG-p) premise at the
    tautological roster, verbatim `RegP (bridgeRegData …)`.  What the ledger
    demands; NOT what the note warrants at wild pools (see the section
    header).  Doc-only vocabulary; no unit proves this. -/
def bridgeRegPBurden {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : Prop :=
  RegP (bridgeRegData hn C hne p)

/-- IB-B16 (display 2/3): THE COVERED PART — both clauses on the active locus;
    exactly IB-B15a ∧ IB-B15b's joint target, the note-warranted transport. -/
def bridgeRegPCovered {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : Prop :=
  ∀ q₀ ∈ bridgeActiveLocus hn C hne p,
    ∀ b : {e : ℕ // e ∈ Finset.Icc 1 n},
      RegPAt (bridgeRegData hn C hne p) q₀ b

/-- IB-B16 (display 3/3): THE RESIDUAL GAP — both clauses on the wild slice
    `bridgeResidualPool` (Pool \ activeLocus).  The precise sublocus where the
    full (r1) EXCEEDS the note (MOVES 12208–12210): junk-block determinants
    are there RECORDED, never required nonzero.  UNASSIGNABLE as stated (see
    the section header); indexes IB-B15a/IB-B15b's typed residuals. -/
def bridgeRegPResidualGap {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : Prop :=
  ∀ q₀ ∈ bridgeResidualPool hn C hne p,
    ∀ b : {e : ℕ // e ∈ Finset.Icc 1 n},
      RegPAt (bridgeRegData hn C hne p) q₀ b

end LeanUrat.MovesU
