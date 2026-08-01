/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps

/-!
# Scaffold/HDischarge/H2/DictIIIProbes — the two adjudication probes
  [HDISCHARGE_H2 unit H2-U7; wave 1, MED, dep DictIII.Hyps]

Transcription of `lean/blueprints/HDISCHARGE_H2.md` §6 unit H2-U7, theorem
statements VERBATIM.

* PROBE F-1 (`dictFresh_junctionPin_trivial`): the `junctionPin` clause of the
  landed `DictIII.FRESH` row is TRIVIAL — its conclusion follows from its own
  guard `i + 1 < H.nodes.length` with no (FRESH) content at all.
* PROBE F-2 (`probe_not_FRESH`): a compiled negation witness — the
  duplicate-node history `nodes = [ν, ν]` (with `base := ⊤`, `psi0 := X`,
  `psihat i := X + 1`, over `F = ZMod 2`) satisfies every `EHist` carrier law
  but refutes the `parentSeparated` clause, so the landed `DictIII.FRESH` row
  is FALSE at an intended-instance class (the carrier laws do NOT obstruct
  duplicate nodes: no `EHist` law mentions `nodes` beyond its type).

Output feeds the §2.3 sign-off-gated adjudication; per the unit charge, NO
restatement of `DictIII.FRESH` is made in this file — the probes only consume
the landed row.  Witness names (`probeNode`, `duplicateEHist`) are this unit's
construction freedom (blueprint: "construction is the unit's work").
-/

namespace LeanUrat.Scaffold.HDischarge.H2

/- The proof below is the blueprint-supplied one, kept verbatim; in this pin
`simp`'s default set already carries the `isSome`/`getElem?` reduction
(`List.isSome_getElem?`), so the listed argument is redundant and only the
`unusedSimpArgs` linter (not the proof) needs quieting. -/
set_option linter.unusedSimpArgs false in
/-- PROBE F-1 (PROVED at blueprint probe): DictIII.FRESH.junctionPin is trivial. -/
theorem dictFresh_junctionPin_trivial {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (H : DictIII.EHist p F) (i : ℕ)
    (h : i + 1 < H.nodes.length) : (H.nodes[i]?).isSome := by
  simp [List.getElem?_eq_some_iff]; omega

/-- The duplicated node ν of the PROBE F-2 witness: e = h = ℓ = 1, s = u = 0,
    terminal (`sel = none`), `inc = false`.  Every `ENodeData` carrier law
    holds (`hsel` is vacuous at `sel = none`). -/
def probeNode : DictIII.ENodeData where
  e := 1
  h := 1
  ℓ := 1
  s := 0
  u := 0
  sel := none
  inc := false
  he := le_rfl
  hh := le_rfl
  hcop := by decide
  hl := le_rfl
  hsel := by simp

/-- The witness dressing laws: `X + 1` over `↥(⊤ : Subfield (ZMod 2))` is
    monic, irreducible, and ≠ `X` (helper for `duplicateEHist.hpsihat`). -/
theorem probePsihat_laws :
    (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).Monic ∧
      Irreducible (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))) ∧
      (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))) ≠
        Polynomial.X := by
  have hm : (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ↥(⊤ : Subfield (ZMod 2)))
  have hd : (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).degree = 1 := by
    simpa using Polynomial.degree_X_add_C (1 : ↥(⊤ : Subfield (ZMod 2)))
  refine ⟨hm, hm.irreducible_of_degree_eq_one hd, ?_⟩
  · intro hXC
    have h10 := congrArg (fun q => Polynomial.coeff q 0) hXC
    simp at h10

/-- The PROBE F-2 duplicate-node witness history over `F = ZMod 2`:
    `nodes = [ν, ν]` with ν = `probeNode`, `base := ⊤`, `psi0 := X`,
    `psihat i := X + 1` — every `EHist` carrier law holds (no law constrains
    `nodes`), yet `nodes[0]? = nodes[1]?`. -/
noncomputable def duplicateEHist : DictIII.EHist 2 (ZMod 2) where
  base := ⊤
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 1
  ha0 := le_rfl
  nodes := [probeNode, probeNode]
  fld := fun _ => ⊤
  psihat := fun _ => Polynomial.X + 1
  hpsihat := fun _ => probePsihat_laws

/-- The witness node list, read back (definitional). -/
theorem duplicateEHist_nodes :
    duplicateEHist.nodes = [probeNode, probeNode] := rfl

/-- PROBE F-2: compiled negation witness — duplicate-node history refutes
    DictIII.FRESH.parentSeparated at an intended-instance class. -/
theorem probe_not_FRESH : ∃ (p : ℕ) (_ : Fact p.Prime),
    ¬ (DictIII.FRESH p (ZMod 2)) := by
  refine ⟨2, inferInstance, fun hF => ?_⟩
  exact hF.parentSeparated (H := duplicateEHist) (i := 0) (j := 1)
    (by simp [duplicateEHist_nodes]) (by simp [duplicateEHist_nodes])
    (by omega) rfl

/-! ## H2-U10 gate probe (PROBE F-4, sign-off execution attempt, 2026-08-05 ledger)

The §2.3 sign-off opened the `DictIII.FRESH` restatement.  At the LANDED
consumption shape (Scaffold/DictIII/CU1.lean fires ONLY `childDetermined`, at
`cu1_stepPair_ge2` — III-U3b landed after the blueprint's gate note was
written), BOTH signed-off routes preserve exactly one candidate faithful
clause:

* Option A (census-face re-point + classifier-face corollary): the census
  face lives at `FreshClauses`/`FreshRowOn` (H2-U2/U8; different carriers, no
  bridge to `EHist`), so the DictIII row's surviving content IS the
  classifier-face clause = `childDetermined`.
* Option B (chain-keyed twins, "III-U3b's consumption shape fixes the field
  list"): the landed consumption is `childDetermined` alone.

PROBE F-4 refutes THAT clause at the U7 witness, so the restated carrier
FAILS its non-vacuity gate in the signed-off form — U10 is BLOCKED:

* Over `duplicateEHist` (all nodes terminal), `continuingPart.nodes = []`,
  so `Theta duplicateEHist` has NO slopes; `GMNReader.side_spec` then FORCES
  `side i = none` at every level for EVERY reader (no side can carry a
  requested slope), while `ConsF` holds vacuously.  Node 0 is nonetheless
  recorded, so `∃! S, R.side 0 = some S` fails.
* Same transcription-overreach class as the III-U8 verdict (CU1.lean): the
  clause's implicit `{H} {D} {R}` range over law-free carriers.  The known
  dichotomy, for the record: guarding by `InteriorChain` (all nodes
  continuing) makes the clause PROVABLE from `ConsF`'s own read clause
  (trivial — placeholder again); leaving it unguarded makes it FALSE (this
  probe).  The terminal-index read is terminal-seam ((T-READ)/H6) content,
  not (FRESH); the honest restatement needs a blueprint-level scope repair
  beyond the §2.3 signed-off envelope — statement fence, NOT executed here.

EXECUTED at H2-U10b (2026-08-01, adjudicated under Asvin's standing
statement-change authority): the consumer check found the ONLY firing site
(`cu1_stepPair_ge2`) interior-only, so `DictIII.FRESH.childDetermined` was
restated to the `InteriorChain`-guarded unique-side form (Hyps.lean — see the
row's docstring for the honest pricing).  This probe STANDS as the compiled
record of why the guard is REQUIRED (the unguarded form is false).  The
mandatory non-vacuity witness is the `interior*` block below. -/

/-- Gate artifact (PROBE F-4): the all-empty semantic datum over the U7
    witness chain, `rootOrder` matched to `duplicateEHist.a0 = 1` so the
    `ConsF` root clause holds. `GMNData` is law-free data. -/
noncomputable def emptyDataDup :
    DictIII.GMNData (Polynomial.X : Polynomial ℤ_[2])
      (DictIII.Theta duplicateEHist) where
  principalSides := fun _ => []
  residualOrder := fun _ => 0
  residualDegree := fun _ => 0
  rootOrder := 1

/-- Gate artifact (PROBE F-4): the forced reader over the U7 witness — with
    no principal sides (and no requested slopes), `side_spec` admits ONLY
    `side ≡ none`; every law is satisfied. -/
noncomputable def noneReaderDup :
    DictIII.GMNReader (Polynomial.X : Polynomial ℤ_[2])
      (DictIII.Theta duplicateEHist) emptyDataDup where
  side := fun _ => none
  side_spec := by intro i S; simp [emptyDataDup]
  side_unique := by intro i S T hS _ _ _; simp [emptyDataDup] at hS
  resOrd := fun _ => 0
  resOrd_spec := fun _ => rfl
  rootOrd := 1
  rootOrd_spec := rfl
  resDeg_eq_sideDeg := by intro i S h; simp at h

/-- PROBE F-4 step: `ConsF` HOLDS at the U7 witness with the none-reader —
    the continuing part is empty (both nodes terminal), and the root orders
    match. -/
theorem consF_noneReaderDup :
    DictIII.ConsF (Polynomial.X : Polynomial ℤ_[2]) duplicateEHist
      emptyDataDup noneReaderDup := by
  refine ⟨rfl, ?_⟩
  intro i ν h
  have hnil : duplicateEHist.continuingPart.nodes = [] := rfl
  rw [hnil] at h
  simp at h

/-- PROBE F-4 (the H2-U10 non-vacuity gate, FAILED): the `childDetermined`
    clause — the single faithful clause BOTH signed-off restatement routes
    preserve at the landed consumption shape — is REFUTED at the U7 witness
    instance class.  The restated `DictIII.FRESH` would be uninhabited at the
    gate prime in the signed-off form: U10 BLOCKED, statement fence held. -/
theorem probe_restated_childDetermined_refuted :
    ¬ (∀ {f : Polynomial ℤ_[2]} {H : DictIII.EHist 2 (ZMod 2)}
        {D : DictIII.GMNData f (DictIII.Theta H)}
        {R : DictIII.GMNReader f (DictIII.Theta H) D}
        {i : ℕ} {ν : DictIII.ENodeData}, DictIII.ConsF f H D R →
          H.nodes[i]? = some ν → ∃! S, R.side i = some S) := by
  intro hcd
  obtain ⟨S, hS, -⟩ := hcd (f := Polynomial.X) (H := duplicateEHist)
    (D := emptyDataDup) (R := noneReaderDup) (i := 0) (ν := probeNode)
    consF_noneReaderDup (by simp [duplicateEHist_nodes])
  simp [noneReaderDup] at hS

/-! ## H2-U10b — the MANDATORY interior non-vacuity witness

The restated (guarded) `DictIII.FRESH.childDetermined` row is anchored here at
a compiled INTERIOR instance: a one-node interior chain (a₀ = 2; the node
continuing with `sel = some (1, 2)`, μ = 2 ≥ 2) whose `Theta` chain carries an
ACTUAL slope `(1, 1)`, together with semantic data holding one principal side
at that slope, a reader reading it, and a `ConsF` proof — so the guarded
clause's ∃! is realized by an actual side (`interior_childDetermined_gate`),
NOT by the vacuous none-world of PROBE F-4.  The F-4 witness cannot anchor
the guarded row: `duplicateEHist_not_interior` shows the guard excludes it.
Witness artifacts only — degenerate toy carriers, never to be quarried as
project data (the U8 witness-style note applies verbatim). -/

/-- H2-U10b witness node: CONTINUING (`sel = some (1, 2)`, μ = 2 ≥ 2),
    e = h = 1, ℓ = 2 (so `hsel`'s `μ·g ≤ ℓ` holds: 2·1 ≤ 2). -/
def interiorNode : DictIII.ENodeData where
  e := 1
  h := 1
  ℓ := 2
  s := 0
  u := 0
  sel := some (1, 2)
  inc := false
  he := le_rfl
  hh := le_rfl
  hcop := by decide
  hl := one_le_two
  hsel := by
    intro gμ hgμ
    simp only [Option.mem_def, Option.some.injEq] at hgμ
    subst hgμ
    exact ⟨le_rfl, one_le_two, le_rfl⟩

/-- H2-U10b witness history: ONE interior node over `F = ZMod 2`, a₀ = 2 —
    every `EHist` carrier law holds, and every `InteriorChain` clause holds. -/
noncomputable def interiorEHist : DictIII.EHist 2 (ZMod 2) where
  base := ⊤
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 2
  ha0 := one_le_two
  nodes := [interiorNode]
  fld := fun _ => ⊤
  psihat := fun _ => Polynomial.X + 1
  hpsihat := fun _ => probePsihat_laws

/-- The witness node list, read back (definitional). -/
theorem interiorEHist_nodes : interiorEHist.nodes = [interiorNode] := rfl

/-- The witness chain has an ACTUAL slope: `Theta`'s slope list is `[(1, 1)]`
    (the node is continuing, so `continuingPart` keeps it) — the exact point
    where the F-4 world (`slopes = []`) is escaped. -/
theorem interiorTheta_slopes :
    (DictIII.Theta interiorEHist).slopes = [(1, 1)] := rfl

/-- H2-U10b guard check: the witness IS an interior chain. -/
theorem interiorEHist_interior : DictIII.InteriorChain interiorEHist := by
  refine ⟨le_rfl, ?_⟩
  intro i ν hν
  rcases i with _ | i
  · rw [interiorEHist_nodes] at hν
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hν
    subst hν
    refine ⟨by simp [interiorNode], ?_⟩
    intro gμ hgμ
    simp only [interiorNode, Option.mem_def, Option.some.injEq] at hgμ
    subst hgμ
    exact le_rfl
  · rw [interiorEHist_nodes] at hν
    simp at hν

/-- H2-U10b guard check, negative face: the U7/F-4 all-terminal witness is NOT
    interior — the guard excludes exactly the refuting world. -/
theorem duplicateEHist_not_interior :
    ¬ DictIII.InteriorChain duplicateEHist := fun h =>
  (h.2 0 probeNode (by simp [duplicateEHist_nodes])).1 rfl

/-- H2-U10b witness side: the (c1)-shape datum matching `interiorNode`
    fieldwise (`SideDatum` is law-free data). -/
def interiorSide : DictIII.SideDatum where
  e := 1
  h := 1
  ℓ := 2
  s := 0
  u := 0
  isNegInfty := false

/-- H2-U10b witness data: ONE principal side at every level (only level 0 is
    ever requested), residual order 2 (= the node's μ), residual degree 2
    (= the side's ℓ), root order 2 (= a₀). -/
noncomputable def interiorData :
    DictIII.GMNData (Polynomial.X : Polynomial ℤ_[2])
      (DictIII.Theta interiorEHist) where
  principalSides := fun _ => [interiorSide]
  residualOrder := fun _ => 2
  residualDegree := fun _ => 2
  rootOrder := 2

/-- H2-U10b witness reader: reads `interiorSide` at level 0 (where the slope
    is requested), `none` above; every reader law is proved. -/
noncomputable def interiorReader :
    DictIII.GMNReader (Polynomial.X : Polynomial ℤ_[2])
      (DictIII.Theta interiorEHist) interiorData where
  side := fun i => if i = 0 then some interiorSide else none
  side_spec := by
    intro i S
    unfold DictIII.HasRequestedSlope DictIII.requestedSlope
    rcases i with _ | i
    · rw [interiorTheta_slopes]
      constructor
      · intro hS
        have hS' : interiorSide = S := by simpa using hS
        subst hS'
        exact ⟨List.mem_singleton.mpr rfl, rfl⟩
      · rintro ⟨hmem, -⟩
        have hS' : S = interiorSide := by simpa [interiorData] using hmem
        subst hS'
        rfl
    · rw [interiorTheta_slopes]
      simp [interiorData]
  side_unique := by
    intro i S T hS hT _ _
    have h1 : S = interiorSide := by simpa [interiorData] using hS
    have h2 : T = interiorSide := by simpa [interiorData] using hT
    rw [h1, h2]
  resOrd := fun _ => 2
  resOrd_spec := fun _ => rfl
  rootOrd := 2
  rootOrd_spec := rfl
  resDeg_eq_sideDeg := by
    intro i S h
    rcases i with _ | i
    · have h' : interiorSide = S := by simpa using h
      subst h'
      rfl
    · simp at h

/-- H2-U10b witness step: `ConsF` HOLDS at the interior witness — the root
    orders match (2 = 2) and the single continuing node is read as
    `interiorSide` with matching fields and residual order. -/
theorem consF_interior :
    DictIII.ConsF (Polynomial.X : Polynomial ℤ_[2]) interiorEHist
      interiorData interiorReader := by
  refine ⟨rfl, ?_⟩
  intro i ν hν
  have hnodes : interiorEHist.continuingPart.nodes = [interiorNode] := rfl
  rw [hnodes] at hν
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hν
    subst hν
    refine ⟨interiorSide, rfl, rfl, ?_⟩
    intro g μ hgμ
    simp only [interiorNode, Option.some.injEq, Prod.mk.injEq] at hgμ
    exact hgμ.2
  · simp at hν

/-- **H2-U10b THE GATE (the mandatory non-vacuity witness, PASSED)**: the
    restated guarded `childDetermined` row is realized NON-VACUOUSLY at the
    interior witness — at level 0 the ∃! holds with the ACTUAL side
    `interiorSide` (compare PROBE F-4, where `side ≡ none` was forced).
    Together with `interiorEHist_interior` and `consF_interior` this
    instantiates every hypothesis of the guarded row at an interior instance
    with an actual slope. -/
theorem interior_childDetermined_gate :
    ∃! S, interiorReader.side 0 = some S ∧
      S ∈ interiorData.principalSides 0 ∧
      DictIII.HasRequestedSlope (DictIII.Theta interiorEHist) 0 S := by
  refine ⟨interiorSide, ⟨rfl, List.mem_singleton.mpr rfl, rfl⟩, ?_⟩
  rintro T ⟨hT, -, -⟩
  exact (Option.some.inj hT).symm

/-- H2-U10b consistency display: the guarded row's full instance at the
    witness, fired through the RESTATED field shape (what `cu1_stepPair_ge2`
    consumes, specialized) — kept as a compiled unit test of the new field
    against its consumer. -/
theorem interior_childDetermined_instance
    (hF : DictIII.FRESH 2 (ZMod 2)) :
    ∃! S, interiorReader.side 0 = some S ∧
      S ∈ interiorData.principalSides 0 ∧
      DictIII.HasRequestedSlope (DictIII.Theta interiorEHist) 0 S :=
  hF.childDetermined (ν := interiorNode) interiorEHist_interior consF_interior
    (by simp [interiorEHist_nodes])

end LeanUrat.Scaffold.HDischarge.H2

-- Footprint audit (unit H2-U7 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.HDischarge.H2.dictFresh_junctionPin_trivial
#print axioms LeanUrat.Scaffold.HDischarge.H2.probe_not_FRESH
-- Footprint audit (H2-U10 gate probe F-4): expect Lean core only.
#print axioms LeanUrat.Scaffold.HDischarge.H2.probe_restated_childDetermined_refuted
-- Footprint audit (H2-U10b interior non-vacuity gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.HDischarge.H2.interiorEHist_interior
#print axioms LeanUrat.Scaffold.HDischarge.H2.duplicateEHist_not_interior
#print axioms LeanUrat.Scaffold.HDischarge.H2.consF_interior
#print axioms LeanUrat.Scaffold.HDischarge.H2.interior_childDetermined_gate
#print axioms LeanUrat.Scaffold.HDischarge.H2.interior_childDetermined_instance
