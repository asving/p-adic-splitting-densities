/-
DEC1 elaboration check — node-plan signatures for the GC-13 PARTITION-RECORD INSTANCE
BRIDGE (`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md`).

Signature layer ONLY. Each planned node's deliverable is pinned as a named `Prop` target
(or a parameterized spec) over the LANDED E.57 schema objects
(`Uniformity/ChapE/E57p.lean`: `PartitionLeg`, `block_split_of_partitionLeg`,
`E57pCert.flatCarrier`). No `sorry`, no `axiom`, no `unsafe`. Two term-level checks are
included because they are the plan's load-bearing joints:

* `legOfSpecs` — the N3/N4 field-group specs are JOINTLY EXACTLY `PartitionLeg`'s
  constructor (the decomposition is lossless: no obligation hides between the
  field-group nodes and the assembly node);
* the final `example` — the assembly node's firing route type-checks verbatim against
  the landed `block_split_of_partitionLeg`.
-/
import Uniformity.ChapE.E57p

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

namespace DEC1Check

open Polynomial E57pCert

/-! ### The SPLIT row's class addresses (labels = the factors' digits `1`, `−1`) -/

/-- class address of the factor `X + 1` (side `(1,1)`, linear label `1`, weight entry `1`). -/
def a1 : ClassIx ℚ := ((1, 1), Sum.inl ((1 : ℚ), 1))

/-- class address of the factor `X − 1` (side `(1,1)`, linear label `−1`, weight entry `1`). -/
def a2 : ClassIx ℚ := ((1, 1), Sum.inl ((-1 : ℚ), 1))

/-- the split row's two-class ledger. -/
def splitCls : Finset (ClassIx ℚ) := {a1, a2}

/-! ### Node targets -/

/-- **DEC1-N1 target** — the PARENT row `mixBlock`/`mixIface`: the two-linear-class parent
`F = X² − 1 = (X+1)(X−1)` over the landed flat carrier (`D = 1`), the C.63
separable-side shape (`s` = two residual labels, class weight `D·ℓ·deg r = 1` each) —
the om4 countermodel's interface shape at a LEGAL (separable-shadow) polynomial. -/
def N1_target : Prop :=
  ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
    B.Φ = X ∧ B.F = X ^ 2 - 1 ∧ B.μ = 2 ∧ B.T = 0 ∧
    I.sides = {(1, 1)} ∧ I.len (1, 1) = 2 ∧
    I.linFac (1, 1) = {((1 : ℚ), 1), ((-1 : ℚ), 1)} ∧ I.hiFac (1, 1) = 0 ∧
    I.classCount (1, 1) ((1 : ℚ), 1) = 1 ∧ I.classCount (1, 1) ((-1 : ℚ), 1) = 1

/-- **DEC1-N2 target** — the SECOND child `pureBlock₂`/`pureIface₂` (`F = X − 1`, label `−1`;
the label-`1` child is the landed `E57pCert.pureBlock`/`pureIface`, reused verbatim). -/
def N2_target : Prop :=
  ∃ (B : BlockData flatCarrier) (J : RungInterface.{0, 0, 0} flatCarrier B),
    B.Φ = X ∧ B.F = X - 1 ∧ B.μ = 1 ∧ B.T = 0 ∧
    J.sides = {(1, 1)} ∧ J.linFac (1, 1) = {((-1 : ℚ), 1)} ∧ J.hiFac (1, 1) = 0

/-- **DEC1-N3 spec** — the ledger/product/disjointness FIELD-GROUP at a row `(I, cls, blk)`:
verbatim the `hclsLin`/`hclsHi`/`hprod`/`hdisj` obligations of `PartitionLeg`
(C-record correspondence: C.63's `s : Finset`, `g = ∏ r ∈ s, Fac r`, and coprimality of
the distinct monic irreducible `Fac r` over `Frac(O)`). -/
def N3_spec {B : BlockData flatCarrier} (I : RungInterface.{0, 0, 0} flatCarrier B)
    (cls : Finset (ClassIx ℚ))
    (blk : ClassIx ℚ → Σ B' : BlockData flatCarrier,
      RungInterface.{0, 0, 0} flatCarrier B') : Prop :=
  (∀ p q, ((p, Sum.inl q) ∈ cls) ↔ (p ∈ I.sides ∧ q ∈ I.linFac p)) ∧
  (∀ p q, ((p, Sum.inr q) ∈ cls) ↔ (p ∈ I.sides ∧ q ∈ I.hiFac p)) ∧
  (B.F = ∏ c ∈ cls, (blk c).1.F) ∧
  (∀ c ∈ cls, ∀ c' ∈ cls, c ≠ c' →
    IsCoprime ((blk c).1.F.map (algebraMap ℤ (FractionRing ℤ)))
      ((blk c').1.F.map (algebraMap ℤ (FractionRing ℤ))))

/-- **DEC1-N4 spec** — the degree/purity/threshold FIELD-GROUP at a row `(I, cls, blk)`:
verbatim the `hdeg`/`hone`/`hpureLin`/`hpureHi`/`hthr` obligations of `PartitionLeg`
(C-record correspondence: C.63's degree law `deg (Fac r) = (e₁f₁)·ℓ·deg r` read as
`classWeight`, and the one-entry `typeOf` singleton read as one-sidedness + purity). -/
def N4_spec {B : BlockData flatCarrier} (I : RungInterface.{0, 0, 0} flatCarrier B)
    (cls : Finset (ClassIx ℚ))
    (blk : ClassIx ℚ → Σ B' : BlockData flatCarrier,
      RungInterface.{0, 0, 0} flatCarrier B') : Prop :=
  (∀ c ∈ cls, (blk c).1.F.natDegree = classWeight I c) ∧
  (∀ c ∈ cls, (blk c).2.sides = {c.1}) ∧
  (∀ p q, (p, Sum.inl q) ∈ cls →
    ∃ k : ℕ, 1 ≤ k ∧ (blk (p, Sum.inl q)).2.linFac p = {(q.1, k)} ∧
      (blk (p, Sum.inl q)).2.hiFac p = 0) ∧
  (∀ p q, (p, Sum.inr q) ∈ cls →
    ∃ k : ℕ, 1 ≤ k ∧ 2 ≤ q.1 ∧ (blk (p, Sum.inr q)).2.hiFac p = {(q.1, k)} ∧
      (blk (p, Sum.inr q)).2.linFac p = 0) ∧
  (∀ c ∈ cls, (blk c).1.T = B.T)

/-- **DEC1-N5 target** — assembly + firing at the split row: a genuinely TWO-class parent
(the om4 countermodel's SHAPE, made legal) with the typed leg inhabited and the suite
assembled through the landed `block_split_of_partitionLeg`. -/
def N5_target : Prop :=
  ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
    B.F = X ^ 2 - 1 ∧ I.linFac (1, 1) = {((1 : ℚ), 1), ((-1 : ℚ), 1)} ∧
    Nonempty (PartitionLeg I) ∧ Nonempty (BlockSuite I)

/-- **DEC1-N6 target** — the HI row `hiBlock`/`hiIface`: one higher class of degree 2
(`F = X² + X + 1`, the inert shape; `hiFac = {(2,1)}`, class weight `D·ℓ·2 = 2`),
exercising the `hclsHi`/`hpureHi` branch no landed gate touches. -/
def N6_target : Prop :=
  ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
    B.Φ = X ∧ B.F = X ^ 2 + X + 1 ∧ B.μ = 2 ∧ B.T = 0 ∧
    I.sides = {(1, 1)} ∧ I.linFac (1, 1) = 0 ∧ I.hiFac (1, 1) = {(2, 1)} ∧
    I.classCountHi (1, 1) (2, 1) = 2

/-- **DEC1-N7 target** — assembly + firing at the hi row. -/
def N7_target : Prop :=
  ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
    B.F = X ^ 2 + X + 1 ∧ I.linFac (1, 1) = 0 ∧ I.hiFac (1, 1) = {(2, 1)} ∧
    Nonempty (PartitionLeg I) ∧ Nonempty (BlockSuite I)

/-! ### The plan's two load-bearing joints, term-checked -/

/-- N3 + N4 are JOINTLY EXACTLY `PartitionLeg`'s constructor: the decomposition into
field-group nodes is lossless — no leg obligation hides outside the two specs. -/
def legOfSpecs {B : BlockData flatCarrier} (I : RungInterface.{0, 0, 0} flatCarrier B)
    (cls : Finset (ClassIx ℚ))
    (blk : ClassIx ℚ → Σ B' : BlockData flatCarrier,
      RungInterface.{0, 0, 0} flatCarrier B')
    (h3 : N3_spec I cls blk) (h4 : N4_spec I cls blk) : PartitionLeg I :=
  ⟨cls, h3.1, h3.2.1, blk, h3.2.2.1, h3.2.2.2,
    h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2⟩

/-- the assembly nodes' firing route, type-checked verbatim against the landed theorem —
this is the exact term N5/N7 produce once `P` is the constructed leg. -/
example {B : BlockData flatCarrier} (I : RungInterface.{0, 0, 0} flatCarrier B)
    (P : PartitionLeg I) : Nonempty (BlockSuite I) :=
  block_split_of_partitionLeg I P.supplies_hblocks P.supplies_hblocksHi ⟨P⟩

end DEC1Check

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — the check file itself adds no axiom) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.DEC1Check.splitCls
#print axioms Uniformity.Density.Ladder.DEC1Check.N1_target
#print axioms Uniformity.Density.Ladder.DEC1Check.N3_spec
#print axioms Uniformity.Density.Ladder.DEC1Check.N4_spec
#print axioms Uniformity.Density.Ladder.DEC1Check.N5_target
#print axioms Uniformity.Density.Ladder.DEC1Check.N7_target
#print axioms Uniformity.Density.Ladder.DEC1Check.legOfSpecs

end AxCheck
