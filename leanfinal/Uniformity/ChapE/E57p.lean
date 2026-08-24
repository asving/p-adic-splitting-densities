/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E13
import Uniformity.ChapE.E39a
import Uniformity.ChapE.E59
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Uniformity.ChapE.E57p — the TYPED partition leg for NODE E.57 (`block_split`), and the
# schema assembly it makes provable

**Chapter E, NODE E.57 [theorem, HARD] — the partition-leg unit** (the A-E.6 mandate's
"GC-13 types `hpart`" half, executed at the SCHEMA level). This file does NOT land `E57.lean`
and does NOT declare `block_split` (A-E.6: *"`leanfinal/Uniformity/ChapE/E57.lean` does not
exist and must not be created before GC-13"*). What it lands:

1. **`PartitionLeg I`** — the typed carrier for E.57's `hpart : True` socket: the
   product/disjointness/per-block-purity data that `EFF.HE7.96`(a)'s partition argument
   supplies and that chapter C's partition record carries at instances
   (C.63 `classSize_separable` / C.69 `ClassSizeSupplyData.separable_side`, landed at
   `Uniformity/ChapC/C140defs.lean` — the E-shadow ↔ C-record correspondence is spelled
   field by field below).
2. **`PartitionLeg.toBlockSuite`** — E.57's schema content at the typed socket: the leg
   ASSEMBLES the full `BlockSuite I` record (A-E.6's re-signed conclusion). With it,
3. **`block_split_of_partitionLeg`** — the corrected E.57 statement, binders `hblocks`/
   `hblocksHi` byte-preserved from the committed signature and `hpart` typed at
   `Nonempty (PartitionLeg I)` — **PROVED**. This is the landing shape the re-sign diff
   in `runs/wave-b/verdict_E57.md` proposes for `Leanspec.ChapE`'s `BlockSplitTarget`.
4. The blueprint PROOF map's derivable clauses: (1) the carrier legs are SUBSUMED
   (`supplies_hblocks`/`supplies_hblocksHi`); (iii) side-length additivity
   (`classWeight_side_sum`, `PartitionLeg.side_degree_sum`); (iv) the per-block trichotomy
   gate via E.59 (`BlockSuite.mu_ge_four_of_hi_jump`/`_lin_jump`); the A-E.6 strength-ledger
   claim (`BlockSuite.committed_shadow`); and **defect E-D15's divisibility, discharged at
   the typed socket** (`PartitionLeg.dvd_classCount_lin`/`_hi`).

## The adjudication this file rests on (all three machine-checked, re-run green 2026-08-24)

* The COMMITTED conclusion was a theorem of Lean core (`blocks := [B.F]`):
  `leanfinal/Uniformity/ChapE/E57_VACUITY.lean.txt`, `block_split_IS_A_THEOREM` +
  `socket_typing_is_orthogonal` (no typing of `hpart` could rescue the committed shape).
* The A-E.6 RE-SIGNED conclusion `Nonempty (BlockSuite I)` is FALSE at `hpart : True`:
  `verification/om4_resign_nontriviality.lean` Part 4, `e57_resigned_false_at_untyped_socket`
  (legal instance `F = X²`, one side, two unit-weight linear classes — `hdisj` would need two
  coprime degree-1 factors of `X²`).
* Hence the socket MUST be typed before assertion. The gate below machine-checks that
  `PartitionLeg` is exactly the repair: at the SAME countermodel shape the typed leg is
  EMPTY (`E57pCert.dup_partitionLeg_empty`), and at a legal pure instance it is INHABITED
  and the assembly fires end-to-end (`E57pCert.pure` gate).

## Field ↔ source ↔ C-record correspondence (the leg's faithfulness ledger)

| `PartitionLeg` field | `EFF.HE7.96`(a) (= ANNEX-LEMMA HE7-13′(a)) | C-record carrier (C.63/C.69) |
|---|---|---|
| `cls`, `hclsLin`, `hclsHi` | the classes are INDEXED by `(λ, r)` | `s : Finset …` (C.63's index) |
| `blk` | *"each `C_{λ,r}` is the root set of a monic block factor `f_{λ,r}`"*, with its OWN polygon read | `Fac : … → Polynomial O` + the per-factor `typeOf` read |
| `hprod` | *"`f_S = Π_{(λ,r)} f_{λ,r}`"* | `g = ∏ r ∈ s, Fac r` |
| `hdisj` | *"they partition the roots … the label's factor is the minimal polynomial"* | distinct monic irreducible factors are coprime over `Frac(O)` |
| `hdeg` | `|C_{λ,r}| = D″·L_{λ,r}` (the class weight IS the factor degree) | `(Fac r).natDegree = (e₁f₁)·ℓ·deg r` |
| `hone` | *"the polygon of `f_{λ,r}` … is the SINGLE side of slope λ"* | `typeOf (Fac r) = ⟨{(e₁ℓ, f₁·deg r)}⟩` (one entry) |
| `hpureLin`/`hpureHi` | *"the residual of `f_{λ,r}` is `c·r^k` … a single irreducible power"* | same `typeOf` singleton, pure in the parent's `r` |
| `hthr` | *"the SAME `T₂`; the blocks are read at the same `Ψ̃`"* | the level frame `L` is fixed |

The instance bridge (C-record ⇒ this E-shadow leg at each instantiated row) is an
E.22/E.23-genre INSTANCE obligation, deliberately not attempted here — this file owns the
schema layer only.

## Honest disclosures

* **The leg is data the schema cannot produce** (that is the point): `blk`'s per-class
  interfaces carry the analytic content of blueprint PROOF-map item 2 (HE7-9/HE7-10 re-run
  on `f_C`), which is C-supplied. Nothing here discharges E.57's node — the assembly theorem
  is E.57's SCHEMA content, conditional on the typed leg exactly as the corrected signature
  displays.
* **`hclsLin`/`hclsHi` enumerate classes as a `Finset`** (matching C.63's `s : Finset`),
  so a degenerate parent whose `linFac`/`hiFac` MULTISET repeats an entry contributes that
  class once to the product. The source has distinct classes (they are indexed by `(λ, r)`);
  the E.12 numerical shadow does not enforce distinctness, and at a repeating parent the
  leg's `hprod` reads the deduplicated product. `BlockSuite`'s membership-based cover fields
  are assembled correctly either way.
* **`hpureHi` carries `2 ≤ q.1`** (the parent's higher classes really have degree ≥ 2 —
  E.12's D-E2 comment says so but no `RungInterface` field enforces it; `BlockSuite.hpure`'s
  hi branch demands it, so the leg must supply it). C-side this is `1 < deg r` for a
  non-linear residual, free at instances.
* **E-D15 is discharged at the typed socket, not repaired in E.12**: `hforce`'s `≤`-shadow
  stays as signed; the leg's `hdeg` + each block's own `hresdeg`/`hlen_sum` force the source
  divisibility `C.D·ℓ·deg q ∣ classCount p q` (`dvd_classCount_lin`/`_hi` below), which is
  A-E.6's predicted cure (*"let the typed `hpart` carry C.63's degree law … which supplies
  it exactly"*).

DEPENDS: E.10 (`SlotCarrier`), E.11 (`BlockData`), E.12 (`RungInterface`, three-universe
convention), E.13 (`BlockData.natDegree_F` — monicity/degree of a block's `F`),
E.39a (`BlockSuite`), E.59 (`block_jump_gate`) · mathlib `Finset.prod_map_toList`,
`List.Nodup.pairwise_of_forall_ne`, `Polynomial.natDegree_prod_of_monic`, `dvd_prime_pow`.

SOURCE: `EFF.HE7.96` (ANNEX-LEMMA HE7-13′(a) + proof, via the A-E.6 adjudication table);
`EFF.HE7.05` (separability convention — enters through `hdisj`, see A-E.6 disclosure D1);
blueprint amendment A-E.6 (the re-sign this types).

TEETH: the positive/negative gate pair below (`E57pCert`), mirroring A-E.2/A-E.6's
non-triviality standard INSIDE the landed file.

ENVIRONMENT: ENV-E2 (+ `[IsDomain O]` where degrees of products are read).

## Status

Sorry-free, axiom-free, `unsafe`-free: every declaration reports at most the Lean-core
triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial

-- E.12's three universes, bound explicitly (A-E.1/E-D6): `uW` occurs only inside
-- `RungInterface`'s body, so anything quantifying over an interface must name it.
universe uO uK uW

/-- A **class address** in a parent interface: a side `p : ℕ × ℕ` paired with either a
linear residual class `(root, mult) : K × ℕ` or a higher residual class
`(deg, mult) : ℕ × ℕ` (E.12's `linFac`/`hiFac` entries). -/
abbrev ClassIx (K : Type uK) : Type uK := (ℕ × ℕ) × ((K × ℕ) ⊕ (ℕ × ℕ))

/-- The parent's recorded **class weight** at a class address (E.12's `classCount` /
`classCountHi`, merged over the address sum). -/
def classWeight {O : Type uO} [CommRing O] {K : Type uK} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) (c : ClassIx K) : ℕ :=
  match c.2 with
  | Sum.inl q => I.classCount c.1 q
  | Sum.inr q => I.classCountHi c.1 q

/-- **The TYPED partition leg for NODE E.57** — what `hpart : True` was a placeholder for
(`EFF.HE7.96`(a)'s partition/product/disjointness content, C-supplied at instances through
C.63/C.69; see the file docstring's correspondence table). Over the parent interface `I`:
a `Finset` ledger `cls` enumerating exactly the parent's `(side, class)` addresses, and a
block assignment `blk` giving each class its own `BlockData`/`RungInterface` pair over the
SAME carrier, such that the class factors are a product/coprime decomposition of `B.F` of
the recorded weights, each block one-sided at its parent side, pure in its parent class,
at the inherited threshold. -/
structure PartitionLeg {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) where
  /-- the class ledger: exactly the parent's class addresses, enumerated without repetition. -/
  cls : Finset (ClassIx K)
  hclsLin : ∀ p q, ((p, Sum.inl q) ∈ cls) ↔ (p ∈ I.sides ∧ q ∈ I.linFac p)
  hclsHi : ∀ p q, ((p, Sum.inr q) ∈ cls) ↔ (p ∈ I.sides ∧ q ∈ I.hiFac p)
  /-- the block assignment: each class's monic factor with its OWN development and its OWN
  interface (blueprint PROOF-map item 2's output, C-supplied). -/
  blk : ClassIx K → Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'
  /-- the PRODUCT law (`(SIDE-PROD)`·`(LABEL-PROD)` at the mixed node): the class factors
  multiply to `B.F`. -/
  hprod : B.F = ∏ c ∈ cls, (blk c).1.F
  /-- the DISJOINTNESS law (*"they partition the roots"*): distinct classes get factors
  coprime over `Frac(O)`. -/
  hdisj : ∀ c ∈ cls, ∀ c' ∈ cls, c ≠ c' →
    IsCoprime ((blk c).1.F.map (algebraMap O (FractionRing O)))
      ((blk c').1.F.map (algebraMap O (FractionRing O)))
  /-- per class: the factor's degree is the parent's recorded class weight
  (`|C_{λ,r}| = D″·L_{λ,r}` read as a degree). -/
  hdeg : ∀ c ∈ cls, (blk c).1.F.natDegree = classWeight I c
  /-- per class: the block is one-sided AT THE PARENT'S OWN side. -/
  hone : ∀ c ∈ cls, (blk c).2.sides = {c.1}
  /-- per linear class: the block's residual is pure in the PARENT's class, of some OWN
  multiplicity `k ≥ 1` (`EFF.T2.17`'s `k`/`m` non-import: `k` is NOT tied to `q.2`). -/
  hpureLin : ∀ p q, (p, Sum.inl q) ∈ cls →
    ∃ k : ℕ, 1 ≤ k ∧ (blk (p, Sum.inl q)).2.linFac p = {(q.1, k)} ∧
      (blk (p, Sum.inl q)).2.hiFac p = 0
  /-- per higher class: same, plus the parent class's degree really is ≥ 2 (D-E2). -/
  hpureHi : ∀ p q, (p, Sum.inr q) ∈ cls →
    ∃ k : ℕ, 1 ≤ k ∧ 2 ≤ q.1 ∧ (blk (p, Sum.inr q)).2.hiFac p = {(q.1, k)} ∧
      (blk (p, Sum.inr q)).2.linFac p = 0
  /-- inherited continuation: the threshold does not move (*"the SAME `T₂`"*). -/
  hthr : ∀ c ∈ cls, (blk c).1.T = B.T

/-! ## The assembly: E.57's schema content at the typed socket

Blueprint PROOF map, executed at the numerical shadow: item 1 (per-class monic divisor) is
`supplies_hblocks` below; item 2 (single side + pure residual per block) is the leg's data;
item 3 (length additivity) is `side_degree_sum`; item 4 (the trichotomy gate) is
`mu_ge_four_of_*_jump` via E.59. The record itself: -/

/-- **The E.57 assembly**: a typed partition leg assembles the full `BlockSuite I` record
(A-E.6's re-signed conclusion). `[IsDomain O]` (E.57's own binder) enters only through
E.13's `natDegree_F`, which supplies each factor's monicity for the degree sum. -/
noncomputable def PartitionLeg.toBlockSuite {O : Type uO} [CommRing O] [IsDomain O]
    {K : Type uK} [Field K] {C : SlotCarrier O K} {B : BlockData C}
    {I : RungInterface.{uO, uK, uW} C B} (P : PartitionLeg I) : BlockSuite I where
  blocks := P.cls.toList.map P.blk
  hprod := by
    rw [List.map_map, Finset.prod_map_toList]
    exact P.hprod
  hdisj := by
    rw [List.pairwise_map]
    refine (Finset.nodup_toList P.cls).pairwise_of_forall_ne ?_
    intro a ha b hb hab
    exact P.hdisj a (Finset.mem_toList.mp ha) b (Finset.mem_toList.mp hb) hab
  hdegsum := by
    rw [List.map_map, Finset.sum_map_toList, P.hprod,
      Polynomial.natDegree_prod_of_monic _ _ (fun c _ => ((P.blk c).1.natDegree_F).2)]
    rfl
  hone := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact ⟨c.1, P.hone c (Finset.mem_toList.mp hc)⟩
  hpure := by
    intro x hx p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hcm : c ∈ P.cls := Finset.mem_toList.mp hc
    have hs := P.hone c hcm
    rw [hs, Finset.mem_singleton] at hp
    subst hp
    obtain ⟨p', q | q⟩ := c
    · obtain ⟨k, hk, hl, hh⟩ := P.hpureLin p' q hcm
      exact Or.inl ⟨q.1, k, hk, hl, hh⟩
    · obtain ⟨k, hk, hd2, hh, hl⟩ := P.hpureHi p' q hcm
      exact Or.inr ⟨q.1, k, hk, hd2, hh, hl⟩
  hcoverLin := by
    intro p hp q hq
    have hc : ((p, Sum.inl q) : ClassIx K) ∈ P.cls := (P.hclsLin p q).mpr ⟨hp, hq⟩
    refine ⟨P.blk (p, Sum.inl q), List.mem_map.mpr ⟨_, Finset.mem_toList.mpr hc, rfl⟩,
      P.hone _ hc, ?_, P.hdeg _ hc⟩
    obtain ⟨k, hk, hl, -⟩ := P.hpureLin p q hc
    exact ⟨k, hk, hl⟩
  hcoverHi := by
    intro p hp q hq
    have hc : ((p, Sum.inr q) : ClassIx K) ∈ P.cls := (P.hclsHi p q).mpr ⟨hp, hq⟩
    refine ⟨P.blk (p, Sum.inr q), List.mem_map.mpr ⟨_, Finset.mem_toList.mpr hc, rfl⟩,
      P.hone _ hc, ?_, P.hdeg _ hc⟩
    obtain ⟨k, hk, -, hh, -⟩ := P.hpureHi p q hc
    exact ⟨k, hk, hh⟩
  hcount := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hcm : c ∈ P.cls := Finset.mem_toList.mp hc
    obtain ⟨p, q | q⟩ := c
    · obtain ⟨hp, hq⟩ := (P.hclsLin p q).mp hcm
      exact ⟨p, hp, Or.inl ⟨q, hq, P.hdeg _ hcm⟩⟩
    · obtain ⟨hp, hq⟩ := (P.hclsHi p q).mp hcm
      exact ⟨p, hp, Or.inr ⟨q, hq, P.hdeg _ hcm⟩⟩
  hthr := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact P.hthr c (Finset.mem_toList.mp hc)

-- The two carrier-leg binders are byte-preserved from the committed signature (A-E.6:
-- "Not touched") and are SUBSUMED by the typed leg (`supplies_hblocks` below), so the
-- assembly does not consume them; the linter is silenced exactly as in the signed stub.
set_option linter.unusedVariables false in
/-- **The corrected E.57 statement, PROVED at the schema level** — the landing shape for the
node once the orchestrator enacts the re-sign (the declaration keeping the blueprint name
`block_split` is GC-13's; this file deliberately does not take it). Binders `hblocks`,
`hblocksHi` byte-preserved from the committed signature; `hpart` typed at
`Nonempty (PartitionLeg I)` per the A-E.6 adjudication. -/
theorem block_split_of_partitionLeg {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK}
    [Field K] {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B)
    (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q)
    (hpart : Nonempty (PartitionLeg I)) :
    Nonempty (BlockSuite I) :=
  hpart.elim fun P => ⟨P.toBlockSuite⟩

/-! ## Blueprint PROOF-map item 1: the carrier legs are subsumed by the typed leg -/

/-- The typed leg supplies `hblocks` (per linear class, a monic divisor of `B.F` of the
recorded weight): `Fpq := (blk c).1.F`, monic by E.13, dividing through `hprod`. -/
theorem PartitionLeg.supplies_hblocks {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK}
    [Field K] {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (P : PartitionLeg I) :
    ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q := by
  intro p hp q hq
  have hc : ((p, Sum.inl q) : ClassIx K) ∈ P.cls := (P.hclsLin p q).mpr ⟨hp, hq⟩
  exact ⟨(P.blk (p, Sum.inl q)).1.F, ((P.blk (p, Sum.inl q)).1.natDegree_F).2,
    P.hprod ▸ Finset.dvd_prod_of_mem _ hc, P.hdeg _ hc⟩

/-- The typed leg supplies `hblocksHi` (per higher class). -/
theorem PartitionLeg.supplies_hblocksHi {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK}
    [Field K] {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (P : PartitionLeg I) :
    ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q := by
  intro p hp q hq
  have hc : ((p, Sum.inr q) : ClassIx K) ∈ P.cls := (P.hclsHi p q).mpr ⟨hp, hq⟩
  exact ⟨(P.blk (p, Sum.inr q)).1.F, ((P.blk (p, Sum.inr q)).1.natDegree_F).2,
    P.hprod ▸ Finset.dvd_prod_of_mem _ hc, P.hdeg _ hc⟩

/-! ## Blueprint STATEMENT clause (iii): side-length additivity — a CONSEQUENCE, per the
A-E.6 adjudication (not a record field: it is `hexhaust` + `haccount` read through `hdeg`) -/

/-- (iii) at the parent, weight form: on each side the class weights sum to `D · len`
(the `D`-scaled `Σ_q L_{p,q} = len p`). Pure E.12 arithmetic. -/
theorem classWeight_side_sum {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) :
    ∀ p ∈ I.sides,
      Multiset.sum ((I.linFac p).map (I.classCount p))
        + Multiset.sum ((I.hiFac p).map (I.classCountHi p)) = C.D * I.len p := by
  intro p hp
  rw [I.hexhaust p hp, I.haccount p hp]

/-- (iii) at the blocks: on each side the assigned factors' degrees sum to `D · len`
(*"Side lengths add"* — `hdeg` composed with `classWeight_side_sum`). -/
theorem PartitionLeg.side_degree_sum {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (P : PartitionLeg I) :
    ∀ p ∈ I.sides,
      Multiset.sum ((I.linFac p).map fun q => (P.blk (p, Sum.inl q)).1.F.natDegree)
        + Multiset.sum ((I.hiFac p).map fun q => (P.blk (p, Sum.inr q)).1.F.natDegree)
      = C.D * I.len p := by
  intro p hp
  have h1 : (I.linFac p).map (fun q => (P.blk (p, Sum.inl q)).1.F.natDegree)
      = (I.linFac p).map (I.classCount p) :=
    Multiset.map_congr rfl fun q hq => P.hdeg _ ((P.hclsLin p q).mpr ⟨hp, hq⟩)
  have h2 : (I.hiFac p).map (fun q => (P.blk (p, Sum.inr q)).1.F.natDegree)
      = (I.hiFac p).map (I.classCountHi p) :=
    Multiset.map_congr rfl fun q hq => P.hdeg _ ((P.hclsHi p q).mpr ⟨hp, hq⟩)
  rw [h1, h2]
  exact classWeight_side_sum I p hp

/-! ## Blueprint STATEMENT clause (iv): the per-block trichotomy gate, via E.59 — CONSUMED
from the record, per the A-E.6 adjudication -/

/-- Mass read of a one-sided block that is pure in a higher class: `μ′ = k·(ℓ·d)`
(`hresdeg` + `hlen_sum` at the block's own interface). -/
theorem one_side_pure_hi_mass {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B' : BlockData C} (J : RungInterface.{uO, uK, uW} C B')
    {p : ℕ × ℕ} (hone : J.sides = {p}) {d k : ℕ}
    (hhi : J.hiFac p = {(d, k)}) (hlin : J.linFac p = 0) :
    B'.μ = k * (p.2 * d) := by
  have hp : p ∈ J.sides := by rw [hone]; exact Finset.mem_singleton_self p
  have hres := J.hresdeg p hp
  rw [hlin, hhi] at hres
  simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.map_singleton,
    Multiset.sum_singleton, zero_add] at hres
  have hsum := J.hlen_sum
  rw [hone, Finset.sum_singleton] at hsum
  rw [← hsum, ← hres]
  ring

/-- Mass read of a one-sided block that is pure in a linear class: `μ′ = k·ℓ`. -/
theorem one_side_pure_lin_mass {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B' : BlockData C} (J : RungInterface.{uO, uK, uW} C B')
    {p : ℕ × ℕ} (hone : J.sides = {p}) {s : K} {k : ℕ}
    (hlin : J.linFac p = {(s, k)}) (hhi : J.hiFac p = 0) :
    B'.μ = k * p.2 := by
  have hp : p ∈ J.sides := by rw [hone]; exact Finset.mem_singleton_self p
  have hres := J.hresdeg p hp
  rw [hlin, hhi] at hres
  simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.map_singleton,
    Multiset.sum_singleton, add_zero] at hres
  have hsum := J.hlen_sum
  rw [hone, Finset.sum_singleton] at hsum
  rw [← hsum, ← hres]
  ring

/-- (iv), hi branch: a suite block pure in a higher class (`d ≥ 2`) with a JUMP
(`k ≥ 2`) has mass `μ ≥ 4` — E.59's `block_jump_gate` consumed from the record. -/
theorem BlockSuite.mu_ge_four_of_hi_jump {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (S : BlockSuite I) {x : Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'}
    (hx : x ∈ S.blocks) {p : ℕ × ℕ} (hp : p ∈ x.2.sides) {d k : ℕ}
    (hhi : x.2.hiFac p = {(d, k)}) (hlin : x.2.linFac p = 0)
    (hd : 2 ≤ d) (hk : 2 ≤ k) : 4 ≤ x.1.μ := by
  obtain ⟨p₀, hone⟩ := S.hone x hx
  obtain rfl : p = p₀ := by rw [hone, Finset.mem_singleton] at hp; exact hp
  have hp2 : 1 ≤ p.2 := by
    have hpm : p ∈ x.2.sides := by rw [hone]; exact Finset.mem_singleton_self p
    exact (x.2.hside_cop p hpm).2
  exact block_jump_gate hk
    (le_trans hd (Nat.le_mul_of_pos_left d hp2))
    (one_side_pure_hi_mass x.2 hone hhi hlin)

/-- (iv), linear branch: a suite block pure in a linear class on a side with `ℓ ≥ 2`,
with a JUMP (`k ≥ 2`), has mass `μ ≥ 4`. -/
theorem BlockSuite.mu_ge_four_of_lin_jump {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (S : BlockSuite I) {x : Σ B' : BlockData C, RungInterface.{uO, uK, uW} C B'}
    (hx : x ∈ S.blocks) {p : ℕ × ℕ} (hp : p ∈ x.2.sides) {s : K} {k : ℕ}
    (hlin : x.2.linFac p = {(s, k)}) (hhi : x.2.hiFac p = 0)
    (hl : 2 ≤ p.2) (hk : 2 ≤ k) : 4 ≤ x.1.μ := by
  obtain ⟨p₀, hone⟩ := S.hone x hx
  obtain rfl : p = p₀ := by rw [hone, Finset.mem_singleton] at hp; exact hp
  have hmass : x.1.μ = k * (p.2 * 1) := by
    rw [mul_one]
    exact one_side_pure_lin_mass x.2 hone hlin hhi
  exact block_jump_gate hk (by omega) hmass

/-! ## Defect E-D15, discharged at the typed socket: the forcing DIVISIBILITY -/

/-- E-D15's missing divisibility, linear classes: at a typed leg the parent's class weight
is divisible by `D·ℓ` (`hdeg` + the block's own `hresdeg`/`hlen_sum` + E.13's degree law) —
the strengthening of `hforce`'s `≤`-shadow that A-E.6 predicted the typed `hpart` supplies. -/
theorem PartitionLeg.dvd_classCount_lin {O : Type uO} [CommRing O] [IsDomain O]
    {K : Type uK} [Field K] {C : SlotCarrier O K} {B : BlockData C}
    {I : RungInterface.{uO, uK, uW} C B} (P : PartitionLeg I) :
    ∀ p ∈ I.sides, ∀ q ∈ I.linFac p, C.D * p.2 ∣ I.classCount p q := by
  intro p hp q hq
  have hc : ((p, Sum.inl q) : ClassIx K) ∈ P.cls := (P.hclsLin p q).mpr ⟨hp, hq⟩
  obtain ⟨k, hk, hl, hh⟩ := P.hpureLin p q hc
  have hmass : (P.blk (p, Sum.inl q)).1.μ = k * p.2 :=
    one_side_pure_lin_mass (P.blk (p, Sum.inl q)).2 (P.hone _ hc) hl hh
  refine ⟨k, ?_⟩
  have hdeg := P.hdeg _ hc
  have hF := ((P.blk (p, Sum.inl q)).1.natDegree_F).1
  calc I.classCount p q = (P.blk (p, Sum.inl q)).1.F.natDegree := hdeg.symm
    _ = (P.blk (p, Sum.inl q)).1.μ * C.D := hF
    _ = (k * p.2) * C.D := by rw [hmass]
    _ = C.D * p.2 * k := by ring

/-- E-D15's missing divisibility, higher classes: `D·ℓ·deg q ∣ classCountHi p q`. -/
theorem PartitionLeg.dvd_classCount_hi {O : Type uO} [CommRing O] [IsDomain O]
    {K : Type uK} [Field K] {C : SlotCarrier O K} {B : BlockData C}
    {I : RungInterface.{uO, uK, uW} C B} (P : PartitionLeg I) :
    ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p, C.D * p.2 * q.1 ∣ I.classCountHi p q := by
  intro p hp q hq
  have hc : ((p, Sum.inr q) : ClassIx K) ∈ P.cls := (P.hclsHi p q).mpr ⟨hp, hq⟩
  obtain ⟨k, hk, hd2, hh, hl⟩ := P.hpureHi p q hc
  have hmass : (P.blk (p, Sum.inr q)).1.μ = k * (p.2 * q.1) :=
    one_side_pure_hi_mass (P.blk (p, Sum.inr q)).2 (P.hone _ hc) hh hl
  refine ⟨k, ?_⟩
  have hdeg := P.hdeg _ hc
  have hF := ((P.blk (p, Sum.inr q)).1.natDegree_F).1
  calc I.classCountHi p q = (P.blk (p, Sum.inr q)).1.F.natDegree := hdeg.symm
    _ = (P.blk (p, Sum.inr q)).1.μ * C.D := hF
    _ = (k * (p.2 * q.1)) * C.D := by rw [hmass]
    _ = C.D * p.2 * q.1 * k := by ring

/-! ## The A-E.6 strength-ledger claim, machine-checked -/

/-- The re-signed conclusion implies the committed one (*"`BlockSuite.hprod` + `hdegsum`
imply the committed conclusion via `blocks.map (·.1.F)`"* — A-E.6's strength ledger). -/
theorem BlockSuite.committed_shadow {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} {I : RungInterface.{uO, uK, uW} C B}
    (S : BlockSuite I) :
    ∃ blocks : List (Polynomial O),
      B.F = blocks.prod ∧
      (blocks.map Polynomial.natDegree).sum = B.F.natDegree :=
  ⟨S.blocks.map fun x => x.1.F, S.hprod, by rw [List.map_map]; exact S.hdegsum⟩

/-! ## Gate (`E57pCert`): the A-E.2/A-E.6 non-triviality standard, inside the landed file

Named instances rather than anonymous `example`s, because both directions are load-bearing:

* **(positive)** `PartitionLeg` is INHABITED at a legal pure instance and the assembly
  fires end-to-end — the typed hypothesis is not `False`-in-disguise, so
  `block_split_of_partitionLeg` is not vacuously conditional.
* **(negative)** at the A-E.6 countermodel shape — `F = X²`, one side, two unit-weight
  linear classes, EXACTLY the instance where `hpart : True` made the re-signed node FALSE
  (`verification/om4_resign_nontriviality.lean` Part 4) — the typed leg is EMPTY
  (`dup_partitionLeg_empty`): the two classes would need coprime degree-1 factors of `X²`.
  So the typing repairs the falsity in the only way an implication can be repaired: the
  hypothesis now excludes the countermodel. The mechanism (the leg's `hdisj`) is the same
  one the suite-level refutation ran on, one level up.

The carrier is the D = 1 "flat" carrier over `ℤ` (heights `0`/`⊤`, constant-term digits in
`ℚ`); every `SlotCarrier` law is PROVED, `Full` is empty so `(LIFT)` is vacuous (legitimate:
`Full`'s finite-domain obligation is the instances', E.10). -/

namespace E57pCert

/-- The flat slot carrier over `ℤ` at key degree `1`: height `0` on nonzero polynomials
(`⊤` at `0`), constant-term digits in `ℚ`. -/
noncomputable def flatCarrier : SlotCarrier ℤ ℚ where
  D := 1
  hD := one_pos
  eC := 1
  fC := 1
  hef := rfl
  heC := le_rfl
  hfC := le_rfl
  hgt := fun A => if A = 0 then ⊤ else 0
  dig := fun A => (A.coeff 0 : ℚ)
  hgt_zero := if_pos rfl
  dig_zero := by simp
  hgt_ne_top := fun A hA _ => by simp [hA]
  dig_ne_zero := by
    intro A hA hdeg
    have h0 : A.natDegree = 0 := Nat.lt_one_iff.mp hdeg
    have hc : A.coeff 0 ≠ 0 := by
      intro hc
      exact hA (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero])
    exact_mod_cast hc
  hgt_add_ge := by
    intro A B
    by_cases hAB : A + B = 0
    · simp [hAB]
    · simp only [if_neg hAB]
      by_cases hA : A = 0
      · have hB : B ≠ 0 := fun h => hAB (by rw [hA, h, add_zero])
        simp [hA, hB]
      · exact le_trans (min_le_left _ _) (by simp [hA])
  hgt_add_eq := by
    intro A B hne
    by_cases hA : A = 0
    · by_cases hB : B = 0
      · exact absurd (by rw [hA, hB]) hne
      · simp [hA, hB]
    · by_cases hB : B = 0
      · simp [hA, hB]
      · exact absurd (by simp [hA, hB]) hne
  dig_add := by
    intro A B k hA hB hne
    have hA0 : A ≠ 0 := by
      intro h; rw [if_pos h] at hA; exact (WithTop.coe_ne_top (a := k)) hA.symm
    have hk : (0 : WithTop ℤ) = (k : WithTop ℤ) := by rwa [if_neg hA0] at hA
    have hsum : A.coeff 0 + B.coeff 0 ≠ 0 := by
      intro h
      apply hne
      show (A.coeff 0 : ℚ) + (B.coeff 0 : ℚ) = 0
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h
    have hAB0 : A + B ≠ 0 := by
      intro h
      apply hsum
      have := congrArg (fun P : Polynomial ℤ => P.coeff 0) h
      simpa [Polynomial.coeff_add] using this
    refine ⟨by rw [if_neg hAB0]; exact hk, ?_⟩
    show ((A + B).coeff 0 : ℚ) = (A.coeff 0 : ℚ) + (B.coeff 0 : ℚ)
    rw [Polynomial.coeff_add]
    push_cast
    ring
  Full := fun _ => False
  hlift := fun _ hk => hk.elim

/-! ### The positive witness: a pure one-class state, its leg, and the assembly firing -/

/-- Block for the positive witness: key `X`, `F = X + 1`, mass `1`. -/
noncomputable def pureBlock : BlockData flatCarrier where
  Φ := X
  F := X + 1
  μ := 1
  hμ := le_rfl
  hΦ := monic_X
  hΦdeg := by simp [flatCarrier]
  A := fun _ => 1
  hdev := by simp
  hdegA := by intro j hj; simp [flatCarrier]
  hkeyfree := by
    refine ⟨1, -1, ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := one_ne_zero
  T := 0

/-- Interface for the positive witness: one side `(1,1)`, one linear class of weight `1`. -/
noncomputable def pureIface : RungInterface.{0, 0, 0} flatCarrier pureBlock where
  sides := {(1, 1)}
  hside_cop := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨Nat.coprime_one_left 1, le_rfl⟩
  hside_node := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp [pureBlock]
  len := fun _ => 1
  hlen_pos := fun _ _ => le_rfl
  hlen_sum := by simp [pureBlock]
  linFac := fun _ => {((1 : ℚ), 1)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => 1
  haccount := by intro p hp; simp [flatCarrier]
  classCount := fun _ _ => 1
  classCountHi := fun _ _ => 1
  hnonempty := by
    intro p hp
    exact ⟨fun q _ => le_rfl, fun q hq => by simp at hq⟩
  hforce := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨fun q _ => by simp [flatCarrier], fun q hq => by simp at hq⟩
  hexhaust := by intro p hp; simp
  W := Unit
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := ()

/-- The positive witness leg: the single class's block is the state itself (the honest
residue E39a disclosed — at a one-side single-class state the suite can be the state). -/
noncomputable def pureLeg : PartitionLeg.{0, 0, 0} pureIface where
  cls := {((1, 1), Sum.inl ((1 : ℚ), 1))}
  hclsLin := by intro p q; simp [pureIface]
  hclsHi := by intro p q; simp [pureIface]
  blk := fun _ => ⟨pureBlock, pureIface⟩
  hprod := by simp
  hdisj := by
    intro c hc c' hc' hne
    rw [Finset.mem_singleton] at hc hc'
    exact absurd (hc.trans hc'.symm) hne
  hdeg := by
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    show (X + 1 : Polynomial ℤ).natDegree = 1
    simpa using natDegree_X_add_C (1 : ℤ)
  hone := by
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    rfl
  hpureLin := by
    intro p q h
    simp only [Finset.mem_singleton, Prod.mk.injEq, Sum.inl.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨1, le_rfl, rfl, rfl⟩
  hpureHi := by intro p q h; simp at h
  hthr := by intro c hc; rfl

/-- **The positive gate**: the typed hypothesis is inhabited at a legal instance and the
E.57 assembly fires end-to-end (consuming the subsumption lemmas as the carrier legs). -/
example : Nonempty (BlockSuite.{0, 0, 0} pureIface) :=
  block_split_of_partitionLeg pureIface
    pureLeg.supplies_hblocks pureLeg.supplies_hblocksHi ⟨pureLeg⟩

/-! ### The negative gate: the typed leg is EMPTY at the A-E.6 countermodel shape -/

/-- The A-E.6 countermodel block over the flat carrier: key `X + 1`, `F = X²`, mass `2`
(`verification/om4_resign_nontriviality.lean` Part 4's `B₃`, re-based). -/
noncomputable def dupBlock : BlockData flatCarrier where
  Φ := X + 1
  F := X ^ 2
  μ := 2
  hμ := by norm_num
  hΦ := by simpa using monic_X_add_C (1 : ℤ)
  hΦdeg := by
    show (X + 1 : Polynomial ℤ).natDegree = flatCarrier.D
    simp [flatCarrier]
    simpa using natDegree_X_add_C (1 : ℤ)
  A := fun j => if j = 0 then 1 else if j = 1 then -2 else 0
  hdev := by
    show (X ^ 2 : Polynomial ℤ) = (X + 1) ^ 2 + ∑ j ∈ Finset.range 2, _ * (X + 1) ^ j
    simp [Finset.sum_range_succ]
    ring
  hdegA := by
    intro j hj
    rcases j with _ | _ | j
    · simp [flatCarrier]
    · simp [flatCarrier]
    · omega
  hkeyfree := by
    refine ⟨1, -(X - 1), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := by norm_num
  T := 0

/-- The A-E.6 countermodel interface: one side `(1,1)`, TWO linear classes (labels `0`, `1`)
of weight `1` each (Part 4's `I₃`, re-based). Every E.12 law holds. -/
noncomputable def dupIface : RungInterface.{0, 0, 0} flatCarrier dupBlock where
  sides := {(1, 1)}
  hside_cop := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨Nat.coprime_one_left 1, le_rfl⟩
  hside_node := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp [dupBlock]
  len := fun _ => 2
  hlen_pos := fun _ _ => by norm_num
  hlen_sum := by simp [dupBlock]
  linFac := fun _ => {((0 : ℚ), 1), ((1 : ℚ), 1)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => 2
  haccount := by intro p hp; simp [flatCarrier]
  classCount := fun _ _ => 1
  classCountHi := fun _ _ => 1
  hnonempty := by
    intro p hp
    exact ⟨fun q _ => le_rfl, fun q hq => by simp at hq⟩
  hforce := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨fun q _ => by simp [flatCarrier], fun q hq => by simp at hq⟩
  hexhaust := by intro p hp; simp
  W := Unit
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := ()

/-- **The negative gate**: at the exact shape where `hpart : True` made the re-signed E.57
FALSE, the TYPED leg is empty — its two forced classes would need coprime degree-1 factors
of `X²` over `Frac(ℤ)`, and any degree-1 factor of `X²` is a unit multiple of `X`. The
mechanism is the leg's `hdisj`, the same clause the suite-level refutation ran on. -/
theorem dup_partitionLeg_empty : ¬ Nonempty (PartitionLeg.{0, 0, 0} dupIface) := by
  rintro ⟨P⟩
  have h₀ : (((1, 1), Sum.inl ((0 : ℚ), 1)) : ClassIx ℚ) ∈ P.cls :=
    (P.hclsLin _ _).mpr (by simp [dupIface])
  have h₁ : (((1, 1), Sum.inl ((1 : ℚ), 1)) : ClassIx ℚ) ∈ P.cls :=
    (P.hclsLin _ _).mpr (by simp [dupIface])
  have hne : (((1, 1), Sum.inl ((0 : ℚ), 1)) : ClassIx ℚ)
      ≠ ((1, 1), Sum.inl ((1 : ℚ), 1)) := by
    simp
  -- the ledger is exactly the two classes
  have hcls : P.cls = {((1, 1), Sum.inl ((0 : ℚ), 1)), ((1, 1), Sum.inl ((1 : ℚ), 1))} := by
    apply Finset.ext
    intro c
    constructor
    · intro hc
      obtain ⟨p, q | q⟩ := c
      · have hm := (P.hclsLin p q).mp hc
        simp only [dupIface, Finset.mem_singleton, Multiset.insert_eq_cons,
          Multiset.mem_cons, Multiset.mem_singleton] at hm
        obtain ⟨rfl, rfl | rfl⟩ := hm
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · have hm := (P.hclsHi p q).mp hc
        simp [dupIface] at hm
    · intro hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact h₀
      · rw [Finset.mem_singleton.mp hc]; exact h₁
  -- the product and degree laws at the two classes
  have hprod := P.hprod
  rw [hcls, Finset.prod_pair hne] at hprod
  have hd₀ : (P.blk ((1, 1), Sum.inl ((0 : ℚ), 1))).1.F.natDegree = 1 := P.hdeg _ h₀
  have hd₁ : (P.blk ((1, 1), Sum.inl ((1 : ℚ), 1))).1.F.natDegree = 1 := P.hdeg _ h₁
  have hcop := P.hdisj _ h₀ _ h₁ hne
  -- pass to `Frac(ℤ)`, where `X` is prime
  have hinj : Function.Injective (algebraMap ℤ (FractionRing ℤ)) :=
    IsFractionRing.injective ℤ (FractionRing ℤ)
  set F₀ := (P.blk ((1, 1), Sum.inl ((0 : ℚ), 1))).1.F.map (algebraMap ℤ (FractionRing ℤ))
    with hF₀
  set F₁ := (P.blk ((1, 1), Sum.inl ((1 : ℚ), 1))).1.F.map (algebraMap ℤ (FractionRing ℤ))
    with hF₁
  have hd₀' : F₀.natDegree = 1 := by
    rw [hF₀, Polynomial.natDegree_map_eq_of_injective hinj]; exact hd₀
  have hd₁' : F₁.natDegree = 1 := by
    rw [hF₁, Polynomial.natDegree_map_eq_of_injective hinj]; exact hd₁
  have hmap : F₀ * F₁ = X ^ 2 := by
    rw [hF₀, hF₁, ← Polynomial.map_mul, ← hprod]
    show (dupBlock.F).map (algebraMap ℤ (FractionRing ℤ)) = X ^ 2
    simp [dupBlock]
  have hXprime : Prime (X : Polynomial (FractionRing ℤ)) := Polynomial.prime_X
  -- any degree-1 divisor of `X ^ 2` is associated to `X`
  have hXdvd : ∀ G : Polynomial (FractionRing ℤ), G.natDegree = 1 →
      G ∣ (X : Polynomial (FractionRing ℤ)) ^ 2 → (X : Polynomial (FractionRing ℤ)) ∣ G := by
    intro G hG hGd
    obtain ⟨i, hi, u, hu⟩ := (dvd_prime_pow hXprime 2).mp hGd
    have hG0 : G ≠ 0 := fun h => by simp [h] at hG
    have hdeg : (G * (u : Polynomial (FractionRing ℤ))).natDegree = i := by
      rw [hu, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_mul hG0 (Units.ne_zero u),
      Polynomial.natDegree_coe_units, add_zero, hG] at hdeg
    subst hdeg
    simpa using (Associated.symm ⟨u, hu⟩).dvd
  have hdvd₀ : (X : Polynomial (FractionRing ℤ)) ∣ F₀ :=
    hXdvd F₀ hd₀' ⟨F₁, hmap.symm⟩
  have hdvd₁ : (X : Polynomial (FractionRing ℤ)) ∣ F₁ :=
    hXdvd F₁ hd₁' ⟨F₀, by rw [← hmap]; ring⟩
  exact Polynomial.not_isUnit_X (hcop.isUnit_of_dvd' hdvd₀ hdvd₁)

end E57pCert

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.classWeight
#print axioms Uniformity.Density.Ladder.PartitionLeg
#print axioms Uniformity.Density.Ladder.PartitionLeg.mk
#print axioms Uniformity.Density.Ladder.PartitionLeg.toBlockSuite
#print axioms Uniformity.Density.Ladder.block_split_of_partitionLeg
#print axioms Uniformity.Density.Ladder.PartitionLeg.supplies_hblocks
#print axioms Uniformity.Density.Ladder.PartitionLeg.supplies_hblocksHi
#print axioms Uniformity.Density.Ladder.classWeight_side_sum
#print axioms Uniformity.Density.Ladder.PartitionLeg.side_degree_sum
#print axioms Uniformity.Density.Ladder.one_side_pure_hi_mass
#print axioms Uniformity.Density.Ladder.one_side_pure_lin_mass
#print axioms Uniformity.Density.Ladder.BlockSuite.mu_ge_four_of_hi_jump
#print axioms Uniformity.Density.Ladder.BlockSuite.mu_ge_four_of_lin_jump
#print axioms Uniformity.Density.Ladder.PartitionLeg.dvd_classCount_lin
#print axioms Uniformity.Density.Ladder.PartitionLeg.dvd_classCount_hi
#print axioms Uniformity.Density.Ladder.BlockSuite.committed_shadow
#print axioms Uniformity.Density.Ladder.E57pCert.flatCarrier
#print axioms Uniformity.Density.Ladder.E57pCert.pureLeg
#print axioms Uniformity.Density.Ladder.E57pCert.dup_partitionLeg_empty

end AxCheck
