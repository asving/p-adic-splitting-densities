/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H03
import Uniformity.ChapH.H04
import Uniformity.ChapH.H112
import Uniformity.ChapB.B30

/-!
# Uniformity.ChapH.H117 — the CS criterion (fires H.03/H.04)

**Chapter H, NODE H.117** [theorem] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a *"zero CS at `m ≤ 3`;
every `m = 4` CS event obeys `4 ≤ e·μ·deg ψ ≤ m`"*, sources `EFF.GENIND.11` (the criterion) and
`EFF.GENIND.43` (`GT-CRIT`'s below-floor absences).  Twelfth node of **N-2**, the cluster event
grammar over `O`, and the one that empties the CS bucket at `2 ≤ m ≤ 3`.

* `cs_block_bounds` (clause ii) — every CS block `(ℓ, μ, deg ψ)` of a non-drain state obeys
  `4 ≤ ℓ * μ * ψ.natDegree ≤ m`;
* `isCSState_four_le` (clause i) — hence no CS event exists below `m = 4`.

The Lean order is the dependency order: clause (ii) is proved first at an arbitrary lift, and
clause (i) reads it at `μ = 2` on the lift the definition's ∀-clause supplies.

## Why this node is the geometric half H.03's scope fence flagged as missing

H.03 proves `4 ≤ e₁ · μ · f₁` for an abstract `GenreDatum`, and its **⚠ SCOPE FENCE** records
that two steps are *geometric* and *"have no node"*: (1) *"a CS event **is** a repeated residual
factor `(ψ, μ)` with `μ ≥ 2` and `e · deg ψ ≥ 2` on a side of the stage polygon"*, and (2)
*"the polygon of a stage with `m` keys spans abscissas `[0, m]`, so `m ≥ 4`"*.  Step (1) is now
a DEFINITION — H.110's `IsCSState` is literally that clause, over chapter B's landed order-1
polygon API at the key `φ = X` — so it needs no proof.  Step (2) is `cs_block_bounds`'s upper
half, proved here.  Correspondingly, H.04 (iii) `four_le_of_sideLen_le` carries `G.sideLen ≤ m`
as an EXPLICIT hypothesis; clause (ii) below is exactly that hypothesis, discharged at the
cluster level, and `cs_block_four_cases` fires H.04 (ii)'s boundary enumeration on it.

## The three mechanisms, none of them new

1. **The lower bound** is H.03's arithmetic on the concrete block: `2 ≤ ℓ * deg ψ` (the block
   size, a conjunct of `IsCSState`) times `2 ≤ μ` (the repeated factor) is `4`, after the same
   commutation `ℓ * μ * γ = (ℓ * γ) * μ` that H.03 performs on `sideLen`.
2. **The upper bound** is degree bookkeeping down chapter B's landed chain.  `ψ ^ μ` divides the
   residual polynomial and the residual polynomial is nonzero (B.30 (b): its constant term does
   not vanish), so `μ * deg ψ ≤ deg R_λ = sideDeg` (B.30 (b) again).  Multiplying by `ℓ` turns
   the residual degree into the side's abscissa length, `ℓ * sideDeg = sideMax − sideMin`
   (B.20 (d) `sideMax_eq`), and the side lives inside the support range, `sideMax ≤ deg f = m`
   (`sideMax_le_natDegree` below, from B.16's `Finset.filter` over `range (natDegree + 1)`).
3. **The two side conditions of B.30** are supplied, not assumed.  `IsKey X` is the order-0 key
   (the three-line `isKey_X`, `private` in C.12/C.19 and therefore re-derived here — see the
   note in C.19: *"`private` does not export"*).  `suppVal X (monicPoly a) u ℓ ≠ ⊤` is H.110's
   **visible-polygon principle** `suppVal_lt_window`: on a non-drain state the abscissa `0`
   already caps the cleared support value at `ℓ * v` with `v < N`.  This is the ONLY place the
   `h0`/`hN`/`hm` binders are consumed, and it is why the criterion is stated on non-drain
   states.

No residual polynomial is *constructed* here and no new polygon type is declared (GC-2): the
node reads B.29's `resPoly` at the pinned `H₀ = npHgt (sideMin …)` (GC-1) and nothing else.

DEPENDS: H.110 (`IsCSState`, `suppVal_lt_window`), H.112 (`exists_proj_eq`) · H.03, H.04
(`sideLen_four_cases`, the boundary census this criterion opens onto) · landed CHAP-B degree
bookkeeping: B.16 (`sideSet`, `OnSide`), B.20 (`sideMin`/`sideMax`/`sideDeg`, `sideMax_eq`),
B.25 (`resField`, `instFieldResField`), B.29 (`resPoly`), B.30 (`natDegree_resPoly`) · landed
`monicPoly_natDegree` · mathlib `Polynomial.natDegree_le_of_dvd`, `Polynomial.natDegree_pow`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0) + `π` explicit, every binder INLINE (the B.42
completeness-binder rule; §17 declares no section variables).  No `[Finite (ResidueField O)]`:
this node counts nothing.

## TEETH (GC-8)

Battery `P1(g) zero CS below m=4` and `P1(g) CS criterion (eμγ=4 ⟹ two solutions)` of
`verification/openmath/OM2_genindb_battery.py` (RESULTS 2026-08-16, 612/612), both
characteristics, the `GT-CRIT` negative half included.  The numeric gate at the end runs both
against H.110's landed enumeration `csSolutions` — the DETECTION side — and adds the sweep that
welds it to this node's two bounds: on every admissible block up to `m = 9` the closed
inequalities `4 ≤ ℓ μ γ ≤ m` hold, and the enumeration is empty exactly below `m = 4`.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

/-! ## 1. The two side conditions of B.30, at the order-0 key -/

/-- **The order-0 key `X` is an order-1 key** in B.01's sense.  C.12 and C.19 both carry this
helper `private`, and `private` does not export, so it is re-derived here (three lines, same
proof).  `private`: a supplier-side helper, not a blueprint node. -/
private theorem isKey_X {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- **The side lies inside the support range.**  B.16 filters `sideSet` out of
`Finset.range (f.natDegree + 1)`, so its greatest element is at most `f.natDegree`.  This is the
"polygon spans abscissas `[0, m]`" step of H.03's scope fence, in the only form §17 needs. -/
theorem sideMax_le_natDegree {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {φ f : Polynomial O} {u ℓ : ℕ} (h : (sideSet φ f u ℓ).Nonempty) :
    sideMax φ f u ℓ h ≤ f.natDegree := by
  classical
  have hmem : sideMax φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.max'_mem _ _
  have hmem' : sideMax φ f u ℓ h ∈
      Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hmem
  have hlt := Finset.mem_range.1 (Finset.mem_filter.1 hmem').1
  omega

/-! ## 2. Clause (ii) — the block bounds -/

set_option linter.unusedVariables false in
/-- **H.117 (clause ii).** Every CS block `(ℓ, μ, deg ψ)` — a repeated irreducible residual
factor `ψ` on a side of denominator `ℓ`, multiplicity `μ ≥ 2`, block size `ℓ · deg ψ ≥ 2` —
obeys `4 ≤ ℓ · μ · deg ψ ≤ m`: the composite-stage opening criterion.

`hψ : Irreducible ψ` is part of the FROZEN blueprint signature and is not consumed by the proof
(the bounds are pure degree bookkeeping: only `ψ ^ μ ∣ R_λ` and `2 ≤ ℓ · deg ψ` are read, and
irreducibility is what makes the block a *stage* rather than a mere divisor); the linter is
silenced rather than the binder dropped. -/
theorem cs_block_bounds {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h0 : ¬ IsDrainState c)
    (a : Fin m → O) (ha : proj O m N a = c.1) (u ℓ : ℕ)
    (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) (H₀ : ℕ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hpin : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞))
    (ψ : Polynomial (resField (X : Polynomial O))) (hψ : Irreducible ψ) (μ : ℕ)
    (hμ : 2 ≤ μ) (hblock : 2 ≤ ℓ * ψ.natDegree)
    (hdvd : ψ ^ μ ∣ resPoly π X (monicPoly a) u ℓ hne H₀) :
    4 ≤ ℓ * μ * ψ.natDegree ∧ ℓ * μ * ψ.natDegree ≤ m := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  -- B.30's finiteness side condition, from H.110's visible-polygon principle
  have htop : suppVal (X : Polynomial O) (monicPoly a) u ℓ ≠ ⊤ :=
    ne_top_of_lt (suppVal_lt_window hπ (by omega : 0 < m) hN h0 ha (u := u) hℓ)
  obtain ⟨hdeg, hc0⟩ := natDegree_resPoly hπ isKey_X hℓ hcop htop hne hpin
  have hRne : resPoly π X (monicPoly a) u ℓ hne H₀ ≠ 0 := by
    intro hz
    exact hc0 (by rw [hz, Polynomial.coeff_zero])
  -- `μ * deg ψ ≤ deg R_λ = sideDeg`
  have hpow := Polynomial.natDegree_le_of_dvd hdvd hRne
  rw [Polynomial.natDegree_pow, hdeg] at hpow
  -- `ℓ * sideDeg = sideMax − sideMin ≤ sideMax ≤ deg (monicPoly a) = m`
  have hsm := sideMax_eq hℓ hcop htop hne
  have hmax := sideMax_le_natDegree (φ := (X : Polynomial O)) (f := monicPoly a) hne
  rw [monicPoly_natDegree] at hmax
  have hls : ℓ * sideDeg X (monicPoly a) u ℓ hne ≤ m := by
    refine le_trans ?_ hmax
    rw [hsm]
    exact Nat.le_add_left _ _
  refine ⟨?_, ?_⟩
  · calc (4 : ℕ) = 2 * 2 := rfl
      _ ≤ (ℓ * ψ.natDegree) * μ := Nat.mul_le_mul hblock hμ
      _ = ℓ * μ * ψ.natDegree := by ring
  · calc ℓ * μ * ψ.natDegree = ℓ * (μ * ψ.natDegree) := by ring
      _ ≤ ℓ * sideDeg X (monicPoly a) u ℓ hne := Nat.mul_le_mul_left ℓ hpow
      _ ≤ m := hls

/-! ## 3. Clause (i) — no CS event below `m = 4` -/

/-- **H.117 (clause i).** No CS event exists below `m = 4`.  The definition's ∀-lift clause is
read at the lift H.112's `exists_proj_eq` supplies; its block has `μ = 2` (a repeated factor),
and clause (ii) chains `4 ≤ ℓ · 2 · deg ψ ≤ m`. -/
theorem isCSState_four_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h : IsCSState π c) : 4 ≤ m := by
  obtain ⟨a, ha⟩ := exists_proj_eq c.1
  obtain ⟨u, ℓ, hne, H₀, hℓ, hcop, hpin, ψ, hψ, hblock, hdvd⟩ := h.2 a ha
  have hb := cs_block_bounds hπ hm hN c h.1 a ha u ℓ hne H₀ hℓ hcop hpin ψ hψ 2 le_rfl
    hblock hdvd
  exact le_trans hb.1 hb.2

/-- **The two buckets D-H17.1 puts at `2 ≤ m ≤ 3` are CS-free.**  The contrapositive of clause
(i), in the form H.121/H.122 consume: at cluster size `m ≤ 3` the CS bucket of H.111's partition
is EMPTY, so the conservative complement splits over DRAIN/α/β/DEC alone. -/
theorem not_isCSState_of_lt_four {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {m N : ℕ} (hπ : Irreducible π) (hm : 1 ≤ m)
    (hN : 1 ≤ N) (hlt : m < 4) (c : ClusterState O m N) : ¬ IsCSState π c := fun h =>
  absurd (isCSState_four_le hπ hm hN c h) (by omega)

/-! ## 4. The boundary census — H.04 fired on a CS block -/

/-- **H.117 fires H.04 (ii).**  A CS block that SATURATES the criterion (`ℓ · μ · deg ψ = 4`,
which by clause (ii) forces `m = 4` whenever the block fits) is one of exactly two: `(2, 1, 2)`
— the ramified opening, genre E — or `(1, 2, 2)` — the inert opening, genre F.  This is H.04's
`sideLen_four_cases`, fired at the cluster-level block instead of an abstract `GenreDatum`. -/
theorem cs_block_four_cases {ℓ μ γ : ℕ} (hμ : 2 ≤ μ) (hblock : 2 ≤ ℓ * γ)
    (h4 : ℓ * μ * γ = 4) : (ℓ = 2 ∧ γ = 1 ∧ μ = 2) ∨ (ℓ = 1 ∧ γ = 2 ∧ μ = 2) :=
  sideLen_four_cases hμ hblock h4

end Uniformity.Density.Induction

/-! ## 5. TEETH — the `P1(g)` pair, reproduced

`csSolutions` is H.110's landed enumeration of admissible CS blocks `(e, γ, μ)` at cluster size
`m` (`1 ≤ e`, `1 ≤ γ`, `2 ≤ μ`, block size `2 ≤ e * γ`, and `e * μ * γ ≤ m`) — the DETECTION
side of the battery.  The first two `#guard`s are the battery's two `P1(g)` checks verbatim; the
third is the weld this node adds, running the two proved bounds over every admissible block in
the range. -/

section NumericGate

-- battery `P1(g) zero CS below m=4`: the enumeration is EMPTY at every `m ≤ 3` — the numeral
-- shadow of `isCSState_four_le`, and what puts H.121/H.122 at `2 ≤ m ≤ 3` (DECISION D-H17.1)
#guard (List.range 4).all fun m => csSolutions m == []

-- battery `P1(g) CS criterion (eμγ=4 ⟹ two solutions)`: at `m = 4` exactly the two blocks
-- `cs_block_four_cases` enumerates, `(e, γ, μ) = (1, 2, 2)` and `(2, 1, 2)`
#guard csSolutions 4 == [(1, 2, 2), (2, 1, 2)]

-- the weld: `cs_block_bounds`' two closed inequalities on every admissible block up to `m = 9`
#guard (List.range 10).all fun m => (csSolutions m).all fun t =>
  decide (4 ≤ t.1 * t.2.2 * t.2.1) && decide (t.1 * t.2.2 * t.2.1 ≤ m)

-- and the saturating blocks are exactly the `m = 4` ones: below the floor there are none, and
-- at the floor every solution saturates (the `GT-CRIT` negative half)
#guard (csSolutions 4).all fun t => t.1 * t.2.2 * t.2.1 == 4

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.sideMax_le_natDegree
#print axioms Uniformity.Density.Induction.cs_block_bounds
#print axioms Uniformity.Density.Induction.isCSState_four_le
#print axioms Uniformity.Density.Induction.not_isCSState_of_lt_four
#print axioms Uniformity.Density.Induction.cs_block_four_cases

end AxCheck
