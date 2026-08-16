/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03
import Uniformity.ChapC.C15

/-!
# Uniformity.ChapC.C83 — `DeepTower`, the depth-`r` tower datum (`DEF GENTOW5-1`)

**Chapter C, NODE C.83** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §9, the third stage
and the thresholds; fragile no. 1 of the A-C.1 signing order), **ENV-C1**.  The carrier the
whole of §9 runs on: stage data `(e_i, f_i, ψ_i)` for `i = 1 … r` over ONE fixed key frame
`F` (GC-7: the bundle `O` is fixed once and a tower level is DATA over it, never a
re-quantified DVR), together with the ladder bookkeeping `ê_i`, `D_i`, `E_i`, the normalizer
recursion, the shift and the cocycle.

* `towerSolve u e k` — the C.15/C.28-pattern class solve at `(u, e)`: the unique `b < e` with
  `b·u ≡ k (mod e)`, junk `0` when there is none (total, computable — D6's discipline).
* `DeepTower F H₀ hpin r` — the datum itself (fields below).
* `ehat`, `Dcum`, `Econst` — `ê_i = e_1⋯e_i`, `D_i = l_1⋯l_i` with `l_i = e_i f_i`, and the
  side constant `E_i = e_i f_i u_i` (`E_1 = D_1·h`).
* `towerNorm`, `towerShift`, `towerCocycle` — the normalizer recursion `n̂_{i+1}` and the
  `Λ_i`/`τ_i` data, carried as EXPONENT bookkeeping only.
* `trunc` — restriction to depth `i ≤ r`, how consumers instantiate a level-general statement
  at one rung.

## ⚠ DECISION A-C.1/GC-7 (the depth-≥ 3 carrier fallback, TAKEN)

The corpus datum carries the iterated residue fields as the literal telescope
`K_1 = F_Q(η_θ)`, `ψ_{i} ∈ K_i[T]`, `K_{i+1} = K_i(β_{i+1}) = AdjoinRoot ψ_i`.  **That
telescope cannot be a list of Lean structure fields**: the type of `ψ_{i+1}` mentions
`AdjoinRoot ψ_i`, a dependency no `structure` field list carries — exactly the elaboration
failure GC-7's depth-≥ 3 note anticipated, and the recorded fallback is therefore triggered
and taken here.  The fallback: the levels `fld i` are ABSTRACT types with `Field` data
(`fldField`, registered as an instance so consumers elaborate), and the fact that they ARE the
iterate is witnessed by two `RingEquiv` fields —

* `base : fld 1 ≃+* F.stageField H₀ hpin` (stage `1` IS the frame; C.03's field),
* `step : ∀ i, 1 ≤ i → i < r → (fld (i + 1) ≃+* AdjoinRoot (ψ i))`.

Nothing weaker than the corpus statement is asserted: a `DeepTower` still pins every level to
the `AdjoinRoot` iterate, only through an isomorphism rather than through definitional
equality.  Consumers that need to MOVE elements along the chain compose `base`/`step`; no
`algebraMap` is used (the D8 gap C.21 hit does not arise here — the maps are supplied as data).

## Indexing and totality conventions (the junk-total discipline)

Stage `1` is the frame: `he1 : e 1 = F.e₁`, `hf1 : f 1 = F.f₁`, `hu1 : u 1 = F.h`.  A
`DeepTower` of depth `r` carries stages `1 … r`; the arithmetic fields `e, f, u : ℕ → ℕ` and
`ψ : (i : ℕ) → Polynomial (fld i)` are TOTAL, with every real hypothesis range-scoped
(`∀ i, 1 ≤ i → i ≤ r → …`, resp. `i < r` for the fields that speak about stage `i + 1`).  Off
the range the data is junk and no lemma may read it.

`towerNorm i k` is the exponent solve of the level-`(i+1)` normalizer `n̂_{i+1}(k)`, so
`towerNorm 1` is §6's `n̂₂` VERBATIM (the off-by-one is deliberate and is the corpus's own
indexing: `towerNorm 0` is the bare frame solve through C.15's `slotIdx`).

## Faithfulness

**⚠ Mandatory, trust-boundary definition.** Four recasts against `EFF.GENTOW5.14`–`.16`, each
flagged for the chapter cross-read (blueprint §16):

* *the residue tower* — recast as `fld`/`base`/`step` per DECISION A-C.1/GC-7 above.  This is
  the one substantive divergence and the reason C.83 is a fragile node.
* *properness* `l_i = e_i f_i ≥ 2` at every `i ≥ 2` — `hproper`.  Stage `1` is EXEMPT (it is
  the frame, whose `D′ = e₁f₁` may be `1` at the degenerate frame C.01 admits); an improper
  stage `i ≥ 2` would be a refinement, not a level.
* *the floor chain* `u_{i+1} > e_{i+1}·E_i` — carried as the DATUM FIELD `hfloor`, not as a
  derived fact.  This is S12.1's explicit carve-out (*"later arguments may still use that
  inequality unconditionally when it is included explicitly in the fixed tower datum"*); its
  automatic derivation at leaves is C.91(e) and is CONDITIONAL at `n ≥ 3`.  Every consumer of
  `hfloor` is therefore consuming a hypothesis of the datum, not a theorem of this chapter.
* *the letters and the cocycle* `Λ_i = Φ_i^{e_{i+1}}/n̂_i(u_{i+1})`, `τ_i(a,b)` — carried as
  the `towerShift`/`towerCocycle` EXPONENT data, never as fraction-field elements.  This is the
  C.15/C.28 discipline iterated rung by rung, and it is what the STATEMENT prescribes.

Additionally, D4: the blueprint writes the pin binder as `F.Pin H₀`, a stub-side abbreviation
that is no node's declaration; it is written out here, exactly as at C.03/C.09/C.42.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

**DEPENDS.** C.01 (`KeyFrame`) · C.03 (`stageField`) · C.15 (`slotIdx`, the bottom solve) —
imported.  By committed node ID and by shape only: C.09 (`LevelDatum`, the depth-2 dictionary)
· C.12 (the `AdjoinRoot` chain) · C.16 (the uniqueness of the rung solve) · C.28 (the level-2
cocycle this iterates) · C.42 (`TowerDatum`, the depth-2 instance this extends; C.85 supplies
the bridge, not this node).

**PROOF.** Definitional.  Uniqueness of the recursion solve per rung is C.16's argument at
`(u_{i+1}, e_{i+1})` — a property of the datum, stated there, not re-proved here.

**SOURCE.** `EFF.GENTOW5.14`–`.16` (verbatim, incl. the FGMN-collapsing gloss for properness
[via GENTOW2's dictionary — documentation only] and the `i = 2` verbatim identification);
`EFF.GENTOW5.21` (the worked pins `n̂₃(85) = 2⁸Φ₂`, `n̂₂(21) = 16Φ′`, which are §13 regression
values read at C.85's witness instance, not here).

**TEETH.** P-B1/B2 (*"floor chain tight, `u = 5, 21, 85, 341`"*) → §13 regression rows; the
rung solves of that chain are checked as `example`s below at the `towerSolve` level, which is
the part of the tooth this node owns.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  Definitional (no proof obligation beyond `trunc`'s
field re-scoping, which is hypothesis weakening).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The C.15/C.28-pattern class solve at the pair `(u, e)`: the unique `b < e` with
`b·u ≡ k (mod e)` — junk `0` when no solve exists, so the function is TOTAL and COMPUTABLE
(D6's discipline, as at C.15's `slotIdx`).  Under `Nat.Coprime u e` the solve exists and is
unique, which is C.16's argument at `(u, e)`. -/
def towerSolve (u e k : ℕ) : ℕ :=
  ((List.range e).find? (fun b => (b * u) % e == k % e)).getD 0

/-- **NODE C.83 — the depth-`r` tower datum** (`DEF GENTOW5-1`), on the GC-7 fallback carrier
(see the module docstring's DECISION block).  Stage `1` is the frame `F`; stages `1 … r` carry
`(e_i, f_i, u_i, ψ_i)` with properness from stage `2`, coprime slopes, and the floor chain
`u_{i+1} > e_{i+1}·E_i` AS A DATUM FIELD.
[A-C.1/D4: the pin binder is written out, as at C.03/C.09/C.42.] -/
structure DeepTower (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (r : ℕ) where
  /-- stage ramification data; `e 1 = F.e₁`; junk outside `1 … r`. -/
  e : ℕ → ℕ
  /-- stage residual degrees; `f 1 = F.f₁`; junk outside `1 … r`. -/
  f : ℕ → ℕ
  /-- stage heights; `u 1 = F.h`; the floor chain is `hfloor`. -/
  u : ℕ → ℕ
  /-- the level residue fields `K_i` (abstract, per DECISION A-C.1/GC-7). -/
  fld : ℕ → Type*
  /-- the `Field` data of the abstract levels; registered as an instance below. -/
  fldField : ∀ i, Field (fld i)
  /-- `ψ i` = the minimal polynomial of the level-`(i+1)` letter over `K_i` (live `1 ≤ i < r`). -/
  ψ : (i : ℕ) → Polynomial (fld i)
  he1 : e 1 = F.e₁
  hf1 : f 1 = F.f₁
  hu1 : u 1 = F.h
  he : ∀ i, 1 ≤ i → i ≤ r → 0 < e i
  hf : ∀ i, 1 ≤ i → i ≤ r → 0 < f i
  /-- PROPERNESS at every stage `≥ 2`: `l_i = e_i f_i ≥ 2` (an improper stage is a refinement,
  not a level).  Stage `1` is exempt — it is the frame. -/
  hproper : ∀ i, 2 ≤ i → i ≤ r → 2 ≤ e i * f i
  hcop : ∀ i, 2 ≤ i → i ≤ r → Nat.Coprime (u i) (e i)
  /-- THE FLOOR CHAIN, AS A DATUM FIELD (S12.1's carve-out): `u_{i+1} > e_{i+1}·E_i` with
  `E_i = e_i f_i u_i`.  Its automatic derivation at leaves is C.91(e), conditional at `n ≥ 3`;
  consumers of this field consume a HYPOTHESIS, not a theorem. -/
  hfloor : ∀ i, 1 ≤ i → i < r → e (i + 1) * (e i * f i * u i) < u (i + 1)
  hψ : ∀ i, 1 ≤ i → i < r →
    (ψ i).Monic ∧ Irreducible (ψ i) ∧ (ψ i).natDegree = f (i + 1) ∧ (ψ i).coeff 0 ≠ 0
  /-- the iterate witness, base: `K_1` IS the frame's stage field (C.03). -/
  base : fld 1 ≃+* F.stageField H₀ hpin
  /-- the iterate witness, step: `K_{i+1} = K_i(β_{i+1})` as the `AdjoinRoot` iterate. -/
  step : ∀ i, 1 ≤ i → i < r → (fld (i + 1) ≃+* AdjoinRoot (ψ i))

-- the abstract chain's `Field` data, registered so consumers elaborate (directed: keyed on
-- the projection `DeepTower.fld`).
attribute [instance] DeepTower.fldField

namespace DeepTower

variable {F : KeyFrame O π} {H₀ : ℕ}
  {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
  {r : ℕ}

/-- `ê_i = e_1⋯e_i`. -/
def ehat (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, T.e j

/-- `D_i = l_1⋯l_i = (e_1f_1)⋯(e_if_i)`. -/
def Dcum (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, (T.e j * T.f j)

/-- the side constant `E_i := e_i·f_i·u_i` (`E_1 = D_1·h`). -/
def Econst (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := T.e i * T.f i * T.u i

/-- The normalizer recursion, as pure exponent bookkeeping: `towerNorm i k` is the exponent
data `(a₀, i₀, (b_1, …, b_i))` of `n̂_{i+1}(k) = π^{a₀} x^{i₀} Φ_1^{b_1} ⋯ Φ_i^{b_i}` —
solved rung by rung by `e_{j+1}·m_j(k) + b_j(k)·u_{j+1} = k`, `0 ≤ b_j(k) < e_{j+1}` (unique by
coprimality, C.16 at `(u_{j+1}, e_{j+1})`), with C.15's frame solve at the bottom.
`towerNorm 1` is §6's `n̂₂`, verbatim.  Exponents only: no fraction-field element is ever
formed (the C.15/C.28 discipline, iterated). -/
def towerNorm (T : DeepTower F H₀ hpin r) : (i : ℕ) → ℕ → ℕ × ℕ × (Fin i → ℕ)
  | 0, k => ((k - F.slotIdx k * F.h) / F.e₁, F.slotIdx k, fun x => x.elim0)
  | i + 1, k =>
      let b := towerSolve (T.u (i + 2)) (T.e (i + 2)) k
      let m := (k - b * T.u (i + 2)) / T.e (i + 2)
      let p := towerNorm T i m
      (p.1, p.2.1, Fin.snoc p.2.2 b)

/-- the rung-`i` shift (C.15's pattern at `(u_i, e_i)`) — the `Λ_i`-exponent bookkeeping. -/
def towerShift (T : DeepTower F H₀ hpin r) (i m : ℕ) : ℕ := towerSolve (T.u i) (T.e i) m

/-- the rung-`i` cocycle (C.28's pattern; the `τ_i`-exponent bookkeeping). -/
def towerCocycle (T : DeepTower F H₀ hpin r) (i a b : ℕ) : ℕ :=
  (T.towerShift i a + T.towerShift i b - T.towerShift i (a + b)) / T.e i

/-- truncation to depth `i ≤ r` (every field re-scoped; used to instantiate level-general
consumers at each rung).  The data is unchanged — only the range-scoped hypotheses are
weakened, which is why this is definitional. -/
def trunc (T : DeepTower F H₀ hpin r) (i : ℕ) (hi : i ≤ r) : DeepTower F H₀ hpin i where
  e := T.e
  f := T.f
  u := T.u
  fld := T.fld
  fldField := T.fldField
  ψ := T.ψ
  he1 := T.he1
  hf1 := T.hf1
  hu1 := T.hu1
  he := fun j h1 h2 => T.he j h1 (h2.trans hi)
  hf := fun j h1 h2 => T.hf j h1 (h2.trans hi)
  hproper := fun j h1 h2 => T.hproper j h1 (h2.trans hi)
  hcop := fun j h1 h2 => T.hcop j h1 (h2.trans hi)
  hfloor := fun j h1 h2 => T.hfloor j h1 (h2.trans_le hi)
  hψ := fun j h1 h2 => T.hψ j h1 (h2.trans_le hi)
  base := T.base
  step := fun j h1 h2 => T.step j h1 (h2.trans_le hi)

end DeepTower

end Uniformity.Density.Tower

/-! ## The rung solves of the P-B1/B2 chain `u = 5, 21, 85, 341`

The part of TOOTH P-B1/B2 this node owns: at every rung of the S4 witness chain the ladder
`e = 2` solve returns `b = 1`, i.e. the height jumps by an odd multiple at each stage.  (The
full regression rows `n̂₃(85) = 2⁸Φ₂`, `n̂₂(21) = 16Φ′` are read at C.85's witness instance,
which supplies the frame numerals this node abstracts over.) -/

namespace Uniformity.Density.Tower

example : towerSolve 5 2 21 = 1 := by decide
example : towerSolve 21 2 85 = 1 := by decide
example : towerSolve 85 2 341 = 1 := by decide

-- the unramified rung `e = 1`: the solve is forced to `0`.
example : towerSolve 5 1 7 = 0 := by decide

-- the JUNK convention, exercised: `2b ≡ 1 (mod 4)` has no solution, so `towerSolve` returns
-- the default `0` rather than failing.  Nothing may read this value (`Nat.Coprime u e` is what
-- every consumer supplies).
example : towerSolve 2 4 1 = 0 := by decide

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerSolve
#print axioms Uniformity.Density.Tower.DeepTower
#print axioms Uniformity.Density.Tower.DeepTower.mk
#print axioms Uniformity.Density.Tower.DeepTower.ehat
#print axioms Uniformity.Density.Tower.DeepTower.Dcum
#print axioms Uniformity.Density.Tower.DeepTower.Econst
#print axioms Uniformity.Density.Tower.DeepTower.towerNorm
#print axioms Uniformity.Density.Tower.DeepTower.towerShift
#print axioms Uniformity.Density.Tower.DeepTower.towerCocycle
#print axioms Uniformity.Density.Tower.DeepTower.trunc

end AxCheck
