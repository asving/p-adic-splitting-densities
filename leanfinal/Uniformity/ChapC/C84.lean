/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C56a
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C84 — `towerWeight`, `flavorMonomial`, `towerLift`: the level-`i` lift layer

**Chapter C, NODE C.84** [def+lemma] [fresh] [signed: A-C.1] (`blueprint/CHAP-C_tower_grammar.md`
§9, lines 5203–5262; twin `leanspec/Leanspec/ChapC.lean:3009-3030`). **ENV-C1.**

The depth-`i` generalization of §6/§8's `n2Exp`/`k2DigitLift` cluster, over C.83's `DeepTower`
carrier: the level-`i` weight `wt_i`, the flavor monomials `M_{r,t}(m)` at the `[GT5-r2]`
CORRECTED display (the base **re-solves per flavor**), and the digit lift `lift_i(c; m)` built
from them.

**STAGE 1 of this file's landing** carries `towerWeight` and `flavorMonomial`; `towerLift` and its
digit read follow in the same node (see the Status section for what is in the file *now*).

## The displays

```
wt_i(v, a, J) = ê_i·v + a·(ê_i/e_1)·u_1 + Σ_{1 ≤ j ≤ i−1} J_j·(ê_i/ê_{j+1})·u_{j+1} + J_i·E_i
M_{r,t}(m)    = n̂_i(m − Δ(r,t))·x^{e_1 r}·Φ_1^{e_2 t_1}⋯Φ_{i−1}^{e_i t_{i−1}},
Δ(r,t)        = e_1 r·(ê_i/e_1)·u_1 + Σ_{1 ≤ j ≤ i−1} e_{j+1} t_j·(ê_i/ê_{j+1})·u_{j+1}
```

with `ê_i = e_1⋯e_i` (C.83's `ehat`), `E_i = e_i f_i u_i` (C.83's `Econst`) and `n̂_i` the
normalizer exponent solve (C.83's `towerNorm`, whose depth-1 instance IS §8's `n2Exp`).

**The TOP variable is priced at `E_i`, which is a LOWER bound, not the exact value** — the
`[GT5-r1]` repair: the field floor gives `> E_i` and nothing sharper is known. `towerWeight` is
therefore an *under*-estimate of the true weight at the top slot, and every consumer that compares
weights must carry that asymmetry rather than assume equality. This is the single most
misreadable thing about `wt_i` and it is why the blueprint spells it out at the node.

**The frozen fixed-base display is DEAD** (as at C.56a): its compensating `π`-exponent goes
non-integer at seam-live heights — FR-A's `11/2 ∉ ℤ` (`EFF.GENTOW5.17`). What is landed is the
`[GT5-r2]` per-flavor re-solve: `towerNorm` is applied to the shifted height `m − Δ(r,t)`, so each
flavor solves its own class equation.

## Trust-boundary notes (⚠ new definitions, flagged for human review)

1. **`towerWeight` prices the top variable at a LOWER bound** (`[GT5-r1]`, above). Nothing in this
   file claims `wt_i` is attained.
2. **`flavorMonomial` does NOT implement the ABSENCE proviso.** The blueprint's STATEMENT (ii)
   says a flavor is *absent* when the ladder solve fails (the negative-height proviso); the signed
   body computes `m − Δ` in `ℕ`, where the failure is silently truncated to `0` and the flavor
   comes back as a junk monomial instead of being omitted. That is the signed body and it is
   transcribed verbatim; the proviso is the CONSUMERS' hypothesis — `EFF.GENTOW5.17`/S12.2 make
   the display valid only for `m > bound_i` (the PRECEDING rung's threshold, **not**
   `bound_{i+1}`; the S11.4 bracket is DEAD), and above that threshold no flavor is absent.
   Nothing here may be read as asserting that a flavor is present, or that its exponents are in
   ladder range (`i₀′ + e_1 r < D_1`, `b_j′ + e_{j+1} t_j < l_{j+1}`): those are C.84's range
   companions, the fleet's, and they consume C.16-at-each-rung.
3. **`towerNorm` is junk-defaulting** (C.83's `towerSolve`, `List.find?`-with-`getD 0`, iterated),
   so every exponent read here inherits that junk off the perimeter, exactly as `n2Exp` does at
   depth 2.

## Divergences from the blueprint text, recorded

* **The pin binder is `F.Pin H₀`** (C.14a's abbreviation), as the signed SIGNATURE writes it —
  C.83 spells the pin out because it predates C.14a. Same `Prop`; `DeepTower F H₀ hpin` accepts
  either, as at C.56a.
* **`let` in the signed bodies is kept.** The twin writes `flavorMonomial` with two `let`s
  (`Δ`, `p`); they are transcribed rather than inlined, so the body is byte-comparable to the
  signed text.

**DEPENDS.** C.83 (`DeepTower`, `ehat`, `Econst`, `towerNorm`, `towerSolve`) · C.14a
(`KeyFrame.Pin`, `stageCoord`, `resLift`) · C.56a (`k2DigitLift` — the `i = 2` instance this
layer must reconcile with) · H.54–H.57 (the base lift, per C-H5, reached only through the C.14a
packaging) — by committed node ID (GC-13(b)).

**PROOF.** definitional.

**SOURCE.** `EFF.GENTOW5.24` (the weight, `[GT5-r1]` TERMINAL); `EFF.GENTOW5.17` (the corrected
flavor display, verbatim, with the FR-A verification `n̂₂(14−3)·Φ₁ = 3⁵xΦ₁` and the fixed-base
non-existence `11/2 ∉ ℤ`); S12.2 via `.17`'s conditionality (the `bound_i` rung).

**TEETH.** FA1-LIFT (22/0: fixed-base flavor non-existence + the re-solved member green) →
executable regression + §13 row; the grid-4 equality instance (`170 = 170 = 170`) → retained.
Neither is dischargeable at these binders (abstract carrier, no numerals — C.15's D7 rider); the
local substitutes are the unfolding checks at the foot of the file.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only). **Partial node: `towerWeight` and `flavorMonomial`
landed; `towerLift` pending in this same file.**
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations -/

/-- **C.84(i) — the level-`i` weight** `wt_i` on exponent data `(v, a, J₁ … J_i)`
(`EFF.GENTOW5.24`, `[GT5-r1]` TERMINAL):

```
wt_i(v, a, J) = ê_i·v + a·(ê_i/e_1)·u_1 + Σ_{1 ≤ j ≤ i−1} J_j·(ê_i/ê_{j+1})·u_{j+1} + J_i·E_i.
```

⚠ **The top variable is priced at `E_i`, a LOWER bound**: the field floor gives only `> E_i` for
the exact top value (`[GT5-r1]`), so `wt_i` under-estimates there and no consumer may read it as
an equality at the top slot. `wt_i` consumes no data beyond the depth-`i` datum. -/
def DeepTower.towerWeight {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i v a : ℕ) (J : ℕ → ℕ) : ℕ :=
  W.ehat i * v + a * (W.ehat i / W.e 1) * W.u 1
    + (∑ j ∈ Finset.Icc 1 (i - 1), J j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
    + J i * W.Econst i

/-- **C.84(ii) — the flavor monomial** `M_{r,t}(m)` at the `[GT5-r2]` CORRECTED display
(`EFF.GENTOW5.17`, verbatim):

```
M_{r,t}(m) = n̂_i(m − Δ(r,t))·x^{e_1 r}·Φ_1^{e_2 t_1}⋯Φ_{i−1}^{e_i t_{i−1}},
Δ(r,t)     = e_1 r·(ê_i/e_1)·u_1 + Σ_{1 ≤ j ≤ i−1} e_{j+1} t_j·(ê_i/ê_{j+1})·u_{j+1}.
```

The **base RE-SOLVES per flavor**: `towerNorm` is applied to the shifted height `m − Δ(r,t)`, not
to a fixed `m`. The frozen fixed-base variant is DEAD (FR-A: the `t₁ = 1` flavor at `m = 14`
demands `π`-exponent `11/2`, so no monomial exists; the re-solved member is `3⁵·x·Φ₁`).

`key : ℕ → Polynomial O` supplies the chain's keys (`key j = Φ_j`); it is a parameter rather than
a field of `DeepTower` because C.83's carrier is the abstract-field GC-7 fallback, which holds no
polynomials.

⚠ **Absence is not implemented**: at `Δ > m` the `ℕ`-subtraction truncates and the flavor returns
a junk monomial rather than being omitted (see the module docstring's trust-boundary note 2). -/
noncomputable def DeepTower.flavorMonomial {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} (W : DeepTower F H₀ hpin r) (key : ℕ → Polynomial O)
    (i rr : ℕ) (t : ℕ → ℕ) (m : ℕ) : Polynomial O :=
  let Δ := F.e₁ * rr * (W.ehat i / W.e 1) * W.u 1
    + ∑ j ∈ Finset.Icc 1 (i - 1), W.e (j + 1) * t j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1)
  let p := W.towerNorm (i - 1) (m - Δ)
  Polynomial.C (π ^ p.1) * Polynomial.X ^ (p.2.1 + F.e₁ * rr)
    * ∏ j : Fin (i - 1), (key (j.1 + 1)) ^ (p.2.2 j + W.e (j + 2) * t (j + 1))

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.towerWeight
#print axioms Uniformity.Density.Tower.DeepTower.flavorMonomial

end AxCheck
