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

**Seven declarations**: the three signed ones (`DeepTower.towerWeight`,
`DeepTower.flavorMonomial`, `DeepTower.towerLift`), the two the lift's body needs — `flavorIdx`
(the multi-index transport `Fin (i−1) → ℕ` ↦ `ℕ → ℕ`) and `DeepTower.deepDigit` (the iterated
`K_{i−1}`-expansion digit read) — and two theorems, `DeepTower.ehat_two` and
`DeepTower.flavorMonomial_depth_two` (the statable half of the node's reconciliation companion).
The twin carries `towerLift` as an **axiom constant** with the body declared "the fleet's" (the
C.45/C.97 rule); it is a **real definition** here, and `deepDigit` is what makes it one.

* `towerWeight W i v a J` — `wt_i`, the level-`i` weight of exponent data.
* `flavorMonomial W key i r t m` — `M_{r,t}(m)`, the base-re-solved flavor monomial.
* `flavorIdx i t` / `deepDigit W i s t r` — the multi-index form, and the digit `d_{r,t}`.
* `towerLift W key i m s` — `lift_i(s; m) = Σ_{r,t} d_{r,t}·M_{r,t}(m)`.
* `ehat_two` (`ê₂ = e₁e₂`) and `flavorMonomial_depth_two` — the `i = 2` monomial IS C.56a's.

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
4. **`towerLift`'s digits are the STRAIGHT expansion digits; the inverse twist rides on the
   argument.** `EFF.GENTOW5.17` glosses `d_{r,t}` as the *inverse-twisted* `K_{i−1}`-expansion
   digits of `c`, and the twist is load-bearing (HE7-T-BADTWIST), but no landed chapter-C object
   supplies `ϑ` — C.85's `theta_dictionary` is an unlanded existence statement and GC-14 defers
   the orientation to chapter D's `[ϑ-TABLE]`. The determination taken here (and flagged at the
   declaration): the twist is the CONSUMER's, i.e. `s` is the already-twisted element. This is
   forced by consistency with the landed `i = 2` instance — C.56a's `k2DigitLift` reads
   `k2Coord`/`stageCoord` untwisted, and this node's own companion demands
   `towerLift`-at-depth-2 `= k2DigitLift`. If the fleet rules otherwise, both nodes change
   together.
5. **The digit read is a power-basis coordinate at every rung** (`deepDigit`), not a
   `Classical.choice` preimage: the discipline the 2026-08-16 repairs installed at C.14a's
   `stageCoord` and C.56a's `k2Coord`, iterated up the chain. What is NOT yet available at depth
   `≥ 3` is the reconstruction identity (`sum_stageCoord`/`sum_k2Coord`'s analogue), because the
   `DeepTower` carrier's rungs are abstract fields tied to `AdjoinRoot (ψ_j)` only by a `RingEquiv`
   (C.83's GC-7 fallback), so `Basis.sum_repr` reassembles the transported element and the
   transport back is the companion's business, not this body's.

## Divergences from the blueprint text, recorded

* **The pin binder is `F.Pin H₀`** (C.14a's abbreviation), as the signed SIGNATURE writes it —
  C.83 spells the pin out because it predates C.14a. Same `Prop`; `DeepTower F H₀ hpin` accepts
  either, as at C.56a.
* **`let` in the signed bodies is kept.** The twin writes `flavorMonomial` with two `let`s
  (`Δ`, `p`); they are transcribed rather than inlined, so the body is byte-comparable to the
  signed text.
* **`towerLift` is a definition, not an axiom.** The twin stub-carries it as an axiom constant
  and says so explicitly ("the variable-length multi-index digit iteration is the fleet's body");
  the C.45 precedent (`towerLabelEquiv`, stub-carried, landed as a real `noncomputable def`) is
  followed. Its **signature is byte-identical to the stub's**.
* **Two helper declarations are added** (`flavorIdx`, `deepDigit`) because the signed body cannot
  be written without them: the display's multi-index is a bounded `(i−1)`-tuple and its digit is
  an iterated basis coordinate. Both are public, since a companion theorem must be able to name
  them (the C.14a `resLift` precedent: `private` is not importable, and these have consumers in
  other files by construction).
* **The depth-2 reconciliation companion is `towerLift T.deepTower … = k2DigitLift`, and it is
  NOT statable yet**: `TowerDatum.deepTower` — the concrete depth-2 chain — is an axiom constant
  of §10 (C.99 region, `leanspec/Leanspec/ChapC.lean:2150`) with no landed file, so the two sides
  cannot be typed against one another. What IS statable is the **exponent-level half**, landed
  below as `DeepTower.flavorMonomial_depth_two`: at `i = 2`, over any `DeepTower` whose rung-2
  data matches a `TowerDatum`, `flavorMonomial` is exactly the monomial factor of C.56a's
  `k2DigitLift` summand. That is where all the index arithmetic lives (the offset `Δ(r,t)`, the
  `n̂₂`-solve, and both exponent shifts), so the residual gap in the companion is only the digit
  map's transport along `deepTower`'s field identification.

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
Neither is dischargeable at these binders (abstract carrier, no numerals — C.15's D7 rider). The
local substitutes are `flavorMonomial_depth_two` — which bites hardest, since it fixes the whole
`i = 2` exponent arithmetic against the independently landed C.56a display, so an `e₁ ↔ e₂` swap,
a dropped `ê`-quotient or a fixed (un-re-solved) base breaks a compile — and the `wt₂` unfolding
`example` at the foot of the file.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only). All three signed declarations landed, `towerLift` as a
real definition, plus the two-rung reconciliation theorem. **Booked, not landed** (recorded so no reader mistakes their absence for a
claim): the exact-height and `wt`-companions, the range clauses (`i₀′ + e_1 r < D_1`,
`b_j′ + e_{j+1} t_j < l_{j+1}`), and the full depth-2 reconciliation to C.56a's `k2DigitLift`
(blocked on §10's `TowerDatum.deepTower`, see the divergences).
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

/-! ### The digit read, and the lift itself -/

/-- The multi-index of the display, `t = (t₁ … t_{i−1})`, in the `ℕ → ℕ` form
`flavorMonomial` and `deepDigit` read it at: `flavorIdx i t j = t_j` for `1 ≤ j ≤ i−1`, and `0`
off that range (no display position reads `t_0` or `t_j` for `j ≥ i`).

`towerLift` sums over `Fin (i−1) → ℕ` — the honest finite index type, one entry per intermediate
rung — and this is the transport to the `ℕ`-indexed form the two signed bodies were signed at. -/
def flavorIdx (i : ℕ) (t : Fin (i - 1) → ℕ) : ℕ → ℕ :=
  fun j => if h : 1 ≤ j ∧ j - 1 < i - 1 then t ⟨j - 1, h.2⟩ else 0

/-- The **iterated digit read**: the `K_{i−1}`-expansion digit of `s ∈ K_i` at the flavor
`(r, t)`, i.e. the coefficient of `η^r·β_1^{t_1}⋯β_{i−1}^{t_{i−1}}` in the residue field.

The recursion descends the chain one rung at a time. At level `i+2` it transports `s` along
C.83's iterate witness `step (i+1) : K_{i+2} ≃+* AdjoinRoot (ψ_{i+1})` and reads the
`t_{i+1}`-coordinate in the **monic power basis** of `ψ_{i+1}` over `K_{i+1}` (dimension
`f_{i+2}`, by C.83's `hψ`), landing in `K_{i+1}`; at level `1` it transports along `base` to the
frame's stage field and takes C.14a's `stageCoord` digit at `r`.

**Both reads are power-basis coordinates, hence invariants of `s`** — this is the discipline the
2026-08-16 repairs installed at C.14a's `stageCoord` and C.56a's `k2Coord`, applied at every rung:
a `Classical.choice` preimage read would carry no degree bound and could not be pinned by any
residue equation. Three junk branches, all total by `Classical.propDecidable` and none reachable
from a consumer inside the perimeter: level `0` (no such digit), a rung outside the chain
(`i + 1 < r` fails, where `step` and monicity are unavailable), and an out-of-range coordinate
(`t_{i+1} ≥ f_{i+2} = dim`, which `towerLift`'s index Finset excludes). -/
noncomputable def DeepTower.deepDigit {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) :
    (i : ℕ) → W.fld i → (ℕ → ℕ) → ℕ → IsLocalRing.ResidueField O
  | 0, _, _, _ => 0
  | 1, s, _, rr => F.stageCoord H₀ hpin (W.base s) rr
  | i + 2, s, t, rr =>
      @dite _ (i + 1 < r) (Classical.propDecidable _)
        (fun h =>
          let hmon : (W.ψ (i + 1)).Monic := (W.hψ (i + 1) (Nat.le_add_left 1 i) h).1
          let pb := AdjoinRoot.powerBasis' hmon
          let s' : AdjoinRoot (W.ψ (i + 1)) := W.step (i + 1) (Nat.le_add_left 1 i) h s
          W.deepDigit (i + 1)
            (if ht : t (i + 1) < pb.dim then pb.basis.repr s' ⟨t (i + 1), ht⟩ else 0) t rr)
        (fun _ => 0)

/-- **C.84(iii) — the level-`i` digit lift** `lift_i(c; m) = Σ_{r,t} d_{r,t}·M_{r,t}(m)`
(`EFF.GENTOW5.17`'s S12.2 TERMINAL display), with `d_{r,t}` the iterated expansion digits
(`deepDigit`) lifted to `O` by C.14a's residue section `resLift`, and `M_{r,t}(m)` the
per-flavor-re-solved monomials (`flavorMonomial`).

The index ranges are the display's: `r < f₁` and `t_j < f_{j+1}` for `1 ≤ j ≤ i−1` (a
`Fin (i−1) → ℕ` bounded by `f_{j+1}`, transported by `flavorIdx`). At `i ≤ 1` the multi-index
type is `Fin 0 → ℕ`, a singleton, so the inner sum is the single flavor `t = 0` — the depth-1
degenerate case, where the display is the frame's own lift.

⚠ **Validity is conditional and is NOT expressed by the body.** S12.2's display holds
`m`-uniformly only above the PRECEDING rung's threshold, `m > bound_i` (**not** `bound_{i+1}`;
the S11.4 bracket is DEAD). Below it a flavor can be absent and `flavorMonomial`'s
`ℕ`-subtraction returns junk instead (trust-boundary note 2). Consumers carry `m > bound_i`.

⚠ **The inverse twist rides on the ARGUMENT, not on this body.** `EFF.GENTOW5.17`'s derivation
sentence calls `d_{r,t}` the *inverse-twisted* `K_{i−1}`-expansion digits of `c` (the flavor
residues are the fixed `τ_i`-cocycle letter units, and the twist by `ϑ_t` is load-bearing, not
cosmetic — HE7-T-BADTWIST). No landed chapter-C object supplies `ϑ`: C.85's `theta_dictionary` is
an existence statement (and unlanded), and GC-14 defers the orientation to chapter D's
`[ϑ-TABLE]`. This body therefore reads the **straight** expansion digits, and the twist is the
consumer's — the element passed as `s` is the already-inverse-twisted one. That is exactly the
convention C.56a's landed `k2DigitLift` fixes at `i = 2` (it reads `k2Coord`/`stageCoord` with no
twist), and it is what this node's own reconciliation companion (`towerLift`-at-depth-2 =
`k2DigitLift`) requires. **Flagged for review**: if the fleet later rules that `ϑ` belongs inside
the lift, THIS body and C.56a's must change together. -/
noncomputable def DeepTower.towerLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (key : ℕ → Polynomial O) (i m : ℕ)
    (s : W.fld i) : Polynomial O :=
  ∑ rr ∈ Finset.range (W.f 1),
    ∑ t ∈ Fintype.piFinset fun j : Fin (i - 1) => Finset.range (W.f (j.1 + 2)),
      Polynomial.C (resLift (W.deepDigit i s (flavorIdx i t) rr))
        * W.flavorMonomial key i rr (flavorIdx i t) m

/-! ### The statable half of the depth-2 reconciliation companion

The blueprint names `towerLift`-at-depth-2 `= k2DigitLift` (C.56a) as this node's companion. The
full statement needs §10's `TowerDatum.deepTower` to type the two sides against each other and is
therefore not yet writable (see the module docstring). Its **exponent-level half is**, and it is
where all the index arithmetic sits: `flavorMonomial` at `i = 2`, over any `DeepTower` whose
rung-2 data matches a `TowerDatum`, is exactly the monomial factor of C.56a's `k2DigitLift`
summand — same flavor offset `Δ(r,t) = e₁e₂h·r + e₂u₂·t₁`, same `n̂₂`-solve, same two exponent
shifts. -/

/-- `ê₂ = e₁·e₂`, the two-rung instance of C.83's `ehat`. Shared by the weight check and the
depth-2 reconciliation below, both of which turn on the two divisions `ê₂/e₁ = e₂` and
`ê₂/ê₂ = 1`. -/
theorem DeepTower.ehat_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) : W.ehat 2 = W.e 1 * W.e 2 := by
  rw [DeepTower.ehat, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]

/-- **The exponent-level depth-2 reconciliation.** Over a `DeepTower` whose rung-2 data matches a
tower datum `T` (`e₂`, `u₂`; the rung-1 data matches by C.83's `he1`/`hu1` fields, unconditionally)
and whose first key is the frame key, the flavor monomial at `i = 2` IS the monomial of C.56a's
`k2DigitLift` summand at flavor `(r, t₁)`:

* the offset is `Δ = e₁e₂h·r + e₂u₂·t₁` — C.56a's, on the nose (this is where `ê₂/e₁ = e₂` and
  `ê₂/ê₂ = 1` are consumed, hence the two positivity hypotheses);
* the base is `n̂₂` re-solved at `m − Δ` — C.83's `towerNorm 1` IS §8's `n2Exp` once the rung data
  agrees;
* the `x`-exponent shifts by `e₁r` and the `Φ′`-exponent by `e₂t₁`.

What this does NOT say is the other half of the companion: that the DIGIT `d_{r,t}` agrees with
C.56a's `resLift (stageCoord (k2Coord …))`. That needs the field identification carried by §10's
`TowerDatum.deepTower` (`fld 2 ≃+* AdjoinRoot T.ψ₂`), which has no landed file. -/
theorem DeepTower.flavorMonomial_depth_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (T : TowerDatum F H₀ hpin) (key : ℕ → Polynomial O)
    (hkey : key 1 = F.key) (hWe2 : W.e 2 = T.e₂) (hWu2 : W.u 2 = T.u₂)
    (he₁ : 0 < F.e₁) (he₂ : 0 < T.e₂) (rr : ℕ) (t : ℕ → ℕ) (m : ℕ) :
    W.flavorMonomial key 2 rr t m
      = Polynomial.C (π ^ (n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).1)
          * Polynomial.X ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.1
              + F.e₁ * rr)
          * F.key ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.2
              + T.e₂ * t 1) := by
  have hehat : W.ehat 2 = F.e₁ * T.e₂ := by rw [W.ehat_two, W.he1, hWe2]
  have hΔ : F.e₁ * rr * (W.ehat 2 / W.e 1) * W.u 1
      + ∑ j ∈ Finset.Icc 1 (2 - 1), W.e (j + 1) * t j * (W.ehat 2 / W.ehat (j + 1)) * W.u (j + 1)
      = F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1 := by
    norm_num [Finset.Icc_self, hehat, W.he1, W.hu1, hWe2, hWu2,
      Nat.mul_div_cancel_left _ he₁, Nat.div_self (Nat.mul_pos he₁ he₂)]
    ring
  have hnorm : W.towerNorm 1 (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))
      = ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).1,
         (n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.1,
         Fin.snoc (fun x : Fin 0 => x.elim0)
           (n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.2) := by
    simp [DeepTower.towerNorm, n2Exp, hWe2, hWu2]
  have hsnoc : (Fin.snoc (fun x : Fin 0 => x.elim0)
      (n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.2 : Fin 1 → ℕ) 0
      = (n2Exp T (m - (F.e₁ * T.e₂ * F.h * rr + T.e₂ * T.u₂ * t 1))).2.2 := rfl
  rw [DeepTower.flavorMonomial]
  simp only [hΔ, show (2 - 1 : ℕ) = 1 from rfl, hnorm]
  congr 1
  simp [hsnoc, hkey, hWe2]

end Uniformity.Density.Tower

/-! ## Unfolding check — the weight's four terms at `i = 2`

An `example`, not a declaration: the local substitute for the §13 numeral row (see the module
docstring's TEETH). It pins which quotient prices which variable — `a` at `ê₂/e₁ = e₂` (NOT at
`e₁`), the intermediate `J₁` at `ê₂/ê₂ = 1` times `u₂`, and the top `J₂` at `E₂` — so an
`e₁ ↔ e₂` swap or a misplaced `ê`-quotient cannot survive it. -/

section UnfoldingChecks

open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `wt₂(v, a, J) = e₁e₂·v + a·e₂·u₁ + J₁·u₂ + J₂·E₂`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ} (W : DeepTower F H₀ hpin r)
    (v a : ℕ) (J : ℕ → ℕ) (he₁ : 0 < W.e 1) (he₂ : 0 < W.e 2) :
    W.towerWeight 2 v a J
      = W.e 1 * W.e 2 * v + a * W.e 2 * W.u 1 + J 1 * W.u 2 + J 2 * W.Econst 2 := by
  have hehat : W.ehat 2 = W.e 1 * W.e 2 := W.ehat_two
  norm_num [DeepTower.towerWeight, Finset.Icc_self, hehat,
    Nat.mul_div_cancel_left _ he₁, Nat.div_self (Nat.mul_pos he₁ he₂)]

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.towerWeight
#print axioms Uniformity.Density.Tower.DeepTower.flavorMonomial
#print axioms Uniformity.Density.Tower.flavorIdx
#print axioms Uniformity.Density.Tower.DeepTower.deepDigit
#print axioms Uniformity.Density.Tower.DeepTower.towerLift
#print axioms Uniformity.Density.Tower.DeepTower.ehat_two
#print axioms Uniformity.Density.Tower.DeepTower.flavorMonomial_depth_two

end AxCheck
