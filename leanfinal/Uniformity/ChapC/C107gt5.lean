/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130pk

/-!
# Uniformity.ChapC.C107gt5 — Chapter C — the GENTOW5 `𝒲`-family consumer matrix (unit GT5)

Unit GT5. Target: the leanfinal twins of the five signed `§9/§10` names of the GENTOW5-`𝒲`
family — leanspec NODE C.89 (`GENTOW5W`, `Wle`, `gentow5w_two`, `gentow5w_one_shape`) and NODE
C.90 (`gentow5_key_certificate`), `ChapC.lean:3764–3807`. Per
`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` §6, all five signatures type against
exactly the accessor set `keyAt, ExactGrade, Rgr, Rres, KP, nuEquiv, letterZ` — all landed in
`C130pk.lean` — so every name here at least *elaborates*. Only two land as declarations; the
other three hit named, source-anchored gaps (the GTA/GTB/GSW adjudication genre: an omitted
source antecedent, not derivable from the current class fields) and are recorded, not bridged.

## What lands, and at what honesty grade

* **`GENTOW5W` [def] — FULL LANDING.** Byte-faithful twin (leanspec `ChapC.lean:3764–3768`).
  No proof obligation: per the C.89 docstring, "the definition IS the carrier" — `GENTOW5W`
  is the `∃`-closure of the single-`w` ratio law, not an assertion that it holds.  This is the
  name `C130pk.lean`'s own docstring names as deliberately NOT landed there ("the GENTOW2
  supply layer stays in leanspec until its own transcription nodes") and DT2 explicitly
  skipped as "FGMNCalculus-adjacent" (`C141defs.lean`'s "Not landed" list) — landed here.
* **`Wle` [def] — FULL LANDING.** Byte-faithful twin (`ChapC.lean:3770–3773`), the depth-`n`
  cumulative closure of `GENTOW5W` over each `W.trunc i hi`.  Distinct from
  `Uniformity.Density.Gauge.Wle` (chapter D's `D55.lean`, an unrelated same-named cumulative
  hypothesis over `ℕ → Prop`): different namespace, different signature, no collision, no
  shared proof content.
* **`gentow5w_two` — BLOCKED (omitted source antecedent, GSW cascade genre).** See §1 below.
* **`gentow5w_one_shape` — BLOCKED (same genre, plus OPEN-LETTERS).** See §2 below.
* **`gentow5_key_certificate` — BLOCKED (omitted admissibility conjunct, GTB genre).** See §3.

No declaration is emitted for the three blocked names: per the parent CLAUDE.md statement-fence
and the GTA precedent (`runs/wave-b/verdict_GTA.md`), a substitute would require re-signing the
leanspec binders (not this unit's authority — CFIX owns spec tooling) or a new axiom, both
excluded by the task's rules.

## §1 — `gentow5w_two`: BLOCKED

Leanspec (`ChapC.lean:3775–3779`):

```lean
axiom gentow5w_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower F H₀ hpin 2) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 2 < u') :
    GENTOW5W W e' f' u' I
```

The C.89 module docstring names its intended proof route explicitly: "(i) the `i = 2` discharge
from C.99". C.99's landed leanfinal twin (`gentow2_Bpp`, `C99r.lean`) proves the identical
per-`t` equation `Rgr(...) * thetaRatio(...) = (Rgr u' (chainNorm r u'))^(f'-t)` — but ONLY
after gaining, on top of `hr/he'/hcop/hfloor`, four supply families never carried by
`gentow5w_two`'s binders:

* `hprev : I.PrevGrade u'` ([A-C.13], restored `Rgr_mul` premise);
* `hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u'))`;
* `hnormdeg : ∀ d, 0 < d → d ≤ f' → (I.chainNorm r (d*u')).natDegree < (I.keyAt r).natDegree`;
* `hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0`.

These are exactly the class-external facts the informal source states as inputs, not
consequences (`GENTOW2_PROOF_2026-08-09.md` S5.2, ll.740–744, quoted in `C99r.lean`'s own
docstring: "ladder monomials, `deg < m₃`, single-point `N₃`-polygon, exact grades `κ̄` resp.
`β_t` (B-1)"). No `FGMNCalculus` field supplies `ExactGrade`/degree/nonzero facts about
`chainNorm` unconditionally — `chainNorm` is a bare product-of-keys polynomial (C.92's own
def), and the class's only law about it is via `Rres_recipe`/`Rgr_ne_zero`, both of which need
these same facts as premises, not conclusions.

This gap is already named, exactly, by the standing adjudication — quoted verbatim
(`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` §2, "Cascade flag"):

> "**Cascade flag (not enacted here):** C.89's `gentow5w_two` (docstring: "the i = 2 discharge
> from C.99") and `gentow5w_one_shape` will need the same three families when their landing
> unit runs; flagged for the next A-C amendment."

and §10 item 3:

> "**C.89 cascade** — `gentow5w_two`/`gentow5w_one_shape` consume the C.99 genre and will need
> the B-1 supply binders when their unit runs."

That amendment has not been enacted (confirmed: neither name appears in the A-C.12 verdict
table nor in any later A-C amendment commit; `rg -n "gentow5w" docs/in-progress/*.md` finds
only the two cascade-flag lines above). Landing `gentow5w_two` today would require silently
adding these binders to the leanfinal twin's own signature, which is a statement change to a
signed name outside this unit's scope (`leanspec/` is read-only here) — so per the task's
instructions the gap is recorded and the node is left undeclared. **No declaration emitted.**

## §2 — `gentow5w_one_shape`: BLOCKED (compounding gap)

Leanspec (`ChapC.lean:3781–3787`):

```lean
axiom gentow5w_one_shape {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower F H₀ hpin 1) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 1 < u') :
    ∃ k : ℕ, ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (I.chainNorm 1 ((f' - t) * u')) * I.thetaRatio (f' - t)
        = (I.letterZ 1 ^ k) ^ (f' - t)
```

This inherits §1's gap in full (the same `hprev`/`hnorm`/`hnormdeg`/`hnormz` family is needed
to control `chainNorm 1` at every grade `(f'-t)*u'`), and adds a SECOND, independent gap: the
conclusion additionally asserts `I.Rgr u' (I.chainNorm 1 u') = I.letterZ 1 ^ k` for some `k`
(the `w = letterZ 1 ^ k` shape, C.89's "(ii) the `i = 1` SHAPE with the tie OPEN"). The only
class law mentioning `letterZ` is `letterZ_ne_zero` (pure nonvanishing); no field ties `Rgr` or
`chainNorm` reads to any power of `letterZ`. This is exactly the audited **OPEN-LETTERS** /
**OPEN-EVAL-ISO** gap GTB records for the sibling node C.102 (`runs/wave-b/verdict_GTB.md`):

> "No class field relates `letterZ` to `ρ` or to `AdjoinRoot.root T.ψ₂`. Audited gap
> **OPEN-EVAL-ISO**/**OPEN-LETTERS** (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md`
> §5)."

and the U9/GSW disposition of the sibling `theta_letter_valued` (`GENTOW2_ADJUDICATION
_2026-08-24.md` §3): "the letter clause needs the value-0-monomial residue laws (Def 3.12
γ-construction + the exponent-lattice split ...) — U7 §5's OPEN-LETTERS row verbatim." No
class field and no landed carrier expresses this tie. **No declaration emitted.**

## §3 — `gentow5_key_certificate`: BLOCKED (omitted admissibility conjunct)

Leanspec (`ChapC.lean:3793–3807`), clause (a) only (clause (b) is the separately BOOKED
Cor 6.3 residual, per the C.90 docstring and
`docs/in-progress/LEVEL_GENERAL_DESIGN_2026-08-24.md` §6.1: "The enacted `leanspec` declaration
`gentow5_key_certificate` is only C.90(a)... There is no term-level Corollary 6.3 conclusion in
the current signature"). The signed `hadm` reads:

```lean
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f') :
    (I r le_rfl).KP Φnext ∧ ...
```

The only class route to `(I r le_rfl).KP Φnext` is `FGMNCalculus.KP_criterion`, whose FIFTH
antecedent is `(Rres g).coeff 0 ≠ 0` — a conjunct `hadm` above does not supply (only 2 of the
3 needed conjuncts: `Irreducible` and `natDegree = f'`, missing the nonzero-constant-term
clause). This is not a bookkeeping accident: the informal source states the admissibility
hypothesis with all three conjuncts explicitly (`lean/notes/openmath/GENTOW5_PROOF_2026-08-09
.md`, ll.793–796, the "(a) KEY CERTIFICATE" clause):

> "`psi_{i+1}^{(w_i)}` is GENTOW2-A-ADMISSIBLE at each value of `w_i` — monic irreducible of
> degree `f_{i+1}` with **nonzero constant term** (`y -> w*y` is a substitution automorphism;
> B'' + the PE5 verification 'psi_3^{(w)} is verifiably admissible for every w in K_2^x' ...)"

i.e. the source's own admissibility notion is exactly `KP_criterion`'s five-conjunct package
(monic, degree, irreducible-residual, residual-degree, residual-nonzero-constant-term); the
signed `hadm` drops the last conjunct. This is the identical genre GTB records for the sibling
node C.103 pre-resign (`runs/wave-b/verdict_GTB.md`): "The only route to `I.KP g` is
`KP_criterion`, which needs `(Rres g).coeff 0 ≠ 0` as its 5th antecedent. The signed `hadm`
hypothesis supplies only `Irreducible (Rres g)` and `(Rres g).natDegree = f'`... No other class
field derives it generically." C.103's analogous gap WAS since repaired by amendment A-C.12
(`gentow2_A`'s `hadm` now carries all three conjuncts, `C99r.lean`'s `gentow2_A_supply`) — but
that amendment's verdict table (`GENTOW2_ADJUDICATION_2026-08-24.md` §0) lists only
C.99/C.100/C.101/C.102/C.103/C.85/C.88/C.106; **C.90 (`gentow5_key_certificate`) is absent from
it and has not been touched by any enacted A-C amendment** (confirmed:
`rg -n "gentow5_key_certificate" docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` finds
no hit).

Secondary observation (not needed to establish the verdict above, recorded for completeness):
even with the coeff-zero conjunct supplied, `KP_criterion`'s second antecedent
`Φnext.natDegree = e' * f' * (keyAt r).natDegree` would still need `(keyAt r).natDegree =
W.Dcum r` via `keyAt_deg`, which is only asserted for `1 ≤ i ≤ r` — and no binder of
`gentow5_key_certificate` supplies `1 ≤ r`. At `r = 0` this leg is likewise unavailable.

**No declaration emitted.**

## DEPENDS

C.83 (`DeepTower`) · C130pk (`FGMNCalculus`, `chainNorm`, `thetaRatio`) — all landed, imported
transitively.

## Status

Two declarations landed (`GENTOW5W`, `Wle`): sorry-free, axiom-free (Lean core only) — both are
`Prop`-valued defs with no proof term beyond the structural `∃`/`∀` closure, so there is no
proof obligation to discharge. Three names (`gentow5w_two`, `gentow5w_one_shape`,
`gentow5_key_certificate`) are recorded BLOCKED above with quoted source gaps; no declaration,
no `sorry`, no new `axiom`, no `unsafe`, no statement weakening.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

/-! ## NODE C.89 — the `𝒲` hypothesis family: `GENTOW5W`, `Wle` (defs, no proof content) -/

/-- **NODE C.89, `GENTOW5W`** — the `𝒲` hypothesis family, single-`w` form in the RATIO
carrier (leanspec byte-faithful twin, `ChapC.lean:3764–3768`, modulo the design-§7 universe
substitution `DeepTower ↦ DeepTower.{0, uKt}`). The definition IS the carrier: no axiom asserts
it holds at any `i`; C.99 discharges it at `i = 2` under extra supply hypotheses (§1 of this
file's docstring), the `i = 1` shape and `i ≥ 3` cases stay OPEN per the C.89 docstring. -/
-- [A-C.21, 2026-08-27 — ANORM/verdict_MSG2] SUPERSEDED CARRIER, RETAINED VERBATIM.
-- The signed `GENTOW5W`/`thetaRatio` now read `Rgr` at the CLEARED grades
-- `e'·((f'-t)·u')`; this pre-A-C.21 carrier is off-grade (reads zero) and is FALSE at
-- the honest μ₃ instance (`C132sg3.s2Mu3_gentow5w_old_refuted`).  Kept byte-unchanged
-- because the do-not-edit record `C132sg2.lean` states its theorems against it.  The
-- A-C.21 twins are `GENTOW5WCleared`/`FGMNCalculus.thetaRatioCleared`/`WleCleared`
-- (`C132sg3.lean`).
def GENTOW5W {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u') : Prop :=
  ∃ w : W.fld r, w ≠ 0 ∧ ∀ t, t < f' →
    I.Rgr ((f' - t) * u') (I.chainNormBelow r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = w ^ (f' - t)

/-- **NODE C.89, `Wle`** — the cumulative `𝒲_{≤n}` closure of `GENTOW5W` at every rung `3 ≤ i
≤ n` of a truncation family (leanspec byte-faithful twin, `ChapC.lean:3770–3773`). Distinct
from `Uniformity.Density.Gauge.Wle` (`D55.lean`, chapter D's unrelated cumulative hypothesis
over `ℕ → Prop`): different namespace, different signature, no shared content, no collision. -/
def Wle {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') (n : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ n → ∀ hi : i ≤ r, GENTOW5W (W.trunc i hi) e' f' u' (I i hi)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.GENTOW5W
#print axioms Uniformity.Density.Tower.Wle

end AxCheck
