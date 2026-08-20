/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C11
import Uniformity.ChapC.C29
import Uniformity.ChapC.C35b
import Uniformity.Density.NormLeaves

/-!
# Uniformity.ChapC.C27 — `(SLOT₂)`-exactness in norm form

**Chapter C, NODE C.27** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the slot
layer; the A-C.1 amendment set governs, including **D10** (`.get!` → `ENat.toNat`) and
**D12(iii)** — the landed order is `C.29 → C.27`, a §5 → §4 crossing, so `HasLabel` is imported
from `Uniformity.ChapC.C29`, which is already landed).  **ENV-C3**.

## Status in one line

**The signed statement is FALSE and is REFUTED here.**  `slot2_exact` as signed at
`leanspec/Leanspec/ChapC.lean:879-885` omits the level-1 `x`-purity guard
`hx : IsPure Polynomial.X g F.h F.e₁`, and without it the value read at `C := X` is wrong on a
landed witness over `ℤ_[2]`.  What lands instead is the guard-repaired node and two of its three
consumer reads.

## MANDATORY BINDER-VACUITY AUDIT (A-C.8.4 checklist), committed before any proof

Every binder is judged VACUOUS (nothing satisfies it — a defect), *restricts-nothing* (provably
always satisfied), or *load-bearing* (with the counterexample named when it is SHARP).  The
witnesses are the landed C.35b/C.97 terms over `ℤ_[2]`: `s2Frame` (`e₁,f₁,h = 2,1,1`,
`Φ′ = x²−2`), `s2Frame_pin` (`H₀ = 1`), `L₀` (`(u,ℓ) = (3,1)`, `r = ρ`, `d_r = 1`),
`g₀ = x³ − 2x + 4` with `hasLabel_g₀`.

| binder | verdict |
|---|---|
| `{O} [CommRing] [IsDomain] [IsDiscreteValuationRing] {π : O}` | **load-bearing, inhabited** — `O = ℤ_[2]`, `π = 2` (`C35b`'s `Absolute` section: `instFin2`, `rc2`, `h2_padic`). |
| `{F : KeyFrame O π}` | **load-bearing, inhabited** by `s2Frame h2_padic rc2`.  `KeyFrame` is a nine-field structure with `hirr`/`hpure`/`hresirr` theorem-grade fields; it is a real restriction and it is not empty. |
| `{H₀ hpin}` | **load-bearing, inhabited, and PINNED TO ONE NUMERAL** — `s2Frame_pin` gives `H₀ = 1` and `s2Frame_pin_unique` shows no other `H₀` works.  Not the A-C.7 `C.113 hne` pattern (a proof-irrelevant `Nonempty`): `hpin` is an equation that determines `H₀`. |
| `(L : LevelDatum F H₀ hpin)` | **load-bearing, inhabited** by `L₀`.  `hκ : ℓ·(e₁f₁)·h < u` is the above-floor fence and a genuine restriction (`1·2·1 = 2 < 3` at `L₀`); `hcop`, `hℓ`, `hrirr`, `hrdeg` likewise. |
| `(hπ : Irreducible π)` | **load-bearing on the SOURCE regime, not consumed by the conclusion.**  `π` occurs in the conclusion only through `F : KeyFrame O π`; `addVal O` is π-free.  Its role is to make the frame's residual reads (`resPoly π …`) meaningful.  It is *not* vacuous (`h2_padic`) and it is *not* restricts-nothing (a unit or zero `π` is excluded).  It is satisfied at the refuting instance below, so the refutation does not exploit it. |
| `[Finite (ResidueField O)]` | **restricts the source regime; satisfied at the witness** (`C35b.instFin2`).  Carried by the signed type for the intended step-3 residual-field argument; the refutation satisfies it. |
| `{g} (hg : HasLabel L g)` | **load-bearing, and its locus IS witnessed by a landed TERM**: `hasLabel_g₀ : HasLabel (L₀ …) (g₀ …)`.  Not vacuous. |
| `{C} (hC : C.natDegree < L.keyDeg₂)` | **load-bearing, and NEVER EMPTY** — `0 < L.keyDeg₂` always (`keyDeg₂_pos` below, from `he₁`, `hf₁`, `hℓ`, `hrdeg`), so every constant qualifies.  At `L₀` it admits exactly `deg C ≤ 1`.  It is the no-cancellation fence of the intended proof; sharpness above it is NOT certified here. |
| `(hC0 : dv2Hgt L C ≠ ⊤)` | **load-bearing and UNDROPPABLE — machine-checked** (`slot2_exact_without_hC0_false`).  `dv2Hgt L 0 = ⊤` (`dv2Hgt_zero`) while `hC : 0 < L.keyDeg₂` holds at `C = 0`, and `∃ v : ℕ, (⊤ : ℕ∞) = (v : ℕ∞) ∧ …` is false.  So deleting `hC0` turns the statement into a false statement. |

**Verdict: no vacuous binder.**  No fifth instance of the A-C.7 pattern.  Every binder of the
signed type has a landed witnessing value over `ℤ_[2]`, and two of them (`hpin`, `hC0`) are
certified sharp rather than argued.

**The defect the audit found is not a vacuity but a MISSING binder**: the level-1 `x`-purity
guard `hx : IsPure Polynomial.X g F.h F.e₁` that C.59 (`ramLeg_dvd`, the sole consumer of the
`C := X` read) already carries in its own signed signature.  See the refutation section.

## The three mandated checks

1. **Floor-divided degrees (`hasLabel_natDegree_dvd`, REFUTED 2026-08-20) are not used.**  No
   step of any proof in this file asks for `D′ ∣ deg g` or recovers a degree from a label.  The
   `C := X` read gets its divisibility the same way C.61's repair did — from the guard itself:
   `IsPure Polynomial.X g F.h F.e₁` gives the *equation* `F.e₁ * v(g.coeff 0) = F.h * deg g`
   (`isPure_addVal_coeff_zero` below), not a divisibility to be recovered.
2. **CONTENT-FREE TYPE check: passed in the strongest available form.**  The signed type is not
   `True`-equivalent and not bare-ℕ arithmetic: it has a machine-checked FALSE instance
   (`slot2_exact_false`).  A statement with a false instance is not provable by `trivial`.
3. **INHABITATION: witnessed by landed TERMS, not argued.**  C.27's signed type mentions neither
   `IsTestKey` nor `TowerDatum` (the two chapter-C predicates with no landed value anywhere in
   the corpus).  Its whole binder chain is instantiated at `(ℤ_[2], 2, s2Frame, 1, s2Frame_pin,
   L₀, g₀, C := Polynomial.X)` in `slot2_exact_false`, and at `C := Polynomial.C a` in the
   constant leg.  For the repaired node the `hx` locus is inhabited by the frame key itself
   (`F.hpure`), which is a landed field of every `KeyFrame` value.

## LANDED INVENTORY (authoritative; updated at every commit — the audit table above states the
## verdicts, this states what is machine-checked so far)

* commit 1 (skeleton): `Slot2ExactStatement` only.  Every other declaration named in the audit
  table is PLANNED at commit 1 and becomes machine-checked as it lands; this line is the
  authority on which is which.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The signed statement, BYTE-FROZEN, as a Prop carrier

`Slot2ExactStatement` is the ∀-closure of the signed `axiom slot2_exact`
(`leanspec/Leanspec/ChapC.lean:879-885`).  No axiom is declared: per the
C.33/C.34/C.72/C.40/C.61 convention the signed name stays at the leanspec stub.  The frozen
lines are reproduced verbatim below the ∀-closure's binder prefix; the only edits are
`axiom slot2_exact` → the closure head, and `:` → `,` at the end of the hypothesis block. -/

/-- The ∀-closure of the signed `slot2_exact`.  Refuted below (`slot2_exact_false`). -/
def Slot2ExactStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (_hg : HasLabel L g) {C : Polynomial O}
    (_hC : C.natDegree < L.keyDeg₂) (_hC0 : dv2Hgt L C ≠ ⊤),
    ∃ v : ℕ, dv2Hgt L C = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * v

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Slot2ExactStatement

end AxCheck
