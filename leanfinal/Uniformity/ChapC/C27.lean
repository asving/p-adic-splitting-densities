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

* commit 1 (skeleton): `Slot2ExactStatement`.
* commit 2 (the refutation): `keyDeg₂_pos`, `dv2Hgt_zero`, `Slot2ExactWithoutHC0Statement`,
  `slot2_exact_without_hC0_false` (the `hC0`-undroppability certificate), the `C := X` slot-height
  computation (`dev_X_zero`, `dev_X_one`, `dvhgt_X_0`, `dvhgt_X_1`, `dv2hgt_X`, `keyDeg₂_L₀`), the
  norm read (`g₀_coeff_zero`, `addVal_norm_g₀_X`), and **`slot2_exact_false` — the signed
  statement is FALSE**.
* Anything named in the audit table and not listed above is PLANNED, not machine-checked.
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

/-! ## Two frame-level facts the audit table quotes -/

private theorem nsmul_top_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k => rw [succ_nsmul]; exact WithTop.add_top _

/-- `0 < L.keyDeg₂` always: `keyDeg₂ = (e₁f₁)·ℓ·d_r` and all four factors are positive
(`F.he₁`, `F.hf₁`, `L.hℓ`, `L.hrdeg`).  So `hC : C.natDegree < L.keyDeg₂` is **never an empty
hypothesis** — every constant `C` satisfies it. -/
theorem keyDeg₂_pos {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    0 < L.keyDeg₂ := by
  rw [LevelDatum.keyDeg₂]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) L.hℓ) L.hrdeg

/-- `dv2Hgt L 0 = ⊤`.  This is what makes `hC0` undroppable: `C = 0` passes `hC`
(`keyDeg₂_pos`) and its level-2 slot height is `⊤`, so no `v : ℕ` can satisfy the first
conjunct of the conclusion. -/
theorem dv2Hgt_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    dv2Hgt L (0 : Polynomial O) = ⊤ := by
  rw [dv2Hgt, dvSupp]
  simp only [Polynomial.natDegree_zero, show Finset.range (0 + 1) = {0} from rfl,
    Finset.inf_singleton]
  rw [dvHgt, show dev F.key (0 : Polynomial O) 0 = 0 from Polynomial.zero_modByMonic _,
    KeyFrame.stageHeight, suppVal_zero_eq_top F.he₁, nsmul_top_pos L.hℓ]
  simp

/-- The signed statement **with `hC0` deleted**. -/
def Slot2ExactWithoutHC0Statement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (_hg : HasLabel L g) {C : Polynomial O}
    (_hC : C.natDegree < L.keyDeg₂),
    ∃ v : ℕ, dv2Hgt L C = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * v

/-! ## The frame's own two elementary reads

`keyDeg_pos` and the level-1 purity value law.  The purity value law is the mechanism the
refutation isolates: it is the CONTENT of the `C := X` read, and it is a theorem of `IsPure`,
not of `HasLabel`. -/

theorem keyDeg_pos (F : KeyFrame O π) : 0 < F.key.natDegree := by
  rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁

theorem key_degree_pos (F : KeyFrame O π) : 0 < F.key.degree :=
  Polynomial.natDegree_pos_iff_degree_pos.1 (keyDeg_pos F)

/-- **the level-1 purity value law.**  If the `x`-polygon of a monic `g` is the single side of
slope `−h/e₁` (`IsPure Polynomial.X g h e₁`, B.34), then
`e₁ · v(g.coeff 0) = h · deg g` on the nose.

This is what the signed C.27 asserts at `C := X`, and `HasLabel` does not supply it: at
`(s2Frame, L₀, g₀)` the left side is `2·2 = 4` and the right side is `1·3 = 3`
(`slot2_exact_false`). -/
theorem isPure_addVal_coeff_zero {g : Polynomial O} (hg : g.Monic) {h e : ℕ}
    (hx : IsPure Polynomial.X g h e) :
    e • addVal O (g.coeff 0) = ((h * g.natDegree : ℕ) : ℕ∞) := by
  obtain ⟨h0, hn⟩ := hx
  -- the right endpoint of the `x`-polygon: `deg g / deg X = deg g`
  rw [Polynomial.natDegree_X, Nat.div_one] at hn
  rw [OnSide, npHgt_X, Nat.mul_zero, Nat.cast_zero, add_zero] at h0
  rw [OnSide, npHgt_X, hg.coeff_natDegree, AddValuation.map_one, smul_zero, zero_add] at hn
  rw [h0, ← hn]

end Uniformity.Density.Tower

/-! ## The refutations, absolute over `ℤ_[2]` -/

namespace Uniformity.Density.Tower.C27Refute

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ### 1. `hC0` is UNDROPPABLE -/

/-- **The signed statement minus `hC0` is FALSE.**  Take `C = 0` at the landed label witness:
`hC` holds (`keyDeg₂_pos`) and `dv2Hgt L₀ 0 = ⊤` (`dv2Hgt_zero`), so no `v : ℕ` exists. -/
theorem slot2_exact_without_hC0_false : ¬ Slot2ExactWithoutHC0Statement := by
  intro hax
  obtain ⟨v, hv, -⟩ := hax (L₀ h2_padic rc2) h2_padic (hasLabel_g₀ h2_padic rc2)
    (C := (0 : Polynomial ℤ_[2])) (by simpa using keyDeg₂_pos (L₀ h2_padic rc2))
  rw [dv2Hgt_zero] at hv
  exact (ENat.coe_ne_top v) hv.symm

/-! ### 2. The `Φ′`-development and the level-2 slot height of `C := X` at the landed frame -/

theorem dev_X_zero : dev (s2Key O) (Polynomial.X : Polynomial O) 0 = Polynomial.X := by
  show (Polynomial.X : Polynomial O) %ₘ (s2Key O) = Polynomial.X
  rw [Polynomial.modByMonic_eq_self_iff s2Key_monic, s2Key_deg, Polynomial.degree_X]
  decide

omit [Finite (ResidueField O)] in
theorem dev_X_one : dev (s2Key O) (Polynomial.X : Polynomial O) 1 = 0 :=
  dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ 1
    (by rw [Polynomial.natDegree_X, s2Key_natDegree]; norm_num)

include h2 hq in
theorem dvhgt_X_0 : dvHgt (s2Frame h2 hq) (Polynomial.X : Polynomial O) 0 = 1 := by
  rw [dvHgt, key_eq, dev_X_zero, sh_X h2 hq]

include h2 hq in
theorem dvhgt_X_1 : dvHgt (s2Frame h2 hq) (Polynomial.X : Polynomial O) 1 = ⊤ := by
  rw [dvHgt, key_eq, dev_X_one, sh_zero h2 hq]

include h2 hq in
/-- **the level-2 slot height of `X` is `ℓ·h = 1`** at `(s2Frame, L₀)` — the blueprint's own
`dv2Hgt = ℓh` read at the linear coefficient. -/
theorem dv2hgt_X : dv2Hgt (L₀ h2 hq) (Polynomial.X : Polynomial O) = 1 := by
  rw [dv2Hgt, show (L₀ h2 hq).u = 3 from rfl, show (L₀ h2 hq).ℓ = 1 from rfl, dvSupp]
  simp only [Polynomial.natDegree_X, show Finset.range (1 + 1) = {0, 1} from rfl,
    Finset.inf_insert, Finset.inf_singleton, dvhgt_X_0 h2 hq, dvhgt_X_1 h2 hq]
  simp

include h2 hq in
/-- `keyDeg₂ = (e₁f₁)·ℓ·d_r = 2·1·1 = 2` at `L₀`, so `C := X` clears `hC`. -/
theorem keyDeg₂_L₀ : (L₀ h2 hq).keyDeg₂ = 2 := by
  rw [LevelDatum.keyDeg₂, e1_eq h2 hq, f1_eq h2 hq, show (L₀ h2 hq).ℓ = 1 from rfl,
    show (L₀ h2 hq).r = ρ h2 hq from rfl, ρ_natDegree h2 hq]

/-! ### 3. The norm read at `C := X`: `N(mk g₀ X) = ±g₀(0) = ±4`, of valuation `2` -/

omit [Finite (ResidueField O)] in
theorem g₀_coeff_zero : (g₀ O).coeff 0 = 4 := by simp [g₀]

include h2 in
theorem addVal_norm_g₀_X :
    addVal O (Algebra.norm O (AdjoinRoot.mk (g₀ O) Polynomial.X)) = ((2 : ℕ) : ℕ∞) := by
  have hmk : AdjoinRoot.mk (g₀ O) Polynomial.X = AdjoinRoot.root (g₀ O) := rfl
  rw [hmk, norm_adjoinRoot_root g₀_monic (by rw [g₀_natDegree]; norm_num), g₀_natDegree,
    AddValuation.map_mul, g₀_coeff_zero,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 (isUnit_one.neg.pow 3),
    show (4 : O) = (2 : O) ^ 2 from by norm_num, addVal_two_pow h2 2, zero_add]

/-! ### 4. THE REFUTATION -/

/-- **C.27 AS SIGNED IS FALSE.**  At `(ℤ_[2], π = 2, s2Frame, H₀ = 1, s2Frame_pin, L₀,
g₀ = x³ − 2x + 4, C := X)` every hypothesis of the signed `slot2_exact` holds —
`hπ = h2_padic`, `hg = hasLabel_g₀`, `hC : 1 < 2` (`keyDeg₂_L₀`), `hC0 : 1 ≠ ⊤`
(`dv2hgt_X`) — while the conclusion demands
`(F.e₁·L.ℓ)·v(N(mk g₀ X)) = deg g₀ · dv2Hgt L₀ X`, i.e. `2·2 = 3·1`, i.e. `4 = 3`.

**Mechanism.**  `dv2Hgt L X = ℓ·h` is the level-1 `x`-slot value the frame *declares*; the norm
side is `v(g₀.coeff 0) = 2`, the value `g₀` *actually has* at the `x`-polygon.  The identity is
`F.e₁ · v(g₀.coeff 0) = F.h · deg g₀` (`2·2 = 1·3`, false), which is exactly the level-1
`x`-purity of `g` — and `HasLabel L g` does not imply it: it constrains the `Φ′`-polygon, not the
`x`-polygon.  `g₀` is the landed witness of that separation (`C35b`, `hx_g₀_false` at C.61). -/
theorem slot2_exact_false : ¬ Slot2ExactStatement := by
  intro hax
  obtain ⟨v, hv, heq⟩ := hax (L₀ h2_padic rc2) h2_padic (hasLabel_g₀ h2_padic rc2)
    (C := (Polynomial.X : Polynomial ℤ_[2]))
    (by rw [Polynomial.natDegree_X, keyDeg₂_L₀ h2_padic rc2]; norm_num)
    (by rw [dv2hgt_X h2_padic rc2]; decide)
  rw [dv2hgt_X h2_padic rc2] at hv
  have hv1 : v = 1 := by
    have : ((1 : ℕ) : ℕ∞) = ((v : ℕ) : ℕ∞) := by exact_mod_cast hv
    exact (Nat.cast_injective this).symm
  rw [hv1, addVal_norm_g₀_X h2_padic, e1_eq h2_padic rc2,
    show (L₀ h2_padic rc2).ℓ = 1 from rfl, g₀_natDegree] at heq
  simp at heq

end Uniformity.Density.Tower.C27Refute

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Slot2ExactStatement
#print axioms Uniformity.Density.Tower.keyDeg₂_pos
#print axioms Uniformity.Density.Tower.dv2Hgt_zero
#print axioms Uniformity.Density.Tower.Slot2ExactWithoutHC0Statement
#print axioms Uniformity.Density.Tower.C27Refute.slot2_exact_without_hC0_false
#print axioms Uniformity.Density.Tower.C27Refute.dv2hgt_X
#print axioms Uniformity.Density.Tower.C27Refute.addVal_norm_g₀_X
#print axioms Uniformity.Density.Tower.C27Refute.slot2_exact_false

end AxCheck
