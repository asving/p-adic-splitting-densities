/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.GateFields
import Uniformity.ChapF.F02
import Uniformity.ChapF.F06
import Uniformity.ChapF.F18
import Uniformity.ChapF.F22
import Uniformity.ChapF.F23
import Uniformity.ChapF.F25
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Uniformity.ChapF.F30 — the character/fence/ledger gate, EXECUTED at `q = 2` AND `q = 3`

**Chapter F, NODE F.30** [gate] [fresh] (`blueprint/CHAP-F_weld_layer.md` §10; GC-11's
both-primes + `e > 1 ∧ f > 1` discipline). ENV-F1. The node signs **no blueprint declaration** —
its contract IS the executed check list, so this file is `example`s over the landed nodes F.02,
F.06, F.18, F.22, F.23, F.25, plus the three gate-local carriers the checks need (the
`Fact (Nat.Prime 5)` instance, the `F₅` unit witness `z5`, and the torsor gauge `gateEta`).
The two table-built fields `F4`/`F9` are §10's shared construction block
(`Uniformity.ChapF.GateFields`, landed separately, shared with F.29).

**The arena (why `F₄`/`F₉` and not `F₂`/`F₃`).** Two degeneracies stalk this chapter's numerics:
(i) over `F₂` the unit group is trivial, so every character check silently passes (F.06 —
promoted to a theorem there); (ii) on involution geographies (`ξ² = 1`) the corrected Σ-map and
the WRONG boxed map coincide — 468 sealed rows hid the defect exactly that way (SL-INVREC
218/218). So the character content runs at `q = 2` on `F₄` (generator of order 3) and at `q = 3`
on `F₉` (generator of order 4), with the `F₂`-triviality, the NONCHAR additive shift and the
involution coincidence kept as explicit NEGATIVE controls. `e > 1 ∧ f > 1` witness: `E = 2` with
`F₄/F₂` (f = 2) and the same shape at `F₉/F₃`.

## The six checks (blueprint §10 NODE F.30)

1. **WM-FENCE instances (F.23):** the source's own `F₅` witness (`EFF.WELDMASTER.25`) —
   `ord(2 : (ZMod 5)ˣ) = 4`, `4 ∤ 1`, `χ₁ = 2⁻¹ = 3 ≠ 1` — plus a `q = 2` pair at `F₄`
   (`z = ω`, order 3: FAILS at `A = 1`, HOLDS at `A = 3`) and a `q = 3` pair at `F₃`
   (`z = −1`, order 2: FAILS at `A = 1`, HOLDS at `A = 2`);
2. **`xiChar` instances (F.18):** the `ξ₂ = θ₂⁻¹` degeneration concrete at `F₅`, and a
   NON-involution instance at each prime (`F₄`: `ω² = (1,1)`; `F₉`: `i³ = (0,2)`), the
   separator-style instances SL-INVREC's lesson demands;
3. **slotScale counts (F.02)** over `Γ = Fin 1`, `K = F₃` on the stratum `S = {v | v 0 = 0}`,
   with the JD0-T-NONCHAR negative control (the additive shift leaves `S`);
4. **the `F₂` degeneracy (F.06):** `slotScale u = id` for every `u` over `K = F₂`;
5. **the torsor witness (F.25):** `E = 2`, `K = F₅`, `η ν = (−1)^ν` — a nontrivial character
   with the SAME coboundary as the trivial gauge, so `H¹ = 0` uniqueness is dead at the
   smallest interesting instance;
6. **the JB shear (F.22):** `jbShear 2 1` and `jbShear 3 2` on the harness vertex pair
   `{(0,0), (2,1)}`.

## ⚠ GATE-FORM RIDER (A-W.1/F-D5), in force here

Five displayed spellings do not kernel-reduce; §10's rider pre-authorises the substituted
forms, **and every expected VALUE of the blueprint display is reproduced** — what moved is the
spelling, not the arithmetic. A gate-form substitution is NOT a value mismatch.

* **(ii)** `orderOf z = 4` — `orderOf` is not computable, so the order is executed as the power
  certificate `z ^ 4 = 1 ∧ z ^ 2 ≠ 1` (`+ z ≠ 1`): the order divides 4 and is neither 1 nor 2,
  hence is 4.
* **(iii)** set-level images (`slotScale u '' S = S`, `jbShear e h '' V = V'`) — `Set` image
  equality is not decidable, so these run pointwise on the named finite witnesses, which is
  exactly the arithmetic the legs pin.
* **(iv)** `(2 : ZMod 5)⁻¹ = 3` — mathlib's `Inv (ZMod n)` is `Nat.gcdA`-based (well-founded
  recursion) and does not kernel-reduce, so the value runs as the UNITS inverse
  `((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 3` **plus** the inverse-pair product `(2 : ZMod 5) * 3 = 1`.
  (Same wall as F.08's `One` instance, F-D3: inverses that must reduce are taken in `Kˣ`.)
* **(v)** any `F₅` instance of a `[Field K]` node needs `Fact (Nat.Prime 5)`, which mathlib does
  not register (only 2 and 3) — declared gate-locally below.
* **(F-D6)** the `AdjoinRoot` field spellings carry no `DecidableEq`/`Fintype`, so no `decide`
  can fire on them at all; §10's pre-authorised table fallback is `GateFields`.

**`native_decide` appears nowhere** in this file (axiom census: Lean core only).

**DEPENDS.** F.02 (`slotScale`, `card_image_slotScale`), F.06
(`slotScale_eq_id_of_card_two`), F.18 (`xiChar`), F.22 (`jbShear`), F.23 (`wmFence_absolute`),
F.25 (`gaugeBdry`, `gaugeBdry_eq_iff`), and §10's `GateFields`. F.22's `jbShear_injective` is
NOT needed — leg 6 is pointwise (A-W.1/F-D4).

**SOURCE.** GC-11; `EFF.WELDMASTER.25` (the `F₅` witness); `EFF.SIGMALAW.02` (the
`ξ₂ = θ₂⁻¹` audit); `EFF.JD0.22` BOX-5 (the `F₂` census) + the JD0-T-NONCHAR tooth.

**TEETH.** Lean-executed gate; mirrored as `verification/chapF_gate_chars.py` (§13).

**ENVIRONMENT.** ENV-F1 (concrete instances).

## Status

Sorry-free, `native_decide`-free. The three gate-local carriers (`gateFactPrimeFive`, `z5`,
`gateEta`) print `[propext, Classical.choice, Quot.sound]`; every check is an anonymous
`example` closed by `decide`, `norm_num`, or an application of a landed F-node theorem
(F.02's `card_image_slotScale`, F.06's `slotScale_eq_id_of_card_two`, F.18's `xiChar_base`,
F.23's `wmFence_absolute`, F.25's `gaugeBdry_eq_iff`), so nothing here can enter the trusted
base. Two imports beyond the F-node dependencies are forced by the arena and are recorded
here rather than left silent: `Mathlib.Algebra.Field.ZMod` (the `Field (ZMod p)` instance —
without it `Kˣ` for `K = ZMod p` elaborates through the `CommRing` path while `xiChar`'s
output sits on the `Field` path, and the two spellings do not unify) and
`Mathlib.Tactic.NormNum.Prime` (the extension that discharges `Nat.Prime 5`).
-/

namespace Uniformity.Density.Weld

section GateF30

/-! ## Gate-local carriers (NOT blueprint declarations) -/

/-- [A-W.1/F-D5(v)] `ZMod 5` is a field only through `Fact (Nat.Prime 5)`, which mathlib does
not register. Gate-local. -/
instance gateFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The source's own `F₅` fence witness: `z = 2`, of multiplicative order 4
(`EFF.WELDMASTER.25`). Gate-local. -/
def z5 : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

/-- Leg 5's gauge `η ν = (−1)^ν` on `ZMod 2`, valued in `(ZMod 5)ˣ`. Gate-local. -/
def gateEta : ZMod 2 → (ZMod 5)ˣ := fun ν => if ν = 1 then -1 else 1

/-! ## LEG 1 — WM-FENCE instances (F.23), both primes

The order-4 witness runs as a power certificate, form (ii); the character value runs in `Kˣ`
plus the inverse-pair product, form (iv). -/

example : z5 ^ 4 = 1 := by decide
example : z5 ^ 2 ≠ 1 := by decide
example : z5 ≠ 1 := by decide
example : ¬ ((4 : ℤ) ∣ 1) := by decide

-- the `χ₁ = 2⁻¹ = 3 ≠ 1` value, form (iv)
example : ((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 3 := by decide
example : (2 : ZMod 5) * 3 = 1 := by decide
example : ((z5⁻¹ : (ZMod 5)ˣ) : ZMod 5) ≠ 1 := by decide

-- F.23's criterion FIRED at the witness: the fence character at `A = 1` is nontrivial, hence
-- (through `wmFence_absolute`) the order of `z5` does not divide 1 — the display's `4 ∤ 1`,
-- reached from the landed theorem rather than from an `orderOf` computation.
example : ¬ ((orderOf z5 : ℤ) ∣ 1) := by
  rw [← wmFence_absolute z5 1]
  intro h
  have h1 : z5 ^ (1 : ℤ) = 1 := by simpa using h 1
  exact absurd (by simpa using h1) (by decide : z5 ≠ 1)

-- the `q = 2` pair at `F₄` (`z = ω`, order 3): the criterion FAILS at `A = 1`, HOLDS at `A = 3`
example : F4.omega ^ (1 : ℤ) ≠ 1 := by decide
example : F4.omega ^ (3 : ℤ) = 1 := by decide
-- the `q = 3` pair at `F₃` (`z = 2 = −1`, order 2): FAILS at `A = 1`, HOLDS at `A = 2`
example : (-1 : (ZMod 3)ˣ) ^ (1 : ℤ) ≠ 1 := by decide
example : (-1 : (ZMod 3)ˣ) ^ (2 : ℤ) = 1 := by decide

/-! ## LEG 2 — `xiChar` instances (F.18), both primes, non-involution -/

-- the `ξ₂ = θ₂⁻¹` degeneration, concrete at `F₅`: `xiChar 1 0 z5 2 1 = (z5²)⁻¹`, value `4`
example : xiChar 1 0 z5 2 1 = (z5 ^ (2 : ℤ))⁻¹ := by decide
example : ((xiChar 1 0 z5 2 1 : (ZMod 5)ˣ) : ZMod 5) = 4 := by decide
-- and F.18's landed lemma at the same data (the decided value and the THEOREM agree)
example : xiChar 1 0 z5 2 1 = (z5 ^ (2 * 1 : ℤ))⁻¹ := xiChar_base 0 z5 2 1

-- NON-involution instances (SL-INVREC's lesson: involution geographies hide the wrong map).
-- `q = 2`, `F₄`: `χ = z = ω` (order 3), `e = 1`, `A = 2` ⟹ `ω¹·ω⁻² = ω⁻¹ = ω² = θ + 1 = (1,1)`.
example : ((xiChar F4.omega 1 F4.omega 1 2 : F4ˣ) : F4) = ((1, 1) : ZMod 2 × ZMod 2) := by decide
example : xiChar F4.omega 1 F4.omega 1 2 = F4.omega ^ (2 : ℤ) := by decide
-- `q = 3`, `F₉`: `χ = z = i` (order 4), `e = 1`, `A = 2` ⟹ `i·i⁻² = i⁻¹ = i³ = −i = (0,2)`.
example : ((xiChar F9.iUnit 1 F9.iUnit 1 2 : F9ˣ) : F9) = ((0, 2) : ZMod 3 × ZMod 3) := by decide
example : xiChar F9.iUnit 1 F9.iUnit 1 2 = F9.iUnit ^ (3 : ℤ) := by decide

-- INVOLUTION negative control (SL-INVREC, 218/218): on `z² = 1` the character and its inverse
-- coincide, so such an instance distinguishes the corrected `Σ_m` from the boxed `σ′` NOT AT
-- ALL …
example : ((-1 : (ZMod 3)ˣ) ^ (1 : ℤ))⁻¹ = (-1 : (ZMod 3)ˣ) ^ (1 : ℤ) := by decide
example : xiChar 1 0 (-1 : (ZMod 3)ˣ) 1 1 = (-1 : (ZMod 3)ˣ) ^ (1 : ℤ) := by decide
-- … while the order-3 / order-4 characters SEPARATE them (why the gate runs on `F₄`/`F₉`).
example : (F4.omega ^ (1 : ℤ))⁻¹ ≠ F4.omega ^ (1 : ℤ) := by decide
example : (F9.iUnit ^ (1 : ℤ))⁻¹ ≠ F9.iUnit ^ (1 : ℤ) := by decide

/-! ## LEG 3 — slotScale counts (F.02) over `Γ = Fin 1`, `K = F₃`

The stratum `S = {v | v 0 = 0}` is carried onto itself by every unit, and has one element;
set-level image equality runs pointwise, form (iii). -/

example : ∀ (u : Fin 1 → (ZMod 3)ˣ) (v : Fin 1 → ZMod 3), v 0 = 0 → slotScale u v 0 = 0 := by
  decide
example : Fintype.card {v : Fin 1 → ZMod 3 // v 0 = 0} = 1 := by decide

-- F.02's count law FIRED at the gate stratum: the gauged read and the direct read count the
-- same (the abstract half of the pointwise closure above).
example (u : Fin 1 → (ZMod 3)ˣ) :
    Nat.card ↥(slotScale u '' {v : Fin 1 → ZMod 3 | v 0 = 0})
      = Nat.card ↥({v : Fin 1 → ZMod 3 | v 0 = 0}) :=
  card_image_slotScale u _

-- NEGATIVE control (JD0-T-NONCHAR): the additive slot shift is a bijection that leaves `S` —
-- it is NOT in the four-line perimeter.
example : ((0 : Fin 1 → ZMod 3) + 1) 0 ≠ 0 := by decide

/-! ## LEG 4 — the `F₂` degeneracy (F.06) -/

example : ∀ (u : Fin 1 → (ZMod 2)ˣ) (v : Fin 1 → ZMod 2), slotScale u v = v := by decide

-- F.06's theorem FIRED at `K = F₂` (the decided leg and the landed theorem agree)
example (u : Fin 1 → (ZMod 2)ˣ) : slotScale u = id :=
  slotScale_eq_id_of_card_two (by decide) u

/-! ## LEG 5 — the torsor witness (F.25) over `E = 2`, `K = F₅`

`μ₂(F₅) ≠ 1` kills gauge uniqueness at the smallest interesting instance. -/

example : gateEta 1 ≠ 1 := by decide
example : ((gateEta 1 : (ZMod 5)ˣ) : ZMod 5) = 4 := by decide
example : gaugeBdry (fun _ : ZMod 2 => (1 : (ZMod 5)ˣ)) = gaugeBdry gateEta := by decide

-- F.25's theorem FIRED at the witness: the coboundary coincidence above is exactly the
-- character condition on the ratio `η = 1 · gateEta⁻¹`.
example : ∀ a b : ZMod 2,
    ((1 : (ZMod 5)ˣ) * (gateEta a)⁻¹) * ((1 : (ZMod 5)ˣ) * (gateEta b)⁻¹)
      = (1 : (ZMod 5)ˣ) * (gateEta (a + b))⁻¹ :=
  (gaugeBdry_eq_iff (fun _ : ZMod 2 => (1 : (ZMod 5)ˣ)) gateEta).mp (by decide)

/-! ## LEG 6 — the JB shear (F.22) on the harness vertex pair `{(0,0), (2,1)}`

`e = 2, h = 1` ⟹ `{(0,0), (2,4)}`; the `q = 3`-side instance `e = 3, h = 2` ⟹ `{(0,0), (2,7)}`.
Pointwise on the named witnesses, form (iii). -/

example : jbShear 2 1 (0, 0) = (0, 0) := by decide
example : jbShear 2 1 (2, 1) = (2, 4) := by decide
example : jbShear 3 2 (0, 0) = (0, 0) := by decide
example : jbShear 3 2 (2, 1) = (2, 7) := by decide

end GateF30

end Uniformity.Density.Weld
