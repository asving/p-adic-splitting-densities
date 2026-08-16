/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09
import Uniformity.ChapC.C15
import Uniformity.ChapC.C19
import Uniformity.ChapC.C42

/-!
# Uniformity.ChapC.C44 — `towerLabel`, `TowerDatum.levelDatum`: the translated label `r̃`

**Chapter C, NODE C.44** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed
keys and the tower bridges; the A-C.1 amendment set governs). **ENV-C1**. Three signed
declarations.

HETOW-1(a). Over a frame `F` (C.01) pinned at `H₀` (C.03) with a tower datum `T` (C.42), write
`K = F.stageField H₀ hpin`, `η = F.stageLetter H₀ hpin` (C.19) and `Q = F.twistExp T.u₂` (C.15).
The **translated label** is the monic normalization of the affine substitution `Z ↦ η^Q·Z` applied
to the inner residual `ψ₂`:

`towerLabel T = η^{−Q·f₂} · ψ₂(η^Q·Z) ∈ K[Z]`,  whose `t`-coefficient is `c_t·η^{−(f₂−t)Q}`.

* `towerLabel T` — the label itself.
* `towerLabel_spec T hπ` — monic, irreducible, of degree `f₂`, with nonzero constant term.
* `TowerDatum.levelDatum T hπ` — hence `⟨T.u₂, T.e₂, towerLabel T⟩` is a C.09 `LevelDatum` over
  `F`: **the bridge datum every §5 object reads at**.

## Why the EXPLICIT form is the definition (`[r1]`, and the coincidence of the two presentations)

`EFF.HETOW.15`(a)'s `[r1]` DEFINITIONAL repair says `r̃` has ONE definition, `minpoly(β)`; the
corpus's second presentation is the explicit `η^{−Qf₂}·ψ₂(η^Q Z)`, and `EFF.HETOW.16`(a) proves
the two coincide. A-C.1 records the determination: the **explicit** form is the Lean definition,
because it is the one whose four properties are provable without first building `β` — the
minimal-polynomial characterization is then C.45's business (`towerLabelEquiv`), not this node's.

## The proof, and where each property comes from

Write `a = η^Q` and `c = (η⁻¹)^(Q·f₂)`, so `towerLabel T = C c * ψ₂.comp (C a * X)`. Both are
nonzero because `η ≠ 0` (C.19's `stageLetter_ne_zero`, and this is the *only* place `hπ` is
consumed — the letter's unitness is what makes the substitution invertible).

* **degree** `f₂`: `natDegree_comp` gives `ψ₂.natDegree * (C a * X).natDegree = f₂ · 1`, and
  `natDegree_C_mul` strips the nonzero scalar. `T.hψdeg` supplies `ψ₂.natDegree = f₂`.
* **monic**: `leadingCoeff_comp` gives `1 · a^{f₂} = η^{Q f₂}` (using `T.hψmonic`), and the
  scalar contributes `c`, so the leading coefficient is `(η⁻¹·η)^{Q f₂} = 1`. This is exactly why
  the normalizing prefactor is `η^{−Q f₂}` and not some other power.
* **`coeff 0 ≠ 0`**: `coeff 0 = eval 0`, and `(C a * X).eval 0 = 0`, so the constant term is
  `c · ψ₂(0)`, nonzero by `T.hψ0`. (`EFF.HETOW.16`(a)'s `ψ₂(0) ≠ 0` full-side argument is what
  puts `hψ0` into C.42's datum in the first place; here it only has to be transported.)
* **irreducible**: `Z ↦ a·Z` is an *algebra automorphism* of `K[Z]` — mathlib's
  `Polynomial.algEquivCMulXAddC a 0`, which needs `Invertible a` and therefore `η ≠ 0` again —
  and multiplication by the unit `C c` is `irreducible_isUnit_mul`. Irreducibility transports
  across any `MulEquiv` (`MulEquiv.irreducible_iff`).

The `LevelDatum` fields then discharge as the blueprint says, with **`hκ` EXACTLY `T.hfloor`**:
C.09 asks for `ℓ·(e₁f₁)·h < u` and C.42's node floor is `e₂·(e₁f₁)·h < u₂`, the same proposition
after `ℓ := e₂`, `u := u₂`. Nothing is re-derived; the `[r1]` floor is carried, not reproved.

## Divergences carried from the gate-verified twin

* **the pin binder.** `KeyFrame.Pin` is C.14a's abbreviation and C.14a has not landed, so the pin
  hypothesis is written out in full, exactly as C.03/C.09/C.42 already do (the A-C.1/D4
  convention). Same proposition, spelled.
* **`levelDatum` gains `hπ`.** Signed by A-C.1 and recorded in the blueprint's own parenthetical:
  the `spec`-fields need the letter's unitness, which needs `hπ`.
* **`isKey_X` re-declared `private`.** C.04/C.12/C.19 each carry their own private copy (defect
  D9's cure) because private declarations are not importable; this file needs it to name the base
  `Field (resField X)` and so carries a fourth copy. When C.14a lands a public `isKey_X`, all four
  retire to it — a RE-PLAN item, not a silent addition here.

## Faithfulness

**⚠ Trust-boundary definition.** `towerLabel`'s body is the signed text of the gate-verified twin
`leanspec/Leanspec/ChapC.lean` character for character. Read against `EFF.HETOW.15`(a): the corpus
display `r̃ = η^{−Qf₂}·ψ₂(η^{Q}Z)` has the negative exponent on the *outer* scalar only, and the
substitution carries the positive one — the Lean body writes `η⁻¹ ^ (Q·f₂)` and `η ^ Q`
respectively, which is that display with `η^{−m}` spelled `(η⁻¹)^m` (equal in `K` since `η ≠ 0`,
and the `(η⁻¹)^m` spelling is what elaborates without a `ℤ`-power instance). No wrap correction
occurs here: HETOW-1(b) flags the substitution POINTWISE-hence-wrap-free, and only the single
height `u₂` is normalized, so `Q = twistExp u₂` appears alone and never as a product of
normalizers. C.43's `composedKey`, by contrast, DOES carry the wrap `W(t)`; the two must not be
conflated.

**DEPENDS.** C.09 (`LevelDatum`) · C.15 (`twistExp`) · C.19 (`stageLetter`,
`stageLetter_ne_zero`) · C.42 (`TowerDatum`) · C.01/C.03 (the frame, `frameRes`, `stageField`,
through those imports) · B.25 (`resField`, `instFieldResField`) — by committed node ID (GC-13(b)).
Mathlib: `Polynomial.natDegree_comp`, `Polynomial.leadingCoeff_comp`, `Polynomial.natDegree_C_mul`,
`Polynomial.leadingCoeff_C_mul_X`, `Polynomial.algEquivCMulXAddC`, `MulEquiv.irreducible_iff`,
`irreducible_isUnit_mul`, `Polynomial.coeff_zero_eq_eval_zero`.

**PROOF.** definitional (`towerLabel`, `levelDatum`); the four clauses of `towerLabel_spec` as
above. Note the twin carries `towerLabel_spec` as an `axiom`; it is **PROVED** here.

SOURCE: `EFF.HETOW.13` (the `(LIFT)` display this label is read against); `EFF.HETOW.15`(a) (the
`[r1]` DEFINITIONAL repair); `EFF.HETOW.16`(a) (the coefficient computation
`−c_t·η^{−(f₂−t)Q}` and the `ψ₂(0) ≠ 0` full-side argument).

**TEETH.** the frame-X value `r̃ = Z² + 2Z + 2` → §13 regression; not dischargeable at these
binders (an abstract `KeyFrame O π` with an abstract `TowerDatum` supplies no numeral — the D7
consequence recorded at C.15).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helper (stub-gate defect **D9**; C.04/C.12/C.19's copy, re-declared) -/

/-- **D9 (cured).** The order-0 key `X` is an order-1 key in B.01's sense. C.04's private copy,
re-declared because private declarations are not importable. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-! ### The signed declarations -/

/-- **C.44(a) — HETOW-1(a)'s translated label `r̃`,** in the EXPLICIT form
`r̃ = η^{−Q f₂}·ψ₂(η^Q Z)` with `Q = twistExp u₂` (`EFF.HETOW.15`(a); the corpus's two
presentations coincide by `EFF.HETOW.16`(a), and A-C.1 signs the explicit one as the body).
[A-C.1/D4: the pin binder is written out, as at C.03/C.09/C.42.] -/
noncomputable def towerLabel {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    (T : TowerDatum F H₀ hpin) : Polynomial (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  Polynomial.C ((F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂))
    * T.ψ₂.comp (Polynomial.C ((F.stageLetter H₀ hpin) ^ F.twistExp T.u₂) * Polynomial.X)

/-- **C.44(b) — the four properties of `r̃`.** Monic, irreducible, of degree `f₂`, with nonzero
constant term: everything C.09's `LevelDatum` asks of a residual factor. The twin carries this as
an axiom; it is proved here. `hπ` is consumed exactly once, through C.19's `stageLetter_ne_zero`
(the letter's unitness is what makes `Z ↦ η^Q Z` invertible). -/
theorem towerLabel_spec {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (towerLabel T).Monic ∧ Irreducible (towerLabel T) ∧
      (towerLabel T).natDegree = T.f₂ ∧ (towerLabel T).coeff 0 ≠ 0 := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  set η : F.stageField H₀ hpin := F.stageLetter H₀ hpin with hη_def
  have hη : η ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  set Q : ℕ := F.twistExp T.u₂ with hQ_def
  set a : F.stageField H₀ hpin := η ^ Q with ha_def
  set c : F.stageField H₀ hpin := η⁻¹ ^ (Q * T.f₂) with hc_def
  have ha : a ≠ 0 := pow_ne_zero _ hη
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero hη)
  have hEq : towerLabel T
      = Polynomial.C c * T.ψ₂.comp (Polynomial.C a * Polynomial.X) := rfl
  -- the substituted polynomial: degree and leading coefficient
  have hqdeg : (Polynomial.C a * Polynomial.X : Polynomial (F.stageField H₀ hpin)).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X a ha
  have hcompdeg : (T.ψ₂.comp (Polynomial.C a * Polynomial.X)).natDegree = T.f₂ := by
    rw [Polynomial.natDegree_comp, hqdeg, mul_one, T.hψdeg]
  have hcomplead : (T.ψ₂.comp (Polynomial.C a * Polynomial.X)).leadingCoeff = a ^ T.f₂ := by
    rw [Polynomial.leadingCoeff_comp (by rw [hqdeg]; exact one_ne_zero),
      Polynomial.leadingCoeff_C_mul_X, T.hψmonic.leadingCoeff, one_mul, T.hψdeg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- monic: the prefactor `η^{−Q f₂}` is chosen to cancel `a^{f₂} = η^{Q f₂}`
    have : (towerLabel T).leadingCoeff = 1 := by
      rw [hEq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hcomplead, hc_def, ha_def,
        ← pow_mul, ← mul_pow, inv_mul_cancel₀ hη, one_pow]
    exact this
  · -- irreducible: a unit scalar times an algebra automorphism applied to `ψ₂`
    letI : Invertible a := invertibleOfNonzero ha
    have hsub : T.ψ₂.comp (Polynomial.C a * Polynomial.X)
        = Polynomial.algEquivCMulXAddC a (0 : F.stageField H₀ hpin) T.ψ₂ := by
      simp [Polynomial.algEquivCMulXAddC_apply, ← Polynomial.comp_eq_aeval]
    have hCunit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
    rw [hEq, irreducible_isUnit_mul hCunit, hsub]
    exact (MulEquiv.irreducible_iff
      (f := Polynomial.algEquivCMulXAddC a (0 : F.stageField H₀ hpin))).mpr T.hψirr
  · rw [hEq, Polynomial.natDegree_C_mul hc, hcompdeg]
  · rw [hEq, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    exact mul_ne_zero hc T.hψ0

/-- **C.44(c) — the bridge datum.** `⟨u₂, e₂, r̃⟩` is a C.09 `LevelDatum` over `F`: the object
every §5 statement reads the tower at. `hκ` is EXACTLY C.42's node floor `T.hfloor` (`[r1]`,
`e₂·D′h < u₂` with `D′ = e₁f₁`) — carried, not re-derived. [A-C.1: `levelDatum` gains the `hπ`
argument its `spec`-fields need.] -/
noncomputable def TowerDatum.levelDatum {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : LevelDatum F H₀ hpin where
  u := T.u₂
  ℓ := T.e₂
  r := towerLabel T
  hℓ := T.he₂
  hcop := T.hcop
  hκ := T.hfloor
  hrmonic := (towerLabel_spec T hπ).1
  hrirr := (towerLabel_spec T hπ).2.1
  hr0 := (towerLabel_spec T hπ).2.2.2
  hrdeg := by rw [(towerLabel_spec T hπ).2.2.1]; exact T.hf₂

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerLabel
#print axioms Uniformity.Density.Tower.towerLabel_spec
#print axioms Uniformity.Density.Tower.TowerDatum.levelDatum

end AxCheck
