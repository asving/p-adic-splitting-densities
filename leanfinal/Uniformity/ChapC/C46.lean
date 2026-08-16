/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B32a
import Uniformity.ChapB.B35a
import Uniformity.ChapB.B39b
import Uniformity.ChapC.C18
import Uniformity.ChapC.C22
import Uniformity.ChapC.C43
import Uniformity.ChapC.C44

/-!
# Uniformity.ChapC.C46 — `composedKey_slot_residue`: HETOW-1(c)

**Chapter C, NODE C.46** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §7, the tower seam;
signed A-C.1). **ENV-C1.** One signed declaration.

HETOW-1(c): *the corrected key's slot residues ARE `r̃`'s coefficients.* For each `t < f₂`, the
`ϖ`-read (C.22's `twistRead`) of `composedKey T`'s slot-`e₂t` development coefficient, taken at
height `(f₂−t)u₂`, is the `t`-th coefficient of C.44's translated label `r̃ = towerLabel T`:

`twistRead ((f₂−t)u₂) (dev Φ′ Φ₂ (e₂t)) = (towerLabel T).coeff t`.

The whole content is one cancellation, `EFF.HETOW.16`(c) step for step:

`η^{W(t)} · η^{−Q((f₂−t)u₂)} = η^{−(f₂−t)Q}`   (C.41(ii): `Q((f₂−t)u₂) = (f₂−t)Q + W(t)`),

and `c_t·η^{−(f₂−t)Q}` is exactly `r̃`'s `t`-th coefficient, since
`r̃ = η^{−Qf₂}·ψ₂(η^Q Z)` has `r̃_t = ψ₂_t·η^{Qt−Qf₂}`.

## The proof in four moves

1. **The development coefficient.** `Φ₂ = Φ′^{e₂f₂} − Σ_{s<f₂} L_{(f₂−s)u₂}(c_s η^{W(s)})·Φ′^{e₂s}`
   (C.43). Each lift `L_M(·) = stageLiftO M (·)` has `x`-degree `< D′ = deg Φ′`
   (`natDegree_stageLiftO_lt` below, H.55(ii) at the frame), so the displayed sum IS the `Φ′`-adic
   development: `dev Φ′ Φ₂ (e₂t) = −L_{(f₂−t)u₂}(c_t η^{W(t)})`. The leading term contributes
   nothing (`dev_mul_pow_of_lt`, since `e₂t < e₂f₂`), the `s > t` terms nothing (same lemma), and
   the `s < t` terms nothing (`dev_eq_zero_of_lt`, the lift being of degree `< D′`).
2. **The slot residue of a lift.** `slotRes M (stageLiftO M c) = c` above the fullness threshold
   `D′h < M` (`slotRes_stageLiftO` below; H.56 at the frame, closed on C.14a's reconstruction
   identity `sum_stageCoord`). Here `M = (f₂−t)u₂ ≥ u₂ > e₂D′h ≥ D′h` by C.42's node floor
   `T.hfloor` — this is the only place the floor is consumed. With the outer minus:
   `slotRes M (dev Φ′ Φ₂ (e₂t)) = −(−ψ₂_t·η^{W(t)}) = ψ₂_t·η^{W(t)}`.
3. **The twist.** `twistRead M A = η^{−Q(M)}·slotRes M A` (C.22), and C.41(ii)'s
   `twistExp_nsmul` splits `Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t)` with `W(t) = wrapExp T t`
   definitionally (C.43(a)). The `η^{W(t)}` from move 2 cancels the `η^{−W(t)}` from the split —
   the audit `η^{W(t)}·η^{−(f₂−t)Q−W(t)} = η^{−(f₂−t)Q}` ✓ of `EFF.HETOW.16`(c).
4. **The label's coefficient.** `(towerLabel T).coeff t = η^{−Qf₂}·ψ₂_t·(η^Q)^t`
   (`coeff_comp_C_mul_X` below), and `η^{−Qf₂}·η^{Qt} = η^{−(f₂−t)Q}` because `t ≤ f₂` and
   `η ≠ 0` (C.19's `stageLetter_ne_zero`, the one consumer of `hπ` on the field side).

**Why the wrap factor is not optional.** Drop `η^{W(t)}` from C.43's lift argument and move 3's
cancellation fails: the residue comes out as `−c_t·η^{−(f₂−t)Q−W(t)}`, the gauge-naive key, whose
assembled polynomial need not be irreducible (`EFF.HETOW.14`, frame X: `(Z+1)²`). That refutation
is transcribed as a record, not a node; this file is the positive half.

## Divergences and private helpers (none is a blueprint node; GC-6.5)

* **`hh : 1 ≤ F.h` is bound but not consumed.** The A-C.1 re-sign gave C.46 the C.14a corpus
  perimeter because the blueprint's PROOF routes move 2 through the H.56 reconciliation. The
  frame-side proof of move 2 assembled here (`slotRes_stageLiftIA` → `slotRes_stageLiftO`) needs
  only the fullness threshold `D′h < M`, which C.42's node floor supplies unconditionally — so
  `hh` is dead weight. It is **kept**, byte for byte, because the signature is signed and C.47
  consumes this lemma at binders that carry it (statement-fence: no weakening, and no
  strengthening either).
* **Four C.14-private lemmas are re-derived here** (`slot_eq`, `coeff_stageLiftIA_mem`,
  `natDegree_stageLiftIA_lt`, `slotRes_stageLiftIA`) together with C.14's `window_data`
  bookkeeping. `private` does not export, and C.14's public export is the existential
  `exists_slotRes_preimage`, which cannot pin `stageLiftO` — C.46 needs the *equation*
  `slotRes M (stageLiftO M c) = c` on a lift it did not choose. Same private-copy pattern as
  `isKey_X` (D9). RE-PLAN item: hoist C.14's four privates and delete this block.
* **`coeff_comp_C_mul_X`** — `(p.comp (C a · X)).coeff t = p.coeff t · a^t`. Mathlib has the
  substitution `Polynomial.algEquivCMulXAddC` (C.44 uses it for irreducibility) but no coefficient
  formula for it; three lines off `comp_eq_sum_left`.

**DEPENDS.** C.14a (`Pin`, `stageLiftIA`, `stageLiftO`, `stageCoord`, `sum_stageCoord`,
`resLift_spec`) · C.16 (`slotIdx_spec`) · C.18 (`slotWindow_full_of_le`) · C.19
(`stageLetter_ne_zero`) · C.21 (`slotRes`) · C.22 (`twistRead`) · C.41 (`twistExp_nsmul`, clause
(ii)) · C.42 (`TowerDatum`, the `[r1]` node floor `hfloor`) · C.43 (`wrapExp`, `composedKey`) ·
C.44 (`towerLabel`) · B.02/B.04 (`dev`, `dev_eq_zero_of_lt`) · B.22 (`digAt_eq`) · B.32a
(`dev_add_of_monic`) · B.35a (`dev_mul_pow`, `dev_mul_pow_of_lt`, `dev_finsetSum`) · B.39b
(`dev_neg`) — by committed node ID (GC-13(b)). Mathlib: `Polynomial.comp_eq_sum_left`,
`Polynomial.modByMonic_eq_self_iff`, `Polynomial.degree_lt_degree`, `Finset.sum_eq_single`,
`Finset.sum_neg_distrib`.

**SOURCE.** `EFF.HETOW.15`(c) + `.16`(c) (verbatim, incl. the audit
`η^{W(t)}·η^{−(f₂−t)Q−W(t)} = η^{−(f₂−t)Q}` ✓); `EFF.HETOW.14` (the naive-key refutation).

**TEETH.** the three-frame supp check (slot residues = `minpoly(β)`) → **Lean theorem** (this
node), at every frame, every tower datum and every `t < f₂` at once; the naive-key `(Z+1)²`
degeneration stays §13's contrast row.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **D9 (cured).** The order-0 key `X` is an order-1 key; the private-copy pattern
(C.04/C.12/C.19/C.21/C.22/C.44 each carry one), because `private` does not export. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-! ### C.14's private lift calculus, re-derived (see the module docstring) -/

/-- The normalizer solve is exact: `i(M)·h + e₁·a = M` with `a = (M − i(M)h)/e₁`. -/
private theorem slot_eq (F : KeyFrame O π) {M : ℕ} (hM : F.slotIdx M * F.h ≤ M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M := by
  have hdvd : F.e₁ ∣ M - F.slotIdx M * F.h :=
    (Nat.modEq_iff_dvd' hM).mp (F.slotIdx_spec M).2
  rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hM]

/-- Above the fullness threshold `D′h < M`: the exact normalizer solve, the full window, and the
integrality of every `π`-exponent `a − s·h`. -/
private theorem window_data (F : KeyFrame O π) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M
      ∧ F.slotWindow M = Finset.range F.f₁
      ∧ ∀ s, s < F.f₁ → s * F.h ≤ (M - F.slotIdx M * F.h) / F.e₁ := by
  have hi : F.slotIdx M < F.e₁ := (F.slotIdx_spec M).1
  have hbelow : ∀ s, s < F.f₁ → (F.slotIdx M + F.e₁ * s) * F.h < M := by
    intro s hs
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    have hle : F.slotIdx M + F.e₁ * s ≤ F.e₁ * F.f₁ := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hM
  have hile : F.slotIdx M * F.h ≤ M := by
    have h0 := hbelow 0 F.hf₁
    rw [Nat.mul_zero, Nat.add_zero] at h0
    omega
  have hMa := slot_eq F hile
  refine ⟨hMa, ?_, ?_⟩
  · refine F.slotWindow_full_of_le M ?_
    have hsub : (F.e₁ * F.f₁ - 1) * F.h ≤ (F.e₁ * F.f₁) * F.h :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  · intro s hs
    have h1 := hbelow s hs
    have hexp : (F.slotIdx M + F.e₁ * s) * F.h = F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
    have h2 : F.e₁ * (s * F.h) < F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) := by omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left h2)

/-- The lift's coefficient at an occupied slot. -/
private theorem coeff_stageLiftIA_mem (F : KeyFrame O π) {i a s : ℕ} (hs : s < F.f₁)
    (lift : ℕ → O) :
    (F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s) = lift s * π ^ (a - s * F.h) := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbs
    have hne : i + F.e₁ * s ≠ i + F.e₁ * b := by
      intro he
      exact hbs (Nat.eq_of_mul_eq_mul_left F.he₁ (by omega)).symm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  · intro hns
    exact absurd (Finset.mem_range.mpr hs) hns

/-- **H.55(ii) at the frame.** Every `X`-exponent of the lift is `< D′ = e₁f₁`. -/
private theorem natDegree_stageLiftIA_lt (F : KeyFrame O π) {i a : ℕ} (hi : i < F.e₁)
    (lift : ℕ → O) : (F.stageLiftIA (π := π) i a lift).natDegree < F.e₁ * F.f₁ := by
  classical
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hbound : (F.stageLiftIA (π := π) i a lift).natDegree ≤ F.e₁ * F.f₁ - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    have hs' : s < F.f₁ := Finset.mem_range.mp hs
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs'
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  omega

/-- **H.56 at the frame — the residue clause.** At a full window the slot residue of the lift
reads its digits back. -/
private theorem slotRes_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {a M : ℕ} (hM : F.slotIdx M * F.h + F.e₁ * a = M)
    (hfull : F.slotWindow M = Finset.range F.f₁) (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a)
    (lift : ℕ → O) :
    F.slotRes H₀ hpin M (F.stageLiftIA (π := π) (F.slotIdx M) a lift)
      = ∑ s ∈ Finset.range F.f₁,
          algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
            (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
              (residue O (lift s))) * F.stageLetter H₀ hpin ^ s := by
  classical
  rw [KeyFrame.slotRes, hfull]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < F.f₁ := Finset.mem_range.mp hs
  have hsa' : s * F.h ≤ a := hsa s hs'
  have hidx : (M - (F.slotIdx M + F.e₁ * s) * F.h) / F.e₁ = a - s * F.h := by
    have hexp : (F.slotIdx M + F.e₁ * s) * F.h = F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
    have hle : F.e₁ * (s * F.h) ≤ F.e₁ * a := Nat.mul_le_mul_left _ hsa'
    have heq : M - (F.slotIdx M + F.e₁ * s) * F.h = F.e₁ * (a - s * F.h) := by
      rw [Nat.mul_sub]
      omega
    rw [heq, Nat.mul_div_cancel_left _ F.he₁]
  rw [hidx, coeff_stageLiftIA_mem F hs' lift,
    digAt_eq hπ (mul_comm (lift s) (π ^ (a - s * F.h)))]

/-! ### The two pins on `stageLiftO` -/

/-- H.55(ii) for the element-at-height lift. -/
private theorem natDegree_stageLiftO_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (M : ℕ)
    (c : F.stageField H₀ hpin) :
    (F.stageLiftO H₀ hpin M c).natDegree < F.e₁ * F.f₁ :=
  natDegree_stageLiftIA_lt F (F.slotIdx_spec M).1 _

/-- **The residue pin.** Above `D′h < M` the slot residue of the element-at-height lift is the
element itself — C.14a's `sum_stageCoord` is exactly what makes this provable. -/
private theorem slotRes_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) (c : F.stageField H₀ hpin) :
    F.slotRes H₀ hpin M (F.stageLiftO H₀ hpin M c) = c := by
  obtain ⟨hMa, hfull, hsa⟩ := window_data F hM
  rw [KeyFrame.stageLiftO, slotRes_stageLiftIA F hπ H₀ hpin hMa hfull hsa]
  refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_) (F.sum_stageCoord H₀ hpin c)
  rw [resLift_spec]

/-- The residue pin with the outer minus C.43's display carries. -/
private theorem slotRes_neg_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) (c : F.stageField H₀ hpin) :
    F.slotRes H₀ hpin M (-(F.stageLiftO H₀ hpin M c)) = -c := by
  obtain ⟨hMa, hfull, hsa⟩ := window_data F hM
  have hneg : -(F.stageLiftO H₀ hpin M c)
      = F.stageLiftIA (π := π) (F.slotIdx M) ((M - F.slotIdx M * F.h) / F.e₁)
          (fun s => -(resLift (F.stageCoord H₀ hpin c s))) := by
    rw [KeyFrame.stageLiftO, KeyFrame.stageLiftIA, KeyFrame.stageLiftIA,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← neg_mul, ← Polynomial.C_neg, neg_mul]
  have hstep : ∑ s ∈ Finset.range F.f₁,
        algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
            (residue O (-(resLift (F.stageCoord H₀ hpin c s))))) * F.stageLetter H₀ hpin ^ s
      = - ∑ s ∈ Finset.range F.f₁,
          algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
            (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
              (F.stageCoord H₀ hpin c s)) * F.stageLetter H₀ hpin ^ s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_neg, resLift_spec, map_neg, map_neg, neg_mul]
  rw [hneg, slotRes_stageLiftIA F hπ H₀ hpin hMa hfull hsa, hstep,
    F.sum_stageCoord H₀ hpin c]

/-! ### The substitution's coefficient -/

/-- `(p ∘ (a·Z)) _t = p_t · a^t`: the coefficient formula mathlib's `algEquivCMulXAddC` lacks. -/
private theorem coeff_comp_C_mul_X {K : Type*} [CommRing K] (p : Polynomial K) (a : K) (t : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff t = p.coeff t * a ^ t := by
  classical
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  have hsummand : ∀ e ∈ p.support,
      (Polynomial.C (p.coeff e) * (Polynomial.C a * Polynomial.X) ^ e).coeff t
        = if e = t then p.coeff e * a ^ e else 0 := by
    intro e _
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    by_cases he : e = t
    · simp [he]
    · simp [he, Ne.symm he]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_ite_eq' p.support t]
  by_cases ht : t ∈ p.support
  · rw [if_pos ht]
  · rw [if_neg ht, Polynomial.notMem_support_iff.mp ht, zero_mul]

/-! ### The signed declaration -/

set_option linter.unusedVariables false in
/-- **NODE C.46 — HETOW-1(c): the corrected key's slot residues are `r̃`'s coefficients.**
`EFF.HETOW.15`(c)/`.16`(c). The wrap factor `η^{W(t)}` C.43 builds into the lift argument is
exactly what the twist `η^{−Q((f₂−t)u₂)}` eats, by C.41(ii); what survives is `ψ₂_t·η^{−(f₂−t)Q}`,
which IS `(towerLabel T).coeff t`. `hh` is bound by the A-C.1 signature and not consumed — see the
module docstring. -/
theorem composedKey_slot_residue {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    {t : ℕ} (ht : t < T.f₂) :
    F.twistRead H₀ hpin ((T.f₂ - t) * T.u₂) (dev F.key (composedKey T) (T.e₂ * t))
      = (towerLabel T).coeff t := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  set η : F.stageField H₀ hpin := F.stageLetter H₀ hpin with hη_def
  have hη : η ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  set Q : ℕ := F.twistExp T.u₂ with hQ_def
  -- the height this slot is read at, and the fullness threshold it clears
  have hsub : 1 ≤ T.f₂ - t := by omega
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hMbig : F.e₁ * F.f₁ * F.h < (T.f₂ - t) * T.u₂ := by
    have hfloor : T.e₂ * (F.e₁ * F.f₁) * F.h < T.u₂ := T.hfloor
    have hle : F.e₁ * F.f₁ * F.h ≤ T.e₂ * (F.e₁ * F.f₁) * F.h :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ T.he₂)
    have hgrow : T.u₂ ≤ (T.f₂ - t) * T.u₂ := Nat.le_mul_of_pos_left _ hsub
    omega
  -- ## move 1 — the development coefficient
  have hmonic : F.key.Monic := F.hmonic
  have hkeydeg : F.key.natDegree = F.e₁ * F.f₁ := F.hdeg
  have hkeypos : 0 < F.key.natDegree := by rw [hkeydeg]; exact hD
  have hdev : dev F.key (composedKey T) (T.e₂ * t)
      = -(F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * η ^ (wrapExp T t))) := by
    have he₂ : 0 < T.e₂ := T.he₂
    have hmullt : ∀ b c : ℕ, b < c → T.e₂ * b < T.e₂ * c := by
      intro b c hbc
      have h1 : T.e₂ * (b + 1) ≤ T.e₂ * c := Nat.mul_le_mul_left _ hbc
      have h2 : T.e₂ * (b + 1) = T.e₂ * b + T.e₂ := by ring
      omega
    have hlead : dev F.key (F.key ^ (T.e₂ * T.f₂)) (T.e₂ * t) = 0 := by
      have hone : F.key ^ (T.e₂ * T.f₂) = (1 : Polynomial O) * F.key ^ (T.e₂ * T.f₂) := by
        rw [one_mul]
      rw [hone]
      exact dev_mul_pow_of_lt hmonic _ _ _ (hmullt t T.f₂ ht)
    have hterm : ∀ s ∈ Finset.range T.f₂,
        dev F.key
            (F.stageLiftO H₀ hpin ((T.f₂ - s) * T.u₂)
                (- T.ψ₂.coeff s * η ^ (wrapExp T s)) * F.key ^ (T.e₂ * s)) (T.e₂ * t)
          = if s = t then
              F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂) (- T.ψ₂.coeff t * η ^ (wrapExp T t))
            else 0 := by
      intro s _
      rcases lt_trichotomy s t with hst | rfl | hst
      · -- `s < t`: the development sits `e₂(t−s) ≥ 1` steps to the left of the lift's support
        have hshift : T.e₂ * t = T.e₂ * s + T.e₂ * (t - s) := by
          rw [← Nat.mul_add]; congr 1; omega
        have hpos : 0 < T.e₂ * (t - s) := Nat.mul_pos T.he₂ (by omega)
        rw [hshift, dev_mul_pow hmonic, if_neg (by omega)]
        refine dev_eq_zero_of_lt hmonic hkeypos _ _ ?_
        refine lt_of_lt_of_le (natDegree_stageLiftO_lt F H₀ hpin _ _) ?_
        rw [← hkeydeg]
        exact Nat.le_mul_of_pos_left _ hpos
      · -- `s = t`: the lift itself, since its degree is `< D′`
        have hshift := dev_mul_pow hmonic (T.e₂ * s)
          (F.stageLiftO H₀ hpin ((T.f₂ - s) * T.u₂)
            (- T.ψ₂.coeff s * η ^ (wrapExp T s))) 0
        rw [Nat.add_zero] at hshift
        rw [hshift, if_pos rfl]
        change (F.stageLiftO H₀ hpin ((T.f₂ - s) * T.u₂)
          (- T.ψ₂.coeff s * η ^ (wrapExp T s))) %ₘ F.key = _
        refine (Polynomial.modByMonic_eq_self_iff hmonic).mpr ?_
        refine Polynomial.degree_lt_degree ?_
        rw [hkeydeg]
        exact natDegree_stageLiftO_lt F H₀ hpin _ _
      · -- `t < s`: nothing sits left of the shift
        rw [if_neg (by omega)]
        exact dev_mul_pow_of_lt hmonic _ _ _ (hmullt t s hst)
    rw [composedKey, sub_eq_add_neg, dev_add_of_monic hmonic, hlead, dev_neg hmonic,
      dev_finsetSum hmonic, Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range T.f₂) t,
      if_pos (Finset.mem_range.mpr ht), zero_add]
  -- ## move 2 — the slot residue
  have hres : F.slotRes H₀ hpin ((T.f₂ - t) * T.u₂) (dev F.key (composedKey T) (T.e₂ * t))
      = T.ψ₂.coeff t * η ^ (wrapExp T t) := by
    rw [hdev, slotRes_neg_stageLiftO F hπ H₀ hpin hMbig, neg_mul, neg_neg]
  -- ## move 3 — the twist, split by C.41(ii)
  have hQsplit : F.twistExp ((T.f₂ - t) * T.u₂) = (T.f₂ - t) * Q + wrapExp T t :=
    F.twistExp_nsmul T.u₂ T.f₂ t ht
  -- ## move 4 — the label's coefficient
  have hlabel : (towerLabel T).coeff t = η⁻¹ ^ (Q * T.f₂) * (T.ψ₂.coeff t * (η ^ Q) ^ t) := by
    have hEq : towerLabel T
        = Polynomial.C (η⁻¹ ^ (Q * T.f₂))
            * T.ψ₂.comp (Polynomial.C (η ^ Q) * Polynomial.X) := rfl
    rw [hEq, Polynomial.coeff_C_mul, coeff_comp_C_mul_X]
  -- ## assembling: the cancellation `η^{W} · η^{−(f₂−t)Q−W} = η^{−(f₂−t)Q}`
  rw [KeyFrame.twistRead, hres, hQsplit, hlabel]
  have hsplitQ : Q * T.f₂ = Q * (T.f₂ - t) + Q * t := by
    rw [← Nat.mul_add]; congr 1; omega
  have hcancelW : (η⁻¹ ^ (wrapExp T t)) * η ^ (wrapExp T t) = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hη)]
  have hcancelQt : (η⁻¹ ^ (Q * t)) * (η ^ Q) ^ t = 1 := by
    rw [← pow_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hη)]
  calc η⁻¹ ^ ((T.f₂ - t) * Q + wrapExp T t) * (T.ψ₂.coeff t * η ^ (wrapExp T t))
      = η⁻¹ ^ ((T.f₂ - t) * Q) * T.ψ₂.coeff t
          * ((η⁻¹ ^ (wrapExp T t)) * η ^ (wrapExp T t)) := by
        rw [pow_add]; ring
    _ = η⁻¹ ^ (Q * (T.f₂ - t)) * T.ψ₂.coeff t := by
        rw [hcancelW, mul_one, Nat.mul_comm]
    _ = η⁻¹ ^ (Q * (T.f₂ - t)) * T.ψ₂.coeff t * ((η⁻¹ ^ (Q * t)) * (η ^ Q) ^ t) := by
        rw [hcancelQt, mul_one]
    _ = η⁻¹ ^ (Q * T.f₂) * (T.ψ₂.coeff t * (η ^ Q) ^ t) := by
        rw [hsplitQ, pow_add]; ring

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.composedKey_slot_residue

end AxCheck
