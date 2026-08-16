/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E08
import Uniformity.ChapE.E10
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Uniformity.ChapE.E31 — the twisted lift at a rung (R1-c)

**Chapter E, NODE E.31** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §6), ENV-E2 + ENV-E3.

`EFF.HE7.111` (ANNEX-THEOREM R1-c) is the constructive half of the σ-ladder's level step: given a
target residue `c = Σ_t γ_t η^t ∈ K'` and a twist vector `ϑ`, BUILD a slot family whose twisted
read is exactly `(k, c)`. The construction is "§S4.2 one level up, with ONE pre-twist line added":
for each coordinate `t` with `γ_t ≠ 0`, invoke the level-`i` lift `(LIFT_{i−1})` at height
`m_t := m₀ − t·u` for the residue **`γ_t · ϑ_t^{−1}`** — the INVERSE twist — and park the result
in slot `s₀ + ℓt`; every other slot is `0`.

The inverse is the whole mechanism: E.29's readout multiplies slot `t`'s digit by `ϑ_t` before
summing, so a digit of `γ_t · ϑ_t^{−1}` reads back as `Σ_t (γ_tϑ_t^{−1})·ϑ_t·η^t = Σ_t γ_tη^t = c`.
"The bound recursion is unchanged — values never see the twist."

## What the signed conclusion carries

Four clauses, exactly as signed: the family is supported below `slotCount`; every slot value is
sub-`D` (so it is a legal slot); at each `t` with `γ t ≠ 0` the slot `s₀ + ℓt` has height
`m₀ − t·u` and digit `γ t · (ϑ t)⁻¹`; and at each `t` with `γ t = 0` that slot is empty.

**Honest reading of what it does NOT carry.** The conclusion says nothing about slots *outside*
the class `s₀ + ℓ·{t < g}` other than the `slotCount` cutoff. So a consumer can read E.29's
`hocc` and its A-E.4 `hatt` off this conclusion (both are gated below), but NOT E.29's `hmin` —
minimality quantifies over every occupied slot, including out-of-class ones, and this signature
does not pin those. `hmin` is the caller's (it is the definition of `k` as the minimum, per
`EFF.HE7.11`). Nor is the residue identity `Σ_t (γϑ⁻¹)ϑη^t = c` stated here: per the blueprint's
PROOF step 2, "the E.29 readout … is the consumer's next move, stated there".

## A-E.4 consumer note (why this node did not move when E.29 was re-signed)

Amendment **A-E.4** (2026-08-16) re-signed E.29's `hatt` at the ATTAINED VALUE
(`∃ v, C.hgt (c s) = v ∧ ℓv + su = k`), the committed height form having been machine-refuted.
The amendment records that "no consumer signature moves (`twisted_lift` (E.31) supplies the new
`hatt` from its own construction: its slots have height `m₀ − tu` in class `s₀ + ℓt`)". That
claim is **machine-checked in the gate below**: from the signed conclusion alone, at any `t` with
`γ t ≠ 0`, the slot `s = s₀ + ℓt` satisfies `s < slotCount`, `c s ≠ 0`, and
`ℓ·(m₀ − tu) + s·u = ℓm₀ + s₀u = k` — the A-E.4 `hatt` verbatim. The `ℕ`-subtraction in
`m₀ − tu` is exact there (`t·u ≤ (g−1)·u ≤ m₀` by `hthr`), which is precisely the step the
refuted truncating-division form got wrong.

## Inert binders (signature fidelity)

`hgen`, `hint`, `hg`, `hk`, `hγ`, `hs₀` describe the ambient frame (`η` generates `K'`, the
degree bookkeeping, the Bézout data) and the target vector; the CONSTRUCTION consumes only
`hfull`, `hthr`, `hϑ` and the per-`t` nonvanishing of `γ`. They are carried unchanged — the
statement fence forbids trimming a signed binder — and `linter.unusedVariables` is switched off
for the declaration.

## Proof

1. Per `t` with `γ t ≠ 0`: `t ≤ g − 1` gives `t·u ≤ (g−1)·u`, so `hthr` yields
   `b ≤ m₀ − t·u` and `hfull` makes that height full; `C.hlift` then realises the digit
   `γ t · (ϑ t)⁻¹` (nonzero: `γ t ≠ 0` and `(ϑ t)⁻¹ ≠ 0`). `choose!` totalises the lift.
2. `A' t := if γ t = 0 then 0 else A t`, and
   `c s := if h : ∃ t, s₀ + ℓ·t = s then A' h.choose else 0`. Since `1 ≤ ℓ` (E.01's `hℓ`) the
   slot map `t ↦ s₀ + ℓt` is injective, so `c (s₀ + ℓt) = A' t` (`hkey`) — this is where the
   `dite`'s chosen index is pinned to the intended one.
3. The support clause: an in-class slot is `s₀ + ℓt < ℓ + ℓ(g−1) = ℓg = slotCount`, so beyond
   the cutoff the `dite` takes its `else` branch. The degree clause: lifts are sub-`D`, and the
   empty slots have degree `0 < D` (`C.hD`).

DEPENDS: E.08 (`lift_threshold_step` — used in the gate for the k-uniform form), E.10 (`Full`,
`hlift`, `hD`, `hgt_zero`), E.01/E.02 (`RungDatum`, `hℓ`, `slotCount`) · mathlib `Nat.cast_sub`,
`Fin.ext`, `Nat.eq_of_mul_eq_mul_left`.

SOURCE: `EFF.HE7.111` (ANNEX-THEOREM R1-c, statement + proof verbatim: "§S4.2 one level up, with
ONE pre-twist line added … invoke (LIFT_{i−1}) at level-i height `m_t := m₀ − tu_i` … for the
residue **γ_t·ϑ_t^{−1} ∈ K_i^×** — the INVERSE twist … The bound recursion is unchanged — values
never see the twist"); `EFF.HE7.12` ((LIFT₂), the `ϑ ≡ 1` instance); `EFF.HE7.27` (DEFINITION
HE7-3's inverse-twisted prescription, "machine-load-bearing per tooth HE7-T-BADTWIST").

TEETH: HE7-T-BADTWIST (21 reads change when the twist is dropped; twisted read == PARI 480/480) +
`he7rannex_supp.py` K2R (R1-c's mechanism used constructively, 15 members) → **Lean theorem**;
Q3 (ten frames) evidences the thresholds (E.68). The gate below carries the machine-checkable
residues of those teeth: the inverse-twist algebra (`(γϑ⁻¹)·ϑ = γ`, and the un-inverted
prescription failing at `γ = 1, ϑ = 2`), the threshold's sharpness at the deepest slot, the
k-uniform corollary through E.08, and the A-E.4 `hatt` supply. The 21-read count and the PARI
cross-check are NUMERIC evidence and are not reproduced in Lean.

ENVIRONMENT: ENV-E2 + ENV-E3.

## Status

Sorry-free, Lean-core axioms only. The signature was transcribed from
`leanspec/Leanspec/ChapE.lean`'s signed stub with binder names, order and explicitness unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- Signature fidelity: `hgen`, `hint`, `hg`, `hk`, `hγ`, `hs₀` are signed binders that the
-- construction does not consume (see the module docstring). They are KEPT.
set_option linter.unusedVariables false in
/-- **E.31** The twisted lift at a rung (R1-c schema; `(LIFT₂)` is its `ϑ ≡ 1` instance): a slot
family realising the coordinate vector `γ` at height `k`, with each digit PRE-DIVIDED by its
twist `ϑ t` so that E.29's readout returns `γ` itself. -/
theorem twisted_lift {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    {b : ℕ} (hfull : ∀ m : ℕ, b ≤ m → C.Full m)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hthr : (R.g - 1) * R.u + b ≤ m₀)
    (γ ϑ : Fin R.g → K) (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    ∃ c : ℕ → Polynomial O,
      (∀ s, R.slotCount ≤ s → c s = 0) ∧ (∀ s, (c s).natDegree < C.D) ∧
      (∀ t : Fin R.g, γ t ≠ 0 →
        C.hgt (c (s₀ + R.ℓ * t)) = ((m₀ - (t : ℕ) * R.u : ℕ) : WithTop ℤ) ∧
        C.dig (c (s₀ + R.ℓ * t)) = γ t * (ϑ t)⁻¹) ∧
      (∀ t : Fin R.g, γ t = 0 → c (s₀ + R.ℓ * t) = 0) := by
  classical
  -- STEP 1 (the pre-twist line): per admissible `t` the height `m_t = m₀ − t·u` clears `b`, so
  -- it is full and `hlift` realises the INVERSE-twisted digit `γ t · (ϑ t)⁻¹`.
  have hstep : ∀ t : Fin R.g, γ t ≠ 0 → ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < C.D ∧
      C.hgt A = (((m₀ - (t : ℕ) * R.u : ℕ) : ℤ) : WithTop ℤ) ∧ C.dig A = γ t * (ϑ t)⁻¹ := by
    intro t ht
    have hmul : (t : ℕ) * R.u ≤ (R.g - 1) * R.u :=
      Nat.mul_le_mul_right _ (by have := t.isLt; omega)
    have hb : b ≤ m₀ - (t : ℕ) * R.u := by omega
    exact C.hlift _ (hfull _ hb) (γ t * (ϑ t)⁻¹) (mul_ne_zero ht (inv_ne_zero (hϑ t)))
  choose! A hA0 hAdeg hAhgt hAdig using hstep
  set A' : Fin R.g → Polynomial O := fun t => if γ t = 0 then 0 else A t with hA'
  set c : ℕ → Polynomial O :=
    fun s => if h : ∃ t : Fin R.g, s₀ + R.ℓ * (t : ℕ) = s then A' h.choose else 0 with hc
  -- the slot map `t ↦ s₀ + ℓt` is injective (`1 ≤ ℓ`), so the `dite` reads back the right index
  have hkey : ∀ t : Fin R.g, c (s₀ + R.ℓ * (t : ℕ)) = A' t := by
    intro t
    have hex : ∃ t' : Fin R.g, s₀ + R.ℓ * (t' : ℕ) = s₀ + R.ℓ * (t : ℕ) := ⟨t, rfl⟩
    have hch : hex.choose = t := by
      have hspec := hex.choose_spec
      have hmul : R.ℓ * (hex.choose : ℕ) = R.ℓ * (t : ℕ) := by omega
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by have := R.hℓ; omega) hmul)
    rw [hc]
    simp only
    rw [dif_pos hex, hch]
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · -- slots at or beyond `slotCount` are empty: an in-class slot is `s₀ + ℓt < ℓ + ℓ(g−1) = ℓg`
    intro s hs
    rw [hc]
    simp only
    refine dif_neg ?_
    rintro ⟨t, rfl⟩
    have h1 : R.ℓ * ((t : ℕ) + 1) ≤ R.ℓ * R.g := Nat.mul_le_mul_left _ t.isLt
    have h2 : R.ℓ * ((t : ℕ) + 1) = R.ℓ * (t : ℕ) + R.ℓ := by ring
    have h3 : R.slotCount = R.ℓ * R.g := rfl
    omega
  · -- every slot value is a lift, hence sub-`D`; the empty slots have degree `0 < D`
    intro s
    rw [hc]
    simp only
    by_cases h : ∃ t : Fin R.g, s₀ + R.ℓ * (t : ℕ) = s
    · rw [dif_pos h, hA']
      by_cases hγ0 : γ h.choose = 0
      · simpa [hγ0] using C.hD
      · simpa [hγ0] using hAdeg h.choose hγ0
    · simpa [dif_neg h] using C.hD
  · -- the two construction clauses at an admissible `t`
    intro t ht
    rw [hkey t]
    simp only [hA', if_neg ht]
    refine ⟨?_, hAdig t ht⟩
    rw [hAhgt t ht]
    norm_cast
  · -- and the slot is empty where the coordinate vanishes
    intro t ht
    rw [hkey t]
    simp only [hA', if_pos ht]

/-! ## Gate (executed `example`s, not blueprint declarations)

Four checks. (1) The A-E.4 consumer contract, machine-checked: the signed conclusion supplies
E.29's `hocc` and its re-signed attained-value `hatt`. (2) The k-uniform form the blueprint's
STATEMENT closes with, routed through E.08. (3) The inverse-twist mechanism (tooth
HE7-T-BADTWIST in miniature). (4) The threshold's sharpness at the deepest slot. -/

section Gate

-- (1) A-E.4 CONSUMER CONTRACT. From `twisted_lift` alone, the constructed family occupies an
-- in-class slot whose ATTAINED VALUE is `k` — i.e. E.29's `hatt` at the re-signed form, plus
-- `hocc`. This is the claim amendment A-E.4 makes on E.31's behalf, checked rather than asserted.
set_option linter.unusedVariables false in
example {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    {b : ℕ} (hfull : ∀ m : ℕ, b ≤ m → C.Full m)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hthr : (R.g - 1) * R.u + b ≤ m₀)
    (γ ϑ : Fin R.g → K) (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    ∃ c : ℕ → Polynomial O,
      (∀ s, R.slotCount ≤ s → c s = 0) ∧ (∀ s, (c s).natDegree < C.D) ∧
      (∃ s < R.slotCount, c s ≠ 0) ∧
      (∃ s < R.slotCount, c s ≠ 0 ∧ ∃ v : ℤ, C.hgt (c s) = (v : WithTop ℤ) ∧
        (R.ℓ : ℤ) * v + (s : ℤ) * (R.u : ℤ) = (k : ℤ)) := by
  obtain ⟨c, hsupp, hdeg, hpos, hzero⟩ :=
    twisted_lift C R hgen hint hg hfull hs₀ hk hthr γ ϑ hγ hϑ
  obtain ⟨t, ht⟩ := hγ
  obtain ⟨hhgt, hdig⟩ := hpos t ht
  -- the slot is in range
  have hrange : s₀ + R.ℓ * (t : ℕ) < R.slotCount := by
    have h1 : R.ℓ * ((t : ℕ) + 1) ≤ R.ℓ * R.g := Nat.mul_le_mul_left _ t.isLt
    have h2 : R.ℓ * ((t : ℕ) + 1) = R.ℓ * (t : ℕ) + R.ℓ := by ring
    have h3 : R.slotCount = R.ℓ * R.g := rfl
    omega
  -- it is occupied: its height is finite, and `hgt 0 = ⊤`
  have hne : c (s₀ + R.ℓ * (t : ℕ)) ≠ 0 := by
    intro h0
    rw [h0, C.hgt_zero] at hhgt
    exact (WithTop.natCast_ne_top (α := ℤ) _) hhgt.symm
  -- the ℕ-subtraction is exact, so the attained VALUE is `k`
  have hmul : (t : ℕ) * R.u ≤ (R.g - 1) * R.u :=
    Nat.mul_le_mul_right _ (by have := t.isLt; omega)
  have hle : (t : ℕ) * R.u ≤ m₀ := by omega
  have hcast : ((m₀ - (t : ℕ) * R.u : ℕ) : ℤ) = (m₀ : ℤ) - (t : ℕ) * (R.u : ℤ) := by
    push_cast [Nat.cast_sub hle]
    ring
  have hk' : (R.ℓ : ℤ) * (m₀ : ℤ) + (s₀ : ℤ) * (R.u : ℤ) = (k : ℤ) := by exact_mod_cast hk
  refine ⟨c, hsupp, hdeg, ⟨_, hrange, hne⟩,
    ⟨_, hrange, hne, ((m₀ - (t : ℕ) * R.u : ℕ) : ℤ), ?_, ?_⟩⟩
  · rw [hhgt]; norm_cast
  · rw [hcast]
    push_cast
    linarith [hk']

-- (2) THE K-UNIFORM FORM. The blueprint's closing sentence: `R.nextBound b ≤ k` suffices — the
-- per-height threshold `hthr` is then E.08's `lift_threshold_step`, not a separate obligation.
set_option linter.unusedVariables false in
example {O : Type*} [CommRing O] {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (C : SlotCarrier O K) (R : RungDatum) {η : K'}
    (hgen : (minpoly K η).natDegree = Module.finrank K K')
    (hint : IsIntegral K η) (hg : R.g = Module.finrank K K')
    {b : ℕ} (hfull : ∀ m : ℕ, b ≤ m → C.Full m)
    {k m₀ s₀ : ℕ} (hs₀ : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hcrit : R.nextBound b ≤ k)
    (γ ϑ : Fin R.g → K) (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    ∃ c : ℕ → Polynomial O,
      (∀ s, R.slotCount ≤ s → c s = 0) ∧ (∀ s, (c s).natDegree < C.D) ∧
      (∀ t : Fin R.g, γ t ≠ 0 →
        C.hgt (c (s₀ + R.ℓ * t)) = ((m₀ - (t : ℕ) * R.u : ℕ) : WithTop ℤ) ∧
        C.dig (c (s₀ + R.ℓ * t)) = γ t * (ϑ t)⁻¹) ∧
      (∀ t : Fin R.g, γ t = 0 → c (s₀ + R.ℓ * t) = 0) :=
  twisted_lift C R hgen hint hg hfull hs₀ hk (lift_threshold_step R hs₀ hk hcrit) γ ϑ hγ hϑ

-- (3) THE INVERSE TWIST (tooth HE7-T-BADTWIST, mechanism half). E.29's readout multiplies the
-- slot digit by `ϑ t`; a digit of `γ t · (ϑ t)⁻¹` therefore reads back as `γ t` exactly.
example {K : Type*} [Field K] (γ ϑ : K) (hϑ : ϑ ≠ 0) : (γ * ϑ⁻¹) * ϑ = γ := by
  field_simp

-- The un-inverted prescription (`γ t · ϑ t` in the slot) does NOT read back as `γ t`: at
-- `γ = 1, ϑ = 2` over ℚ it returns `4`. This is why DEFINITION HE7-3's inverse is
-- machine-load-bearing and not cosmetic.
example : ((1 : ℚ) * 2) * 2 ≠ 1 := by norm_num

-- (4) THRESHOLD SHARPNESS. `hthr` is exactly what keeps the DEEPEST slot `t = g − 1` legal. At
-- `(g, u, b, m₀) = (2, 3, 1, 2)` the hypothesis fails — `(g−1)u + b = 4 > 2` — and the deepest
-- height `m₀ − (g−1)u` is `0`, strictly below `b = 1`, so `hfull` cannot be applied there.
example : ¬ ((2 - 1) * 3 + 1 ≤ 2) ∧ (2 : ℕ) - (2 - 1) * 3 < 1 := by norm_num

-- Positively: under `hthr` every slot of the class clears `b`. (The proof above uses exactly
-- this step; here it is in isolation at `(g, u, b, m₀) = (3, 2, 1, 5)`, deepest slot `t = 2`.)
example : (3 - 1) * 2 + 1 ≤ 5 ∧ 1 ≤ (5 : ℕ) - 2 * 2 := by norm_num

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.twisted_lift

end AxCheck
