/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.C4_nsLadder
import LeanUrat.MovesT.C5_nsFree
import LeanUrat.MovesT.C6_nsPrice
import LeanUrat.MovesC.C0_pinTransport
import LeanUrat.MovesC.C6_thmC_a
import LeanUrat.MovesC.C6_thmC_b

/-! # T-C7 `ns_null` — THE FINITE-LEVEL FACE of (ns-null) (MOVES 7210–7231). SCOPE
RIDER (binding on every consumer, quoted in T-D12's S-2 row): this corpus states ONLY
the truncated-ratio limit; continuity-from-above and the profinite class NEVER enter.
`Mlev`/`JetTower`/`stateTruncAt`/`nsTruncAt` are Defs §2.5a/§2.10 carriers (the
stateTruncAt/nsTruncAt junk-total `dite` is an E-DEV, MANIFEST). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-! PROOF-LAYER HELPERS (private; no statement surface): the recorded move composite
`seg`/`Psi` is unitriangular — `id` is, and unitriangular maps compose.  Feeds
`C0_pinTransport` inside `ns_null`'s finite→locus bridge. -/

private lemma unitri_id {m : ℕ} :
    IsUnitriangular (id : (Fin m → ZMod p) → (Fin m → ZMod p)) :=
  fun _ => ⟨fun _ => 0, fun x => (add_zero _).symm⟩

private lemma unitri_comp {m : ℕ}
    {Θ₁ Θ₂ : (Fin m → ZMod p) → (Fin m → ZMod p)}
    (h₁ : IsUnitriangular Θ₁) (h₂ : IsUnitriangular Θ₂) :
    IsUnitriangular (Θ₁ ∘ Θ₂) := by
  intro i
  obtain ⟨c₁, hc₁⟩ := h₁ i
  choose c₂ hc₂ using h₂
  refine ⟨fun f => c₂ i f
    + c₁ (fun j hj => f j hj + c₂ j (fun j' hj' => f j' (hj'.trans hj))), fun x => ?_⟩
  show Θ₁ (Θ₂ x) i = _
  rw [hc₁ (Θ₂ x)]
  have hΘ₂x : ∀ j : Fin m, Θ₂ x j = x j + c₂ j (fun j' _ => x j') := fun j => hc₂ j x
  have harg : (fun j (_ : j < i) => Θ₂ x j)
      = (fun j (_ : j < i) => x j + c₂ j (fun j' _ => x j')) := by
    funext j hj; exact hΘ₂x j
  rw [hΘ₂x i, harg, add_assoc]

private lemma seg_unitri {N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) :
    ∀ k : ℕ, IsUnitriangular (J.seg i k)
  | 0 => unitri_id
  | (k + 1) => by
      show IsUnitriangular (if i ≤ k then J.seg i k ∘ J.Theta k else id)
      split
      · exact unitri_comp (seg_unitri J i k) (J.Theta_uni k)
      · exact unitri_id

theorem ns_null {H : History p F} (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hzc : ∀ N' h, ZCPack (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop)
    (hne : ∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ)
        / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0) := by
  -- Per level (T-C5 at M = Mlev): the admissible cap-M lump locus, its lump shape,
  -- and the pin-count lower bound `Mlev − M₀ ≤ pinCount Z`.
  -- T-C5 (`nsZ_free`) instantiated at `M = Mlev`, per level (its `hMcap` is `le_rfl`
  -- exactly at the cap — the blueprint row's consumption).
  have nsZ_free' : ∀ N' : {k // N₀ ≤ k},
      ∃ Z : Locus p (n * N'.1),
        AdmissibleZ ((Jat N'.1 N'.2).Sigma H.nodes.length) Z ∧
          IsLumpLocus (Jat N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1) Z ∧
          Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2) ≤ pinCount Z := by
    intro N'
    exact nsZ_free (Jat N'.1 N'.2) (hzc N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1)
      (hM₀ N'.1 N'.2) le_rfl
  choose Z hZadm hZlump hZcnt using nsZ_free'
  -- The pin-count ladder tends to 0 (T-C4 with `lower := Mlev − M₀`, whose divergence
  -- is exactly `hMgrow`).
  have hlad : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (p : ℝ) ^ (-(pinCount (Z N') : ℤ)))
      Filter.atTop (nhds 0) :=
    ns_ladder (fun N' => pinCount (Z N'))
      (fun N' => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      (fun N' => hZcnt N') hMgrow
  refine squeeze_zero (fun N' => by positivity) (fun N' => ?_) hlad
  -- Fix the level; the ratio is bounded above by `p^(−pinCount Z)`.
  have hstate : stateTruncAt Jat N'.1
      = (Jat N'.1 N'.2).SHZ (topLocus p (n * N'.1)) := by
    simp only [stateTruncAt, dif_pos N'.2]
  have hns : nsTruncAt Jat Lat N'.1
      = stateTruncAt Jat N'.1 ∩ (Lat N'.1 N'.2).L (Mlev (Jat N'.1 N'.2) N'.1) := by
    simp only [nsTruncAt, dif_pos N'.2]
  -- THE FINITE→LOCUS BRIDGE, through the pin-transport pullback (`C0_pinTransport`):
  -- the lump event is a FRAME-0 digit condition (`vanish` reads `digitAt x` on the
  -- box point), while `SHZ (Z N')` pins the TERMINAL frame — the two loci differ by
  -- the recorded move composite `Psi`.  Pull `Z N'` back along the unitriangular
  -- `Psi` to a terminal locus `Zt` with THE SAME PINS: the truncated lump event
  -- lands in `SHZ Zt` (via `C6_thmC_a`'s image form), and `SHZ Zt` / `SHZ (Z N')`
  -- have EQUAL counts (two `C6_thmC_b` instances share the box mass), which is all
  -- the pricing squeeze consumes.
  have hPsiU : IsUnitriangular ((Jat N'.1 N'.2).Psi H.nodes.length) :=
    seg_unitri (Jat N'.1 N'.2) 0 H.nodes.length
  obtain ⟨Zt, hZtSol, hZtPins⟩ := C0_pinTransport (Z N') hPsiU
  have hZtadm : AdmissibleZ ((Jat N'.1 N'.2).Sigma H.nodes.length) Zt := by
    intro c hc
    exact hZadm N' c ((hZtPins c) ▸ hc)
  have hsub : nsTruncAt Jat Lat N'.1 ⊆ (Jat N'.1 N'.2).SHZ Zt := by
    rw [hns]
    rintro x ⟨hxs, hxL⟩
    obtain ⟨-, htopEq, -⟩ := C6_thmC_a (Jat N'.1 N'.2) (topLocus p (n * N'.1))
      (topLocus_admissible ((Jat N'.1 N'.2).Sigma H.nodes.length))
    rw [hstate, htopEq] at hxs
    obtain ⟨w, ⟨hwSig, -⟩, rfl⟩ := hxs
    -- `vanish` + the lump locus's literal-zero values: `Z N'` solves at `Psi w = x`.
    have hZsol : (Z N').IsSolution ((Jat N'.1 N'.2).Psi H.nodes.length w) := by
      intro c hc
      have hciFI : c ∈ interiorFreshIdx (Jat N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1) :=
        ((hZlump N').1 c).mp hc
      rw [(hZlump N').2 c hciFI]
      exact ((Lat N'.1 N'.2).vanish _ _).mp hxL c hciFI
    obtain ⟨-, hZtEq, -⟩ := C6_thmC_a (Jat N'.1 N'.2) Zt hZtadm
    rw [hZtEq]
    exact ⟨w, ⟨hwSig, (hZtSol w).mpr hZsol⟩, rfl⟩
  -- Equal counts across the pin-transport: same pins ⇒ same `totalPins`, and two
  -- Theorem C(b) instances share the box mass.
  have hcards : Nat.card ↥((Jat N'.1 N'.2).SHZ Zt)
      = Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) := by
    have h1 := C6_thmC_b (Jat N'.1 N'.2) Zt hZtadm
    have h2 := C6_thmC_b (Jat N'.1 N'.2) (Z N') (hZadm N')
    have hTP : totalPins (Jat N'.1 N'.2) Zt = totalPins (Jat N'.1 N'.2) (Z N') := by
      have hpe : Zt.pinned = (Z N').pinned := funext hZtPins
      unfold totalPins DigitSystem.numPinned
      rw [hpe]
    rw [hTP, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right
      (pow_pos (Fact.out : p.Prime).pos (totalPins (Jat N'.1 N'.2) (Z N'))) h1
  -- T-C6 prices the locus exactly: |S(H, Z)| · p^{pinCount Z} = |state|.
  have hprice : Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) * p ^ pinCount (Z N')
      = Nat.card ↥(stateTruncAt Jat N'.1) := by
    rw [hstate]
    exact ns_price (Jat N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1) (hM₀ N'.1 N'.2)
      (Z N') (hZadm N') (hZlump N')
  -- Cardinal monotonicity along the bridge inclusion, read through the equal counts.
  have hbcard : Nat.card ↥(nsTruncAt Jat Lat N'.1)
      ≤ Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) := by
    rw [← hcards]
    exact Set.ncard_le_ncard hsub (Set.toFinite ((Jat N'.1 N'.2).SHZ Zt))
  -- Denominator positive (realized states have members — `hne`).
  have hDpos : 0 < Nat.card ↥(stateTruncAt Jat N'.1) := by
    haveI : Nonempty ↥(stateTruncAt Jat N'.1) := (hne N'.1 N'.2).to_subtype
    exact Nat.card_pos
  set b := Nat.card ↥(nsTruncAt Jat Lat N'.1) with hb
  set a := Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) with ha
  set D := Nat.card ↥(stateTruncAt Jat N'.1) with hD'
  set P := pinCount (Z N') with hP
  -- Recast the price as a real identity `D = a · p^P`.
  have hDR : (D : ℝ) = (a : ℝ) * (p : ℝ) ^ P := by
    rw [← hprice]; push_cast; ring
  have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have hpPpos : (0 : ℝ) < (p : ℝ) ^ P := pow_pos hp0 P
  have hpPne : ((p : ℝ) ^ P) ≠ 0 := ne_of_gt hpPpos
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_mul] at hprice; omega
    · exact h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  -- Assemble: b/D ≤ a/D = 1/p^P = p^{−P}.
  show (b : ℝ) / D ≤ (p : ℝ) ^ (-(P : ℤ))
  rw [zpow_neg, zpow_natCast, hDR, div_le_iff₀ (mul_pos haR hpPpos)]
  have hsimp : ((p : ℝ) ^ P)⁻¹ * ((a : ℝ) * (p : ℝ) ^ P) = (a : ℝ) := by
    rw [mul_comm ((p : ℝ) ^ P)⁻¹, mul_assoc, mul_inv_cancel₀ hpPne, mul_one]
  rw [hsimp]
  exact_mod_cast hbcard

end LeanUrat.MovesT
