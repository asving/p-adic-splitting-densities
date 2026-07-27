/-
REFUTATION SCRATCH (escalation prover, U27.gate_order0_inert, 2026-07-27) — NOT part of the
HC2 corpus; checked standalone via `lake env lean`.

CLAIM: `PresentSeed p F H n N keys` is UNINHABITED for EVERY nonempty history H — hence the
`∃ S : PresentSeed …` conjunct of U27 `gate_order0_inert` is FALSE, and the unit is
unprovable as stated (a Defs-layer bug, not a prover failure).

MECHANISM: `ZCSeedLaws.downsets_literal` states an unguarded ↔ for ALL polynomials f, ALL
development slots j, ALL β : ℚ. Take f := Φ₀ ^ n (the frame key power), whose development has
the single nonzero slot j = n. No box coordinate has fine slot n (base indices are < n and
`fineSlot b = b / Dwidth ≤ b`), so the right side is VACUOUSLY TRUE for every β; the ↔ then
forces `B n = 0 ∨ β ≤ (σ.w 1)/STR` for every β — but `B n = 1 ≠ 0` and `σ.w 1 = 0` (from the
valuation law `hwmul`), so β := 1 refutes it. The finite-box truncation was dropped in the
E-phase transcription of §C C.1.5's "Downsets are literal" display.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- **The seed type is empty**: no `PresentSeed` exists over ANY history (its
`zcSeed.downsets_literal` is self-contradictory at the out-of-box slot `j = n`). -/
theorem presentSeed_isEmpty {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (keys : ℕ → Polynomial ℤ_[p]) :
    IsEmpty (PresentSeed p F H n N keys) := by
  constructor
  intro S
  have hlen : 0 < H.nodes.length := List.length_pos_iff.mpr H.nonempty
  set ν : Node p F := H.nodes[0]'hlen with hν
  set σ : Stage p F := ν.σ with hσ
  -- the counterexample polynomial and its Φ₀-development
  set f : Polynomial ℤ_[p] := σ.Φ ^ n with hf
  set B : ℕ → Polynomial ℤ_[p] := fun k => if k = n then 1 else 0 with hB
  have hBn : B n = 1 := by simp [hB]
  -- a frame-0 presentation of f (pres 0 is pinned to the literal digit chart)
  obtain ⟨x, hpres⟩ : ∃ x, S.pres 0 x f :=
    ⟨_, (S.pres_zero _ f).mpr (fun j => rfl)⟩
  have hdegpos : 0 < σ.Φ.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega)
  have hdev : IsDevelopment σ.Φ f B (n + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = n
      · simpa [hB, hj, Polynomial.degree_one] using hdegpos
      · simpa [hB, hj] using lt_of_le_of_lt bot_le hdegpos
    · intro j hj
      have hjn : j ≠ n := by omega
      simp [hB, hjn]
    · rw [Finset.sum_eq_single n]
      · simp [hB, hf]
      · intro k _ hkn; simp [hB, hkn]
      · intro hn; exact absurd (Finset.self_mem_range_succ n) hn
  -- fire the seed law at slot j = n, β = 1
  have hiff := S.zcSeed.downsets_literal 0 hlen x f B (n + 1) hpres hdev n 1
  -- the right side is vacuous: no box coordinate has fine slot n
  have hvac : ∀ c : Fin (n * N), ν.fineSlot (boxChart n N c).2 = n →
      H.htH 0 (boxChart n N c) < 1 → x c = 0 := by
    intro c hc _
    exfalso
    have hb : (boxChart n N c).2 < n := (boxChart_lt n N c).2
    have hle : ν.fineSlot (boxChart n N c).2 ≤ (boxChart n N c).2 := Nat.div_le_self _ _
    omega
  have hlhs := hiff.mpr hvac
  -- but the left side is false: B n = 1 ≠ 0, and σ.w 1 = 0 forces β ≤ 0
  have hw1 : σ.w 1 = 0 := by
    have := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  rcases hlhs with h0 | hle
  · rw [hBn] at h0
    exact one_ne_zero h0
  · rw [hBn, hw1] at hle
    norm_num at hle

/-- **U27 `gate_order0_inert` is FALSE as stated** (byte-identical body to the target, under
`¬`): every witness tuple would include an `S : PresentSeed 2 F4 H₀ 2 N keys`, which cannot
exist. -/
theorem gate_order0_inert_refuted (N : ℕ) (hN : 1 ≤ N) :
    ¬ (∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
      KeysLawful H₀ keys ∧
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ∃ (S : PresentSeed 2 F4 H₀ 2 N keys) (J : JetSetup H₀ 2 N (2 * N)),
        totalPins J (topLocus 2 (2 * N)) = 2 ∧
        Nat.card (J.SHZ (topLocus 2 (2 * N))) * 2 ^ 2 = 2 ^ (2 * N)) := by
  rintro ⟨H₀, keys, -, -, -, S, -⟩
  exact (presentSeed_isEmpty H₀ 2 N keys).false S

end LeanUrat.MovesJ
