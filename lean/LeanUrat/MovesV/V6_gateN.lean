/-  MovesV unit V6-4c `gateB_threshold` (PREMISE AUDITABLE C21) — THRESHOLD
    N = 3 GIVEN the typed `hensel : CoprimeLiftPack` premise (NEVER an
    unconditional axiom); the multiplier lemma PROVED. -/
import LeanUrat.MovesV.V6_gateB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the multiplier lemma: each level adds exactly 2³ free digits. -/
theorem gateB_multiplier (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℚ) ^ (3 * (N + 1) - 5 : ℕ) = 2 ^ 3 * 2 ^ (3 * N - 5 : ℕ) := by
  rw [← pow_add]
  congr 1
  omega

/-- level-3 determinacy of the event data, GIVEN the lift pack: the
designated factor is a FUNCTION of f mod 2^k BY TYPE, and its mod-2^k
data determine the box events from level 3 on (sorry-gated derivation). -/
theorem gateB_threshold (hensel : CoprimeLiftPack) (k : ℕ) (hk : 1 ≤ k)
    (f : Polynomial (ZMod (2 ^ k))) (hf : f.Monic)
    (ub hb : Polynomial (ZMod 2)) (hcop : IsCoprime ub hb) (hmh : hb.Monic)
    (hfac : reduce2 k hk f = ub * hb) :
    (∃ u, u * hensel.hOf k f = f) ∧ (hensel.hOf k f).Monic ∧
      reduce2 k hk (hensel.hOf k f) = hb :=
  hensel.hOf_spec k hk f hf ub hb hcop hmh hfac

end LeanUrat.MovesV
