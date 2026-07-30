/-
Unit C5.massRec
moves_ref: §C.2 proof spine: the (ZC-c) mass recursion (statement unchanged; ROUND 3: the
summands are now PINNED to the D.11 inventory by J.mstar_eq — audit R2 F39/blocker 57)

The (ZC-c) cumulative bookkeeping: the number of pinned coordinates of the state cylinder
`Σ_k` equals the running total of the fresh species-inventory counts `m*(ν_i)` over the reads
`i < k`. A clean induction on `k`:
* base (`k = 0`): `Σ_0` is the full box (`J.init` — nothing pinned), so `numPinned = 0`, which
  is the empty sum `Σ_{i∈range 0} m*`;
* step (`k → k+1`): one read pins exactly `m*(ν_k)` new coordinates — the declared per-step
  dependency `C4.numPinnedStep`, imported from its unit module `C4_numPinnedStep`.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C4_numPinnedStep

open Polynomial LeanUrat.Moves
namespace LeanUrat.MovesC
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C5_massRec {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (k : ℕ) (hk : k ≤ H.nodes.length) : (J.Sigma k).numPinned = (Finset.range k).sum (fun i => (J.fresh i).mstar) := by
  revert hk
  induction k with
  | zero =>
      intro _
      -- `Σ_0` is the full box: nothing pinned, so `numPinned = 0 = Σ_{range 0}`.
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold DigitSystem.numPinned
      simp [J.init]
  | succ k ih =>
      intro hk
      have hk' : k ≤ H.nodes.length := Nat.le_of_succ_le hk
      have hik : k < H.nodes.length := hk
      rw [Finset.sum_range_succ, ← ih hk', C4_numPinnedStep J k hik]

end LeanUrat.MovesC
