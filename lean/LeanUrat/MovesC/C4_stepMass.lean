/-
Unit C4.stepMass
moves_ref: §C.1.5'(1)+(2) mass clause (statement unchanged; ROUND 3: the recursion runs
through the STRATUM — J.recursion + J.inh_implied replace the round-2 fresh-only recursion,
audit R2 F43)

One step of the mass recursion: consuming read `ν_i` multiplies the mass by `p^{−m*(ν_i)}`,
i.e. `mass(Σ_{i+1}) · p^{m*} = mass(Σ_i)`.

Proof (per sketch):
* `J.recursion i hi`: `Σ_{i+1}`-solutions are the `Θ_i`-pullback of `{Σ_i ∧ stratum ν_i}`.
* `J.inh_implied i hi` rewrites `stratum ν_i` to `(fresh ν_i).sat` ON `Σ_i`-solutions
  (`and_congr_right`, since the inherited content is implied on the state cylinder).
* `Θ_i` is bijective (`C0.unitriBij` on `J.Theta_uni`); transporting the pulled-back joint
  count along it (`Nat.card_congr` + `Equiv.subtypeEquiv`) identifies it with the joint count
  `#{Σ_i ∧ fresh}`.
* `C4.conditionalMass` with `hfree := C2.freshFree` closes `#{Σ_i ∧ fresh}·p^{m*} = mass(Σ_i)`.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C4_conditionalMass
import LeanUrat.MovesC.C0_unitriBij
import LeanUrat.MovesC.C2_freshFree

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C4_stepMass {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) (hi : i < H.nodes.length) : (J.Sigma (i+1)).mass * p ^ (J.fresh i).mstar = (J.Sigma i).mass := by
  -- `Θ_i` is bijective (unitriangular ⟹ bijective).
  have hbij : Function.Bijective (J.Theta i) := C0_unitriBij (J.Theta_uni i)
  -- Claim A: `Σ_{i+1}`-solutions ↔ the `Θ_i`-pullback of `{Σ_i-solutions ∧ fresh-sat}`.
  -- `recursion` gives the stratum form; `inh_implied` reduces the stratum to `fresh.sat` on
  -- `Σ_i`-solutions (the inherited content is implied there).
  have hA : ∀ x : Fin m → ZMod p,
      (J.Sigma (i+1)).IsSolution x ↔
        ((J.Sigma i).IsSolution (J.Theta i x) ∧ (J.fresh i).sat (J.Theta i x)) := fun x =>
    (J.recursion i hi x).trans
      (and_congr_right (fun hsol => J.inh_implied i hi (J.Theta i x) hsol))
  -- Rewrite `mass(Σ_{i+1})` as the pulled-back joint count.
  have hmass : (J.Sigma (i+1)).mass
      = Nat.card {x : Fin m → ZMod p //
          (J.Sigma i).IsSolution (J.Theta i x) ∧ (J.fresh i).sat (J.Theta i x)} := by
    unfold Locus.mass
    exact Nat.card_congr (Equiv.subtypeEquivRight hA)
  -- Transport the joint count along the bijection `Θ_i` (side condition is `Iff.rfl`, since
  -- `Equiv.ofBijective (J.Theta i) hbij` applied is defeq `J.Theta i`).
  have htrans : Nat.card {x : Fin m → ZMod p //
        (J.Sigma i).IsSolution (J.Theta i x) ∧ (J.fresh i).sat (J.Theta i x)}
      = Nat.card {y : Fin m → ZMod p //
          (J.Sigma i).IsSolution y ∧ (J.fresh i).sat y} :=
    Nat.card_congr
      (Equiv.subtypeEquiv (Equiv.ofBijective (J.Theta i) hbij) (fun _ => Iff.rfl))
  -- Fresh clause supports live on FREE coordinates of `Σ_i` (C2.freshFree = the `hfree`
  -- hypothesis of C4.conditionalMass, at `Sigma := J.Sigma i`, `fd := J.fresh i`).
  have hfree : ∀ cl ∈ (J.fresh i).clauses, ∀ c ∈ cl.support, (J.Sigma i).pinned c = false :=
    C2_freshFree J i hi
  -- Assemble.
  calc (J.Sigma (i+1)).mass * p ^ (J.fresh i).mstar
      = Nat.card {y : Fin m → ZMod p //
          (J.Sigma i).IsSolution y ∧ (J.fresh i).sat y} * p ^ (J.fresh i).mstar := by
        rw [hmass, htrans]
    _ = (J.Sigma i).mass := C4_conditionalMass (J.Sigma i) (J.fresh i) hfree

end LeanUrat.MovesC
