/-
Unit U-9b `ksub` (medium) — the SYMBOLIC (K-SUB) `= 1` in Qq, via U-9a at every
ALL-ACTIVE pool (activity supplied by the locus) + U-27 infinitude on U-22b's
derived infinitude (R39).  deps: U-8, U-9a, U-22b, U-27.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubEval
import LeanUrat.MovesS.RatfuncEvalInfinite
import LeanUrat.MovesS.AllActiveCofinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem ksub {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∑ o : T.Out e τ, routedMass RB e τ o = 1 := by
  -- The symbolic sum `S := ∑ o, routedMass` is a rational function.  U-9a evaluates it
  -- to `1` at every ALL-ACTIVE pool; U-22b makes that locus infinite; U-27 (a rational
  -- function agreeing with `1` at infinitely many points is `1`) closes it, applied to
  -- `S - 1`.
  apply sub_eq_zero.mp
  refine ratfunc_eval_infinite _ (allActivePools M) (allActive_cofinite RB).2 ?_ ?_
  · -- denominator regular on the locus: `S - 1 ∈ OKat x`
    intro x hx
    obtain ⟨hxpool, hxact⟩ := hx
    obtain ⟨hok, -⟩ := ksub_eval RB L hdc he τ hK x hxpool (hxact e he τ)
    have hmem : (∑ o : T.Out e τ, routedMass RB e τ o) - 1 ∈ OKat x :=
      (OKat x).sub_mem hok (OKat x).one_mem
    exact mem_OKat_iff.mp hmem
  · -- the value `(S - 1)(x) = 0`, via the ring hom `evalAt x`
    intro x hx
    obtain ⟨hxpool, hxact⟩ := hx
    obtain ⟨hok, heval⟩ := ksub_eval RB L hdc he τ hK x hxpool (hxact e he τ)
    have hmem : (∑ o : T.Out e τ, routedMass RB e τ o) - 1 ∈ OKat x :=
      (OKat x).sub_mem hok (OKat x).one_mem
    have hsplit : (⟨(∑ o : T.Out e τ, routedMass RB e τ o) - 1, hmem⟩ : OKat x)
        = ⟨∑ o : T.Out e τ, routedMass RB e τ o, hok⟩ - 1 := by
      apply Subtype.ext
      simp
    have key : evalAt x ⟨(∑ o : T.Out e τ, routedMass RB e τ o) - 1, hmem⟩ = 0 := by
      rw [hsplit, map_sub, map_one, heval, sub_self]
    exact key

end LeanUrat.MovesS
