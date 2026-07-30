/-
Unit C0.pinStatus — moves_ref: §C.0.5 PIN-WELLDEF, rev-9 scope: cardinality AND
per-coordinate free/determined STATUS.
Two loci with the same solution set have the same pinned status at every coordinate.
Key fact (no counting needed): for a unitriangular digit system, coordinate `j` is
PINNED iff every pair of solutions that agree on all ≺-earlier coordinates already
agrees at `j` — a property of the solution set alone. The `→` direction is the pin
equation; the `←` direction builds two solutions that differ exactly at `j`
(`mkSol`), which needs a second alphabet element, hence `Fact p.Prime`.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime]

/-! ### Solution construction for a unitriangular digit system (file-local helpers). -/

/-- Build the solution of `D` whose free (non-pinned) coordinates take the prescribed
values `free`; pinned coordinates are solved from strictly-earlier ones. -/
private def mkSol {m : ℕ} {α : Type*} (D : DigitSystem m α) (free : Fin m → α) : (i : Fin m) → α
  | i => if D.pinned i = true then D.solve i (fun j hj => mkSol D free j) else free i
  termination_by i => i.val
  decreasing_by exact hj

private theorem mkSol_eq {m : ℕ} {α : Type*} (D : DigitSystem m α) (free : Fin m → α) (i : Fin m) :
    mkSol D free i = if D.pinned i = true then D.solve i (fun j _ => mkSol D free j) else free i := by
  rw [mkSol]

private theorem mkSol_isSol {m : ℕ} {α : Type*} (D : DigitSystem m α) (free : Fin m → α) :
    D.IsSolution (mkSol D free) := by
  intro i hi
  rw [mkSol_eq D free i, if_pos hi]

private theorem mkSol_free {m : ℕ} {α : Type*} (D : DigitSystem m α) (free : Fin m → α) (i : Fin m)
    (hi : D.pinned i = false) : mkSol D free i = free i := by
  rw [mkSol_eq D free i, if_neg (by rw [hi]; decide)]

/-- If two free assignments agree below `j`, the two built solutions agree below `j`. -/
private theorem mkSol_agree_below {m : ℕ} {α : Type*} (D : DigitSystem m α) (f1 f2 : Fin m → α)
    (j : Fin m) (hf : ∀ i : Fin m, i < j → f1 i = f2 i) :
    ∀ i : Fin m, i < j → mkSol D f1 i = mkSol D f2 i
  | i, hi => by
    rw [mkSol_eq D f1 i, mkSol_eq D f2 i]
    by_cases hp : D.pinned i = true
    · rw [if_pos hp, if_pos hp]
      have harg : (fun (k : Fin m) (_ : k < i) => mkSol D f1 k)
          = (fun (k : Fin m) (_ : k < i) => mkSol D f2 k) := by
        funext k hk
        exact mkSol_agree_below D f1 f2 j hf k (hk.trans hi)
      rw [harg]
    · rw [if_neg hp, if_neg hp]
      exact hf i hi
  termination_by i _ => i.val
  decreasing_by exact hk

/-- **PIN-WELLDEF, per-coordinate.** For a unitriangular digit system over a nontrivial
alphabet, coordinate `j` is pinned iff every two solutions agreeing on all ≺-earlier
coordinates agree at `j`. The RHS mentions only the solution set. -/
private theorem pinnedIffDet {m : ℕ} {α : Type*} [Nontrivial α] (D : DigitSystem m α) (j : Fin m) :
    D.pinned j = true ↔
      ∀ x y : Fin m → α, D.IsSolution x → D.IsSolution y →
        (∀ i : Fin m, i < j → x i = y i) → x j = y j := by
  constructor
  · intro hpin x y hx hy hag
    have hxj := hx j hpin
    have hyj := hy j hpin
    have harg : (fun (k : Fin m) (_ : k < j) => x k) = (fun (k : Fin m) (_ : k < j) => y k) := by
      funext k hk; exact hag k hk
    rw [hxj, hyj, harg]
  · intro hdet
    by_contra hcon
    rw [Bool.not_eq_true] at hcon
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    have hagf : ∀ i : Fin m, i < j →
        (fun _ : Fin m => a) i = (fun i => if i = j then b else a) i := by
      intro i hi
      simp only [if_neg hi.ne]
    have hx : D.IsSolution (mkSol D (fun _ => a)) := mkSol_isSol D _
    have hy : D.IsSolution (mkSol D (fun i => if i = j then b else a)) := mkSol_isSol D _
    have hag := mkSol_agree_below D (fun _ => a) (fun i => if i = j then b else a) j hagf
    have hxj : mkSol D (fun _ : Fin m => a) j = a := by rw [mkSol_free D _ j hcon]
    have hyj : mkSol D (fun i => if i = j then b else a) j = b := by
      rw [mkSol_free D _ j hcon]; simp
    have hcontra := hdet _ _ hx hy hag
    rw [hxj, hyj] at hcontra
    exact hab hcontra

/-! ### The unit statement. -/

theorem C0_pinStatus {m : ℕ} (D D' : Locus p m) (h : ∀ x, D.IsSolution x ↔ D'.IsSolution x) : ∀ j : Fin m, D.pinned j = D'.pinned j := by
  haveI : Nontrivial (ZMod p) := inferInstance
  intro j
  have key : D.pinned j = true ↔ D'.pinned j = true := by
    rw [pinnedIffDet D j, pinnedIffDet D' j]
    constructor
    · exact fun hd x y hx hy hag => hd x y ((h x).mpr hx) ((h y).mpr hy) hag
    · exact fun hd x y hx hy hag => hd x y ((h x).mp hx) ((h y).mp hy) hag
  cases hD : D.pinned j <;> cases hD' : D'.pinned j <;> simp_all

end LeanUrat.MovesC
