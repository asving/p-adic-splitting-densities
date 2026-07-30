/-
Unit C0.unitriBij — moves_ref: §C.0.5 (unitriangular ⟹ bijection, both directions)
A unitriangular move Θ (each coordinate = identity + a correction of ≺-earlier coordinates)
is bijective. Both directions run by strong recursion on the coordinate index i.val:
injectivity recovers x i from Θx i once the earlier coordinates agree; surjectivity builds
the preimage one coordinate at a time. ZMod p may be infinite (p = 0), so we cannot use the
"injective on a finite type" shortcut and must construct the inverse explicitly.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

theorem C0_unitriBij {m : ℕ} {Θ : (Fin m → ZMod p) → (Fin m → ZMod p)} (h : IsUnitriangular Θ) : Function.Bijective Θ := by
  -- Extract the per-coordinate correction functions and their defining law.
  choose C hC using h
  -- hC : ∀ (i : Fin m) (x : Fin m → ZMod p), Θ x i = x i + C i (fun j _ => x j)
  refine ⟨?_, ?_⟩
  · -- Injectivity: strong recursion on i.val.
    intro x y hxy
    funext i
    have aux : ∀ n : ℕ, ∀ i : Fin m, i.val < n → x i = y i := by
      intro n
      induction n with
      | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
      | succ n ih =>
        intro i hi
        have hile : i.val ≤ n := Nat.lt_succ_iff.mp hi
        -- The correction argument agrees, by the inductive hypothesis on earlier coordinates.
        have hcorr : (fun (j : Fin m) (_ : j < i) => x j) = (fun j _ => y j) := by
          funext j hj
          exact ih j (by omega)
        have e1 : Θ x i = x i + C i (fun j _ => y j) := by rw [hC i x, hcorr]
        have e2 : Θ y i = y i + C i (fun j _ => y j) := hC i y
        have hcancel : x i + C i (fun j _ => y j) = y i + C i (fun j _ => y j) := by
          rw [← e1, ← e2, hxy]
        exact add_right_cancel hcancel
    exact aux (i.val + 1) i (Nat.lt_succ_self _)
  · -- Surjectivity: build the preimage coordinate by coordinate.
    intro y
    have aux : ∀ n : ℕ, ∃ x : Fin m → ZMod p, ∀ i : Fin m, i.val < n → Θ x i = y i := by
      intro n
      induction n with
      | zero => exact ⟨y, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      | succ n ih =>
        obtain ⟨x, hx⟩ := ih
        by_cases hn : n < m
        · -- Fix coordinate n by an explicit update; earlier coordinates are untouched.
          set k : Fin m := ⟨n, hn⟩ with hkdef
          set x' : Fin m → ZMod p :=
            fun i => if i.val = n then y k - C k (fun j _ => x j) else x i with hx'def
          refine ⟨x', ?_⟩
          intro i hi
          have hile : i.val ≤ n := Nat.lt_succ_iff.mp hi
          -- The correction argument for x' agrees with x (all earlier coords are < n).
          have corrAgree : (fun (j : Fin m) (_ : j < i) => x' j) = (fun j _ => x j) := by
            funext j hj
            have hjn : j.val < n := by omega
            simp only [hx'def]
            rw [if_neg (ne_of_lt hjn)]
          have hstep : Θ x' i = x' i + C i (fun j _ => x j) := by
            rw [hC i x', corrAgree]
          by_cases hlt : i.val < n
          · -- Earlier coordinate: x' i = x i, so Θ x' i = Θ x i = y i.
            have hxi : x' i = x i := by
              simp only [hx'def]
              rw [if_neg (ne_of_lt hlt)]
            rw [hstep, hxi, ← hC i x]
            exact hx i hlt
          · -- The freshly-fixed coordinate i = k: the update makes Θ x' i = y i by design.
            have hin : i.val = n := le_antisymm hile (not_lt.mp hlt)
            have hik : i = k := Fin.ext (by rw [hkdef]; exact hin)
            have hxi : x' i = y k - C k (fun j _ => x j) := by
              simp only [hx'def]
              rw [if_pos hin]
            have hy : y i = y k := by rw [hik]
            have hCeq : C i (fun j _ => x j) = C k (fun j _ => x j) := by rw [hik]
            rw [hstep, hxi, hCeq, hy]
            ring
        · -- n ≥ m: every coordinate already has val < n, so x works unchanged.
          refine ⟨x, ?_⟩
          intro i _
          exact hx i (lt_of_lt_of_le i.isLt (not_lt.mp hn))
    obtain ⟨x, hx⟩ := aux m
    exact ⟨x, funext fun i => hx i i.isLt⟩

end LeanUrat.MovesC
