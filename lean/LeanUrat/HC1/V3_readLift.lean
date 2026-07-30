/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V2_readResidual
import LeanUrat.HC1.V34_readKernel
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_GRg

/-!
# HC1.V3_readLift — the recorded lift is the regrade's standard lift (blueprint §10, V3)

V′-KERNEL unit (blueprint §10.1; §10 Key Finding 1): the recorded lift
`IsReadLift σ ψ g e★ h★ Φ̂` is (†)-EQUAL-WEIGHT — its weights
`σ.w(t_k) = h★·(g−k)` give `e★·σ.w(t_k) + (e★k)·h★ = e★·h★·g` for every present
slot and for the leading slot, EXACTLY D.5's "EQUAL WEIGHTS" display (MOVES
2268–2269) transposed to wV — hence `IsReadLift` IS the standard-lift shape OF
THE REGRADED FRAME (wVPrev := σ.w, index (e★, h★)), and the D.5 residual
computation re-runs verbatim:

* the lift's read weight `wV(Φ̂) = e★·h★·g`;
* the D.5 residual display `RV(Φ̂) = T(m̂★)·(ψ as Laurent)`, `m̂★ = −t★·h★·g`
  (via the distinct-exponents sum `k − t★·h★·g`, MOVES 2270–2276);
* K1(Φ̂/wV): `wV(f) = min_m (wV(B_m) + m·e★h★g)` with attainment.

moves_ref: D.5 VERBATIM (MOVES 2253–2289 — the whole display re-runs at the
ReadFrame; the Lean pattern is L3_liftResidual + L3_K1).
deps: V2, the L3_digPrime_nonzero-analog at the same key (width < g: D.3(d)).
difficulty: medium.  E-phase: statement per §10.1, `sorry` body.

## P-phase proof structure (2026-07-28; the D.5 mirror at the ReadFrame)

The regrade is NOT a `Stage` (§10 Finding 3: `hS6b`/`hvalgrp` are unsatisfiable
at regrades for `σ.e > 1`), so `L3_liftResidual`/`L3_K1` cannot be cited — they
are MIRRORED over the partial pack `(wV, RV) = (childW σ σ.Φ e★ h★, V.D.Rv)`:

* `v3_decomp_sum` — the distinct-position monomial decomposition engine (the
  `L2_slotDecomp` `decomp_sum`, transposed; consumes `hRadd`/`hWjump`/`hRneg`).
* `v3_lift_core` — C2+C3 in ONE decomp_sum application: all lift slots are tied
  at weight `e★h★g` with residual monomials at the DISTINCT positions `D + k`,
  `D = −t★h★g` (Bézout `e★s★ + h★t★ = 1`), so `wV(Φ̂) = e★h★g` and
  `RV(Φ̂) = T(D)·ψ` in one stroke; the (S5)-preserved scalar of each slot is
  identified with `ψ_k` by matching `σ.R` monomials (hS5 ∧ IsReadLift).
* `v3_devForm` — RV of ANY `Φ`-development is the sum of its wV-minimizing slot
  residuals (V.hK1 + decomp_sum + hRlt); hence `v3_width`: on `Ĉ∖0` the RV
  support has width < g (`e★·pos = j − t★·wV`, slots `j < e★g`), hence
  `v3_psiNotDvd`: `ψ ∤ RV(B)` (the L3_digPrime_nonzero-analog at the same key).
* `v3_key_no_cancel`/`v3_minsum_facts` — the L3_K1 no-cancellation engine at
  `(Φ̂, wV, RV)` (simplified: the pack carries `hRneg`/`hWjump` outright, so no
  `R(−1)` bookkeeping); C4 assembles exactly as L3_K1's main body.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ


/-- Unit V3: the recorded read-pair lift is the REGRADE's standard lift — equal
(†)-weights of all present slots (the D.5 EQUAL WEIGHTS display at wV), the D.5
residual display `RV(Φ̂) = T(−t★h★g)·ψ`, and K1 at (Φ̂, wV).

The first conjunct is the D.5 arithmetic in ARBITRARY-FAMILY form (any `tt`
satisfying the weight premise); the form TIED TO `hlift`'s own witness family,
with D.5's leading-slot equation, is the addendum `V3_equalWeights_lift` below
(VPRIME_CONFIRM gap 7, closed 2026-07-28). -/
theorem V3_readLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hirr : Irreducible ψ)
    (hne : ψ ≠ Polynomial.X) (hdeg : ψ.natDegree = g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    (∀ tt : ℕ → Polynomial ℤ_[p],
        (∀ k, k < g → ψ.coeff k ≠ 0 →
          σ.w (tt k) = (hstar : ℤ) * ((g : ℤ) - (k : ℤ))) →
        ∀ k, k < g → ψ.coeff k ≠ 0 →
          (estar : ℤ) * σ.w (tt k) + ((estar : ℤ) * (k : ℤ)) * (hstar : ℤ)
            = (estar : ℤ) * (hstar : ℤ) * (g : ℤ)) ∧
    childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
    V.D.Rv Φhat
      = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
          Polynomial.toLaurent ψ ∧
    K1At (childW σ σ.Φ estar hstar) Φhat ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
  classical
  have hee : 1 ≤ estar := hrp.1
  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have hg1 : 1 ≤ g := by
    have := hirr.natDegree_pos
    omega
  obtain ⟨hΦne, hwhat, hRhat⟩ := v3_lift_core V hrp ψ g hmon hdeg hg1 Φhat hlift
  obtain ⟨hMon, hDeg⟩ := v3_lift_monic hee ψ g hg1 Φhat hlift
  refine ⟨?_, hwhat, hRhat, ?_⟩
  · -- C1: the D.5 EQUAL WEIGHTS display at wV
    intro tt htw k hk hc
    rw [htw k hk hc]
    ring
  · -- C4: Lemma K1 at (Φ̂, wV) — the L3_K1 main body, mirrored
    intro f B N hf hdev
    obtain ⟨hdegB, hzero, hsumf⟩ := hdev
    -- slot weights
    have hwa : ∀ j, B j ≠ 0 →
        childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B j) + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      intro j hBj
      rw [V.hwmul _ _ hBj (pow_ne_zero j hΦne), v3_wv_pow V Φhat hΦne j, hwhat]
    -- the nonzero-slot set and the attained minimum
    set SN : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSNdef
    have hSNmem : ∀ j : ℕ, j ∈ SN ↔ j < N ∧ B j ≠ 0 := by
      intro j
      rw [hSNdef, Finset.mem_filter, Finset.mem_range]
    have hSNne : SN.Nonempty := by
      have hfs : (∑ j ∈ Finset.range N, B j * Φhat ^ j) ≠ 0 := by rw [← hsumf]; exact hf
      obtain ⟨j, hjr, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfs
      refine ⟨j, (hSNmem j).mpr ⟨Finset.mem_range.mp hjr, fun hBj => hjne ?_⟩⟩
      rw [hBj, zero_mul]
    obtain ⟨m, hmle, j₀, hj₀SN, hj₀eq⟩ :
        ∃ m : ℤ, (∀ j ∈ SN, m ≤ childW σ σ.Φ estar hstar (B j)
            + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
          ∃ j₀, j₀ ∈ SN ∧ m = childW σ σ.Φ estar hstar (B j₀)
            + (j₀ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      obtain ⟨j₁, hj₁, heq₁⟩ := Finset.exists_mem_eq_inf' hSNne
        (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)))
      exact ⟨SN.inf' hSNne (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))),
        fun j hj => Finset.inf'_le _ hj, j₁, hj₁, heq₁⟩
    have hSN_B : ∀ j ∈ SN, B j ≠ 0 := fun j hj => ((hSNmem j).mp hj).2
    -- minimizing and non-minimizing slots
    set Smin : Finset ℕ := SN.filter
      (fun j => childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) with hSminDef
    set Srest : Finset ℕ := SN.filter
      (fun j => ¬ (childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m)) with hSrestDef
    have hSminMem : ∀ j : ℕ, j ∈ Smin ↔
        j ∈ SN ∧ childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m := by
      intro j
      rw [hSminDef, Finset.mem_filter]
    have hSrestMem : ∀ j : ℕ, j ∈ Srest ↔
        j ∈ SN ∧ ¬ (childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) := by
      intro j
      rw [hSrestDef, Finset.mem_filter]
    have hj₀Smin : j₀ ∈ Smin := (hSminMem j₀).mpr ⟨hj₀SN, hj₀eq.symm⟩
    have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => hSN_B j ((hSminMem j).mp hj).1
    have hSminw : ∀ j ∈ Smin, childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m := by
      intro j hj
      rw [hwa j (hSminB j hj)]
      exact ((hSminMem j).mp hj).2
    obtain ⟨hminNe, hminW, -⟩ := v3_minsum_facts V hee hbez ψ g hdeg hmon hirr hne Φhat hΦne
      hRhat hDeg B hdegB m Smin hSminB hSminw ⟨j₀, hj₀Smin⟩
    -- the development sum over the nonzero slots, split at the minimum
    have hfSN : f = ∑ j ∈ SN, B j * Φhat ^ j := by
      rw [hsumf, hSNdef]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro x hx hax hBx
      exact hax (by rw [hBx, zero_mul])
    have hfd : f = (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) := by
      rw [hfSN, hSminDef, hSrestDef]
      exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
    -- wV f = m
    have hwf : childW σ σ.Φ estar hstar f = m := by
      rcases eq_or_ne (∑ j ∈ Srest, B j * Φhat ^ j) 0 with hr0 | hrne
      · rw [hfd, hr0, add_zero]
        exact hminW
      · have hwrest : m + 1 ≤ childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j) := by
          refine v3_wv_sum_ge V Srest _ (m + 1) ?_ hrne
          intro j hj haj
          have hjSN : j ∈ SN := ((hSrestMem j).mp hj).1
          have hBj : B j ≠ 0 := hSN_B j hjSN
          have h1 := hmle j hjSN
          have h2 : ¬ (childW σ σ.Φ estar hstar (B j)
              + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) :=
            ((hSrestMem j).mp hj).2
          rw [hwa j hBj]
          omega
        have hfne' : (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfd]; exact hf
        have hge : m ≤ childW σ σ.Φ estar hstar f := by
          rw [hfd]
          have h1 := V.hwult _ _ hminNe hrne hfne'
          rw [hminW] at h1
          exact le_trans (le_min le_rfl (by omega)) h1
        by_contra hne'
        have hgt : m < childW σ σ.Φ estar hstar f := lt_of_le_of_ne hge (fun h => hne' h.symm)
        have hnegne : -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrne
        have hfmin_eq : (∑ j ∈ Smin, B j * Φhat ^ j)
            = f + -(∑ j ∈ Srest, B j * Φhat ^ j) := by
          rw [hfd]; ring
        have hminne' : f + -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfmin_eq]; exact hminNe
        have h1 := V.hwult f _ hf hnegne hminne'
        rw [← hfmin_eq, hminW, v3_wv_neg V _ hrne] at h1
        have h3 : m < min (childW σ σ.Φ estar hstar f)
            (childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j)) := lt_min hgt (by omega)
        omega
    -- assemble SlotMinAttained
    refine ⟨?_, j₀, ?_, ?_, ?_⟩
    · intro j hjN hBj
      have hjSN : j ∈ SN := (hSNmem j).mpr ⟨hjN, hBj⟩
      rw [hwf]
      exact hmle j hjSN
    · exact ((hSNmem j₀).mp hj₀SN).1
    · exact hSN_B j₀ hj₀SN
    · rw [hwf]; exact hj₀eq

/-- **V3 addendum (VPRIME_CONFIRM gap 7, closed 2026-07-28): the EQUAL-WEIGHTS
display TIED TO THE LIFT WITNESS.** `V3_readLift`'s first conjunct states the
D.5 arithmetic for an ARBITRARY weight-conforming family; this corollary
instantiates it at the witness family `tt` CONTAINED IN `hlift` (the
`IsReadLift` destructuring — its weight clause `σ.w (tt k) = h★·(g−k)` is
exactly the premise), and adds the LEADING-SLOT equation of D.5's display
(MOVES 2268–2269: "EQUAL WEIGHTS: each present slot has w(t_k) + ek·h =
eh(g−k) + ekh = ehg, and the leading slot 0 + eg·h = ehg", transposed to wV):
the recorded lift's leading slot is `σ.Φ^{e★g}` with coefficient literally `1`,
of parent weight `σ.w 1 = 0`. -/
theorem V3_equalWeights_lift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (estar hstar : ℕ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p])
    (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    ∃ tt : ℕ → Polynomial ℤ_[p],
      Φhat = σ.Φ ^ (estar * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (estar * k) ∧
      (∀ k, k < g → ψ.coeff k ≠ 0 →
        (estar : ℤ) * σ.w (tt k) + ((estar : ℤ) * (k : ℤ)) * (hstar : ℤ)
          = (estar : ℤ) * (hstar : ℤ) * (g : ℤ)) ∧
      (estar : ℤ) * σ.w (1 : Polynomial ℤ_[p]) + ((estar : ℤ) * (g : ℤ)) * (hstar : ℤ)
        = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) := by
  obtain ⟨tt, htt0, httk, hΦhat⟩ := hlift
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  refine ⟨tt, hΦhat, ?_, ?_⟩
  · intro k hk hc
    rw [(httk k hk hc).2.2.1]
    ring
  · rw [hw1]
    ring

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V3_readLift
#print axioms LeanUrat.HC1.V3_equalWeights_lift
