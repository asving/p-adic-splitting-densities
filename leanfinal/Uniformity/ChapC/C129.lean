/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39b
import Uniformity.ChapC.C02

/-!
# Uniformity.ChapC.C129 — the slot-height calculus for monomial data at a binomial key

**Chapter C, NODE C.129** [lemma] [fresh] [signed: A-C.5]
(`blueprint/CHAP-C_tower_grammar.md`, amendment A-C.5 of 2026-08-16; twin
`leanspec/Leanspec/ChapC.lean`, section `AC5SlotHeights`).  **ENV-C1**.

## What this node is

`leanfinal/notes/C127_PIN_BLOCKED_2026-08-16.md` records C.127's `lawEW_pin` as BLOCKED with
SIX named missing pieces, and judges pieces **1–5** to be "a *height-evaluation layer* that no
landed C-chapter node owns … The honest scope of that layer is its own node (a 'slot-height
calculus' for monomial data at a binomial key), not an inline block inside C.127".  A-C.5
signs that layer as NODE C.129.  Piece **6** (the `b = m − 1` collision) is E-W-specific and
stays inside C.127.

| record piece | clause | declaration |
|---|---|---|
| 1 (`red` of a monomial) | (a) | `binomKey_mod_monomial` |
| 2 (the `Φ′`-digits of a reassembly) | (b) | `dev_reass` — **in `C127.lean`**, see below |
| 3 (`stageHeight` of a monomial) | (c) | `stageHeight_C_mul_X_pow` |
| 4 (`gaussVal` of a unit times a `π`-power) | (d) | `gaussVal_C_unit_mul_pow` |
| 5 (`inf`-evaluation over `ℕ∞`) | (e) | `inf_eq_of_attained` |

## Where clause (b) lives, and why it is not in this file

Clause (b) reads `reass`, whose landed carrier is `Uniformity/ChapC/C127.lean`, and its proof
consumes that module's `reass_eq_sum_range` and `dev_eval_eq_coeff`.  Since C.127's `lawEW_pin`
consumes THIS file, a module-level `C129 → C127` import would be a cycle, so `dev_reass` is
landed in `C127.lean` itself, immediately after the reassembly API it reads.  This matches the
blueprint's DAG adjudication (`C.129 → C.71`, "the OBJECT is C.71's … the naive `C.129 → C.127`
would have closed a cycle against `C.127 → C.129`") and the leanspec note that clause (b) has
no leanspec twin deliberately.  Its frame-generic helper `degree_modByMonicHom_lt` needs no
C.127 material and is landed here, where both clause (b) and future consumers can read it.

## Two adjudications carried from the signature

* **(a) is stated ring-generically** (`{R} [CommRing R] [Nontrivial R]`, key `X^D − C w`), not
  at `F.key`: the corpus's binomial keys are `X^{D′} − C(πω)`, the instance at `w = πω`.
  `Nontrivial` is what makes `degree (X^D − C w) = D`; it is free at every consumer (`O` is a
  domain).  The proof is the divisibility
  `X^D − C w ∣ C λ X^N − C(λw^{N/D})X^{N%D}` (through `sub_dvd_pow_sub_pow` after splitting
  `N = D(N/D) + N%D`) plus the degree bound `N % D < D` — the C127 record's guess that this
  "needs an induction on `N / D`" is not so.
* **(c) needs no `λ ≠ 0` side condition**: at `λ = 0` both sides are `⊤`, because
  `F.he₁ : 0 < F.e₁` makes `F.e₁ • (⊤ : ℕ∞) = ⊤`.  The clause is therefore usable without a case
  split at the call site — the shape the pin's slot dictionary wants.  Its proof uses clause
  (e), the internal coherence check of the designed list.

Transcribed from the certification record
`leanfinal/Uniformity/ChapC/C129_CERT.lean.txt` (A-C.3 certify-before-sign standard: all five
clauses were PROVED before the signature was written).

## Status

Sorry-free, Lean-core axioms only (`#print axioms` block at the foot).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.129 (e)** (record piece 5) — attainment for an `ℕ∞`-valued `Finset.inf`: all terms
`≥ M`, one term `= M`.  Absent slots are `⊤` and satisfy the lower bound vacuously, which is
how the slot dictionary uses it. -/
theorem inf_eq_of_attained {ι : Type*} {s : Finset ι} {g : ι → ℕ∞} {M : ℕ∞}
    (hlb : ∀ i ∈ s, M ≤ g i) {i₀ : ι} (hi₀ : i₀ ∈ s) (hat : g i₀ = M) :
    s.inf g = M :=
  le_antisymm (hat ▸ Finset.inf_le hi₀) (Finset.le_inf hlb)

/-- **C.129 (a)** (record piece 1) — the reduction of a MONOMIAL at a binomial key,
`(λx^N) mod (x^D − w) = λw^{⌊N/D⌋}x^{N mod D}`.  Ring-generic: nothing in the proof is frame
data, and the corpus's `X^{D′} − C(πω)` is the instance at `w = π * ω`. -/
theorem binomKey_mod_monomial {R : Type*} [CommRing R] [Nontrivial R] {D : ℕ} (hD : 0 < D)
    (w lam : R) (N : ℕ) :
    (Polynomial.C lam * Polynomial.X ^ N) %ₘ (Polynomial.X ^ D - Polynomial.C w)
      = Polynomial.C (lam * w ^ (N / D)) * Polynomial.X ^ (N % D) := by
  have hmon : (Polynomial.X ^ D - Polynomial.C w).Monic :=
    Polynomial.monic_X_pow_sub_C w (by omega)
  have hdegK : (Polynomial.X ^ D - Polynomial.C w).degree = (D : WithBot ℕ) :=
    Polynomial.degree_X_pow_sub_C hD w
  -- the difference is divisible by the key
  have hdvd : (Polynomial.X ^ D - Polynomial.C w) ∣
      Polynomial.C lam * Polynomial.X ^ N
        - Polynomial.C (lam * w ^ (N / D)) * Polynomial.X ^ (N % D) := by
    have hsplit : N = D * (N / D) + N % D := (Nat.div_add_mod N D).symm
    have hkey : Polynomial.C lam * Polynomial.X ^ N
        - Polynomial.C (lam * w ^ (N / D)) * Polynomial.X ^ (N % D)
        = (Polynomial.C lam * Polynomial.X ^ (N % D))
            * ((Polynomial.X ^ D) ^ (N / D) - (Polynomial.C w) ^ (N / D)) := by
      have hx : (Polynomial.X : Polynomial R) ^ N
          = Polynomial.X ^ (N % D) * (Polynomial.X ^ D) ^ (N / D) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hx, map_mul, map_pow]
      ring
    rw [hkey]
    exact Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _
  have h1 : Polynomial.C lam * Polynomial.X ^ N %ₘ (Polynomial.X ^ D - Polynomial.C w)
      = Polynomial.C (lam * w ^ (N / D)) * Polynomial.X ^ (N % D)
          %ₘ (Polynomial.X ^ D - Polynomial.C w) :=
    Polynomial.modByMonic_eq_of_dvd_sub hmon hdvd
  rw [h1, (Polynomial.modByMonic_eq_self_iff hmon).2]
  rw [hdegK]
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le (N % D) (lam * w ^ (N / D))) ?_
  exact_mod_cast Nat.mod_lt _ hD

/-- Helper for **C.129 (b)**: the canonical representative of a class mod `F.key` is in-grid.
Clause (b) itself (`dev_reass`) is landed in `Uniformity/ChapC/C127.lean`, where `reass` lives
— see this file's header. -/
theorem degree_modByMonicHom_lt (F : KeyFrame O π) (x : AdjoinRoot F.key) :
    (AdjoinRoot.modByMonicHom F.hmonic x).degree < F.key.degree :=
  AdjoinRoot.induction_on _ x fun p => by
    rw [AdjoinRoot.modByMonicHom_mk]; exact degree_modByMonic_lt p F.hmonic

/-- **C.129 (d)** (record piece 4) — `gaussVal` of a unit times a `π`-power.  This is the
clause that consumes the `IsUnit` hypotheses (`hc`, `hc₂`, `hc₀`, `hω`) that C.127's frozen
signature carries and its two landed clauses do not. -/
theorem gaussVal_C_unit_mul_pow (hπ : Irreducible π) {u : O} (hu : IsUnit u) (n : ℕ) :
    gaussVal (Polynomial.C (u * π ^ n)) = (n : ℕ∞) := by
  rw [gaussVal, Polynomial.natDegree_C, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_C_zero, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, addVal_pow_uniformizer hπ, zero_add]

private theorem nsmul_top_of_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr hn.ne']

/-- **C.129 (c)** (record piece 3) — the `stageHeight` of a monomial,
`dv(λx^a) = e₁·v(λ) + h·a`.  NO `λ ≠ 0` side condition: at `λ = 0` both sides are `⊤`, because
`F.he₁` makes `F.e₁ • (⊤ : ℕ∞) = ⊤`. -/
theorem stageHeight_C_mul_X_pow (F : KeyFrame O π) (lam : O) (a : ℕ) :
    F.stageHeight (Polynomial.C lam * Polynomial.X ^ a)
      = F.e₁ • gaussVal (Polynomial.C lam) + ((F.h * a : ℕ) : ℕ∞) := by
  classical
  have hcoeff : ∀ j, (Polynomial.C lam * Polynomial.X ^ a).coeff j
      = if j = a then lam else 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split <;> simp_all
  rcases eq_or_ne lam 0 with rfl | hlam
  · have h0 : (Polynomial.C (0 : O) * Polynomial.X ^ a) = 0 := by simp
    rw [h0, KeyFrame.stageHeight_eq_inf]
    simp only [Polynomial.natDegree_zero, Polynomial.coeff_zero, map_zero]
    rw [show gaussVal (0 : Polynomial O) = ⊤ from gaussVal_eq_top_iff.mpr rfl,
      nsmul_top_of_pos F.he₁]
    simp
  · have hdeg : (Polynomial.C lam * Polynomial.X ^ a).natDegree = a := by
      simp [hlam]
    rw [KeyFrame.stageHeight_eq_inf, hdeg]
    refine inf_eq_of_attained ?_ (Finset.self_mem_range_succ a) ?_
    · intro j hj
      rcases eq_or_ne j a with rfl | hja
      · rw [hcoeff, if_pos rfl, Nat.cast_mul]
      · rw [hcoeff, if_neg hja, map_zero,
          show gaussVal (0 : Polynomial O) = ⊤ from gaussVal_eq_top_iff.mpr rfl,
          nsmul_top_of_pos F.he₁]
        simp
    · rw [hcoeff, if_pos rfl, Nat.cast_mul]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.inf_eq_of_attained
#print axioms Uniformity.Density.Tower.binomKey_mod_monomial
#print axioms Uniformity.Density.Tower.degree_modByMonicHom_lt
#print axioms Uniformity.Density.Tower.gaussVal_C_unit_mul_pow
#print axioms Uniformity.Density.Tower.stageHeight_C_mul_X_pow

end AxCheck
