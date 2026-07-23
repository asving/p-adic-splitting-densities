/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.DevBijection
import LeanUrat.OM.RecenterBox
import LeanUrat.OM.ChainMenuU

/-!
# DescendBijection — Wave W9a: the class-3 descend bijection (J1-step) and the JOINT-D1 tower

**Provenance.** `notes/JOINT_D1_2026-07-23.md` (status: ACCEPTED for the deg-2-key perimeter —
Codex adversarial pass 1 confirmed the one-step machinery and found the tower criticals, rev 2
repaired them, pass 2: 0 critical, 1 threshold gap fixed with the boundary case pre-verified),
§§1–4: **Lemma J1a** (the explicit descend re-development map Θ_ĉ; the four formulas were
machine-checked on 300 random instances over p ∈ {2,3,5}), **Lemma J1b** (staircase inclusion),
**Theorem J1-step** (the descend bijection S_{m,c̃} → B′, level N ≥ 2m+1 — threshold sharpened
at Codex pass 2), and **Theorem JOINT-D1** (deg-2-key descend towers at ABSOLUTE heights, the
restriction-of-a-bijection induction). Empirical pins of the note: Case E (`case_e_gate.py`,
D1-marginal), Case F (`case_f_gate.py`, p = 2, N = 5, exact joint uniformity — the 144-count
tied below), Case F-odd (`case_f_oddp.py`, p = 3, exact joint uniformity at every center).
Formalization task card: `notes/WILD_WAVE9_BLUEPRINT_2026-07-23.md` §W9a.

## The mathematics

φ = x² + sx + t monic quadratic; every monic quartic has the unique development
f = φ² + a₁φ + a₀ with deg aᵢ ≤ 1, coordinates `fourTuple` = ((a₁₁, a₁₀), (a₀₁, a₀₀))
(`OM/DevBijection.lean`, W8a). The child key is φ′ = φ − p^m·ĉ (ĉ = ĉ₁x + ĉ₀ a lift of the
center c̃ ∈ F_Q = F_p[x]/(φ̄)); re-developing the SAME f along φ′ gives (note §1, J1a):

  a₁′₁ = a₁₁ + 2p^mĉ₁
  a₁′₀ = a₁₀ + 2p^mĉ₀ + p^m·ĉ₁a₁₁ + p^{2m}·ĉ₁²
  a₀′₁ = a₀₁ + p^m[ĉ₁a₁₀ + ĉ₀a₁₁ − ĉ₁a₁₁s′] + p^{2m}[2ĉ₁ĉ₀ − ĉ₁²s′]
  a₀′₀ = a₀₀ + p^m[ĉ₀a₁₀ − ĉ₁a₁₁t′] + p^{2m}[ĉ₀² − ĉ₁²t′]      (s′ = s − p^mĉ₁, t′ = t − p^mĉ₀)

This module delivers, purely additively (general prime `p`):

* **A. The map and the box equiv**: `descendMap (s t c₁ c₀ pm : R)` on `fourTuple R` for any
  CommRing `R` (`pm` stands for p^m, keeping every law `ring`-closable); the inverse
  `descendInv` is the SAME map at parameters (s′, t′, −ĉ) — recentering back by −ĉ, which IS
  the closed form of back-substitution (solve a₁₁, then a₁₀, then the a₀-coordinates); Equiv
  laws by `ring`; `descendEquiv p N m s t c₁ c₀ : fourBox p N ≃ fourBox p N` at
  pm := (p : ZMod (p^N))^m.
* **B. The genuine re-development identity** `descend_redevelopment` (+ `_of` hypothesis form,
  + `descend_division_padic` chaining `DevBijection.dev_division` over ℤ_[p]):
  φ² + A₁φ + A₀ = φ′² + A₁′φ′ + A₀′ with the displayed coefficients — `ring` after pushing `C`
  through. Box commutation with any ring hom: `fourMap_descendMap` (once, generically), and
  `descendMap_toZModPow` for `PadicInt.toZModPow`.
* **C. J1-step**: the stratum `DescStratum p N m sb tb c̃` (heights 0..m−1 of both a₁-coords
  zero with height-m digit pair = −2c̃; heights 0..2m−1 of both a₀-coords zero with height-2m
  pair = c̃², the F_Q-square computed by `pairSq`) and the box `DescBox p N m` (divisibility by
  p^{m+1} / p^{2m+1}); the membership iff `descStratum_iff_descBox` (both directions, at the
  ZMod digit level via the `CoordCond`/`digit`/`resp` bridges); **THE THEOREM**
  `descend_bijection : {a // DescStratum …} ≃ {b // DescBox …}` via `Equiv.subtypeEquiv`;
  the equal closed-form cards `card_descStratum` = `card_descBox` = p^{4N−6m−4} (N ≥ 2m+1).
* **D. The tower (JOINT-D1, note §4)**: histories are lists of (ABSOLUTE height M_j, center
  c̃_j) with `List.Chain (· < ·) 0` strict increase (0 < M₁ < ⋯ < M_k — the polygon stays
  anchored at (2,0), heights accumulate absolutely, per the Codex pass-1 repair);
  `JointStratum` = the iterated stratum J_k (each step recenters the level-N key data
  (s,t) ↦ (s − p^{M_j}ĉ_j1, t − p^{M_j}ĉ_j0) and transports by Θ_j); `descendTower_bijection` :
  J_k-subtype ≃ B_k-box by list recursion (each step = J1-step + the T_j ⊆ B_{j−1} inclusion
  `descBox_of_descStratum` + `Equiv.trans`); `joint_count` : #(J_k ∩ Ψ_k⁻¹C) = #C for any leaf
  predicate C ⊆ B_k (`towerMap` = the composite Ψ_k) — the class-3 joint ledger (J-D1).
* **E. Gates**: (i) p = 2, m = 1, N = 3 — stratum and box cards BOTH 4 by kernel `decide`,
  plus the full membership-iff mechanism `decide`d over all 4096 points; (ii) **the Case-F
  tie**: depth-2 history (M₁, M₂) = (1, 2) at p = 2, N = 5 (the BOUNDARY level 2M₂+1 = 5):
  per-center-pair joint count 16 via the tower + closed form, and summed over the 9 center
  pairs (3×3, c̃ ∈ F₄ˣ): 9·16 = **144** = the external Case-F (v₀′ = 4, v₁′ ≥ 3)
  square-residual bucket count (note §4 consistency check (i): 3072·(3/64) = 144); (iii)
  p = 3 gates at the center c̃ = x̄+1 over F₉ = F₃[x]/(x²+1): the `pairSq` value (2,0) by
  `decide`, the two digit atoms (counts 3 and 1 in ZMod 27) by `decide`, the stratum closed
  form 9.

## Residual-multiplication convention (FLAGGED)

The height-2m center equation lives in F_Q = F_p[x]/(x² + s̄x + t̄); its multiplication is
formalized as the pair product `pairMul s t u w = (u₁w₀ + u₀w₁ − u₁w₁s, u₀w₀ − u₁w₁t)` in the
**(linear, constant)** coordinate order matching `fourTuple`'s descending-degree pairs — this
is exactly the note §1 single-division step u·w = (u₁w₁)·φ′ + [remainder pair], proved as the
polynomial identity `linPair_mul_linPair`. **`ChainMenuU.squareUnitPairs` is DIFFERENT**: it is
the deg-1 residue-field (F_p) pool, in (constant, linear) order, with no (s,t)-dependence — it
cannot be consumed directly at deg-2 keys. The overlap is PROVED, not remarked: for a scalar
center c̃ = (0, c₀) ∈ F_p ⊆ F_Q the linear component of c̃² vanishes (`pairSq_scalar_fst`) and
the constant components (c₀², −2c₀) are literally a `squareUnitPairs` element
(`pairSq_scalar_mem_squareUnitPairs`).

## HONEST SCOPE (read before consuming)

This module is **COUNTING ONLY**: bijections and cardinalities of digit-condition sets over
`ZMod (p^N)`. It makes **NO type/leaf/faithfulness claim** — that the strata correspond to
classifier reads/types (keying, leaf masters, menu re-scope) is a LATER wave with its own
axiom re-scope and semantic-guardian audit. The deg-d ≥ 3 key analogue (J1-general-d), the
order-r ≥ 2 reads, and D3/D5 remain OPEN (note §5) and must not be cited from here.

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck` at bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.DescendBijection

open Polynomial
open LeanUrat.OM LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox LeanUrat.OM.RestartEquiv
open LeanUrat.OM.ChainMenu LeanUrat.OM.ChainMenuU
open LeanUrat.OM.DevBijection

/-! ## 1. The descend map over a general commutative ring (Lemma J1a, the four formulas)

Coordinates are `DevBijection.fourTuple` = ((a₁₁, a₁₀), (a₀₁, a₀₀)), descending degree within
each pair. `pm` stands for p^m; the maps are affine over ℤ[s,t,ĉ₁,ĉ₀,pm] with
lower-unitriangular linear part, so all laws are `ring` identities. -/

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The descend re-development map Θ_ĉ** (note §1, Lemma J1a): the φ′-development
coordinates of f in terms of its φ-development coordinates, at φ′ = φ − p^m·ĉ. The internal
s′ = s − pm·ĉ₁ and t′ = t − pm·ĉ₀ are inlined. -/
def descendMap (s t c₁ c₀ pm : R) (a : fourTuple R) : fourTuple R :=
  ((a.1.1 + 2 * pm * c₁,
    a.1.2 + 2 * pm * c₀ + pm * c₁ * a.1.1 + pm ^ 2 * c₁ ^ 2),
   (a.2.1 + pm * (c₁ * a.1.2 + c₀ * a.1.1 - c₁ * a.1.1 * (s - pm * c₁))
      + pm ^ 2 * (2 * c₁ * c₀ - c₁ ^ 2 * (s - pm * c₁)),
    a.2.2 + pm * (c₀ * a.1.2 - c₁ * a.1.1 * (t - pm * c₀))
      + pm ^ 2 * (c₀ ^ 2 - c₁ ^ 2 * (t - pm * c₀))))

/-- **The inverse: recenter back by −ĉ.** φ = φ′ − p^m·(−ĉ), so the inverse of Θ_ĉ (at key
data (s,t)) is Θ_{−ĉ} at the CHILD key data (s′, t′) — the closed form of back-substitution
(solve a₁₁ from the first line, then a₁₀, then the a₀-coordinates). -/
def descendInv (s t c₁ c₀ pm : R) (a : fourTuple R) : fourTuple R :=
  descendMap (s - pm * c₁) (t - pm * c₀) (-c₁) (-c₀) pm a

/-- Back-substitution recovers the original coordinates (`ring`, coordinatewise). -/
theorem descendInv_descendMap (s t c₁ c₀ pm : R) (a : fourTuple R) :
    descendInv s t c₁ c₀ pm (descendMap s t c₁ c₀ pm a) = a := by
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  simp only [descendMap, descendInv, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- Θ_ĉ of the back-substitution is the identity (`ring`, coordinatewise). -/
theorem descendMap_descendInv (s t c₁ c₀ pm : R) (a : fourTuple R) :
    descendMap s t c₁ c₀ pm (descendInv s t c₁ c₀ pm a) = a := by
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  simp only [descendMap, descendInv, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- **Θ_ĉ commutes with every ring hom** (the formulas are ℤ[s,t,ĉ₁,ĉ₀,pm]-polynomial) — the
generic form of the box commutation, proved ONCE (the DevBijection §C pattern). -/
theorem fourMap_descendMap (g : R →+* S) (s t c₁ c₀ pm : R) (a : fourTuple R) :
    fourMap g (descendMap s t c₁ c₀ pm a)
      = descendMap (g s) (g t) (g c₁) (g c₀) (g pm) (fourMap g a) := by
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  simp only [descendMap, fourMap, map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- **The residual pair product** (the note §1 single-division step, coefficient form): for
deg-≤1 residues u = u₁x + u₀, w = w₁x + w₀ read against the key x² + sx + t,
u·w = (u₁w₁)·key + remainder, and `pairMul` is that remainder's (linear, constant) pair.
This is the F_Q-multiplication of the J1b residue computation (F_Q = F_p[x]/(x² + s̄x + t̄)),
in the `fourTuple` descending-degree pair convention. -/
def pairMul (s t : R) (u w : R × R) : R × R :=
  (u.1 * w.2 + u.2 * w.1 - u.1 * w.1 * s, u.2 * w.2 - u.1 * w.1 * t)

/-- **The residual square** c̃² in F_Q, explicit: (2c̃₁c̃₀ − c̃₁²s, c̃₀² − c̃₁²t). -/
def pairSq (s t : R) (c : R × R) : R × R :=
  (2 * c.1 * c.2 - c.1 ^ 2 * s, c.2 ^ 2 - c.1 ^ 2 * t)

theorem pairSq_eq_pairMul (s t : R) (c : R × R) : pairSq s t c = pairMul s t c c := by
  refine Prod.ext ?_ ?_ <;> simp only [pairSq, pairMul] <;> ring

/-- The linear component of a SCALAR center's square vanishes: c̃ = (0, c₀) ∈ F_p ⊆ F_Q has
c̃² = (0, c₀²) — the overlap leg of the `squareUnitPairs` convention tie. -/
theorem pairSq_scalar_fst (s t c₀ : R) : (pairSq s t (0, c₀)).1 = 0 := by
  simp only [pairSq]
  ring

theorem pairSq_scalar_snd (s t c₀ : R) : (pairSq s t (0, c₀)).2 = c₀ ^ 2 := by
  simp only [pairSq]
  ring

end Ring

/-! ## 2. The box equiv (deliverable A) and the box commutation -/

section Box

variable (p : ℕ) [hp : Fact p.Prime]

/-- **THE DESCEND BOX EQUIV** (Lemma J1a's bijectivity): at every level `N`, Θ_ĉ at
pm := (p : ZMod (p^N))^m is a bijection of the coefficient box — affine unitriangular,
explicit inverse by recentering back. -/
def descendEquiv (N m : ℕ) (s t c₁ c₀ : ZMod (p ^ N)) : fourBox p N ≃ fourBox p N where
  toFun := descendMap s t c₁ c₀ ((p : ZMod (p ^ N)) ^ m)
  invFun := descendInv s t c₁ c₀ ((p : ZMod (p ^ N)) ^ m)
  left_inv := descendInv_descendMap s t c₁ c₀ _
  right_inv := descendMap_descendInv s t c₁ c₀ _

theorem descendEquiv_apply (N m : ℕ) (s t c₁ c₀ : ZMod (p ^ N)) (a : fourBox p N) :
    descendEquiv p N m s t c₁ c₀ a = descendMap s t c₁ c₀ ((p : ZMod (p ^ N)) ^ m) a := rfl

theorem descendEquiv_symm_apply (N m : ℕ) (s t c₁ c₀ : ZMod (p ^ N)) (a : fourBox p N) :
    (descendEquiv p N m s t c₁ c₀).symm a
      = descendInv s t c₁ c₀ ((p : ZMod (p ^ N)) ^ m) a := rfl

/-- **Box commutation with `toZModPow`** (deliverable B leg): reducing the genuine ℤ_[p]-level
re-developed coordinates mod p^N = `descendEquiv` applied to the reduced coordinates. -/
theorem descendMap_toZModPow (N m : ℕ) (s t c₁ c₀ : ℤ_[p]) (a : fourTuple ℤ_[p]) :
    fourMap (PadicInt.toZModPow N) (descendMap s t c₁ c₀ ((p : ℤ_[p]) ^ m) a)
      = descendEquiv p N m (PadicInt.toZModPow N s) (PadicInt.toZModPow N t)
          (PadicInt.toZModPow N c₁) (PadicInt.toZModPow N c₀)
          (fourMap (PadicInt.toZModPow N) a) := by
  have h := fourMap_descendMap (PadicInt.toZModPow (p := p) N) s t c₁ c₀ ((p : ℤ_[p]) ^ m) a
  rw [map_pow, map_natCast] at h
  exact h

end Box

/-! ## 3. The genuine re-development identity (deliverable B) -/

noncomputable section Poly

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The single-division step as a POLYNOMIAL identity (the note §1 display):
`linPair u * linPair w = C(u₁w₁)·key + linPair (pairMul s t u w)` — the residual pair product
IS multiplication modulo the monic key. -/
theorem linPair_mul_linPair (s t : R) (u w : R × R) :
    linPair u * linPair w
      = C (u.1 * w.1) * keyPoly s t + linPair (pairMul s t u w) := by
  simp only [linPair, keyPoly, pairMul, map_add, map_sub, map_mul]
  ring

/-- **THE GENUINE RE-DEVELOPMENT IDENTITY (Lemma J1a's content)**: over ANY commutative ring,
φ² + A₁·φ + A₀ = φ′² + A₁′·φ′ + A₀′ with φ′ = key(s − pm·c₁, t − pm·c₀) and (A₁′, A₀′) the
`descendMap` linear forms — expand and `ring`. -/
theorem descend_redevelopment (s t c₁ c₀ pm : R) (a : fourTuple R) :
    keyPoly s t ^ 2 + linPair a.1 * keyPoly s t + linPair a.2
      = keyPoly (s - pm * c₁) (t - pm * c₀) ^ 2
        + linPair (descendMap s t c₁ c₀ pm a).1 * keyPoly (s - pm * c₁) (t - pm * c₀)
        + linPair (descendMap s t c₁ c₀ pm a).2 := by
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  simp only [descendMap, keyPoly, linPair, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The hypothesis-consuming form (the task-card statement): GIVEN f = φ² + A₁φ + A₀,
f = φ′² + A₁′φ′ + A₀′ with the displayed coefficients. -/
theorem descend_redevelopment_of {f : R[X]} (s t c₁ c₀ pm : R) (a : fourTuple R)
    (hf : f = keyPoly s t ^ 2 + linPair a.1 * keyPoly s t + linPair a.2) :
    f = keyPoly (s - pm * c₁) (t - pm * c₀) ^ 2
        + linPair (descendMap s t c₁ c₀ pm a).1 * keyPoly (s - pm * c₁) (t - pm * c₀)
        + linPair (descendMap s t c₁ c₀ pm a).2 :=
  hf.trans (descend_redevelopment s t c₁ c₀ pm a)

/-- **The full ℤ_[p] chain (deliverable B)**: for a monic quartic with coefficient tuple `c`,
its φ-development (`DevBijection.dev_division`) re-develops along φ′ = φ − p^m·ĉ with the four
J1a coefficient formulas. -/
theorem descend_division_padic (p : ℕ) [Fact p.Prime] (m : ℕ) (s t c₁ c₀ : ℤ_[p])
    (c : fourTuple ℤ_[p]) :
    quartic c
      = keyPoly (s - (p : ℤ_[p]) ^ m * c₁) (t - (p : ℤ_[p]) ^ m * c₀) ^ 2
        + linPair (descendMap s t c₁ c₀ ((p : ℤ_[p]) ^ m) (devMap s t c)).1
            * keyPoly (s - (p : ℤ_[p]) ^ m * c₁) (t - (p : ℤ_[p]) ^ m * c₀)
        + linPair (descendMap s t c₁ c₀ ((p : ℤ_[p]) ^ m) (devMap s t c)).2 :=
  descend_redevelopment_of s t c₁ c₀ ((p : ℤ_[p]) ^ m) (devMap s t c) (dev_division s t c)

end Poly

/-! ## 4. Digit bridges (the `CoordCond`/`resp` workhorses for J1b) -/

section Bridges

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The coordinate-condition bridge**: divisibility + pinned digit at height `k` is exactly
"a π^k-multiple with prescribed residue" (π = (p : ZMod (p^N))). Built on the banked
`RestartEquiv.pow_dvd_iff_dvd_val` and `digit_pow_mul`. -/
theorem coordCond_iff_exists {N k : ℕ} (hk : k < N) (d : ZMod p) (x : ZMod (p ^ N)) :
    CoordCond p N k d x
      ↔ ∃ u : ZMod (p ^ N), x = (p : ZMod (p ^ N)) ^ k * u ∧ resp p N u = d := by
  constructor
  · rintro ⟨hdvd, hdig⟩
    obtain ⟨u, hu⟩ := (pow_dvd_iff_dvd_val p N hk.le x).mpr hdvd
    refine ⟨u, hu, ?_⟩
    rw [← digit_pow_mul p N hk u, ← hu]
    exact hdig
  · rintro ⟨u, rfl, hu⟩
    exact ⟨(pow_dvd_iff_dvd_val p N hk.le _).mp ⟨u, rfl⟩,
      by rw [digit_pow_mul p N hk u]; exact hu⟩

/-- **The box-condition bridge**: divisibility by p^{k+1} is exactly "a π^k-multiple with
VANISHING residue". -/
theorem dvd_succ_iff_exists {N k : ℕ} (hk : k < N) (x : ZMod (p ^ N)) :
    p ^ (k + 1) ∣ x.val
      ↔ ∃ u : ZMod (p ^ N), x = (p : ZMod (p ^ N)) ^ k * u ∧ resp p N u = 0 := by
  have hN0 : 0 < N := by omega
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (pow_dvd_iff_dvd_val p N (by omega : k + 1 ≤ N) x).mpr h
    refine ⟨(p : ZMod (p ^ N)) * w, by rw [hw]; ring, ?_⟩
    rw [resp_mul p N hN0, resp_p p N hN0, zero_mul]
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨w, hw⟩ := (resp_eq_zero_iff p N hN0 u).mp hu
    rw [hw, ← pow_dvd_iff_dvd_val p N (by omega : k + 1 ≤ N)]
    exact ⟨w, by ring⟩

/-- The canonical residue lift `ZMod p → ZMod (p^N)` (any fixed lift works for the descend
machinery; this is the one the tower uses). -/
def liftp (N : ℕ) (c : ZMod p) : ZMod (p ^ N) := ((c.val : ℕ) : ZMod (p ^ N))

theorem resp_liftp (N : ℕ) (hN : 0 < N) (c : ZMod p) : resp p N (liftp p N c) = c := by
  rw [liftp, resp_natCast p N hN]
  exact ZMod.natCast_rightInverse c

/-- The scalar-center overlap with the deg-1 pool: for c̃ = (0, c) with c ∈ F_pˣ, the CONSTANT
components of the descend residual data (c̃²-pair, −2c̃-pair) form literally a
`ChainMenuU.squareUnitPairs` element ((constant, linear) order there). This ties the two
residual-multiplication conventions on their overlap — see the module docstring FLAG. -/
theorem pairSq_scalar_mem_squareUnitPairs (sb tb : ZMod p) (c : (ZMod p)ˣ) :
    ((pairSq sb tb ((0 : ZMod p), (c : ZMod p))).2, -(2 * (c : ZMod p)))
      ∈ squareUnitPairs p := by
  rw [mem_squareUnitPairs]
  exact ⟨c, by rw [pairSq_scalar_snd], rfl⟩

end Bridges

/-! ## 5. J1-step: the stratum, the box, the membership iff, THE BIJECTION (deliverable C) -/

section Step

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The descend stratum S_{m,c̃}** (note §0) at level `N`, slope `m`, residue-level key data
`(sb, tb)` (the mod-p digits of (s,t)) and center `ct` = (c̃₁, c̃₀) ∈ F_Q in (linear, constant)
order: both a₁-coordinates have heights 0..m−1 zero with height-m digit pair = −2c̃, both
a₀-coordinates have heights 0..2m−1 zero with height-2m digit pair = c̃² (the `pairSq` F_Q
square). Grouped ((a₁-pair) ∧ (a₀-pair)) for the product-count route. -/
def DescStratum (N m : ℕ) (sb tb : ZMod p) (ct : ZMod p × ZMod p) (a : fourBox p N) : Prop :=
  (CoordCond p N m (-(2 * ct.1)) a.1.1 ∧ CoordCond p N m (-(2 * ct.2)) a.1.2)
    ∧ (CoordCond p N (2 * m) ((pairSq sb tb ct).1) a.2.1
        ∧ CoordCond p N (2 * m) ((pairSq sb tb ct).2) a.2.2)

instance instDecidableDescStratum (N m : ℕ) (sb tb : ZMod p) (ct : ZMod p × ZMod p) :
    DecidablePred (DescStratum p N m sb tb ct) := fun _ => by
  unfold DescStratum; infer_instance

/-- **The child cluster box B′** (note §3): v(a₁) ≥ m+1 and v(a₀) ≥ 2m+1, coordinatewise. -/
def DescBox (N m : ℕ) (b : fourBox p N) : Prop :=
  (p ^ (m + 1) ∣ b.1.1.val ∧ p ^ (m + 1) ∣ b.1.2.val)
    ∧ (p ^ (2 * m + 1) ∣ b.2.1.val ∧ p ^ (2 * m + 1) ∣ b.2.2.val)

instance instDecidableDescBox (N m : ℕ) : DecidablePred (DescBox p N m) := fun _ => by
  unfold DescBox; infer_instance

/-- **The J1b membership iff (the J1-step core)**: a lies in the descend stratum at center c̃
iff Θ_ĉ(a) lies in the child cluster box — both directions, at every level N ≥ 2m+1 (the
Codex-pass-2 sharpened threshold; the boundary N = 2m+1 is exercised by gate (ii)). Stated for
any level-N key data (s, t) and any lifts (c₁, c₀) of the center. -/
theorem descStratum_iff_descBox (N m : ℕ) (hm : 1 ≤ m) (hN : 2 * m + 1 ≤ N)
    (s t c₁ c₀ : ZMod (p ^ N)) {sb tb : ZMod p} {ct : ZMod p × ZMod p}
    (hs : resp p N s = sb) (ht : resp p N t = tb)
    (hc : (resp p N c₁, resp p N c₀) = ct) (a : fourBox p N) :
    DescStratum p N m sb tb ct a
      ↔ DescBox p N m (descendMap s t c₁ c₀ ((p : ZMod (p ^ N)) ^ m) a) := by
  subst hs ht hc
  obtain ⟨⟨a₁₁, a₁₀⟩, a₀₁, a₀₀⟩ := a
  have hN0 : 0 < N := by omega
  have hm0 : m ≠ 0 := by omega
  have hkm : m < N := by omega
  have hk2m : 2 * m < N := by omega
  constructor
  · rintro ⟨⟨h11, h10⟩, h01, h00⟩
    rw [coordCond_iff_exists p hkm] at h11 h10
    rw [coordCond_iff_exists p hk2m] at h01 h00
    obtain ⟨u₁₁, rfl, hr11⟩ := h11
    obtain ⟨u₁₀, rfl, hr10⟩ := h10
    obtain ⟨u₀₁, rfl, hr01⟩ := h01
    obtain ⟨u₀₀, rfl, hr00⟩ := h00
    simp only [pairSq] at hr01 hr00
    simp only [descendMap, DescBox]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · refine (dvd_succ_iff_exists p hkm _).mpr ⟨u₁₁ + 2 * c₁, by ring, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr11 ⊢
      simp only [map_add, map_mul, map_ofNat]
      rw [hr11]
      ring
    · refine (dvd_succ_iff_exists p hkm _).mpr
        ⟨u₁₀ + 2 * c₀ + (p : ZMod (p ^ N)) ^ m * (c₁ * u₁₁ + c₁ ^ 2), by ring, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr10 ⊢
      simp only [map_add, map_mul, map_pow, map_ofNat, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, add_zero]
      rw [hr10]
      ring
    · refine (dvd_succ_iff_exists p hk2m _).mpr
        ⟨u₀₁ + c₁ * u₁₀ + c₀ * u₁₁ - c₁ * u₁₁ * s + 2 * c₁ * c₀ - c₁ ^ 2 * s
            + (p : ZMod (p ^ N)) ^ m * (c₁ ^ 2 * u₁₁ + c₁ ^ 3), by ring, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr01 hr10 hr11 ⊢
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, add_zero]
      rw [hr01, hr10, hr11]
      ring
    · refine (dvd_succ_iff_exists p hk2m _).mpr
        ⟨u₀₀ + c₀ * u₁₀ - c₁ * u₁₁ * t + c₀ ^ 2 - c₁ ^ 2 * t
            + (p : ZMod (p ^ N)) ^ m * (c₁ * c₀ * u₁₁ + c₁ ^ 2 * c₀), by ring, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr00 hr10 hr11 ⊢
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, add_zero]
      rw [hr00, hr10, hr11]
      ring
  · intro hbox
    simp only [descendMap, DescBox] at hbox
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbox
    rw [dvd_succ_iff_exists p hkm] at h1 h2
    rw [dvd_succ_iff_exists p hk2m] at h3 h4
    obtain ⟨v₁₁, hv11, hr11⟩ := h1
    obtain ⟨v₁₀, hv10, hr10⟩ := h2
    obtain ⟨v₀₁, hv01, hr01⟩ := h3
    obtain ⟨v₀₀, hv00, hr00⟩ := h4
    have ha11 : a₁₁ = (p : ZMod (p ^ N)) ^ m * (v₁₁ - 2 * c₁) := by
      linear_combination hv11
    subst ha11
    have ha10 : a₁₀ = (p : ZMod (p ^ N)) ^ m
        * (v₁₀ - 2 * c₀ - (p : ZMod (p ^ N)) ^ m * (c₁ * (v₁₁ - 2 * c₁) + c₁ ^ 2)) := by
      linear_combination hv10
    subst ha10
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · refine (coordCond_iff_exists p hkm _ _).mpr ⟨v₁₁ - 2 * c₁, rfl, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr11 ⊢
      simp only [map_sub, map_mul, map_ofNat]
      rw [hr11]
      ring
    · refine (coordCond_iff_exists p hkm _ _).mpr
        ⟨v₁₀ - 2 * c₀ - (p : ZMod (p ^ N)) ^ m * (c₁ * (v₁₁ - 2 * c₁) + c₁ ^ 2), rfl, ?_⟩
      simp only [resp_eq_castHom p N hN0] at hr10 ⊢
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, sub_zero]
      rw [hr10]
      ring
    · refine (coordCond_iff_exists p hk2m _ _).mpr
        ⟨v₀₁ - (c₁ * (v₁₀ - 2 * c₀ - (p : ZMod (p ^ N)) ^ m * (c₁ * (v₁₁ - 2 * c₁) + c₁ ^ 2))
              + c₀ * (v₁₁ - 2 * c₁)
              - c₁ * (v₁₁ - 2 * c₁) * (s - (p : ZMod (p ^ N)) ^ m * c₁))
            - (2 * c₁ * c₀ - c₁ ^ 2 * (s - (p : ZMod (p ^ N)) ^ m * c₁)),
          by linear_combination hv01, ?_⟩
      simp only [pairSq]
      simp only [resp_eq_castHom p N hN0] at hr01 hr10 hr11 ⊢
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, sub_zero]
      rw [hr01, hr10, hr11]
      ring
    · refine (coordCond_iff_exists p hk2m _ _).mpr
        ⟨v₀₀ - (c₀ * (v₁₀ - 2 * c₀ - (p : ZMod (p ^ N)) ^ m * (c₁ * (v₁₁ - 2 * c₁) + c₁ ^ 2))
              - c₁ * (v₁₁ - 2 * c₁) * (t - (p : ZMod (p ^ N)) ^ m * c₀))
            - (c₀ ^ 2 - c₁ ^ 2 * (t - (p : ZMod (p ^ N)) ^ m * c₀)),
          by linear_combination hv00, ?_⟩
      simp only [pairSq]
      simp only [resp_eq_castHom p N hN0] at hr00 hr10 hr11 ⊢
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
        ZMod.natCast_self, zero_pow hm0, zero_mul, sub_zero]
      rw [hr00, hr10, hr11]
      ring

/-- **THE DESCEND BIJECTION (Theorem J1-step, note §3)**: Θ_ĉ restricts to a bijection
S_{m,c̃} → B′ at every level N ≥ 2m+1, as a subtype equiv (the form the tower consumes). -/
def descend_bijection (N m : ℕ) (hm : 1 ≤ m) (hN : 2 * m + 1 ≤ N)
    (s t c₁ c₀ : ZMod (p ^ N)) {sb tb : ZMod p} {ct : ZMod p × ZMod p}
    (hs : resp p N s = sb) (ht : resp p N t = tb)
    (hc : (resp p N c₁, resp p N c₀) = ct) :
    {a : fourBox p N // DescStratum p N m sb tb ct a}
      ≃ {b : fourBox p N // DescBox p N m b} :=
  Equiv.subtypeEquiv (descendEquiv p N m s t c₁ c₀)
    (fun a => descStratum_iff_descBox p N m hm hN s t c₁ c₀ hs ht hc a)

/-! ### Cardinalities (equal closed forms, N ≥ 2m+1) -/

/-- One-coordinate stratum atom: `#{x : CoordCond k d} = p^{N−k−1}` (the banked
`ChainMenu.card_dvd_digit_eq` in `CoordCond` dress). -/
theorem card_coordCond {N k : ℕ} (hk : k < N) (d : ZMod p) :
    Nat.card {x : ZMod (p ^ N) // CoordCond p N k d x} = p ^ (N - k - 1) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun x => (Iff.rfl : CoordCond p N k d x ↔ p ^ k ∣ x.val ∧ digit p N k x = d)))]
  exact card_dvd_digit_eq p hk d

/-- Pair-of-coordinates stratum atom. -/
theorem card_coordCond_pair {N k : ℕ} (hk : k < N) (d₁ d₂ : ZMod p) :
    Nat.card {u : ZMod (p ^ N) × ZMod (p ^ N) //
        CoordCond p N k d₁ u.1 ∧ CoordCond p N k d₂ u.2}
      = p ^ (N - k - 1) * p ^ (N - k - 1) := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := CoordCond p N k d₁) (q := CoordCond p N k d₂)),
    Nat.card_prod, card_coordCond p hk d₁, card_coordCond p hk d₂]

/-- Pair-of-coordinates divisibility atom. -/
theorem card_dvd_pair {N k : ℕ} (hk : k ≤ N) :
    Nat.card {u : ZMod (p ^ N) × ZMod (p ^ N) // p ^ k ∣ u.1.val ∧ p ^ k ∣ u.2.val}
      = p ^ (N - k) * p ^ (N - k) := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun x : ZMod (p ^ N) => p ^ k ∣ x.val) (q := fun x : ZMod (p ^ N) => p ^ k ∣ x.val)),
    Nat.card_prod, card_dvd_subtype p hk]

/-- **The stratum count**: `#S_{m,c̃} = p^{4N−6m−4}` — heights 0..m of both a₁-coords and
0..2m of both a₀-coords pinned, the rest free (note §3's count). -/
theorem card_descStratum (N m : ℕ) (hN : 2 * m + 1 ≤ N) (sb tb : ZMod p)
    (ct : ZMod p × ZMod p) :
    Nat.card {a : fourBox p N // DescStratum p N m sb tb ct a}
      = p ^ (4 * N - 6 * m - 4) := by
  have hkm : m < N := by omega
  have hk2m : 2 * m < N := by omega
  unfold DescStratum
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun u : ZMod (p ^ N) × ZMod (p ^ N) =>
        CoordCond p N m (-(2 * ct.1)) u.1 ∧ CoordCond p N m (-(2 * ct.2)) u.2)
      (q := fun v : ZMod (p ^ N) × ZMod (p ^ N) =>
        CoordCond p N (2 * m) ((pairSq sb tb ct).1) v.1
          ∧ CoordCond p N (2 * m) ((pairSq sb tb ct).2) v.2)),
    Nat.card_prod, card_coordCond_pair p hkm, card_coordCond_pair p hk2m,
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **The box count**: `#B′ = p^{4N−6m−4}` — the SAME closed form (heights 0..m of a₁ and
0..2m of a₀ pinned to zero). -/
theorem card_descBox (N m : ℕ) (hN : 2 * m + 1 ≤ N) :
    Nat.card {b : fourBox p N // DescBox p N m b} = p ^ (4 * N - 6 * m - 4) := by
  unfold DescBox
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun u : ZMod (p ^ N) × ZMod (p ^ N) =>
        p ^ (m + 1) ∣ u.1.val ∧ p ^ (m + 1) ∣ u.2.val)
      (q := fun v : ZMod (p ^ N) × ZMod (p ^ N) =>
        p ^ (2 * m + 1) ∣ v.1.val ∧ p ^ (2 * m + 1) ∣ v.2.val)),
    Nat.card_prod, card_dvd_pair p (by omega : m + 1 ≤ N),
    card_dvd_pair p (by omega : 2 * m + 1 ≤ N), ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- Stratum and box are equinumerous (the count leg of J1-step, now a corollary of the
bijection route — stated for audit). -/
theorem card_descStratum_eq_card_descBox (N m : ℕ) (hN : 2 * m + 1 ≤ N) (sb tb : ZMod p)
    (ct : ZMod p × ZMod p) :
    Nat.card {a : fourBox p N // DescStratum p N m sb tb ct a}
      = Nat.card {b : fourBox p N // DescBox p N m b} := by
  rw [card_descStratum p N m hN sb tb ct, card_descBox p N m hN]

end Step

/-! ## 6. The tower (Theorem JOINT-D1, note §4; deliverable D)

A history is a `List (ℕ × (ZMod p × ZMod p))` of (ABSOLUTE height M_j, center c̃_j), strictly
increasing from 0 (`List.Chain (· < ·) 0` on the heights). Each step recenters the level-N key
data and transports by Θ_j; `JointStratum` is J_k in root coordinates, `towerMap` is the
composite Ψ_k. -/

section Tower

variable (p : ℕ) [hp : Fact p.Prime]

/-- The final (deepest) absolute height of a history, seeded by the previous height. -/
def lastHeight {α : Type*} : ℕ → List (ℕ × α) → ℕ
  | M₀, [] => M₀
  | _, h :: rest => lastHeight h.1 rest

theorem le_lastHeight {α : Type*} :
    ∀ (l : List (ℕ × α)) (M₀ : ℕ), List.IsChain (· < ·) (M₀ :: l.map Prod.fst) →
      M₀ ≤ lastHeight M₀ l
  | [], _, _ => le_rfl
  | h :: l, _M₀, hchain =>
      le_of_lt (lt_of_lt_of_le (List.isChain_cons_cons.mp hchain).1
        (le_lastHeight l h.1 (List.isChain_cons_cons.mp hchain).2))

/-- **The joint descend stratum J_k** (note §4), in the coordinates of the CURRENT key: the
head reads the descend stratum at its absolute height with the current key's residue data,
and the tail recurses through Θ (with the key data recentered by p^{M}·ĉ). -/
def JointStratum (N : ℕ) :
    ZMod (p ^ N) → ZMod (p ^ N) → List (ℕ × (ZMod p × ZMod p)) → fourBox p N → Prop
  | _, _, [], _ => True
  | s, t, h :: rest, a =>
      DescStratum p N h.1 (resp p N s) (resp p N t) h.2 a
        ∧ JointStratum N (s - (p : ZMod (p ^ N)) ^ h.1 * liftp p N h.2.1)
            (t - (p : ZMod (p ^ N)) ^ h.1 * liftp p N h.2.2) rest
            (descendMap s t (liftp p N h.2.1) (liftp p N h.2.2)
              ((p : ZMod (p ^ N)) ^ h.1) a)

/-- **The composite coordinate map Ψ_k** (note §4): the composition Θ_k ∘ ⋯ ∘ Θ₁ along the
history, with the same key-data recentering as `JointStratum`. -/
def towerMap (N : ℕ) :
    ZMod (p ^ N) → ZMod (p ^ N) → List (ℕ × (ZMod p × ZMod p)) → fourBox p N → fourBox p N
  | _, _, [], a => a
  | s, t, h :: rest, a =>
      towerMap N (s - (p : ZMod (p ^ N)) ^ h.1 * liftp p N h.2.1)
        (t - (p : ZMod (p ^ N)) ^ h.1 * liftp p N h.2.2) rest
        (descendMap s t (liftp p N h.2.1) (liftp p N h.2.2) ((p : ZMod (p ^ N)) ^ h.1) a)

/-- **The staircase inclusion T ⊆ B (note §4)**: a descend stratum at height m′ > m sits
inside the height-m child box (v(a₁) ≥ m′ ≥ m+1, v(a₀) ≥ 2m′ ≥ 2m+1). -/
theorem descBox_of_descStratum {N m m' : ℕ} (h : m + 1 ≤ m') {sb tb : ZMod p}
    {ct : ZMod p × ZMod p} {b : fourBox p N} (hb : DescStratum p N m' sb tb ct b) :
    DescBox p N m b := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hb
  exact ⟨⟨dvd_trans (pow_dvd_pow p h) h1.1, dvd_trans (pow_dvd_pow p h) h2.1⟩,
    dvd_trans (pow_dvd_pow p (by omega : 2 * m + 1 ≤ 2 * m')) h3.1,
    dvd_trans (pow_dvd_pow p (by omega : 2 * m + 1 ≤ 2 * m')) h4.1⟩

/-- **THE TOWER BIJECTION (Theorem JOINT-D1, note §4)**: for a nonempty strictly increasing
history ((M, c̃) :: rest) at level N ≥ 2M_k + 1, Ψ restricts to a bijection from the joint
stratum onto the FINAL box B_k — by list recursion: each step is J1-step + the T ⊆ B inclusion
+ the restriction of an equiv to the preimage of a sub-predicate (`Equiv.subtypeEquiv`). -/
def descendTower_bijection (N : ℕ) :
    (rest : List (ℕ × (ZMod p × ZMod p))) → (M : ℕ) → (ct : ZMod p × ZMod p) →
      (s t : ZMod (p ^ N)) → 1 ≤ M → List.IsChain (· < ·) (M :: rest.map Prod.fst) →
      2 * lastHeight M rest + 1 ≤ N →
      ({a : fourBox p N // JointStratum p N s t ((M, ct) :: rest) a}
        ≃ {b : fourBox p N // DescBox p N (lastHeight M rest) b})
  | [], M, ct, s, t, hm, _, hN =>
      (Equiv.subtypeEquivRight (fun a =>
        ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩)).trans
        (descend_bijection p N M hm hN s t (liftp p N ct.1) (liftp p N ct.2) rfl rfl
          (by rw [resp_liftp p N (by omega) ct.1, resp_liftp p N (by omega) ct.2]))
  | (M₂, ct₂) :: rest', M, ct, s, t, hm, hchain, hN =>
      have hlt : M < M₂ := (List.isChain_cons_cons.mp hchain).1
      have hchain₂ : List.IsChain (· < ·) (M₂ :: rest'.map Prod.fst) :=
        (List.isChain_cons_cons.mp hchain).2
      have hle : M₂ ≤ lastHeight M₂ rest' := le_lastHeight rest' M₂ hchain₂
      have hlast : lastHeight M ((M₂, ct₂) :: rest') = lastHeight M₂ rest' := rfl
      have hNM : 2 * M + 1 ≤ N := by omega
      ((Equiv.subtypeEquiv (descendEquiv p N M s t (liftp p N ct.1) (liftp p N ct.2))
          (q := fun b : fourBox p N => DescBox p N M b
            ∧ JointStratum p N (s - (p : ZMod (p ^ N)) ^ M * liftp p N ct.1)
                (t - (p : ZMod (p ^ N)) ^ M * liftp p N ct.2) ((M₂, ct₂) :: rest') b)
          (fun a => and_congr
            (descStratum_iff_descBox p N M hm hNM s t (liftp p N ct.1) (liftp p N ct.2)
              rfl rfl
              (by rw [resp_liftp p N (by omega) ct.1, resp_liftp p N (by omega) ct.2]) a)
            Iff.rfl)).trans <|
        (Equiv.subtypeEquivRight (fun b =>
          ⟨fun h => h.2, fun h => ⟨descBox_of_descStratum p (by omega : M + 1 ≤ M₂) h.1, h⟩⟩)).trans
          (descendTower_bijection N rest' M₂ ct₂
            (s - (p : ZMod (p ^ N)) ^ M * liftp p N ct.1)
            (t - (p : ZMod (p ^ N)) ^ M * liftp p N ct.2) (by omega) hchain₂ hN))

/-- The tower bijection's underlying coordinate map IS Ψ_k (`towerMap`) — the value lemma
`joint_count` pulls the leaf condition through. -/
theorem descendTower_bijection_coe (N : ℕ) :
    ∀ (rest : List (ℕ × (ZMod p × ZMod p))) (M : ℕ) (ct : ZMod p × ZMod p)
      (s t : ZMod (p ^ N)) (hm : 1 ≤ M)
      (hchain : List.IsChain (· < ·) (M :: rest.map Prod.fst))
      (hN : 2 * lastHeight M rest + 1 ≤ N)
      (x : {a : fourBox p N // JointStratum p N s t ((M, ct) :: rest) a}),
      (descendTower_bijection p N rest M ct s t hm hchain hN x : fourBox p N)
        = towerMap p N s t ((M, ct) :: rest) x.1
  | [], M, ct, s, t, hm, hchain, hN, x => rfl
  | (M₂, ct₂) :: rest', M, ct, s, t, hm, hchain, hN, x =>
      descendTower_bijection_coe N rest' M₂ ct₂
        (s - (p : ZMod (p ^ N)) ^ M * liftp p N ct.1)
        (t - (p : ZMod (p ^ N)) ^ M * liftp p N ct.2)
        (by have := (List.isChain_cons_cons.mp hchain).1; omega)
        ((List.isChain_cons_cons.mp hchain).2) hN
        ⟨descendMap s t (liftp p N ct.1) (liftp p N ct.2) ((p : ZMod (p ^ N)) ^ M) x.1,
          x.2.2⟩

/-- **The joint ledger (J-D1, note §4)**: for ANY leaf condition C inside the final box B_k,
the joint-stratum members whose Ψ_k-image satisfies C count EXACTLY #C — counts transport with
no normalization (the statement Cases F / F-odd verify bucket-by-bucket). -/
theorem joint_count (N : ℕ) (rest : List (ℕ × (ZMod p × ZMod p))) (M : ℕ)
    (ct : ZMod p × ZMod p) (s t : ZMod (p ^ N)) (hm : 1 ≤ M)
    (hchain : List.IsChain (· < ·) (M :: rest.map Prod.fst))
    (hN : 2 * lastHeight M rest + 1 ≤ N)
    (C : fourBox p N → Prop) (hC : ∀ b, C b → DescBox p N (lastHeight M rest) b) :
    Nat.card {a : fourBox p N //
        JointStratum p N s t ((M, ct) :: rest) a ∧ C (towerMap p N s t ((M, ct) :: rest) a)}
      = Nat.card {b : fourBox p N // C b} := by
  have e1 : {a : fourBox p N //
        JointStratum p N s t ((M, ct) :: rest) a ∧ C (towerMap p N s t ((M, ct) :: rest) a)}
      ≃ {x : {a : fourBox p N // JointStratum p N s t ((M, ct) :: rest) a} //
          C (towerMap p N s t ((M, ct) :: rest) x.1)} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun a : fourBox p N => JointStratum p N s t ((M, ct) :: rest) a)
      (fun a => C (towerMap p N s t ((M, ct) :: rest) a))).symm
  have e2 : {x : {a : fourBox p N // JointStratum p N s t ((M, ct) :: rest) a} //
        C (towerMap p N s t ((M, ct) :: rest) x.1)}
      ≃ {y : {b : fourBox p N // DescBox p N (lastHeight M rest) b} // C y.1} :=
    (descendTower_bijection p N rest M ct s t hm hchain hN).subtypeEquiv
      (fun x => by rw [descendTower_bijection_coe p N rest M ct s t hm hchain hN x])
  have e3 : {y : {b : fourBox p N // DescBox p N (lastHeight M rest) b} // C y.1}
      ≃ {b : fourBox p N // DescBox p N (lastHeight M rest) b ∧ C b} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun b : fourBox p N => DescBox p N (lastHeight M rest) b) C
  have e4 : {b : fourBox p N // DescBox p N (lastHeight M rest) b ∧ C b}
      ≃ {b : fourBox p N // C b} :=
    Equiv.subtypeEquivRight (fun b => ⟨fun h => h.2, fun h => ⟨hC b h, h⟩⟩)
  rw [Nat.card_congr (((e1.trans e2).trans e3).trans e4)]

end Tower

/-! ## 7. Gates (deliverable E) -/

section Gates

set_option maxRecDepth 100000 in
/-- **Gate (i-a), p = 2, m = 1, N = 3, key (s̄,t̄) = (1,1), center c̃ = x̄+1**: stratum count 4
by kernel `decide` — matches the closed form 2^{4·3−6−4} = 4 (`card_descStratum`). -/
theorem gate_p2_stratum :
    Nat.card {a : fourBox 2 3 //
        DescStratum 2 3 1 1 1 ((1 : ZMod 2), (1 : ZMod 2)) a} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

set_option maxRecDepth 100000 in
/-- **Gate (i-b)**: the child box count 4 by kernel `decide` — stratum card = box card, the
J1-step equinumerosity, machine-verified in-kernel. -/
theorem gate_p2_box :
    Nat.card {b : fourBox 2 3 // DescBox 2 3 1 b} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

set_option maxRecDepth 100000 in
/-- **Gate (i-c), the membership-iff mechanism in-kernel**: over ALL 4096 points of the
p = 2, N = 3 box, the stratum condition holds iff Θ_ĉ lands in the child box — `decide`
re-runs `descStratum_iff_descBox`'s content pointwise (s = t = 1, ĉ = x̄+1 lifted as (1,1)). -/
theorem gate_p2_iff_mechanism :
    ∀ a : fourBox 2 3,
      DescStratum 2 3 1 1 1 ((1 : ZMod 2), (1 : ZMod 2)) a
        ↔ DescBox 2 3 1 (descendMap 1 1 1 1 (((2 : ℕ) : ZMod (2 ^ 3)) ^ 1) a) := by
  decide

/-- The three centers of F₄ˣ as (linear, constant) digit pairs: x̄, x̄+1, and 1. -/
def f4UnitCenters : Finset (ZMod 2 × ZMod 2) := {(1, 0), (1, 1), (0, 1)}

/-- **Gate (ii-a), the Case-F depth-2 tower at the BOUNDARY level** (p = 2, key x²+x+1,
history (M₁, M₂) = (1, 2), N = 5 = 2M₂+1): the per-center-pair joint-stratum count is 16 —
`descendTower_bijection` + the closed-form box card 2^{4·5−6·2−4} = 16. Uniform in the
center pair (any (c̃₁, c̃₂)), which IS the exact joint uniformity Case F verifies. -/
theorem gate_caseF_joint (ct₁ ct₂ : ZMod 2 × ZMod 2) :
    Nat.card {a : fourBox 2 5 //
        JointStratum 2 5 1 1 [(1, ct₁), (2, ct₂)] a} = 16 := by
  rw [Nat.card_congr (descendTower_bijection 2 5 [(2, ct₂)] 1 ct₁ 1 1 (by norm_num)
      (by simp) (by simp [lastHeight]))]
  have h : lastHeight 1 [(2, ct₂)] = 2 := rfl
  rw [h, card_descBox 2 5 2 (by norm_num)]
  norm_num

/-- **Gate (ii-b), THE CASE-F 144 TIE** (note §4 consistency check (i)): summing the
per-center-pair count 16 over the 9 center pairs (c̃₁, c̃₂) ∈ F₄ˣ × F₄ˣ gives
9·16 = **144** — the external `case_f_gate.py` count of the (v₀′ = 4, v₁′ ≥ 3)
square-residual bucket at p = 2, N = 5 (the note's 3072·(3/64) = 144: 3072 = 3·1024
step-1 stratum members over the 3 first centers, conditional volume 4⁻³ per second center). -/
theorem gate_caseF_144 :
    ∑ c₁ ∈ f4UnitCenters, ∑ c₂ ∈ f4UnitCenters,
        Nat.card {a : fourBox 2 5 // JointStratum 2 5 1 1 [(1, c₁), (2, c₂)] a} = 144 := by
  simp only [gate_caseF_joint]
  decide

/-- **Gate (iii-a), p = 3 residual arithmetic**: over F₉ = F₃[x]/(x²+1) (key digits
(s̄, t̄) = (0, 1)), the center c̃ = x̄+1 has c̃² = 2x̄·1 − 1·0 ↦ linear 2, and 1 − 1·1 ↦
constant 0: `pairSq` = (2, 0) — kernel `decide` on the F_Q pair product. -/
theorem gate_p3_pairSq :
    pairSq (0 : ZMod 3) (1 : ZMod 3) ((1 : ZMod 3), (1 : ZMod 3)) = (2, 0) := by
  decide

/-- **Gate (iii-b), p = 3 digit atoms** (N = 3, m = 1, center x̄+1): the a₁-coordinate atom
(height 1, digit −2·1 = 1) counts 3 = 3^{3−1−1} in ZMod 27 — kernel `decide`. -/
theorem gate_p3_a1_atom :
    Nat.card {x : ZMod (3 ^ 3) // CoordCond 3 3 1 (-(2 * 1) : ZMod 3) x} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-- **Gate (iii-c)**: the a₀-coordinate atom (height 2, digit = the `pairSq` linear read 2)
counts 1 = 3^{3−2−1} in ZMod 27 — kernel `decide`. -/
theorem gate_p3_a0_atom :
    Nat.card {x : ZMod (3 ^ 3) //
        CoordCond 3 3 2 ((pairSq (0 : ZMod 3) (1 : ZMod 3) (1, 1)).1) x} = 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-- **Gate (iii-d), the p = 3 stratum closed form at the center x̄+1**: count
3^{4·3−6−4} = 9 (= the atom products 3·3·1·1) — the odd-parity instance of the J1-step
ledger (the note's Case F-odd family). -/
theorem gate_p3_stratum :
    Nat.card {a : fourBox 3 3 //
        DescStratum 3 3 1 0 1 ((1 : ZMod 3), (1 : ZMod 3)) a} = 9 := by
  rw [card_descStratum 3 3 1 (by norm_num) 0 1 ((1 : ZMod 3), (1 : ZMod 3))]
  norm_num

end Gates

/-! ## 8. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms descendMap
#print axioms descendInv
#print axioms descendInv_descendMap
#print axioms descendMap_descendInv
#print axioms fourMap_descendMap
#print axioms pairMul
#print axioms pairSq
#print axioms pairSq_eq_pairMul
#print axioms pairSq_scalar_fst
#print axioms pairSq_scalar_snd
#print axioms descendEquiv
#print axioms descendEquiv_apply
#print axioms descendEquiv_symm_apply
#print axioms descendMap_toZModPow
#print axioms linPair_mul_linPair
#print axioms descend_redevelopment
#print axioms descend_redevelopment_of
#print axioms descend_division_padic
#print axioms coordCond_iff_exists
#print axioms dvd_succ_iff_exists
#print axioms liftp
#print axioms resp_liftp
#print axioms pairSq_scalar_mem_squareUnitPairs
#print axioms DescStratum
#print axioms instDecidableDescStratum
#print axioms DescBox
#print axioms instDecidableDescBox
#print axioms descStratum_iff_descBox
#print axioms descend_bijection
#print axioms card_coordCond
#print axioms card_coordCond_pair
#print axioms card_dvd_pair
#print axioms card_descStratum
#print axioms card_descBox
#print axioms card_descStratum_eq_card_descBox
#print axioms lastHeight
#print axioms le_lastHeight
#print axioms JointStratum
#print axioms towerMap
#print axioms descBox_of_descStratum
#print axioms descendTower_bijection
#print axioms descendTower_bijection_coe
#print axioms joint_count
#print axioms gate_p2_stratum
#print axioms gate_p2_box
#print axioms gate_p2_iff_mechanism
#print axioms f4UnitCenters
#print axioms gate_caseF_joint
#print axioms gate_caseF_144
#print axioms gate_p3_pairSq
#print axioms gate_p3_a1_atom
#print axioms gate_p3_a0_atom
#print axioms gate_p3_stratum
end AxCheck

end LeanUrat.OM.DescendBijection
