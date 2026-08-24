/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130k
import Uniformity.ChapC.C16
import Uniformity.ChapC.C87

/-!
# Uniformity.ChapC.C130ln — the Laurent normalizer solve (chain-carrier node CC-4)

**Chain-carrier node CC-4** of `docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` (§4.1,
§10 row CC-4): construct the integer normalizer exponents by Bézout/rung recursion
(`DeepTower.laurentSolve`), prove the **exact weighted-height law for ALL `k : ℤ`**
(`laurentNormAt_exact_height`), and state compatibility with C.83's `towerNorm` ONLY on the
guarded nontruncation domain (`DeepTower.NoTrunc`, `laurentSolve_eq_towerNorm`) — the domain
named by C130B's verdict (`runs/wave-b/verdict_C130B.md`), whose counterexample at
`(e₂, u₂, k) = (2, 5, 1)` refuted the freeze's demand that C.83's ℕ-truncated `towerNorm`
itself be the exact solve.

The recursion is C.83's ladder recursion `e_{j+1}·m_j + b_j·u_{j+1} = k` run over `ℤ`: at each
rung the exponent `b_j` is the SAME canonical representative C.83 would pick (`towerSolve` at
the Euclidean residue `(k % e).toNat ∈ [0, e)`; at the bottom, C.15's `slotIdx`), but the
descent `m_j = (k − b_j·u_{j+1})/e_{j+1}` is exact integer division — Laurent words at negative
residual heights instead of C130B's truncation.  Coprimality (C.83's `hcop` rung fields,
`F.hcop` at the frame) makes every division exact; this is the general-depth form of D62w's
landed depth-3 greedy solve (`d3b2`/`d3m2`/…, `deep3_exact_height`).

## ⚠ STOP-THE-LINE FINDING — REPAIRED 2026-08-24 (orchestrator; refuter retired to git history)

The landed `levelExponentHeight` (C.130f) carries the Φ-weight denominator `T.e (a.1 + 2)`.
The corpus pattern is `T.ehat (a.1 + 2)`: C.130f's own docstring says `(ê_j/ê_(a+2))u_(a+2)`,
and D62w's regressed lattices pin it numerically — at the F-LW3/F-P5/F-EC3 chain
(`e = (2,2,2)`, `h = 1`, `u = (1,5,21)`), the depth-3 weights on `(π, x, Φ₁, Φ₂)` are
`(8, 4, 10, 21)`, i.e. `Φ₁ ↦ (ê₃/ê₂)u₂ = 10`, whereas the landed denominator gives
`(ê₃/e₂)u₂ = 20`; the GENTOW5.21 regression rows `n̂₂(21) = 2⁴Φ′`, `n̂₃(85) = 2⁸Φ₂` force the
same weights (`4·4 + 5 = 21`, `8·8 + 21 = 85`).  Consequence, PROVED below
(`isEmpty_laurentNormalizer_of_two_dvd`): whenever `2 ∣ e₁`, `2 ∣ e₂` and `2 ≤ r` — in
particular at every S2/S4 witness chain, the intended first instance — ALL level-2 landed
weights are even, so `C130k.LaurentNormalizer`'s `exact_height` field is **uninhabitable**
(`ofAdd 1` is never hit).  No construction can target the landed structure as-is; C.130f and
C.130k are read-only to this unit, so the one-token repair (`T.e (a.1 + 2)` →
`T.ehat (a.1 + 2)` in `levelExponentHeight`) is left to the orchestrator.

This file therefore lands the mathematics against the corrected height
`levelExponentHeightHat` — a byte-mirror of the landed definition with exactly that one token
fixed — and packages the literal `LaurentNormalizer T` constructor behind the named agreement
hypothesis (`laurentNormalizerOfAgree`), which becomes `fun _ _ _ => rfl` the moment C.130f is
repaired.  No statement is weakened: the exact-height law is proved for every `k : ℤ` at every
stage-live level, with no `sorry`, no axiom, no `True`-bodied interface.

## Declarations

* `towerSolve_spec` · `towerSolve_mod` · `KeyFrame.slotIdx_eq_towerSolve` ·
  `KeyFrame.slotIdx_mod` · `towerSolve_rung_dvd` — the Bézout rung layer: C.16's spec
  generalized from the frame `(h, e₁)` to any coprime rung `(u, e)` (existence = H.51(b)
  `class_sep_bij`), and the ℤ-exactness of one rung at the canonical representative.
* `levelExponentHeightHat` — the corrected height (see the finding above).
* `DeepTower.ehat_one` · `DeepTower.natCast_ehat_div_succ` — cast-quotient rung scaling on
  C.87's `ehat` API.
* `DeepTower.laurentSolve` · `DeepTower.laurentNormAt` · `…_zero` — the CC-4 normalizer.
* `DeepTower.heightAux` · `levelExponentHeightHat_ofAdd` · `DeepTower.heightAux_snoc` ·
  `DeepTower.laurentSolve_exact` · `DeepTower.laurentNormAt_exact_height` — the exact-height
  law for all `k : ℤ` (the CC-4 exit condition).
* `DeepTower.NoTrunc` · `DeepTower.laurentSolve_eq_towerNorm` ·
  `DeepTower.towerNormLattice_eq_laurentNormAt` · `DeepTower.towerNormLattice_exact_heightHat`
  — the guarded C.83 compatibility: on the nontruncation domain the Laurent solve IS
  `towerNorm`, and C.83's word then sits at exact Hat-height.
* `DeepTower.laurentNormalizerOfAgree` — the `C130k.LaurentNormalizer` constructor behind the
  named landed-height agreement hypothesis.
* `DeepTower.laurentNormalizer` — the literal instance (post-repair; the refuter
  `isEmpty_laurentNormalizer_of_two_dvd` is retired to the "BP: CC-4" commit in git history).

## Status

Sorry-free, axiom-free (Lean core only).  C.130f/C.130k untouched (read-only vocabulary).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf
open Uniformity.Density.Induction

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## The Bézout rung layer -/

/-- **The rung-solve spec** — C.16 (i) generalized from the frame `(h, e₁)` to an arbitrary
coprime rung `(u, e)`: under `Nat.Coprime u e` and `0 < e`, C.83's `towerSolve u e k` lands in
`[0, e)` and solves `b·u ≡ k (mod e)`.  Existence is H.51(b) `class_sep_bij`, exactly as at
C.16; this is the Bézout input of the CC-4 rung recursion. -/
theorem towerSolve_spec {u e : ℕ} (hcop : Nat.Coprime u e) (he : 0 < e) (k : ℕ) :
    towerSolve u e k < e ∧ towerSolve u e k * u % e = k % e := by
  have hex : ∃ i ∈ (↑(Finset.range e) : Set ℕ), i * u % e = k % e :=
    (class_sep_bij hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt k he)
  have hnone : (List.range e).find? (fun b => (b * u) % e == k % e) ≠ none := by
    intro hn
    obtain ⟨i, hi, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact (List.find?_eq_none.mp hn i (List.mem_range.mpr hi)) (by simpa using hcong)
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : towerSolve u e k = b := by rw [towerSolve, hb]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some hb), ?_⟩
  have hp := List.find?_some hb
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

/-- `towerSolve` reads `k` only through its class `k % e` (the search predicate does). -/
theorem towerSolve_mod (u e k : ℕ) : towerSolve u e (k % e) = towerSolve u e k := by
  unfold towerSolve
  rw [Nat.mod_mod_of_dvd k dvd_rfl]

/-- C.15's frame solve IS C.83's rung solve at `(h, e₁)` — the bodies are byte-identical. -/
theorem KeyFrame.slotIdx_eq_towerSolve (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx k = towerSolve F.h F.e₁ k := rfl

/-- `slotIdx` reads `k` only through its class `k % e₁`. -/
theorem KeyFrame.slotIdx_mod (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx (k % F.e₁) = F.slotIdx k := by
  rw [F.slotIdx_eq_towerSolve, F.slotIdx_eq_towerSolve, towerSolve_mod]

/-- **One exact Laurent rung.**  For a coprime rung `(u, e)`, the canonical solve at the
Euclidean residue `(k % e).toNat ∈ [0, e)` clears the rung exactly over `ℤ`: `e ∣ k − b·u`
for EVERY `k : ℤ`.  This is the descent step C.83's ℕ recursion can only make above `b·u`
(C130B's truncation refutation); over `ℤ` it is unconditional. -/
theorem towerSolve_rung_dvd {u e : ℕ} (hcop : Nat.Coprime u e) (he : 0 < e) (k : ℤ) :
    (e : ℤ) ∣ k - (towerSolve u e (k % (e : ℤ)).toNat : ℤ) * (u : ℤ) := by
  have hne : ((e : ℤ)) ≠ 0 := by exact_mod_cast he.ne'
  have htz : (((k % (e : ℤ)).toNat : ℕ) : ℤ) = k % (e : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg k hne)
  have hs : towerSolve u e (k % (e : ℤ)).toNat * u % e = (k % (e : ℤ)).toNat % e :=
    (towerSolve_spec hcop he _).2
  have h2 : ((towerSolve u e (k % (e : ℤ)).toNat : ℤ) * (u : ℤ)) % (e : ℤ) = k % (e : ℤ) := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hs
    push_cast at hcast
    rw [hcast, htz, Int.emod_emod_of_dvd k dvd_rfl]
  exact Int.ModEq.dvd h2

/-! ## The corrected level height

`levelExponentHeightHat` is a byte-mirror of C.130f's landed `levelExponentHeight` with the
single mis-transcribed token corrected: the Φ-weight denominator is `T.ehat (a.1 + 2)`, not
`T.e (a.1 + 2)`.  See the module docstring's finding for the D62w/GENTOW5.21 evidence; the
formal refuter for the landed pattern is `isEmpty_laurentNormalizer_of_two_dvd` below. -/

/-- The corrected level-`j` height of a Laurent exponent vector: weights `ê_j` on `π`,
`(ê_j/e₁)u₁` on `x`, and `(ê_j/ê_(a+2))u_(a+2)` on `Φ_(a+1)` — the pattern regressed by D62w's
depth-two and depth-three lattices (`(4, 2, 5)` and `(8, 4, 10, 21)`) and by the GENTOW5.21
rows.  Byte-mirror of the landed `levelExponentHeight` except the one corrected token. -/
def levelExponentHeightHat (T : DeepTower F H₀ hpin r) (j : ℕ) :
    LevelExponentLattice j →* Multiplicative ℤ where
  toFun g :=
    let z := Multiplicative.toAdd g
    Multiplicative.ofAdd
      (z.1 * T.ehat j + z.2.1 * ((T.ehat j / T.e 1) * T.u 1) +
        ∑ a : Fin (j - 1), z.2.2 a * ((T.ehat j / T.ehat (a.1 + 2)) * T.u (a.1 + 2)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring

namespace DeepTower

/-! ## `ehat` cast-quotient helpers (on C.87's API) -/

/-- `ê_1 = e_1`: the cumulative product at depth one is the single frame rung. -/
theorem ehat_one (T : DeepTower F H₀ hpin r) : T.ehat 1 = T.e 1 := by
  rw [DeepTower.ehat, Finset.Icc_self, Finset.prod_singleton]

/-- One-rung scaling of the exact cast quotients: if `d ∣ ê_i` then, over `ℤ`,
`ê_{i+1}/d = (ê_i/d)·e_{i+1}`.  Exactness is C.87's `ehat_dvd`/`ehat_succ`; the cast
divisions are Euclidean, which on the exact nonnegative quotients is `Nat`-division. -/
theorem natCast_ehat_div_succ (T : DeepTower F H₀ hpin r) {d i : ℕ} (hdvd : d ∣ T.ehat i) :
    (T.ehat (i + 1) : ℤ) / (d : ℤ) = ((T.ehat i : ℤ) / (d : ℤ)) * (T.e (i + 1) : ℤ) := by
  have hN : T.ehat (i + 1) / d = T.ehat i / d * T.e (i + 1) := by
    rw [T.ehat_succ i, mul_comm (T.ehat i) (T.e (i + 1)), Nat.mul_div_assoc _ hdvd,
      mul_comm (T.e (i + 1)) (T.ehat i / d)]
  rw [← Int.natCast_ediv, ← Int.natCast_ediv, hN, Nat.cast_mul]

/-! ## The CC-4 Laurent solve -/

/-- **The CC-4 integer normalizer exponents** (`EFF.T2.07`, `EFF.GENTOW5.15`): C.83's ladder
recursion `e_{j+1}·m_j + b_j·u_{j+1} = k`, run over `ℤ`.  Each rung picks the SAME canonical
representative C.83's `towerNorm` picks — `towerSolve` at the Euclidean residue
`(k % e).toNat ∈ [0, e)` (at the bottom, C.15's `slotIdx`) — but descends by exact integer
division, so negative residual heights produce Laurent words instead of C130B's truncation.
Total in `(i, k)`; off the live range the values are junk and no lemma reads them. -/
def laurentSolve (T : DeepTower F H₀ hpin r) : (i : ℕ) → ℤ → ℤ × ℤ × (Fin i → ℤ)
  | 0, k =>
      let b := F.slotIdx (k % (F.e₁ : ℤ)).toNat
      ((k - b * F.h) / F.e₁, (b : ℤ), fun x => x.elim0)
  | i + 1, k =>
      let b := towerSolve (T.u (i + 2)) (T.e (i + 2)) (k % (T.e (i + 2) : ℤ)).toNat
      let m := (k - b * T.u (i + 2)) / T.e (i + 2)
      let p := laurentSolve T i m
      (p.1, p.2.1, Fin.snoc p.2.2 (b : ℤ))

/-- The lattice-valued Laurent section at level `j` (the `j - 1` offset mirrors
`towerNormLattice`: level `j` carries the `n̂_j`-exponents `(a₀, i₀, b_1 … b_{j-1})`). -/
def laurentNormAt (T : DeepTower F H₀ hpin r) (j : ℕ) (k : ℤ) : LevelExponentLattice j :=
  Multiplicative.ofAdd (T.laurentSolve (j - 1) k)

/-- The Laurent solve at height `0` is the zero exponent tuple, at every depth (including junk
depths — no liveness is consumed): every rung solve returns `0` at `0`. -/
theorem laurentSolve_zero (T : DeepTower F H₀ hpin r) (i : ℕ) :
    T.laurentSolve i 0 = (0, 0, fun _ => 0) := by
  induction i with
  | zero =>
      simp only [laurentSolve, Int.zero_emod, Int.toNat_zero, F.slotIdx_zero]
      norm_num
      funext x
      exact x.elim0
  | succ i ih =>
      simp only [laurentSolve, Int.zero_emod, Int.toNat_zero, towerSolve_zero]
      norm_num [ih]
      funext x
      refine Fin.lastCases ?_ (fun a => ?_) x <;> simp

/-- `n(0) = 1`: the D.01 `NormSection` normalization holds for the Laurent section. -/
theorem laurentNormAt_zero (T : DeepTower F H₀ hpin r) (j : ℕ) : T.laurentNormAt j 0 = 1 := by
  unfold laurentNormAt
  rw [T.laurentSolve_zero]
  rfl

/-! ## The exact-height law for all `k : ℤ` -/

/-- The additive level-`(i+1)` Hat-height of a raw exponent tuple — the scalar form the rung
induction runs on.  `levelExponentHeightHat_ofAdd` ties it to the bundled homomorphism. -/
def heightAux (T : DeepTower F H₀ hpin r) (i : ℕ) (v : ℤ × ℤ × (Fin i → ℤ)) : ℤ :=
  v.1 * T.ehat (i + 1) + v.2.1 * ((T.ehat (i + 1) / T.e 1) * T.u 1) +
    ∑ a : Fin i, v.2.2 a * ((T.ehat (i + 1) / T.ehat (a.1 + 2)) * T.u (a.1 + 2))

end DeepTower

/-- The bundled Hat height at level `i + 1` on an `ofAdd` tuple is the additive `heightAux`. -/
theorem levelExponentHeightHat_ofAdd (T : DeepTower F H₀ hpin r) (i : ℕ)
    (v : ℤ × ℤ × (Fin i → ℤ)) :
    levelExponentHeightHat T (i + 1) (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (T.heightAux i v) := rfl

namespace DeepTower

/-- **The rung-peel identity of the Hat height**: appending a top exponent `b` at a live level
`i + 2` scales the lower-level height by `e_{i+2}` and adds `b·u_{i+2}`.  This is exactly the
weight recursion D62w regressed; the landed `T.e`-denominator pattern does NOT satisfy it. -/
theorem heightAux_snoc (T : DeepTower F H₀ hpin r) {i : ℕ} (hi : i + 2 ≤ r)
    (v : ℤ × ℤ × (Fin i → ℤ)) (b : ℤ) :
    T.heightAux (i + 1) (v.1, v.2.1, Fin.snoc v.2.2 b) =
      T.e (i + 2) * T.heightAux i v + b * T.u (i + 2) := by
  have he1 : T.e 1 ∣ T.ehat (i + 1) := T.ehat_one ▸ T.ehat_dvd (by omega)
  have hx : (T.ehat (i + 2) : ℤ) / (T.e 1 : ℤ) =
      ((T.ehat (i + 1) : ℤ) / (T.e 1 : ℤ)) * (T.e (i + 2) : ℤ) :=
    T.natCast_ehat_div_succ he1
  have hw : ∀ a : Fin i, (T.ehat (i + 2) : ℤ) / (T.ehat (a.1 + 2) : ℤ) =
      ((T.ehat (i + 1) : ℤ) / (T.ehat (a.1 + 2) : ℤ)) * (T.e (i + 2) : ℤ) :=
    fun a => T.natCast_ehat_div_succ (T.ehat_dvd (by omega))
  have htop : (T.ehat (i + 2) : ℤ) / (T.ehat (i + 2) : ℤ) = 1 :=
    Int.ediv_self (by exact_mod_cast (T.ehat_pos hi).ne')
  have hπ : ((T.ehat (i + 2) : ℕ) : ℤ) = (T.ehat (i + 1) : ℤ) * (T.e (i + 2) : ℤ) := by
    rw [T.ehat_succ (i + 1)]
    push_cast
    ring
  have hsum : ∑ a : Fin i,
        v.2.2 a * ((T.ehat (i + 2) : ℤ) / (T.ehat (a.1 + 2) : ℤ) * (T.u (a.1 + 2) : ℤ)) =
      (∑ a : Fin i,
        v.2.2 a * ((T.ehat (i + 1) : ℤ) / (T.ehat (a.1 + 2) : ℤ) * (T.u (a.1 + 2) : ℤ))) *
        (T.e (i + 2) : ℤ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [hw a]; ring
  unfold heightAux
  simp only [show i + 1 + 1 = i + 2 from rfl]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [hsum, hx, htop, hπ]
  ring

/-- **The CC-4 exact-height solve, additive form**: on the live range `i + 1 ≤ r`, the Laurent
solve hits EVERY integer height exactly — `heightAux i (laurentSolve i k) = k` for all
`k : ℤ`.  Bézout at each rung (coprimality from C.83's `hcop`, `F.hcop` at the frame), rung
recursion by `heightAux_snoc`. -/
theorem laurentSolve_exact (T : DeepTower F H₀ hpin r) :
    ∀ i : ℕ, i + 1 ≤ r → ∀ k : ℤ, T.heightAux i (T.laurentSolve i k) = k := by
  intro i
  induction i with
  | zero =>
      intro hi k
      have hne : ((F.e₁ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast F.he₁.ne'
      have hdvd : (F.e₁ : ℤ) ∣ k - (F.slotIdx (k % (F.e₁ : ℤ)).toNat : ℤ) * (F.h : ℤ) := by
        rw [KeyFrame.slotIdx_eq_towerSolve]
        exact towerSolve_rung_dvd F.hcop F.he₁ k
      simp only [laurentSolve, heightAux, Fin.sum_univ_zero, Nat.zero_add, T.ehat_one,
        T.he1, T.hu1, add_zero]
      rw [Int.ediv_self hne, Int.ediv_mul_cancel hdvd]
      ring
  | succ i ih =>
      intro hi k
      have h2r : i + 2 ≤ r := hi
      have hcop := T.hcop (i + 2) (by omega) h2r
      have hepos := T.he (i + 2) (by omega) h2r
      have hdvd : (T.e (i + 2) : ℤ) ∣
          k - (towerSolve (T.u (i + 2)) (T.e (i + 2)) (k % (T.e (i + 2) : ℤ)).toNat : ℤ) *
            (T.u (i + 2) : ℤ) :=
        towerSolve_rung_dvd hcop hepos k
      simp only [laurentSolve]
      rw [T.heightAux_snoc h2r, ih (by omega), Int.mul_ediv_cancel' hdvd]
      ring

/-- **CC-4 exit condition: the exact-height law for ALL `k : ℤ`**, at every stage-live level,
against the corrected Hat height (`EFF.T2.07`/`EFF.GENTOW5.15`).  This is the theorem C130B
proved impossible for C.83's ℕ-truncated `towerNorm`; the Laurent solve satisfies it with no
domain restriction whatsoever. -/
theorem laurentNormAt_exact_height (T : DeepTower F H₀ hpin r) (i : ℕ) (hi : StageLive r i)
    (k : ℤ) :
    levelExponentHeightHat T i (T.laurentNormAt i k) = Multiplicative.ofAdd k := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- `laurentNormAt (j+1) = ofAdd (laurentSolve j ·)` and `Hat (ofAdd ·) = ofAdd (heightAux ·)`
  -- both hold by `rfl`, so the additive exact solve closes the goal up to defeq.
  exact congrArg Multiplicative.ofAdd (T.laurentSolve_exact j h2 k)

/-! ## Guarded compatibility with C.83's `towerNorm`

C130B's verdict: the freeze's demand that `towerNorm` itself be the exact solve at every
nonnegative height is FALSE — the ℕ recursion truncates `(k − b·u)/e` whenever `b·u > k`
(already at `(e₂, u₂, k) = (2, 5, 1)`).  The honest compatibility is therefore guarded by the
nontruncation domain: `NoTrunc` names exactly the heights whose entire descent chain stays
nonnegative, and THERE the Laurent solve coincides with C.83's word verbatim. -/

/-- The nontruncation domain of C.83's `towerNorm` recursion: at every rung the subtraction
`k − b·u` is genuine (no ℕ truncation), hereditarily down the descent chain.  This is the
domain C130B's verdict names for any `towerNorm` compatibility. -/
def NoTrunc (T : DeepTower F H₀ hpin r) : (i : ℕ) → ℕ → Prop
  | 0, k => F.slotIdx k * F.h ≤ k
  | i + 1, k =>
      towerSolve (T.u (i + 2)) (T.e (i + 2)) k * T.u (i + 2) ≤ k ∧
        T.NoTrunc i
          ((k - towerSolve (T.u (i + 2)) (T.e (i + 2)) k * T.u (i + 2)) / T.e (i + 2))

/-- **The guarded compatibility** (CC-4's third clause): on the nontruncation domain the
Laurent solve IS C.83's `towerNorm` word, componentwise under the cast `ℕ → ℤ`.  No
coprimality is consumed — both recursions pick the same `towerSolve` representative and both
divisions agree on genuine (nonnegative, nontruncated) inputs. -/
theorem laurentSolve_eq_towerNorm (T : DeepTower F H₀ hpin r) :
    ∀ (i : ℕ) (k : ℕ), T.NoTrunc i k →
      T.laurentSolve i (k : ℤ) =
        (((T.towerNorm i k).1 : ℤ), ((T.towerNorm i k).2.1 : ℤ),
          fun a => ((T.towerNorm i k).2.2 a : ℤ)) := by
  intro i
  induction i with
  | zero =>
      intro k hk
      simp only [NoTrunc] at hk
      have hmod : ((k : ℤ) % (F.e₁ : ℤ)).toNat = k % F.e₁ := by
        rw [← Int.natCast_mod, Int.toNat_natCast]
      simp only [laurentSolve, DeepTower.towerNorm, hmod, F.slotIdx_mod]
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial, ?_⟩
      · rw [← Nat.cast_mul, ← Nat.cast_sub hk, ← Int.natCast_ediv]
      · funext x
        exact x.elim0
  | succ i ih =>
      intro k hk
      simp only [NoTrunc] at hk
      obtain ⟨hb, hrec⟩ := hk
      have hmod : ((k : ℤ) % (T.e (i + 2) : ℤ)).toNat = k % T.e (i + 2) := by
        rw [← Int.natCast_mod, Int.toNat_natCast]
      have hcast : ((k : ℤ)) - (towerSolve (T.u (i + 2)) (T.e (i + 2)) k : ℤ) *
            (T.u (i + 2) : ℤ) =
          ((k - towerSolve (T.u (i + 2)) (T.e (i + 2)) k * T.u (i + 2) : ℕ) : ℤ) := by
        rw [← Nat.cast_mul, ← Nat.cast_sub hb]
      simp only [laurentSolve, DeepTower.towerNorm, hmod, towerSolve_mod, hcast,
        ← Int.natCast_ediv, ih _ hrec]
      simp only [Prod.mk.injEq]
      refine ⟨trivial, trivial, ?_⟩
      funext x
      refine Fin.lastCases ?_ (fun a => ?_) x <;> simp

/-- C.83's lattice word is the Laurent section, on the nontruncation domain. -/
theorem towerNormLattice_eq_laurentNormAt (T : DeepTower F H₀ hpin r) (j k : ℕ)
    (hk : T.NoTrunc (j - 1) k) :
    towerNormLattice T j k = T.laurentNormAt j (k : ℤ) := by
  simp only [towerNormLattice, laurentNormAt]
  exact congrArg Multiplicative.ofAdd (T.laurentSolve_eq_towerNorm (j - 1) k hk).symm

/-- Retro-validation of C.83 on its honest domain: at a stage-live level, a NONTRUNCATED
`towerNorm` word sits at exact Hat-height.  (The GENTOW5.21 regression rows live here.) -/
theorem towerNormLattice_exact_heightHat (T : DeepTower F H₀ hpin r) {j : ℕ}
    (hj : StageLive r j) (k : ℕ) (hk : T.NoTrunc (j - 1) k) :
    levelExponentHeightHat T j (towerNormLattice T j k) = Multiplicative.ofAdd (k : ℤ) := by
  rw [T.towerNormLattice_eq_laurentNormAt j k hk]
  exact T.laurentNormAt_exact_height j hj (k : ℤ)

/-- **The `C130k.LaurentNormalizer` constructor**, packaged behind the named agreement
hypothesis between the landed height and the corrected Hat height.  The hypothesis is honest:
it is UNSATISFIABLE on towers with `2 ∣ e₁`, `2 ∣ e₂` (see
`isEmpty_laurentNormalizer_of_two_dvd` — the landed weight pattern is mis-transcribed), and
becomes `fun _ _ _ => rfl` the moment C.130f's one-token repair lands.  No field of the
returned structure is weakened. -/
def laurentNormalizerOfAgree (T : DeepTower F H₀ hpin r)
    (hagree : ∀ i, StageLive r i → ∀ g : LevelExponentLattice i,
      levelExponentHeight T i g = levelExponentHeightHat T i g) :
    LaurentNormalizer T where
  norm := T.laurentNormAt
  norm_zero := T.laurentNormAt_zero
  exact_height := fun i hi k => by
    rw [hagree i hi]
    exact T.laurentNormAt_exact_height i hi k

/-- The literal `C130k.LaurentNormalizer`, unconditionally: after the C.130f one-token
repair (2026-08-24, orchestrator; refuter history in the "BP: CC-4" commit), the landed
`levelExponentHeight` and this file's `levelExponentHeightHat` agree definitionally. -/
def laurentNormalizer (T : DeepTower F H₀ hpin r) : LaurentNormalizer T :=
  T.laurentNormalizerOfAgree fun _ _ _ => rfl

end DeepTower

/-! ## The stop-the-line refuter — RETIRED (repair enacted 2026-08-24)

The machine-checked refuter `isEmpty_laurentNormalizer_of_two_dvd` (the LANDED weight
pattern `T.e (a.1+2)` made `LaurentNormalizer` empty on every doubly even-ramified tower)
is preserved verbatim in git history at the commit titled "BP: CC-4 SUPPLY +
STOP-THE-LINE" (8f8537d7).  The orchestrator then enacted the one-token C.130f repair
(`T.e (a.1+2)` → `T.ehat (a.1+2)` in `levelExponentHeight`), after which the landed height
and `levelExponentHeightHat` agree definitionally and the refuter's premise no longer
exists.  The literal instance is `DeepTower.laurentNormalizer` above. -/

/-! ## Teeth: C130B's truncation site, at the predicate level

At the rung `(u₂, e₂) = (5, 2)` and height `k = 1` — C130B's counterexample — the guard
excludes exactly the failing input: the solve picks `b = 1` and `b·u₂ = 5 > 1`, so `NoTrunc`
fails at its first clause and the guarded compatibility never fires there. -/

example (T : DeepTower F H₀ hpin r) (hu : T.u 2 = 5) (he : T.e 2 = 2) :
    ¬ T.NoTrunc 1 1 := by
  simp only [DeepTower.NoTrunc, hu, he]
  intro h
  have h1 : towerSolve 5 2 1 = 1 := by decide
  rw [h1] at h
  omega

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerSolve_spec
#print axioms Uniformity.Density.Tower.towerSolve_mod
#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_eq_towerSolve
#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_mod
#print axioms Uniformity.Density.Tower.towerSolve_rung_dvd
#print axioms Uniformity.Density.Tower.levelExponentHeightHat
#print axioms Uniformity.Density.Tower.DeepTower.ehat_one
#print axioms Uniformity.Density.Tower.DeepTower.natCast_ehat_div_succ
#print axioms Uniformity.Density.Tower.DeepTower.laurentSolve
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormAt
#print axioms Uniformity.Density.Tower.DeepTower.laurentSolve_zero
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormAt_zero
#print axioms Uniformity.Density.Tower.DeepTower.heightAux
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormalizer
#print axioms Uniformity.Density.Tower.levelExponentHeightHat_ofAdd
#print axioms Uniformity.Density.Tower.DeepTower.heightAux_snoc
#print axioms Uniformity.Density.Tower.DeepTower.laurentSolve_exact
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormAt_exact_height
#print axioms Uniformity.Density.Tower.DeepTower.NoTrunc
#print axioms Uniformity.Density.Tower.DeepTower.laurentSolve_eq_towerNorm
#print axioms Uniformity.Density.Tower.DeepTower.towerNormLattice_eq_laurentNormAt
#print axioms Uniformity.Density.Tower.DeepTower.towerNormLattice_exact_heightHat
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormalizerOfAgree

end AxCheck
