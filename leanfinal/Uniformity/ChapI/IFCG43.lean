/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG27
import Uniformity.ChapI.IFCG29
import Uniformity.ChapI.IFCG39

/-!
# Uniformity.ChapI.IFCG43 — [PSL3 2026-08-30] the power sector's four named legs:
the compositum, the cell transport, the `ZcURLim` closure, the transfer criterion

Stage PSL3 of the cone census (design record `runs/wave-c/verdict_PSL3.md`; the fence
is IFCG39's docstring + `runs/wave-c/verdict_PSL.md`).  IFCG39 landed the power
sector's second-order Montes instruments (the strict mass drop, the `xKey`, the
Eisenstein complete-DVR cascade with its coordinate lattice, the dev-transform
bijection with two-way level exactness).  This file takes the four named legs of
`PowerSectorLaw m σ` in tractability order:

* **§1 LEG 4 — the general-face compositum** (`compositum_recentring_stack`): the
  unramified step (IFCG27's cascade at a residual key `φ`, residue field `𝔽_{q^d}`)
  composed with the Eisenstein step (IFCG39's cascade at `eisKey π₁ c₁ e'` over
  `O₁ = AdjoinRoot φ`): the composite `O₂` is a COMPLETE DVR with
  `residueCard O₂ = q ^ deg φ` and full-tower ramification
  `𝔪^K·O₂ = 𝔪₂^{e'·K}` — the ring where the general-face `(h, e', d)` recentred
  cells live, at every complete DVR, every key, every unit centre, every `e' ≥ 2`.
* **§2 LEG 2 — the cell/count transport** (`cellTransport`): the dev-transform
  bijection DESCENDS to the finite coefficient boxes — a level-exact equivalence
  `Coeff O (e'·k) N ≃ Coeff O' k (e'·N)` (level scales by exactly `fScale = e'`),
  computed on lifts by `devVec`/`reassVec` (`cellTransport_apply`, `_symm_apply`);
  hence the COUNT TRANSPORT `Nat.card (T '' S) = Nat.card S` for every cell set `S`
  and the box pin `Nat.card (Coeff O' k (e'·N)) = q ^ (k·(e'·N))` at the SAME `q`.
* **§3 LEG 3 — the `ZcURLim` closure instruments**: `eis_recentring_stack` (the
  general `(c, e')` instance package — every ∀-DVR law family may legally be
  instantiated at the recentring ring; generalizes IFCG39 §6's dd `(2,2)` point) and
  `ZcURLim.eis_value` (the consumption: any `ZcURLim` family, instantiated at the
  Eisenstein ring, converges to the value of ITS OWN rational pair at the ORIGINAL
  `q` — `q' = q`, so recentred limits stay in the same rational family).
* **§4 LEG 1 — the residual-box transfer criterion** (the mathematical heart):
  C110's translate-residual criterion at the recentred frame `e' ≥ 2`, x-frame
  `(h, d) = (1, 1)` sub-sector, BOTH directions proved: `eis_transfer_digits_iff`
  (a pure slope-`1/e'` block of degree `e'·k` has lattice digits reading
  `(X − z̄)^k` ⟺ its `eisKey`-adic development lies in the DEEP recentred box
  `α^{e'(k−t)+1} ∣ mk (dev t)` over `O'`), through the replicated C110 binomial
  shift, the `X^{e'}`-block reads, and the digit-combination vanishing
  `Σ_s C(s,t)C(k,s)(−1)^{k−s} = C(k,t)·(1−1)^{k−t} = 0`; plus the sector-facing
  form `resPoly_eq_pow_iff_box` (the x-frame residual polynomial is the recentred
  `k`-th power ⟺ the deep box), under explicit side pins.

## Honest scope (the exact remainder toward `PowerSectorLaw m σ`)

The four legs are landed as INSTRUMENTS; `PowerSectorLaw m σ` itself does NOT fire
in this file.  The exact surviving open set:
1. **The face-indexed assembly** — partition `powerSector` by its (unique) minimal
   face and residual centre, transport `classResidualPoly` to a lift's `resPoly`
   (IFCG39 §1's `resPoly_rep` idiom), extract the side pins + raw purity from
   `IsPure`/`MinFaceAt`, and identify each face's cell set through
   `resPoly_eq_pow_iff_box` + `cellTransport` — bookkeeping against landed API.
2. **The general-`(h, d)` criterion** — LEG 1 is proved at the Eisenstein frame
   `(h, d) = (1, 1)`; `h > 1` needs the key `X^{e'} + C(c·π^h)` (the `d = 1` xKey)
   and `d ≥ 2` the composed key over LEG 4's compositum ring: the RINGS are landed
   (`compositum_recentring_stack`), their coordinate lattices are not.
3. **The recentred-mass induction wiring** — consume the strictly-smaller-mass laws
   (mass `k ≤ m/2` by IFCG39's `powerSector_mass_drop`) at `O'` via
   `zcURLim_eis_value` + the count transport, and sum the (finitely many)
   face/centre contributions into one `ZcURLim` family.

## Axiom fence

Everything here composes landed Lean-core material (IFCG27/29/39); expected
footprint: pure Lean core `{propext, Classical.choice, Quot.sound}` throughout
(the B.42/C.33 cites must NOT occur).  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG43

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf (IsKey keyIsDomain)
open Uniformity.Density.IFCG24 (ZcURLim)
open Uniformity.Density.IFCG27 (adjoinRoot_isDVR adjoinRoot_maximalIdeal_eq
  adjoinRoot_isAdicComplete adjoinRoot_finite_residueField residueCard_adjoinRoot)
open Uniformity.Density.IFCG29 (irreducible_algebraMap_adjoinRoot)
open Uniformity.Density.IFCG39 (eisKey eisKey_monic eisKey_natDegree
  eisKey_irreducible eis_root_pow eis_root_pow_dvd_mk_iff eis_isDomain
  eis_isLocalRing eis_maximalIdeal_eq eis_isDVR eis_map_pow_maximalIdeal
  eis_isAdicComplete eis_finite_residueField eis_residueCard
  devT reassT devT_coeff devT_monic devT_reassT reassT_devT reassT_monic
  devT_sub_root_pow_dvd reassT_sub_pi_pow_dvd)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit -/

section Kit

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Level-`N` class equality IS `ϖ^N`-divisibility of the difference (the quotient
read of the DVR filtration; LocalData's `mem_pow_maximalIdeal_iff` composed with the
quotient extensionality). -/
private theorem res_mk_eq_iff {ϖ : R} (hϖ : Irreducible ϖ) {N : ℕ} {x y : R} :
    Ideal.Quotient.mk ((maximalIdeal R) ^ N) x
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) y
      ↔ ϖ ^ N ∣ x - y := by
  rw [Ideal.Quotient.eq]
  exact mem_pow_maximalIdeal_iff hϖ N _

omit [IsDiscreteValuationRing R] in
/-- `monicPoly` reads its own vector below the top (C109a's idiom, private copy). -/
private theorem monicPoly_coeff_lt {n : ℕ} (a : Fin n → R) {i : ℕ} (hi : i < n) :
    (monicPoly a).coeff i = a ⟨i, hi⟩ := by
  classical
  rw [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ i = n), zero_add, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul_X_pow,
      if_neg (fun hcon => hb (Fin.val_injective hcon.symm))]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

omit [IsDiscreteValuationRing R] in
/-- A monic polynomial of degree `n` is `monicPoly` of its own low coefficient vector
(C53b's idiom, private copy). -/
private theorem monicPoly_coeff_self {n : ℕ} {f : Polynomial R} (hf : f.Monic)
    (hn : f.natDegree = n) : monicPoly (fun i : Fin n => f.coeff i.1) = f := by
  classical
  have hlead : f.coeff n = 1 := by rw [← hn]; exact hf.coeff_natDegree
  refine Polynomial.ext fun m => ?_
  rcases lt_trichotomy m n with h | h | h
  · rw [monicPoly_coeff_lt _ h]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).coeff n = 1 := by
      have h2 := (monicPoly_monic (fun i : Fin n => f.coeff i.1)).coeff_natDegree
      rwa [monicPoly_natDegree] at h2
    rw [h, h1, hlead]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree = n :=
      monicPoly_natDegree _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree < m),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m)]

/-- Class-equal coefficient vectors have `ϖ^N`-divisible monic-block differences at
EVERY slot (top and beyond included: there the difference vanishes). -/
private theorem pow_dvd_monicPoly_sub_coeff {ϖ : R} (hϖ : Irreducible ϖ) {n N : ℕ}
    {a a' : Fin n → R} (h : proj R n N a = proj R n N a') (l : ℕ) :
    ϖ ^ N ∣ (monicPoly a - monicPoly a').coeff l := by
  rw [Polynomial.coeff_sub]
  rcases lt_trichotomy l n with hl | hl | hl
  · rw [monicPoly_coeff_lt a hl, monicPoly_coeff_lt a' hl]
    have hcl : Ideal.Quotient.mk ((maximalIdeal R) ^ N) (a ⟨l, hl⟩)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) (a' ⟨l, hl⟩) :=
      congrFun h ⟨l, hl⟩
    exact (res_mk_eq_iff hϖ).mp hcl
  · subst hl
    have h1 : (monicPoly a).coeff l = 1 := by
      have := (monicPoly_monic a).coeff_natDegree
      rwa [monicPoly_natDegree] at this
    have h2 : (monicPoly a').coeff l = 1 := by
      have := (monicPoly_monic a').coeff_natDegree
      rwa [monicPoly_natDegree] at this
    rw [h1, h2, sub_self]
    exact dvd_zero _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      sub_self]
    exact dvd_zero _

end Kit

/-! ## §1 — LEG 4: the general-face compositum (unramified ∘ Eisenstein) -/

section Compositum

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **THE GENERAL-FACE COMPOSITUM STACK** — the two-step tower under the `xKey`:
the unramified step `O → O₁ = AdjoinRoot φ` (IFCG27's cascade at a residual key `φ`,
residue field `𝔽_{q^{deg φ}}`) followed by the Eisenstein step
`O₁ → O₂ = AdjoinRoot (eisKey π₁ c₁ e')` (IFCG39's cascade, totally ramified of
degree `e'`).  The composite is a COMPLETE DVR with finite residue field of
cardinality `q ^ deg φ` and full-tower ramification `𝔪^K·O₂ = 𝔪₂^{e'·K}` — uniformly
in `q, φ, c₁, e'`, every complete DVR.  (`π₁ = algebraMap π` stays a uniformizer by
IFCG29's `irreducible_algebraMap_adjoinRoot`; the composition is formal exactly
because both cascades were landed instance-shaped.) -/
theorem compositum_recentring_stack {φ : Polynomial O} (hφ : IsKey φ) {π : O}
    (hπ : Irreducible π) [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)]
    {c₁ : AdjoinRoot φ} (hc₁ : IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0)
    {e' : ℕ} (he' : 2 ≤ e') :
    ∃ (_ : IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
      (_ : IsLocalRing (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
      (_ : IsDiscreteValuationRing
        (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
      (_ : Finite (ResidueField
        (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))),
      IsAdicComplete
          (maximalIdeal (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
          (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))
      ∧ residueCard (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))
          = residueCard O ^ φ.natDegree
      ∧ ∀ K : ℕ,
          ((maximalIdeal O) ^ K).map
            ((algebraMap (AdjoinRoot φ)
                (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))).comp
              (algebraMap O (AdjoinRoot φ)))
          = (maximalIdeal
              (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))) ^ (e' * K) := by
  -- the unramified stage's instance supply
  haveI hAC₁ : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI hFin₁ : Finite (ResidueField (AdjoinRoot φ)) :=
    adjoinRoot_finite_residueField hφ
  -- the uniformizer persists across the unramified stage
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  -- the Eisenstein stage's cascade at `O₁`
  haveI i1 : IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) :=
    eis_isDomain hπ₁ hc₁ he'
  haveI i2 : IsLocalRing (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) :=
    eis_isLocalRing hπ₁ hc₁ he'
  haveI i3 : IsDiscreteValuationRing
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) :=
    eis_isDVR hπ₁ hc₁ he'
  haveI i4 : Finite (ResidueField
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))) :=
    eis_finite_residueField hπ₁ hc₁ he'
  refine ⟨i1, i2, i3, i4, eis_isAdicComplete hπ₁ hc₁ he', ?_, ?_⟩
  · -- the residue cardinality composes: totally ramified over unramified
    rw [eis_residueCard hπ₁ hc₁ he', residueCard_adjoinRoot hφ]
  · -- full-tower ramification: `𝔪^K·O₂ = (𝔪₁^K)·O₂ = 𝔪₂^{e'·K}`
    intro K
    rw [← Ideal.map_map, Ideal.map_pow, ← adjoinRoot_maximalIdeal_eq hφ,
      eis_map_pow_maximalIdeal hπ₁ hc₁ he' K]

end Compositum

/-! ## §2 — LEG 2: the cell/count transport (the dev-transform on the finite boxes) -/

section CellTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {π c : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π c e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]
  [Finite (ResidueField O)] [Finite (ResidueField (AdjoinRoot (eisKey π c e')))]

/-- ★ **The root is a uniformizer of the recentring ring** (the coordinate of every
recentred box; `𝔪' = (α)` read through the DVR dictionary). -/
theorem eis_root_irreducible (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') : Irreducible (AdjoinRoot.root (eisKey π c e')) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact eis_maximalIdeal_eq hπ hc he'

/-- **The transform vector**: the `O'`-coordinates of the dev transform of the monic
block with coefficient vector `a`. -/
def devVec (π c : O) (e' k : ℕ) (a : Fin (e' * k) → O) :
    Fin k → AdjoinRoot (eisKey π c e') :=
  fun j => (devT (eisKey π c e') k (monicPoly a)).coeff j.1

/-- **The reassembly vector**: the `O`-coordinates of the reassembled block of the
monic `O'`-polynomial with coefficient vector `b`. -/
def reassVec (π c : O) (he' : 0 < e') (k : ℕ)
    (b : Fin k → AdjoinRoot (eisKey π c e')) : Fin (e' * k) → O :=
  fun i => (reassT (eisKey π c e') (eisKey_monic he') k (monicPoly b)).coeff i.1

/-- Level-`N` classes transport to level-`e'·N` classes (well-definedness of the
transport on cells: IFCG39's outbound level exactness at every slot). -/
private theorem devVec_congr (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') {k N : ℕ} {a a' : Fin (e' * k) → O}
    (h : proj O (e' * k) N a = proj O (e' * k) N a') :
    proj (AdjoinRoot (eisKey π c e')) k (e' * N) (devVec π c e' k a)
      = proj (AdjoinRoot (eisKey π c e')) k (e' * N) (devVec π c e' k a') := by
  have he'' : 0 < e' := Nat.zero_lt_two.trans_le he'
  have hα : Irreducible (AdjoinRoot.root (eisKey π c e')) :=
    eis_root_irreducible hπ hc he'
  funext j
  have hdvd := devT_sub_root_pow_dvd (k := k) hπ hc he'' (N := N)
    (f := monicPoly a) (f' := monicPoly a')
    (fun l => pow_dvd_monicPoly_sub_coeff hπ h l) (j := j.1) j.isLt.le
  rw [Polynomial.coeff_sub] at hdvd
  exact (res_mk_eq_iff hα).mpr hdvd

/-- Level-`e'·N` classes transport back to level-`N` classes (well-definedness of the
inverse transport: IFCG39's inbound level exactness). -/
private theorem reassVec_congr (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') {k N : ℕ} {b b' : Fin k → AdjoinRoot (eisKey π c e')}
    (h : proj (AdjoinRoot (eisKey π c e')) k (e' * N) b
        = proj (AdjoinRoot (eisKey π c e')) k (e' * N) b') :
    proj O (e' * k) N (reassVec π c (Nat.zero_lt_two.trans_le he') k b)
      = proj O (e' * k) N (reassVec π c (Nat.zero_lt_two.trans_le he') k b') := by
  have he'' : 0 < e' := Nat.zero_lt_two.trans_le he'
  have hα : Irreducible (AdjoinRoot.root (eisKey π c e')) :=
    eis_root_irreducible hπ hc he'
  funext i
  have hdvd := reassT_sub_pi_pow_dvd (k := k) hπ hc he'' (N := N)
    (G := monicPoly b) (G' := monicPoly b')
    (fun j => pow_dvd_monicPoly_sub_coeff hα h j) i.1
  rw [Polynomial.coeff_sub] at hdvd
  exact (res_mk_eq_iff hπ).mpr hdvd

/-- The exact round trip on canonical lifts: reassembling the transform recovers the
block vector ON THE NOSE (IFCG39's `reassT_devT` read coefficientwise). -/
private theorem reassVec_devVec (he' : 2 ≤ e') (k : ℕ) (a : Fin (e' * k) → O) :
    reassVec π c (Nat.zero_lt_two.trans_le he') k (devVec π c e' k a) = a := by
  have he'' : 0 < e' := Nat.zero_lt_two.trans_le he'
  have hm : (eisKey π c e').Monic := eisKey_monic (Nat.zero_lt_two.trans_le he')
  have hD : 0 < (eisKey π c e').natDegree := by rw [eisKey_natDegree he'']; omega
  have hdeg : (monicPoly a).natDegree = (eisKey π c e').natDegree * k := by
    rw [monicPoly_natDegree, eisKey_natDegree he'']
  have hmon := devT_monic (φ := eisKey π c e') (k := k) hm hD (monicPoly_monic a) hdeg
  have hfun : monicPoly (devVec π c e' k a) = devT (eisKey π c e') k (monicPoly a) :=
    monicPoly_coeff_self hmon.1 hmon.2
  have hlt : (monicPoly a).natDegree < (k + 1) * (eisKey π c e').natDegree := by
    rw [monicPoly_natDegree, eisKey_natDegree he'', Nat.mul_comm e' k, Nat.add_mul,
      Nat.one_mul]
    generalize k * e' = A
    omega
  funext i
  show (reassT (eisKey π c e') (eisKey_monic (Nat.zero_lt_two.trans_le he')) k
      (monicPoly (devVec π c e' k a))).coeff i.1 = a i
  rw [hfun, reassT_devT hm hD hlt]
  exact monicPoly_coeff_lt a i.isLt

/-- The exact round trip on canonical lifts, inbound: transforming the reassembly
recovers the `O'`-vector ON THE NOSE (IFCG39's `devT_reassT`). -/
private theorem devVec_reassVec (he' : 2 ≤ e') (k : ℕ)
    (b : Fin k → AdjoinRoot (eisKey π c e')) :
    devVec π c e' k (reassVec π c (Nat.zero_lt_two.trans_le he') k b) = b := by
  have he'' : 0 < e' := Nat.zero_lt_two.trans_le he'
  have hm : (eisKey π c e').Monic := eisKey_monic (Nat.zero_lt_two.trans_le he')
  have hD : 0 < (eisKey π c e').natDegree := by rw [eisKey_natDegree he'']; omega
  have hre := reassT_monic (φ := eisKey π c e') hm hD (monicPoly_monic b)
    (monicPoly_natDegree b)
  have hfun : monicPoly (reassVec π c (Nat.zero_lt_two.trans_le he') k b)
      = reassT (eisKey π c e') hm k (monicPoly b) :=
    monicPoly_coeff_self hre.1 (by rw [hre.2, eisKey_natDegree he''])
  funext j
  show (devT (eisKey π c e') k
      (monicPoly (reassVec π c (Nat.zero_lt_two.trans_le he') k b))).coeff j.1 = b j
  rw [hfun, devT_reassT hm hD (le_of_eq (monicPoly_natDegree b))]
  exact monicPoly_coeff_lt b j.isLt

/-- ★★ **THE CELL TRANSPORT** — the dev-transform bijection DESCENDS to the finite
coefficient boxes: level-`N` classes of monic degree-`e'·k` blocks over `O` correspond
exactly to level-`e'·N` classes of monic degree-`k` blocks over the recentring ring
`O' = AdjoinRoot (eisKey π c e')` — the finite level scales by exactly the
ramification index (`fScale = e'`), uniformly in `q, e', k, N`, every complete DVR.
Computed on lifts by `cellTransport_apply` / `cellTransport_symm_apply`. -/
noncomputable def cellTransport (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e') (k N : ℕ) :
    Coeff O (e' * k) N ≃ Coeff (AdjoinRoot (eisKey π c e')) k (e' * N) where
  toFun x := proj (AdjoinRoot (eisKey π c e')) k (e' * N)
    (devVec π c e' k (proj_surjective O (e' * k) N x).choose)
  invFun y := proj O (e' * k) N
    (reassVec π c (Nat.zero_lt_two.trans_le he') k
      (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) y).choose)
  left_inv := fun x => by
    have ha : proj O (e' * k) N (proj_surjective O (e' * k) N x).choose = x :=
      (proj_surjective O (e' * k) N x).choose_spec
    have hb : proj (AdjoinRoot (eisKey π c e')) k (e' * N)
        (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N)
          (proj (AdjoinRoot (eisKey π c e')) k (e' * N)
            (devVec π c e' k (proj_surjective O (e' * k) N x).choose))).choose
        = proj (AdjoinRoot (eisKey π c e')) k (e' * N)
            (devVec π c e' k (proj_surjective O (e' * k) N x).choose) :=
      (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) _).choose_spec
    have h1 := reassVec_congr hπ hc he' hb
    rw [reassVec_devVec he' k _] at h1
    exact h1.trans ha
  right_inv := fun y => by
    have hb : proj (AdjoinRoot (eisKey π c e')) k (e' * N)
        (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) y).choose = y :=
      (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) y).choose_spec
    have ha : proj O (e' * k) N (proj_surjective O (e' * k) N
        (proj O (e' * k) N (reassVec π c (Nat.zero_lt_two.trans_le he') k
          (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) y).choose))).choose
        = proj O (e' * k) N (reassVec π c (Nat.zero_lt_two.trans_le he') k
            (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N) y).choose) :=
      (proj_surjective O (e' * k) N _).choose_spec
    have h1 := devVec_congr hπ hc he' ha
    rw [devVec_reassVec he' k _] at h1
    exact h1.trans hb

/-- ★ The transport is computed on ANY lift by the transform vector (the interface
consumers read cells through). -/
theorem cellTransport_apply (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    (he' : 2 ≤ e') (k N : ℕ) (a : Fin (e' * k) → O) :
    cellTransport hπ hc he' k N (proj O (e' * k) N a)
      = proj (AdjoinRoot (eisKey π c e')) k (e' * N) (devVec π c e' k a) :=
  devVec_congr hπ hc he'
    (proj_surjective O (e' * k) N (proj O (e' * k) N a)).choose_spec

/-- ★ The inverse transport is computed on ANY lift by the reassembly vector. -/
theorem cellTransport_symm_apply (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e') (k N : ℕ)
    (b : Fin k → AdjoinRoot (eisKey π c e')) :
    (cellTransport hπ hc he' k N).symm
        (proj (AdjoinRoot (eisKey π c e')) k (e' * N) b)
      = proj O (e' * k) N (reassVec π c (Nat.zero_lt_two.trans_le he') k b) :=
  reassVec_congr hπ hc he'
    (proj_surjective (AdjoinRoot (eisKey π c e')) k (e' * N)
      (proj (AdjoinRoot (eisKey π c e')) k (e' * N) b)).choose_spec

/-- ★ **THE COUNT TRANSPORT**: the transport carries every cell set to a set of the
SAME cardinality — the counting content of "the dev-transform carries cells to
cells". -/
theorem cellTransport_card_image (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e') (k N : ℕ)
    (S : Set (Coeff O (e' * k) N)) :
    Nat.card ((cellTransport hπ hc he' k N) '' S) = Nat.card S :=
  Nat.card_image_of_injective (cellTransport hπ hc he' k N).injective S

/-- ★ The recentred box is `𝔪'`-adic at the SAME `q`: the level-`e'·N` box over `O'`
counts `q^(k·e'·N)` — the eScale bookkeeping `(e, f) ↦ (e'·e, f)` leaves the
cardinality base unchanged. -/
theorem card_coeff_eis
    (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0) (he' : 2 ≤ e')
    (k N : ℕ) :
    Nat.card (Coeff (AdjoinRoot (eisKey π c e')) k (e' * N))
      = residueCard O ^ (k * (e' * N)) := by
  rw [card_coeff, eis_residueCard hπ hc he']

end CellTransport

/-! ## §3 — LEG 3: the `ZcURLim` closure instruments -/

section Closure

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The general recentring stack** — every `(c, e')` with `c` residually nonzero
and `e' ≥ 2`: the recentring ring is a complete DVR with finite residue field of
UNCHANGED cardinality, hence a LEGAL instantiation point for every ∀-DVR law family
at the SAME `q`.  (Generalizes IFCG39 §6's dd `(2, 2)` instance point to the whole
power sector.) -/
theorem eis_recentring_stack (π c : O) (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) {e' : ℕ} (he' : 2 ≤ e') :
    ∃ (_ : IsDomain (AdjoinRoot (eisKey π c e')))
      (_ : IsLocalRing (AdjoinRoot (eisKey π c e')))
      (_ : IsDiscreteValuationRing (AdjoinRoot (eisKey π c e')))
      (_ : Finite (ResidueField (AdjoinRoot (eisKey π c e')))),
      IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π c e')))
          (AdjoinRoot (eisKey π c e'))
      ∧ residueCard (AdjoinRoot (eisKey π c e')) = residueCard O := by
  haveI i1 : IsDomain (AdjoinRoot (eisKey π c e')) := eis_isDomain hπ hc he'
  haveI i2 : IsLocalRing (AdjoinRoot (eisKey π c e')) := eis_isLocalRing hπ hc he'
  haveI i3 : IsDiscreteValuationRing (AdjoinRoot (eisKey π c e')) :=
    eis_isDVR hπ hc he'
  haveI i4 : Finite (ResidueField (AdjoinRoot (eisKey π c e'))) :=
    eis_finite_residueField hπ hc he'
  exact ⟨i1, i2, i3, i4, eis_isAdicComplete hπ hc he', eis_residueCard hπ hc he'⟩

end Closure

section ZcClosure

/-- ★★ **THE `ZcURLim` CLOSURE CONSUMPTION** — instantiating any uniform law family
at any Eisenstein recentring ring keeps the family's OWN rational pair, evaluated at
the ORIGINAL `q`: the witness `(n, d)` of `ZcURLim F` satisfies, at every complete
DVR `O`, BOTH the base clause (F's limit at `O` is `n(q)/d(q)`, the `ZcURLim` body)
AND the recentred clause — for every `π, c, e'` (with `c` residually nonzero,
`e' ≥ 2`) and every uniformizer `π'` of `O' = AdjoinRoot (eisKey π c e')`, the limit
of `F O' π'` is the SAME value `n(q)/d(q)`.  This is what lets the face-summed
recentred counts stay inside one rational family: `q' = q` pays exactly here
(smaller-mass laws instantiated at `O'` return values at the base `q`). -/
theorem zcURLim_eis_value
    {F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hF : ZcURLim F) :
    ∃ n d : Polynomial ℚ, d ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        (d.eval ((residueCard O : ℕ) : ℚ) ≠ 0
          ∧ ∀ π : O, Irreducible π →
              Filter.Tendsto (F O π) Filter.atTop
                (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                  / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)))
        ∧ ∀ (π c : O), Irreducible π → IsLocalRing.residue O c ≠ 0 →
            ∀ e' : ℕ, 2 ≤ e' →
            ∀ [IsDomain (AdjoinRoot (eisKey π c e'))]
              [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))]
              [IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π c e')))
                (AdjoinRoot (eisKey π c e'))]
              [Finite (ResidueField (AdjoinRoot (eisKey π c e')))],
              ∀ π' : AdjoinRoot (eisKey π c e'), Irreducible π' →
                Filter.Tendsto (F (AdjoinRoot (eisKey π c e')) π') Filter.atTop
                  (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                    / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) := by
  obtain ⟨n, d, hd, hval⟩ := hF
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  refine ⟨hval O, ?_⟩
  intro π c hπ hc e' he' i1 i2 i3 i4 π' hπ'
  have h1 := (hval (AdjoinRoot (eisKey π c e'))).2 π' hπ'
  have h2 : residueCard (AdjoinRoot (eisKey π c e')) = residueCard O :=
    eis_residueCard hπ hc he'
  rwa [h2] at h1

end ZcClosure

/-! ## §4 — LEG 1: the residual-box transfer criterion (C110's mechanism at `e' ≥ 2`)

The support layer: the recentred key is the constant shift of `X^{e'}` (so C110's
binomial `shiftDev` rearrangement applies verbatim — replicated privates below), and
the `X^{e'}`-adic development reads coefficient BLOCKS. -/

section TransferSupport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

open Uniformity.Density.Leaf

/-- Normalization pin: the recentring key at centre `z` IS `X^{e'} − C (z·π)`
(IFCG39's `eisKey_dd` idiom at every `e'`). -/
theorem eisKey_neg (π z : O) (e' : ℕ) :
    eisKey π (-z) e' = Polynomial.X ^ e' - Polynomial.C (z * π) := by
  rw [eisKey, neg_mul, map_neg, ← sub_eq_add_neg]

/-! ### C110's shift stack, replicated (private) -/

private theorem degree_C_lt_of_pos {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) :
    (Polynomial.C c : Polynomial O).degree < φ.degree := by
  refine lt_of_le_of_lt Polynomial.degree_C_le ?_
  rw [Polynomial.degree_eq_natDegree hφ.ne_zero]
  exact_mod_cast hd

private theorem monic_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (c : O) : (φ - Polynomial.C c).Monic :=
  hφ.sub_of_left (degree_C_lt_of_pos hφ hd c)

private theorem degree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) : (φ - Polynomial.C c).degree = φ.degree := by
  rw [sub_eq_add_neg]
  exact Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_neg]; exact degree_C_lt_of_pos hφ hd c)

private theorem natDegree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) : (φ - Polynomial.C c).natDegree = φ.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (degree_sub_C_eq hφ hd c)

/-- The recentred development coefficient: the binomial rearrangement of the `φ`-adic
development when the key moves from `φ` to `φ − c` (C110's private, replicated). -/
private noncomputable def shiftDev (φ : Polynomial O) (c : O) (f : Polynomial O)
    (n j : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.Ico j n, Polynomial.C (c ^ (i - j) * (i.choose j : O)) * dev φ f i

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem degree_C_mul_le' (x : O) (p : Polynomial O) :
    (Polynomial.C x * p).degree ≤ p.degree := by
  refine le_trans (Polynomial.degree_mul_le _ _) ?_
  simpa using add_le_add_left (Polynomial.degree_C_le (a := x)) p.degree

private theorem degree_shiftDev_lt {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) (f : Polynomial O) (n j : ℕ) :
    (shiftDev φ c f n j).degree < φ.degree := by
  have hbot : (⊥ : WithBot ℕ) < φ.degree := by
    rw [Polynomial.degree_eq_natDegree hφ.ne_zero]; exact WithBot.bot_lt_coe _
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 ?_)
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_le' _ _) (degree_dev_lt hφ hd f i)

private theorem dev_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (c : O) (f : Polynomial O) {n : ℕ} (hf : f.natDegree < n * φ.natDegree) (j : ℕ)
    (hj : j < n) : dev (φ - Polynomial.C c) f j = shiftDev φ c f n j := by
  classical
  set ψ : Polynomial O := φ - Polynomial.C c with hψdef
  have hψ : ψ.Monic := monic_sub_C hφ hd c
  have hψd : ψ.natDegree = φ.natDegree := natDegree_sub_C_eq hφ hd c
  have hψdeg : ψ.degree = φ.degree := degree_sub_C_eq hφ hd c
  have hφeq : ψ + Polynomial.C c = φ := by rw [hψdef]; ring
  have hdeg : ∀ t, (shiftDev φ c f n t).degree < ψ.degree := by
    intro t; rw [hψdeg]; exact degree_shiftDev_lt hφ hd c f n t
  have hsum : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t = f := by
    have h1 : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t
        = ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t := by
      rw [Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun t _ => by rw [shiftDev, Finset.sum_mul]
    have h2 : ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = ∑ i ∈ Finset.Ico 0 n, ∑ t ∈ Finset.Ico 0 (i + 1),
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t :=
      Finset.sum_Ico_Ico_comm 0 n
        (fun t i => Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t)
    have h3 : ∀ i, ∑ t ∈ Finset.Ico 0 (i + 1),
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = dev φ f i * φ ^ i := by
      intro i
      rw [← hφeq, add_pow, Finset.mul_sum, ← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.C_mul, map_pow, Polynomial.C_eq_natCast]
      ring
    rw [h1, h2, Finset.sum_congr rfl fun i _ => h3 i, ← Finset.range_eq_Ico]
    exact sum_dev_eq hφ hd f hf
  exact (dev_unique hψ (by rw [hψd]; exact hd) hdeg hsum j hj).symm

/-! ### the `X^{e'}`-adic development reads coefficient blocks -/

variable {e' : ℕ}

private theorem blk_coeff (f : Polynomial O) (t j : ℕ) :
    (∑ i ∈ Finset.range e',
        Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i).coeff j
      = if j < e' then f.coeff (e' * t + j) else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range e') j (fun i => f.coeff (e' * t + i))]
  simp [Finset.mem_range]

private theorem blk_degree_lt (_he' : 0 < e') (f : Polynomial O) (t : ℕ) :
    (∑ i ∈ Finset.range e',
        Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i).degree
      < ((e' : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe e')]
  intro i hi
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Finset.mem_range.mp hi

private theorem sum_blk_eq (he' : 0 < e') {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e') :
    ∑ t ∈ Finset.range n,
        (∑ i ∈ Finset.range e',
          Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i)
          * (Polynomial.X ^ e' : Polynomial O) ^ t = f := by
  classical
  refine Polynomial.ext fun m => ?_
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ t, ((∑ i ∈ Finset.range e',
        Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i)
        * (Polynomial.X ^ e' : Polynomial O) ^ t).coeff m
      = if e' * t ≤ m ∧ m - e' * t < e' then f.coeff (e' * t + (m - e' * t)) else 0 := by
    intro t
    rw [← pow_mul, Polynomial.coeff_mul_X_pow']
    by_cases h1 : e' * t ≤ m
    · rw [if_pos h1, blk_coeff]
      by_cases h2 : m - e' * t < e'
      · rw [if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_neg h2, if_neg (fun hcon => h2 hcon.2)]
    · rw [if_neg h1, if_neg (fun hcon => h1 hcon.1)]
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  have hdm := Nat.div_add_mod m e'
  have hmod : m % e' < e' := Nat.mod_lt m he'
  by_cases hm : m / e' < n
  · rw [Finset.sum_eq_single (m / e')]
    · have h1 : e' * (m / e') ≤ m := by
        generalize hA : e' * (m / e') = A at hdm
        omega
      have h2 : m - e' * (m / e') < e' := by
        generalize hA : e' * (m / e') = A at hdm
        omega
      rw [if_pos ⟨h1, h2⟩]
      refine congrArg f.coeff ?_
      generalize hA : e' * (m / e') = A at hdm ⊢
      omega
    · intro b _ hb
      rw [if_neg]
      rintro ⟨hb1, hb2⟩
      have hb1' : b * e' ≤ m := by rwa [Nat.mul_comm] at hb1
      have hb2' : m < (b + 1) * e' := by
        have h4 : m < e' * b + e' := by
          generalize hB : e' * b = B at hb1 hb2
          omega
        calc m < e' * b + e' := h4
          _ = (b + 1) * e' := by ring
      exact hb (Nat.div_eq_of_lt_le hb1' hb2').symm
    · intro hcon
      exact absurd (Finset.mem_range.mpr hm) hcon
  · rw [Finset.sum_eq_zero, eq_comm]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hf ?_)
      have h1 : n ≤ m / e' := by omega
      have h2 : n * e' ≤ (m / e') * e' := Nat.mul_le_mul_right e' h1
      have h3 : (m / e') * e' ≤ m := Nat.div_mul_le_self m e'
      omega
    · intro t ht
      rw [if_neg]
      rintro ⟨ht1, ht2⟩
      have htn : t < n := Finset.mem_range.mp ht
      have ht1' : t * e' ≤ m := by rwa [Nat.mul_comm] at ht1
      have ht2' : m < (t + 1) * e' := by
        have h4 : m < e' * t + e' := by
          generalize hB : e' * t = B at ht1 ht2
          omega
        calc m < e' * t + e' := h4
          _ = (t + 1) * e' := by ring
      have hdiv : m / e' = t := Nat.div_eq_of_lt_le ht1' ht2'
      omega

/-- **The `X^{e'}`-adic digits are the coefficient blocks**: the development at the
unshifted lattice key reads `f`'s coefficients in blocks of width `e'`. -/
private theorem dev_X_pow_blk (he' : 0 < e') {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e') {t : ℕ} (ht : t < n) :
    dev (Polynomial.X ^ e' : Polynomial O) f t
      = ∑ i ∈ Finset.range e',
          Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i := by
  have hmon : (Polynomial.X ^ e' : Polynomial O).Monic := Polynomial.monic_X_pow e'
  have hd : 0 < (Polynomial.X ^ e' : Polynomial O).natDegree := by
    rw [Polynomial.natDegree_X_pow]; exact he'
  refine (dev_unique hmon hd (a := fun t => ∑ i ∈ Finset.range e',
      Polynomial.C (f.coeff (e' * t + i)) * Polynomial.X ^ i) (fun j => ?_)
      (sum_blk_eq he' hf) t ht).symm
  rw [Polynomial.degree_X_pow]
  exact blk_degree_lt he' f j

private theorem dev_X_pow_coeff (he' : 0 < e') {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e') {t : ℕ} (ht : t < n) (i : ℕ) :
    (dev (Polynomial.X ^ e' : Polynomial O) f t).coeff i
      = if i < e' then f.coeff (e' * t + i) else 0 := by
  rw [dev_X_pow_blk he' hf ht, blk_coeff]

/-! ### the two shift readings between `X^{e'}` and the recentred key -/

/-- The recentred digits as binomial combinations of the coefficient-block digits. -/
private theorem dev_eisKey_eq (he' : 0 < e') {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e') {t : ℕ} (ht : t < n) (z : O) :
    dev (eisKey π (-z) e') f t
      = ∑ s ∈ Finset.Ico t n,
          Polynomial.C ((z * π) ^ (s - t) * (s.choose t : O))
            * dev (Polynomial.X ^ e' : Polynomial O) f s := by
  have hmon : (Polynomial.X ^ e' : Polynomial O).Monic := Polynomial.monic_X_pow e'
  have hd : 0 < (Polynomial.X ^ e' : Polynomial O).natDegree := by
    rw [Polynomial.natDegree_X_pow]; exact he'
  rw [eisKey_neg π z e']
  exact dev_sub_C hmon hd (z * π) f
    (by rw [Polynomial.natDegree_X_pow]; exact hf) t ht

/-- The coefficient-block digits as binomial combinations of the recentred digits
(the inverse shift). -/
private theorem dev_X_pow_eq (he' : 0 < e') {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e') {t : ℕ} (ht : t < n) (z : O) :
    dev (Polynomial.X ^ e' : Polynomial O) f t
      = ∑ s ∈ Finset.Ico t n,
          Polynomial.C ((-(z * π)) ^ (s - t) * (s.choose t : O))
            * dev (eisKey π (-z) e') f s := by
  have hkm : (eisKey π (-z) e').Monic := eisKey_monic he'
  have hkd : 0 < (eisKey π (-z) e').natDegree := by
    rw [eisKey_natDegree he']; exact he'
  have hkey : (Polynomial.X ^ e' : Polynomial O)
      = eisKey π (-z) e' - Polynomial.C (-(z * π)) := by
    rw [eisKey_neg π z e', map_neg, sub_neg_eq_add, sub_add_cancel]
  rw [hkey]
  exact dev_sub_C hkm hkd (-(z * π)) f
    (by rw [eisKey_natDegree he']; exact hf) t ht

/-! ### the digit kit: sums, exponents, and the binomial vanishing -/

private theorem digAt_zero' (hπ : Irreducible π) (K : ℕ) : digAt π K (0 : O) = 0 := by
  rw [digAt_eq hπ (mul_zero (π ^ K)).symm]
  exact map_zero _

/-- The digit is additive over any finite sum of `π^K`-divisible terms. -/
private theorem digAt_sum (hπ : Irreducible π) {K : ℕ} (s : Finset ℕ) (g : ℕ → O)
    (h : ∀ a ∈ s, π ^ K ∣ g a) :
    digAt π K (∑ a ∈ s, g a) = ∑ a ∈ s, digAt π K (g a) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, digAt_zero' hπ]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      digAt_add hπ (h a (Finset.mem_cons_self a s))
        (Finset.dvd_sum fun b hb => h b (Finset.mem_cons_of_mem hb)),
      ih (fun b hb => h b (Finset.mem_cons_of_mem hb))]

/-- The purity exponent at the slot `e'·s + i` (`s < k`, `i < e'`) is `k − s`. -/
private theorem pure_exp_eq (he'' : 0 < e') {k s i : ℕ} (hs : s < k) (hi : i < e') :
    (e' * k - (e' * s + i) + (e' - 1)) / e' = k - s := by
  obtain ⟨d, hd⟩ : ∃ d, k - s = d + 1 := ⟨k - s - 1, by omega⟩
  have hks : k = s + (d + 1) := by omega
  subst hks
  have h1 : e' * (s + (d + 1)) - (e' * s + i) + (e' - 1)
      = e' * (d + 1) + (e' - 1 - i) := by
    rw [Nat.mul_add]
    generalize e' * s = A
    generalize hB : e' * (d + 1) = B
    have hB' : e' ≤ B := by
      rw [← hB]
      exact Nat.le_mul_of_pos_right e' (by omega)
    omega
  rw [h1, Nat.mul_add_div he'', Nat.div_eq_of_lt (by omega : e' - 1 - i < e')]
  omega

/-- The raw-purity supply at block slots: `π^{k−s} ∣ G.coeff (e'·s + i)`. -/
private theorem pure_dvd {k : ℕ} {G : Polynomial O} (he'' : 0 < e')
    (hpure : ∀ j, j < e' * k → π ^ ((e' * k - j + (e' - 1)) / e') ∣ G.coeff j)
    {s i : ℕ} (hs : s < k) (hi : i < e') :
    π ^ (k - s) ∣ G.coeff (e' * s + i) := by
  have hlt : e' * s + i < e' * k := by
    have h3 : e' * (s + 1) ≤ e' * k := Nat.mul_le_mul_left e' (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h3
    generalize e' * s = A at h3 ⊢
    omega
  have h1 := hpure (e' * s + i) hlt
  rwa [pure_exp_eq he'' hs hi] at h1

/-- The lattice exponent of the deep box at slot `0` is `k − t + 1`. -/
private theorem lat_exp_zero (he'' : 0 < e') (k t : ℕ) :
    (e' * (k - t) + 1 + e' - 1 - 0) / e' = k - t + 1 := by
  have h1 : e' * (k - t) + 1 + e' - 1 - 0 = e' * (k - t) + e' := by
    generalize e' * (k - t) = A
    omega
  rw [h1, Nat.mul_add_div he'', Nat.div_self he'']

/-- The lattice exponent of the deep box at slots `1 ≤ i < e'` is `k − t`. -/
private theorem lat_exp_pos (he'' : 0 < e') (k t : ℕ) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i < e') :
    (e' * (k - t) + 1 + e' - 1 - i) / e' = k - t := by
  have h1 : e' * (k - t) + 1 + e' - 1 - i = e' * (k - t) + (e' - i) := by
    generalize e' * (k - t) = A
    omega
  rw [h1, Nat.mul_add_div he'', Nat.div_eq_of_lt (by omega : e' - i < e'), Nat.add_zero]

/-- **The binomial vanishing** (the "k lower digit combinations vanish" identity):
`Σ_{t ≤ s ≤ k} w^{s−t}·C(s,t)·C(k,s)·(−w)^{k−s} = C(k,t)·(w − w)^{k−t} = 0` for
`t < k` — the trinomial revision composed with the alternating binomial sum. -/
private theorem binom_vanish {F : Type*} [CommRing F] (w : F) {t k : ℕ} (ht : t < k) :
    ∑ s ∈ Finset.Ico t (k + 1),
        w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s) = 0 := by
  have hstep : ∀ s ∈ Finset.Ico t (k + 1),
      w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s)
        = (k.choose t : F) * (((k - t).choose (s - t) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    have hch : k.choose s * s.choose t = k.choose t * (k - t).choose (s - t) :=
      Nat.choose_mul (by omega : t ≤ s)
    have hexp : k - s = k - t - (s - t) := by omega
    calc w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s)
        = ((k.choose s * s.choose t : ℕ) : F) * (w ^ (s - t) * (-w) ^ (k - s)) := by
          push_cast
          ring
      _ = ((k.choose t * (k - t).choose (s - t) : ℕ) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t))) := by rw [hch, hexp]
      _ = (k.choose t : F) * (((k - t).choose (s - t) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))) := by
          push_cast
          ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hpow : (w + -w) ^ (k - t) = ∑ j ∈ Finset.range (k - t + 1),
      ((k - t).choose j : F) * (w ^ j * (-w) ^ (k - t - j)) := by
    rw [add_pow]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hreindex : ∑ s ∈ Finset.Ico t (k + 1),
      ((k - t).choose (s - t) : F) * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))
        = ∑ j ∈ Finset.range (k - t + 1),
            ((k - t).choose j : F) * (w ^ j * (-w) ^ (k - t - j)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hr : k + 1 - t = k - t + 1 := by omega
    rw [hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.add_sub_cancel_left]
  rw [hreindex, ← hpow, add_neg_cancel, zero_pow (by omega : k - t ≠ 0), mul_zero]

/-! ### the two directions of the criterion -/

/-- **Digits → box** (the recentred `k`-th power residual pushes the transform into
the deep box): if the lattice digits of `G` read `(X − z̄)^k`, every recentred
development coefficient clears the side line strictly — the vanishing of the `k`
lower digit combinations (the binomial identity) pays the `+1`. -/
private theorem box_of_digits (hπ : Irreducible π) {z : O}
    (hz : IsLocalRing.residue O z ≠ 0) {k : ℕ} (he' : 2 ≤ e') {G : Polynomial O}
    (hG : G.Monic) (hGdeg : G.natDegree = e' * k)
    (hpure : ∀ j, j < e' * k → π ^ ((e' * k - j + (e' - 1)) / e') ∣ G.coeff j)
    (hdig : ∀ t, t < k → digAt π (k - t) (G.coeff (e' * t))
        = (k.choose t : IsLocalRing.ResidueField O)
            * (- IsLocalRing.residue O z) ^ (k - t))
    {t : ℕ} (ht : t < k) :
    (AdjoinRoot.root (eisKey π (-z) e')) ^ (e' * (k - t) + 1)
      ∣ AdjoinRoot.mk (eisKey π (-z) e') (dev (eisKey π (-z) e') G t) := by
  have he'' : 0 < e' := by omega
  have hcneg : IsLocalRing.residue O (-z) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact hz
  have hGdeg' : G.natDegree < (k + 1) * e' := by
    rw [hGdeg]
    calc e' * k < e' * k + e' := by omega
      _ = (k + 1) * e' := by ring
  have hGtop : G.coeff (e' * k) = 1 := by
    rw [← hGdeg]
    exact hG.coeff_natDegree
  have hdevdeg : (dev (eisKey π (-z) e') G t).degree < ((e' : ℕ) : WithBot ℕ) := by
    have h1 := degree_dev_lt (eisKey_monic (π := π) (c := -z) he'')
      (by rw [eisKey_natDegree he'']; exact he'') G t
    rwa [Polynomial.degree_eq_natDegree (eisKey_monic he'').ne_zero,
      eisKey_natDegree he''] at h1
  rw [eis_root_pow_dvd_mk_iff hπ hcneg he'' hdevdeg]
  intro i hi
  rw [dev_eisKey_eq he'' hGdeg' (by omega : t < k + 1) z, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hread : ∀ s, s < k + 1 →
      (dev (Polynomial.X ^ e' : Polynomial O) G s).coeff i = G.coeff (e' * s + i) := by
    intro s hs2
    rw [dev_X_pow_coeff he'' hGdeg' hs2 i, if_pos hi]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- slot 0: the digit-combination vanishing lifts the divisibility by one
    subst hi0
    rw [lat_exp_zero he'' k t]
    have hsum : ∑ s ∈ Finset.Ico t (k + 1),
        (z * π) ^ (s - t) * (s.choose t : O)
          * (dev (Polynomial.X ^ e' : Polynomial O) G s).coeff 0
        = ∑ s ∈ Finset.Ico t (k + 1),
            (z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      rw [hread s hs2, Nat.add_zero]
    rw [hsum]
    -- the uniform digit values and π-power supply at every `s ≤ k`
    have hdig' : ∀ s, t ≤ s → s < k + 1 →
        digAt π (k - s) (G.coeff (e' * s))
          = (k.choose s : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O z) ^ (k - s) := by
      intro s hs1 hs2
      rcases Nat.lt_or_ge s k with hsk | hsk
      · exact hdig s hsk
      · have hsk' : s = k := by omega
        subst hsk'
        rw [Nat.sub_self, digAt_zero, hGtop, map_one, Nat.choose_self,
          Nat.cast_one, pow_zero, mul_one]
    have hdvd : ∀ s, s < k + 1 → π ^ (k - s) ∣ G.coeff (e' * s) := by
      intro s hs2
      rcases Nat.lt_or_ge s k with hsk | hsk
      · have h1 := pure_dvd he'' hpure hsk he''
        rwa [Nat.add_zero] at h1
      · have hsk' : s = k := by omega
        subst hsk'
        rw [Nat.sub_self, pow_zero]
        exact one_dvd _
    -- every term is `π^{k−t}`-divisible
    have hterm_dvd : ∀ s ∈ Finset.Ico t (k + 1),
        π ^ (k - t) ∣ (z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      obtain ⟨y, hy⟩ := hdvd s hs2
      have hkt : k - t = (s - t) + (k - s) := by omega
      refine ⟨z ^ (s - t) * (s.choose t : O) * y, ?_⟩
      rw [hy, mul_pow, hkt, pow_add]
      ring
    have hDdvd : π ^ (k - t) ∣ ∑ s ∈ Finset.Ico t (k + 1),
        (z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s) :=
      Finset.dvd_sum hterm_dvd
    rw [← digAt_eq_zero_iff hπ hDdvd, digAt_sum hπ _ _ hterm_dvd]
    -- each term's digit is the binomial combination of the residual digits
    have hterm_dig : ∀ s ∈ Finset.Ico t (k + 1),
        digAt π (k - t) ((z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s))
          = (IsLocalRing.residue O z) ^ (s - t)
              * ((s.choose t : IsLocalRing.ResidueField O)
                * (k.choose s : IsLocalRing.ResidueField O))
              * (- IsLocalRing.residue O z) ^ (k - s) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      obtain ⟨y, hy⟩ := hdvd s hs2
      have hry : IsLocalRing.residue O y
          = (k.choose s : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O z) ^ (k - s) :=
        (digAt_eq hπ hy).symm.trans (hdig' s hs1 hs2)
      have hkt : k - t = (s - t) + (k - s) := by omega
      have heq : (z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s)
          = π ^ (k - t) * (z ^ (s - t) * (s.choose t : O) * y) := by
        rw [hy, mul_pow, hkt, pow_add]
        ring
      calc digAt π (k - t) ((z * π) ^ (s - t) * (s.choose t : O) * G.coeff (e' * s))
          = IsLocalRing.residue O (z ^ (s - t) * (s.choose t : O) * y) :=
            digAt_eq hπ heq
        _ = _ := by
            rw [map_mul, map_mul, map_pow, map_natCast, hry]
            ring
    rw [Finset.sum_congr rfl hterm_dig]
    exact binom_vanish (IsLocalRing.residue O z) ht
  · -- slots `1 ≤ i < e'`: purity alone pays the side bound
    rw [lat_exp_pos he'' k t hipos hi]
    refine Finset.dvd_sum fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    rw [hread s hs2]
    rcases Nat.lt_or_ge s k with hsk | hsk
    · obtain ⟨y, hy⟩ := pure_dvd he'' hpure hsk hi
      have hkt : k - t = (s - t) + (k - s) := by omega
      refine ⟨z ^ (s - t) * (s.choose t : O) * y, ?_⟩
      rw [hy, mul_pow, hkt, pow_add]
      ring
    · have hsk' : s = k := by omega
      have hcz : G.coeff (e' * s + i) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hGdeg, hsk']; omega)
      rw [hcz, mul_zero]
      exact dvd_zero _

/-- **Box → digits**: if the transform lies in the deep recentred box, the lattice
digits of `G` read exactly the recentred `k`-th power — the inverse binomial
expansion of the block coefficient, with the deep terms falling out of the digit. -/
private theorem digits_of_box (hπ : Irreducible π) {z : O}
    (hz : IsLocalRing.residue O z ≠ 0) {k : ℕ} (he' : 2 ≤ e') {G : Polynomial O}
    (hG : G.Monic) (hGdeg : G.natDegree = e' * k)
    (hbox : ∀ t, t < k → (AdjoinRoot.root (eisKey π (-z) e')) ^ (e' * (k - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π (-z) e') (dev (eisKey π (-z) e') G t))
    {t : ℕ} (ht : t < k) :
    digAt π (k - t) (G.coeff (e' * t))
      = (k.choose t : IsLocalRing.ResidueField O)
          * (- IsLocalRing.residue O z) ^ (k - t) := by
  have he'' : 0 < e' := by omega
  have hcneg : IsLocalRing.residue O (-z) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact hz
  have hGdeg' : G.natDegree < (k + 1) * e' := by
    rw [hGdeg]
    calc e' * k < e' * k + e' := by omega
      _ = (k + 1) * e' := by ring
  -- the block coefficient as a binomial combination of the recentred digits
  have h1 := dev_X_pow_coeff he'' hGdeg' (by omega : t < k + 1) 0
  rw [if_pos he'', Nat.add_zero] at h1
  have h0 : G.coeff (e' * t)
      = ∑ s ∈ Finset.Ico t (k + 1), (-(z * π)) ^ (s - t) * (s.choose t : O)
          * (dev (eisKey π (-z) e') G s).coeff 0 := by
    rw [← h1, dev_X_pow_eq he'' hGdeg' (by omega : t < k + 1) z,
      Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun s _ => by rw [Polynomial.coeff_C_mul]
  -- the deep supply at `s < k` — the lattice read of the box
  have hdeep : ∀ s, s < k →
      π ^ (k - s + 1) ∣ (dev (eisKey π (-z) e') G s).coeff 0 := by
    intro s hs
    have hdevdeg : (dev (eisKey π (-z) e') G s).degree < ((e' : ℕ) : WithBot ℕ) := by
      have h2 := degree_dev_lt (eisKey_monic (π := π) (c := -z) he'')
        (by rw [eisKey_natDegree he'']; exact he'') G s
      rwa [Polynomial.degree_eq_natDegree (eisKey_monic he'').ne_zero,
        eisKey_natDegree he''] at h2
    have h3 := (eis_root_pow_dvd_mk_iff hπ hcneg he'' hdevdeg
      (e' * (k - s) + 1)).mp (hbox s hs) 0 he''
    rwa [lat_exp_zero he'' k s] at h3
  -- the top digit is `1`
  have htop : dev (eisKey π (-z) e') G k = 1 :=
    dev_top (eisKey_monic he'') (by rw [eisKey_natDegree he'']; exact he'') hG
      (by rw [hGdeg, eisKey_natDegree he'', Nat.mul_comm])
  rw [h0, Finset.sum_Ico_succ_top (by omega : t ≤ k)]
  -- the deep part: strictly below the digit
  have hSdvd : π ^ (k - t + 1) ∣ ∑ s ∈ Finset.Ico t k,
      (-(z * π)) ^ (s - t) * (s.choose t : O)
        * (dev (eisKey π (-z) e') G s).coeff 0 := by
    refine Finset.dvd_sum fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    obtain ⟨y, hy⟩ := hdeep s hs2
    have hkt : k - t + 1 = (s - t) + (k - s + 1) := by omega
    refine ⟨(-z) ^ (s - t) * (s.choose t : O) * y, ?_⟩
    rw [hy, ← neg_mul z π, mul_pow, hkt, pow_add]
    ring
  have hS' : π ^ (k - t) ∣ ∑ s ∈ Finset.Ico t k,
      (-(z * π)) ^ (s - t) * (s.choose t : O)
        * (dev (eisKey π (-z) e') G s).coeff 0 :=
    dvd_trans (pow_dvd_pow π (by omega : k - t ≤ k - t + 1)) hSdvd
  -- the top term carries exactly the digit
  have heq : (-(z * π)) ^ (k - t) * (k.choose t : O)
      * (dev (eisKey π (-z) e') G k).coeff 0
      = π ^ (k - t) * ((-z) ^ (k - t) * (k.choose t : O)) := by
    rw [htop, Polynomial.coeff_one_zero, ← neg_mul z π, mul_pow]
    ring
  have hT' : π ^ (k - t) ∣ (-(z * π)) ^ (k - t) * (k.choose t : O)
      * (dev (eisKey π (-z) e') G k).coeff 0 :=
    ⟨(-z) ^ (k - t) * (k.choose t : O), heq⟩
  rw [digAt_add hπ hS' hT', (digAt_eq_zero_iff hπ hS').mpr hSdvd, zero_add,
    digAt_eq hπ heq, map_mul, map_pow, map_neg, map_natCast]
  ring

/-- ★★★ **THE RESIDUAL-BOX TRANSFER CRITERION** (LEG 1, digit form) — C110's
translate-residual mechanism at the recentred frame `e' ≥ 2`, x-frame `(h, d) =
(1, 1)` sub-sector: a monic block `G` of degree `e'·k`, pure of slope `1/e'` (the
raw valuation form `π^{⌈(e'k−j)/e'⌉} ∣ G_j`), has lattice digits reading the
`k`-th power of the recentred linear residual `(X − z̄)^k` — i.e.
`digAt_{k−t}(G_{e't}) = C(k,t)·(−z̄)^{k−t}` — IF AND ONLY IF its `eisKey`-adic
development lies in the DEEP RECENTRED BOX over `O' = AdjoinRoot (eisKey π (−z) e')`:
`α^{e'(k−t)+1} ∣ mk (dev t)` for every `t < k` (strictly above the side line, one
`α`-notch deep).  Uniform in `q, e', k, z`, every DVR. -/
theorem eis_transfer_digits_iff (hπ : Irreducible π) {z : O}
    (hz : IsLocalRing.residue O z ≠ 0) {k : ℕ} (he' : 2 ≤ e') {G : Polynomial O}
    (hG : G.Monic) (hGdeg : G.natDegree = e' * k)
    (hpure : ∀ j, j < e' * k → π ^ ((e' * k - j + (e' - 1)) / e') ∣ G.coeff j) :
    (∀ t, t < k → (AdjoinRoot.root (eisKey π (-z) e')) ^ (e' * (k - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π (-z) e') (dev (eisKey π (-z) e') G t))
      ↔ ∀ t, t < k →
          digAt π (k - t) (G.coeff (e' * t))
            = (k.choose t : IsLocalRing.ResidueField O)
                * (- IsLocalRing.residue O z) ^ (k - t) :=
  ⟨fun hbox t ht => digits_of_box (t := t) hπ hz he' hG hGdeg hbox ht,
    fun hdig t ht => box_of_digits (t := t) hπ hz he' hG hGdeg hpure hdig ht⟩

/-! ### the wrapper: the digit equations ARE the residual `k`-th power -/

open Uniformity.Density.IFCG37 (xres resPoly_x_frame)

/-- The coefficient read of the x-frame residual under the side pins. -/
private theorem xres_coeff_read {k : ℕ} {G : Polynomial O}
    (hne : (sideSet (Polynomial.X : Polynomial O) G 1 e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G 1 e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G 1 e' hne = k) (j : ℕ) :
    (xres π G 1 e' hne k).coeff j
      = if j < k + 1 then digAt π (k - j) (G.coeff (e' * j)) else 0 := by
  classical
  unfold xres
  rw [hdeg, hmin]
  simp only [one_mul, zero_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (k + 1)) j
    (fun t => digAt π (k - t) (G.coeff (e' * t)))]
  simp [Finset.mem_range]

/-- ★★ **The residual-power reading of the digits**: under the side pins
(`sideMin = 0`, `sideDeg = k`, pinned height `H₀ = k`), the x-frame residual is
the recentred `k`-th power `(X − z̄)^k` iff the `k` lattice digits read the
binomial expansion — the bridge between LEG 1's digit form and the corpus'
residual objects. -/
theorem xres_eq_pow_iff_digits {z : O} {k : ℕ}
    {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = e' * k)
    (hne : (sideSet (Polynomial.X : Polynomial O) G 1 e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G 1 e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G 1 e' hne = k) :
    xres π G 1 e' hne k
        = (Polynomial.X - Polynomial.C (IsLocalRing.residue O z)) ^ k
      ↔ ∀ t, t < k → digAt π (k - t) (G.coeff (e' * t))
          = (k.choose t : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O z) ^ (k - t) := by
  have hGtop : G.coeff (e' * k) = 1 := by
    rw [← hGdeg]
    exact hG.coeff_natDegree
  have hpc : ∀ j : ℕ,
      ((Polynomial.X - Polynomial.C (IsLocalRing.residue O z)) ^ k).coeff j
        = (k.choose j : IsLocalRing.ResidueField O)
            * (- IsLocalRing.residue O z) ^ (k - j) := by
    intro j
    rw [sub_eq_add_neg, ← map_neg, Polynomial.coeff_X_add_C_pow]
    ring
  constructor
  · intro h t ht
    have h1 := congrArg (fun P => Polynomial.coeff P t) h
    rw [xres_coeff_read hne hmin hdeg t, if_pos (by omega : t < k + 1), hpc t] at h1
    exact h1
  · intro hdig
    refine Polynomial.ext fun j => ?_
    rw [xres_coeff_read hne hmin hdeg j, hpc j]
    rcases Nat.lt_trichotomy j k with hj | hj | hj
    · rw [if_pos (by omega : j < k + 1)]
      exact hdig j hj
    · rw [if_pos (by omega : j < k + 1), hj, Nat.sub_self, digAt_zero, hGtop,
        map_one, Nat.choose_self, Nat.cast_one, pow_zero, mul_one]
    · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]

/-- ★★★ **LEG 1, the sector-facing form**: under the side pins, the x-frame RESIDUAL
POLYNOMIAL (the object `classResidualPoly` transports to) is the recentred `k`-th
power `(X − z̄)^k` IF AND ONLY IF the `eisKey`-adic transform lies in the deep
recentred box over `O'` — C110's translate-residual criterion at `e' ≥ 2`. -/
theorem resPoly_eq_pow_iff_box (hπ : Irreducible π) {z : O}
    (hz : IsLocalRing.residue O z ≠ 0) {k : ℕ} (he' : 2 ≤ e') {G : Polynomial O}
    (hG : G.Monic) (hGdeg : G.natDegree = e' * k)
    (hpure : ∀ j, j < e' * k → π ^ ((e' * k - j + (e' - 1)) / e') ∣ G.coeff j)
    (hne : (sideSet (Polynomial.X : Polynomial O) G 1 e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G 1 e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G 1 e' hne = k) :
    resPoly π (Polynomial.X : Polynomial O) G 1 e' hne k
        = (Polynomial.X - Polynomial.C
            (resFieldXEquiv O (IsLocalRing.residue O z))) ^ k
      ↔ ∀ t, t < k → (AdjoinRoot.root (eisKey π (-z) e')) ^ (e' * (k - t) + 1)
          ∣ AdjoinRoot.mk (eisKey π (-z) e') (dev (eisKey π (-z) e') G t) := by
  rw [eis_transfer_digits_iff hπ hz he' hG hGdeg hpure, resPoly_x_frame,
    ← xres_eq_pow_iff_digits (z := z) hG hGdeg hne hmin hdeg]
  constructor
  · intro h
    have hinj : Function.Injective
        (Polynomial.map ((resFieldXEquiv O :
          ResidueField O ≃+* resField (Polynomial.X : Polynomial O)) :
            ResidueField O →+* resField (Polynomial.X : Polynomial O))) :=
      Polynomial.map_injective _ (resFieldXEquiv O).injective
    refine hinj ?_
    rw [h]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, RingEquiv.coe_toRingHom]
  · intro h
    rw [h]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, RingEquiv.coe_toRingHom]

end TransferSupport

end Uniformity.Density.IFCG43

section AxCheck
#print axioms Uniformity.Density.IFCG43.compositum_recentring_stack
#print axioms Uniformity.Density.IFCG43.eis_root_irreducible
#print axioms Uniformity.Density.IFCG43.devVec
#print axioms Uniformity.Density.IFCG43.reassVec
#print axioms Uniformity.Density.IFCG43.cellTransport
#print axioms Uniformity.Density.IFCG43.cellTransport_apply
#print axioms Uniformity.Density.IFCG43.cellTransport_symm_apply
#print axioms Uniformity.Density.IFCG43.cellTransport_card_image
#print axioms Uniformity.Density.IFCG43.card_coeff_eis
#print axioms Uniformity.Density.IFCG43.eis_recentring_stack
#print axioms Uniformity.Density.IFCG43.zcURLim_eis_value
#print axioms Uniformity.Density.IFCG43.eisKey_neg
#print axioms Uniformity.Density.IFCG43.eis_transfer_digits_iff
#print axioms Uniformity.Density.IFCG43.xres_eq_pow_iff_digits
#print axioms Uniformity.Density.IFCG43.resPoly_eq_pow_iff_box
end AxCheck
