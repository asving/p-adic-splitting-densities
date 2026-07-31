/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL27_reductionInterface
import LeanUrat.HC1.CL11_posUniq
import LeanUrat.HC1.T12_coordFin

/-!
# HC1.CL12_nclAssembly — NCL: the ℤ_[p] assembly (BP5 CL-12, display (10))

**Unit CL-12** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4,
REWRITTEN at REVISION 2, findings 4/5/9 — the interface work lives in CL-27; this
unit is application-sized). **GATED on CL-10's clean outcome** (countermodel-first;
risk R-1): no prover works this unit before the CL-10 probe completes — if CL-10
finds a cancellation, this statement is FALSE as stated and R6 escalates to
adjudication (window-guard (i-b) / NCL as a named pack law / re-fence).

**Informal statement (display (10) — NCL, no-cancellation at a level).** For a
digit assignment `y ≠ 0` supported inside the (finite) level set `levelSet b γ`:
`T.slotCoeff b y = Σ_{c ∈ supp y} digLift(y c)·mono c ≠ 0`. Mathematically: the
mixed-radix p/Φ-adic development with unit digits has no nonzero kernel — THE one
genuinely new lemma of the R6 closure (T4/C1 take `slotCoeff ≠ 0` as a hypothesis;
T8's BijOn runs on a subgroup, dodging kernel-triviality).

**Proof sketch (the §3.2 REVISION-2 factor-out route; all vocabulary CL-27's).**
`l_min :=` the least p-exponent over `supp y` (finite — `levelSet_finite'`;
NONEMPTY since `y ≠ 0`). `slotCoeff_factor` + IsDomain cancellation
(`C_p_pow_ne`, `mul_ne_zero_iff` in `ℤ_[p][x]`) reduce (10) to the cofactor
`Σ_c digLift(y c)·C(p^{l c − l_min})·∏Φ^{s c} ≠ 0`. Apply `red` (a ring hom —
transports sums/products): the `l c > l_min` terms die (`red_p_pow_zero`); the
survivors — at least one, `l_min` is attained — have DISTINCT slot vectors
(`coord_eq_of_ht_l_eq`: same block b, same height γ, same level l_min ⇒ equal, so
distinct survivors have distinct slot vectors; the top slot is constantly b).
The reduced sum is `Σ_c d̄_c·∏_r Φ̄_r^{s_c(r)}` with `d̄_c = red (digLift (y c)) ≠ 0`
(`red_digLift_ne`), `deg d̄_c < deg Φ̄₀` (`red_digLift_deg` — degree may drop, R-2),
`Φ̄_r` monic of the EXACT degrees (`red_monic_deg`, `red_ratio_law`). Close with
`CL11_posUniq` at `K₀ = 𝔽_p = ZMod p`: nonemptiness from the attained `l_min`;
`0 < deg Φ̄₀` from `(T.stg 0).hdeg` + `red_monic_deg`. The cofactor is ≠ 0 because
its red-image is ≠ 0.

**E-phase resolutions recorded.**
* Display (10) is stated on FULL-DOMAIN digit assignments with level-set support
  (`∃ c, y c ≠ 0` + `∀ c, y c ≠ 0 → c ∈ levelSet b γ`) — the ŷ-extension form,
  matching the CL-10 probe's shape EXACTLY (`CL10_nclProbe.lean` states the
  negation of this statement's instance; the probe file records the same
  resolution). No `hfin` hypothesis: level sets are finite (T7's
  `levelSet_finite'`), so the support is automatically finite.
* SPLIT RULE (CL-12a/b) NOT exercised at E-phase: the finsum bookkeeping is already
  carried by CL-27(c)'s `slotCoeff_factor`. If it resists there, the prover emits
  CL-12a (sum normalization) / CL-12b (the application).
* T9 itself is NOT imported: its kernel reaches this unit only through CL-27(d)'s
  `coord_eq_of_ht_l_eq`.

**PROVER NOTES (as-built, 2026-07-30).**
* CL-10 gate COMPLETED first (BLOCKED as sealed-predicted; mechanism survey in the
  probe file). Proof follows the ratified factor-out route exactly.
* One proof-time import added (`T12_coordFin`) for the `levelSet_finite` copy
  (private at C2_TYPa:470; the CL-13 E-phase note's re-derive route).
* Survivor distinctness in the FORMAL proof needs only the `l = l_min` slice:
  equal slot vector + equal `l` gives equal coordinate by `Coord` extensionality —
  the fibers of `c ↦ c.slot` over the survivors are singletons, so the
  slot-vector reindexing (`Finset.sum_image'`) carries unit digits. CL-27(d)'s
  `coord_eq_of_ht_l_eq` (the general equal-ht kernel, PROVED there) is the
  blueprint-named guarantee; the level-set instance used here is its `hl`-slice.

**Deps.** CL-10 (gate), CL-11, CL-27 (, T9 via CL-27(d)). difficulty: hard-fable.
Size: ~60. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Coordinate extensionality (the `Coord` structure has a proof-irrelevant third field). -/
private lemma cl12_coord_ext {T : Tower p F} {c c' : T.Coord}
    (hl : c.l = c'.l) (hs : c.slot = c'.slot) : c = c' := by
  obtain ⟨l, s, _⟩ := c
  obtain ⟨l', s', _⟩ := c'
  cases hl
  cases hs
  rfl

private lemma cl12_kappa_nonneg (T : Tower p F) (r : Fin (T.K + 1)) : 0 ≤ T.kappa r := by
  rw [Tower.kappa]
  positivity

/-- The level set is finite (copy of C2_TYPa's private `levelSet_finite`, via T12's box). -/
private lemma cl12_levelSet_finite (T : Tower p F) (b : ℕ) (γ : ℚ) :
    (T.levelSet b γ).Finite := by
  apply Set.Finite.subset ((T12_coordFin T (⌊γ⌋.toNat + 1) (b + 1)).1)
  rintro c ⟨hblk, hht⟩
  constructor
  · have hle : (c.l : ℚ) ≤ γ := by
      rw [← hht, Tower.ht]
      have hsum : 0 ≤ ∑ r, (c.slot r : ℚ) * T.kappa r :=
        Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (cl12_kappa_nonneg T r)
      linarith
    have h1 : (c.l : ℤ) ≤ ⌊γ⌋ := Int.le_floor.mpr (by exact_mod_cast hle)
    omega
  · have hb : c.slot (Fin.last T.K) = b := hblk
    omega

/-- **CL-12 (display (10), NCL)**: no cancellation at a level — a nonzero digit
assignment supported inside one level set has nonzero slot coefficient (uniqueness
of the mixed-radix p/Φ-adic development with unit digits). GATED on CL-10. -/
theorem CL12_ncl {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hne : ∃ c : T.Coord, y c ≠ 0)
    (hsupp : ∀ c : T.Coord, y c ≠ 0 → c ∈ T.levelSet b γ) :
    T.slotCoeff b y ≠ 0 := by
  classical
  -- support data
  have hfin : (Function.support y).Finite :=
    (cl12_levelSet_finite T b γ).subset (fun c hc => hsupp c (Function.mem_support.mp hc))
  have hblk : ∀ c : T.Coord, y c ≠ 0 → T.blk c = b := fun c hc => (hsupp c hc).1
  set S : Finset T.Coord := hfin.toFinset with hSdef
  have hmemS : ∀ c, c ∈ S ↔ y c ≠ 0 := by
    intro c
    rw [hSdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hSne : S.Nonempty := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨c, (hmemS c).mpr hc⟩
  -- the least p-exponent over the support, attained
  set Limg : Finset ℕ := S.image (fun c => c.l) with hLimg
  have hLne : Limg.Nonempty := hSne.image _
  set lmin : ℕ := Limg.min' hLne with hlmindef
  have hlmin : ∀ c : T.Coord, y c ≠ 0 → lmin ≤ c.l := by
    intro c hc
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ ((hmemS c).mpr hc))
  obtain ⟨c₀, hc₀S, hc₀l⟩ := Finset.mem_image.mp (Finset.min'_mem Limg hLne)
  -- the factor-out identity (CL-27(c)) + domain cancellation
  rw [slotCoeff_factor T b y hfin hblk lmin hlmin]
  -- the reduced-cofactor machinery
  set W : Polynomial ℤ_[p] :=
    ∑ c ∈ hfin.toFinset,
      T.digLift (y c) *
        (Polynomial.C ((p : ℤ_[p]) ^ (c.l - lmin)) * ∏ r, (T.stg r).Φ ^ c.slot r) with hWdef
  -- the survivor slice and its slot-vector image
  set S₀ : Finset T.Coord := S.filter (fun c => c.l = lmin) with hS₀def
  have hS₀sub : ∀ c ∈ S₀, y c ≠ 0 := fun c hc => (hmemS c).mp (Finset.mem_filter.mp hc).1
  have hS₀l : ∀ c ∈ S₀, c.l = lmin := fun c hc => (Finset.mem_filter.mp hc).2
  have hc₀ : c₀ ∈ S₀ := Finset.mem_filter.mpr ⟨hc₀S, hc₀l⟩
  -- fibers of the slot map over the survivors are singletons (survivor distinctness;
  -- the CL-27(d) mechanism restricted to the l = l_min slice)
  have hfiber : ∀ c ∈ S₀, S₀.filter (fun c' => c'.slot = c.slot) = {c} := by
    intro c hc
    ext c'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc'S₀, hslot⟩
      exact cl12_coord_ext (by rw [hS₀l c' hc'S₀, hS₀l c hc]) hslot
    · rintro rfl
      exact ⟨hc, rfl⟩
  -- the reduced digit function on slot vectors
  set dd : (Fin (T.K + 1) → ℕ) → Polynomial (ZMod p) :=
    fun s => ∑ c ∈ S₀.filter (fun c' => c'.slot = s), red p (T.digLift (y c)) with hdddef
  have hdd : ∀ c ∈ S₀, dd c.slot = red p (T.digLift (y c)) := by
    intro c hc
    rw [hdddef]
    simp only
    rw [hfiber c hc, Finset.sum_singleton]
  -- compute the reduction of the cofactor
  have hredW : red p W = ∑ s ∈ S₀.image (fun c => c.slot),
      dd s * ∏ r, (red p ((T.stg r).Φ)) ^ (s r) := by
    have h1 : red p W = ∑ c ∈ S,
        red p (T.digLift (y c)) *
          (red p (Polynomial.C ((p : ℤ_[p]) ^ (c.l - lmin))) *
            ∏ r, (red p ((T.stg r).Φ)) ^ c.slot r) := by
      rw [hWdef, red, ← Polynomial.coe_mapRingHom, map_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [map_mul, map_mul, map_prod]
      simp only [map_pow, Polynomial.coe_mapRingHom]
    have h2 : ∑ c ∈ S,
        red p (T.digLift (y c)) *
          (red p (Polynomial.C ((p : ℤ_[p]) ^ (c.l - lmin))) *
            ∏ r, (red p ((T.stg r).Φ)) ^ c.slot r)
        = ∑ c ∈ S₀,
            red p (T.digLift (y c)) * ∏ r, (red p ((T.stg r).Φ)) ^ c.slot r := by
      have hcond : ∀ c ∈ S,
          red p (T.digLift (y c)) *
            (red p (Polynomial.C ((p : ℤ_[p]) ^ (c.l - lmin))) *
              ∏ r, (red p ((T.stg r).Φ)) ^ c.slot r) ≠ 0
          → c.l = lmin := by
        intro c hcS hcne
        by_contra hcl
        apply hcne
        have h1le : 1 ≤ c.l - lmin := by
          have := hlmin c ((hmemS c).mp hcS)
          omega
        rw [red_p_pow_zero (c.l - lmin) h1le, zero_mul, mul_zero]
      have hshrink := (Finset.sum_filter_of_ne (p := fun c : T.Coord => c.l = lmin) hcond).symm
      rw [hshrink, hS₀def]
      apply Finset.sum_congr rfl
      intro c hc
      have hcl : c.l = lmin := (Finset.mem_filter.mp hc).2
      have h0 : c.l - lmin = 0 := by omega
      rw [h0, pow_zero, Polynomial.C_1, red, Polynomial.map_one, one_mul]
    rw [h1, h2]
    -- reindex the survivor sum by slot vectors (fibers are singletons)
    exact (Finset.sum_image'
      (fun c => red p (T.digLift (y c)) * ∏ r, (red p ((T.stg r).Φ)) ^ c.slot r)
      (fun c hc => by
        rw [hdd c hc, hfiber c hc, Finset.sum_singleton])).symm
  -- the CL-11 application at K₀ = 𝔽_p
  have hCL11 : ∑ s ∈ S₀.image (fun c => c.slot),
      dd s * ∏ r, (red p ((T.stg r).Φ)) ^ (s r) ≠ 0 := by
    apply CL11_posUniq T.K T.slotBound (fun r => red p ((T.stg r).Φ)) b
    · exact fun r => (red_monic_deg ((T.stg r).Φ) (T.stg r).hmonic).1
    · rw [(red_monic_deg ((T.stg 0).Φ) (T.stg 0).hmonic).2]
      exact (T.stg 0).hdeg
    · exact fun r => red_ratio_law T r
    · exact ⟨c₀.slot, Finset.mem_image_of_mem _ hc₀⟩
    · intro s hs r
      obtain ⟨c, hcS₀, rfl⟩ := Finset.mem_image.mp hs
      exact c.slot_lt r
    · intro s hs
      obtain ⟨c, hcS₀, rfl⟩ := Finset.mem_image.mp hs
      exact hblk c (hS₀sub c hcS₀)
    · intro s hs
      obtain ⟨c, hcS₀, rfl⟩ := Finset.mem_image.mp hs
      rw [hdd c hcS₀]
      exact red_digLift_ne T (hS₀sub c hcS₀)
    · intro s hs
      obtain ⟨c, hcS₀, rfl⟩ := Finset.mem_image.mp hs
      rw [hdd c hcS₀]
      exact red_digLift_deg T (y c)
  -- assemble: the cofactor is nonzero because its reduction is
  have hWne : W ≠ 0 := by
    intro hW0
    apply hCL11
    rw [← hredW, hW0, red, Polynomial.map_zero]
  exact mul_ne_zero (C_p_pow_ne lmin) hWne

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL12_ncl
