/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C29
import Uniformity.ChapC.C131y
import Uniformity.ChapC.C131ae

/-!
# Uniformity.ChapC.C133mh0 — `[MH0A6 2026-08-28]`: MH.0a, MH.0c-remainder, MH.6

**Nodes MH.0a + MH.0c-remainder + MH.6** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §9's
node table). Three small, mutually independent Hensel-engine nodes:

* **MH.0a** — `stageHeight_key`: `F.stageHeight F.key = (D′ * F.h : ℕ∞)` (`D′ := F.e₁ * F.f₁`),
  derived from `F.hpure` (the key's own one-sidedness at the order-0 key `X`) plus its top
  coefficient reading `1` (monicity).
* **MH.0c remainder** — the two small C.22 definitional chases left open after C133mh1 landed
  the cocycle row: `twistExp 0 = 0` and `twistRead 0 1 = 1`.
* **MH.6** — the perturbation law M4 (§4.3, the dv-twin of B41a's `pure_add_of_lt`): adding `y`
  with `deg y < deg x` and `W(y) ≥ W(x) + 1` to a monic pure `x` preserves monicity, degree,
  purity, `M₀` (the height), and the residual (`dvResPoly`). `W := dvSupp` (C.06).

## MH.6: what is reused, and what is transcribed fresh

The four landed atoms named in the doc's node table are `dev_add_of_monic` (B32a),
`dvHgt_add_eq_left_of_lt` (C131y), `twistRead_add_eq_left_of_lt` (C131ae),
`dvHgt_add_min` (C131y). Beyond these, C131y (built for the unrelated C.72 shadow-band
theorem) already carries a *stronger*, LevelDatum-packaged residual-invariance theorem
(`dvResPoly_add_deep`) whose proof consumes only bare `u ℓ hℓ hcop`, never the level
datum's residual label `r`. Rather than manufacture an unused `LevelDatum` witness just to
match that signature, this file re-derives the same small support lemmas at bare `u ℓ`
(`coord_lt_of_onSide_of_deep'`, `dvOnSide_nat_eq'`, `read_height_lt_of_deep'` — mechanical
transcriptions of C131y's private Part-2/Part-3 helpers, dropping only the `LevelDatum`
wrapper) and assembles the residual clause directly. This is "assembly of landed atoms"
in substance: every atomic fact consumed (`dvSupp_le_term`, `dvSideSet_add_deep`,
`dvSideLen_eq`, `dvOnSide_modEq`, `dev_add_of_monic`, `twistRead_add_eq_left_of_lt`) is
already landed and public; only the small gluing lemmas are re-derived here, verbatim in
mechanism, because the `LevelDatum` wrapper on the landed originals is not otherwise
removable from outside their file.

## Status

Sorry-free; footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## MH.0a — the key's own stage height -/

private theorem gaussVal_C' (c : O) : gaussVal (Polynomial.C c) = addVal O c := by
  rw [gaussVal, Polynomial.natDegree_C, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_C_zero]

/-- ★ **MH.0a — the key's stage height.** `F.stageHeight F.key = D′·F.h`, `D′ := F.e₁ * F.f₁`.
Read off `F.hpure`'s right endpoint (`X`-abscissa `D′`, since `F.key.natDegree = D′` by
`F.hdeg`): the endpoint's order-0 Gauss height is `0` (monicity, top coefficient `1`), so the
on-side equation collapses to `stageHeight F.key = F.h * D′`. -/
theorem stageHeight_key (F : KeyFrame O π) :
    F.stageHeight F.key = ((F.e₁ * F.f₁) * F.h : ℕ) := by
  have hj : F.key.natDegree / (Polynomial.X : Polynomial O).natDegree = F.e₁ * F.f₁ := by
    rw [Polynomial.natDegree_X, Nat.div_one, F.hdeg]
  have hend : OnSide Polynomial.X F.key F.h F.e₁ (F.e₁ * F.f₁) := by
    have h2 := F.hpure.2
    rwa [hj] at h2
  have hcoeff : F.key.coeff (F.e₁ * F.f₁) = 1 := by
    rw [← F.hdeg]; exact F.hmonic.coeff_natDegree
  have hnp : npHgt Polynomial.X F.key (F.e₁ * F.f₁) = 0 := by
    show gaussVal (dev Polynomial.X F.key (F.e₁ * F.f₁)) = 0
    rw [dev_X, hcoeff, gaussVal_C', IsDiscreteValuationRing.addVal_one]
  have heq : F.e₁ • npHgt Polynomial.X F.key (F.e₁ * F.f₁)
      + (F.h * (F.e₁ * F.f₁) : ℕ) = suppVal Polynomial.X F.key F.h F.e₁ := hend
  rw [hnp, smul_zero, zero_add] at heq
  show suppVal Polynomial.X F.key F.h F.e₁ = _
  rw [← heq]
  push_cast
  ring

/-! ## MH.0c remainder — the two C.22 definitional chases -/

/-- ★ **MH.0c remainder, clause 1.** `twistExp 0 = 0`. Immediate from C.16's `twistExp_spec`
at `k = 0`: `slotIdx 1 * 0 = slotIdx 0 + e₁ * twistExp 0`, i.e. `0` is a sum of two naturals,
so both vanish; `e₁ ≠ 0` (`F.he₁`) then kills the `e₁ = 0` disjunct of `mul_eq_zero`. -/
theorem twistExp_zero (F : KeyFrame O π) : F.twistExp 0 = 0 := by
  have hspec := F.twistExp_spec 0
  simp only [mul_zero] at hspec
  have h2 : F.e₁ * F.twistExp 0 = 0 := by omega
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h F.he₁.ne'
  · exact h

/-- ★ **MH.0c remainder, clause 2.** `twistRead 0 1 = 1` (the frame's top-slot normalization).
Needs `0 < F.h` (§1's standing nondegeneracy; at `h = 0` every `t < f₁` is affordable at
height `0` and the window is not a singleton). `slotIdx 0 = 0` (uniqueness at the trivial
witness), so the window `T(0) = {t < f₁ : e₁t·h ≤ 0}` is exactly `{0}`; the lone term reads
`digAt π 0 ((1:O[X]).coeff 0) = residue 1 = 1` through the two algebra maps, times
`stageLetter^0 = 1`. -/
theorem twistRead_one (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (hh : 0 < F.h) :
    F.twistRead H₀ hpin 0 (1 : Polynomial O) = 1 := by
  have hs0 : F.slotIdx 0 = 0 := (F.slotIdx_unique F.he₁ (by simp [Nat.ModEq])).symm
  have hwin : F.slotWindow 0 = ({0} : Finset ℕ) := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · simp [KeyFrame.slotWindow, hs0, F.hf₁]
    · intro t ht
      simp only [KeyFrame.slotWindow, Finset.mem_filter, Finset.mem_range, hs0, zero_add] at ht
      obtain ⟨-, hle⟩ := ht
      have h0 : F.e₁ * t * F.h = 0 := Nat.le_zero.mp hle
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 F.he₁.ne'
        · exact h2
      · exact absurd h1 hh.ne'
  have htw0 : F.twistExp 0 = 0 := twistExp_zero F
  rw [KeyFrame.twistRead, htw0, pow_zero, one_mul]
  unfold KeyFrame.slotRes
  rw [hs0, hwin, Finset.sum_singleton]
  simp [digAt_zero, Polynomial.coeff_one_zero]

/-! ## MH.6 — the perturbation law M4 -/

/-! ### Private helpers (bare-`u,ℓ` transcriptions of C131y's Part-2/Part-3 machinery,
dropping only the `LevelDatum` wrapper — see the header note). -/

private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

private theorem coord_lt_of_onSide_of_deep' (F : KeyFrame O π) {A B : Polynomial O}
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {m j : ℕ}
    (hval : dvSupp F A u ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B u ℓ) (hj : DvOnSide F A u ℓ j) :
    dvHgt F A j < dvHgt F B j := by
  have hterm : ℓ • dvHgt F A j + (u * j : ℕ∞)
      < ℓ • dvHgt F B j + (u * j : ℕ∞) := by
    calc
      ℓ • dvHgt F A j + (u * j : ℕ∞) = (m : ℕ∞) := hj.1.symm.trans hval
      _ < dvSupp F B u ℓ := hdeep
      _ ≤ ℓ • dvHgt F B j + (u * j : ℕ∞) := C131y.dvSupp_le_term F B u hℓ j
  exact lt_of_nsmul_lt_nsmul_right ℓ
    ((ENat.add_lt_add_iff_right (ENat.coe_ne_top (u * j))).mp hterm)

private theorem min'_congr' {s t : Finset ℕ} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst t; congr

private theorem max'_congr' {s t : Finset ℕ} (hst : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.max' hs = t.max' ht := by
  subst t; congr

private theorem dvOnSide_nat_eq' {F : KeyFrame O π} {u ℓ : ℕ}
    {A : Polynomial O} {j j' H H' : ℕ}
    (hH : dvHgt F A j = (H : ℕ∞)) (hH' : dvHgt F A j' = (H' : ℕ∞))
    (hj : DvOnSide F A u ℓ j) (hj' : DvOnSide F A u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have e : ℓ • (H : ℕ∞) + (u * j : ℕ∞)
      = ℓ • (H' : ℕ∞) + (u * j' : ℕ∞) := by
    rw [← hH, ← hH', ← hj.1, hj'.1]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞)
      = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

private theorem read_height_lt_of_deep' {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {A B : Polynomial O} {m M : ℕ}
    (hval : dvSupp F A u ℓ = (m : ℕ∞))
    (hdeep : (m : ℕ∞) < dvSupp F B u ℓ)
    (hne : (dvSideSet F A u ℓ).Nonempty)
    (hpinM : dvHgt F A (dvSideMin F A u ℓ hne) = (M : ℕ∞))
    {t : ℕ} (ht : t < dvSideDeg F A u ℓ hne + 1) :
    ((M - t * u : ℕ) : ℕ∞)
      < dvHgt F B (dvSideMin F A u ℓ hne + t * ℓ) := by
  let jmin := dvSideMin F A u ℓ hne
  let jmax := dvSideMax F A u ℓ hne
  let d := dvSideDeg F A u ℓ hne
  have hminmem : jmin ∈ dvSideSet F A u ℓ := Finset.min'_mem _ _
  have hmaxmem : jmax ∈ dvSideSet F A u ℓ := Finset.max'_mem _ _
  have hminon : DvOnSide F A u ℓ jmin := dvOnSide_of_mem' hminmem
  have hmaxon : DvOnSide F A u ℓ jmax := dvOnSide_of_mem' hmaxmem
  obtain ⟨Hmax, hHmax⟩ : ∃ Hmax : ℕ, dvHgt F A jmax = (Hmax : ℕ∞) := by
    rcases ENat.ne_top_iff_exists.mp hmaxon.2 with ⟨Hmax, hh⟩
    exact ⟨Hmax, hh.symm⟩
  have hle : jmin ≤ jmax := Finset.min'_le _ _ hmaxmem
  have hlen := dvSideLen_eq F hℓ hcop hne
  have hmaxeq : jmax = jmin + ℓ * d := by
    change jmax - jmin = ℓ * d at hlen
    omega
  have hsideeq : ℓ * M + u * jmin = ℓ * Hmax + u * jmax :=
    dvOnSide_nat_eq' hpinM hHmax hminon hmaxon
  have hMeq : M = Hmax + u * d := by
    have hmul : ℓ * M = ℓ * (Hmax + u * d) := by
      rw [hmaxeq] at hsideeq
      nlinarith
    simpa [d] using Nat.eq_of_mul_eq_mul_left hℓ hmul
  have htu : t * u ≤ M := by
    have htd : t ≤ d := by change t < d + 1 at ht; omega
    rw [hMeq]
    calc
      t * u ≤ d * u := Nat.mul_le_mul_right u htd
      _ = u * d := by ring
      _ ≤ Hmax + u * d := Nat.le_add_left _ _
  have hmNat : m = ℓ * M + u * jmin := by
    have he : (m : ℕ∞) = ℓ • (M : ℕ∞) + (u * jmin : ℕ∞) := by
      rw [← hval, hminon.1, hpinM]
    have he' : ((m : ℕ) : ℕ∞) = ((ℓ * M + u * jmin : ℕ) : ℕ∞) := by
      simpa [nsmul_eq_mul] using he
    exact ENat.coe_inj.mp he'
  let k := M - t * u
  let j := jmin + t * ℓ
  have hweighted : ℓ * k + u * j = m := by
    dsimp only [k, j]
    rw [hmNat]
    have hmul_le : ℓ * (t * u) ≤ ℓ * M := Nat.mul_le_mul_left ℓ htu
    have hcross : ℓ * (t * u) = u * (t * ℓ) := by ring
    rw [Nat.mul_sub_left_distrib, Nat.mul_add]
    calc
      (ℓ * M - ℓ * (t * u)) + (u * jmin + u * (t * ℓ))
          = (ℓ * M - ℓ * (t * u)) +
              (u * jmin + ℓ * (t * u)) := by rw [hcross]
      _ = (ℓ * M - ℓ * (t * u) + ℓ * (t * u)) + u * jmin := by
        ac_rfl
      _ = ℓ * M + u * jmin := by rw [Nat.sub_add_cancel hmul_le]
  have hterm : (m : ℕ∞)
      < ℓ • dvHgt F B j + (u * j : ℕ∞) :=
    hdeep.trans_le (C131y.dvSupp_le_term F B u hℓ j)
  have hweighted' : ℓ • (k : ℕ∞) + (u * j : ℕ∞) = (m : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    exact_mod_cast hweighted
  rw [← hweighted'] at hterm
  have hsmul : ℓ • (k : ℕ∞) < ℓ • dvHgt F B j :=
    (ENat.add_lt_add_iff_right (ENat.coe_ne_top (u * j))).mp hterm
  exact lt_of_nsmul_lt_nsmul_right ℓ hsmul

/-- **MH.6, clause A (purity).** Adding a strictly-deeper `y` to a level-pure `x` preserves
`IsDvPure`: the side set is unchanged (`dvSideSet_add_deep`), so both endpoints transfer. -/
theorem dv_purity_add_of_lt (F : KeyFrame O π) {x y : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hxpure : IsDvPure F x u ℓ) {m : ℕ} (hxsupp : dvSupp F x u ℓ = (m : ℕ∞))
    (hydeg : y.degree < x.degree)
    (hy : ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ) :
    IsDvPure F (x + y) u ℓ := by
  have hdeep : (m : ℕ∞) < dvSupp F y u ℓ :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hy
  have hset : dvSideSet F (x + y) u ℓ = dvSideSet F x u ℓ :=
    C131y.dvSideSet_add_deep F u hℓ hxsupp hdeep
  have hdegeq : (x + y).natDegree = x.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hydeg)
  refine ⟨?_, ?_⟩
  · rw [hset]; exact hxpure.1
  · rw [hset, hdegeq]; exact hxpure.2

/-- **MH.6, clause B (height, `M₀`).** The perturbed polynomial's level height at its own
(unchanged) side minimum equals the original's. -/
theorem dv_height_add_of_lt (F : KeyFrame O π) {x y : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {hxne : (dvSideSet F x u ℓ).Nonempty} {Mx m : ℕ}
    (hMx : dvHgt F x (dvSideMin F x u ℓ hxne) = (Mx : ℕ∞))
    (hxsupp : dvSupp F x u ℓ = (m : ℕ∞))
    (hy : ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ)
    {hne' : (dvSideSet F (x + y) u ℓ).Nonempty} :
    dvHgt F (x + y) (dvSideMin F (x + y) u ℓ hne') = (Mx : ℕ∞) := by
  have hdeep : (m : ℕ∞) < dvSupp F y u ℓ :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hy
  have hset : dvSideSet F (x + y) u ℓ = dvSideSet F x u ℓ :=
    C131y.dvSideSet_add_deep F u hℓ hxsupp hdeep
  have hmin : dvSideMin F (x + y) u ℓ hne' = dvSideMin F x u ℓ hxne :=
    min'_congr' hset hne' hxne
  have hminmem : dvSideMin F x u ℓ hxne ∈ dvSideSet F x u ℓ := Finset.min'_mem _ _
  have hcoord := coord_lt_of_onSide_of_deep' F u hℓ hxsupp hdeep (dvOnSide_of_mem' hminmem)
  rw [hmin, C131y.dvHgt_add_eq_left_of_lt F hcoord, hMx]

/-- **MH.6, clause C (residual).** The perturbed polynomial's level residual polynomial, at
the shared pin `(hne', Mx, hpinM')`, equals the original's — the crux node. -/
theorem dv_resPoly_add_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {x y : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {hxne : (dvSideSet F x u ℓ).Nonempty} {Mx m : ℕ}
    (hMx : dvHgt F x (dvSideMin F x u ℓ hxne) = (Mx : ℕ∞))
    (hxsupp : dvSupp F x u ℓ = (m : ℕ∞))
    (hy : ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ)
    {hne' : (dvSideSet F (x + y) u ℓ).Nonempty}
    {hpinM' : dvHgt F (x + y) (dvSideMin F (x + y) u ℓ hne') = (Mx : ℕ∞)} :
    dvResPoly F H₀ hpin (x + y) u ℓ hne' Mx hpinM'
      = dvResPoly F H₀ hpin x u ℓ hxne Mx hMx := by
  have hdeep : (m : ℕ∞) < dvSupp F y u ℓ :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hy
  have hset : dvSideSet F (x + y) u ℓ = dvSideSet F x u ℓ :=
    C131y.dvSideSet_add_deep F u hℓ hxsupp hdeep
  have hmin : dvSideMin F (x + y) u ℓ hne' = dvSideMin F x u ℓ hxne :=
    min'_congr' hset hne' hxne
  have hmax : dvSideMax F (x + y) u ℓ hne' = dvSideMax F x u ℓ hxne :=
    max'_congr' hset hne' hxne
  have hdeg : dvSideDeg F (x + y) u ℓ hne' = dvSideDeg F x u ℓ hxne := by
    rw [dvSideDeg, dvSideDeg, hmin, hmax]
  rw [dvResPoly, dvResPoly, hdeg, hmin]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [dev_add_of_monic F.hmonic,
    C131ae.twistRead_add_eq_left_of_lt F hπ H₀ hpin
      (read_height_lt_of_deep' hℓ hcop hxsupp hdeep hxne hMx (Finset.mem_range.mp ht))]

/-- ★ **MH.6 — the perturbation law M4** (dv-twin of B41a's `pure_add_of_lt`; §4.3's
invariant-persistence mechanism). Adding `y` with `deg y < deg x` and `W(y) ≥ W(x) + 1`
(`W := dvSupp`) to a monic, level-pure `x` preserves monicity, degree, level purity, the
pinned height `M₀`, and the level residual `dvResPoly`. -/
theorem dv_pure_add_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {x y : Polynomial O} (hx : x.Monic) (hxpure : IsDvPure F x u ℓ)
    {hxne : (dvSideSet F x u ℓ).Nonempty} {Mx m : ℕ}
    (hMx : dvHgt F x (dvSideMin F x u ℓ hxne) = (Mx : ℕ∞))
    (hxsupp : dvSupp F x u ℓ = (m : ℕ∞))
    (hydeg : y.degree < x.degree)
    (hy : ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ) :
    (x + y).Monic ∧ (x + y).natDegree = x.natDegree ∧ IsDvPure F (x + y) u ℓ ∧
      ∃ hne' : (dvSideSet F (x + y) u ℓ).Nonempty,
      ∃ hpinM' : dvHgt F (x + y) (dvSideMin F (x + y) u ℓ hne') = (Mx : ℕ∞),
        dvResPoly F H₀ hpin (x + y) u ℓ hne' Mx hpinM'
          = dvResPoly F H₀ hpin x u ℓ hxne Mx hMx := by
  have hmon : (x + y).Monic := hx.add_of_left hydeg
  have hdegeq : (x + y).natDegree = x.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hydeg)
  have hpure : IsDvPure F (x + y) u ℓ :=
    dv_purity_add_of_lt F hℓ hxpure hxsupp hydeg hy
  have hne' : (dvSideSet F (x + y) u ℓ).Nonempty := ⟨0, hpure.1⟩
  have hheight : dvHgt F (x + y) (dvSideMin F (x + y) u ℓ hne') = (Mx : ℕ∞) :=
    dv_height_add_of_lt F hℓ hMx hxsupp hy
  refine ⟨hmon, hdegeq, hpure, hne', hheight, ?_⟩
  exact dv_resPoly_add_of_lt F hπ H₀ hpin hℓ hcop hMx hxsupp hy

end Uniformity.Density.Tower.C133mh0

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh0.stageHeight_key
#print axioms Uniformity.Density.Tower.C133mh0.twistExp_zero
#print axioms Uniformity.Density.Tower.C133mh0.twistRead_one
#print axioms Uniformity.Density.Tower.C133mh0.dv_purity_add_of_lt
#print axioms Uniformity.Density.Tower.C133mh0.dv_height_add_of_lt
#print axioms Uniformity.Density.Tower.C133mh0.dv_resPoly_add_of_lt
#print axioms Uniformity.Density.Tower.C133mh0.dv_pure_add_of_lt

end AxCheck
