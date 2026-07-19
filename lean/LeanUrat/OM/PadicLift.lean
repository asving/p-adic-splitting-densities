import Mathlib
import Mathlib.NumberTheory.Padics.RingHoms
import LeanUrat.OM.QuotientBox

/-!
# BUNDLE 3b — `PadicLift`: classifier pre-build infrastructure

B-independent plumbing for the Layer-B classifier (CLASSIFIER_BLUEPRINT.md §5):

* **`toZModPow` surjectivity** — `PadicInt.toZModPow N` hits every residue (`§5.2` ledger entry,
  "(none named) — DERIVABLE, 3 lines").
* **B.0 `toBox`** (`§2.1`) — reduce a monic `f : ℤ_[p][X]` of degree `n` to a level-`N` box polynomial
  `QuotientBox.monicBox p N n`, via `f.map (PadicInt.toZModPow N)`. Needs `0 < N` so the codomain
  `ZMod (p^N)` is nontrivial (`Monic.natDegree_map`).
* **L-W1 `toBox_boxReduceLE`** (`§4` glue) — the tower-coherence one-liner:
  reducing `toBox M f` down to level `N` is `toBox N f`.
* **B.1 `ZMod(p^N)`-native valuation / unit-residue** (`§5.3` resolution (ii)) — the "largest `k < N`
  with `p^k ∣ x`" valuation and the unit-residue map directly on `ZMod (p^N)`, so `boxCoeffData` can
  read coefficient data mod `p^N` without threading a `ℤ_[p]` lift-choice obligation. Built on
  `ZMod.val` + `Nat.factorization`, with the unit part `ordCompl[p] x.val` projected to `ZMod p`.

All declarations here are B-independent (do not touch the frozen `omStep`/`classify` STUBS) and are
intended to be `sorry`-free with the `[propext, Classical.choice, Quot.sound]` core only.
-/

namespace LeanUrat.OM.PadicLift

open Polynomial QuotientBox

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. `toZModPow` surjectivity -/

/-- **`PadicInt.toZModPow N` is surjective.** Every residue mod `p^N` is `toZModPow N` of some `ℤ_[p]`:
factor the natural-number cast `ℕ ↠ ZMod (p^N)` (`ZMod.natCast_zmod_surjective`) through
`toZModPow N (n : ℤ_[p]) = (n : ZMod (p^N))` (`map_natCast`). -/
theorem toZModPow_surjective (N : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) N) := by
  intro y
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective y
  exact ⟨(n : ℤ_[p]), map_natCast (PadicInt.toZModPow (p := p) N) n⟩

/-! ## 2. B.0 `toBox` and L-W1 tower coherence -/

/-- **B.0 `toBox`** (`CLASSIFIER_BLUEPRINT.md §2.1`). Reduce a monic degree-`n` polynomial
`f : ℤ_[p][X]` to the level-`N` box `QuotientBox.monicBox p N n`, by mapping coefficients through
`PadicInt.toZModPow N`. Monicity is preserved by `Monic.map`; the degree is preserved by
`Monic.natDegree_map`, which needs the codomain `ZMod (p^N)` nontrivial — supplied here by
`Fact (1 < p^N)` derived from `0 < N`. -/
noncomputable def toBox (n N : ℕ) (hN : 0 < N) (f : ℤ_[p][X]) (hf : f.Monic)
    (hdeg : f.natDegree = n) : QuotientBox.monicBox p N n :=
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  ⟨f.map (PadicInt.toZModPow (p := p) N),
    hf.map _, by rw [hf.natDegree_map, hdeg]⟩

@[simp] theorem toBox_val (n N : ℕ) (hN : 0 < N) (f : ℤ_[p][X]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    (toBox p n N hN f hf hdeg).1 = f.map (PadicInt.toZModPow (p := p) N) := rfl

/-- **L-W1 `toBox_boxReduceLE`** (`CLASSIFIER_BLUEPRINT.md §4`). The box-tower coherence:
reducing `toBox M f` down to level `N` (`N ≤ M`) recovers `toBox N f`. One line of
`Polynomial.map_map` + `PadicInt.zmod_cast_comp_toZModPow`; the box-reduction map
`Classifier.boxReduceLE` is `Polynomial.map (ZMod.castHom (pow_dvd_pow p h) _)`, so this is exactly
`boxReduceLE p N M n h hN (toBox M f) = toBox N f` at the underlying-polynomial level. -/
theorem toBox_map_castHom (n N M : ℕ) (h : N ≤ M) (hN : 0 < N) (f : ℤ_[p][X])
    (hf : f.Monic) (hdeg : f.natDegree = n) :
    ((toBox p n M (hN.trans_le h) f hf hdeg).1).map
        (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N)))
      = (toBox p n N hN f hf hdeg).1 := by
  simp only [toBox_val, Polynomial.map_map, PadicInt.zmod_cast_comp_toZModPow N M h]

/-! ## 3. B.1 — `ZMod(p^N)`-native valuation and unit-residue

`monicBox p N n` lives over `ZMod (p^N)`, which has no `PadicInt.valuation`/`unitCoeff`. We build a
native "valuation up to `N`" and a unit-residue map directly on `ZMod (p^N)` (blueprint §5.3
resolution (ii)), reading coefficient data through the canonical representative `ZMod.val : ZMod (p^N)
→ ℕ` and `Nat.factorization`. The unit part is `ordCompl[p] x.val = x.val / p^v`, projected to `ZMod p`.
-/

/-- **`ZMod(p^N)`-native valuation.** For `x : ZMod (p^N)`, the largest `k` with `p^k ∣ x`,
*capped at `N`*: `zmodValuation x = N` when `x = 0` (matching `p^N = 0`), otherwise the `p`-adic
valuation of the canonical representative `x.val`. For `x ≠ 0` this is `< N` (`zmodValuation_lt`). -/
noncomputable def zmodValuation (N : ℕ) (x : ZMod (p ^ N)) : ℕ :=
  if x = 0 then N else (x.val).factorization p

/-- **`ZMod(p^N)`-native unit residue.** The image in `ZMod p` of the unit part of `x`, i.e.
`ordCompl[p] x.val = x.val / p^(zmodValuation x)` cast to `ZMod p`. For `x ≠ 0` this is a unit
(nonzero), since `p ∤ ordCompl[p] x.val` (`zmodUnitResidue_ne_zero`). -/
noncomputable def zmodUnitResidue (N : ℕ) (x : ZMod (p ^ N)) : ZMod p :=
  ((ordCompl[p] x.val : ℕ) : ZMod p)

/-! ### Spec lemmas -/

omit hp in
@[simp] theorem zmodValuation_zero (N : ℕ) : zmodValuation p N (0 : ZMod (p ^ N)) = N := by
  simp [zmodValuation]

omit hp in
theorem zmodValuation_of_ne_zero {N : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0) :
    zmodValuation p N x = (x.val).factorization p := by
  simp [zmodValuation, hx]

/-- For `x ≠ 0` (with `0 < N`), the native valuation is genuinely `< N`. The canonical
representative `x.val` is a nonzero natural `< p^N`; if its `p`-valuation were `≥ N` then
`p^N ∣ x.val`, forcing `p^N ≤ x.val`, contradiction. -/
theorem zmodValuation_lt {N : ℕ} (_hN : 0 < N) {x : ZMod (p ^ N)} (hx : x ≠ 0) :
    zmodValuation p N x < N := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  rw [zmodValuation_of_ne_zero p hx]
  have hval0 : x.val ≠ 0 := by
    simpa [ZMod.val_eq_zero] using hx
  have hlt : x.val < p ^ N := ZMod.val_lt x
  by_contra hge
  rw [not_lt] at hge
  -- `p ^ N ∣ p ^ (x.val.factorization p) ∣ x.val`, hence `p ^ N ≤ x.val`, contradicting `x.val < p^N`.
  have hdvd : p ^ N ∣ x.val :=
    (pow_dvd_pow p hge).trans (Nat.ordProj_dvd x.val p)
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hval0) hdvd) (not_le.mpr hlt)

/-- For `x ≠ 0`, the unit-residue is nonzero in `ZMod p`: `p ∤ ordCompl[p] x.val`
(`Nat.not_dvd_ordCompl`), so its cast to `ZMod p` is nonzero. -/
theorem zmodUnitResidue_ne_zero {N : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0) :
    zmodUnitResidue p N x ≠ 0 := by
  have hval0 : x.val ≠ 0 := by
    simpa [ZMod.val_eq_zero] using hx
  have hnotdvd : ¬ p ∣ ordCompl[p] x.val := Nat.not_dvd_ordCompl hp.out hval0
  rw [zmodUnitResidue, Ne, ZMod.natCast_eq_zero_iff]
  exact hnotdvd

omit hp in
/-- The defining decomposition: `x.val = p ^ (zmodValuation x) * ordCompl[p] x.val` for `x ≠ 0`.
This couples `zmodValuation` (the height) and `zmodUnitResidue` (the unit part) back to the
canonical representative, the native analogue of `unitCoeff_spec`. -/
theorem zmod_val_eq_ordProj_mul_ordCompl {N : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0) :
    x.val = p ^ (zmodValuation p N x) * ordCompl[p] x.val := by
  rw [zmodValuation_of_ne_zero p hx]
  exact (Nat.ordProj_mul_ordCompl_eq_self x.val p).symm

omit hp in
/-- `p ^ (zmodValuation x) ∣ x.val` — the native "valuation lower bound on divisibility". -/
theorem ordProj_zmodValuation_dvd_val {N : ℕ} {x : ZMod (p ^ N)} (hx : x ≠ 0) :
    p ^ (zmodValuation p N x) ∣ x.val := by
  rw [zmodValuation_of_ne_zero p hx]
  exact Nat.ordProj_dvd x.val p

/-! ## 4. Layer A — one-digit (level `N+1 → N`) arithmetic stability

`CERTLEVEL_DECOMP.md` Layer A. The `ZMod`-native valuation and unit-residue are **stable** under the
single-step coefficient reduction `coeffReduce : ZMod(p^{N+1}) →+* ZMod(p^N)` *below the cutoff* —
i.e. whenever the `(N+1)`-level valuation is `< N`. (The naive "full representative `val` is stable"
claim is FALSE: `x.val = p^N + 1` has valuation `0 < N` but `x.val % p^N = 1 ≠ x.val`; only the
valuation and the unit-residue are stable, never the full `val`.)

`coeffReduce p N` is defined here as `ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p^N))`,
syntactically identical to `Classifier.coeffReduce` (the seam bridge in Layer B reconciles the two
distinct-but-defeq constants). -/

/-- **Single-step coefficient reduction** `ZMod(p^{N+1}) →+* ZMod(p^N)` (Layer A; defeq to
`Classifier.coeffReduce`). -/
noncomputable def coeffReduce (N : ℕ) :
    ZMod (p ^ (N + 1)) →+* ZMod (p ^ N) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p ^ N))

/-- **A0** (`CERTLEVEL_DECOMP.md` Layer A). The canonical representative of the reduction is the
representative of `x` reduced mod `p^N`: `(coeffReduce x).val = x.val % p^N`. (`castHom_apply` →
`cast`; `natCast_val` rewrites `cast x` as `((x.val:ℕ) : ZMod(p^N))`; `val_natCast` evaluates.) -/
theorem coeffReduce_val_eq (N : ℕ) (x : ZMod (p ^ (N + 1))) :
    (coeffReduce p N x).val = x.val % p ^ N := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  rw [coeffReduce, ZMod.castHom_apply, ← ZMod.natCast_val x, ZMod.val_natCast]

/-- **Arithmetic core (support guard, ℕ-level).** If `m ≠ 0` and `v_p(m) < N` then `m % p^N ≠ 0`:
`m % p^N = 0` means `p^N ∣ m`, forcing `N ≤ v_p(m)`, contradicting the cutoff. -/
theorem mod_ne_zero_of_factorization_lt {m N : ℕ} (hm : m ≠ 0)
    (hlt : m.factorization p < N) : m % p ^ N ≠ 0 := by
  intro h0
  have hdvd : p ^ N ∣ m := Nat.dvd_of_mod_eq_zero h0
  have : N ≤ m.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out hm).1 hdvd
  omega

/-- **Arithmetic core (valuation stability, ℕ-level).** Reducing mod `p^N` preserves the `p`-adic
valuation as long as it is below the cutoff: `v_p(m % p^N) = v_p(m)` when `v_p(m) < N`. Antisymmetry
through `pow_dvd_iff_le_factorization`, transferring `p^k`-divisibility across `% p^N` via
`Nat.dvd_mod_iff` (valid since `p^k ∣ p^N` for `k ≤ N`). -/
theorem factorization_mod_eq {m N : ℕ} (hm : m ≠ 0) (hlt : m.factorization p < N) :
    (m % p ^ N).factorization p = m.factorization p := by
  have hm' : m % p ^ N ≠ 0 := mod_ne_zero_of_factorization_lt p hm hlt
  set v := m.factorization p with hv
  apply le_antisymm
  · by_contra hge
    rw [not_le] at hge
    have h1 : p ^ (v + 1) ∣ m % p ^ N :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp.out hm').2 hge
    have h2 : p ^ (v + 1) ∣ m := (Nat.dvd_mod_iff (pow_dvd_pow p hlt)).1 h1
    have : v + 1 ≤ v := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hm).1 h2
    omega
  · have hpvm : p ^ v ∣ m := by have := Nat.ordProj_dvd m p; rwa [← hv] at this
    have hpd : p ^ v ∣ p ^ N := pow_dvd_pow p (le_of_lt hlt)
    have : p ^ v ∣ m % p ^ N := (Nat.dvd_mod_iff hpd).2 hpvm
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out hm').1 this

/-- **Arithmetic core (unit-residue stability, ℕ-level).** Reducing mod `p^N` preserves the unit
part *as a residue mod `p`*: `ordCompl[p] (m % p^N) ≡ ordCompl[p] m (mod p)` when `v_p(m) < N`.
Both representatives factor as `p^v · (unit)` over the *same* `p^v` (by `factorization_mod_eq`); they
are congruent mod `p^{v+1}` (since `m ≡ m % p^N (mod p^N)` and `v+1 ≤ N`); cancelling `p^v`
(`Nat.ModEq.mul_left_cancel'`) leaves the units congruent mod `p`. -/
theorem ordCompl_mod_cast_eq {m N : ℕ} (hm : m ≠ 0) (hlt : m.factorization p < N) :
    ((ordCompl[p] (m % p ^ N) : ℕ) : ZMod p) = ((ordCompl[p] m : ℕ) : ZMod p) := by
  have hm' : m % p ^ N ≠ 0 := mod_ne_zero_of_factorization_lt p hm hlt
  have hfac : (m % p ^ N).factorization p = m.factorization p := factorization_mod_eq p hm hlt
  set v := m.factorization p with hvdef
  have hdecomp_m : m = p ^ v * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hdecomp_m' : m % p ^ N = p ^ v * ordCompl[p] (m % p ^ N) := by
    have hordProj : ordProj[p] (m % p ^ N) = p ^ v := by rw [hfac]
    calc m % p ^ N
        = ordProj[p] (m % p ^ N) * ordCompl[p] (m % p ^ N) :=
          (Nat.ordProj_mul_ordCompl_eq_self (m % p ^ N) p).symm
      _ = p ^ v * ordCompl[p] (m % p ^ N) := by rw [hordProj]
  have hcong : p ^ v * ordCompl[p] m ≡ p ^ v * ordCompl[p] (m % p ^ N) [MOD p ^ (v + 1)] := by
    have hmodN : m ≡ m % p ^ N [MOD p ^ N] := (Nat.mod_modEq m (p ^ N)).symm
    have hcongN : m ≡ m % p ^ N [MOD p ^ (v + 1)] :=
      hmodN.of_dvd (pow_dvd_pow p hlt)
    rw [← hdecomp_m, ← hdecomp_m']
    exact hcongN
  have hcong2 : ordCompl[p] m ≡ ordCompl[p] (m % p ^ N) [MOD p] := by
    have hpvpos : p ^ v ≠ 0 := pow_ne_zero v hp.out.ne_zero
    have hrw : p ^ (v + 1) = p ^ v * p := by ring
    rw [hrw] at hcong
    exact Nat.ModEq.mul_left_cancel' hpvpos hcong
  rw [ZMod.natCast_eq_natCast_iff]
  exact hcong2.symm

/-- **A1** (`CERTLEVEL_DECOMP.md` Layer A, the headline primitive). The native valuation is stable
below the cutoff: if `zmodValuation (N+1) x < N` then
`zmodValuation N (coeffReduce x) = zmodValuation (N+1) x`. Both reduce to `Nat.factorization p` of
`x.val` resp. `x.val % p^N` (`zmodValuation_of_ne_zero`, `coeffReduce_val_eq`); these agree by
`factorization_mod_eq`. -/
theorem zmodValuation_reduce_stable (N : ℕ) (_hN : 0 < N) (x : ZMod (p ^ (N + 1)))
    (hx : zmodValuation p (N + 1) x < N) :
    zmodValuation p N (coeffReduce p N x) = zmodValuation p (N + 1) x := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero (N + 1) hp.out.ne_zero⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [zmodValuation] at hx
  have hval0 : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx0
  rw [zmodValuation_of_ne_zero p hx0] at hx
  have hred_val : (coeffReduce p N x).val = x.val % p ^ N := coeffReduce_val_eq p N x
  have hred_ne : coeffReduce p N x ≠ 0 := by
    rw [← ZMod.val_ne_zero (coeffReduce p N x), hred_val]
    exact mod_ne_zero_of_factorization_lt p hval0 hx
  rw [zmodValuation_of_ne_zero p hred_ne, hred_val,
      factorization_mod_eq p hval0 hx, zmodValuation_of_ne_zero p hx0]

/-- **A2** (`CERTLEVEL_DECOMP.md` Layer A). The native unit-residue is stable below the cutoff:
if `zmodValuation (N+1) x < N` then
`zmodUnitResidue N (coeffReduce x) = zmodUnitResidue (N+1) x`. Both unfold to the `ZMod p` cast of
`ordCompl[p]` of `x.val` resp. `x.val % p^N` (`coeffReduce_val_eq`); these agree by
`ordCompl_mod_cast_eq`. -/
theorem zmodUnitResidue_reduce_stable (N : ℕ) (_hN : 0 < N) (x : ZMod (p ^ (N + 1)))
    (hx : zmodValuation p (N + 1) x < N) :
    zmodUnitResidue p N (coeffReduce p N x) = zmodUnitResidue p (N + 1) x := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero (N + 1) hp.out.ne_zero⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [zmodValuation] at hx
  have hval0 : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx0
  rw [zmodValuation_of_ne_zero p hx0] at hx
  have hred_val : (coeffReduce p N x).val = x.val % p ^ N := coeffReduce_val_eq p N x
  rw [zmodUnitResidue, zmodUnitResidue, hred_val]
  exact ordCompl_mod_cast_eq p hval0 hx

/-- **A3** (`CERTLEVEL_DECOMP.md` Layer A, support nonvanishing transfer). If
`zmodValuation (N+1) x < N` then the reduction is nonzero: `coeffReduce x ≠ 0`. Via
`ZMod.val_ne_zero` and `coeffReduce_val_eq` this is exactly `x.val % p^N ≠ 0`
(`mod_ne_zero_of_factorization_lt`). -/
theorem coeffReduce_ne_zero_of_val_lt (N : ℕ) (_hN : 0 < N) (x : ZMod (p ^ (N + 1)))
    (hx : zmodValuation p (N + 1) x < N) :
    coeffReduce p N x ≠ 0 := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩
  haveI : NeZero (p ^ (N + 1)) := ⟨pow_ne_zero (N + 1) hp.out.ne_zero⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [zmodValuation] at hx
  have hval0 : x.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hx0
  rw [zmodValuation_of_ne_zero p hx0] at hx
  have hred_val : (coeffReduce p N x).val = x.val % p ^ N := coeffReduce_val_eq p N x
  rw [← ZMod.val_ne_zero (coeffReduce p N x), hred_val]
  exact mod_ne_zero_of_factorization_lt p hval0 hx

end LeanUrat.OM.PadicLift
