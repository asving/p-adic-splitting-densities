/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C133mh3
import Mathlib

/-!
# Uniformity.ChapC.C133mh12 — `[MH12 2026-08-28]`: defect-vanishing, no-far-primes, Gauss descent

**Node MH.12** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §9's node table: "§6.1
defect-vanishing + no-far-primes; Gauss descent (mathlib `IsIntegrallyClosed` search)";
named inputs **MH.2** (Theorem M clauses 1–2, landed `C133mh3.dvSideMin_mul` /
`dvSideMax_mul` / `dvSideDeg_mul`) **+ mathlib**; sized 60–110 lines; feeds **MH.13**
(Theorem C placement)). Source: doc §6.1 (lines ~814–823) plus the (B1) argument of §5
that §6.1 explicitly generalizes.

## What this node proves (three self-contained lemmas)

1. **Defect-vanishing** (`dvSideMax_tight_and_dvd_of_isDvPure_mul`, §6.1 paragraph 1 /
   the (B1) mechanism, made symmetric in the two cofactors). If `x = y·z` is a monic
   product, `x` is level-pure (`IsDvPure F x u ℓ`), and `D′ := F.e₁ * F.f₁` divides
   `x.natDegree`, then **both** cofactors are `D′`-divisible and **both** have their
   `dvSideMax` reading exactly `natDegree / D′` (no floor defect on either side). The doc
   states the consequence only for "whenever `y` is pure"; the proof below shows purity of
   `y` (or `z`) is never used — the additivity law (MH.2) plus the elementary "sum of two
   `≤`-bounded naturals that add up to the untruncated total forces each bound tight, and
   the total's own divisibility forces both remainders to vanish" arithmetic
   (`nat_defect_vanishing`) does the whole job symmetrically. This is strictly the (B1)
   argument of §5 with `a', b'` renamed `y, z` and the pure-`a'` reading dropped as
   unnecessary.

2. **No-far-primes** (`natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero` +
   the contradiction corollary `not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos`,
   §6.1 paragraph 2). A "far" (point-sided: `dvSideDeg F q u ℓ hnq = 0`) monic factor `q`
   of a level-pure `D′`-divisible `x = q·w` is forced to `q.natDegree = 0`: `dvSideMin`
   additivity inside the pure `x` pins `dvSideMin(q) = 0`; the point hypothesis, via the
   landed exact spacing law `dvSideLen_eq` (C.08), then pins `dvSideMax(q) = dvSideMin(q)
   = 0`; and lemma 1 above reads `q.natDegree = D′ · dvSideMax(q) = 0` off the now-tight
   cap. A genuine (positive-degree) prime factor cannot be far — the contradiction
   corollary packages exactly that use.

3. **Gauss descent** (`exists_monic_map_eq_of_dvd_map`, §6.2's mathlib-search input). A
   monic divisor, over the fraction field `K₀`, of the image of a monic `O[x]`-polynomial
   is itself the image of a monic `O[x]`-polynomial. Classical Gauss's-lemma territory,
   executed against the pinned mathlib API rather than re-derived: every coefficient of
   the `K₀`-divisor is integral over `O`
   (`Polynomial.isIntegral_coeff_of_dvd`, `Mathlib.RingTheory.Polynomial.IsIntegral`), `O`
   — a DVR, hence `IsIntegrallyClosed` (the instance resolves from the DVR hypotheses
   exactly as `C130lb.lean`'s docstring records for the neighboring Gauss-lemma
   transport) — supplies the preimage of each coefficient
   (`IsIntegrallyClosed.isIntegral_iff`), and `Polynomial.lifts_and_degree_eq_and_monic`
   reassembles the coefficientwise preimages into one monic polynomial with the right
   image. No new mathematics; the doc's own framing ("classical, not new") is followed
   literally — this is a ~10-line application, not a re-proof of Gauss's lemma.

## What this node does NOT do

The `∏ᵢ qᵢ` factorization of a squarefree `O[x]`-divisor into `K₀[x]`-irreducibles (§6.2's
"Over `K₀ := FractionField O`, `K₀[x]` is a PID; `fS' ∣ f` squarefree ⟹ `fS' = ∏ᵢ qᵢ`
…") and the per-prime placement argument that consumes lemmas 1–3 above are **MH.13's**
job (Theorem C placement), not this node's: MH.12 supplies the three reusable primitives,
MH.13 assembles them against the actual `UniqueFactorizationMonoid`/`Squarefree` API.

## Status

Sorry-free; footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh12

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

/-! ## A purely arithmetic core (no frame content) -/

/-- **The defect-vanishing arithmetic core.** If `qA ≤ A/D`, `qB ≤ B/D`, `qA+qB = k`, and
`A+B = D*k` (i.e. `D ∣ A+B` witnessed by `k`), then BOTH bounds are tight (`qA = A/D`,
`qB = B/D`) and `D` divides `A` and `B` individually. Pure `ℕ` division/remainder algebra;
`Nat.div_add_div_le_add_div` (`a/D+b/D ≤ (a+b)/D`, always true) is the one external fact,
squeezed against the given `≤`s and the exact division `(A+B)/D = k`. -/
private theorem nat_defect_vanishing {D A B qA qB k : ℕ} (hD : 0 < D)
    (hqA : qA ≤ A / D) (hqB : qB ≤ B / D)
    (hsum : qA + qB = k) (hk : A + B = D * k) :
    qA = A / D ∧ qB = B / D ∧ D ∣ A ∧ D ∣ B := by
  have hfloor : A / D + B / D ≤ (A + B) / D := Nat.div_add_div_le_add_div
  have hkeq : (A + B) / D = k := by
    rw [hk]; exact Nat.mul_div_cancel_left k hD
  have hle : k ≤ A / D + B / D := by omega
  have heq : A / D + B / D = k := by omega
  have hqAeq : qA = A / D := by omega
  have hqBeq : qB = B / D := by omega
  have hAeq : D * (A / D) + A % D = A := Nat.div_add_mod A D
  have hBeq : D * (B / D) + B % D = B := Nat.div_add_mod B D
  have hDk : D * (A / D) + D * (B / D) = D * k := by rw [← Nat.mul_add, heq]
  have hmodsum : A % D + B % D = 0 := by omega
  have hAmod : A % D = 0 := by omega
  have hBmod : B % D = 0 := by omega
  exact ⟨hqAeq, hqBeq, Nat.dvd_of_mod_eq_zero hAmod, Nat.dvd_of_mod_eq_zero hBmod⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## §6.1 paragraph 1 — defect-vanishing -/

/-- ★ **MH.12, defect-vanishing (§6.1, paragraph 1; generalizes the (B1) argument of §5).**
If `x = y·z` is a monic product, `x` is level-pure (`IsDvPure F x u ℓ`), and
`D′ := F.e₁ * F.f₁` divides `x.natDegree`, then BOTH cofactors are forced `D′`-divisible
and BOTH have their `dvSideMax` reading tight against the floor bound `natDegree / D′` —
with NO purity hypothesis on `y` or `z` individually (only on the product `y * z`). -/
theorem dvSideMax_tight_and_dvd_of_isDvPure_mul
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {y z : Polynomial O} (hy : y.Monic) (hz : z.Monic)
    (hpure : IsDvPure F (y * z) u ℓ) (hdvd : (F.e₁ * F.f₁) ∣ (y * z).natDegree)
    (hny : (dvSideSet F y u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty) :
    dvSideMax F y u ℓ hny = y.natDegree / (F.e₁ * F.f₁) ∧
      dvSideMax F z u ℓ hnz = z.natDegree / (F.e₁ * F.f₁) ∧
      (F.e₁ * F.f₁) ∣ y.natDegree ∧ (F.e₁ * F.f₁) ∣ z.natDegree := by
  set D := F.e₁ * F.f₁ with hDdef
  have hDpos : 0 < D := Nat.mul_pos F.he₁ F.hf₁
  have hnyz : (dvSideSet F (y * z) u ℓ).Nonempty :=
    dvSideSet_nonempty F (hy.mul hz).ne_zero u hℓ
  have hImax : dvSideMax F (y * z) u ℓ hnyz = (y * z).natDegree / D :=
    dvSideMax_eq_of_isDvPure hpure hnyz
  have hIImax : dvSideMax F (y * z) u ℓ hnyz
      = dvSideMax F y u ℓ hny + dvSideMax F z u ℓ hnz :=
    C133mh3.dvSideMax_mul hπ hh H₀ hpin hℓ hcop hfloor hy.ne_zero hz.ne_zero hny hnz hnyz
  have hIIIy : dvSideMax F y u ℓ hny ≤ y.natDegree / D :=
    le_natDegree_div_of_mem_dvSideSet F (Finset.max'_mem _ hny)
  have hIIIz : dvSideMax F z u ℓ hnz ≤ z.natDegree / D :=
    le_natDegree_div_of_mem_dvSideSet F (Finset.max'_mem _ hnz)
  have hmuldeg : (y * z).natDegree = y.natDegree + z.natDegree :=
    Polynomial.natDegree_mul hy.ne_zero hz.ne_zero
  obtain ⟨k, hk⟩ := hdvd
  have hsum : dvSideMax F y u ℓ hny + dvSideMax F z u ℓ hnz = k := by
    rw [← hIImax, hImax, hk]
    exact Nat.mul_div_cancel_left k hDpos
  have hkAB : y.natDegree + z.natDegree = D * k := by rw [← hmuldeg, hk]
  obtain ⟨hqA, hqB, hdA, hdB⟩ := nat_defect_vanishing hDpos hIIIy hIIIz hsum hkAB
  exact ⟨hqA, hqB, hdA, hdB⟩

/-! ## §6.1 paragraph 2 — no-far-primes -/

/-- ★ **MH.12, no-far-primes (§6.1, paragraph 2).** A "far" (point-sided:
`dvSideDeg F q u ℓ hnq = 0`) monic factor `q` of a level-pure, `D′`-divisible `x = q·w` is
forced to degree `0`: `dvSideMin(q)` is pinned to `0` by additivity inside the pure `x`
(`C133mh3.dvSideMin_mul` + `dvSideMin_eq_zero_of_isDvPure`); the point hypothesis, via the
landed exact spacing law `dvSideLen_eq` (C.08), then pins `dvSideMax(q) = dvSideMin(q) =
0`; and the defect-vanishing lemma above reads `q.natDegree = D′ · dvSideMax(q) = 0` off
the now-tight cap. -/
theorem natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {q w : Polynomial O} (hq : q.Monic) (hw : w.Monic)
    (hpure : IsDvPure F (q * w) u ℓ) (hdvd : (F.e₁ * F.f₁) ∣ (q * w).natDegree)
    (hnq : (dvSideSet F q u ℓ).Nonempty) (hpt : dvSideDeg F q u ℓ hnq = 0) :
    q.natDegree = 0 := by
  set D := F.e₁ * F.f₁ with hDdef
  have hDpos : 0 < D := Nat.mul_pos F.he₁ F.hf₁
  have hnqw : (dvSideSet F (q * w) u ℓ).Nonempty :=
    dvSideSet_nonempty F (hq.mul hw).ne_zero u hℓ
  have hnw : (dvSideSet F w u ℓ).Nonempty := dvSideSet_nonempty F hw.ne_zero u hℓ
  have hminqw : dvSideMin F (q * w) u ℓ hnqw = 0 := dvSideMin_eq_zero_of_isDvPure hpure hnqw
  have hminsum : dvSideMin F (q * w) u ℓ hnqw
      = dvSideMin F q u ℓ hnq + dvSideMin F w u ℓ hnw :=
    C133mh3.dvSideMin_mul hπ hh H₀ hpin hℓ hfloor hq.ne_zero hw.ne_zero hnq hnw hnqw
  have hminq : dvSideMin F q u ℓ hnq = 0 := by omega
  have hlen : dvSideLen F q u ℓ hnq = ℓ * dvSideDeg F q u ℓ hnq := dvSideLen_eq F hℓ hcop hnq
  rw [dvSideLen, hpt, Nat.mul_zero] at hlen
  have hmaxq : dvSideMax F q u ℓ hnq = 0 := by omega
  obtain ⟨hqmax, -, hqdvd, -⟩ :=
    dvSideMax_tight_and_dvd_of_isDvPure_mul hπ hh H₀ hpin hℓ hcop hfloor hq hw hpure hdvd hnq hnw
  rw [← hDdef] at hqmax hqdvd
  rw [hmaxq] at hqmax
  obtain ⟨m, hm⟩ := hqdvd
  have hdivm : q.natDegree / D = m := by rw [hm]; exact Nat.mul_div_cancel_left m hDpos
  have hm0 : m = 0 := by omega
  rw [hm0, Nat.mul_zero] at hm
  exact hm

/-- ★ **MH.12, no-far-primes, contradiction form.** A monic factor `q` of POSITIVE degree
dividing a level-pure, `D′`-divisible `x = q·w` cannot be "far" (point-sided): this is the
form §6.1's prose actually applies ("`q` is a unit — contradiction"). -/
theorem not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {q w : Polynomial O} (hq : q.Monic) (hw : w.Monic)
    (hpure : IsDvPure F (q * w) u ℓ) (hdvd : (F.e₁ * F.f₁) ∣ (q * w).natDegree)
    (hnq : (dvSideSet F q u ℓ).Nonempty) (hqpos : 0 < q.natDegree) :
    dvSideDeg F q u ℓ hnq ≠ 0 := by
  intro hpt
  have hz0 := natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero
    hπ hh H₀ hpin hℓ hcop hfloor hq hw hpure hdvd hnq hpt
  omega

/-! ## §6.2's mathlib input — Gauss descent -/

/-- ★ **MH.12, Gauss descent (§6.2's mathlib `IsIntegrallyClosed` search).** A monic
divisor, over a fraction field `Kv` of `O`, of the image of a monic `O[x]`-polynomial is
itself the image of a monic `O[x]`-polynomial. Every coefficient of the `Kv`-divisor is
integral over `O` (`Polynomial.isIntegral_coeff_of_dvd`); `O` — a DVR, hence
`IsIntegrallyClosed` (the instance resolves from the DVR hypotheses, exactly as at
`C130lb.lean`'s neighboring Gauss-lemma transport) — supplies the preimage of each
coefficient (`IsIntegrallyClosed.isIntegral_iff`); `Polynomial.lifts_and_degree_eq_and_monic`
reassembles the coefficientwise preimages into one monic polynomial with the right image.
Classical Gauss's-lemma territory, executed against the pinned mathlib API — no new
mathematics. -/
theorem exists_monic_map_eq_of_dvd_map
    {Kv : Type*} [Field Kv] [Algebra O Kv] [IsFractionRing O Kv]
    {f : Polynomial O} (hf : f.Monic) {q : Polynomial Kv} (hq : q.Monic)
    (hdvd : q ∣ f.map (algebraMap O Kv)) :
    ∃ q' : Polynomial O, q'.Monic ∧ q'.map (algebraMap O Kv) = q := by
  have hcoeff : ∀ i, IsIntegral O (q.coeff i) :=
    Polynomial.isIntegral_coeff_of_dvd f q hf hq hdvd
  have hlifts : q ∈ Polynomial.lifts (algebraMap O Kv) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsIntegrallyClosed.isIntegral_iff.mp (hcoeff n)
  obtain ⟨q', hmap, _hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hq
  exact ⟨q', hmon, hmap⟩

end Uniformity.Density.Tower.C133mh12

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh12.dvSideMax_tight_and_dvd_of_isDvPure_mul
#print axioms Uniformity.Density.Tower.C133mh12.natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero
#print axioms Uniformity.Density.Tower.C133mh12.not_dvSideDeg_eq_zero_of_isDvPure_mul_of_natDegree_pos
#print axioms Uniformity.Density.Tower.C133mh12.exists_monic_map_eq_of_dvd_map

end AxCheck
