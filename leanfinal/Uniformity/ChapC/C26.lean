/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C08
import Uniformity.ChapC.C23
import Uniformity.ChapC.C25

/-!
# Uniformity.ChapC.C26 — `R_λ` has degree `d` and nonzero constant term

**Chapter C, NODE C.26** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the
slot-exactness layer; the A-C.1 amendment set governs). **ENV-C1′** = ENV-C1 + `hπ` explicit
(finiteness of the residue field is *not* bound: nothing here counts residues). Two signed
declarations — B.30's level-1 route replayed one level up, at C.25's `dv`-carrier.

C.25 defines the level residual polynomial `R_λ ∈ K[Z]`, `K = F.stageField H₀ hpin`, as the
coefficient list

`R_λ = Σ_{t ≤ d} C (twistRead F H₀ hpin (M₀ − tu) (dev F.key f (j₁ + tℓ))) · Z^t`,

with `j₁ := dvSideMin F f u ℓ hne₂` the side's left endpoint, `d := dvSideDeg F f u ℓ hne₂` its
residual degree, and `M₀` the pinned height at `j₁`. **C.25 is a definition and asserts nothing.**
This node is where the shape is certified:

* `dvResPoly_coeff_eq_zero_iff` — clause (i): for `t ≤ d`, the `t`-th coefficient vanishes **iff**
  the lattice abscissa `j₁ + ℓt` is *off* the side (`¬ DvOnSide F f u ℓ (j₁ + ℓ * t)`);
* `natDegree_dvResPoly` — clauses (ii)/(iii): `natDegree R_λ = d` and `R_λ.coeff 0 ≠ 0`, i.e.
  `EFF.HE6.11`'s "so `R_λ` has degree `d` and `R_λ(0) ≠ 0`".

Both endpoint clauses fall out of (i) because the endpoints `j₁` and `j₁ + ℓd = dvSideMax` are
*members* of `dvSideSet` (`Finset.min'_mem` / `Finset.max'_mem`), hence on-side by construction.

## The proof, in the blueprint's two steps

**Step 1 — the side line (private `dv_side_line`).** Everything geometric is packaged in one
private lemma: for `t ≤ d`,

* `(M₀ − ut : ℕ) ≤ dvHgt F f (j₁ + ℓt)` — the abscissa's true height is never *below* the side
  line; and
* `DvOnSide F f u ℓ (j₁ + ℓt) ↔ dvHgt F f (j₁ + ℓt) = ((M₀ − ut : ℕ) : ℕ∞)` — it lies *on* the
  side exactly when the height meets the line.

The derivation is pure line arithmetic in `ℕ`, done after descending out of `ℕ∞`. `DvOnSide` is
C.07(a)'s equation `dvSupp = ℓ • dvHgt + u * j` (plus finiteness of the height), so any two
on-side abscissae satisfy `ℓH + uj = ℓH′ + uj′` (private `dvOnSide_nat_eq'`). Applying that to the
two endpoints, with C.08's `dvSideLen_eq` supplying `dvSideMax = j₁ + ℓd` (private
`dvSideMax_eq'`, the only consumer of `Nat.Coprime u ℓ`; `0 < ℓ` is used there and again for the
two `ℕ`-cancellations below), gives
`M₀ = H_d + ud`, hence `ut ≤ M₀` for every `t ≤ d`: **the `ℕ`-truncated subtraction in C.25's body
never truncates on the intended range.** The inequality half is then the `Finset.inf` bound
`dvSupp ≤ ℓ • dvHgt (j₁ + ℓt) + u(j₁ + ℓt)` (private `dvSupp_le'`, legal because
`j₁ + ℓt ≤ dvSideMax ≤ f.natDegree`), cancelled by `hℓ` down to `M₀ ≤ p + ut`; the `iff` half is
the same cancellation run as an equality. The `dvHgt = ⊤` case (the abscissa's development
coefficient is `0`) is discharged first: `⊤` is above everything and `DvOnSide`'s second conjunct
explicitly excludes it.

**Step 2 — reading the coefficient.** `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` extracts the
`t`-th coefficient of C.25's sum as `twistRead F H₀ hpin (M₀ − ut) (dev F.key f (j₁ + ℓt))` for
`t ≤ d` (and `0` for `t > d`, which is the degree bound in `natDegree_dvResPoly`). The ϖ-twist
`η⁻¹ ^ twistExp k` is a **unit** — C.19's stage letter is nonzero — so `twistRead = 0 ↔ slotRes = 0`
(private `twistRead_eq_zero_iff`) and the whole question reduces to C.21's normalized slot residue:

* **on-side ⇒ nonzero.** The height is *exactly* `M₀ − ut` by step 1, so C.23's slot lemma
  (`KeyFrame.slotRes_ne_zero`, the attained-height nonvanishing half) applies. Its degree
  hypothesis `deg (dev F.key f j) < e₁f₁ = D′` is B.03's `degree_dev_lt` at C.01's `hdeg`
  (private `natDegree_dev_lt`).
* **off-side ⇒ zero.** Then step 1 upgrades `≤` to `<`: the true height sits **strictly above**
  the side line, so every window slot's digit index `(k − (slotIdx k + e₁t)h)/e₁` undershoots that
  coefficient's valuation, `π^{index+1}` divides it, and B.22's `digAt_eq_zero_iff` makes every
  digit — hence the whole normalized sum — vanish (private `slotRes_eq_zero_of_lt`). This is
  B.24's junk-`0` discipline doing exactly the work C.25's docstring promised it would.

## Divergences and private helpers (none is a blueprint node; GC-6.5)

* **`isKey_X` re-declared `private`.** The D9 cure, as at C.04/C.12/C.19/C.21/C.23/C.44: private
  declarations are not importable, and this is what names the base `Field (resField X)` instance
  without which `K` has no field structure. Retires to a public copy at the RE-PLAN item, not
  silently.
* **`slotRes_eq_zero_of_lt`** is C.23's *missing* half — the vanishing direction of the slot
  lemma, stated for a strictly-undershooting index rather than an attained one. It is proved here
  rather than backported into C.23 because C.23's signature is signed and this is the only
  consumer; if a second consumer appears it should be hoisted (a RE-PLAN item).
* **`slotDigit_index_spec'`** is the arithmetic identity `e₁·((k − ih)/e₁) + ih = k` for
  `i = slotIdx k + e₁t` in the window — C.17's window membership plus C.16's class congruence,
  re-derived locally because C.21 keeps its copy private.
* **`pow_dvd_of_le_addVal`, `dvOnSide_of_mem'`, `le_natDegree_of_mem_dvSideSet`,
  `dvOnSide_iff_nat`, `dvSupp_le'`** are one-line `ℕ∞`/`Finset` bureaucracy with no mathematical
  content.

## What is NOT claimed here

Nothing ties `R_λ`'s roots to factors of `f`: the `EFF.HE6.11` gloss "`Z` is the class of
`y^ℓ/ϖ^u`" stays documentation (C.25's ⚠ FAITHFULNESS clause 1). The semantic tie is C.27 plus
the §5 laws. What this node licenses downstream is exactly the *shape* facts — degree `d`, unit
constant term, and the vanishing criterion — which is what C.29/C.33/C.61/C.66 and the §13 frame
audit consume.

**DEPENDS.** C.07 (`dvSideSet`, `dvSideMin`, `dvSideMax`, `dvSideDeg`) · C.08 (`dvSideLen_eq`, the
spacing) · C.19 (`stageLetter_ne_zero`, the twist unit) · C.20/C.21 (`slotRes` and its class
bookkeeping, through C.23) · C.22 (`twistRead`) ·
C.23 (`KeyFrame.slotRes_ne_zero`) · C.25 (`dvResPoly`, the object) · B.03 (`degree_dev_lt`) ·
B.08/B.15 (`addVal`) · B.22/B.24 (`digAt`, `digAt_eq_zero_iff`) — by committed node ID (GC-13(b)).
The three imports are `Uniformity.ChapC.C08`, `Uniformity.ChapC.C23`, `Uniformity.ChapC.C25`, which
between them pull the whole §3/§4 chain.

**PROOF.** Blueprint steps 1–2, as narrated above; the blueprint's "endpoints are on-side by
definition of min'/max'" is `Finset.min'_mem` / `Finset.max'_mem` and its "(iii) follows" is
`Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`.

SOURCE: `EFF.HE6.11` ("So `R_λ` has degree `d` and `R_λ(0) ≠ 0`"); B.30 (the level-1 twin whose
route is replayed).

**TEETH.** `W12-SHAPE`-family at level 1 is B.30's; the level-2 shape is guarded by blueprint
§13's frame audit (`R_λ = r²` with `r` quadratic at the `EFF.HE6R1.18` frame → the `q = 2` /
`q = 3` gate instances), which fires against these two declarations.

ENVIRONMENT: ENV-C1′ (`hπ` explicit — consumed twice: through `digAt_eq_zero_iff` in the vanishing
half, and through C.23 in the nonvanishing half).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

private theorem pow_dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

private theorem slotDigit_index_spec' (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + (F.slotIdx k + F.e₁ * t) * F.h = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact this.2
  have hdvd : F.e₁ ∣ k - (F.slotIdx k + F.e₁ * t) * F.h := by
    refine (Nat.modEq_iff_dvd' hle).mp ?_
    calc (F.slotIdx k + F.e₁ * t) * F.h
        = F.slotIdx k * F.h + F.e₁ * (t * F.h) := by ring
      _ ≡ F.slotIdx k * F.h + 0 [MOD F.e₁] :=
          Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr ⟨t * F.h, rfl⟩)
      _ = F.slotIdx k * F.h := by ring
      _ ≡ k [MOD F.e₁] := (F.slotIdx_spec k).2
  rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hle]

private theorem slotRes_eq_zero_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {A : Polynomial O} {k : ℕ} (hlt : (k : ℕ∞) < F.stageHeight A) :
    F.slotRes H₀ hpin k A = 0 := by
  classical
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  rw [KeyFrame.slotRes]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hspec := slotDigit_index_spec' F k t ht
  set i := F.slotIdx k + F.e₁ * t with hidef
  set m := (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ with hmdef
  -- The digit index sits strictly below the coefficient's valuation.
  have hval : ((m + 1 : ℕ) : ℕ∞) ≤ addVal O (A.coeff i) := by
    by_cases hile : i ≤ A.natDegree
    · have hle : F.stageHeight A ≤ F.e₁ • addVal O (A.coeff i) + ((F.h * i : ℕ) : ℕ∞) := by
        rw [hinf]
        exact Finset.inf_le (f := fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hile))
      have hlt' : (k : ℕ∞) < F.e₁ • addVal O (A.coeff i) + ((F.h * i : ℕ) : ℕ∞) :=
        lt_of_lt_of_le hlt hle
      rcases eq_or_ne (addVal O (A.coeff i)) ⊤ with hT | hT
      · rw [hT]; exact le_top
      · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hT
        rw [← hv] at hlt' ⊢
        rw [show F.e₁ • ((v : ℕ) : ℕ∞) + ((F.h * i : ℕ) : ℕ∞)
              = ((F.e₁ * v + F.h * i : ℕ) : ℕ∞) by push_cast [nsmul_eq_mul]; ring] at hlt'
        have hnat : k < F.e₁ * v + F.h * i := by exact_mod_cast hlt'
        have hmv : F.e₁ * m < F.e₁ * v := by
          have hstep : F.e₁ * m + i * F.h < F.e₁ * v + F.h * i := by rw [hspec]; exact hnat
          have hc : i * F.h = F.h * i := Nat.mul_comm i F.h
          omega
        have : m < v := Nat.lt_of_mul_lt_mul_left hmv
        exact_mod_cast this
    · have h0 : A.coeff i = 0 := A.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0, addVal_zero]
      exact le_top
  have hdvd1 : π ^ m ∣ A.coeff i :=
    pow_dvd_of_le_addVal hπ (le_trans (by exact_mod_cast Nat.le_succ m) hval)
  have hdvd2 : π ^ (m + 1) ∣ A.coeff i := pow_dvd_of_le_addVal hπ hval
  have hdig : digAt π m (A.coeff i) = 0 := (digAt_eq_zero_iff hπ hdvd1).mpr hdvd2
  rw [hdig, map_zero, map_zero, zero_mul]

private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  have hj' : j ∈ Finset.filter (DvOnSide F f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact (Finset.mem_filter.mp hj').2

private theorem le_natDegree_of_mem_dvSideSet {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : j ≤ f.natDegree := by
  classical
  have hj' : j ∈ Finset.filter (DvOnSide F f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj').1)

private theorem dvOnSide_nat_eq' {F : KeyFrame O π} {u ℓ : ℕ} {f : Polynomial O} {j j' H H' : ℕ}
    (hH : dvHgt F f j = (H : ℕ∞)) (hH' : dvHgt F f j' = (H' : ℕ∞))
    (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    ℓ * H + u * j = ℓ * H' + u * j' := by
  have hja : dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) := hj.1
  have hjb : dvSupp F f u ℓ = ℓ • dvHgt F f j' + (u * j' : ℕ∞) := hj'.1
  have e : ℓ • (H : ℕ∞) + (u * j : ℕ∞) = ℓ • (H' : ℕ∞) + (u * j' : ℕ∞) := by
    rw [← hH, ← hH', ← hja, hjb]
  have e' : ((ℓ * H + u * j : ℕ) : ℕ∞) = ((ℓ * H' + u * j' : ℕ) : ℕ∞) := by
    push_cast
    simpa [nsmul_eq_mul] using e
  exact_mod_cast e'

private theorem dvSideMax_eq' (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} (h : (dvSideSet F f u ℓ).Nonempty) :
    dvSideMax F f u ℓ h = dvSideMin F f u ℓ h + ℓ * dvSideDeg F f u ℓ h := by
  have hmax : dvSideMax F f u ℓ h ∈ dvSideSet F f u ℓ := Finset.max'_mem _ _
  have hle : dvSideMin F f u ℓ h ≤ dvSideMax F f u ℓ h := Finset.min'_le _ _ hmax
  have hlen := dvSideLen_eq F hℓ hcop h
  rw [dvSideLen] at hlen
  omega

private theorem dvOnSide_iff_nat {F : KeyFrame O π} {f : Polynomial O} {u ℓ j p : ℕ}
    (hp : dvHgt F f j = (p : ℕ∞)) {S : ℕ} (hS : dvSupp F f u ℓ = (S : ℕ∞)) :
    DvOnSide F f u ℓ j ↔ S = ℓ * p + u * j := by
  constructor
  · rintro ⟨h1, -⟩
    rw [hS, hp] at h1
    have h2 : ((S : ℕ) : ℕ∞) = ((ℓ * p + u * j : ℕ) : ℕ∞) := by
      rw [h1]; push_cast [nsmul_eq_mul]; ring
    exact_mod_cast h2
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hS, hp, h]; push_cast [nsmul_eq_mul]; ring
    · rw [hp]; exact ENat.coe_ne_top _

private theorem dvSupp_le' (F : KeyFrame O π) {f : Polynomial O} {u ℓ j : ℕ}
    (hj : j ≤ f.natDegree) :
    dvSupp F f u ℓ ≤ ℓ • dvHgt F f j + ((u * j : ℕ) : ℕ∞) := by
  rw [Nat.cast_mul]
  exact Finset.inf_le (f := fun i => ℓ • dvHgt F f i + (u * i : ℕ∞))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- **C.26, steps 1–2 (private) — the `dv`-side's line lies below the level polygon, with
equality exactly on the side.** B.30's `side_line` at C.06/C.07's carrier. -/
private theorem dv_side_line (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    ((M₀ - u * t : ℕ) : ℕ∞) ≤ dvHgt F f (dvSideMin F f u ℓ hne₂ + ℓ * t) ∧
      (DvOnSide F f u ℓ (dvSideMin F f u ℓ hne₂ + ℓ * t) ↔
        dvHgt F f (dvSideMin F f u ℓ hne₂ + ℓ * t) = ((M₀ - u * t : ℕ) : ℕ∞)) := by
  classical
  set j₀ := dvSideMin F f u ℓ hne₂ with hj₀def
  set d := dvSideDeg F f u ℓ hne₂ with hddef
  have hminmem : j₀ ∈ dvSideSet F f u ℓ := Finset.min'_mem _ _
  have hmaxmem : dvSideMax F f u ℓ hne₂ ∈ dvSideSet F f u ℓ := Finset.max'_mem _ _
  have honmin : DvOnSide F f u ℓ j₀ := dvOnSide_of_mem' hminmem
  have honmax : DvOnSide F f u ℓ (dvSideMax F f u ℓ hne₂) := dvOnSide_of_mem' hmaxmem
  have hmaxeq : dvSideMax F f u ℓ hne₂ = j₀ + ℓ * d := dvSideMax_eq' F hℓ hcop hne₂
  -- Step 1: `M₀ = Hd + u*d`, hence `u*t ≤ M₀` for every `t ≤ d`.
  obtain ⟨Hd, hHd⟩ := ENat.ne_top_iff_exists.mp honmax.2
  have hnat : ℓ * M₀ + u * j₀ = ℓ * Hd + u * dvSideMax F f u ℓ hne₂ :=
    dvOnSide_nat_eq' hpin₂ hHd.symm honmin honmax
  have hsum : ℓ * M₀ = ℓ * (Hd + u * d) := by
    refine Nat.add_right_cancel (m := u * j₀) ?_
    rw [hnat, hmaxeq]
    ring
  have hM₀d : M₀ = Hd + u * d := Nat.eq_of_mul_eq_mul_left hℓ hsum
  have hud : u * t ≤ M₀ := by
    refine le_trans (Nat.mul_le_mul_left u ht) ?_
    rw [hM₀d]
    exact Nat.le_add_left _ _
  -- Step 2: the `inf` bound at the lattice abscissa `j₀ + ℓ*t`.
  have hjtle : j₀ + ℓ * t ≤ f.natDegree := by
    refine le_trans ?_ (le_natDegree_of_mem_dvSideSet hmaxmem)
    rw [hmaxeq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left ℓ ht) _
  have hS : dvSupp F f u ℓ = ((ℓ * M₀ + u * j₀ : ℕ) : ℕ∞) := by
    have h1 : dvSupp F f u ℓ = ℓ • dvHgt F f j₀ + (u * j₀ : ℕ∞) := honmin.1
    rw [h1, hpin₂]
    push_cast [nsmul_eq_mul]
    ring
  have hSle := dvSupp_le' F (u := u) (ℓ := ℓ) hjtle
  rcases eq_or_ne (dvHgt F f (j₀ + ℓ * t)) ⊤ with hP | hP
  · refine ⟨by rw [hP]; exact le_top, iff_of_false (fun hon => hon.2 hP) ?_⟩
    intro heq
    rw [hP] at heq
    exact (ENat.coe_ne_top _) heq.symm
  · obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hP
    have honiff := dvOnSide_iff_nat (F := F) (f := f) (u := u) (ℓ := ℓ) hp.symm hS
    -- the `inf` inequality, in `ℕ`
    rw [hS, ← hp] at hSle
    have hSnat : ℓ * M₀ + u * j₀ ≤ ℓ * p + u * (j₀ + ℓ * t) := by
      have hcast : ℓ • ((p : ℕ) : ℕ∞) + ((u * (j₀ + ℓ * t) : ℕ) : ℕ∞)
          = ((ℓ * p + u * (j₀ + ℓ * t) : ℕ) : ℕ∞) := by
        push_cast [nsmul_eq_mul]
        ring
      rw [hcast] at hSle
      exact_mod_cast hSle
    have hmul : ℓ * M₀ ≤ ℓ * (p + u * t) := by
      have e : ℓ * p + u * (j₀ + ℓ * t) = ℓ * (p + u * t) + u * j₀ := by ring
      rw [e] at hSnat
      exact Nat.le_of_add_le_add_right hSnat
    have hle' : M₀ ≤ p + u * t := Nat.le_of_mul_le_mul_left hmul hℓ
    have hfinal : (ℓ * M₀ + u * j₀ = ℓ * p + u * (j₀ + ℓ * t)) ↔ (p = M₀ - u * t) := by
      constructor
      · intro e
        have e2 : ℓ * M₀ + u * j₀ = ℓ * (p + u * t) + u * j₀ := by rw [e]; ring
        have e3 : M₀ = p + u * t := Nat.eq_of_mul_eq_mul_left hℓ (Nat.add_right_cancel e2)
        omega
      · intro e
        have e3 : p + u * t = M₀ := by omega
        calc ℓ * M₀ + u * j₀ = ℓ * (p + u * t) + u * j₀ := by rw [e3]
          _ = ℓ * p + u * (j₀ + ℓ * t) := by ring
    refine ⟨?_, ?_⟩
    · rw [← hp]
      exact_mod_cast Nat.sub_le_iff_le_add.mpr hle'
    · rw [honiff, hfinal, ← hp]
      constructor
      · intro e; exact_mod_cast e
      · intro e; exact_mod_cast e

/-- **The twist factor is a unit**, so the ϖ-read vanishes exactly when the `n(k)`-read does. -/
private theorem twistRead_eq_zero_iff (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) (A : Polynomial O) :
    F.twistRead H₀ hpin k A = 0 ↔ F.slotRes H₀ hpin k A = 0 := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  have hη : F.stageLetter H₀ hpin ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  have hbody : F.twistRead H₀ hpin k A
      = (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A := rfl
  rw [hbody, mul_eq_zero]
  simp [hη]

/-- The `Φ′`-development of `f` sits below the frame key's degree `D′ = e₁f₁` (B.03), which is
exactly C.23's degree hypothesis. -/
private theorem natDegree_dev_lt (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) :
    (dev F.key f j).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  have hlt : (dev F.key f j).degree < F.key.degree := degree_dev_lt F.hmonic hpos f j
  rw [← F.hdeg]
  rcases eq_or_ne (dev F.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hpos
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rwa [Polynomial.degree_eq_natDegree F.hmonic.ne_zero] at hlt

/-! ### The signed declarations -/

/-- **C.26 (i) — a level residual coefficient vanishes exactly off the side.** -/
theorem dvResPoly_coeff_eq_zero_iff (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff t = 0
      ↔ ¬ DvOnSide F f u ℓ (dvSideMin F f u ℓ hne₂ + ℓ * t) := by
  classical
  obtain ⟨hle, honiff⟩ := dv_side_line F hℓ hcop hne₂ hpin₂ ht
  have hcoeff : (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff t
      = F.twistRead H₀ hpin (M₀ - u * t)
          (dev F.key f (dvSideMin F f u ℓ hne₂ + ℓ * t)) := by
    rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
      if_pos (Nat.lt_succ_of_le ht), Nat.mul_comm t u, Nat.mul_comm t ℓ]
  rw [hcoeff, twistRead_eq_zero_iff F hπ H₀ hpin]
  constructor
  · intro h0 hon
    exact F.slotRes_ne_zero hπ H₀ hpin (natDegree_dev_lt F f _) (honiff.mp hon) h0
  · intro hoff
    refine slotRes_eq_zero_of_lt F hπ H₀ hpin ?_
    refine lt_of_le_of_ne hle (fun hh => hoff (honiff.mpr hh.symm))

/-- **C.26 (ii)/(iii) — the level residual polynomial has degree `d` and nonzero constant
term.** -/
theorem natDegree_dvResPoly (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).natDegree = dvSideDeg F f u ℓ hne₂ ∧
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff 0 ≠ 0 := by
  classical
  have hzero : (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff 0 ≠ 0 := by
    rw [Ne, dvResPoly_coeff_eq_zero_iff F hπ H₀ hpin hℓ hcop hne₂ hpin₂ (Nat.zero_le _), not_not]
    have hmem : dvSideMin F f u ℓ hne₂ ∈ dvSideSet F f u ℓ := Finset.min'_mem _ _
    simpa using dvOnSide_of_mem' hmem
  have hlead : (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff (dvSideDeg F f u ℓ hne₂) ≠ 0 := by
    rw [Ne, dvResPoly_coeff_eq_zero_iff F hπ H₀ hpin hℓ hcop hne₂ hpin₂ le_rfl, not_not]
    have hmem : dvSideMax F f u ℓ hne₂ ∈ dvSideSet F f u ℓ := Finset.max'_mem _ _
    have hm := dvOnSide_of_mem' hmem
    rwa [dvSideMax_eq' F hℓ hcop hne₂] at hm
  have hdegle : (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).natDegree ≤ dvSideDeg F f u ℓ hne₂ := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]
  exact ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegle hlead, hzero⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dvResPoly_coeff_eq_zero_iff
#print axioms Uniformity.Density.Tower.natDegree_dvResPoly

end AxCheck
