/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132nv3
import Uniformity.ChapC.C130np5

/-!
# Uniformity.ChapC.C132nv3b — closing `Dv2ResSurv`'s slot-0 equality; slot-1 BLOCKED at `(5,2)` (μ₃ campaign, node M3-NV3b)

**[M3-NV3b, 2026-08-27]**: discharges (partially — see below) the honest gap `C132nv3`
(node M3-NV3) recorded against `C132nv2.Dv2ResSurv` (`C132nv2.lean:220-233`, the ONLY spec
that matters) at the S2 instance `L := (s2Tower h2 hq).levelDatum h2`,
`Ψ := Φ₂ := s2DepthTwoKeyAt h2 hq 2`, `(u₂, ℓ₂) = (5, 2)`.

`Dv2ResSurv` needs, for `A B` of degree `< Ψ.natDegree` with `dv2Hgt L A = Ha`,
`dv2Hgt L B = Hb`: **(1)** `dv2Hgt L (dev Ψ (A*B) 0) = Ha + Hb` (EQUALITY); **(2)**
`ℓ₂ • (Ha+Hb) + 1 ≤ ℓ₂ • dv2Hgt L (dev Ψ (A*B) 1) + u₂` (the strict carry bound).

## Half 1 — DISCHARGED: the slot-0 equality

`C132nv3` proved only `≤` (`s2_dvSupp_mul_modByComposedKey_le`). The missing `≥` closes with
the SAME mechanism, run on the REMAINDER `r := (a·b) %ₘ Φ₂` instead of on the two factors:
`s2_dvSupp_mul` (unconditional S2 multiplicativity) gives `dvSupp(a·b) = Ha+Hb` outright, so
proving `Ha+Hb ≤ dvSupp(r)` finishes the job. Writing `a·b = r + Φ₂·q₀`
(`Polynomial.modByMonic_add_div`): if `dvSupp(r) < dvSupp(a·b)`, ultrametric case analysis
(no ties possible without deriving `dvSupp(r) = dvSupp(Φ₂·q₀)` exactly first) forces
`S2InitialEquiv r (-(Φ₂·q₀))`, i.e. `Φ₂ ∣_µ r`. But `r` has degree `< 4`
(`Polynomial.natDegree_modByMonic_lt`, no monic-factorization argument needed — unlike
`C132nv3`'s proof, `r` is a SINGLE polynomial, not a product, so only `S2MuMinimal` is used,
not `S2MuIrreducible`'s prime clause) and, if `r ≠ 0`, `S2MuMinimal Φ₂` (already packaged
inside `s2Φ₂_keyPoly`) directly excludes `Φ₂ ∣_µ r` — contradiction. `r = 0` is the trivial
`⊤`-RHS case. Lands as `s2_dvSupp_mul_modByComposedKey_eq` and its `dv2Hgt`-shaped corollary
`dv2Hgt_dev_composedKey_mod_eq`, which matches `Dv2ResSurv`'s slot-0 clause VERBATIM.

## Half 2 — BLOCKED at `(u₂,ℓ₂) = (5,2)`: the slot-1 carry bound

The SAME computation, run once slot 0 is known (`dvSupp(a·b) = dvSupp(r) = Ha+Hb`), gives a
SHARP bound with NO case split: `min(dvSupp(a·b), dvSupp(r)) ≤ dvSupp(Φ₂·q₀)` collapses
(the two arguments of `min` being equal) to `Ha+Hb ≤ dvSupp(Φ₂·q₀) = dvSupp(Φ₂) + Hq₀`
(`s2_dvSupp_mul`, `Hq₀` the quotient digit's own height). **`dvSupp (s2Frame h2 hq) Φ₂ 5 2 =
10` is ALREADY LANDED** (`C130np5.dvSupp_composedKey_s2Tower`, via the `rfl` bridge
`s2DepthTwoKeyAt_two`) — so the landed-fact-derived bound is exactly `Ha + Hb ≤ Hq₀ + 10`
(proved below as `s2_le_composedKey_quot_add`). This bound is TIGHT: nothing landed excludes
`dvSupp(r) = dvSupp(Φ₂·q₀)` (the tie case), so `Hq₀ = Ha+Hb-10` is not landed-forbidden and
the bound cannot be sharpened by re-running the SAME argument.

`Dv2ResSurv`'s clause 2 at `u₂=5, ℓ₂=2` needs `2(Ha+Hb)+1 ≤ 2Hq₀+5`, i.e. `Ha+Hb ≤ Hq₀+2` —
**8 tighter** than the landed `Ha+Hb ≤ Hq₀+10`. No landed fact supplies this: the corpus's
only numeral for `Φ₂`'s own grade at these numerals is the `10` above (nothing bounds it by
`2`), and the `Ha+Hb≤Hq₀+10` bound's own tightness means no restructuring of this argument
alone closes an 8-wide gap. Discharging clause 2 at `(5,2)` would need a genuinely finer
graded-residual fact about `Φ₂`'s leading behaviour relative to a `Ψ`-quotient — the μ₃
graded-residual apparatus (`M3-RP0` onward), which does not exist in the corpus yet (per
`C132nv3`'s own honesty note). **BLOCKED-BECAUSE**: `Dv2ResSurv L Φ₂ 5 2`'s slot-1 clause
needs `Ha+Hb ≤ Hq₀+2`; landed facts give only the tight `Ha+Hb ≤ Hq₀+10`; the gap is a
missing numeral/finer bound, not a proof-search failure.

**Cross-check, not part of the charge**: the identical argument closes cleanly at
`(u₂,ℓ₂) = (21,2)` — the numeral pair the μ₃ campaign's own row M3-NV1 already fixes for
`s2Hgt₃` (`dv2Supp L Φ₂ g 21 2`, `C132nv1`), matching the independently-landed
`s2Hgt₃ Φ₂ = 21`. Proved as `s2_dv2ResSurv_slot1_at_21` below, to pin the exact threshold
and confirm the argument itself (not merely the numeral choice) is sound. This strongly
suggests `(u₂,ℓ₂)=(5,2)` is simply the wrong instantiation for this row; a follow-up node
should confirm the μ₃ campaign in fact needs `Dv2ResSurv` at `(21,2)`.

## What this file does NOT claim

`Dv2ResSurv ((s2Tower h2 hq).levelDatum h2) Φ₂ 5 2` is NOT stated as discharged (it cannot
be, at `(5,2)`, from landed facts) — only its slot-0 half, plus the diagnostic slot-1 facts
and the `(21,2)` cross-check, are landed as separate theorems.

## DEPENDS

C132nv3 (`s2_dvSupp_mul_modByComposedKey_le`, `s2Φ₂_keyPoly`) · C130nv3 (`s2_dvSupp_mul`) ·
C130kp0 (`S2MuMinimal`, `S2MuDvd`, `S2InitialEquiv`) · C130s6 (`dvSupp` ultrametric bank,
`s2Hgt₂_eq_dvSupp`, `s2Hgt₂_eq_dv2Hgt`, `toZ_inj`) · C130rp0 (`toZ_lt_toZ_iff`) · C130np5
(`dvSupp_composedKey_s2Tower` = 10) · C130s2 (`s2DepthTwoKeyAt_two`) · C132nv1
(`s2Φ₂_monic`, `s2Φ₂_natDegree`) · C.11 (`dv2Hgt`) · B.02 (`dev`) · mathlib
(`Polynomial.natDegree_modByMonic_lt`, `natDegree_divByMonic`, `modByMonic_eq_self_iff`,
`natDegree_mul_le`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no statement invented beyond what is
documented above; no `Dv2ResSurv` term is claimed at `(5,2)`.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_dvSupp_mul_modByComposedKey_eq`, `dv2Hgt_dev_composedKey_mod_eq`,
`s2_le_composedKey_quot_add`, `s2_dv2ResSurv_slot1_at_21`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv3b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130kp0
open Uniformity.Density.Tower.C130kp5 Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv3 Uniformity.Density.Tower.C130np5
open Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130nv2 (dev_zero_pin)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — the `dv2Hgt`/`dvSupp` bridge (a local re-derivation; `C132nv3`'s copy is
`private` and hence not visible from this file) -/

/-- the `dvSupp`/`dv2Hgt` bridge at the S2 level datum — the SAME anti-drift identity
`s2Hgt₂_eq_dv2Hgt`/`s2Hgt₂_eq_dvSupp` `C132nv3` already used under this name. -/
private theorem dv2Hgt_eq_dvSupp_local (A : Polynomial O) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = dvSupp (s2Frame h2 hq) A 5 2 :=
  C130s6.toZ_inj ((s2Hgt₂_eq_dv2Hgt h2 hq A).symm.trans (s2Hgt₂_eq_dvSupp h2 hq A))

/-! ## Part 1 — ★ the slot-0 EQUALITY -/

/-- ★ **The missing `≥` half of `C132nv3`'s survival core**, giving EQUALITY: for `a, b` of
degree `< 4`, reduction modulo `Φ₂` preserves the product endpoint value EXACTLY. -/
theorem s2_dvSupp_mul_modByComposedKey_eq (a b : Polynomial O)
    (ha : a.natDegree < 4) (hb : b.natDegree < 4) :
    dvSupp (s2Frame h2 hq) ((a * b) %ₘ (s2DepthTwoKeyAt h2 hq 2)) 5 2
      = dvSupp (s2Frame h2 hq) a 5 2 + dvSupp (s2Frame h2 hq) b 5 2 := by
  set F := s2Frame h2 hq with hF
  set Ψ := s2DepthTwoKeyAt h2 hq 2 with hΨ
  refine le_antisymm (s2_dvSupp_mul_modByComposedKey_le h2 hq a b ha hb) ?_
  rw [← s2_dvSupp_mul h2 hq a b]
  set r := (a * b) %ₘ Ψ with hrdef
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, dvSupp_zero_eq_top F 5 (by norm_num)]
    exact le_top
  set q0 := (a * b) /ₘ Ψ with hq0def
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  have hΨmonic : Ψ.Monic := s2Φ₂_monic h2 hq
  have hΨdeg : Ψ.natDegree = 4 := s2Φ₂_natDegree h2 hq
  have hΨne1 : Ψ ≠ 1 := by
    intro h1
    rw [h1, Polynomial.natDegree_one] at hΨdeg
    omega
  have hrdeg : r.natDegree < 4 := by
    have h := Polynomial.natDegree_modByMonic_lt (a * b) hΨmonic hΨne1
    rwa [hΨdeg] at h
  by_contra hcon
  rw [not_le] at hcon
  have htie : dvSupp F r 5 2 = dvSupp F (Ψ * q0) 5 2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heqX : dvSupp F (a * b) 5 2 = dvSupp F r 5 2 := by
        rw [← hab]
        exact dvSupp_add_eq_of_lt F (by norm_num) hlt
      rw [heqX] at hcon
      exact lt_irrefl _ hcon
    · have heqX : dvSupp F (a * b) 5 2 = dvSupp F (Ψ * q0) 5 2 := by
        rw [← hab, add_comm]
        exact dvSupp_add_eq_of_lt F (by norm_num) hgt
      rw [heqX] at hcon
      exact lt_irrefl _ (hcon.trans hgt)
  have hIE : S2InitialEquiv h2 hq r (-(Ψ * q0)) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [sub_neg_eq_add, hab, s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp]
      exact toZ_lt_toZ_iff.mpr hcon
    · rw [s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp, dvSupp_neg]
      exact congrArg toZ htie
  have hMuDvd : S2MuDvd h2 hq Ψ r := ⟨-q0, by rw [mul_neg]; exact hIE⟩
  have hkey : S2KeyPoly h2 hq Ψ := s2Φ₂_keyPoly h2 hq
  exact hkey.2.1.2 r hr0 (by rw [hΨdeg]; exact hrdeg) hMuDvd

/-- ★ **the `dv2Hgt`-shaped slot-0 corollary — `Dv2ResSurv`'s FIRST clause, verbatim**, at
the S2 instance, universal in `u₂, ℓ₂` (the clause does not mention them). -/
theorem dv2Hgt_dev_composedKey_mod_eq {A B : Polynomial O} {Ha Hb : ℕ}
    (hA : A.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hB : B.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hHa : dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = (Ha : ℕ∞))
    (hHb : dv2Hgt ((s2Tower h2 hq).levelDatum h2) B = (Hb : ℕ∞)) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2)
        (dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 0) = ((Ha + Hb : ℕ) : ℕ∞) := by
  have ha4 : A.natDegree < 4 := by rwa [s2Φ₂_natDegree h2 hq] at hA
  have hb4 : B.natDegree < 4 := by rwa [s2Φ₂_natDegree h2 hq] at hB
  have hHa' : dvSupp (s2Frame h2 hq) A 5 2 = (Ha : ℕ∞) := by
    rwa [dv2Hgt_eq_dvSupp_local h2 hq] at hHa
  have hHb' : dvSupp (s2Frame h2 hq) B 5 2 = (Hb : ℕ∞) := by
    rwa [dv2Hgt_eq_dvSupp_local h2 hq] at hHb
  rw [dev_zero_pin, dv2Hgt_eq_dvSupp_local h2 hq,
    s2_dvSupp_mul_modByComposedKey_eq h2 hq A B ha4 hb4, hHa', hHb']
  push_cast
  ring

section AxCheck1
#print axioms Uniformity.Density.Tower.C132nv3b.s2_dvSupp_mul_modByComposedKey_eq
#print axioms Uniformity.Density.Tower.C132nv3b.dv2Hgt_dev_composedKey_mod_eq
end AxCheck1

/-! ## Part 2 — the slot-1 DIAGNOSTIC: the sharp bound landed facts give, and why `(5,2)`
fails (BLOCKED-BECAUSE, see the file docstring for the full explanation) -/

/-- `Φ₂`'s own μ₂-level `dvSupp` grade IS `10`, already landed
(`C130np5.dvSupp_composedKey_s2Tower`, via the `rfl` identity `s2DepthTwoKeyAt_two`) — the
exact numeral the slot-1 analysis pivots on. -/
theorem s2_dvSupp_Φ₂ : dvSupp (s2Frame h2 hq) (s2DepthTwoKeyAt h2 hq 2) 5 2 = (10 : ℕ∞) := by
  rw [s2DepthTwoKeyAt_two h2 hq]
  exact dvSupp_composedKey_s2Tower h2 hq

/-- ★ **The SHARP slot-1 relation landed facts supply**: `Ha + Hb ≤ dvSupp(Φ₂) + Hq₀`
(`Hq₀` the bare quotient digit's own height), with NO case split once slot 0 is known:
`min(dvSupp(a·b), dvSupp(r)) ≤ dvSupp(Φ₂·q₀)` and `dvSupp(a·b) = dvSupp(r)` (slot 0)
collapse the `min` to `dvSupp(a·b)` itself. TIGHT — nothing landed excludes equality
(`dvSupp(r) = dvSupp(Φ₂·q₀)` is not landed-forbidden). -/
theorem s2_le_composedKey_quot_add (a b : Polynomial O)
    (ha : a.natDegree < 4) (hb : b.natDegree < 4) :
    dvSupp (s2Frame h2 hq) a 5 2 + dvSupp (s2Frame h2 hq) b 5 2
      ≤ dvSupp (s2Frame h2 hq) (s2DepthTwoKeyAt h2 hq 2) 5 2
        + dvSupp (s2Frame h2 hq) ((a * b) /ₘ (s2DepthTwoKeyAt h2 hq 2)) 5 2 := by
  set F := s2Frame h2 hq with hF
  set Ψ := s2DepthTwoKeyAt h2 hq 2 with hΨ
  set q0 := (a * b) /ₘ Ψ with hq0def
  set r := (a * b) %ₘ Ψ with hrdef
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  have heq0 : dvSupp F r 5 2 = dvSupp F a 5 2 + dvSupp F b 5 2 :=
    s2_dvSupp_mul_modByComposedKey_eq h2 hq a b ha hb
  have heqXr : dvSupp F (a * b) 5 2 = dvSupp F r 5 2 := by
    rw [s2_dvSupp_mul h2 hq a b, heq0]
  rw [← s2_dvSupp_mul h2 hq Ψ q0, ← s2_dvSupp_mul h2 hq a b, heqXr]
  have hmin : min (dvSupp F (a * b) 5 2) (dvSupp F r 5 2) ≤ dvSupp F (Ψ * q0) 5 2 := by
    have h := min_dvSupp_le_dvSupp_add F (u := 5) (by norm_num : (0:ℕ) < 2) (a * b) (-r)
    rw [dvSupp_neg] at h
    have hsub : a * b + -r = Ψ * q0 := by rw [← hab]; ring
    rwa [hsub] at h
  rwa [heqXr, min_self] at hmin

section AxCheck2
#print axioms Uniformity.Density.Tower.C132nv3b.s2_dvSupp_Φ₂
#print axioms Uniformity.Density.Tower.C132nv3b.s2_le_composedKey_quot_add
end AxCheck2

/-! ## Part 3 — cross-check (NOT part of the charge): the identical argument closes at
`(u₂,ℓ₂)=(21,2)`, the numeral the μ₃ campaign's row M3-NV1 actually fixes -/

private theorem natDegree_quot_lt {A B : Polynomial O}
    (hA : A.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hB : B.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree) :
    ((A * B) /ₘ (s2DepthTwoKeyAt h2 hq 2)).natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree := by
  have hΨmonic : (s2DepthTwoKeyAt h2 hq 2).Monic := s2Φ₂_monic h2 hq
  have hΨdeg : (s2DepthTwoKeyAt h2 hq 2).natDegree = 4 := s2Φ₂_natDegree h2 hq
  rw [Polynomial.natDegree_divByMonic _ hΨmonic]
  have hABdeg : (A * B).natDegree ≤ A.natDegree + B.natDegree := Polynomial.natDegree_mul_le
  omega

private theorem s2_dev_one_eq_quot {A B : Polynomial O}
    (hA : A.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hB : B.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree) :
    dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 1 = (A * B) /ₘ (s2DepthTwoKeyAt h2 hq 2) := by
  have hunfold : dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 1
      = dev (s2DepthTwoKeyAt h2 hq 2) ((A * B) /ₘ (s2DepthTwoKeyAt h2 hq 2)) 0 := rfl
  rw [hunfold, dev_zero_pin]
  set q0 := (A * B) /ₘ (s2DepthTwoKeyAt h2 hq 2) with hq0def
  rcases eq_or_ne q0 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · have hΨmonic : (s2DepthTwoKeyAt h2 hq 2).Monic := s2Φ₂_monic h2 hq
    have hqdeg : q0.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree :=
      natDegree_quot_lt h2 hq hA hB
    exact (Polynomial.modByMonic_eq_self_iff hΨmonic).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
          Polynomial.degree_eq_natDegree hΨmonic.ne_zero]
          exact_mod_cast hqdeg)

/-- ★ **`Dv2ResSurv`'s slot-1 clause DOES close at `(u₂,ℓ₂)=(21,2)`** — pins the exact
threshold and confirms the argument above (not merely the numeral choice) is sound. -/
theorem s2_dv2ResSurv_slot1_at_21 {A B : Polynomial O} {Ha Hb : ℕ}
    (hA : A.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hB : B.natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree)
    (hHa : dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = (Ha : ℕ∞))
    (hHb : dv2Hgt ((s2Tower h2 hq).levelDatum h2) B = (Hb : ℕ∞)) :
    (2 : ℕ) • ((Ha + Hb : ℕ) : ℕ∞) + 1
      ≤ (2 : ℕ) • dv2Hgt ((s2Tower h2 hq).levelDatum h2)
          (dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 1) + ((21 : ℕ) : ℕ∞) := by
  have ha4 : A.natDegree < 4 := by rwa [s2Φ₂_natDegree h2 hq] at hA
  have hb4 : B.natDegree < 4 := by rwa [s2Φ₂_natDegree h2 hq] at hB
  have hHa' : dvSupp (s2Frame h2 hq) A 5 2 = (Ha : ℕ∞) := by
    rwa [dv2Hgt_eq_dvSupp_local h2 hq] at hHa
  have hHb' : dvSupp (s2Frame h2 hq) B 5 2 = (Hb : ℕ∞) := by
    rwa [dv2Hgt_eq_dvSupp_local h2 hq] at hHb
  have hsharp := s2_le_composedKey_quot_add h2 hq A B ha4 hb4
  rw [hHa', hHb', s2_dvSupp_Φ₂ h2 hq] at hsharp
  rw [s2_dev_one_eq_quot h2 hq hA hB, dv2Hgt_eq_dvSupp_local h2 hq]
  set Hq0 := dvSupp (s2Frame h2 hq) ((A * B) /ₘ (s2DepthTwoKeyAt h2 hq 2)) 5 2 with hHq0def
  rcases eq_or_ne Hq0 ⊤ with hq0top | hq0ne
  · rw [hq0top]
    simp
  · obtain ⟨Hq0', hHq0'⟩ := ENat.ne_top_iff_exists.1 hq0ne
    rw [← hHq0'] at hsharp ⊢
    have hnat : Ha + Hb ≤ 10 + Hq0' := by exact_mod_cast hsharp
    have hgoal : 2 * (Ha + Hb) + 1 ≤ 2 * Hq0' + 21 := by omega
    calc (2 : ℕ) • ((Ha + Hb : ℕ) : ℕ∞) + 1
        = ((2 * (Ha + Hb) + 1 : ℕ) : ℕ∞) := by rw [nsmul_eq_mul]; push_cast; ring
      _ ≤ ((2 * Hq0' + 21 : ℕ) : ℕ∞) := by exact_mod_cast hgoal
      _ = (2 : ℕ) • ((Hq0' : ℕ) : ℕ∞) + ((21 : ℕ) : ℕ∞) := by rw [nsmul_eq_mul]; push_cast; ring

section AxCheck3
#print axioms Uniformity.Density.Tower.C132nv3b.s2_dv2ResSurv_slot1_at_21
end AxCheck3

end Uniformity.Density.Tower.C132nv3b
