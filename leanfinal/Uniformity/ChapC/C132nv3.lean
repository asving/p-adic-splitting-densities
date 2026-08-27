/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132nv1
import Uniformity.ChapC.C130kp5

/-!
# Uniformity.ChapC.C132nv3 — the μ₂ survival core at `Φ₂` (μ₃ campaign, node M3-NV3)

**[M3-NV3, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV3):
for coefficients of degree `< 4`, reduction modulo `Φ₂ := s2DepthTwoKeyAt h2 hq 2` (CC-2's
promoted level-2 key, `= composedKey (s2Tower h2 hq)`, `C130s2.lean:181-206`) PRESERVES the
product endpoint value: `dvSupp ((a·b) %ₘ Φ₂) 5 2 ≤ dvSupp a 5 2 + dvSupp b 5 2`. This is
the `hsurv`-shaped fact the `dv2Supp` generic endpoint theorem (M3-NV2, ported one level up
from `C130nv3.stageHeight_dev_endpoint_le_of_surv`) needs at its endpoint digits
`a := dev Φ₂ g jg`, `b := dev Φ₂ z jz` (each of degree `< deg Φ₂ = 4` by `degree_dev_lt`).

## Why this is NOT the depth-1 parity proof, one level up

At depth 1 (`C130nv3.s2_stageHeight_mul_modByMonic_le`) the survival core is proved by an
EXPLICIT remainder formula: `Φ′ = X² − 2` is a literal known binomial, so `(a·b) %ₘ Φ′` for
LINEAR `a, b` is a hand-computable two-slot expression, and the bound falls out of PARITY.
Here the "coefficients" `a, b` have degree `< 4` (not `≤ 1`), and the modulus `Φ₂` is an
abstract degree-4 key with NO known explicit coefficient formula (`composedKey`'s only
landed facts are `Monic` and degree — `C130kp5.lean:94`: "No irreducibility of `composedKey`
... is claimed" as a bare polynomial fact). Redoing the parity argument is not an option.

The mechanism used instead is FGMN's own: `Φ₂` is ALREADY known to be a valid `S2KeyPoly`
(`s2KeyPoly_composedKey`, `C130kp5.lean:353-357`), i.e. `Φ₂` is `μ₂`-MINIMAL and
`μ₂`-IRREDUCIBLE in the graded sense (`S2MuMinimal`/`S2MuIrreducible`, `C130kp0.lean`) — a
STRICTLY WEAKER, easier-to-certify notion than plain polynomial irreducibility, built
entirely from the landed `s2NormRes`/graded-residual machinery (RP-0 through RP-8: `Φ₂`'s
own residual `R₃(Φ₂) = X + 1`, `C130kp5.lean:344-346`, has a NONZERO scalar and a
degree-one — hence automatically irreducible — residual, which is exactly what makes `Φ₂` a
key polynomial in the FGMN sense). Given `a, b ≠ 0` of degree `< deg Φ₂ = 4`, `S2MuMinimal`
gives `Φ₂ ∤_µ a` and `Φ₂ ∤_µ b`; `S2MuIrreducible`'s prime clause then forces `Φ₂ ∤_µ (a·b)`.
The genuinely new step of THIS node is showing that `Φ₂ ∤_µ (a·b)` is EXACTLY the negation of
the bad case in the ultrametric division identity `a·b = Φ₂·q + r` (`r := (a·b) %ₘ Φ₂`):
if the survival bound failed (`dvSupp a 5 2 + dvSupp b 5 2 < dvSupp r 5 2`), the standard
`dvSupp` ultrametric bank (`C130s6`'s `min_dvSupp_le_dvSupp_add`/`dvSupp_add_eq_of_lt`) forces
`Φ₂·q` and `a·b` to have the SAME `dvSupp` value with `r` STRICTLY above it — i.e. exactly
`S2InitialEquiv (a·b) (Φ₂·q)` — witnessing `S2MuDvd h2 hq Φ₂ (a·b)`, contradicting
`Φ₂ ∤_µ (a·b)`. No new axiom, no re-derivation of `Φ₂`'s coefficients, and no appeal to
plain polynomial irreducibility of `Φ₂` (which is NOT landed and is flagged open elsewhere).

## What lands

★ `s2_dvSupp_mul_modByComposedKey_le` — the core survival law, at the `dvSupp`/`s2Frame`
level (universal in `a, b`, zero cases included). ★ `dv2Hgt_dev_composedKey_mod_le` — the
consumable `dv2Hgt`-shaped corollary at the endpoint digits `dev Φ₂ g jg`/`dev Φ₂ z jz`,
matching M3-NV2's expected `hsurv` premise verbatim (degree `< 4` supplied automatically by
`degree_dev_lt` against `Φ₂`'s own monicity/degree, `C132nv1`'s `s2Φ₂_monic`/
`s2Φ₂_natDegree`).

## What this node does NOT claim (honesty scope)

* No plain-polynomial `Irreducible Φ₂`: only the strictly weaker `μ₂`-graded notions
  (`S2MuMinimal`, `S2MuIrreducible`) already packaged inside `S2KeyPoly h2 hq Φ₂`.
* No `dv2Supp`/`FGMNSourceData` assembly: this node supplies exactly the one survival fact,
  not the endpoint theorem it feeds (M3-NV2's job) nor any packaging (M3-FD0/M3-SG's).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_dvSupp_mul_modByComposedKey_le` and its `dv2Hgt` corollary.

**DEPENDS.** C132nv1 (`s2Φ₂_monic`, `s2Φ₂_natDegree`) · C130s2 (`s2DepthTwoKeyAt`,
`s2DepthTwoKeyAt_two`) · C130kp5 (`s2KeyPoly_composedKey`) · C130kp0 (`S2KeyPoly`,
`S2MuMinimal`, `S2MuIrreducible`, `S2MuDvd`, `S2InitialEquiv`) · C130nv3 (`s2_dvSupp_mul`,
the unfenced S2 level-two product law) · C130s6 (`dvSupp` ultrametric bank:
`dvSupp_zero_eq_top`, `dvSupp_ne_top_of_ne_zero`, `min_dvSupp_le_dvSupp_add`,
`dvSupp_add_eq_of_lt`, `s2Hgt₂_eq_dvSupp`, `s2Hgt₂_eq_dv2Hgt`) · C130rp0 (`toZ_lt_toZ_iff`)
· C.11 (`dv2Hgt`) · B.02/B.03 (`dev`, `degree_dev_lt`) · mathlib
(`Polynomial.modByMonic_add_div`, `Polynomial.natDegree_lt_natDegree`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130kp0
open Uniformity.Density.Tower.C130kp5 Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — `Φ₂` is a key polynomial at the `s2DepthTwoKeyAt` numeral -/

/-- `Φ₂ := s2DepthTwoKeyAt h2 hq 2` is a valid `S2KeyPoly` — the tower's own promoted level-2
key IS `composedKey`, and `s2KeyPoly_composedKey` (`C130kp5`) already certifies it. -/
theorem s2Φ₂_keyPoly : S2KeyPoly h2 hq (s2DepthTwoKeyAt h2 hq 2) := by
  rw [s2DepthTwoKeyAt_two h2 hq]
  exact s2KeyPoly_composedKey h2 hq

/-! ## Part 2 — ★ the survival core -/

/-- ★ **NODE M3-NV3 — the `dvSupp` survival core**: for ANY `a, b : Polynomial O` of degree
`< deg Φ₂ = 4`, reducing `a·b` modulo `Φ₂` does not raise the μ₂ value above the sum of `a`'s
and `b`'s own values. Universal (zero cases ride the `⊤` conventions). -/
theorem s2_dvSupp_mul_modByComposedKey_le (a b : Polynomial O)
    (ha : a.natDegree < 4) (hb : b.natDegree < 4) :
    dvSupp (s2Frame h2 hq) ((a * b) %ₘ (s2DepthTwoKeyAt h2 hq 2)) 5 2
      ≤ dvSupp (s2Frame h2 hq) a 5 2 + dvSupp (s2Frame h2 hq) b 5 2 := by
  set F := s2Frame h2 hq with hF
  set Ψ := s2DepthTwoKeyAt h2 hq 2 with hΨ
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F 5 (by norm_num), top_add]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F 5 (by norm_num), add_top]
  set r := (a * b) %ₘ Ψ with hr
  set q0 := (a * b) /ₘ Ψ with hq0
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  rw [← s2_dvSupp_mul h2 hq a b]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp F (a*b) 5 2 < dvSupp F r 5 2`
  have hmin' : min (dvSupp F r 5 2) (dvSupp F (Ψ * q0) 5 2) ≤ dvSupp F (a * b) 5 2 := by
    have h := min_dvSupp_le_dvSupp_add F (u := 5) (by norm_num : (0:ℕ) < 2) r (Ψ * q0)
    rwa [hab] at h
  have hy : dvSupp F (Ψ * q0) 5 2 < dvSupp F r 5 2 := by
    by_contra hge
    rw [not_lt] at hge
    rw [min_eq_left hge] at hmin'
    exact absurd hmin' (not_le.mpr hcon)
  have heq' : dvSupp F (a * b) 5 2 = dvSupp F (Ψ * q0) 5 2 := by
    rw [← hab, add_comm]
    exact dvSupp_add_eq_of_lt F (by norm_num) hy
  -- `Ψ * q0 ≠ 0`, hence `q0 ≠ 0`
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hΨq0ne : Ψ * q0 ≠ 0 := by
    intro h0
    rw [h0, dvSupp_zero_eq_top F 5 (by norm_num)] at heq'
    exact dvSupp_ne_top_of_ne_zero F 5 2 hab0 heq'
  have hq0ne : q0 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hΨq0ne; exact hΨq0ne rfl
  -- assemble `S2InitialEquiv (a*b) (Ψ*q0)`, hence `S2MuDvd h2 hq Ψ (a*b)`
  have hsub : a * b - Ψ * q0 = r := by
    rw [← hab]; ring
  have hIE : S2InitialEquiv h2 hq (a * b) (Ψ * q0) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp, hsub]
      exact toZ_lt_toZ_iff.mpr hcon
    · rw [s2Hgt₂_eq_dvSupp, s2Hgt₂_eq_dvSupp]
      exact congrArg C130s6.toZ heq'
  have hMuDvd : S2MuDvd h2 hq Ψ (a * b) := ⟨q0, hIE⟩
  -- contradiction: `Φ₂` is `μ₂`-minimal at `a, b` and `μ₂`-irreducible
  have hkey : S2KeyPoly h2 hq Ψ := s2Φ₂_keyPoly h2 hq
  have hΨdeg : Ψ.natDegree = 4 := s2Φ₂_natDegree h2 hq
  have hdisj : S2MuDvd h2 hq Ψ a ∨ S2MuDvd h2 hq Ψ b := hkey.2.2.2.2 a b hMuDvd
  rcases hdisj with h | h
  · exact hkey.2.1.2 a ha0 (by rw [hΨdeg]; exact ha) h
  · exact hkey.2.1.2 b hb0 (by rw [hΨdeg]; exact hb) h

/-! ## Part 3 — the `dv2Hgt`-shaped corollary, ready for M3-NV2's endpoint theorem -/

/-- private copy of the degree-`< 4` bound on `Φ₂`-development digits (mirror of `C130rp8`'s
`natDegree_dev_lt_two`, one level up: every `dev Φ₂ f j` has degree `< deg Φ₂ = 4`). -/
private theorem natDegree_dev_composedKey_lt_four (f : Polynomial O) (j : ℕ) :
    (dev (s2DepthTwoKeyAt h2 hq 2) f j).natDegree < 4 := by
  rcases eq_or_ne (dev (s2DepthTwoKeyAt h2 hq 2) f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; omega
  · have hd : (0:ℕ) < (s2DepthTwoKeyAt h2 hq 2).natDegree := by
      rw [s2Φ₂_natDegree h2 hq]; norm_num
    have h := Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2Φ₂_monic h2 hq) hd f j)
    rw [s2Φ₂_natDegree h2 hq] at h
    omega

/-- the `dvSupp`/`dv2Hgt` bridge: `dv2Hgt` at the S2 level datum reading `Φ₂`-development
digits IS `dvSupp` at the S2 numerals — the SAME anti-drift identity `s2Hgt₂_eq_dv2Hgt`/
`s2Hgt₂_eq_dvSupp` already used by `C132nv1`, read as an equation of the underlying `ℕ∞`
values via `toZ`'s injectivity. -/
private theorem dv2Hgt_eq_dvSupp (A : Polynomial O) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = dvSupp (s2Frame h2 hq) A 5 2 :=
  C130s6.toZ_inj ((s2Hgt₂_eq_dv2Hgt h2 hq A).symm.trans (s2Hgt₂_eq_dvSupp h2 hq A))

/-- ★ **the `dv2Hgt`-shaped survival corollary**: at the endpoint digits `a := dev Φ₂ g jg`,
`b := dev Φ₂ z jz` (degree `< 4` automatic), reduction modulo `Φ₂` preserves the product
endpoint value — EXACTLY the `hsurv` premise the ported (`dv2Supp`) generic endpoint theorem
(M3-NV2) needs. -/
theorem dv2Hgt_dev_composedKey_mod_le (g z : Polynomial O) (jg jz : ℕ) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2)
        ((dev (s2DepthTwoKeyAt h2 hq 2) g jg * dev (s2DepthTwoKeyAt h2 hq 2) z jz)
          %ₘ (s2DepthTwoKeyAt h2 hq 2))
      ≤ dv2Hgt ((s2Tower h2 hq).levelDatum h2) (dev (s2DepthTwoKeyAt h2 hq 2) g jg)
        + dv2Hgt ((s2Tower h2 hq).levelDatum h2) (dev (s2DepthTwoKeyAt h2 hq 2) z jz) := by
  rw [dv2Hgt_eq_dvSupp h2 hq, dv2Hgt_eq_dvSupp h2 hq, dv2Hgt_eq_dvSupp h2 hq]
  exact s2_dvSupp_mul_modByComposedKey_le h2 hq _ _
    (natDegree_dev_composedKey_lt_four h2 hq g jg)
    (natDegree_dev_composedKey_lt_four h2 hq z jz)

end Uniformity.Density.Tower.C132nv3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv3.s2Φ₂_keyPoly
#print axioms Uniformity.Density.Tower.C132nv3.s2_dvSupp_mul_modByComposedKey_le
#print axioms Uniformity.Density.Tower.C132nv3.dv2Hgt_dev_composedKey_mod_le

end AxCheck
