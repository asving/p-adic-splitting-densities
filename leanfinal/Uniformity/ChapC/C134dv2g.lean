/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132nv2
import Uniformity.ChapC.C133mh3
import Uniformity.ChapC.C134cfs
import Uniformity.ChapC.C141defs

/-!
# Uniformity.ChapC.C134dv2g — the two level-2 subgoals gating F1.3–F1.6 [DV2G 2026-08-28]

**[DV2G 2026-08-28]** (`runs/wave-c/verdict_F12C.md`'s BLOCKED section): the F1.3–F1.6
chain is gated by exactly two level-2 subgoals — (i) a FRAME-GENERIC `Dv2ResSurv`
discharge (only the S2 numeric instance `C132nv4.s2_dv2ResSurv_at_21` exists), and
(ii) `dv2Pin_mul_complement`, the complement's dv2-profile collapse (the no-interaction
node the BLOCKERS_PLAN priced at 70–120 lines), relating `dvSupp F (g %ₘ Ψ)` to
`dvSupp F g` so the complement's level-2 side collapses to abscissa 0.

## The mechanism (C132nv3/C132nv3b generalized)

The S2 discharge used three S2-specific inputs, each of which now has a frame-generic
supplier or an honest generic hypothesis:

1. `s2_dvSupp_mul` (unconditional S2 `dvSupp` multiplicativity) → **`C133mh3.dvSupp_mul`**
   (Theorem M clause 1, landed 2026-08-28): all nonzero factors, any frame with
   `hπ : Irreducible π`, `hh : 0 < F.h`, a pin, `0 < ℓ`, and the floor
   `ℓ·(e₁f₁·h) < u` — at the level datum's inner pair `(L.u, L.ℓ)` the floor IS `L.hκ`.
2. `S2KeyPoly Φ₂` (FGMN key-polynomialhood at μ₂ = the S2 `dvSupp`) → the generic
   predicates **`MuEquiv`/`MuDvd`/`MuMinimal`/`MuPrime`/`IsMuKey`** below, stated at the
   level valuation `dvSupp F · L.u L.ℓ` (= `dv2Hgt L`, definitionally) — C130kp0's FGMN
   Def 1.2/1.4 shapes, one frame up, taken as ONE honest hypothesis `IsMuKey L Ψ`.
3. `dvSupp Φ₂ = 10` + the numeral check `2·10 < 21` → the generic key grade
   `hKΨ : dvSupp F Ψ L.u L.ℓ = KΨ` and the OUTER floor **`hfence : ℓ₂ · KΨ < u₂`** (the
   exact level-2 twin of the level-1 floor `ℓ·(D′h) < u`; at S2 `(21,2)`: `2·10 < 21`,
   the same margin `C132nv3b` pinned).

## What lands

* Part 1 — the generic μ-predicates at a level datum (FGMN Def 1.2/1.4, `dvSupp`-valued).
* Part 2 — the generic survival core: `dvSupp_mul_modByKey_le` / `dvSupp_mul_modByKey_eq`
  (C132nv3 + C132nv3b's Half 1, frame-generic) and the sharp slot-1 bound
  `dvSupp_add_le_key_quot_add` (C132nv3b's Half 2 diagnostic, frame-generic).
* Part 3 — ★ **subgoal (i)**: `dv2ResSurv_of_muKey : Dv2ResSurv L Ψ u₂ ℓ₂` from the frame
  pack + `IsMuKey` + the key grade + the outer floor. The widest honest generalization:
  at S2 every hypothesis matches a landed certificate (`s2Φ₂_keyPoly` through the `toZ`
  value bridge, `s2_dvSupp_Φ₂ = 10`, `2·10 < 21` — the same margin C132nv3b pinned).
* Part 4 — the no-interaction bank: the level-2 MacLane expansion floors
  (`dvSupp_le_modByKey`, `dvSupp_le_divByKey_add`, `dvSupp_le_dev_add` — the digit floor
  C132nv2's docstring recorded as having "no level-2 analogue", now derivable from
  Theorem M + μ-minimality), the complement's slot-0 pin
  (`dvSupp_modByKey_eq_of_not_muDvd`), and the abscissa-0 collapse
  (`dv2Supp_collapse_of_not_muDvd`).
* Part 5 — ★ **subgoal (ii)**: `dv2Pin_mul_complement` — the translation shape
  `dv2Supp L Ψ (b·g) u₂ ℓ₂ = dv2Supp L Ψ b u₂ ℓ₂ + ℓ₂ • dvSupp F g L.u L.ℓ` for any
  nonzero `b` and any complement `g` not μ-divisible by the key.
* Part 6 — the F1.3 carrier `dv2Supp_translation_of_muKey` (signed conclusion, honest
  premises) + the F1.3–F1.6 BLOCKED-BECAUSE record (end of file).

## Status

Sorry-free; Lean core only on every Part 1–5 declaration (no `exists_dvDissection` —
nothing here touches the dissection); Part 6's carrier inherits
`exists_dvDissection` through `C134cfs.blockFactor_spec` (the one allowlisted C.33 cite),
and nothing else does (see the AxCheck footer). No landed file edited; no new axiom.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`MuEquiv`, `MuDvd`, `MuMinimal`, `MuPrime`, `IsMuKey`, `dv2ResSurv_of_muKey`,
`dv2Pin_mul_complement`, `dv2Supp_collapse_of_not_muDvd`, `dv2Supp_translation_of_muKey`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C134dv2g

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C130nv2 (dev_zero_pin)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 1 — the generic μ-predicates at a level datum (FGMN Def 1.2/1.4, `dvSupp`-valued)

`C130kp0`'s S2 shapes (`S2InitialEquiv`/`S2MuDvd`/`S2MuMinimal`/`S2MuIrreducible`/
`S2KeyPoly`, themselves FGMN's published Definitions 1.2 and 1.4 at μ₂), restated at the
GENERIC level valuation `dvSupp F · L.u L.ℓ` (`ℕ∞`-valued; the S2 versions read the same
values through `toZ`, cf. `C130s6.s2Hgt₂_eq_dvSupp`). -/

/-- FGMN Def 1.2's `g ∼µ h` at the level valuation: `µ(g − h) > µ(g) = µ(h)`, or both
zero. (`ℕ∞`-valued twin of `C130kp0.S2InitialEquiv`.) -/
def MuEquiv (L : LevelDatum F H₀ hpin) (g h : Polynomial O) : Prop :=
  (dvSupp F g L.u L.ℓ < dvSupp F (g - h) L.u L.ℓ ∧
    dvSupp F g L.u L.ℓ = dvSupp F h L.u L.ℓ) ∨ (g = 0 ∧ h = 0)

/-- FGMN Def 1.2's `Ψ ∣µ g` at the level valuation (twin of `C130kp0.S2MuDvd`). -/
def MuDvd (L : LevelDatum F H₀ hpin) (Ψ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, MuEquiv L g (Ψ * q)

/-- FGMN Def 1.2's µ-minimality at the level valuation (twin of `C130kp0.S2MuMinimal`). -/
def MuMinimal (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O) : Prop :=
  0 < Ψ.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < Ψ.natDegree → ¬ MuDvd L Ψ g

/-- The prime clause of FGMN Def 1.2's µ-irreducibility at the level valuation (the one
clause the survival core consumes; twin of `C130kp0.S2MuIrreducible`'s third conjunct). -/
def MuPrime (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O) : Prop :=
  ∀ g h : Polynomial O, MuDvd L Ψ (g * h) → MuDvd L Ψ g ∨ MuDvd L Ψ h

/-- FGMN Def 1.4's key-polynomialhood at the level valuation (twin of
`C130kp0.S2KeyPoly`; µ-irreducibility's nonzero/proper clauses follow from monicity and
µ-minimality, so only the prime clause is carried). -/
def IsMuKey (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O) : Prop :=
  Ψ.Monic ∧ MuMinimal L Ψ ∧ MuPrime L Ψ

variable (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}

/-- `0` is μ-divisible by anything (witness `0`; the `⊤` conventions). -/
theorem muDvd_zero : MuDvd L Ψ (0 : Polynomial O) :=
  ⟨0, Or.inr ⟨rfl, mul_zero Ψ⟩⟩

/-- The inner floor at the level pair IS `L.hκ` (associativity bridge to
`C133mh3.dvSupp_mul`'s spelling). -/
private theorem inner_floor : L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]; exact L.hκ

/-- Theorem M clause 1 at the level pair: `dvSupp` is exactly multiplicative at
`(L.u, L.ℓ)` (all nonzero factors). -/
private theorem dvSupp_mul' (hπ : Irreducible π) (hh : 0 < F.h)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dvSupp F (g * z) L.u L.ℓ = dvSupp F g L.u L.ℓ + dvSupp F z L.u L.ℓ :=
  C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ (inner_floor L) hg hz

/-! ## Part 2 — the generic survival core (C132nv3 + C132nv3b, frame-generic) -/

/-- ★ **The `≤` half (C132nv3's mechanism, frame-generic)**: for `a, b` of degree
`< deg Ψ`, reducing `a·b` modulo the μ-key `Ψ` does not raise the level value above the
sum of the factors' values. -/
theorem dvSupp_mul_modByKey_le (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {a b : Polynomial O}
    (ha : a.natDegree < Ψ.natDegree) (hb : b.natDegree < Ψ.natDegree) :
    dvSupp F ((a * b) %ₘ Ψ) L.u L.ℓ ≤ dvSupp F a L.u L.ℓ + dvSupp F b L.u L.ℓ := by
  obtain ⟨hΨm, hΨmin, hΨpr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F L.u L.hℓ, top_add]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F L.u L.hℓ, add_top]
  set r := (a * b) %ₘ Ψ with hrdef
  set q0 := (a * b) /ₘ Ψ with hq0def
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  rw [← dvSupp_mul' L hπ hh ha0 hb0]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp F (a*b) < dvSupp F r`
  have hmin' : min (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q0) L.u L.ℓ)
      ≤ dvSupp F (a * b) L.u L.ℓ := by
    have h := min_dvSupp_le_dvSupp_add (u := L.u) F L.hℓ r (Ψ * q0)
    rwa [hab] at h
  have hy : dvSupp F (Ψ * q0) L.u L.ℓ < dvSupp F r L.u L.ℓ := by
    by_contra hge
    rw [not_lt] at hge
    rw [min_eq_left hge] at hmin'
    exact absurd hmin' (not_le.mpr hcon)
  have heq' : dvSupp F (a * b) L.u L.ℓ = dvSupp F (Ψ * q0) L.u L.ℓ := by
    rw [← hab, add_comm]
    exact dvSupp_add_eq_of_lt F L.hℓ hy
  -- initial equivalence `a·b ∼µ Ψ·q0`, hence `Ψ ∣µ a·b`
  have hMuDvd : MuDvd L Ψ (a * b) := by
    refine ⟨q0, Or.inl ⟨?_, heq'⟩⟩
    have hsub : a * b - Ψ * q0 = r := by rw [← hab]; ring
    rw [hsub]
    exact hcon
  -- contradiction: μ-primality + μ-minimality at the digit-bounded factors
  rcases hΨpr a b hMuDvd with h | h
  · exact hΨmin.2 a ha0 ha h
  · exact hΨmin.2 b hb0 hb h

/-- ★ **The EQUALITY (C132nv3b Half 1's mechanism, frame-generic)**: reduction modulo the
μ-key preserves the product value exactly. -/
theorem dvSupp_mul_modByKey_eq (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {a b : Polynomial O}
    (ha : a.natDegree < Ψ.natDegree) (hb : b.natDegree < Ψ.natDegree) :
    dvSupp F ((a * b) %ₘ Ψ) L.u L.ℓ = dvSupp F a L.u L.ℓ + dvSupp F b L.u L.ℓ := by
  refine le_antisymm (dvSupp_mul_modByKey_le L hπ hh hkey ha hb) ?_
  obtain ⟨hΨm, hΨmin, hΨpr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F L.u L.hℓ]
    exact le_top
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dvSupp_zero_eq_top F L.u L.hℓ]
    exact le_top
  rw [← dvSupp_mul' L hπ hh ha0 hb0]
  set r := (a * b) %ₘ Ψ with hrdef
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, dvSupp_zero_eq_top F L.u L.hℓ]
    exact le_top
  set q0 := (a * b) /ₘ Ψ with hq0def
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  have hΨd : 0 < Ψ.natDegree := hΨmin.1
  have hΨne1 : Ψ ≠ 1 := fun h1 => by simp [h1] at hΨd
  have hrdeg : r.natDegree < Ψ.natDegree :=
    Polynomial.natDegree_modByMonic_lt (a * b) hΨm hΨne1
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp F r < dvSupp F (a*b)` — the tie analysis forces `dvSupp r = dvSupp (Ψ·q0)`
  have htie : dvSupp F r L.u L.ℓ = dvSupp F (Ψ * q0) L.u L.ℓ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heqX : dvSupp F (a * b) L.u L.ℓ = dvSupp F r L.u L.ℓ := by
        rw [← hab]
        exact dvSupp_add_eq_of_lt F L.hℓ hlt
      rw [heqX] at hcon
      exact lt_irrefl _ hcon
    · have heqX : dvSupp F (a * b) L.u L.ℓ = dvSupp F (Ψ * q0) L.u L.ℓ := by
        rw [← hab, add_comm]
        exact dvSupp_add_eq_of_lt F L.hℓ hgt
      rw [heqX] at hcon
      exact lt_irrefl _ (hcon.trans hgt)
  -- initial equivalence `r ∼µ Ψ·(−q0)`, hence `Ψ ∣µ r` — excluded by μ-minimality
  have hMuDvd : MuDvd L Ψ r := by
    refine ⟨-q0, Or.inl ⟨?_, ?_⟩⟩
    · have hsub : r - Ψ * -q0 = a * b := by rw [mul_neg, sub_neg_eq_add, hab]
      rw [hsub]
      exact hcon
    · rw [mul_neg, dvSupp_neg]
      exact htie
  exact hΨmin.2 r hr0 hrdeg hMuDvd

/-- ★ **The sharp slot-1 relation (C132nv3b Half 2's diagnostic, frame-generic)**:
`µ(a) + µ(b) ≤ µ(Ψ) + µ((a·b) /ₘ Ψ)`. -/
theorem dvSupp_add_le_key_quot_add (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {a b : Polynomial O}
    (ha : a.natDegree < Ψ.natDegree) (hb : b.natDegree < Ψ.natDegree) :
    dvSupp F a L.u L.ℓ + dvSupp F b L.u L.ℓ
      ≤ dvSupp F Ψ L.u L.ℓ + dvSupp F ((a * b) /ₘ Ψ) L.u L.ℓ := by
  set r := (a * b) %ₘ Ψ with hrdef
  set q0 := (a * b) /ₘ Ψ with hq0def
  rcases eq_or_ne q0 0 with hq00 | hq00
  · rw [hq00, dvSupp_zero_eq_top F L.u L.hℓ, add_top]
    exact le_top
  rcases eq_or_ne a 0 with rfl | ha0
  · exact absurd (by rw [hq0def, zero_mul, Polynomial.zero_divByMonic]) hq00
  rcases eq_or_ne b 0 with rfl | hb0
  · exact absurd (by rw [hq0def, mul_zero, Polynomial.zero_divByMonic]) hq00
  have hΨm : Ψ.Monic := hkey.1
  have hab : r + Ψ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ
  have heq0 : dvSupp F r L.u L.ℓ = dvSupp F a L.u L.ℓ + dvSupp F b L.u L.ℓ :=
    dvSupp_mul_modByKey_eq L hπ hh hkey ha hb
  have hXab : dvSupp F (a * b) L.u L.ℓ = dvSupp F a L.u L.ℓ + dvSupp F b L.u L.ℓ :=
    dvSupp_mul' L hπ hh ha0 hb0
  have heqXr : dvSupp F (a * b) L.u L.ℓ = dvSupp F r L.u L.ℓ := by rw [hXab, heq0]
  rw [← hXab, ← dvSupp_mul' L hπ hh hΨm.ne_zero hq00]
  -- `min(dvSupp(a·b), dvSupp r) ≤ dvSupp(Ψ·q0)`, and slot 0 collapses the `min`
  have hmin : min (dvSupp F (a * b) L.u L.ℓ) (dvSupp F r L.u L.ℓ)
      ≤ dvSupp F (Ψ * q0) L.u L.ℓ := by
    have h := min_dvSupp_le_dvSupp_add (u := L.u) F L.hℓ (a * b) (-r)
    rw [dvSupp_neg] at h
    have hsub : a * b + -r = Ψ * q0 := by rw [← hab]; ring
    rwa [hsub] at h
  rwa [← heqXr, min_self] at hmin

/-- Slot 1 of a short product's `Ψ`-development is the bare quotient
(`C132nv3b.s2_dev_one_eq_quot`, frame-generic). -/
private theorem dev_one_eq_quot (hΨm : Ψ.Monic) {a b : Polynomial O}
    (ha : a.natDegree < Ψ.natDegree) (hb : b.natDegree < Ψ.natDegree) :
    dev Ψ (a * b) 1 = (a * b) /ₘ Ψ := by
  have hunfold : dev Ψ (a * b) 1 = dev Ψ ((a * b) /ₘ Ψ) 0 := rfl
  rw [hunfold, dev_zero_pin]
  set q0 := (a * b) /ₘ Ψ with hq0def
  rcases eq_or_ne q0 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · have hqdeg : q0.natDegree < Ψ.natDegree := by
      rw [hq0def, Polynomial.natDegree_divByMonic _ hΨm]
      have hABdeg : (a * b).natDegree ≤ a.natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      omega
    exact (Polynomial.modByMonic_eq_self_iff hΨm).mpr
      (by rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hΨm.ne_zero]
          exact_mod_cast hqdeg)

/-! ## Part 3 — ★ SUBGOAL (i): the frame-generic `Dv2ResSurv` discharge -/

/-- ★ **SUBGOAL (i) — the frame-generic survival package**: `Dv2ResSurv L Ψ u₂ ℓ₂` holds
at ANY level datum, for ANY μ-key `Ψ` of known level grade `KΨ`, at ANY outer pair
`(u₂, ℓ₂)` clearing the OUTER floor `ℓ₂ · KΨ < u₂` — the exact generalization of
`C132nv4.s2_dv2ResSurv_at_21` (there: `KΨ = 10`, `(u₂, ℓ₂) = (21, 2)`, `2·10 < 21`). -/
theorem dv2ResSurv_of_muKey (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂) :
    Dv2ResSurv L Ψ u₂ ℓ₂ := by
  intro A B Ha Hb hA hB hHa hHb
  have hHa' : dvSupp F A L.u L.ℓ = (Ha : ℕ∞) := hHa
  have hHb' : dvSupp F B L.u L.ℓ = (Hb : ℕ∞) := hHb
  constructor
  · -- slot-0 equality = `Dv2ResSurv`'s first clause, verbatim
    show dvSupp F (dev Ψ (A * B) 0) L.u L.ℓ = ((Ha + Hb : ℕ) : ℕ∞)
    rw [dev_zero_pin, dvSupp_mul_modByKey_eq L hπ hh hkey hA hB, hHa', hHb']
    push_cast
    ring
  · -- slot-1 strict carry bound, from the sharp relation + the OUTER floor
    show ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) + 1
      ≤ ℓ₂ • dvSupp F (dev Ψ (A * B) 1) L.u L.ℓ + (u₂ : ℕ∞)
    rw [dev_one_eq_quot hkey.1 hA hB]
    have hsharp := dvSupp_add_le_key_quot_add L hπ hh hkey hA hB
    rw [hHa', hHb', hKΨ] at hsharp
    set Hq0 := dvSupp F ((A * B) /ₘ Ψ) L.u L.ℓ with hHq0def
    rcases eq_or_ne Hq0 ⊤ with hq0top | hq0ne
    · rw [hq0top, C118a.smul_top_pos hℓ₂, top_add]
      exact le_top
    · obtain ⟨Hq0', hHq0'⟩ := ENat.ne_top_iff_exists.1 hq0ne
      rw [← hHq0'] at hsharp ⊢
      have hnat : Ha + Hb ≤ KΨ + Hq0' := by exact_mod_cast hsharp
      have hgoal : ℓ₂ * (Ha + Hb) + 1 ≤ ℓ₂ * Hq0' + u₂ := by
        have h1 : ℓ₂ * (Ha + Hb) ≤ ℓ₂ * (KΨ + Hq0') := Nat.mul_le_mul le_rfl hnat
        have h2 : ℓ₂ * (KΨ + Hq0') = ℓ₂ * KΨ + ℓ₂ * Hq0' := Nat.mul_add ℓ₂ KΨ Hq0'
        omega
      calc ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) + 1 = ((ℓ₂ * (Ha + Hb) + 1 : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring
        _ ≤ ((ℓ₂ * Hq0' + u₂ : ℕ) : ℕ∞) := by exact_mod_cast hgoal
        _ = ℓ₂ • ((Hq0' : ℕ) : ℕ∞) + ((u₂ : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring

/-! ## Part 4 — the no-interaction bank (the level-2 MacLane expansion floors) -/

/-- **The slot-0 expansion floor**: reduction modulo a μ-key never lowers the level value
(μ-minimality alone; the level-2 twin of `C130nv2.stageHeight_le_modByMonic`, whose
level-1 proof was degree bookkeeping — here it is the FGMN tie-exclusion). -/
theorem dvSupp_le_modByKey (hkey : IsMuKey L Ψ) (g : Polynomial O) :
    dvSupp F g L.u L.ℓ ≤ dvSupp F (g %ₘ Ψ) L.u L.ℓ := by
  obtain ⟨hΨm, hΨmin, hΨpr⟩ := hkey
  set r := g %ₘ Ψ with hrdef
  set q := g /ₘ Ψ with hqdef
  have hab : r + Ψ * q = g := Polynomial.modByMonic_add_div g Ψ
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp r < dvSupp g`
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, dvSupp_zero_eq_top F L.u L.hℓ] at hcon
    exact not_top_lt hcon
  have hΨd : 0 < Ψ.natDegree := hΨmin.1
  have hΨne1 : Ψ ≠ 1 := fun h1 => by simp [h1] at hΨd
  have hrdeg : r.natDegree < Ψ.natDegree := Polynomial.natDegree_modByMonic_lt g hΨm hΨne1
  have htie : dvSupp F r L.u L.ℓ = dvSupp F (Ψ * q) L.u L.ℓ := by
    by_contra hne
    have heq : dvSupp F g L.u L.ℓ
        = min (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ) := by
      rw [← hab]
      exact dvSupp_add_eq F L.hℓ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left hlt.le] at heq
      rw [heq] at hcon
      exact lt_irrefl _ hcon
    · rw [min_eq_right hgt.le] at heq
      rw [heq] at hcon
      exact lt_irrefl _ (hcon.trans hgt)
  have hMuDvd : MuDvd L Ψ r := by
    refine ⟨-q, Or.inl ⟨?_, ?_⟩⟩
    · have hsub : r - Ψ * -q = g := by rw [mul_neg, sub_neg_eq_add, hab]
      rw [hsub]
      exact hcon
    · rw [mul_neg, dvSupp_neg]
      exact htie
  exact hΨmin.2 r hr0 hrdeg hMuDvd

/-- **The slot-1 expansion floor**: the quotient prices at least `µ(g) − µ(Ψ)` (stated
additively; the level-2 twin of `C130nv2.stageHeight_le_divByMonic`). -/
theorem dvSupp_le_divByKey_add (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) (g : Polynomial O) :
    dvSupp F g L.u L.ℓ ≤ dvSupp F Ψ L.u L.ℓ + dvSupp F (g /ₘ Ψ) L.u L.ℓ := by
  obtain ⟨hΨm, hΨmin, hΨpr⟩ := hkey
  set r := g %ₘ Ψ with hrdef
  set q := g /ₘ Ψ with hqdef
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, dvSupp_zero_eq_top F L.u L.hℓ, add_top]
    exact le_top
  have hab : r + Ψ * q = g := Polynomial.modByMonic_add_div g Ψ
  rw [← dvSupp_mul' L hπ hh hΨm.ne_zero hq0]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp (Ψ·q) < dvSupp g`
  have hΨd : 0 < Ψ.natDegree := hΨmin.1
  have hΨne1 : Ψ ≠ 1 := fun h1 => by simp [h1] at hΨd
  have hrdeg : r.natDegree < Ψ.natDegree := Polynomial.natDegree_modByMonic_lt g hΨm hΨne1
  have htie : dvSupp F r L.u L.ℓ = dvSupp F (Ψ * q) L.u L.ℓ := by
    by_contra hne
    have heq : dvSupp F g L.u L.ℓ
        = min (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ) := by
      rw [← hab]
      exact dvSupp_add_eq F L.hℓ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left hlt.le] at heq
      rw [heq] at hcon
      exact lt_irrefl _ (hcon.trans hlt)
    · rw [min_eq_right hgt.le] at heq
      rw [heq] at hcon
      exact lt_irrefl _ hcon
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, dvSupp_zero_eq_top F L.u L.hℓ] at htie
    exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ
      (mul_ne_zero hΨm.ne_zero hq0) htie.symm
  have hMuDvd : MuDvd L Ψ r := by
    refine ⟨-q, Or.inl ⟨?_, ?_⟩⟩
    · have hsub : r - Ψ * -q = g := by rw [mul_neg, sub_neg_eq_add, hab]
      rw [hsub, htie]
      exact hcon
    · rw [mul_neg, dvSupp_neg]
      exact htie
  exact hΨmin.2 r hr0 hrdeg hMuDvd

/-- **The all-slots digit floor**: every `Ψ`-development digit prices at least
`µ(g) − j·µ(Ψ)` (stated additively) — the level-2 MacLane expansion inequality. -/
theorem dvSupp_le_dev_add (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    (g : Polynomial O) (j : ℕ) :
    dvSupp F g L.u L.ℓ ≤ dvSupp F (dev Ψ g j) L.u L.ℓ + ((j * KΨ : ℕ) : ℕ∞) := by
  induction j generalizing g with
  | zero =>
    rw [dev_zero_pin]
    simpa using dvSupp_le_modByKey L hkey g
  | succ j ih =>
    have hstep : dev Ψ g (j + 1) = dev Ψ (g /ₘ Ψ) j := rfl
    rw [hstep]
    calc dvSupp F g L.u L.ℓ
        ≤ dvSupp F Ψ L.u L.ℓ + dvSupp F (g /ₘ Ψ) L.u L.ℓ :=
          dvSupp_le_divByKey_add L hπ hh hkey g
      _ ≤ dvSupp F Ψ L.u L.ℓ
            + (dvSupp F (dev Ψ (g /ₘ Ψ) j) L.u L.ℓ + ((j * KΨ : ℕ) : ℕ∞)) :=
          add_le_add le_rfl (ih (g /ₘ Ψ))
      _ = dvSupp F (dev Ψ (g /ₘ Ψ) j) L.u L.ℓ + (((j + 1) * KΨ : ℕ) : ℕ∞) := by
          rw [hKΨ]
          push_cast
          ring

/-- **The complement's slot-0 pin**: if the μ-key does NOT μ-divide `g`, reduction modulo
`Ψ` preserves `g`'s level value EXACTLY — the `dvSupp F (g %ₘ Ψ)`-to-`dvSupp F g`
relation `verdict_F12C.md` names as the heart of the no-interaction node. -/
theorem dvSupp_modByKey_eq_of_not_muDvd (hkey : IsMuKey L Ψ)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g) :
    dvSupp F (g %ₘ Ψ) L.u L.ℓ = dvSupp F g L.u L.ℓ := by
  refine le_antisymm ?_ (dvSupp_le_modByKey L hkey g)
  set r := g %ₘ Ψ with hrdef
  set q := g /ₘ Ψ with hqdef
  have hab : r + Ψ * q = g := Polynomial.modByMonic_add_div g Ψ
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dvSupp g < dvSupp r`
  rcases eq_or_ne (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ) with htie | hne
  · -- tie: the ultrametric min collapses onto `dvSupp r ≤ dvSupp g`, against `hcon`
    have hmin : min (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ)
        ≤ dvSupp F g L.u L.ℓ := by
      have h := min_dvSupp_le_dvSupp_add (u := L.u) F L.hℓ r (Ψ * q)
      rwa [hab] at h
    rw [← htie, min_self] at hmin
    exact absurd hcon (not_lt.mpr hmin)
  · have heq : dvSupp F g L.u L.ℓ
        = min (dvSupp F r L.u L.ℓ) (dvSupp F (Ψ * q) L.u L.ℓ) := by
      rw [← hab]
      exact dvSupp_add_eq F L.hℓ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left hlt.le] at heq
      rw [heq] at hcon
      exact lt_irrefl _ hcon
    · -- `dvSupp g = dvSupp (Ψ·q)` and `g − Ψ·q = r` prices strictly above: `Ψ ∣µ g`
      rw [min_eq_right hgt.le] at heq
      apply hnd
      refine ⟨q, Or.inl ⟨?_, heq⟩⟩
      have hsub : g - Ψ * q = r := by rw [← hab]; ring
      rw [hsub]
      exact hcon

/-- ★ **The abscissa-0 collapse**: a polynomial not μ-divisible by the key has its whole
level-2 support at slot `0` — `dv2Supp L Ψ g u₂ ℓ₂ = ℓ₂ • dvSupp F g L.u L.ℓ` (the
"level-2 side collapses to abscissa 0 with pin `dvSupp F g`" shape of `verdict_F12C.md`). -/
theorem dv2Supp_collapse_of_not_muDvd (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g) :
    dv2Supp L Ψ g u₂ ℓ₂ = ℓ₂ • dvSupp F g L.u L.ℓ := by
  have hg0 : g ≠ 0 := fun h0 => hnd (by rw [h0]; exact muDvd_zero L)
  have hSg' : dvSupp F g L.u L.ℓ ≠ ⊤ := dvSupp_ne_top_of_ne_zero F L.u L.ℓ hg0
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 hSg'
  refine le_antisymm ?_ ?_
  · -- `≤`: the `j = 0` term reads exactly `ℓ₂ • dvSupp g`, by the slot-0 pin
    have hle : dv2Supp L Ψ g u₂ ℓ₂ ≤ ℓ₂ • dv2Pin L Ψ g 0 + (u₂ * 0 : ℕ∞) := by
      rw [dv2Supp]
      exact Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))
    have hpin0 : dv2Pin L Ψ g 0 = dvSupp F g L.u L.ℓ := by
      show dvSupp F (dev Ψ g 0) L.u L.ℓ = dvSupp F g L.u L.ℓ
      rw [dev_zero_pin]
      exact dvSupp_modByKey_eq_of_not_muDvd L hkey hnd
    rw [hpin0] at hle
    simpa using hle
  · -- `≥`: every slot prices at least `ℓ₂ • dvSupp g`, by the digit floor + the OUTER floor
    rw [dv2Supp]
    refine Finset.le_inf fun j _ => ?_
    have hfloor := dvSupp_le_dev_add L hπ hh hkey hKΨ g j
    rcases eq_or_ne (dv2Pin L Ψ g j) ⊤ with hj_top | hj_ne
    · rw [hj_top, C118a.smul_top_pos hℓ₂, top_add]
      exact le_top
    obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hj_ne
    have hpinj : dvSupp F (dev Ψ g j) L.u L.ℓ = (Hj : ℕ∞) := hHj.symm
    rw [← hSg, hpinj] at hfloor
    have hnat : Sg ≤ Hj + j * KΨ := by exact_mod_cast hfloor
    have hgoal : ℓ₂ * Sg ≤ ℓ₂ * Hj + u₂ * j := by
      have h1 : ℓ₂ * Sg ≤ ℓ₂ * Hj + ℓ₂ * (j * KΨ) := by
        have h := Nat.mul_le_mul (le_refl ℓ₂) hnat
        rw [Nat.mul_add] at h
        exact h
      have h2 : ℓ₂ * (j * KΨ) ≤ u₂ * j := by
        calc ℓ₂ * (j * KΨ) = (ℓ₂ * KΨ) * j := by ring
          _ ≤ u₂ * j := Nat.mul_le_mul (le_of_lt hfence) (le_refl j)
      omega
    rw [← hSg, ← hHj]
    calc ℓ₂ • ((Sg : ℕ) : ℕ∞) = ((ℓ₂ * Sg : ℕ) : ℕ∞) := by
          rw [nsmul_eq_mul]; push_cast; ring
      _ ≤ ((ℓ₂ * Hj + u₂ * j : ℕ) : ℕ∞) := by exact_mod_cast hgoal
      _ = ℓ₂ • ((Hj : ℕ) : ℕ∞) + (u₂ * j : ℕ∞) := by
          rw [nsmul_eq_mul]; push_cast; ring

/-- The level-2 side set of a nonzero polynomial is nonempty (attainment of the finite
`inf`; the `dv2` twin of `C34.dvSideSet_nonempty`). -/
theorem dv2SideSet_nonempty_of_ne_zero (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {g : Polynomial O} (hg : g ≠ 0) :
    (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty := by
  classical
  have hfin : dv2Supp L Ψ g u₂ ℓ₂ ≠ ⊤ := dv2Supp_ne_top_of_ne_zero L hΨm hΨd u₂ ℓ₂ hg
  obtain ⟨j₁, _, hj₁⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (fun j => ℓ₂ • dv2Pin L Ψ g j + (u₂ * j : ℕ∞))
  have hside : dv2Supp L Ψ g u₂ ℓ₂ = ℓ₂ • dv2Pin L Ψ g j₁ + (u₂ * j₁ : ℕ∞) := hj₁
  have hhgt₁ : dv2Pin L Ψ g j₁ ≠ ⊤ := by
    intro htop
    apply hfin
    rw [hside, htop, C118a.smul_top_pos hℓ₂, top_add]
  exact ⟨j₁, mem_dv2SideSet_of_dv2OnSide L hΨm hΨd ⟨hside, hhgt₁⟩⟩

/-! ## Part 5 — ★ SUBGOAL (ii): `dv2Pin_mul_complement` -/

/-- ★ **SUBGOAL (ii) — the no-interaction node** (`dv2Pin_mul_complement`,
BLOCKERS_PLAN F1.3 row, 70–120-line pricing): multiplying by a complement `g` that the
μ-key does not μ-divide translates the level-2 support by the CONSTANT
`ℓ₂ • dvSupp F g L.u L.ℓ` — the complement's whole dv2-profile collapses onto its
abscissa-0 pin. This is the exact translation shape F1.3's infimum needs. -/
theorem dv2Pin_mul_complement (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {b g : Polynomial O} (hb : b ≠ 0) (hnd : ¬ MuDvd L Ψ g) :
    dv2Supp L Ψ (b * g) u₂ ℓ₂
      = dv2Supp L Ψ b u₂ ℓ₂ + ℓ₂ • dvSupp F g L.u L.ℓ := by
  have hΨm : Ψ.Monic := hkey.1
  have hΨd : 0 < Ψ.natDegree := hkey.2.1.1
  have hg0 : g ≠ 0 := fun h0 => hnd (by rw [h0]; exact muDvd_zero L)
  have hSurv : Dv2ResSurv L Ψ u₂ ℓ₂ := dv2ResSurv_of_muKey L hπ hh hkey hKΨ hℓ₂ hfence
  have hng : (dv2SideSet L Ψ b u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hΨm hΨd hℓ₂ hb
  have hnz : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hΨm hΨd hℓ₂ hg0
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height L b u₂ ℓ₂ hng
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height L g u₂ ℓ₂ hnz
  rw [dv2Supp_mul_eq_add_of_endpoint_le L hΨm hΨd hℓ₂ hSurv hng hnz hHg hHz,
    dv2Supp_collapse_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd]

/-! ## Part 6 — the F1.3 carrier: the signed translation conclusion, honest premises

F1.3's SIGNED form (`leanspec/Leanspec/ChapC.lean:1635-1641`, `dv2Supp_translation`)
remains BLOCKED — see the record at the end of the file.  What lands here is the carrier:
the signed conclusion **byte-as-is**, from `BlockContext` + the three honest premise
replacements this unit's engine consumes (`IsMuKey`, the key grade + OUTER floor, and the
complement's `¬ MuDvd`). -/

/-- ★ **The F1.3 carrier** — NODE C.37's signed conclusion
(`dv2Supp L Ψ f u₂ ℓ₂ = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞)`,
byte-as-is), from the standing context and the honest level-2 premises.  Consumes
`C134cfs.blockFactor_spec` (F1.1, landed) for the block split, then fires subgoal (ii). -/
theorem dv2Supp_translation_of_muKey (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hh : 0 < F.h)
    {f Ψ : Polynomial O} (hctx : BlockContext L f)
    (hkeyμ : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    (hcomp : ¬ MuDvd L Ψ (f /ₘ blockFactor L f)) :
    dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞) := by
  have hspec := C134cfs.blockFactor_spec L hπ hh hctx
  have hbf_monic : (blockFactor L f).Monic := hspec.1.1
  have hsplit : blockFactor L f * (f /ₘ blockFactor L f) = f := by
    have h := Polynomial.modByMonic_add_div f (blockFactor L f)
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hbf_monic).mpr hspec.2.1, zero_add] at h
  have hg0 : (f /ₘ blockFactor L f) ≠ 0 := fun h0 => hcomp (by rw [h0]; exact muDvd_zero L)
  have hfin : dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤ :=
    dvSupp_ne_top_of_ne_zero F L.u L.ℓ hg0
  calc dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ := by rw [hsplit]
    _ = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂
          + ℓ₂ • dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ :=
        dv2Pin_mul_complement L hπ hh hkeyμ hKΨ hℓ₂ hfence hbf_monic.ne_zero hcomp
    _ = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞) := by
        simp only [complementConst]
        rw [ENat.coe_toNat hfin]

/-! ## Part 7 — F1.3–F1.6 as SIGNED: the re-attempt record (BLOCKED-BECAUSE)

Per the F12C discipline, none of the four signed names is declared as a `theorem`,
`axiom`, or `sorry`; a signed statement is either proved in full or left to the leanspec
stub.  Against THIS unit's landed engine, the four signed forms miss exactly three
premises (re-derived, not carried over):

* **(P1) `IsTestKey L Ψ ⟹ IsMuKey L Ψ`** — the Montes "test keys are key polynomials at
  the level valuation" theorem.  Nothing landed supplies μ-minimality or μ-primality for
  a generic test key (the only landed key-polynomialhood is the S2 instance
  `C132nv3.s2Φ₂_keyPoly`, via the concrete `S2KeyPoly` certificate chain
  `C130kp5.s2KeyPoly_composedKey`).  This is the one genuinely NEW mechanism left.
* **(P2) the complement's `¬ MuDvd L Ψ (f /ₘ blockFactor L f)`** — the μ-shadow of
  F1.2's landed residual clause (`C134f12c.block_complement_notdvd`, clause 2: the
  complement's residual is not `L.r`-divisible).  Converting residual-non-divisibility
  to μ-non-divisibility is the level-2 residual↔initial-form correspondence
  (C.26/C131aa territory), not landed generically.
* **(P3) the OUTER floor** `ℓ₂ * KΨ < u₂` with `KΨ` the key's own level grade.  For a
  test key the grade is `KΨ = (L.ℓ · d_r) · L.u = L.ℓ · L.seam`
  (`C131aa.dvSupp_testKey`, private there), so the honest fence is
  `ℓ₂ * (L.ℓ * L.seam) < u₂`; the SIGNED hypothesis is only `hseam : ℓ₂ * L.seam < u₂`
  — an `L.ℓ`-factor weaker (they coincide iff `L.ℓ = 1`; at S2: signed gives `10 < 21`,
  the engine needs `20 < 21` — which holds, but is not implied).  Slot-1's landed sharp
  bound is TIGHT (`C132nv3b`'s tightness note), so no rearrangement of THIS argument
  closes the gap; either the signed statements gain the stronger fence, or a genuinely
  finer graded-residual mechanism (the μ₃ `M3-RP0` apparatus) supersedes the bound.
  [A-C.22 ENACTED, 2026-08-28 (unit A22E, per P1U/verdict_P1U §P3): the F1.3–F1.6
  signed floors are now the engine-honest `ℓ₂ * (L.ℓ * L.seam) < u₂` — RE-SIGNED
  records at C.37/C.38/C.39/C.64 in `leanspec/Leanspec/ChapC.lean`.  (P3) is no
  longer a signed-surface gap; (P1) and (P2) remain the open premises.]

Row-by-row: **F1.3** = the carrier above modulo (P1)+(P2)+(P3).  **F1.4/F1.5** need
F1.3's translated pin plus the per-slot `dv2Res` cocycle telescope — untouched here (one
refinement deeper than the support-level engine).  **F1.6** needs, beyond (P1)–(P3), the
level-2 MINIMIZER/MAXIMIZER additivity (`dv2SideMin_mul` as an EQUALITY — only the `≤`
half `C132nv2.dv2SideMin_mul_le` is landed; the level-1 equality is Theorem M clause 2,
whose level-2 twin is a full MH-scale lift), even though this unit's collapse + fence
would pin the complement's side set at `{0}` (derivable from Parts 4–5; not landed as a
named lemma here). -/

end Uniformity.Density.Tower.C134dv2g

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134dv2g.MuEquiv
#print axioms Uniformity.Density.Tower.C134dv2g.MuDvd
#print axioms Uniformity.Density.Tower.C134dv2g.MuMinimal
#print axioms Uniformity.Density.Tower.C134dv2g.MuPrime
#print axioms Uniformity.Density.Tower.C134dv2g.IsMuKey
#print axioms Uniformity.Density.Tower.C134dv2g.muDvd_zero
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_mul_modByKey_le
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_mul_modByKey_eq
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_add_le_key_quot_add
#print axioms Uniformity.Density.Tower.C134dv2g.dv2ResSurv_of_muKey
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_le_modByKey
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_le_divByKey_add
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_le_dev_add
#print axioms Uniformity.Density.Tower.C134dv2g.dvSupp_modByKey_eq_of_not_muDvd
#print axioms Uniformity.Density.Tower.C134dv2g.dv2SideSet_nonempty_of_ne_zero
#print axioms Uniformity.Density.Tower.C134dv2g.dv2Supp_collapse_of_not_muDvd
#print axioms Uniformity.Density.Tower.C134dv2g.dv2Pin_mul_complement
#print axioms Uniformity.Density.Tower.C134dv2g.dv2Supp_translation_of_muKey

end AxCheck
