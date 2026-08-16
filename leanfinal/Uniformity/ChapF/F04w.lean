/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F05
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapF.F04w — the `JD0-BOX-2` witness layer (HYP.74's fold route, proved half)

**An F.04/F.05-adjacent appendix file, not a blueprint node** (the H09w/H89w/H73w
precedent; registered by blueprint AMENDMENT A-W.2, 2026-08-16, unit OM-9). It lands the
SITE-INDEPENDENT halves of HYP.74's discharge route, certified before proving by
`verification/openmath/om9_weld_cert.py` LEG A (95-check battery, both primes, 8/8 planted
mutants caught):

* `JD0SiteStrike.jd0Box2` — a per-site strike whose ledger leg is exhibited WITNESSES the
  perimeter `JD0Box2` for its site. This is HYP.74's own disposition made a theorem shape:
  "record per site that the gauge consumed there is an explicit z-power unit character
  verified in-note, which strikes the inheritance." Seven strike instances (W11, W12,
  HMENU3, HEX3, GENIND, GENH4, GENHN) remain INSTANCE-ROWS gated on chapter H/C site
  objects (GC-13) — this file supplies the lemma each instantiation fires.
* `IsGaugeCocycle` + `IsGaugeCocycle.mul` + `gaugeCobdry_isCocycle` — the perimeter's
  CONSISTENCY: the ledger leg `c ↦ c·∂u` carries the 2-cocycle class to itself (∂u is a
  coboundary, coboundaries are cocycles, cocycles are closed under products). So the
  four-line action is well-posed on exactly the class of tables F.07's `CarryCocycle`
  carries — the two surviving weld conjuncts ride ONE gauge mechanism.
* `gaugeCobdry_gaugeCobdry` — the action property: gauging by `u` then `w` is gauging by
  `u * w`.

**What this file does NOT do (the honest boundary, HYP.74 unchanged):** it does not prove
`JD0Box2` for any site, and it cannot — that the weld's actual value dictionary IS of the
four-line form is synthesis priced at GRTJA 1/2 (`EFF.JD0.22` BOX-2, honesty F-6/F-7). The
conjunct stays CARRY; what shrinks is the mechanism side, which is now theorems.
-/

namespace Uniformity.Density.Weld

variable {Γ : Type*} [AddCommGroup Γ] {K : Type*} [Field K]

/-- The `Kˣ`-valued 2-cocycle law over the slot group `Γ` — F.07's `cocycle` field shape,
at the gauge layer's generality (the class the four-line action acts on). -/
def IsGaugeCocycle (c : Γ → Γ → Kˣ) : Prop :=
  ∀ a b d, c a b * c (a + b) d = c b d * c a (b + d)

/-- Cocycles are closed under pointwise products. -/
theorem IsGaugeCocycle.mul {c e : Γ → Γ → Kˣ} (hc : IsGaugeCocycle c)
    (he : IsGaugeCocycle e) : IsGaugeCocycle fun a b => c a b * e a b := by
  intro a b d
  show (c a b * e a b) * (c (a + b) d * e (a + b) d)
      = (c b d * e b d) * (c a (b + d) * e a (b + d))
  rw [mul_mul_mul_comm, hc a b d, he a b d, mul_mul_mul_comm]

/-- **The perimeter's consistency** (certified at om9_weld_cert.py LEG A2 over every
enumerated cocycle at `E ∈ {2,3}`, both primes, before proving): the ledger leg `c ↦ c·∂u`
of `EFF.JD0.05` carries 2-cocycles to 2-cocycles. -/
theorem gaugeCobdry_isCocycle (u : Γ → Kˣ) {c : Γ → Γ → Kˣ} (hc : IsGaugeCocycle c) :
    IsGaugeCocycle (gaugeCobdry u c) := by
  intro a b d
  show (c a b * u a * u b) * (u (a + b))⁻¹ * ((c (a + b) d * u (a + b) * u d) * (u (a + b + d))⁻¹)
      = (c b d * u b * u d) * (u (b + d))⁻¹ * ((c a (b + d) * u a * u (b + d)) * (u (a + (b + d)))⁻¹)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_mul_div_comm, div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  apply Units.ext
  push_cast
  have key := congrArg (Units.val : Kˣ → K) (hc a b d)
  push_cast at key
  simp only [add_assoc]
  ring_nf
  ring_nf at key
  linear_combination ((u a : K) * (u b : K) * (u d : K) * (u (a + (b + d)) : K)
    * (u (a + b) : K) * (u (b + d) : K)) * key

/-- The gauge action composes: gauging by `u` then `w` is gauging by `u * w`. -/
theorem gaugeCobdry_gaugeCobdry (u w : Γ → Kˣ) (c : Γ → Γ → Kˣ) :
    gaugeCobdry w (gaugeCobdry u c) = gaugeCobdry (u * w) c := by
  funext a b
  show (c a b * u a * u b) * (u (a + b))⁻¹ * w a * w b * (w (a + b))⁻¹
      = c a b * (u a * w a) * (u b * w b) * (u (a + b) * w (a + b))⁻¹
  rw [mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- **HYP.74's fold route, site-independent half:** a strike (the site's gauge exhibited as
an explicit z-power unit character, slot leg) together with its ledger leg witnesses the
perimeter `JD0Box2` for its site. Seven per-site instances remain GC-13-gated. -/
theorem JD0SiteStrike.jd0Box2 (st : JD0SiteStrike Γ K)
    (hledger : st.site.ledgerAct = gaugeCobdry fun γ => st.z ^ st.a γ) :
    JD0Box2 st.site :=
  ⟨fun γ => st.z ^ st.a γ, st.strike, hledger⟩

end Uniformity.Density.Weld
