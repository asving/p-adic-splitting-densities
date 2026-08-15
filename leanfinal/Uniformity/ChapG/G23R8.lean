/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G11
import Uniformity.ChapG.G23R3
import Uniformity.ChapG.G23R7

/-!
# Uniformity.ChapG.G23R8 — `resCert`, the residual-class census datum at centre modulus `m = k`

**Chapter G, NODE G.23R8** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The route's analogue of G.18 `tangCert`, at centre
modulus `m = k` and admissible set `resAdm π P k N` — the certified family A-1 names `cert_𝒫`.
The three `card_certSet_gen` hypotheses:

* `hcert` is `Iff.rfl` (the certificate is *defined* as the read landing in `resAdm`);
* **`hshift` at `m = k` HOLDS** — this is exactly the point of the replacement route, and it is
  what A-1's route (a) needed and did not have. Moving the centre inside its coset mod `π^k`,
  `γ' = γ + π^k·d`, sends the residual pair to `transPair d̄` of it (`qval_shift`/`qder_shift`),
  and `TransInvariant P` absorbs that.
* **`huniq` at `m = k` is G.11 verbatim**: the certificate gives `Tang π a (2k) γ` (since
  `⌈(2k)/2⌉ = k`), and `tang_centre_unique` pins the centre mod `π^k`.

The last conjunct identifies the certified set with `resClassSet π P k N`.

DEPENDS: G.11 (`tang_centre_unique`), G.23R3 (`TransInvariant`), G.23R7 (`resAdm_read_iff`) ·
landed `proj_surjective`, `Ideal.Quotient.mk_surjective`, `qval_shift`, `qder_shift`,
`mem_maximalIdeal_pow_iff_dvd`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem resCert (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : TransInvariant P) (k r : ℕ) :
    ∃ cert : Res O (2 * k + 1 + r) → Coeff O 2 (2 * k + 1 + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ resAdm π P k (2 * k + 1 + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ resClassSet π P k (2 * k + 1 + r)) := by
  have hkN : k ≤ 2 * k + 1 + r := by omega
  have h2k : 2 * k < 2 * k + 1 + r := by omega
  have hk : k < 2 * k + 1 + r := by omega
  have hhalf : (2 * k + 1) / 2 = k := by omega
  refine ⟨fun g c => readEquiv g c ∈ resAdm π P k (2 * k + 1 + r), fun _ _ => Iff.rfl, ?_, ?_, ?_⟩
  · -- hshift: the residual class is translation-invariant
    intro g g' c hcert hres
    obtain ⟨a, ha⟩ := proj_surjective O 2 (2 * k + 1 + r) c
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨γ', hγ'⟩ := Ideal.Quotient.mk_surjective g'
    rw [← ha, ← hγ] at hcert
    obtain ⟨b₀, b₁, e0, e1, hpair⟩ := (resAdm_read_iff hπ h2k hk γ a).1 hcert
    have heqres : resFactor (O := O) hkN (Ideal.Quotient.mk _ γ')
        = resFactor (O := O) hkN (Ideal.Quotient.mk _ γ) := by rw [hγ, hγ']; exact hres
    rw [resFactor_mk, resFactor_mk] at heqres
    obtain ⟨d, hd⟩ : π ^ k ∣ (γ' - γ) :=
      (mem_maximalIdeal_pow_iff_dvd hπ k _).1 (Ideal.Quotient.eq.1 heqres)
    have hγ'eq : γ' = γ + π ^ k * d := by linear_combination hd
    rw [← ha, ← hγ']
    refine (resAdm_read_iff hπ h2k hk γ' a).2 ⟨b₀ + b₁ * d + d * d, b₁ + 2 * d, ?_, ?_, ?_⟩
    · rw [hγ'eq, qval_shift, e0, e1]; ring
    · rw [hγ'eq, qder_shift, e1]; ring
    · have hr0 : IsLocalRing.residue O (b₀ + b₁ * d + d * d)
          = IsLocalRing.residue O b₀ + IsLocalRing.residue O b₁ * IsLocalRing.residue O d
            + IsLocalRing.residue O d * IsLocalRing.residue O d := by
        rw [map_add, map_add, map_mul, map_mul]
      have hr1 : IsLocalRing.residue O (b₁ + 2 * d)
          = IsLocalRing.residue O b₁ + 2 * IsLocalRing.residue O d := by
        rw [map_add, show (2 : O) * d = d + d by ring, map_add]; ring
      rw [hr0, hr1]
      exact hP (IsLocalRing.residue O d) _ hpair
  · -- huniq: G.11 at `t = 2k`
    intro g g' c hc1 hc2
    obtain ⟨a, ha⟩ := proj_surjective O 2 (2 * k + 1 + r) c
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨γ', hγ'⟩ := Ideal.Quotient.mk_surjective g'
    rw [← ha, ← hγ] at hc1
    rw [← ha, ← hγ'] at hc2
    obtain ⟨b₀, b₁, e0, e1, -⟩ := (resAdm_read_iff hπ h2k hk γ a).1 hc1
    obtain ⟨c₀, c₁, f0, f1, -⟩ := (resAdm_read_iff hπ h2k hk γ' a).1 hc2
    have ht : Tang π a (2 * k) γ := ⟨⟨b₀, e0⟩, by rw [hhalf]; exact ⟨b₁, e1⟩⟩
    have ht' : Tang π a (2 * k) γ' := ⟨⟨c₀, f0⟩, by rw [hhalf]; exact ⟨c₁, f1⟩⟩
    have hdvd := tang_centre_unique hπ ht ht'
    rw [hhalf] at hdvd
    rw [← hγ, ← hγ', resFactor_mk, resFactor_mk]
    exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ k _).2 hdvd)
  · -- the certified set is `resClassSet`
    intro c
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha⟩ := proj_surjective O 2 (2 * k + 1 + r) c
      obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
      rw [← ha, ← hγ] at hg
      obtain ⟨b₀, b₁, e0, e1, hpair⟩ := (resAdm_read_iff hπ h2k hk γ a).1 hg
      exact ⟨a, γ, b₀, b₁, ha, e0, e1, hpair⟩
    · rintro ⟨a, γ, b₀, b₁, ha, e0, e1, hpair⟩
      refine ⟨Ideal.Quotient.mk _ γ, ?_⟩
      rw [← ha]
      exact (resAdm_read_iff hπ h2k hk γ a).2 ⟨b₀, b₁, e0, e1, hpair⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.resCert

end AxCheck
