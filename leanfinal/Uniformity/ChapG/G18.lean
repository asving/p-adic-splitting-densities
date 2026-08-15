/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G03
import Uniformity.ChapG.G04
import Uniformity.ChapG.G09
import Uniformity.ChapG.G10
import Uniformity.ChapG.G11
import Uniformity.ChapG.G13
import Uniformity.ChapG.G15

/-!
# Uniformity.ChapG.G18 — `tangCert`, the depth-`t` census datum

**Chapter G, NODE G.18** (`blueprint/CHAP-G_base_cases_menus.md` §4). The depth-`t` certified
family in the sense of G.05, minus the forcing field: centre modulus `⌈t/2⌉`, read `readEquiv`,
admissible set `tangAdm`, with `hcert`, `hshift`, `huniq` discharged.

DEPENDS: G.03, G.04, G.09, G.10, G.11, G.13, G.15 · landed `mem_maximalIdeal_pow_iff_dvd`,
`proj_surjective`, `Ideal.Quotient.mk_surjective`.

**Stage-0e defect D1, fixed here (blueprint entry still owes the fill).** The blueprint's
SIGNATURE writes the second occurrence of the `hshift`/`huniq` modulus proof as a bare `resFactor
_ g`, which does not elaborate (`don't know how to synthesize placeholder for argument 'h'`,
goal `(t + 1) / 2 ≤ t + r`): the two equation sides' types unify the level but a bare `_` still
needs an actual proof term, which nothing forces. The fix, already applied in
`leanspec/Leanspec/ChapG.lean` (D1), is the minimal one: repeat the same `(by omega : (t + 1) / 2
≤ t + r)` proof explicitly. By proof irrelevance this is type-identical to the left-hand side's
proof, so no consumer of this node is affected.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- A class of `Res O N` reads inside `dvdSet π k N` at its own lift iff the lift is divisible by
`π ^ k` — the bridge between the abstract-class membership `dvdSet` and concrete divisibility,
needed whenever a centre in `Res O N` is unfolded to an `O`-lift. -/
theorem mem_dvdSet_iff_dvd (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N) (z : O) :
    (Ideal.Quotient.mk _ z : Res O N) ∈ dvdSet π k N ↔ π ^ k ∣ z := by
  constructor
  · rintro ⟨y, hy⟩
    have hdvd : π ^ N ∣ (π ^ k * y - z) :=
      (mem_maximalIdeal_pow_iff_dvd hπ N _).1 (Ideal.Quotient.eq.1 hy)
    have hdvd' : π ^ k ∣ (π ^ k * y - z) := dvd_trans (pow_dvd_pow π hk) hdvd
    have hz : π ^ k ∣ (π ^ k * y - (π ^ k * y - z)) := dvd_sub (dvd_mul_right (π ^ k) y) hdvd'
    rwa [sub_sub_cancel] at hz
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem tangCert (hπ : Irreducible π) (t r : ℕ) :
    ∃ cert : Res O (t + r) → Coeff O 2 (t + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ tangAdm π t (t + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : (t + 1) / 2 ≤ t + r) g'
            = resFactor (by omega : (t + 1) / 2 ≤ t + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : (t + 1) / 2 ≤ t + r) g'
            = resFactor (by omega : (t + 1) / 2 ≤ t + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ tangSet π (t + r) t) := by
  have htN : t ≤ t + r := by omega
  have hmN : (t + 1) / 2 ≤ t + r := by omega
  have cert_iff_tang : ∀ (γ : O) (a : Fin 2 → O),
      readEquiv (Ideal.Quotient.mk _ γ) (proj O 2 (t + r) a) ∈ tangAdm π t (t + r) ↔
        Tang π a t γ := by
    intro γ a
    rw [readEquiv_proj]
    simp only [tangAdm, Set.mem_prod, Tang]
    exact and_congr (mem_dvdSet_iff_dvd hπ htN _) (mem_dvdSet_iff_dvd hπ hmN _)
  refine ⟨fun g c => readEquiv g c ∈ tangAdm π t (t + r), fun _ _ => Iff.rfl, ?_, ?_, ?_⟩
  · -- hshift
    intro g g' c hcertg hres
    obtain ⟨a, ha⟩ := proj_surjective O 2 (t + r) c
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨γ', hγ'⟩ := Ideal.Quotient.mk_surjective g'
    rw [← ha, ← hγ] at hcertg
    have htang : Tang π a t γ := (cert_iff_tang γ a).1 hcertg
    have heq : resFactor (O := O) hmN (Ideal.Quotient.mk _ γ')
        = resFactor (O := O) hmN (Ideal.Quotient.mk _ γ) := by rw [hγ, hγ']; exact hres
    rw [resFactor_mk, resFactor_mk] at heq
    have hdvd : π ^ ((t + 1) / 2) ∣ (γ' - γ) :=
      (mem_maximalIdeal_pow_iff_dvd hπ ((t + 1) / 2) _).1 (Ideal.Quotient.eq.1 heq)
    have htang' : Tang π a t γ' := tang_shift htang hdvd
    rw [← ha, ← hγ']
    exact (cert_iff_tang γ' a).2 htang'
  · -- huniq
    intro g g' c hc1 hc2
    obtain ⟨a, ha⟩ := proj_surjective O 2 (t + r) c
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨γ', hγ'⟩ := Ideal.Quotient.mk_surjective g'
    rw [← ha, ← hγ] at hc1
    rw [← ha, ← hγ'] at hc2
    have htang : Tang π a t γ := (cert_iff_tang γ a).1 hc1
    have htang' : Tang π a t γ' := (cert_iff_tang γ' a).1 hc2
    have hdvd : π ^ ((t + 1) / 2) ∣ (γ' - γ) := tang_centre_unique hπ htang htang'
    rw [← hγ, ← hγ', resFactor_mk, resFactor_mk]
    exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ ((t + 1) / 2) _).2 hdvd)
  · -- the tangSet identification
    intro c
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨a, ha⟩ := proj_surjective O 2 (t + r) c
      obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective g
      rw [← ha, ← hγ] at hg
      exact ⟨a, ha, γ, (cert_iff_tang γ a).1 hg⟩
    · rintro ⟨a, ha, γ, hTang⟩
      exact ⟨Ideal.Quotient.mk _ γ, by rw [← ha]; exact (cert_iff_tang γ a).2 hTang⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.mem_dvdSet_iff_dvd
#print axioms Uniformity.Density.Menu.tangCert

end AxCheck
