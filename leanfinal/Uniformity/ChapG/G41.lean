/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G13
import Uniformity.ChapG.G23R9
import Uniformity.ChapG.G23R11
import Uniformity.ChapG.G23R12
import Uniformity.ChapG.G26
import Uniformity.ChapG.G27
import Uniformity.ChapG.G28
import Uniformity.ChapG.G30
import Uniformity.ChapG.G31
import Uniformity.ChapG.G38

/-!
# Uniformity.ChapG.G41 — `card_inertStratum`, the exact inert half of an even stratum

**Chapter G, NODE G.41** (`blueprint/CHAP-G_base_cases_menus.md` §5, AMENDMENT §A-8.1). *The inert
count at level `N = 2k+1+r`*:

  `2 · #(inertStratum π (2k+1+r) k) + q^(2k+2r+1) = q^(2k+2r+2)`,

i.e. `#(inertStratum) = (q−1)·q^(2k+2r)/2` in additive, `ℕ`-subtraction-free form. The factor `2`
is the residue-field count `#{anisotropic pairs} = q(q−1)/2` of G.38 carried up the tower.

The mechanism is a chain of three landed identities:
* `inertStratum_eq` — the inert half of the even depth-`2k` stratum is *exactly* the residual class
  set of the anisotropic pairs, `resClassSet π {p | AniForm p} k N` (needs `2k+1 ≤ N`);
* `card_resClassSet` (G.23R9) — that set has `#P · q^(2k+2r)` elements;
* `two_mul_card_aniForm` (G.38) — `2·#{p | AniForm p} + q = q·q` over the residue field.

Following the blueprint's SIZE note, the set identity is factored through the
predicate-parametrised `stratum_eq_resClassSet`, which G.42 reuses verbatim with
`AniForm ↝ SepPair`; and the node also carries the two reusable counting utilities the rest of the
chapter's roll-up consumes: `card_biUnion_range_of_disjoint` (G.43, G.44) and `depthSet_disjoint`
(G.43, G.44). Finally `decidedSet_inert_eq` — the companion of G.31's `decidedSet_ram_eq`, which
G.31's docstring defers to here — is landed with the EXACT index set `Finset.range ((N+1)/2)`
(`k < (N+1)/2 ↔ 2k+1 ≤ N`), no overshoot.

DEPENDS: G.13 (`tangSet_antitone`), G.23R9 (`card_resClassSet`), G.23R11
(`resClassSet_subset_depthSet`), G.23R12 (`aniso_iff_aniForm`, `sepPair_iff_exists_simple_root`),
G.26 (`depth_even_dichotomy`), G.27 (`decidedAt_inert_of_ani`), G.28 (`decidedAt_split_of_sep`),
G.30 (`depth_type`), G.31 (`inertStratum`, template `decidedSet_ram_eq`), G.38
(`two_mul_card_aniForm`) · landed `resClassSet` (G.23R4), `aniForm_transInvariant`,
`aniForm_not_dblPair` (G.23R3), `exists_split_lift` (G.33), `depthSet_odd_eq_empty` is NOT needed
here (the inert index set does not overshoot), `exists_max_step`, `Tang_zero`,
`splitType_ne_inertType`, `inertType_ne_ramType`.

**PROOF of the set identity** (`stratum_eq_resClassSet`, both halves).
* (⊇) `resClassSet π P k N ⊆ depthSet π N (2k)` is G.23R11, whose hypothesis "no member of `P` is a
  `DblPair`" is `aniForm_not_dblPair`; `σ`-decidedness of the class comes from the membership data
  `(a, γ, b₀, b₁)` through the caller-supplied certificate `hcertP` (for inert: `aniso_iff_aniForm`
  into `decidedAt_inert_of_ani`), transported along `proj O 2 N a = c`.
* (⊆) a class in the depth-EXACTLY-`2k` stratum has a lift `a` and a centre `γ` with
  `Tang π a (2k) γ` and no centre at depth `2k+1`; reading `Tang` gives `b₀, b₁` with
  `qval a γ = π^(2k)·b₀`, `qder a γ = π^k·b₁` (note `(2k+1)/2 = k` in `ℕ`). G.26's dichotomy
  then says the residual pair is anisotropic or has a simple root, i.e. lands in `P ∪ Q`; the `Q`
  branch certifies the class as `τ`-decided, contradicting `σ`-decidedness since `σ ≠ τ`.

**PROOF of `decidedSet_inert_eq`** = verbatim G.31's `decidedSet_ram_eq` with the roles rotated:
an inert-decided class admits no depth-`N` centre (G.33 would produce a `splitType` lift),
`exists_max_step` returns a maximal depth `t < N`, `c ∈ depthSet π N t`, and G.30's `depth_type`
kills the odd branch (it would make `c` ram-decided).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-! ## 1. Two reusable counting utilities -/

/-- **Counting a finite disjoint union indexed by `Finset.range m`.** Consumed by G.43 and G.44. -/
theorem card_biUnion_range_of_disjoint {α : Type*} [Finite α] (m : ℕ) (S : ℕ → Set α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    Nat.card (⋃ k ∈ Finset.range m, S k) = ∑ k ∈ Finset.range m, Nat.card (S k) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : Disjoint (S m) (⋃ k ∈ Finset.range m, S k) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx'
      have hlt := Finset.mem_range.1 hi
      exact (Set.disjoint_left.1 (hdisj m i (by omega))) hx hxi
    rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self,
      Finset.set_biUnion_insert, Nat.card_coe_set_eq,
      Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, ih]

omit [Finite (IsLocalRing.ResidueField O)] in
/-- **Distinct depths give disjoint strata.** The deeper stratum sits inside `tangSet π N (t+1)`,
which the shallower one avoids by construction. Consumed by G.43 and G.44. -/
theorem depthSet_disjoint (hπ : Irreducible π) {N t t' : ℕ} (h : t ≠ t') :
    Disjoint (depthSet π N t) (depthSet π N t') := by
  rcases Nat.lt_or_ge t t' with hlt | hge
  · rw [Set.disjoint_left]
    intro c hc hc'
    exact hc.2 (tangSet_antitone hπ (show t + 1 ≤ t' by omega) hc'.1)
  · rw [Set.disjoint_left]
    intro c hc hc'
    exact hc'.2 (tangSet_antitone hπ (show t' + 1 ≤ t by omega) hc.1)

/-! ## 2. The shared set identity -/

/-- **The engine of G.41/G.42.** The even depth-`2k` stratum cut out by `σ`-decidedness is exactly
the residual class set of `P`, whenever `P` certifies type `σ`, the complementary class `Q`
certifies a DIFFERENT type `τ`, `P` avoids the double-root pairs, and `P ∪ Q` absorbs G.26's
dichotomy `AniForm ∨ SepPair`. -/
theorem stratum_eq_resClassSet (hπ : Irreducible π)
    {P Q : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    {σ τ : FactorizationType} {k N : ℕ} (hN : 2 * k + 1 ≤ N) (hστ : σ ≠ τ)
    (hPdbl : ∀ p ∈ P, ¬ DblPair p)
    (hcertP : ∀ (a : Fin 2 → O) (γ b₀ b₁ : O), qval a γ = π ^ (2 * k) * b₀ →
      qder a γ = π ^ k * b₁ →
      (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P →
      DecidedAt O 2 σ N (proj O 2 N a))
    (hcertQ : ∀ (a : Fin 2 → O) (γ b₀ b₁ : O), qval a γ = π ^ (2 * k) * b₀ →
      qder a γ = π ^ k * b₁ →
      (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ Q →
      DecidedAt O 2 τ N (proj O 2 N a))
    (hdich : ∀ p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O,
      AniForm p ∨ SepPair p → p ∈ P ∨ p ∈ Q) :
    {c ∈ depthSet π N (2 * k) | DecidedAt O 2 σ N c} = resClassSet π P k N := by
  ext c
  constructor
  · rintro ⟨⟨⟨a, ha, γ, hT⟩, hnot⟩, hdec⟩
    have hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ' := by
      rintro ⟨γ', hγ'⟩
      exact hnot ⟨a, ha, γ', hγ'⟩
    obtain ⟨b₀, e0⟩ := hT.1
    obtain ⟨b₁, e1⟩ : π ^ k ∣ qder a γ := by
      have h := hT.2
      rwa [show (2 * k + 1) / 2 = k by omega] at h
    have hres := hdich (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)
      ((depth_even_dichotomy (N := N) hπ hT hmax e0 e1).imp
        (fun h => (aniso_iff_aniForm hπ b₀ b₁).1 h)
        (fun h => (sepPair_iff_exists_simple_root hπ b₀ b₁).2 h))
    rcases hres with hp | hq
    · exact ⟨a, γ, b₀, b₁, ha, e0, e1, hp⟩
    · exact absurd ((hdec a ha).symm.trans (hcertQ a γ b₀ b₁ e0 e1 hq a rfl)) hστ
  · intro hc
    refine ⟨resClassSet_subset_depthSet hπ hPdbl hN hc, ?_⟩
    obtain ⟨a, γ, b₀, b₁, ha, e0, e1, hp⟩ := hc
    rw [← ha]
    exact hcertP a γ b₀ b₁ e0 e1 hp

/-- **The inert half of an even stratum, in residual form.** -/
theorem inertStratum_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} (hN : 2 * k + 1 ≤ N) :
    inertStratum π N k = resClassSet π {p | AniForm p} k N := by
  refine stratum_eq_resClassSet hπ (Q := {p | SepPair p}) (τ := splitType) hN
    (Ne.symm splitType_ne_inertType) (fun _ hp => aniForm_not_dblPair hp) ?_ ?_ (fun _ h => h)
  · intro a γ b₀ b₁ h0 h1 hp
    exact decidedAt_inert_of_ani hπ hN h0 h1 ((aniso_iff_aniForm hπ b₀ b₁).2 hp)
  · intro a γ b₀ b₁ h0 h1 hp
    obtain ⟨z, hz, hs⟩ := (sepPair_iff_exists_simple_root hπ b₀ b₁).1 hp
    exact decidedAt_split_of_sep hπ hN h0 h1 hz hs

/-! ## 3. The decided-set union identity (companion of G.31's ram form) -/

/-- **The level-`N` partition, inert half.** A class is `inertType`-decided at level `N` exactly
when it lies in one of the inert halves of the even depth strata with `2k+1 ≤ N`. Unlike G.31's
ram form the index set `Finset.range ((N+1)/2)` is EXACT: `k < (N+1)/2 ↔ 2k+1 ≤ N`. -/
theorem decidedSet_inert_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 inertType N = ⋃ k ∈ Finset.range ((N + 1) / 2), inertStratum π N k := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    have hnt : ¬ ∃ γ, Tang π a N γ := by
      rintro ⟨γ, hγ⟩
      obtain ⟨b, hb, hbty⟩ := exists_split_lift hπ hγ
      exact splitType_ne_inertType (hbty.symm.trans (hc b (hb.trans ha)))
    obtain ⟨t, htlt, hPt, hmax⟩ :=
      exists_max_step (Q := fun t => ∃ γ, Tang π a t γ) ⟨0, Tang_zero π a 0⟩ N hnt
    have hmem : c ∈ depthSet π N t := by
      refine ⟨?_, ?_⟩
      · obtain ⟨γ, hγ⟩ := hPt
        exact ⟨a, ha, γ, hγ⟩
      · rintro ⟨b, hb, γ', hγ'⟩
        exact hmax ⟨γ', tang_of_proj_eq hπ (by omega) (hb.trans ha.symm) hγ'⟩
    rcases depth_type hπ htlt hmem with ⟨j, hj, hd⟩ | ⟨k, hk, _⟩
    · exact absurd ((hc a ha).symm.trans (hd a ha)) inertType_ne_ramType
    · subst hk
      exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), hmem, hc⟩
  · intro hc
    obtain ⟨k, _, hmem⟩ := Set.mem_iUnion₂.1 hc
    exact hmem.2

/-! ## 4. The count -/

/-- **G.41.** The exact inert count at level `N = 2k+1+r`, in additive form:
`2·#(inertStratum) + q^(2k+2r+1) = q^(2k+2r+2)`. -/
theorem card_inertStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (inertStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2) := by
  rw [inertStratum_eq hπ (show 2 * k + 1 ≤ 2 * k + 1 + r by omega),
    card_resClassSet hπ aniForm_transInvariant k r]
  have h38 : 2 * Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O //
      AniForm p} + residueCard O = residueCard O * residueCard O :=
    two_mul_card_aniForm (IsLocalRing.ResidueField O)
  have hcast : Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O |
      AniForm p} = Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O //
      AniForm p} := rfl
  rw [hcast]
  set A := Nat.card {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O // AniForm p}
  set q := residueCard O
  calc 2 * (A * q ^ (2 * k + 2 * r)) + q ^ (2 * k + 2 * r + 1)
      = (2 * A + q) * q ^ (2 * k + 2 * r) := by ring
    _ = (q * q) * q ^ (2 * k + 2 * r) := by rw [h38]
    _ = q ^ (2 * k + 2 * r + 2) := by ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_biUnion_range_of_disjoint
#print axioms Uniformity.Density.Menu.depthSet_disjoint
#print axioms Uniformity.Density.Menu.stratum_eq_resClassSet
#print axioms Uniformity.Density.Menu.inertStratum_eq
#print axioms Uniformity.Density.Menu.decidedSet_inert_eq
#print axioms Uniformity.Density.Menu.card_inertStratum

end AxCheck
