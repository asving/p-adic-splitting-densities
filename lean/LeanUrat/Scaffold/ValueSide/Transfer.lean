/-
BP_IV §1.1 — Step 13, the drainage-transfer layer (`Transfer.lean`).
Units in this file: SKEL (module skeleton, this unit).  Later waves add
T0 (`card_boxProj_fiber`), T1 (`env_antitone`, landed), T2 (FLOOR), T3 (TR-Q skeleton),
T4a/T4 (`discV` + `DrainageImports`), T5, T6 (`env_tendsto_zero_of_imports`),
and the wave-4 HARD constructors T7 (CEIL) and T8 (tail).
Import graph (BP_IV §0/§1.0): no value-side module is imported here; the
counting vocabulary (`ClassifierSpec.decided/undec/env/dmass`, `Box`,
`boxProj`, `canonical_stable`) is reused BY IMPORT from the corpus
(`LeanUrat/MovesU/Defs.lean`), never redefined.
-/
import Mathlib
import LeanUrat.MovesU.Defs

/-!
# The abstract drainage-transfer layer [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.1, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.1 (statement layer) and §0
  (module map row `Transfer.lean` | step 13 | "abstract drainage transfer
  over `ClassifierSpec`").
* Math source of record: the O4T brief (drainage transfer; M05 core), per
  BP_IV §0 step-13 row.
* Imports: `Mathlib` + `LeanUrat.MovesU.Defs` (corpus `ClassifierSpec`
  vocabulary, §3 corpus-reuse map). No value-side module.
-/

namespace LeanUrat.Scaffold

open Filter
open LeanUrat.MovesU

/-!
**PROVENANCE (unit T0; BP_IV §1.1 row T0, source O4T brief §2, level bookkeeping).**
Statement transcribed VERBATIM from `lean/blueprints/BP_IV.md` §1.1.
Mechanism (blueprint row T0): per-coordinate, the fiber of `ZMod.castHom`
has size p^(N'−N) (helper `card_castHom_fiber`: translate the fiber to the
kernel, then Lagrange + first isomorphism theorem — the C1_TYP_toClause
pattern); then product over `Fin n` (the HNode1 `subtypePiEquivPi` pattern).
-/

/-- T0 helper (per-coordinate): the fiber of `ZMod.castHom : ZMod (p^N') → ZMod (p^N)`
over any point has exactly p^(N'−N) elements. -/
theorem card_castHom_fiber {p : ℕ} [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (y : ZMod (p ^ N)) :
    Nat.card {x : ZMod (p ^ N') //
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N)) x = y} = p ^ (N' - N) := by
  have hp : p.Prime := Fact.out
  set ψ : ZMod (p ^ N') →+ ZMod (p ^ N) :=
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N))).toAddMonoidHom with hψ
  have hψsurj : Function.Surjective ψ := ZMod.castHom_surjective (pow_dvd_pow p h)
  -- Lagrange + first isomorphism theorem: p^N' = p^N · #ker ψ
  have hLag : p ^ N' = p ^ N * Nat.card ψ.ker := by
    have hG := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv]
      at hG
    simpa [Nat.card_zmod] using hG
  -- cancel the positive factor p^N
  have hker : Nat.card ψ.ker = p ^ (N' - N) := by
    have hpow : p ^ N' = p ^ N * p ^ (N' - N) := by
      rw [← pow_add, Nat.add_sub_cancel' h]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos N) (hLag.symm.trans hpow)
  -- the fiber over y is equinumerous with the kernel
  have e : {x : ZMod (p ^ N') // ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N)) x = y}
      ≃ ↥(ψ ⁻¹' {y}) := Equiv.subtypeEquivRight (fun x => by simp [hψ])
  rw [Nat.card_congr e,
    Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hψsurj y), hker]

/-- T0: fibers of the level reduction have exact size p^{n(N'−N)}. -/
theorem card_boxProj_fiber {p n : ℕ} [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (f : Box p n N) :
    Nat.card {g : Box p n N' // boxProj p n h g = f} = p ^ (n * (N' - N)) := by
  have hiff : ∀ g : Box p n N',
      boxProj p n h g = f ↔
        ∀ i, ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N)) (g i) = f i := by
    intro g
    exact funext_iff
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans
      (Equiv.subtypePiEquivPi (p := fun i (b : ZMod (p ^ N')) =>
        ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N)) b = f i))),
    Nat.card_pi]
  simp only [card_castHom_fiber h]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    Nat.mul_comm]

/-!
**PROVENANCE (unit T1; BP_IV §1.1 row T1, source O4T §2 TR-0 prelim).**
Statement transcribed VERBATIM from `lean/blueprints/BP_IV.md` §1.1.
Mechanism (blueprint row T1): `canonical_stable` contraposed — an undecided
level-N' class projects to an undecided level-N class — so Undec(N') injects
into the disjoint union of the `boxProj` fibers over Undec(N); each fiber has
exactly p^{n(N'−N)} elements (T0), giving undec(N') ≤ undec(N)·p^{n(N'−N)},
i.e. env(N') ≤ env(N) after dividing by p^{nN'}.
-/

/-- T1 (stability ⇒ monotone envelope): env is antitone. -/
theorem ClassifierSpec.env_antitone {n p : ℕ} [Fact p.Prime]
    (X : ClassifierSpec n p) : Antitone X.env := by
  intro N N' h
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ N') := ⟨pow_ne_zero _ hp.ne_zero⟩
  -- `canonical_stable`, contraposed: undecided at N' ⇒ undecided projection at N.
  have hnone : ∀ g : Box p n N', X.canonical N' g = none →
      X.canonical N (boxProj p n h g) = none := by
    intro g hg
    cases hc : X.canonical N (boxProj p n h g) with
    | none => rfl
    | some σ =>
        have hs := X.canonical_stable h g σ hc
        rw [hg] at hs
        simp at hs
  -- T0 counting: the undecided-at-N lift block has size undec(N)·p^{n(N'−N)}.
  have hcount : Nat.card {g : Box p n N' // X.canonical N (boxProj p n h g) = none}
      = X.undec N * p ^ (n * (N' - N)) := by
    have E : {g : Box p n N' // X.canonical N (boxProj p n h g) = none} ≃
        Σ f : {f : Box p n N // X.canonical N f = none},
          {g : Box p n N' // boxProj p n h g = f.1} :=
      { toFun := fun g => ⟨⟨boxProj p n h g.1, g.2⟩, ⟨g.1, rfl⟩⟩
        invFun := fun x => ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
        left_inv := fun g => rfl
        right_inv := fun x => by
          obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := x
          dsimp only at hg
          subst hg
          rfl }
    rw [Nat.card_congr E, Nat.card_sigma]
    simp only [card_boxProj_fiber h]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    unfold ClassifierSpec.undec
    rw [Nat.card_eq_fintype_card]
  -- inject Undec(N') into the lift block, then compare counts.
  have hle : X.undec N' ≤ X.undec N * p ^ (n * (N' - N)) := by
    rw [← hcount]
    unfold ClassifierSpec.undec
    exact Nat.card_le_card_of_injective
      (fun g => (⟨g.1, hnone g.1 g.2⟩ :
        {g : Box p n N' // X.canonical N (boxProj p n h g) = none}))
      (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
  -- divide by p^{nN'} and cancel the fiber factor.
  have hexp : n * N' = n * N + n * (N' - N) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' h]
  unfold ClassifierSpec.env
  calc (X.undec N' : ℝ) / (p : ℝ) ^ (n * N')
      ≤ ((X.undec N * p ^ (n * (N' - N)) : ℕ) : ℝ) / (p : ℝ) ^ (n * N') :=
        div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)
    _ = (X.undec N : ℝ) / (p : ℝ) ^ (n * N) := by
        push_cast
        rw [hexp, pow_add]
        exact mul_div_mul_right _ _
          (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))

/-!
**PROVENANCE (unit T2; BP_IV §1.1 row T2, source O4T §2 FLOOR).**
Statement transcribed VERBATIM from `lean/blueprints/BP_IV.md` §1.1.
Mechanism (blueprint row T2): pointwise undecided-nesting gives a subtype
injection Undec_X(N) ↪ Undec_Y(N), hence `Nat.card` monotonicity on
`undec`; the envelopes then compare after dividing by the common positive
normalizer p^{nN}.
-/

/-- T2 (FLOOR, abstract): pointwise undecided-nesting transfers envelopes. -/
theorem env_le_of_undec_subset {n p : ℕ} [Fact p.Prime]
    {X Y : ClassifierSpec n p}
    (hsub : ∀ N (f : Box p n N), X.canonical N f = none → Y.canonical N f = none) :
    ∀ N, X.env N ≤ Y.env N := by
  intro N
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  -- subtype injection ⇒ Nat.card mono on `undec`
  have hcard : X.undec N ≤ Y.undec N := by
    unfold ClassifierSpec.undec
    exact Nat.card_le_card_of_injective
      (fun f => (⟨f.1, hsub N f.1 f.2⟩ :
        {f : Box p n N // Y.canonical N f = none}))
      (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
  -- divide by the common positive normalizer p^{nN}
  have hpow : (0 : ℝ) < (p : ℝ) ^ (n * N) :=
    pow_pos (by exact_mod_cast hp.pos) _
  unfold ClassifierSpec.env
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpow.le

/-- T3 (TR-Q skeleton): an antitone envelope dominated along an unbounded monotone
    reparametrization by a vanishing bound itself vanishes.  (The O4T pass-1
    critical — Γ unbounded — is the `hg` hypothesis; never state without it.) -/
theorem env_tendsto_zero_of_majorant {E B : ℕ → ℝ} {g : ℕ → ℕ}
    (hE : Antitone E) (hE0 : ∀ N, 0 ≤ E N) (hg : Tendsto g atTop atTop)
    (hle : ∀ N, E (g N) ≤ B N) (hB : Tendsto B atTop (nhds 0)) :
    Tendsto E atTop (nhds 0) := by
  -- E is antitone and bounded below, so it converges to its infimum.
  have hbdd : BddBelow (Set.range E) :=
    ⟨0, fun x hx => by obtain ⟨n, rfl⟩ := hx; exact hE0 n⟩
  have hlim : Tendsto E atTop (nhds (⨅ i, E i)) := tendsto_atTop_ciInf hE hbdd
  -- Along the unbounded reparametrization `g`, the subsequence has the same limit …
  have hEg : Tendsto (fun N => E (g N)) atTop (nhds (⨅ i, E i)) := hlim.comp hg
  -- … and is squeezed to 0 by the vanishing majorant.
  have hEg0 : Tendsto (fun N => E (g N)) atTop (nhds 0) :=
    squeeze_zero (fun N => hE0 (g N)) hle hB
  have h0 : (⨅ i, E i) = 0 := tendsto_nhds_unique hEg hEg0
  rwa [h0] at hlim

end LeanUrat.Scaffold
