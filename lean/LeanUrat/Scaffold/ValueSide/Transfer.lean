/-
BP_IV §1.1 — Step 13, the drainage-transfer layer (`Transfer.lean`).
Units in this file: SKEL (module skeleton), T0 (`card_boxProj_fiber`),
T1 (`env_antitone`), T2 (FLOOR), T3 (TR-Q skeleton), T4a (`discV`, landed),
T4 (`tailC` + `DrainageImports` + `undec_subset_tail`, landed — `tailC` is a
NEW flagged supporting definition, see the unit-T4 provenance note),
T4b (`canonicalOrderLEOne`, the concrete order-≤1 classifier, landed —
see the unit-T4b provenance note for its walk-transcription layer).
Later waves add T5 (T6 landed early with the T5 bound inline).
T7 (CEIL) is PARTIAL: the verbatim statement `canonicalOrderLEOne_ceil`
compiles, its closure-reduction and Step-0 assembly layers are PROVED, and
the remaining content is exactly ONE honest `sorry` at the per-cluster core
`OrderLEOne.clusterWalk_audit` (BLOCKED(T7) — the Theorem-N3 chain over
`Q̄_p` root valuations; see the unit-T7 provenance note).
T8 (tail) LANDED (`discV_tail_count`, the `DrainageImports.tail` constructor):
it adds the corpus import `LeanUrat.MovesX.XF7` (M05 Lemma C's Lean count form
`tailCountBound`, PROVED corpus, itself importing only MovesX modules — the
value-side import graph stays acyclic).
Import graph (BP_IV §0/§1.0 + §2 T-table deps): the counting vocabulary
(`ClassifierSpec.decided/undec/env/dmass`, `Box`, `boxProj`,
`canonical_stable`) is reused BY IMPORT from the corpus
(`LeanUrat/MovesU/Defs.lean`), never redefined; the K0 valuation vocabulary
(`zmodVal`, units K0a/K0b) is reused BY IMPORT from
`LeanUrat/Scaffold/ValueSide/KCount.lean` — T4a's declared dep is K0
(BP_IV §2 T-table), and `KCount.lean` imports only Mathlib, so the
value-side import graph stays acyclic.  Unit T4b adds corpus reuse (§3):
the lower-hull engine (`LeanUrat/OM/NewtonPolygon.lean`, `npHeight`/`npSides`)
and the ℤ_p true-type reading (`MovesU/BridgeD9a_trueTypeDef.lean`'s
`bridgeTrueType` at `MovesU/BridgeZp.lean`'s `bridgeZfType`) — corpus
modules, not value-side ones, so the value-side graph stays acyclic.
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.MovesU.BridgeD9a_trueTypeDef
import LeanUrat.MovesU.BridgeZp
import LeanUrat.OM.NewtonPolygon
import LeanUrat.MovesX.XF7
import LeanUrat.Scaffold.ValueSide.KCount

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

/-!
**PROVENANCE (unit T4a; BP_IV §1.1 `DrainageImports` docstring + §2 T-table
row T4a, sources O4T §3.1 and LIT-8c).**
Signature exactly as consumed by the §1.1 displayed statements
(`DrainageImports.ceil/.tail`, `canonicalOrderLEOne_ceil`): `discV p n N f : ℕ`
with `f : Box p n N`, all of `p n N` explicit.  Mechanism (blueprint row T4a):
the discriminant of the level-N polynomial `Box.toPoly f` — Mathlib's
`Polynomial.discr`, the sign-adjusted Sylvester determinant, which for the
monic `Box.toPoly f` is the standard discriminant `disc f` of O4T §2's
conventions up to the unit sign (−1)^{n(n−1)/2} (LIT-8c: disc = ±Res(f, f′)
for monic f); a unit factor is invisible to the valuation — then the
TRUNCATED valuation `zmodVal` (unit K0a, `ValueSide/KCount.lean`) in
`ZMod (p^N)`, with the truncation-top convention v(0) = N (the level-N
reading of v_p(0) = ∞: a vanishing truncated discriminant reads
"v_p(disc) ≥ N", exactly the T4/T5 tail-event convention `{discV ≥ N}`).
-/

/-- T4a: the truncated discriminant valuation of the level-N box polynomial —
`v_p(disc(Box.toPoly f))` read in `ZMod (p^N)` via `zmodVal` (so capped at N,
with `discV = N` when the truncated discriminant vanishes mod p^N).  The
quantity of O4T §3.1's three imports: CEIL bounds the read length by
`discV + 1` (field `DrainageImports.ceil`, HARD unit T7), I-TAIL counts
`{m ≤ discV}` (field `DrainageImports.tail`, HARD unit T8). -/
noncomputable def discV (p n N : ℕ) [Fact p.Prime] (f : Box p n N) : ℕ :=
  zmodVal (p := p) (M := N) (Polynomial.discr (Box.toPoly f))

/-! ### T4a spec lemmas (definitional pins, the K0a-style spec layer) -/

/-- Definitional pin: `discV` is the K0 truncated valuation of the Mathlib
discriminant of the box polynomial. -/
theorem discV_def {p n N : ℕ} [Fact p.Prime] (f : Box p n N) :
    discV p n N f = zmodVal (Polynomial.discr (Box.toPoly f)) := rfl

/-- The truncation cap: `discV ≤ N` (so `¬(discV + 1 ≤ N)` forces
`discV = N` — the inclusion shape unit T4 extracts from CEIL). -/
theorem discV_le {p n N : ℕ} [Fact p.Prime] (f : Box p n N) :
    discV p n N f ≤ N :=
  zmodVal_le _

/-- The K0b divisibility bridge, specialized: for `k ≤ N`, the truncated
discriminant valuation is `≥ k` iff `p^k` divides the truncated discriminant
in `ZMod (p^N)` (the reading T8's resultant-divisibility count consumes). -/
theorem le_discV_iff {p n N k : ℕ} [Fact p.Prime] (hk : k ≤ N)
    (f : Box p n N) :
    k ≤ discV p n N f ↔
      (p : ZMod (p ^ N)) ^ k ∣ Polynomial.discr (Box.toPoly f) :=
  le_zmodVal_iff hk _

/-- The truncation top is exact: `discV` reaches `N` precisely on the
vanishing truncated discriminant (v(0) = N convention made explicit). -/
theorem le_discV_iff_discr_eq_zero {p n N : ℕ} [Fact p.Prime]
    (f : Box p n N) :
    N ≤ discV p n N f ↔ Polynomial.discr (Box.toPoly f) = 0 := by
  have hp0 : (p : ZMod (p ^ N)) ^ N = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [le_discV_iff le_rfl f, hp0, zero_dvd_iff]

/-!
**PROVENANCE (unit T4; BP_IV §1.1 `DrainageImports` display + §2 T-table row T4,
source O4T §3.4 N3-ENV step 1).**
Structure + docstring transcribed VERBATIM from `lean/blueprints/BP_IV.md` §1.1.
The fields `ceil`/`tail` are [M]-hypothesis ROWS (named structure rows, never
axioms): their discharge for the concrete classifier is the queued wave-4 HARD
units T7/T8.  Mechanism of `undec_subset_tail` (blueprint row T4): set inclusion
from the ceiling inequality — CEIL contraposed against the truncation cap
`discV_le`.

**FLAGGED FOR REVIEW — `tailC` is a NEW supporting definition of this unit.**
The §1.1 display consumes `tailC n` but the blueprint assigns it to no unit;
without it the verbatim `tail` row cannot compile, so unit T4 supplies it here
(definition-change authority applies; T5 and T8 are its only planned consumers).
Value justification (M05 Lemma C, Lean count form `MovesX.XF7.tailCountBound`,
whose constant is (n−1); wild shift `p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} ≤ n²` for
n ≥ 2, using `p^{v_p(n)} ≤ n` and `n/(n−1) ≤ 2`): row `tail`'s discharge target
needs `tailC n ≥ (n−1)·p^{n·v_p(n)/(n−1)}` uniformly in the prime p, and
`(n−1)·n²` dominates this for every p at n ≥ 2.
-/

/-- The I-TAIL constant of the `DrainageImports.tail` row — supporting
definition of unit T4 (see the provenance note: NEW, flagged; sized so that
`(n−1)·n² ≥ (n−1)·p^{n·v_p(n)/(n−1)}` for every prime p at n ≥ 2, the margin
T8's discharge needs). -/
noncomputable def tailC (n : ℕ) : ℝ := (n - 1 : ℝ) * (n : ℝ) ^ 2

/-- The two EXTERNAL analytic imports of Step 13, as one displayed row structure
    (I-TAIL = the discriminant tail bound, M05 Lemma C's counting form; CEIL = the
    Theorem-N3 read ceiling L(f) ≤ v_p(disc f) + 1 at 2 ≤ n ≤ 3).  `discV` is the
    level-N truncated discriminant valuation (a definition of this file, unit T4a).
    CEIL is the movement's queued HARD unit T7; until it lands the structure is a
    named row, exactly O4T's honest conditionality shape. -/
structure DrainageImports (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p) : Prop where
  n_lower : 2 ≤ n
  n_upper : n ≤ 3
  ceil : ∀ N (f : Box p n N), discV p n N f + 1 ≤ N → X.canonical N f ≠ none
  tail : ∀ N m : ℕ, (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
      ≤ tailC n * (p : ℝ) ^ (n * N) * (p : ℝ) ^ (-(m : ℝ) / (2 * (n - 1)))

/-- T4 (N3-ENV step 1): CEIL contraposed — every undecided level-N class lies in
the deep-discriminant tail `{discV ≥ N}` (the inclusion `Undec(N) ⊆ {discV ≥ N}`
in pointwise form, exactly what T5's subtype-injection card count consumes). -/
theorem undec_subset_tail {n p : ℕ} [Fact p.Prime] {X : ClassifierSpec n p}
    (hI : DrainageImports n p X) (N : ℕ) (f : Box p n N)
    (hf : X.canonical N f = none) : N ≤ discV p n N f := by
  by_contra hlt
  exact hI.ceil N f (by omega) hf

/-!
**PROVENANCE (unit T6; BP_IV §1.1 display + §2 T-table row T6, source O4T §3.4
N3-ENV).**
Statement transcribed VERBATIM from `lean/blueprints/BP_IV.md` §1.1.
Mechanism (blueprint row T6): T5's exponential-decay bound → 0, fed to T3
(`env_tendsto_zero_of_majorant`) with the identity reparametrization.  The
N3-ENV step-2 bound (T5's shape, at tail depth m := N) is derived inline from
unit T4's `undec_subset_tail` injection + the `DrainageImports.tail` row, so
this unit stays green independently of T5's final displayed form.  Exactly the
shape of the corpus row `BridgeKernels.env_tendsto` (the delivery seam of
Step 13); the n = 2 OM-model gate `OM.SeriesAssembly.hExhaust_n2` is NOT a
discharge of this row (different model — the D19 agreement seam; fence
recorded in BP_IV §1.1).
-/

/-- T6 (N3-ENV assembled): the scoped imports force drainage. -/
theorem env_tendsto_zero_of_imports {n p : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} (hI : DrainageImports n p X) :
    Tendsto X.env atTop (nhds 0) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hc : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hI.n_lower
    linarith
  -- N3-ENV step 2 (T5's bound, inline at m := N): Undec(N) ↪ {N ≤ discV} (T4),
  -- then the I-TAIL row, then divide by the box normalizer p^{nN}.
  have hle : ∀ N, X.env N ≤
      tailC n * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1))) := by
    intro N
    have hcard : (X.undec N : ℝ) ≤
        (Nat.card {f : Box p n N // N ≤ discV p n N f} : ℝ) := by
      have hinj : X.undec N ≤ Nat.card {f : Box p n N // N ≤ discV p n N f} := by
        unfold ClassifierSpec.undec
        exact Nat.card_le_card_of_injective
          (fun f => (⟨f.1, undec_subset_tail hI N f.1 f.2⟩ :
            {f : Box p n N // N ≤ discV p n N f}))
          (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
      exact_mod_cast hinj
    have hpow : (0 : ℝ) < (p : ℝ) ^ (n * N) := by positivity
    unfold ClassifierSpec.env
    rw [div_le_iff₀ hpow]
    calc (X.undec N : ℝ)
        ≤ (Nat.card {f : Box p n N // N ≤ discV p n N f} : ℝ) := hcard
      _ ≤ tailC n * (p : ℝ) ^ (n * N)
            * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1))) := hI.tail N N
      _ = tailC n * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1)))
            * (p : ℝ) ^ (n * N) := by ring
  -- the majorant vanishes: base p > 1 at an exponent falling to −∞.
  have hB : Tendsto
      (fun N : ℕ => tailC n * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1))))
      atTop (nhds 0) := by
    have h2 : Tendsto (fun N : ℕ => -(N : ℝ) / (2 * ((n : ℝ) - 1)))
        atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_div_const hc)
      simpa [Function.comp_def, neg_div] using this
    have h3 := (tendsto_rpow_atBot_of_base_gt_one _ hp1).comp h2
    simpa using h3.const_mul (tailC n)
  -- T3 with the identity reparametrization forces drainage.
  have h0 : ∀ N, 0 ≤ X.env N := fun N => by
    unfold ClassifierSpec.env; positivity
  exact env_tendsto_zero_of_majorant (ClassifierSpec.env_antitone X) h0
    tendsto_id hle hB

/-!
**PROVENANCE (unit T5; BP_IV §2 T-table row T5, source O4T §3.4 N3-ENV
step 2; LANDED at REVISION 3, mop-up).**  The blueprint displays no §1.1 code
block for T5 — only the T-table row "`env_le_tail`: env N ≤
tailC·p^(−(N−1)/(2(n−1))) | T4's inclusion + card mono + the `tail` field".
The T5→T6 chain had been collapsed by the T6 prover (T6's proof derives the
m = N bound inline, its `hle`, so T6 is green independently of T5); the
standalone displayed T5 row is landed here, closing the unit: the inline
m = N chain re-run standalone, then the exponent relaxed −N → −(N−1)
(base p > 1), which is exactly the displayed T5 form. -/

/-- T5 (`env_le_tail`, N3-ENV step 2 as the standalone displayed bound): the
undecided envelope decays exponentially,
`env N ≤ tailC n · p^(−(N−1)/(2(n−1)))` — unit T4's tail inclusion
`Undec(N) ⊆ {N ≤ discV}`, the I-TAIL row at depth m = N, and the −N → −(N−1)
exponent relaxation. -/
theorem env_le_tail {n p : ℕ} [Fact p.Prime] {X : ClassifierSpec n p}
    (hI : DrainageImports n p X) (N : ℕ) :
    X.env N ≤ tailC n * (p : ℝ) ^ (-((N : ℝ) - 1) / (2 * ((n : ℝ) - 1))) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hI.n_lower
  have hc : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  -- the m = N bound (T4's injection + the I-TAIL row; T6's inline chain)
  have hle : X.env N ≤ tailC n * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1))) := by
    have hcard : (X.undec N : ℝ) ≤
        (Nat.card {f : Box p n N // N ≤ discV p n N f} : ℝ) := by
      have hinj : X.undec N ≤ Nat.card {f : Box p n N // N ≤ discV p n N f} := by
        unfold ClassifierSpec.undec
        exact Nat.card_le_card_of_injective
          (fun f => (⟨f.1, undec_subset_tail hI N f.1 f.2⟩ :
            {f : Box p n N // N ≤ discV p n N f}))
          (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
      exact_mod_cast hinj
    have hpow : (0 : ℝ) < (p : ℝ) ^ (n * N) := by positivity
    unfold ClassifierSpec.env
    rw [div_le_iff₀ hpow]
    calc (X.undec N : ℝ)
        ≤ (Nat.card {f : Box p n N // N ≤ discV p n N f} : ℝ) := hcard
      _ ≤ tailC n * (p : ℝ) ^ (n * N)
            * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1))) := hI.tail N N
      _ = tailC n * (p : ℝ) ^ (-(N : ℝ) / (2 * ((n : ℝ) - 1)))
            * (p : ℝ) ^ (n * N) := by ring
  -- exponent relaxation −N ≤ −(N−1) at base p > 1
  have htail0 : (0 : ℝ) ≤ tailC n := by
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    exact mul_nonneg hn1 (by positivity)
  have hexp : -(N : ℝ) / (2 * ((n : ℝ) - 1))
      ≤ -((N : ℝ) - 1) / (2 * ((n : ℝ) - 1)) := by
    have h1 : -(N : ℝ) ≤ -((N : ℝ) - 1) := by linarith
    calc -(N : ℝ) / (2 * ((n : ℝ) - 1))
        = -(N : ℝ) * (2 * ((n : ℝ) - 1))⁻¹ := div_eq_mul_inv _ _
      _ ≤ -((N : ℝ) - 1) * (2 * ((n : ℝ) - 1))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hc.le)
      _ = -((N : ℝ) - 1) / (2 * ((n : ℝ) - 1)) := (div_eq_mul_inv _ _).symm
  exact hle.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1.le hexp) htail0)

/-!
**PROVENANCE (unit T4b; BP_IV §1.1 T7-interface block — "`canonicalOrderLEOne`
is the concrete classifier definition of unit T4b"; §4 wave-2 chain
T4a → T4b → T4).**  Signature transcribed VERBATIM from §1.1 (the
`noncomputable def` before `canonicalOrderLEOne_ceil`); the blueprint fixes no
body, so the body below is this unit's construction, flagged for review per
the trust-boundary rule (definitions are where errors hide).

The body is the O4T §3.2 PINNED WALK (`O4T_phaseB_verifybrief_rev4.md` §3.2,
"this definition IS the object of N3"), transcribed clause by clause in the
sub-namespace `OrderLEOne`:

* digit/valuation reads: `digitAt` (base-p digit of a `ZMod (p^M)` value) and
  `cVal` (the K0a truncated valuation `zmodVal` of the recentered coefficient
  `g_i`, `g = F(x + c)`) — §3.2's `y_i`, with `y_i ≥ k` read as "unresolved at
  scan level k" (truncation top v(0) = N = the T4a convention);
* the resolved hull: `resolvedIdx/resolvedSet/x0` (§3.2's resolved indices,
  `H_res` support, and least resolved index x₀), hull heights/sides by CORPUS
  REUSE from `OM/NewtonPolygon.lean` (`npHeight`, `npSides`; brief slope
  s = −`Side.slope`, since the corpus slope convention is (v₁−v₀)/Δx ≤ 0 on
  descending sides);
* `Certifies` (§3.2 (C1)+(C2), byte-faithful: (C1) is transcribed although the
  rev-4 record note proves it REDUNDANT — pinned policy kept byte-stable);
* `processResidual` (§3.2's residual factor read: simple irreducible factor of
  degree d′ ↦ (1, d′); repeated ROOT of multiplicity m′ ≥ 2 ↦ recursion) and
  `processSide` (side of slope h/e in lowest terms: d = 1 ↦ (e, 1); e = 1,
  d ≥ 2 ↦ the on-line digit residual `R(z) = Σ r_j z^j`);
* `clusterWalk` (the cluster step `(c, m, λ_prev)`; recursion shift
  `c + z₀·p^h`, λ' := h; FUEL-guarded — λ_prev strictly increases and a
  certify level needs λ_prev < k ≤ N, so fuel N suffices; fuel exhaustion
  emits ⊥, never a wrong verdict);
* `fbar/rawLEOne/rawType` (§3.2 Step 0: factor f̄ mod p; simple irreducible
  factors ↦ (1, d), repeated residue roots open clusters at λ_prev = 0), with
  the verdict packaged into `SplittingType n` behind the degree audit
  Σ eᵢfᵢ = n (a guarded dite: T7-side soundness will show the guard never
  fails on emitted verdicts);
* OUT-OF-SCOPE TOTALIZATIONS (each emits ⊥, the walk's honest refusal, never
  a verdict): repeated residual factors of degree ≥ 2 (impossible at n ≤ 3 —
  §3.2 "at n ≤ 3 repeated factors are linear"), sides with e ≥ 2 and d ≥ 2
  (need e·d ≥ 4 > n), and N = 0 (the single-class box, the
  `bridgeCanonical_level0` convention).

**Stabilization closure (`decideAt/stabVerdict`) — recorded design decision.**
`ClassifierSpec.canonical_stable` is a STRUCTURE FIELD, so the definition must
carry its stability proof.  The §3.2 walk's verdict at level N reads only
digits below its certify level, so it agrees with the verdict read at the
least deciding level of the projections — decision stability (TREE-N) says
raw = stabilized.  We DEFINE `canonical N f` as the raw walk verdict at the
LEAST level N₀ ≤ N at which the projected class decides
(`Nat.find`-first-decision closure): stability then holds BY CONSTRUCTION
(`stabVerdict_stable`, via `boxProj` composition), and the closure is
mathematically inert — proving "stabilized = raw at every level" is exactly
the TREE-N decision-stability lemma, a T7-side obligation, NOT assumed here.

**`trueType` and `baseSection` (fields the O4T walk does not fix).**
`trueType := bridgeTrueType n p bridgeZfType` — the corpus's genuine ℤ_p
factorization-type reading (IB-D9a at IB-E11's concrete `bridgeZfType`; "the
σ every monic ℤ_p lift reads, if one exists").  `VPSound` for this instance
is a GENUINE OPEN CLAIM (= N3 soundness), exactly as the interface demands —
NOT baked in (`trueType := canonical` would have made it `rfl`-true; refused).
`baseSection := .teichmuller` — the O3 ledger pin; the order-≤1 walk only
reads leading digits at exact valuations (graded-piece data, section-
INDEPENDENT), so the pin costs nothing and keeps the ledger seam open.
-/

namespace OrderLEOne

-- Classical decidability for the walk's dites/`Nat.find` (the corpus
-- `bridgeCanonical`/`bridgeTrueType` precedent); style linter off for it.
set_option linter.style.openClassical false
open scoped Classical

open Polynomial

section Walk

variable {p n N : ℕ} [Fact p.Prime]

/-- §3.2 digit read: the base-p digit of (the standard representative of)
`x : ZMod (p^M)` at level `j` — a function of the digits of `x` below level
`j + 1`, so a class read. -/
noncomputable def digitAt {M : ℕ} (x : ZMod (p ^ M)) (j : ℕ) : ZMod p :=
  (((x.val / p ^ j) % p : ℕ) : ZMod p)

/-- The recentered level-N coefficient `g_i` of the cluster step:
`g := F(x + c)`, `F = Box.toPoly f` (§3.2 "put g := f(x + c)"). -/
noncomputable def shiftedCoeff (f : Box p n N) (c : ZMod (p ^ N)) (i : ℕ) :
    ZMod (p ^ N) :=
  ((Box.toPoly f).comp (X + C c)).coeff i

/-- §3.2's `y_i`: the truncated valuation of the recentered coefficient
(K0a `zmodVal`; `y_i < k` = "resolved at scan level k", exact below the
truncation; `y_i ≥ k` = "unresolved", knowledge `v ≥ k`). -/
noncomputable def cVal (f : Box p n N) (c : ZMod (p ^ N)) (i : ℕ) : ℕ :=
  zmodVal (shiftedCoeff f c i)

/-- The resolved index set at scan level `k` (§3.2: `i` resolved iff
`y_i < k`; `i = n` always resolved — `g` is monic). -/
noncomputable def resolvedIdx (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) :
    Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i => cVal f c i < k ∨ i = n)

theorem resolvedIdx_nonempty (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) :
    (resolvedIdx f c k).Nonempty :=
  ⟨n, by simp [resolvedIdx]⟩

/-- The resolved support dots `(i, y_i)` — the point set whose lower hull is
§3.2's `H_res`. -/
noncomputable def resolvedSet (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) :
    Finset (ℕ × ℕ) :=
  (resolvedIdx f c k).image (fun i => (i, cVal f c i))

theorem resolvedSet_nonempty (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) :
    (resolvedSet f c k).Nonempty :=
  (resolvedIdx_nonempty f c k).image _

/-- §3.2's `x₀`: the least resolved index. -/
noncomputable def x0 (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) : ℕ :=
  (resolvedIdx f c k).min' (resolvedIdx_nonempty f c k)

/-- §3.2 certification at scan level `k` of the cluster step `(c, ·, λ_prev)`:
(C1) every unresolved `i > x₀` sits strictly above the resolved hull
(transcribed byte-faithfully although rev-4 records it as redundant), and
(C2) `x₀ = 0`, or `x₀ = 1` with `k > y₁ + s_r` and `k > y₁ + λ_prev`
(`s_r` = the brief slope of the FIRST side of `H_res` = −slope of the head of
the corpus side list).  `lam < k ≤ N` bounds the scan window (verdict-at-N
semantics: all consumption ≤ N). -/
def Certifies (f : Box p n N) (c : ZMod (p ^ N)) (lam k : ℕ) : Prop :=
  lam < k ∧ k ≤ N ∧
    (∀ i < n, ¬ (cVal f c i < k ∨ i = n) → x0 f c k < i →
      OM.NewtonPolygon.npHeight (resolvedSet f c k)
        (resolvedSet_nonempty f c k) (i : ℚ) < (k : ℚ)) ∧
    (x0 f c k = 0 ∨
      (x0 f c k = 1 ∧
        ∃ s₀, (OM.NewtonPolygon.npSides (resolvedSet f c k)
            (resolvedSet_nonempty f c k)).head? = some s₀ ∧
          (cVal f c 1 : ℚ) + (- s₀.slope) < (k : ℚ) ∧
          cVal f c 1 + lam < k))

/-- §3.2 residual processing, shared by Step 0 (on `f̄`) and the side reads
(on `R`): each SIMPLE irreducible factor of degree `d′` certifies `(1, d′)`;
each repeated ROOT `z₀` of multiplicity `m′ ≥ 2` recurses through `rec z₀ m′`;
a repeated factor of degree ≥ 2 (impossible at n ≤ 3) refuses with `none`. -/
noncomputable def processResidual (R : Polynomial (ZMod p))
    (rec : ZMod p → ℕ → Option (Multiset (ℕ × ℕ))) :
    Option (Multiset (ℕ × ℕ)) :=
  ((UniqueFactorizationMonoid.normalizedFactors R).toFinset.toList.mapM
    (fun ψ =>
      if (UniqueFactorizationMonoid.normalizedFactors R).count ψ = 1 then
        some ({(1, ψ.natDegree)} : Multiset (ℕ × ℕ))
      else if ψ.natDegree = 1 then
        rec (- ψ.coeff 0)
          ((UniqueFactorizationMonoid.normalizedFactors R).count ψ)
      else none)).map List.sum

/-- §3.2 side processing (brief slope `s = −Side.slope = h/e` in lowest terms,
length `ℓ = e·d`): `d = 1` (i.e. `ℓ = e`) certifies `(e, 1)`; `e = 1`, `d ≥ 2`
reads the on-line digit residual `R(z) = Σ_j r_j z^j` (`r_j` = the digit of
`g_{i₁+j}` at level `y₁ − j·h` when on the side line, else 0) and processes
it, recursing at slope datum `h` through `rec z m′ h`; the remaining case
(`e ≥ 2` with `d ≥ 2`, needing `e·d ≥ 4 > n`) refuses with `none`. -/
noncomputable def processSide (f : Box p n N) (c : ZMod (p ^ N))
    (s : OM.NewtonPolygon.Side)
    (rec : ZMod p → ℕ → ℕ → Option (Multiset (ℕ × ℕ))) :
    Option (Multiset (ℕ × ℕ)) :=
  if (- s.slope).den = s.length then
    some ({((- s.slope).den, 1)} : Multiset (ℕ × ℕ))
  else if (- s.slope).den = 1 ∧ 2 ≤ s.length then
    processResidual
      (∑ j ∈ Finset.range (s.length + 1),
        C (if (cVal f c (s.i₀ + j) : ℤ) = (s.v₀ : ℤ) - (j : ℤ) * (- s.slope).num
           then digitAt (shiftedCoeff f c (s.i₀ + j))
             ((s.v₀ : ℤ) - (j : ℤ) * (- s.slope).num).toNat
           else 0) * X ^ j)
      (fun z m => rec z m (- s.slope).num.toNat)
  else none

/-- §3.2 cluster step `(c, m, λ_prev)` (the multiplicity `_m` is the (I1)
invariant datum — carried, never read).  Scan for the FIRST certify level
`k ∈ (λ_prev, N]` (`Nat.find`); on certification process the sides of `H_res`
of brief slope `> λ_prev`, prepending the left-edge-shortcut factor `(1,1)`
when `x₀ = 1` (§3.2 (C2)); a repeated residual root `z₀` on a slope-`h` side
recurses at `(c + z₀·p^h, m′, λ_prev := h)`.  Fuel-guarded recursion: λ_prev
strictly increases and certification needs `λ_prev < k ≤ N`, so fuel `N`
suffices; fuel exhaustion refuses with `none`. -/
noncomputable def clusterWalk (f : Box p n N) :
    ℕ → ZMod (p ^ N) → ℕ → ℕ → Option (Multiset (ℕ × ℕ))
  | 0, _, _, _ => none
  | fuel + 1, c, _m, lam =>
      if h : ∃ k, Certifies f c lam k then
        (((OM.NewtonPolygon.npSides (resolvedSet f c (Nat.find h))
              (resolvedSet_nonempty f c (Nat.find h))).filter
            (fun s => decide ((lam : ℚ) < - s.slope))).mapM
          (fun s => processSide f c s
            (fun z m' hh =>
              clusterWalk f fuel
                (c + (z.val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ hh)
                m' hh))).map
        (fun l =>
          (if x0 f c (Nat.find h) = 1 then ({(1, 1)} : Multiset (ℕ × ℕ)) else 0)
            + l.sum)
      else none

/-- §3.2 Step 0's input: the residue polynomial `f̄ ∈ F_p[x]` of the box class
(level-1 read; monic of degree n). -/
noncomputable def fbar (hN : 0 < N) (f : Box p n N) : Polynomial (ZMod p) :=
  (Box.toPoly f).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))

/-- The raw §3.2 walk verdict at truncation level N (Step 0 + clusters):
`some` of the certified factor multiset if the walk completes with all
consumption ≤ N, else `none` (including at the unguarded level N = 0). -/
noncomputable def rawLEOne (f : Box p n N) : Option (Multiset (ℕ × ℕ)) :=
  if hN : 0 < N then
    processResidual (fbar hN f)
      (fun z m => clusterWalk f N ((z.val : ZMod (p ^ N))) m 0)
  else none

/-- The raw walk verdict packaged as a `SplittingType n`, behind the degree
audit `Σ eᵢfᵢ = n` with entries ≥ 1 (a guarded dite; T7-side soundness shows
the guard never fails on emitted verdicts — here it is the honest fence). -/
noncomputable def rawType (f : Box p n N) : Option (SplittingType n) :=
  (rawLEOne f).bind (fun S =>
    if h : (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
        (S.map fun x => x.1 * x.2).sum = n then
      some ⟨S, h⟩
    else none)

end Walk

section Stab

variable {p n : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Level reductions compose (the `ZMod.castHom_comp` law, box form). -/
theorem boxProj_boxProj {N₀ N N' : ℕ} (h₀ : N₀ ≤ N) (h : N ≤ N')
    (f : Box p n N') :
    boxProj p n h₀ (boxProj p n h f) = boxProj p n (h₀.trans h) f := by
  funext i
  exact RingHom.congr_fun
    (ZMod.castHom_comp (pow_dvd_pow p h₀) (pow_dvd_pow p h)) (f i)

/-- The raw verdict of the level-N₀ projection, seen from horizon N
(`none` beyond the horizon). -/
noncomputable def decideAt (N : ℕ) (f : Box p n N) (N₀ : ℕ) :
    Option (SplittingType n) :=
  if h : N₀ ≤ N then rawType (boxProj p n h f) else none

/-- Horizon extension: below the smaller horizon the two readings agree
(projections compose). -/
theorem decideAt_agree {N N' : ℕ} (hNN' : N ≤ N') (f : Box p n N') {N₀ : ℕ}
    (hN₀ : N₀ ≤ N) :
    decideAt N (boxProj p n hNN' f) N₀ = decideAt N' f N₀ := by
  unfold decideAt
  rw [dif_pos hN₀, dif_pos (hN₀.trans hNN'), boxProj_boxProj]

/-- The first-decision closure of the raw walk verdict: the verdict at the
LEAST deciding level of the projections (see the unit-T4b provenance note —
by TREE-N decision stability this closure is mathematically inert; it makes
`canonical_stable` hold by construction). -/
noncomputable def stabVerdict (N : ℕ) (f : Box p n N) :
    Option (SplittingType n) :=
  if h : ∃ N₀, decideAt N f N₀ ≠ none then decideAt N f (Nat.find h)
  else none

/-- Stability of the first-decision closure: a verdict at level N persists,
verbatim, to every level N' ≥ N — the `ClassifierSpec.canonical_stable` field
of unit T4b. -/
theorem stabVerdict_stable {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
    (σ : SplittingType n)
    (hs : stabVerdict N (boxProj p n h f) = some σ) :
    stabVerdict N' f = some σ := by
  unfold stabVerdict at hs
  by_cases hex : ∃ N₀, decideAt N (boxProj p n h f) N₀ ≠ none
  · rw [dif_pos hex] at hs
    -- the least deciding level sits below the smaller horizon
    have hkle : Nat.find hex ≤ N := by
      by_contra hgt
      apply Nat.find_spec hex
      unfold decideAt
      exact dif_neg hgt
    have htrans : decideAt N' f (Nat.find hex) = some σ := by
      rw [← decideAt_agree h f hkle]; exact hs
    have hex' : ∃ N₀, decideAt N' f N₀ ≠ none :=
      ⟨Nat.find hex, by rw [htrans]; exact Option.some_ne_none σ⟩
    have hfind : Nat.find hex' = Nat.find hex := by
      refine le_antisymm
        (Nat.find_le (by rw [htrans]; exact Option.some_ne_none σ)) ?_
      refine (Nat.le_find_iff hex' (Nat.find hex)).mpr (fun j hj => ?_)
      have hjN : j ≤ N := (Nat.le_of_lt hj).trans hkle
      simp only [ne_eq, not_not]
      rw [← decideAt_agree h f hjN]
      have hmin := Nat.find_min hex hj
      simpa [ne_eq, not_not] using hmin
    unfold stabVerdict
    rw [dif_pos hex', hfind]
    exact htrans
  · rw [dif_neg hex] at hs
    simp at hs

end Stab

/-!
**PROVENANCE (unit T7, PARTIAL; BP_IV §1.1 T7-interface block + §2 T-table
row T7, sources O4T §§3.2–3.4 and the rev-4 dispositions).**
The unit's target statement `canonicalOrderLEOne_ceil` is transcribed VERBATIM
from `lean/blueprints/BP_IV.md` §1.1 (below, after the T4b pins).  Mechanism
(blueprint row T7 = Theorem N3 (CEIL)): every cluster step certifies at a
level `k ≤ v_p(disc f) + 1` — case (a) `b₁ = b₂` at `k = y(0) + 1`, case (b)
`b₁ > b₂` by the left-edge shortcut at `k = y(1) + ⌊b₂⌋ + 1`, both bounded
through Fact D (`v = 2·Σ_{i<j} δ_ij`) with the (I1) "> 0" criterion per rev 4
(the rev-3 `≥ 1` form is FALSE — the `x² − p` refutation); Krasner via M05
Lemma D underwrites the §4 seam, NOT this clause.  So the raw walk completes
within horizon `N ≥ discV + 1` and its verdict passes the degree audit
(step 0 partitions n; each cluster partitions its m by (I1) + SIDE + REC).

**Unit status: PARTIAL.**  Proved sorry-free here, reducing the verbatim T7
statement to ONE open per-cluster core:
* the closure-reduction layer — the first-decision closure decides whenever
  the raw walk decides (`stabVerdict_ne_none_of_raw` via
  `boxProj_self`/`decideAt_self`);
* the Step-0 assembly layer — `rawType_ne_none_of_clusterWalk` via the
  engine audit `processResidual_audit` (the repeated-deg-≥2 refusal is
  VACUOUS at degree ≤ 3; simple factors contribute `(1, deg ψ)`; the
  normalized-factorization degree partition `Σ_ψ count·deg = n` closes the
  audit) with supports `mapM_option_spec`, `forall₂_multiset_audit`,
  `toPoly_monic`, `toPoly_natDegree`, `fbar_monic`, `fbar_natDegree`.
The OPEN core, `clusterWalk_audit`, is the Theorem-N3 per-cluster
termination + audit chain over the true root valuations `b_j = v(α_j − c)`
in `Q̄_p`: (I1) needs Fact EXT (unique valuation extension, Galois
invariance), CERT(ii) needs Fact DES (Galois descent), SIDE needs Facts
SF/HEN/EF/HRG, RES needs Fact GRD, and the certify-level arithmetic needs
Fact D — extended-valuation root theory for `Q̄_p` that neither the corpus
nor this Mathlib pin carries; a coefficients-only reproof would be a NEW
mathematical development outside the source of record.  It stays an honest
`sorry` with the blocking reason inline (BP_IV row T7: "a dedicated
formalization campaign").  No declaration consumes the sorried lemma except
the T7 chain itself; `DrainageImports.ceil` stays a named row — NO discharge
of the row is claimed until the core lands.
-/

section T7

variable {p n : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- The reflexive level reduction is the identity (`ZMod.cast_id` pointwise;
proof-irrelevant in the divisibility witness). -/
theorem boxProj_self {N : ℕ} (f : Box p n N) :
    boxProj p n (le_refl N) f = f := by
  funext i
  show ZMod.castHom _ (ZMod (p ^ N)) (f i) = f i
  rw [ZMod.castHom_apply, ZMod.cast_id]

/-- `decideAt` at its own horizon reads the raw walk verdict itself. -/
theorem decideAt_self {N : ℕ} (f : Box p n N) :
    decideAt N f N = rawType f := by
  unfold decideAt
  rw [dif_pos (le_refl N), boxProj_self]

/-- Closure reduction (the sorry-free half of T7): if the raw §3.2 walk
verdict exists at level N, the first-decision closure also decides at N —
the horizon N is itself a deciding level, so the `Nat.find` level exists and
decides by `Nat.find_spec`.  This moves the CEIL obligation from
`stabVerdict` (= `canonical`, by the T4b pin) to the raw walk. -/
theorem stabVerdict_ne_none_of_raw {N : ℕ} (f : Box p n N)
    (h : rawType f ≠ none) : stabVerdict N f ≠ none := by
  have hd : decideAt N f N ≠ none := by rw [decideAt_self]; exact h
  have hex : ∃ N₀, decideAt N f N₀ ≠ none := ⟨N, hd⟩
  unfold stabVerdict
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- `Option`-monad `mapM` with a per-element specification: if every list
element has a `some` image satisfying `P`, the whole `mapM` returns `some`
of a `Forall₂ P`-related list (supporting lemma of unit T7's step-0
assembly). -/
theorem mapM_option_spec {α β : Type*} {F : α → Option β} {P : α → β → Prop}
    {l : List α} (h : ∀ a ∈ l, ∃ b, F a = some b ∧ P a b) :
    ∃ L, l.mapM F = some L ∧ List.Forall₂ P l L := by
  induction l with
  | nil => exact ⟨[], by simp, List.Forall₂.nil⟩
  | cons a as ih =>
      obtain ⟨b, hFa, hPa⟩ := h a (by simp)
      obtain ⟨L, hL, hforall⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨b :: L, by rw [List.mapM_cons, hFa, hL]; rfl,
        List.Forall₂.cons hPa hforall⟩

/-- Aggregating a `Forall₂` audit over a list of factor multisets: entries
stay ≥ 1 and the weights `e·f` add up blockwise (supporting lemma of unit
T7's step-0 assembly). -/
theorem forall₂_multiset_audit {α : Type*} {g : α → ℕ}
    {l : List α} {L : List (Multiset (ℕ × ℕ))}
    (h : List.Forall₂ (fun a S => (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = g a) l L) :
    (∀ x ∈ L.sum, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      ((L.sum).map fun x => x.1 * x.2).sum = (l.map g).sum := by
  induction h with
  | nil => simp
  | cons ha hl ih =>
      constructor
      · intro x hx
        rw [List.sum_cons] at hx
        rcases Multiset.mem_add.mp hx with h1 | h2
        · exact ha.1 x h1
        · exact ih.1 x h2
      · rw [List.sum_cons, List.map_cons, List.sum_cons, Multiset.map_add,
          Multiset.sum_add, ha.2, ih.2]

omit [Fact p.Prime] in
/-- The box polynomial is monic (the §3.2 Step-0 input's leading audit). -/
theorem toPoly_monic {N : ℕ} (f : Box p n N) : (Box.toPoly f).Monic := by
  unfold Box.toPoly
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
    (fun i _ => lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact WithBot.coe_lt_coe.mpr i.2))

/-- The box polynomial has exact degree n (N ≥ 1 keeps `ZMod (p^N)`
nontrivial). -/
theorem toPoly_natDegree {N : ℕ} (hN : 0 < N) (f : Box p n N) :
    (Box.toPoly f).natDegree = n := by
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.one_lt⟩
  unfold Box.toPoly
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
    (fun i _ => lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact WithBot.coe_lt_coe.mpr i.2))

/-- The Step-0 residue polynomial `f̄` is monic. -/
theorem fbar_monic {N : ℕ} (hN : 0 < N) (f : Box p n N) : (fbar hN f).Monic :=
  (toPoly_monic f).map _

/-- The Step-0 residue polynomial `f̄` is monic of degree n — the degree
that Step 0's certified factors and clusters partition. -/
theorem fbar_natDegree {N : ℕ} (hN : 0 < N) (f : Box p n N) :
    (fbar hN f).natDegree = n := by
  unfold fbar
  rw [(toPoly_monic f).natDegree_map, toPoly_natDegree hN f]

/-- Step-0 engine audit (sorry-free): for monic `R` of degree ≤ 3, if every
repeated LINEAR factor's recursion completes with a multiset partitioning
its multiplicity, then `processResidual R rec` completes with a multiset of
entries ≥ 1 partitioning `deg R`.  Mechanism: the repeated-deg-≥2 refusal
branch is VACUOUS at degree ≤ 3 (O4T §3.2 "at n ≤ 3 repeated factors are
linear": count·deg ≥ 4 > 3 against the normalized-factorization degree
partition `Σ_ψ count(ψ)·deg(ψ) = deg R`), and the simple-factor branch
contributes `(1, deg ψ)` exactly. -/
theorem processResidual_audit {R : Polynomial (ZMod p)} (hmonic : R.Monic)
    (hdeg3 : R.natDegree ≤ 3)
    {rec : ZMod p → ℕ → Option (Multiset (ℕ × ℕ))}
    (hrec : ∀ ψ ∈ UniqueFactorizationMonoid.normalizedFactors R,
      2 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ →
      ψ.natDegree = 1 →
      ∃ S, rec (- ψ.coeff 0)
          ((UniqueFactorizationMonoid.normalizedFactors R).count ψ) = some S ∧
        (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
        (S.map fun x => x.1 * x.2).sum
          = (UniqueFactorizationMonoid.normalizedFactors R).count ψ) :
    ∃ S, processResidual R rec = some S ∧
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = R.natDegree := by
  have hR0 : R ≠ 0 := hmonic.ne_zero
  have h0 : (0 : Polynomial (ZMod p)) ∉ UniqueFactorizationMonoid.normalizedFactors R :=
    UniqueFactorizationMonoid.zero_notMem_normalizedFactors R
  -- the degree partition Σ_ψ count(ψ)·deg(ψ) = deg R
  have hmapsum : ((UniqueFactorizationMonoid.normalizedFactors R).map
      Polynomial.natDegree).sum = R.natDegree := by
    conv_rhs => rw [← (Polynomial.normalize_eq_self_iff_monic hR0).mpr hmonic,
      ← UniqueFactorizationMonoid.prod_normalizedFactors_eq hR0]
    exact (Polynomial.natDegree_multiset_prod _ h0).symm
  have hkey : ∑ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors R).toFinset,
      (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree
      = R.natDegree := by
    rw [Finset.sum_multiset_map_count] at hmapsum
    simpa [smul_eq_mul, nsmul_eq_mul] using hmapsum
  -- per-factor branch spec for the mapM
  have hspec : ∀ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors R).toFinset.toList,
      ∃ S, (if (UniqueFactorizationMonoid.normalizedFactors R).count ψ = 1 then
          some ({(1, ψ.natDegree)} : Multiset (ℕ × ℕ))
        else if ψ.natDegree = 1 then
          rec (- ψ.coeff 0)
            ((UniqueFactorizationMonoid.normalizedFactors R).count ψ)
        else none) = some S ∧
        ((∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
          (S.map fun x => x.1 * x.2).sum
            = (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree) := by
    intro ψ hψl
    have hψ : ψ ∈ UniqueFactorizationMonoid.normalizedFactors R := by
      rw [← Multiset.mem_toFinset]
      exact Finset.mem_toList.mp hψl
    have hirr : Irreducible ψ :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψ
    have hdpos : 0 < ψ.natDegree := hirr.natDegree_pos
    have hcpos : 0 < (UniqueFactorizationMonoid.normalizedFactors R).count ψ :=
      Multiset.count_pos.mpr hψ
    by_cases hc : (UniqueFactorizationMonoid.normalizedFactors R).count ψ = 1
    · refine ⟨{(1, ψ.natDegree)}, by rw [if_pos hc], ?_, by simp [hc]⟩
      intro x hx
      rw [Multiset.mem_singleton] at hx
      subst hx
      exact ⟨le_rfl, hdpos⟩
    · have hc2 : 2 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ := by
        omega
      have hd1 : ψ.natDegree = 1 := by
        by_contra hne
        have hd2 : 2 ≤ ψ.natDegree := by omega
        have hle : (UniqueFactorizationMonoid.normalizedFactors R).count ψ
            * ψ.natDegree ≤ R.natDegree := by
          rw [← hkey]
          exact Finset.single_le_sum
            (f := fun φ => (UniqueFactorizationMonoid.normalizedFactors R).count φ
              * φ.natDegree)
            (fun i _ => Nat.zero_le _) (Multiset.mem_toFinset.mpr hψ)
        have h4 : 4 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ
            * ψ.natDegree := Nat.mul_le_mul hc2 hd2
        omega
      obtain ⟨S, hS, hS1, hS2⟩ := hrec ψ hψ hc2 hd1
      refine ⟨S, ?_, hS1, by rw [hS2, hd1, mul_one]⟩
      rw [if_neg hc, if_pos hd1]
      exact hS
  obtain ⟨L, hmapM, hforall⟩ := mapM_option_spec
    (P := fun (ψ : Polynomial (ZMod p)) (S : Multiset (ℕ × ℕ)) =>
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum
        = (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree)
    hspec
  have haudit := forall₂_multiset_audit hforall
  refine ⟨L.sum, ?_, haudit.1, ?_⟩
  · unfold processResidual
    rw [hmapM]
    rfl
  · rw [haudit.2, Finset.sum_map_toList, hkey]

/-!
### T7-core campaign, session 1 (BP_IV R3.7 row T7-core; 2026-08-01)

The Theorem-N3 per-cluster core `clusterWalk_audit` stays OPEN (the honest
`sorry` below), but its perimeter is now strictly smaller: everything in this
subsection is PROVED, and reduces the remaining content to exactly the
analytic N3 chain.  Layers landed here:

* **Certification calculus.**  The rev-4 record note "(C1) is redundant" is
  now a THEOREM (`certifies_C1_auto`, via `npHeight_lt_of_x0_le`: every valid
  supporting line of the resolved hull is `< k` on `[x₀, n]`, because its
  values at the two anchor dots `(x₀, y_{x₀})` and `(n, 0)` are `< k` and an
  affine function on an interval is bounded by its endpoint values).  Hence
  certification reduces to the (C2) gate alone: `certifies_of_x0_eq_zero`,
  and EXISTENCE of a certify level holds outright on the x₀ = 0 route
  (`exists_certifies_of_cVal_lt`: `y₀ < N` and `λ_prev < N` suffice).  The
  x₀ = 1 route (`y₀ = N`, the left-edge shortcut) is the Fact-D certify-level
  arithmetic `y₁ + max(s_r, λ_prev) < k ≤ v_p(disc f) + 1` — OPEN, in the core.
* **DIG reads.**  `digitAt_ne_zero_of_zmodVal_eq` / `digitAt_eq_zero_of_lt_zmodVal`
  — the leading digit at the exact truncated valuation is nonzero, digits
  below the valuation vanish (what the residual degree/constant-term pins of
  the side reads will consume).
* **Engine audit, `≠ 0` form.**  `processResidual_audit'` re-proves the Step-0
  engine audit from `R ≠ 0` alone (side residuals are NOT monic — their
  leading digit is an arbitrary unit; the degree partition now runs through
  the associated normalized product, unit factors carrying degree 0).
* **Side audit.**  `sideResidual` names the on-line digit residual (a
  spec-layer object; `processSide_def` pins it to the walk by `rfl`) and
  `processSide_audit` discharges the side read: every non-refusing side
  (`e = ℓ`, or `e = 1 ≤ 3` with `d = ℓ ≥ 2`) processes to a multiset
  partitioning its length, GIVEN the residual degree pin and the sub-cluster
  recursion hypothesis.
* **Step audit.**  `clusterWalk_succ` (the walk's successor equation, a `rfl`
  pin) + `clusterWalk_succ_audit`: one full cluster step completes and
  partitions `m`, GIVEN (i) a certify level exists, (ii) each processed side
  partitions its length, (iii) the side inventory
  `[x₀ = 1] + Σ_{s : slope > λ} ℓ(s) = m` at the found level.  All
  Option/monad/multiset plumbing is discharged.

What remains INSIDE the core `sorry` after this layer: (i) certification
existence on the x₀ = 1 route, (ii) the residual degree pin + the recursion
invariant transport into sub-clusters, (iii) the (I1) hull inventory at the
least certify level — the genuinely analytic Theorem-N3 chain over the true
root valuations `b_j = v(α_j − c)` (Facts EXT/DES/SF/HEN/EF/GRD/HRG/D).
-/

/-- The top coefficient read of the cluster step: `cVal` at index `n` is `0`
(`g = F(x + c)` stays monic of degree `n`; at `N = 0` the truncation cap
forces the same value). -/
theorem cVal_top {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N)) :
    cVal f c n = 0 := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · have h := zmodVal_le (shiftedCoeff f c n)
    unfold cVal
    omega
  · have hp : p.Prime := Fact.out
    haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.one_lt⟩
    have hc : shiftedCoeff f c n = 1 := by
      unfold shiftedCoeff
      have hm : ((Box.toPoly f).comp (X + C c)).Monic :=
        (toPoly_monic f).comp_X_add_C c
      have hd : ((Box.toPoly f).comp (X + C c)).natDegree = n := by
        rw [← taylor_apply, natDegree_taylor, toPoly_natDegree hN f]
      have hcoe := hm.coeff_natDegree
      rw [hd] at hcoe
      exact hcoe
    unfold cVal
    rw [hc, zmodVal_of_ne_zero one_ne_zero, ZMod.val_one,
      padicValNat_one_right]
    simp

/-- `n` is always a resolved index (the monic top dot). -/
theorem mem_resolvedIdx_top {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    (k : ℕ) : n ∈ resolvedIdx f c k := by
  simp [resolvedIdx]

/-- The least resolved index is genuinely resolved: `y_{x₀} < k` unless
`x₀ = n`. -/
theorem cVal_x0_lt {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N)) (k : ℕ) :
    cVal f c (x0 f c k) < k ∨ x0 f c k = n := by
  have h := Finset.min'_mem (resolvedIdx f c k) (resolvedIdx_nonempty f c k)
  unfold resolvedIdx at h
  rw [Finset.mem_filter] at h
  exact h.2

/-- Between the least resolved index and `n`, the resolved lower hull stays
strictly below the scan level: every valid supporting line of `resolvedSet`
is `< k` on `[x₀, n]` (its values at the anchor dots `(x₀, y_{x₀})` and
`(n, 0)` are `< k`, and an affine function on an interval is bounded by its
endpoint values). -/
theorem npHeight_lt_of_x0_le {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    {k i : ℕ} (hk : 0 < k) (hx0 : x0 f c k ≤ i) (hin : i ≤ n) :
    OM.NewtonPolygon.npHeight (resolvedSet f c k) (resolvedSet_nonempty f c k)
      (i : ℚ) < (k : ℚ) := by
  have hx0mem : x0 f c k ∈ resolvedIdx f c k :=
    Finset.min'_mem _ (resolvedIdx_nonempty f c k)
  have hdotx : (x0 f c k, cVal f c (x0 f c k)) ∈ resolvedSet f c k :=
    Finset.mem_image_of_mem _ hx0mem
  have hdotn : (n, cVal f c n) ∈ resolvedSet f c k :=
    Finset.mem_image_of_mem _ (mem_resolvedIdx_top f c k)
  have hyn : cVal f c n = 0 := cVal_top f c
  have hk0 : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hcast1 : (x0 f c k : ℚ) ≤ (i : ℚ) := by exact_mod_cast hx0
  have hcast2 : (i : ℚ) ≤ (n : ℚ) := by exact_mod_cast hin
  unfold OM.NewtonPolygon.npHeight
  rw [Finset.sup'_lt_iff]
  intro PR hPR
  have h1 := OM.NewtonPolygon.pairLine_le_of_valid _ hPR hdotx
  have h2 := OM.NewtonPolygon.pairLine_le_of_valid _ hPR hdotn
  rw [hyn] at h2
  norm_num at h2
  -- affine difference law: L t − L u = s·(t − u)
  have hlin : ∀ t u : ℚ,
      OM.NewtonPolygon.pairLine PR.1 PR.2 t
        - OM.NewtonPolygon.pairLine PR.1 PR.2 u
        = OM.NewtonPolygon.pairSlope PR.1 PR.2 * (t - u) := by
    intro t u
    simp only [OM.NewtonPolygon.pairLine]
    ring
  rcases cVal_x0_lt f c k with hylt | hxn
  · have hyltQ : (cVal f c (x0 f c k) : ℚ) < (k : ℚ) := by exact_mod_cast hylt
    by_cases hs0 : 0 ≤ OM.NewtonPolygon.pairSlope PR.1 PR.2
    · -- nonneg slope: L i ≤ L n ≤ 0 < k
      have hd := hlin (n : ℚ) (i : ℚ)
      have hnn : 0 ≤ OM.NewtonPolygon.pairSlope PR.1 PR.2 * ((n : ℚ) - (i : ℚ)) :=
        mul_nonneg hs0 (sub_nonneg.mpr hcast2)
      linarith
    · -- neg slope: L i ≤ L x₀ ≤ y_{x₀} < k
      have hs0' : OM.NewtonPolygon.pairSlope PR.1 PR.2 ≤ 0 :=
        (not_le.mp hs0).le
      have hd := hlin (i : ℚ) ((x0 f c k : ℕ) : ℚ)
      have hnp : OM.NewtonPolygon.pairSlope PR.1 PR.2
          * ((i : ℚ) - (x0 f c k : ℚ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hs0' (sub_nonneg.mpr hcast1)
      linarith
  · -- x₀ = n forces i = n
    have hi : i = n := le_antisymm hin (hxn ▸ hx0)
    subst hi
    linarith

/-- (C1) is REDUNDANT — the rev-4 record note, now a theorem: at any positive
scan level the strictly-above-hull clause of `Certifies` holds for every
index in `(x₀, n)`. -/
theorem certifies_C1_auto {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    {k : ℕ} (hk : 0 < k) :
    ∀ i < n, ¬ (cVal f c i < k ∨ i = n) → x0 f c k < i →
      OM.NewtonPolygon.npHeight (resolvedSet f c k)
        (resolvedSet_nonempty f c k) (i : ℚ) < (k : ℚ) :=
  fun _ hi _ hx0 => npHeight_lt_of_x0_le f c hk hx0.le hi.le

/-- Certification via the `x₀ = 0` gate: any scan level `k ∈ (λ_prev, N]`
at which the constant term is resolved certifies ((C1) is automatic, (C2)
is its left disjunct). -/
theorem certifies_of_x0_eq_zero {N : ℕ} {f : Box p n N} {c : ZMod (p ^ N)}
    {lam k : ℕ} (hlam : lam < k) (hkN : k ≤ N) (hx0 : x0 f c k = 0) :
    Certifies f c lam k :=
  ⟨hlam, hkN,
    certifies_C1_auto f c (lt_of_le_of_lt (Nat.zero_le lam) hlam),
    Or.inl hx0⟩

/-- The constant term resolved at level `k` forces `x₀ = 0`. -/
theorem x0_eq_zero_of_cVal_lt {N : ℕ} {f : Box p n N} {c : ZMod (p ^ N)}
    {k : ℕ} (h : cVal f c 0 < k) : x0 f c k = 0 := by
  have h0 : 0 ∈ resolvedIdx f c k := by
    rw [resolvedIdx, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.succ_pos n), Or.inl h⟩
  exact Nat.le_zero.mp (Finset.min'_le _ _ h0)

/-- EXISTENCE of a certify level, x₀ = 0 route: if the recentered constant
term resolves before the horizon (`y₀ < N`) and the entry slope datum is
below the horizon (`λ_prev < N`), some level certifies.  (The x₀ = 1 route —
`y₀ = N`, the left-edge shortcut — is the Fact-D certify-level arithmetic,
part of the OPEN core below.) -/
theorem exists_certifies_of_cVal_lt {N : ℕ} {f : Box p n N} {c : ZMod (p ^ N)}
    {lam : ℕ} (h0 : cVal f c 0 < N) (hlam : lam < N) :
    ∃ k, Certifies f c lam k :=
  ⟨max (cVal f c 0) lam + 1,
    certifies_of_x0_eq_zero (by omega) (by omega)
      (x0_eq_zero_of_cVal_lt (by omega))⟩

/-- DIG nonvanishing read: the base-p digit of `x` at its EXACT truncated
valuation is nonzero (`zmodVal x = j < M` says `p^j ‖ x.val`). -/
theorem digitAt_ne_zero_of_zmodVal_eq {M : ℕ} {x : ZMod (p ^ M)} {j : ℕ}
    (hj : zmodVal x = j) (hjM : j < M) : digitAt x j ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hx : x ≠ 0 := by
    intro h
    rw [h, zmodVal_zero] at hj
    omega
  have hj' := hj
  rw [zmodVal_of_ne_zero hx] at hj'
  have hval : padicValNat p x.val = j := by omega
  have hvne : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).mp h)
  have hdvd : p ^ j ∣ x.val := by
    rw [← hval]
    exact pow_padicValNat_dvd
  have hndvd : ¬ p ^ (j + 1) ∣ x.val := by
    rw [← hval]
    exact pow_succ_padicValNat_not_dvd hvne
  unfold digitAt
  intro hdig
  rw [ZMod.natCast_eq_zero_iff] at hdig
  have hlt : x.val / p ^ j % p < p := Nat.mod_lt _ hp.pos
  have hmod : x.val / p ^ j % p = 0 := Nat.eq_zero_of_dvd_of_lt hdig hlt
  have hpd : p ∣ x.val / p ^ j := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨t, ht⟩ := hpd
  apply hndvd
  refine ⟨t, ?_⟩
  calc x.val = p ^ j * (x.val / p ^ j) := (Nat.mul_div_cancel' hdvd).symm
    _ = p ^ j * (p * t) := by rw [ht]
    _ = p ^ (j + 1) * t := by ring

/-- DIG vanishing read: digits strictly below the truncated valuation
vanish. -/
theorem digitAt_eq_zero_of_lt_zmodVal {M : ℕ} {x : ZMod (p ^ M)} {j : ℕ}
    (hj : j < zmodVal x) : digitAt x j = 0 := by
  have hp : p.Prime := Fact.out
  have hkM : j + 1 ≤ M := le_trans (Nat.succ_le_of_lt hj) (zmodVal_le x)
  have hdvd : (p : ZMod (p ^ M)) ^ (j + 1) ∣ x :=
    (le_zmodVal_iff hkM x).mp (Nat.succ_le_of_lt hj)
  have hdvd' : p ^ (j + 1) ∣ x.val := (pow_dvd_iff_dvd_val hkM x).mp hdvd
  obtain ⟨t, ht⟩ := hdvd'
  unfold digitAt
  rw [ht]
  have hq : p ^ (j + 1) * t / p ^ j = p * t := by
    have hnum : p ^ (j + 1) * t = p ^ j * (p * t) := by ring
    rw [hnum]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.pos j)
  rw [hq, Nat.mul_mod_right]
  simp

/-- The Step-0 engine audit, `≠ 0` form (campaign layer): the side-read
residuals are nonzero but NOT monic (their leading digit is an arbitrary
unit), so the audit is re-proved from `R ≠ 0` alone — the degree partition
`Σ_ψ count·deg = deg R` runs through the associated normalized product
(the unit factor carries degree 0). -/
theorem processResidual_audit' {R : Polynomial (ZMod p)} (hR0 : R ≠ 0)
    (hdeg3 : R.natDegree ≤ 3)
    {rec : ZMod p → ℕ → Option (Multiset (ℕ × ℕ))}
    (hrec : ∀ ψ ∈ UniqueFactorizationMonoid.normalizedFactors R,
      2 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ →
      ψ.natDegree = 1 →
      ∃ S, rec (- ψ.coeff 0)
          ((UniqueFactorizationMonoid.normalizedFactors R).count ψ) = some S ∧
        (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
        (S.map fun x => x.1 * x.2).sum
          = (UniqueFactorizationMonoid.normalizedFactors R).count ψ) :
    ∃ S, processResidual R rec = some S ∧
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = R.natDegree := by
  have h0 : (0 : Polynomial (ZMod p)) ∉ UniqueFactorizationMonoid.normalizedFactors R :=
    UniqueFactorizationMonoid.zero_notMem_normalizedFactors R
  -- the degree partition Σ_ψ count(ψ)·deg(ψ) = deg R, via the associated product
  have hmapsum : ((UniqueFactorizationMonoid.normalizedFactors R).map
      Polynomial.natDegree).sum = R.natDegree := by
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hR0
    have hprod0 : (UniqueFactorizationMonoid.normalizedFactors R).prod ≠ 0 :=
      Multiset.prod_ne_zero h0
    have hu0 : (u : Polynomial (ZMod p)) ≠ 0 := u.ne_zero
    have hdegprod : (UniqueFactorizationMonoid.normalizedFactors R).prod.natDegree
        = R.natDegree := by
      conv_rhs => rw [← hu]
      rw [Polynomial.natDegree_mul hprod0 hu0,
        Polynomial.natDegree_eq_zero_of_isUnit u.isUnit, add_zero]
    rw [← hdegprod]
    exact (Polynomial.natDegree_multiset_prod _ h0).symm
  have hkey : ∑ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors R).toFinset,
      (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree
      = R.natDegree := by
    rw [Finset.sum_multiset_map_count] at hmapsum
    simpa [smul_eq_mul, nsmul_eq_mul] using hmapsum
  have hspec : ∀ ψ ∈ (UniqueFactorizationMonoid.normalizedFactors R).toFinset.toList,
      ∃ S, (if (UniqueFactorizationMonoid.normalizedFactors R).count ψ = 1 then
          some ({(1, ψ.natDegree)} : Multiset (ℕ × ℕ))
        else if ψ.natDegree = 1 then
          rec (- ψ.coeff 0)
            ((UniqueFactorizationMonoid.normalizedFactors R).count ψ)
        else none) = some S ∧
        ((∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
          (S.map fun x => x.1 * x.2).sum
            = (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree) := by
    intro ψ hψl
    have hψ : ψ ∈ UniqueFactorizationMonoid.normalizedFactors R := by
      rw [← Multiset.mem_toFinset]
      exact Finset.mem_toList.mp hψl
    have hirr : Irreducible ψ :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψ
    have hdpos : 0 < ψ.natDegree := hirr.natDegree_pos
    by_cases hc : (UniqueFactorizationMonoid.normalizedFactors R).count ψ = 1
    · refine ⟨{(1, ψ.natDegree)}, by rw [if_pos hc], ?_, by simp [hc]⟩
      intro x hx
      rw [Multiset.mem_singleton] at hx
      subst hx
      exact ⟨le_rfl, hdpos⟩
    · have hcpos : 0 < (UniqueFactorizationMonoid.normalizedFactors R).count ψ :=
        Multiset.count_pos.mpr hψ
      have hc2 : 2 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ := by
        omega
      have hd1 : ψ.natDegree = 1 := by
        by_contra hne
        have hd2 : 2 ≤ ψ.natDegree := by omega
        have hle : (UniqueFactorizationMonoid.normalizedFactors R).count ψ
            * ψ.natDegree ≤ R.natDegree := by
          rw [← hkey]
          exact Finset.single_le_sum
            (f := fun φ => (UniqueFactorizationMonoid.normalizedFactors R).count φ
              * φ.natDegree)
            (fun i _ => Nat.zero_le _) (Multiset.mem_toFinset.mpr hψ)
        have h4 : 4 ≤ (UniqueFactorizationMonoid.normalizedFactors R).count ψ
            * ψ.natDegree := Nat.mul_le_mul hc2 hd2
        omega
      obtain ⟨S, hS, hS1, hS2⟩ := hrec ψ hψ hc2 hd1
      refine ⟨S, ?_, hS1, by rw [hS2, hd1, mul_one]⟩
      rw [if_neg hc, if_pos hd1]
      exact hS
  obtain ⟨L, hmapM, hforall⟩ := mapM_option_spec
    (P := fun (ψ : Polynomial (ZMod p)) (S : Multiset (ℕ × ℕ)) =>
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum
        = (UniqueFactorizationMonoid.normalizedFactors R).count ψ * ψ.natDegree)
    hspec
  have haudit := forall₂_multiset_audit hforall
  refine ⟨L.sum, ?_, haudit.1, ?_⟩
  · unfold processResidual
    rw [hmapM]
    rfl
  · rw [haudit.2, Finset.sum_map_toList, hkey]

/-- The on-line digit residual of a side, as a NAMED spec-layer object
(campaign layer; `processSide_def` pins it to the walk's inline expression
by `rfl` — no walk clause is changed). -/
noncomputable def sideResidual {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    (s : OM.NewtonPolygon.Side) : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range (s.length + 1),
    C (if (cVal f c (s.i₀ + j) : ℤ) = (s.v₀ : ℤ) - (j : ℤ) * (- s.slope).num
       then digitAt (shiftedCoeff f c (s.i₀ + j))
         ((s.v₀ : ℤ) - (j : ℤ) * (- s.slope).num).toNat
       else 0) * X ^ j

/-- Definitional pin: `processSide` in terms of the named residual. -/
theorem processSide_def {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    (s : OM.NewtonPolygon.Side)
    (rec : ZMod p → ℕ → ℕ → Option (Multiset (ℕ × ℕ))) :
    processSide f c s rec =
      if (- s.slope).den = s.length then
        some ({((- s.slope).den, 1)} : Multiset (ℕ × ℕ))
      else if (- s.slope).den = 1 ∧ 2 ≤ s.length then
        processResidual (sideResidual f c s)
          (fun z m => rec z m (- s.slope).num.toNat)
      else none := rfl

/-- Side audit (campaign layer): every NON-REFUSING side read completes with
a multiset partitioning the side's horizontal length — the `d = 1` branch
certifies `(e, 1)` of weight `e = ℓ`, and the `e = 1, d = ℓ ≥ 2` branch runs
the engine audit on the digit residual, GIVEN its degree pin (`deg R = ℓ`,
the on-hull endpoint digits being nonzero — an N3-side input) and the
sub-cluster recursion hypothesis. -/
theorem processSide_audit {N : ℕ} (f : Box p n N) (c : ZMod (p ^ N))
    (s : OM.NewtonPolygon.Side)
    (rec : ZMod p → ℕ → ℕ → Option (Multiset (ℕ × ℕ)))
    (hok : (- s.slope).den = s.length ∨ ((- s.slope).den = 1 ∧ 2 ≤ s.length))
    (hlen3 : s.length ≤ 3)
    (hdeg : (- s.slope).den ≠ s.length →
      (sideResidual f c s).natDegree = s.length)
    (hrec : (- s.slope).den ≠ s.length →
      ∀ ψ ∈ UniqueFactorizationMonoid.normalizedFactors (sideResidual f c s),
        2 ≤ (UniqueFactorizationMonoid.normalizedFactors
          (sideResidual f c s)).count ψ →
        ψ.natDegree = 1 →
        ∃ S, rec (- ψ.coeff 0)
            ((UniqueFactorizationMonoid.normalizedFactors
              (sideResidual f c s)).count ψ)
            (- s.slope).num.toNat = some S ∧
          (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
          (S.map fun x => x.1 * x.2).sum
            = (UniqueFactorizationMonoid.normalizedFactors
              (sideResidual f c s)).count ψ) :
    ∃ S, processSide f c s rec = some S ∧
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = s.length := by
  rw [processSide_def]
  by_cases hden : (- s.slope).den = s.length
  · rw [if_pos hden]
    refine ⟨_, rfl, ?_, ?_⟩
    · intro x hx
      rw [Multiset.mem_singleton] at hx
      subst hx
      exact ⟨(- s.slope).den_pos, le_rfl⟩
    · simp [hden]
  · have hres : (- s.slope).den = 1 ∧ 2 ≤ s.length := hok.resolve_left hden
    rw [if_neg hden, if_pos hres]
    have hd : (sideResidual f c s).natDegree = s.length := hdeg hden
    have hR0 : sideResidual f c s ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hd
      omega
    obtain ⟨S, hS, h1, h2⟩ := processResidual_audit'
      (rec := fun z m => rec z m (- s.slope).num.toNat) hR0
      (by rw [hd]; exact hlen3) (hrec hden)
    exact ⟨S, hS, h1, by rw [h2, hd]⟩

/-- The walk's successor equation (a definitional pin, so the step audit can
be stated without re-unfolding the recursion). -/
theorem clusterWalk_succ {N : ℕ} (f : Box p n N) (fuel : ℕ)
    (c : ZMod (p ^ N)) (m lam : ℕ) :
    clusterWalk f (fuel + 1) c m lam =
      if h : ∃ k, Certifies f c lam k then
        (((OM.NewtonPolygon.npSides (resolvedSet f c (Nat.find h))
              (resolvedSet_nonempty f c (Nat.find h))).filter
            (fun s => decide ((lam : ℚ) < - s.slope))).mapM
          (fun s => processSide f c s
            (fun z m' hh =>
              clusterWalk f fuel
                (c + (z.val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ hh)
                m' hh))).map
        (fun l =>
          (if x0 f c (Nat.find h) = 1 then ({(1, 1)} : Multiset (ℕ × ℕ)) else 0)
            + l.sum)
      else none := rfl

/-- Step audit (campaign layer): one full cluster step completes with a
multiset partitioning `m`, GIVEN (i) a certify level exists, (ii) each
processed side partitions its length, and (iii) the side inventory
`[x₀ = 1] + Σ_{slope > λ_prev} ℓ = m` at the found level.  All Option/monad
plumbing of the step is discharged here; (i)–(iii) at the LEAST certify
level are exactly the open N3 chain. -/
theorem clusterWalk_succ_audit {N : ℕ} (f : Box p n N) (fuel : ℕ)
    (c : ZMod (p ^ N)) (m lam : ℕ)
    (hcert : ∃ k, Certifies f c lam k)
    (hsides : ∀ s ∈ (OM.NewtonPolygon.npSides (resolvedSet f c (Nat.find hcert))
        (resolvedSet_nonempty f c (Nat.find hcert))).filter
        (fun s => decide ((lam : ℚ) < - s.slope)),
      ∃ S, processSide f c s
          (fun z m' hh =>
            clusterWalk f fuel
              (c + (z.val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ hh)
              m' hh) = some S ∧
        (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
        (S.map fun x => x.1 * x.2).sum = s.length)
    (htotal : (if x0 f c (Nat.find hcert) = 1 then 1 else 0)
        + (((OM.NewtonPolygon.npSides (resolvedSet f c (Nat.find hcert))
            (resolvedSet_nonempty f c (Nat.find hcert))).filter
            (fun s => decide ((lam : ℚ) < - s.slope))).map
            OM.NewtonPolygon.Side.length).sum = m) :
    ∃ S, clusterWalk f (fuel + 1) c m lam = some S ∧
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = m := by
  obtain ⟨L, hmapM, hforall⟩ := mapM_option_spec
    (P := fun (s : OM.NewtonPolygon.Side) (S : Multiset (ℕ × ℕ)) =>
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = s.length)
    hsides
  have haudit := forall₂_multiset_audit (g := OM.NewtonPolygon.Side.length)
    hforall
  refine ⟨(if x0 f c (Nat.find hcert) = 1 then ({(1, 1)} : Multiset (ℕ × ℕ))
      else 0) + L.sum, ?_, ?_, ?_⟩
  · rw [clusterWalk_succ, dif_pos hcert, hmapM]
    rfl
  · intro x hx
    rcases Multiset.mem_add.mp hx with h1 | h2
    · by_cases h : x0 f c (Nat.find hcert) = 1
      · rw [if_pos h, Multiset.mem_singleton] at h1
        subst h1
        exact ⟨le_rfl, le_rfl⟩
      · rw [if_neg h] at h1
        simp at h1
    · exact haudit.1 x h2
  · rw [Multiset.map_add, Multiset.sum_add, haudit.2]
    by_cases h : x0 f c (Nat.find hcert) = 1
    · rw [if_pos h]
      rw [if_pos h] at htotal
      simpa using htotal
    · rw [if_neg h]
      rw [if_neg h] at htotal
      simpa using htotal

/-- T7 HARD CORE (OPEN): each cluster step the walk opens at a repeated
residue root completes within fuel N under the ceiling hypothesis
`discV + 1 ≤ N`, certifying a multiset that partitions its multiplicity —
Theorem N3's termination + audit chain ((I1) "> 0" criterion, Lemmas
CERT/SIDE/REC, the case (a)/(b) certify-level arithmetic against Fact D).
Everything downstream of this lemma is proved. -/
theorem clusterWalk_audit {N : ℕ} (hn0 : 2 ≤ n) (hn1 : n ≤ 3) (hN : 0 < N)
    (f : Box p n N) (hdisc : discV p n N f + 1 ≤ N)
    (ψ : Polynomial (ZMod p))
    (hψ : ψ ∈ UniqueFactorizationMonoid.normalizedFactors (fbar hN f))
    (hm : 2 ≤ (UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ)
    (hdeg : ψ.natDegree = 1) :
    ∃ S, clusterWalk f N (((- ψ.coeff 0).val : ZMod (p ^ N)))
        ((UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ) 0
        = some S ∧
      (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum
        = (UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ := by
  -- BLOCKED(T7-core): the Theorem-N3 (CEIL) analytic core.  The paper proof
  -- (O4T rev 4 §§3.3–3.4) runs through the true root valuations
  -- b_j = v(α_j − c) in Q̄_p and consumes Facts NP/SF/HEN +
  -- EXT/EF/D/GRD/UCT/HRG/SEP/DES: (I1) needs Fact EXT (unique valuation
  -- extension + Galois invariance), CERT(ii) needs Fact DES (Galois
  -- descent), SIDE needs Facts SF/HEN/EF/HRG, RES needs Fact GRD, and the
  -- certify-level bound k ≤ v_p(disc f)+1 needs Fact D
  -- (disc = ∏(α_i−α_j)²).  None of this extended-valuation root theory
  -- for Q̄_p exists in the corpus or in this Mathlib pin, and a
  -- coefficients-only reproof is a NEW mathematical development not
  -- sanctioned by the source of record.  Dedicated campaign required
  -- (BP_IV row T7: "a dedicated formalization campaign").
  --
  -- CAMPAIGN SESSION 1 (2026-08-01, see the campaign subsection above):
  -- the sorry's perimeter is now strictly the N3 chain.  PROVED and
  -- available at this point: (C1)-redundancy + x₀ = 0 certification
  -- existence (`exists_certifies_of_cVal_lt`), the DIG digit reads, the
  -- ≠ 0 engine audit (`processResidual_audit'`), the side audit
  -- (`processSide_audit` over the named `sideResidual`), and the step
  -- audit (`clusterWalk_succ_audit` — via `clusterWalk_succ`, both the
  -- Option/monad plumbing and the multiset bookkeeping of one full step).
  -- STILL OPEN inside this sorry, per side-inventory at the LEAST certify
  -- level of every visited cluster: (i) certification existence on the
  -- x₀ = 1 route (Fact-D arithmetic y₁ + max(s_r, λ) < k ≤ v_p(disc)+1),
  -- (ii) each processed side's `hok`/`hdeg`/`hrec` inputs (hull-endpoint
  -- digit exactness + sub-cluster invariant transport), (iii) the (I1)
  -- inventory [x₀ = 1] + Σ_{slope>λ} ℓ = m, (iv) the fuel induction
  -- tying (i)–(iii) through recursion depth ≤ N.
  sorry

/-- Step-0 assembly (sorry-free): granted the per-cluster walk-completion
hypothesis, the raw verdict exists and passes the degree audit — Step 0
partitions n into simple certified factors `(1, deg ψ)` and cluster blocks
of total weight `count ψ` (`processResidual_audit` at `R = f̄`, degree n by
`fbar_natDegree`). -/
theorem rawType_ne_none_of_clusterWalk {N : ℕ} (hn1 : n ≤ 3) (hN : 0 < N)
    (f : Box p n N)
    (hclu : ∀ ψ ∈ UniqueFactorizationMonoid.normalizedFactors (fbar hN f),
      2 ≤ (UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ →
      ψ.natDegree = 1 →
      ∃ S, clusterWalk f N (((- ψ.coeff 0).val : ZMod (p ^ N)))
          ((UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ) 0
          = some S ∧
        (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
        (S.map fun x => x.1 * x.2).sum
          = (UniqueFactorizationMonoid.normalizedFactors (fbar hN f)).count ψ) :
    rawType f ≠ none := by
  obtain ⟨S, hS, hS1, hS2⟩ := processResidual_audit
    (rec := fun z m => clusterWalk f N ((z.val : ZMod (p ^ N))) m 0)
    (fbar_monic hN f) (by rw [fbar_natDegree hN f]; exact hn1)
    (fun ψ hψ h2 h1 => hclu ψ hψ h2 h1)
  have hrle : rawLEOne f = some S := by
    unfold rawLEOne
    rw [dif_pos hN]
    exact hS
  have hok : (∀ x ∈ S, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
      (S.map fun x => x.1 * x.2).sum = n :=
    ⟨hS1, by rw [hS2, fbar_natDegree hN f]⟩
  unfold rawType
  rw [hrle, Option.bind_some, dif_pos hok]
  exact Option.some_ne_none _

/-- T7 core interface, assembled: under the ceiling hypothesis
`discV + 1 ≤ N` the raw §3.2 walk completes with a degree-audited verdict.
Sorry-free EXCEPT through `clusterWalk_audit` (the unit's one open core —
see its `BLOCKED(T7)` note). -/
theorem rawType_ne_none_of_discV_succ_le {N : ℕ}
    (hn0 : 2 ≤ n) (hn1 : n ≤ 3) (f : Box p n N)
    (hdisc : discV p n N f + 1 ≤ N) :
    rawType f ≠ none := by
  have hN : 0 < N := by omega
  exact rawType_ne_none_of_clusterWalk hn1 hN f
    (fun ψ hψ hm hdeg => clusterWalk_audit hn0 hn1 hN f hdisc ψ hψ hm hdeg)

end T7

end OrderLEOne

/-- T7's complete CEIL interface. `canonicalOrderLEOne` is the concrete
classifier definition of unit T4b; the theorem has exactly the N3 degree scope. -/
noncomputable def canonicalOrderLEOne (n p : ℕ) [Fact p.Prime] :
    ClassifierSpec n p where
  canonical := fun N f => OrderLEOne.stabVerdict N f
  trueType := bridgeTrueType n p bridgeZfType
  canonical_stable := fun {_ _} h f σ hσ =>
    OrderLEOne.stabVerdict_stable h f σ hσ
  baseSection := .teichmuller

/-! ### T4b definitional pins (the K0a-style spec layer) -/

/-- The canonical map is the first-decision closure of the §3.2 walk verdict
(definitional display, for T7's consumption). -/
theorem canonicalOrderLEOne_canonical (n p : ℕ) [Fact p.Prime] (N : ℕ)
    (f : Box p n N) :
    (canonicalOrderLEOne n p).canonical N f = OrderLEOne.stabVerdict N f := rfl

/-- The true-type field is the corpus ℤ_p reading — `bridgeTrueType` at the
concrete `bridgeZfType` (definitional display; `VPSound` for this instance
stays a genuine open claim = N3 soundness). -/
theorem canonicalOrderLEOne_trueType (n p : ℕ) [Fact p.Prime] :
    (canonicalOrderLEOne n p).trueType = bridgeTrueType n p bridgeZfType := rfl

/-- The O3 base-section pin (definitional display — the
`CapstoneLedger.o3_teichmuller`-shaped supply). -/
theorem canonicalOrderLEOne_teichmuller (n p : ℕ) [Fact p.Prime] :
    (canonicalOrderLEOne n p).baseSection = BaseSection.teichmuller := rfl

/-- T7 (statement VERBATIM from BP_IV §1.1; unit status PARTIAL — see the
unit-T7 provenance note): the CEIL clause for the canonical order-≤1
classifier at the N3 degree scope.  Assembled from the PROVED closure
reduction `OrderLEOne.stabVerdict_ne_none_of_raw`, the PROVED Step-0
assembly `OrderLEOne.rawType_ne_none_of_clusterWalk`, and the OPEN
per-cluster core `OrderLEOne.clusterWalk_audit` (the one `sorry` of this
unit — Theorem N3's walk-completion chain; see the `BLOCKED(T7)` note
there). -/
theorem canonicalOrderLEOne_ceil {n p : ℕ} [Fact p.Prime]
    (hn0 : 2 ≤ n) (hn1 : n ≤ 3) :
    ∀ N (f : Box p n N), discV p n N f + 1 ≤ N →
      (canonicalOrderLEOne n p).canonical N f ≠ none := by
  intro N f hdisc
  rw [canonicalOrderLEOne_canonical]
  exact OrderLEOne.stabVerdict_ne_none_of_raw f
    (OrderLEOne.rawType_ne_none_of_discV_succ_le hn0 hn1 f hdisc)

/-!
**PROVENANCE (unit T8; BP_IV §1.1 `DrainageImports` display — the `tail`
field — + §2 T-table row T8, sources M05 Lemma C and O4T §3.1 (THREE imports
note)).**  Conclusion transcribed VERBATIM from the §1.1 `tail` row;
`discV_tail_count` is the row's constructor (the T8 discharge), exactly as
`canonicalOrderLEOne_ceil` is CEIL's (unit T7).

Mechanism (blueprint row T8: "resultant divisibility ⇒ coefficient
constraints; wild shift n·v_p(n) additive"):

* the level-N tail event `{m ≤ discV}` is level-m cylinder data —
  discriminant naturality for monic polynomials (`discr_map_monic`; the
  corpus engine of `MovesX/XF1.lean` is `private`, so it is re-proved here
  through the resultant, byte-faithfully) converts `p^m ∣ disc` at level N
  into `disc = 0` at level m (`le_discV_iff_proj_discr_eq_zero`);
* the exact T0 fiber count (`card_boxProj_fiber`, sigma-packaged over an
  arbitrary level-m predicate in `card_boxProj_preimage`) then gives
  `count = tailCount p n m · p^{n(N−m)}` (`card_tail_event`; the level-m
  discriminant-zero count IS the corpus carrier `MovesX.tailCount`,
  definitionally — `card_discrZero_eq_tailCount`);
* M05 Lemma C's Lean count form `MovesX.tailCountBound` (corpus, PROVED)
  bounds `tailCount p n m ≤ (n−1)·p^{nm−tailExp}` with
  `tailExp = ⌈(m − n·v_p(n))/(n−1)⌉`;
* the wild shift `n·v_p(n)` is ADDITIVE in the exponent and absorbed by the
  `n²` factor of `tailC`: `p^{m/(2(n−1)) − tailExp} ≤ p^{n·v_p(n)/(n−1)}
  ≤ n^{n/(n−1)} ≤ n²` for every prime p at n ≥ 2 (`tail_wild_shift_bound`,
  via `p^{v_p(n)} ∣ n` and `n/(n−1) ≤ 2`) — exactly the margin the unit-T4
  provenance note sized `tailC n = (n−1)·n²` for.  (The displayed rate
  `m/(2(n−1))` is HALF the available `(m − n·v_p(n))/(n−1)`; the slack is
  spent making the constant p-uniform.)
-/

section T8

open Polynomial

variable {p n : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Monic-case discriminant/resultant tie (the `MovesX/XF1.lean` private
helper, re-proved verbatim): for monic `f` of positive degree,
`discr = ± Res(f, f′)`. -/
theorem discr_monic_eq_resultant {R : Type*} [CommRing R] (f : R[X])
    (hf : f.Monic) (hpos : 0 < f.natDegree) :
    f.discr =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        resultant f f.derivative f.natDegree (f.natDegree - 1) := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  have h := resultant_deriv hdeg
  rw [hf.leadingCoeff, mul_one] at h
  have hsq : ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [h, ← mul_assoc, hsq, one_mul]

omit [Fact p.Prime] in
/-- Discriminant naturality for monic polynomials (the `MovesX/XF1.lean`
private helper, re-proved verbatim): `discr` commutes with any ring hom —
the "resultant divisibility ⇒ coefficient constraints" engine of the T8 row,
in the form this file consumes. -/
theorem discr_map_monic {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : R[X]) (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with hz | hpos
  · have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hf hz
    subst hf1
    have h1R : discr (1 : R[X]) = 1 := by rw [← C_1]; exact discr_C 1
    have h1S : discr (1 : S[X]) = 1 := by rw [← C_1]; exact discr_C 1
    rw [Polynomial.map_one, h1R, h1S, map_one]
  · by_cases hS : Nontrivial S
    · have hmap : (f.map φ).Monic := hf.map φ
      have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
      have hpos' : 0 < (f.map φ).natDegree := by rw [hdeg]; exact hpos
      rw [discr_monic_eq_resultant f hf hpos,
          discr_monic_eq_resultant (f.map φ) hmap hpos']
      have hder : (f.map φ).derivative = f.derivative.map φ := derivative_map f φ
      rw [hder, hdeg, resultant_map_map, map_mul, map_pow, map_neg, map_one]
    · rw [not_nontrivial_iff_subsingleton] at hS
      exact Subsingleton.elim _ _

omit [Fact p.Prime] in
/-- The box polynomial is monic: its lower part has degree < n. -/
theorem toPoly_monic {N : ℕ} (f : Box p n N) : (Box.toPoly f).Monic := by
  have hlt : (∑ i : Fin n, C (f i) * X ^ (i : ℕ)).degree < (n : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
    intro i _
    calc (C (f i) * X ^ (i : ℕ)).degree
        ≤ ((i : ℕ) : WithBot ℕ) := degree_C_mul_X_pow_le _ _
      _ < (n : WithBot ℕ) := by exact_mod_cast i.2
  exact monic_X_pow_add hlt

omit [Fact p.Prime] in
/-- `Box.toPoly` naturality: the box polynomial of the level reduction is the
coefficient-wise `ZMod.castHom` base change of the box polynomial. -/
theorem toPoly_boxProj {N m : ℕ} (h : m ≤ N) (f : Box p n N) :
    Box.toPoly (boxProj p n h f)
      = (Box.toPoly f).map (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) := by
  simp only [Box.toPoly, boxProj, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    ZMod.castHom_apply]

/-- Cylinder transfer of the tail event: for `m ≤ N`, "`m ≤ discV` at level N"
reads exactly "the level-m reduction has vanishing truncated discriminant"
(the K0b divisibility bridge + discriminant naturality). -/
theorem le_discV_iff_proj_discr_eq_zero {N m : ℕ} (h : m ≤ N) (f : Box p n N) :
    m ≤ discV p n N f ↔
      Polynomial.discr (Box.toPoly (boxProj p n h f)) = 0 := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  rw [le_discV_iff h f, toPoly_boxProj h f,
    discr_map_monic (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)))
      (Box.toPoly f) (toPoly_monic f),
    pow_dvd_iff_dvd_val h, ZMod.castHom_apply, ← ZMod.natCast_val,
    ZMod.natCast_eq_zero_iff]

/-- The exact fiber count over the level reduction, packaged for an arbitrary
level-m predicate (T0's `card_boxProj_fiber`, sigma-assembled — the T1
counting pattern, predicate form). -/
theorem card_boxProj_preimage {N m : ℕ} (h : m ≤ N) (P : Box p n m → Prop) :
    Nat.card {f : Box p n N // P (boxProj p n h f)}
      = Nat.card {g : Box p n m // P g} * p ^ (n * (N - m)) := by
  classical
  have E : {f : Box p n N // P (boxProj p n h f)} ≃
      Σ g : {g : Box p n m // P g}, {f : Box p n N // boxProj p n h f = g.1} :=
    { toFun := fun f => ⟨⟨boxProj p n h f.1, f.2⟩, ⟨f.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
      left_inv := fun f => rfl
      right_inv := fun x => by
        obtain ⟨⟨g, hg⟩, ⟨f, hf⟩⟩ := x
        dsimp only at hf
        subst hf
        rfl }
  rw [Nat.card_congr E, Nat.card_sigma]
  simp only [card_boxProj_fiber h]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

omit [Fact p.Prime] in
/-- The level-m discriminant-zero box count IS the corpus (3b) carrier
`MovesX.tailCount` (definitional identification: `Box p n m` is
`Fin n → ZMod (p^m)` and `Box.toPoly` is `MovesX.polyOfCoeffs`, term for
term). -/
theorem card_discrZero_eq_tailCount (m : ℕ) :
    Nat.card {g : Box p n m // Polynomial.discr (Box.toPoly g) = 0}
      = MovesX.tailCount p n m := rfl

/-- T8 counting layer: the level-N tail event is the level-m
discriminant-zero count times the exact T0 fiber size. -/
theorem card_tail_event {N m : ℕ} (hmN : m ≤ N) :
    Nat.card {f : Box p n N // m ≤ discV p n N f}
      = MovesX.tailCount p n m * p ^ (n * (N - m)) := by
  have hiff : ∀ f : Box p n N, m ≤ discV p n N f ↔
      Polynomial.discr (Box.toPoly (boxProj p n hmN f)) = 0 :=
    fun f => le_discV_iff_proj_discr_eq_zero hmN f
  calc Nat.card {f : Box p n N // m ≤ discV p n N f}
      = Nat.card {f : Box p n N //
          Polynomial.discr (Box.toPoly (boxProj p n hmN f)) = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = Nat.card {g : Box p n m // Polynomial.discr (Box.toPoly g) = 0}
          * p ^ (n * (N - m)) :=
        card_boxProj_preimage hmN (fun g => Polynomial.discr (Box.toPoly g) = 0)
    _ = MovesX.tailCount p n m * p ^ (n * (N - m)) := by
        rw [card_discrZero_eq_tailCount]

/-- T8 wild-shift absorption (M05 Lemma C's exponent arithmetic): the gap
between the ceiling exponent `tailExp = ⌈(m − n·v_p(n))/(n−1)⌉` and the
displayed rate `m/(2(n−1))` is at most `n·v_p(n)/(n−1)`, and
`p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} ≤ n²` uniformly in the prime p (via
`p^{v_p(n)} ∣ n` and `n/(n−1) ≤ 2` at `n ≥ 2`) — the margin `tailC` was
sized for (unit-T4 provenance note). -/
theorem tail_wild_shift_bound (hn0 : 2 ≤ n) (m : ℕ) :
    (p : ℝ) ^ ((m : ℝ) / (2 * ((n : ℝ) - 1)) - (MovesX.tailExp p n m : ℝ))
      ≤ (n : ℝ) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hden : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- the ceiling lower bound, cast to ℝ
  have htlbQ : ((m : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)
      ≤ (MovesX.tailExp p n m : ℚ) := by
    unfold MovesX.tailExp
    exact Int.le_ceil _
  have htlb : ((m : ℝ) - (n : ℝ) * (padicValNat p n : ℝ)) / ((n : ℝ) - 1)
      ≤ (MovesX.tailExp p n m : ℝ) := by
    have h2 : ((((m : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ) : ℚ) : ℝ)
        ≤ (((MovesX.tailExp p n m : ℚ)) : ℝ) := by exact_mod_cast htlbQ
    calc ((m : ℝ) - (n : ℝ) * (padicValNat p n : ℝ)) / ((n : ℝ) - 1)
        = ((((m : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ) : ℚ) : ℝ) := by
          push_cast
          ring
      _ ≤ (((MovesX.tailExp p n m : ℚ)) : ℝ) := h2
      _ = (MovesX.tailExp p n m : ℝ) := by push_cast; ring
  -- exponent comparison: m/(2(n−1)) − tailExp ≤ n·v/(n−1)
  have hmm : (m : ℝ) / (2 * ((n : ℝ) - 1)) ≤ (m : ℝ) / ((n : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by linarith) hden]
    nlinarith [mul_nonneg hm0 hden.le]
  have hexp : (m : ℝ) / (2 * ((n : ℝ) - 1)) - (MovesX.tailExp p n m : ℝ)
      ≤ (n : ℝ) * (padicValNat p n : ℝ) / ((n : ℝ) - 1) := by
    have hsum : ((m : ℝ) - (n : ℝ) * (padicValNat p n : ℝ)) / ((n : ℝ) - 1)
        + (n : ℝ) * (padicValNat p n : ℝ) / ((n : ℝ) - 1)
        = (m : ℝ) / ((n : ℝ) - 1) := by ring
    linarith
  -- p^gap ≤ p^{n·v/(n−1)} = (p^v)^{n/(n−1)} ≤ n^{n/(n−1)} ≤ n²
  have h2 : (p : ℝ) ^ ((n : ℝ) * (padicValNat p n : ℝ) / ((n : ℝ) - 1))
      = ((p : ℝ) ^ padicValNat p n) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
    rw [← Real.rpow_natCast (p : ℝ) (padicValNat p n), ← Real.rpow_mul hp0.le]
    congr 1
    ring
  have hpv : ((p : ℝ) ^ padicValNat p n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have h4 : (n : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤ (n : ℝ) ^ (2 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    rw [div_le_iff₀ hden]
    linarith
  calc (p : ℝ) ^ ((m : ℝ) / (2 * ((n : ℝ) - 1)) - (MovesX.tailExp p n m : ℝ))
      ≤ (p : ℝ) ^ ((n : ℝ) * (padicValNat p n : ℝ) / ((n : ℝ) - 1)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 hexp
    _ = ((p : ℝ) ^ padicValNat p n) ^ ((n : ℝ) / ((n : ℝ) - 1)) := h2
    _ ≤ (n : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) :=
        Real.rpow_le_rpow (by positivity) hpv (by positivity)
    _ ≤ (n : ℝ) ^ (2 : ℝ) := h4
    _ = (n : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **T8 (the `tail` clause, I-TAIL counting form) — the
`DrainageImports.tail` constructor.**  Conclusion VERBATIM from BP_IV §1.1's
`tail` row.  M05 Lemma C's discriminant tail count at level m (the corpus
`MovesX.tailCountBound`), transported up the exact T0 fibers
(`card_tail_event`), with the additive wild shift `n·v_p(n)` absorbed into
`tailC`'s `n²` factor (`tail_wild_shift_bound`). -/
theorem discV_tail_count (hn0 : 2 ≤ n) :
    ∀ N m : ℕ, (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
      ≤ tailC n * (p : ℝ) ^ (n * N) * (p : ℝ) ^ (-(m : ℝ) / (2 * (n - 1))) := by
  intro N m
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have htailC0 : (0 : ℝ) ≤ tailC n := by
    unfold tailC
    exact mul_nonneg (by linarith) (sq_nonneg _)
  by_cases hmN : m ≤ N
  · -- the counted case m ≤ N
    have hcount := card_tail_event (p := p) (n := n) hmN
    -- M05 Lemma C's corpus bound, cast to ℝ
    have hboundR : (MovesX.tailCount p n m : ℝ) * (p : ℝ) ^ MovesX.tailExp p n m
        ≤ ((n : ℝ) - 1) * (p : ℝ) ^ ((n * m : ℕ) : ℤ) := by
      have h2 : (((MovesX.tailCount p n m : ℚ)
              * (p : ℚ) ^ MovesX.tailExp p n m : ℚ) : ℝ)
          ≤ (((n - 1 : ℚ) * (p : ℚ) ^ ((n * m : ℕ) : ℤ) : ℚ) : ℝ) := by
        exact_mod_cast MovesX.tailCountBound p n m hn0
      calc (MovesX.tailCount p n m : ℝ) * (p : ℝ) ^ MovesX.tailExp p n m
          = (((MovesX.tailCount p n m : ℚ)
              * (p : ℚ) ^ MovesX.tailExp p n m : ℚ) : ℝ) := by
            push_cast
            ring
        _ ≤ (((n - 1 : ℚ) * (p : ℚ) ^ ((n * m : ℕ) : ℤ) : ℚ) : ℝ) := h2
        _ = ((n : ℝ) - 1) * (p : ℝ) ^ ((n * m : ℕ) : ℤ) := by
            push_cast
            ring
    set t : ℤ := MovesX.tailExp p n m with ht
    have htc_le : (MovesX.tailCount p n m : ℝ)
        ≤ ((n : ℝ) - 1) * (p : ℝ) ^ ((n * m : ℕ) : ℤ) / (p : ℝ) ^ t := by
      rw [le_div_iff₀ (zpow_pos hp0 t)]
      exact hboundR
    have hns : ((n * m : ℕ) : ℤ) + ((n * (N - m) : ℕ) : ℤ)
        = ((n * N : ℕ) : ℤ) := by
      have hNat : n * m + n * (N - m) = n * N := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hmN]
      exact_mod_cast hNat
    have hstep : (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
        ≤ ((n : ℝ) - 1) * (p : ℝ) ^ (((n * N : ℕ) : ℤ) - t) := by
      have hcountR : (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
          = (MovesX.tailCount p n m : ℝ) * (p : ℝ) ^ (n * (N - m)) := by
        rw [hcount]
        push_cast
        ring
      rw [hcountR]
      refine (mul_le_mul_of_nonneg_right htc_le (by positivity)).trans
        (le_of_eq ?_)
      rw [← zpow_natCast (p : ℝ) (n * (N - m)), zpow_sub₀ (ne_of_gt hp0),
        ← hns, zpow_add₀ (ne_of_gt hp0)]
      ring
    have hrpow_eq : (p : ℝ) ^ (((n * N : ℕ) : ℤ) - t)
        = (p : ℝ) ^ (n * N) * (p : ℝ) ^ (-(m : ℝ) / (2 * ((n : ℝ) - 1)))
          * (p : ℝ) ^ ((m : ℝ) / (2 * ((n : ℝ) - 1)) - (t : ℝ)) := by
      rw [← Real.rpow_natCast (p : ℝ) (n * N),
        ← Real.rpow_intCast (p : ℝ) (((n * N : ℕ) : ℤ) - t),
        ← Real.rpow_add hp0, ← Real.rpow_add hp0]
      congr 1
      push_cast
      ring
    calc (Nat.card {f : Box p n N // m ≤ discV p n N f} : ℝ)
        ≤ ((n : ℝ) - 1) * (p : ℝ) ^ (((n * N : ℕ) : ℤ) - t) := hstep
      _ = ((n : ℝ) - 1) * ((p : ℝ) ^ (n * N)
            * (p : ℝ) ^ (-(m : ℝ) / (2 * ((n : ℝ) - 1)))
            * (p : ℝ) ^ ((m : ℝ) / (2 * ((n : ℝ) - 1)) - (t : ℝ))) := by
          rw [hrpow_eq]
      _ ≤ ((n : ℝ) - 1) * ((p : ℝ) ^ (n * N)
            * (p : ℝ) ^ (-(m : ℝ) / (2 * ((n : ℝ) - 1))) * (n : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by linarith)
          rw [ht]
          exact tail_wild_shift_bound hn0 m
      _ = tailC n * (p : ℝ) ^ (n * N)
            * (p : ℝ) ^ (-(m : ℝ) / (2 * ((n : ℝ) - 1))) := by
          unfold tailC
          ring
  · -- N < m: the tail event is empty (discV ≤ N)
    haveI : IsEmpty {f : Box p n N // m ≤ discV p n N f} :=
      ⟨fun f => absurd (f.2.trans (discV_le f.1)) (by omega)⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg htailC0 (by positivity))
      (Real.rpow_nonneg hp0.le _)

end T8

end LeanUrat.Scaffold
