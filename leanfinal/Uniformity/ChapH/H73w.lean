/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H01
import Uniformity.ChapH.H02
import Uniformity.ChapH.H06
import Uniformity.ChapH.H73
import Uniformity.ChapH.H74

/-!
# Uniformity.ChapH.H73w — the `μ = 3` stage-σ dictionary: the `[GENHN-HE(μ = 3)]`
# transcription (orchestrator item O-1)

**An H.73-adjacent appendix file, not a blueprint node** (the H09w/H89w precedent; registered
by blueprint AMENDMENT A-H.4, 2026-08-16, unit OM-7). It books CHAP-I's orchestrator item
**O-1**: *"book the `[GENHN-HE(μ = 3)]` transcription (THEOREM HE3.A at `μ = 3`, first-live
`n = 6, 7` — corpus-unconditional, NO owner in any committed chapter; honesty I-11(i))"* —
the missing transcription owner CHAP-I's §3.7 row HYP.81 records, at the home the OM-7
charter names (an H-adjacent witness file), one `μ` above H.73's landed `μ = 2` dictionary.

Source: **THEOREM HE3.A** (the stage-σ recursion, `EFF.HE3.16`, statement verbatim at
`HE3_PROOF_2026-08-08.md` 312–331): at a DECIDED stage leaf of stage type
`τ = {(e_s⁽ⁱ⁾, f_s⁽ⁱ⁾)}` on a composite-stage genre `G`, every `disc ≠ 0` lift factors into
exactly `k` irreducibles with `σ = {(e₁·e_s⁽ⁱ⁾, f₁·f_s⁽ⁱ⁾)}` — *"the σ-decision at a
multiplicity-μ stage is the σ-decision at DEGREE μ over the stage ring R, transported by the
multiplicative re-basing `(e, f) ↦ (e₁e, f₁f)`"*. And **COROLLARY HE3.B** (`EFF.HE3.17`):
`μ ≤ 3` is UNCONDITIONAL — composite-stage-free (no stage-CS event fits: GENIND.A(IV)'s
arithmetic) and HE3-BOX-6-free (branch (ii) needs a side of length `ℓd ≥ 4 > 3`).

## What is transcribed here — and what is NOT (the H.73 trust boundary, verbatim standard)

Exactly H.73's own standard, one `μ` up: *"the σ decision itself is carried by the executable
regression …, not by this file."* This file lands:

* **the transport** `heTransport` — HE3.A's re-basing `(e, f) ↦ (e₁e, f₁f)` as a map on
  stage-type multisets, with its degree law (`heTransport_degree`);
* **the `μ = 3` dictionary** `StageLeaf3` / `stageType3` / `stageSigma3` — the FIVE decided
  `μ = 3` stage types and their σ-blocks relative to the ambient, with degree conservation
  (`stageSigma3_degree`, the H.74 analogue: block degree `3·keyDeg`);
* **five-type exhaustiveness** (`stageType3_complete`): any multiset of pairs `(e_s, f_s)`,
  all entries positive, of stage mass `Σ e_s f_s = 3`, IS one of the five — the μ = 3 case of
  HE3.A's "in bijection with the members of τ_stage" has no sixth shape;
* **the μ = 2 consistency theorem** (`stageSigma_eq_heTransport`): H.73's landed `stageSigma`
  IS `heTransport` at the three `μ = 2` stage types — the corpus's *"GENHN.C … is consumed as
  a CROSS-CHECK only: §S6 re-derives it as the μ = 2 case of HE3.A, so no circularity"*
  (`EFF.HE3.03`), transcribed as a theorem;
* **the HE3.B arithmetic** that makes `μ ≤ 3` unconditional: `no_stageCS_below_four` /
  `composite_stage_free_mu3` (GENIND.A(IV): a stage-CS event forces `μ ≥ 4`),
  `stageCS_strict_descent` (`μ′ ≤ μ/2`), `branch_ii_needs_mu_four` (HE3-BOX-6 branch (ii)
  is unreachable below `μ = 4`), and the first-live degrees `mu3_first_live` (`n = D′μ ≥ 6`,
  sharp at the E3 genre) and `mu4_lives_at_eight` (`μ ≥ 4` composite stages live at `n ≥ 8`).

NOT landed, by design: the σ-DECISION itself (that an actual `p`-adic lift on a decided leaf
takes the dictionary's value) — that is HE3.A's analytic content (§S3–S6 of the note), carried
by the executable teeth: `verification/openmath/om7_cert.py` (this unit: 97 rows GREEN — the
FIRST embedded `n = 7` rows and the first equal-characteristic `μ = 3` rows anywhere in the
HE3 orbit, plus the `D′ = 4, f₁ = 2` and `h = 3` fresh frames) and the note's own HE-SIG
(947 PARI jobs, all five types). Nothing here asserts any particular polynomial has any
particular σ.

## Scope fences (carried unchanged)

* **μ ≥ 4 is NOT touched**: `[GENHN-HE(μ ≥ 4)]` rides HE3-BOX-6 branch (ii) = ledger
  HYP.143 (OM-10's family). This file's dictionary is `μ = 3` only.
* **`GenreDatum` carries `hkey : 2 ≤ e₁f₁`** (H.01: *"else the event is order-1 α/β"*), so
  the `D′ = 1` direct case (LEMMA HE3-4D1, R8-3 — needed by HE3.B's "every `n ≤ 7`" claim at
  linear keys) is OUTSIDE this file's grammar, exactly as it is outside H.01's: at `D′ = 1`
  the read is the classical order-1 Newton/Hensel read, owned by the order-1 layer.
* **Chapter E's trap E-3 is unaffected**: E still carries `hσ₃`/`BLOCKED: HYP.81` fields and
  still never DECIDES a `μ ≥ 3` σ. What changes is only that CHAP-I's I.06 carrier now has a
  named transcription owner for its `μ = 3` slice.
* **HYP.81 stays CARRY** as a Display-A conjunct; its `μ = 3` slice is now owned + toothed,
  its `μ ≥ 4` slice rides HYP.143. No conjunct is weakened or discharged by this file.

DEPENDS: H.01 (`GenreDatum`) · H.02 (`keyDeg`) · H.73 (`StageLeaf`, `stageSigma`) ·
H.74 (`stageSigma_degree`, gate cross-check only) · landed `FactorizationType`.

SOURCE: `EFF.HE3.16` (THEOREM HE3.A) · `EFF.HE3.17` (COROLLARY HE3.B + the strict-descent
and branch-(ii) arithmetic, reproduced by the compiler's own rule-22 audit) · `EFF.HE3.03`
(the no-circularity cross-check) · ledger HYP.81 (v3 scope split) · CHAP-I I.06 + O-1.

## Status

Sorry-free, axiom-free (Lean core only). Gate section + axiom print at the bottom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-! ## 1. The transport — HE3.A's multiplicative re-basing `(e, f) ↦ (e₁e, f₁f)` -/

/-- **HE3.A's transport.** The σ-block of a decided stage read of type `τ` (a multiset of
inner pairs `(e_s, f_s)`), re-based multiplicatively to the ambient genre `G`:
`(e_s, f_s) ↦ (e₁·e_s, f₁·f_s)`. This is the display's `σ(f) = {(e₁e_s⁽ⁱ⁾, f₁f_s⁽ⁱ⁾)}_i`
as a function of the stage type. -/
def heTransport (G : GenreDatum) (τ : Multiset (ℕ × ℕ)) : FactorizationType :=
  ⟨τ.map fun p => (G.e₁ * p.1, G.f₁ * p.2)⟩

/-- The stage mass `Σ e_s·f_s` of a stage type. -/
def stageMass (τ : Multiset (ℕ × ℕ)) : ℕ :=
  (τ.map fun p => p.1 * p.2).sum

/-- **The transport's degree law**: the transported block has degree `keyDeg · stageMass τ`
(= `D′·μ` at a multiplicity-`μ` type) — HE3.A's per-factor degree `D′e_s f_s`, summed. -/
theorem heTransport_degree (G : GenreDatum) (τ : Multiset (ℕ × ℕ)) :
    (heTransport G τ).degree = G.keyDeg * stageMass τ := by
  induction τ using Multiset.induction_on with
  | empty => simp [heTransport, stageMass, FactorizationType.degree]
  | cons a s ih =>
    simp only [heTransport, stageMass, FactorizationType.degree, Multiset.map_cons,
      Multiset.sum_cons] at ih ⊢
    rw [ih, GenreDatum.keyDeg]
    ring

/-! ## 2. The `μ = 3` dictionary — the five decided stage types and their σ-blocks -/

/-- The five decided leaf labels of a `μ = 3` stage read (COROLLARY HE3.B's first-live case;
the five types realized and PARI-confirmed by HE-SIG and by `om7_cert.py`):

* `ram3`       — stage type `{(3,1)}`       (one denominator-3 side)
* `inert3`     — stage type `{(1,3)}`       (integer side, irreducible cubic residual)
* `ramSplit`   — stage type `{(1,1),(2,1)}` (a linear label + a denominator-2 side)
* `inertSplit` — stage type `{(1,1),(1,2)}` (a linear label + an irreducible quadratic)
* `split3`     — stage type `{(1,1),(1,1),(1,1)}` (three linear labels — the 3-label type). -/
inductive StageLeaf3 where
  | ram3
  | inert3
  | ramSplit
  | inertSplit
  | split3
  deriving DecidableEq, Fintype

/-- The stage type (multiset of inner `(e_s, f_s)` pairs) of each `μ = 3` leaf. -/
def stageType3 : StageLeaf3 → Multiset (ℕ × ℕ)
  | .ram3       => {(3, 1)}
  | .inert3     => {(1, 3)}
  | .ramSplit   => {(1, 1), (2, 1)}
  | .inertSplit => {(1, 1), (1, 2)}
  | .split3     => {(1, 1), (1, 1), (1, 1)}

/-- **The `μ = 3` dictionary** (THEOREM HE3.A at `μ = 3`, relative to the ambient): the
σ-block of a decided `μ = 3` leaf is its stage type transported by `(e,f) ↦ (e₁e, f₁f)`. -/
def stageSigma3 (G : GenreDatum) (l : StageLeaf3) : FactorizationType :=
  heTransport G (stageType3 l)

/-- Every `μ = 3` stage type has stage mass 3. -/
theorem stageType3_mass (l : StageLeaf3) : stageMass (stageType3 l) = 3 := by
  cases l <;> rfl

/-- **The `μ = 3` dictionary is degree-exhausting** (the H.74 analogue): each of the five
σ-blocks has total degree `3 · keyDeg G = 3e₁f₁`, the block degree of a `μ = 3` stage. -/
theorem stageSigma3_degree (G : GenreDatum) (l : StageLeaf3) :
    (stageSigma3 G l).degree = 3 * G.keyDeg := by
  rw [stageSigma3, heTransport_degree, stageType3_mass]
  ring

/-! ## 3. Five-type exhaustiveness — there is no sixth `μ = 3` shape -/

private lemma mass_zero_iff (τ : Multiset (ℕ × ℕ))
    (hpos : ∀ p ∈ τ, 1 ≤ p.1 ∧ 1 ≤ p.2) (h : stageMass τ = 0) : τ = 0 := by
  induction τ using Multiset.induction_on with
  | empty => rfl
  | cons a s _ =>
    exfalso
    have ha := hpos a (Multiset.mem_cons_self a s)
    have : 1 ≤ a.1 * a.2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp ha.1) (Nat.one_le_iff_ne_zero.mp ha.2))
    simp only [stageMass, Multiset.map_cons, Multiset.sum_cons] at h
    omega

private lemma pair_mul_one (a : ℕ × ℕ) (h : a.1 * a.2 = 1) : a = (1, 1) := by
  have := Nat.eq_one_of_mul_eq_one_left h
  have := Nat.eq_one_of_mul_eq_one_right h
  exact Prod.ext (by omega) (by omega)

private lemma pair_mul_two (a : ℕ × ℕ) (h : a.1 * a.2 = 2) :
    a = (2, 1) ∨ a = (1, 2) := by
  have h1 : a.1 ≤ 2 := Nat.le_of_dvd (by omega) ⟨a.2, h.symm⟩
  have h2 : a.2 ≤ 2 := Nat.le_of_dvd (by omega) ⟨a.1, by rw [Nat.mul_comm]; exact h.symm⟩
  interval_cases h1' : a.1 <;> interval_cases h2' : a.2 <;>
    first
      | (left; exact Prod.ext (by omega) (by omega))
      | (right; exact Prod.ext (by omega) (by omega))

private lemma pair_mul_three (a : ℕ × ℕ) (h : a.1 * a.2 = 3) :
    a = (3, 1) ∨ a = (1, 3) := by
  have h1 : a.1 ≤ 3 := Nat.le_of_dvd (by omega) ⟨a.2, h.symm⟩
  have h2 : a.2 ≤ 3 := Nat.le_of_dvd (by omega) ⟨a.1, by rw [Nat.mul_comm]; exact h.symm⟩
  interval_cases h1' : a.1 <;> interval_cases h2' : a.2 <;>
    first
      | (left; exact Prod.ext (by omega) (by omega))
      | (right; exact Prod.ext (by omega) (by omega))

private lemma mass_one_iff (τ : Multiset (ℕ × ℕ))
    (hpos : ∀ p ∈ τ, 1 ≤ p.1 ∧ 1 ≤ p.2) (h : stageMass τ = 1) :
    τ = {(1, 1)} := by
  induction τ using Multiset.induction_on with
  | empty => simp [stageMass] at h
  | cons a s _ =>
    have ha := hpos a (Multiset.mem_cons_self a s)
    simp only [stageMass, Multiset.map_cons, Multiset.sum_cons] at h
    have hpos' : ∀ p ∈ s, 1 ≤ p.1 ∧ 1 ≤ p.2 :=
      fun p hp => hpos p (Multiset.mem_cons_of_mem hp)
    have h1 : 1 ≤ a.1 * a.2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (by omega) (by omega))
    have hs : stageMass s = 0 := by unfold stageMass; omega
    have ha1 : a.1 * a.2 = 1 := by unfold stageMass at hs; omega
    rw [mass_zero_iff s hpos' hs, pair_mul_one a ha1]
    rfl

private lemma mass_two_iff (τ : Multiset (ℕ × ℕ))
    (hpos : ∀ p ∈ τ, 1 ≤ p.1 ∧ 1 ≤ p.2) (h : stageMass τ = 2) :
    τ = {(2, 1)} ∨ τ = {(1, 2)} ∨ τ = {(1, 1), (1, 1)} := by
  induction τ using Multiset.induction_on with
  | empty => simp [stageMass] at h
  | cons a s _ =>
    have ha := hpos a (Multiset.mem_cons_self a s)
    simp only [stageMass, Multiset.map_cons, Multiset.sum_cons] at h
    have hpos' : ∀ p ∈ s, 1 ≤ p.1 ∧ 1 ≤ p.2 :=
      fun p hp => hpos p (Multiset.mem_cons_of_mem hp)
    have h1 : 1 ≤ a.1 * a.2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (by omega) (by omega))
    have h2 : a.1 * a.2 ≤ 2 := by unfold stageMass at *; omega
    rcases Nat.lt_or_ge (a.1 * a.2) 2 with hlt | hge
    · -- a.1 * a.2 = 1: a = (1,1), s has mass 1
      have ha1 : a.1 * a.2 = 1 := by omega
      have hs : stageMass s = 1 := by unfold stageMass at *; omega
      rw [mass_one_iff s hpos' hs, pair_mul_one a ha1]
      right; right; rfl
    · -- a.1 * a.2 = 2: s has mass 0
      have ha2 : a.1 * a.2 = 2 := by omega
      have hs : stageMass s = 0 := by unfold stageMass at *; omega
      rw [mass_zero_iff s hpos' hs]
      rcases pair_mul_two a ha2 with h' | h' <;> rw [h']
      · left; rfl
      · right; left; rfl

/-- **Five-type exhaustiveness** (81-S1; certified exhaustively in `om7_cert.py` LEG A1):
every multiset of positive pairs with stage mass 3 is one of the five `μ = 3` stage types.
This is the finiteness half of HE3.A's "in bijection with the members of τ_stage" at
`μ = 3`: the dictionary above has no missing row. -/
theorem stageType3_complete (τ : Multiset (ℕ × ℕ))
    (hpos : ∀ p ∈ τ, 1 ≤ p.1 ∧ 1 ≤ p.2) (hmass : stageMass τ = 3) :
    ∃ l : StageLeaf3, τ = stageType3 l := by
  induction τ using Multiset.induction_on with
  | empty => simp [stageMass] at hmass
  | cons a s _ =>
    have ha := hpos a (Multiset.mem_cons_self a s)
    simp only [stageMass, Multiset.map_cons, Multiset.sum_cons] at hmass
    have hpos' : ∀ p ∈ s, 1 ≤ p.1 ∧ 1 ≤ p.2 :=
      fun p hp => hpos p (Multiset.mem_cons_of_mem hp)
    have h1 : 1 ≤ a.1 * a.2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (by omega) (by omega))
    have h3 : a.1 * a.2 ≤ 3 := by unfold stageMass at *; omega
    interval_cases hq : (a.1 * a.2)
    · -- mass 1 head: a = (1,1), tail mass 2
      have hs : stageMass s = 2 := by unfold stageMass at *; omega
      rw [pair_mul_one a hq]
      rcases mass_two_iff s hpos' hs with h' | h' | h' <;> rw [h']
      · exact ⟨.ramSplit, rfl⟩
      · exact ⟨.inertSplit, rfl⟩
      · exact ⟨.split3, rfl⟩
    · -- mass 2 head: tail mass 1 = {(1,1)}
      have hs : stageMass s = 1 := by unfold stageMass at *; omega
      rw [mass_one_iff s hpos' hs]
      rcases pair_mul_two a hq with h' | h' <;> rw [h']
      · exact ⟨.ramSplit, Multiset.cons_swap _ _ _ ▸ rfl⟩
      · exact ⟨.inertSplit, Multiset.cons_swap _ _ _ ▸ rfl⟩
    · -- mass 3 head: tail mass 0
      have hs : stageMass s = 0 := by unfold stageMass at *; omega
      rw [mass_zero_iff s hpos' hs]
      rcases pair_mul_three a hq with h' | h' <;> rw [h']
      · exact ⟨.ram3, rfl⟩
      · exact ⟨.inert3, rfl⟩

/-! ## 4. The `μ = 2` consistency theorem — no circularity with GENHN.C -/

/-- The stage type of each `μ = 2` leaf (H.73's three labels as inner pairs). -/
def mu2Type : StageLeaf → Multiset (ℕ × ℕ)
  | .ram      => {(2, 1)}
  | .twoSided => {(1, 1), (1, 1)}
  | .inert    => {(1, 2)}

/-- **H.73's landed dictionary IS the transport at `μ = 2`** — `EFF.HE3.03`'s *"§S6
re-derives it as the μ = 2 case of HE3.A, so no circularity"*, as a theorem: the `μ = 2`
and `μ = 3` dictionaries are instances of ONE law. -/
theorem stageSigma_eq_heTransport (G : GenreDatum) (l : StageLeaf) :
    stageSigma G l = heTransport G (mu2Type l) := by
  cases l <;>
    · apply FactorizationType.ext
      simp [stageSigma, heTransport, mu2Type, Nat.mul_comm]

/-! ## 5. The HE3.B arithmetic — why `μ ≤ 3` is unconditional -/

/-- **GENIND.A(IV)'s threshold** (COROLLARY HE3.B's displayed arithmetic, rule-22-audited
by the compiler and re-certified in `om7_cert.py` LEG A3): a stage-CS event — inner key
degree `e₁′f₁′ ≥ 2`, inner multiplicity `μ′ ≥ 2`, budget `e₁′f₁′·μ′ ≤ μ` — forces `μ ≥ 4`. -/
theorem no_stageCS_below_four {ek μ' μ : ℕ} (hk : 2 ≤ ek) (hμ' : 2 ≤ μ')
    (hle : ek * μ' ≤ μ) : 4 ≤ μ :=
  le_trans (Nat.mul_le_mul hk hμ') hle

/-- **`μ ≤ 3` is composite-stage-free** (HE3.B, the base case): no stage-CS event fits
inside a multiplicity-3 stage, so the `μ ∈ {2, 3}` proofs need no recursive input. -/
theorem composite_stage_free_mu3 :
    ¬ ∃ ek μ' : ℕ, 2 ≤ ek ∧ 2 ≤ μ' ∧ ek * μ' ≤ 3 := by
  rintro ⟨ek, μ', hk, hμ', hle⟩
  have := no_stageCS_below_four hk hμ' hle
  omega

/-- **Strict descent** (HE3.B's displayed `μ′ ≤ μ/2 < μ`): the recursion of THEOREM HE3.A
is well-founded. -/
theorem stageCS_strict_descent {ek μ' μ : ℕ} (hk : 2 ≤ ek) (hle : ek * μ' ≤ μ) :
    μ' ≤ μ / 2 := by
  have h2 : 2 * μ' ≤ μ := le_trans (Nat.mul_le_mul hk le_rfl) hle
  omega

/-- **HE3-BOX-6 branch (ii) is unreachable at `μ ≤ 3`** (HE3.B's displayed *"it needs a side
with `ℓ ≥ 2` and residual degree ≥ 2, hence length `ℓd ≥ 4 ≤ μ`"*): a ramified base-change
branch needs `μ ≥ 4`, so the `μ = 3` dictionary above carries no HYP.143 conditionality. -/
theorem branch_ii_needs_mu_four {ℓ d μ : ℕ} (hℓ : 2 ≤ ℓ) (hd : 2 ≤ d)
    (hside : ℓ * d ≤ μ) : 4 ≤ μ :=
  le_trans (Nat.mul_le_mul hℓ hd) hside

/-- **First-live degrees** (ledger HYP.81's "first live n = 6"): a composite stage
(`D′ = keyDeg ≥ 2`, H.01's `hkey`) of multiplicity 3 has block degree `n = D′μ ≥ 6`. -/
theorem mu3_first_live (G : GenreDatum) (h3 : G.μ = 3) : 6 ≤ G.keyDeg * G.μ := by
  have := G.hkey
  rw [h3, GenreDatum.keyDeg]
  omega

/-- **The `μ ≥ 4` region lives at `n ≥ 8`** (HE3.B's `n = D′μ ≥ 2·4 = 8` — the reason the
first-live degrees `n = 6, 7` are entirely inside the unconditional `μ = 3` slice). At
`D′ = 1` this arithmetic is vacuous BY GRAMMAR (`hkey`), matching R8-3's LEMMA HE3-4D1:
linear-key stages are order-1 events, outside `GenreDatum`. -/
theorem mu4_lives_at_eight (G : GenreDatum) (h4 : 4 ≤ G.μ) : 8 ≤ G.keyDeg * G.μ := by
  have := G.hkey
  have : 2 * 4 ≤ G.keyDeg * G.μ :=
    Nat.mul_le_mul (by rw [GenreDatum.keyDeg]; omega) h4
  omega

/-! ## 6. The E3 sharpness genre — `n = 6` attained, and the `n = 7` embedded degree -/

/-- The E3 genre `(Q; e₁, f₁, μ; h) = (2; 2, 1, 3; 1)` — HE3's own battery genre, the
sharpness witness for `n = 6` (`om7_cert.py` LEG B runs its `p ∈ {2,3,5}` instances). -/
def genreE3 : GenreDatum where
  Q := 2
  e₁ := 2
  f₁ := 1
  μ := 3
  h := 1
  hQ := by norm_num
  he₁ := by norm_num
  hh := by norm_num
  hkey := by norm_num
  hmul := by norm_num
  hcop := by decide

end Uniformity.Density.Induction

/-! ## 7. GATE — the dictionary fired at the certified genres

Each `example` states a machine-checkable instance tied to a row of the OM-7 battery
(`verification/openmath/om7_cert.py`, VERDICT GREEN) or of HE-SIG. -/

section DictionaryGate

open Uniformity.Density.Induction

-- The five σ-blocks at the E3 genre (LEG B's PARI-confirmed dictionary, (e₁,f₁) = (2,1)):
example : (stageSigma3 genreE3 .ram3).data = {(6, 1)} := by decide
example : (stageSigma3 genreE3 .inert3).data = {(2, 3)} := by decide
example : (stageSigma3 genreE3 .ramSplit).data = {(2, 1), (4, 1)} := by decide
example : (stageSigma3 genreE3 .inertSplit).data = {(2, 1), (2, 2)} := by decide
example : (stageSigma3 genreE3 .split3).data = {(2, 1), (2, 1), (2, 1)} := by decide

-- Sharpness: the first-live degree 6 is ATTAINED at genreE3, and the n = 7 slice is its
-- embedded companion (block + split linear sibling — LEG B's n7 rows):
example : genreE3.keyDeg * genreE3.μ = 6 := by decide
example : genreE3.keyDeg * genreE3.μ + 1 = 7 := by decide

-- The LEG D genre (3; 2, 2, 3; 1) — D′ = 4, f₁ = 2, degree 12: the dictionary rows PARI
-- confirmed at the first f₁ ≥ 2, D′ = 4 frame ever machine-run:
example : (stageSigma3 ⟨3, 2, 2, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by decide⟩ .inertSplit).data = {(2, 2), (2, 4)} := by decide
example : (stageSigma3 ⟨3, 2, 2, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by decide⟩ .ram3).data = {(6, 2)} := by decide

-- Degree conservation at both gate genres (the H.74 analogue, block degree 3·D′):
example : (stageSigma3 genreE3 .split3).degree = 6 := by decide
example : (stageSigma3 ⟨3, 2, 2, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by decide⟩ .inert3).degree = 12 := by decide

-- The μ = 2 dictionary really is the transport's μ = 2 shadow, instance-checked (twoSided
-- at genreE2 0 — H.73's own genre; the theorem covers every genre):
example : stageSigma (genreE2 0) .twoSided = heTransport (genreE2 0) (mu2Type .twoSided) :=
  stageSigma_eq_heTransport (genreE2 0) .twoSided

end DictionaryGate

/-! ## 8. Axiom footprint — Lean core only -/

section AxCheck

#print axioms Uniformity.Density.Induction.heTransport_degree
#print axioms Uniformity.Density.Induction.stageSigma3_degree
#print axioms Uniformity.Density.Induction.stageType3_complete
#print axioms Uniformity.Density.Induction.stageSigma_eq_heTransport
#print axioms Uniformity.Density.Induction.composite_stage_free_mu3
#print axioms Uniformity.Density.Induction.stageCS_strict_descent
#print axioms Uniformity.Density.Induction.branch_ii_needs_mu_four
#print axioms Uniformity.Density.Induction.mu3_first_live
#print axioms Uniformity.Density.Induction.mu4_lives_at_eight

end AxCheck
