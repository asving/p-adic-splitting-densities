/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.ResVal

/-!
# HC1.V8_childResidual — S9w-(i) via the explicit descent carrier (blueprint §10, V8)

V′-KERNEL unit (blueprint §10.1), the DESCENT instance of (†) — the honest §9.5
core: the explicit carrier

  `Rc f := Σ_{j minimizing childW} C(⟨digPrime z̄ (B_j), mem⟩)·T(j·s′ − t′·σ.w B_j)`

(choice-packaged against `ChildResData`'s pins — `hS5′` is the single-slot case
DEFINITIONALLY: `mfun ≡ 0` is CORRECT per §10 Key Finding 2's first bullet, whose
WARRANT DISPLAY is D.7(v)'s D-map definition, MOVES 2364–2367: "D(x) := R(x)
mod ψ ∈ F′" — reduction mod ψ IS evaluation at the root z̄ (F′ = F[z]/(ψ) ≅ F(z̄)),
i.e. `digPrime` itself, so the child digit is DEFINED as the raw parent-residual
evaluation and no alignment twist exists; the D.7(vi)–(vii) excerpt alone does not
state this (VPRIME_CONFIRM gap 2, closed 2026-07-28) — the
strip mismatch was hS6a's transcription, never the pin; `hRPhi` the slot-1 case)
satisfies the FULL `ChildResLaws`:

* **(a)** additive legs hR0/hRne/hRadd/hRlt/hRneg + w_jump: slot-min ties (S2's
  hSMW), position-injectivity across tied slots, parent hRadd/hRlt slotwise;
  hRne needs D.3(d) (ψ ∤ R(B), width < g — on disk as `L3_digPrime_nonzero`)
  for digit nonvanishing and F′[z^{±1}]-domain for sums.  difficulty: medium.
* **(b)** hRmul: the bilinear slot expansion; per-pair monic division
  `B_j·B″_k = Q_{jk}·Φ̂ + R_{jk}`; `L3_DIV` gives `R_{jk} ≠ 0`, exact weight,
  digit product; Q-terms strictly deeper by th's (I-aug) (D.7(i) verbatim);
  tied (j,k)-pairs land at ONE position `(j+k)s′ − t′(σ.w B_j + σ.w B″_k)` and
  SUM as the Laurent product's convolution coefficient; a vanishing convolution
  coefficient = a parent-residual cancellation = the SAME zero on both sides
  (the D.1(b) δ-calculus, MOVES 2305–2313).  difficulty: HARD, every
  ingredient displayed + on disk.
* **(c)** w_strict (S9w conjunct (ii)): S9a's in-file hwult pattern + strict
  slot domination.  difficulty: short.

DEMOTION NOTE (§10): in the TOTAL (evaluated) V′ coordinate the carry cocycle is
INVISIBLE — z̄^{e·⌊k/e⌋+ρ} recombines, positions add exactly, and hRmul needs
only `L3_DIV`'s evaluated identity.  The proved D-layer (D1–D8, `cmul`, `digD`)
is the GRADED certificate of the alignment's well-definedness; it is NOT
load-bearing here.  "hRmul via D7's cmul law + L3_DIV" reads, post-design:
via L3_DIV; D7 certifies.

moves_ref: D.6 Lemma DIV (MOVES 2299–2322), D.7(i)–(iii) (2331–2352),
D.7(v) D-map definition = the `mfun ≡ 0` warrant (2364–2367; injectivity
2388–2390), D.7(vi)–(vii) normalization (2392–2418). deps: V0 (shape only), S2, S3, L3_DIV,
L3_liftMonic, L3_digPrime_nonzero, L4_TRANSii/iii, th.  **NOT dependent on V5**
(the carrier + laws never mention hS6a).  UNBLOCKS: S9w → S9r (already reduced),
the S9a census's carrier legs; kills the S9w cone's sorryAx.

**P-PHASE COMPLETE (2026-07-28, second escalation): V8a, V8b, V8c ALL PROVED —
zero sorry, Lean-core footprint on every theorem including the capstone.**
The construction: the explicit carrier `v8Rc` ((†) on THE Fact-A/B development,
`0` at `f = 0`) + the private **graded-residue calculus `v8gr`** (the D.1(b) tie
laws — parent hRadd/hRlt + StageCore w_strict/w_jump/R_neg — packaged as one
additive map on the zero-or-`w ≥ ω` domain), which reduces every per-slot digit
claim to a two-line computation.  hRmul = the L4_TRANSiii product development
`Cdev` (re-derived at digit level; those helpers are private) + `L3_DIV`
per-pair remainders + (I-aug) depth for carried quotients + the `v8gr` slot
computation + the Laurent convolution regroup (`Finset.sum_fiberwise_of_maps_to`);
a vanishing convolution coefficient is the SAME zero on both sides via D.3(d)
digit-nonvanishing (the D.1(b) δ-calculus, exactly as the header route displays).
V8c was proved at the first escalation and MOVED above V8a/V8b (its strict law
feeds V8b's hRlt leg through `V8c_wStrict`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open scoped Classical in
/-- **The explicit descent carrier display** (§10 V8, the (†) formula at the descent
instance): on every nonzero f with Φ̂-development data, the carrier value is the
minimizing-slot sum `Σ_j C(dig′(B_j))·T(j·s′ − t′·σ.w B_j)` — digits the parent
ψ-digits (z̄-evaluation, landing in K′ = K⟮z̄⟯), positions the (S5′) law at the
child pair.  Stated as a Prop ON a carrier (the choice-packaging precedent);
well-defined across developments by Fact B uniqueness. -/
def ExplicitDescentCarrier {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
    {zbar : Fˣ} {s' t' : ℤ} (D : ChildResData σ Φhat e' h' zbar s' t') : Prop :=
  ∀ (f : Polynomial ℤ_[p]), f ≠ 0 → ∀ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ),
    IsDevelopment Φhat f B N →
    ∃ cdig : ℕ → ↥(σ.nextField zbar),
      (∀ j, ((cdig j : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar (B j)) ∧
      D.Rc f = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0 ∧
          (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f),
        LaurentPolynomial.C (cdig j) *
          LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))

/-- **V8b ATOM 1 (tied-slot position injectivity — the hRne crux):** on childW-tied
slots, the child position map `j ↦ j·s′ − t′·w_j` is injective (the Bézout collapse:
`d = d·(e′s′ + h′t′)` telescopes to 0 through the tie and position equations).
Escalation round 2026-07-28; PROVED. -/
theorem V8_tiedPos_inj {e' h' : ℕ} {s' t' : ℤ}
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    {j₁ j₂ : ℕ} {w₁ w₂ : ℤ}
    (htie : (e' : ℤ) * w₁ + (j₁ : ℤ) * (h' : ℤ) = (e' : ℤ) * w₂ + (j₂ : ℤ) * (h' : ℤ))
    (hpos : (j₁ : ℤ) * s' - t' * w₁ = (j₂ : ℤ) * s' - t' * w₂) :
    j₁ = j₂ ∧ (e' : ℤ) * w₁ = (e' : ℤ) * w₂ := by
  have hjZ : (j₁ : ℤ) = (j₂ : ℤ) := by
    linear_combination ((j₂ : ℤ) - (j₁ : ℤ)) * hbez' + (e' : ℤ) * hpos + t' * htie
  have hj : j₁ = j₂ := by exact_mod_cast hjZ
  refine ⟨hj, ?_⟩
  rw [hjZ] at htie
  linarith

/-- **V8b ATOM 2 (digit membership):** the z̄-evaluation of any current-field Laurent
polynomial lands in the child field `K′ = K⟮z̄⟯` (`LaurentPolynomial.induction_on`:
constants via `K ≤ K′`, the `T ±1` steps via `z̄, z̄⁻¹ ∈ K′`).
Escalation round 2026-07-28; PROVED. -/
theorem V8_eval₂_mem_nextField (σ : Stage p F) (zbar : Fˣ)
    (l : LaurentPolynomial ↥σ.K) :
    LaurentPolynomial.eval₂ σ.K.subtype zbar l ∈ σ.nextField zbar := by
  have hz : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
  induction l using LaurentPolynomial.induction_on with
  | h_C a =>
      rw [LaurentPolynomial.eval₂_C]
      exact σ.le_nextField zbar a.2
  | h_add hp hq =>
      rw [map_add]
      exact add_mem hp hq
  | h_C_mul_T n a ih =>
      have hsplit : (LaurentPolynomial.C a * LaurentPolynomial.T ((n : ℤ) + 1)) =
          (LaurentPolynomial.C a * LaurentPolynomial.T (n : ℤ)) * LaurentPolynomial.T 1 := by
        rw [mul_assoc, ← LaurentPolynomial.T_add]
      rw [hsplit, map_mul, LaurentPolynomial.eval₂_T]
      exact mul_mem ih (by simpa using hz)
  | h_C_mul_T_Z n a ih =>
      have hsplit : (LaurentPolynomial.C a * LaurentPolynomial.T (-(n : ℤ) - 1)) =
          (LaurentPolynomial.C a * LaurentPolynomial.T (-(n : ℤ))) *
            LaurentPolynomial.T (-1) := by
        rw [mul_assoc, ← LaurentPolynomial.T_add]
        ring_nf
      rw [hsplit, map_mul, LaurentPolynomial.eval₂_T]
      refine mul_mem ih ?_
      rw [zpow_neg_one, Units.val_inv_eq_inv_val]
      exact inv_mem hz

/-- **V8b ATOM 3 (the digit-unit lift — hS5′/hRne's scalar):** for a nonzero
sub-Φ̂-degree coefficient `B`, the parent ψ-digit `dig′(B)` is realized by a UNIT of
the child field `K′` (membership by atom 2; nonvanishing by `L3_digPrime_nonzero`,
D.3(d)).  Escalation round 2026-07-28; PROVED. -/
theorem V8_digitUnit (σ : Stage p F)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBd : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ∃ c' : (↥(σ.nextField zbar))ˣ,
      ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := by
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
  have hmem : σ.digPrime zbar B ∈ σ.nextField zbar :=
    V8_eval₂_mem_nextField σ zbar (σ.R B)
  have hne : σ.digPrime zbar B ≠ 0 :=
    L3_digPrime_nonzero σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar B hB hBd
  have hne' : (⟨σ.digPrime zbar B, hmem⟩ : ↥(σ.nextField zbar)) ≠ 0 := by
    intro h0
    exact hne (congrArg Subtype.val h0)
  exact ⟨Units.mk0 _ hne', rfl⟩

/-! ### P-phase infrastructure (2026-07-28 escalation; blueprint §10.1 V8 P-phase)

Private helpers, in dependency order: parent w-arithmetic (the `L4_TRANSiii`
private-helper pattern, re-derived here since those are `private`); the
**graded-residue calculus** `v8gr` — the D.1(b) tie laws (`hRadd`/`hRlt` +
StageCore's `w_strict`/`w_jump`/`R_neg`) packaged as ONE additive map on the
"zero-or-`w ≥ ω`" domain, which is what turns every per-slot digit claim into a
two-line computation; development plumbing (sum/neg/single-slot/key
developments); digits landing in `K′` (`v8cdig`); and the explicit carrier
`v8Rc` (the (†) formula) with its development-independence spec `v8Rc_eq`
(Fact B) and the position-injectivity nonvanishing `v8dsum_ne`. -/

/-! SYN-M8 record (2026-07-30, C1 cluster): `v8w_one`/`v8w_neg`/`v8sum_w_ge` deleted;
call sites re-pointed at `Moves.ResVal.w_one/w_neg` and `ult_sum_ge σ.w σ.hwult`
(the ι-generic bare form; statement-identical specialization, SYN-E0 §3 VAR-G). -/
section V8Infra

variable (σ : Stage p F)
/-- "zero, or `w`-deep at least `ω`" — the domain of the level-`ω` graded residue. -/
private def v8Deep (ω : ℤ) (x : Polynomial ℤ_[p]) : Prop := x = 0 ∨ ω ≤ σ.w x

open scoped Classical in
/-- **the graded residue at level `ω`**: `R x` on the `w = ω` stratum, `0` elsewhere. -/
private noncomputable def v8gr (ω : ℤ) (x : Polynomial ℤ_[p]) : LaurentPolynomial ↥σ.K :=
  if x ≠ 0 ∧ σ.w x = ω then σ.R x else 0

private lemma v8gr_zero (ω : ℤ) : v8gr σ ω 0 = 0 := by
  unfold v8gr; rw [if_neg]; rintro ⟨h, -⟩; exact h rfl

private lemma v8gr_eq {ω : ℤ} {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hw : σ.w x = ω) :
    v8gr σ ω x = σ.R x := by
  unfold v8gr; rw [if_pos ⟨hx, hw⟩]

private lemma v8gr_deep {ω : ℤ} {x : Polynomial ℤ_[p]} (hw : σ.w x ≠ ω) :
    v8gr σ ω x = 0 := by
  unfold v8gr; rw [if_neg]; rintro ⟨-, h⟩; exact hw h

private lemma v8gr_spec {ω : ℤ} {x : Polynomial ℤ_[p]} (h : v8gr σ ω x ≠ 0) :
    x ≠ 0 ∧ σ.w x = ω := by
  by_contra hcon
  exact h (by unfold v8gr; rw [if_neg hcon])

/-- The graded residue is additive on the `Deep ω` domain (closed under `+`): the
D.1(b) tie calculus in one lemma — `hRadd` at ties, `hRlt`/`w_strict` at strict
drops, `w_jump` at weight jumps, `R_neg` at exact cancellations. -/
private lemma v8gr_add (hσ : StageCore σ) {ω : ℤ} {x y : Polynomial ℤ_[p]}
    (hx : v8Deep σ ω x) (hy : v8Deep σ ω y) :
    v8Deep σ ω (x + y) ∧ v8gr σ ω (x + y) = v8gr σ ω x + v8gr σ ω y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, v8gr_zero, zero_add]; exact ⟨hy, rfl⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, v8gr_zero, add_zero]; exact ⟨hx, rfl⟩
  have hxw : ω ≤ σ.w x := hx.resolve_left hx0
  have hyw : ω ≤ σ.w y := hy.resolve_left hy0
  rcases eq_or_ne (x + y) 0 with hxy0 | hxy0
  · -- exact cancellation: `y = −x`
    have hyx : y = -x := eq_neg_of_add_eq_zero_right hxy0
    refine ⟨Or.inl hxy0, ?_⟩
    rw [hxy0, v8gr_zero]
    rcases eq_or_ne (σ.w x) ω with hwx | hwx
    · have hwy : σ.w y = ω := by rw [hyx, ResVal.w_neg σ x hx0]; exact hwx
      rw [v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy, hyx, hσ.R_neg, add_neg_cancel]
    · have hwy : σ.w y ≠ ω := by rw [hyx, ResVal.w_neg σ x hx0]; exact hwx
      rw [v8gr_deep σ hwx, v8gr_deep σ hwy, add_zero]
  have hult := σ.hwult x y hx0 hy0 hxy0
  have hDeep : v8Deep σ ω (x + y) := Or.inr (le_trans (le_min hxw hyw) hult)
  refine ⟨hDeep, ?_⟩
  rcases eq_or_ne (σ.w x) ω with hwx | hwx
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- both at level ω: hRadd at a tie, w_jump at a jump
      rcases eq_or_ne (σ.w (x + y)) ω with hwxy | hwxy
      · rw [v8gr_eq σ hxy0 hwxy, v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy]
        exact σ.hRadd x y hx0 hy0 hxy0 (by rw [hwx, hwy]) (by rw [hwxy, hwx])
      · have hwge : ω ≤ σ.w (x + y) := le_trans (le_min hxw hyw) hult
        have hj : σ.w x < σ.w (x + y) := by omega
        rw [v8gr_deep σ hwxy, v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy]
        exact (hσ.w_jump x y hx0 hy0 hxy0 (by rw [hwx, hwy]) hj).symm
    · -- x at ω, y strictly deeper: hRlt + w_strict
      have hlt : σ.w x < σ.w y := by omega
      have hws := hσ.w_strict x y hx0 hy0 hlt
      rw [v8gr_eq σ hxy0 (by rw [hws, hwx]), v8gr_eq σ hx0 hwx, v8gr_deep σ hwy, add_zero]
      exact σ.hRlt x y hx0 hy0 hxy0 hlt
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- y at ω, x strictly deeper: symmetric
      have hlt : σ.w y < σ.w x := by omega
      have hws := hσ.w_strict y x hy0 hx0 hlt
      have hyx0 : y + x ≠ 0 := by rwa [add_comm]
      rw [v8gr_deep σ hwx, zero_add, add_comm x y,
        v8gr_eq σ hyx0 (by rw [hws, hwy]), v8gr_eq σ hy0 hwy]
      exact σ.hRlt y x hy0 hx0 hyx0 hlt
    · -- both strictly deeper
      have hgt : ω < σ.w (x + y) := by
        have h1 : ω < σ.w x := by omega
        have h2 : ω < σ.w y := by omega
        exact lt_of_lt_of_le (lt_min h1 h2) hult
      rw [v8gr_deep σ (by omega : σ.w (x + y) ≠ ω), v8gr_deep σ hwx, v8gr_deep σ hwy, add_zero]

/-- finite-sum graded additivity. -/
private lemma v8gr_sum (hσ : StageCore σ) {ω : ℤ} {ι : Type*} (S : Finset ι)
    (a : ι → Polynomial ℤ_[p]) (h : ∀ j ∈ S, v8Deep σ ω (a j)) :
    v8Deep σ ω (∑ j ∈ S, a j) ∧ v8gr σ ω (∑ j ∈ S, a j) = ∑ j ∈ S, v8gr σ ω (a j) := by
  classical
  revert h
  induction S using Finset.induction with
  | empty =>
    intro h
    simp only [Finset.sum_empty]
    exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
  | insert i T hiT ih =>
    intro h
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
    obtain ⟨hD, hE⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨hD', hE'⟩ := v8gr_add σ hσ (h i (Finset.mem_insert_self i T)) hD
    exact ⟨hD', by rw [hE', hE]⟩

/-- developments add slotwise. -/
private lemma v8dev_add {Φ : Polynomial ℤ_[p]} {f g : Polynomial ℤ_[p]}
    {B B' : ℕ → Polynomial ℤ_[p]} {N N' : ℕ}
    (h : IsDevelopment Φ f B N) (h' : IsDevelopment Φ g B' N') :
    IsDevelopment Φ (f + g) (fun j => B j + B' j) (max N N') := by
  refine ⟨fun j => lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (h.1 j) (h'.1 j)),
    fun j hj => ?_, ?_⟩
  · show B j + B' j = 0
    rw [h.2.1 j (le_trans (le_max_left _ _) hj), h'.2.1 j (le_trans (le_max_right _ _) hj),
      add_zero]
  · have hf2 : f = ∑ j ∈ Finset.range (max N N'), B j * Φ ^ j := by
      rw [h.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))) ?_
      intro j _ hj
      rw [h.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    have hg2 : g = ∑ j ∈ Finset.range (max N N'), B' j * Φ ^ j := by
      rw [h'.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))) ?_
      intro j _ hj
      rw [h'.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    rw [hf2, hg2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_mul])

/-- developments negate slotwise. -/
private lemma v8dev_neg {Φ : Polynomial ℤ_[p]} {f : Polynomial ℤ_[p]}
    {B : ℕ → Polynomial ℤ_[p]} {N : ℕ} (h : IsDevelopment Φ f B N) :
    IsDevelopment Φ (-f) (fun j => -(B j)) N := by
  refine ⟨fun j => by rw [Polynomial.degree_neg]; exact h.1 j,
    fun j hj => by show -(B j) = 0; rw [h.2.1 j hj, neg_zero], ?_⟩
  calc -f = -∑ j ∈ Finset.range N, B j * Φ ^ j := by rw [← h.2.2]
    _ = ∑ j ∈ Finset.range N, -(B j * Φ ^ j) := by rw [Finset.sum_neg_distrib]
    _ = ∑ j ∈ Finset.range N, -(B j) * Φ ^ j :=
        Finset.sum_congr rfl fun j _ => (neg_mul (B j) (Φ ^ j)).symm

/-- the single-slot development of a coefficient. -/
private lemma v8dev_single {Φ B : Polynomial ℤ_[p]} (hΦ : Φ ≠ 0) (hB : inC Φ B) :
    IsDevelopment Φ B (fun j => if j = 0 then B else 0) 1 := by
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h0 : j = 0
    · subst h0
      simpa using (show B.degree < Φ.degree from hB)
    · simpa [h0] using hbot
  · show (if j = 0 then B else 0) = 0
    rw [if_neg (by omega : j ≠ 0)]
  · simp

/-- the 2-slot development of the key itself: `Φ = 0·Φ⁰ + 1·Φ¹`. -/
private lemma v8dev_key {Φ : Polynomial ℤ_[p]} (hmon : Φ.Monic) (hd1 : 1 ≤ Φ.natDegree) :
    IsDevelopment Φ Φ (fun j => if j = 1 then 1 else 0) 2 := by
  have hΦ : Φ ≠ 0 := hmon.ne_zero
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  have hdpos : (0 : WithBot ℕ) < Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ]
    exact_mod_cast hd1
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h1 : j = 1
    · simpa [h1, Polynomial.degree_one] using hdpos
    · simpa [h1] using hbot
  · show (if j = 1 then 1 else 0) = 0
    rw [if_neg (by omega : j ≠ 1)]
  · simp [Finset.sum_range_succ]

/-- attained slot minima are unique. -/
private lemma v8slotMin_unique {m m' : ℤ} {N : ℕ} {sw : ℕ → ℤ} {nz : ℕ → Prop}
    (h : SlotMinAttained m N sw nz) (h' : SlotMinAttained m' N sw nz) : m = m' := by
  obtain ⟨j, hj, hjnz, hje⟩ := h.2
  obtain ⟨k, hk, hknz, hke⟩ := h'.2
  have h1 := h.1 k hk hknz
  have h2 := h'.1 j hj hjnz
  omega

/-- every `z̄`-evaluation of a `↥K`-Laurent polynomial lands in `K′ = K⟮z̄⟯`. -/
private lemma v8dig_mem (zbar : Fˣ) (q : LaurentPolynomial ↥σ.K) :
    LaurentPolynomial.eval₂ σ.K.subtype zbar q ∈ σ.nextField zbar := by
  induction q using LaurentPolynomial.induction_on' with
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | C_mul_T n a =>
    rw [LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
    have hz : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
    exact mul_mem (σ.le_nextField zbar (SetLike.coe_mem a)) (zpow_mem hz n)

/-- the parent digit as an element of `K′`. -/
private noncomputable def v8cdig (zbar : Fˣ) (B : Polynomial ℤ_[p]) :
    ↥(σ.nextField zbar) :=
  ⟨σ.digPrime zbar B, v8dig_mem σ zbar (σ.R B)⟩

private lemma v8cdig_coe (zbar : Fˣ) (B : Polynomial ℤ_[p]) :
    ((v8cdig σ zbar B : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := rfl

/-- digit multiplicativity on nonzero inputs (the L3_DIV (★) step). -/
private lemma v8dig_mul (zbar : Fˣ) {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    σ.digPrime zbar (f * g) = σ.digPrime zbar f * σ.digPrime zbar g := by
  simp only [Stage.digPrime]
  rw [σ.hRmul f g hf hg, map_mul]

open scoped Classical in
/-- the tied-slot sum: digits at `childW`-minimizing slots, positions per the child
Bézout pair — the body of the (†) carrier on one development. -/
private noncomputable def v8dsum (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
    (s' t' : ℤ) (m : ℤ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) :
    LaurentPolynomial ↥(σ.nextField zbar) :=
  ∑ j ∈ (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m),
    LaurentPolynomial.C (v8cdig σ zbar (B j)) *
      LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))

open scoped Classical in
/-- **the explicit descent carrier** (§10 (†), descent instance), as a total function:
the tied-slot sum of THE development (Fact A/B) at the `childW` value; `0` at `f = 0`. -/
private noncomputable def v8Rc (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
    (s' t' : ℤ) (f : Polynomial ℤ_[p]) : LaurentPolynomial ↥(σ.nextField zbar) :=
  if hf : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment Φhat f BN.1 BN.2
  then v8dsum σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f) hf.2.choose.1 hf.2.choose.2
  else 0

private lemma v8Rc_zero (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) (s' t' : ℤ) :
    v8Rc σ Φhat e' h' zbar s' t' 0 = 0 := by
  unfold v8Rc
  rw [dif_neg]
  rintro ⟨h, -⟩; exact h rfl

/-- `v8dsum` ignores padding beyond the last nonzero slot. -/
private lemma v8dsum_ext (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) (s' t' : ℤ)
    (m : ℤ) {B : ℕ → Polynomial ℤ_[p]} {N N₂ : ℕ} (hN : N ≤ N₂)
    (hvan : ∀ j, N ≤ j → B j = 0) :
    v8dsum σ Φhat e' h' zbar s' t' m B N₂ = v8dsum σ Φhat e' h' zbar s' t' m B N := by
  unfold v8dsum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hBj, he⟩
    refine ⟨?_, hBj, he⟩
    by_contra hc
    exact hBj (hvan j (le_of_not_gt hc))
  · rintro ⟨hj, hBj, he⟩
    exact ⟨lt_of_lt_of_le hj hN, hBj, he⟩

/-- **the carrier spec** (Fact B independence): on any development of a nonzero `f`,
`v8Rc f` IS the tied-slot sum of that development. -/
private lemma v8Rc_eq {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) {f : Polynomial ℤ_[p]} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hf : f ≠ 0) (hdev : IsDevelopment Φhat f B N) :
    v8Rc σ Φhat e' h' zbar s' t' f
      = v8dsum σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f) B N := by
  have hex : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment Φhat f BN.1 BN.2 :=
    ⟨hf, ⟨(B, N), hdev⟩⟩
  unfold v8Rc
  rw [dif_pos hex]
  have hdev₀ : IsDevelopment Φhat f hex.2.choose.1 hex.2.choose.2 := hex.2.choose_spec
  have hBeq : hex.2.choose.1 = B := funext (L0_FactB_unique Φhat hmon f hdev₀ hdev)
  rw [← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left hex.2.choose.2 N) hdev₀.2.1, hBeq,
    v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right hex.2.choose.2 N) hdev.2.1]

/-- position injectivity across tied slots: `e′·pos(j) = j − t′·m`, so positions
determine slots (Bézout). -/
private lemma v8pos_inj {e' h' : ℕ} {s' t' m : ℤ}
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) {j k : ℕ} {wj wk : ℤ}
    (hj : (e' : ℤ) * wj + (j : ℤ) * (h' : ℤ) = m)
    (hk : (e' : ℤ) * wk + (k : ℤ) * (h' : ℤ) = m)
    (hp : (j : ℤ) * s' - t' * wj = (k : ℤ) * s' - t' * wk) : j = k := by
  have h1 : (e' : ℤ) * ((j : ℤ) * s' - t' * wj) = (j : ℤ) - t' * m := by
    linear_combination (-t') * hj + (j : ℤ) * hbez'
  have h2 : (e' : ℤ) * ((k : ℤ) * s' - t' * wk) = (k : ℤ) - t' * m := by
    linear_combination (-t') * hk + (k : ℤ) * hbez'
  rw [hp] at h1
  have h3 : (j : ℤ) = (k : ℤ) := by linarith [h1.symm.trans h2]
  exact_mod_cast h3

/-- the tied-slot sum is nonzero once one tied slot exists: distinct positions
(`v8pos_inj`), nonzero digits (D.3(d) via `L3_digPrime_nonzero`). -/
private lemma v8dsum_ne (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ) (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    {m : ℤ} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hdeg : ∀ j, (B j).degree < Φhat.degree)
    {j₀ : ℕ} (hj₀N : j₀ < N) (hj₀nz : B j₀ ≠ 0)
    (hj₀m : (e' : ℤ) * σ.w (B j₀) + (j₀ : ℤ) * (h' : ℤ) = m) :
    v8dsum σ Φhat e' h' zbar s' t' m B N ≠ 0 := by
  classical
  have hdigne : ∀ j, B j ≠ 0 → σ.digPrime zbar (B j) ≠ 0 := by
    intro j hj
    refine L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar (B j) hj ?_
    rw [← hΦd]
    exact Polynomial.natDegree_lt_natDegree hj (hdeg j)
  intro hcon
  unfold v8dsum at hcon
  set T := (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m) with hT
  have hj₀T : j₀ ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj₀N, hj₀nz, hj₀m⟩
  simp_rw [← LaurentPolynomial.single_eq_C_mul_T] at hcon
  have hcon' : (∑ j ∈ T, Finsupp.single ((j : ℤ) * s' - t' * σ.w (B j))
      (v8cdig σ zbar (B j)) : ℤ →₀ ↥(σ.nextField zbar)) = 0 := hcon
  have happ := DFunLike.congr_fun hcon' ((j₀ : ℤ) * s' - t' * σ.w (B j₀))
  rw [Finset.sum_apply'] at happ
  simp only [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at happ
  rw [Finset.sum_eq_single j₀] at happ
  · rw [if_pos rfl] at happ
    exact hdigne j₀ hj₀nz (by simpa [v8cdig, Subtype.ext_iff] using happ)
  · intro b hb hbne
    rw [if_neg]
    intro hpe
    have hbT := hb
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hbT
    exact hbne (v8pos_inj hbez' hbT.2.2 hj₀m hpe)
  · intro hnot
    exact absurd hj₀T hnot

/-! #### slot-value ↔ parent-weight converters (the `e′ > 0` cancellations) -/

private lemma v8Deep_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : x = 0 ∨ m ≤ (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ)) : v8Deep σ ω x := by
  rcases hx with h | h
  · exact Or.inl h
  · right
    have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
    have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * σ.w x := by linarith
    exact le_of_mul_le_mul_left h2 he0

private lemma v8w_eq_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) = m) : σ.w x = ω := by
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  have h2 : (e' : ℤ) * σ.w x = (e' : ℤ) * ω := by linarith
  exact mul_left_cancel₀ he0.ne' h2

private lemma v8w_ne_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) ≠ m) : σ.w x ≠ ω := by
  intro hc
  exact hx (by rw [hc]; exact hω)

/-! #### `childW` at the distinguished elements -/

/-- `childW` at the key: `w′(Φ̂) = h′` (slot-1 arithmetic on the 2-slot development). -/
private lemma v8cw_key {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w) :
    childW σ Φhat e' h' Φhat = (h' : ℤ) := by
  have hatt := hSMW Φhat _ 2 hmon.ne_zero (v8dev_key hmon hd1)
  refine v8slotMin_unique hatt ⟨?_, ?_⟩
  · intro j hj hnz
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with rfl | rfl
    · exfalso
      apply hnz
      show (if 0 = 1 then (1 : Polynomial ℤ_[p]) else 0) = 0
      rw [if_neg (by omega : (0 : ℕ) ≠ 1)]
    · show (h' : ℤ) ≤ (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, ResVal.w_one σ]
      push_cast
      omega
  · refine ⟨1, by omega, ?_, ?_⟩
    · show (if 1 = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0
      rw [if_pos rfl]
      exact one_ne_zero
    · show (h' : ℤ) = (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, ResVal.w_one σ]
      push_cast
      omega

/-- `childW` is negation-invariant. -/
private lemma v8cw_neg {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    childW σ Φhat e' h' (-f) = childW σ Φhat e' h' f := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  have hatt := hSMW f B N hf hdev
  have hattn := hSMW (-f) _ N (neg_ne_zero.mpr hf) (v8dev_neg hdev)
  have hattn' : SlotMinAttained (childW σ Φhat e' h' (-f)) N
      (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0) := by
    obtain ⟨hlo, jj, hjj, hjjnz, hjje⟩ := hattn
    have hjjB : B jj ≠ 0 := fun h0 => hjjnz (show -(B jj) = 0 by rw [h0, neg_zero])
    constructor
    · intro j hj hnz
      have h := hlo j hj (show -(B j) ≠ 0 from neg_ne_zero.mpr hnz)
      simpa only [ResVal.w_neg σ (B j) hnz] using h
    · exact ⟨jj, hjj, hjjB, by simpa only [ResVal.w_neg σ (B jj) hjjB] using hjje⟩
  exact v8slotMin_unique hattn' hatt

/-- `dig′(1) = 1` (idempotent nonzero element of the field `F`). -/
private lemma v8dig_one (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg1 : 1 ≤ g) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) :
    σ.digPrime zbar (1 : Polynomial ℤ_[p]) = 1 := by
  have hpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hne : σ.digPrime zbar (1 : Polynomial ℤ_[p]) ≠ 0 :=
    L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar 1 one_ne_zero (by simpa using hpos)
  have hsq : σ.digPrime zbar (1 : Polynomial ℤ_[p]) * σ.digPrime zbar 1
      = σ.digPrime zbar 1 * 1 := by
    rw [← v8dig_mul σ zbar one_ne_zero one_ne_zero, mul_one, mul_one]
  exact mul_left_cancel₀ hne hsq

/-! #### the two `ChildResData` pins for the explicit carrier -/

/-- the D.3(b) key pin: `v8Rc(Φ̂) = z^{s′}`. -/
private lemma v8Rc_phi (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg1 : 1 ≤ g) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w) :
    v8Rc σ Φhat e' h' zbar s' t' Φhat = LaurentPolynomial.T s' := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hΦne (v8dev_key hmon hd1)]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_one]
  have h0cond : ¬((if (0 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 1 then 1 else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' Φhat) := by
    rintro ⟨h0, -⟩
    exact h0 (by rw [if_neg (by omega : (0 : ℕ) ≠ 1)])
  have h1cond : (if (1 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (1 : ℕ) = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' Φhat := by
    rw [if_pos rfl, v8cw_key σ hmon hd1 e' h' hSMW, ResVal.w_one σ]
    refine ⟨one_ne_zero, ?_⟩
    push_cast
    omega
  rw [if_neg h0cond, if_pos h1cond, zero_add]
  have hred : ((fun j : ℕ => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 1) = 1 := by
    norm_num
  rw [hred]
  have hcd1 : v8cdig σ zbar (1 : Polynomial ℤ_[p]) = 1 := by
    apply Subtype.ext
    rw [v8cdig_coe, v8dig_one σ ψ g hg hψ hψz hg1 zbar hzbar]
    rfl
  rw [hcd1, map_one, one_mul, ResVal.w_one σ]
  norm_num

/-- the S5′ pin: single-slot coefficients carry the parent digit at position
`−t′·σ.w B` (the `mfun ≡ 0` normalization — DEFINITIONAL for the explicit carrier;
warrant: D.7(v)'s D-map definition `D(x) := R(x) mod ψ`, MOVES 2364–2367 — the
child digit IS the raw z̄-evaluation `digPrime` of the parent residual). -/
private lemma v8Rc_S5' (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC Φhat B) :
    ∃ c' : (↥(σ.nextField zbar))ˣ,
      v8Rc σ Φhat e' h' zbar s' t' B
        = LaurentPolynomial.C ((c' : ↥(σ.nextField zbar))) *
            LaurentPolynomial.T (- t' * σ.w B) ∧
      ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hcw : childW σ Φhat e' h' B = (e' : ℤ) * σ.w B :=
    L4_TRANSii σ Φhat e' h' _ hSMW B hB hBc
  have hdigne : σ.digPrime zbar B ≠ 0 :=
    L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar B hB
      (by rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB hBc)
  have hcne : v8cdig σ zbar B ≠ 0 := fun h0 => hdigne (congrArg Subtype.val h0)
  refine ⟨Units.mk0 _ hcne, ?_, rfl⟩
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hB (v8dev_single hΦne hBc)]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_range_one]
  have h0cond : (if (0 : ℕ) = 0 then B else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 0 then B else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' B := by
    rw [if_pos rfl, hcw]
    exact ⟨hB, by push_cast; ring⟩
  rw [if_pos h0cond]
  have hred : ((fun j : ℕ => if j = 0 then B else 0) 0) = B := by norm_num
  rw [hred]
  show LaurentPolynomial.C (v8cdig σ zbar B) *
      LaurentPolynomial.T (((0 : ℕ) : ℤ) * s' - t' * σ.w B) = _
  norm_num

/-! #### the easy law legs: hRne, hRneg -/

/-- hRne: the carrier is nonvanishing on nonzero inputs. -/
private lemma v8Rc_ne (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ) (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    v8Rc σ Φhat e' h' zbar s' t' f ≠ 0 := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨-, j₀, hj₀N, hj₀nz, hj₀e⟩ := hSMW f B N hf hdev
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdev]
  exact v8dsum_ne σ ψ g hg hψ hψz zbar hzbar hΦd e' h' s' t' hbez' hdev.1 hj₀N hj₀nz hj₀e.symm

/-- hRneg: the carrier is odd (parent `R_neg` slotwise; positions and ties are
negation-invariant). -/
private lemma v8Rc_negLaw (hσ : StageCore σ) (zbar : Fˣ)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    (f : Polynomial ℤ_[p]) :
    v8Rc σ Φhat e' h' zbar s' t' (-f) = - v8Rc σ Φhat e' h' zbar s' t' f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero, v8Rc_zero, neg_zero]
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdev,
    v8Rc_eq σ hmon e' h' zbar s' t' (neg_ne_zero.mpr hf) (v8dev_neg hdev),
    v8cw_neg σ hmon hd1 e' h' hSMW hf]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if -(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (-(B j))) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (-(B j)))
      else 0)
    = -(if B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (B j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))
      else 0)
  by_cases hBj : B j = 0
  · have hn1 : ¬(-(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 (by rw [hBj, neg_zero])
    have hn2 : ¬(B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 hBj
    rw [if_neg hn1, if_neg hn2, neg_zero]
  · have hwn := ResVal.w_neg σ (B j) hBj
    have hdig : σ.digPrime zbar (-(B j)) = - σ.digPrime zbar (B j) := by
      simp only [Stage.digPrime]
      rw [hσ.R_neg, map_neg]
    have hcd : v8cdig σ zbar (-(B j)) = - v8cdig σ zbar (B j) := by
      apply Subtype.ext
      rw [v8cdig_coe, hdig]
      push_cast
      rfl
    by_cases hc : B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · rw [if_pos hc, if_pos ⟨neg_ne_zero.mpr hBj, by rw [hwn]; exact hc.2⟩,
        hwn, hcd, map_neg, neg_mul]
    · rw [if_neg hc, if_neg (fun hcn => hc ⟨hBj, by rw [← hwn]; exact hcn.2⟩), neg_zero]

/-! #### residue → digit bridges + monic-division sum plumbing -/

private lemma v8dig_ne_of_deg (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hxd : x.degree < Φhat.degree) :
    σ.digPrime zbar x ≠ 0 :=
  L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar x hx
    (by rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hx hxd)

private lemma v8dig_of_Radd (zbar : Fˣ) {x a b : Polynomial ℤ_[p]}
    (h : σ.R x = σ.R a + σ.R b) :
    σ.digPrime zbar x = σ.digPrime zbar a + σ.digPrime zbar b := by
  simp only [Stage.digPrime]
  rw [h, map_add]

private lemma v8dig_of_Req (zbar : Fˣ) {x a : Polynomial ℤ_[p]} (h : σ.R x = σ.R a) :
    σ.digPrime zbar x = σ.digPrime zbar a := by
  simp only [Stage.digPrime]
  rw [h]

/-- `%ₘ` is additive (monic divisor). -/
private lemma v8add_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic)
    (a b : Polynomial ℤ_[p]) : (a + b) %ₘ q = a %ₘ q + b %ₘ q := by
  have ha := Polynomial.modByMonic_add_div a q
  have hb := Polynomial.modByMonic_add_div b q
  refine (Polynomial.div_modByMonic_unique (a /ₘ q + b /ₘ q) (a %ₘ q + b %ₘ q) hq
    ⟨?_, ?_⟩).2
  · linear_combination ha + hb
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (Polynomial.degree_modByMonic_lt a hq) (Polynomial.degree_modByMonic_lt b hq))

/-- `%ₘ` distributes over finite sums (monic divisor). -/
private lemma v8sum_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic) {ι : Type*}
    (S : Finset ι) (a : ι → Polynomial ℤ_[p]) :
    (∑ j ∈ S, a j) %ₘ q = ∑ j ∈ S, (a j %ₘ q) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i T hiT ih =>
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT, v8add_modByMonic hq, ih]

/-! #### the three D.1(b) tie laws for the explicit carrier (per-slot `v8gr` calculus) -/

/-- hRadd: at a childW tie with no jump, the carrier adds. -/
private lemma v8Rc_addLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ Φhat e' h' f = childW σ Φhat e' h' g')
    (hSum : childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) :
    v8Rc σ Φhat e' h' zbar s' t' (f + g')
      = v8Rc σ Φhat e' h' zbar s' t' f + v8Rc σ Φhat e' h' zbar s' t' g' := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, hSum, ← hEq,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0)
  -- slot lower bounds (∨-form) for both halves, keyed to the common tie level
  have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  have hDg : Bg j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hEq ▸ hming j ?_ h0)
      by_contra hc
      exact h0 (hdevg.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- both tied at slot j; ω := σ.w (Bf j)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hge
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v8gr_eq σ hf0 rfl, v8gr_eq σ hg0 hwg] at hgr
      by_cases hd : v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) = 0
      · -- digit cancellation: the sum slot is NOT tied; the two terms cancel
        have hdF : σ.digPrime zbar (Bf j) + σ.digPrime zbar (Bg j) = 0 := by
          rw [← v8cdig_coe σ zbar (Bf j), ← v8cdig_coe σ zbar (Bg j)]
          exact_mod_cast congrArg Subtype.val hd
        have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
              = childW σ Φhat e' h' f) := by
          rintro ⟨hs0, hse⟩
          have hws : σ.w (Bf j + Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hse
          have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
            rw [← v8gr_eq σ hs0 hws]; exact hgr
          refine v8dig_ne_of_deg σ ψ g hg hψ hψz zbar hzbar hΦd hs0
            (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
              (max_lt (hdevf.1 j) (hdevg.1 j))) ?_
          rw [v8dig_of_Radd σ zbar hRs]
          exact hdF
        rw [if_neg hnotied, if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg,
          ← add_mul, ← map_add, hd, map_zero, zero_mul]
      · -- no cancellation: the sum slot is tied, digits add
        have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
          rw [hgr]
          intro h0
          apply hd
          apply Subtype.ext
          have : ((v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) :
              ↥(σ.nextField zbar)) : F)
              = LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Bf j) + σ.R (Bg j)) := by
            rw [map_add]
            rfl
          rw [this, h0, map_zero]
          rfl
        obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
        have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
          rw [← v8gr_eq σ hs0 hws]; exact hgr
        have hcds : v8cdig σ zbar (Bf j + Bg j)
            = v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) := by
          apply Subtype.ext
          rw [v8cdig_coe, v8dig_of_Radd σ zbar hRs]
          push_cast
          rfl
        rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩,
          if_pos ⟨hg0, hge⟩, hws, hwg, hcds, map_add, add_mul]
    · -- f tied, g not: the g half is invisible at level ω
      have hgrg : v8gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v8Deep_of_slot σ he' hfe hDg)).2
      rw [v8gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
      have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hf0
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
        rw [← v8gr_eq σ hs0 hws]; exact hgr
      have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bf j) :=
        Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
      rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, if_neg hjg,
        add_zero, hws, hcds]
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- g tied, f not: mirror
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v8gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v8gr_eq σ hg0 rfl, hgrf, zero_add] at hgr
      have hgrne : v8gr σ (σ.w (Bg j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hg0
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bg j) := by
        rw [← v8gr_eq σ hs0 hws]; exact hgr
      have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bg j) :=
        Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
      rw [if_pos ⟨hs0, by rw [hws]; exact hge⟩, if_neg hjf,
        if_pos ⟨hg0, hge⟩, zero_add, hws, hcds]
    · -- neither tied: the sum slot cannot be tied either
      have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
            = childW σ Φhat e' h' f) := by
        rintro ⟨hs0, hse⟩
        have hgrf : v8gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
          rcases eq_or_ne (Bf j) 0 with h0 | h0
          · rw [h0, v8gr_zero]
          · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjf ⟨h0, hce⟩
        have hgrg : v8gr σ (σ.w (Bf j + Bg j)) (Bg j) = 0 := by
          rcases eq_or_ne (Bg j) 0 with h0 | h0
          · rw [h0, v8gr_zero]
          · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjg ⟨h0, hce⟩
        have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hse hDf)
          (v8Deep_of_slot σ he' hse hDg)).2
        rw [v8gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
        exact σ.hRne _ hs0 hgr
      rw [if_neg hnotied, if_neg hjf, if_neg hjg, add_zero]

/-- w_jump: at a childW tie whose sum jumps, the carriers cancel. -/
private lemma v8Rc_jumpLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ Φhat e' h' f = childW σ Φhat e' h' g')
    (hJump : childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g')) :
    v8Rc σ Φhat e' h' zbar s' t' f + v8Rc σ Φhat e' h' zbar s' t' g' = 0 := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  obtain ⟨hminC, -⟩ := hSMW (f + g') _ (max Nf Ng) hfg hdevC
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, ← hEq,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  show (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0) = 0
  have hjN : j < max Nf Ng := Finset.mem_range.mp hj
  -- a tied sum-slot at the pre-jump level contradicts the jump
  have hnoslot : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f →
      v8gr σ ω (Bf j + Bg j) = 0 := by
    intro ω hω
    by_contra hne
    obtain ⟨hs0, hws⟩ := v8gr_spec σ hne
    have hle : childW σ Φhat e' h' (f + g')
        ≤ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ) := hminC j hjN hs0
    rw [hws] at hle
    omega
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- both tied: residues must cancel (else the sum slot survives at the old level)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hge
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v8gr_eq σ hf0 rfl, v8gr_eq σ hg0 hwg, hnoslot (σ.w (Bf j)) hfe] at hgr
      -- hgr : 0 = R (Bf j) + R (Bg j)
      have hcds : v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) = 0 := by
        apply Subtype.ext
        have : ((v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) :
            ↥(σ.nextField zbar)) : F)
            = LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Bf j) + σ.R (Bg j)) := by
          rw [map_add]
          rfl
        rw [this, ← hgr, map_zero]
        rfl
      rw [if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg, ← add_mul, ← map_add, hcds,
        map_zero, zero_mul]
    · -- f tied alone: its residue would survive — contradiction
      exfalso
      have hgrg : v8gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hDg : Bg j = 0 ∨ childW σ Φhat e' h' f
          ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hEq ▸ hming j ?_ h0)
          by_contra hc
          exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v8Deep_of_slot σ he' hfe hDg)).2
      rw [v8gr_eq σ hf0 rfl, hgrg, add_zero, hnoslot (σ.w (Bf j)) hfe] at hgr
      exact σ.hRne _ hf0 hgr.symm
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- g tied alone: mirror contradiction
      exfalso
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v8gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
          ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hminf j ?_ h0)
          by_contra hc
          exact h0 (hdevf.2.1 j (le_of_not_gt hc))
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v8gr_eq σ hg0 rfl, hgrf, zero_add, hnoslot (σ.w (Bg j)) hge] at hgr
      exact σ.hRne _ hg0 hgr.symm
    · rw [if_neg hjf, if_neg hjg, add_zero]

/-- hRlt: below a strictly deeper summand, the carrier is unchanged. -/
private lemma v8Rc_ltLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hLt : childW σ Φhat e' h' f < childW σ Φhat e' h' g')
    (hStr : childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) :
    v8Rc σ Φhat e' h' zbar s' t' (f + g') = v8Rc σ Φhat e' h' zbar s' t' f := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf, hStr,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
  -- the g half is strictly deep at every pre-level slot
  have hgdeep : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f →
      v8gr σ ω (Bg j) = 0 ∧ (Bg j = 0 ∨ ω ≤ σ.w (Bg j)) := by
    intro ω hω
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact ⟨by rw [h0, v8gr_zero], Or.inl h0⟩
    · have hjNg : j < Ng := by
        by_contra hc
        exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgt : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) < (e' : ℤ) * σ.w (Bg j)
          + (j : ℤ) * (h' : ℤ) := by
        have h1 : childW σ Φhat e' h' g'
            ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := hming j hjNg h0
        omega
      have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
      have hwgt : ω < σ.w (Bg j) := by
        have h2 : (e' : ℤ) * ω < (e' : ℤ) * σ.w (Bg j) := by omega
        exact lt_of_mul_lt_mul_left h2 he0.le
      exact ⟨v8gr_deep σ (ne_of_gt hwgt), Or.inr hwgt.le⟩
  have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · -- f tied: sum slot tied with f's digit and weight
    obtain ⟨hf0, hfe⟩ := hjf
    obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j)) hfe
    have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j)))) hDg).2
    rw [v8gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
    have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
      rw [hgr]; exact σ.hRne _ hf0
    obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
    have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
      rw [← v8gr_eq σ hs0 hws]; exact hgr
    have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bf j) :=
      Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
    rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, hws, hcds]
  · -- f untied: the sum slot cannot be tied
    have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f) := by
      rintro ⟨hs0, hse⟩
      obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j + Bg j)) hse
      have hgrf : v8gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hse hDf) hDg).2
      rw [v8gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
      exact σ.hRne _ hs0 hgr
    rw [if_neg hnotied, if_neg hjf]

/-! #### hRmul — the bilinear slot expansion through `L3_DIV` (blueprint §10 V8(b);
the honest §9.5 core).  Route: the product development `Cdev` by convolution + monic
division (the `L4_TRANSiii` construction, re-derived at digit level since those
helpers are private); per-diagonal, the graded residue of `Cdev m` at the level
forced by `childW`-multiplicativity is EXACTLY the sum of the tied-pair remainder
residues (`L3_DIV` weights + (I-aug) for the carried quotients); evaluation at z̄
turns this into the Laurent product's convolution coefficient, with a vanishing
coefficient = the SAME zero on both sides (the D.1(b) δ-calculus — here: a tied
sum-slot with zero digit would contradict D.3(d) digit-nonvanishing). -/
private lemma v8Rc_mulLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hlift : IsStandardLift σ ψ g Φhat)
    (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (hcop : Nat.gcd e' h' = 1) (hiaug : IAug σ Φhat e' h')
    (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) :
    v8Rc σ Φhat e' h' zbar s' t' (f * g')
      = v8Rc σ Φhat e' h' zbar s' t' f * v8Rc σ Φhat e' h' zbar s' t' g' := by
  classical
  have hfg : f * g' ≠ 0 := mul_ne_zero hf hg'
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hg1 : 1 ≤ g := by rw [← hg]; exact hψ.natDegree_pos
  have hdpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hWmul : childW σ Φhat e' h' (f * g')
      = childW σ Φhat e' h' f + childW σ Φhat e' h' g' :=
    L4_TRANSiii σ ψ g Φhat hlift hψ hψz hmon zbar hzbar e' h' hcop _ hSMW hiaug
      f g' hf hg' hfg
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  have hBfz : ∀ j, Nf ≤ j → Bf j = 0 := hdevf.2.1
  have hBgz : ∀ k, Ng ≤ k → Bg k = 0 := hdevg.2.1
  have hNf1 : 1 ≤ Nf := by
    by_contra hcon
    have h0 : Nf = 0 := by omega
    have := hdevf.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hf this
  have hNg1 : 1 ≤ Ng := by
    by_contra hcon
    have h0 : Ng = 0 := by omega
    have := hdevg.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hg' this
  -- ===== the generating polynomials and the convolution (the L4_TRANSiii block) =====
  set FF : Polynomial (Polynomial ℤ_[p]) :=
    ∑ j ∈ Finset.range Nf, Polynomial.C (Bf j) * Polynomial.X ^ j with hFFdef
  set GG : Polynomial (Polynomial ℤ_[p]) :=
    ∑ k ∈ Finset.range Ng, Polynomial.C (Bg k) * Polynomial.X ^ k with hGGdef
  have hFFc : ∀ m, FF.coeff m = Bf m := by
    intro m
    rw [hFFdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Nf
    · rw [Finset.sum_eq_single m]
      · simp
      · intro j hj hjm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBfz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro j hj
      have hmj : m ≠ j := by
        have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmj]
  have hGGc : ∀ m, GG.coeff m = Bg m := by
    intro m
    rw [hGGdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Ng
    · rw [Finset.sum_eq_single m]
      · simp
      · intro k hk hkm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hkm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBgz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro k hk
      have hmk : m ≠ k := by
        have := Finset.mem_range.mp hk; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmk]
  have hFFeval : Polynomial.eval Φhat FF = f := by
    rw [hFFdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevf.2.2.symm
  have hGGeval : Polynomial.eval Φhat GG = g' := by
    rw [hGGdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevg.2.2.symm
  have hFFnd : FF.natDegree ≤ Nf - 1 := by
    rw [hFFdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hj
    omega
  have hGGnd : GG.natDegree ≤ Ng - 1 := by
    rw [hGGdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hk
    omega
  set H : Polynomial (Polynomial ℤ_[p]) := FF * GG with hHdef
  have hHnd : H.natDegree ≤ Nf + Ng - 2 := by
    rw [hHdef]
    refine le_trans Polynomial.natDegree_mul_le ?_
    omega
  have hHcoeff : ∀ m, H.coeff m = ∑ jk ∈ Finset.antidiagonal m, Bf jk.1 * Bg jk.2 := by
    intro m
    rw [hHdef, Polynomial.coeff_mul]
    exact Finset.sum_congr rfl (fun jk _ => by rw [hFFc, hGGc])
  have hHvan : ∀ m, Nf + Ng - 1 ≤ m → H.coeff m = 0 := by
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hprodsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), H.coeff m * Φhat ^ m := by
    rw [← hFFeval, ← hGGeval, ← Polynomial.eval_mul, ← hHdef]
    exact Polynomial.eval_eq_sum_range' (by omega) Φhat
  -- ===== the development of f·g': remainders on the diagonal, carried quotients shifted =====
  set Cdev : ℕ → Polynomial ℤ_[p] := fun m =>
    H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) with hCdef
  have hCdev_eq : ∀ m, Cdev m
      = H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) := fun m => rfl
  have hBfnd : ∀ j, (Bf j).natDegree ≤ Φhat.natDegree - 1 := by
    intro j
    by_cases hz : Bf j = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevf.1 j)
      omega
  have hBgnd : ∀ k, (Bg k).natDegree ≤ Φhat.natDegree - 1 := by
    intro k
    by_cases hz : Bg k = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevg.1 k)
      omega
  have hHcnd : ∀ m, (H.coeff m).natDegree ≤ 2 * Φhat.natDegree - 2 := by
    intro m
    rw [hHcoeff m]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro jk hjk
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hBfnd jk.1
    have h2 := hBgnd jk.2
    omega
  have hQdeg : ∀ m, (H.coeff m /ₘ Φhat).degree < Φhat.degree := by
    intro m
    have hnd : (H.coeff m /ₘ Φhat).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_divByMonic _ hmon]
      have h2 := hHcnd m
      omega
    calc (H.coeff m /ₘ Φhat).degree
        ≤ ((H.coeff m /ₘ Φhat).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (Φhat.natDegree : WithBot ℕ) := by exact_mod_cast hnd
      _ = Φhat.degree := (Polynomial.degree_eq_natDegree hΦne).symm
  have hCdeg : ∀ m, (Cdev m).degree < Φhat.degree := by
    intro m
    rw [hCdev_eq m]
    by_cases hm : m = 0
    · rw [if_pos hm, add_zero]
      exact Polynomial.degree_modByMonic_lt _ hmon
    · rw [if_neg hm]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact Polynomial.degree_modByMonic_lt _ hmon
      · exact hQdeg (m - 1)
  have hCvan : ∀ m, Nf + Ng ≤ m → Cdev m = 0 := by
    intro m hm
    rw [hCdev_eq m]
    have hm0 : m ≠ 0 := by omega
    rw [if_neg hm0, hHvan m (by omega), hHvan (m - 1) (by omega),
      Polynomial.zero_modByMonic, Polynomial.zero_divByMonic, add_zero]
  have hCsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, Nf + Ng = N₁ + 1 := ⟨Nf + Ng - 1, by omega⟩
    have hz2 : H.coeff N₁ = 0 := hHvan N₁ (by omega)
    have hsplit : ∀ m, Cdev m * Φhat ^ m
        = (H.coeff m %ₘ Φhat) * Φhat ^ m
          + (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      intro m
      rw [hCdev_eq m]
      by_cases hm : m = 0
      · simp only [if_pos hm]
        rw [add_zero, add_zero]
      · simp only [if_neg hm]
        rw [add_mul]
    have hshift : (∑ m ∈ Finset.range (Nf + Ng),
          (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m))
        = ∑ m ∈ Finset.range (Nf + Ng), (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1) := by
      rw [hN₁]
      rw [Finset.sum_range_succ'
        (fun m => if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) N₁]
      rw [Finset.sum_range_succ (fun m => (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1)) N₁]
      rw [if_pos rfl, add_zero, hz2, Polynomial.zero_divByMonic, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    rw [hprodsum]
    have e1 : ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m
        = (∑ m ∈ Finset.range (Nf + Ng), (H.coeff m %ₘ Φhat) * Φhat ^ m)
          + ∑ m ∈ Finset.range (Nf + Ng),
              (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => hsplit m)
    rw [e1, hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    conv_lhs => rw [← Polynomial.modByMonic_add_div (H.coeff m) Φhat]
    ring
  have hdevC : IsDevelopment Φhat (f * g') Cdev (Nf + Ng) := ⟨hCdeg, hCvan, hCsum⟩
  -- ===== Lemma DIV wrapper (weight + digit) =====
  have hDIV : ∀ (a b : Polynomial ℤ_[p]), a ≠ 0 → b ≠ 0 →
      a.degree < Φhat.degree → b.degree < Φhat.degree →
      (a * b) %ₘ Φhat ≠ 0 ∧ σ.w ((a * b) %ₘ Φhat) = σ.w a + σ.w b ∧
        σ.digPrime zbar ((a * b) %ₘ Φhat) = σ.digPrime zbar a * σ.digPrime zbar b := by
    intro a b ha hb had hbd
    have had' : a.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree ha had
    have hbd' : b.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hb hbd
    have hRd' : ((a * b) %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
      by_cases hz : (a * b) %ₘ Φhat = 0
      · rw [hz]; simpa using hdpos
      · rw [← hΦd]
        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hmon)
    have hdiv : a * b = ((a * b) /ₘ Φhat) * Φhat + (a * b) %ₘ Φhat := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div (a * b) Φhat]
      ring
    exact L3_DIV σ ψ g hg hψ hψz Φhat hlift zbar hzbar a b ha hb had' hbd' _ _ hdiv hRd'
  -- ===== per-pair slot arithmetic =====
  have hpairw : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      childW σ Φhat e' h' f + childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) + (m' : ℤ) * (h' : ℤ) := by
    intro m' jk hd hBf hBg
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ Φhat e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    linarith
  have hpair_tie : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      ∀ ω : ℤ, (e' : ℤ) * ω + (m' : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      (σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω
        ↔ ((e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
           ∧ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ)
              = childW σ Φhat e' h' g')) := by
    intro m' jk hd hBf hBg ω hω
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ Φhat e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    constructor
    · intro hsum
      have hkey : (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2)
          + (m' : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
        rw [← hexp, hsum]
        exact hω
      constructor
      · linarith
      · linarith
    · rintro ⟨ht1, ht2⟩
      have hkey : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) = (e' : ℤ) * ω := by
        linarith
      exact mul_left_cancel₀ he0.ne' hkey
  -- ===== the carried quotient is strictly deep (I-aug) =====
  have hQdeep : ∀ (m' : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + ((m' : ℤ) + 1) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      H.coeff m' /ₘ Φhat ≠ 0 → ω < σ.w (H.coeff m' /ₘ Φhat) := by
    intro m' ω hω hy
    have hbound : ∀ jk ∈ Finset.antidiagonal m', Bf jk.1 * Bg jk.2 = 0 ∨
        ω + σ.w Φhat + 1 ≤ σ.w (Bf jk.1 * Bg jk.2) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · exact Or.inl hPz
      right
      have hBf := left_ne_zero_of_mul hPz
      have hBg := right_ne_zero_of_mul hPz
      have hp := hpairw m' jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
      have hwP : σ.w (Bf jk.1 * Bg jk.2) = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
        σ.hwmul _ _ hBf hBg
      rw [hwP]
      by_contra hcon
      push_neg at hcon
      have hS : σ.w (Bf jk.1) + σ.w (Bg jk.2) ≤ ω + σ.w Φhat := by omega
      have hmul : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
          ≤ (e' : ℤ) * (ω + σ.w Φhat) :=
        mul_le_mul_of_nonneg_left hS (Int.natCast_nonneg e')
      have hexp : (e' : ℤ) * (ω + σ.w Φhat) = (e' : ℤ) * ω + (e' : ℤ) * σ.w Φhat := by
        ring
      have hia : (e' : ℤ) * σ.w Φhat < (h' : ℤ) := hiaug
      linarith
    have hconv_ne : H.coeff m' ≠ 0 := fun h0 => hy (by rw [h0, Polynomial.zero_divByMonic])
    have hwconv : ω + σ.w Φhat + 1 ≤ σ.w (H.coeff m') := by
      rw [hHcoeff m']
      refine ult_sum_ge σ.w σ.hwult _ _ _ (fun jk hjk hne0 => (hbound jk hjk).resolve_left hne0)
        (by rw [← hHcoeff m']; exact hconv_ne)
    have hyΦ : Φhat * (H.coeff m' /ₘ Φhat) = H.coeff m' + -(H.coeff m' %ₘ Φhat) := by
      have hmd := Polynomial.modByMonic_add_div (H.coeff m') Φhat
      linear_combination hmd
    have hΦyne : Φhat * (H.coeff m' /ₘ Φhat) ≠ 0 := mul_ne_zero hΦne hy
    have hwΦy : ω + σ.w Φhat + 1 ≤ σ.w (Φhat * (H.coeff m' /ₘ Φhat)) := by
      rw [hyΦ]
      by_cases hrz : H.coeff m' %ₘ Φhat = 0
      · rw [hrz, neg_zero, add_zero]; exact hwconv
      · have hrw : ω + σ.w Φhat + 1 ≤ σ.w (H.coeff m' %ₘ Φhat) := by
          have hremsum : H.coeff m' %ₘ Φhat
              = ∑ jk ∈ Finset.antidiagonal m', (Bf jk.1 * Bg jk.2) %ₘ Φhat := by
            rw [hHcoeff m']
            exact v8sum_modByMonic hmon _ _
          rw [hremsum]
          refine ult_sum_ge σ.w σ.hwult _ _ _ ?_ (by rw [← hremsum]; exact hrz)
          intro jk hjk hne0
          have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
            intro h0; rw [h0, Polynomial.zero_modByMonic] at hne0; exact hne0 rfl
          have hBf := left_ne_zero_of_mul hPne
          have hBg := right_ne_zero_of_mul hPne
          have hw_eq := (hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)).2.1
          rw [hw_eq]
          have hb := (hbound jk hjk).resolve_left hPne
          rw [σ.hwmul _ _ hBf hBg] at hb
          exact hb
        have hnegne : -(H.coeff m' %ₘ Φhat) ≠ 0 := neg_ne_zero.mpr hrz
        have hsumne : H.coeff m' + -(H.coeff m' %ₘ Φhat) ≠ 0 := by
          rw [← hyΦ]; exact hΦyne
        have hult := σ.hwult _ _ hconv_ne hnegne hsumne
        rw [ResVal.w_neg σ _ hrz] at hult
        exact le_trans (le_min hwconv hrw) hult
    have hmulw := σ.hwmul Φhat (H.coeff m' /ₘ Φhat) hΦne hy
    rw [hmulw] at hwΦy
    omega
  -- ===== the graded slot computation: grw of Cdev m = the tied-pair residue sum =====
  have hgrC : ∀ (m : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      v8gr σ ω (Cdev m)
        = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
    intro m ω hω
    have hCm : Cdev m = (∑ jk ∈ Finset.antidiagonal m, (Bf jk.1 * Bg jk.2) %ₘ Φhat)
        + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) := by
      rw [hCdev_eq m, hHcoeff m, v8sum_modByMonic hmon]
    have hQpack : v8Deep σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat)
        ∧ v8gr σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) = 0 := by
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
        exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
      · rw [if_neg hm0]
        by_cases hy : H.coeff (m - 1) /ₘ Φhat = 0
        · rw [hy]
          exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
        · have hω' : (e' : ℤ) * ω + (((m - 1 : ℕ) : ℤ) + 1) * (h' : ℤ)
              = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
            have hc : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by omega
            rw [hc]; exact hω
          have hlt := hQdeep (m - 1) ω hω' hy
          exact ⟨Or.inr hlt.le, v8gr_deep σ (ne_of_gt hlt)⟩
    have hDeepR : ∀ jk ∈ Finset.antidiagonal m,
        v8Deep σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · rw [hPz, Polynomial.zero_modByMonic]
        exact Or.inl rfl
      · have hBf := left_ne_zero_of_mul hPz
        have hBg := right_ne_zero_of_mul hPz
        obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
        right
        rw [hrw]
        have hp := hpairw m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
        have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) := by
          linarith
        exact le_of_mul_le_mul_left h2 he0
    obtain ⟨hDsum, hEsum⟩ := v8gr_sum σ hσ (Finset.antidiagonal m) _ hDeepR
    have hEtot := (v8gr_add σ hσ hDsum hQpack.1).2
    rw [hCm, hEtot, hEsum, hQpack.2, add_zero]
    have hstep1 : ∑ jk ∈ Finset.antidiagonal m, v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat)
        = ∑ jk ∈ (Finset.antidiagonal m).filter
            (fun jk => (Bf jk.1 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)
            ∧ (Bg jk.2 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
            v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro jk hjk hne
      obtain ⟨hrne, hrw⟩ := v8gr_spec σ hne
      have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
        intro h0; rw [h0, Polynomial.zero_modByMonic] at hrne; exact hrne rfl
      have hBf := left_ne_zero_of_mul hPne
      have hBg := right_ne_zero_of_mul hPne
      obtain ⟨-, hwr, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω := by rw [← hwr]; exact hrw
      have hti := (hpair_tie m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg ω hω).mp hsum
      exact ⟨⟨hBf, hti.1⟩, ⟨hBg, hti.2⟩⟩
    have hstep2 : ∀ jk ∈ (Finset.antidiagonal m).filter
        (fun jk => (Bf jk.1 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)
        ∧ (Bg jk.2 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
        v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) = σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      intro jk hjk
      rw [Finset.mem_filter] at hjk
      obtain ⟨hjkd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩ := hjk
      obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω :=
        (hpair_tie m jk (Finset.mem_antidiagonal.mp hjkd) hBf hBg ω hω).mpr ⟨ht1, ht2⟩
      exact v8gr_eq σ hrne (by rw [hrw]; exact hsum)
    rw [hstep1, Finset.sum_congr rfl hstep2]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.ext
    intro jk
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
      have hjNf : jk.1 < Nf := by
        by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
      have hkNg : jk.2 < Ng := by
        by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
      exact ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
    · rintro ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
      exact ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
  -- ===== final assembly: both sides as fiberwise sums over the diagonals =====
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, hWmul]
  unfold v8dsum
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  have hmaps : ∀ jk ∈ ((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
      ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
        (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
      jk.1 + jk.2 ∈ Finset.range (Nf + Ng) := by
    intro jk hjk
    rw [Finset.mem_product] at hjk
    obtain ⟨h1, h2⟩ := hjk
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  show (if Cdev m ≠ 0 ∧ (e' : ℤ) * σ.w (Cdev m) + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g'
      then LaurentPolynomial.C (v8cdig σ zbar (Cdev m)) *
        LaurentPolynomial.T ((m : ℤ) * s' - t' * σ.w (Cdev m))
      else 0)
    = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v8cdig σ zbar (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v8cdig σ zbar (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2)))
  rcases Finset.eq_empty_or_nonempty ((((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
      (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
    ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
      (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
    (fun jk => jk.1 + jk.2 = m)) with hFIB | hFIB
  · -- empty fiber: a tied sum-slot would have zero graded residue — impossible
    rw [hFIB, Finset.sum_empty, if_neg ?_]
    rintro ⟨hs0, hse⟩
    have hgr := hgrC m (σ.w (Cdev m)) hse
    rw [hFIB, Finset.sum_empty, v8gr_eq σ hs0 rfl] at hgr
    exact σ.hRne _ hs0 hgr
  · -- nonempty fiber: constant weight-sum ω₀ and position across the fiber
    obtain ⟨jk₀, hjk₀⟩ := hFIB
    have hjk₀' := hjk₀
    rw [Finset.mem_filter, Finset.mem_product] at hjk₀'
    obtain ⟨⟨hj₀mem, hk₀mem⟩, hd₀⟩ := hjk₀'
    rw [Finset.mem_filter, Finset.mem_range] at hj₀mem hk₀mem
    obtain ⟨hj₀Nf, hBf₀, ht₀f⟩ := hj₀mem
    obtain ⟨hk₀Ng, hBg₀, ht₀g⟩ := hk₀mem
    have hω₀ : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
      have hcast : (jk₀.1 : ℤ) + (jk₀.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd₀
      have hexp : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))
          = (e' : ℤ) * σ.w (Bf jk₀.1) + (e' : ℤ) * σ.w (Bg jk₀.2) := by ring
      have hch : (jk₀.1 : ℤ) * (h' : ℤ) + (jk₀.2 : ℤ) * (h' : ℤ)
          = (m : ℤ) * (h' : ℤ) := by
        rw [← add_mul, hcast]
      linarith
    -- fiberwise constancy of the weight sum
    have hwconst : ∀ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        σ.w (Bf jk.1) + σ.w (Bg jk.2) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) := by
      intro jk hjk
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, hd⟩ := hjk
      rw [Finset.mem_filter, Finset.mem_range] at hjmem hkmem
      exact (hpair_tie m jk hd hjmem.2.1 hkmem.2.1 _ hω₀).mpr ⟨hjmem.2.2, hkmem.2.2⟩
    -- the RHS fiber sum collapses to C (digit convolution) · T (forced position)
    have hRHS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v8cdig σ zbar (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v8cdig σ zbar (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2))))
      = LaurentPolynomial.C (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2)) *
        LaurentPolynomial.T ((m : ℤ) * s'
          - t' * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      have hw := hwconst jk hjk
      have hd : jk.1 + jk.2 = m := by
        rw [Finset.mem_filter] at hjk
        exact hjk.2
      have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd
      have hcs : (jk.1 : ℤ) * s' + (jk.2 : ℤ) * s' = (m : ℤ) * s' := by
        rw [← add_mul, hcast]
      rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
      congr 2
      rw [← hw]
      linarith
    rw [hRHS]
    -- the digit bridge: eval₂ of the tied residue sum = the digit convolution
    have hevalS : LaurentPolynomial.eval₂ σ.K.subtype zbar
        (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat))
        = ((∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) : ↥(σ.nextField zbar)) : F) := by
      rw [map_sum]
      have hcoe : ((∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) : ↥(σ.nextField zbar)) : F)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          (σ.digPrime zbar (Bf jk.1) * σ.digPrime zbar (Bg jk.2)) := by
        push_cast
        rfl
      rw [hcoe]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, -⟩ := hjk
      rw [Finset.mem_filter] at hjmem hkmem
      have hdig := (hDIV (Bf jk.1) (Bg jk.2) hjmem.2.1 hkmem.2.1
        (hdevf.1 jk.1) (hdevg.1 jk.2)).2.2
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat)) = _
      exact hdig
    have hgr := hgrC m (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) hω₀
    by_cases hS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2)) = 0
    · -- vanishing convolution coefficient: BOTH sides are the same zero
      rw [hS, map_zero, zero_mul, if_neg ?_]
      rintro ⟨hs0, hse⟩
      have hws : σ.w (Cdev m) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) :=
        v8w_eq_of_slot σ he' hω₀ hse
      have hRs := hgr
      rw [v8gr_eq σ hs0 hws] at hRs
      refine v8dig_ne_of_deg σ ψ g hg hψ hψz zbar hzbar hΦd hs0 (hCdeg m) ?_
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Cdev m)) = 0
      rw [hRs, hevalS, hS]
      rfl
    · -- surviving coefficient: the sum slot is tied with digit = the convolution
      have hgrne : v8gr σ (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) (Cdev m) ≠ 0 := by
        rw [hgr]
        intro h0
        apply hS
        apply Subtype.ext
        rw [← hevalS, h0, map_zero]
        rfl
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
        rw [← v8gr_eq σ hs0 hws]
        exact hgr
      have hcdS : v8cdig σ zbar (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) := by
        apply Subtype.ext
        rw [v8cdig_coe]
        show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Cdev m)) = _
        rw [hRs, hevalS]
      rw [if_pos ⟨hs0, by rw [hws]; exact hω₀⟩, hws, hcdS]

end V8Infra

/-- Unit V8(c): the childW-only strict law — S9w's conjunct (ii).  PROVED
(escalation round 2026-07-28): S9a's in-file `hwult` pattern (developments add
slotwise; the parent ultrametric per slot) + the negation trick
`f = (f + g') + (−g')` for the reverse inequality (childW is negation-invariant
slotwise since `σ.w (−B) = σ.w B` for any multiplicative integer valuation).
MOVED above V8a/V8b (2026-07-28 second escalation): V8b's hRlt leg consumes it. -/
theorem V8c_wStrict (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∀ f g', f ≠ 0 → g' ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f := by
  classical
  -- ## Φ̂ is monic of degree ≥ 1 (L3), so the S2 development pack applies
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hdeg1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨hdevMin, hSMW⟩ := S2_childW σ Φhat hmonΦ hdeg1 e' h'
  -- ## parent valuation: negation invariance
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    linarith
  have hwneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have key := σ.hwmul (-1) (-1) hn1 hn1
    rw [neg_one_mul, neg_neg, hw1] at key
    linarith
  have hwB : ∀ B : Polynomial ℤ_[p], B ≠ 0 → σ.w (-B) = σ.w B := by
    intro B hB
    have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h2 := σ.hwmul (-1) B hn1 hB
    rwa [neg_one_mul, hwneg1, zero_add] at h2
  -- ## childW negation invariance (slotwise: the negated development has the same slot data)
  have hwnegC : ∀ x : Polynomial ℤ_[p], x ≠ 0 →
      childW σ Φhat e' h' (-x) = childW σ Φhat e' h' x := by
    intro x hx
    obtain ⟨B, N, hdev, hlow0, j0, hj0N, hj0nz, hj0eq⟩ := hdevMin x hx
    have hxneg : (-x : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hx
    have hdevneg : IsDevelopment Φhat (-x) (fun j => -(B j)) N := by
      refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [Polynomial.degree_neg]
        exact hdev.1 j
      · show -(B j) = 0
        rw [hdev.2.1 j hj, neg_zero]
      · calc -x = -∑ j ∈ Finset.range N, B j * Φhat ^ j := by rw [← hdev.2.2]
          _ = ∑ j ∈ Finset.range N, -(B j * Φhat ^ j) := by rw [Finset.sum_neg_distrib]
          _ = ∑ j ∈ Finset.range N, -(B j) * Φhat ^ j :=
              Finset.sum_congr rfl fun j _ => (neg_mul (B j) (Φhat ^ j)).symm
    obtain ⟨hlow1, j1, hj1N, hj1nz, hj1eq⟩ := hSMW (-x) _ N hxneg hdevneg
    have hBj1 : B j1 ≠ 0 := fun h => hj1nz (by simp [h])
    -- ≥: childW(−x) sits at a slot of x's development
    have h1 : childW σ Φhat e' h' x ≤ childW σ Φhat e' h' (-x) := by
      rw [hj1eq]
      simp only [hwB (B j1) hBj1]
      exact hlow0 j1 hj1N hBj1
    -- ≤: childW(x) sits at a slot of (−x)'s development
    have h2 : childW σ Φhat e' h' (-x) ≤ childW σ Φhat e' h' x := by
      rw [hj0eq]
      have h := hlow1 j0 hj0N (by simp [hj0nz])
      simpa only [hwB (B j0) hj0nz] using h
    omega
  -- ## the child ultrametric law (the S9a in-file pattern, verbatim)
  have hwult : ∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g') ≤
        childW σ Φhat e' h' (f + g') := by
    intro f g' hf hg' hfg
    obtain ⟨Bf, Nf, hdf, hmf⟩ := hdevMin f hf
    obtain ⟨Bg, Ng, hdg, hmg⟩ := hdevMin g' hg'
    set N := max Nf Ng with hN
    have hsub_f : Finset.range Nf ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))
    have hsub_g : Finset.range Ng ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))
    have hsum_f : f = ∑ j ∈ Finset.range N, Bf j * Φhat ^ j := by
      rw [hdf.2.2]
      refine Finset.sum_subset hsub_f ?_
      intro j hjN hjNf
      rw [hdf.2.1 j (by simpa using hjNf), zero_mul]
    have hsum_g : g' = ∑ j ∈ Finset.range N, Bg j * Φhat ^ j := by
      rw [hdg.2.2]
      refine Finset.sum_subset hsub_g ?_
      intro j hjN hjNg
      rw [hdg.2.1 j (by simpa using hjNg), zero_mul]
    have hdevS : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) N := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdf.1 j) (hdg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdf.2.1 j (le_trans (le_max_left _ _) hj),
          hdg.2.1 j (le_trans (le_max_right _ _) hj), add_zero]
      · rw [hsum_f, hsum_g, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => (add_mul (Bf j) (Bg j) (Φhat ^ j)).symm
    obtain ⟨hlow, jS, hjSN, hjSnz, hjSeq⟩ := hSMW (f + g') _ N hfg hdevS
    rw [hjSeq]
    by_cases hBf : Bf jS = 0
    · have hBg : Bg jS ≠ 0 := by
        intro hBg
        exact hjSnz (by rw [hBf, hBg, add_zero])
      have hjNg : jS < Ng := by
        by_contra hge
        exact hBg (hdg.2.1 jS (le_of_not_gt hge))
      have hle := (hmg.1) jS hjNg hBg
      have hval : σ.w (Bf jS + Bg jS) = σ.w (Bg jS) := by rw [hBf, zero_add]
      calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
          ≤ childW σ Φhat e' h' g' := min_le_right _ _
        _ ≤ (e' : ℤ) * σ.w (Bg jS) + (jS : ℤ) * (h' : ℤ) := hle
        _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
    · by_cases hBg : Bg jS = 0
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hle := (hmf.1) jS hjNf hBf
        have hval : σ.w (Bf jS + Bg jS) = σ.w (Bf jS) := by rw [hBg, add_zero]
        calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
            ≤ childW σ Φhat e' h' f := min_le_left _ _
          _ ≤ (e' : ℤ) * σ.w (Bf jS) + (jS : ℤ) * (h' : ℤ) := hle
          _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hjNg : jS < Ng := by
          by_contra hge
          exact hBg (hdg.2.1 jS (le_of_not_gt hge))
        have hult := σ.hwult (Bf jS) (Bg jS) hBf hBg hjSnz
        have hlef := (hmf.1) jS hjNf hBf
        have hleg := (hmg.1) jS hjNg hBg
        have he'nn : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
        rcases min_cases (σ.w (Bf jS)) (σ.w (Bg jS)) with ⟨hmin, hcmp⟩ | ⟨hmin, hcmp⟩
        · have : childW σ Φhat e' h' f ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bf jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_left _ _) this
        · have : childW σ Φhat e' h' g' ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bg jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_right _ _) this
  -- ## assembly: strict domination pins the sum's value to the lower side
  intro f g' hf hg' hlt
  have hfg : f + g' ≠ 0 := by
    intro h0
    have hgeq : g' = -f := eq_neg_of_add_eq_zero_right h0
    rw [hgeq, hwnegC f hf] at hlt
    exact lt_irrefl _ hlt
  have hge : childW σ Φhat e' h' f ≤ childW σ Φhat e' h' (f + g') := by
    have h := hwult f g' hf hg' hfg
    rwa [min_eq_left (le_of_lt hlt)] at h
  have hle : childW σ Φhat e' h' (f + g') ≤ childW σ Φhat e' h' f := by
    by_contra hcon
    push_neg at hcon
    have hng : (-g' : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hg'
    have hsum : (f + g') + (-g') = f := by ring
    have h := hwult (f + g') (-g') hfg hng (by rw [hsum]; exact hf)
    rw [hsum, hwnegC g' hg'] at h
    have h1 : childW σ Φhat e' h' f <
        min (childW σ Φhat e' h' (f + g')) (childW σ Φhat e' h' g') :=
      lt_min hcon hlt
    omega
  omega

/-- Unit V8(a): the explicit descent carrier exists with the ADDITIVE law legs —
hR0, hRne, hRadd, hRlt, hRneg + w_jump (the D.1(b) tie laws at childW). -/
theorem V8a_carrierAdditive (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∃ D : ChildResData σ Φhat e' h' zbar s' t',
      ExplicitDescentCarrier D ∧
      (D.Rc 0 = 0) ∧
      (∀ f, f ≠ 0 → D.Rc f ≠ 0) ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
          childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f →
          D.Rc (f + g') = D.Rc f + D.Rc g') ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
          D.Rc (f + g') = D.Rc f) ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
          childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g') →
          D.Rc f + D.Rc g' = 0) ∧
      (∀ f, D.Rc (-f) = - D.Rc f) := by
  classical
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hd1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨-, hSMW⟩ := S2_childW σ Φhat hmonΦ hd1 e' h'
  refine ⟨⟨v8Rc σ Φhat e' h' zbar s' t',
      v8Rc_phi σ ψ g th.hdeg th.hirr th.hne_z th.hg zbar hzbar hmonΦ hd1 e' h' s' t' hSMW,
      fun B hB hBc => v8Rc_S5' σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hΦdeg
        e' h' s' t' hSMW B hB hBc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf B N hdev
    exact ⟨fun j => v8cdig σ zbar (B j), fun j => rfl,
      v8Rc_eq σ hmonΦ e' h' zbar s' t' hf hdev⟩
  · exact v8Rc_zero σ Φhat e' h' zbar s' t'
  · exact fun f hf => v8Rc_ne σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' s' t' hbez' hSMW hf
  · exact fun f g'' hf hg hfg hEq hSum => v8Rc_addLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hSum
  · intro f g'' hf hg hfg hLt
    exact v8Rc_ltLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' th.he' s' t' hSMW hf hg hfg hLt
      (V8c_wStrict σ hσ th s' t' hbez' ht'0 f g'' hf hg hLt)
  · exact fun f g'' hf hg hfg hEq hJump => v8Rc_jumpLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hJump
  · exact fun f => v8Rc_negLaw σ hσ.core zbar hmonΦ hd1 e' h' s' t' hSMW f

/-- Unit V8(b): the explicit descent carrier is FULLY lawful — `ChildResLaws`
including hRmul (the bilinear slot expansion through `L3_DIV`, the honest §9.5
core; see the header for the displayed route). -/
theorem V8b_carrierLaws (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∃ D : ChildResData σ Φhat e' h' zbar s' t',
      ExplicitDescentCarrier D ∧ ChildResLaws D := by
  classical
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hd1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨-, hSMW⟩ := S2_childW σ Φhat hmonΦ hd1 e' h'
  refine ⟨⟨v8Rc σ Φhat e' h' zbar s' t',
      v8Rc_phi σ ψ g th.hdeg th.hirr th.hne_z th.hg zbar hzbar hmonΦ hd1 e' h' s' t' hSMW,
      fun B hB hBc => v8Rc_S5' σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hΦdeg
        e' h' s' t' hSMW B hB hBc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf B N hdev
    exact ⟨fun j => v8cdig σ zbar (B j), fun j => rfl,
      v8Rc_eq σ hmonΦ e' h' zbar s' t' hf hdev⟩
  · exact v8Rc_zero σ Φhat e' h' zbar s' t'
  · exact fun f hf => v8Rc_ne σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' s' t' hbez' hSMW hf
  · exact fun f g'' hf hg => v8Rc_mulLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar
      hzbar th.hlift hmonΦ hd1 hΦdeg e' h' th.he' th.hcop th.hiaug s' t' hSMW hf hg
  · exact fun f g'' hf hg hfg hEq hSum => v8Rc_addLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hSum
  · intro f g'' hf hg hfg hLt
    exact v8Rc_ltLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' th.he' s' t' hSMW hf hg hfg hLt
      (V8c_wStrict σ hσ th s' t' hbez' ht'0 f g'' hf hg hLt)
  · exact fun f g'' hf hg hfg hEq hJump => v8Rc_jumpLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hJump
  · exact fun f => v8Rc_negLaw σ hσ.core zbar hmonΦ hd1 e' h' s' t' hSMW f

/-- Unit V8 (capstone — S9w's EXACT statement shape, assembled from V8b + V8c):
a lawful `ChildResData` carrier exists, and the childW strict law holds.
`S9w_residualLaws` closes from this by `exact` once V8b/V8c land. -/
theorem V8_childResidual (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    (∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) := by
  obtain ⟨D, -, hD⟩ := V8b_carrierLaws σ hσ th s' t' hbez' ht'0
  exact ⟨⟨D, hD⟩, V8c_wStrict σ hσ th s' t' hbez' ht'0⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V8_tiedPos_inj
#print axioms LeanUrat.HC1.V8_eval₂_mem_nextField
#print axioms LeanUrat.HC1.V8_digitUnit
#print axioms LeanUrat.HC1.V8a_carrierAdditive
#print axioms LeanUrat.HC1.V8b_carrierLaws
#print axioms LeanUrat.HC1.V8c_wStrict
#print axioms LeanUrat.HC1.V8_childResidual
