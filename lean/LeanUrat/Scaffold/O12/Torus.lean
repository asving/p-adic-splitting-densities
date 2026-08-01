/-
BP_II §1.8 — the torus telescope (`Scaffold/O12/Torus.lean`), units II-T2,
II-T1, II-T5, II-T3, II-T4.
Units in this file: II-T2 (`chain_telescope`) — the abstract fibered telescope
over shared-vertex chains, anchor V_{k+1} := 1 at index k (L6d Step 2);
II-T1 (`torus_count` + helpers `torus_monic_smul_mem` / `torus_fiber_smul_mem` /
`torusEquiv`) — (T1), the torus identity: the c-fiber count equals the monic
z-free count at every fixed pattern ρ and degree d, independent of c
(L6d Step 1; see its transcription note for the `#`/`open Cardinal in`
elaboration context and the II-F9-dependency scoping);
II-T3 (**PARTIAL — see its section note**): the blueprint display `theorem
jc_count ...` is ELIDED and its "= ∏_j (Ppoly ρ_j).eval q" tie is refuted
against the landed `patternOf` (`jc_count_ppoly_refuted`); the unit's entire
§2 proof content — telescope over the interior-coefficient counts, hrow from
(T1), anchor c = 1 — is compiled in full as `jc_count_core` (helpers
`finite_of_natDegree_le` / `torus_cfiber_lead_ne_zero` / `torus_row_sum`);
II-T5 (**BLOCKED — see its section note**): the intended consistency identity
`zfree_total` is displayed ELIDED in BP_II §1.8 (`theorem zfree_total ...`)
and its sole dependency II-F9 is BLOCKED-refuted (`FactF.lean`), with the
on-record disposition that II-T5 reassigns only after the `patternOf` dedup
repair lands. UNLIKE II-F8/F9, NO refutation touches II-T5's content —
compiled instance artifacts (`pattern_degree_one_iff`,
`pattern_degree_two_iff`, `Ppoly_atom_one_one`, `Ppoly_atom_two_one`,
`Ppoly_pair_one_one`, `zfree_total_one`, `zfree_total_two`) verify the
identity at d = 1, 2 with the index sets classified complete;
II-T4 (**PARTIAL — see its section note**): the blueprint display `theorem
jc_prob ...` is ELIDED and its Ppoly factors are refuted-blocked with
II-F8/F9 (`jc_prob_ppoly_refuted`); the unit's entire §2 proof content —
divisor = total count (`card_fiber_lead_const`/`total_row_sum`/
`jc_total_count`), joint probability = product of per-face factors
(`jc_prob_core`, docstring form `jc_prob_core'` via `sub_one_mul_pow_pred`),
marginals by one-face-unsummed telescope (`jc_marginal_core`/
`jc_prob_marginal`), independence (`jc_prob_indep`) — is compiled in full.
-/
import Mathlib
import LeanUrat.Scaffold.O12.FactF

/-!
# The fibered telescope, abstract form [unit II-T2]

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.8 (unit II-T2; row table §2, MED).
* Math source of record: L6d Step 2.
* Deps: none. Later torus units (II-T1, II-T3, II-T4) extend this file.

Proof: induction on k, left to right — sum the first vertex via the
c-independent row sums `hrow`, pull out `P 0`, recurse on the tail chain.

Transcription note: the blueprint binder `λ` in `hrow` is Lean 4's reserved
lambda token; it is transcribed as the escaped identifier `«λ»` (the same
binder name, alpha-identical statement). The classical instances (`Fintype Fˣ`
and decidability of the anchor condition over an abstract finite field) enter
via `open Classical in`, as elaboration context only — the displayed statement
is otherwise byte-verbatim from BP_II §1.8.
-/

namespace LeanUrat.Scaffold

open Finset

open Classical in
/-- Helper for unit II-T2 (not a blueprint statement): the telescope with the
`Fin` bookkeeping in `castSucc`/`succ`/`last` normal form — definitionally the
blueprint display. Induction on `k`: split off the first vertex `v₀` by
`Fin.consEquiv`, sum it via the c-independent row sum `hrow 0`, pull out `P 0`,
recurse on the tail chain `j ↦ n j.succ`. -/
private theorem chain_telescope_aux {F : Type*} [Field F] [Fintype F] :
    ∀ (k : ℕ) (n : Fin k → Fˣ → Fˣ → ℕ) (P : Fin k → ℕ),
      (∀ j c, ∑ l : Fˣ, n j l c = P j) →
      (∑ V : Fin (k + 1) → Fˣ,
        if V (Fin.last k) = 1 then
          ∏ j : Fin k, n j (V j.castSucc) (V j.succ)
        else 0) =
      ∏ j, P j := by
  intro k
  induction k with
  | zero =>
    intro n P hrow
    rw [← ((Equiv.funUnique (Fin 1) Fˣ).symm).sum_comp]
    simp
  | succ k ih =>
    intro n P hrow
    -- Split off the first vertex: V = Fin.cons v₀ W.
    have hsplit :
        (∑ V : Fin (k + 1 + 1) → Fˣ,
          if V (Fin.last (k + 1)) = 1 then
            ∏ j : Fin (k + 1), n j (V j.castSucc) (V j.succ)
          else 0)
        = ∑ W : Fin (k + 1) → Fˣ, ∑ v₀ : Fˣ,
            if (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = 1 then
              ∏ j : Fin (k + 1),
                n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ)
            else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (k + 1 + 1) => Fˣ).sum_comp,
        Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    -- The inner sum over v₀: the anchor condition and the tail product do not
    -- see v₀, so `hrow 0` collapses it to `P 0`.
    have key : ∀ W : Fin (k + 1) → Fˣ,
        (∑ v₀ : Fˣ,
          if (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = 1 then
            ∏ j : Fin (k + 1),
              n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ)
          else 0)
        = P 0 *
          (if W (Fin.last k) = 1 then
            ∏ j : Fin k, n j.succ (W j.castSucc) (W j.succ)
          else 0) := by
      intro W
      have hanchor : ∀ v₀ : Fˣ,
          (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = W (Fin.last k) := by
        intro v₀
        rw [← Fin.succ_last, Fin.cons_succ]
      have hprod : ∀ v₀ : Fˣ,
          (∏ j : Fin (k + 1),
            n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ))
          = n 0 v₀ (W 0) * ∏ j : Fin k, n j.succ (W j.castSucc) (W j.succ) := by
        intro v₀
        rw [Fin.prod_univ_succ]
        rfl
      by_cases hW : W (Fin.last k) = 1
      · simp only [hanchor, hprod, hW, if_true, ← Finset.sum_mul, hrow 0]
      · simp only [hanchor, hW, if_false, Finset.sum_const_zero, mul_zero]
    -- Recurse on the tail chain.
    rw [hsplit, Finset.sum_congr rfl fun W _ => key W, ← Finset.mul_sum,
      ih (fun j => n j.succ) (fun j => P j.succ) (fun j c => hrow j.succ c),
      ← Fin.prod_univ_succ]

open Classical in
/-- **The fibered telescope** (L6d Step 2), abstract form: counting functions
n_j : Fˣ × Fˣ → ℕ whose torus row-sums Σ_λ n_j(λ, c) = P_j are c-independent
telescope over shared-vertex chains: Σ_{V ∈ (Fˣ)^k} ∏_j n_j(V_j, V_{j+1}) = ∏_j P_j
(V_{k+1} := 1, the anchor). Induction on k, left to right. -/
theorem chain_telescope {F : Type*} [Field F] [Fintype F] {k : ℕ}
    (n : Fin k → Fˣ → Fˣ → ℕ) (P : Fin k → ℕ)
    (hrow : ∀ j c, ∑ «λ» : Fˣ, n j «λ» c = P j) :
    (∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k, n j
          (V ⟨j, Nat.lt.step j.isLt⟩)
          (V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)
      else 0) =
    ∏ j, P j :=
  chain_telescope_aux k n P hrow

/-! ## Unit II-T1 — (T1), the torus identity (L6d Step 1)

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.8 (unit II-T1; row table §2, MED).
* Math source of record: L6d Step 1.
* Deps: II-F3 (`patternOf` + `patternOf_smul_unit`, landed in `FactF.lean`);
  the row also lists II-F9 — see the dependency note below.

TRANSCRIPTION NOTE (II-T1). The `torus_count` statement is VERBATIM from
BP_II.md §1.8. Elaboration context (same device as II-T2's
`open Classical in`; the displayed statement is byte-verbatim):

1. The count notation `#{x | p x}` cannot elaborate through the file's
   `open Finset` scoped `#` = `Finset.card`: the Finset set-builder needs
   `Fintype (Polynomial F)` and a `DecidablePred`, and `Polynomial F` is not
   a Fintype (errors on record in the unit report). It elaborates through the
   scoped `Cardinal.mk` prefix `#` instead, with the set-builder coerced to
   its subtype — so `open Cardinal in` is supplied, and the statement is the
   equality `Cardinal.mk ↥{R | …} = Cardinal.mk ↥{S | …}`. Both sets are
   finite (polynomials of bounded degree over a finite field), so the
   cardinal equality is precisely the (T1) count identity; the proof is the
   blueprint's two-sided bijection itself (`Cardinal.mk_congr ∘ torusEquiv`,
   the Equiv playing the role of the sketched `Finset.card_bij`).

DEPENDENCY NOTE (II-T1 vs the BLOCKED II-F9). The §2 row lists II-F9 as a
dep, and II-F9 (with II-F8) is BLOCKED — refuted against the landed II-F3
`patternOf` (see the FactF.lean section notes). Only the DOCSTRING's
"= (Ppoly ρ).eval q" gloss consumes Fact F(iii): the DISPLAYED statement is
the pure c-fiber ↔ monic-z-free count identity, references no `Ppoly`, and
holds for the landed `patternOf` unchanged — the bijection only needs the
unit-scalar invariance `patternOf_smul_unit` (II-F3), which is indifferent
to the F8/F9 multiplicity defect. The `Ppoly` tie remains with II-F8/F9's
repair (the docstring gloss is quoted verbatim and flagged inline). -/

section TorusCount

variable {F : Type*} [Field F]

/-- Helper [unit II-T1], forward leg of the bijection: rescaling by the
inverse leading coefficient, `R ↦ lead(R)⁻¹ • R`, carries the c-fiber
conditions (degree d, constant coefficient c, pattern ρ) to the monic z-free
conditions (pattern invariance = II-F3 `patternOf_smul_unit`; `R ≠ 0` since
`R(0) = c` is a unit). -/
theorem torus_monic_smul_mem {d : ℕ} {ρ : Multiset (ℕ+ × ℕ+)} {c : Fˣ}
    {R : Polynomial F}
    (h : R.natDegree = d ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ) :
    (R.leadingCoeff⁻¹ • R).Monic ∧ (R.leadingCoeff⁻¹ • R).natDegree = d ∧
      (R.leadingCoeff⁻¹ • R).coeff 0 ≠ 0 ∧ patternOf (R.leadingCoeff⁻¹ • R) = ρ := by
  obtain ⟨hdeg, hc0, hpat⟩ := h
  have hR0 : R ≠ 0 := fun h0 => c.ne_zero (by rw [← hc0, h0, Polynomial.coeff_zero])
  have hlead : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Polynomial.smul_eq_C_mul, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv hR0
  · rw [Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul (inv_ne_zero hlead), hdeg]
  · rw [Polynomial.coeff_smul, hc0, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hlead) c.ne_zero
  · exact (patternOf_smul_unit (Units.mk0 R.leadingCoeff⁻¹ (inv_ne_zero hlead)) R).trans hpat

/-- Helper [unit II-T1], backward leg of the bijection: rescaling by
`c / S(0)`, `S ↦ (c·S(0)⁻¹) • S`, carries the monic z-free conditions back to
the c-fiber conditions (`c·S(0)⁻¹ ≠ 0` since both factors are nonzero). -/
theorem torus_fiber_smul_mem {d : ℕ} {ρ : Multiset (ℕ+ × ℕ+)} {c : Fˣ}
    {S : Polynomial F}
    (h : S.Monic ∧ S.natDegree = d ∧ S.coeff 0 ≠ 0 ∧ patternOf S = ρ) :
    (((↑c : F) * (S.coeff 0)⁻¹) • S).natDegree = d ∧
      (((↑c : F) * (S.coeff 0)⁻¹) • S).coeff 0 = ↑c ∧
      patternOf (((↑c : F) * (S.coeff 0)⁻¹) • S) = ρ := by
  obtain ⟨hmon, hdeg, hc0, hpat⟩ := h
  have hb : (↑c : F) * (S.coeff 0)⁻¹ ≠ 0 := mul_ne_zero c.ne_zero (inv_ne_zero hc0)
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hb, hdeg]
  · rw [Polynomial.coeff_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  · exact (patternOf_smul_unit (Units.mk0 _ hb) S).trans hpat

/-- Helper [unit II-T1]: **the displayed two-sided bijection** of L6d Step 1,
`R ↦ lead(R)⁻¹ • R` with two-sided inverse `S ↦ (c/S(0)) • S`, between the
c-fiber and the monic z-free stratum of a fixed pattern ρ and degree d.
Left inverse: `(lead(R)⁻¹ • R)(0) = lead(R)⁻¹·c`, so the return scalar is
`c·(lead(R)⁻¹·c)⁻¹ = lead(R)`. Right inverse: `lead((c·S(0)⁻¹) • S) =
c·S(0)⁻¹` for monic S, so the return scalar is its inverse. -/
noncomputable def torusEquiv (d : ℕ) (ρ : Multiset (ℕ+ × ℕ+)) (c : Fˣ) :
    {R : Polynomial F | R.natDegree = d ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ} ≃
      {S : Polynomial F | S.Monic ∧ S.natDegree = d ∧ S.coeff 0 ≠ 0 ∧ patternOf S = ρ} where
  toFun R := ⟨R.1.leadingCoeff⁻¹ • R.1, torus_monic_smul_mem R.2⟩
  invFun S := ⟨((↑c : F) * (S.1.coeff 0)⁻¹) • S.1, torus_fiber_smul_mem S.2⟩
  left_inv := by
    rintro ⟨R, hdeg, hc0, hpat⟩
    have hR0 : R ≠ 0 := fun h0 => c.ne_zero (by rw [← hc0, h0, Polynomial.coeff_zero])
    have hlead : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
    apply Subtype.ext
    change ((↑c : F) * ((R.leadingCoeff⁻¹ • R).coeff 0)⁻¹) • (R.leadingCoeff⁻¹ • R) = R
    rw [Polynomial.coeff_smul, hc0, smul_eq_mul, smul_smul]
    have hc : (↑c : F) ≠ 0 := c.ne_zero
    have hscal : (↑c : F) * (R.leadingCoeff⁻¹ * ↑c)⁻¹ * R.leadingCoeff⁻¹ = 1 := by
      field_simp
    rw [hscal, one_smul]
  right_inv := by
    rintro ⟨S, hmon, hdeg, hc0, hpat⟩
    have hb : (↑c : F) * (S.coeff 0)⁻¹ ≠ 0 := mul_ne_zero c.ne_zero (inv_ne_zero hc0)
    apply Subtype.ext
    change ((((↑c : F) * (S.coeff 0)⁻¹) • S).leadingCoeff)⁻¹ •
        (((↑c : F) * (S.coeff 0)⁻¹) • S) = S
    have hlc : (((↑c : F) * (S.coeff 0)⁻¹) • S).leadingCoeff = (↑c : F) * (S.coeff 0)⁻¹ := by
      rw [Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        hmon.leadingCoeff, mul_one]
    rw [hlc, smul_smul, inv_mul_cancel₀ hb, one_smul]

set_option linter.unusedFintypeInType false in
open Cardinal in
/-- **(T1), the torus identity** (L6d Step 1) [unit II-T1, statement verbatim
BP_II.md §1.8]: for every c ∈ Fˣ and z-free ρ,
#{R : deg R = d, R(0) = c, patternOf R = ρ} = (Ppoly ρ).eval q — independent of c
(the two-sided unit-rescaling bijection).

[Unit note: the docstring above is the blueprint's, quoted verbatim. Its
"(Ppoly ρ).eval q" gloss is the Fact F(iii) tie, which is NOT part of this
statement and is currently BLOCKED with II-F8/F9 (refuted against the landed
`patternOf` — see FactF.lean); what is proved here is exactly the displayed
c-independence identity: c-fiber count = monic z-free count, as an equality
of cardinals (see the section's transcription note).] -/
theorem torus_count (F) [Field F] [Fintype F] (d : ℕ) (ρ) (c : Fˣ) :
    #{R : Polynomial F | R.natDegree = d ∧ R.coeff 0 = c ∧ patternOf R = ρ}
      = #{S : Polynomial F | S.Monic ∧ S.natDegree = d ∧ S.coeff 0 ≠ 0 ∧ patternOf S = ρ} :=
  Cardinal.mk_congr (torusEquiv d ρ c)

end TorusCount

/-! ## Unit II-T5 — `zfree_total`: BLOCKED (statement elided in the blueprint;
sole dependency II-F9 BLOCKED-refuted, reassignment gated on the `patternOf`
repair)

TRANSCRIPTION NOTE (II-T5). BP_II.md §1.8 displays this unit's statement as
`theorem zfree_total ...` — ELIDED like II-F8/II-F9 (no verbatim Lean text to
transcribe); the verbatim docstring is "Consistency: Σ_{ρ z-free of degree d}
(Ppoly ρ).eval q = q^d − q^{d−1}." A faithful GENERAL transcription requires
an index-set construction (the finite set of all patterns of total degree d)
that the blueprint does not display — that design choice belongs to the
repair milestone, not to this unit.

BLOCKED(II-T5): the sole dependency II-F9 (Fact F(iii), the per-pattern
z-free count `(Ppoly ρ).eval q`) is BLOCKED — the intended equality is
refuted against the landed II-F3 `patternOf` (`card_pattern_zfree_eq_refuted`
in `FactF.lean`), and the II-F8 section note there records the disposition:
"II-F8 (and II-F9, II-T1, II-T5 downstream) should be reassigned only after
the repair lands and the milestone is split per the §2 preamble." The
intended proof of this unit (§2 row: partition all monics with nonzero
constant term by pattern, then sum II-F9 over the classes) is therefore
unavailable, and any self-contained substitute (re-deriving F(i)–F(iii) with
dedup semantics, or the power-series/necklace identity
∏_D (1−t^D)^{−M_D} = (1−qt)⁻¹) is the not-yet-landed HARD count cluster
(II-F6/F7/F8/F9), outside this EASY unit's authority.

UNLIKE II-F8/F9, however, NO refutation touches II-T5: the intended identity
never mentions the defective `patternOf` — it is a pure statement about
`Ppoly` sums, immune to the multiplicity defect. The artifacts below compile
its d = 1 and d = 2 instances IN FULL: the index sets are classified complete
(`pattern_degree_one_iff`, `pattern_degree_two_iff` — every multiset of atoms
(D, m) with Σ D·m = d, no encoding choice: the instance theorems quantify
over ANY enumerating Finset), and the sums evaluate to x^d − x^{d−1} for all
x : ℚ (stronger than the docstring's x = q). Compiled evidence that the
eventual `zfree_total` statement needs NO repair — only the route through
the repaired Fact F is pending. -/

section ZfreeTotalBlocked

/-- BLOCKED(II-T5) artifact 0 (helper): a pattern of total degree 0 is empty —
every atom (D, m) of ℕ+ pairs contributes D·m ≥ 1. -/
private theorem pattern_degree_zero (s : Multiset (ℕ+ × ℕ+))
    (h : (s.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 0) : s = 0 := by
  rcases Multiset.empty_or_exists_mem s with rfl | ⟨b, hb⟩
  · rfl
  · exfalso
    have hbpos : 0 < (b.1 : ℕ) * (b.2 : ℕ) := Nat.mul_pos b.1.pos b.2.pos
    have hle : (b.1 : ℕ) * (b.2 : ℕ) ≤
        (s.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
        (Multiset.mem_map_of_mem _ hb)
    omega

/-- BLOCKED(II-T5) artifact 1: the degree-1 index set, classified complete —
a pattern has total degree 1 iff it is the single atom (1, 1). -/
theorem pattern_degree_one_iff (ρ : Multiset (ℕ+ × ℕ+)) :
    (ρ.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 1 ↔
      ρ = {((1 : ℕ+), (1 : ℕ+))} := by
  constructor
  · intro h
    rcases Multiset.empty_or_exists_mem ρ with rfl | ⟨a, ha⟩
    · simp at h
    obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.sum_cons] at h
    have hapos : 0 < (a.1 : ℕ) * (a.2 : ℕ) := Nat.mul_pos a.1.pos a.2.pos
    have ha1 : (a.1 : ℕ) * (a.2 : ℕ) = 1 := by omega
    have hs0 : (s.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 0 := by omega
    have h1 : a.1 = 1 := PNat.coe_eq_one_iff.mp
      (Nat.dvd_one.mp ⟨(a.2 : ℕ), ha1.symm⟩)
    have h2 : a.2 = 1 := PNat.coe_eq_one_iff.mp
      (Nat.dvd_one.mp ⟨(a.1 : ℕ), by rw [← ha1]; ring⟩)
    rw [pattern_degree_zero s hs0,
      show a = ((1 : ℕ+), (1 : ℕ+)) from Prod.ext h1 h2]
    rfl
  · rintro rfl
    simp

/-- BLOCKED(II-T5) artifact 2: the degree-2 index set, classified complete —
a pattern has total degree 2 iff it is one of {(2,1)} (irreducible quadratic),
{(1,2)} (squared linear), {(1,1),(1,1)} (two distinct linears). -/
theorem pattern_degree_two_iff (ρ : Multiset (ℕ+ × ℕ+)) :
    (ρ.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 2 ↔
      (ρ = {((2 : ℕ+), (1 : ℕ+))} ∨ ρ = {((1 : ℕ+), (2 : ℕ+))} ∨
        ρ = {((1 : ℕ+), (1 : ℕ+)), ((1 : ℕ+), (1 : ℕ+))}) := by
  constructor
  · intro h
    rcases Multiset.empty_or_exists_mem ρ with rfl | ⟨a, ha⟩
    · simp at h
    obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.sum_cons] at h
    have hapos : 0 < (a.1 : ℕ) * (a.2 : ℕ) := Nat.mul_pos a.1.pos a.2.pos
    rcases Nat.lt_or_ge ((a.1 : ℕ) * (a.2 : ℕ)) 2 with hlt | hge
    · -- head atom of degree 1, tail of degree 1
      have ha1 : (a.1 : ℕ) * (a.2 : ℕ) = 1 := by omega
      have hs1 : (s.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 1 := by omega
      have h1 : a.1 = 1 := PNat.coe_eq_one_iff.mp
        (Nat.dvd_one.mp ⟨(a.2 : ℕ), ha1.symm⟩)
      have h2 : a.2 = 1 := PNat.coe_eq_one_iff.mp
        (Nat.dvd_one.mp ⟨(a.1 : ℕ), by rw [← ha1]; ring⟩)
      right; right
      rw [(pattern_degree_one_iff s).mp hs1,
        show a = ((1 : ℕ+), (1 : ℕ+)) from Prod.ext h1 h2]
      rfl
    · -- head atom of degree 2, tail empty
      have ha2 : (a.1 : ℕ) * (a.2 : ℕ) = 2 := by omega
      have hs0 : (s.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 0 := by omega
      rw [pattern_degree_zero s hs0]
      rcases Nat.prime_two.eq_one_or_self_of_dvd (a.1 : ℕ)
          ⟨(a.2 : ℕ), ha2.symm⟩ with h1 | h1
      · -- D = 1 forces m = 2
        have h2 : (a.2 : ℕ) = 2 := by rw [h1, one_mul] at ha2; exact ha2
        right; left
        rw [show a = ((1 : ℕ+), (2 : ℕ+)) from
          Prod.ext (PNat.coe_eq_one_iff.mp h1) (PNat.coe_injective (by simp [h2]))]
        rfl
      · -- D = 2 forces m = 1
        have h2 : (a.2 : ℕ) = 1 := by rw [h1] at ha2; omega
        left
        rw [show a = ((2 : ℕ+), (1 : ℕ+)) from
          Prod.ext (PNat.coe_injective (by simp [h1])) (PNat.coe_eq_one_iff.mp h2)]
        rfl
  · rintro (rfl | rfl | rfl) <;> simp

/-- BLOCKED(II-T5) artifact 3: the z-free count polynomial of the pattern
{(1,1)} (a single linear factor): P_ρ(x) = x − 1 (the D = 1 supply with z
removed). -/
theorem Ppoly_atom_one_one (x : ℚ) :
    (Ppoly ({((1 : ℕ+), (1 : ℕ+))} : Multiset (ℕ+ × ℕ+))).eval x = x - 1 := by
  simp [Ppoly, patternFactor, fallingFac, degreeCount, multiplicityCount,
    Multiset.filter_singleton]

/-- BLOCKED(II-T5) artifact 4: the z-free count polynomial of the pattern
{(2,1)} (a single irreducible quadratic): P_ρ(x) = (x² − x)/2 = M₂(x), the
degree-2 supply (z-freeness does not touch D = 2). -/
theorem Ppoly_atom_two_one (x : ℚ) :
    (Ppoly ({((2 : ℕ+), (1 : ℕ+))} : Multiset (ℕ+ × ℕ+))).eval x
      = (x ^ 2 - x) / 2 := by
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  simp [Ppoly, patternFactor, fallingFac, degreeCount, multiplicityCount,
    Multiset.filter_singleton, Mpoly, hdiv,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  ring

/-- BLOCKED(II-T5) artifact 5: the z-free count polynomial of the pattern
{(1,1),(1,1)} (two DISTINCT linear factors): P_ρ(x) = (x−1)(x−2)/2 — the
falling factorial of length 2 on the z-free supply x − 1, divided by the
repeated-atom factorial 2!. -/
theorem Ppoly_pair_one_one (x : ℚ) :
    (Ppoly ({((1 : ℕ+), (1 : ℕ+)), ((1 : ℕ+), (1 : ℕ+))} :
        Multiset (ℕ+ × ℕ+))).eval x = (x - 1) * (x - 2) / 2 := by
  simp [Ppoly, patternFactor, fallingFac, degreeCount, multiplicityCount,
    Multiset.filter_cons, Multiset.filter_singleton, Finset.prod_range_succ]
  ring

/-- BLOCKED(II-T5) artifact 6: the d = 1 instance of the intended
`zfree_total`, index set semantic (ANY Finset enumerating the degree-1
patterns): Σ_{ρ z-free of degree 1} P_ρ(x) = x¹ − x⁰. -/
theorem zfree_total_one (x : ℚ) (S : Finset (Multiset (ℕ+ × ℕ+)))
    (hS : ∀ ρ, ρ ∈ S ↔ (ρ.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 1) :
    ∑ ρ ∈ S, (Ppoly ρ).eval x = x ^ 1 - x ^ 0 := by
  have hSeq : S = {({((1 : ℕ+), (1 : ℕ+))} : Multiset (ℕ+ × ℕ+))} := by
    ext ρ
    rw [hS ρ, pattern_degree_one_iff, Finset.mem_singleton]
  rw [hSeq, Finset.sum_singleton, Ppoly_atom_one_one]
  ring

/-- BLOCKED(II-T5) artifact 7: the d = 2 instance of the intended
`zfree_total`, index set semantic (ANY Finset enumerating the degree-2
patterns): Σ_{ρ z-free of degree 2} P_ρ(x) = (x²−x)/2 + (x−1) + (x−1)(x−2)/2
= x² − x¹. -/
theorem zfree_total_two (x : ℚ) (S : Finset (Multiset (ℕ+ × ℕ+)))
    (hS : ∀ ρ, ρ ∈ S ↔ (ρ.map fun a => (a.1 : ℕ) * (a.2 : ℕ)).sum = 2) :
    ∑ ρ ∈ S, (Ppoly ρ).eval x = x ^ 2 - x ^ 1 := by
  have hSeq : S = ({{((2 : ℕ+), (1 : ℕ+))}, {((1 : ℕ+), (2 : ℕ+))},
      {((1 : ℕ+), (1 : ℕ+)), ((1 : ℕ+), (1 : ℕ+))}} :
        Finset (Multiset (ℕ+ × ℕ+))) := by
    ext ρ
    rw [hS ρ, pattern_degree_two_iff]
    simp
  rw [hSeq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Ppoly_atom_two_one, Ppoly_atom_one_two,
    Ppoly_pair_one_one]
  ring

end ZfreeTotalBlocked

/-! ## Unit II-T3 — `jc_count`, the (JC) count form (L6d Step 2): PARTIAL
(statement elided in the blueprint; the Ppoly display refuted-blocked with
II-F8/F9; the unit's telescope content compiled in full as `jc_count_core`)

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.8 (unit II-T3; row table §2, MED).
* Math source of record: L6d Step 2.
* Deps: II-T2 (`chain_telescope`, this file), II-T1 (`torusEquiv`, this file).

TRANSCRIPTION NOTE (II-T3). BP_II.md §1.8 displays this unit's statement as
`theorem jc_count ...` — ELIDED like II-F8/F9/II-T5 (no verbatim Lean text to
transcribe); the verbatim docstring is "**(JC) count form** (L6d): the joint
residue-configuration count over a face-kind κ with shape vector ρ⃗ equals
∏_j (Ppoly ρ_j).eval q — instantiating the telescope with the
interior-coefficient counts, row sums supplied by (T1)."

BLOCKED half (the Ppoly display). The "= ∏_j (Ppoly ρ_j).eval q" tie consumes
Fact F(iii) (unit II-F9), which is BLOCKED — refuted against the landed II-F3
`patternOf` (`card_pattern_zfree_eq_refuted`, FactF.lean). The defect reaches
II-T3 itself: every faithful fixing of the elided display is FALSE at k = 1,
d₁ = 2, ρ₁ = {(1,2)}, over EVERY finite field — the joint chain count is 0
(no polynomial has the singleton pattern {(1,2)}: `patternOf_ne_atom_one_two`)
while ∏_j (Ppoly ρ_j).eval q = q − 1 ≥ 1. Compiled below as
`jc_count_ppoly_refuted`. Reassign the Ppoly display together with II-F8/F9
after the `patternOf` dedup repair (the II-F8 section note's disposition).

PROVED half (`jc_count_core`). The §2 row's ENTIRE proof content —
"instantiate II-T2 with interior-coefficient counts n_j; hrow from II-T1;
anchor c = 1" — is immune to the multiplicity defect and is compiled in full
generality: the anchored chain sum of the interior-coefficient counts
n_j(λ, c) = #{R : deg R = d_j, lead(R) = λ, R(0) = c, patternOf R = ρ_j}
equals ∏_j (the monic z-free count at (d_j, ρ_j)) — (T1)'s c-independent row
value, which is exactly what "(Ppoly ρ_j).eval q" DENOTES under the intended
(repaired) Fact F(iii). When the II-F8/F9 repair lands, `jc_count` is
`jc_count_core` composed with the repaired `card_pattern_zfree_eq` per face —
no change to the telescope content below. -/

section JcCount

variable {F : Type*} [Field F]

/-- Helper [unit II-T3]: over a finite field, any set of polynomials of
bounded `natDegree` is finite (inject into the submodule `Polynomial.degreeLT`,
carried to the finite type `Fin (d+1) → F` by `Polynomial.degreeLTEquiv`).
Supplies the `Finite` instances that keep the `Nat.card` bookkeeping below
honest (no junk-value collapse of an infinite count to 0). -/
theorem finite_of_natDegree_le [Fintype F] {d : ℕ} {s : Set (Polynomial F)}
    (hs : ∀ R ∈ s, R.natDegree ≤ d) : Finite s := by
  have h1 : Finite (Polynomial.degreeLT F (d + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv F (d + 1)).toEquiv.symm
  have hmem : ∀ R : s, (R : Polynomial F) ∈ Polynomial.degreeLT F (d + 1) := by
    intro R
    rw [Polynomial.mem_degreeLT]
    calc (R : Polynomial F).degree
        ≤ ((R : Polynomial F).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (d : WithBot ℕ) := by exact_mod_cast hs R R.2
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  refine Finite.of_injective
    (fun R : s => (⟨R, hmem R⟩ : Polynomial.degreeLT F (d + 1))) ?_
  intro R S h
  exact Subtype.ext
    (congrArg (fun x : Polynomial.degreeLT F (d + 1) => (x : Polynomial F)) h)

/-- Helper [unit II-T3]: a member of the c-fiber has nonzero leading
coefficient (it is nonzero, since its constant coefficient is the unit c). -/
theorem torus_cfiber_lead_ne_zero {d : ℕ} {ρ : Multiset (ℕ+ × ℕ+)} {c : Fˣ}
    {R : Polynomial F} (h : R.natDegree = d ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ) :
    R.leadingCoeff ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr
    (fun h0 => c.ne_zero (by rw [← h.2.1, h0, Polynomial.coeff_zero]))

open Classical in
/-- Helper [unit II-T3], **the (T1) row sums** of the telescope: for every
anchor c ∈ Fˣ, the interior-coefficient counts n(λ, c) sum over the lead
coordinate λ to the monic z-free count — the c-INDEPENDENT row value P.
Proof: fiber the c-fiber by the leading coefficient (a unit, by
`torus_cfiber_lead_ne_zero`), collapse the sigma type (`Nat.card_sigma`), and
apply the II-T1 bijection `torusEquiv` at the anchor c. -/
theorem torus_row_sum [Fintype F] (d : ℕ) (ρ : Multiset (ℕ+ × ℕ+)) (c : Fˣ) :
    ∑ l : Fˣ, Nat.card {R : Polynomial F | R.natDegree = d ∧
        R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ}
      = Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d ∧
        S.coeff 0 ≠ 0 ∧ patternOf S = ρ} := by
  haveI : ∀ l : Fˣ, Finite ↥{R : Polynomial F | R.natDegree = d ∧
      R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ} := fun _ =>
    finite_of_natDegree_le fun _ hR => le_of_eq hR.1
  have e : (Σ l : Fˣ, ↥{R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧
        R.coeff 0 = ↑c ∧ patternOf R = ρ}) ≃
      ↥{R : Polynomial F | R.natDegree = d ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ} :=
    { toFun := fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
      invFun := fun R => ⟨Units.mk0 R.1.leadingCoeff (torus_cfiber_lead_ne_zero R.2),
        R.1, R.2.1, rfl, R.2.2.1, R.2.2.2⟩
      left_inv := by
        rintro ⟨l, R, hdeg, hlc, hc0, hpat⟩
        have hl : Units.mk0 R.leadingCoeff
            (torus_cfiber_lead_ne_zero ⟨hdeg, hc0, hpat⟩) = l := Units.ext hlc
        subst hl
        rfl
      right_inv := fun _ => rfl }
  calc ∑ l : Fˣ, Nat.card ↥{R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧
        R.coeff 0 = ↑c ∧ patternOf R = ρ}
      = Nat.card (Σ l : Fˣ, ↥{R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧
          R.coeff 0 = ↑c ∧ patternOf R = ρ}) := Nat.card_sigma.symm
    _ = Nat.card ↥{R : Polynomial F | R.natDegree = d ∧ R.coeff 0 = ↑c ∧
          patternOf R = ρ} := Nat.card_congr e
    _ = Nat.card ↥{S : Polynomial F | S.Monic ∧ S.natDegree = d ∧ S.coeff 0 ≠ 0 ∧
          patternOf S = ρ} := Nat.card_congr (torusEquiv d ρ c)

open Classical in
/-- **The (JC) count form, telescope content** [unit II-T3, PROVED half —
see the section note: the blueprint display is elided and its Ppoly tie is
refuted-blocked with II-F8/F9]: the anchored chain sum of the
interior-coefficient counts n_j(λ, c) = #{R : deg R = d_j, lead(R) = λ,
R(0) = c, patternOf R = ρ_j} over shared-vertex chains V ∈ (Fˣ)^{k+1} with
anchor V_{k+1} = 1 equals ∏_j (the monic z-free count at (d_j, ρ_j)) — the
instantiation of II-T2 `chain_telescope` with hrow = `torus_row_sum` (II-T1),
anchor c = 1, exactly the §2 row's proof sketch. -/
theorem jc_count_core (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) :
    (∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          Nat.card {R : Polynomial F | R.natDegree = d j ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ρ j}
      else 0) =
    ∏ j : Fin k,
      Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d j ∧
        S.coeff 0 ≠ 0 ∧ patternOf S = ρ j} :=
  chain_telescope (F := F) (k := k)
    (fun j l c => Nat.card {R : Polynomial F | R.natDegree = d j ∧
      R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c ∧ patternOf R = ρ j})
    (fun j => Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d j ∧
      S.coeff 0 ≠ 0 ∧ patternOf S = ρ j})
    (fun j c => torus_row_sum (d j) (ρ j) c)

open Classical in
/-- **BLOCKED(II-T3) refutation**: the intended (JC) count display
"joint chain count = ∏_j (Ppoly ρ_j).eval q" (BP_II §1.8, elided) is FALSE
against the landed `patternOf`, already at k = 1, d₁ = 2, ρ₁ = {(1,2)}, over
EVERY finite field: the joint count is 0 (`patternOf_ne_atom_one_two`) while
the right side is q − 1 ≥ 1 (`Ppoly_atom_one_two`) — the same multiplicity
defect that blocks II-F8/F9. -/
theorem jc_count_ppoly_refuted (F : Type*) [Field F] [Fintype F] :
    ¬ (((∑ V : Fin 2 → Fˣ,
        if V ⟨1, Nat.lt_succ_self 1⟩ = 1 then
          ∏ j : Fin 1,
            Nat.card {R : Polynomial F | R.natDegree = 2 ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
              patternOf R = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))}
        else 0 : ℕ) : ℚ)
      = ∏ _j : Fin 1,
          (Ppoly ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))).eval
            (Fintype.card F : ℚ)) := by
  intro h
  haveI : IsEmpty ↥{S : Polynomial F | S.Monic ∧ S.natDegree = 2 ∧ S.coeff 0 ≠ 0 ∧
      patternOf S = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))} :=
    ⟨fun ⟨S, _, _, _, hpat⟩ => patternOf_ne_atom_one_two S hpat⟩
  have hcore : (∑ V : Fin 2 → Fˣ,
      if V ⟨1, Nat.lt_succ_self 1⟩ = 1 then
        ∏ j : Fin 1,
          Nat.card {R : Polynomial F | R.natDegree = 2 ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))}
      else 0)
      = ∏ _j : Fin 1,
          Nat.card ↥{S : Polynomial F | S.Monic ∧ S.natDegree = 2 ∧ S.coeff 0 ≠ 0 ∧
            patternOf S = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))} :=
    jc_count_core F (fun _ => 2)
      (fun _ => ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+)))
  rw [hcore] at h
  rw [Fin.prod_univ_one, Fin.prod_univ_one, Nat.card_of_isEmpty, Nat.cast_zero,
    Ppoly_atom_one_two] at h
  have h1 : (1 : ℚ) < (Fintype.card F : ℚ) := by exact_mod_cast Fintype.one_lt_card
  linarith [h, h1]

end JcCount

/-! ## Unit II-T4 — `jc_prob` + independence (L6d Step 3): PARTIAL
(statement elided in the blueprint; the Ppoly display refuted-blocked with
II-F8/F9; the unit's entire §2 proof content compiled in full)

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.8 (unit II-T4; row table §2, EASY).
* Math source of record: L6d Step 3 + the consistency ¶.
* Deps: II-T3 (`jc_count_core`, this file), II-T2 (`chain_telescope`, this
  file), II-T1 (`torusEquiv` via `torus_row_sum`, this file).

TRANSCRIPTION NOTE (II-T4). BP_II.md §1.8 displays this unit's statement as
`theorem jc_prob ...` — ELIDED like II-T3/II-T5 (no verbatim Lean text to
transcribe); the verbatim docstring is "**(JC) probability** +
product-of-marginals: divide by (q−1)^k·q^{Σ(d_j−1)}; each factor is
P_{ρ_j}(q)·(q^{d_j} − q^{d_j−1})⁻¹ — ONE element of ℚ(q), uniform in the
characteristic (Fact F), face events independent."

BLOCKED half (the Ppoly display). As with II-T3, the "P_{ρ_j}(q)" factors
consume Fact F(iii) (unit II-F9), BLOCKED — refuted against the landed II-F3
`patternOf` (`card_pattern_zfree_eq_refuted`, FactF.lean); the same k = 1,
d₁ = 2, ρ₁ = {(1,2)} counterexample refutes every faithful fixing of the
probability display too, compiled below as `jc_prob_ppoly_refuted` (the joint
probability is 0, the intended product of Ppoly factors is 1/q ≠ 0). The
docstring's "ONE element of ℚ(q), uniform in the characteristic" gloss rides
on that Fact F tie and stays blocked with it. Reassign the Ppoly display
together with II-F8/F9 after the `patternOf` dedup repair.

PROVED half. The §2 row's ENTIRE proof content — "divide by
(q−1)^k·q^{Σ(d_j−1)}; (q−1)q^{d−1} = q^d − q^{d−1}; marginals by re-running
II-T2 with one face unsummed" — is immune to the multiplicity defect and is
compiled in full, with the monic z-free count in place of the blocked
"(Ppoly ρ_j).eval q" (exactly the `jc_count_core` device):

* THE DIVISOR IS THE TOTAL: `card_fiber_lead_const` (each (lead, const)-pinned
  fiber of degree-d polynomials has q^{d−1} points — the interior
  coefficients), `total_row_sum` (its c-INDEPENDENT torus row sums
  (q−1)·q^{d−1}), `jc_total_count` (the pattern-free telescope: the total
  anchored-configuration count IS (q−1)^k·q^{Σ(d_j−1)}, so "divide by" is
  honest probability, not formal algebra);
* `jc_prob_core`: joint count / ((q−1)^k·q^{Σ(d_j−1)}) = ∏_j (per-face
  factor), each factor = (monic z-free count)_j / ((q−1)·q^{d_j−1});
* the display identity `sub_one_mul_pow_pred`: (x−1)·x^{d−1} = x^d − x^{d−1}
  (d ≥ 1), and the docstring-shaped `jc_prob_core'` with the denominators
  q^{d_j} − q^{d_j−1};
* MARGINALS by re-running II-T2 with one face unsummed: `jc_marginal_core`
  (face i keeps its pattern constraint, every other face runs unconstrained;
  the telescope evaluates to (monic count)_i · ∏_{j≠i} (q−1)·q^{d_j−1}) and
  `jc_prob_marginal` (marginal count / total = the face-i factor);
* INDEPENDENCE `jc_prob_indep`: joint probability = ∏_i (marginal probability
  of face i) — the product-of-marginals statement, all over the SAME total.

HONESTY NOTE (the `1 ≤ d j` hypotheses). The counting statements carry the
face-degree hypothesis d_j ≥ 1: L6d faces have positive degree, and the
blueprint's own divisor presupposes it — at d = 0 the (lead, const)-pinned
fiber count is {c = l}-dependent (1 or 0, never q^{0−1}-shaped) and
(q−1)·q^{0−1} truncates to q−1 ≠ 1, so the displayed formula is FALSE at
d = 0. The hypothesis is faithfulness to the elided display's face-kind
data, not a weakening. -/

section JcProb

variable {F : Type*} [Field F]

/-- Helper [unit II-T4] (not a blueprint statement): the coefficient formula
of the interior-coefficient parametrization c + Σ_i g_i·X^{i+1} + l·X^d
(constant c, interior coefficients g, leading coefficient l; d ≥ 1). -/
private theorem interior_coeff {d : ℕ} (hd : 1 ≤ d) (l c : F)
    (g : Fin (d - 1) → F) (n : ℕ) :
    (Polynomial.C c +
        (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
        Polynomial.C l * Polynomial.X ^ d).coeff n =
      if n = 0 then c
      else if hn : n - 1 < d - 1 then g ⟨n - 1, hn⟩
      else if n = d then l
      else 0 := by
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, mul_ite, mul_one, mul_zero]
  by_cases h0 : n = 0
  · subst h0
    have hs : (∑ i : Fin (d - 1), if (0 : ℕ) = (i : ℕ) + 1 then g i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg (by omega)
    rw [hs]
    simp [show ¬(0 : ℕ) = d by omega]
  · by_cases h1 : n - 1 < d - 1
    · have hs : (∑ i : Fin (d - 1), if n = (i : ℕ) + 1 then g i else 0)
          = g ⟨n - 1, h1⟩ := by
        rw [Finset.sum_eq_single (⟨n - 1, h1⟩ : Fin (d - 1))
          (fun i _ hne => if_neg fun hc => hne (Fin.ext (show (i : ℕ) = n - 1 by omega)))
          (fun hmem => absurd (Finset.mem_univ _) hmem)]
        exact if_pos (show n = (n - 1) + 1 by omega)
      rw [hs]
      simp [h0, dif_pos h1, show ¬n = d by omega]
    · by_cases h2 : n = d
      · have hs : (∑ i : Fin (d - 1), if n = (i : ℕ) + 1 then g i else 0) = 0 :=
          Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)
        rw [hs]
        simp [h2, show ¬d = 0 by omega, show ¬(d - 1 < d - 1) by omega]
      · have hs : (∑ i : Fin (d - 1), if n = (i : ℕ) + 1 then g i else 0) = 0 :=
          Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)
        rw [hs]
        simp [h0, h1, h2]

/-- Helper [unit II-T4] (not a blueprint statement): the parametrized
polynomial lies in the (lead, const)-pinned degree-d fiber. -/
private theorem interior_mem {d : ℕ} (hd : 1 ≤ d) (l c : Fˣ) (g : Fin (d - 1) → F) :
    (Polynomial.C (c : F) +
        (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
        Polynomial.C (l : F) * Polynomial.X ^ d) ∈
      {R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c} := by
  have hcf := interior_coeff hd (l : F) (c : F) g
  have htop : (Polynomial.C (c : F) +
      (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
      Polynomial.C (l : F) * Polynomial.X ^ d).coeff d = (l : F) := by
    rw [hcf, if_neg (by omega : ¬d = 0), dif_neg (by omega : ¬(d - 1 < d - 1)), if_pos rfl]
  have hdeg : (Polynomial.C (c : F) +
      (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
      Polynomial.C (l : F) * Polynomial.X ^ d).natDegree = d := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
      (Polynomial.le_natDegree_of_ne_zero (by rw [htop]; exact l.ne_zero))
    rw [hcf, if_neg (by omega : ¬N = 0), dif_neg (by omega : ¬(N - 1 < d - 1)),
      if_neg (by omega : ¬N = d)]
  refine ⟨hdeg, ?_, ?_⟩
  · show (Polynomial.C (c : F) +
        (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
        Polynomial.C (l : F) * Polynomial.X ^ d).coeff _ = (l : F)
    rw [hdeg, htop]
  · rw [hcf, if_pos rfl]

/-- Helper [unit II-T4]: **the interior-coefficient parametrization** — a
degree-d polynomial with pinned unit leading coefficient l and pinned unit
constant coefficient c is exactly its d − 1 interior coefficients. -/
noncomputable def fiberInteriorEquiv (d : ℕ) (hd : 1 ≤ d) (l c : Fˣ) :
    {R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c} ≃
      (Fin (d - 1) → F) where
  toFun R i := R.1.coeff ((i : ℕ) + 1)
  invFun g := ⟨_, interior_mem hd l c g⟩
  left_inv := by
    rintro ⟨R, hdeg, hlead, hc0⟩
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    show (Polynomial.C (c : F) +
        (∑ i : Fin (d - 1), Polynomial.C (R.coeff ((i : ℕ) + 1)) *
          Polynomial.X ^ ((i : ℕ) + 1)) +
        Polynomial.C (l : F) * Polynomial.X ^ d).coeff n = R.coeff n
    rw [interior_coeff hd]
    by_cases h0 : n = 0
    · subst h0
      rw [if_pos rfl, hc0]
    · rw [if_neg h0]
      by_cases h1 : n - 1 < d - 1
      · rw [dif_pos h1]
        show R.coeff (n - 1 + 1) = R.coeff n
        congr 1
        omega
      · rw [dif_neg h1]
        by_cases h2 : n = d
        · rw [if_pos h2, ← hlead]
          show R.coeff R.natDegree = R.coeff n
          rw [hdeg, h2]
        · rw [if_neg h2]
          exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)).symm
  right_inv := by
    intro g
    funext i
    show (Polynomial.C (c : F) +
        (∑ i : Fin (d - 1), Polynomial.C (g i) * Polynomial.X ^ ((i : ℕ) + 1)) +
        Polynomial.C (l : F) * Polynomial.X ^ d).coeff ((i : ℕ) + 1) = g i
    rw [interior_coeff hd, if_neg (by omega : ¬(i : ℕ) + 1 = 0),
      dif_pos (by have := i.isLt; omega : (i : ℕ) + 1 - 1 < d - 1)]
    congr 1

/-- Helper [unit II-T4]: **the fiber count** — each (lead, const)-pinned fiber
of degree-d polynomials has exactly q^{d−1} points (its interior
coefficients, `fiberInteriorEquiv`). These are the counts whose torus row
sums make the blueprint's divisor (q−1)^k·q^{Σ(d_j−1)} the honest TOTAL
configuration count below. -/
theorem card_fiber_lead_const [Fintype F] {d : ℕ} (hd : 1 ≤ d) (l c : Fˣ) :
    Nat.card {R : Polynomial F | R.natDegree = d ∧ R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c}
      = Fintype.card F ^ (d - 1) := by
  rw [Nat.card_congr (fiberInteriorEquiv d hd l c), Nat.card_fun,
    Nat.card_eq_fintype_card (α := F), Nat.card_eq_fintype_card (α := Fin (d - 1)),
    Fintype.card_fin]

open Classical in
/-- Helper [unit II-T4], **the pattern-free torus row sums**: for every anchor
c ∈ Fˣ, the UNCONSTRAINED interior-coefficient counts sum over the lead
coordinate to (q−1)·q^{d−1} — c-independent, the row value of the total-count
telescope (the pattern-free companion of II-T1's `torus_row_sum`). -/
theorem total_row_sum [Fintype F] {d : ℕ} (hd : 1 ≤ d) (c : Fˣ) :
    ∑ l : Fˣ, Nat.card {R : Polynomial F | R.natDegree = d ∧
        R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c}
      = (Fintype.card F - 1) * Fintype.card F ^ (d - 1) := by
  rw [Finset.sum_congr rfl fun l _ => card_fiber_lead_const hd l c, Finset.sum_const,
    Finset.card_univ, Fintype.card_units, smul_eq_mul]

open Classical in
/-- **The divisor is the total count** [unit II-T4]: the anchored chain sum of
the pattern-FREE interior-coefficient counts — the total number of joint
residue configurations — equals the blueprint's divisor (q−1)^k·q^{Σ(d_j−1)}.
This is what makes `jc_prob_core`'s division an honest probability. -/
theorem jc_total_count (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 1 ≤ d j) :
    (∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          Nat.card {R : Polynomial F | R.natDegree = d j ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)}
      else 0) =
    (Fintype.card F - 1) ^ k * Fintype.card F ^ (∑ j : Fin k, (d j - 1)) := by
  refine (chain_telescope (F := F) (k := k)
    (fun j l c => Nat.card {R : Polynomial F | R.natDegree = d j ∧
      R.leadingCoeff = ↑l ∧ R.coeff 0 = ↑c})
    (fun j => (Fintype.card F - 1) * Fintype.card F ^ (d j - 1))
    (fun j c => total_row_sum (hd j) c)).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

open Classical in
/-- **The marginal count** [unit II-T4] — the §2 sketch's "re-running II-T2
with one face unsummed": in the anchored chain, face i keeps its pattern
constraint ρ_i while every other face runs pattern-free; the telescope
evaluates to (monic z-free count)_i · ∏_{j≠i} (q−1)·q^{d_j−1}. -/
theorem jc_marginal_core (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 1 ≤ d j) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) (i : Fin k) :
    (∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          (if j = i then
            Nat.card {R : Polynomial F | R.natDegree = d j ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
              patternOf R = ρ j}
          else
            Nat.card {R : Polynomial F | R.natDegree = d j ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)})
      else 0) =
    Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d i ∧
        S.coeff 0 ≠ 0 ∧ patternOf S = ρ i} *
      ∏ j ∈ Finset.univ.erase i, ((Fintype.card F - 1) * Fintype.card F ^ (d j - 1)) := by
  refine (chain_telescope (F := F) (k := k)
    (fun j l c =>
      if j = i then
        Nat.card {R : Polynomial F | R.natDegree = d j ∧ R.leadingCoeff = ↑l ∧
          R.coeff 0 = ↑c ∧ patternOf R = ρ j}
      else
        Nat.card {R : Polynomial F | R.natDegree = d j ∧ R.leadingCoeff = ↑l ∧
          R.coeff 0 = ↑c})
    (fun j =>
      if j = i then
        Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d j ∧
          S.coeff 0 ≠ 0 ∧ patternOf S = ρ j}
      else (Fintype.card F - 1) * Fintype.card F ^ (d j - 1))
    (fun j c => ?_)).trans ?_
  · by_cases hji : j = i
    · simp only [if_pos hji]
      exact torus_row_sum (d j) (ρ j) c
    · simp only [if_neg hji]
      exact total_row_sum (hd j) c
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [if_pos rfl]
    exact congrArg _ (Finset.prod_congr rfl fun j hj =>
      if_neg (Finset.ne_of_mem_erase hj))

/-- **The blueprint's display identity** [unit II-T4]: (x−1)·x^{d−1} =
x^d − x^{d−1} for d ≥ 1 — the per-face total in its docstring form. -/
theorem sub_one_mul_pow_pred (x : ℚ) {d : ℕ} (hd : 1 ≤ d) :
    (x - 1) * x ^ (d - 1) = x ^ d - x ^ (d - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [show 1 + m - 1 = m by omega, pow_add, pow_one]
  ring

/-- Helper [unit II-T4]: the ℚ-cast of the per-face total (q−1)·q^m. -/
private theorem cast_face_total [Fintype F] (m : ℕ) :
    (((Fintype.card F - 1) * Fintype.card F ^ m : ℕ) : ℚ)
      = ((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ m := by
  have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
  push_cast [Nat.cast_sub h1]
  ring

open Classical in
/-- **(JC) probability, telescope content** [unit II-T4, PROVED half — see
the section note: the blueprint display is elided and its Ppoly numerators
are refuted-blocked with II-F8/F9]: the joint configuration count divided by
the blueprint divisor (q−1)^k·q^{Σ(d_j−1)} — which IS the total count,
`jc_total_count` — equals the product over faces of
(monic z-free count)_j / ((q−1)·q^{d_j−1}): one ℚ-value per face. -/
theorem jc_prob_core (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) :
    ((∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          Nat.card {R : Polynomial F | R.natDegree = d j ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ρ j}
      else 0 : ℕ) : ℚ) /
      (((Fintype.card F : ℚ) - 1) ^ k *
        (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1))) =
    ∏ j : Fin k,
      (Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d j ∧
          S.coeff 0 ≠ 0 ∧ patternOf S = ρ j} : ℚ) /
        (((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d j - 1)) := by
  rw [jc_count_core F d ρ, Nat.cast_prod, Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

open Classical in
/-- The docstring-shaped factors [unit II-T4]: via the display identity
`sub_one_mul_pow_pred`, each face factor of `jc_prob_core` is
(monic z-free count)_j / (q^{d_j} − q^{d_j−1}) — the blueprint's
"P_{ρ_j}(q)·(q^{d_j} − q^{d_j−1})⁻¹" with the (BLOCKED) Ppoly numerator
replaced by the count it denotes under the intended repaired Fact F(iii). -/
theorem jc_prob_core' (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 1 ≤ d j) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) :
    ((∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          Nat.card {R : Polynomial F | R.natDegree = d j ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ρ j}
      else 0 : ℕ) : ℚ) /
      (((Fintype.card F : ℚ) - 1) ^ k *
        (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1))) =
    ∏ j : Fin k,
      (Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d j ∧
          S.coeff 0 ≠ 0 ∧ patternOf S = ρ j} : ℚ) /
        ((Fintype.card F : ℚ) ^ (d j) - (Fintype.card F : ℚ) ^ (d j - 1)) := by
  rw [jc_prob_core F d ρ]
  exact Finset.prod_congr rfl fun j _ => by rw [sub_one_mul_pow_pred _ (hd j)]

open Classical in
/-- **The marginal probability** [unit II-T4]: face i's marginal count (its
pattern constrained, every other face free) divided by the SAME total
(q−1)^k·q^{Σ(d_j−1)} equals the face-i factor of `jc_prob_core` — the
per-face events have exactly the product's factors as probabilities. -/
theorem jc_prob_marginal (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 1 ≤ d j) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) (i : Fin k) :
    ((∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          (if j = i then
            Nat.card {R : Polynomial F | R.natDegree = d j ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
              patternOf R = ρ j}
          else
            Nat.card {R : Polynomial F | R.natDegree = d j ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)})
      else 0 : ℕ) : ℚ) /
      (((Fintype.card F : ℚ) - 1) ^ k *
        (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1))) =
    (Nat.card {S : Polynomial F | S.Monic ∧ S.natDegree = d i ∧
        S.coeff 0 ≠ 0 ∧ patternOf S = ρ i} : ℚ) /
      (((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d i - 1)) := by
  have hq : (1 : ℚ) < (Fintype.card F : ℚ) := by exact_mod_cast Fintype.one_lt_card
  have hX : (∏ j ∈ Finset.univ.erase i,
      (((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d j - 1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ =>
      mul_ne_zero (by linarith) (pow_ne_zero _ (by linarith))
  have hD : ((Fintype.card F : ℚ) - 1) ^ k *
      (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1)) =
      (((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d i - 1)) *
        ∏ j ∈ Finset.univ.erase i,
          (((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d j - 1)) := by
    rw [Finset.mul_prod_erase Finset.univ
        (fun j => ((Fintype.card F : ℚ) - 1) * (Fintype.card F : ℚ) ^ (d j - 1))
        (Finset.mem_univ i),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum]
  rw [jc_marginal_core F d hd ρ i, Nat.cast_mul, Nat.cast_prod,
    Finset.prod_congr rfl fun j _ => cast_face_total (F := F) (d j - 1), hD]
  exact mul_div_mul_right _ _ hX

open Classical in
/-- **INDEPENDENCE — the product of marginals** [unit II-T4]: the joint
probability equals the product over faces of the marginal probabilities,
every count divided by the SAME total (q−1)^k·q^{Σ(d_j−1)}
(= the total configuration count, `jc_total_count`). This is the L6d Step 3
independence statement, with the per-face factor values supplied by
`jc_prob_core`/`jc_prob_marginal`. -/
theorem jc_prob_indep (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 1 ≤ d j) (ρ : Fin k → Multiset (ℕ+ × ℕ+)) :
    ((∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k,
          Nat.card {R : Polynomial F | R.natDegree = d j ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ρ j}
      else 0 : ℕ) : ℚ) /
      (((Fintype.card F : ℚ) - 1) ^ k *
        (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1))) =
    ∏ i : Fin k,
      ((∑ V : Fin (k + 1) → Fˣ,
        if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
          ∏ j : Fin k,
            (if j = i then
              Nat.card {R : Polynomial F | R.natDegree = d j ∧
                R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
                R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
                patternOf R = ρ j}
            else
              Nat.card {R : Polynomial F | R.natDegree = d j ∧
                R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
                R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)})
        else 0 : ℕ) : ℚ) /
        (((Fintype.card F : ℚ) - 1) ^ k *
          (Fintype.card F : ℚ) ^ (∑ j : Fin k, (d j - 1))) := by
  rw [jc_prob_core F d ρ]
  exact Finset.prod_congr rfl fun i _ => (jc_prob_marginal F d hd ρ i).symm

open Classical in
/-- **BLOCKED(II-T4) refutation**: the intended (JC) probability display
"joint count / ((q−1)^k·q^{Σ(d_j−1)}) = ∏_j (Ppoly ρ_j).eval q /
(q^{d_j} − q^{d_j−1})" (BP_II §1.8, elided) is FALSE against the landed
`patternOf`, at the same witness as II-T3's `jc_count_ppoly_refuted`:
k = 1, d₁ = 2, ρ₁ = {(1,2)}, over EVERY finite field — the joint probability
is 0 (`patternOf_ne_atom_one_two`) while the intended right side is
(q−1)/(q²−q) = 1/q ≠ 0 (`Ppoly_atom_one_two`). -/
theorem jc_prob_ppoly_refuted (F : Type*) [Field F] [Fintype F] :
    ¬ ((((∑ V : Fin 2 → Fˣ,
        if V ⟨1, Nat.lt_succ_self 1⟩ = 1 then
          ∏ j : Fin 1,
            Nat.card {R : Polynomial F | R.natDegree = 2 ∧
              R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
              R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
              patternOf R = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))}
        else 0 : ℕ) : ℚ) /
        (((Fintype.card F : ℚ) - 1) ^ 1 * (Fintype.card F : ℚ) ^ 1)
      = ∏ _j : Fin 1,
          (Ppoly ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))).eval
              (Fintype.card F : ℚ) /
            ((Fintype.card F : ℚ) ^ 2 - (Fintype.card F : ℚ) ^ 1))) := by
  intro h
  haveI : IsEmpty ↥{S : Polynomial F | S.Monic ∧ S.natDegree = 2 ∧ S.coeff 0 ≠ 0 ∧
      patternOf S = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))} :=
    ⟨fun ⟨S, _, _, _, hpat⟩ => patternOf_ne_atom_one_two S hpat⟩
  have hcore : (∑ V : Fin 2 → Fˣ,
      if V ⟨1, Nat.lt_succ_self 1⟩ = 1 then
        ∏ j : Fin 1,
          Nat.card {R : Polynomial F | R.natDegree = 2 ∧
            R.leadingCoeff = ↑(V ⟨j, Nat.lt.step j.isLt⟩) ∧
            R.coeff 0 = ↑(V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩) ∧
            patternOf R = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))}
      else 0)
      = ∏ _j : Fin 1,
          Nat.card ↥{S : Polynomial F | S.Monic ∧ S.natDegree = 2 ∧ S.coeff 0 ≠ 0 ∧
            patternOf S = ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+))} :=
    jc_count_core F (fun _ => 2)
      (fun _ => ({((1 : ℕ+), (2 : ℕ+))} : Multiset (ℕ+ × ℕ+)))
  rw [hcore, Fin.prod_univ_one, Nat.card_of_isEmpty, Nat.cast_zero, zero_div,
    Fin.prod_univ_one, Ppoly_atom_one_two] at h
  have h1 : (1 : ℚ) < (Fintype.card F : ℚ) := by exact_mod_cast Fintype.one_lt_card
  have hden : (Fintype.card F : ℚ) ^ 2 - (Fintype.card F : ℚ) ^ 1 ≠ 0 := by
    have : (Fintype.card F : ℚ) ^ 1 < (Fintype.card F : ℚ) ^ 2 := by nlinarith
    linarith
  rcases div_eq_zero_iff.mp h.symm with hnum | hzero
  · linarith
  · exact hden hzero

end JcProb

end LeanUrat.Scaffold
