/-
BP_II §1.8 — the torus telescope (`Scaffold/O12/Torus.lean`), units II-T2,
II-T1, II-T5.
Units in this file: II-T2 (`chain_telescope`) — the abstract fibered telescope
over shared-vertex chains, anchor V_{k+1} := 1 at index k (L6d Step 2);
II-T1 (`torus_count` + helpers `torus_monic_smul_mem` / `torus_fiber_smul_mem` /
`torusEquiv`) — (T1), the torus identity: the c-fiber count equals the monic
z-free count at every fixed pattern ρ and degree d, independent of c
(L6d Step 1; see its transcription note for the `#`/`open Cardinal in`
elaboration context and the II-F9-dependency scoping);
II-T5 (**BLOCKED — see its section note**): the intended consistency identity
`zfree_total` is displayed ELIDED in BP_II §1.8 (`theorem zfree_total ...`)
and its sole dependency II-F9 is BLOCKED-refuted (`FactF.lean`), with the
on-record disposition that II-T5 reassigns only after the `patternOf` dedup
repair lands. UNLIKE II-F8/F9, NO refutation touches II-T5's content —
compiled instance artifacts (`pattern_degree_one_iff`,
`pattern_degree_two_iff`, `Ppoly_atom_one_one`, `Ppoly_atom_two_one`,
`Ppoly_pair_one_one`, `zfree_total_one`, `zfree_total_two`) verify the
identity at d = 1, 2 with the index sets classified complete.
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

end LeanUrat.Scaffold
