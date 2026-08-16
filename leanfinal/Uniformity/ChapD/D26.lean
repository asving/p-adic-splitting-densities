/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D25a
import Uniformity.ChapB.B22

/-!
# Uniformity.ChapD.D26 — `gammaCoord`, `(C5-gamma)` point-free, and `γ ∘ L = id`

**Chapter D, NODE D.26** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1, A-D.2 govern — A-D.1/D-D4 RE-SIGNED both declarations with
`π` EXPLICIT and FIRST, and spelled the `Fin` coercion in the slot index). ENV-D4. Two signed
declarations, the blueprint's "split candidate (def / theorem)" kept in ONE file.

*`(C5-gamma)`, point-free, and `γ ∘ L = id`.*

* **(i) the normalized coordinate read.** For `A : Polynomial O`, a height `k : ℕ` and a slot
  `t : Fin f₁`, put `j := i(k) + e₁·t` (the `t`-th lattice slot above the reduced x-exponent)
  and `w := (k − j·h)/e₁ : ℤ` (the exact π-exponent that puts slot `j` at height `k`). Then
  `gammaCoord π e₁ h f₁ k A t` is B.21's digit `digAt π w (A.coeff j)` — the corpus's
  `res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})` — with junk `0` at `w < 0`, where the corpus's term
  "vanishes". The assembled `K₁`-element `γ_k(A) = Σ_t gammaCoord·η^t` is a two-line corollary
  for any carrier `(K₁, η, basis)` and is deliberately NOT a separate public name.
* **(ii) the residue identity `(C6-residue)`, point-free.** On the live domain
  (`e₁·f₁·h < M`), `gammaCoord π e₁ h f₁ M (liftC6 π e₁ h σ M l) t = l t` for every slot `t`:
  the coordinate read inverts D.24's lift, slotwise.

## What stays with chapter C (the blueprint's ⚠, transcribed)

The `ξ`-evaluation forms — `(C5-normalizer-read)` `res(A(ξ)/n̂(k)(ξ)) = ι_ξ(γ_k(A))` and
`(C5-varpi-read)` `res(A(ξ)/ϖ(ξ)^k) = ι_ξ(γ_k(A))·η_ξ^{−q(k)}` — quantify over tower points `ξ`
with compatible embeddings (`res(ξ^{e₁}/π^h) = ι_ξ(η)`), a valued-extension carrier `leanfinal`
does NOT have (GC-7). They are the embedding interface `EFF.T1.18 [supplied-by: chapter C]` and
are NOT stated here; the `η^{−q(k)}` factor of the second one is D.19's `res_chi_varpi`, so
chapter C's discharge is **this node + D.19 + C's own point carrier**. The HE6 F-1 provenance
("normalized slot coefficients in LEMMA HE6-0″") rides the same placeholder.

## Faithfulness

**⚠ Trust-boundary definition** (`gammaCoord`). Flagged for human review.

* *the junk branch is deliberate and is never read.* `w < 0` returns `0`; the theorem below
  runs only on the live domain, where D.25's `liftC6_exp_nonneg` puts `w = a(M) − t·h ≥ 0`, so
  the `if` is exact wherever anything is claimed. Slots `j ≥ D′` likewise read the zero
  coefficient of the polynomial, matching the corpus's vanishing.
* *`w` is an EXACT `Int` division on the live domain*, not a truncation: `k − j·h = e₁·(a(k) −
  t·h)` by D.13's exact-height identity, so `w = a(k) − t·h` on the nose
  (`Int.mul_ediv_cancel_left`).
* *`π` is EXPLICIT and FIRST* (defect D-D4, note SD-4): with `{π : O}` implicit, `π` occurs only
  under `digAt` and every call site would leave an unsolvable metavariable — Lean cannot invent
  the uniformizer. `f₁` is explicit here (it is not determined by `A`), unlike in D.24 where `l`
  determines it.

DEPENDS: D.13 (`iexp`, `aexp`, `iexp_aexp_spec`) · D.24 (`liftC6`) · D.25a
(`liftC6_exp_nonneg` — clause 1's exponent fact) · B.21 (`digAt`), B.22 (`digAt_eq`), all landed
· mathlib `Int.mul_ediv_cancel_left`, `Polynomial.finsetSum_coeff`,
`Polynomial.coeff_C_mul_X_pow`.

**PROOF.** 1. The coefficient of `X^{i(M)+e₁t}` in `liftC6 π e₁ h σ M l` is the single summand
`σ(l t)·π^{(a(M) − t·h).toNat}` — the defining sum collapses because `r ↦ i(M) + e₁r` is
injective for `0 < e₁` (D.25's step 3; private helpers `coeff_liftC6`/`coeff_liftC6_at`
re-derived here, chapter D's copies being private to `D25a`/`D25b`). 2. The slot exponent is
exact: `(M − (i(M) + e₁t)h)/e₁ = a(M) − t·h`, by D.13's identity. 3. `0 ≤ a(M) − t·h` on the
live domain (D.25a), so the `if` takes its live branch. 4. `digAt π n (σ(l t)·π^n) =
residue (σ (l t)) = l t` — B.22's `digAt_eq` (with `mul_comm` supplying the witness) and `hσ`.
This is the corpus's "Direct division turns each tying term into its normalized coefficient
residue" (`EFF.T1.18`), run on coordinates. The `gammaCoord` body is the gate-verified
`leanspec/Leanspec/ChapD.lean` stub body verbatim, with the landed namespace restored.

SOURCE: `EFF.T1.18` (the boxed `(C5-gamma)`; its two read displays → the ⚠ interface above);
`EFF.T1.20` (`(C6-residue)` — this is its point-free content); `EFF.T1.30` (A6: "`C5-gamma` and
its two reads prove the scalar pin", the GENTOW-6.3 OUT-interface).

**TEETH.** T1 §4.2 check 4; §7 attack 2 → **Lean theorem** (the identity `γ ∘ L = id`, which
fails outright if the slot index or the π-exponent is off by one). The `ξ`-read half → the
chapter-C placeholder recorded in §11's edges, NOT scored here. Nothing numeric runs in this
file: the arena is an abstract DVR with an abstract residue field, which admits no `decide`.

ENVIRONMENT: ENV-D4 (CHAP-B's ENV-A′ MINUS its `{π : O}` — per defect D-D4 both declarations
bind `π` themselves, explicitly and first, exactly as D.24/D.25 do).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open IsLocalRing Polynomial

-- ENV-D4 (blueprint §0.1) = CHAP-B's ENV-A′, MINUS its `{π : O}`: per defect D-D4 the nodes of
-- this file bind `π` themselves, explicitly and first.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **D.26 — `(C5-gamma)`, point-free: the normalized coordinate read.**
Slot `j = i(k) + e₁t`, π-exponent `w = (k − j·h)/e₁`, value the digit `digAt π w (A.coeff j)`
(B.21) — the corpus's `res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})` (`EFF.T1.18`).  Junk `0` on `w < 0`,
where the corpus's term vanishes; on the live domain the branch is never taken
(`liftC6_exp_nonneg`).  ⚠ `π` is EXPLICIT and FIRST (defect D-D4, note SD-4). -/
noncomputable def gammaCoord (π : O) (e₁ h f₁ : ℕ) (k : ℕ) (A : Polynomial O) (t : Fin f₁) :
    ResidueField O :=
  let j := iexp e₁ h k + e₁ * (t : ℕ)
  let w : ℤ := ((k : ℤ) - j * h) / e₁
  if 0 ≤ w then Uniformity.Density.Leaf.digAt π w.toNat (A.coeff j) else 0

/-- Slotwise read of `liftC6`. Private helper, byte-identical to `D25a`'s and `D25b`'s (their
copies are private to their own files; a shared public helper would breach GC-6.5). -/
private theorem coeff_liftC6 (π : O) {f₁ : ℕ} (e₁ h : ℕ) (σ : ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → ResidueField O) (j : ℕ) :
    (liftC6 π e₁ h σ M l).coeff j
      = ∑ r : Fin f₁, if j = iexp e₁ h M + e₁ * (r : ℕ)
          then σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat else 0 := by
  simp only [liftC6, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

/-- The coefficient AT a slot `i(M) + e₁r`: the sum collapses because `r ↦ i(M) + e₁r` is
injective for `0 < e₁`. Private helper, byte-identical to `D25a`'s and `D25b`'s. -/
private theorem coeff_liftC6_at (π : O) {f₁ : ℕ} (e₁ h : ℕ) (he : 0 < e₁)
    (σ : ResidueField O → O) (M : ℕ) (l : Fin f₁ → ResidueField O) (r : Fin f₁) :
    (liftC6 π e₁ h σ M l).coeff (iexp e₁ h M + e₁ * (r : ℕ))
      = σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat := by
  rw [coeff_liftC6, Finset.sum_eq_single r]
  · simp
  · intro b _ hb
    refine if_neg fun heq => hb (Fin.ext ?_)
    exact (Nat.eq_of_mul_eq_mul_left he (Nat.add_left_cancel heq)).symm
  · intro hb
    exact absurd (Finset.mem_univ r) hb

-- `hh : 0 < h` is a signed hypothesis of the frozen statement and is not consumed: the
-- π-exponent identity of step 2 is exact at every `h`, and the `h = 0` corner is already
-- covered by D.25's clause 1 (blueprint §13 item 6). Kept, not removed — the D.25 precedent.
set_option linter.unusedVariables false in
/-- **D.26 — `(C6-residue)`, point-free: `γ ∘ L = id` on coordinates** (`EFF.T1.18`,
`EFF.T1.20`).  On the live domain `e₁f₁h < M`, reading slot `t` of D.24's lift returns the
`t`-th coordinate: "Direct division turns each tying term into its normalized coefficient
residue", run on coordinates.

⚠ The `ξ`-evaluation clauses `(C5-normalizer-read)` / `(C5-varpi-read)` stay with chapter C
(`EFF.T1.18 [supplied-by: chapter C]`) — see the module docstring. -/
theorem gammaCoord_liftC6 (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hh : 0 < h)
    (hf : 0 < f₁) (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (t : Fin f₁) :
    gammaCoord π e₁ h f₁ M (liftC6 π e₁ h σ M l) t = l t := by
  have hne : (e₁ : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hid : (iexp e₁ h M : ℤ) * h + aexp e₁ h M * e₁ = (M : ℤ) :=
    (iexp_aexp_spec e₁ h he hcop (M : ℤ)).2
  -- step 2: the slot π-exponent is EXACT.
  have hw : ((M : ℤ) - ((iexp e₁ h M + e₁ * (t : ℕ) : ℕ) : ℤ) * (h : ℤ)) / (e₁ : ℤ)
      = aexp e₁ h M - ((t : ℕ) : ℤ) * (h : ℤ) := by
    have hnum : ((M : ℤ) - ((iexp e₁ h M + e₁ * (t : ℕ) : ℕ) : ℤ) * (h : ℤ))
        = (e₁ : ℤ) * (aexp e₁ h M - ((t : ℕ) : ℤ) * (h : ℤ)) := by
      push_cast
      linarith [hid]
    rw [hnum, Int.mul_ediv_cancel_left _ hne]
  -- step 3: the live branch.
  have hnn : 0 ≤ aexp e₁ h M - ((t : ℕ) : ℤ) * (h : ℤ) :=
    liftC6_exp_nonneg π e₁ h f₁ hπ he hf hcop σ hσ hσ0 M hM t
  -- steps 1 and 4.
  simp only [gammaCoord, hw, if_pos hnn, coeff_liftC6_at π e₁ h he σ M l t]
  rw [Uniformity.Density.Leaf.digAt_eq hπ (mul_comm (σ (l t)) _), hσ]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.gammaCoord
#print axioms Uniformity.Density.Gauge.gammaCoord_liftC6

end AxCheck
