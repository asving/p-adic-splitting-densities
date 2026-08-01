/-
BP_IV §1.2 — the order-r census carrier root (`CensusCore.lean`).
Units in this file: C0a (`CensusData`, this unit) · later waves add C0b
(`d/period/J`), C0c (`wt/Gset/attainDim/s`), C0d (`onLineSlots`), and `ADMFull`
(declared immediately after the derived definitions, per BP_IV §1.0).
This module imports no value-side module (import graph: CensusCore → Hyps →
Census, never a cycle).
-/
import Mathlib

/-!
# The order-r census carriers [wave IV-0a]

**PROVENANCE (unit C0a; BP_IV §1.2).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement verbatim) and §1.0
  (module/namespace placement).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` (§§1, 5.1, the r4
  FULL-attainment form) and M08 (`M08-cl6-general_fable.md` §2, Theorem 2).
* Imports: `Mathlib` only.
-/

namespace LeanUrat.Scaffold

/-- The order-r census datum: the ledger of stage triples (e_i, h_i, f_i),
    i = 0..r, with e_i, f_i ≥ 1.  Derived: d = ∏ f_i (census field degree —
    O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the period
    e = ∏ e_i, the slot-weight function wt on the mixed-radix φ-monomial index
    set J (a Fintype), the graded pieces G_β, and s(β) = #{j | wt j ≤ β}. -/
structure CensusData where
  r : ℕ
  e : Fin (r + 1) → ℕ
  h : Fin (r + 1) → ℕ
  f : Fin (r + 1) → ℕ
  he : ∀ i, 1 ≤ e i
  hf : ∀ i, 1 ≤ f i
  triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i
  h_coprime : ∀ i, Nat.Coprime (h i) (e i)

/-!
**PROVENANCE (unit C0b; BP_IV §1.2, wave IV-0b).**  Derived defs, verbatim from
the blueprint: `d` = ∏ f_i (the census field degree, O-9's DELTA-3 index fix:
d = f₀⋯f_r, NOT f₀⋯f_{r−1}), `period` = ∏ e_i, and the mixed-radix φ-monomial
index set `J` (a Fintype — instance supplied immediately after the def).
-/

namespace CensusData

def d (D : CensusData) : ℕ := ∏ i, D.f i

def period (D : CensusData) : ℕ := ∏ i, D.e i

def J (D : CensusData) : Type := (i : Fin (D.r + 1)) → Fin (D.e i) × Fin (D.f i)

/-- `J` is a Fintype (the blueprint carrier docstring: "the mixed-radix
    φ-monomial index set J (a Fintype)"). -/
instance instFintypeJ (D : CensusData) : Fintype D.J :=
  inferInstanceAs (Fintype ((i : Fin (D.r + 1)) → Fin (D.e i) × Fin (D.f i)))

instance instDecidableEqJ (D : CensusData) : DecidableEq D.J :=
  inferInstanceAs (DecidableEq ((i : Fin (D.r + 1)) → Fin (D.e i) × Fin (D.f i)))

end CensusData

end LeanUrat.Scaffold
