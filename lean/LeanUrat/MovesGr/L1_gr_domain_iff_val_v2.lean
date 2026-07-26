/-
MovesGr unit `L1_gr_domain_iff_val` (v2; the manifest-path file is an earlier attempt).
Statement byte-identical to `LeanUrat/MovesGr/MANIFEST.json`.

STATUS: forward direction (IsDomain → valuation) FULLY PROVED — in fact it needs no
domain hypothesis: `Rg.if_mul` + `Rg.mul_of` + degree-injectivity of `DirectSum.of`
already force `w (f*g) = w f + w g`. Backward direction: `Nontrivial` proved; ONE
`sorry` at `NoZeroDivisors S.Gr`.

WHY THE `sorry` CANNOT BE DISCHARGED (diagnosis, sharpened from "blocked" to FALSE):
the backward direction of the statement is UNPROVABLE because it is false as stated.
Since the RHS is unconditional (see above), the statement is equivalent to
  ∀ Rg : GradedRingStr S, IsDomain S.Gr (w.r.t. Rg.ring),
and `GradedRingStr` pins Rg.ring's MULTIPLICATION only on homogeneous elements
(`mul_of`), its unit (`one_def`), and `initialForm` laws (`if_mul`, `if_add_lt`) —
it never pins Rg.ring's ADDITION or ZERO to the DirectSum's. Counterexample scheme:
take S a genuine side valuation with ≥ 2 active degrees (e.g. the Gauss valuation
w = min coefficient p-adic valuation, which satisfies hval), let R₀ be the genuine
graded ring on S.Gr (DS addition, convolution product: the `L1_gradedRingStr_exists`
construction), and let R' := R₀ × R₀ (NOT a domain: (1,0)·(0,1) = 0). The set
H := range (DirectSum.of) of homogeneous elements embeds multiplicatively in R' by
h ↦ (h,h), with 1_{R'} = diag(initialForm 1) and 0_{R'} = diag(DS-0); both complements
S.Gr \ H and R' \ diag(H) have cardinality continuum, so a bijection φ : R' ≃ S.Gr
with φ ∘ diag = id on H exists (Cantor–Schröder–Bernstein). Transporting R' along φ
gives a `CommRing S.Gr` satisfying ALL four `GradedRingStr` fields (each field only
mentions products/units of H-elements, where the transported structure agrees with
R₀) — but it has zero divisors φ(1,0)·φ(0,1) = φ(0,0) = DS-0 = transported 0. So
LHS false, RHS true: the iff fails for this Rg.

Note this does NOT contradict the informal §B2-DEF D.1(c) (MOVES_2026-07-24.md
line 1937): there "gr is a domain" refers to the genuine graded ring, whose addition
IS the DirectSum's, and the leading-term argument goes through. FIX REQUIRED IN
Defs.lean (out of this unit's authority): add an additive compatibility field to
`GradedRingStr`, e.g.
  add_def : letI := ring; ∀ x y : S.Gr, x + y = DirectSum.instAdd... x y   (or
  state the ring as `DirectSum.commRing` of a `GCommRing` instance). With that field
the backward direction is the honest graded-domain leading-term argument: mul is then
determined everywhere by biadditivity + `mul_of`, and the top-degree component of a
product of nonzero elements is `pmul` of nonzero classes = `[ab]` with
w(ab) = w a + w b (hval), hence nonzero.

A machine-checked disproof needs the full genuine graded ring + a CSB transport;
out of budget for this unit. No axioms; `lake env lean` green except the 1 sorry.
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Inlined dep content (`L0_initialForm_ne_zero`): the initial form of a nonzero
element is nonzero — `[f] = 0` in degree `deg f` would mean `deg f < w f`, against
`deg_eq`. Stated OUTSIDE any `Rg.ring` scope: the `0` is the DirectSum zero. -/
private theorem if_ne_zero (S : SideVal p) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    S.initialForm f ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : S.Gr => x (S.deg f)) h
  simp only [SideVal.initialForm, DirectSum.of_eq_same, DirectSum.zero_apply] at h2
  simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at h2
  have hlt : (S.deg f : WithTop ℤ) < S.w f := h2
  rw [S.deg_eq hf] at hlt
  exact lt_irrefl _ hlt

theorem L1_gr_domain_iff_val (S : SideVal p) (Rg : GradedRingStr S) : (letI := Rg.ring; IsDomain S.Gr) ↔ (∀ f g, f ≠ 0 → g ≠ 0 → S.w (f * g) = S.w f + S.w g) := by
  letI := Rg.ring
  constructor
  · -- (⟹). In fact unconditional: `if_mul` + `mul_of` + degree-injectivity of `of`.
    intro _hdom f g hf hg
    have hfg : f * g ≠ 0 := mul_ne_zero hf hg
    have heq : DirectSum.of (fun γ => S.grPiece γ) (S.deg (f * g)) (S.mkPiece (f * g))
        = DirectSum.of (fun γ => S.grPiece γ) (S.deg f + S.deg g)
            (S.pmul (S.deg f) (S.deg g) (S.mkPiece f) (S.mkPiece g)) :=
      (Rg.if_mul f g hf hg).trans (Rg.mul_of _ _ _ _)
    have hdeg : S.deg (f * g) = S.deg f + S.deg g := by
      by_contra hne
      have hcomp := congrArg (fun x : S.Gr => x (S.deg (f * g))) heq
      simp only [DirectSum.of_eq_same] at hcomp
      rw [DirectSum.of_eq_of_ne (S.deg f + S.deg g) (S.deg (f * g)) _ hne] at hcomp
      -- hcomp : `[f*g] = 0` in its own degree piece — kills `deg_eq`
      simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at hcomp
      have hlt : (S.deg (f * g) : WithTop ℤ) < S.w (f * g) := hcomp
      rw [S.deg_eq hfg] at hlt
      exact lt_irrefl _ hlt
    have hcast : (↑(S.deg (f * g)) : WithTop ℤ) = ↑(S.deg f) + ↑(S.deg g) := by
      rw [hdeg, WithTop.coe_add]
    rw [S.deg_eq hfg, S.deg_eq hf, S.deg_eq hg] at hcast
    exact hcast
  · -- (⟸). Nontrivial: genuine (type-level, structure-independent).
    intro hval
    haveI hnt : Nontrivial S.Gr := nontrivial_of_ne _ _ (if_ne_zero S one_ne_zero)
    haveI hnzd : NoZeroDivisors S.Gr :=
      { eq_zero_or_eq_zero_of_mul_eq_zero := by
          intro a b hab
          -- FALSE for arbitrary `Rg`: `GradedRingStr` does not pin `Rg.ring`'s
          -- addition/zero to the DirectSum's, so `a`, `b` cannot be decomposed
          -- into homogeneous pieces and `mul_of` cannot reach general products.
          -- See the header for the transport counterexample (R₀ × R₀ along a
          -- bijection fixing homogeneous elements) and the Defs-level fix.
          sorry }
    exact NoZeroDivisors.to_isDomain _
