/-
BP_III §1.6 — Module `Scaffold/DictIII/Locality.lean`: O-1thr Theorem 1 (D-14)
+ lemma stock.  This file currently holds unit III-T3 (`dev_congr_zp`, Lemma
DEV at ℤ_[p]) — the instance of III-G2 (`devg_congr`, GDOrder1.lean) at
O = ℤ_[p], π = p.  Src: O1thr §2.1 DEV.  The blueprint's §1.6 display is
`theorem dev_congr_zp (Φ : Polynomial ℤ_[p]) (hm : Φ.Monic) …`; the elided
tail is completed here EXACTLY as the ℤ_[p]-specialization of the III-G2
statement (which the O-1thr source states with "monic of degree d ≥ 1", hence
the `hd` binder), with the maximal ideal rendered as `Ideal.span {(p : ℤ_[p])}`
— the form §1.6's `read_locality` consumer displays.

Other §1.6 units (III-T1/T2/T5..T10) are separate prover assignments and
extend this file.
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.GDOrder1
import LeanUrat.MovesC.Defs
import LeanUrat.Moves.ResVal

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime]

/-- **Unit III-T3 (Lemma DEV at the corpus carrier, O1thr §2.1).**
Developments of ≡-mod-p^L polynomials are ≡ mod p^L slotwise: if
`B ≡ B' (mod p^L)` coefficientwise, then every `Φ`-adic development
coefficient satisfies `devCoeff Φ B j ≡ devCoeff Φ B' j (mod p^L)`
coefficientwise.  Instance of III-G2 (`devg_congr`) at `O = ℤ_[p]`, `π = p`
(integrality of the slots is III-G1's `devCoeff`, already in `ℤ_[p][X]`). -/
theorem dev_congr_zp (Φ : Polynomial ℤ_[p]) (hm : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) (L : ℕ) {B B' : Polynomial ℤ_[p]}
    (h : ∀ k, (B - B').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ L) :
    ∀ j k, (devCoeff Φ B j - devCoeff Φ B' j).coeff k ∈
      (Ideal.span {(p : ℤ_[p])}) ^ L :=
  devg_congr (p : ℤ_[p]) PadicInt.maximalIdeal_eq_span_p.symm Φ hm hd L h

/-! ## Unit III-T1 — the read ceiling (O-1thr §3 NAT)

O-1thr §3 display: `I_i := γ_i/e_i` (the side line's value at slot 0, the
read's constrained-height bound), `E_i := H.strFrame i` (the accumulated
stretch), `L(H) := 1 + max_{i<k} ⌈I_i/E_i⌉ ∈ ℕ`.  The ceiling lands in ℕ via
`Nat.ceil` — for LAWFUL records `I_i/E_i ≥ 1 > 0` (O1thr §3 Lemma NAT), where
`Nat.ceil` and `Int.ceil` agree, and `Nat.ceil` keeps the record function
total and ℕ-valued on arbitrary records, exactly the source's `L(H) ∈ ℕ`
typing.  Node lookups are `H.nodes[i]?` (the same sanctioned spelling
convention as Carriers.lean: `List.get?` is removed in this pin), junk `0`
beyond the history as in the corpus `History.kappaH`.

Display adjustment (III-T1, binder only): the §1.6 display writes the theorem
binder as the untyped `(H)`; the ambient `{p} {F}` variables are not picked up
by a statement that never mentions them syntactically, and elaboration stalls
(exact error: "typeclass instance problem is stuck: Finite ?m.9" — the
instance's type argument stays a metavariable).  The binder is therefore
spelled with its unique well-typed reading `(H : MovesC.History p F)`.  The
proposition is unchanged; no other token differs from the display. -/

section ReadCeil

open LeanUrat.MovesC

variable {F : Type*} [Field F] [Finite F]

/-- The read ceiling L(H) := 1 + max_{i<k} ⌈I_i/E_i⌉, a record function (O-1thr §3).
    I_i, E_i from Node/Stage fields (I_i := the read's constrained-height bound;
    E_i := the accumulated stretch H.strFrame i). -/
def readCeil (H : MovesC.History p F) : ℕ :=
  1 + ((List.range H.nodes.length).map fun i =>
      ⌈(H.nodes[i]?).elim 0
          (fun ν => ((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ))⌉₊).foldr max 0

set_option linter.unusedVariables false in
/-- **Unit III-T1 (Lemma NAT positivity clause, O1thr §3).**  The read ceiling
is a positive integer; trivial from the leading `1 +` of the record function.
The `HistoryCoherent` hypothesis is part of the §1.6 display (kept VERBATIM,
hence the local linter silence — the positivity clause happens not to consume
it; the full Lemma NAT bound `L(H) ≥ 2` is where coherence earns its place). -/
theorem readCeil_pos (H : MovesC.History p F) (h : HistoryCoherent H) :
    1 ≤ readCeil H :=
  Nat.le_add_right 1 _

end ReadCeil

/-! ## Unit III-T5 — Lemma R-LOC (O-1thr §2.3, residual locality at `σ.R`)

Src: O1thr §2.3 R-LOC (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`).
The §1.6 display line is ELIDED (`theorem rloc (σ : Moves.Stage p F) …`), so
the statement is completed from the source of record — the same sanctioned
convention as Devid.lean's III-G18 (`bridge_equivDiv`) completion ledger:

* O1thr §2.3: if w(B − B′) > β and w(B) ≥ β, then B and B′ have the same
  image in gr_β(w) = P_β/P_β⁺, hence every residual/digit value the machine
  reads at height β agrees between B and B′.
* The corpus carrier is `Stage.R` (BP §3.2: "`Stage.R : … → LaurentPolynomial
  ↥K` is R-LOC's carrier (III-T5)"); `R(B) = [B]·T^{−w(B)}` (Moves/Defs.lean
  D.1(e)) is the recorded-unit-normalized coordinate of the gr-class at B's
  OWN height, so the faithful `σ.R` rendering pins the read height EXACTLY,
  `σ.w B = β` — precisely where the machine invokes R-LOC (brief §4 (R2):
  "w_i(B_j) = β_{i,j} exactly … by R-LOC … the height-β_{i,j} residuals
  agree"; (R5): "w_i(C_{μ_i}) = vhtx_i exactly, and R-LOC … transfers the
  height-vhtx_i residual").  Under a merely strict `w B > β` the source
  conclusion is the ZERO gr_β-class on both sides, which pins no `σ.R`
  equality — the `≥` form is not expressible at this carrier and is not what
  any consumer uses.
* The source hypothesis w(B − B′) > β silently covers B = B′ (0 ∈ P_β⁺
  trivially); the corpus `Stage.w` is a bare ℤ-valued function lawful only on
  nonzero arguments, so that degenerate case rides the guard `B ≠ B' →` (the
  conclusion is definitional there).  Nonzero-ness of B, B′ is the standing
  corpus side condition (every `Stage` residual law is so quantified).

Proof: the graded-residue definitional unfold — `Stage.hRlt` applied at
`B + (B′ − B)`, with the corpus engine's `ResVal.w_neg` aligning
`w(B − B′) = w(B′ − B)`. -/

section RLoc

variable {F : Type*} [Field F] [Finite F]

/-- Lemma R-LOC: height-β residuals agree when w(B − B′) > β (σ.R locality). -/
theorem rloc (σ : Moves.Stage p F) {β : ℤ} {B B' : Polynomial ℤ_[p]}
    (hB : B ≠ 0) (hB' : B' ≠ 0) (hwB : σ.w B = β)
    (hgt : B ≠ B' → β < σ.w (B - B')) :
    σ.R B = σ.R B' := by
  by_cases hne : B = B'
  · rw [hne]
  · have hg : B' - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hsum : B + (B' - B) = B' := by ring
    have hw : σ.w B < σ.w (B' - B) := by
      have h2 : σ.w (B - B') = σ.w (B' - B) := by
        have h3 := Moves.ResVal.w_neg σ (B' - B) hg
        rwa [neg_sub] at h3
      rw [hwB]
      calc β < σ.w (B - B') := hgt hne
        _ = σ.w (B' - B) := h2
    have hr := σ.hRlt B (B' - B) hB hg (by rw [hsum]; exact hB') hw
    rw [hsum] at hr
    exact hr.symm

end RLoc

end LeanUrat.Scaffold.DictIII
