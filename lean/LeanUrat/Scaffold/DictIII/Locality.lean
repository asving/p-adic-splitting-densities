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
import LeanUrat.HC2.Defs

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

/-! ## Unit III-T4 — Lemma POS at the corpus `Stage.w` (O-1thr §2.2)

Src: O1thr §2.2 POS (`lean/notes/openmath/O1thr_phaseB_verifybrief.md`,
verbatim-stable through rev4 per `O1thr_phaseB_attempt_rev3.md`).  The §1.6
code block carries NO display line for III-T4 (T3/T5 were elided with `…`;
T4 is absent outright), so the statement is completed from the unit table's
own display — row III-T4: "Lemma POS at the corpus `Stage.w`
(w ≥ 0, π-shift, ultrametric ⇒ w(B−B′) ≥ L·E)" — read against the source of
record, the same completion-ledger convention as III-T5 above:

* O1thr §2.2 asserts the three frame-valuation laws (i) w(B) ≥ 0,
  (ii) w(p·B) = E + w(B) (E the stretch, = w(p)), (iii) the ultrametric —
  and the consequence B ≡ B′ (mod p^L) ⟹ w(B − B′) ≥ L·E.  The row displays
  the laws as the hypotheses of the implication; they are the three named
  rows below, and the conclusion is the consequence.  Law (iii) is carried
  VERBATIM as a row even though the consequence proof (exactly the source's:
  B − B′ = p^L·C with C integral, so w(B − B′) = L·E + w(C) ≥ L·E) consumes
  only (i)-(ii) — same discipline as `readCeil_pos`'s unconsumed coherence
  hypothesis, hence the local linter silence.  At corpus consumption sites
  (ii) is `σ.hwmul` at `Polynomial.C p` (with E := σ.w (C p)) and (iii) is
  `σ.hwult` — Stage-record laws; (i) is genuinely a row (the corpus `Stage`
  does not record nonnegativity-on-integral-polynomials; the anticipated
  `StageCoreL` supply (BP §3.2) carries the tie/parent laws, not (i)).
* Congruence is rendered coefficientwise in the `Ideal.span {(p : ℤ_[p])}^L`
  form — the exact form of III-T3's `dev_congr_zp` above and of the §1.6
  `read_locality` display that consumes this lemma through (†) (III-T6).
* The guard `B ≠ B'` is the standing corpus side condition (the bare
  ℤ-valued `Stage.w` is lawful only on nonzero arguments — III-T5's ledger),
  and (i)-(ii) are likewise quantified over nonzero arguments. -/

section StagePos

variable {F : Type*} [Field F] [Finite F]

set_option linter.unusedVariables false in
/-- **Unit III-T4 (Lemma POS at the corpus `Stage.w`, O1thr §2.2).**
w ≥ 0 (`hpos`), π-shift (`hshift`), ultrametric (`hult`) ⇒
w(B − B′) ≥ L·E for `B ≡ B′ (mod p^L)` coefficientwise. -/
theorem stage_pos (σ : Moves.Stage p F) (E : ℤ) (L : ℕ)
    (hpos : ∀ C : Polynomial ℤ_[p], C ≠ 0 → 0 ≤ σ.w C)
    (hshift : ∀ C : Polynomial ℤ_[p], C ≠ 0 →
      σ.w (Polynomial.C (p : ℤ_[p]) * C) = E + σ.w C)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ.w f) (σ.w g) ≤ σ.w (f + g))
    {B B' : Polynomial ℤ_[p]} (hne : B ≠ B')
    (hcong : ∀ k, (B - B').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ L) :
    (L : ℤ) * E ≤ σ.w (B - B') := by
  have hsub : B - B' ≠ 0 := sub_ne_zero.mpr hne
  -- coefficientwise congruence ⇒ global division: B − B′ = p^L · D, D integral
  have hdvd : (Polynomial.C ((p : ℤ_[p]) ^ L)) ∣ (B - B') := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro k
    have hk := hcong k
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hk
  obtain ⟨D, hD⟩ := hdvd
  have hDne : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hD
    exact hsub hD
  have hpne : (Polynomial.C (p : ℤ_[p])) ≠ 0 := by
    simpa using PadicInt.prime_p.ne_zero
  -- the π-shift iterated: w(p^M · D) = M·E + w(D)
  have key : ∀ M : ℕ,
      σ.w ((Polynomial.C (p : ℤ_[p])) ^ M * D) = (M : ℤ) * E + σ.w D := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have h1 : (Polynomial.C (p : ℤ_[p])) ^ M * D ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hpne) hDne
      have h2 : (Polynomial.C (p : ℤ_[p])) ^ (M + 1) * D
          = Polynomial.C (p : ℤ_[p]) * ((Polynomial.C (p : ℤ_[p])) ^ M * D) := by
        ring
      rw [h2, hshift _ h1, ih]
      push_cast
      ring
  have hCpow : (Polynomial.C ((p : ℤ_[p]) ^ L) : Polynomial ℤ_[p])
      = (Polynomial.C (p : ℤ_[p])) ^ L := map_pow _ _ _
  rw [hCpow] at hD
  rw [hD, key L]
  have := hpos D hDne
  linarith

end StagePos

/-! ## Unit III-T7 — Theorem 1 transfer, (R1) clause (O-1thr §4 (R1))

Src: O1thr §4, the (R1) bullet of the Theorem 1 proof
(`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`).  Corpus rendering:
per BP §3.2 "the clause list Theorem 1 transfers IS `SideReads`'s" — the (R1)
side-support clause is `MovesJ.SideReads` clause (i) (`HC2/Defs.lean`), copied
VERBATIM below as `SideClauseR1`, with the definitional projection
`sideReads_r1` as the tie (the new def is a verbatim move of the clause).

The §1.6 code block carries NO display line for III-T7 (only III-T10's
assembled `read_locality`); the unit-table display is "threshold ⟺ via (†) +
ultrametric; 3 sub-cases as displayed" — completed from the source of record,
the same completion-ledger convention as III-T4/T5 above:

* (†) — `w_i(B_j − B′_j) ≥ L·E_i > I_i ≥ every constrained height` (unit
  III-T6, from DEV/POS/`readCeil` arithmetic) — enters as the NAMED HYPOTHESIS
  ROW `hdag`, in its sheared per-slot residue: the ONLY threshold clause (i)
  compares against is the recorded total side weight `γ = ν.gam` (the brief's
  "every sheared-height comparison reduces to the bare coefficient heights
  against the pulled-back thresholds"), so (†)'s clause-(i) content at slot `j`
  is exactly `ν.gam < e·w(B_j − B′_j) + j·h` wherever the developments differ.
  III-T10 discharges `hdag` from III-T6; nothing is discharged by fiat here.
* The 3 sub-cases as displayed in the source:
  (1) `B′_j = 0` — the clause is vacuous (its guard `B′_j ≠ 0` fails);
  (2) `B′_j ≠ 0` and `B_j ≠ 0` — by (†) and ultrametricity the sheared heights
      compare identically against `γ`: the support inequality transfers, and a
      sheared equality at `B′_j` forces `w(B_j) = w(B′_j)` (`w_eq_of_sub_gt`),
      so the equality-only-at-strides pattern transfers;
  (3) `B′_j ≠ 0` but `B_j = 0` — then `B′_j = −(B_j − B′_j)`, so by (†)
      `γ < e·w(B′_j) + j·h`: the strict inequality holds at `j` and no
      forbidden equality occurs.
* "threshold ⟺": (†) is symmetric under `B ↔ B′` (`ResVal.w_neg`), so the
  clause transfers both ways (`sideClauseR1_transfer_iff`) — the per-clause
  face of Theorem 1's "the converse is symmetric". -/

section R1Transfer

open LeanUrat.MovesC LeanUrat.MovesJ

variable {F : Type*} [Field F] [Finite F]

/-- **The (R1) side-support clause** — `MovesJ.SideReads` clause (i), VERBATIM
(`HC2/Defs.lean`): the read functional `e·w(B_j) + j·h` is ≥ the recorded total
side weight `γ` at every nonzero slot, with equality ONLY at the recorded
stride digits `j = s0 + e·k`, `pat k ≠ 0`.  Named so III-T10 can consume the
per-clause transfer; `sideReads_r1` is the definitional tie. -/
def SideClauseR1 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) : Prop :=
  (∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ)) ∧
  (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)

/-- The definitional projection: `SideClauseR1` IS `SideReads`'s clause (i). -/
theorem sideReads_r1 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) (h : SideReads ν B Nd Φnext) :
    SideClauseR1 ν B Nd :=
  h.1

/-- **Ultrametric threshold kernel** (the "(†) + ultrametric" mechanism of
O1thr §4 (R1)): if `w(a − b)` strictly exceeds `w(b)`, then `a ≠ 0` and
`w(a) = w(b)` — heights at or below the perturbation threshold are shared.
Stage laws used: `hwult` (ultrametric) and `ResVal.w_neg` (evenness). -/
theorem w_eq_of_sub_gt (σ : Moves.Stage p F) {a b : Polynomial ℤ_[p]}
    (hb : b ≠ 0) (hab : a - b ≠ 0) (h : σ.w b < σ.w (a - b)) :
    a ≠ 0 ∧ σ.w a = σ.w b := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_sub, Moves.ResVal.w_neg σ b hb] at h
    exact lt_irrefl _ h
  refine ⟨ha, ?_⟩
  have h0 : b + (a - b) = a := by ring
  have hge : σ.w b ≤ σ.w a := by
    have hu := σ.hwult b (a - b) hb hab (by rw [h0]; exact ha)
    rwa [h0, min_eq_left h.le] at hu
  have hle : σ.w a ≤ σ.w b := by
    by_contra hlt
    push Not at hlt
    have h0' : a + -(a - b) = b := by ring
    have hne : -(a - b) ≠ 0 := neg_ne_zero.mpr hab
    have hu := σ.hwult a (-(a - b)) ha hne (by rw [h0']; exact hb)
    rw [h0', Moves.ResVal.w_neg σ _ hab] at hu
    rcases le_total (σ.w a) (σ.w (a - b)) with hc | hc
    · rw [min_eq_left hc] at hu; omega
    · rw [min_eq_right hc] at hu; omega
  omega

/-- **Unit III-T7 (transfer direction): Theorem 1 transfer, (R1) clause**
(O1thr §4 (R1); BP Wave 3 row III-T7).  Under the (†) hypothesis row `hdag` —
the sheared height of `B_j − B′_j` strictly exceeds the recorded threshold
`γ = ν.gam` at every slot where the developments differ (III-T6's supply at
every lawful site) — the (R1) side-support clause transfers from `B` to `B′`.
The proof is the displayed three-sub-case analysis (section header ledger). -/
theorem sideClauseR1_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ)
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ))
    (h1 : SideClauseR1 ν B Nd) : SideClauseR1 ν B' Nd := by
  obtain ⟨hsupp, hstr⟩ := h1
  have hemul : ∀ x y : ℤ, x ≤ y → (ν.e : ℤ) * x ≤ (ν.e : ℤ) * y :=
    fun x y hxy => mul_le_mul_of_nonneg_left hxy (by positivity)
  constructor
  · -- support inequality at every nonzero slot of B′
    intro j hj hB'
    by_cases hEq : B j = B' j
    · -- degenerate: the slots agree; the clause is B's own
      rw [← hEq] at hB' ⊢
      exact hsupp j hj hB'
    · have hd : B j - B' j ≠ 0 := sub_ne_zero.mpr hEq
      have hdag' := hdag j hj hEq
      by_cases hB : B j = 0
      · -- sub-case (3): B′_j ≠ 0 but B_j = 0 — strict inequality from (†)
        rw [hB, zero_sub, Moves.ResVal.w_neg ν.σ (B' j) hB'] at hdag'
        linarith
      · -- sub-case (2), support leg: both nonzero — ultrametric + (†)
        have h0 : B j + -(B j - B' j) = B' j := by ring
        have hne : -(B j - B' j) ≠ 0 := neg_ne_zero.mpr hd
        have hu := ν.σ.hwult (B j) (-(B j - B' j)) hB hne
          (by rw [h0]; exact hB')
        rw [h0, Moves.ResVal.w_neg ν.σ _ hd] at hu
        have hs := hsupp j hj hB
        rcases le_total (ν.σ.w (B j)) (ν.σ.w (B j - B' j)) with hc | hc
        · rw [min_eq_left hc] at hu
          have := hemul _ _ hu
          linarith
        · rw [min_eq_right hc] at hu
          have := hemul _ _ hu
          linarith
  · -- equality only at the recorded strides
    intro j hj hB' heq
    by_cases hEq : B j = B' j
    · exact hstr j hj (by rw [hEq]; exact hB') (by rw [hEq]; exact heq)
    · have hd : B j - B' j ≠ 0 := sub_ne_zero.mpr hEq
      have hdag' := hdag j hj hEq
      by_cases hB : B j = 0
      · -- sub-case (3): no forbidden equality occurs
        exfalso
        rw [hB, zero_sub, Moves.ResVal.w_neg ν.σ (B' j) hB'] at hdag'
        linarith
      · -- sub-case (2), equality leg: w(B′_j) sits strictly below
        -- w(B_j − B′_j), so the heights agree and B's stride witness is B′'s
        have hprod : (ν.e : ℤ) * ν.σ.w (B' j)
            < (ν.e : ℤ) * ν.σ.w (B j - B' j) := by linarith
        have hwlt : ν.σ.w (B' j) < ν.σ.w (B j - B' j) :=
          lt_of_mul_lt_mul_left hprod (by positivity)
        obtain ⟨-, hwEq⟩ := w_eq_of_sub_gt ν.σ hB' hd hwlt
        exact hstr j hj hB (by rw [hwEq]; exact heq)

/-- **Unit III-T7: the "threshold ⟺" form.**  (†) is symmetric in `B ↔ B′`
(`w(B′_j − B_j) = w(B_j − B′_j)`, `ResVal.w_neg`), so the (R1) clause
transfers BOTH ways — the per-clause face of Theorem 1's "the converse is
symmetric" (O1thr §4). -/
theorem sideClauseR1_transfer_iff (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ)
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ)) :
    SideClauseR1 ν B Nd ↔ SideClauseR1 ν B' Nd := by
  constructor
  · exact sideClauseR1_transfer ν B B' Nd hdag
  · refine sideClauseR1_transfer ν B' B Nd ?_
    intro j hj hne
    have hne' : B j ≠ B' j := fun h => hne h.symm
    have hd : B j - B' j ≠ 0 := sub_ne_zero.mpr hne'
    have hflip : B' j - B j = -(B j - B' j) := by ring
    rw [hflip, Moves.ResVal.w_neg ν.σ _ hd]
    exact hdag j hj hne'

/-- Consumption wrapper for III-T10: the (R1) clause of a full `SideReads`
bundle on `B` transfers to `B′` under the (†) row. -/
theorem sideReads_r1_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ))
    (h : SideReads ν B Nd Φnext) : SideClauseR1 ν B' Nd :=
  sideClauseR1_transfer ν B B' Nd hdag (sideReads_r1 ν B Nd Φnext h)

end R1Transfer

/-! ## Unit III-T16 — Lemma ROOT-M (O-1thr §2.5, root confinement)

Src: O1thr §2.5 ROOT-M (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`
line 598).  BP_III's §1.6 block displays no line for this unit; per the
sanctioned completion convention (this file's III-T5 header), the statement is
completed from the source of record, at exactly the unit-row scope
(BP_III Wave-3 row III-T16): "w₀(B_j) ≥ 1 below m, = 0 at m; from
ord_{φ̄}(f̄) = m".

Completion ledger:

* Source setting: "At a root state of a track with reduction factor φ̄^m
  (m ≥ 2, so ord_{φ̄}(f̄) = m exactly): w_0(B_j) ≥ 1 for j < m and
  w_0(B_m) = 0."  Here B_j is the j-th Φ₀-adic development digit of f
  (III-G1 `devCoeff`), Φ₀ a monic lift of φ̄.
* The row's dep III-G3 (`gaussW`) is BLOCKED (see GDOrder1.lean), so w₀ is
  not a declaration.  For the INTEGRAL digits B_j ∈ ℤ_[p][X] the two clauses
  are literally: w₀(B_j) ≥ 1 ⟺ every coefficient of B_j is divisible by p
  ⟺ B_j reduces to 0 mod p; and w₀(B_m) = 0 ⟺ ¬(w₀(B_m) ≥ 1), since
  w₀ ≥ 0 is automatic on ℤ_[p][X].  The source proof itself makes this
  identification — "the φ̄-digits of f̄ below slot m vanish (w_0(B_j) ≥ 1,
  j < m) and the slot-m digit does not (w_0(B_m) = 0)" via "Lemma DEV with
  L = 1" — so the mod-p rendering `(devCoeff Φ f j).map PadicInt.toZMod = 0`
  (resp. `≠ 0`) is the source's own equivalent form, gaussW-free.  Reduction
  spelling `.map PadicInt.toZMod` is the corpus convention (O2aOrder1.lean).
* ord_{φ̄}(f̄) = m is rendered as the exact-order pair
  φ̄^m ∣ f̄ ∧ ¬φ̄^{m+1} ∣ f̄ (corpus precedent: MovesC/C3_vtxPolyNe.lean).
* The lemma's face-confinement tail ("consequently every principal face …")
  is OUTSIDE the unit row's scope (it is (M6c)(i)-at-root territory, the
  III-T11 consumers) and is not transcribed here.
* The setting binders `hd` (root key degree ≥ 1, this file's standing DEV
  convention) and `hm2` (the source's m ≥ 2 root-track multiplicity) are
  kept VERBATIM from the source setting; the digit clauses happen not to
  consume them (hence the local linter silence — the same discipline as
  III-T1's unused `HistoryCoherent`).

Proof: DEV bridge (III-G1 `devCoeff_map`: developing commutes with mod-p
reduction) + the two monic-division digit laws below (slot shift under
`Φ * ·`), then exact-order bookkeeping via `modByMonic_eq_zero_iff_dvd`. -/

section RootM

/-- III-T16 support: slot 0 of the development of `Φ * B` vanishes. -/
theorem devCoeff_mul_left_zero {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (B : Polynomial O) : devCoeff Φ (Φ * B) 0 = 0 := by
  simp only [devCoeff]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hΦ).mpr (dvd_mul_right Φ B)

/-- III-T16 support: developing `Φ * B` shifts slots up by one. -/
theorem devCoeff_mul_left_succ {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (B : Polynomial O) (j : ℕ) :
    devCoeff Φ (Φ * B) (j + 1) = devCoeff Φ B j := by
  simp only [devCoeff]
  rw [Polynomial.mul_divByMonic_cancel_left B hΦ]

/-- III-T16 support: the digits of `Φ^m * B` below slot `m` vanish. -/
theorem devCoeff_pow_mul_of_lt {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (B : Polynomial O) :
    ∀ {m j : ℕ}, j < m → devCoeff Φ (Φ ^ m * B) j = 0 := by
  intro m
  induction m with
  | zero => exact fun {j} hj => absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro j hj
    rw [pow_succ', mul_assoc]
    cases j with
    | zero => exact devCoeff_mul_left_zero hΦ _
    | succ j =>
      rw [devCoeff_mul_left_succ hΦ _ j]
      exact ih (Nat.lt_of_succ_lt_succ hj)

/-- III-T16 support: the slot-`m` digit of `Φ^m * B` is `B %ₘ Φ`. -/
theorem devCoeff_pow_mul_self {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (B : Polynomial O) :
    ∀ m : ℕ, devCoeff Φ (Φ ^ m * B) m = B %ₘ Φ := by
  intro m
  induction m with
  | zero => simp [devCoeff]
  | succ m ih =>
    rw [pow_succ', mul_assoc, devCoeff_mul_left_succ hΦ _ m]
    exact ih

set_option linter.unusedVariables false in
/-- **Unit III-T16 (Lemma ROOT-M, root confinement, O1thr §2.5).**  At a root
state of a track with reduction factor φ̄^m (`m ≥ 2`, so ord_{φ̄}(f̄) = m
exactly — the hypothesis pair `hdvd`/`hndvd`): the Φ₀-adic development digits
`B_j := devCoeff Φ f j` of `f` satisfy w₀(B_j) ≥ 1 for `j < m` (the digit
reduces to 0 mod p) and w₀(B_m) = 0 (the slot-`m` digit does not).  Digit
form per the completion ledger above (the source's own "Lemma DEV with
L = 1" identification); the face-confinement consequence is outside this
unit's row scope. -/
theorem rootM (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree)
    {f : Polynomial ℤ_[p]} {m : ℕ} (hm2 : 2 ≤ m)
    (hdvd : (Φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) ^ m ∣
      f.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))
    (hndvd : ¬ (Φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) ^ (m + 1) ∣
      f.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) :
    (∀ j < m, (devCoeff Φ f j).map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) = 0) ∧
      (devCoeff Φ f m).map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) ≠ 0 := by
  obtain ⟨B, hB⟩ := hdvd
  have hφ : ((Φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))).Monic := hΦ.map _
  constructor
  · intro j hj
    rw [devCoeff_map _ hΦ, hB]
    exact devCoeff_pow_mul_of_lt hφ B hj
  · rw [devCoeff_map _ hΦ, hB, devCoeff_pow_mul_self hφ B m]
    intro h0
    obtain ⟨k, hk⟩ := (Polynomial.modByMonic_eq_zero_iff_dvd hφ).mp h0
    exact hndvd ⟨k, by rw [hB, hk, pow_succ, mul_assoc]⟩

end RootM

/-! ## Unit III-T6 — the (†) display (O-1thr §4)

Src: O1thr §4 (†) (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`):

    w_i(B_j − B′_j) ≥ L·E_i > I_i     (†)

"(the strict middle inequality: I_i/E_i ≤ ⌈I_i/E_i⌉ ≤ L − 1 < L)".  The §1.6
code block carries NO display line for III-T6 (same situation as III-T4/T7
above), so the statement is completed from the unit table's own display —
row III-T6: "(†) display: w_i(B_j − B′_j) ≥ L·E_i > I_i (the strict middle
inequality)", proof sketch "III-T3 + III-T4 + `Nat.ceil` arith" — read
against the source of record, the completion-ledger convention of III-T4/T5:

* `L := readCeil H`, `E_i := H.strFrame i`, `I_i := ν.gam/ν.e` at the
  recorded node `ν` (`H.nodes[i]? = some ν`) — exactly the quantities
  III-T1's `readCeil` record function is built from (its slot-`i` entry is
  `⌈(I_i/E_i)⌉₊`).
* The FIRST inequality of (†) is III-T4's consequence (`stage_pos`, above)
  at `E := H.strFrame i`, `L := readCeil H`; its hypothesis rows (w ≥ 0,
  π-shift at `E_i`, ultrametric — quantified over nonzero arguments — plus
  the standing `B ≠ B'` guard) ride along VERBATIM.  The congruence
  hypothesis is the coefficientwise `Ideal.span {(p : ℤ_[p])} ^ readCeil H`
  form — III-T3's `dev_congr_zp` output shape, which is how consumers
  III-T7..T10 discharge it at development slots.
* The STRICT MIDDLE inequality `L·E_i > I_i` is the unit's new content —
  the source's parenthetical `Nat.ceil` chain
  `I_i/E_i ≤ ⌈I_i/E_i⌉₊ ≤ L − 1 < L` against the record function, then
  clearing the positive stretch `E_i` (every node has `1 ≤ e`, so
  `E_i ≥ 1`).  It is stated separately (`readCeil_strict_middle`) since it
  holds for EVERY recorded node with no valuation in sight; `dagger`
  assembles the (†) chain from it and III-T4.
* Scales: `I_i ∈ ℚ` (the record ratio, exactly as in `readCeil`'s body);
  `w`-values ∈ ℤ (the corpus `Stage.w`).  The middle inequality is stated
  in ℚ, the first leg in ℤ exactly as III-T4 emits it; (†) is the
  conjunction with each leg in its native scale (no information lost to
  casts; consumers project legs).
* `dagger_sheared` is (†)'s consumer-facing residue in III-T7's `hdag`-row
  shape — `γ < e·w(B_j − B′_j) + j·h` (the brief's "every sheared-height
  comparison reduces to the bare coefficient heights against the
  pulled-back thresholds β_{i,j} ≤ I_i"): from (†),
  `e·w(B_j − B′_j) ≥ e·(L·E_i) > e·I_i = γ` and `j·h ≥ 0`.  III-T10
  discharges T7's `hdag` through it. -/

section Dagger

open LeanUrat.MovesC

variable {F : Type*} [Field F] [Finite F]

/-- Every element of a `ℕ`-list is `≤` the list's `foldr max 0` (helper;
same content as the `MovesD/L9s_Astable.lean` private lemma). -/
private lemma t6_le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

/-- The accumulated stretch is positive — every read has `1 ≤ e` (helper;
same content as the corpus-local `HC2.strFrame_pos` copies). -/
private lemma t6_strFrame_pos (H : MovesC.History p F) (i : ℕ) :
    0 < H.strFrame i := by
  unfold MovesC.History.strFrame
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨ν, -, hν0⟩ := List.mem_map.mp h0
  exact absurd hν0.symm (by have := ν.he; omega)

/-- **Unit III-T6 (the strict middle inequality of (†), O1thr §4).**
`L·E_i > I_i` at every recorded node: `readCeil H` majorizes its own
slot-`i` ceiling entry, so `I_i/E_i ≤ ⌈I_i/E_i⌉₊ ≤ L − 1 < L` (the source's
parenthetical), and clearing the positive stretch `E_i` gives
`I_i < L·E_i`.  Pure `Nat.ceil` arithmetic on the record function. -/
theorem readCeil_strict_middle (H : MovesC.History p F) {i : ℕ}
    {ν : MovesC.Node p F} (hν : H.nodes[i]? = some ν) :
    (ν.gam : ℚ) / (ν.e : ℚ) < (readCeil H : ℚ) * (H.strFrame i : ℚ) := by
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hν
  -- the slot-i entry of the record function is majorized by the fold
  have hfold : ⌈((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ)⌉₊ ≤
      ((List.range H.nodes.length).map fun j =>
        ⌈(H.nodes[j]?).elim 0
            (fun ν => ((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame j : ℚ))⌉₊).foldr max 0 := by
    apply t6_le_foldr_max
    refine List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    simp [hν]
  have hL : ⌈((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ)⌉₊ < readCeil H := by
    have hdef : readCeil H = 1 + ((List.range H.nodes.length).map fun j =>
        ⌈(H.nodes[j]?).elim 0
            (fun ν => ((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame j : ℚ))⌉₊).foldr max 0 := rfl
    omega
  have hE : (0 : ℚ) < (H.strFrame i : ℚ) := by
    exact_mod_cast t6_strFrame_pos H i
  have h1 : ((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ) ≤
      (⌈((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ)⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : (⌈((ν.gam : ℚ) / (ν.e : ℚ)) / (H.strFrame i : ℚ)⌉₊ : ℚ) < (readCeil H : ℚ) := by
    exact_mod_cast hL
  exact (div_lt_iff₀ hE).mp (lt_of_le_of_lt h1 h2)

/-- **Unit III-T6 ((†) display, O1thr §4).**  At read `i` (recorded node
`ν`), for `B ≡ B' (mod p^{readCeil H})` coefficientwise:

    w(B − B′) ≥ L·E_i  >  I_i     (†)

first leg = III-T4's consequence (`stage_pos` at `E := H.strFrame i`,
`L := readCeil H`; its hypothesis rows ride along verbatim), strict middle
leg = `readCeil_strict_middle`. -/
theorem dagger (H : MovesC.History p F) {i : ℕ} {ν : MovesC.Node p F}
    (hν : H.nodes[i]? = some ν)
    (σ : Moves.Stage p F)
    (hpos : ∀ C : Polynomial ℤ_[p], C ≠ 0 → 0 ≤ σ.w C)
    (hshift : ∀ C : Polynomial ℤ_[p], C ≠ 0 →
      σ.w (Polynomial.C (p : ℤ_[p]) * C) = (H.strFrame i : ℤ) + σ.w C)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ.w f) (σ.w g) ≤ σ.w (f + g))
    {B B' : Polynomial ℤ_[p]} (hne : B ≠ B')
    (hcong : ∀ k, (B - B').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H)) :
    (readCeil H : ℤ) * (H.strFrame i : ℤ) ≤ σ.w (B - B') ∧
      (ν.gam : ℚ) / (ν.e : ℚ) < (readCeil H : ℚ) * (H.strFrame i : ℚ) :=
  ⟨stage_pos σ (H.strFrame i : ℤ) (readCeil H) hpos hshift hult hne hcong,
   readCeil_strict_middle H hν⟩

/-- **Unit III-T6 ((†) in the sheared per-slot residue — III-T7's `hdag`-row
shape).**  `γ < e·w(B − B′) + j·h` at every slot `j`: from (†),
`e·w(B − B′) ≥ e·(L·E_i) > e·I_i = γ`, and the shear term `j·h` is
nonnegative.  III-T10 discharges III-T7's `hdag` row through this (at
`σ := ν.σ`, `B := B_j - B'_j` the differing development slots). -/
theorem dagger_sheared (H : MovesC.History p F) {i : ℕ} {ν : MovesC.Node p F}
    (hν : H.nodes[i]? = some ν)
    (σ : Moves.Stage p F)
    (hpos : ∀ C : Polynomial ℤ_[p], C ≠ 0 → 0 ≤ σ.w C)
    (hshift : ∀ C : Polynomial ℤ_[p], C ≠ 0 →
      σ.w (Polynomial.C (p : ℤ_[p]) * C) = (H.strFrame i : ℤ) + σ.w C)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ.w f) (σ.w g) ≤ σ.w (f + g))
    {B B' : Polynomial ℤ_[p]} (hne : B ≠ B')
    (hcong : ∀ k, (B - B').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H))
    (j : ℕ) :
    ν.gam < (ν.e : ℤ) * σ.w (B - B') + (j : ℤ) * (ν.h : ℤ) := by
  obtain ⟨hw, hmid⟩ := dagger H hν σ hpos hshift hult hne hcong
  have he : (0 : ℚ) < (ν.e : ℚ) := by exact_mod_cast ν.he
  -- clear I_i's denominator: γ < (L·E_i)·e in ℚ, hence in ℤ
  have hq : (ν.gam : ℚ) < ((readCeil H : ℚ) * (H.strFrame i : ℚ)) * (ν.e : ℚ) :=
    (div_lt_iff₀ he).mp hmid
  have hz : ν.gam < ((readCeil H : ℤ) * (H.strFrame i : ℤ)) * (ν.e : ℤ) := by
    exact_mod_cast hq
  -- stretch the first leg of (†) by e ≥ 0
  have h1 : ((readCeil H : ℤ) * (H.strFrame i : ℤ)) * (ν.e : ℤ)
      ≤ (ν.e : ℤ) * σ.w (B - B') := by
    calc ((readCeil H : ℤ) * (H.strFrame i : ℤ)) * (ν.e : ℤ)
        = (ν.e : ℤ) * ((readCeil H : ℤ) * (H.strFrame i : ℤ)) := by ring
      _ ≤ (ν.e : ℤ) * σ.w (B - B') :=
          mul_le_mul_of_nonneg_left hw (by positivity)
  have hjh : (0 : ℤ) ≤ (j : ℤ) * (ν.h : ℤ) := by positivity
  linarith

end Dagger

/-! ## Unit III-T8 — Theorem 1 transfer, (R2) stride clause (O-1thr §4 (R2))

Src: O1thr §4, the (R2) bullet of the Theorem 1 proof
(`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`), QUOTED: "(R2) at a
stride slot j: w_i(B_j) = β_{i,j} ≤ I_i < L·E_i, so by (†) w_i(B′_j) = β_{i,j}
exactly and B′_j ≠ 0; by R-LOC (w_i(B_j − B′_j) > β_{i,j}) the height-β_{i,j}
residuals agree, so the recorded pattern value is read identically."

The §1.6 code block carries NO display line for III-T8 (only III-T10's
assembled `read_locality`); the unit-table display is "exact-height transfer +
R-LOC pattern read" — completed from the source of record, the same
completion-ledger convention as III-T4/T5/T7 above:

* Corpus rendering (BP §3.2 "the clause list Theorem 1 transfers IS
  `SideReads`'s"): the (R2) digit-pins clause is `MovesJ.SideReads` clause (ii)
  DIGITS (`HC2/Defs.lean`), copied VERBATIM below as `SideClauseR2` (a verbatim
  move, no new content), with the definitional projection `sideReads_r2` as
  the tie.  The clause is stated in the sheared read-functional form
  `e·w(B_j) + j·h = γ` — the source's `w_i(B_j) = β_{i,j}` pulled back through
  the slot shear (§4: "every sheared-height comparison reduces to the bare
  coefficient heights").
* (†) enters as the SAME named hypothesis row `hdag` as III-T7's (one III-T6
  supply at III-T10 feeds every per-clause unit): `γ < e·w(B_j − B′_j) + j·h`
  wherever the developments differ, `j < Nd`.  The stride slots sit below
  `Nd` because clause (ii) pins `B_j ≠ 0` while the development vanishes from
  `Nd` on — the `hvan` row, `IsDevelopment`'s second conjunct, supplied
  verbatim at every consumer.  III-T10 discharges `hdag` from III-T6; nothing
  is discharged by fiat here.
* "exact-height transfer": at a stride slot the height is PINNED
  (`e·w(B_j) + j·h = γ` exactly), so (†) puts the perturbation strictly above
  it and the ultrametric kernel `w_eq_of_sub_gt` (III-T7) gives `B′_j ≠ 0`
  with `w(B′_j) = w(B_j)` — the read-functional pin transfers EXACTLY.
* "R-LOC pattern read": III-T5's `rloc`, fired at the pinned height
  `β := w(B_j)` — the height-β residuals agree, so the recorded pattern value
  `pat k` is read identically.
* The pattern value's recorded normalization exponent `−t·wPrev(B_j)` also
  transfers: `wPrev(B′_j) = wPrev(B_j)` via the stretch law `Stage.hStretch`
  (DEF-4, `w = e·wPrev` on nonzero coefficients, `e ≥ 1` cancels) — whence
  the `inC` rows `hC`/`hC'`, `IsDevelopment`'s first conjunct at every
  consumer.
* Nonzero-ness guards ride the corpus convention (III-T5's ledger): `B_j ≠ 0`
  is clause (ii)'s own first conjunct; `B′_j ≠ 0` is CONCLUDED (the source's
  "B′_j ≠ 0"). -/

section R2Transfer

open LeanUrat.MovesC LeanUrat.MovesJ

variable {F : Type*} [Field F] [Finite F]

/-- **The (R2) digit-pins clause** — `MovesJ.SideReads` clause (ii) DIGITS,
VERBATIM (`HC2/Defs.lean`): at every recorded stride slot `j = s0 + e·k` with
`pat k ≠ 0`, the coefficient is nonzero, ON the side (the read functional
`e·w(B_j) + j·h` equals the recorded total side weight `γ` exactly), and its
residual is the monomial-unit with scalar `pat k` at the forced (S5) position.
Named so III-T10 can consume the per-clause transfer; `sideReads_r2` is the
definitional tie. -/
def SideClauseR2 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) : Prop :=
  ∀ k : ℕ, k ≤ ν.wSide / ν.e → ν.pat k ≠ 0 →
      B (ν.s0 + ν.e * k) ≠ 0 ∧
      (ν.e : ℤ) * ν.σ.w (B (ν.s0 + ν.e * k)) + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ)
        = ν.gam ∧
      ν.σ.R (B (ν.s0 + ν.e * k)) = LaurentPolynomial.C (ν.pat k) *
        LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (B (ν.s0 + ν.e * k)))

/-- The definitional projection: `SideClauseR2` IS `SideReads`'s clause (ii). -/
theorem sideReads_r2 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) (h : SideReads ν B Nd Φnext) :
    SideClauseR2 ν B :=
  h.2.1

/-- **III-T8 slot kernel (exact-height transfer + R-LOC read, one slot).**
If the perturbation sits strictly above the slot's own height
(`w b < w (b − b')` whenever `b ≠ b'` — (†)'s content at a PINNED slot), then
the primed coefficient is nonzero, at the SAME height (`w_eq_of_sub_gt`,
III-T7's ultrametric kernel), at the same parent-scale weight (`hStretch`,
`e ≥ 1` cancellation), and with the SAME residual (III-T5's `rloc` at
`β := w b`): the recorded pattern value is read identically. -/
theorem r2_slot_transfer (σ : Moves.Stage p F) {b b' : Polynomial ℤ_[p]}
    (hb : b ≠ 0) (hbC : Moves.inC σ.Φ b) (hb'C : Moves.inC σ.Φ b')
    (hgap : b ≠ b' → σ.w b < σ.w (b - b')) :
    b' ≠ 0 ∧ σ.w b' = σ.w b ∧ σ.wPrev b' = σ.wPrev b ∧ σ.R b' = σ.R b := by
  by_cases heq : b = b'
  · subst heq
    exact ⟨hb, rfl, rfl, rfl⟩
  · have hd : b - b' ≠ 0 := sub_ne_zero.mpr heq
    have hw : σ.w b < σ.w (b - b') := hgap heq
    -- exact-height transfer: III-T7's ultrametric kernel at a := b'
    have hd' : b' - b ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
    have hflip : b' - b = -(b - b') := by ring
    obtain ⟨hb'ne, hwe⟩ := w_eq_of_sub_gt σ hb hd'
      (by rw [hflip, Moves.ResVal.w_neg σ _ hd]; exact hw)
    -- R-LOC pattern read: III-T5's `rloc` at the pinned height β := σ.w b
    have hR : σ.R b' = σ.R b := (rloc σ hb hb'ne rfl fun _ => hw).symm
    -- parent-scale weight via the stretch law (DEF-4); `e ≥ 1` cancels
    have hwp : σ.wPrev b' = σ.wPrev b := by
      have hs := σ.hStretch b hb hbC
      have hs' := σ.hStretch b' hb'ne hb'C
      have he' : (1 : ℤ) ≤ (σ.e : ℤ) := by exact_mod_cast σ.he
      have hene : (σ.e : ℤ) ≠ 0 := by omega
      refine mul_left_cancel₀ hene ?_
      rw [← hs, ← hs', hwe]
    exact ⟨hb'ne, hwe, hwp, hR⟩

/-- **Unit III-T8 (transfer direction): Theorem 1 transfer, (R2) stride
clause** (O1thr §4 (R2); BP Wave 3 row III-T8).  Under the (†) hypothesis row
`hdag` (III-T7's shape — one III-T6 supply at III-T10 feeds every per-clause
unit), the development-truncation row `hvan` and the coefficient-space rows
`hC`/`hC'` (`IsDevelopment`'s two conjuncts at every consumer), the (R2)
digit-pins clause transfers from `B` to `B′`: exact-height transfer at every
stride slot + R-LOC pattern read (`r2_slot_transfer`). -/
theorem sideClauseR2_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ)
    (hvan : ∀ j : ℕ, Nd ≤ j → B j = 0)
    (hC : ∀ j, Moves.inC ν.σ.Φ (B j)) (hC' : ∀ j, Moves.inC ν.σ.Φ (B' j))
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ))
    (h2 : SideClauseR2 ν B) : SideClauseR2 ν B' := by
  intro k hk hpat
  obtain ⟨hBne, hpin, hres⟩ := h2 k hk hpat
  set j := ν.s0 + ν.e * k with hj
  -- the stride slot sits below the truncation: B_j ≠ 0 but B vanishes ≥ Nd
  have hjNd : j < Nd := by
    by_contra hge
    exact hBne (hvan j (Nat.le_of_not_lt hge))
  -- (†) at the pinned slot: the perturbation sits strictly above the height
  have hgapw : B j ≠ B' j → ν.σ.w (B j) < ν.σ.w (B j - B' j) := by
    intro hne
    have hg := hdag j hjNd hne
    have hprod : (ν.e : ℤ) * ν.σ.w (B j) < (ν.e : ℤ) * ν.σ.w (B j - B' j) := by
      linarith
    exact lt_of_mul_lt_mul_left hprod (by positivity)
  obtain ⟨hB'ne, hwe, hwp, hR⟩ := r2_slot_transfer ν.σ hBne (hC j) (hC' j) hgapw
  refine ⟨hB'ne, ?_, ?_⟩
  · -- the read-functional pin transfers EXACTLY (w(B′_j) = w(B_j))
    rw [hwe]
    exact hpin
  · -- the recorded pattern value is read identically (R-LOC + wPrev transfer)
    rw [hR, hwp]
    exact hres

/-- **Unit III-T8: the symmetric form.**  (†) is symmetric in `B ↔ B′`
(`w(B′_j − B_j) = w(B_j − B′_j)`, `ResVal.w_neg`), so with both truncation
rows the (R2) clause transfers BOTH ways — the per-clause face of Theorem 1's
"the converse is symmetric" (O1thr §4). -/
theorem sideClauseR2_transfer_iff (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ)
    (hvan : ∀ j : ℕ, Nd ≤ j → B j = 0) (hvan' : ∀ j : ℕ, Nd ≤ j → B' j = 0)
    (hC : ∀ j, Moves.inC ν.σ.Φ (B j)) (hC' : ∀ j, Moves.inC ν.σ.Φ (B' j))
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ)) :
    SideClauseR2 ν B ↔ SideClauseR2 ν B' := by
  constructor
  · exact sideClauseR2_transfer ν B B' Nd hvan hC hC' hdag
  · refine sideClauseR2_transfer ν B' B Nd hvan' hC' hC ?_
    intro j hj hne
    have hne' : B j ≠ B' j := fun h => hne h.symm
    have hd : B j - B' j ≠ 0 := sub_ne_zero.mpr hne'
    have hflip : B' j - B j = -(B j - B' j) := by ring
    rw [hflip, Moves.ResVal.w_neg ν.σ _ hd]
    exact hdag j hj hne'

/-- Consumption wrapper for III-T10: the (R2) clause of a full `SideReads`
bundle on `B` transfers to `B′` under the (†) row + the `IsDevelopment` rows. -/
theorem sideReads_r2_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd : ℕ) (Φnext : Polynomial ℤ_[p])
    (hvan : ∀ j : ℕ, Nd ≤ j → B j = 0)
    (hC : ∀ j, Moves.inC ν.σ.Φ (B j)) (hC' : ∀ j, Moves.inC ν.σ.Φ (B' j))
    (hdag : ∀ j : ℕ, j < Nd → B j ≠ B' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - B' j) + (j : ℤ) * (ν.h : ℤ))
    (h : SideReads ν B Nd Φnext) : SideClauseR2 ν B' :=
  sideClauseR2_transfer ν B B' Nd hvan hC hC' hdag (sideReads_r2 ν B Nd Φnext h)

end R2Transfer

/-! ## Unit III-T9 — Theorem 1 transfer, (R5) vertex clause (O-1thr §4 (R5))

Src: O1thr §4, the (R5) bullet of the Theorem 1 proof
(`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md` lines 913–924).
Corpus rendering: per BP §3.2 "the clause list Theorem 1 transfers IS
`SideReads`'s" — the (R5) vertex read-off is `MovesJ.SideReads` clause (vi)
(`HC2/Defs.lean`), copied VERBATIM below as `SideClauseR5`, with the
definitional projection `sideReads_r5` as the tie (III-T7's convention).

The §1.6 code block carries NO display line for III-T9 (only III-T10's
assembled `read_locality`); the unit-table display — "(†′) rederived at
Φ_{i+1}; DEV/POS verbatim at the child key; R-LOC at vtx" — is completed
from the source of record, the same completion-ledger convention as
III-T4/T5/T7/T8:

* Source (R5) transfer: "Let (C_j), (C′_j) be the Φ_{i+1}-adic developments
  of f, f′; by DEV (applied with Φ = Φ_{i+1}), C_j ≡ C′_j (mod p^L), so by
  POS  w_i(C_j − C′_j) ≥ L·E_i > I_i ≥ vhtx_i  (†′) — the Φ_{i+1}-analogue
  of (†), rederived rather than reused ...  Since w_i(C_{μ_i}) = vhtx_i ≤
  I_i < L·E_i, ultrametricity and (†′) give w_i(C′_{μ_i}) = vhtx_i exactly,
  and R-LOC (w_i(C_μ − C′_μ) > vhtx_i) transfers the height-vhtx_i
  residual; the recorded vertex value vtx_i is read identically."
* DEV/POS VERBATIM AT THE CHILD KEY = `childDev_pos`: III-T3's
  `dev_congr_zp` instantiated at `Φnext`, composed with III-T4's
  `stage_pos` (its three law rows riding along verbatim) — (†′)'s lower
  half.  (†) itself (III-T6 `dagger`, the Φ_i-development display) is NOT
  invoked — the source's own "rederived rather than borrowed" (rev-4
  changelog line 21).
* The heights stay measured in `ν.σ.w` (= w_i, the CURRENT frame): `Φnext`
  enters only as the development key, never through w_{i+1} — (R5)'s own
  prescription ("The valuation and grading are those of w_i ... Φ_{i+1}
  enters only as the development key, never through w_{i+1}").  The HK-52
  e′-stretch seam (`ν_{i+1}.e`; BP §3.3 fence) is therefore never crossed:
  no `σ_{i+1}.w` occurs in any statement below, so no `e′ = 1` hypothesis
  is needed — the fence demands displayed `e′ = 1` wherever the seam IS
  crossed.
* (†′)'s upper leg — the vertex slot is nonzero and its height sits
  strictly below the perturbation floor L·E_i (w_i(C_μ) = vhtx ≤ I_i <
  L·E_i: law (N4) + Lemma CEIL) — enters as the NAMED HYPOTHESIS ROWS
  `hvne`/`hvlt`, exactly III-T7's `hdag` discipline: III-T10/T11 discharge
  them from the σV-vertex law (`HK11a.sigmaV_vertexLaw`, whose first two
  conclusions are literally `B μ ≠ 0` and the vertex-height pin — BP §3.1:
  "the (R5) vertex-clause vocabulary IS this law's", with its carried trio
  hσL/hsteep/species displayed THERE) + `readCeil_strict_middle`;
  `childDev_dag` below assembles the rows' discharge shape.  Nothing is
  discharged by fiat here.
* R-LOC at vtx = III-T5's `rloc` at `β := ν.σ.w (C_μ)` — the corpus digit
  is read at the coefficient's OWN weight (`σ.R` normalizes at `w(B)`;
  the rev-2 restatement ledger, III-T5 header), so the recorded-height
  binder `vhtx` of the source display is realized as `w(C_μ)` itself. -/

section R5Transfer

open LeanUrat.MovesC LeanUrat.MovesJ

variable {F : Type*} [Field F] [Finite F]

/-- **The (R5) vertex read-off clause** — `MovesJ.SideReads` clause (vi),
VERBATIM (`HC2/Defs.lean`): at the read's window vertex — slot `μ` of the
development in the DESIGNATED NEXT key — the actual frame-`i` residual digit
IS the recorded transported vertex value.  Named so III-T10 can consume the
per-clause transfer; `sideReads_r5` is the definitional tie. -/
def SideClauseR5 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) : Prop :=
  ∀ (Bh : ℕ → Polynomial ℤ_[p]) (Nh : ℕ),
    Moves.IsDevelopment Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) Bh Nh →
    ν.σ.digPrime ν.zbar (Bh ν.μ) = ν.vtx

/-- The definitional projection: `SideClauseR5` IS `SideReads`'s clause (vi). -/
theorem sideReads_r5 (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) (h : SideReads ν B Nd Φnext) :
    SideClauseR5 ν B Nd Φnext :=
  h.2.2.2.2.2

/-- **(†′) lower half — Lemma DEV + Lemma POS verbatim at the child key** (the
source's "rederived rather than reused" step): if `g ≡ g′ (mod p^L)`
coefficientwise, every differing slot of their `Φnext`-adic developments has
weight ≥ L·E in the CURRENT frame — III-T3 (`dev_congr_zp`) instantiated at
the monic child key, composed with III-T4 (`stage_pos`), nothing else. -/
theorem childDev_pos (σ : Moves.Stage p F) {Φnext : Polynomial ℤ_[p]}
    (hm : Φnext.Monic) (hd : 1 ≤ Φnext.natDegree) (E : ℤ) (L : ℕ)
    (hpos : ∀ C : Polynomial ℤ_[p], C ≠ 0 → 0 ≤ σ.w C)
    (hshift : ∀ C : Polynomial ℤ_[p], C ≠ 0 →
      σ.w (Polynomial.C (p : ℤ_[p]) * C) = E + σ.w C)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ.w f) (σ.w g) ≤ σ.w (f + g))
    {g g' : Polynomial ℤ_[p]}
    (hcong : ∀ k, (g - g').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ L)
    (j : ℕ) (hne : devCoeff Φnext g j ≠ devCoeff Φnext g' j) :
    (L : ℤ) * E ≤ σ.w (devCoeff Φnext g j - devCoeff Φnext g' j) :=
  stage_pos σ E L hpos hshift hult hne (dev_congr_zp Φnext hm hd L hcong j)

/-- **(†′) assembled at a slot** (the source display "w_i(C_μ) = vhtx ≤ I_i <
L·E_i, ultrametricity and (†′)"): DEV/POS at the child key plus the
slot-height ceiling `hvhtx` (where law (N4)/Lemma CEIL — the σV-vertex-law
supply, III-T10/T11's leg — lands) yield III-T9's `hvlt` row shape. -/
theorem childDev_dag (σ : Moves.Stage p F) {Φnext : Polynomial ℤ_[p]}
    (hm : Φnext.Monic) (hd : 1 ≤ Φnext.natDegree) (E : ℤ) (L : ℕ)
    (hpos : ∀ C : Polynomial ℤ_[p], C ≠ 0 → 0 ≤ σ.w C)
    (hshift : ∀ C : Polynomial ℤ_[p], C ≠ 0 →
      σ.w (Polynomial.C (p : ℤ_[p]) * C) = E + σ.w C)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ.w f) (σ.w g) ≤ σ.w (f + g))
    {g g' : Polynomial ℤ_[p]}
    (hcong : ∀ k, (g - g').coeff k ∈ (Ideal.span {(p : ℤ_[p])}) ^ L)
    (j : ℕ) (hvhtx : σ.w (devCoeff Φnext g j) < (L : ℤ) * E) :
    devCoeff Φnext g j ≠ devCoeff Φnext g' j →
      σ.w (devCoeff Φnext g j) < σ.w (devCoeff Φnext g j - devCoeff Φnext g' j) :=
  fun hne =>
    lt_of_lt_of_le hvhtx (childDev_pos σ hm hd E L hpos hshift hult hcong j hne)

/-- **Unit III-T9 (transfer direction): Theorem 1 transfer, (R5) vertex
clause** (O1thr §4 (R5); BP Wave 3 row III-T9).  Under the named rows `hvne`
(the vertex slot of `B`'s child-key development is nonzero — the σV-vertex
law's first leg) and `hvlt` (the (†′) height gap at the vertex: wherever the
two canonical vertex slots differ, the perturbation weight strictly exceeds
the vertex's own height — `childDev_dag`'s conclusion), the (R5) clause
transfers from `B` to `B′`.  Mechanism: Fact-A uniqueness folds any
development onto the canonical `devCoeff` slots (III-G1 bridge), then R-LOC
(`rloc`, III-T5) at `β := ν.σ.w (C_μ)` transfers the vertex digit. -/
theorem sideClauseR5_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd Nd' : ℕ) (Φnext : Polynomial ℤ_[p])
    (hm : Φnext.Monic) (hd : 1 ≤ Φnext.natDegree)
    (hvne : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ ≠ 0)
    (hvlt : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
        ≠ devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ →
      ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ)
        < ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
            - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ))
    (h5 : SideClauseR5 ν B Nd Φnext) : SideClauseR5 ν B' Nd' Φnext := by
  intro Bh' Nh' hdev'
  -- Fact-A uniqueness: the given development's vertex slot is the canonical one
  have hslot : Bh' ν.μ
      = devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ :=
    devCoeff_eq_of_isDevelopment hm Nh' _ Bh' hdev' ν.μ
  -- the clause for B at the canonical child-key development
  have h1 : ν.σ.digPrime ν.zbar
      (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ) = ν.vtx :=
    h5 (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j))
      ((∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j).natDegree + 1)
      (isDevelopment_devCoeff hm hd _)
  by_cases hEq : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
      = devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ
  · rw [hslot, ← hEq]
    exact h1
  · -- R-LOC at the vertex: residuals at the vertex's own height agree
    have hlt := hvlt hEq
    have hC'ne : devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ
        ≠ 0 := by
      intro h0
      rw [h0, sub_zero] at hlt
      exact lt_irrefl _ hlt
    have hR := rloc ν.σ hvne hC'ne rfl (fun _ => hlt)
    have hdig : ν.σ.digPrime ν.zbar
          (devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ)
        = ν.σ.digPrime ν.zbar
          (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ) := by
      unfold Moves.Stage.digPrime
      rw [hR]
    rw [hslot, hdig]
    exact h1

/-- **Unit III-T9: the "threshold ⟺" form.**  The mirrored rows are DERIVED:
under `hvne`/`hvlt`, ultrametricity pins `w(C′_μ) = w(C_μ)` (`w_eq_of_sub_gt`)
and `w` is even under negation (`ResVal.w_neg`), so the (R5) clause transfers
BOTH ways — the per-clause face of Theorem 1's "the converse is symmetric"
(O1thr §4). -/
theorem sideClauseR5_transfer_iff (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd Nd' : ℕ) (Φnext : Polynomial ℤ_[p])
    (hm : Φnext.Monic) (hd : 1 ≤ Φnext.natDegree)
    (hvne : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ ≠ 0)
    (hvlt : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
        ≠ devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ →
      ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ)
        < ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
            - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ)) :
    SideClauseR5 ν B Nd Φnext ↔ SideClauseR5 ν B' Nd' Φnext := by
  constructor
  · exact sideClauseR5_transfer ν B B' Nd Nd' Φnext hm hd hvne hvlt
  · by_cases hEq : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
        = devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ
    · -- degenerate: equal vertex slots — the mirrored rows are B's own
      refine sideClauseR5_transfer ν B' B Nd' Nd Φnext hm hd ?_ ?_
      · rw [← hEq]; exact hvne
      · intro hne'
        exact absurd hEq.symm hne'
    · -- differing vertex slots: derive the mirrored rows
      have hlt := hvlt hEq
      have hd0 : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
          - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ ≠ 0 :=
        sub_ne_zero.mpr hEq
      have hflip : devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ
          - devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
          = -(devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
              - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ) := by
        ring
      have hwflip :
          ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ
            - devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ)
          = ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
            - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ) := by
        rw [hflip, Moves.ResVal.w_neg ν.σ _ hd0]
      obtain ⟨hC'ne, hwEq⟩ := w_eq_of_sub_gt ν.σ hvne
        (by rw [hflip]; exact neg_ne_zero.mpr hd0) (by rw [hwflip]; exact hlt)
      refine sideClauseR5_transfer ν B' B Nd' Nd Φnext hm hd hC'ne ?_
      intro _
      rw [hwEq, hwflip]
      exact hlt

/-- Consumption wrapper for III-T10: the (R5) clause of a full `SideReads`
bundle on `B` transfers to `B′` under the (†′) vertex rows. -/
theorem sideReads_r5_transfer (ν : Node p F) (B B' : ℕ → Polynomial ℤ_[p])
    (Nd Nd' : ℕ) (Φnext : Polynomial ℤ_[p])
    (hm : Φnext.Monic) (hd : 1 ≤ Φnext.natDegree)
    (hvne : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ ≠ 0)
    (hvlt : devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
        ≠ devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ →
      ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ)
        < ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) ν.μ
            - devCoeff Φnext (∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j) ν.μ))
    (h : SideReads ν B Nd Φnext) : SideClauseR5 ν B' Nd' Φnext :=
  sideClauseR5_transfer ν B B' Nd Nd' Φnext hm hd hvne hvlt
    (sideReads_r5 ν B Nd Φnext h)

end R5Transfer

/-! ## Unit III-T10 — Theorem 1 assembled: `read_locality` (O-1thr §4 Thm 1, D-14)

Src: O1thr §4 Theorem 1 (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev4.md`
lines 868–927).  The §1.6 display for THIS unit is VERBATIM (blueprint lines
505–512, no elision) — transcribed byte-for-byte as `read_locality` below.
Unit row: "`read_locality` assembled ((R3)/(R4) record-only; symmetry)",
proof sketch "combine T7–T9 per read; induct over `H.nodes`", deps III-T7..T9.

Assembly ledger (the same completion-ledger convention as III-T4..T9 above):

* Per read `i < H.nodes.length`, f's recorded witness `(B, Nd, Φnext)` is
  transferred to the witness `(devCoeff Φᵢ f', NN, Φnext)` for `f'`,
  `NN := max Nd (f'.natDegree) + 1`: the developments are first PADDED to the
  common slot count `NN` (`sideReads_mono` — vanishing slots have vacuous
  guards; the recomposition sums are equal by `Finset.sum_subset`), then the
  clauses transfer per the T7/T8/T9 units:
  - clause (i) = (R1): `sideClauseR1_transfer` under the (†) row, discharged
    from III-T6 `dagger_sheared` + III-T3 `dev_congr_zp` (Fact-A
    identification `B j = devCoeff Φᵢ f j`, `devCoeff_eq_of_isDevelopment`);
  - clause (ii) = (R2): `sideClauseR2_transfer`, same (†) supply; the
    `IsDevelopment` rows ride verbatim;
  - clause (iii): OrdPsiPoly is record-only; the anchor transfers through
    R-LOC (`rloc`) at `β := w_i(f)` — `w_i(f − f') ≥ L·E_i` (III-T4
    `stage_pos`) `> w_i(f)` (the `fside` row below);
  - clauses (iv)/(v) = (R3)/(R4): record-only — shared verbatim (the source's
    "(R3), (R4): record-only / policy-pinned — shared");
  - clause (vi) = (R5): `sideClauseR5_transfer`; (†′) is REDERIVED at the
    landing key (`childDev_dag`), whose monicity/positive degree is DERIVED
    from `LandingKey` + the Node laws (`landingKey_monic` — recentering:
    `Φ − lift` with `deg lift < deg Φ`; otherwise the standard-lift shape
    `Φ^{eg} + Σ tt_k Φ^{ek}` with `e·g ≥ 1`).
  "Induct over `H.nodes`" is realized as the per-read `∀ i < H.nodes.length`
  transfer under the ONE `readCeil H` congruence supply (the fold over
  `H.nodes` lives inside `readCeil`; `readCeil_strict_middle` majorizes every
  read's entry).  Symmetry (the source's "the converse is symmetric") is the
  per-clause `_iff` units already landed (T7/T8/T9); the assembled statement
  is the displayed one-directional form.

* THE LAW-SUPPLY ROWS (`SiteLawRows` below) — the source proof consumes, at
  every read, the machine's box-free laws through LAWFUL(H·ν): POS (i)/(ii)
  (O1thr §2.2: `w_i ≥ 0` and the π-shift at the accumulated stretch `E_i`),
  the side pin `w_i(f) ≤ I_i < L·E_i` (the (iii)-anchor leg), and law (N4) +
  Lemma CEIL at the vertex slot (the (R5) rows `hvne`/`hvlt`; III-T9 header).
  The corpus carrier `MovesC.HistoryCoherent` (MovesC/Defs.lean:717) records
  root-degree/slope/γ-tie/transition clauses ONLY — none of these valuation
  laws are among its conjuncts, nor among the `Stage` laws (Moves/Defs.lean;
  the III-T4 header: "(i) is genuinely a row"), so they are NOT derivable
  from the verbatim binder set (hcoh/hcong/hm'/hd'/h) and enter as the named
  [M]-hypothesis-row structure `SiteLawRows` — the same discipline as
  T7/T8/T9's `hdag`/`hvne`/`hvlt` rows, bundled.  `read_locality_rows` (the
  assembly UNDER the rows) is PROVED sorry-free; the VERBATIM `read_locality`
  fires it and carries its row supply as this unit's single honest sorry —
  see the BLOCKED record at the sorry site. -/

section ReadLocality

open LeanUrat.MovesC LeanUrat.MovesJ

variable {F : Type*} [Field F] [Finite F]

/-- **III-T10 support (derived, not a row): the landing key is monic of
positive degree.**  From `LandingKey` + the Node laws alone.  Recentering leg:
`Φtop = Φ − lift` with `lift ∈ C` (`deg lift < deg Φ`), so monicity and the
degree pass from the stage key (`hmonic`/`hdeg`).  Non-recentering leg:
`Φtop = Φ^{e·g} + Σ_{k<g} tt_k·Φ^{e·k}` (`IsNodeLift`) with each present
`tt_k ∈ C`; every summand has degree `< e·g·deg Φ` (from `k < g`, `1 ≤ e`),
so the sum sits below the monic leading power (`Monic.add_of_left`), and
`natDegree = e·g·deg Φ ≥ 1` (`he`/`hg`/`hdeg`). -/
theorem landingKey_monic (ν : Node p F) (Φtop : Polynomial ℤ_[p])
    (h : MovesC.LandingKey ν Φtop) : Φtop.Monic ∧ 1 ≤ Φtop.natDegree := by
  by_cases hsp : ν.species = ReadSpecies.recentering
  · obtain ⟨hlC, -, -, -, hΦ⟩ := h.1 hsp
    have hlt : (ν.lift).degree < (ν.σ.Φ).degree := hlC
    have hdeq : (ν.σ.Φ - ν.lift).degree = (ν.σ.Φ).degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt hlt
    constructor
    · rw [hΦ, sub_eq_add_neg]
      exact ν.σ.hmonic.add_of_left (by rwa [Polynomial.degree_neg])
    · rw [hΦ, Polynomial.natDegree_eq_of_degree_eq hdeq]
      exact ν.σ.hdeg
  · obtain ⟨tt, htt0, httk, hΦ⟩ := h.2 hsp
    have hmon := ν.σ.hmonic
    have hd := ν.σ.hdeg
    have hm1 : 1 ≤ ν.e * ν.g := by
      have := Nat.mul_le_mul ν.he ν.hg
      omega
    have hpowne : ν.σ.Φ ^ (ν.e * ν.g) ≠ 0 := (hmon.pow _).ne_zero
    have hbot : (⊥ : WithBot ℕ) < (ν.σ.Φ ^ (ν.e * ν.g)).degree :=
      bot_lt_iff_ne_bot.mpr fun hb => hpowne (Polynomial.degree_eq_bot.mp hb)
    -- every summand sits strictly below the leading power
    have hSlt : (∑ k ∈ Finset.range ν.g, tt k * ν.σ.Φ ^ (ν.e * k)).degree
        < (ν.σ.Φ ^ (ν.e * ν.g)).degree := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff hbot]
      intro k hk
      by_cases h0 : tt k = 0
      · simpa [h0] using hbot
      · have hklt : k < ν.g := Finset.mem_range.mp hk
        have hck : ν.ψ.coeff k ≠ 0 := fun hc => h0 (htt0 k hc)
        obtain ⟨-, hinC, -, -⟩ := httk k hklt hck
        refine Polynomial.degree_lt_degree ?_
        have h1 : (tt k).natDegree < ν.σ.Φ.natDegree :=
          Polynomial.natDegree_lt_natDegree h0 hinC
        have h2 : (tt k * ν.σ.Φ ^ (ν.e * k)).natDegree
            ≤ (tt k).natDegree + (ν.e * k) * ν.σ.Φ.natDegree := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [hmon.natDegree_pow]
        have h3 : (ν.e * k) * ν.σ.Φ.natDegree + ν.σ.Φ.natDegree
            ≤ (ν.e * ν.g) * ν.σ.Φ.natDegree := by
          have hek : ν.e * k + 1 ≤ ν.e * ν.g := by
            have h1 : ν.e * (k + 1) ≤ ν.e * ν.g := Nat.mul_le_mul le_rfl (by omega)
            have h2 : ν.e * (k + 1) = ν.e * k + ν.e := by ring
            have := ν.he
            omega
          calc (ν.e * k) * ν.σ.Φ.natDegree + ν.σ.Φ.natDegree
              = (ν.e * k + 1) * ν.σ.Φ.natDegree := by ring
            _ ≤ (ν.e * ν.g) * ν.σ.Φ.natDegree :=
                Nat.mul_le_mul_right _ hek
        rw [hmon.natDegree_pow]
        omega
    have hdeq : (ν.σ.Φ ^ (ν.e * ν.g)
        + ∑ k ∈ Finset.range ν.g, tt k * ν.σ.Φ ^ (ν.e * k)).degree
        = (ν.σ.Φ ^ (ν.e * ν.g)).degree :=
      Polynomial.degree_add_eq_left_of_degree_lt hSlt
    constructor
    · rw [hΦ]
      exact (hmon.pow _).add_of_left hSlt
    · rw [hΦ, Polynomial.natDegree_eq_of_degree_eq hdeq, hmon.natDegree_pow]
      simpa using Nat.mul_le_mul hm1 hd

/-- **III-T10 support (derived, not a row): `SideReads` slot-count padding.**
A `SideReads` bundle at slot count `Nd` holds at any `NN ≥ Nd` once the
development vanishes from `Nd` on: the (i)-guards at the new slots are vacuous
(`B j = 0`), clause (ii) is `Nd`-free, the (iii)/(vi) recomposition sums are
unchanged (`Finset.sum_subset`), and (iv)/(v) are record-only. -/
theorem sideReads_mono (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) {Nd NN : ℕ}
    (Φnext : Polynomial ℤ_[p]) (hle : Nd ≤ NN)
    (hvan : ∀ j, Nd ≤ j → B j = 0)
    (h : SideReads ν B Nd Φnext) : SideReads ν B NN Φnext := by
  obtain ⟨⟨h1a, h1b⟩, h2, h3, h4, h5, h6⟩ := h
  have hsum : ∑ j ∈ Finset.range NN, B j * ν.σ.Φ ^ j
      = ∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j :=
    (Finset.sum_subset (Finset.range_subset_range.mpr hle)
      (fun j _ hj => by
        rw [hvan j (Nat.le_of_not_lt fun hlt => hj (Finset.mem_range.mpr hlt)),
          zero_mul])).symm
  refine ⟨⟨?_, ?_⟩, h2, ?_, h4, h5, ?_⟩
  · intro j hj hB
    rcases Nat.lt_or_ge j Nd with hlt | hge
    · exact h1a j hlt hB
    · exact absurd (hvan j hge) hB
  · intro j hj hB heq
    rcases Nat.lt_or_ge j Nd with hlt | hge
    · exact h1b j hlt hB heq
    · exact absurd (hvan j hge) hB
  · rw [hsum]; exact h3
  · intro Bh Nh hdev
    rw [hsum] at hdev
    exact h6 Bh Nh hdev

/-- **The III-T10 law-supply rows** — the box-free machine laws the source
proof consumes per read through LAWFUL(H·ν), NOT carried by the corpus
`MovesC.HistoryCoherent` (see the section header ledger).  Named [M]-hypothesis
rows (T7/T8/T9's `hdag`/`hvne`/`hvlt` discipline, bundled); nothing here is
discharged by fiat:
* `pos`/`shift` — Lemma POS (i)/(ii) at read `i` (O1thr §2.2): `w_i ≥ 0` on
  nonzero polynomials, and the π-shift at the accumulated stretch
  `E_i = H.strFrame i` (III-T4's first two law rows, per-read);
* `fside` — the whole-`f` side pin `w_i(f) < L·E_i` (the source's
  `w_i(f) ≤ I_i` + the strict middle inequality; consumed by the
  clause-(iii) anchor transfer through R-LOC at `β = w_i(f)`);
* `vtxNe`/`vtxHt` — law (N4) + Lemma CEIL at the vertex slot of `f`'s
  development in the read's landing key (the (R5) rows; the σV-vertex-law
  supply named by the III-T9 header, `HK11a.sigmaV_vertexLaw`, carries
  `StageCoreL`/steepness/species hypotheses beyond this unit's binder set —
  III-T11's leg, not this unit's). -/
structure SiteLawRows (H : MovesC.History p F) (f : Polynomial ℤ_[p]) :
    Prop where
  pos : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ C : Polynomial ℤ_[p], C ≠ 0 →
    0 ≤ (H.nodes[i]'hi).σ.w C
  shift : ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ C : Polynomial ℤ_[p],
    C ≠ 0 → (H.nodes[i]'hi).σ.w (Polynomial.C (p : ℤ_[p]) * C)
      = (H.strFrame i : ℤ) + (H.nodes[i]'hi).σ.w C
  fside : ∀ (i : ℕ) (hi : i < H.nodes.length),
    (H.nodes[i]'hi).σ.w f < (readCeil H : ℤ) * (H.strFrame i : ℤ)
  vtxNe : ∀ (i : ℕ) (hi : i < H.nodes.length) (Φnext : Polynomial ℤ_[p]),
    MovesC.LandingKey (H.nodes[i]'hi) Φnext →
    devCoeff Φnext f (H.nodes[i]'hi).μ ≠ 0
  vtxHt : ∀ (i : ℕ) (hi : i < H.nodes.length) (Φnext : Polynomial ℤ_[p]),
    MovesC.LandingKey (H.nodes[i]'hi) Φnext →
    (H.nodes[i]'hi).σ.w (devCoeff Φnext f (H.nodes[i]'hi).μ)
      < (readCeil H : ℤ) * (H.strFrame i : ℤ)

/-- **Unit III-T10, the assembly UNDER the law rows (PROVED).**  Theorem 1's
transfer `READ(f, H·ν) ⟹ READ(f′, H·ν)` at every read of the site, given the
`SiteLawRows` supply: per read, pad to a common slot count, identify the
recorded development with the canonical `devCoeff` slots (Fact A), discharge
the (†) row from III-T6 + III-T3, and fire the per-clause units III-T7/T8/T9;
clauses (iii)-anchor via R-LOC at `w_i(f)`, (iv)/(v) record-only. -/
theorem read_locality_rows {n : ℕ} {f f' : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hcoh : MovesC.HistoryCoherent H)
    (hcong : ∀ k, (f - f').coeff k ∈
      (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H))
    (hm' : f'.Monic) (hd' : f'.natDegree = n)
    (h : MovesJ.ReadsOf p F n f H)
    (rows : SiteLawRows H f) :
    MovesJ.ReadsOf p F n f' H := by
  classical
  obtain ⟨hm, hd, hcohf, hreads⟩ := h
  by_cases hff : f = f'
  · exact hff ▸ ⟨hm, hd, hcohf, hreads⟩
  refine ⟨hm', hd', hcoh, ?_⟩
  intro i hi
  obtain ⟨B, Nd, Φnext, hdev, hpin, hsr⟩ := hreads i hi
  set ν := H.nodes[i]'hi with hνdef
  have hν? : H.nodes[i]? = some ν := by
    rw [hνdef]; exact List.getElem?_eq_getElem hi
  have hmonΦ : (ν.σ.Φ).Monic := ν.σ.hmonic
  have hdegΦ : 1 ≤ (ν.σ.Φ).natDegree := ν.σ.hdeg
  have hNdNN : Nd ≤ max Nd f'.natDegree + 1 := by
    have := le_max_left Nd f'.natDegree; omega
  -- pad f's recorded development to the common slot count
  have hfsum : f = ∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
      B j * ν.σ.Φ ^ j := by
    rw [hdev.2.2]
    exact Finset.sum_subset (Finset.range_subset_range.mpr hNdNN)
      (fun j _ hj => by
        rw [hdev.2.1 j (Nat.le_of_not_lt fun hlt => hj (Finset.mem_range.mpr hlt)),
          zero_mul])
  have hdevNN : Moves.IsDevelopment ν.σ.Φ f B (max Nd f'.natDegree + 1) :=
    ⟨hdev.1, fun j hj => hdev.2.1 j (le_trans hNdNN hj), hfsum⟩
  have hsrNN : SideReads ν B (max Nd f'.natDegree + 1) Φnext :=
    sideReads_mono ν B Φnext hNdNN hdev.2.1 hsr
  -- f''s canonical development at the same slot count
  have hdev' : Moves.IsDevelopment ν.σ.Φ f' (devCoeff ν.σ.Φ f')
      (max Nd f'.natDegree + 1) := by
    refine ⟨fun j => degree_devCoeff_lt hmonΦ f' j, fun j hj =>
      devCoeff_eq_zero_of_natDegree_lt hmonΦ hdegΦ j f'
        (by have := le_max_right Nd f'.natDegree; omega), ?_⟩
    exact sum_devCoeff_mul_pow hmonΦ hdegΦ (max Nd f'.natDegree) f'
      (le_max_right _ _)
  -- Fact-A identification + DEV: the (†) row (III-T6 supply, one per site)
  have hB : ∀ j, B j = devCoeff ν.σ.Φ f j :=
    devCoeff_eq_of_isDevelopment hmonΦ Nd f B hdev
  have hdc := dev_congr_zp ν.σ.Φ hmonΦ hdegΦ (readCeil H) hcong
  have hdag : ∀ j : ℕ, j < max Nd f'.natDegree + 1 →
      B j ≠ devCoeff ν.σ.Φ f' j →
      ν.gam < (ν.e : ℤ) * ν.σ.w (B j - devCoeff ν.σ.Φ f' j)
        + (j : ℤ) * (ν.h : ℤ) := by
    intro j _ hne
    have hcj : ∀ k, (B j - devCoeff ν.σ.Φ f' j).coeff k ∈
        (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H) := by
      intro k; rw [hB j]; exact hdc j k
    exact dagger_sheared H hν? ν.σ (rows.pos i hi) (rows.shift i hi)
      ν.σ.hwult hne hcj j
  -- clause (iii) anchor leg: R-LOC at β = w_i(f)
  have hRf'f : ν.σ.R f' = ν.σ.R f := by
    have hgap : ν.σ.w f < ν.σ.w (f - f') :=
      lt_of_lt_of_le (rows.fside i hi)
        (stage_pos ν.σ (H.strFrame i : ℤ) (readCeil H) (rows.pos i hi)
          (rows.shift i hi) ν.σ.hwult hff hcong)
    exact (rloc ν.σ hm.ne_zero hm'.ne_zero rfl (fun _ => hgap)).symm
  -- clause (vi) rows: landing-key monicity + (†′) at the vertex
  have hLK : MovesC.LandingKey ν Φnext := hsrNN.2.2.2.1
  obtain ⟨hmΦn, hdΦn⟩ := landingKey_monic ν Φnext hLK
  have hvne : devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
      B j * ν.σ.Φ ^ j) ν.μ ≠ 0 := by
    rw [← hfsum]; exact rows.vtxNe i hi Φnext hLK
  have hvlt : devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
        B j * ν.σ.Φ ^ j) ν.μ
      ≠ devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
        devCoeff ν.σ.Φ f' j * ν.σ.Φ ^ j) ν.μ →
      ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
        B j * ν.σ.Φ ^ j) ν.μ)
      < ν.σ.w (devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
          B j * ν.σ.Φ ^ j) ν.μ
        - devCoeff Φnext (∑ j ∈ Finset.range (max Nd f'.natDegree + 1),
          devCoeff ν.σ.Φ f' j * ν.σ.Φ ^ j) ν.μ) := by
    rw [← hfsum, ← hdev'.2.2]
    exact childDev_dag ν.σ hmΦn hdΦn (H.strFrame i : ℤ) (readCeil H)
      (rows.pos i hi) (rows.shift i hi) ν.σ.hwult hcong ν.μ
      (rows.vtxHt i hi Φnext hLK)
  -- fire the per-clause units and assemble
  refine ⟨devCoeff ν.σ.Φ f', max Nd f'.natDegree + 1, Φnext, hdev', hpin,
    ?_, ?_, ⟨?_, hsrNN.2.2.1.2⟩, hsrNN.2.2.2.1, hsrNN.2.2.2.2.1, ?_⟩
  · exact sideClauseR1_transfer ν B (devCoeff ν.σ.Φ f') _ hdag
      (sideReads_r1 ν B _ Φnext hsrNN)
  · exact sideClauseR2_transfer ν B (devCoeff ν.σ.Φ f') _ hdevNN.2.1
      (fun j => hdevNN.1 j) (fun j => hdev'.1 j) hdag
      (sideReads_r2 ν B _ Φnext hsrNN)
  · have h3 := hsrNN.2.2.1.1
    rw [← hfsum] at h3
    rw [← hdev'.2.2, hRf'f]
    exact h3
  · exact sideClauseR5_transfer ν B (devCoeff ν.σ.Φ f') _ _ Φnext hmΦn hdΦn
      hvne hvlt (sideReads_r5 ν B _ Φnext hsrNN)

/-- THEOREM 1 (D-14, the noncircular quantifier form): reads transfer between
    f ≡ f′ (mod p^{readCeil}) at EVERY lawful site — per-clause units III-T7..T9,
    assembled here. The corpus rendering: ReadsOf-clause transfer at each i. -/
theorem read_locality {n : ℕ} {f f' : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hcoh : MovesC.HistoryCoherent H)
    (hcong : ∀ k, (f - f').coeff k ∈
      (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H))
    (hm' : f'.Monic) (hd' : f'.natDegree = n)
    (h : MovesJ.ReadsOf p F n f H) :
    MovesJ.ReadsOf p F n f' H :=
  read_locality_rows hcoh hcong hm' hd' h
    (by
      -- BLOCKED(III-T10): the `SiteLawRows` supply is not derivable from the
      -- verbatim binder set.  The source proof consumes these laws through
      -- "LAWFUL(H·ν)" (O1thr §4: POS (i)/(ii), the side pin w_i(f) ≤ I_i, and
      -- law (N4)+CEIL at the vertex), but the corpus carrier
      -- `MovesC.HistoryCoherent` (MovesC/Defs.lean:717) records
      -- root-degree/slope/γ-tie/transition clauses ONLY — no clause ties
      -- `σᵢ.w` to `p` (w ≥ 0, w(p·C) = strFrame i + w C) or supplies (N4);
      -- the `Stage` laws don't either (III-T4 header: "(i) is genuinely a
      -- row"), and the σV-vertex-law supply (HK11a.sigmaV_vertexLaw) carries
      -- StageCoreL/steepness/species hypotheses beyond this signature.
      -- The assembled transfer under the rows is PROVED above
      -- (`read_locality_rows`, sorry-free); THIS sorry is exactly the row
      -- supply.  Escalation: either `HistoryCoherent` grows the per-read
      -- valuation-law clauses (architect ruling — statement-adjacent), or
      -- CU-1-LVL consumes `read_locality_rows` with the rows discharged at
      -- its concrete instance.
      sorry)

end ReadLocality

end LeanUrat.Scaffold.DictIII
