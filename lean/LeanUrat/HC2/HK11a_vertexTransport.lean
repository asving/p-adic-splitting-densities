import Mathlib
import LeanUrat.HC2.HK52_stretchGate
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC1.V2_readResidual

/-!
# HK-11a VERTEX TRANSPORT — the re-pointed HK-11a kernel: the σV-vertex law at the
recorded regrade, and its e′ = 1 consumption shape
(post-wave unit, 2026-07-31; BP2 sequencing HK-12 → HK-52 → HK-11a; agent: post-wave-4)

## What this unit is (read `notes/HK12_RECHECK_2026-07-31.md` first)

HK-12 finding F3: BP2 HK-11a's DISPLAYED bottom-window law
(`σ'.wPrev (B μ) = νᵢ.e·σᵢ.w (B μ)`) stays REFUTED verbatim on the r3b countermodel
data — and V9 never consumes it.  The honest re-pointed HK-11a target is the
**σV-VERTEX LAW** at the recorded (S-a) STEP-1 regrade,

    (†)   σV.w (B μ) = ν.gam − μ·e★·h★·g      (+ B μ ≠ 0, + the strict (BOX) below μ),

whose supply is V4-(VERTEX) at the regrade + the R3a ANCHOR TRANSPORT (the ~300-line
V4-kernel-shaped derivation spec'd in V9's REV-2 obstruction record).  THIS FILE BUILDS
EXACTLY THAT:

* `HK11a.anchor_transport` — **R3a, PROVED**: from SideReads(i)+(ii) alone (the ⚠-clean
  pool — SideReads(iii)'s fenced `σ.R f` rendering is NOT consumed), f's read-functional
  weight is the recorded `gam` (attained) and the ReadFrame residual `Rv f` carries the
  recorded anchor: `Rv f = T(a)·Ranch`, `HasAnchorK` verbatim.  Mechanism per the REV-2
  spec: the min-sum decomposition of `Rv` over f's frame-i development — SideReads(i)
  makes the read side a genuine support line with ties exactly the stride digits,
  the tie positions `(j − t★·gam)/e★ = a + k` are injective across ties (hAnchor +
  Bézout), and `D.hS5` matches each tie scalar against SideReads(ii)'s recorded digit.
* `HK11a.sigmaV_vertexLaw` — **THE KERNEL (†)**: R3a fires V4-(VERTEX)+(BOX) at the
  ReadFrame, and the regrade's slot-min-forced weight (`RegradeOf`'s `IsSlotMinWeight`
  clause, unique-valued against `S2_childW`) transports the landing to EVERY recorded
  regrade σV of the read pair.  σ-level statement; the recorded node data enter as
  explicit hypotheses.
* `HK11a.readVertex_e1` / `HK11a.readBox_e1` — the CONSUMPTION SHAPES: V9's two
  displayed ℚ-forms (`V9_K1nonrec` / `V9_E1box_nonrec` conclusions, byte-shaped), at a
  coherent `ReadsOf` record, derived from the kernel through HK-52's stretch identity
  `σ_{i+1}.w B = ν_{i+1}.e·σV.w B` — **on the `ν_{i+1}.e = 1` sub-perimeter** (where the
  stretch is the identity), with the γ-tie + slope-law + `hLineU` scale arithmetic
  (`lineAt_arith`) converting (†) to the fenced ℚ-form.

## Carried hypotheses (the honest conditionality — named, never silent)

The consumption shapes carry THREE hypotheses beyond V9's binders:
1. `he'1 : ν_{i+1}.e = 1` — the HK-12 F4 adjudication item (the ν_{i+1}.e ≥ 2
   disposition is UNRULED; the Q2-extension fenced the PARENT stride only).  V9's four
   sorries quantify over ALL ν_{i+1}.e, so they must NOT be filled from this supplier
   before that ruling (HK12_RECHECK §ADJUDICATION); this hypothesis is where ruling
   option (i)'s guard would land.
2. `hsteep : νᵢ.e·σᵢ.h < νᵢ.h` — STRICT read steepness, the `ReadPair` clause.  Genuine
   h-steep reads live at i = 0 / post-recentering only (HK-12 F5: at i ≥ 1 with a
   non-recentering predecessor `child_h` pins σᵢ.h = νᵢ.h, the read is NOT steep, and
   the e★ = 1 regrade is weight-idempotent — that face is HK-08 restatement territory,
   not this kernel).  The old derivation suppliers (`V9_transSteepness` etc.) were
   wave-refuted; steepness at the root read is (I-aug) classifier-semantics content,
   hypothesis class.
3. `hσL : StageCoreL σᵢ` — tower provenance of the recorded frame (the V2/V4 engine's
   standing hypothesis; recorded histories do not carry it — HC-1's TRANS supplies it
   along constructed towers).

Statements of V9 are BYTE-UNTOUCHED (this is a supplier leaf; its V9-side consumption
waits on the ν_{i+1}.e ruling).  SideReads(iii) NOT consumed (the U31 fence holds);
`ν.hOrd` is read off the NODE field, never off clause (iii).  No new axioms.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace HK11a

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### Sub-development bookkeeping (Fact A/B plumbing) -/

/-- The masked family of a slot subset is a development of the sub-sum. -/
private lemma subdev {R : Type*} [CommRing R] {Φ : Polynomial R} (hΦ : Φ ≠ 0)
    {B : ℕ → Polynomial R} {N : ℕ} (hdeg : ∀ j, (B j).degree < Φ.degree)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < N) :
    IsDevelopment Φ (∑ j ∈ S, B j * Φ ^ j) (fun j => if j ∈ S then B j else 0) N := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · simpa [hj] using hdeg j
    · simp only [hj, if_false, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun hb => hΦ (Polynomial.degree_eq_bot.mp hb))
  · intro j hjN
    have : j ∉ S := fun hj => absurd (hS j hj) (by omega)
    simp [this]
  · have hsub : S ⊆ Finset.range N := fun j hj => Finset.mem_range.mpr (hS j hj)
    rw [← Finset.sum_subset hsub (fun x _ hx => by simp [hx])]
    exact (Finset.sum_congr rfl (fun j hj => by simp [hj])).symm

/-- A sub-sum of development slots with a nonzero member is nonzero (Fact B). -/
private lemma subdev_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {Φ : Polynomial R}
    (hmon : Φ.Monic) {B : ℕ → Polynomial R} {N : ℕ}
    (hdeg : ∀ j, (B j).degree < Φ.degree)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < N)
    {j₀ : ℕ} (hj₀ : j₀ ∈ S) (hne : B j₀ ≠ 0) :
    (∑ j ∈ S, B j * Φ ^ j) ≠ 0 := by
  classical
  intro h0
  have hΦ : Φ ≠ 0 := hmon.ne_zero
  have hdevS : IsDevelopment Φ 0 (fun j => if j ∈ S then B j else 0) N :=
    h0 ▸ subdev hΦ hdeg S hS
  have hdev0 : IsDevelopment Φ 0 (fun _ => (0 : Polynomial R)) 0 := by
    refine ⟨?_, fun _ _ => rfl, by simp⟩
    intro j
    simp only [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun hb => hΦ (Polynomial.degree_eq_bot.mp hb))
  have := L0_FactB_unique Φ hmon 0 hdevS hdev0 j₀
  rw [if_pos hj₀] at this
  exact hne this

/-! ### The ReadFrame slot calculus (weight and residual of one slot term) -/

/-- Slot weight law: `wV(B·Φ^j) = wV(B) + j·h★` (V.hwmul + V.hwPhi, key power peeled). -/
private lemma wv_slot {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (j : ℕ) :
    childW σ σ.Φ estar hstar (B * σ.Φ ^ j)
      = childW σ σ.Φ estar hstar B + (j : ℤ) * (hstar : ℤ) := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp
  | succ k ih =>
      have h1 : B * σ.Φ ^ (k + 1) = (B * σ.Φ ^ k) * σ.Φ := by ring
      rw [h1, V.hwmul _ _ (mul_ne_zero hB (pow_ne_zero k hΦne)) hΦne, ih, V.hwPhi]
      push_cast; ring

/-- Slot residual law: `Rv(B·Φ^j) = Rv(B)·T(s★)^j` (laws.hRmul + the key pin hRPhi). -/
private lemma rv_slot {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (j : ℕ) :
    V.D.Rv (B * σ.Φ ^ j) = V.D.Rv B * (LaurentPolynomial.T sstar) ^ j := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp
  | succ k ih =>
      have h1 : B * σ.Φ ^ (k + 1) = (B * σ.Φ ^ k) * σ.Φ := by ring
      rw [h1, hRmul _ _ (mul_ne_zero hB (pow_ne_zero k hΦne)) hΦne, ih, V.D.hRPhi,
        pow_succ, mul_assoc]

/-! ### Scalar and position bookkeeping -/

/-- Monomial scalar match: equal `C·T` monomials at the same position share the scalar. -/
private lemma CT_scalar_match {K : Type*} [CommRing K] {a b : K} {n : ℤ}
    (h : LaurentPolynomial.C a * LaurentPolynomial.T n
        = LaurentPolynomial.C b * LaurentPolynomial.T n) : a = b := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : (Finsupp.single n a : ℤ →₀ K) = Finsupp.single n b := h
  have hc := DFunLike.congr_fun h' n
  rwa [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_pos rfl] at hc

/-- The stride-position arithmetic (D.3(c) at the read pair): at an on-side stride slot
`j = s0 + e★·k` of total read weight `gam`, the (S5) position `j·s★ − t★·σ.w(B_j)` is the
anchored `a + k` (hAnchor + Bézout; e★-cleared, then cancelled). -/
private lemma stride_pos {estar hstar : ℕ} {sstar tstar a gam w : ℤ}
    {s0 k : ℕ} (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (hAnchor : (estar : ℤ) * a = (s0 : ℤ) - tstar * gam)
    (hw : (estar : ℤ) * w + ((s0 + estar * k : ℕ) : ℤ) * (hstar : ℤ) = gam) :
    ((s0 + estar * k : ℕ) : ℤ) * sstar - tstar * w = a + (k : ℤ) := by
  have hE : (estar : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (estar : ℤ) := by exact_mod_cast hee
    omega
  apply mul_left_cancel₀ hE
  push_cast at hw ⊢
  linear_combination ((s0 : ℤ) + (estar : ℤ) * (k : ℤ)) * hbez - tstar * hw - hAnchor

/-- `strFrame` recursion: `STR_{k+1} = STR_k · e_k` (private copy of the V9 lemma). -/
private lemma strFrame_succ (H : History p F) (k : ℕ) (hk : k < H.nodes.length) :
    H.strFrame (k + 1) = H.strFrame k * (H.nodes[k]'hk).e := by
  unfold History.strFrame
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [List.map_append, List.prod_append, Option.toList_some, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-! ### The regrade's weight is slot-min-forced (HK-12 finding F1's compiled half) -/

/-- **The regrade weight is the read functional**: `RegradeOf`'s `IsSlotMinWeight` clause
determines `σV.w` on every nonzero polynomial — it agrees with `childW` (S2's attained
slot-min at the same pair), by uniqueness of attained minima over the shared development. -/
lemma regrade_w_eq_childW {σ σV : Stage p F} {estar hstar : ℕ}
    (hreg : RegradeOf σ estar hstar σV) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σV.w x = childW σ σ.Φ estar hstar x := by
  have hsm := hreg.2.2.2.2.2.2.2
  obtain ⟨B₀, N₀, hdev₀⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg x
  obtain ⟨hlo1, j1, hj1N, hj1ne, hj1eq⟩ := hsm x B₀ N₀ hx hdev₀
  obtain ⟨-, hSMW⟩ := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  obtain ⟨hlo2, j2, hj2N, hj2ne, hj2eq⟩ := hSMW x B₀ N₀ hx hdev₀
  have h1 := hlo1 j2 hj2N hj2ne
  have h2 := hlo2 j1 hj1N hj1ne
  omega

/-! ### The min-sum core over a tie set -/

/-- A slot sub-sum is nonzero, its read weight is bounded by every own slot weight, and
it ATTAINS one of them (V.hK1 at the masked sub-development, hStretch-converted). -/
private lemma subsum_attain {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    {B : ℕ → Polynomial ℤ_[p]} {N : ℕ} (hdeg : ∀ j, (B j).degree < σ.Φ.degree)
    (S : Finset ℕ) (hSne : S.Nonempty)
    (hSnz : ∀ j ∈ S, B j ≠ 0) (hSN : ∀ j ∈ S, j < N) :
    (∑ j ∈ S, B j * σ.Φ ^ j) ≠ 0 ∧
    (∀ j ∈ S, childW σ σ.Φ estar hstar (∑ j' ∈ S, B j' * σ.Φ ^ j')
        ≤ (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ)) ∧
    ∃ j ∈ S, childW σ σ.Φ estar hstar (∑ j' ∈ S, B j' * σ.Φ ^ j')
      = (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) := by
  classical
  obtain ⟨j₀, hj₀⟩ := hSne
  have hne0 := subdev_ne_zero σ.hmonic hdeg S hSN hj₀ (hSnz j₀ hj₀)
  have hdevS := subdev σ.hmonic.ne_zero hdeg S hSN
  obtain ⟨hlow, jm, hjmN, hjmne, hjmeq⟩ := V.hK1 _ _ N hne0 hdevS
  have hjmS : jm ∈ S := by
    by_contra hcon
    exact hjmne (by simp [hcon])
  refine ⟨hne0, ?_, ⟨jm, hjmS, ?_⟩⟩
  · intro j hj
    have h := hlow j (hSN j hj) (by simp only [if_pos hj]; exact hSnz j hj)
    simp only [if_pos hj] at h
    rwa [V.hStretch _ (hSnz j hj) (hdeg j)] at h
  · simp only [if_pos hjmS] at hjmeq
    rw [V.hStretch _ (hSnz jm hjmS) (hdeg jm)] at hjmeq
    exact hjmeq

/-- Residual additivity over an equal-weight tie set: `Rv(Σ_S B_j Φ^j) = Σ_S Rv(B_j Φ^j)`
when every slot of `S` ties at the same read weight (laws.hRadd, summed — every partial
sub-sum stays at the tie weight by `subsum_attain`, so the pairwise law iterates). -/
private lemma rv_sum {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    {B : ℕ → Polynomial ℤ_[p]} {N : ℕ} (hdeg : ∀ j, (B j).degree < σ.Φ.degree)
    (gam : ℤ) (S : Finset ℕ) :
    S.Nonempty → (∀ j ∈ S, B j ≠ 0) → (∀ j ∈ S, j < N) →
    (∀ j ∈ S, (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) = gam) →
    V.D.Rv (∑ j ∈ S, B j * σ.Φ ^ j) = ∑ j ∈ S, V.D.Rv (B j * σ.Φ ^ j) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction S using Finset.induction_on with
  | empty => intro h _ _ _; exact absurd h (by simp)
  | @insert a s ha ih =>
      intro hne hnz hN hw
      have hxne : B a ≠ 0 := hnz a (Finset.mem_insert_self a s)
      by_cases hs : s.Nonempty
      · have hnz' : ∀ j ∈ s, B j ≠ 0 := fun j hj => hnz j (Finset.mem_insert_of_mem hj)
        have hN' : ∀ j ∈ s, j < N := fun j hj => hN j (Finset.mem_insert_of_mem hj)
        have hw' : ∀ j ∈ s,
            (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) = gam :=
          fun j hj => hw j (Finset.mem_insert_of_mem hj)
        obtain ⟨hsne0, -, js, hjs, hjseq⟩ := subsum_attain V hdeg s hs hnz' hN'
        have hyw : childW σ σ.Φ estar hstar (∑ j ∈ s, B j * σ.Φ ^ j) = gam := by
          rw [hjseq]; exact hw' js hjs
        obtain ⟨hins0, -, ji, hji, hjieq⟩ := subsum_attain V hdeg (insert a s)
          ⟨a, Finset.mem_insert_self a s⟩ hnz hN
        have hinsw : childW σ σ.Φ estar hstar
            (∑ j ∈ insert a s, B j * σ.Φ ^ j) = gam := by
          rw [hjieq]; exact hw ji hji
        have hxw : childW σ σ.Φ estar hstar (B a * σ.Φ ^ a) = gam := by
          rw [wv_slot V _ hxne a, V.hStretch _ hxne (hdeg a)]
          exact hw a (Finset.mem_insert_self a s)
        have haΦne : B a * σ.Φ ^ a ≠ 0 := mul_ne_zero hxne (pow_ne_zero _ hΦne)
        have hsum := Finset.sum_insert (f := fun j => B j * σ.Φ ^ j) ha
        have hfne : B a * σ.Φ ^ a + ∑ j ∈ s, B j * σ.Φ ^ j ≠ 0 := by
          rw [← hsum]; exact hins0
        have hR := hRadd (B a * σ.Φ ^ a) (∑ j ∈ s, B j * σ.Φ ^ j) haΦne hsne0 hfne
          (by rw [hxw, hyw])
          (by rw [← hsum, hinsw, hxw])
        rw [Finset.sum_insert ha, hR, ih hs hnz' hN' hw', Finset.sum_insert ha]
      · rw [Finset.not_nonempty_iff_eq_empty] at hs
        subst hs
        simp

/-! ### R3a — THE ANCHOR TRANSPORT (the REV-2 derivation spec, executed) -/

/-- **R3a**: from SideReads(i)+(ii)-shaped side data alone — the support-line clause with
ties exactly the stride digits, and the recorded digit monomials — the ReadFrame reads
f at the recorded total side weight, and its residual carries the recorded anchor:
`wV(f) = gam` (attained) and `Rv f = T(a)·Ranch` (`HasAnchorK` verbatim).
SideReads(iii) is NOT consumed. -/
theorem anchor_transport (σ : Stage p F)
    {estar hstar : ℕ} {sstar tstar : ℤ}
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (hdev : IsDevelopment σ.Φ f B Nd)
    (gam : ℤ) (s0 wSide : ℕ) (pat : ℕ → ↥σ.K) (a : ℤ) (Ranch : Polynomial ↥σ.K)
    (hpat0 : pat 0 ≠ 0)
    (hRanch : Ranch = ∑ k ∈ Finset.range (wSide / estar + 1),
        Polynomial.C (pat k) * Polynomial.X ^ k)
    (hAnchor : (estar : ℤ) * a = (s0 : ℤ) - tstar * gam)
    (hSideGe : ∀ j : ℕ, j < Nd → B j ≠ 0 →
        gam ≤ (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ))
    (hSideEq : ∀ j : ℕ, j < Nd → B j ≠ 0 →
        (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) = gam →
        ∃ k : ℕ, k ≤ wSide / estar ∧ j = s0 + estar * k ∧ pat k ≠ 0)
    (hDig : ∀ k : ℕ, k ≤ wSide / estar → pat k ≠ 0 →
        B (s0 + estar * k) ≠ 0 ∧
        (estar : ℤ) * σ.w (B (s0 + estar * k))
            + ((s0 + estar * k : ℕ) : ℤ) * (hstar : ℤ) = gam ∧
        σ.R (B (s0 + estar * k)) = LaurentPolynomial.C (pat k) *
          LaurentPolynomial.T (- σ.t * σ.wPrev (B (s0 + estar * k)))) :
    childW σ σ.Φ estar hstar f = gam ∧ HasAnchorK (V.D.Rv f) a Ranch := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have hee : 1 ≤ estar := hrp.1
  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  obtain ⟨hdegdev, hzerodev, hsumdev⟩ := hdev
  -- the base stride slot `s0 = s0 + e★·0`
  have hDig0 := hDig 0 (Nat.zero_le _) hpat0
  simp only [Nat.mul_zero, Nat.add_zero] at hDig0
  obtain ⟨hBs0ne, hws0, -⟩ := hDig0
  have hs0Nd : s0 < Nd := by
    by_contra hcon
    exact hBs0ne (hzerodev s0 (not_lt.mp hcon))
  -- the stride index set and its slot image (the tie set M)
  set KK : Finset ℕ := (Finset.range (wSide / estar + 1)).filter (fun k => pat k ≠ 0)
    with hKK
  set M : Finset ℕ := KK.image (fun k => s0 + estar * k) with hMM
  have hMmem : ∀ j ∈ M, B j ≠ 0 ∧
      (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) = gam := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hkr, hkp⟩ := Finset.mem_filter.mp hk
    obtain ⟨h1, h2, -⟩ := hDig k (by have := Finset.mem_range.mp hkr; omega) hkp
    exact ⟨h1, by exact_mod_cast h2⟩
  have hMnz : ∀ j ∈ M, B j ≠ 0 := fun j hj => (hMmem j hj).1
  have hMw : ∀ j ∈ M, (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) = gam :=
    fun j hj => (hMmem j hj).2
  have hMNd : ∀ j ∈ M, j < Nd := by
    intro j hj
    by_contra hcon
    exact hMnz j hj (hzerodev j (not_lt.mp hcon))
  have h0K : 0 ∈ KK := by
    rw [hKK]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), hpat0⟩
  have hs0M : s0 ∈ M := by
    rw [hMM]
    exact Finset.mem_image.mpr ⟨0, h0K, by simp⟩
  have hMne : M.Nonempty := ⟨s0, hs0M⟩
  -- ── (A) the read weight of f is gam ────────────────────────────────────────────
  have hwf : childW σ σ.Φ estar hstar f = gam := by
    obtain ⟨hlow, jm, hjmN, hjmne, hjmeq⟩ :=
      V.hK1 f B Nd hf ⟨hdegdev, hzerodev, hsumdev⟩
    have hup := hlow s0 hs0Nd hBs0ne
    simp only [V.hStretch _ hBs0ne (hdegdev s0)] at hup
    have hge := hSideGe jm hjmN hjmne
    simp only [V.hStretch _ hjmne (hdegdev jm)] at hjmeq
    linarith [hup, hws0, hge, hjmeq]
  -- ── (B) min-sum: Rv f splits over the tie set M ────────────────────────────────
  have hMsub : M ⊆ Finset.range Nd := fun j hj => Finset.mem_range.mpr (hMNd j hj)
  have hsplit : f = (∑ j ∈ M, B j * σ.Φ ^ j)
      + ∑ j ∈ Finset.range Nd \ M, B j * σ.Φ ^ j := by
    rw [hsumdev, ← Finset.sum_sdiff hMsub, add_comm]
  set T : Finset ℕ := (Finset.range Nd \ M).filter (fun j => B j ≠ 0) with hTT
  have hTsum : ∑ j ∈ T, B j * σ.Φ ^ j = ∑ j ∈ Finset.range Nd \ M, B j * σ.Φ ^ j := by
    refine Finset.sum_filter_of_ne ?_
    intro j hj hne' hBj
    exact hne' (by rw [hBj, zero_mul])
  have hTnz : ∀ j ∈ T, B j ≠ 0 := fun j hj => (Finset.mem_filter.mp hj).2
  have hTN : ∀ j ∈ T, j < Nd := fun j hj =>
    Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hj).1).1
  have hTw : ∀ j ∈ T, gam + 1 ≤ (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ) := by
    intro j hj
    obtain ⟨hjsd, hjne⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjr, hjM⟩ := Finset.mem_sdiff.mp hjsd
    have hjNd := Finset.mem_range.mp hjr
    have hge := hSideGe j hjNd hjne
    rcases lt_or_eq_of_le hge with h | h
    · exact Int.add_one_le_iff.mpr h
    · exfalso
      obtain ⟨k, hk, hjk, hkp⟩ := hSideEq j hjNd hjne h.symm
      exact hjM (Finset.mem_image.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hkp⟩, hjk.symm⟩)
  have hRvfM : V.D.Rv f = V.D.Rv (∑ j ∈ M, B j * σ.Φ ^ j) := by
    by_cases hrest : (∑ j ∈ Finset.range Nd \ M, B j * σ.Φ ^ j) = 0
    · rw [hsplit, hrest, add_zero]
    · have hTne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        exact hrest (by rw [← hTsum, hemp, Finset.sum_empty])
      obtain ⟨hTne0, -, jt, hjt, hjteq⟩ := subsum_attain V hdegdev T hTne hTnz hTN
      have hTgt : gam < childW σ σ.Φ estar hstar (∑ j ∈ T, B j * σ.Φ ^ j) := by
        rw [hjteq]
        have := hTw jt hjt
        linarith
      obtain ⟨hMne0, -, jm2, hjm2, hjm2eq⟩ := subsum_attain V hdegdev M hMne hMnz hMNd
      have hMwgam : childW σ σ.Φ estar hstar (∑ j ∈ M, B j * σ.Φ ^ j) = gam := by
        rw [hjm2eq]; exact hMw jm2 hjm2
      have hfne' : (∑ j ∈ M, B j * σ.Φ ^ j) + (∑ j ∈ T, B j * σ.Φ ^ j) ≠ 0 := by
        rw [hTsum, ← hsplit]; exact hf
      have hstep := hRlt (∑ j ∈ M, B j * σ.Φ ^ j) (∑ j ∈ T, B j * σ.Φ ^ j)
        hMne0 hTne0 hfne' (by rw [hMwgam]; exact hTgt)
      calc V.D.Rv f
          = V.D.Rv ((∑ j ∈ M, B j * σ.Φ ^ j) + ∑ j ∈ T, B j * σ.Φ ^ j) := by
            rw [hTsum, ← hsplit]
        _ = V.D.Rv (∑ j ∈ M, B j * σ.Φ ^ j) := hstep
  have hRvsum : V.D.Rv (∑ j ∈ M, B j * σ.Φ ^ j) = ∑ j ∈ M, V.D.Rv (B j * σ.Φ ^ j) :=
    rv_sum V hdegdev gam M hMne hMnz hMNd hMw
  -- ── (C) each tie term is the anchored stride monomial ──────────────────────────
  have hterm : ∀ k ∈ KK, V.D.Rv (B (s0 + estar * k) * σ.Φ ^ (s0 + estar * k))
      = LaurentPolynomial.C (pat k) * LaurentPolynomial.T (a + (k : ℤ)) := by
    intro k hk
    obtain ⟨hkr, hkp⟩ := Finset.mem_filter.mp hk
    have hkle : k ≤ wSide / estar := by have := Finset.mem_range.mp hkr; omega
    obtain ⟨hBne, hBw, hBR⟩ := hDig k hkle hkp
    obtain ⟨c, hcR, hcRv⟩ := V.D.hS5 (B (s0 + estar * k)) hBne (hdegdev _)
    have hceq : ((c : (↥σ.K)ˣ) : ↥σ.K) = pat k := CT_scalar_match (hcR.symm.trans hBR)
    have hpos := stride_pos hee hbez hAnchor hBw
    rw [rv_slot V _ hBne, hcRv, hceq, LaurentPolynomial.T_pow, mul_assoc,
      ← LaurentPolynomial.T_add]
    have harg : - tstar * σ.w (B (s0 + estar * k))
        + ((s0 + estar * k : ℕ) : ℤ) * sstar = a + (k : ℤ) := by linarith [hpos]
    rw [harg]
  -- ── (D) reassembly: Σ over the tie set = T(a)·Ranch ────────────────────────────
  have hinj : ∀ x ∈ KK, ∀ y ∈ KK, s0 + estar * x = s0 + estar * y → x = y := by
    intro x _ y _ h
    have h2 : estar * x = estar * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hsumM : ∑ j ∈ M, V.D.Rv (B j * σ.Φ ^ j)
      = ∑ k ∈ KK, LaurentPolynomial.C (pat k) * LaurentPolynomial.T (a + (k : ℤ)) := by
    rw [hMM, Finset.sum_image hinj]
    exact Finset.sum_congr rfl hterm
  have hRanchL : Polynomial.toLaurent Ranch
      = ∑ k ∈ Finset.range (wSide / estar + 1),
          LaurentPolynomial.C (pat k) * LaurentPolynomial.T (k : ℤ) := by
    rw [hRanch, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.toLaurent_C_mul_T k (pat k)
  have hKfull : ∑ k ∈ KK, LaurentPolynomial.C (pat k) * LaurentPolynomial.T (a + (k : ℤ))
      = LaurentPolynomial.T a * Polynomial.toLaurent Ranch := by
    rw [hRanchL, Finset.mul_sum, hKK, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro k _
    by_cases hp : pat k ≠ 0
    · rw [if_pos hp, LaurentPolynomial.T_add]; ring
    · rw [if_neg hp, not_not.mp hp]
      simp
  have hcoeff0 : Ranch.coeff 0 = pat 0 := by
    rw [hRanch, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp
    · intro k _ hkne
      simp [Polynomial.coeff_X_pow, Ne.symm hkne]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  refine ⟨hwf, by rw [hcoeff0]; exact hpat0, ?_⟩
  rw [hRvfM, hRvsum, hsumM, hKfull]

/-! ### THE KERNEL — the σV-vertex law at the recorded regrade (re-pointed HK-11a) -/

/-- **The σV-vertex law** (HK-12 finding F3's re-pointed HK-11a target): at a coherent
`ReadsOf` record with a non-recentering read `i`, for f's development `B` in the
RECORDED child key, EVERY recorded regrade `σV` of the read pair weighs the vertex
coefficient exactly on the recorded side —

    `σV.w (B μ) = gam − μ·e★·h★·g`  with  `B μ ≠ 0`,

and STRICTLY ABOVE the side below the vertex (the (BOX) leg).  Carried hypotheses:
`StageCoreL σᵢ` (tower provenance) and STRICT read steepness `e★·σᵢ.h < h★` (genuine
only at root/post-recentering reads — HK-12 F5).  Supply: R3a (`anchor_transport`)
fires `V4_readLanding` at V2's ReadFrame; `RegradeOf`'s slot-min clause transports the
landing to σV (`regrade_w_eq_childW`).  SideReads(iii) NOT consumed; `ord_ψ` is the
NODE field `hOrd`. -/
theorem sigmaV_vertexLaw {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (σV : Stage p F)
    (hreg : RegradeOf (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).e
        (H.nodes[i]'(by omega)).h σV) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
    σV.w (B ((H.nodes[i]'(by omega)).μ))
      = (H.nodes[i]'(by omega)).gam
        - ((H.nodes[i]'(by omega)).μ : ℤ)
          * (((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).h : ℤ)
            * ((H.nodes[i]'(by omega)).g : ℤ)) ∧
    ∀ m : ℕ, m < (H.nodes[i]'(by omega)).μ → B m ≠ 0 →
      (H.nodes[i]'(by omega)).gam
        - (m : ℤ) * (((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).h : ℤ)
          * ((H.nodes[i]'(by omega)).g : ℤ))
        < σV.w (B m) := by
  classical
  have hilen : i < H.nodes.length := by omega
  obtain ⟨hmon, hdegf, hcoh, hreads⟩ := h
  have hf : f ≠ 0 := hmon.ne_zero
  -- the recorded frame-i side data
  obtain ⟨B', Nd', Φnext, hdev', hΦnext, hside⟩ := hreads i hilen
  obtain ⟨⟨hSideGe, hSideEq⟩, hDig, -, -, -, -⟩ := hside
  -- the recorded lift = the child key (the coherence leg's IsNodeLift)
  obtain ⟨-, σV', -, hnlift, -⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  -- the read pair (Bézout from the node, steepness carried)
  have hrp : ReadPair (H.nodes[i]'hilen).σ (H.nodes[i]'hilen).e (H.nodes[i]'hilen).h
      (H.nodes[i]'hilen).s (H.nodes[i]'hilen).t := by
    refine ⟨(H.nodes[i]'hilen).he, (H.nodes[i]'hilen).hh, (H.nodes[i]'hilen).hcop,
      (H.nodes[i]'hilen).hbez, ?_, hsteep⟩
    intro he1
    have hc := (H.nodes[i]'hilen).hbezCanon
    rw [he1] at hc
    omega
  -- the ReadFrame (V2) and ψ ≠ X
  have hV := V2_readFrame (H.nodes[i]'hilen).σ hσL (H.nodes[i]'hilen).e
    (H.nodes[i]'hilen).h (H.nodes[i]'hilen).s (H.nodes[i]'hilen).t hrp
  obtain ⟨V⟩ := hV
  have hψne : (H.nodes[i]'hilen).ψ ≠ Polynomial.X := by
    intro hX
    have h0 := (H.nodes[i]'hilen).hzbarRoot
    rw [hX] at h0
    simp only [Polynomial.eval₂_X] at h0
    exact Units.ne_zero (H.nodes[i]'hilen).zbar h0
  -- R3a: the anchor transport at the frame-i development
  obtain ⟨hwf, hanch⟩ := anchor_transport (H.nodes[i]'hilen).σ hrp V f hf B' Nd' hdev'
    (H.nodes[i]'hilen).gam (H.nodes[i]'hilen).s0 (H.nodes[i]'hilen).wSide
    (H.nodes[i]'hilen).pat (H.nodes[i]'hilen).a (H.nodes[i]'hilen).Ranch
    (H.nodes[i]'hilen).hpat0 (H.nodes[i]'hilen).hRanch (H.nodes[i]'hilen).hAnchor
    hSideGe hSideEq hDig
  -- V4-(VERTEX)+(BOX) at the recorded lift
  obtain ⟨⟨hBμne, hVERT⟩, hBOX, -⟩ :=
    V4_readLanding (H.nodes[i]'hilen).σ hσL (H.nodes[i]'hilen).e (H.nodes[i]'hilen).h
      (H.nodes[i]'hilen).s (H.nodes[i]'hilen).t hrp V (H.nodes[i]'hilen).ψ
      (H.nodes[i]'hilen).g (H.nodes[i]'hilen).hψdeg (H.nodes[i]'hilen).hψmonic
      (H.nodes[i]'hilen).hψirr hψne ((H.nodes[i+1]'hi1).σ.Φ)
      ((isNodeLift_iff _ _).mp hnlift) f hf (H.nodes[i]'hilen).μ (H.nodes[i]'hilen).a
      (H.nodes[i]'hilen).Ranch hanch (H.nodes[i]'hilen).hOrd B Nd hdev
  rw [hwf] at hVERT
  refine ⟨hBμne, ?_, ?_⟩
  · rw [regrade_w_eq_childW hreg _ hBμne]
    linarith [hVERT]
  · intro m hm hBm
    have h1 := hBOX m hm hBm
    rw [hwf] at h1
    rw [regrade_w_eq_childW hreg _ hBm]
    linarith [h1]

/-! ### The scale arithmetic (γ-tie + slope law + hLineU → the fenced ℚ-form RHS) -/

/-- The recorded side value at any child-width base index, in the child stage scale:
`STR_{i+1}·line.at(j·childWidth) = gam − j·e★·h★·g` — the K1_SAE arithmetic pattern,
per-index. -/
private lemma lineAt_arith {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hilen : i < H.nodes.length) (hi1 : i + 1 < H.nodes.length) (j : ℕ) :
    ((H.nodes[i]'hilen).gam : ℚ)
      - (j : ℚ) * (((H.nodes[i]'hilen).e : ℚ) * ((H.nodes[i]'hilen).h : ℚ)
          * ((H.nodes[i]'hilen).g : ℚ))
      = (H.strFrame (i+1) : ℚ)
        * (H.nodes[i]'hilen).line.at (j * (H.nodes[i]'hilen).childWidth) := by
  have hγ := hcoh.2.2.1 i hilen
  have hsl := hcoh.2.1 i hilen
  have hu := (H.nodes[i]'hilen).hLineU
  have hDw := (H.nodes[i]'hilen).hDwidth
  rw [strFrame_succ H i hilen]
  simp only [Line.at, Node.childWidth] at hu ⊢
  push_cast at hγ hsl hu ⊢
  linear_combination hγ
    - ((H.strFrame i : ℚ) * (((H.nodes[i]'hilen).e : ℕ) : ℚ)) * hu
    + (((j : ℚ) * (((H.nodes[i]'hilen).e : ℕ) : ℚ) * (((H.nodes[i]'hilen).g : ℕ) : ℚ))
      - ((((H.nodes[i]'hilen).s0 : ℕ) : ℚ) + (((H.nodes[i]'hilen).wSide : ℕ) : ℚ))) * hsl

/-! ### The e′ = 1 consumption shapes (V9's displayed forms; suppliers-in-waiting) -/

/-- **V9_K1nonrec's displayed conclusion on the `ν_{i+1}.e = 1` sub-perimeter** — the
kernel (†) pushed through HK-52's stretch identity (the identity at `e′ = 1`) and the
scale arithmetic.  Binders mirror `V9_K1nonrec` PLUS the three carried hypotheses
(`hσL`, `hsteep`, `he'1` — see the header).  ⚠ NOT a V9 fill: V9's statements quantify
over all `ν_{i+1}.e`; consumption waits on the HK-12 F4 adjudication. -/
theorem readVertex_e1 {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (he'1 : (H.nodes[i+1]'hi1).e = 1)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  classical
  have hilen : i < H.nodes.length := by omega
  have hcoh := h.2.2.1
  obtain ⟨-, σV, hregV, -, htcore⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  obtain ⟨hBμne, hvertex, -⟩ := sigmaV_vertexLaw h i hi1 hsp hσL hsteep B Nd hdev σV hregV
  refine ⟨hBμne, ?_⟩
  have hin : inC (H.nodes[i+1]'hi1).σ.Φ (B ((H.nodes[i]'hilen).μ)) := hdev.1 _
  have hstretch := HK52.hk52_qform_stretch htcore _ hBμne hin
  rw [he'1] at hstretch
  have harith := lineAt_arith hcoh i hilen hi1 (H.nodes[i]'hilen).μ
  rw [hstretch, hvertex]
  push_cast
  linear_combination harith

/-- **V9_E1box_nonrec's displayed conclusion on the `ν_{i+1}.e = 1` sub-perimeter** —
the strict (BOX) leg of the kernel, same transport.  Same three carried hypotheses;
same ⚠ non-fill fence. -/
theorem readBox_e1 {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (he'1 : (H.nodes[i+1]'hi1).e = 1)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (j : ℕ) (hjμ : j < (H.nodes[i]'(by omega)).μ) (hjne : B j ≠ 0) :
    (H.strFrame (i+1) : ℚ) *
        (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
      < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  classical
  have hilen : i < H.nodes.length := by omega
  have hcoh := h.2.2.1
  obtain ⟨-, σV, hregV, -, htcore⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  obtain ⟨-, -, hbox⟩ := sigmaV_vertexLaw h i hi1 hsp hσL hsteep B Nd hdev σV hregV
  have h1 := hbox j hjμ hjne
  have hin : inC (H.nodes[i+1]'hi1).σ.Φ (B j) := hdev.1 _
  have hstretch := HK52.hk52_qform_stretch htcore _ hjne hin
  rw [he'1] at hstretch
  have harith := lineAt_arith hcoh i hilen hi1 j
  rw [← harith, hstretch]
  push_cast
  rw [one_mul]
  exact_mod_cast h1

end HK11a

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK11a.anchor_transport
#print axioms LeanUrat.MovesJ.HK11a.regrade_w_eq_childW
#print axioms LeanUrat.MovesJ.HK11a.sigmaV_vertexLaw
#print axioms LeanUrat.MovesJ.HK11a.readVertex_e1
#print axioms LeanUrat.MovesJ.HK11a.readBox_e1
