/-
Unit K1.vertexPin  (HC-2 campaign — K1 KERNEL bridge, 2026-07-28; ADDITIVE unit, census +1;
no existing statement or Defs change anywhere in this file's cone)

THE READ-INDEXED D.8 VERTEX PIN — the single law behind the three open HC-2 residuals
U20a (`NA_transport_root`), U20b (`NA_transport_increment`), U22-E2 (`SAE_vertexEq_endpoint`):
at consecutive reads (i, i+1) of a run, for ANY parent species, the parent's line value at
the standing vertex base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of
f's development at the vertex slot, and the vertex coefficient is nonzero (§B2-DEF D.8
(VERTEX), read against §C C.1.0(c)'s stage scale: stage-(i+1) weights are `STR_{i+1} ×`
absolute, `Node.line` absolute).

STRUCTURE (what is proved here / what is the one named residual):
* `K1_readVertexPin` — THE UNIFIED KERNEL (species-generic). Proof = species dichotomy:
  - RECENTERING parent: PROVED — consumed verbatim from the landed `NA_transport_recentering`
    (U20c, the g = 1 `IsStandardLift` route through `L5_landVertex`).
  - ROOT/INCREMENT parent: `K1_readVertexPin_nonrec` — the ONE remaining sorry, with the
    full obstruction record at its declaration (why no on-disk asset closes it; the exact
    carry-algebra design it needs).
* `K1_NA_transport_root` / `K1_NA_transport_increment` — U20a's/U20b's fenced statements
  VERBATIM (byte-identical conclusions and binders), one-line consumers of the kernel:
  the assigned provers can close the unit files by `exact` against these.
* `K1_SAE_vertexEq_endpoint` — U22-E2's fenced statement VERBATIM, PROVED from the kernel
  + the child read's SideReads(ii) top-endpoint equality + the γ-tie (the u*-tie of the
  F-4 spec). Its only conditionality is the kernel's non-recentering leg.

moves_ref: §B2-DEF D.8 (BOX)/(VERTEX) displays (MOVES 2467–2546); §C C.0 (NA)/(SAE)
displays; blueprint §9 F-2/F-4 semantic specs.
deps: D4 (`SideReads`/`ReadsOf`), `HistoryCoherent` (γ-tie, width chain), U20c's
`NA_transport_recentering` (PROVED, this file's only unit-layer import).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U20c_NAtransportRecentering

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

section K1Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A development truncation extends upward: the zero tail is free (Fact A bookkeeping —
lets the kernel be applied at `max Nd (μ+1)` when the recorded truncation is short). -/
lemma isDevelopment_extend {R : Type*} [CommRing R] {Φ f : Polynomial R}
    {B : ℕ → Polynomial R} {N N' : ℕ} (h : IsDevelopment Φ f B N) (hNN' : N ≤ N') :
    IsDevelopment Φ f B N' := by
  refine ⟨h.1, fun j hj => h.2.1 j (le_trans hNN' hj), ?_⟩
  rw [h.2.2]
  refine Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNN')) ?_
  intro j hj hjN
  rw [h.2.1 j (by simpa using hjN), zero_mul]

/-- The accumulated stretch is positive (every read has `1 ≤ e`). -/
lemma strFrame_pos (H : History p F) (i : ℕ) : 0 < H.strFrame i := by
  unfold History.strFrame
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨ν, -, hν0⟩ := List.mem_map.mp h0
  exact absurd hν0.symm (by have := ν.he; omega)

end K1Helpers

/-  ═══════════════════════════════════════════════════════════════════════════════════
    K1 CORE OBSTRUCTION RECORD (2026-07-28, K1 kernel pass) — the non-recentering leg is
    the genuine kernel; it does not close from any proved on-disk asset:

    1. WHAT CLOSES. At a RECENTERING parent the read pair is tied to the frame pair
       (σ.e = 1, and the two-endpoint h-tie inside `NA_transport_recentering` forces
       ν.h = σ.h), so `Φ − lift` is a g = 1 `IsStandardLift` of the PARENT stage and the
       PROVED frame-pair engine `L5_landVertex` applies. That leg is consumed verbatim
       below; U20c LANDED on this route.

    2. WHY THE STANDARD-LIFT TRICK DOES NOT EXTEND TO INCREMENTS/ROOT (the charge's
       explicit check — answer: NO analogous bridge exists). The recorded lift at a
       non-recentering parent is `IsNodeLift ν Φ̂` (HistoryCoherent's non-recentering leg):
       stride ν.e, realizer weights σ.w(t_k) = ν.h·(g − k) on the CURRENT valuation,
       residual positions −σ.t·σ.wPrev(t_k). `IsStandardLift σ ψ g Φ̂` demands stride σ.e,
       PARENT-valuation weights σ.wPrev(t_k) = σ.h·(g − k), positions −σ.t·σ.h·(g − k).
       Under `hStretch` the two systems coincide exactly when (ν.e, ν.h) = (σ.e, σ.e·σ.h)
       — which is the recentering configuration after the h-tie — and at a genuine
       increment read the side is strictly steeper (ν.h > ν.e·σ.h, forced by the slot
       computation in 3 below), so NO stage instantiates the frame-pair engine on the
       recorded lift. The root read is the same case (the root frame's pair is the base
       pair, the root READ's pair is f's own first side — unrelated).

    3. WHY THE FRAME GRADING IS STRUCTURALLY BLIND HERE. Every proved D.8 asset
       (`L5_landVertex`, `L5_landVertexDigit` + repair, `L5_landTwoSided_repair`,
       `L5_landTransport_R4`) pins the vertex AT THE FRAME PAIR: they route the ψ-order
       through the lift residual `σ.R Φ̂ = T(−σ.t·σ.h·g)·ψ(z)`, which holds because a
       frame-pair standard lift is σ.w-EQUAL-WEIGHT across its slots
       (σ.w(t_k·Φ^{σ.e·k}) = σ.e·σ.h·g for every k). The READ-pair lift is NOT: its slot
       weights are ν.h·(g−k) + ν.e·k·σ.h, strictly decreasing in k whenever ν.h > ν.e·σ.h
       (and ν.h ≤ ν.e·σ.h contradicts (I-aug): each slot term would weigh ≥ g·ν.h ≥ ν.h,
       forcing σ.w Φ̂ ≥ ν.h against ν.h > ν.e·σ.w Φ̂) — so the σ.w-minimal slot is the TOP
       slot alone, `hRlt` gives `σ.R Φ̂ = T(σ.s·ν.e·g)`, and ψ NEVER APPEARS in the parent
       grading of the read lift. No argument through σ.R(Φ̂) can see the descend datum.

    4. WHAT THE LEG NEEDS (the named design, for the dedicated unit — the B2-FINAL carry
       algebra, MOVES pass 7–8). The vertex law lives in the READ grading
       F(j) := ν.e·σ.w(B_j) + j·ν.h (= σ'.w on the Φ̂-development, via `child_slotmin` +
       `hStretch`/`child_wPrev`), and its content is the parent↔child development carry
       composition: writing B_j = Σ_{l<ν.e·g} b_{j,l}·Φ^l and expanding
       f = Σ_j B_j·(Φ^{ν.e·g} + τ)^j (τ := Σ_k t_k·Φ^{ν.e·k}), EVERY expansion path
       b_{j,l}·(∏_i t_{k_i})·Φ^L (L = l + ν.e·Σk_i + ν.e·g·(j−m), ψ-level carry offset r)
       has read value
         ν.e·σ.w(b_{j,l}·∏t) + (L+r)·ν.h
           = [ν.e·σ.w(b_{j,l}) + l·ν.h] + j·(ν.e·g·ν.h) + r·(ν.h − ν.e·σ.h) + (≥ 0 slack),
       with ν.h − ν.e·σ.h > 0: the read functional is EQUAL-WEIGHT on each (j, l) block
       across all carry paths, and genuine carries strictly ascend — the triangular
       composition inverts, and SideReads(i)'s support line at value gam transports to
       (BOX)+(VERTEX) of the child development: F(μ) = gam − μ·(ν.e·g − 1)·ν.h attained,
       B μ ≠ 0. The scale arithmetic below (`γ-tie + slope law + hLineU`) converts exactly
       this to the fenced ℚ-form. This is the ONE hard dedicated unit the kernel names —
       the read-side mirror of HC-1 §9.5's S9w block; no smaller on-disk lemma suffices
       (the fleet round-3 U20a/U20b chains were report-side only, and the F-2 spec's
       pointer to `L5_landTransport_R4` is frame-pair-keyed, see 3).

    5. REV (2026-07-28, carry-bridge escalation round) — THE DEFINITIVE R3b RECORD now
       lives at `HC1/V9_K1nonrec.lean` (the REV-3 block at its `sorry`).  Summary: the
       residue of item 4 is REDUCED, Lean-core, to the BOTTOM-WINDOW LAW at the vertex
       coefficient (`V9_wvEqStretch_of_bottomSlot`/`V9_bottomSlot_of_wvEqStretch`); a
       sympy-verified countermodel (f = (X+8)(Φ̂²+8X³), (1,1)-Gauss frame, read pair
       (1,2)) shows it is NOT derivable from SideReads(i)/(ii)/(vi) + hOrd + the proved
       V-frame engine (V1–V4) — the sole blocking clause is SideReads(iii)'s `σ.R f`
       rendering, the U31-fenced seam.  The needed display: §B2-DEF D.8-(TRANSPORT),
       upward leg, the FORCED-WINDOW clause (MOVES 2521–2528) at the regraded frame —
       fenced OUT of V4 by HC-1 blueprint §10.1 ("not needed"): that fencing is WRONG
       for this kernel.  Dedicated unit = the (TRANSPORT) transcription at the
       ReadFrame; the kernel then closes through V9's reduction lemmas.
    ═══════════════════════════════════════════════════════════════════════════════════ -/

/-- **The K1 kernel residual** (read-indexed D.8 vertex law, NON-RECENTERING parent):
at consecutive reads of a run whose parent read `i` is a root or increment read, the
parent's line value at the standing vertex base is realized as the frame-(i+1) actual
slot weight of f's development at the vertex slot, and that vertex coefficient is
nonzero. QUEUED-HARD: the carry-algebra unit per the obstruction record above. -/
theorem K1_readVertexPin_nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

/-- **THE READ-INDEXED D.8 VERTEX PIN** (the K1 kernel, species-generic): at consecutive
reads (i, i+1) of a run — ANY parent species — the parent's line value at the standing
vertex base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of f's
development at the vertex slot (stage scale: `σ.w = STR ×` absolute), and that vertex
coefficient is nonzero. The single law U20a/U20b/U22-E2 consume. -/
theorem K1_readVertexPin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  by_cases hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering
  · exact NA_transport_recentering h i hi1 hsp B Nd hdev hNd
  · exact K1_readVertexPin_nonrec h i hi1 hsp B Nd hdev hNd

/-- U20a's fenced statement VERBATIM (F-2/U20a `NA_transport_root`), from the kernel —
the species hypothesis is not even needed (the kernel is species-generic); it is carried
so the unit file can close by `exact K1_NA_transport_root h i hi1 hsp B Nd hdev hNd`. -/
theorem K1_NA_transport_root {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.root)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) :=
  K1_readVertexPin h i hi1 B Nd hdev hNd

/-- U20b's fenced statement VERBATIM (F-2/U20b `NA_transport_increment`), from the
kernel; species hypothesis carried for unit-file `exact`-closure. -/
theorem K1_NA_transport_increment {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.increment)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) :=
  K1_readVertexPin h i hi1 B Nd hdev hNd

/-- U22-E2's fenced statement VERBATIM (F-4/U22-E2 `SAE_vertexEq_endpoint`), PROVED from
the kernel: at consecutive reads of a run whose child window REACHES the standing vertex
(`s0' + wSide' = μ`), the new side height `u*'` equals the standing vertex height — the
parent line's value at the vertex base `μ·childWidth`.

ROUTE (the F-4 u*-tie, executed): the run's recorded development at read i+1 realizes the
child side; its TOP stride slot is `s0' + wSide' = μ` (SideReads(ii) at `k = wSide'/e'`,
`hEdvd` + `hpatTop`), giving the ON-SIDE equality
`e'·σ'.w(B μ) + μ·h' = gam'`; the γ-tie at read i+1 (with the adjacency hypothesis) turns
this into `σ'.w(B μ) = STR_{i+1}·u*'`; the kernel pins the SAME quantity to
`STR_{i+1}·line_i.at(μ·childWidth)`; cancel `STR_{i+1} > 0`. `Node.line`/`Node.ustar` are
absolute v_p-scale, so no stretch factor survives — exactly as the unit's header states. -/
theorem K1_SAE_vertexEq_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ) :
    (H.nodes[i+1]'hi1).ustar
      = (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  classical
  have hi : i < H.nodes.length := by omega
  have h' := h
  obtain ⟨hfmon, hfdeg, hcoh, hruns⟩ := h'
  obtain ⟨-, -, hgamtie, -⟩ := hcoh
  obtain ⟨B, Nd, Φnext, hdev, -, hside⟩ := hruns (i+1) hi1
  obtain ⟨-, hdig, -, -, -, -⟩ := hside
  set νp : Node p F := H.nodes[i]'hi with hνp
  set ν' : Node p F := H.nodes[i+1]'hi1 with hν'
  -- the kernel at the (upward-extended) recorded development
  have hdev' := isDevelopment_extend hdev (le_max_left Nd (νp.μ + 1))
  obtain ⟨hBne, hkey⟩ := K1_readVertexPin h i hi1 B (max Nd (νp.μ + 1)) hdev'
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
  -- the child side's top endpoint sits ON the side at slot μ
  obtain ⟨-, heqtop, -⟩ := hdig (ν'.wSide / ν'.e) le_rfl ν'.hpatTop
  have hslot : ν'.s0 + ν'.e * (ν'.wSide / ν'.e) = νp.μ := by
    rw [Nat.mul_div_cancel' ν'.hEdvd]; exact hadj
  rw [hslot] at heqtop
  -- the γ-tie at read i+1, with the adjacency rewrite
  have hgt := hgamtie (i+1) hi1
  rw [← hν'] at hgt
  rw [hadj] at hgt
  -- positivity of the cancellation factors
  have hepos : (0 : ℚ) < (ν'.e : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ν'.he
  have hSpos : (0 : ℚ) < (H.strFrame (i + 1) : ℚ) := by exact_mod_cast strFrame_pos H (i + 1)
  -- combine in ℚ: e'·σ'.w(B μ) + μ·h' = gam' = e'·(STR·u*') + μ·h'
  have heqQ : (ν'.e : ℚ) * ((ν'.σ.w (B νp.μ) : ℤ) : ℚ) + (νp.μ : ℚ) * (ν'.h : ℚ)
      = ((ν'.gam : ℤ) : ℚ) := by exact_mod_cast heqtop
  have h1 : ((ν'.σ.w (B νp.μ) : ℤ) : ℚ) = (H.strFrame (i + 1) : ℚ) * ν'.ustar := by
    have h2 : (ν'.e : ℚ) * ((ν'.σ.w (B νp.μ) : ℤ) : ℚ)
        = (ν'.e : ℚ) * ((H.strFrame (i + 1) : ℚ) * ν'.ustar) := by
      linarith
    exact mul_left_cancel₀ (ne_of_gt hepos) h2
  have h3 : (H.strFrame (i + 1) : ℚ) * ν'.ustar
      = (H.strFrame (i + 1) : ℚ) * νp.line.at (νp.μ * νp.childWidth) := by
    rw [← h1]
    exact hkey
  exact mul_left_cancel₀ (ne_of_gt hSpos) h3

end LeanUrat.MovesJ
