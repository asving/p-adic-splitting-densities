/-
Unit HK-20  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-20.

INFORMAL STATEMENT (blueprint): "SideReads at read 1 (terminal): the Φ̂-development
(0, 2, 1) — clause (i)/(ii) at the recorded side; (iii) anchor of σ₁.R f (single-side
read — the ⚠ (iii) seam is FAITHFUL here); (iv) terminal `LandingKey ν₁ Φtop`
(existential Φnext — the last-read freedom); (v)/(vi) at ν₁ (vi's development is in
Φtop; concrete)."  deps: HK-16, HK-18.

E-PHASE RESOLUTIONS (recorded; inherited from HK-18):
* The development is (16, 2, 1), not "(0, 2, 1)" — HK-18 resolution R-1 (the primary
  quartic has no coherent read 1; the blueprint's own "minimal variant" branch is
  taken: fgate = Φ̂² + 2·Φ̂ + 16, adjacent side slots 0–1 at the steep pair (1, 3),
  γ₁ = 4, slot 2 strictly above at 6).
* σ₁ (HK-15, not on disk) is a parameter; its laws enter through the HK-16 hypothesis
  pack (htc : the transition record — child_key/child_wPrev/child_slotmin/…; hpin :
  the D.8 vertex pin, supplying the mfun ≡ 0 digit scalars clause (ii) reads; hw :
  the childW tie, computing σ₁.w on the concrete slots). hΦ := htc.base.child_key at
  the P-phase re-bind; here it is bound separately because `ν₁gate` consumes it.
* Blueprint MANDATORY split rule (>100 proof lines ⇒ named seams): pre-executed —
  each SideReads conjunct is its own named declaration; (iv)+(vi) are ONE declaration
  because both read the SAME existential Φtop (the SideReads Φnext parameter: the
  last-read freedom is a single designation, not two).

DATA (hand-verified): child weights σ₁.w(C 16) = 4, σ₁.w(C 2) = 1, σ₁.w(1) = 0 (childW
at (1,3) over bw); side functional 1·w + j·3 = (4, 4, 6) — γ₁ = 4 exactly at the
stride slots 0, 1 (= s0 + k, k ≤ wSide/e = 1), digits pat ≡ 1 at position
T(−σ₁.t·σ₁.wPrev B) = T 0 (σ₁.t = 0 via Stage.he1t at σ₁.e = 1). Anchor: σ₁.R fgate
= R(C 16) + R(C 2)·R(Φ̂) = 1 + z (hRPhi: R(Φ̂) = T s₁ = z) = T 0·toLaurent(Ranch₁),
a₁ = 0, ord_{z−1}(z + 1) = 1 = μ₁ (char 2). Landing: ν₁ is recentering-species (HK-18
resolution R-2) — LandingKey's recentering leg wants the recorded lift to realize the
center: lift = polOM's choice on `RecenterLiftSpec ν₁` (nonempty: C 8 has σ₁.w = 3 =
σ₁.w Φ̂ and digit 1 = center₁ at position 0), Φtop := Φ̂ − ν₁.lift. Vertex read-off:
in Φtop-coordinates fgate = Φtop² + (2ℓ + 2)Φtop + (ℓ² + 2ℓ + 16) at ℓ := ν₁.lift, so
the μ₁ = 1 slot digit is digPrime(2ℓ + 2) = digPrime(C 2) = 1 (w(2ℓ) = 4 > 1 = w(C 2))
= vtx ν₁ (a = 0, m̂ = 0, vtxPoly = 1).

PROOF SKETCH (P-phase): clause (i)/(ii) by interval_cases over the three slots with hw
+ hpin (digit scalars) + he1t (t = 0); (iii) by the residual computation above through
htc.base + hpin + hRPhi-from-htc (the S5′ key residual is `child_dig_frame`/VertexPin
content at B := Φ̂? NO — R(Φ̂) = T s' is `ChildResData.hRPhi`, an HK-15 pin: if the
HK-16 pack under-supplies it, SURFACE per the K-4 seam rule — expected residue, noted);
(iv)+(vi) via polOM choice + Fact-B uniqueness in Φtop (monic quadratic);
(v) lift leg by `CanonPolicy.blind` (rfl-grade), canonRoot leg: unique root 1 of
z − 1. Difficulty hard-fable ~120 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK18
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.K1_vertexPin

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace HK20

open HK18

/-- The child (frame-1, key Φ̂ = fq) development of fgate: slot coefficients
(C 16, C 2, 1), window length 3 (HK-18 resolution R-1's corrected display of the
blueprint's "(0, 2, 1)"). -/
noncomputable def Bdev1 : ℕ → Polynomial ℤ_[2] :=
  fun j =>
    if j = 0 then Polynomial.C 16
    else if j = 1 then Polynomial.C 2
    else if j = 2 then 1
    else 0

/-- Bdev1 IS fgate's development at the child key fq (the `ReadsOf` i = 1 witness
datum — the P-phase rewrites the key to σ₁.Φ through the transition record's
child_key). -/
theorem Bdev1_dev : IsDevelopment U31.fq fgate Bdev1 3 := by
  sorry

section

variable (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq)
  (htc : TransitionCoreL U31.bStage σ₁ U31.fq 1 3 U31.ν₀.zbar)
  (hpin : VertexPin U31.bStage σ₁ U31.fq U31.ν₀.zbar)
  (hw : ∀ f, f ≠ 0 → σ₁.w f = childW U31.bStage U31.fq 1 3 f)

/-- SideReads clause (i), lower bound, at (ν₁gate σ₁ hΦ, Bdev1, 3): the read
functional `e·σ₁.w(B_j) + j·h` at the steep pair (1, 3) is ≥ γ₁ = 4 at every nonzero
slot. Byte-copy of the first (i) conjunct of `SideReads` at read 1. -/
theorem sideReads1_side_lb :
    ∀ j : ℕ, j < 3 → Bdev1 j ≠ 0 →
      (ν₁gate σ₁ hΦ).gam ≤ ((ν₁gate σ₁ hΦ).e : ℤ) * (ν₁gate σ₁ hΦ).σ.w (Bdev1 j)
        + (j : ℤ) * ((ν₁gate σ₁ hΦ).h : ℤ) := by
  sorry

/-- SideReads clause (i), equality slots are stride slots, at (ν₁gate σ₁ hΦ, Bdev1, 3):
equality (= 4) holds only at slots 0, 1 = s0 + k, k ≤ wSide/e = 1 (slot 2 sits at 6).
Byte-copy of the second (i) conjunct of `SideReads` at read 1. -/
theorem sideReads1_side_eq :
    ∀ j : ℕ, j < 3 → Bdev1 j ≠ 0 →
      ((ν₁gate σ₁ hΦ).e : ℤ) * (ν₁gate σ₁ hΦ).σ.w (Bdev1 j)
          + (j : ℤ) * ((ν₁gate σ₁ hΦ).h : ℤ) = (ν₁gate σ₁ hΦ).gam →
      ∃ k : ℕ, k ≤ (ν₁gate σ₁ hΦ).wSide / (ν₁gate σ₁ hΦ).e ∧
        j = (ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k ∧ (ν₁gate σ₁ hΦ).pat k ≠ 0 := by
  sorry

/-- SideReads clause (ii), DIGITS, at (ν₁gate σ₁ hΦ, Bdev1, 3): both stride
coefficients (C 16, C 2) are nonzero, ON the side, with monomial-unit residuals of
scalar pat k = 1 at position T(−σ₁.t·σ₁.wPrev B) (= T 0 at σ₁.t = 0; scalars via the
vertex pin `hpin`, mfun ≡ 0). Byte-copy of the (ii) conjunct of `SideReads` at
read 1. -/
theorem sideReads1_digits :
    ∀ k : ℕ, k ≤ (ν₁gate σ₁ hΦ).wSide / (ν₁gate σ₁ hΦ).e → (ν₁gate σ₁ hΦ).pat k ≠ 0 →
      Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k) ≠ 0 ∧
      ((ν₁gate σ₁ hΦ).e : ℤ) *
          (ν₁gate σ₁ hΦ).σ.w (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k))
          + (((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k : ℕ) : ℤ) *
            ((ν₁gate σ₁ hΦ).h : ℤ) = (ν₁gate σ₁ hΦ).gam ∧
      (ν₁gate σ₁ hΦ).σ.R (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k)) =
        LaurentPolynomial.C ((ν₁gate σ₁ hΦ).pat k) *
          LaurentPolynomial.T (- (ν₁gate σ₁ hΦ).σ.t *
            (ν₁gate σ₁ hΦ).σ.wPrev (Bdev1 ((ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).e * k))) := by
  sorry

/-- SideReads clause (iii), ANCHOR + ψ-ORDER, at read 1 (the single-side read — the
⚠ (iii) `σ.R f` seam is FAITHFUL here, per the blueprint): σ₁.R(window sum) =
T 0 · toLaurent(z + 1) anchors at (a₁, Ranch₁) = (0, z + 1), and ord_{z−1}(z+1) = 1
= μ₁ (char 2). Byte-copy of the (iii) conjunct of `SideReads` at read 1. -/
theorem sideReads1_anchor_ord :
    HasAnchorK ((ν₁gate σ₁ hΦ).σ.R
        (∑ j ∈ Finset.range 3, Bdev1 j * (ν₁gate σ₁ hΦ).σ.Φ ^ j))
      (ν₁gate σ₁ hΦ).a (ν₁gate σ₁ hΦ).Ranch ∧
    OrdPsiPoly (ν₁gate σ₁ hΦ).ψ (ν₁gate σ₁ hΦ).Ranch (ν₁gate σ₁ hΦ).μ := by
  sorry

/-- SideReads clauses (iv) + (vi) jointly, at read 1 (TERMINAL — the last-read
freedom: Φnext is EXISTENTIAL, one designation shared by both clauses):
(iv) the recorded landing produces a key — `LandingKey (ν₁gate …) Φtop` (ν₁ is
recentering-species, HK-18 resolution R-2, so this is the recorded-lift realizer leg:
Φtop = Φ̂ − ν₁.lift);
(vi) VERTEX READ-OFF in Φtop-coordinates: any Φtop-development of the window sum
(= fgate) has its μ₁ = 1 slot digit equal to vtx ν₁ (= 1; digit of 2·lift + 2). -/
theorem sideReads1_terminal :
    ∃ Φtop : Polynomial ℤ_[2],
      LandingKey (ν₁gate σ₁ hΦ) Φtop ∧
      ∀ (Bh : ℕ → Polynomial ℤ_[2]) (Nh : ℕ),
        IsDevelopment Φtop (∑ j ∈ Finset.range 3, Bdev1 j * (ν₁gate σ₁ hΦ).σ.Φ ^ j) Bh Nh →
        (ν₁gate σ₁ hΦ).σ.digPrime (ν₁gate σ₁ hΦ).zbar (Bh (ν₁gate σ₁ hΦ).μ)
          = (ν₁gate σ₁ hΦ).vtx := by
  sorry

/-- SideReads clause (v), at read 1: ν₁ carries the polOM lift (rfl-grade via
`CanonPolicy.blind` — HK-18's aux-node pattern) and the canonical residue root
(z − 1 has the unique root 1 in F4). -/
theorem sideReads1_lifts :
    (ν₁gate σ₁ hΦ).lift = (polOM 2 F4).liftOf (ν₁gate σ₁ hΦ) ∧
    (((ν₁gate σ₁ hΦ).zbar : F4ˣ) : F4) = canonRoot (ν₁gate σ₁ hΦ) := by
  sorry

end

end HK20

end LeanUrat.MovesJ
