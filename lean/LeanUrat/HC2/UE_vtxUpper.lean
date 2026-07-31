import Mathlib
import LeanUrat.HC2.HK11a_vertexTransport

/-!
# UE — U-E: the WGEO/VTX degree-1 perimeter — (M6b)(i) + the (N4)-upper band
(LEANW6 unit, 2026-08-01; SYNTH4 §4 U-E; twins HK-11a/HK-52)

## What this unit is

O-1thr rev 3 (`lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md` §2.5) proved
**Corollary VTX** at the displayed degree-1 perimeter: at every harvested child of a
non-root state, the vertex coefficient `C_μ` is NONZERO (**(M6b)(i)**), its sheared
height is pinned `u_μ = γ`, and its OWN-frame height obeys the **(N4)-UPPER** band

    e₀·vhtx = e₀·w_i(C_μ) ≤ w_{i+1}(C_μ) = γ − μ·γ̂ ≤ γ,   i.e.   vhtx ≤ γ/e₀ = I.

SYNTH4 §4: formalizing this retires the (M6b)(i)/(N4)-upper interface rows and is the
semantic twin of HK-11a — the WGEO vertex pin `u_μ = γ` IS the transport content whose
`e′ ≥ 2` failure HK-52 compiled.  This unit supplies exactly that layer over the
CORPUS carriers (Stage/ReadFrame/History), consuming HK-11a's vertex law:

* `UE.childW_ge_estar_mul_w` — **THE NEW KERNEL** (the level-`i` consumption of the
  development identity (V2b), the step Corollary VTX flags as "needs `e_i·w_i(C_μ) ≤
  w_{i+1}(C_μ)`"): at any read frame with WEAK steepness `e★·σ.h ≤ h★`, the read
  functional dominates `e★·σ.w` on EVERY nonzero polynomial — not only on the
  coefficient space where `hStretch` gives equality.  Proof: the read weight is the
  attained slot-min (`ReadFrame.hK1`), the parent weight is a slot-min LOWER bound at
  the same development (`Stage.hK1` + `hwΦ`), and steepness closes the slot gap.
* `UE.vtx_m6bi_n4upper` — **the packaged Corollary-VTX shape** at a coherent
  `ReadsOf` record with a non-recentering read `i`: for `f`'s development `B` in the
  recorded child key, (a) `B μ ≠ 0` — the (M6b)(i) row; (b) the (N4)-upper WITH the
  displayed shear slack, `e★·σᵢ.w(B μ) ≤ gam − μ·e★·h★·g`; (c) hence
  `e★·σᵢ.w(B μ) ≤ gam`.  Supply: HK-11a's `sigmaV_vertexLaw` (the pin `σV.w(B μ) =
  gam − μ·e★·h★·g`) + `regrade_w_eq_childW` + the kernel.
* `UE.vtx_htUpper_div` — the ℚ display `vhtx ≤ γ/e₀ = I` verbatim (the (R5)-record
  bound the (N4)-upper band asserts; O-1thr §2.5's Corollary VTX final form).

## Carried hypotheses (the honest conditionality — same trio as HK-11a)

`hσL : StageCoreL σᵢ` (tower provenance), STRICT read steepness `e★·σᵢ.h < h★`
(genuine at root/post-recentering reads — HK-12 F5), non-recentering species.  The
e′-stretch guard does NOT enter: the conclusions live at the PARENT frame σᵢ and the
regrade σV, below the `ν_{i+1}.e` seam HK-52 compiled — that is exactly WHY the
degree-1 (N4)-upper is unconditional in e′.  The lower (N4) band and AUX stay with
(M6b)(ii)/(iii) (O-1thr §2.4) — NOT claimed here.  Statements elsewhere are
byte-untouched; new module only; no new axioms.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace UE

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **THE KERNEL — the read functional dominates `e★·σ.w` everywhere** (the level-`i`
development-identity consumption of Corollary VTX/(N4)-upper).  For ANY nonzero `x`
(not merely a key coefficient): develop `x` at `σ.Φ`; the read weight attains
`e★·σ.w(B_j) + j·h★` at some slot `j` (`V.hK1` + `hStretch`), the parent weight is
bounded by `σ.w(B_j) + j·σ.h` at that same slot (`σ.hK1` + `hwΦ`), and weak steepness
`e★·σ.h ≤ h★` closes the slot term.  At `j = 0` (coefficients) this is `hStretch`'s
equality; the content is the general slot. -/
theorem childW_ge_estar_mul_w {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    (hweak : (estar : ℤ) * (σ.h : ℤ) ≤ (hstar : ℤ))
    (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    (estar : ℤ) * σ.w x ≤ childW σ σ.Φ estar hstar x := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg x
  obtain ⟨-, j, hjN, hjne, hjeq⟩ := V.hK1 x B N hx hdev
  obtain ⟨hlow, -⟩ := σ.hK1 x B N hx hdev
  have hj := hlow j hjN hjne
  dsimp only at hjeq hj
  rw [σ.hwΦ] at hj
  rw [hjeq, V.hStretch (B j) hjne (hdev.1 j)]
  have hjnn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  have henn : (0 : ℤ) ≤ (estar : ℤ) := Int.natCast_nonneg estar
  nlinarith [mul_le_mul_of_nonneg_left hj henn, mul_le_mul_of_nonneg_right hweak hjnn]

/-- The kernel at a recorded regrade: `e★·σ.w x ≤ σV.w x` for every nonzero `x`
(`RegradeOf`'s weight is the read functional — `HK11a.regrade_w_eq_childW`). -/
theorem regrade_ge_estar_mul_w {σ σV : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (V : ReadFrame σ estar hstar sstar tstar)
    (hreg : RegradeOf σ estar hstar σV)
    (hweak : (estar : ℤ) * (σ.h : ℤ) ≤ (hstar : ℤ))
    (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    (estar : ℤ) * σ.w x ≤ σV.w x := by
  rw [HK11a.regrade_w_eq_childW hreg x hx]
  exact childW_ge_estar_mul_w V hweak x hx

/-- **The packaged Corollary-VTX shape — (M6b)(i) + the (N4)-upper at degree 1.**
At a coherent `ReadsOf` record with non-recentering read `i` (hypotheses as in
`HK11a.sigmaV_vertexLaw`: tower provenance + strict steepness), for `f`'s
development `B` in the recorded child key:

    (a) `B μ ≠ 0`                                              [(M6b)(i)]
    (b) `e★·σᵢ.w (B μ) ≤ gam − μ·(e★·h★·g)`                    [(N4)-upper, slack displayed]
    (c) `e★·σᵢ.w (B μ) ≤ gam`                                  [`vhtx ≤ I`, cleared form]

Supply: HK-11a's vertex pin `σV.w (B μ) = gam − μ·e★·h★·g` + the kernel above.  The
`e′`-stretch seam (HK-52) never enters: all conclusions live at the parent frame. -/
theorem vtx_m6bi_n4upper {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
    ((H.nodes[i]'(by omega)).e : ℤ)
        * (H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ))
      ≤ (H.nodes[i]'(by omega)).gam
        - ((H.nodes[i]'(by omega)).μ : ℤ)
          * (((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).h : ℤ)
            * ((H.nodes[i]'(by omega)).g : ℤ)) ∧
    ((H.nodes[i]'(by omega)).e : ℤ)
        * (H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ))
      ≤ (H.nodes[i]'(by omega)).gam := by
  have hilen : i < H.nodes.length := by omega
  obtain ⟨hmon, hdegf, hcoh, hreads⟩ := h
  obtain ⟨-, σV, hregV, -, -⟩ := (hcoh.2.2.2 i hi1).2.1 hsp
  obtain ⟨hBμne, hvert, -⟩ := HK11a.sigmaV_vertexLaw ⟨hmon, hdegf, hcoh, hreads⟩
    i hi1 hsp hσL hsteep B Nd hdev σV hregV
  -- the read pair and its frame (as in HK-11a)
  have hrp : ReadPair (H.nodes[i]'hilen).σ (H.nodes[i]'hilen).e (H.nodes[i]'hilen).h
      (H.nodes[i]'hilen).s (H.nodes[i]'hilen).t := by
    refine ⟨(H.nodes[i]'hilen).he, (H.nodes[i]'hilen).hh, (H.nodes[i]'hilen).hcop,
      (H.nodes[i]'hilen).hbez, ?_, hsteep⟩
    intro he1
    have hc := (H.nodes[i]'hilen).hbezCanon
    rw [he1] at hc
    omega
  obtain ⟨V⟩ := V2_readFrame (H.nodes[i]'hilen).σ hσL (H.nodes[i]'hilen).e
    (H.nodes[i]'hilen).h (H.nodes[i]'hilen).s (H.nodes[i]'hilen).t hrp
  -- kernel: e★·σᵢ.w (B μ) ≤ σV.w (B μ) = gam − μ·e★·h★·g
  have hker := regrade_ge_estar_mul_w V hregV (le_of_lt hsteep) _ hBμne
  rw [hvert] at hker
  have hnn : (0 : ℤ) ≤ ((H.nodes[i]'hilen).μ : ℤ)
      * (((H.nodes[i]'hilen).e : ℤ) * ((H.nodes[i]'hilen).h : ℤ)
        * ((H.nodes[i]'hilen).g : ℤ)) := by positivity
  exact ⟨hBμne, hker, by linarith⟩

/-- **Corollary VTX's final ℚ display: `vhtx ≤ γ/e₀ = I`.**  The vertex coefficient's
own-frame height is at most the read intercept — the exact (R5)-record bound of the
(N4)-UPPER band (O-1thr rev 3 §2.5), at the recorded read's data. -/
theorem vtx_htUpper_div {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hσL : StageCoreL (H.nodes[i]'(by omega)).σ)
    (hsteep : ((H.nodes[i]'(by omega)).e : ℤ) * ((H.nodes[i]'(by omega)).σ.h : ℤ)
        < ((H.nodes[i]'(by omega)).h : ℤ))
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    ((H.nodes[i]'(by omega)).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ)
      ≤ ((H.nodes[i]'(by omega)).gam : ℚ) / ((H.nodes[i]'(by omega)).e : ℚ) := by
  have hilen : i < H.nodes.length := by omega
  obtain ⟨-, -, hup⟩ := vtx_m6bi_n4upper h i hi1 hsp hσL hsteep B Nd hdev
  have hepos : (0 : ℚ) < ((H.nodes[i]'hilen).e : ℚ) := by
    have := (H.nodes[i]'hilen).he
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  rw [le_div_iff₀ hepos]
  have hq : (((H.nodes[i]'hilen).e : ℤ)
      * (H.nodes[i]'hilen).σ.w (B ((H.nodes[i]'hilen).μ)) : ℚ)
      ≤ (((H.nodes[i]'hilen).gam : ℤ) : ℚ) := by
    exact_mod_cast hup
  push_cast at hq ⊢
  linarith

end UE

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.UE.childW_ge_estar_mul_w
#print axioms LeanUrat.MovesJ.UE.regrade_ge_estar_mul_w
#print axioms LeanUrat.MovesJ.UE.vtx_m6bi_n4upper
#print axioms LeanUrat.MovesJ.UE.vtx_htUpper_div
