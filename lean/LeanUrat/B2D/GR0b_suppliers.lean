/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs
import LeanUrat.B2D.GR0_readHyps

/-!
# B2D/GR0b_suppliers — THE WAVE-2a SUPPLIER VERDICT for `hscale`/`hψ0`
  [B2DEF_LEAN unit GR-0 addendum; wave 2a]

Blueprint §5 GR-0 ("the history-level slope law of `HistoryCoherent` is the wave-2
supplier candidate") + the wave-2a charge: attempt `readHyps_of_history`, or compile
the exact obstruction. deps: E1, GR-0. **NO sorry in this file.**

## VERDICT (both displayed residues discharged; GR-0's table updated in place)

* **`hψ0` — SUPPLIED AT EVERY SINGLE NODE** (`node_hψ0` below): the GR-0 probe
  verdict "no corpus pin `c̃ ≠ 0`" was WRONG — the pin exists through the
  anchored-residual provenance: `Node.hOrd` gives `ψ^μ ∣ Ranch` with `μ ≥ 1`
  (`Node.hμ`), and `Ranch.coeff 0 = pat 0 ≠ 0` (`Node.hRanch` + `Node.hpat0`), so
  `ψ.coeff 0 = 0` would force `X ∣ ψ ∣ Ranch`, killing the anchor digit. At a
  recentering (`ψ = z − c̃`) this IS the pin `c̃ ≠ 0`. No history needed.
* **`hscale` — SUPPLIED AT INTERIOR COHERENT READS** (`readHyps_of_history`): for a
  NON-ROOT node `ν = H.nodes[i+1]` of a coherent history whose frame-creating
  transition is non-recentering, `TransitionCoreL`'s `child_e`/`child_h` tie the
  frame pair to the node's own read pair (`ν.σ.e = ν.e`, `ν.σ.h = ν.h`), whence with
  `Stage.hwΦ`: `hscale ⟺ ν.e = 1`. The `ν.e = 1` leg is itself supplied on the
  recorded perimeter: by the RG-2 recording fence at interior non-recentering reads
  (`node_e_one_of_interior`), and by `Node.hspecRec` at recenterings — so `hscale`
  is EXACTLY the corpus's disclosed e = 1 recording perimeter, now compiled.
* **THE SCOPING FORCING, compiled** (`readHyps_e_eq_one`): `ReadHyps ν` alone
  already forces `ν.e = 1` (via `Node.hcop`: `gcd(e, e·σ.h) = e`), hence `ν.t = 0`
  (`hbezCanon` window), `ν.s = 1` (`hbez`), `ν.mhat = 0`, `ν.h = ν.σ.h`. So the
  displayed pack was never a steep-read theory: GR is honestly the e = 1/[NR] layer
  (matching blueprint fence (ii) and the RG-2 fence). At a steep recorded read
  (`ν.e ≥ 2`, e.g. the compiled `ramifiedStage` read pair (2,5)) `hscale` is FALSE
  (`child_h` makes it `5 = 2·5`), so `graded_read` is vacuous there — the steep
  graded identity is `kp_step`'s child-model business (fence (viii)), not GR's.
* **THE FRAME-SIDE RESIDUE, named** (`frame_level_of_history`): GR-3/GR-4's sum
  arithmetic additionally consumes the FRAME pins `ν.σ.s = 1`, `ν.σ.t = 0` — NOT
  `ReadHyps` fields, NOT derivable from them at the abstract carrier (see the GR-3
  obstruction record), but supplied at the SAME interior-read configuration by
  `child_e` + `Stage.he1t` + `Stage.hbez`. This is the GR-3/GR-4 supplier.

Scope note: the root node (`i = 0`) has NO supplier (its frame pair is untied to the
read pair — a single-node coherent history hosts arbitrary frames), and a node whose
frame was created by a RECENTERING ties to the grandparent chain (`IsRecentering`
preserves `w`, so `σ'.h = σ.h` propagates back to the last genuine landing); the
recentering-chain extension is stated as future work, not silently assumed.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ## 1. The `hψ0` supplier — single-node, no history -/

/-- **`hψ0` IS corpus-supplied at every node** (upgrading GR-0's table): the anchored
residual has nonzero constant digit (`hpat0` is the polygon's anchor-exactness), `ψ`
divides it (`hOrd` at `μ ≥ 1`), so `ψ(0) ≠ 0`. At a recentering `ψ = z − c̃` this is
exactly the missing pin `c̃ ≠ 0`. -/
theorem node_hψ0 (ν : Node p F) : ν.ψ.coeff 0 ≠ 0 := by
  intro h0
  -- `X ∣ ψ ∣ ψ^μ ∣ Ranch` (μ ≥ 1), so the anchor digit vanishes:
  have hXψ : Polynomial.X ∣ ν.ψ := Polynomial.X_dvd_iff.mpr h0
  have hψR : ν.ψ ∣ ν.Ranch :=
    dvd_trans (dvd_pow_self ν.ψ (by have := ν.hμ; omega)) ν.hOrd.1
  have hR0 : ν.Ranch.coeff 0 = 0 := Polynomial.X_dvd_iff.mp (hXψ.trans hψR)
  -- but `Ranch.coeff 0 = pat 0 ≠ 0`:
  apply ν.hpat0
  have hc : ν.Ranch.coeff 0 = ν.pat 0 := by
    rw [ν.hRanch, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [Polynomial.coeff_X_pow, Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  rwa [hc] at hR0

/-- The upgraded GR-0 supplier map: `readHyps_of_node` with `hψ0` discharged —
10/13 fields corpus-supplied at a bare node; the residue is `hscale` + the two
frame pins `hσs`/`hσt` (route (a), GR34_DISPOSITION 2026-08-08). -/
theorem readHyps_of_node' (ν : Node p F)
    (hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) :
    ReadHyps ν :=
  readHyps_of_node ν hscale (node_hψ0 ν) hσs hσt

/-! ## 2. The scoping forcing — what `ReadHyps` already pins -/

/-- **`ReadHyps` forces `ν.e = 1`**: `hscale` + `Stage.hwΦ` give `ν.h = ν.e·ν.σ.h`,
and `Node.hcop` (`gcd(ν.e, ν.h) = 1`) then collapses `ν.e` (`gcd(e, e·m) = e`). The
displayed pack is the compiled e = 1 recording perimeter (RG-2), never a steep-read
hypothesis. -/
theorem readHyps_e_eq_one (ν : Node p F) (R : ReadHyps ν) : ν.e = 1 := by
  have hs : (ν.h : ℤ) = (ν.e : ℤ) * (ν.σ.h : ℤ) := by
    rw [R.hscale, ν.σ.hwΦ]
  have hnat : ν.h = ν.e * ν.σ.h := by exact_mod_cast hs
  have hcop := ν.hcop
  rw [hnat, Nat.gcd_eq_left ⟨ν.σ.h, rfl⟩] at hcop
  exact hcop

/-- `ReadHyps` pins the read's slope numerator to the frame's: `ν.h = ν.σ.h`. -/
theorem readHyps_h_eq (ν : Node p F) (R : ReadHyps ν) : ν.h = ν.σ.h := by
  have hs : (ν.h : ℤ) = (ν.e : ℤ) * (ν.σ.h : ℤ) := by
    rw [R.hscale, ν.σ.hwΦ]
  have he1 := readHyps_e_eq_one ν R
  rw [he1] at hs
  exact_mod_cast (by simpa using hs)

/-- `ReadHyps` forces the read's canonical Bézout pair `(s, t) = (1, 0)` (the
`hbezCanon` window at `e = 1`), hence `m̂ = 0`. -/
theorem readHyps_t_eq_zero (ν : Node p F) (R : ReadHyps ν) : ν.t = 0 := by
  have he1 := readHyps_e_eq_one ν R
  have hc := ν.hbezCanon
  rw [he1] at hc
  push_cast at hc
  omega

/-- `ReadHyps` forces the D.8 normalization exponent `m̂ = −t·h·g = 0` (rev 14's "at
`e = 1` the window forces `t = 0`, so `m̂ = 0` BY the convention"). -/
theorem readHyps_mhat_eq_zero (ν : Node p F) (R : ReadHyps ν) : ν.mhat = 0 := by
  rw [Node.mhat, readHyps_t_eq_zero ν R]
  ring

/-! ## 3. The history-level suppliers — `HistoryCoherent` at interior reads -/

/-- **The frame-pair tie at a coherent non-recentering transition**
(`TransitionCoreL.base.child_e/child_h`, the (S-a) two-step keying): the child
frame's stage pair IS the child node's read pair. This is the history-level content
GR-0 pointed at (its slope-law candidate reduces to this through the width chain —
the direct `child_e`/`child_h` route needs no rational arithmetic). -/
theorem frame_pair_of_coherent {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering) :
    (H.nodes[i+1]'hi).σ.e = (H.nodes[i+1]'hi).e ∧
      (H.nodes[i+1]'hi).σ.h = (H.nodes[i+1]'hi).h := by
  obtain ⟨-, -, -, htrans⟩ := hcoh
  obtain ⟨-, hnonrec, -⟩ := htrans i hi
  obtain ⟨-, σV, -, -, hcore⟩ := hnonrec hprev
  exact ⟨hcore.base.child_e, hcore.base.child_h⟩

/-- **The RG-2 recording fence, extracted**: an interior non-recentering read has
`e = 1` (the disclosed definitional scope restriction of the HK-06 wave — the
`ν.e = 1` conjunct of `HistoryCoherent`'s non-recentering leg). -/
theorem node_e_one_of_interior {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hspec : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering) :
    (H.nodes[i]'(by omega)).e = 1 := by
  obtain ⟨-, -, -, htrans⟩ := hcoh
  obtain ⟨-, hnonrec, -⟩ := htrans i hi
  exact (hnonrec hspec).1

/-! ## 3b. The frame-side supplier — the GR-3/GR-4 pins, now `ReadHyps` fields
(route (a), GR34_DISPOSITION 2026-08-08) -/

/-- **The frame level pins at the same interior configuration**: `child_e` + the
read's `e = 1` give `ν.σ.e = 1`, whence `ν.σ.t = 0` (`Stage.he1t`) and `ν.σ.s = 1`
(`Stage.hbez`). These two pins are the EXACT residue of the GR-3/GR-4 statements
(their sum arithmetic reads the slot positions `−σ.t·wPrev(t_κ) + eκ·σ.s` against
the node's `m̂` — see the GR-3 obstruction record). Since route (a) they are
`ReadHyps` FIELDS (`hσs`/`hσt`), SUPPLIED here at history level; at a bare node
they ride as displayed hypotheses on `readHyps_of_node`. -/
theorem frame_level_of_history {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (he1 : (H.nodes[i+1]'hi).e = 1) :
    (H.nodes[i+1]'hi).σ.s = 1 ∧ (H.nodes[i+1]'hi).σ.t = 0 := by
  have hσe : (H.nodes[i+1]'hi).σ.e = 1 :=
    (frame_pair_of_coherent hcoh hi hprev).1.trans he1
  have hσt : (H.nodes[i+1]'hi).σ.t = 0 := (H.nodes[i+1]'hi).σ.he1t hσe
  refine ⟨?_, hσt⟩
  have hbez := (H.nodes[i+1]'hi).σ.hbez
  rw [hσe, hσt] at hbez
  push_cast at hbez
  omega

/-- **THE `hscale` SUPPLIER** (blueprint §5 GR-0's wave-2 candidate, PROVED): at a
non-root node of a coherent history whose frame-creating transition is
non-recentering, and whose own read is level (`e = 1` — see the two dischargers
below), the full `ReadHyps` pack holds (incl. the route-(a) frame pins, via
`frame_level_of_history`). `hscale` comes from `child_h` + `Stage.hwΦ`;
`hψ0` from `node_hψ0`; the other nine fields from GR-0's supplier map. -/
theorem readHyps_of_history {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (he1 : (H.nodes[i+1]'hi).e = 1) :
    ReadHyps (H.nodes[i+1]'hi) := by
  have hlv := frame_level_of_history hcoh hi hprev he1
  refine readHyps_of_node' _ ?_ hlv.1 hlv.2
  rw [he1, (H.nodes[i+1]'hi).σ.hwΦ, (frame_pair_of_coherent hcoh hi hprev).2]
  push_cast
  ring

/-- `readHyps_of_history` with the `e = 1` leg discharged by the RG-2 fence: the
INTERIOR (successor-having) non-recentering read. -/
theorem readHyps_of_history_interior {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi2 : i + 1 + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'(by omega)).species ≠ ReadSpecies.recentering) :
    ReadHyps (H.nodes[i+1]'(by omega)) :=
  readHyps_of_history hcoh (by omega) hprev
    (node_e_one_of_interior hcoh hi2 hspec)

/-- `readHyps_of_history` with the `e = 1` leg discharged by the recentering species
law (`Node.hspecRec`): a recentering read anywhere after a non-recentering landing —
successor NOT required (terminal recenterings included). -/
theorem readHyps_of_history_rec {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'hi).species = ReadSpecies.recentering) :
    ReadHyps (H.nodes[i+1]'hi) :=
  readHyps_of_history hcoh hi hprev ((H.nodes[i+1]'hi).hspecRec hspec).1

end LeanUrat.B2D

#print axioms LeanUrat.B2D.node_hψ0
#print axioms LeanUrat.B2D.readHyps_e_eq_one
#print axioms LeanUrat.B2D.readHyps_of_history
#print axioms LeanUrat.B2D.readHyps_of_history_interior
#print axioms LeanUrat.B2D.frame_level_of_history
