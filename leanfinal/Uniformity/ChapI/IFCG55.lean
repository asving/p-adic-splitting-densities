/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG54
import Uniformity.ChapI.IFCG37
import Uniformity.ChapI.ID12

/-!
# Uniformity.ChapI.IFCG55 — THE SCOREBOARD RECONCILIATION: one master census theorem

**UNIT SCB** (wave C, 2026-08-31).  After the blitz the census front's premises were
scattered across a dozen wrappers (IFCG14 → … → IFCG54), and the per-unit scoreboards
had drifted: DDT's mass-4 row still listed `E1IrrLeafDecision` (RIS's IFCG37 had
PROVED it, Lean-core, but IFCG54 never imported IFCG37), and every post-INS wrapper
still carried the block-bridge premise `hBr` that IFCG32's
`unramifiedBlockBridge_all` closed unconditionally.  This file composes the corpus
maximally and states the surviving premise surface as CHECKED THEOREMS.

## THE RECONCILIATION (charge item 1)

* `IFCG37.e1IrrLeafDecision : IFCG34.E1IrrLeafDecision` (Lean-core, no premises) is
  EXACTLY the `hL` premise of IFCG51's type22/type41 rows and IFCG54's census fronts
  — the composition is a direct application (§1, §2).
* `IFCG32.unramifiedBlockBridge_all` (δ ≥ 1, unconditional) discharges every `hBr`.
* CONSEQUENCE (§1): **MASS 4 RESTS ON `FactorCorrespondenceAt 2` ALONE** —
  `coneRemainderLaw_four_all : FactorCorrespondenceAt 2 → ∀ σ, ConeRemainderLaw 4 σ`
  (every type, not just the five even-ramification rows).

## THE MASTER (charge item 2) — the census scoreboard as ONE checked theorem

`decidedSliceAt_all_of_MASTER` (§4): the all-degree decided slice from EXACTLY

| # | master premise | scoreboard row |
|---|---|---|
| 1 | `hFC : ∀ D, 2 ≤ D → FactorCorrespondenceAt D` | THE STAGED CITE (owner gate; CTS's package).  `D = 2` alone fires all of mass 4. |
| 2 | `hEis : EisFullSpanRemainderLaw m σ` at composite `m ≥ 6` (witnessed ramified, under the `< m` value laws) | ASM's named remainder (the `h ≥ 2` faces + `deg ψ ≥ 2` residuals) |
| 3 | `hSD : SplitConvolutionDefectLaw e σ`, `e ≥ 5` ram. witnessed (under `< e` laws) | IFCG38's genre |
| 4 | `hPD : PowerConvolutionDefectLaw e σ`, same guards | IFCG44's genre |
| 5 | `hLeaf : LeafSectorLaw e σ`, same guards | the leaf cell count (decisions CLOSED by RIS: `decidedAt_of_spanning_irr`) |

GONE from every earlier wrapper's list: `E1IrrLeafDecision` (RIS, Lean-core),
`UnramifiedBlockBridge` (INS, Lean-core), `PowerFullSpanLaw` (decomposed here through
ASM's `powerFullSpanLaw_of_prime_or_correspondence` — prime masses close outright,
composite masses on rows 1+2 with the divisor-depth supplies wired from the census
recursion itself, §3), ALL `e ≤ 4` remainder laws (closed: e ≤ 3 outright; e = 4 on
row 1 at `D = 2`), the E1/E2 depth-0 and dd recursion families (IFCG36/51/54), and
the unramified laws at every mass (UZL).

## The engine (§3): `coneRemainderLaw_all_of_master`

`ConeRemainderLaw e σ` for EVERY `e ≥ 2` and EVERY σ from the five master premises,
by strong induction on the mass: e = 2 (IFCG25's tooth), e = 3 (CRL), e = 4 (the
even/odd dichotomy: `coneRemainderLaw_four_of_sectors` on the four closed sector
limits vs `coneRemainderLaw_four_of_odd`), e ≥ 5 (unwitnessed → §0's zero law;
unramified → UZL; else the three sector laws, with `PowerFullSpanLaw` fired at prime
mass by DTR and at composite mass by ASM's correspondence family, whose
`ZeroConeClause` divisor-depth supplies are the INDUCTION HYPOTHESIS composed with
`zeroConeClause_of_remainderLaw` — the recursion is well-founded because divisor
depths satisfy `2·D ≤ e`).

## Cross-front (charge item 3): the capstone master

`capstoneHypotheses_of_MASTER` (§5): `CapstoneHypotheses n` — the WHOLE proof's
remaining surface — from {ladder, deepTwist} (ID12's live fronts, byte-copied field
types) + the five census master premises, through ID12's frontier reduction
(consuming the previously-declared allowlisted cite `agnprw_termination`).

## Axiom fence

No new axiom, no sorry, no statement change to any landed file.  §0–§1 and the
engine expect Lean core `{propext, Classical.choice, Quot.sound}` + the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited
through the IFCG26→…→54 chain — never re-consumed); `capstoneHypotheses_of_MASTER`
additionally inherits exactly `agnprw_termination` (ID12).  The C.33 cites must NOT
occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG55

open IsLocalRing Polynomial
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ConeRemainderLaw ZeroConeClause
  coneRemainderCount zeroConeClause_two zeroConeClause_of_remainderLaw)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge coneRemainderLaw_two
  decidedSet_eq_empty_of_unwitnessed decidedSliceAt_all_of_remainder_bridge)
open Uniformity.Density.IFCG26 (coneRemainderLaw_three)
open Uniformity.Density.IFCG31 (mixedType4 ramPairType coneRemainderLaw_four_of_odd)
open Uniformity.Density.IFCG32 (unramifiedBlockBridge_all)
open Uniformity.Density.IFCG33 (coneRemainderLaw_unramified)
open Uniformity.Density.IFCG34 (type22 type41 splitTailType inertTailType
  E1IrrLeafDecision coneRemainderLaw_four_of_sectors)
open Uniformity.Density.IFCG35 (SplitSectorLaw PowerSectorLaw LeafSectorLaw
  coneRemainderLaw_of_sectorLaws)
open Uniformity.Density.IFCG36 (zcURLim_e1SplitDecFam zcURLim_e1IrrDecFam
  zcURLim_e1IrrFam)
open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw splitSectorLaw_of_defectLaw)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw
  powerSectorLaw_of_rebase)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw
  powerFullSpanLaw_of_prime_or_correspondence zcURLim_e1DdDecFam
  coneRemainderLaw_four_type22_of_correspondence
  coneRemainderLaw_four_type41_of_correspondence)
open Uniformity.Density.IFCG54 (zcURLim_e2DecFam_final
  coneRemainderLaw_four_ramPair_of_fc2)

/-! ## §0 — the unwitnessed zero law (the one new mechanism lemma)

The remainder carrier is a subset of the decided set, and an unwitnessed label's
decided set is empty at every level (IFCG25) — so its remainder law holds with
value `0`.  This closes the `∀ τ` quantifier of the divisor-depth `ZeroConeClause`
supplies (ASM's `hZC` shape ranges over ALL types of degree `D`, witnessed or not). -/

/-- **The unwitnessed remainder law**: `ConeRemainderLaw m σ` (value `0`) for every
unwitnessed `σ` — the remainder carrier sits inside the (empty) decided set. -/
theorem coneRemainderLaw_of_unwitnessed {m : ℕ} {σ : FactorizationType}
    (h : ¬ Witnessed m σ) : ConeRemainderLaw m σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  show (0 : ℝ) = (coneRemainderCount O m σ M : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  have hzero : coneRemainderCount O m σ M = 0 := by
    unfold coneRemainderCount
    rw [decidedSet_eq_empty_of_unwitnessed (O := O) h (M + m)]
    simp
  rw [hzero]
  simp

/-! ## §1 — THE RECONCILIATION: RIS's fire composed into the mass-4 rows

DDT's scoreboard listed mass 4 = {`FactorCorrespondenceAt 2`, `E1IrrLeafDecision`};
RIS's IFCG37 proved `e1IrrLeafDecision : IFCG34.E1IrrLeafDecision` (Lean-core, no
premises) — the exact Prop the rows consume.  IFCG54 never imported IFCG37 (its
imports are IFCG53/IFCG51/IFCG1), so the composition simply had no shared module
until now.  There is no namespace or statement mismatch. -/

/-- ★★★ **The `{(2,2)}` mass-4 row on `FactorCorrespondenceAt 2` ALONE** — IFCG51's
row with the leaf premise discharged by RIS (`IFCG37.e1IrrLeafDecision`) and the
irreducible-box limit by IFCG36 (`zcURLim_e1IrrFam`, unconditional). -/
theorem coneRemainderLaw_four_type22 (hFC2 : FactorCorrespondenceAt 2) :
    ConeRemainderLaw 4 type22 :=
  coneRemainderLaw_four_type22_of_correspondence
    Uniformity.Density.IFCG37.e1IrrLeafDecision hFC2 zcURLim_e1IrrFam

/-- ★★★ **The `{(4,1)}` mass-4 row on `FactorCorrespondenceAt 2` ALONE** — the
census's deep-wild row, its leaf premise discharged by RIS. -/
theorem coneRemainderLaw_four_type41 (hFC2 : FactorCorrespondenceAt 2) :
    ConeRemainderLaw 4 type41 :=
  coneRemainderLaw_four_type41_of_correspondence
    Uniformity.Density.IFCG37.e1IrrLeafDecision hFC2

/-- ★★★ **MASS 4 RESTS ON `FactorCorrespondenceAt 2` ALONE — every type at once**:
even-member types by the forced sector partition (all four sector limits are now
closed: split/irr by IFCG36 (+RIS's leaf), dd by IFCG51 on FC 2, E2 by IFCG54
unconditionally); no-even-member types by IFCG31's odd law (which also covers the
mixed, unramified, and unwitnessed cases at mass 4). -/
theorem coneRemainderLaw_four_all (hFC2 : FactorCorrespondenceAt 2)
    (σ : FactorizationType) : ConeRemainderLaw 4 σ := by
  by_cases heven : ∃ p ∈ σ.data, 2 ∣ p.1
  · have hσm : σ ≠ mixedType4 := by
      rintro rfl
      obtain ⟨p, hp, h2⟩ := heven
      have hmem : p = (1, 1) ∨ p = (3, 1) := by
        have hp' : p ∈ ({(1, 1), (3, 1)} : Multiset (ℕ × ℕ)) := hp
        simpa using hp'
      rcases hmem with rfl | rfl <;> omega
    exact coneRemainderLaw_four_of_sectors hσm (zcURLim_e1SplitDecFam σ)
      (zcURLim_e1IrrDecFam Uniformity.Density.IFCG37.e1IrrLeafDecision σ)
      (zcURLim_e1DdDecFam hFC2 σ) (zcURLim_e2DecFam_final σ)
  · push Not at heven
    exact coneRemainderLaw_four_of_odd heven

/-! ## §2 — DDT's census front, reconciled

IFCG54's `decidedSliceAt_all_of_fc2` with the leaf premise fired by RIS and the
block bridges by INS — the E2-free front now rests on {`FactorCorrespondenceAt 2`,
the generic `e ≥ 5` ramified laws}.  (Subsumed by §4's master, which also
decomposes the `e ≥ 5` family; recorded here as the direct composition.) -/

/-- ★★ **DDT's front, two premises gone**: `E1IrrLeafDecision` (RIS, Lean-core) and
`UnramifiedBlockBridge` (INS, Lean-core) are DISCHARGED; the slice rests on
{`FactorCorrespondenceAt 2`, the `e ≥ 5` ramified remainder laws}. -/
theorem decidedSliceAt_all_of_fc2_final (hFC : FactorCorrespondenceAt 2)
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG54.decidedSliceAt_all_of_fc2
    Uniformity.Density.IFCG37.e1IrrLeafDecision hFC hR
    (fun δ e hδ _ => unramifiedBlockBridge_all (by omega : 1 ≤ δ) e)

/-! ## §3 — THE ENGINE: every remainder law from the five master premises

Strong induction on the mass.  `e ≤ 3` and the unramified/unwitnessed/odd-mass-4
sectors are closed outright; mass 4 fires on `hFC 2` (§1); at `e ≥ 5` the three
sector laws assemble, with `PowerFullSpanLaw` fired at prime mass by DTR's
unconditional law and at composite mass (`≥ 6`) by ASM's correspondence family —
whose divisor-depth `DecidedValueLaw` supplies are the census induction hypothesis
`hsm` verbatim, and whose `ZeroConeClause` supplies are THE ENGINE ITSELF at the
strictly smaller mass `D` (`2·D ≤ e`), composed with
`zeroConeClause_of_remainderLaw` (`D = 2` closes on `zeroConeClause_two`). -/

/-- ★★★ **The engine**: `ConeRemainderLaw e σ` for EVERY `e ≥ 2` and EVERY `σ`
(witnessed or not, ramified or not) from the five master premises, under the census
recursion's own smaller-mass value laws. -/
theorem coneRemainderLaw_all_of_master
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ) :
    ∀ e : ℕ, 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → ConeRemainderLaw e σ := by
  have main : ∀ N e : ℕ, e ≤ N → 2 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → ConeRemainderLaw e σ := by
    intro N
    induction N with
    | zero => intro e heN he2 hsm σ hσ; omega
    | succ n IH =>
      intro e heN he2 hsm σ hσ
      rcases Nat.lt_or_ge e 5 with hlt | hge
      · -- e ∈ {2, 3, 4}: closed outright (mass 4 on `hFC 2`)
        interval_cases e
        · exact coneRemainderLaw_two σ
        · exact coneRemainderLaw_three σ
        · exact coneRemainderLaw_four_all (hFC 2 le_rfl) σ
      · -- e ≥ 5
        by_cases hwit : Witnessed e σ
        · by_cases hram : ∃ p ∈ σ.data, p.1 ≠ 1
          · -- witnessed ramified: the three sector laws assemble
            have he0 : 0 < e := by omega
            have hS : SplitSectorLaw e σ :=
              splitSectorLaw_of_defectLaw he0 σ hsm (hSD e hge hsm σ hσ hwit hram)
            have hPF : PowerFullSpanLaw e σ := by
              by_cases hp : e.Prime
              · exact powerFullSpanLaw_of_prime_or_correspondence σ (Or.inl hp)
              · refine powerFullSpanLaw_of_prime_or_correspondence σ
                  (Or.inr ⟨fun D _ h2D _ => hFC D h2D, ?_, ?_, ?_⟩)
                · -- the divisor-depth value laws: the census induction hypothesis
                  intro D _ h2D h2Dm τ hτ
                  exact hsm D (by omega) τ hτ
                · -- the divisor-depth zero-cone clauses: the engine, recursively
                  intro D _ h2D h2Dm τ hτ
                  rcases Nat.lt_or_ge D 3 with hD2 | hD3
                  · have hD : D = 2 := by omega
                    subst hD
                    exact zeroConeClause_two τ
                  · refine zeroConeClause_of_remainderLaw (by omega) τ ?_
                    exact IH D (by omega) (by omega)
                      (fun k hk σ'' h'' => hsm k (by omega) σ'' h'') τ hτ
                · -- the named Eisenstein-frame remainder at composite mass ≥ 6
                  have h5ne : e ≠ 5 := fun h => hp (h ▸ (by norm_num : Nat.Prime 5))
                  exact hEis e (by omega) hp hsm σ hσ hwit hram
            have hP : PowerSectorLaw e σ :=
              powerSectorLaw_of_rebase he0 σ hsm (hPD e hge hsm σ hσ hwit hram) hPF
            exact coneRemainderLaw_of_sectorLaws he0 σ hS hP
              (hLeaf e hge hsm σ hσ hwit hram)
          · -- unramified: UZL's zero law, every mass
            push Not at hram
            exact coneRemainderLaw_unramified e hram
        · -- unwitnessed: §0's zero law
          exact coneRemainderLaw_of_unwitnessed hwit
  exact fun e he2 hsm σ hσ => main e e le_rfl he2 hsm σ hσ

/-! ## §4 — ★★★ THE MASTER CENSUS THEOREM -/

/-- ★★★ **THE CENSUS SCOREBOARD AS ONE CHECKED THEOREM**: the all-degree decided
slice from EXACTLY the five surviving premises —

1. `hFC` — `FactorCorrespondenceAt D` for every `D ≥ 2` (THE STAGED CITE, owner
   gate; `D = 2` alone fires all of mass 4);
2. `hEis` — `EisFullSpanRemainderLaw m σ` at composite `m ≥ 6` (witnessed ramified,
   under the `< m` value laws);
3. `hSD` — `SplitConvolutionDefectLaw e σ` at `e ≥ 5` (same guards);
4. `hPD` — `PowerConvolutionDefectLaw e σ` at `e ≥ 5` (same guards);
5. `hLeaf` — `LeafSectorLaw e σ` at `e ≥ 5` (same guards).

Everything else on any earlier wrapper's list is DISCHARGED inside: the leaf
decision (RIS), the block bridges (INS), the full-span laws (ASM + the engine's
recursion), the `e ≤ 4` remainder laws, the depth-0/dd/E2 recursion families, and
the unramified/unwitnessed sectors. -/
theorem decidedSliceAt_all_of_MASTER
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_remainder_bridge
    (fun e he2 hsm σ hσ _ =>
      coneRemainderLaw_all_of_master hFC hEis hSD hPD hLeaf e he2 hsm σ hσ)
    (fun δ e hδ _ => unramifiedBlockBridge_all (by omega : 1 ≤ δ) e)

/-! ## §5 — the cross-front capstone master

ID12's frontier reduction (`capstoneHypotheses_of_three`: `CapstoneHypotheses n`
from exactly {ladder, deepTwist, a0}) composed with §4's census master on the `a0`
leg.  The `hladder`/`hdeepTwist` hypothesis types are the capstone's field types,
byte-copied from `I10_I15_I18.lean` via ID12.  Footprint: §4's + the
previously-declared allowlisted cite `agnprw_termination` (through ID12's
`ns7Termination_of_cite`).  NOTE ID12's honesty frame applies verbatim: the three
I-D12 fields are supplied AS SIGNED (`True`-bodied at HEAD) — this statement's
conditionality is exactly the SIGNED capstone's. -/

universe uW uG uKt uL

/-- ★★★ **THE WHOLE PROOF'S REMAINING SURFACE, one Lean statement**:
`CapstoneHypotheses n` from {the two live structural fronts (ladder, deepTwist)} +
{the five census master premises (§4)}. -/
theorem capstoneHypotheses_of_MASTER (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.ID12.capstoneHypotheses_of_three n hladder hdeepTwist
    (decidedSliceAt_all_of_MASTER hFC hEis hSD hPD hLeaf n)

end Uniformity.Density.IFCG55

end

/-! ## AXCHECK FOOTER — `coneRemainderLaw_of_unwitnessed` expects pure Lean core
`{propext, Classical.choice, Quot.sound}`; the reconciliation fires, the engine, and
the census master expect Lean core PLUS exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through the
IFCG26→…→54 chain — never re-consumed); the capstone master additionally inherits
exactly the previously-declared allowlisted cite `agnprw_termination` (ID12's
`ns7Termination_of_cite`).  The C.33 cites must NOT occur. -/

#print axioms Uniformity.Density.IFCG55.coneRemainderLaw_of_unwitnessed
#print axioms Uniformity.Density.IFCG55.coneRemainderLaw_four_type22
#print axioms Uniformity.Density.IFCG55.coneRemainderLaw_four_type41
#print axioms Uniformity.Density.IFCG55.coneRemainderLaw_four_all
#print axioms Uniformity.Density.IFCG55.decidedSliceAt_all_of_fc2_final
#print axioms Uniformity.Density.IFCG55.coneRemainderLaw_all_of_master
#print axioms Uniformity.Density.IFCG55.decidedSliceAt_all_of_MASTER
#print axioms Uniformity.Density.IFCG55.capstoneHypotheses_of_MASTER
