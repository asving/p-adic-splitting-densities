/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B11
import Uniformity.ChapB.B20
import Uniformity.ChapC.C01
import Uniformity.ChapC.C03
import Uniformity.ChapC.C06
import Uniformity.ChapC.C07
import Uniformity.ChapC.C09
import Uniformity.ChapC.C11
import Uniformity.ChapC.C25
import Uniformity.ChapC.C29
import Uniformity.ChapC.C35
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C42
import Uniformity.ChapC.C43
import Uniformity.ChapC.C44
import Uniformity.ChapC.C51
import Uniformity.ChapC.C56a
import Uniformity.ChapF.GateFields
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C141defs — transcription batch DT2: definitional twins, no proof content

**Transcription unit DT2**, the second batch of small signed DEFINITIONAL declarations from
`leanspec/Leanspec/ChapC.lean` (defs carrying no proof content — no axioms, no theorems),
landed here as BYTE-FAITHFUL twins of the signed leanspec text. Deviations: none, beyond the
namespace/import adjustments the parent `CLAUDE.md` statement-fence explicitly allows, and (for
`f9mul`) reusing the already-landed `Uniformity.Density.Weld.F9` carrier instead of
re-declaring leanspec's local `abbrev F9` (the census already classifies that abbrev as
`CARRIER`, satisfied by `leanfinal/Uniformity/ChapF/GateFields.lean:108`).

## Landed in this file (per-item leanspec ranges; see `runs/wave-b/verdict_DT2.md` for the
full curation record)

* `complementConst` — `ChapC.lean:1608–1612` (NODE C.36(a), the complement constant `c_g`).
* `γg` — `ChapC.lean:1694–1697` (NODE C.39, the complement's own `K₂`-residue read).
* `pinHeight` — `ChapC.lean:1699–1703` (NODE C.39, the PIN height at the side's start index).
* `refineDom`, `refineCod` — `ChapC.lean:2161–2168` / `:2170–2176` (NODE C.57, R2b's domain and
  codomain coefficient-box strata).
* `FgmnResidualMulStatement` — `ChapC.lean:3991–4046` (NODE C.66's A-C.6 REDRAFT: the named
  `[cite:FGMN]` Prop that superseded the machine-refuted A-C.1 draft. Landed here as a bare
  `Prop`-valued def, universe-polymorphic exactly as signed; it is NOT wired to any axiom — the
  already-landed `Uniformity.ChapC.C66.fgmn_residual_mul` independently carries an
  inlined copy of the same statement at a fixed `Type`, per its own module's design choice. The
  two coexist; landing this name closes the one remaining UNLANDED def-kind node of C.66's
  drafting history without creating or strengthening any axiom.)
* The `§13` numeric-gate arithmetic mirrors (no signature, defect D1 — audit-script defs, not
  blueprint declarations): `slotIdxN`, `twistExpN`, `slotWindowN` (`:4062–4068`); `shiftN`,
  `cocycleN` (`:4070–4072`, leanspec's own top-level mirrors, carried because `c28_grid` needs
  them — `Uniformity.ChapC.C28`'s same-named mirrors are `private`, hence inaccessible here);
  `c16_grid` (`:4074–4087`); `c18_grid` (`:4091–4102`); `f9mul` (`:4119`); `c28_grid`
  (`:4139–4153`);
  `c30_grid` (`:4163–4175`); `c31_floor_grid` (`:4179–4192`); `jumpDropAsSigned`,
  `jumpDropCounterCount`, `jumpDropRepaired`, `jumpDropRepairedCount` (`:4196–4237`);
  `c32_check` (`:4241–4247`); `c50_grid` (`:4252–4267`); `clipDivergesAt` (`:4285–4290`);
  `c55_grid` (`:4307–4320`); `c10_grid` (`:4339–4352`); `v2` (`:4381–4383`); `isPure2`
  (`:4392–4398`);
  `vtheta`, `vxi`, `vzeta`, `vPhi1_at_xi`, `vPhi1_at_zeta`, `vPhi2_at_theta`, `vPhi2_at_zeta`
  (`:4405–4411`); `c16_unique_grid` (`:4433–4442`); `c18_iff_grid` (`:4446–4455`); `c41_grid`
  (`:4459–4472`); `c41_nsmul_grid` (`:4476–4487`); `gateC_q3_budget_w0`, `gateC_q3_budget_w5`,
  `gateC_q3_htSpot_atN6` (`:4514–4517`, the `q = 3` companions of C123's already-landed `q = 2`
  rows). None of the leanspec `#guard`/`#eval` self-test lines are carried, per the DT1
  precedent (`C140defs.lean`'s docstring: "the later `#eval`/`#guard` rows are NOT part of this
  batch").

**Not landed in this file** — see `runs/wave-b/verdict_DT2.md` for the full per-name
disposition: `DescentStep`/`NS7TerminationStatement` (already adjudicated SKIPPED at DT1 —
machine-refuted A-C.1 drafts, struck in leanspec itself) and `GENTOW5W` (FGMNCalculus-adjacent:
C130pk's own docstring lists "any `FGMNCalculus`-conditional §10 theorem — the GENTOW2 supply
layer stays in leanspec until its own transcription nodes" as deliberately NOT there).

## Status

Sorry-free, axiom-free, `unsafe`-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Uniformity.Density.Weld IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### NODE C.36(a) [def] — `complementConst` [signed: A-C.1] -/

/-- `c_g` — the complement constant, in `dv₂`-units: the level support value of
`g = f /ₘ f_S` at the datum's side (`EFF.HE6R1.13`'s `c_g`, ℕ-cleared; finite under C.36). -/
noncomputable def complementConst {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ :=
  (dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ).toNat

/-! ### NODE C.39 [def] — `γg`, the per-side scalar's own residue read [signed: A-C.1] -/

/-- `γ_g` — the complement's own `K₂`-residue read (a `K₂^×` unit under C.36). -/
noncomputable def γg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L (f /ₘ blockFactor L f)

/-- the PIN height at the side's starting index (PE3 F-1's integer; GC-1 discipline at
level 2). -/
noncomputable def pinHeight {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne)).toNat

/-! ### NODE C.57 [def] — R2b's domain/codomain coefficient-box strata [signed: A-C.1;
`DOM_N`/`COD_N` as the named strata — R2b's completed inventory] -/

def refineDom {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∃ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1).Nonempty,
      dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1 hne
        = (Polynomial.X - Polynomial.C s) ^ μ₂}

def refineCod {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∀ j < μ₂, (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) (monicPoly a) j}

/-! ### NODE C.66 [cite:FGMN] — the A-C.6 REDRAFT statement, `FgmnResidualMulStatement`
[signed: A-C.6; on signature this is what `axiom fgmn_residual_mul` becomes — landed here as
a bare Prop-valued def, universe-polymorphic exactly as signed, wired to no axiom] -/

-- the binders `hπ`/`hg`/`hg'`/`hℓ`/`hcop`/`hfloor`/`hdg`/`hdg'`/`hpos`/`hpos'`/`hpg`/`hpg'`
-- quote the source's own hypothesis list verbatim (per the module docstring's dictionary);
-- each is threaded but not referenced in the conclusion body, exactly as signed — the same
-- situation as `ClassSizeSupplyData` in `C140defs.lean` (C35.lean/C97.lean precedent).
set_option linter.unusedVariables false in
/-- **REDRAFT A-C.6.** NODE C.66 `[cite:FGMN]`, residual multiplicativity at the
`dv`-carrier. [FGMN] Thm 2.8 + Cor 4.9(3) + Cor 4.12(3), J. Algebra 427 (2015) 30–75,
DOI 10.1016/j.jalgebra.2014.12.022. SCOPE FENCE: exactly the multiplicativity clause Step II
of `LEMMA GENTOW-6.1` consumes — never the full FGMN machinery, never `w`'s closed form. -/
def FgmnResidualMulStatement.{v} : Prop :=
  ∀ {O : Type v} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ)
    (hne : (dvSideSet F g u ℓ).Nonempty) (hne' : (dvSideSet F g' u ℓ).Nonempty)
    (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
    {M₀ M₀' M₀'' : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
    (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
    (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
    ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
      dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
        = Polynomial.C c
            * (dvResPoly F H₀ hpin g u ℓ hne M₀ hp * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp')

/-! ### C.16/C.18's numeral mirror generators [no signature, defect D1] -/

def slotIdxN (e₁ h k : ℕ) : ℕ :=
  ((List.range e₁).find? (fun i => (i * h) % e₁ == k % e₁)).getD 0

def twistExpN (e₁ h k : ℕ) : ℕ := (slotIdxN e₁ h 1 * k - slotIdxN e₁ h k) / e₁

def slotWindowN (e₁ f₁ h k : ℕ) : List ℕ :=
  (List.range f₁).filter (fun t => decide ((slotIdxN e₁ h k + e₁ * t) * h ≤ k))

/-- leanspec's own top-level mirror (`ChapC.lean:4070`), carried verbatim because `c28_grid`
needs it: `Uniformity.ChapC.C28`'s same-named mirror is declared `private` there (file-local),
hence inaccessible here — this is a distinct declaration under the same name, not a duplicate
export of C28's. -/
def shiftN (u l m : ℕ) : ℕ := ((List.range l).find? (fun b => (b * u) % l == m % l)).getD 0

/-- leanspec's own top-level mirror (`ChapC.lean:4072`), carried for the same reason as
`shiftN` above. -/
def cocycleN (u l a b : ℕ) : ℕ := (shiftN u l a + shiftN u l b - shiftN u l (a + b)) / l

/-! ### C.16(a) — `slotIdx_spec` + `twistExp_spec`, over every coprime frame with `e₁ ≤ 8`,
`h ≤ 12`, `k ≤ 40`. -/

def c16_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for k in [0:41] do
          let i := slotIdxN e₁ h k
          if !(i < e₁ && (i * h) % e₁ == k % e₁) then ok := false
          if !(slotIdxN e₁ h 1 * k == i + e₁ * twistExpN e₁ h k) then ok := false
  return ok

/-! ### C.18(b) — `slotWindow_full_of_le` over the same box. -/

def c18_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:5] do
      for h in [0:9] do
        if Nat.gcd h e₁ == 1 then
          for k in [0:80] do
            if (e₁ * f₁ - 1) * h ≤ k then
              if (slotWindowN e₁ f₁ h k).length != f₁ then ok := false
  return ok

def f9mul (x y : F9) : F9 := (x.1 * y.1 + 2 * (x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-! ### C.28 — `cocycle_mem` (`ℓ·c₁(a,b) = s(a)+s(b)−s(a+b)` and `c₁ ≤ 1`) over every coprime
`(u, ℓ)` with `ℓ ≤ 9`, `u ≤ 20`, `a, b ≤ 12`. -/

def c28_grid : Bool := Id.run do
  let mut ok := true
  for l in [1:10] do
    for u in [0:21] do
      if Nat.gcd u l == 1 then
        for a in [0:13] do
          for b in [0:13] do
            let c := cocycleN u l a b
            if !(l * c == shiftN u l a + shiftN u l b - shiftN u l (a + b)) then ok := false
            if !(c ≤ 1) then ok := false
  return ok

/-! ### C.30 — the descent trichotomy, decided over `mr, ℓ, dr ≤ 8`. -/

def c30_grid : Bool := Id.run do
  let mut ok := true
  for mr in [1:9] do
    for l in [1:9] do
      for dr in [1:9] do
        let c1 := mr == 1
        let c2 := mr ≥ 2 && l == 1 && dr == 1
        let c3 := mr ≥ 2 && 2 ≤ l * dr
        if !((c1 && !c2 && !c3) || (c2 && !(2 ≤ l*dr) && mr != 1)
              || (c3 && !(l == 1 && dr == 1) && mr != 1)) then ok := false
  return ok

/-! ### C.31 — `jump_floor` and `first_bite` hold on their boxes; `jump_drop` IS FALSE AS
SIGNED (defect D21). -/

def c31_floor_grid : Bool := Id.run do
  let mut ok := true
  for mr in [2:9] do
    for l in [1:7] do
      for dr in [1:7] do
        if 2 ≤ l * dr then
          for L in [0:60] do
            for mu in [0:60] do
              if mr * (l * dr) ≤ L && L ≤ mu then
                if !(4 ≤ L && 4 ≤ mu) then ok := false
  return ok

/-! C.31's third clause exactly as ORIGINALLY signed (pre-A-C.1; the refutation record of D21,
preserved verbatim per the re-sign discipline), as a decidable predicate: all hypotheses true
and the conclusion false. -/
def jumpDropAsSigned (D l dr mu mu2 dfS : ℕ) : Bool :=
  decide (0 < D) && decide (0 < l) && decide (0 < dr) &&
  decide (mu2 * (D * l * dr) = dfS) && decide (dfS ≤ D * (l * (mu / l))) &&
  decide (l * dr * 2 ≤ 2 * mu) && !decide (2 * mu2 ≤ mu)

def jumpDropCounterCount : ℕ := Id.run do
  let mut n := 0
  for D in [1:5] do
    for l in [1:5] do
      for dr in [1:5] do
        for mu in [0:13] do
          for mu2 in [0:13] do
            if jumpDropAsSigned D l dr mu mu2 (mu2 * (D * l * dr)) then n := n + 1
  return n

/-! The repair: replace `hL : ℓ·d_r·2 ≤ 2μ` (which says `ℓ d_r ≤ μ`) by the JUMP hypothesis
`2 ≤ ℓ·d_r` that the sibling `jump_floor` carries and this clause drops. -/
def jumpDropRepaired (D l dr mu mu2 dfS : ℕ) : Bool :=
  decide (0 < D) && decide (0 < l) && decide (0 < dr) && decide (2 ≤ l * dr) &&
  decide (mu2 * (D * l * dr) = dfS) && decide (dfS ≤ D * (l * (mu / l))) &&
  !decide (2 * mu2 ≤ mu)

def jumpDropRepairedCount : ℕ := Id.run do
  let mut n := 0
  for D in [1:6] do
    for l in [1:6] do
      for dr in [1:6] do
        for mu in [0:25] do
          for mu2 in [0:25] do
            if jumpDropRepaired D l dr mu mu2 (mu2 * (D * l * dr)) then n := n + 1
  return n

/-! ### C.32 — `jump_count_bound` on explicit chains, `J ≤ 4`, values `≤ 200`. -/

def c32_check (a : List ℕ) : Bool :=
  let J := a.length - 1
  let floors := a.all (fun x => decide (4 ≤ x))
  let drops := (List.range J).all (fun j => decide (2 * a[j+1]! ≤ a[j]!))
  !(floors && drops) || decide (2 ^ (J + 2) ≤ 2 * a[0]!)

/-! ### C.42 / C.50 — `E₂_gt_xfloor` follows from `TowerDatum.hfloor`, checked on the box
`e₁,f₁,e₂,f₂ ≤ 5`, `h ≤ 5`, `u₂ ≤ 200`. -/

def c50_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:6] do
    for f₁ in [1:6] do
      for h in [0:6] do
        for e₂ in [1:6] do
          for f₂ in [1:6] do
            for u₂ in [0:201] do
              if e₂ * (e₁ * f₁) * h < u₂ then
                let D₂ := (e₁ * f₁) * (e₂ * f₂)
                let E₂ := e₂ * f₂ * u₂
                if !(D₂ * (e₂ * h) < E₂) then ok := false
  return ok

/-- `q`-free, but the two gate primes enter through `E₂ = e₂f₂u₂` at the two witnesses. -/
def clipDivergesAt (floors : List ℕ) (N : ℕ) : Bool :=
  let clipped := (floors.map (fun f => max 0 (N - f))).sum
  let naive := (floors.map (fun f => N - f)).sum   -- ℕ-truncated: agrees with clipped
  let signedNaive : Int := (floors.map (fun f => (N : Int) - (f : Int))).sum
  decide (clipped == naive) && decide ((clipped : Int) != signedNaive)

/-! ### C.55 — the depth-3 floor in cleared form: pins `p_j ≥ (μ₂−j)E₂ + 1` with right endpoint
`(μ₂, 0)` force every two-point slope `u₃/ℓ₃ > E₂`, i.e. `ℓ₃·E₂ < u₃`. Checked directly on the
pin lattice for `μ₂ ≤ 8`, `E₂ ≤ 30`. -/

def c55_grid : Bool := Id.run do
  let mut ok := true
  for μ₂ in [1:9] do
    for E₂ in [1:31] do
      for j in [0:μ₂] do
        -- the two-point slope from `(j, (μ₂−j)E₂+1)` to `(μ₂, 0)`, cleared
        let l₃ := μ₂ - j
        let u₃ := (μ₂ - j) * E₂ + 1
        if !(l₃ * E₂ < u₃) then ok := false
  return ok

/-! ### C.10's dictionary arithmetic (`D″ = D′ℓd_r = (e₁ℓ)(f₁d_r)`, `4 ≤ D″` under the jump)
and C.31's `first_bite`, both decided on their boxes. -/

def c10_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:7] do
      for l in [1:7] do
        for dr in [1:7] do
          if !((e₁ * f₁) * l * dr == (e₁ * l) * (f₁ * dr)) then ok := false
          if 2 ≤ e₁ * f₁ && 2 ≤ l * dr then
            if !(4 ≤ (e₁ * f₁) * l * dr) then ok := false
  return ok

/-! ### C.97's S2 TOWER WITNESS arithmetic: `v2` (the `2`-adic valuation on `ℤ`) and `isPure2`
(the one-sidedness test on `List ℤ` coefficient vectors), the two helpers `Phi2`/`Phi3`'s
purity checks consume (`Phi1`/`Phi2`/`Phi3` themselves are DT1's `C140defs.lean`). -/

def v2 : ℤ → ℕ
  | 0 => 0
  | n => (n.natAbs).factorization 2

/-- `f` is one-sided of slope `v(a₀)/n` at `p = 2`: every support point lies on or above the line
through `(0, v(a₀))` and `(n, 0)`, cleared to `n·v(aᵢ) ≥ v(a₀)·(n − i)`. -/
def isPure2 (f : List ℤ) : Bool :=
  let n := f.length - 1
  let v0 := v2 (f.getD 0 0)
  (f.getD n 0 == 1) && (List.range (n + 1)).all (fun i =>
    if f.getD i 0 == 0 then true else decide (n * v2 (f.getD i 0) ≥ v0 * (n - i)))

def vtheta : ℚ := 1/2
def vxi : ℚ := 1/2
def vzeta : ℚ := 1/2
def vPhi1_at_xi : ℚ := (2 + vxi) / 2            -- Φ′(ξ)² = 4ξ
def vPhi1_at_zeta : ℚ := (2 + vzeta) / 2
def vPhi2_at_theta : ℚ := 2 + vtheta            -- Φ₂(θ) = −4θ
def vPhi2_at_zeta : ℚ := (4 + vPhi1_at_zeta) / 2 -- Φ₂(ζ)² = 16Φ′(ζ)

/-! ### C.16(b), C.18(a), C.41 — the remaining decidable signed statements, grid-verified. -/

def c16_unique_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for k in [0:41] do
          for i in [0:e₁] do
            if (i * h) % e₁ == k % e₁ then
              if i != slotIdxN e₁ h k then ok := false
  return ok

def c18_iff_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:6] do
      for h in [0:9] do
        if Nat.gcd h e₁ == 1 then
          for k in [0:80] do
            let full := (slotWindowN e₁ f₁ h k).length == f₁
            if full != decide ((slotIdxN e₁ h k + e₁ * (f₁ - 1)) * h ≤ k) then ok := false
  return ok

def c41_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for a in [0:25] do
          for b in [0:25] do
            let sa := slotIdxN e₁ h a
            let sb := slotIdxN e₁ h b
            if !(sa + sb == slotIdxN e₁ h (a + b) + e₁ * ((sa + sb) / e₁)) then ok := false
            if !((sa + sb) / e₁ ≤ 1) then ok := false
            if !(twistExpN e₁ h (a + b)
                  == twistExpN e₁ h a + twistExpN e₁ h b + (sa + sb) / e₁) then ok := false
  return ok

def c41_nsmul_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:8] do
    for h in [0:11] do
      if Nat.gcd h e₁ == 1 then
        for f₂ in [1:9] do
          for t in [0:f₂] do
            for u₂ in [0:15] do
              if !(twistExpN e₁ h ((f₂ - t) * u₂)
                    == (f₂ - t) * twistExpN e₁ h u₂
                        + (f₂ - t) * slotIdxN e₁ h u₂ / e₁) then ok := false
  return ok

/-! ### C.124's machine-form expected values (`q = 3`), the companion of C123's already-landed
`q = 2` rows (`gateC_q2_*`, `Uniformity.ChapC.C123`). D15 RESOLVED against `EFF.W12.87`: the
FULL-coefficient reading `htSpot` is the source's; the `q = 3` witness decides. -/

def gateC_q3_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q3_budget_w5 : List ℕ := [6, 4, 2, 0]
def gateC_q3_htSpot_atN6 : ℕ := 2 * 3 ^ 4   -- D15 DECIDED: the full-coefficient reading

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.complementConst
#print axioms Uniformity.Density.Tower.γg
#print axioms Uniformity.Density.Tower.pinHeight
#print axioms Uniformity.Density.Tower.refineDom
#print axioms Uniformity.Density.Tower.refineCod
#print axioms Uniformity.Density.Tower.FgmnResidualMulStatement
#print axioms Uniformity.Density.Tower.slotIdxN
#print axioms Uniformity.Density.Tower.twistExpN
#print axioms Uniformity.Density.Tower.slotWindowN
#print axioms Uniformity.Density.Tower.shiftN
#print axioms Uniformity.Density.Tower.cocycleN
#print axioms Uniformity.Density.Tower.c16_grid
#print axioms Uniformity.Density.Tower.c18_grid
#print axioms Uniformity.Density.Tower.f9mul
#print axioms Uniformity.Density.Tower.c30_grid
#print axioms Uniformity.Density.Tower.c31_floor_grid
#print axioms Uniformity.Density.Tower.jumpDropAsSigned
#print axioms Uniformity.Density.Tower.jumpDropCounterCount
#print axioms Uniformity.Density.Tower.jumpDropRepaired
#print axioms Uniformity.Density.Tower.jumpDropRepairedCount
#print axioms Uniformity.Density.Tower.c32_check
#print axioms Uniformity.Density.Tower.c50_grid
#print axioms Uniformity.Density.Tower.clipDivergesAt
#print axioms Uniformity.Density.Tower.c55_grid
#print axioms Uniformity.Density.Tower.c10_grid
#print axioms Uniformity.Density.Tower.v2
#print axioms Uniformity.Density.Tower.isPure2
#print axioms Uniformity.Density.Tower.vtheta
#print axioms Uniformity.Density.Tower.vxi
#print axioms Uniformity.Density.Tower.vzeta
#print axioms Uniformity.Density.Tower.vPhi1_at_xi
#print axioms Uniformity.Density.Tower.vPhi1_at_zeta
#print axioms Uniformity.Density.Tower.vPhi2_at_theta
#print axioms Uniformity.Density.Tower.vPhi2_at_zeta
#print axioms Uniformity.Density.Tower.c16_unique_grid
#print axioms Uniformity.Density.Tower.c18_iff_grid
#print axioms Uniformity.Density.Tower.c41_grid
#print axioms Uniformity.Density.Tower.c41_nsmul_grid
#print axioms Uniformity.Density.Tower.gateC_q3_budget_w0
#print axioms Uniformity.Density.Tower.gateC_q3_budget_w5
#print axioms Uniformity.Density.Tower.gateC_q3_htSpot_atN6

end AxCheck
