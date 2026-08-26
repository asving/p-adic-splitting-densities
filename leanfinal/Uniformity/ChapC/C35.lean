/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C34
import Uniformity.ChapC.C118a

/-!
# Uniformity.ChapC.C35 — the block factor `f_S`, `μ₂`, and the block context

**Chapter C, NODE C.35** [def] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5, ~line 2354). ENV-C2. Four signed declarations,
transcribed from `leanspec/Leanspec/ChapC.lean` (the A-C.1 §5 block, amended by A-C.20):

* `BlockContext L f` — the §5 standing block context: the PEEL-CONVENTION pair
  (`f.Monic`, `Squarefree f`, `¬ F.key ∣ f`) plus a genuine `(λ, r)`-side of `f`'s OWN read
  (nonempty side, positive side degree, `L.r`-divisible residual);
* `blockFactor L f` — the block `f_S`, as the MAXIMAL degree-pinned `(λ, r)`-labelled
  monic divisor of `f` (total: choice; junk `1` when none exists);
* `mult₂ L f = (blockFactor L f).natDegree / L.keyDeg₂` — the corpus's `μ₂ = deg f_S / D″`
  (`EFF.HE6R1.12`);
* `blockFactor_spec` — the companion: under `hctx` the block is genuine, divides `f`, has
  degree EXACTLY `L.keyDeg₂ * mult₂ L f`, and `0 < mult₂ L f`.

## Landing status (honest)

* the three DEFS: **LANDED**, with the A-C.20 degree-pinned selector enacted.
* `blockFactor_spec`: **BLOCKED** — see `C35_BLOCKED_2026-08-20.md`. Its content is reduced,
  here and Lean-core, to the single frontier Prop `BlockFrontier` below, and every other
  ingredient (the level-side endpoint calculus, the `HasLabel` degree law, the D13
  multiplicity tie) is LANDED. The frontier is C.34's existence+uniqueness, which
  `C34_BLOCKED_2026-08-18.md` records as unreachable from the landed engine.

## MANDATORY A-C.7 five-instance vacuity audit — VERDICT: NO INSTANCE, but ONE NEW DEFECT FOUND

Audited before any proof work, against the five-instance registry (C.111 `hnode` unpinned
carrier · C.94 self-loop · C.113 unconditional `hne` · C.118 clause-1 one-sided `≠ ⊤` guard ·
C.118 clause-2 unguarded consulted side data) plus A-C.8.4's low-degree-purity row.

**Per-hypothesis audit of `blockFactor_spec` (the only signed Prop with hypotheses).**

* **`L : LevelDatum F H₀ hpin`** — fenced at the source (C.09): `hℓ : 0 < L.ℓ`, `hcop`, the
  node floor `hκ`, and `L.r` monic IRREDUCIBLE with `0 < L.r.natDegree`, `L.r.coeff 0 ≠ 0`.
  So no `L.ℓ = 0` stratum (on which `0 • ⊤ = 0` would let `⊤`-height abscissae attain the
  support and every `DvOnSide` would degenerate) and no unit-`L.r` stratum (on which
  `L.r ∣ ·` is unconditional and `HasLabel`'s `L.r ^ m` clause carries no information).
* **`hπ : Irreducible π`** — consumed (it is what makes `natDegree_dvResPoly` fire); not inert.
* **`[IsAdicComplete (IsLocalRing.maximalIdeal O) O]`** — a scope hypothesis of the signed
  form, inherited from C.34; it restricts the regime and is not a guard.
* **`hctx : BlockContext L f`** — the risk site, audited clause by clause:
  1. `f.Monic` ⟹ `f ≠ 0`, so C.34's landed `dvSideSet_nonempty` makes EVERY `dvSideSet F f u ℓ`
     nonempty at `0 < ℓ`. The `∃ hne` in `BlockContext` is therefore not an empty-domain
     escape: it can always be inhabited, so it adds no content of its own and the content
     sits entirely in the two clauses under it.
  2. `0 < dvSideDeg F f L.u L.ℓ hne` is a POSITIVE requirement, not an implication guard: it
     is exactly the A-C.8.4 fence that kills the C.66 low-degree purity collapse
     (`0 < deg g < D′`), because a positive side degree forces `dvSideMax ≥ L.ℓ ≥ 1` hence
     (`le_natDegree_div_of_mem_dvSideSet`, landed below) `D′ ≤ f.natDegree`.
  3. `L.r ∣ dvResPoly …` is a POSITIVE divisibility requirement on the residual, and C.34's
     landed `one_le_dvSideDeg_of_dvd_dvResPoly` shows it independently forces
     `1 ≤ dvSideDeg`; the two clauses are mutually consistent, neither is vacuous.
  4. `Squarefree f` and `¬ F.key ∣ f` are the PEEL-CONVENTION pair; `Squarefree f` also
     excludes `f = 1`-style degeneracies only vacuously (`Squarefree 1` holds), which is why
     clauses 2–3 and not squarefreeness carry the nondegeneracy.
  So `BlockContext` is inhabited-in-principle and every clause binds. **No C.113 instance.**
* **the conclusion's shape** — no `≠ ⊤`-guarded implication, no `Visible`-style window, no
  self-referential relation: **no C.118 and no C.94 instance.** `blockFactor` is TOTAL, so
  there is no unpinned carrier field to leave free: **no C.111 instance.**

**NEW DEFECT FOUND (recorded, NOT a vacuity instance) — the D′-divisibility gap in clause 3.**
The audit produced a genuine arithmetic obstruction, worth recording because it is a
statement/body mismatch of exactly the A-C.7 family (a clause that the body does not supply):

> `HasLabel L g` does NOT imply `(F.e₁ * F.f₁) ∣ g.natDegree`, and clause 3
> (`natDegree = L.keyDeg₂ * mult₂`) is FALSE without it.

Witness arithmetic (`D′ = F.e₁ * F.f₁ = 2`, `L.ℓ = 1`, `L.r.natDegree = 1`, so
`L.keyDeg₂ = 2`): a `g` with `g.natDegree = 3` has top `Φ′`-digit index `3 / 2 = 1`, and
`IsDvPure` only asks that the abscissae `0` and `1` be on the side — which is compatible with
`deg (dev F.key g 1) = 1 < D′`. Then `dvSideDeg = 1`, so the residual has degree `1 = m·d_r`
with `m = 1`, so `HasLabel L g` can hold, while `mult₂ = 3 / 2 = 1` and
`L.keyDeg₂ * mult₂ = 2 ≠ 3 = g.natDegree`. Hence clause 3 CANNOT be proved from clauses 1+2:
the exactness comes from C.34's dissection degree law (`DvDissection.hdeg`,
`deg factor = D′·(ℓ·dvSideDeg)`), i.e. from the BLOCK's provenance, not from the maximal
labelled divisor as a bare object. **Consequence for the design:** the frontier below carries
the divisibility rider `(F.e₁ * F.f₁) ∣ fS.natDegree` explicitly; it is discharged, not
assumed away, once the block comes from the dissection. Under the frontier the identification
of `blockFactor L f` with the frontier witness is forced (mutual divisibility of two maximal
labelled divisors + monicity), so the rider transports.
The landed theorem `hasLabel_natDegree_div` isolates exactly what `HasLabel` DOES give:
`g.natDegree / D′ = L.ℓ * (m * L.r.natDegree)` with `0 < m`.

**Refutation attempt on the frontier itself** (standing lesson: a drafted guard is itself a
refutation target). Can `BlockFrontier` be vacuous — i.e. can the `∀ fS'` maximality clause be
empty? No: `HasLabel L 1` is false (`0 < natDegree` fails) but the clause quantifies over ALL
labelled divisors, and `hctx` clause 3 + C.34's `hasLabel_self_of_dvResPoly_eq_pow` produce
labelled divisors on the single-class stratum `dvResPoly f = L.r ^ m` (where `fS = f` itself
qualifies) — so the maximality clause is non-empty on a genuine stratum, and the frontier is
not satisfiable-by-vacuity. Conversely the frontier is not trivially TRUE either: dropping the
divisibility rider makes the packaging theorem UNPROVABLE (the witness arithmetic above).

**DEPENDS.** C.09 (`LevelDatum`, `keyDeg₂`) · C.07/C.08 (side endpoints, `dvSideLen_eq`) ·
C.25/C.26 (`dvResPoly`, `natDegree_dvResPoly`) · C.29 (`IsDvPure`, `HasLabel`) · C.33 · C.34
(imported: `dvSideSet_nonempty`, `hasLabel_self_of_dvResPoly_eq_pow`) · C.118a
(`stageHeight_zero`).

## Status

Sorry-free. Axiom footprint of every declaration below: Lean core
`{propext, Classical.choice, Quot.sound}` (AxCheck footer). No cite is inherited.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations (BYTE-FROZEN from `leanspec/Leanspec/ChapC.lean`) -/

/-- The §5 standing block context on `f` at the datum `L`: the PEEL-CONVENTION pair, a
genuine `(λ, r)`-side of `f`'s own read (nonempty, positive length, `r`-divisible residual). -/
def BlockContext {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Prop :=
  f.Monic ∧ Squarefree f ∧ ¬ F.key ∣ f ∧
  ∃ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
    0 < dvSideDeg F f L.u L.ℓ hne ∧
    L.r ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp

/-- Historical pre-A-C.20 selector, retained only so the machine refutation records can name
the leaky object they refuted.  New consumers use `blockFactor`. -/
noncomputable def blockFactorLeaky {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Polynomial O :=
  open Classical in
  if h : ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS
  then h.choose else 1

/-- Historical multiplicity attached to `blockFactorLeaky`; refutation records only. -/
noncomputable def mult₂Leaky {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ := (blockFactorLeaky L f).natDegree / L.keyDeg₂

/-- Choice pin for the historical leaky selector; used only by pre-A-C.20 refutation rows. -/
theorem blockFactorLeaky_eq_of_frontier {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {f fS : Polynomial O} (hlab : HasLabel L fS)
    (hdvd : fS ∣ f)
    (hmax : ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS) :
    blockFactorLeaky L f = fS := by
  classical
  have h : ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS :=
    ⟨fS, hlab, hdvd, hmax⟩
  have hbf : blockFactorLeaky L f = h.choose := by
    rw [blockFactorLeaky]
    exact dif_pos h
  obtain ⟨hlab', hdvd', hmax'⟩ := h.choose_spec
  rw [hbf]
  exact Polynomial.eq_of_monic_of_associated hlab'.1 hlab.1
    (associated_of_dvd_dvd (hmax _ hlab' hdvd') (hmax' _ hlab hdvd))

/-- [A-C.20, 2026-08-26] `blockFactor L f` — the block `f_S`, selected among the
degree-pinned labels `HasLabel L fS ∧ D′ ∣ deg fS`. -/
noncomputable def blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Polynomial O :=
  open Classical in
  if h : ∃ fS : Polynomial O,
      (HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree) ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O,
        (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ fS
  then h.choose else 1

/-- `μ₂ = deg f_S / D″` (`EFF.HE6R1.12`). -/
noncomputable def mult₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ := (blockFactor L f).natDegree / L.keyDeg₂

/-! ### The level-side endpoint calculus under purity -/

/-- `dvSideSet` membership unfolds to `DvOnSide` (C.07's `filter`).  (C.26 has the same
one-liner as a `private` helper; it is not exported, so it is re-derived here.) -/
theorem dvOnSide_of_mem_dvSideSet {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (h : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  simpa [dvSideSet] using (Finset.mem_filter.mp h).2

/-- **Every side abscissa is a genuine `Φ′`-digit index.**  `j ∈ dvSideSet` forces
`dev F.key f j ≠ 0` (else the height is `⊤`, contradicting `DvOnSide`'s finiteness conjunct),
hence `j * D′ ≤ f.natDegree`, i.e. `j ≤ f.natDegree / D′`.  This is the upper bound that turns
`IsDvPure`'s top-abscissa clause into an EQUALITY for `dvSideMax`. -/
theorem le_natDegree_div_of_mem_dvSideSet (F : KeyFrame O π) {f : Polynomial O} {u ℓ j : ℕ}
    (h : j ∈ dvSideSet F f u ℓ) : j ≤ f.natDegree / (F.e₁ * F.f₁) := by
  have hkeydeg : F.key.natDegree = F.e₁ * F.f₁ := F.hdeg
  have hd : 0 < F.key.natDegree := hkeydeg ▸ Nat.mul_pos F.he₁ F.hf₁
  have hdevne : dev F.key f j ≠ 0 := by
    intro h0
    have hfin : dvHgt F f j ≠ ⊤ := (dvOnSide_of_mem_dvSideSet h).2
    rw [dvHgt, h0, C118a.stageHeight_zero] at hfin
    exact hfin rfl
  have hnlt : ¬ f.natDegree < j * (F.e₁ * F.f₁) := by
    rw [← hkeydeg]
    exact fun hlt => hdevne (dev_eq_zero_of_lt F.hmonic hd f j hlt)
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos F.he₁ F.hf₁)]
  omega

/-- **`dvSideMin = 0` on a pure polygon.** -/
theorem dvSideMin_eq_zero_of_isDvPure {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}
    (hpure : IsDvPure F g u ℓ) (hne : (dvSideSet F g u ℓ).Nonempty) :
    dvSideMin F g u ℓ hne = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ _ hpure.1)

/-- **`dvSideMax = deg g / D′` on a pure polygon.**  `≥` is `IsDvPure`'s second clause; `≤` is
`le_natDegree_div_of_mem_dvSideSet` on every member. -/
theorem dvSideMax_eq_of_isDvPure {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}
    (hpure : IsDvPure F g u ℓ) (hne : (dvSideSet F g u ℓ).Nonempty) :
    dvSideMax F g u ℓ hne = g.natDegree / (F.e₁ * F.f₁) :=
  le_antisymm
    (Finset.max'_le _ _ _ fun _ hj => le_natDegree_div_of_mem_dvSideSet F hj)
    (Finset.le_max' _ _ hpure.2)

/-- **The pure-side degree law.**  On a pure polygon the residual degree reads the top digit
index: `deg g / D′ = ℓ · dvSideDeg`.  (C.08's `dvSideLen_eq` makes the `ℕ`-division exact; the
two endpoints are the two lemmas above.) -/
theorem natDegree_div_eq_of_isDvPure {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsDvPure F g u ℓ)
    (hne : (dvSideSet F g u ℓ).Nonempty) :
    g.natDegree / (F.e₁ * F.f₁) = ℓ * dvSideDeg F g u ℓ hne := by
  have hlen := dvSideLen_eq F hℓ hcop hne
  rw [dvSideLen, dvSideMax_eq_of_isDvPure hpure hne,
    dvSideMin_eq_zero_of_isDvPure hpure hne, Nat.sub_zero] at hlen
  exact hlen

/-! ### The `HasLabel` degree law and the D13 multiplicity tie -/

/-- **What `HasLabel` DOES give (the D13 half that is provable).**  A labelled `g` has
`deg g / D′ = ℓ · (m · d_r)` with `0 < m` the `HasLabel` exponent.  Note the `/ D′`: the
un-divided identity `deg g = D″ · m` needs `D′ ∣ deg g`, which `HasLabel` does NOT supply
(see the header's NEW DEFECT block). -/
theorem hasLabel_natDegree_div {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {g : Polynomial O} (hg : HasLabel L g) :
    ∃ m : ℕ, 0 < m ∧ g.natDegree / (F.e₁ * F.f₁) = L.ℓ * (m * L.r.natDegree) := by
  obtain ⟨-, -, hpure, hne₂, M₀, hpin₂, m, hm, hres⟩ := hg
  refine ⟨m, hm, ?_⟩
  have hdegres : (dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂).natDegree
      = dvSideDeg F g L.u L.ℓ hne₂ :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne₂ hpin₂).1
  rw [hres, L.hrmonic.natDegree_pow] at hdegres
  rw [natDegree_div_eq_of_isDvPure L.hℓ L.hcop hpure hne₂, ← hdegres]

/-- **The D13 tie, in the form clause 3/4 of `blockFactor_spec` needs it.**  Given the
divisibility that the block's PROVENANCE supplies, a labelled `g` has degree exactly
`D″ · (deg g / D″)` with positive quotient — and that quotient IS `HasLabel`'s `m`. -/
theorem hasLabel_natDegree_eq_of_dvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {g : Polynomial O} (hg : HasLabel L g)
    (hdvd : (F.e₁ * F.f₁) ∣ g.natDegree) :
    g.natDegree = L.keyDeg₂ * (g.natDegree / L.keyDeg₂) ∧ 0 < g.natDegree / L.keyDeg₂ := by
  obtain ⟨m, hm, hdiv⟩ := hasLabel_natDegree_div L hπ hg
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hkey : g.natDegree = L.keyDeg₂ * m := by
    have h1 : (F.e₁ * F.f₁) * (g.natDegree / (F.e₁ * F.f₁)) = g.natDegree :=
      Nat.mul_div_cancel' hdvd
    rw [hdiv] at h1
    rw [← h1, LevelDatum.keyDeg₂]
    ring
  have hpos : 0 < L.keyDeg₂ := by
    rw [LevelDatum.keyDeg₂]
    exact Nat.mul_pos (Nat.mul_pos hD L.hℓ) L.hrdeg
  rw [hkey, Nat.mul_div_cancel_left m hpos]
  exact ⟨rfl, hm⟩

/-! ### The frontier, isolated -/

/-- **`BlockFrontier L f` — the exact remaining content of `blockFactor_spec`.**  A maximal
`(λ, r)`-labelled monic divisor of `f` EXISTS and its degree is divisible by `D′` (the
dissection degree law of C.34; see the header's NEW DEFECT block for why the rider cannot be
dropped).  This is C.34's existence+uniqueness at the `(λ, r)`-block, which
`C34_BLOCKED_2026-08-18.md` records as unreachable from the landed engine. -/
def BlockFrontier {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Prop :=
  ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧ (F.e₁ * F.f₁) ∣ fS.natDegree ∧
    ∀ fS' : Polynomial O,
      (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ fS

/-- **The frontier witness IS `blockFactor`.**  Two maximal labelled divisors divide each
other, and both are monic, so they are equal. -/
theorem blockFactor_eq_of_frontier {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {f fS : Polynomial O} (hlab : HasLabel L fS)
    (hdeg : (F.e₁ * F.f₁) ∣ fS.natDegree) (hdvd : fS ∣ f)
    (hmax : ∀ fS' : Polynomial O,
      (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ fS) :
    blockFactor L f = fS := by
  classical
  have h : ∃ fS : Polynomial O,
      (HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree) ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O,
        (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ fS :=
    ⟨fS, ⟨hlab, hdeg⟩, hdvd, hmax⟩
  have hbf : blockFactor L f = h.choose := by
    rw [blockFactor]
    exact dif_pos h
  obtain ⟨⟨hlab', hdeg'⟩, hdvd', hmax'⟩ := h.choose_spec
  rw [hbf]
  exact Polynomial.eq_of_monic_of_associated hlab'.1 hlab.1
    (associated_of_dvd_dvd (hmax _ ⟨hlab', hdeg'⟩ hdvd') (hmax' _ ⟨hlab, hdeg⟩ hdvd))

/-- **NODE C.35's companion, from the frontier alone (Lean-core).**  All four clauses of the
signed `blockFactor_spec` follow from `BlockFrontier L f`; `hctx` is not even consumed by the
reduction (it is what the frontier's PROOF would consume — C.33's dissection at `f` followed by
C.34's `(λ, r)`-block split of the slope-`λ` factor). -/
theorem blockFactor_spec_of_frontier {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hfr : BlockFrontier L f) :
    HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f ∧ 0 < mult₂ L f := by
  obtain ⟨fS, hlab, hdvd, hdeg, hmax⟩ := hfr
  have hbf : blockFactor L f = fS := blockFactor_eq_of_frontier L hlab hdeg hdvd hmax
  have hdeg' : (F.e₁ * F.f₁) ∣ (blockFactor L f).natDegree := by rw [hbf]; exact hdeg
  obtain ⟨hexact, hpos⟩ :=
    hasLabel_natDegree_eq_of_dvd L hπ (g := blockFactor L f) (by rw [hbf]; exact hlab) hdeg'
  exact ⟨by rw [hbf]; exact hlab, by rw [hbf]; exact hdvd, hexact, hpos⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.BlockContext
#print axioms Uniformity.Density.Tower.blockFactorLeaky
#print axioms Uniformity.Density.Tower.mult₂Leaky
#print axioms Uniformity.Density.Tower.blockFactorLeaky_eq_of_frontier
#print axioms Uniformity.Density.Tower.blockFactor
#print axioms Uniformity.Density.Tower.mult₂
#print axioms Uniformity.Density.Tower.dvOnSide_of_mem_dvSideSet
#print axioms Uniformity.Density.Tower.le_natDegree_div_of_mem_dvSideSet
#print axioms Uniformity.Density.Tower.dvSideMin_eq_zero_of_isDvPure
#print axioms Uniformity.Density.Tower.dvSideMax_eq_of_isDvPure
#print axioms Uniformity.Density.Tower.natDegree_div_eq_of_isDvPure
#print axioms Uniformity.Density.Tower.hasLabel_natDegree_div
#print axioms Uniformity.Density.Tower.hasLabel_natDegree_eq_of_dvd
#print axioms Uniformity.Density.Tower.BlockFrontier
#print axioms Uniformity.Density.Tower.blockFactor_eq_of_frontier
#print axioms Uniformity.Density.Tower.blockFactor_spec_of_frontier

end AxCheck
