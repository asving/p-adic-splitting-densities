/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C34 — the residual dissection at the level polygon (PARTIAL landing)

**Chapter C, NODE C.34** [theorem] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5). ENV-C2. One signed declaration:
`exists_dv_residual_dissection`, signed at the consumed `(λ, r)`-block clause (the
"in particular" of the blueprint STATEMENT — what C.35/C.36/C.61 read); the general
coprime-prime-power refinement is proof content (B.48's route), not a second public
statement. Statement transcribed byte-exact from `leanspec/Leanspec/ChapC.lean`
(A-C.1 §5 block, byte-frozen there).

## MANDATORY vacuity audit (A-C.7 registry, five instances) — VERDICT: no instance

Audited against the five-instance registry (C.111 `hnode` unpinned carrier; C.94
self-loop; C.113 unconditional `hne`; C.118 clause-1 one-sided `≠ ⊤` guard; C.118
clause-2 unguarded consulted side data), plus A-C.8.4's extra low-degree-purity row:

* **`L : LevelDatum`** — the label is fenced at the source: `hℓ : 0 < ℓ`, `hcop`, the
  floor `hκ`, and `r` monic IRREDUCIBLE with `0 < natDegree` and `coeff 0 ≠ 0` (C.09).
  No unit-`r` stratum (on which `hdvd` would be unconditional and the complement clause
  unsatisfiable) and no `ℓ = 0` stratum (on which `0 • ⊤ = 0` would let ⊤-height
  abscissae attain the support) exists.
* **`hpure : IsDvPure F g L.u L.ℓ`** — the KNOWN C.66 low-degree collapse
  (`0 < deg g < D′` makes the two conjuncts coincide at abscissa `0`) is fenced HERE by
  `hdvd`: on that stratum the side is the single point `{0}` (`dvSideDeg = 0`), so
  `dvResPoly` is the constant `C (read at the pinned height)`, nonzero by C.26's
  pinned-read law (`natDegree_dvResPoly`, clause (iii): `coeff 0 ≠ 0`), and the
  nonconstant irreducible `L.r` divides no nonzero constant of the stage-field
  polynomial ring. `hdvd` is UNSATISFIABLE on the degenerate stratum — the guard binds.
  (This fence is a machine-checkable consequence of C.26; it lands as a lemma in this
  unit's leg 2.)
* **`hne : (dvSideSet F g L.u L.ℓ).Nonempty`** — C.113-SHAPE NOTE, benign: for monic
  `g` under `L.hℓ : 0 < ℓ` this is always inhabited (some `dev` block of a nonzero
  polynomial is nonzero, its `stageHeight` is finite, the finite-range `inf` is
  attained, and `0 < ℓ` blocks the `0 • ⊤ = 0` escape), so `hne` carries no fence
  content — but it is a dependent WITNESS binder (needed to state `dvSideMin`/
  `dvResPoly`), C.25's plumbing pattern, not a guard. The content guards are
  `hpure`/`hdvd`.
* **`{M₀} (hp : dvHgt … = (M₀ : ℕ∞))`** — the GC-1 numeral pin (C.25's `hpin₂`
  pattern): side members have finite height BY `DvOnSide`'s second conjunct (the
  finiteness is carried positively in the side-set definition, C.07), so `M₀` always
  exists and is unique. A pin, not a guard; the ⊤-height stratum is excluded one level
  earlier, positively — NOT by a C.118-style one-sided `≠ ⊤ →` implication. No such
  implication-guard occurs anywhere in the statement.
* **The complement `∀ (hne') (M₀') (hp'), ¬ L.r ∣ dvResPoly … g' …` (and its twin in
  the uniqueness clause)** — the C.118-pattern question is whether a degenerate
  competitor `g''` can satisfy this VACUOUSLY (empty quantification domain) and defeat
  uniqueness. It cannot: `g''` is constrained monic, and for monic `g''` under
  `L.hℓ > 0` the domain is never empty (same argument as `hne` above — the side set is
  nonempty and its min has finite height, so `(hne', M₀', hp')` always exists). The
  ∀-form over the complement's OWN pin witnesses is the blueprint's dependent-plumbing
  resolution, and it quantifies over a provably nonempty domain.
* **C.111 shape** — no unpinned carrier: `fS`, `g'` are tied to `g` by the product
  equation, `HasLabel`, monicity, and the complement clause; `HasLabel`'s internal
  existentials are pinned to `fS`'s own side read (C.29).
* **C.94 shape** — no relation/history is quantified; `(fS', g'') = (fS, g')` in the
  uniqueness clause is a consistency instance, not a collapse.

One SEAM (not a vacuity defect, recorded per the blueprint's C.39 note): the blueprint
STATEMENT text reads "up to the C.39-class unit scalar", while the signed Lean clause
uses `HasLabel` (C.29), whose residual clause is the EXACT power `dvResPoly … = L.r ^ m`.
The A-C.1 signature resolved the scalar to the exact-power normal form; discharging it
is part of the proof obligation (C.26's leading-read control), not a statement defect.

## ⚠ PARTIAL LANDING — the signed theorem is ROUTE-BLOCKED

**NOT landed — `exists_dv_residual_dissection`.** Its A-C.20 degree-pinned signed statement
remains an axiom in `leanspec/Leanspec/ChapC.lean`; only the conditional packaging twin is
proved here.  The pre-A-C.20 form was compiled at commits `cdf53b30`/`e93bb724`; the
obstruction record is **`C34_BLOCKED_2026-08-18.md`** (this directory) with
the two frontier goals quoted verbatim: the signed route is B.48's graded-coprime lift
AT THE `dv`-CARRIER, and (i) no dv-level Hensel engine exists at all (the C.33 record's
obstruction 2 — B.44–B.48 are `IsKey`-fenced and `IsKey F.key` is FALSE at `F.h ≥ 1`),
(ii) separation needs the complements' purity (dv-polygon additivity, landed nowhere,
NOT in C.66's signed same-slope clause) and the residue-field coprimality that
`Hensel.monic_factorization_unique` demands is structurally unavailable at `F.h ≥ 1`,
(iii) the owner-signed A-C.8 cite pair (not yet landed) covers C.33's SLOPE dissection
only — its scope fence explicitly excludes this node's residual-primary refinement.
The statement is NOT claimed false — it is the residual-primary refinement of the
theorem of the polygon and is expected true as signed.

**Landed here (sorry-free, Lean-core):** the two machine-checked audit legs
(`stageHeight_ne_top`, `dvSideSet_nonempty`), the `hdvd` fence
(`one_le_dvSideDeg_of_dvd_dvResPoly`, `natDegree_pos_of_one_le_dvSideDeg`), the
constant-complement law (`not_dvd_dvResPoly_of_natDegree_eq_zero`), the `R = r^m`
single-class supply (`hasLabel_self_of_dvResPoly_eq_pow`,
`block_pair_self_of_dvResPoly_eq_pow` — `EFF.HE6.20` item 1), and the frontier
packaging (`exists_dv_residual_dissection_of_frontier`, updated to A-C.20): the FULL signed conclusion
follows from exactly the two frontier Props, so the node's remaining content is
precisely FRONTIER 1 (hex) + FRONTIER 2 (hsep) of the record.

DEPENDS: C.25 · C.26 · C.29 · C.33 · B.44–B.48 (route templates) · landed Hensel
engine (see the record for why the templates cannot be consumed at the `dv`-carrier).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The machine-checked audit legs -/

/-- **Audit leg 1 (machine-checked): a nonzero polynomial has finite stage height.**
`⊤` level heights occur ONLY at zero development blocks (the A-C.7 degenerate stratum):
the leading coefficient of a nonzero block reads at a finite `gaussVal`. -/
theorem KeyFrame.stageHeight_ne_top (F : KeyFrame O π) {A : Polynomial O} (hA : A ≠ 0) :
    F.stageHeight A ≠ ⊤ := by
  have hgv : gaussVal (Polynomial.C (A.coeff A.natDegree)) ≠ ⊤ := fun h =>
    Polynomial.C_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hA) (gaussVal_eq_top_iff.mp h)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hgv
  have hle : F.stageHeight A ≤ ((F.e₁ * m + F.h * A.natDegree : ℕ) : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    refine le_trans (Finset.inf_le (Finset.self_mem_range_succ A.natDegree)) ?_
    rw [← hm, nsmul_eq_mul]
    push_cast
    exact le_refl _
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

/-- **Audit leg 2 (machine-checked): the `dv` side set of a NONZERO polynomial is
nonempty in every positive-denominator direction.** This closes the C.118-pattern escape
route through NODE C.34's complement clause: the `∀ (hne') (M₀') (hp')` quantification
domain never empties on monic competitors (monic ⟹ nonzero), so the complement's
non-divisibility is never vacuously satisfiable. -/
theorem dvSideSet_nonempty (F : KeyFrame O π) {g : Polynomial O} (hg : g ≠ 0)
    (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) : (dvSideSet F g u ℓ).Nonempty := by
  classical
  have hkeydeg : 0 < F.key.natDegree := F.hdeg ▸ Nat.mul_pos F.he₁ F.hf₁
  -- a nonzero block exists within the support range
  have hblock : ∃ j ∈ Finset.range (g.natDegree + 1), dev F.key g j ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hg ?_
    have hrep : ∑ j ∈ Finset.range (g.natDegree + 1), dev F.key g j * F.key ^ j = g :=
      sum_dev_eq F.hmonic hkeydeg g
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hkeydeg))
    rw [← hrep]
    exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]
  obtain ⟨j₀, hj₀mem, hj₀⟩ := hblock
  have hhgt₀ : dvHgt F g j₀ ≠ ⊤ := F.stageHeight_ne_top hj₀
  -- hence the cleared support is finite
  have hfin : dvSupp F g u ℓ ≠ ⊤ := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hhgt₀
    have hle : dvSupp F g u ℓ ≤ ((ℓ * m + u * j₀ : ℕ) : ℕ∞) := by
      simp only [dvSupp]
      refine le_trans (Finset.inf_le hj₀mem) ?_
      rw [← hm, nsmul_eq_mul]
      push_cast
      exact le_refl _
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  -- the inf is attained; the attaining abscissa's height is finite since `0 < ℓ`
  obtain ⟨j₁, hj₁mem, hj₁⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (fun j => ℓ • dvHgt F g j + (u * j : ℕ∞))
  have hside : dvSupp F g u ℓ = ℓ • dvHgt F g j₁ + (u * j₁ : ℕ∞) := hj₁
  have hhgt₁ : dvHgt F g j₁ ≠ ⊤ := by
    intro htop
    apply hfin
    rw [hside, htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hℓ.ne'), top_add]
  refine ⟨j₁, ?_⟩
  show j₁ ∈ Finset.filter (DvOnSide F g u ℓ) (Finset.range (g.natDegree + 1))
  exact Finset.mem_filter.mpr ⟨hj₁mem, hside, hhgt₁⟩

/-! ### The `hdvd` fence and its consumers -/

-- C.26's `le_natDegree_of_mem_dvSideSet` is `private` there; reproved locally.
private theorem mem_dvSideSet_le_natDegree {F : KeyFrame O π} {u ℓ j : ℕ}
    {f : Polynomial O} (hj : j ∈ dvSideSet F f u ℓ) : j ≤ f.natDegree := by
  classical
  have hj' : j ∈ Finset.filter (DvOnSide F f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj').1)

/-- **The audit fence, machine-checked: `hdvd` is unsatisfiable on the degenerate
stratum.** Divisibility by the label's `r` forces a positive residual side degree — in
particular the C.66 low-degree purity collapse (`dvSideDeg = 0`, constant residual)
cannot satisfy NODE C.34's hypothesis pack. Monic-`r` degree arithmetic; NO field
instance on the stage field is consumed. -/
theorem one_le_dvSideDeg_of_dvd_dvResPoly {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) {g : Polynomial O}
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hdvd : L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) :
    1 ≤ dvSideDeg F g L.u L.ℓ hne := by
  obtain ⟨hdeg, h0⟩ := natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne hp
  obtain ⟨c, hc⟩ := hdvd
  have hRne : dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp ≠ 0 := fun h => h0 (by simp [h])
  have hcne : c ≠ 0 := fun h => hRne (by rw [hc, h, mul_zero])
  have hmul : (L.r * c).natDegree = L.r.natDegree + c.natDegree :=
    Polynomial.natDegree_mul' (by
      rw [L.hrmonic.leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hcne)
  calc 1 ≤ L.r.natDegree := L.hrdeg
    _ ≤ L.r.natDegree + c.natDegree := Nat.le_add_right _ _
    _ = (L.r * c).natDegree := hmul.symm
    _ = dvSideDeg F g L.u L.ℓ hne := by rw [← hc, hdeg]

/-- A positive residual side degree forces a positive polynomial degree (`ℓ` fits under
the side's horizontal length). Bookkeeping for `HasLabel`'s `0 < natDegree` clause. -/
theorem natDegree_pos_of_one_le_dvSideDeg {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {g : Polynomial O} (hne : (dvSideSet F g u ℓ).Nonempty)
    (h1 : 1 ≤ dvSideDeg F g u ℓ hne) : 0 < g.natDegree := by
  have hlen : ℓ ≤ dvSideMax F g u ℓ hne - dvSideMin F g u ℓ hne :=
    (Nat.one_le_div_iff hℓ).mp h1
  have hmax : dvSideMax F g u ℓ hne ≤ g.natDegree :=
    mem_dvSideSet_le_natDegree (Finset.max'_mem _ _)
  omega

/-- **The constant-complement law: a degree-zero polynomial's level residual is never
divisible by the label's `r`** (its side is the single abscissa `0`, so the residual is
a nonzero constant, and `L.r` is nonconstant). This is what discharges the complement
clause at `g' = 1` in the `R = r^m` case (`EFF.HE6.20` item 1). -/
theorem not_dvd_dvResPoly_of_natDegree_eq_zero {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) {g' : Polynomial O}
    (hdeg0 : g'.natDegree = 0)
    (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) {M₀' : ℕ}
    (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)) :
    ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp' := by
  intro hdvd
  have h1 := one_le_dvSideDeg_of_dvd_dvResPoly L hπ hne' hp' hdvd
  have hpos := natDegree_pos_of_one_le_dvSideDeg L.hℓ hne' h1
  omega

/-- **The `R = r^m` self-label (`EFF.HE6.20` item 1: single-label sides need no
dissection).** When the whole residual is a positive power of `L.r`, `g` itself carries
the label — the EXISTENCE frontier's supply in the single-class case, packaged for the
frontier theorem below with `g' = 1`. -/
theorem hasLabel_self_of_dvResPoly_eq_pow {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsDvPure F g L.u L.ℓ)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)) {m : ℕ} (hm : 0 < m)
    (hres : dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r ^ m) :
    HasLabel L g := by
  have hdvd : L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp := by
    rw [hres]
    exact dvd_pow_self _ hm.ne'
  have h1 := one_le_dvSideDeg_of_dvd_dvResPoly L hπ hne hp hdvd
  exact ⟨hg, natDegree_pos_of_one_le_dvSideDeg L.hℓ hne h1, hpure,
    hne, M₀, hp, m, hm, hres⟩

/-- **The single-class case's existence supply, packaged (`EFF.HE6.20` item 1: a
single-label side needs no dissection).** When the whole residual is a positive power
of `L.r`, the trivial pair `(g, 1)` IS a labelled block pair — the packaging theorem's
existence frontier holds with no Hensel content in this case. (The general-`R`
existence and the separation frontier remain open; see `C34_BLOCKED_2026-08-18.md`.) -/
theorem block_pair_self_of_dvResPoly_eq_pow {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsDvPure F g L.u L.ℓ)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)) {m : ℕ} (hm : 0 < m)
    (hres : dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r ^ m) :
    ∃ fS g' : Polynomial O, g = fS * g' ∧ HasLabel L fS ∧ g'.Monic ∧
      ∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp' :=
  ⟨g, 1, (mul_one g).symm, hasLabel_self_of_dvResPoly_eq_pow L hπ hg hpure hne hp hm hres,
    Polynomial.monic_one,
    fun hne' _ hp' =>
      not_dvd_dvResPoly_of_natDegree_eq_zero L hπ Polynomial.natDegree_one hne' hp'⟩

/-! ### Frontier isolation — the packaging -/

/-- **Frontier isolation (C.33's `dvDissection_unique_of_factor_eq` pattern).** NODE
C.34's FULL signed conclusion follows from exactly two frontier facts: EXISTENCE of one
labelled block pair (`hex` — the dv-graded Hensel lift), and SEPARATION (`hsep` — any
two labelled block pairs share the block; the same-slope uniqueness frontier). The
second component of the uniqueness clause is Lean-core monic cancellation, supplied
here. So the entire remaining content of the signed statement is `hex` + `hsep`. -/
theorem exists_dv_residual_dissection_of_frontier {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {g : Polynomial O}
    (hex : ∃ fS g' : Polynomial O, g = fS * g' ∧
      (HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree) ∧ g'.Monic ∧
      ∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp')
    (hsep : ∀ fS g' fS' g'' : Polynomial O, g = fS * g' →
      (HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree) → g'.Monic →
      (∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp') →
      g = fS' * g'' →
      (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → g''.Monic →
      (∀ (hne' : (dvSideSet F g'' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g'' (dvSideMin F g'' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g'' L.u L.ℓ hne' M₀' hp') →
      fS' = fS) :
    ∃ fS g' : Polynomial O, g = fS * g' ∧
      (HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree) ∧ g'.Monic ∧
      (∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp') ∧
      ∀ fS' g'' : Polynomial O, g = fS' * g'' →
        (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → g''.Monic →
        (∀ (hne' : (dvSideSet F g'' L.u L.ℓ).Nonempty) (M₀' : ℕ)
          (hp' : dvHgt F g'' (dvSideMin F g'' L.u L.ℓ hne') = (M₀' : ℕ∞)),
          ¬ L.r ∣ dvResPoly F H₀ hpin g'' L.u L.ℓ hne' M₀' hp') →
        fS' = fS ∧ g'' = g' := by
  obtain ⟨fS, g', hprod, hlab, hmon, hcomp⟩ := hex
  refine ⟨fS, g', hprod, hlab, hmon, hcomp, ?_⟩
  intro fS' g'' hprod' hlab' hmon' hcomp'
  have heq : fS' = fS := hsep fS g' fS' g'' hprod hlab hmon hcomp hprod' hlab' hmon' hcomp'
  exact ⟨heq, mul_left_cancel₀ hlab.1.1.ne_zero ((heq ▸ hprod').symm.trans hprod)⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_ne_top
#print axioms Uniformity.Density.Tower.dvSideSet_nonempty
#print axioms Uniformity.Density.Tower.one_le_dvSideDeg_of_dvd_dvResPoly
#print axioms Uniformity.Density.Tower.natDegree_pos_of_one_le_dvSideDeg
#print axioms Uniformity.Density.Tower.not_dvd_dvResPoly_of_natDegree_eq_zero
#print axioms Uniformity.Density.Tower.hasLabel_self_of_dvResPoly_eq_pow
#print axioms Uniformity.Density.Tower.block_pair_self_of_dvResPoly_eq_pow
#print axioms Uniformity.Density.Tower.exists_dv_residual_dissection_of_frontier

end AxCheck
