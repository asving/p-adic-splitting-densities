/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B12
import Uniformity.ChapB.B18
import Uniformity.ChapB.B20
import Uniformity.ChapB.B30
import Uniformity.ChapB.B35a

/-!
# Uniformity.ChapB.B66a — the two canonical order-1 index `Finset`s, with REAL bodies

**Chapter B, NODE B.66a** [RE-PLAN supplier] (`blueprint/CHAP-B_leaf_layer.md` §9, booking at
B.79's ⚠ RE-PLAN item and A-§9.5; signed forms at amendment **A-F.3 item B-D4**), ENV-C in the
blueprint, **ENV-A as elaborated** (neither body consults completeness or residue finiteness).

Four signed declarations: the two `Finset` suppliers `slopeFinset` / `resFactorFinset` — the
index sets B.66's `order1Type` binds over — and their two membership lemmas.

## HEADLINE: the two suppliers land as REAL DEFINITIONS, and this file adds NO axiom

DEFECT **B-D4** signed the two `Finset`s as *"`axiom`-typed opaque constants"* on the ground
that they are "underdetermined (B.42 produces its slope `Finset` existentially; no abscissa
bound is stated)", and instructed the fleet unit to *"choose a definitional body, e.g. a
`Finset.filter` of B.42-step-1's bounded slope grid, and prove the membership lemmas for it"*.

**That is what happened here, and the opaque fallback is NOT used.** The chosen body is not a
grid filter but the canonical one: each supplier is the `Set.Finite.toFinset` of *exactly the
set its own membership lemma describes* (junk value `∅` off the finiteness hypothesis).
Consequences:

* the file's footprint is Lean-core — in particular **the landed B.42 axiom
  `exists_slope_factorization` is NOT consumed** (it is not even imported): the canonical
  characterisation, not the existential dissection, is what pins these two objects;
* the `→` half of each membership lemma holds **with no hypotheses at all** (`mem_slopeFinset_imp`,
  `mem_resFactorFinset_imp`) — off the finiteness regime the supplier is `∅` and the implication
  is vacuous;
* the abscissa bound B-D4 called missing is supplied here as a *theorem*, `slopeSet_finite`
  (see "the bound" below), so no arbitrary grid choice enters the interface.

## STOP-THE-LINE: both signed membership statements are FALSE as signed (missing hypotheses)

A-F.3's B-D4 forms are marked **NOT-CONTRACT** ("the gate's determinate reading of an
under-specified booking; the orchestrator confirms or re-signs them when the B.66a unit fires").
The unit has fired, and the answer is: **as written — quantified over ALL `φ f : Polynomial O`,
with no key/monicity hypothesis — neither statement can be proved for ANY body, because each
asserts that an INFINITE set is a `Finset`.** Both counterexamples are in this file.

1. **`mem_slopeFinset` (B.66a-iii).** Take `φ = 1` and `f = X`. Then every `φ`-adic development
   coefficient vanishes (`dev_one_eq_zero`: `f %ₘ 1 = 0` and `f /ₘ 1 = f`), so every height is
   `⊤` (`npHgt_one_eq_top`), so the cleared support value is `⊤` at every slope
   (`suppVal_one_eq_top`), so EVERY abscissa in range is on EVERY side
   (`sideSet_one : sideSet 1 f u ℓ = Finset.range (f.natDegree + 1)`). With
   `X.natDegree = 1` that is a two-element side for every `(u, 1)`, `u : ℕ` — infinitely many
   slopes satisfy the right-hand side. `no_unconditional_slopeFinset` turns this into a
   machine-checked refutation: **no** assignment `S : Polynomial O → Polynomial O → Finset (ℕ × ℕ)`
   whatsoever satisfies the signed biconditional for all `φ, f, p`.
2. **`mem_resFactorFinset` (B.66a-iv).** Take `f = 0` (any key `φ`). Every height is `⊤`
   (`npHgt_zero_eq_top`, from B.35a's `dev_of_zero`), so there is NO `H₀ : ℕ` with
   `npHgt φ 0 (sideMin …) = (H₀ : ℕ∞)`, so the divisibility clause is **vacuous** and the signed
   right-hand side collapses to `ψ.Monic ∧ Irreducible ψ` — machine-checked here as
   `resFactorSet_of_zero`. For a key `φ` the residual field `resField φ` is a field (B.25), and
   over any field the monic irreducible polynomials are infinite (Euclid's argument, not
   formalized here — the load-bearing and non-obvious half, the vacuity, is). So no `Finset` can
   satisfy that biconditional either.

**The repair, and what needs an owner/orchestrator re-sign.** The two `mem_…` lemmas below carry
the *minimal* extra hypotheses that make them true, and every one of them is already present in
B.42's own binder list, so no consumer pays anything new:

```
mem_slopeFinset      (hφ : IsKey φ) (hf : f.Monic) (hdeg : f.natDegree = μ * φ.natDegree)
mem_resFactorFinset  (hπ : Irreducible π) (hφ : IsKey φ) (hf : f.Monic)
                     (hdeg : f.natDegree = μ * φ.natDegree) (hℓ : 0 < p.2)
                     (hcop : Nat.Coprime p.1 p.2)
```

`hdeg` is the standing shape of B.18/B.30 (which is where it is consumed: `suppVal_ne_top`,
`sideSet_nonempty`, `natDegree_resPoly`), and it is free at every consumer: monic `f` with
`f.map (residue O) = (φ.map (residue O)) ^ μ` has `f.natDegree = μ * φ.natDegree` (B.58 step 1).
**The conclusions are byte-identical to the signed ones**; only the binder list grew. Names are
kept so that B.63/B.66/B.71/B.79a/B.79b/B.80 can read them by name.

## The bound B-D4 said was missing (`slopeSet_finite`)

Let `n = f.natDegree` and `Hb = sup_{j ≤ n} (npHgt φ f j).toNat`. If `(u,ℓ)` carries a two-point
side then, with `suppVal φ f u ℓ ≠ ⊤` (B.18, from `hφ hf hdeg`), pick two on-side abscissae
`j < j'`. Both heights are finite (B.17 step 1), so B.17's `onSide_nat_eq` gives
`ℓH + uj = ℓH' + uj'`, and B.17's `onSide_modEq` gives `ℓ ∣ j' - j`, say `j' - j = ℓk` with
`k ≥ 1`. Cancelling `ℓ`: `H = H' + uk`. Hence

```
ℓ ≤ ℓk = j' - j ≤ n        and        u ≤ uk ≤ H ≤ Hb,
```

so the qualifying slopes inject into `range (Hb+1) ×ˢ range (n+1)`. This is the "abscissa bound
the blueprint never states", stated and proved.

DEPENDS: B.01 (`IsKey`) · B.02 (`dev`) · B.11/B.12 (`npHgt`, `npHgt_eq_top_iff`) · B.14
(`suppVal`) · B.16 (`OnSide`, `sideSet`) · B.17 (`npHgt_ne_top_of_onSide`, `onSide_nat_eq`,
`onSide_modEq`) · B.18 (`suppVal_ne_top`, `sideSet_nonempty`) · B.20 (`sideMin`,
`onSide_of_mem_sideSet`) · B.25 (`resField`, `instFieldResField`) · B.29 (`resPoly`) · B.30
(`natDegree_resPoly`) · B.35a (`dev_of_zero`) · mathlib `Set.Finite.toFinset`,
`Polynomial.mem_normalizedFactors_iff`, `Finset.one_lt_card`, `Nat.modEq_iff_dvd'`.

**NOT depended on: B.42.** See the headline.

## Faithfulness

The two suppliers are the B.42/B.45 index sets *as characterised*, not *as constructed*:
`slopeFinset` is the set of slopes carrying a two-point side — B.42's own clause 5
(`1 < (sideSet φ f u ℓ).card ↔ (u,ℓ) ∈ s`), verbatim, which is precisely why the canonical body
is available; `resFactorFinset` is the monic irreducible divisor set of the side's residual
polynomial at the GC-1 `sideMin` pin — B.45's `(normalizedFactors R).toFinset` read
(`Polynomial.mem_normalizedFactors_iff`: membership ↔ `Irreducible ψ ∧ ψ.Monic ∧ ψ ∣ R`), which
is exactly how `resFactorSet_finite` discharges finiteness. **Flagged for human review**
(definition faithfulness; parent CLAUDE.md trust boundary), and the two membership statements
additionally need the orchestrator's re-sign per B-D4's own caveat marker.

SOURCE: `blueprint/CHAP-B_leaf_layer.md` A-F.3 item **B-D4** (the signed forms) and A-§9.5 (the
booking); B.42 clause 5 (the slope characterisation); B.45 (the residual factorization read).

**TEETH.** Definitions: signed non-applicability. The two refutations are this node's own
regression: they are Lean theorems, so a future re-signing that drops the repair hypotheses
cannot compile.

## Status

Sorry-free, axiom-free (Lean core only). No `axiom` is declared here and none is consumed —
in particular not the 2026-08-16 B.42 literature cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena. The blueprint tags this node ENV-C; neither
-- body nor any statement below consults completeness or residue finiteness, so the elaborated
-- types carry ENV-A only (the same 0e type-diff artifact recorded at B.26 and B.58).
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The two suppliers -/

-- `π` is part of the frozen A-F.3/B-D4 signature and is not consumed by the body (the slope
-- data is `π`-free; only `resFactorFinset`'s residual polynomials see `π`). Kept verbatim.
set_option linter.unusedVariables false in
/-- **B.66a-i — the canonical slope `Finset`.** The slopes `(u,ℓ)` in lowest terms, `ℓ > 0`,
that carry a two-point side of `f`'s `φ`-adic Newton polygon — B.42's clause-5 characterisation
taken as the *definition*, via `Set.Finite.toFinset`. The junk value `∅` is returned off the
finiteness regime; `slopeSet_finite` shows that regime contains every key/monic instance. -/
noncomputable def slopeFinset (π : O) (φ f : Polynomial O) : Finset (ℕ × ℕ) :=
  open Classical in
  if h : {p : ℕ × ℕ | 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      1 < (sideSet φ f p.1 p.2).card}.Finite then h.toFinset else ∅

/-- **B.66a-ii — the canonical residual factor `Finset` at a slope.** The monic irreducible
`ψ ∈ (resField φ)[Y]` dividing the `(p.1,p.2)`-side's residual polynomial at the GC-1 `sideMin`
pin — B.45's factor reading taken as the *definition*, via `Set.Finite.toFinset`, junk value `∅`
off the finiteness regime (`resFactorSet_finite`). -/
noncomputable def resFactorFinset (π : O) (φ f : Polynomial O) (p : ℕ × ℕ) :
    Finset (Polynomial (resField φ)) :=
  open Classical in
  if h : {ψ : Polynomial (resField φ) | ψ.Monic ∧ Irreducible ψ ∧
      ∀ (hne : (sideSet φ f p.1 p.2).Nonempty) (H₀ : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
          ψ ∣ resPoly π φ f p.1 p.2 hne H₀}.Finite then h.toFinset else ∅

/-! ## 2. The `→` halves — unconditional -/

/-- **B.66a-iii, `→` half — no hypotheses.** A member of `slopeFinset` really is a two-point-side
slope in lowest terms. Off the finiteness regime the supplier is `∅` and this is vacuous. -/
theorem mem_slopeFinset_imp {φ f : Polynomial O} {p : ℕ × ℕ} (hp : p ∈ slopeFinset π φ f) :
    0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ 1 < (sideSet φ f p.1 p.2).card := by
  classical
  rw [slopeFinset] at hp
  split_ifs at hp with h
  · exact (Set.Finite.mem_toFinset h).mp hp
  · exact absurd hp (Finset.notMem_empty p)

/-- **B.66a-iv, `→` half — no hypotheses.** A member of `resFactorFinset` really is a monic
irreducible dividing the pinned residual polynomial. -/
theorem mem_resFactorFinset_imp {φ f : Polynomial O} {p : ℕ × ℕ}
    {ψ : Polynomial (resField φ)} (hψ : ψ ∈ resFactorFinset π φ f p) :
    ψ.Monic ∧ Irreducible ψ ∧
      ∀ (hne : (sideSet φ f p.1 p.2).Nonempty) (H₀ : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
          ψ ∣ resPoly π φ f p.1 p.2 hne H₀ := by
  classical
  rw [resFactorFinset] at hψ
  split_ifs at hψ with h
  · exact (Set.Finite.mem_toFinset h).mp hψ
  · exact absurd hψ (Finset.notMem_empty ψ)

/-! ## 3. Finiteness — the abscissa bound B-D4 called missing -/

/-- **The slope bound.** For an order-1 key `φ` and a monic `f` of degree `μ * φ.natDegree`, only
finitely many coprime slopes carry a two-point side: they inject into
`range (Hb+1) ×ˢ range (f.natDegree+1)` with `Hb = sup_{j ≤ n} (npHgt φ f j).toNat`, by B.17's
`ℓ`-spacing and the cancelled height equation `H = H' + u*k`. -/
theorem slopeSet_finite {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) :
    {p : ℕ × ℕ | 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      1 < (sideSet φ f p.1 p.2).card}.Finite := by
  classical
  set n := f.natDegree with hn
  set Hb := (Finset.range (n + 1)).sup (fun j => (npHgt φ f j).toNat) with hHb
  refine Set.Finite.subset
    (Finset.finite_toSet ((Finset.range (Hb + 1)) ×ˢ (Finset.range (n + 1)))) ?_
  rintro ⟨u, ℓ⟩ ⟨hℓ, hcop, hcard⟩
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have hrange : ∀ j ∈ sideSet φ f u ℓ, j ∈ Finset.range (n + 1) := by
    intro j hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    exact (Finset.mem_filter.mp hj').1
  -- the whole content: two on-side abscissae bound both coordinates of the slope
  have key : ∀ j j' : ℕ, j ∈ sideSet φ f u ℓ → j' ∈ sideSet φ f u ℓ → j < j' →
      ℓ < n + 1 ∧ u < Hb + 1 := by
    intro j j' hj hj' hlt
    have hjs : OnSide φ f u ℓ j := onSide_of_mem_sideSet hj
    have hj's : OnSide φ f u ℓ j' := onSide_of_mem_sideSet hj'
    obtain ⟨H, hH⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hjs)
    obtain ⟨H', hH'⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hj's)
    have heq : ℓ * H + u * j = ℓ * H' + u * j' := onSide_nat_eq hH.symm hH'.symm hjs hj's
    have hmod : j ≡ j' [MOD ℓ] := onSide_modEq hℓ hcop htop hjs hj's
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, Nat.mul_zero] at hk; omega
      · exact h0
    have hj'eq : j' = j + ℓ * k := by omega
    have hHk : H = H' + u * k := by
      have e1 : ℓ * H + u * j = ℓ * H' + u * (j + ℓ * k) := by rw [← hj'eq]; exact heq
      have e2 : ℓ * H = ℓ * (H' + u * k) := by nlinarith [e1]
      exact Nat.eq_of_mul_eq_mul_left hℓ e2
    have hjn : j ∈ Finset.range (n + 1) := hrange j hj
    have hj'n : j' ∈ Finset.range (n + 1) := hrange j' hj'
    have hHle : H ≤ Hb := by
      have hcast : (npHgt φ f j).toNat = H := by rw [← hH]; exact ENat.toNat_coe H
      calc H = (npHgt φ f j).toNat := hcast.symm
        _ ≤ Hb := Finset.le_sup (f := fun j => (npHgt φ f j).toNat) hjn
    have hj'le : j' ≤ n := by
      have := Finset.mem_range.mp hj'n; omega
    constructor
    · have : ℓ * 1 ≤ ℓ * k := Nat.mul_le_mul_left ℓ hk0
      omega
    · have : u * 1 ≤ u * k := Nat.mul_le_mul_left u hk0
      omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have hres : ℓ < n + 1 ∧ u < Hb + 1 := by
    rcases Nat.lt_or_ge a b with h | h
    · exact key a b ha hb h
    · exact key b a hb ha (by omega)
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hres.2, Finset.mem_range.mpr hres.1⟩)

/-- **The residual factor bound.** At a coprime slope with `0 < ℓ`, the pinned residual
polynomial is nonzero (B.30's `natDegree_resPoly`, second clause), so its monic irreducible
divisors are its normalized factors — a `Finset`. -/
theorem resFactorSet_finite (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {p : ℕ × ℕ} (hℓ : 0 < p.2) (hcop : Nat.Coprime p.1 p.2) :
    {ψ : Polynomial (resField φ) | ψ.Monic ∧ Irreducible ψ ∧
      ∀ (hne : (sideSet φ f p.1 p.2).Nonempty) (H₀ : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
          ψ ∣ resPoly π φ f p.1 p.2 hne H₀}.Finite := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have htop : suppVal φ f p.1 p.2 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg p.1 p.2)
  have hne : (sideSet φ f p.1 p.2).Nonempty := sideSet_nonempty hφ.monic hφ.pos hf hdeg p.1 p.2
  have hmin : sideMin φ f p.1 p.2 hne ∈ sideSet φ f p.1 p.2 := Finset.min'_mem _ _
  obtain ⟨H₀, hH₀⟩ := WithTop.ne_top_iff_exists.mp
    (npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hmin))
  have hR0 : resPoly π φ f p.1 p.2 hne H₀ ≠ 0 := by
    intro h0
    have hc := (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀.symm).2
    rw [h0] at hc
    exact hc (Polynomial.coeff_zero 0)
  refine Set.Finite.subset (Finset.finite_toSet
    (UniqueFactorizationMonoid.normalizedFactors (resPoly π φ f p.1 p.2 hne H₀)).toFinset) ?_
  intro ψ hψ
  simp only [Multiset.mem_toFinset, Finset.mem_coe]
  exact (Polynomial.mem_normalizedFactors_iff hR0).2 ⟨hψ.2.1, hψ.1, hψ.2.2 hne H₀ hH₀.symm⟩

/-! ## 4. The membership lemmas — A-F.3/B-D4's conclusions, with the repair hypotheses -/

/-- **B.66a-iii `mem_slopeFinset` [repaired: B-D4 — hypotheses added, conclusion verbatim].**
`p ∈ slopeFinset π φ f` exactly for the coprime, two-point-side slopes. The three hypotheses are
B.42's own and are NOT droppable: `no_unconditional_slopeFinset` refutes the hypothesis-free
form for every body. -/
theorem mem_slopeFinset {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) {p : ℕ × ℕ} :
    p ∈ slopeFinset π φ f ↔
      (0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ 1 < (sideSet φ f p.1 p.2).card) := by
  classical
  refine ⟨mem_slopeFinset_imp, fun hp => ?_⟩
  rw [slopeFinset]
  split_ifs with h
  · exact (Set.Finite.mem_toFinset h).mpr hp
  · exact absurd (slopeSet_finite hφ hf hdeg) h

/-- **B.66a-iv `mem_resFactorFinset` [repaired: B-D4 — hypotheses added, conclusion verbatim].**
`ψ ∈ resFactorFinset π φ f p` exactly for the monic irreducible divisors of the side's residual
polynomial at the `sideMin` pin. The hypotheses are B.42's/B.30's own and are NOT droppable: at
`f = 0` the divisibility clause is vacuous (`resFactorSet_of_zero`) and the right-hand side
describes the infinite set of ALL monic irreducibles. -/
theorem mem_resFactorFinset (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {p : ℕ × ℕ} (hℓ : 0 < p.2) (hcop : Nat.Coprime p.1 p.2)
    {ψ : Polynomial (resField φ)} :
    ψ ∈ resFactorFinset π φ f p ↔
      (ψ.Monic ∧ Irreducible ψ ∧
        ∀ (hne : (sideSet φ f p.1 p.2).Nonempty) (H₀ : ℕ),
          npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
            ψ ∣ resPoly π φ f p.1 p.2 hne H₀) := by
  classical
  refine ⟨mem_resFactorFinset_imp, fun hψ => ?_⟩
  rw [resFactorFinset]
  split_ifs with h
  · exact (Set.Finite.mem_toFinset h).mpr hψ
  · exact absurd (resFactorSet_finite hπ hφ hf hdeg hℓ hcop) h

/-! ## 5. The two refutations — why the hypotheses above are not decoration

Neither declaration in this section is contract text; they are the node's own regression against
a future re-signing that drops the repair hypotheses. -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- At the degenerate "key" `φ = 1` the `φ`-adic development is identically zero: `f %ₘ 1 = 0`
and `f /ₘ 1 = f`. -/
theorem dev_one_eq_zero (f : Polynomial O) (j : ℕ) : dev (1 : Polynomial O) f j = 0 := by
  induction j generalizing f with
  | zero => simp [dev]
  | succ j ih => rw [dev]; exact ih _

/-- …hence every polygon height at `φ = 1` is `⊤`. -/
theorem npHgt_one_eq_top (f : Polynomial O) (j : ℕ) : npHgt (1 : Polynomial O) f j = ⊤ :=
  npHgt_eq_top_iff.mpr (dev_one_eq_zero f j)

/-- …hence every cleared support value at `φ = 1` is `⊤` (`0 < ℓ` makes `ℓ • ⊤ = ⊤`). -/
theorem suppVal_one_eq_top (f : Polynomial O) {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    suppVal (1 : Polynomial O) f u ℓ = ⊤ := by
  have hcong : ∀ j ∈ Finset.range (f.natDegree + 1),
      ℓ • npHgt (1 : Polynomial O) f j + ((u * j : ℕ) : ℕ∞) = ⊤ := by
    intro j _
    rw [npHgt_one_eq_top]
    simp [nsmul_eq_mul, hℓ.ne']
  rw [suppVal, Finset.inf_congr rfl hcong]
  simp

/-- …hence at `φ = 1` EVERY abscissa in range is on EVERY side: the "polygon" degenerates and
`sideSet` stops depending on the slope. -/
theorem sideSet_one (f : Polynomial O) {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    sideSet (1 : Polynomial O) f u ℓ = Finset.range (f.natDegree + 1) := by
  classical
  rw [sideSet]
  refine Finset.filter_true_of_mem ?_
  intro j _
  show ℓ • npHgt (1 : Polynomial O) f j + ((u * j : ℕ) : ℕ∞) = suppVal (1 : Polynomial O) f u ℓ
  rw [npHgt_one_eq_top, suppVal_one_eq_top f hℓ]
  simp [nsmul_eq_mul, hℓ.ne']

/-- **REFUTATION of A-F.3/B-D4's `mem_slopeFinset` as signed.** No assignment of `Finset`s to
pairs `(φ, f)` — the signed `slopeFinset` or any other — satisfies the hypothesis-free
biconditional: at `φ = 1`, `f = X` the right-hand side holds for all of the infinitely many
slopes `(u, 1)`. Hence the `hφ`/`hf`/`hdeg` of `mem_slopeFinset` above are necessary, and B-D4's
statement must be re-signed. -/
theorem no_unconditional_slopeFinset (S : Polynomial O → Polynomial O → Finset (ℕ × ℕ)) :
    ¬ ∀ (φ f : Polynomial O) (p : ℕ × ℕ), p ∈ S φ f ↔
        (0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ 1 < (sideSet φ f p.1 p.2).card) := by
  classical
  intro hS
  have hmem : ∀ u : ℕ, (u, 1) ∈ S 1 X := by
    intro u
    refine (hS 1 X (u, 1)).mpr ⟨Nat.one_pos, Nat.coprime_one_right u, ?_⟩
    have h2 : sideSet (1 : Polynomial O) X u 1
        = Finset.range ((X : Polynomial O).natDegree + 1) := sideSet_one X Nat.one_pos
    simp [h2, Polynomial.natDegree_X]
  have hsub : (Finset.range ((S 1 X).card + 1)).image (fun u => ((u, 1) : ℕ × ℕ)) ⊆ S 1 X := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_range] at hq
    obtain ⟨u, -, rfl⟩ := hq
    exact hmem u
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at hcard
  omega

/-- At `f = 0` every height is `⊤` (B.35a's `dev_of_zero`). -/
theorem npHgt_zero_eq_top (φ : Polynomial O) (j : ℕ) : npHgt φ (0 : Polynomial O) j = ⊤ :=
  npHgt_eq_top_iff.mpr (dev_of_zero φ j)

/-- **REFUTATION half for A-F.3/B-D4's `mem_resFactorFinset` as signed.** At `f = 0` there is no
`H₀ : ℕ` pinning the height at `sideMin`, so the divisibility clause is vacuous and the signed
right-hand side is exactly "monic irreducible" — an infinite set of polynomials over the field
`resField φ` (Euclid; not formalized). Hence the hypotheses of `mem_resFactorFinset` above are
necessary, and B-D4's statement must be re-signed. -/
theorem resFactorSet_of_zero (φ : Polynomial O) (p : ℕ × ℕ) (ψ : Polynomial (resField φ)) :
    (ψ.Monic ∧ Irreducible ψ ∧
        ∀ (hne : (sideSet φ (0 : Polynomial O) p.1 p.2).Nonempty) (H₀ : ℕ),
          npHgt φ (0 : Polynomial O) (sideMin φ (0 : Polynomial O) p.1 p.2 hne) = (H₀ : ℕ∞) →
            ψ ∣ resPoly π φ (0 : Polynomial O) p.1 p.2 hne H₀)
      ↔ (ψ.Monic ∧ Irreducible ψ) := by
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, fun hne H₀ hH => absurd hH ?_⟩
    rw [npHgt_zero_eq_top]
    exact Ne.symm (ENat.coe_ne_top H₀)

end Uniformity.Density.Leaf

/-! ## Axiom footprint

Lean core throughout — no `axiom` is declared here, and the B.42 literature cite is neither
imported nor consumed. -/

section AxCheck
#print axioms Uniformity.Density.Leaf.slopeFinset
#print axioms Uniformity.Density.Leaf.resFactorFinset
#print axioms Uniformity.Density.Leaf.mem_slopeFinset_imp
#print axioms Uniformity.Density.Leaf.mem_resFactorFinset_imp
#print axioms Uniformity.Density.Leaf.slopeSet_finite
#print axioms Uniformity.Density.Leaf.resFactorSet_finite
#print axioms Uniformity.Density.Leaf.mem_slopeFinset
#print axioms Uniformity.Density.Leaf.mem_resFactorFinset
#print axioms Uniformity.Density.Leaf.no_unconditional_slopeFinset
#print axioms Uniformity.Density.Leaf.resFactorSet_of_zero
end AxCheck
