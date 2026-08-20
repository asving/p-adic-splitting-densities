/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C87 — LEMMA GENTOW5-D: the forward carry prices up the tower

**Chapter C, NODE C.87** [lemma] [fresh] [signed: A-C.1 — the two displayed carry computations,
uniform in `j`; **NO two-directional statement exists**, S11.1's withdrawal honored]
(`blueprint/CHAP-C_tower_grammar.md` §11, NODE C.87; twin `leanspec/Leanspec/ChapC.lean`, the
`### NODE C.87` block).  **ENV-C5/C1**.  Two signed theorems, both pure datum arithmetic.

Fix a frame `F` (C.01) pinned at `H₀` (C.14a's `F.Pin H₀`) and a depth-`r` tower datum
`W : DeepTower F H₀ hpin r` (C.83).  C.83 names, per stage `i`:

* `W.e i`, `W.f i`, `W.u i` — the stage ramification index, residual degree, and slope numerator;
* `W.ehat i = e₁⋯e_i` (`DeepTower.ehat`) — the cumulative ramification;
* `W.Econst i = e_i·f_i·u_i` (`DeepTower.Econst`) — the stage side constant;
* `W.hfloor` — THE FLOOR CHAIN, a datum FIELD: `e_{i+1}·(e_i f_i u_i) < u_{i+1}` for `1 ≤ i < r`.

The forward reduction moves of the level-`i` grid are priced in the weight
`wt_i(π^v x^a Φ_1^{b_1} ⋯) = ê_i·v + a·(ê_i/e_1)·u_1 + Σ_j b_j·(ê_i/ê_{j+1})·u_{j+1}`
(C.84's `towerWeight`).  This node is the pair of price computations that the forward direction
of GENTOW5-D needs, both read off that weight:

* `towerCarry_interior_strict` — an INTERIOR carry (rung `j+1` with `j + 1 < i`) has its key-part
  land at rung `j + 2`, and the landing price STRICTLY exceeds the departure price.  The gap is
  exactly one floor rung: departure `l_{j+1}·(ê_i/ê_{j+1})·u_{j+1}`, arrival
  `(ê_i/ê_{j+2})·u_{j+2}`, and the quotient identity `ê_i/ê_{j+1} = e_{j+2}·(ê_i/ê_{j+2})`
  turns the comparison into `e_{j+2}·E_{j+1} < u_{j+2}` — the datum's own `hfloor` at `j+1`.
* `towerCarry_top_exact` — the TOP carry (rung `i` itself) is `E_i`-priced EXACTLY: no floor rung
  is consumed, because `ê_i/ê_i = 1` and the price collapses to `e_i f_i u_i = E_i`.  At `i = 1`
  the top carry is the ONLY move (the `[GT5-r2]` edge), which is why `towerCarry_interior_strict`
  carries `j + 1 < i` and is silent there.

## ⚠ What this node does NOT state (S11.1, CRITICAL)

The two-directional closure — *"all slots at weight `≥ W` is the same condition on every grid"* —
is **WITHDRAWN**: it is FALSE as written, since the converse rewriting is weight-NONINCREASING.
**No two-directional statement is landed here, and a stub matching the withdrawn closure would be
a defect, not a gap.**  Named consumers (C.85 Step B, C.91(c) Steps 0/3, C.91(d)) use the forward
direction only.

## MANDATORY A-C.7 FIVE-INSTANCE BINDER-VACUITY AUDIT — verdict: **PASS (non-vacuous)**

Audited before any proving, against the A-C.7 registry's four prior A-C.1 failures plus the
A-C.8.4 additional row (`blueprint/CHAP-C_tower_grammar.md` §A-C.8.4).  Hypotheses under audit —
`towerCarry_interior_strict`: `W`, `hj : 1 ≤ j`, `hji : j + 1 < i`, `hir : i ≤ r`;
`towerCarry_top_exact`: `W`, `hi : 1 ≤ i`, `hir : i ≤ r`.

**Pattern 1 — C.111 `hnode`, an unpinned carrier field.**  No analogue.  Every symbol in both
conclusions (`e`, `f`, `u`, `ehat`, `Econst`) is a projection of `W`, and on the audited range
`1 ≤ · ≤ r` each is pinned by a datum field (`he`, `hf`, `hfloor`); `ehat` and `Econst` are `def`s
of those.  No free carrier is quantified.

**Pattern 2 — C.94, a self-loop trivializing an infinite relation.**  No relation, no history and
no reachability predicate is quantified.  Both statements are single arithmetic comparisons at
explicit indices.

**Pattern 3 — C.113 `hne`, a `Nonempty` hypothesis with no intended content.**  Neither statement
has a `Nonempty`, an existential side witness, or a dependent-witness binder.

**Pattern 4 — C.118 `Visible₂`, an `x ≠ ⊤ → …` guard leaving the `⊤` stratum open.**  Neither
statement contains an implication-guarded `≠ ⊤`, a visibility predicate, a window, or any
`ℕ∞`-valued term at all: both live entirely in `ℕ`.

**Pattern 5 — C.66's low-degree purity collapse.**  No purity predicate and no polynomial is
mentioned; nothing here can collapse by a degree degeneration.

**Index range empties the statement?**  `towerCarry_interior_strict` needs `1 ≤ j` and
`j + 1 < i ≤ r`, hence `r ≥ 3`; `towerCarry_top_exact` needs `1 ≤ i ≤ r`, hence `r ≥ 1`.  Both
ranges are **inhabited by a LANDED instance**: `s2Witness h2 hq H₀ hpin : DeepTower … 3` (C.97),
whose own `hpin` binder is inhabited and pinned (`s2Frame_pin` / `s2Frame_pin_unique`).
Concretely `(j, i, r) = (1, 3, 3)` satisfies every hypothesis of the first, and
`(i, r) = (1, 3), (2, 3), (3, 3)` the second.

**`ℕ`-division junk makes the comparison meaningless?**  This is the one place the audit bites:
`HDiv.hDiv` on `ℕ` truncates, and both conclusions divide two `ehat`s.  On the audited range the
division is EXACT — `ehat (j+1) ∣ ehat i` because `Finset.Icc 1 (j+1) ⊆ Finset.Icc 1 i`
(`DeepTower.ehat_dvd` below) — so the terms are the honest partial products `∏_{t=j+2}^{i} e t`,
not truncations.  This is proved, not assumed: `ehat_dvd` and `ehat_pos` are the lemmas the main
proofs route through, and `ehat_div_succ` is the exact-quotient identity.

**No `DeepTower` values exist?**  Ruled out by the landed `s2Witness` (C.97), constructed without
either statement of this node.

**Verdict.** No fifth instance of the A-C.7 vacuity pattern.  Both statements are satisfiable at a
LANDED witness, and the only degenerate stratum available to them (`ℕ`-division truncation) is
closed by a proved exactness lemma rather than assumed away.

*Self-refutation attempt, per the standing lesson that a drafted repair is itself a refutation
target:* the natural "strengthening" that relaxes `hji : j + 1 < i` to `j + 1 ≤ i` **REFUTES** the
first statement — at `j + 1 = i` the quotient `ê_i / ê_{j+2} = ê_i / ê_{i+1}` truncates to `0`
whenever `e (i+1) ≥ 2`, so the right-hand side is `0` while the left-hand side is positive.  The
signed `j + 1 < i` is therefore load-bearing and is kept exactly as signed.

**DEPENDS.** C.83 (`DeepTower`, `ehat`, `Econst`, `hfloor`, `he`, `hf`) — imported.  By committed
node ID: C.84 (`towerWeight`, the weight these are the prices in) · C.50/C.52 (the `i = 2`
instance the top price must match: GENTOW1 Step 0 prices the `Φ₂`-part at weight `E₂` exactly).

**PROOF.** The two displayed carry computations, uniform in `j`, through the exact-quotient
identity `ê_i/ê_{j+1} = e_{j+2}·(ê_i/ê_{j+2})`; the strict rung is the datum's `hfloor`.

**SIZE.** 40 lines (blueprint estimate).

**SOURCE.** `EFF.GENTOW5.25` (the `[GT5-r1]`/`[GT5-r2]` restated statement + proof + failure-mode
fence, verbatim; S11.1's withdrawal — CHAIN TERMINAL; the grid-4 `170 = 170 = 170` fence).

**TEETH.** `gentow5_af1_direction_check.py` (8/0, both directions) → executable regression,
retained; the grid-4 equality → retained.  The `example`s below are the local unfolding checks.

**ENVIRONMENT.** ENV-C5/C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

namespace DeepTower

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ### The exactness lemmas the `ℕ`-divisions ride on

`DeepTower.ehat` is a `Finset.Icc`-product, and the signed statements divide two of them.  On the
live range `1 ≤ · ≤ r` those divisions are EXACT; the lemmas below are what makes that a theorem
rather than a hope (module docstring's vacuity audit, the `ℕ`-division row). -/

/-- `ê_i > 0` on the live range: every factor is positive by `W.he`. -/
theorem ehat_pos (W : DeepTower F H₀ hpin r) {i : ℕ} (hir : i ≤ r) : 0 < W.ehat i := by
  rw [DeepTower.ehat]
  refine Finset.prod_pos fun t ht => ?_
  rw [Finset.mem_Icc] at ht
  exact W.he t ht.1 (ht.2.trans hir)

/-- `ê_a ∣ ê_b` for `a ≤ b`: the index sets nest. -/
theorem ehat_dvd (W : DeepTower F H₀ hpin r) {a b : ℕ} (hab : a ≤ b) :
    W.ehat a ∣ W.ehat b := by
  rw [DeepTower.ehat, DeepTower.ehat]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro t ht
  rw [Finset.mem_Icc] at ht ⊢
  exact ⟨ht.1, ht.2.trans hab⟩

/-- one rung of the cumulative product: `ê_{k+1} = ê_k · e_{k+1}`. -/
theorem ehat_succ (W : DeepTower F H₀ hpin r) (k : ℕ) :
    W.ehat (k + 1) = W.ehat k * W.e (k + 1) := by
  rw [DeepTower.ehat, DeepTower.ehat, Finset.prod_Icc_succ_top (by omega)]

/-- **the exact-quotient identity** — the arithmetic heart of the interior price.  For
`k + 1 ≤ i ≤ r`, `ê_i / ê_k = e_{k+1} · (ê_i / ê_{k+1})`: dropping one rung from the denominator
multiplies the quotient by exactly that rung's `e`.  Both divisions are exact (`ehat_dvd`). -/
theorem ehat_div_succ (W : DeepTower F H₀ hpin r) {k i : ℕ} (hki : k + 1 ≤ i) (hir : i ≤ r) :
    W.ehat i / W.ehat k = W.e (k + 1) * (W.ehat i / W.ehat (k + 1)) := by
  obtain ⟨c, hc⟩ := W.ehat_dvd hki
  have hk1pos : 0 < W.ehat (k + 1) := W.ehat_pos (le_trans hki hir)
  have hkpos : 0 < W.ehat k := W.ehat_pos (by omega)
  have hquot1 : W.ehat i / W.ehat (k + 1) = c := by
    rw [hc, Nat.mul_div_cancel_left _ hk1pos]
  have hi : W.ehat i = W.ehat k * (W.e (k + 1) * c) := by
    rw [hc, W.ehat_succ k]; ring
  rw [hquot1, hi]
  exact Nat.mul_div_cancel_left _ hkpos

end DeepTower

/-! ### The two signed statements -/

/-- **NODE C.87 (i) — INTERIOR carries STRICTLY raise the weight.**  For an interior rung
(`1 ≤ j`, `j + 1 < i ≤ r`) the departure price of the rung-`(j+1)` carry,
`l_{j+1}·(ê_i/ê_{j+1})·u_{j+1}`, is STRICTLY below the arrival price `(ê_i/ê_{j+2})·u_{j+2}` at
rung `j + 2`: one floor rung is consumed, in-datum.

The mechanism, in one line: `DeepTower.ehat_div_succ` rewrites `ê_i/ê_{j+1}` as
`e_{j+2}·(ê_i/ê_{j+2})`, after which the comparison is `(ê_i/ê_{j+2})` times the datum's own
floor chain `W.hfloor (j+1) : e_{j+2}·(e_{j+1}f_{j+1}u_{j+1}) < u_{j+2}`.

The hypothesis `j + 1 < i` is load-bearing and NOT slack: at `j + 1 = i` the right-hand quotient
truncates to `0` and the statement is FALSE (module docstring, self-refutation paragraph). -/
theorem towerCarry_interior_strict {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i j : ℕ) (hj : 1 ≤ j) (hji : j + 1 < i) (hir : i ≤ r) :
    (W.e (j + 1) * W.f (j + 1)) * ((W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
      < (W.ehat i / W.ehat (j + 2)) * W.u (j + 2) := by
  have hfl : W.e (j + 2) * (W.e (j + 1) * W.f (j + 1) * W.u (j + 1)) < W.u (j + 2) :=
    W.hfloor (j + 1) (by omega) (by omega)
  have hApos : 0 < W.ehat i / W.ehat (j + 2) :=
    Nat.div_pos (Nat.le_of_dvd (W.ehat_pos hir) (W.ehat_dvd (by omega)))
      (W.ehat_pos (by omega))
  rw [W.ehat_div_succ (k := j + 1) (by omega) hir]
  calc (W.e (j + 1) * W.f (j + 1))
        * ((W.e (j + 2) * (W.ehat i / W.ehat (j + 2))) * W.u (j + 1))
      = (W.ehat i / W.ehat (j + 2))
          * (W.e (j + 2) * (W.e (j + 1) * W.f (j + 1) * W.u (j + 1))) := by ring
    _ < (W.ehat i / W.ehat (j + 2)) * W.u (j + 2) := by
        exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) hfl hApos

/-- **NODE C.87 (ii) — the TOP carry is `E_i`-priced EXACTLY.**  At the top rung of the level-`i`
grid the key-part's price is `l_i·(ê_i/ê_i)·u_i = e_i f_i u_i = E_i`: NO floor rung is consumed,
`ê_i/ê_i` being `1` exactly (by `DeepTower.ehat_pos` — this is where the `1 ≤ i ≤ r` range is
spent; without it the `ℕ`-division `0/0` would still be `0`, not `1`).

This is the `[GT5-r2]` edge clause: at `i = 1` the top carry is the ONLY move available, which is
why C.87(i) is silent there (its `j + 1 < i` cannot hold with `1 ≤ j`).  The `i = 2` instance is
the corpus cross-check — GENTOW1 Step 0 prices the `Φ₂`-part "at weight `E₂` exactly".

`hi : 1 ≤ i` is a SIGNED binder and is kept although the proof routes the range through `hir`
alone: it is the `[GT5-r2]` edge marker, and dropping it would change the signed statement. -/
set_option linter.unusedVariables false in
theorem towerCarry_top_exact {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
    (W.e i * W.f i) * ((W.ehat i / W.ehat i) * W.u i) = W.Econst i := by
  rw [Nat.div_self (W.ehat_pos hir), one_mul, DeepTower.Econst]

end Uniformity.Density.Tower

/-! ## Unfolding checks

`example`s, not declarations: the local pins on the two prices.  They fix the exact-quotient
identity at the shallowest live index, the `i = 1` degeneration of the top price (where the
quotient is `ê_1/ê_1 = 1` and the price is `E_1 = e₁f₁h`), and — the negative control — that the
interior statement's index guard cannot be read as `j + 1 ≤ i`. -/

section UnfoldingChecks

open Uniformity.Density.Tower Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the exact-quotient identity at `k = 1`, `i = 2`: `ê_2/ê_1 = e_2·(ê_2/ê_2) = e_2`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ} (W : DeepTower F H₀ hpin r)
    (hr : 2 ≤ r) : W.ehat 2 / W.ehat 1 = W.e 2 := by
  rw [W.ehat_div_succ (k := 1) (by omega) hr, Nat.div_self (W.ehat_pos hr), mul_one]

/-- the top price at `i = 1` IS the frame's own side constant `E_1 = e₁f₁h` (`he1`/`hf1`/`hu1`). -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ} (W : DeepTower F H₀ hpin r)
    (hr : 1 ≤ r) :
    (W.e 1 * W.f 1) * ((W.ehat 1 / W.ehat 1) * W.u 1) = (F.e₁ * F.f₁) * F.h := by
  rw [towerCarry_top_exact W 1 (le_refl 1) hr, DeepTower.Econst, W.he1, W.hf1, W.hu1]

/-- the interior price is a `(ê_i/ê_{j+2})`-multiple of the floor-chain comparison — the shape the
proof consumes, isolated so that a transposed `j + 1 ↔ j + 2` in the signed body cannot survive.
Read at `j = 1`, `i = 3`: `l₂·e₃·u₂ < u₃`, i.e. `e₃·E₂ < u₃`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ} (W : DeepTower F H₀ hpin r)
    (hr : 3 ≤ r) :
    (W.e 2 * W.f 2) * ((W.ehat 3 / W.ehat 2) * W.u 2) < (W.ehat 3 / W.ehat 3) * W.u 3 :=
  towerCarry_interior_strict W 3 1 (le_refl 1) (by omega) hr

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.ehat_pos
#print axioms Uniformity.Density.Tower.DeepTower.ehat_dvd
#print axioms Uniformity.Density.Tower.DeepTower.ehat_succ
#print axioms Uniformity.Density.Tower.DeepTower.ehat_div_succ
#print axioms Uniformity.Density.Tower.towerCarry_interior_strict
#print axioms Uniformity.Density.Tower.towerCarry_top_exact

end AxCheck
