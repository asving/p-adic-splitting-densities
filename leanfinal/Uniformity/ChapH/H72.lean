/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H09
import Uniformity.ChapH.H33

/-!
# Uniformity.ChapH.H72 — `rate_lossPriced`, the loss-priced stage-drain exponent `(C2Q.1)`

**Chapter H, NODE H.72** (`blueprint/CHAP-H_general_induction.md` §10, the drainage-rate calculus;
`GENIND-C2Q`). Let `G` be a genre datum, `S` the actual side length, `H` the entry height, and
`I : StageInterface G N H S` (H.09). If the entry mass obeys
`ρ ≤ (Q^(b_S·H + C_G^extra))⁻¹` in the `2*`-cleared form of H.33 and the stage drain obeys
`δ ≤ K★ · N^B★ · (Q^(f₁·M_G))⁻¹`, then

  `ρ · δ ≤ K★ · N^B★ · (Q^(a(N−1)))⁻¹ · (Q^(H/2))⁻¹ · Q^(O_G(1))`,

i.e. the exponent is `−a(N−1) − H/2 + O_G(1)`, exactly `(C2Q.1)`, with `a = keyDeg G = e₁f₁`.
**This file lands the exponent bookkeeping of that line**, cleared of every division and stated in
`ℕ`, which is the whole content of the corpus's proof.

## ⚠ AMENDMENT BANNER — THE COMMITTED DISPLAY WAS MACHINE-REFUTED (A-H.1/D4)

The signature below is **not** the shape committed at the first pass. The committed display

    2 * (G.f₁ * I.stageWindow) + 2 * ((S + 1) * H) + 2 * (2 * I.entryCodim)
      ≥ 2 * (2 * G.keyDeg * (N - 1 - H)) + 2 * (2 * G.keyDeg * H) + H
        - 2 * (2 * I.slack)

is **FALSE**. The stage-0e stub gate (`leanspec/Leanspec/ChapH.lean`) constructs a genuine
instance `stageIfaceE : StageInterface (genreE2 0) 2 0 4` — genre E at `t = 0`, `stageWindow = 2`,
`stageLoss = entryCodim = slack = 0`, the `EFF.GENIND.199` entry exemption, all eleven fields
proved — at which that display evaluates to `4 ≥ 8`, checked by `decide`; an independent external
sweep finds **29,418 counterexamples among 2,777,911 admissible configurations**. Signing it would
have made the stub file's axiom set inconsistent (`rate_lossPriced stageIfaceE` proves `False`), so
the stub was **withdrawn, not signed**, and the blueprint's SIGNATURE was repaired in place.

**The diagnosis: a `2*`-clearing error on five of the seven terms.** Every half-integer quantity in
`(C2Q.1)` — the supporting-line price `b_S = (S+1)/2` (H.32/H.33's licence) and the `H/2` — must be
cleared *once* by the global `×2`. The committed display multiplied `(S+1)*H`, `entryCodim`, both
`keyDeg` terms and `slack` by `2` a **second** time while leaving the window term `2*(f₁*M_G)` and
the lone `+H` single — an inhomogeneous clearing, hence false. Truncation was a secondary defect
(the committed docstring claimed the inequality was "stated over `ℤ`", which was false of the type:
every term was `ℕ`, so the trailing `- 2*(2*I.slack)` truncated), but it is *not* the cause — the
sweep with the slack moved left fails at exactly the same 29,418 points.

**The repair landed here is the gate's CANDIDATE A**, re-derived term for term from
`EFF.GENIND.198`'s `(C2Q.1)` chain (the PROOF steps below), verified with **zero** counterexamples
over the same admissible sweep, and tight (`4 ≥ 4`) at `stageIfaceE`, as an entry-exemption
instance should be. CANDIDATE B (Candidate A uniformly doubled) is also counterexample-free but is
a clearing by `4`, not the corpus's by-`2` form, and was rejected as unfaithful to H.33's licence.

## ⚠ SIGNATURE NOTE — READ BEFORE CLAIMING

The displayed inequality is the **exponent bookkeeping** of `(C2Q.1)`, cleared of every division
and stated in `ℕ` with the slack cleared to the LEFT so that `ℕ` cannot truncate it. It is
**deliberately not** the real-analytic product bound: that bound needs `ρ` and `δ` as hypotheses
with three further nonnegativity side conditions, while the content of the corpus's proof is the
exponent algebra (its own audit: *"Multiplying: exponent `= −b_S H − C_extra − a(N−1−H) + γΔ_G +
O(1) = −a(N−1) − (b_S − a)H − C_extra + γΔ_G + O(1)` ✓ as displayed. Applying (CS-1Q.b): the
exponent `≤ −a(N−1) − H/2 + O(1)` ✓ **exact**"*). In the display: `(S+1)*H` is `2·b_S·H` (H.32's
supporting-line sum at the actual side length, consumed **once**, not doubled) and the lone `+H` is
the cleared `H/2`. A re-derivation that disagrees with this display is a stop-the-line event.

## ⚠ The hypothesis is not stronger than the use — a design virtue the spec names

`EFF.GENIND.197`'s audit: *"(CS-1Q.b) is exactly the inequality C2Q's algebra requires, no more and
no less. That is a design virtue: the hypothesis is not stronger than the use."* H.09's
`StageInterface.hprice` is stated at exactly that strength, and this node is the proof that
consumes it. **The floor-adjacent branch** (`M_G < M₀`, where the quantitative stage estimate is not
invoked and the trivial bound `δ ≤ 1` carries) is `EFF.GENIND.198`'s second half and is *not* a
separate statement: it is H.68's `rate_bounded` applied with the entry price in place of the route
prefactor, assembled by the caller.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`, `GenreDatum.sideLen`), H.09
(`StageInterface`, fields `hS`/`hwin`/`hprice`), H.33 (`two_mul_a_le_S`, the `2a ≤ S` domination
that makes `hprice`'s `(S − 2·keyDeg)` factor honest), H.32 (the supporting-line sum `2·Σ_{r<S}
(r+1)H = S(S+1)H`, whose per-height price `(S+1)H` is the second summand of the display; consumed
here as the shape of that term, not as a rewrite).

PROOF (the repaired chain; steps 3–5 are the ones A-H.1/D4 re-derived):
1. from `I.hwin` (`(CS-1Q.a)`), multiplied by `f₁`: `a(N−1−H) ≤ f₁·M_G + f₁·Δ_G` with
   `a = keyDeg = e₁f₁`;
2. from `I.hprice` (`(CS-1Q.b)`): `2(f₁·Δ_G) ≤ 2C + (S − 2a)H + 2·O`, whose `(S − 2a)` factor is
   honest because `2a ≤ S` (H.33, from `I.hS` and `G.hmul`);
3. double 1 and chain 2: `2a(N−1−H) ≤ 2(f₁·M_G) + 2C + (S − 2a)H + 2·O`;
4. add `2aH` to both sides, using `(S − 2a)H + 2aH = SH` (honest by step 2's `2a ≤ S`);
5. add `H` to both sides, using `SH + H = (S+1)H`.

SOURCE: `EFF.GENIND.198` (`ANNEX-LEMMA GENIND-C2Q`, statement `(C2Q.1)` with its proof quoted in
full, and the corrected entry count `(C2Q.2)` from `C2-G3`), with that spec's audit: *"**the C2Q
proof is correct and every step re-derives.** It is CLEANER than `.189`'s, because the hypothesis
was reverse-engineered from the algebra."*; `EFF.GENIND.197` (`(CS-1Q.a)`/`(CS-1Q.b)`);
`EFF.GENIND.204` (`C2-G3`'s `(C2E.1)`–`(C2E.3)`).

TEETH: **NONE** (`EFF.GENIND.198`: *"No machine leg was added at R11 … Disposition: `signed vacuity
disclosure` — the lemma is proved and unexercised, and its hypothesis is per-genre unverified"*) →
**Lean theorem** for the exponent algebra; the per-genre verification of the hypothesis stays
`HYP.36`, CARRY (honesty item H-2). **This is the exact place where the capstone's conditionality
enters the Lean development.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **(C2Q.1)** — the loss-priced stage-drain exponent, in the `2*`-cleared form. Stated in `ℕ`
with the slack cleared to the LEFT, so no truncating `-` appears anywhere in the display (the
committed form's trailing `- 2 * (2 * I.slack)` did truncate, and its docstring's "stated over `ℤ`"
claim was false of the type — see AMENDMENT §A-H.1/D4). -/
theorem rate_lossPriced {G : GenreDatum} {N H S : ℕ} (I : StageInterface G N H S) :
    2 * (G.f₁ * I.stageWindow) + (S + 1) * H + 2 * I.entryCodim + 2 * I.slack
      ≥ 2 * G.keyDeg * (N - 1 - H) + 2 * G.keyDeg * H + H := by
  -- H.33 at the actual side length: `2a ≤ S`, so `hprice`'s `(S − 2·keyDeg)` factor is honest.
  have hSa : 2 * G.keyDeg ≤ S := by
    have h := two_mul_a_le_S (e := G.e₁) (f := G.f₁) (m := G.μ) (S := S) G.hmul I.hS
    simpa [GenreDatum.keyDeg] using h
  -- Steps 1 and 3: `hwin` multiplied by `f₁` and doubled.
  have h1 : 2 * G.keyDeg * (N - 1 - H)
      ≤ 2 * (G.f₁ * I.stageWindow) + 2 * (G.f₁ * I.stageLoss) := by
    calc 2 * G.keyDeg * (N - 1 - H)
        = 2 * G.f₁ * (G.e₁ * (N - 1 - H)) := by
          simp only [GenreDatum.keyDeg]; ring
      _ ≤ 2 * G.f₁ * (I.stageWindow + I.stageLoss) := Nat.mul_le_mul_left _ I.hwin
      _ = 2 * (G.f₁ * I.stageWindow) + 2 * (G.f₁ * I.stageLoss) := by ring
  -- Step 4: `(S − 2a)H + 2aH = SH`, honest by `hSa`.
  have hsplit : (S - 2 * G.keyDeg) * H + 2 * G.keyDeg * H = S * H := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hSa]
  -- Step 5: `SH + H = (S+1)H`, H.32's supporting-line price consumed ONCE.
  have hSH : (S + 1) * H = S * H + H := by ring
  have hprice := I.hprice
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.rate_lossPriced

end AxCheck
