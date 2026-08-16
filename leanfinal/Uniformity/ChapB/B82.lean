/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B78
import Uniformity.ChapB.B79b
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapB.B82 — the single-key certificate: §9's capstone and the §10 gates' engine

**Chapter B, NODE B.82** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C. One signed
declaration. **⚠ THE CRITICAL PATH ENDS HERE** (§2: `… → B.58 → B.63 → B.79 → B.82`).

*The statement.* Let `a : Fin n → O` with `0 < n`, write `f := monicPoly a`, and let `φ` be an
order-1 key with `f‾ = (φ‾) ^ μ`, `0 < μ` (one block, no peel). Under R8-1's two clauses on `f`
itself (`Visible π φ f N`, `¬ NeedsDescent π φ f`) and the perimeter:

```
DecidedAt O n (order1Type π φ f) N (proj O n N a)
```

This is the general-`(O, n, q, N)` statement of which the landed `leancheck` suite
(`UniformityCheck/N3CertRam.lean`, `N3CertLinRam.lean`, `N3InertExact.lean`, …) is the hand-cased
`n = 3` instance layer, and it is the node the §10 gates fire — a `q = 2` and a `q = 3` instance
with `e > 1` **and** `f > 1` is a `(u,ℓ)`-leaf with `ℓ ≥ 2` on a key of degree `m ≥ 2`, `d = 1`,
i.e. inside D-3's unconditional perimeter, so the gates carry **no** `B-BOX-1` hypothesis.

## `hperim` is the window-class closure at `(φ, monicPoly a, N)` — the A-F.12 re-sign, and why

R8-1's two clauses stay on `f` itself: they transport (B.74/B.76/B.77 carry `Visible` and
`NeedsDescent` across a level-`N` congruence). `hperim` does **not** transport — it quantifies
over the monic divisors of the polynomial and its third disjunct speaks about `inertiaDegOf` of
their monic factors, and no congruence-invariance for those exists. Since this node fires B.79(b)
at `g' := monicPoly b` for an arbitrary lift `b` bound *inside* landed `decidedAt_of_congr`, and
B.79(b)'s own clause was re-signed at the lift, the perimeter must be signed over `f`'s level-`N`
window class (§12 item 4's display (4a″) at `(φ, monicPoly a, N)`). Reflexivity
(`gT := monicPoly a`, `π ^ N ∣ 0`) recovers the clause at `f` itself, so the frozen form is
implied and no consumer loses anything.

The §10 gates keep their `B-BOX-1`-free status: their discharge becomes uniform in the class
member by the degree bound `ℓ · φ.natDegree · ψ.natDegree = gS.natDegree ≤ n` (B.30's
`natDegree_resPoly` plus landed B.35b `sideDeg_of_pure`), displayed at B.83's PROOF step 6.

## Proof — the blueprint's three legs

1. Enter through landed `decidedAt_of_congr`: fix `b` with `π ^ N ∣ (b i - a i)` for all `i`;
   it remains to show `typeOf (monicPoly b) = order1Type π φ (monicPoly a)`.
2. B.78(i) `monicPoly_congr` turns the vector congruence into
   `π ^ N ∣ (monicPoly a - monicPoly b).coeff j`; `monicPoly b` is monic of the same degree `n`
   (landed `monicPoly_monic`, `monicPoly_natDegree`).
3. B.79(b) with `hvis`, `hterm` and `hperim` instantiated at `gT := monicPoly b` — monicity and
   the degree pin are step 2's landed facts, the congruence is step 2's B.78(i).

DEPENDS (direct): B.66 (`order1Type`) · B.75 (`Visible`) · B.78(i) (`monicPoly_congr`) · B.79(b)
(`typeOf_congr_of_certificate`) · landed `Uniformity.Density.decidedAt_of_congr`,
`Uniformity.Density.monicPoly_monic`, `Uniformity.Density.monicPoly_natDegree`.

**SIZE.** blueprint 26 lines; landed 11 — the node is deliberately **thin**: all mathematics is
upstream, so the §10 gate agents (which instantiate `O`, `q`, `a`, `φ` concretely and must also
*evaluate* `Visible`/`NeedsDescent`/`order1Type` on their instance) inherit no proof burden beyond
the evaluation. Gate calibration: `N3CertRam.lean`'s CASE R (`π² ∣ B₀, π³ ∤ B₀, π² ∣ B₁, π ∣ B₂`
⟹ `typeOf = {(3,1)}`) is this node at `n = 3, φ = X, μ = 3, (u,ℓ) = (2,3), d = 1, N = 3` — proved
there by hand without polygons; the gates must fire **this** node, not re-case.

**⚠ FULL-GENERALITY CLAIM, DELIMITED.** "In full generality" means: general complete-DVR `O` in
both characteristics, every degree `n`, every key degree `m`, every window `N`, every slope, every
residual degree — with exactly two carried conditionalities, both named: `B-BOX-1` inside
`hperim` at `ℓ ≥ 2 ∧ d ≥ 2` (H-7), and order-1-ness itself (`hterm`; the descent/recursion layer
is chapter C's, D-4(c)). Nothing else is scoped: no `n ≤ 3`, no `q`-list, no
mixed-characteristic pin.

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad) → **Lean theorem** inside the perimeter;
`W12-ORACLE` (0 / 41,923) → **executable regression** retained (PARI stays the independent
engine, per B.58's precedent); `HE-BND` (RE-SCOPED) → **executable regression** per D-4(c); the
`σ(λ)` dictionary of `EFF.W12.29` — B.71's instance table — is checked at the gates through this
node (two rows: the `e = 2` and `e = 3` sides with degree-`≥ 2` keys).

SOURCE: `EFF.W12.27` (the certification clause, at D-4(a)'s stronger quantifier); `EFF.HE3.67`
(R8-1, delivered on `leanfinal`'s `DecidedAt` per H-4's line-221 commitment);
`leancheck/UniformityCheck/N3CertRam.lean` and siblings (`notes/N3_CHECK_2026-08-13.md` §13).

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through B.79(b) ← B.79(a) ←
B.63 — the 2026-08-16 owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `hn : 0 < n` is part of the frozen signature and is not consumed by the proof (this node needs
-- no nonempty-block argument — B.80's step 1 did): the certificate is uniform in `n`, and at
-- `n = 0` it degenerates harmlessly. The binder is KEPT so that the landed form matches the stub
-- (`leanspec/Leanspec/ChapB.lean`, **B.82**); only the linter is silenced.
set_option linter.unusedVariables false in
/-- **B.82 — the single-key certificate.** A terminating, visible order-1 read of `monicPoly a`
at one key, inside D-3's perimeter, decides the whole level-`N` class of `a` at B.66's order-1
datum. `hperim` is signed over the level-`N` **window class** of `monicPoly a` (amendment
A-F.12). This is §9's capstone and the engine the §10 gates fire. -/
theorem decidedAt_of_leaf_certificate (hπ : Irreducible π) {n N : ℕ} (hn : 0 < n)
    (a : Fin n → O) {φ : Polynomial O} (hφ : IsKey φ) {μ : ℕ} (hμ : 0 < μ)
    (hres : (Uniformity.Density.monicPoly a).map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hvis : Visible π φ (Uniformity.Density.monicPoly a) N)
    (hterm : ¬ NeedsDescent π φ (Uniformity.Density.monicPoly a))
    -- [re-signed: A-F.12] the window-class closure at `(φ, monicPoly a, N)` — §12 item 4 (4a″)
    (hperim : ∀ gT : Polynomial O, gT.Monic →
      gT.natDegree = (Uniformity.Density.monicPoly a).natDegree →
      (∀ k, π ^ N ∣ ((Uniformity.Density.monicPoly a) - gT).coeff k) →
      ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ gT →
        IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g'' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g'')) :
    Uniformity.Density.DecidedAt O n (order1Type π φ (Uniformity.Density.monicPoly a)) N
      (Uniformity.Density.proj O n N a) := by
  -- ## step 1 — enter through the landed certificate/census interface
  refine Uniformity.Density.decidedAt_of_congr hπ ?_
  intro b hb
  -- ## step 2 — the lift is monic of the same degree, and congruent at level `N`
  have hcong : ∀ j, π ^ N ∣
      (Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b).coeff j :=
    monicPoly_congr (fun i => dvd_sub_comm.1 (hb i))
  have hdeg : (Uniformity.Density.monicPoly b).natDegree
      = (Uniformity.Density.monicPoly a).natDegree := by
    rw [Uniformity.Density.monicPoly_natDegree, Uniformity.Density.monicPoly_natDegree]
  -- ## step 3 — B.79(b), the closure instantiated at `gT := monicPoly b`
  exact typeOf_congr_of_certificate hπ hφ (Uniformity.Density.monicPoly_monic a) hμ hres hterm
    hvis (Uniformity.Density.monicPoly_monic b) hdeg hcong
    (hperim (Uniformity.Density.monicPoly b) (Uniformity.Density.monicPoly_monic b) hdeg hcong)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.decidedAt_of_leaf_certificate
end AxCheck
