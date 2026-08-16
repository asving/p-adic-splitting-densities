/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D07
import Uniformity.ChapD.D08
import Uniformity.ChapD.D12

/-!
# Uniformity.ChapD.D39 — `compData`, the two-section comparison data `(ρ, ρ̂, δ)`

**Chapter D, NODE D.39** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, the telescope
port (T3); amendments A-1, A-D.1, A-D.2 govern — this node's SIGNATURE was **RE-SIGNED at
A-D.1/D-D3 with a REAL BODY**: the originally-signed row stopped at its type, and the body
needs two names the original text used unquoted or not at all). ENV-D2 + ENV-D3. Three signed
declarations, all landed with the A-D.1 bodies.

*The two-section comparison data.* Fix an arena `A : GaugeArena G K N` and a SECOND normalized
exact-height section `N̂` for the SAME height hom — `hNhat : ∀ k, A.v (N̂.n k) = ofAdd k`, which
is `EFF.T3.12`'s "two normalized exact-height sections on the same set of heights". Then:

* `chiK k := A.res ⟨chi N̂ N k, _⟩ : Kˣ` — the `K`-valued section ratio; membership because the
  two heights CANCEL (`A.v (N̂.n k) = ofAdd k = A.v (N.n k)`), which is D.08's `mem_ker_div`;
* `δ := chiK q`, the value at the ladder step (`EFF.T3.13`'s `δ = χ(q)`);
* for descent data `H₀ q : ℤ`, `D : ℕ` and coefficients `Acoef : Fin (D+1) → G` at the exact
  heights `H_t = H₀ − t·q` (`hA`), the two assembled families
  `ρ_t := A.res ⟨A_t·N(q)^t·N(H₀)⁻¹, _⟩` and `ρ̂_t := A.res ⟨A_t·N̂(q)^t·N̂(H₀)⁻¹, _⟩`.

`compData` packages exactly `(ρ, ρ̂, δ)`.

## `EFF.T3.13`'s height-zero clause is the PROVED sibling, not an assumption

*"All displayed residual quotients have height zero."* That sentence is `rho_mem_ker` below,
and it is a **theorem**, because `compData`'s body applies `A.res` to those quotients and
therefore cannot be written without it. Its computation is one line: `v` is a hom, so

`v(A_t · M(q)^t · M(H₀)⁻¹) = ofAdd (H₀ − t·q) · ofAdd(q)^t · ofAdd(H₀)⁻¹ = ofAdd 0 = 1`,

for EITHER section `M ∈ {N, N̂}` — which is why the lemma is stated over a general `M` with its
own exact-height hypothesis `hM`, and is then applied twice: at `M := N` with `A.exact_height`
(the arena's own field) and at `M := N̂` with `hNhat`.

## Why this is a FRAGILE signature (A-D.1/D-D3), and how it is discharged

`compData` puts kernel-membership PROOF TERMS inside a `def` body. §12 rule 1 makes such
signatures elaborate first, and §12 rule 2 forbids the two shortcuts that would otherwise be
tempting:

1. **no tactic holes** — the membership arguments are applications of the PUBLIC lemmas
   `GaugeArena.mem_ker_div` (D.08) and `GaugeArena.rho_mem_ker` (here), spelled out;
2. **no `axiom`** — an `axiom` inside a `def` body would put a stub in the def layer, which
   D.68(iv)'s census treats as a stop-the-line event. The def layer of chapter D is
   axiom-clean apart from D.17's one licensed definitional dependency.

`GaugeArena.chiK` is itself a **NEW public name** signed at A-D.1/SD-3: the blueprint's text
used `chiK` unquoted in D.40's `(chiK-of-H₀-term)`, and §12 rule 5 explicitly left its spelling
to stub time. This is that spelling, transcribed unchanged; D.40 consumes it by name.

## Faithfulness

Two readings, both the blueprint's own and both visible in the types:

1. **`δ` is `chiK q`, the third component**, so the packaging is `(ρ, ρ̂, δ)` and NOT
   `(ρ, ρ̂, χ)`: only the ladder-step value is packaged, while `χ(H₀)` — the other value D.40
   needs — is obtained by calling `A.chiK Nhat hNhat H₀` at the consumer. That asymmetry is
   `EFF.T3.13`'s, not an editorial choice.
2. **The two polynomials `R(Z) = Σ_t ρ_t Z^t` and `R̂(Z)` get NO public name.** They are formed
   as `∑ t, C ((ρ t : K)) * X ^ (t : ℕ)` shapes at the consumer (D.40's polynomial leg), exactly
   as the A-D.1 SIGNATURE comment directs — so nothing here fixes a polynomial-ring convention
   that D.40 would then have to match.

⚠ **direction of `chi`** (D.12, inherited): `chi Nhat N k = n̂(k)·(n(k))⁻¹`, HATTED section
first. `chiK` therefore measures `N̂` against `N`, the arena's own section, in that order.

**Flagged for human review** (definition faithfulness), per the repo trust boundary.

DEPENDS: D.01 (`NormSection`, reaching this file through D.07) · D.07 (`GaugeArena`) · D.08
(`GaugeArena.mem_ker_div` — the A-D.1 addition to this node's DEPENDS field, since the body
applies it) · D.12 (`NormSection.chi`) · mathlib `MonoidHom.ker`, `MonoidHom.mem_ker`,
`map_mul`, `map_inv`, `map_pow`, `ofAdd_nsmul`. No other landed node.

**PROOF.** definitional; the three membership facts are `map_mul`/`map_pow`/`map_inv` plus
`hNhat`/`hA`/`exact_height` and an exponent cancellation (`H₀ − t·q + t·q − H₀ = 0`).

SOURCE: `EFF.T3.12` (`χ`, `δ`, and the renaming fence that turned HETOW's `τ` into `χ`),
`EFF.T3.13` (`H_t = H₀ − tq`, `ρ_t`, `ρ̂_t`, `R(Z)`, `R̂(Z)`, `δ = χ(q)`, and the height-zero
clause).

**TEETH.** T3 §8.2 (the port frames) → gate **D.67** instantiates this data at FRAME-C's
`p = 5` tables; the def-layer axiom census is D.68(iv), where `GaugeArena.chiK` and
`GaugeArena.rho_mem_ker` are two of the named lines.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written
inline per the B.42 binder rule — this file has no `variable` block; the A-D.1/D-D7-class
spelling riders are in force, so `hNhat`'s and `hA`'s binders carry their types and the
exponent is cast `(t : ℕ) * q`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.39 — the `K`-valued section ratio `χ`** (`EFF.T3.12`).  `chiK k = res(n̂(k)/n(k))`,
where `N̂` is a SECOND normalized exact-height section for the same height hom; the membership
holds because the two heights cancel (D.08's `mem_ker_div`).  `δ := chiK q`.

[A-D.1/SD-3: a NEW public name — the blueprint's `chiK`, used unquoted in D.40's
`(chiK-of-H₀-term)`; §12 rule 5 left its spelling to stub time and THIS is the spelling.]

⚠ direction (D.12): `chi Nhat N k = n̂(k)·(n(k))⁻¹`, hatted section FIRST. -/
noncomputable def GaugeArena.chiK {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k) (k : ℤ) : Kˣ :=
  A.res ⟨NormSection.chi Nhat N k, A.mem_ker_div ((hNhat k).trans (A.exact_height k).symm)⟩

/-- **D.39 — the height-zero fact** (`EFF.T3.13`: "All displayed residual quotients have height
zero").  PROVED, never an `axiom`: `compData`'s body applies `A.res` to these quotients inside a
`def`, so the fact must be available as a term.  Stated over a GENERAL section `M` with its own
exact-height hypothesis, because it is applied twice — at `M := N` with the arena's
`exact_height`, and at `M := N̂` with `hNhat`. -/
theorem GaugeArena.rho_mem_ker {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (M : NormSection G)
    (hM : ∀ k : ℤ, A.v (M.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (t : ℕ) {x : G} (hx : A.v x = Multiplicative.ofAdd (H₀ - t * q)) :
    x * (M.n q) ^ t * (M.n H₀)⁻¹ ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_pow, hx, hM, hM, ← ofAdd_nsmul]
  simp

/-- **D.39 — the two-section comparison data `(ρ, ρ̂, δ)`** (`EFF.T3.12`, `EFF.T3.13`).

`ρ_t = res(A_t·N(q)^t·N(H₀)⁻¹)` and `ρ̂_t = res(A_t·N̂(q)^t·N̂(H₀)⁻¹)` for coefficients `A_t` at
the exact heights `H_t = H₀ − t·q`, together with `δ = χ(q)`.

The two polynomials `R(Z) = Σ_t ρ_t Z^t`, `R̂(Z) = Σ_t ρ̂_t Z^t` are formed as
`∑ t, C ((ρ t : K)) * X ^ (t : ℕ)` shapes AT THE CONSUMERS (D.40) — no separate public name.
`χ(H₀)`, D.40's other ingredient, is likewise obtained by calling `A.chiK Nhat hNhat H₀`: only
`δ` is packaged here, per `EFF.T3.13`. -/
noncomputable def compData {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q)) :
    (Fin (D + 1) → Kˣ) × (Fin (D + 1) → Kˣ) × Kˣ :=
  (fun t => A.res ⟨Acoef t * (N.n q) ^ (t : ℕ) * (N.n H₀)⁻¹,
      A.rho_mem_ker N A.exact_height H₀ q (t : ℕ) (hA t)⟩,
   fun t => A.res ⟨Acoef t * (Nhat.n q) ^ (t : ℕ) * (Nhat.n H₀)⁻¹,
      A.rho_mem_ker Nhat hNhat H₀ q (t : ℕ) (hA t)⟩,
   A.chiK Nhat hNhat q)

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.chiK
#print axioms Uniformity.Density.Gauge.GaugeArena.rho_mem_ker
#print axioms Uniformity.Density.Gauge.compData

end AxCheck
