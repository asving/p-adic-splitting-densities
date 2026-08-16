/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D43 — `(ABS-HE4)`: the HETOW comparison discharge

**Chapter D, NODE D.43** [interface] [fresh — GC-13 placeholders]
(`blueprint/CHAP-D_gauge_tchain.md` §6, the telescope port (T3); amendments A-1 and A-D.1
govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag, so the composed text is
its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none in chapter
D (same rationale as D.42)` — i.e. "the conclusion is [the landed chapter-D lemmas] applied to
C's instance; a D-side alias theorem would duplicate a name across the chapter boundary" —
together with `PROOF. n/a`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`. §12 rule 4 is the reason
and it is mandatory: **"No stub for another chapter's placeholder: the `[supplied-by: chapter C]`
rows are NOT axiomatized in leanspec (axiomatizing a supplier's theorem would fake the
discharge — exactly the class of defect the honesty items fence). Held at the gate: D.42, D.43,
D.53, D.54, D.56 and D.61 declare nothing, and no chapter-C/E/F node ID is guessed."** The
stage-0e stub gate held that line, and this landed copy holds it: the file **imports nothing and
defines nothing**, so no `EFF.HETOW` fact acquires a Lean name here and this node can never
become a silent dependency of a proof.

What the node *is*, then, is the absorption record for T3's §4: which chapter-D objects the
HETOW instance binds, which of HETOW-4's components chapter D supplies *in full*, which stay with
the supplier, and which fences travel along. That record is transcribed below.

## The instantiation dictionary (`EFF.T3.20`)

| T3 datum | HETOW binding |
|---|---|
| the unhatted section | `N = n₂` |
| the hatted section | `N̂ = n̂₂` |
| the comparison character | `τ_H = chiK` — **"T3's χ, not T1's two-variable cocycle"** |
| the step height | `q = u₃` |
| the substitution scalar | `δ = τ_H(u₃)` |
| the coefficient heights | `H_t = H₀ − t·u₃` |

HETOW's assembled coefficients instantiate **D.39's** data (`Uniformity.ChapD.D39`, landed and
green: `GaugeArena.chiK` is `τ_H`, `GaugeArena.rho_mem_ker` is the height-zero fact, and
`compData` packages `(ρ, ρ̂, δ)` at exactly the heights `H_t = H₀ − t·q`), and **D.40/D.41**
supply `(ABS-HE4)`'s displays:

* `ρ_t = ρ̂_t · τ_H(H₀) · δ^{−t}` — D.40's coefficient leg, `compData_cmp`;
* `R_{λ₂}(Z) = τ_H(H₀) · R̂_{λ₂}(Z/δ)` — D.40's polynomial leg, `compData_cmp_poly`;
* the monic-factor and root routing — D.41's `t3_route`, `t3_route_roots`, with the rationality
  clause `t3_route_map`;

plus `(HE4-COB)` = **D.12's** instance (`NormSection.chi_coboundary`, the coboundary law
`χ(a)χ(b)χ(a+b)⁻¹ = τ̂(a,b)·τ(a,b)⁻¹`).

## ⚠ The fence: no character law for `τ_H` is asserted

`EFF.T3.20` carries it, and D.12's landed file already enforces it with a machine-checked
witness: *"NO character law for `χ` is asserted anywhere: `χ` is a character precisely when the
two cocycles agree, and the executed witness at the foot of this file exhibits a pair where they
do not"* — `χ(1)·χ(1) = 1` while `χ(2) ≠ 1` in the ENV-D2 shadow of FRAME-C. Every display above
is therefore stated through the coboundary law, never through multiplicativity of `τ_H`. This is
the T3 §8.4(1) character mutant's kill site (D.12 + gate D.67).

## The absorption boundary table, transcribed verbatim

Each row is a supply or a fence; chapter C's HETOW transcription cites this table.

| HETOW-4 component | status |
|---|---|
| clause (a), `τ_H(k) = η^{−Q(m(k))}` | source-specific ladder arithmetic; NOT supplied by T3/D — the level-1 shape is D.19 + D.27's carry leg, the bridge is `EFF.HETOW [supplied-by: chapter C]` |
| clause (b), coboundary-comparison shape | supplied by D.12 (`(T3-COB)`) |
| clause (b), explicit two-floor exponent | obtained after substituting HETOW's floor arithmetic — supplier-side |
| clause (c), coefficient telescope + polynomial rescaling | fully supplied by D.11 (`(T3-BKT)`) + D.40 (`(T3-CMP)`) |
| clause (d), separability/factor/root routing | fully supplied by D.41 (`(T3-ROUTE)`) |
| common polynomial lift and later iterate independence | remain on HETOW-4's lift and finite-chain inputs — supplier-side |

In landed Lean names, all in `Uniformity.Density.Gauge` and all green at HEAD: `(T3-BKT)` is
`NormSection.tau_bracket_telescope` (D.11); `(T3-COB)` is `NormSection.chi_coboundary` (D.12);
`(T3-CMP)` is `compData_cmp` / `compData_cmp_poly` (D.40); `(T3-ROUTE)` is `t3_route`,
`t3_route_roots`, `t3_route_map` (D.41). The two "supplier-side" rows and clause (a) have **no**
chapter-D name, by design.

## The supplier interface, and where it is already recorded

`EFF.HETOW [supplied-by: chapter C]` is the bridge: the level-two relation
`n̂₂(k)/n₂(k) = n̂(m(k))/ϖ^{m(k)}`, the function `m`, the range `0 ≤ s(a) < e₂`, the binary carry
`c₂ᴴᴱᵀ = ⌊(s(k)+s(k′))/e₂⌋ ∈ {0,1}`, and the identification of `τ` — i.e. `(H-HETOW-LOCAL)`'s
fields, "external and essential". Chapter D does **not** state it; D.27 (`qexp_binary_carry`,
landed) is D's side of the A2/HETOW consumption check, and D.27's own non-import sentence is the
companion of this table: *"T1 does not absorb HETOW-4(c)–(d). The side-assembly brackets,
telescoping coefficient identity, side-letter equality, routing transport, and common refinement
polynomial remain HETOW/HE7 supplier conclusions."* Note the seam that sentence marks: what T1
does not absorb, **T3 does** for clauses (c)–(d) — that is precisely the two "fully supplied"
rows above — while the assembly and the lift stay with HETOW.

## Reading notes for a consumer

* **Chapter D discharges nothing on the supplier's side of the table.** A chapter-D declaration
  that appears to prove clause (a), the two-floor exponent, or the common lift has found a
  defect, not a discharge.
* **The four supplied rows are unconditional chapter-D theorems**, and they are unconditional
  *at frame level*: they are statements about any two normalizer sections and any comparison
  data. Instantiating them at HETOW's assembled coefficients is C's step, and it is the step
  that carries `(H-HETOW-LOCAL)`.
* **`τ_H` is `chiK`, one argument.** Any consumer that reaches for `NormSection.tau` (the
  two-variable cocycle) at this instance has confused T1's object with T3's; the renaming is the
  spec's own, recorded at D.12.

**DEPENDS.** D.11, D.12, D.39, D.40, D.41 · `EFF.HETOW [supplied-by: chapter C]` (the bridge,
`m`, the `τ` identification — `(H-HETOW-LOCAL)`'s fields; see D.27).

**SOURCE.** `EFF.T3.20` (the `(ABS-HE4)` displays, `(HE4-COB)`, the "No character law for `τ_H`
is asserted" fence, and the verbatim absorption-boundary table).

**TEETH.** T3 §8.3(2) → executable regression retained; §8.4(1) character mutant → D.12 + gate
D.67. The §13 routing row reads T3 §8.3(2) (HETOW-4) as "**Lean theorem** (D.11/D.40/D.41) +
D.43's boundary table" — this file is that boundary table.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
