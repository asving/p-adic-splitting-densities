/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D37
import Uniformity.ChapD.D38

/-!
# Uniformity.ChapD.D44 — `GentowW`, the `[GENTOW5-W(i)]` carrier, and `(ABS-G5W)`

**Chapter D, NODE D.44** [def+theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, the
telescope port (T3); amendments A-1, A-D.1, A-D.2 govern — none of them re-signs this node, so
the SIGNATURE below is the composition-time one, re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`). ENV-D2 + ENV-D3. Two signed declarations.

*(i) The sitewise B-law predicate.*

`GentowW A q R w := ∀ s : ℕ, R (N.n (s·q)) = (A.theta q s : K)·(w : K)^s`

— "the sitewise B-law holds for the level's read data". The corpus's `[GENTOW5-W(i)]` is this
predicate AT chapter C's level-`i` tower instantiation (arena + FGMN read + `w_i`); chapters
C/E/I consume the NAME `GentowW` with their own instances (the GC-13 resolution wires
`EFF.T3.21`'s `θ_i(t) = Θ_N(s;u_{i+1})`, `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))` data).

*(ii) `(ABS-G5W)`, the derivation theorem.* A family of boundary-read ports at every `s` yields
the predicate: "The certified level-`i` expansion, peel, positive-degree elimination, exact-grade
law, and root-evaluation package instantiate (BR1)–(BR5). Hence `[GENTOW5-W(i)]`."

## What this node does NOT do (the fence, transcribed)

**Nothing here discharges any instance.** `gentowW_of_ports` converts a supplied port family into
the predicate; it does not build ports, and chapter D never exhibits a level-`i` port family for
`i ≥ 3`. The instance boundary is the corpus's own:

* at `i = 2` the discharge is the landed GENTOW2-B″ instance (D.42, `(ABS-G2)`) — an
  `[interface]` node with NO Lean declaration in chapter D, because axiomatizing a supplier's
  theorem would fake the discharge (§12 rule 4);
* at `i = 1` "the residual remains GENTOW5 S11.3's fixed `z₁`-letter-power statement; T3 does not
  identify that unit with a displayed `w₁`" — the `ω₁`/OPEN-2 fence (§8), carried by D.59/D.61;
* at `i ≥ 3` the conditionality is carried by D.60/D.62/D.65, not by this file.

The SUPPLY STATUS is transcribed verbatim from `EFF.T3.21`: "SUPPLIED by T3-A0 and §7;
consumption check + dated append outstanding." The GENTOW5_WI §S2 span is
`PERIMETER-UNRESOLVED` in T3's own XREF (X18), so the port-family hypothesis is the blueprint's
exact rendering of "the certified … package"; the perimeter resolution is
`EFF.GENTOW5 [supplied-by: chapter C]` (T3 §8 deferred obligation 1), and D.64's routing table
carries that row.

## Faithfulness (trust boundary — this node introduces a public DEFINITION)

1. **The predicate is stated in the exponent `s`,** matching D.08's two-index telescope and
   D.37/D.38's port index. The corpus displays `(ABS-G5W)` as `u_i(β_t) = θ_i(t)·w_i^{f_{i+1}−t}`;
   consumers reindex by `s = f_{i+1} − t` (this is the D.06 row-1/row-4 reflection, and it is why
   gate D.67's leg 4 has to score the reflection numerically — see ORIENTATION below).
2. **The read is an arbitrary function `R : G → K`,** evaluated only at the ladder points
   `N.n (s·q)`. Nothing constrains `R` off the ladder, and nothing here asserts that `R` is a
   residue read of anything: that is the instantiating supplier's obligation.
3. **The unit `w : Kˣ`** is the peel unit, typed as a unit exactly as at D.29/D.37 (D-H6), so the
   predicate never divides and never incurs a `w ≠ 0` side condition.

DEPENDS: D.37 (`BoundaryReadPort`) · D.38 (`BoundaryReadPort.t3_br`, the telescope endpoint) ·
D.08 (`GaugeArena.theta`) and D.01 (`NormSection`), reaching this file through those two. No
mathlib lemma beyond the `rw` chain.

**PROOF.** per `s`: destructure the supplied port, rewrite with D.38. The hypothesis pins the
port's `U` to the read at `N.n (s·q)` and its `w` to the given unit, so D.38's conclusion
`U = Θ_N(s;q)·w^s` IS the predicate's clause at `s`.

SOURCE: `EFF.T3.21` (the `(ABS-G5W)` display `u_i(β_t) = θ_i(t)w_i^{f_{i+1}−t}` at `i ≥ 3`, its
BR-instantiation derivation, the `i = 2`/`i = 1` boundary sentences, and the SUPPLY STATUS line).

**ORIENTATION.** `A.theta` — the B-law orientation (D.06 rows 2–3; the corpus's `θ_i(t)`), NOT
`A.vartheta`. A swap would have to falsify D.10's involution to typecheck through D.38, and gate
D.67 scores the numerical distinctness of the two orientations at FRAME-C.

**TEETH.** T3 §8.3(3), §8.4(2)–(4) → **Lean theorem** (the derivation, this node); §8.3(4) (the
conditionality) → D.60/D.62/D.65 carry it. D.68's census `#print axioms`-es
`gentowW_of_ports` and `#check`s `GentowW` at its stated type as one of the six carriers
chapters E and I consume by name.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written
inline per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only): `gentowW_of_ports` is PROVED here, not the leanspec
`axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.44 — the sitewise B-law predicate** whose level-`i` tower instance is `[GENTOW5-W(i)]`
(`EFF.T3.21`).  SUPPLY STATUS transcribed: "SUPPLIED by T3-A0 and §7; consumption check + dated
append outstanding."

Consumers (chapters C/E/I) instantiate the NAME with their own arena, read and peel unit; the
predicate is stated in the exponent `s`, and the corpus's `t`-indexed display is recovered by
`s = f_{i+1} − t`.  ORIENTATION: `theta` (D.06 rows 2–3). -/
def GentowW {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) (R : G → K) (w : Kˣ) : Prop :=
  ∀ s : ℕ, R (N.n (s * q)) = (A.theta q s : K) * (w : K) ^ s

/-- **D.44 — `(ABS-G5W)`** (`EFF.T3.21`): a family of boundary-read ports at every `s`, whose
per-grade factor is the read at the ladder point and whose peel unit is the given `w`, yields the
sitewise B-law predicate.

**Nothing here discharges any instance**: the port family is a HYPOTHESIS, supplied by chapter C
at `i = 2` (D.42's `(ABS-G2)`) and left open at `i ≥ 3` behind D.60/D.62's carriers.  The `i = 1`
residual is the `ω₁`/OPEN-2 fence: T3 does not identify GENTOW5 S11.3's `z₁`-letter power with a
displayed `w₁`. -/
theorem gentowW_of_ports {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {R : G → K} {w : Kˣ}
    (h : ∀ s : ℕ, ∃ P : BoundaryReadPort A q s, P.U = R (N.n (s * q)) ∧ P.w = w) :
    GentowW A q R w := by
  intro s
  obtain ⟨P, hU, hw⟩ := h s
  -- D.38 gives `P.U = Θ_N(s;q)·(P.w)^s`; the hypothesis identifies `P.U` with the read and
  -- `P.w` with `w`, so this IS the predicate's clause at `s`.
  rw [← hU, P.t3_br, hw]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GentowW
#print axioms Uniformity.Density.Gauge.gentowW_of_ports

end AxCheck
