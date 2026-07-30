/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE5 — [ATTEMPT] X2TailsP: the tall-event tail from the D4R.2 pool bound

BRIDGE CAMPAIGN unit **KE5** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-iv) + §4 KE5, risk R8).
E-PHASE STATEMENT MODULE — statement with `sorry` body.

THE KERNEL: `X2TailsP n X K` (MovesX/Defs.lean) —
`frac(TallEvent h*) ≤ C_T·p^{−c_T·h*}`. Blueprint sketch: price the FIRST
height-≥h* read via the D4R.2 pool bound `μ(P̂) ≤ M(P̂)·p^{W(P̂)−A(P̂)}` (`A`
grows with the tall read's height); union over prefixes with the per-depth
species-menu factor; CONVERGENCE OF THAT SERIES IS THE RISK (R8).

RECORDED RESOLUTIONS:
1. `TallExtEvent C H h*` (defined below) is the first-read event: some branch's
   history is `H ++ [ν]` with `h* ≤ ν.h`. The covering
   `TallEvent ⊆ ⋃_{d<cap} ⋃_{H realized, |H|=d} TallExtEvent ∪ (TallEvent ∩ DeepEvent cap)`
   holds by the earliest-tall-node ancestor (`parent_hist` prefixes; `termLast`
   converts length to `dTotal`); `realizedHists` is NOT restricted to tall-free
   prefixes (a superset union — sound and simpler).
2. INTERFACE-FORCED SHAPE: `XCtx.frac` has FINITE subadditivity
   (`frac_union_le`) and null countable unions ONLY — no countable
   subadditivity. The note's "sum over prefixes" is therefore transcribed as a
   FINITE depth window `depthCap h*` plus the deep remainder
   `frac(TallEvent ∩ DeepEvent (depthCap h*))`, both priced inside one field
   (`series_ok`). Any route must supply its own cutoff; this is recorded as an
   interface note, not a weakening (the target `X2TailsP` is verbatim).
3. ⚑ `TailsRoute` is the NAMED CARRIER (Q4 shape) bundling: the D4R.2 read
   price (`read_price`, depth-indexed), the species-menu count (`menu_card` on
   `realizedHists` — §M-SPECIES finite menus), and the R8 risk EXACTLY at
   `series_ok` (the summed window + remainder vs. `C_T·p^{−c_T·h*}`). If
   `series_ok` is uninhabitable, the divergent-series obstruction record is
   the deliverable.

deps: KE4 PHASE 1 (CM gate — candidate-stress + divergence detection runs
FIRST); MovesD mass laws (D4R.1/D4R.2 built) for the instance leg; ACCEPTANCE
GATED on KE4 phase 2 against the prover's actual constants (REV 2, F10).
Consumers: X.2's exponential envelope leg (CL-2/CL-3 tag set).
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- KE5 event vocabulary — the FIRST-tall-read extension event of a prefix `H`:
some branch of `f` has history exactly `H ++ [ν]` with a tall read `h* ≤ ν.h`. -/
def TallExtEvent {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (H : XHistory n)
    (hstar : ℕ) : Set (MonicBox n p) :=
  { f | ∃ b : C.Branch f, ∃ ν : XNode n, hstar ≤ ν.h ∧ C.hist b = H ++ [ν] }

/-- KE5 counting vocabulary — the depth-`d` REALIZED prefixes of a context: the
histories of length `d` realized by some branch of some box point (the union
index of the first-read decomposition; unrestricted per resolution 1). -/
def realizedHists {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (d : ℕ) :
    Set (XHistory n) :=
  { H | H.length = d ∧ ∃ f : MonicBox n p, ∃ b : C.Branch f, C.hist b = H }

/-- **KE5 named carrier (⚑ ratification)** — one context's tails route:
* `read_price` — the D4R.2 pool bound, packaged per prefix depth: the first-read
  event after any depth-`d` prefix has mass ≤ `price d h*`;
* `menu_finite`/`menu_card` — the per-depth species-menu factor: at most
  `menu^d` realized depth-`d` prefixes (§M-SPECIES finite menus);
* `series_ok` — THE R8 FIELD: the finite depth window `depthCap h*` of
  menu-weighted prices plus the deep remainder is dominated by the target
  envelope `CT·p^{−cT·h*}` (interface-forced finite shape, resolution 2). -/
structure TailsRoute (n p : ℕ) [Fact p.Prime] (C : XCtx n p) (CT cT : ℝ) where
  menu : ℕ
  price : ℕ → ℕ → ℝ
  depthCap : ℕ → ℕ
  price_nonneg : ∀ d hstar : ℕ, 0 ≤ price d hstar
  menu_finite : ∀ d : ℕ, (realizedHists C d).Finite
  menu_card : ∀ d : ℕ, (realizedHists C d).ncard ≤ menu ^ d
  read_price : ∀ (H : XHistory n) (hstar : ℕ),
    ((C.frac (TallExtEvent C H hstar) : ℚ) : ℝ) ≤ price H.length hstar
  series_ok : ∀ hstar : ℕ,
    (∑ d ∈ Finset.range (depthCap hstar), (menu : ℝ) ^ d * price d hstar)
        + ((C.frac (TallEvent C hstar ∩ DeepEvent C (depthCap hstar)) : ℚ) : ℝ)
      ≤ CT * (p : ℝ) ^ (-(cT * hstar))

/-- **KE5 [ATTEMPT]** — `X2TailsP` from a tails route at every prime: the
first-read covering (resolution 1) + finite subadditivity (`frac_union_le`,
`frac_mono`) bound `frac(TallEvent h*)` by the depth-window sum plus the deep
remainder; `menu_card` and `read_price` dominate each depth slice by
`menu^d·price d h*`; `series_ok` closes against `K.CT·p^{−K.cT·h*}`.
deps: KE4 phase 1 (gate — runs FIRST), `TailsRoute` (⚑); acceptance gated on
KE4 phase 2 (the prover's actual constants re-probed). Fallback: the
divergent-series obstruction record. -/
theorem x2Tails_of_route {n : ℕ} (X : XFamily n) (K : XConsts n)
    (hroute : ∀ (p : ℕ) [Fact p.Prime],
      Nonempty (TailsRoute n p (X.ctx p) K.CT K.cT)) :
    X2TailsP n X K := by
  sorry

end LeanUrat.MovesX
