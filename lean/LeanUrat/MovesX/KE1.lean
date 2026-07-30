/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE1 — the (ns-null) port: `NsNullP` from single-state admissible-Z lump chains

BRIDGE CAMPAIGN unit **KE1** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-i) + §4 KE1).
E-PHASE STATEMENT MODULE — statements with `sorry` bodies; the blueprint's
pre-approved split KE1a/KE1b is executed as the two theorems below.

THE KERNEL: `NsNullP n X` (MovesX/Defs.lean) — every (NS-c) fiber is `frac`-null.
The paper proof is ON RECORD (MOVES_2026-07-24.md:7212-7240, the rev-2
SINGLE-STATE admissible-Z argument; four verifications): per fiber, the (τ-ns)
class is the decreasing intersection of capped lumps `L_M` ((ns-lump), B(iii));
Theorem C(b) with the admissible fresh-clause set `Z_M` prices the lump exactly,
`μ(Σ ∩ L_M) = μ(Σ)·p^{−|Z_M|}`; slot 0's unit-spaced ladder gives
`|Z_M| ≥ M − M₀ → ∞`; hence the class is null.

RECORDED RESOLUTIONS (E-phase rules; each minimal against the repo vocabulary):
1. ⚑ `NsLumpChain` is a NEW NAMED CARRIER (hypothesis/carrier shape per the Q4
   adjudication — never a new field on the frozen `XCtx`). Its fields transcribe
   exactly the paper proof's three finite-level facts; inhabitation at the real
   context is the port's remaining obligation. The corpus's REAL-carrier side
   already exists in MovesT (`NsLumpFamily`/`capMassAt`/`nsZAt` + the PROVED
   analysis leg `MovesT.nsNull_of_pricing_growth`, MovesT/Defs.lean §2.10, and
   the OPEN `NsPricing`/`NsGrowth` owners MovesS wave 5/[2b]); the seam
   identifying that data with a chain here is owner-corpus work, not this unit's.
2. `priced` is stated as `≤` (the C(b) pricing is an EQUALITY; the inequality
   suffices for nullity and makes the carrier strictly easier to inhabit).
3. `XCtx.frac` has NO continuity-from-above field, so the paper's
   "continuity from above" step is replaced by the monotone-bound squeeze
   through `mem_lump` (`frac_mono` + archimedean vanishing of
   `stateMass/p^{zcount M}`) — the XF10 `discZeroNull` pattern. This is a
   strengthening-free reroute: the class is CONTAINED in every lump.

deps: locating the paper proof text (done — MOVES (ns-null) closure record) +
XCtx. Consumers: KE7 (the X2Bridge a.e. clause's nsFiber leg), XG3/`x3Density`
(which takes `NsNullP` by name). Highest value/effort unit of the KE cluster.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE1 carrier (⚑ named-carrier ratification)** — a single-state admissible-Z
LUMP CHAIN for a set `S` (intended: one (NS-c) fiber `C.nsFiber i`), transcribing
the MOVES (ns-null) proof's finite-level data over the `XCtx` vocabulary:

* `lump M` — the capped lump `L_M` ((ns-lump)/B(iii): all window-slot digits
  vanish up to height `M`), a superset of `S` at every cap (`mem_lump`; the
  paper's `S = ⋂_M (Σ ∩ L_M)` is consumed only through `⊆`);
* `stateMass` — the entrance-state mass `μ(S(H,⊤))` of Theorem C(b);
* `zcount M` — the fresh admissible clause count `|Z_M|`, with the slot-0
  ladder lower bound `M − M₀ ≤ zcount M` (`M₀` = the entrance resolution);
* `priced` — the Theorem C(b) pricing, weakened to `≤` (resolution 2 above).

Inhabiting this at the real context per fiber is the port's open leg (the
MovesT/MovesS `NsPricing`/`NsGrowth` owners); THIS module only consumes it. -/
structure NsLumpChain (n p : ℕ) [Fact p.Prime] (C : XCtx n p)
    (S : Set (MonicBox n p)) where
  lump : ℕ → Set (MonicBox n p)
  mem_lump : ∀ M : ℕ, S ⊆ lump M
  stateMass : ℚ
  M0 : ℕ
  zcount : ℕ → ℕ
  zcount_lb : ∀ M : ℕ, M - M0 ≤ zcount M
  priced : ∀ M : ℕ, C.frac (lump M) ≤ stateMass / (p : ℚ) ^ zcount M

/-- **KE1a — the single-state lemma**: a set carrying an admissible-Z lump chain
is `frac`-null. Sketch (the XF10 squeeze, no topology needed): for every `M`,
`frac S ≤ frac (lump M) ≤ stateMass/p^{zcount M} ≤ stateMass/p^{M−M₀}`
(`frac_mono` + `priced` + `zcount_lb`, `p ≥ 2`); the bound is archimedean-small,
and `frac_nonneg` closes `frac S = 0`. deps: the carrier above. -/
theorem nsNull_of_lumpChain {n p : ℕ} [Fact p.Prime] (C : XCtx n p)
    (S : Set (MonicBox n p)) (L : NsLumpChain n p C S) :
    C.frac S = 0 := by
  sorry

/-- **KE1b — the fiber-null assembly**: `NsNullP n X` given a lump chain at every
(NS-c) fiber of every prime's context. This is the ported (ns-null) with its
remaining obligation stated as the named per-fiber carrier hypothesis — the
honest conditional form until the real-carrier pricing/growth legs
(`MovesT.NsPricing`/`NsGrowth`, owners MovesS wave 5/[2b]) land and the seam
inhabits the chains. deps: KE1a. Consumers: KE7, `x3Density` (XG3). -/
theorem nsNullP_of_lumpChains {n : ℕ} (X : XFamily n)
    (hch : ∀ (p : ℕ) [Fact p.Prime] (i : (X.ctx p).nsIdx),
      Nonempty (NsLumpChain n p (X.ctx p) ((X.ctx p).nsFiber i))) :
    NsNullP n X := by
  sorry

end LeanUrat.MovesX
