/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD3_treeCarrier

/-!
# IB-D4 — vt / vt_inj / vt_typemult / vt_thr (bridge campaign BP1, cluster c7)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†5) /
§4 group D (IB-D4).  Deps: IB-D3 (`bridgeTree`).  Charge: the carrier's
`TreePin`-facing accessors, ALL rfl-level by (†5)'s design:
`vt := Subtype.val` (injective), `vt_typemult`/`vt_thr` := rfl — the exact
suppliers of `TreePin.vt`/`vt_inj`/`vt_typemult`/`vt_thr` (DefsLedger.lean:
352–356) at IB-D18's assembly.

TRANSCRIPTION RESOLUTION (recorded): `TreePin.vt_thr` reads
`F.thr σ T = (vt σ T).thr n`, so the carrier-side threshold is DEFINED as the
VTree's own threshold (`bridgeThr σ T := (vt σ T).thr n` — the value IB-D14
wires into `FiberSeries.thr`), making `vt_thr` literally `rfl`.  The
realizability accessor `bridgeVt_realizedSelf` (the carrier's third clause)
is included here as IB-D15's entry point (`vt_real` = transfer from lvl).

All four laws are rfl-level and PROVED outright (no sorries in this unit;
E-phase precedent: BridgeD2's `bridgeChart_inj`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†5) `vt := Subtype.val`: the carried tree IS a `MovesT.VTree` —
    `TreePin.vt`'s supply. -/
def bridgeVt (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : MovesT.VTree p (ZMod p) :=
  T.1

/-- `TreePin.vt_inj`'s supply: subtype-val injectivity. -/
theorem bridgeVt_inj (n p : ℕ) [Fact p.Prime] (σ : SplittingType n) :
    Function.Injective (bridgeVt n p σ) :=
  fun _ _ h => Subtype.ext h

/-- The carrier-side threshold — DEFINED as the VTree's own `thr n` (see the
    header resolution; `FiberSeries.thr`'s value at IB-D14). -/
noncomputable def bridgeThr (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : ℕ :=
  (bridgeVt n p σ T).thr n

/-- `TreePin.vt_typemult`'s supply: the carried tree has verdict type σ —
    the carrier's first clause. -/
theorem bridgeVt_typemult (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : (bridgeVt n p σ T).typemult = σ.1 :=
  T.2.1

/-- `TreePin.vt_thr`'s supply — rfl by the header resolution. -/
theorem bridgeVt_thr (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : bridgeThr n p σ T = (bridgeVt n p σ T).thr n :=
  rfl

/-- The carrier's realizability clause, read off — IB-D15's entry point
    (`vt_real` = `TransferRow.realizes_transfer` from lvl T). -/
theorem bridgeVt_realizedSelf (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : RealizedSelf n p (bridgeVt n p σ T) :=
  T.2.2.1

/-- The carrier's ns-free clause, read off (the NSF-KEY repair conjunct —
    M02 §2 / (NSF-KEY-RET) R-1, sign-off 2026-08-05): NO carried tree has an
    ns-marked leaf.  In particular M02 §2's exact-square poison V₀ (ns-marked
    at its maximal chain) is NOT carried — the compiled record that the V₀
    refutations of `count_tie`/`canonical_stable`/`VPSound` are DEAD at the
    guarded carrier (R-3(3)); `MovesT.treeN`'s `hdet` clause is THIS fact at
    the wired instance. -/
theorem bridgeVt_nsFree (n p : ℕ) [Fact p.Prime] (σ : SplittingType n)
    (T : bridgeTree n p σ) : MovesT.NsFree (bridgeVt n p σ T) :=
  T.2.2.2

end LeanUrat.MovesU
