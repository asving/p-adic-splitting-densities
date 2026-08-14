/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.Density.ScaleExtraction — the forward `π`-power extraction and its level bookkeeping

Two nodes of `spec/CERTAIN_NODES_2026-08-14.md`:

* **CN-12** `exists_monic_scaleRoots` — the integrality side condition of the FORWARD extraction
  `X = π^m Y`, in the one polygon formulation that is representation-free.
* **CN-13** `dvd_sub_coeff_of_scaleRoots` — how a congruence level survives the extraction.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

end Uniformity.Density
