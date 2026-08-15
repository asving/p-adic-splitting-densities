/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Quarry.RamificationInertiaLocal
import Uniformity.Quarry.AdjoinRootDVR

/-!
# Uniformity.Quarry — vendored-library backports and the locality layer

Roll-up for the `Quarry/` directory. Two kinds of file live here, and the distinction is the
whole point of the directory:

* **Backports.** Declarations copied (near-)verbatim from a vendored external library after
  verification against our own mathlib pin. Every such file carries a provenance block naming the
  source repo, commit, file, line, licence, and the date the copy was verified, plus an explicit
  dedup-audit statement listing every adaptation. Source inventory:
  `docs/VENDOR_QUARRY_MAP_2026-08-15.md`.
* **Original locality/ramification infrastructure** written here because no quarry and no mathlib
  at our pin has it. Those files say so in their own header and carry no provenance block.

Nothing in this directory may depend on `Uniformity.Density.*`; the dependency runs the other way.
-/
