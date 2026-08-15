/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G21
import Uniformity.ChapG.G14
import Uniformity.ChapG.G12
import Uniformity.ChapG.G10
import Uniformity.ChapG.G09
import Uniformity.ChapG.G05
import Uniformity.ChapG.G03
import Uniformity.ChapG.G01

/-!
# Uniformity.ChapG — chapter G roll-up (BASE CASES AND MENUS)

Imports every landed chapter-G node module, in the blueprint's topological order
(`blueprint/CHAP-G_base_cases_menus.md`). One node = one file under `Uniformity/ChapG/`,
named `G<nn>.lean` after its blueprint node number; this file is the sole place that wires them
into the rest of `leanfinal` via the root import `Uniformity.lean`.

Node files land their public declaration(s) in the namespace prescribed by the blueprint
(`Uniformity.Density` for theorems about landed objects, `Uniformity.Density.Menu` for new
chapter-G definitions), never inventing a new top-level namespace.

Status tracked per-node in the fleet's commit log (prefix `G1:`); this header carries no
per-node status table — see `docs/PROJECT_STATE.md` for the standing summary.
-/
