/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G01
import Uniformity.ChapG.G02
import Uniformity.ChapG.G03
import Uniformity.ChapG.G04
import Uniformity.ChapG.G05
import Uniformity.ChapG.G06
import Uniformity.ChapG.G07
import Uniformity.ChapG.G08
import Uniformity.ChapG.G09
import Uniformity.ChapG.G10
import Uniformity.ChapG.G11
import Uniformity.ChapG.G12
import Uniformity.ChapG.G13
import Uniformity.ChapG.G14
import Uniformity.ChapG.G15
import Uniformity.ChapG.G16
import Uniformity.ChapG.G17
import Uniformity.ChapG.G18
import Uniformity.ChapG.G19
import Uniformity.ChapG.G20
import Uniformity.ChapG.G21
import Uniformity.ChapG.G22
import Uniformity.ChapG.G24
import Uniformity.ChapG.G25
import Uniformity.ChapG.G26
import Uniformity.ChapG.G27
import Uniformity.ChapG.G28
import Uniformity.ChapG.G29
import Uniformity.ChapG.G30
import Uniformity.ChapG.G30a
import Uniformity.ChapG.G31
import Uniformity.ChapG.G32
import Uniformity.ChapG.G33
import Uniformity.ChapG.G34
import Uniformity.ChapG.G35
import Uniformity.ChapG.G36
import Uniformity.ChapG.G37
import Uniformity.ChapG.G38
import Uniformity.ChapG.G39
import Uniformity.ChapG.G40
-- The G.23 REPLACEMENT ROUTE (blueprint AMENDMENT §A-8). Node-numbered at G.23, but it
-- rests on the finite-field layer G.38–G.40, so it is imported after them.
import Uniformity.ChapG.G23R1
import Uniformity.ChapG.G23R2
import Uniformity.ChapG.G23R3
import Uniformity.ChapG.G23R4
import Uniformity.ChapG.G23R5
import Uniformity.ChapG.G23R6
import Uniformity.ChapG.G23R7
import Uniformity.ChapG.G23R8
import Uniformity.ChapG.G23R9
import Uniformity.ChapG.G23R10
import Uniformity.ChapG.G23R11
import Uniformity.ChapG.G23R12
import Uniformity.ChapG.G45
import Uniformity.ChapG.G50
import Uniformity.ChapG.G52
import Uniformity.ChapG.G53
import Uniformity.ChapG.G54
import Uniformity.ChapG.G55
import Uniformity.ChapG.G56
import Uniformity.ChapG.G57
import Uniformity.ChapG.G58
import Uniformity.ChapG.G59
import Uniformity.ChapG.G60
import Uniformity.ChapG.G62
import Uniformity.ChapG.G63
import Uniformity.ChapG.G64
import Uniformity.ChapG.G65
import Uniformity.ChapG.G66
import Uniformity.ChapG.G67
import Uniformity.ChapG.G68
import Uniformity.ChapG.G69
import Uniformity.ChapG.G70
import Uniformity.ChapG.G71
import Uniformity.ChapG.G72
import Uniformity.ChapG.G73
import Uniformity.ChapG.G74
import Uniformity.ChapG.G75
import Uniformity.ChapG.G76

/-!
# Uniformity.ChapG — chapter G roll-up (BASE CASES AND MENUS)

Imports every landed chapter-G node module, in the blueprint's topological order
(`blueprint/CHAP-G_base_cases_menus.md`). One node = one file under `Uniformity/ChapG/`,
named `G<nn>.lean` after its blueprint node number; this file is the sole place that wires them
into the rest of `leanfinal` via the root import `Uniformity.lean`.

Node files land their public declaration(s) in the namespace prescribed by the blueprint
(`Uniformity.Density` for theorems about landed objects, `Uniformity.Density.Menu` for new
chapter-G definitions), never inventing a new top-level namespace.

Status tracked per-node in the fleet's commit log (prefixes `G1:`/`G2:`/`G3:` by wave); this
header carries no per-node status table — see `docs/PROJECT_STATE.md` for the standing summary.
-/
