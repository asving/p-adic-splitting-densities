# RESCHEDULE record — NODE C.38a clause 2 (`dv2Res` / `dv2ResPoly`), Chapter-C fleet wave 7, agent 3

> **SUPERSEDED, same slot (2026-08-16).** The block described below lasted about twenty minutes.
> NODE C.25 (`dvResPoly`) landed mid-slot from a sibling agent at commit `495eb769`, and clause 2
> went in against it at commit `3b146848` — **NODE C.38a is COMPLETE**, all seven signed
> declarations in `leanfinal/Uniformity/ChapC/C38a.lean`, Lean-core axioms only, `lake build
> Uniformity.ChapC.C38a` green. Nothing below is an open obligation. The file is kept for two
> things that are still live: the **C.25 fanout table** in "Everything else waiting on C.25"
> (C.26/C.27/C.29/C.34/C.61/C.67 and the rest are still unlanded), and the recorded precedent for
> landing one half of a signed def-cluster when the other half's dependency is missing.

**Date.** 2026-08-16. **Verdict.** clause 1 LANDED (`leanfinal/Uniformity/ChapC/C38a.lean`,
commit `ac84a745`); **clause 2 BLOCKED — dependency not landed. Not weakened, no stand-in.**
*(Verdict superseded within the slot — see the box above.)*

## The node and its split

NODE C.38a is the RE-PLAN'd helper cluster booked inside C.38's SIGNATURE block
(`blueprint/CHAP-C_tower_grammar.md:2494-2500`; amendment A-C.1(e) at `:7838-7841` records it as
the 129th node, census `+1 def`). Its signed twin, `leanspec/Leanspec/ChapC.lean:1504-1546`, has
seven declarations in two independent halves:

| clause | declarations | calls | status |
| --- | --- | --- | --- |
| 1 — side geometry | `Dv2OnSide`, `dv2SideSet`, `dv2SideMin`, `dv2SideMax`, `dv2SideDeg` | `dv2Supp`, `dv2Pin` (C.11) | **LANDED** |
| 2 — residual read | `dv2Res`, `dv2ResPoly` | `dvResPoly` (**C.25**) | **BLOCKED** |

## The block

`dv2Res` is, by its A-C.1 determination, *"`A`'s own `dvResPoly` evaluated at the letter `β`"*
(`AdjoinRoot.mk L.r`), signed body:

```lean
noncomputable def dv2Res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : AdjoinRoot L.r :=
  open Classical in
  if h : ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M₀ : ℕ∞)
  then AdjoinRoot.mk L.r
    (dvResPoly F H₀ hpin A L.u L.ℓ h.choose h.choose_spec.choose h.choose_spec.choose_spec)
  else 0
```

`dvResPoly` is **NODE C.25** (`blueprint:1685-1714`, twin `leanspec:774-785`) and has no file in
`leanfinal/Uniformity/ChapC/`. Verified: `grep -rn dvResPoly leanfinal/Uniformity/` returns a
single hit, a prose mention in `C09.lean:66`; there is no `C25.lean`. `dvResPoly` is a **public**
node `def`, not a private helper, so the standing D9 local-copy pattern (which C.04/C.12/C.19/
C.22/C.44 use for `isKey_X`) does not apply — a local re-declaration would fork the definition
and put two `dvResPoly`s in the tree.

`dv2ResPoly` (the per-slot assembly, C.25 one level up) calls `dv2Res` and is blocked with it.

## Why clause 1 was landed anyway (not the C.56a "orphan defs" situation)

The wave-6 C.56a reschedule (`RESCHEDULE_C56a_2026-08-16.md`, commit `12295314`) declined a
partial landing because the writable defs' only consumer was the blocked one. That does not hold
here. Four signed statements consume clause 1 and **none of them mentions `dv2ResPoly` or
`dv2Res`**:

| consumer | node | leanspec | clause-1 names used |
| --- | --- | --- | --- |
| `towerLocus_depth3_floor` | C.55 | `:1824` | `dv2SideSet` |
| `mult₂_readable` | C.64 | `:2015-2024` | `dv2SideSet`, `dv2SideMin`, `dv2SideDeg` |
| `dv2_length_sum` | C.65 | `:2029-2037` | `dv2SideSet`, `dv2SideMax` |
| `dv2Pin_translation_interior` | C.68 | `:2058-2066` | `dv2SideSet`, `dv2SideMin`, `dv2SideMax` |

So clause 1 unblocks four nodes today and none of them has to wait on C.25.

## C.25 is itself unblocked — the reschedule is a one-hop wait

Every item C.25's signed body calls IS landed, so C.25 can be transcribed in the next wave with
no further prerequisite:

| item | node | file |
| --- | --- | --- |
| `KeyFrame`, `KeyFrame.Pin`-shaped `hpin` binder | C.01 | `C01.lean` |
| `KeyFrame.frameRes`, `KeyFrame.stageField` | C.03 | `C03.lean` |
| `dvHgt` | C.06 | `C06.lean` |
| `dvSideSet`, `dvSideMin`, `dvSideDeg` | C.07 | `C07.lean` |
| `KeyFrame.twistRead` | C.22 | `C22.lean` |
| `dev` | B.02 | `ChapB/B02.lean` |

(Checked against the landed signatures: `C22.lean`'s `twistRead` takes `(F) (H₀) (hpin) (k) (A)`
and returns `F.stageField H₀ hpin`, exactly the shape C.25's body applies it in; `C03.lean`'s
`stageField` is the `abbrev` to `AdjoinRoot (F.frameRes H₀ hpin)`.)

## Everything else waiting on C.25 (scheduling intel)

Beyond C.38a clause 2: C.26 (`dvResPoly_coeff_eq_zero_iff`, `natDegree_dvResPoly`), C.27, C.29,
C.34, C.35's `mult₂` spec companion, C.38 (`dv2ResPoly_radical_eq`), C.39 (`γg`, `pinHeight`,
`dv2ResPoly_scalar`), C.61, C.67 (`multiplicity_tie`), and §10's `repoRead := dv2Res` (C.104).
C.25 is therefore a high-fanout landing; recommend it be scheduled ahead of the rest of §5.

## Disposition

**RESCHEDULE C.38a clause 2 behind C.25.** The rescheduled agent appends `dv2Res` and
`dv2ResPoly` to the existing `leanfinal/Uniformity/ChapC/C38a.lean` (adding
`import Uniformity.ChapC.C25` and `import Uniformity.ChapC.C22` as needed), extends the
`#print axioms` block, and flips the file docstring's `## Status` line from "Clause 1 of 2" to
complete. No statement was weakened and nothing was stubbed to fake a landing.
