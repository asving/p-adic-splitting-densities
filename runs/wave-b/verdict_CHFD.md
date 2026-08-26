# CHFD verdict — 2026-08-26

Status: **SUPPLY MAP COMPLETE; TWO STOP-THE-LINE INDEX/SIGNATURE FINDINGS.** Full evidence and fleet table are in
`docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md`.

## Verdict

The two eleven-field structure declarations are textually aligned, but there is a stop-the-line
semantic drift after unfolding `ns7`: leanspec still signs `NS7Termination` with a `True` body,
while leanfinal has already typed the redrafted descent assertion, declared C.94's
`agnprw_termination`, and consumed it.  The campaign state saying C.94 is “ready to declare” is
stale.

At current landed signatures, `CapstoneHypotheses 2` reduces exactly to three substantive inputs:
`NS7Termination`, the universal `ladder` supplier, and the universal `deepTwist` supplier.
`a0`, `a1`, and `a2` at degree 2 are already provable; the remaining fields are literal `True`
or have impossible numeric guards.  `scratch/CHFD_probe.lean` machine-checks that boundary.

The landed S2 socket teeth do not supply degree 2: S2 has tower depth 2 but input degree 4.  They
construct particular socket antecedents and supply neither `LadderSupply` nor the deep-twist
conclusion.  Consequently the decisive missing campaigns are LADDER-SUPPLY and
DEEP-TWIST-SUPPLY, not more socket packaging.

## Eleven-field disposition

| field | live supply | gap |
|---|---|---|
| `ns7` | C.94 `agnprw_termination` plus I.01 wrapper (`C94.lean:107-121`; `I01.lean:132-140`) | owner reconciliation with signed `True` body |
| `ladder` | C130s18/sg construct arising guards (`C130s18.lean:238-247`; `C130sg.lean:518-535`) | no guard-to-`LadderSupply`; HE7A/LB1/MP1/ϑ multi-node campaign |
| `deepTwist` | C130s18/sg construct joint guards; depth-2 conclusion is empty (`C130s18.lean:249-262`; probe) | no guard-to-live D/E conjunction; research campaign |
| `a0` | degree 2 proof replayed from I.02/G.51 (`I02.lean:116-125`) | public wrapper; cubic/general exact counts open |
| `a1` | degree 2 I.03 gate; cubic menu G.54 (`I03.lean:177-210`; `G54.lean:35-38`) | public n=2/n=3 wrappers; general family extraction |
| `a2` | n=1,2,3 drainage landed; H.98 conditional general bridge (`H98.lean:142-159`) | general `InductionPackage`; H.116b4 research cores |
| `jd0` | literal `True`; intended F.04 fold half exists (`F04w.lean:85-91`) | arising weld-site socket |
| `genhnBox2` | guarded `True`; intended F.11 carrier exists (`F11.lean:46-51`) | same weld socket |
| `windowPinning` | literal `True` (`I05.lean:90-94`) | type real `hwin` body and finish general pinning |
| `genhnHE` | `6≤n`-guarded `True`; H73w supplies the μ=3 slice | μ≥4 HE tail |
| `genhnTow1` | `8≤n`-guarded `True`; C.93 threshold partial | full tower census |

`w1` is not an eleventh field: it is a named missing-field debt. F.28’s real weld bundle has
three fields, and A-I.1 forbids binding them at the refutable all-sites shape
(`Leanspec/ChapI.lean:310-324`; `F28.lean:48-54`). `TypeOfFaithful` remains `True` but is not in
this structure (`I21.lean:98-110`).

## DAG and fleet decision

The two hard joins are:

```text
arising realization/views -> HE7A + LB1 + MP1 + HVarthetaRes -> ladder
arising joint arena/views  -> per-live HVarthetaRes + GentowW  -> deepTwist
```

Counts/menu/drainage form a separate `a0/a1/a2` branch; weld, window, HE-tail, and tower-census
branches become relevant as their real bodies/degree guards become live. For current n=2, only
`ns7 + ladder + deepTwist` remain after the probe’s Lean-core `a0/a1/a2` and stub-tail assembly.

First wave: fire the 30–60 minute public wrappers for `DecidedSliceAt 2`, `MenuLawAt 2`,
`DrainageAt 2`, and `MenuLawAt 3`; separately launch interface nodes LADDER-SUPPLY-L0,
DEEP-TWIST-DT0, WELD-SITE-W0, and WINDOW-PINNING-WIN0. Do not duplicate AMND’s fenced `hprev`
and coordinated `chainNormBelow` work. The μ₃ chain is one deep-twist tooth, not the capstone
supply map.

## Verification

`cd leanfinal && lake env lean scratch/CHFD_probe.lean` exits 0. There is no `sorry`, no axiom
declaration, and all six new proof declarations print only
`[propext, Classical.choice, Quot.sound]`. The imported I.01 wrapper separately prints the
intended cite dependency `Uniformity.Density.Tower.agnprw_termination`.
