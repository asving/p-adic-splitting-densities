# CapstoneHypotheses supply map — 2026-08-26

Status: complete.  This audit reads the live landed tree at 2026-08-26 HEAD and keeps
signed/landed drift separate from mathematical supply.

## Stop-the-line findings

1. The two `CapstoneHypotheses` field lists themselves agree: eleven fields, in the same order,
   with identical binder blocks, universes, guards, and placeholder bodies
   (`leanspec/Leanspec/ChapI.lean:812-840`;
   `leanfinal/Uniformity/ChapI/I10_I15_I18.lean:151-179`).
2. After unfolding the first field, they do **not** demand the same proposition.  Signed
   `LeanspecI.NS7Termination` still ends in `True`
   (`leanspec/Leanspec/ChapI.lean:449-452`), whereas landed `NS7Termination` is the full
   redrafted descent assertion (`leanfinal/Uniformity/ChapI/I01.lean:122-129`).  Moreover the
   allegedly “ready to declare” C.94 cite is already declared at
   `leanfinal/Uniformity/ChapC/C94.lean:107-121` and already consumed by
   `ns7Termination_of_cite` (`leanfinal/Uniformity/ChapI/I01.lean:132-140`).  Thus the field-list
   text is byte-stable but its referenced `ns7` body has semantic drift.  The signed source and
   `docs/PROJECT_STATE.md:55-66,81-82` need an owner amendment/state refresh before any claim of
   signed/landed agreement after unfolding.
3. “S2” has two indices that must not be conflated.  The landed S2 socket witness has tower
   depth `r = 2`, but its input/capstone degree is `n = 4`
   (`leanfinal/Uniformity/ChapC/C130s18.lean:305-312,314-355`;
   `leanfinal/Uniformity/ChapC/C130sg.lean:509-556`).  It is therefore evidence for the socket
   predicates at degree 4, not a supplier for `CapstoneHypotheses 2`.

## Exact field inventory and supply rows

The live landed interpretation is used below; signed drift is called out explicitly.

| field | exact demand after unfolding | landed supply | exact gap / owner / size |
|---|---|---|---|
| `ns7` | Landed: for every complete DVR with finite residue field, uniformizer `π`, monic squarefree `f`, and infinite sequence of `DescentState`, divisibility of every block into `f` and a `DescentStepR` at every successor imply `False` (`I01.lean:122-129`; redraft at `C94.lean:107-116`). Signed: only the same ring bundle followed by `True` (`Leanspec/ChapI.lean:449-452`). | `Tower.agnprw_termination : NS7TerminationStatementR` is declared (`C94.lean:118-121`), and the definitional identification plus wrapper are landed (`I01.lean:132-140`). | **Supply exists cite-conditionally, but stop-the-line signed drift.** Declaration node requested by the older plan was C.94 `agnprw_termination`; it has already landed. Remaining work is an owner-gated signed I.01 resolution/state reconciliation, 30–60 min transcription/review, not a new proof. |
| `ladder` | For every socket argument tuple, a proof that it is an arising degree-`n` configuration must yield `LadderSupply`. The guard unfolds to existence of a DVR/domain instance, a field `E`, `ArisingCore n`, `ChainRealization`, `RealizedInput`, carrier/block equivalence, gauge-lattice equivalence, and the three CC-12 view equalities (`C130s18.lean:147-175`). The result is a four-field record (`E24.lean:147-155`): (i) `Nonempty RungInterface`, whose fields are the side coprimality/window, hull lengths, residual-degree accounting, nonemptiness/forcing/exhaustion, and well-founded rank data (`E12.lean:127-157`); (ii) `LB1Carrier`, which produces `Nonempty (BlockSuite I)` whenever `I` is multi-side or has a nonseparable side (`E39.lean:105-114`); (iii) `MP1Carrier`, which produces `Nonempty (MidPeelEmission B B')` for every nonzero lower-degree recentering whose new key divides the block polynomial (`E40.lean:152-178`); and (iv) for every `i≥3`, `HVarthetaRes`, i.e. every `varthetaEl q s` ambient residue is an algebra-mapped `Kt` unit (`D62.lean:81-85`; `E61.lean:145-157`). | Generic and S2 *guard constructors* exist: `realizedInput_ladderConfigData` (`C130s18.lean:238-247`) and `s2Frontier_ladder_socket` at degree 4, conditional on `S2LevelOneThreshold` and adic completeness (`C130sg.lean:518-535`). These prove antecedents, not `LadderSupply`. E.24 explicitly says all four result fields are carried-open (`E24.lean:134-146`). | **No theorem maps the guard to the result.** New campaign **LADDER-SUPPLY**: split into HE7A/RungInterface, LB1, MP1, and `HVarthetaRes` suppliers, then an assembly node. The first three depend on Chapter E/C block machinery; the last on D/E gauge data. `BLOCKERS_PLAN_2026-08-26.md` F1/F2 (BlockFrontier and exact slot reads, lines 32–139) is a prerequisite candidate for the C-to-E block legs, not a direct supplier; MP1 also exposes the queued `recentered_key_emission` cite candidate (`E40.lean:145-148`). Multi-node; `HVarthetaRes` is research-open (E.61 says it has no teeth at `E61.lean:119-127`). S2 teeth do not close this universal function. |
| `deepTwist` | For every arising joint realization at input degree `n` and its witness-pinned tower depth `r`, prove `∀ i, (3 ≤ i ∧ i < r) → VarthetaRes i ∧ WFrame i` (`I10FreezeV2.lean:43-60`). `VarthetaRes` is the sitewise `HVarthetaRes` just expanded in the ladder row. `WFrame i` is `∀ j, 3 ≤ j → j ≤ i → GentowW ... j` (`E62.lean:127-137`), and `GentowW` is the exact identity `R (N.n (s*q)) = theta(q,s) * w^s` for every exponent `s` (`D44.lean:93-102`). The guard includes all ladder views plus the arena-family view and `core.r = r` (`C130s18.lean:177-218`). | `realizedInput_deepTwistConfigData` constructs the guard (`C130s18.lean:249-262`); the S2 guard is landed at degree 4/depth 2 (`C130sg.lean:537-556`). At depth 2 the conclusion is arithmetically vacuous, as probed in `scratch/CHFD_probe.lean`; this is only the named S2 occurrence, not the universal field. | **No guard-to-conclusion theorem.** New campaign **DEEP-TWIST-SUPPLY**. Per live level it needs both D.62 `HVarthetaRes` and D.44 `GentowW`; E.61/E.62 explicitly carry rather than discharge them (`E61.lean:119-127`; `E62.lean:121-126`). The μ₃ campaign supplies a depth-2 `gentow5w_two` endpoint only after its 29-node chain and the concurrent amendments `hprev : 2 ≤ f' → PrevGrade u'` plus the coordinated `chainNormBelow`/`thetaRatio` re-index (`MU3_CAMPAIGN_2026-08-26.md:108-188,223-263`). It remains blocked on `OPEN-RP1-TRANSPORT` (`MU3_CAMPAIGN_2026-08-26.md:292-308`); it is a tooth, not the general supplier. Multi-node/research-open. |
| `a0` | `DecidedSliceAt n`: for every factorization type of degree `n`, exhibit rational polynomials `num, den`, with `den ≠ 0`, whose denominator is nonzero at every residue cardinality and whose quotient equals `decidedDensity` uniformly over complete DVRs (`I02.lean:94-105`). | Degree 2 is fully proved in the anonymous gate from `uniformityStatement_two` plus the drainage tie (`I02.lean:116-125`; source theorem `G51.lean:70-79`). | At `n=2`, only a public declaration is missing: 30–60 min transcription (probe contains the proof). At `n=3`, Chapter H supplies drainage, not the five rational decided-density formulae (`H97b.lean:214-238`): **NEW A0-CUBIC** count campaign, multi-node. General `n` is the main exact-count research program. Also `a0 : DecidedSliceAt 0` is an acknowledged over-demand when asking for `∀ n, CapstoneHypotheses n` (`I02.lean:109-114`). |
| `a1` | `MenuLawAt n`: exhibit an `A1Family`, a finite menu `S`, both directions of label coverage between the family and `S`, degree `n` for every label, and `CoveringMenu O n S` for every complete DVR (`I03.lean:123-130`). | Degree 2 is proved by a real three-cell family in the anonymous gate (`I03.lean:177-210`). Degree 3 already has the five-type covering menu (`G54.lean:35-38`), so the same label-cell packaging is mechanical. H.95/H.96/H.97 package covering menus and rates, but `InductionPackage` does not contain the `A1Family` label-equivalence demanded here (`H95.lean:61-66`; `H96.lean:61-67`; `H97b.lean:174-177`). | Public `MenuLawAt 2`: 30–60 min transcription. `MenuLawAt 3`: 30–60 min label-family wrapper over `coveringMenu_three`. General `n`: **MENU-FAMILY** campaign; Chapter H’s induction/menu production supplies the covering-menu half, but a uniform A1-family extraction must be added (multi-node). |
| `a2` | `DrainageAt n`: for every complete DVR and every type `σ`, `UndecidedVanishes O n σ` (`Density/Statement.lean:114-122`). | Degrees 1 and 2 have `drainage_one`/`drainage_two` (`Density/Gates.lean:125-135`; `Density/Drainage.lean:838-860`); degree 3 has `drainageAt_three` (`H97b.lean:233-238`). General H.98 maps `∀ n, InductionPackage n` to all drainage slices (`H98.lean:142-159`). | At `n=2`, a 5-line wrapper only (probe). At `n=3`, already named. General `n` is blocked on supplying `InductionPackage n`; the current H.116b4 route contains immediate rows (GR-1/2 and GR-3/3b, 290–470 lines) but research-open restricted Smith, nonlinear lifting, and uniform-pushforward cores (`H116B4_MAP_2026-08-26.md:76-78,136-138,219-222,295-299,374-378`). Multi-node/research-open. |
| `jd0` | Literally `True` today (`I10_I15_I18.lean:175`), so `True.intro` inhabits it. Intended I.08 demand is per arising weld site `JD0Box2`; a `JD0SiteStrike` plus ledger equality yields it (`F04w.lean:85-91`). | Placeholder supply is immediate. Chapter F has the intended carrier and proved fold half, but seven per-site instances remain GC-13-gated (`F04w.lean:85-91`). | **Do not bind at the old all-sites shape.** A-I.1 requires a new weld site-supply socket before re-signing (`Leanspec/ChapI.lean:300-315,594-611`). New campaign **WELD-SITE-SUPPLY**, multi-node; after it, the field amendment/wrapper is 30–60 min. |
| `genhnBox2` | Literally `6 ≤ n → True` today (`I10_I15_I18.lean:176`); at any `n` it is `fun _ => True.intro`. Intended I.09 demand is `GenhnBox2 s := 3 ≤ s.μ → ∃ CarryCocycle ...` at arising carry sites (`F11.lean:46-51`). | Placeholder is immediate. The intended carrier is landed, as is `WeldObligations.genhnBox2` (`F28.lean:48-54`), but neither supplies arising sites. | Same **WELD-SITE-SUPPLY** socket and owner field amendment as `jd0`. Multi-node for site supply; 30–60 min final binding. |
| `windowPinning` | Today `WindowPinningAt n` unfolds to `True` (`I05.lean:90-94`). Intended body quantifies over degree-`n` stage data and requires `StageInterface.hwin` at every stage/genre (`I05.lean:22-27,90-93`). | Placeholder is immediate. H.89w supplies the consulted-height ledger and window clauses at the restricted `e₁=2` regime, but not `hwin` itself; I.05 says so explicitly (`I05.lean:22-27`). | New campaign **WINDOW-PINNING-RESOLUTION**: first type the real body against `StageInterface`, then combine H.89w with GENHN-3/GENIND-2 consulted-height supply. Multi-node; general case open, not a transcription. |
| `genhnHE` | Use-site demand is `6 ≤ n → GenhnHEAt n`; today `GenhnHEAt n = True` (`I06.lean:96-99`). Intended body: every degree-`n` stage leaf with `μ ≥ 3` has its σ-decision. | Placeholder is immediate. H.73w lands the `μ=3` dictionary/decision slice; I.06 records exactly that and leaves `μ≥4` open (`I06.lean:22-30,96-99`). | At current signatures no gap. Real resolution: wrapper/body for μ=3 (multi-node because the stage-leaf bridge is absent), then **GENHN-HE-TAIL** for `μ≥4` / HYP.143, research-open. At `n=2` the outer guard is impossible. |
| `genhnTow1` | Use-site demand is `8 ≤ n → GenhnTow1At n`; today `GenhnTow1At n = True` (`I07.lean:90-93`). Intended body is the C.93 deep-tower census conjunction. | Placeholder is immediate. Only C.93 clause (i), `tower_first_live`, is connected (`I07.lean:23-30,100-106`); it proves the sharp threshold, not the census. | New campaign **GENHN-TOW1-RESOLUTION**, covering HYP.67–71/78–80/142/143/144-BOX-2. Multi-node/research-open. At `n=2` and all `n<8` the outer guard is impossible. |

## Special accounting beyond the eleven field rows

### The five I-D12 names

The campaign prose counts five named I-D12 carriers: `NS7Termination`, `WindowPinningAt`,
`GenhnHEAt`, `GenhnTow1At`, and `TypeOfFaithful`.  Live HEAD has only the last four signed
`True` bodies: landed I.01 has already resolved `NS7Termination`, while signed leanspec has not.
`TypeOfFaithful` remains exactly `True` (`leanfinal/Uniformity/ChapI/I21.lean:98-110`) but is
**not a field of `CapstoneHypotheses`**.  It therefore cannot block constructing this record;
it blocks only consumers that separately require the I.21 trust-boundary identification.
`jd0` and `genhnBox2` are field-level placeholders counted separately by I-D12’s older “six
bodies” prose (`Leanspec/ChapI.lean:363-374`).

### The missing `w1` field

There is no `w1` field.  A-I.1 rules that this is a named debt, not permission to fold a vacuous
typed instance into `genhnBox2`: `W1Transport` can be false at a site, and the old all-sites
shape was machine-refuted (`Leanspec/ChapI.lean:310-324`; landed negative witness
`F12w.lean:106-114`).  F.28’s actual weld bundle has three separate fields — `jd0box2`,
`genhnBox2`, and `w1` (`F28.lean:48-54`).  The future weld socket and I.10 owner amendment must
bind all three together.

## DAG and minimal paths

```text
signed reconciliation ──> trustworthy ns7 field

ArisingCore + ChainRealization + RealizedInput + CC-12 views
  ├─> CanonicalLadderConfig ──> [HE7A, LB1, MP1, HVarthetaRes] ──> ladder
  └─> CanonicalDeepTwistConfig
        └─> per-live-level [HVarthetaRes + GentowW] ──> deepTwist

Chapter G counts ──> a0
Chapter G menu + A1 label family ──> a1
Chapter H InductionPackage/rate ──> a2

weld arising-site socket ──> jd0 + genhnBox2 + missing w1 amendment
H89w + GENIND consulted-height bridge ──> WindowPinning body
H73w μ=3 + HE tail ──> GenhnHE body
C93 + tower census tail ──> GenhnTow1 body

all eleven field proofs ──> CapstoneHypotheses n
  ├─> a2 projection ──> DrainageAt n / I.15 ──> TotalMassOne / I.18
  ├─> a0 projection (+ 0<n) ──> decided slice / I.16
  └─> a0 + a2 across all n ──> UniformityStatement / I.17
```

No capstone field logically supplies another field.  In particular, `deepTwist`'s antecedent
contains a `CanonicalLadderConfig`, but it does not consume the record's `ladder` proof; the two
supplier campaigns merely share the `HVarthetaRes` subproblem.  Likewise `a1` and the weld/window/
GENHN fields are not read by I.15–I.18 after construction, yet they still block construction of
the eleven-field record.  This is why “assembly landed” does not reduce the obligation to only
`a0+a2` (`leanfinal/Uniformity/ChapI/I10_I15_I18.lean:187-221`).

For the **current placeholder-bearing landed structure at `n=2`**, `a0`, `a1`, and `a2` have
Lean-core proofs (the probe replays them); `jd0` and `windowPinning` are `True`; and the three
numeric guards `6≤2`, `6≤2`, `8≤2` are impossible.  The minimal substantive inputs are therefore:

1. `NS7Termination` (available through the C.94 cite, or passed as an explicit hypothesis for a
   Lean-core-only constructor);
2. the universal `ladder` supplier at degree 2;
3. the universal `deepTwist` supplier at degree 2.

The S2 sockets do not shorten that path: they construct particular antecedents at **degree 4**
and supply neither universal implication’s conclusion.  For a future real-body version of the
record, weld and window fields re-enter even at low degree unless their re-signed bodies preserve
appropriate degree/site guards.

For **general `n`**, all eleven rows are present, with `a0/a1` newly open from `n≥3`; `genhnBox2` and
`genhnHE` become live at `n≥6`; and `genhnTow1` at `n≥8`.  The general critical path is not the
μ₃ chain alone: it is the join of LADDER-SUPPLY, DEEP-TWIST-SUPPLY, general exact counts/menu,
general induction/drainage, WELD-SITE-SUPPLY, and the three I-D12 body-resolution campaigns.

## Fleet-ready first wave

| node | output | dependencies | size / disposition |
|---|---|---|---|
| CHFD-S0 | owner reconciliation: signed I.01 body and state docs match already-landed C.94/I.01 | owner gate; `C94.lean:107-121`, `I01.lean:122-140` | 30–60 min transcription/review |
| CHFD-N2A0 | public `decidedSliceAt_two : DecidedSliceAt 2` | `uniformityStatement_two`, drainage tie; proof in probe | 30–60 min transcription |
| CHFD-N2A1 | public `menuLawAt_two : MenuLawAt 2` | I.03 gate proof | 30–60 min transcription |
| CHFD-N2A2 | public `drainageAt_two : DrainageAt 2` | `drainage_two` | 30–60 min transcription |
| CHFD-N3A1 | public `menuLawAt_three : MenuLawAt 3` | `coveringMenu_three` + label cells | 30–60 min transcription |
| CHFD-L0 | exact `CanonicalLadderConfig → LadderSupply` obligation record split into HE7A/LB1/MP1/ϑ subgoals | C130s18 views, E.24 | 30–60 min decomposition; launches multi-node campaign |
| CHFD-DT0 | exact `CanonicalDeepTwistConfig → DeepTwistConjunctLive` obligation record, per-live-index projections | C130s18, D.62, E.61/E.62 | 30–60 min decomposition; launches research campaign |
| CHFD-W0 | design the arising weld-site socket carrying `JD0Box2`, `GenhnBox2`, `W1Transport` together | A-I.1 ruling; F.28 | multi-node; statement/design review first |
| CHFD-WIN0 | type the intended `WindowPinningAt` body against `StageInterface.hwin` without asserting it | H.09/I.05/H89w | 30–60 min carrier transcription, then multi-node proof |
| M3-A0/A1 | enact fenced `hprev` and coordinated `chainNormBelow` re-index before μ₃ consumers | concurrent AMND unit; MU3 §§3–4 | already assigned; do not duplicate |

Rows CHFD-N2A0/A1/A2 and CHFD-N3A1 are immediately fireable and independent.  CHFD-L0,
CHFD-DT0, CHFD-W0, and CHFD-WIN0 are honest interface/decomposition nodes; none should be
mislabelled as a proof supplier.

## Verification record

- Direct `diff -u` of `Leanspec/ChapI.lean:812-840` and
  `I10_I15_I18.lean:151-179` is empty (eleven-field list exact).
- A declaration-anchored repository scan for results mentioning `LadderSupply` or
  `DeepTwistConjunctLive` finds only the two definitions themselves (`E24.lean:147` and
  `I10FreezeV2.lean:45`), supporting the negative supplier finding without relying on comment
  hits.
- `cd leanfinal && lake env lean scratch/CHFD_probe.lean` exits 0.  Its six named proof
  declarations have Lean-core footprints only; the separately printed landed NS7 wrapper has
  the intended `Tower.agnprw_termination` cite dependency.
