# READSOF F3 WALK (2026-08-08) — the B-M2 readsOf-debt consumer walk (synthesis pass 5 F3, queue #6)

CHARGE (F3): the narrowed `readsOf_landing_K0` recentering-branch debt — is it a
consumer need at all? Walk the truncated-carrier witness (the `ReadsOfFrom` face +
`gate_ftie_chain`'s f-tied landing) INTO the (K0) recentering-branch consumer and
adjudicate. Paper walk only: NO Lean file touched; the restatement below is a DRAFT
for orchestrator adjudication.

Sources read: `docs/SYNTHESIS_PASS5_2026-08-08.md` F3; `H1_BM2_2026-08-06.md` §S0/§S2/
§S4 (consolidated-opens item 4 + REV 15 re-pricing + POST-ACCEPTANCE disposition 4);
`H1/Conformance.lean`; `H1/RCWitness.lean`; `H1/RecParamE.lean` (transport);
`H1/TruncatedRun.lean`; `H1/GlueRun.lean`; `H1/SiteBlock.lean`; `H1/TowerStep.lean`;
`HC2/Defs.lean` (`ReadsOf`).

## 1. The debt of record (restated for a fresh reader)

`readsOf_landing_K0` (`H1/Conformance.lean:250`):

```
theorem readsOf_landing_K0 (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F)
    (hRO : ReadsOf p F n f H) (i : ℕ) (hi : i < H.nodes.length) :
    ∃ Φnext : Polynomial ℤ_[p],
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      ((H.nodes[i]'hi).species ≠ ReadSpecies.recentering →
        K0Conformant (H.nodes[i]'hi).σ (H.nodes[i]'hi).g (H.nodes[i]'hi).e Φnext) ∧
      ((H.nodes[i]'hi).species = ReadSpecies.recentering →
        K0Conformant (H.nodes[i]'hi).σ 1 1 Φnext)
```

The debt (§S0 synthetic-pair row; §S4 item 4; disposition 4): no compiled `ReadsOf`
run contains a recentering-SPECIES read, so the THIRD clause (the recentering branch)
has no on-file firing — its antecedent pair (`hRO : ReadsOf p F n f H` together with
`(H.nodes[i]'hi).species = ReadSpecies.recentering`) is not compiled-instantiable.
The landing CONTENT is meanwhile f-tied-witnessed on the `ReadsOfFrom` face:
`gate_ftie_chain : FTiedTruncLanding 2 U31.fq HK25.σ₁rec σ₂rc.Φ` (`GlueRun.lean:1089`)
chains U31's full fq-run into the truncated continuation `H₂rc` whose base read is
RCW's recentering read ROOT-respecied (`ν₁rcRoot := ν₁rc.respec ReadSpecies.root`),
with landing `landingKey_ν₁rcRoot : LandingKey ν₁rcRoot σ₂rc.Φ` (`GlueRun.lean:986`).

## 2. The consumption site (charge item 1)

**Corpus fact A (grep, exhaustive).** `readsOf_landing_K0` has ZERO term-level
consumers. All five corpus references are the declaration itself plus comments
(`Conformance.lean:38,76,250`; `SiteExhProbe.lean:233`; `RCWitness.lean:37`). No
compiled declaration takes its conclusion — in either branch — as input.

**Corpus fact B (the K0Conformant consumer graph is closed).** `K0Conformant` appears
in exactly three modules: `Conformance.lean` (def + the seven site corollaries),
`RecParamE.lean` (`k0_actual_of_recentering`, the (1,1)→actual-pair transport), and
`RCWitness.lean` (the terminal witness gates `rc_landingKey_gate` etc.). No module
outside this closed triangle consumes a `K0Conformant` hypothesis.

**The one compiled consumer slot for (K0)-at-a-recentering CONTENT.** The note's §S4
(i-c) consumer list for the [RC] legs names KP-STEP application at recentering reads.
Its compiled face is `kp_step` (`H1/TowerStep.lean:725`):

```
theorem kp_step (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h)
    (hprev : σ'.wPrev = ν.σ.w) (D : DevBound ν σ' M) :
    Nonempty (KPBlock σ' M)
```

The (K0)-bearing argument position is `hΦ : IsNodeLift ν σ'.Φ` (position 4). It is
threaded along histories by `key1_along_history`'s `hlink` row, 4th conjunct
(`H1/SiteBlock.lean:74-78`):

```
    (hlink : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      (H.nodes[i+1]'hi).σ.e = (H.nodes[i]'(by omega)).e ∧ ... ∧
      IsNodeLift (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi).σ.Φ)
```

and at a single step by `key1SiteBlock_step` (`SiteBlock.lean:158`, `kp_step`'s
binder block verbatim). The SiteBlock header (lines 38-43) displays exactly why this
is the recentering-branch consumer shape: under the HK-06 re-key, `HistoryCoherent`
supplies `IsNodeLift` ONLY on non-recentering legs, so at a recentering-species node
the `hlink`/`hΦ` slot is the displayed per-step row — the (K0) recentering-branch
obligation's only compiled demand point. **No declaration anywhere binds
`ReadsOf ... ∧ species = recentering`: the ReadsOf-SPECIES antecedent is demanded by
`readsOf_landing_K0`'s own hypothesis bundle and by nothing else.**

## 3. The walk (charge item 2): truncated-carrier witness into the consumer, type-by-type

**Leg 1 — what the species branch would deliver, fitted to the slot.** Suppose the
species antecedent WERE instantiable: `hRO : ReadsOf p F n f H` with node i
recentering. Firing the third clause yields `K0Conformant (H.nodes[i]).σ 1 1 Φnext`,
i.e. (`Conformance.lean:120-121`) exactly

```
  Φnext.Monic ∧ Φnext.natDegree = 1 * 1 * σ.Φ.natDegree
```

Offer this to `kp_step`'s `hΦ : IsNodeLift ν σ'.Φ`: **fails to unify** —
`IsNodeLift ν Φ` is definitionally `IsReadLift ν.σ ν.ψ ν.g ν.e ν.h Φ`, the full
D8 read-lift shape (realizer vector, coefficient-window membership, weight law,
twist-residual law, the Φ-expansion identity). `K0Conformant` carries monicity +
degree ONLY. The species branch's conclusion is strictly weaker than the one
compiled consumer slot demands: even a compiled ReadsOf-species witness would
discharge NOTHING through this branch. (The weaker `K0Conformant`-shaped consumers
— OL-1(a) on [RC] and the DevBound [RC] degree identification — were already
discharged at REV 10 via `landingKey_recentering_K0` + `k0_actual_of_recentering`,
never via `readsOf_landing_K0`; note §S4 (i-c) "DISCHARGED from this consumer list".)

**Leg 2 — what the truncated-carrier witness delivers, fitted to the same slot.**
The `ReadsOfFrom`-face witness is `gate_truncRun_H₂rc : TruncRunFrom HK25.σ₁rec
U31.fq H₂rc` (`GlueRun.lean:1048`; = `ReadsOfFrom HK25.σ₁rec score_σ₁rec U31.fq H₂rc`
by `readsOfFrom_iff_kernel`, `TruncatedRun.lean:244` — `Iff.rfl`), carrying per-read
landing `Or.inl landingKey_ν₁rcRoot`. Now the decisive type fact:

  `landingKey_ν₁rcRoot : LandingKey ν₁rcRoot σ₂rc.Φ`'s non-recentering clause is
  LITERALLY `IsNodeLift ν₁rc σ₂rc.Φ` — the proof body's `show IsNodeLift ν₁rc
  σ₂rc.Φ` (`GlueRun.lean:991`) succeeds because `Node.respec` rewrites only the
  species field and its three species laws (`GlueRun.lean:174-180`), and
  `IsNodeLift` reads only (σ, ψ, g, e, h), never species.

So the truncated witness hands `kp_step` its `hΦ` slot DIRECTLY at ν := ν₁rc,
σ' := σ₂rc — the recentering's fired key, f-tied to the ambient fq by
`gate_ftie_chain`. It unifies where the species branch's own conclusion could not.
For the `K0Conformant`-shaped consumers the same witness reproduces the exact
compiled conclusion: `landingKey_K0 ν₁rcRoot σ₂rc.Φ landingKey_ν₁rcRoot
(noConfusion)` gives `K0Conformant ν₁rcRoot.σ ν₁rcRoot.g ν₁rcRoot.e σ₂rc.Φ` =
`K0Conformant σ₁rec 1 1 σ₂rc.Φ` (respec preserves σ/g/e; ν₁rc has e = 1, g = 1,
`RCWitness.lean:216,220`) — byte-identical to the compiled `rc_landingKey_gate`
(`RCWitness.lean:298`). Content parity is total; the [RC] residue that remains
(kp_step's M, D, laws slots) is REC-SL proper + GRADED-READ, the separately-owned
opens — untouched by this walk, exactly as displayed.

**Leg 3 — where the truncated witness fails to unify with the SPECIES antecedent
itself (why the debt looked open).** Two independent type walls, both by design:
(i) `ReadsOf` (`HC2/Defs.lean:320`) demands `HistoryCoherent H`, whose base is the
standard root frame — `H₂rc`'s head stage is the DEEP σ₁rec (Φ = fq, natDegree 2),
so `hRO` cannot be instantiated at H₂rc; this is the C-e exhibit's content (a real
tower's recentering hosts nowhere on its own f — the general same-f From→ReadsOf
converse is DEAD, and the TruncatedRun extension exists BECAUSE it is dead).
(ii) Even inside a hypothetical host, the landing node of a truncated base is
ROOT-species by `History.root_iff`, so the branch guard `species = recentering` is
false at every truncated base — `ν₁rcRoot` enters `readsOf_landing_K0`-shaped
conclusions through the NON-recentering clause. The species antecedent is thus
uninstantiable on the truncated carrier BY CONSTRUCTION, while every consumer-shaped
consequence of the species branch is delivered anyway.

## 4. VERDICT (charge item 3): (a) — the consumer accepts the truncated-carrier witness, and the species form has NO consumer

Stronger than F3's (a): not only does every (K0)-recentering consumer obligation go
through with the `ReadsOfFrom` witness + `gate_ftie_chain`'s f-tied landing — the
species branch's own conclusion (`K0Conformant`, monic + degree) could never have
fed the one compiled consumer slot (`kp_step`'s `hΦ : IsNodeLift`), which the
truncated witness feeds literally. The debt is a pure non-vacuity DISPLAY on one
branch of one carrier corollary, not a proof obligation gating anything. The F5
run-forge is NOT needed for this consumer (the forge question survives only for
`junc_bundle`'s deg f > deg Φ₁ gate and the GR stage forge, adjudicated elsewhere).

## 5. DRAFT RESTATEMENT (charge item 3) — NOT APPLIED; orchestrator adjudicates

Mechanics: per the B-M2 note's annotation discipline (REV 15 precedent) this is an
ADDITIVE bracket — no accepted sentence edited, acceptance history untouched, clean
counter not reset (annotation of an external walk, not correction of accepted
content). Lean edits: NONE (a comment-only sync of `RCWitness.lean:37` MAY ride a
future campaign; the sentence as written stays TRUE — it claims only
unwitnessed-ness — so census row C237 needs no supersedure).

### BEFORE (the two displays of record, quoted)

§S4 consolidated list item 4 (acceptance-time, byte-frozen):

> 4. **the `readsOf_landing_K0` recentering-branch witness debt** — that
>    branch stays UNWITNESSED-ON-FILE [REV 10 scope; §S0 synthetic-pair row].

REV 15 §S4 bracket, item-4 sentence (tail):

> Item 4 the `readsOf_landing_K0` recentering-branch witness debt: STANDS,
> NARROWED — the recentering landing (ν₁rc's fired key σ₂rc.Φ) is now witnessed
> f-tied at the `ReadsOfFrom`/`TruncRunFrom` face (`gate_ftie_chain` chains through
> `ν₁rcRoot` = ν₁rc ROOT-respecied inside `H₂rc`). But no compiled `ReadsOf` run
> contains a recentering-SPECIES read, so the branch antecedent is still not
> compiled-instantiable.

POST-ACCEPTANCE disposition 4 verdict line: "STANDS, NARROWED".

### AFTER (proposed additive REV 16 bracket, to follow the REV 15 §S4 bracket)

> **[REV 16 — the F3 consumer walk (`READSOF_F3_WALK_2026-08-08.md`): item 4 is
> RESTATED AT THE `ReadsOfFrom` FACE; the species form carries a NO-CONSUMER
> disposition. The walk's compiled facts: (i) `readsOf_landing_K0` has ZERO
> term-level consumers (all corpus references are the declaration + comments);
> (ii) the only compiled consumer slot for (K0)-at-a-recentering content is
> `kp_step`'s `hΦ : IsNodeLift ν σ'.Φ` (`H1/TowerStep.lean:725`; threaded as
> `key1_along_history`'s `hlink` 4th conjunct and `key1SiteBlock_step`'s verbatim
> binder, `H1/SiteBlock.lean`) — a slot the species branch's own conclusion
> `K0Conformant σ 1 1 Φnext` (monic + degree only) could NEVER feed, and which the
> `ReadsOfFrom`-face witness feeds LITERALLY (`landingKey_ν₁rcRoot`'s
> non-recentering clause is definitionally `IsNodeLift ν₁rc σ₂rc.Φ`; `Node.respec`
> rewrites only the species fields); (iii) the `K0Conformant`-shaped [RC] consumers
> (OL-1(a), the DevBound degree identification) were discharged at REV 10 through
> `landingKey_recentering_K0` + the transport, never through `readsOf_landing_K0`,
> and the same conclusion re-derives on the truncated witness via `landingKey_K0`
> at the ROOT-respecied node (= the compiled `rc_landingKey_gate`, byte-identical).
> THE DEBT OF RECORD is accordingly RESTATED: f-tied recentering-landing coverage
> is WITNESSED at the `ReadsOfFrom` face (`gate_ftie_chain`); the ReadsOf-SPECIES
> antecedent pair (`hRO : ReadsOf p F n f H` + `species = recentering` at the
> landing node) gates NO consumer and stands ONLY as the compiled fence display
> that the general same-f From→ReadsOf converse is DEAD (the C-e exhibit — the
> truncated carrier exists BECAUSE that converse fails). Item 4 therefore leaves
> the opens list as an OBLIGATION and re-enters as a FENCE DISPLAY; the [RC]
> obligations that remain open on B-M2's face are exactly REC-SL proper and
> GRADED-READ's frame residue, as already listed. Disposition 4's two discharge
> routes (a direct recentering-bearing `ReadsOf` run — the F5 run forge; the glue
> route behind `junc_bundle`) stay priced there for anyone who ever wants the
> species form FOR ITS OWN SAKE; neither is a consumer need.]**

### The no-consumer disposition of the species form (one paragraph, for the
POST-ACCEPTANCE section, superseding disposition 4's verdict line only)

> **Disposition 4 (re-priced by the F3 walk) — the `readsOf_landing_K0`
> recentering-branch witness debt: NO CONSUMER; RESTATED at the `ReadsOfFrom`
> face.** The branch's antecedent stays uninstantiable exactly as recorded, but
> the walk established that nothing consumes the branch: not the corpus (zero
> term-level references), not the KP-STEP route (its slot demands `IsNodeLift`,
> which the branch's `K0Conformant` conclusion cannot supply and the truncated
> witness supplies literally), not the OL-1(a)/DevBound row (REV 10 transport,
> independent of this branch). The debt is a display of the dead From→ReadsOf
> converse, not an obligation. FORGE IMPLICATION (F5): no run-forge target is
> chartered by this consumer; the deep-instance forge question survives only on
> `junc_bundle`'s deg f > deg Φ₁ gate and the GR stage-forge, adjudicated at
> their own rows.

## 6. Verdict (b) branch — N/A

Charge item 4 does not fire: no consumer genuinely needs the species form, so no
run-forge species target is specified from this walk. (If the orchestrator
nevertheless wants the species form witnessed for display completeness, the
cheapest named target remains disposition 4's glue route: `readsOf_glue` with
sp' = recentering at a junction whose `junc_bundle` leg is compiled — i.e. it
funnels into the SAME `junc_bundle` wall as disposition 3, adding no new forge
species.)

— READSOF F3 WALK unit, 2026-08-08. Paper walk; zero Lean edits; draft only.
