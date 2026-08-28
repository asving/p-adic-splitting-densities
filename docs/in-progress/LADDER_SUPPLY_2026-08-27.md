# LADDER-SUPPLY campaign blueprint

**Date:** 2026-08-27  
**Unit:** LDEC (BLUEPRINT decomposer)  
**Scope:** the four suppliers exactly equivalent to the capstone `ladder` field in
`leanfinal/Uniformity/ChapI/IFC0.lean`; no proof of an open supplier is claimed here.

**[VAUD, 2026-08-27]** The four stop-line validity audits have now run.  Their certificates
are `leanfinal/scratch/VAUD_probe.lean`; adjudication is recorded below and in
`runs/wave-b/verdict_VAUD.md`.

**[LVT, 2026-08-28]** The vartheta owner amendment is ENACTED as supersession twins —
NEW `leanfinal/Uniformity/ChapI/IFC5.lean`, IFC0 byte-untouched as the tension record; see
the dated `[LVT 2026-08-28]` section at the end of this file and `runs/wave-b/verdict_LVT.md`.

## Verdict

The decomposition is exact and already machine checked:

```text
LadderField n
  ↔ LadderPackageSupplier n
  ∧ LadderLB1Supplier n
  ∧ LadderMP1Supplier n
  ∧ LadderVarthetaSupplier n.
```

This is `IFC0.ladderField_iff_suppliers` (`IFC0.lean:120-137`), and the reverse assembly is
`ladderField_of_suppliers` (`IFC0.lean:141-147`). Therefore there is no fifth join theorem
and no weakening hidden in this campaign.

There is, however, a stop-line before a proof fleet is launched. Three conclusions are
strictly broader than the data visibly pinned by the guard:

1. `LB1Carrier` quantifies over **every** `RungInterface C B`, not an interface exported by
   the arising realization (`E39.lean:110-114`).
2. `MP1Carrier` quantifies over **every** recentered `B' : BlockData C` satisfying a key
   equality and divisibility, while `BlockData` does not itself certify that its key is
   irreducible; the conclusion does (`E40.lean:152-178`).
3. `LadderVarthetaSupplier` requires every external `i ≥ 3` (`IFC0.lean:108-115`), whereas
   `GaugeFamilyViewEq` pins the supplied families only when `GaugeLive core.r i`, i.e.
   `1 ≤ i < core.r` (`C130vw.lean:214-223`). Every finite-depth witness consequently has
   indices demanded by the conclusion but invisible to the guard.

The last item is a structural scope mismatch, not merely missing gauge mathematics. The
campaign must first run the negative/validity probes below. If any supplier is refuted at an
inhabited arising socket, exact equivalence means that the capstone field itself needs an owner
amendment; a proof unit must not repair it by adding a conclusion-shaped guard hypothesis.

Honest campaign sizes:

| Supplier | Present status | Size after its validity gate |
|---|---|---|
| HE7A/package | meaningful but no C-to-E exporter | **XL:** roughly 1,500–3,000 new Lean lines, 3–6 focused weeks, plus unfinished F1/F2 prerequisites |
| LB1 | schema landed; arbitrary-interface endpoint unproved and possibly overstrong | **L/blocked:** 700–1,500 lines, 1–3 weeks if retained and true; owner repair first otherwise |
| MP1 | record typed; quotient/interface/irreducibility endpoint absent | **L/blocked:** 500–1,200 lines, 1–2 weeks plus the queued cite gate; owner repair first if the universal `B'` target fails |
| vartheta | `HVarthetaRes` typed; guard/result scope mismatch and twist obstruction | **research/blocked:** no honest proof estimate before adjudication; after repair, likely 300–800 lines, 3–7 days |
| degree-2 non-vacuity | no landed inhabitant | **L:** roughly 600–1,200 lines, 1–2 weeks, reusing the S2 depth-one anchor but building a new occurrence/realization |

These are campaign sizes, not the 30–60 minute wrapper grains listed later.

### [VAUD] Stop-line adjudication

| Audit | Adjudication | Machine tooth / exact consequence |
|---|---|---|
| LB1 inhabited socket | **NOT VALIDATED; stop remains** | `s2_degree_four_socket` supplies the landed honest antecedent and `lb1_inhabited_socket_tooth` shows that, after it, LB1 still accepts an independently quantified arbitrary `I`.  No realization-link premise is present.  No malicious `I` on the landed S2 carrier was constructed, so this is not promoted to a refutation of `LB1Carrier` at an arising pair. |
| MP1 cite hypotheses | **CITE ROUTE REFUTED** | `mp1_inhabited_socket_forces_irreducible` derives `hirr` from only `Λ ≠ 0`, `deg Λ < D`, `B'.Φ = B.Φ-Λ`, and `B'.Φ ∣ B.F` (plus `B' : BlockData C`). The checked source record does not say this. [GN15] Thm 2.3 starts with an inductive valuation/MacLane chain, a key polynomial `φ` in a specified tangent class, and a monic `g`; its irreducible-leaf clause also needs residual multiplicity one. GMN Thm 2.11 constructs a representative/key polynomial of a type with prescribed residual data. Neither identifies an arbitrary divisibility-only `B'.Φ` with that representative. |
| vartheta all `i ≥ 3` | **GUARD-DERIVABILITY REFUTED; OWNER AMENDMENT REQUIRED** | `gauge_view_offRange_kernel_replacement` proves that an arbitrary dependent `(v,ρ)` package and `q` may be replaced at every `¬ GaugeLive` index without changing `GaugeFamilyViewEq`; `vartheta_sitewise_negative` gives a concrete false `HVarthetaRes`; and `s2_three_not_gaugeLive` pins the first demanded S2 index `3` outside the landed depth-two range.  Thus the live-range guard cannot derive the present unbounded demand. |
| closed degree two | **NOT CONSTRUCTIBLE FROM LANDED MATERIAL** | `s2DepthOne`, `s2DepthOneKeyChain`, and `s2AnchorCalculus` land only the tower/key/calculus anchor.  The missing first object is a `SplitNodePointSource` on `s2DepthOne`, hence a `ChainRealization`; after it one still needs an `ArisingCore … 2` occurrence and `RealizedInput`.  The only landed source/realization is stage/depth two and its input is definitionally degree `4` (`s2_degree_four_socket`, `landed_s2_degree_ne_two`). |

The vartheta adjudication is deliberately about **derivability from the enacted guard**.  It
does not claim a closed countermodel to the whole universal supplier: the repo has no closed
degree-two socket, and the landed S2 socket retains its honest completeness/threshold context.
It does prove that any proof whose only family information is `GaugeFamilyViewEq` cannot
justify an off-range site.  Adding an HVR-shaped premise to the guard remains forbidden.

### [VAUD] Proposed vartheta owner amendment — exact IFC0 replacement

The smallest honest target keeps the first three fields and restricts the fourth to indices
live in a realization witnessing the **same** external socket data.  The fully elaborated
definitions and proof are in `VAUD_probe.lean` as `CanonicalLadderLiveAt`,
`LadderSupplyLive`, `LadderVarthetaSupplierLive`, `LadderFieldLive`,
`ladderFieldLive_iff_suppliers`, and `ladderFieldLive_of_suppliers`.

The exact signature diff to `IFC0.lean` is (insert the two new declarations immediately
before `LadderField`, then make the two shown replacements):

```diff
+def CanonicalLadderLiveAt {O : Type} [CommRing O] {K : Type} [Field K]
+    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
+    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
+    (L : Type uL) [Field L] [Algebra Kt L]
+    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
+    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n i : ℕ) : Prop :=
+  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
+    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
+    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
+      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
+    (X : Tower.RealizedInput core A)
+    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG} core.r),
+    Tower.SlotViewEq X eK C ∧
+    (∃ hC : C = X.stageCarrierTransport eK,
+      Tower.BlockViewEq X eK (hC ▸ B)) ∧
+    Tower.GaugeFamilyViewEq X (N.transport eG)
+      (fun j => (v j).comp eG.symm.toMonoidHom)
+      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
+    Tower.GaugeLive core.r i
+
+structure LadderSupplyLive {O : Type} [CommRing O] {K : Type} [Field K]
+    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
+    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
+    (L : Type uL) [Field L] [Algebra Kt L]
+    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
+    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
+  package : Ladder.HE7APackage.{0, 0, uW} C B
+  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
+  mp1 : Ladder.MP1Carrier.{0, 0, uW} C B
+  vartheta : ∀ i ≥ 3, CanonicalLadderLiveAt C B G Kt L N v ρ q n i →
+    Ladder.VarthetaRes G Kt L N v ρ q i

 def LadderField (n : ℕ) : Prop :=
   ∀ (O : Type) [CommRing O] (K : Type) [Field K]
     (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
     (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
     (L : Type uL) [Field L] [Algebra Kt L]
     (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
     (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
     CanonicalLadderConfig C B G Kt L N v ρ q n →
-    Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q
+    LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n

 def LadderVarthetaSupplier (n : ℕ) : Prop :=
   ∀ (O : Type) [CommRing O] (K : Type) [Field K]
     (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
     (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
     (L : Type uL) [Field L] [Algebra Kt L]
     (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
     (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
     CanonicalLadderConfig C B G Kt L N v ρ q n →
-    ∀ i ≥ 3, Ladder.VarthetaRes G Kt L N v ρ q i
+    ∀ i ≥ 3, CanonicalLadderLiveAt C B G Kt L N v ρ q n i →
+      Ladder.VarthetaRes G Kt L N v ρ q i
```

There are no hidden hypotheses. With these two replacements, the body of
`ladderField_iff_suppliers` remains the same projection/constructor proof and is machine
checked by `ladderFieldLive_iff_suppliers`; reverse assembly is checked by
`ladderFieldLive_of_suppliers`.

This is an owner proposal, not an enacted signature change.  Since current
`CapstoneHypotheses.ladder` returns E.24's unbounded `LadderSupply`, owner acceptance must also
rebind that field (or move `LadderSupplyLive` into E.24).  An IFC0-only edit that pretends the
old capstone field is definitionally unchanged would be false.

## 1. Exact demand and landed base

`CanonicalLadderConfig` is definitionally C130s18's guard (`I10_I15_I18.lean:103-112`).
Unfolded, it supplies existential `IsDomain O` and DVR instances, a field `E`, an
`ArisingCore n`, `ChainRealization`, `RealizedInput`, carrier and gauge equivalences, and the
slot/block/gauge view equalities (`C130s18.lean:149-175`). Given any `RealizedInput`, the
generic constructor of that guard is landed at `C130s18.lean:238-247`.

The target is E.24's record (`E24.lean:147-155`):

| Field | Exact carrier |
|---|---|
| `package` | `HE7APackage C B = Nonempty (RungInterface C B)` (`E24.lean:130-132`) |
| `lb1` | `LB1Carrier C B` (`E39.lean:110-114`) |
| `mp1` | `MP1Carrier C B` (`E40.lean:172-178`) |
| `vartheta` | `∀ i ≥ 3, VarthetaRes … i`, definitionally sitewise `HVarthetaRes` (`E61.lean:145-157`) |

E.24 explicitly discharges none of them. Chapter E mostly provides schemas. Its own
level-two obligation audit says the polygon, count, forcing, carrier, and composed-key rank
legs remain C-supplied placeholders (`E23.lean:49-60`) and warns that E-internal proofs never
supply carrier content (`E23.lean:130-136`).

The only landed application resembling non-vacuity is S2 at **degree 4**, conditional on
`S2LevelOneThreshold` and adic completeness (`C130sg.lean:522-535`). It is not an `n = 2`
witness and proves only the antecedent.

## 2. Per-supplier analysis

### 2.1 `LadderPackageSupplier` / HE7A

**Demand.** For every degree-`n` arising guard, construct one `RungInterface C B`. Its fields
are the side ledger and window inequalities, positive side lengths and their sum to `B.μ`,
residual-factor ledgers and residual-degree accounting, root/class counts, nonemptiness, local
forcing, exhaustion, and a well-founded secondary rank (`E12.lean:130-157`). “One interface”
is existential, but every field is contentful.

**Landed.** The guard exposes the actual occurrence and exact views (`C130s18.lean:149-175`).
E.14–E.16, E.29, E.31, E.33, E.36–E.38, E.42, E.55–E.56 provide numerical/fold/lift/rank
schemas; E.23 identifies the still-C-supplied parts (`E23.lean:49-60`).

- `EFF.HE7.13` (`spec/EFF-HE7.md:745`) proves the level-two side sum and separable-class exact
  sizes/orbits under the proper-block and separability hypotheses.
- `EFF.HE7.14` (`spec/EFF-HE7.md:800`) gives the repeated-residual trichotomy/refinement wiring;
  its mixed-node route uses the annex block split.
- `EFF.HE7.15` (`spec/EFF-HE7.md:854`) gives finite ladder/rank bounds, with the rider that
  level 3 is only *not excluded* first at degree 16.
- `EFF.HE7.16` (`spec/EFF-HE7.md:943`) is the composition corollary; its all-degree clause
  retains annex/arc-grade conditionality.
- `EFF.HE7.96` (`spec/EFF-HE7.md:3679`) is the per-class partition/block mathematics.
  `PartitionLeg` and `PartitionLeg.toBlockSuite` are landed (`E57p.lean:144-246`).
- F1/F2 are prerequisite candidates, not exporters. `BlockFrontier` remains only a carrier
  (`C35.lean:278`); no `blockFrontier_of_context` exists in `leanfinal`. `ClassSizeSupplyData`
  is only a structure (`C140defs.lean:76-101`); no `classSize_supply` theorem exists.

**Gap.** No theorem takes the hidden `RealizedInput` and produces the actual
polygon/residual/class/rank fields. The HE7 prose assumes the level-two datum, proper block,
residual factorization, and standing `Ψ ∤ f_S` convention; the guard does not hand those to
Lean in E.12 vocabulary. The exporter must extract a frontier, transport exact reads, build
linear and higher factor ledgers, prove count/forcing/nonempty/exhaustion, install a real rank,
and cover pure, mixed, refined, and jump nodes.

The source also leaves HE7-12(d)/HE7-13 mutual dependence as an undisplayed simultaneous
induction (`EFF-HE7.md:5885-5910`). Lean needs its joint invariant, base, and step. The source
claims characteristic two but records no test coverage; that is a coverage debt, not a proof.

**Size.** XL: 1,500–3,000 lines over 8–15 mathematical nodes after F1/F2, with hostile teeth
for pure, split, higher-residual, refined, and jump branches. The final `Nonempty` wrapper is
only 30 minutes.

### 2.2 `LadderLB1Supplier`

**Demand.** For **every** `I : RungInterface C B`, a multi-side or nonseparable-side trigger
must yield `Nonempty (BlockSuite I)` (`E39.lean:110-114`). `BlockSuite` includes product,
coprimality/disjointness, degree, one-side/pure-residual, cover/count, and threshold clauses.

**Landed.** `PartitionLeg I` carries the typed class partition and per-class blocks
(`E57p.lean:144-176`), and `PartitionLeg.toBlockSuite` assembles the suite
(`E57p.lean:188-246`). E57c says the arena bridge from C tower objects to `PartitionLeg` at an
arbitrary row is missing (`E57c.lean:63-67`). The LDEC probe verifies:

```text
(∀ triggered I, Nonempty (PartitionLeg I)) → LB1Carrier C B.
```

**Gap/validity gate.** The carrier asks for a partition for an **arbitrary E-side interface**.
`RungInterface` is a numerical shadow and does not connect fabricated side/class data to
`B.F`. The landed certificate constructs a legal two-side interface over `X²+X+1` for which
`LB1Carrier` is false (`verification/om4_resign_nontriviality.lean:144-220`).

That abstract counterexample is not an arising socket, so it does not yet refute the supplier.
But a C exporter for one canonical interface cannot establish this universal target. First
either construct an inhabited arising guard supporting the malicious-interface argument, or
prove a new arising-block theorem realizing every legal numerical `I`. The latter is much
stronger than HE7.96. If the negative tooth fires, bind LB1 to the canonical interface or a
realization-linked interface by owner amendment.

**Size.** Blocked. If retained and true, 700–1,500 lines, 1–3 weeks; final wrapper 30–45 min.

**[VAUD] Audit result.** The landed S2 degree-four guard is a real antecedent at the stated
threshold/completeness context, but `lb1_inhabited_socket_tooth` confirms that the next binder
is still an arbitrary, independently supplied `I`. The guard contains no equality, transport,
or provenance field connecting that `I` to its `RealizedInput`. Therefore LB1 has **not passed
validity**. The abstract `C₁/B₁/I₁` counterexample still does not rebase itself onto S2, so
VAUD records **not validated**, not a false claim at an arising pair. LS-G0 remains a stop.

### 2.3 `LadderMP1Supplier`

**Demand.** For every nonzero `Λ` of degree `< C.D` and every `B' : BlockData C` with
`B'.Φ = B.Φ - Λ` and `B'.Φ ∣ B.F`, construct `MidPeelEmission B B'`
(`E40.lean:172-178`). Nontrivial fields are a quotient block at the recentered key, peel
identity, mass, inherited threshold, quotient `RungInterface`, and irreducibility of the
recentered key (`E40.lean:152-164`). `hef` is free from `B'.hΦdeg.trans C.hef`, as probed.

**Landed.** The record and carrier are typed. E.40 names the intended gate-(b) source
`recentered_key_emission` ([GN15] Thm 2.3 + (2.1), GMN Thm 2.11), but no such theorem or
equivalent endpoint is present (`E40.lean:145-148`).

**Gap/validity gate.** One must produce the quotient, exact product and mass, threshold,
quotient interface, and irreducibility. Divisibility does not imply irreducibility. The landed
countermodel uses `Λ=4` and reducible `X²-4` to refute `MP1Carrier` at a legal abstract block
(`verification/om4_resign_nontriviality.lean:284-365`). Determine whether the arising guard
enforces the cite's actual hypotheses for every current `B'`. If extra hypotheses are absent,
amend the carrier; adding irreducibility to the guard would swallow the conclusion.

**Size.** Blocked. If true, 500–1,200 lines, 1–2 weeks including cite landing and interface
reuse; final record/supplier assembly 45–60 min each.

**[VAUD] Audit result.** The cite check fails at the exact hypotheses. The machine tooth
`mp1_inhabited_socket_forces_irreducible` exposes that the current carrier requires `hirr`
after only recentering/divisibility data. [GN15] Thm 2.3 requires the MacLane/key-polynomial
and residual-multiplicity-one package; GMN Thm 2.11 constructs a representative of a type
from prescribed residual data. Thus the proposed cite cannot fill `hirr` for the arbitrary
current `B'`: the carrier has no premise identifying `B'.Φ` with the cited representative. Repair choices
are to quantify only cited key-polynomial lifts, or add a non-conclusion-shaped
minimality/key-polynomial premise to the **MP1 trigger** after owner review. It may not be
added to `CanonicalLadderConfig`.

### 2.4 `LadderVarthetaSupplier`

**Demand.** Every `i ≥ 3` must satisfy D.62's sitewise statement: for every `s`, the ambient
residue of `N.varthetaEl (q i) s` lies in the image of a `Kt` unit (`D62.lean:81-85`;
`E61.lean:145-157`).

**Landed.** Arena/canonical agreement closes HVR (`D62.lean:89-95`), and τ-letter embedded
values close it (`D62w.lean:94-103`). Neither is in the guard. `twistNode` changes the
canonical read while preserving the realization (`C130s18.lean:407-465`), and
`arenaAgreement_not_uniform`/`embeddedValue_not_uniform` defeat uniform extraction of those
trap hypotheses (`C130s18.lean:498-552`).

There is a decisive scope defect. `GaugeFamilyViewEq` guards every equation by
`GaugeLive core.r i` (`C130vw.lean:214-223`) and off-range `q` updates are invisible
(`C130vw.lean:321-333`; ladder lint `C130s18.lean:640-651`). The supplier has no live premise
and no exposed depth; every finite witness has infinitely many demanded off-range sites.

**Gap.** Prove or refute invariance of the unbounded conclusion under all off-range data the
guard permits. The definitions predict refutation because HVR depends exactly on
`(v i,ρ i,q i)`. A complete negative tooth combines an inhabited socket, dependent off-range
replacement, and the concrete false HVR certificate (`verification/om4_resign_nontriviality.lean:432-441`).

If refuted, use a live-range target like `DeepVarthetaSupplier`, or definitionally fix canonical
off-range values. The latter must be a producer definition, not an added residue-law premise.

**Size.** Research-blocked. Negative probe 2–5 days after a concrete socket. Repaired live
scope plausibly 300–800 lines; current unbounded form has no defensible proof estimate.

**[VAUD] Audit result.** The guard-derivability question is now **REFUTED**. The probe proves
dependent off-range replacement for the complete `(v,ρ,q)` site, not merely for `q`, and a
separate concrete false HVR. At the landed S2 depth, `i=3` is already off range. The corrected
owner proposal is `LadderVarthetaSupplierLive`: it adds `CanonicalLadderLiveAt … i`, which
re-exhibits the same full realization and `GaugeLive core.r i`, as a premise to the conclusion.
The corresponding repaired record and four-way join elaborate in the probe. This is a scope
repair, not a vartheta proof.

## 3. Dependency DAG

```text
Validity gates: LB-arbitrary-I, MP-arbitrary-B', V-off-range/twist
                         │
                         ├── refutation ──> owner amendment ──> re-pin exact L0 split
                         │
                         └── survives
                              │
       F1/F2 + C exact reads ─┼──> C-to-E RungInterface exporter ──> HE7A
                              │                       │
       HE7.96 class blocks ───┴──> arbitrary-row PartitionLeg ────> LB1
                              │
       recentered-key cite + quotient/interface exporter ─────────> MP1
                              │
       canonical residue descent/agreement at repaired scope ─────> vartheta
                                                                      │
                         four supplier proofs ── REUSE IFC0 join ────> LadderField
```

The degree-2 non-vacuity track is an exit dependency: no degree-2 positive-conditionality
claim may be made until it lands.

## 4. Formalization-trivial nodes (30–60 minute grain)

These contain no new mathematics. `NEW` means a new wrapper/record constructor; `REUSE` means
the theorem exists and must not be duplicated. Hard exporters and validity proofs are absent.

| ID | Kind | Action | Exact inputs (file:line) | Output |
|---|---|---|---|---|
| LS-T00 | REUSE | Pin exact four-way equivalence | `leanfinal/Uniformity/ChapI/IFC0.lean:120-137` | `ladderField_iff_suppliers` |
| LS-T01 | REUSE | Pin four-to-field assembly | `leanfinal/Uniformity/ChapI/IFC0.lean:141-147`; `leanfinal/Uniformity/ChapE/E24.lean:147-155` | `ladderField_of_suppliers` |
| LS-T02 | NEW | Destructure guard; install domain/DVR instances | `leanfinal/Uniformity/ChapC/C130s18.lean:169-175` | wrapper helper |
| LS-H00 | REUSE | Rewrite package to `Nonempty RungInterface` | `leanfinal/Uniformity/ChapE/E24.lean:130-132`; `leanfinal/Uniformity/ChapE/E12.lean:130-157` | unfold only |
| LS-H01 | NEW | Package completed HE7 certificate as `RungInterface` | `leanfinal/Uniformity/ChapE/E12.lean:130-157`; hard exporter | structure literal |
| LS-H02 | NEW | Lift completed exporter to package supplier | `leanfinal/Uniformity/ChapI/IFC0.lean:74-81`; LS-T02/H01 | exact binder wrapper |
| LS-L00 | REUSE | One `PartitionLeg` to one `BlockSuite` | `leanfinal/Uniformity/ChapE/E57p.lean:188-246` | `toBlockSuite` |
| LS-L01 | NEW | Map `Nonempty PartitionLeg` to `Nonempty BlockSuite` | `leanfinal/Uniformity/ChapE/E57p.lean:188-246`; `leanfinal/Uniformity/ChapE/E39.lean:110-114` | probed helper |
| LS-L02 | NEW | Curry partition endpoint into `LB1Carrier` | `leanfinal/Uniformity/ChapE/E39.lean:110-114`; LS-L01 | trigger wrapper |
| LS-L03 | NEW | Lift carrier to `LadderLB1Supplier` | `leanfinal/Uniformity/ChapI/IFC0.lean:85-92`; LS-T02/L02 | binder wrapper |
| LS-M00 | NEW | Assemble `MidPeelEmission` from seven real fields | `leanfinal/Uniformity/ChapE/E40.lean:152-164` | probed record literal |
| LS-M01 | NEW | Curry recentered endpoint into `MP1Carrier` | `leanfinal/Uniformity/ChapE/E40.lean:172-178`; LS-M00 | trigger wrapper |
| LS-M02 | NEW | Lift carrier to `LadderMP1Supplier` | `leanfinal/Uniformity/ChapI/IFC0.lean:96-103`; LS-T02/M01 | binder wrapper |
| LS-V00 | REUSE | Rewrite `VarthetaRes` to `HVarthetaRes` | `leanfinal/Uniformity/ChapE/E61.lean:145-157` | constructor/projection |
| LS-V01 | REUSE | Close HVR from arena agreement | `leanfinal/Uniformity/ChapD/D62.lean:89-95` | landed theorem |
| LS-V02 | REUSE | Close HVR from τ-letter laws | `leanfinal/Uniformity/ChapD/D62w.lean:94-103` | landed theorem |
| LS-V03 | NEW | Wrap owner-approved sitewise endpoint | `leanfinal/Uniformity/ChapI/IFC0.lean:108-115`; LS-V00 | index/binder wrapper |
| LS-A00 | REUSE | Assemble four suppliers | `leanfinal/Uniformity/ChapI/IFC0.lean:141-147` | `LadderField n` |
| LS-A01 | NEW | Project four fields at concrete tooth | `leanfinal/Uniformity/ChapE/E24.lean:147-155`; N2 guard | four bite lemmas |
| LS-A02 | NEW | Axiom and signature anti-drift audit | `leanfinal/Uniformity/ChapI/IFC0.lean:59-147`; wrappers | `#print axioms`, pins |

Each `NEW` row is 10–40 lines after its hard input exists. Dispatching them earlier would only
create proposition-valued placeholders and is forbidden.

## 5. Hard nodes and ordering

| ID | Task | Status / size |
|---|---|---|
| LS-G0 | LB1 arbitrary-`I` negative audit at inhabited arising `(C,B)` | **[VAUD] PARTIAL / NOT VALIDATED:** inhabited-socket universal bite proved; hostile arising `I` still absent |
| LS-G1 | MP1 arbitrary-`B'` audit against cite hypotheses | **[VAUD] FAILED:** cited results do not supply `hirr` at current hypotheses |
| LS-G2 | Off-range family replacement and false-HVR tooth | **[VAUD] COMPLETE / REFUTED:** dependent replacement + false HVR; live-range owner amendment proposed |
| LS-H10 | C exact frontier/slot/residual prerequisites | **OPEN F1/F2**, at least 1,000–2,000 lines |
| LS-H11 | HE7 refined-key joint induction | **NEW proof/formalization**, 2–4 days after APIs |
| LS-H12 | `RealizedInput → RungInterface`, pure/separable | **NEW math**, 250–450 lines |
| LS-H13 | repeated-linear refine and rank | **NEW math**, 250–500 lines |
| LS-H14 | higher-residual jump | **NEW math**, 250–500 lines |
| LS-H15 | mixed-node HE7.96 routing/join | **NEW math**, 350–700 lines |
| LS-L10 | C object to `PartitionLeg I` at target scope | **genuinely missing**, 500–1,000 lines if valid |
| LS-M10 | Owner-approved `recentered_key_emission` cite | **missing cite landing**, 150–350 lines |
| LS-M11 | Quotient block and full quotient interface | **NEW math**, 300–700 lines |
| LS-V10 | Canonical residue descent at repaired scope | **NEW math**, 300–800 lines |

Order: `G0/G1/G2`; then H10; then H/L/M/V branches; then trivial wrappers and exact assembly.
A failed validity gate terminates its branch and opens an owner amendment.

## 6. Non-vacuity teeth at `n = 2`

The campaign owes closed concrete data and a proof of

```text
CanonicalLadderConfig C B G Kt L N v ρ q 2.
```

The generic “given `RealizedInput`” theorem is not a tooth, nor is conditional degree-four S2.
The least-duplication route reuses the S2 depth-one base:

- `s2DepthOne` and its degree-two theorem (`leanfinal/Uniformity/ChapC/C130fd0.lean:486-516`);
- the unconditional depth-one FGMN calculus (`leanfinal/Uniformity/ChapC/C130sg.lean:488-499`);
- but a degree-two occurrence, depth-one `ChainRealization`, and `RealizedInput` are new. The
  current S2 occurrence selects stage 2 and degree 4 (`leanfinal/Uniformity/ChapC/C130s17.lean:488-590`).

**[VAUD] Occurrence audit.** No closed degree-two occurrence is constructible by composition
of landed declarations. `s2DepthOne` + `s2DepthOneKeyChain` + `s2AnchorCalculus` do not form a
`ChainRealization`: the precise first missing carrier is
`SplitNodePointSource (s2DepthOne h2 hq) E receiver (s2DepthOneKeyChain h2 hq)` (including its
legal point, stage tables, threshold/window and split residue reads). Without it there is no
depth-one `ChainRealization`; without that, an `ArisingCore … 2` cannot be paired with a
`RealizedInput` and sent through `realizedInput_ladderConfigData`. The landed
`s2Frontier` cannot be downcast: it is a depth/stage-two source and its occurrence has
`stageDeg = 4`, `μ = 1`, hence input degree `4` by `degree_block`.

| Tooth | 30–60 minute grain | Reuse / new |
|---|---|---|
| N2-0 | State `DegreeTwoLadderSocketWitness` with explicit data | NEW wrapper |
| N2-1 | Pin concrete DVR, fields, algebra, completeness | NEW packaging; mathlib reuse |
| N2-2 | Pin depth-one tower/key/degree/calculus | REUSE `leanfinal/Uniformity/ChapC/C130fd0.lean:486-526`, `leanfinal/Uniformity/ChapC/C130sg.lean:488-499` |
| N2-3 | Degree-two input polynomial: monic/degree/block/key-free | NEW; model `leanfinal/Uniformity/ChapC/C130s17.lean:532-583` |
| N2-4 | Build `ArisingCore ... 2` | NEW record assembly |
| N2-5 | Build depth-one split-node source and `ChainRealization` | NEW substantive node |
| N2-6 | Choose accepted point and build `RealizedInput` | NEW; model `leanfinal/Uniformity/ChapC/C130s17.lean:600-629` |
| N2-7 | Fire and publish closed guard | REUSE `leanfinal/Uniformity/ChapC/C130s18.lean:238-247` |
| N2-8 | Apply HE7A; exhibit nonempty side ledger | NEW conclusion-sensitive bite |
| N2-9 | Construct genuinely firing LB1 `I` on same `(C,B)` | NEW hostile bite |
| N2-10 | Construct nonzero `Λ` and valid MP1 `B'` trigger | NEW hostile bite |
| N2-11 | At `i=3`, attempt concrete false-HVR off-range replacement | NEW hostile bite |
| N2-12 | Publish non-vacuous supplier statements only after all teeth | NEW wrapper |

N2-7 defeats ex-falso but is insufficient. N2-9/N2-10 must fire premises; N2-11 must target
the exact unbounded conclusion.

Anti-vacuity/anti-swallow rules:

1. Do not use `S2LevelOneThreshold` as an uninhabited premise and call it a witness.
2. Do not confuse S2 tower depth 2 with input degree 2.
3. Do not add agreement, τ-letter values, a block suite, irreducibility, or the desired
   interface to the guard.
4. Keep the whole guard; destructing it only for its domain/DVR instances is legitimate.
5. Re-run the χ-twist audit after any guard change (`C130s18.lean:411-552`).
6. Re-run off-range mutation after any vartheta change (`C130vw.lean:321-333`).

## 7. OPEN list — genuinely new mathematics or owner decisions

1. **Owner:** reconcile unbounded vartheta with live-range-only guard; current form is expected
   refutable.
2. **Owner:** decide whether LB1 means every abstract interface or a canonical linked one.
3. **Owner/cite:** check `recentered_key_emission` hypotheses against arbitrary `B'`.
4. Finish the F1/F2 frontier and exact-read engine.
5. Prove the full C-to-E `RungInterface` exporter, including higher factors and rank.
6. Display/formalize the HE7-12(d)/HE7-13 simultaneous induction.
7. Build the mixed-node arena-to-`PartitionLeg` bridge; E57p supplies only the schema.
8. Construct MP1 quotient/interface and prove recentered-key irreducibility at exact hypotheses.
9. Prove canonical residue descent at repaired scope without swallowing the target.
10. Land a closed degree-two occurrence, realization, and accepted input.
11. Add characteristic-two HE7 hostile teeth (coverage debt, not substitute for proof).

## 8. Exit gates

Complete only when:

- validity gates pass or recorded owner amendments land;
- four suppliers elaborate at exact IFC0 types with no extra hypotheses;
- `ladderField_of_suppliers` assembles them without adapters;
- a closed degree-two guard exists;
- HE7A/LB1/MP1 fire contentful teeth and vartheta passes the repaired scope tooth;
- twist/off-range anti-swallow audits remain green;
- all declarations are sorry-free with no non-core axiom.

## 9. Probe

`leanfinal/scratch/LDEC_probe.lean` elaborates the exact split, guard instance extraction,
landed `PartitionLeg → LB1Carrier` assembly, MP1 record assembly, HVR binding, and unbounded
vartheta consequence.

```bash
cd leanfinal
lake env lean scratch/LDEC_probe.lean
```

It exits 0. The named probe declarations print only
`[propext, Classical.choice, Quot.sound]`; there is no `sorry` or new axiom declaration.

**[VAUD]** `leanfinal/scratch/VAUD_probe.lean` now additionally checks the conditional landed
S2 degree-four socket, the LB1 arbitrary-interface bite, the MP1 irreducibility projection at
its exact trigger hypotheses, a concrete false HVR, dependent off-range `(v,ρ,q)` replacement,
the repaired live-range supplier/field equivalence and assembly, and the landed S2 degree
mismatch. Verification:

```bash
cd leanfinal
lake env lean scratch/VAUD_probe.lean
```

It exits 0. The printed audited declarations use only
`[propext, Classical.choice, Quot.sound]`.

## [LVT 2026-08-28] Enactment of the vartheta owner amendment

**Route chosen: SUPERSESSION (new file), not the in-place IFC0 diff.**  Reasons, recorded
also in the new file's header:

1. The in-place diff cannot compile alone: IFC0's anti-drift pin
   (`example … : LadderField n := h.ladder`) ties `LadderField` definitionally to
   `CapstoneHypotheses.ladder`, which returns E.24's unbounded `LadderSupply`.  Applying the
   diff forces rebinding that SIGNED capstone field (leanspec NODE I.10, re-signed at A-I.3)
   — one of the two owner gates.  The probe's own record: "An IFC0-only edit that pretends
   the old capstone field is definitionally unchanged would be false."
2. House precedent (GCW-6): IFC3 retired IFC0's `DeepGentowSupplier` as a campaign target
   with IFC0 byte-untouched as the tension record; IFC3's header and leanspec A-I.5 record
   the coordination rule "`IFC0.lean` untouched; corrected shapes route through supersession
   twins."
3. Honesty invariant: the refuted-as-guard-derivable unbounded target survives as a named
   record instead of a silent rewrite.
4. `LadderField` has no consumers outside `IFC0.lean` (orchestrator grep, 2026-08-28), so
   supersession costs nothing downstream.

**Landed** (`leanfinal/Uniformity/ChapI/IFC5.lean`, namespace `Uniformity.Density.IFC5`;
`lake env lean Uniformity/ChapI/IFC5.lean` exit 0, zero `sorry`, all `#print axioms`
exactly `[propext, Classical.choice, Quot.sound]`):

* the six probe declarations, byte-shape, universes matched: `CanonicalLadderLiveAt`,
  `LadderVarthetaSupplierLive`, `LadderSupplyLive`, `LadderFieldLive`,
  `ladderFieldLive_iff_suppliers`, `ladderFieldLive_of_suppliers`;
* two supersession-direction pins: `ladderVarthetaSupplierLive_of_unbounded` and
  `ladderFieldLive_of_ladderField` (old targets ⟹ new — the amendment only RESTRICTS the
  demanded range; the converse is exactly the refuted derivability and is absent).

`IFC0.LadderVarthetaSupplier` / `IFC0.LadderField` are RETIRED AS CAMPAIGN TARGETS,
byte-frozen; `LadderFieldLive` is the campaign target.  The four-way split at the repaired
target consumes IFC0's suppliers 1–3 UNCHANGED.

**Leanspec surface:** the unbounded demand IS signed there (I.10's `ladder` field consumes
E.24's `LadderSupply`, whose `vartheta` field is the unbounded `∀ i ≥ 3`); a comment-level
dated LVT record was added to `leanspec/Leanspec/ChapI.lean` after the A-I.5 state-update
block, quoting VAUD's machine certificates.  NO signed statement, declaration, gate, or
count changed; `lake env lean Leanspec/ChapI.lean` re-run, exit 0.  Rebinding
`CapstoneHypotheses.ladder` to `LadderSupplyLive` (or moving the live record into E.24)
remains OWNER-GATED and would be the numbered amendment A-I.6 — NOT enacted.

**Remains open after LVT** (unchanged by this unit):

* LS-G0 — LB1's socket-link stop: the landed S2 socket still feeds an independently
  quantified arbitrary `RungInterface`; owner decision (canonical vs realization-linked
  interface) owed before any LB1 proof fleet.
* LS-G1 — MP1's cite route REFUTED: [GN15] Thm 2.3 / GMN Thm 2.11 cannot fill `hirr` at the
  current divisibility-only trigger; owner repair of the MP1 trigger owed (non-circular
  key-polynomial/minimality premise, never on the global guard).
* Package supplier (HE7A): XL, blocked on the F1/F2 frontier/exact-read prerequisites and
  the C-to-E `RungInterface` exporter; no wrapper dispatched.
* Degree-2 non-vacuity: still no closed degree-two occurrence (first missing object: a
  depth-one `SplitNodePointSource` on `s2DepthOne`).
* Vartheta at the REPAIRED scope: `LadderVarthetaSupplierLive` is a typed target, not a
  proof; canonical residue descent at live indices (LS-V10) is the remaining mathematics.

## [AI6 2026-08-28] A-I.6 fork adjudication — closed refutation, rebinding mandatory

**Verdict: REFUTED. Recommendation: REBIND; a rider is not honest.**  The new compiling
certificate is `leanfinal/scratch/AI6_probe.lean`; the claim ledger and exact non-enacted A-I.6
diff are in `runs/wave-c/verdict_AI6.md`.

AI6 closes the gap VAUD deliberately left open.  It constructs a concrete degree-four S2
configuration over `O = ℤ_[2]`, with `Kt` the landed S2 terminal field,
`L = FractionRing (Polynomial Kt)`, `G = GaugeLattice 2`, and the actual S2 carrier, block, and
normal section (`AI6_probe.lean:27-54`).  The dependent `(v,ρ)` package and `q` are changed only
at the off-range index `3`: `v 3` is trivial, `ρ 3` maps the first Laurent exponent to powers of
the rational-function unit `X`, and `q 3 = 1` (`AI6_probe.lean:89-149`).

The load-bearing certificates are:

- **PROVED** — `firstExponent_vartheta`: at `q = 1, s = 2`, the actual S2 normal section's
  first Laurent exponent is `-1` (`AI6_probe.lean:115-119`).
- **PROVED** — `s2_junk_vartheta_negative`: the resulting residue `X⁻¹` is not in the image of
  any `Kt` unit (`AI6_probe.lean:121-141`).
- **PROVED** — `gauge_view_offRange_kernel_replacement` and `s2_bad_gauge_view`: the full
  dependent kernel package and `q` replacement preserve `GaugeFamilyViewEq`
  (`AI6_probe.lean:66-87`, `151-157`).
- **PROVED** — `s2_bad_ladder_socket`: the updated data satisfy the complete
  `CanonicalLadderConfig` antecedent (`AI6_probe.lean:159-181`).  This is the identical guard
  antecedent of IFC0 suppliers 1–3 (`IFC0.lean:74-103`); their conclusions are not needed for a
  record refutation.
- **PROVED** — `s2_bad_vartheta_three`: the demanded `VarthetaRes` fails at `i = 3`
  (`AI6_probe.lean:183-191`).
- **PROVED** — `ladderField_four_refuted : ¬ IFC0.LadderField 4` and
  `capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4`
  (`AI6_probe.lean:193-202`).
- **PROVED** — the required command exits `0`; every footer print is exactly
  `[propext, Classical.choice, Quot.sound]` (`AI6_probe.lean:206-216`).
- **BLOCKED-BECAUSE, non-load-bearing** — no degree-two version was constructed because the
  landed corpus still lacks the depth-one `SplitNodePointSource`; the closed degree-four
  refutation already decides A-I.6.
- **GAP, irrelevant to this refutation** — HE7A/LB1/MP1 conclusions at the chosen socket remain
  open.  Their shared antecedent is inhabited; refuting the fourth field suffices.

This changes the rider-vs-rebind merits decisively.  IFC0's current anti-drift pin says the
signed `CapstoneHypotheses.ladder` is definitionally the refuted unbounded field
(`IFC0.lean:57-70`), so the signed block is a fake hypothesis at `n = 4`.  Unlike A-I.5's
interpretive routing rider (`leanspec/Leanspec/ChapI.lean:1000-1006`), no prose can repair a
machine-proved contradiction in the field bytes.  A-I.6 must bind the field to
`IFC5.LadderSupplyLive`; the old unbounded `IFC0.LadderField` should remain as the named tension
record.

The consumer audit is finite.  At enactment, promote `IFC5.CanonicalLadderLiveAt` and
`IFC5.LadderSupplyLive` to an acyclic early module, replace the `ladder` result type in both
leanspec (`Leanspec/ChapI.lean:990-996`) and landed I.10
(`I10_I15_I18.lean:154-160`), replace IFC0's stale `h.ladder` anti-drift pin, add the liveness
argument to leanspec gate item (4) (`Leanspec/ChapI.lean:1062-1069`), and update the sole
structure constructor `scratch/CHFD_probe.lean:118-146`.  I.15–I.18
(`I10_I15_I18.lean:188-221`) project only `a0`/`a2` and require no code change.  AI6 enacted
none of those signed or landed edits.

## [LB1G 2026-08-28] Guard-link adjudication: S2 is vacuous; restrict anyway

**Verdict: RESTRICT-ANYWAY.** The arbitrary-interface carrier is not refuted at the only
landed arising pair. It is instead PROVED there for a structural but vacuous reason: the S2
exported block has mass `μ = 1`, and the full `RungInterface` arithmetic forces every legal
interface on any mass-one block to have exactly one side and to make that side separable.
Consequently neither half of E.39's trigger can fire. This closes the requested malicious-S2
attempt negatively; it does not validate the universal quantifier at future arising blocks of
mass at least two.

The machine record is `leanfinal/scratch/LB1G_probe.lean` (zero `sorry`; exact verification
command below). Load-bearing declarations:

| Status | Declaration | Exact consequence |
|---|---|---|
| PROVED | `LB1GProbe.s2_exported_block_mu_one` (`LB1G_probe.lean:44-47`) | the landed S2 block has `μ = 1` |
| PROVED | `LB1GProbe.rungInterface_card_eq_one_of_mu_eq_one` (`:56-71`) | every interface on a mass-one block has one side |
| PROVED | `LB1GProbe.rungInterface_sep_of_mu_eq_one` (`:83-248`) | residual degree + forcing + exhaustion make every such side separable |
| PROVED | `LB1GProbe.not_lb1_trigger_of_mu_eq_one` (`:251-258`) | the complete LB1 trigger is false at mass one |
| PROVED | `LB1GProbe.s2_unrestricted_lb1_vacuous` (`:279-286`) | the unrestricted `LB1Carrier` holds at the landed S2 pair, vacuously |

This also explains why the abstract malicious interface from
`verification/om4_resign_nontriviality.lean:144-220` cannot be transported: its block has
`μ = 2` and its interface has two positive-length sides, whereas the S2 block has `μ = 1`.
Attempts to use the mixed-side disjunct also fail: `hresdeg` fixes total residual degree to
one, while `hforce` and `hexhaust` leave room for exactly the unique positive residual class;
`rungInterface_sep_of_mu_eq_one` checks both the linear and higher-factor cases, including
zero multiplicity/zero degree loopholes.

### Exact restricted statement and the missing realization link

The E-layer statement that can be signed without fabricating a C exporter is the elaborated
probe declaration (`LB1G_probe.lean:296-301`):

```lean
def LB1CarrierLive {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop) : Prop :=
  ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (Ladder.BlockSuite I)
```

Here `Exported I` must be instantiated by the future C-to-E relation saying that ONE
`RealizedInput` witnessing the same external slot/block views exports `I`. Its intended
chapter-I predicate must mirror `IFC5.CanonicalLadderLiveAt` (`IFC5.lean:105-123`): existential
domain/DVR instances, `ArisingCore`, `ChainRealization`, `RealizedInput`, and carrier/gauge
equivalences; `SlotViewEq` and `BlockViewEq` for the same `(C,B)`; then the missing
`RealizedRungInterfaceExport X eK I` relation in place of `GaugeLive`. That final relation is
not landed anywhere: the existing realization views stop at slot/block/gauge data
(`C130s18.lean:149-175`), and LS-H12 is precisely the missing
`RealizedInput → RungInterface` exporter. Defining `Exported := fun _ => True`, or merely
existentially bundling an arbitrary `I`, would reproduce the defect and is forbidden.

Supersession is machine-pinned: `lb1CarrierLive_of_unrestricted` (`LB1G_probe.lean:304-310`)
proves OLD implies NEW for every export relation. The E.57 route is also pinned at exactly the
restricted strength: `lb1CarrierLive_of_exported_partitionLegs` (`:314-322`) needs
`PartitionLeg I` only for exported triggering interfaces and maps it through the landed
`PartitionLeg.toBlockSuite` (`E57p.lean:188-246`).

### Consumer table

Repository-wide grep of `LB1Carrier` and `.lb1` gives the following complete semantic table.
“No instantiation” means the declaration only stores, projects, or rearranges the carrier.

| Consumer | Interface instantiated | Exported? | Consequence for restriction |
|---|---|---|---|
| `E39.lean` gate example (`:140-143`) | caller-supplied arbitrary `I` | no | test-only; add an export premise in the supersession twin |
| `E24.lean` gate `S.lb1 I` (`:193-200`) | caller-supplied arbitrary `I` | no | the only production-file application; it is an executed type gate, not downstream mathematics |
| `E24.LadderSupply.lb1` (`:147-155`) | no instantiation | n/a | field type must become the restricted twin in an owner-approved record twin |
| `E44.LadderObligations` and gates (`:111-168`) | no instantiation | n/a | packaging/projection only |
| `I10_I15_I18.CapstoneHypotheses.ladder` (`:151-160`) | no instantiation | n/a | returns E.24's record; rebinding is owner-gated |
| `IFC0.LadderLB1Supplier` and split (`:85-92`, `:120-147`) | no instantiation | n/a | supplier/record bookkeeping only |
| `IFC5.LadderSupplyLive` and joins (`:146-157`, `:179-234`) | no instantiation | n/a | vartheta-only supersession retained old LB1 field; needs an LB1 twin |
| `E57p.PartitionLeg.toBlockSuite` (`:188-246`) | its input `I`, already carrying `PartitionLeg I` | not specified | mathematical funnel is parametric and works at restricted strength (probe theorem above) |
| `E57iCert.split_blockSuite` (`E57i.lean:201-205`) | synthetic `mixIface` | no arising export | non-vacuity row for E.57 schema, not an LB1 consumer |
| `E57iCert.hi_blockSuite` (`E57ih.lean:180-183`) | synthetic `hiIface` | no arising export | same |
| `LDECProbe.lb1Carrier_of_partitionLegs` (`LDEC_probe.lean:59-66`) | every arbitrary `I` | no | scratch elaboration probe; restricted replacement is `LB1GProbe.lb1CarrierLive_of_exported_partitionLegs` |
| `VAUDProbe.lb1_inhabited_socket_tooth` (`VAUD_probe.lean:70-86`) | caller-supplied arbitrary `I` | no | diagnostic tooth establishing the defect, not a proof route |

Thus the proposed claim “E.24 only ever instantiates LB1 at exported interfaces” is literally
false in the landed source: its gate instantiates an arbitrary caller-provided `I`. But no
landed mathematical consumer relies on that strength. The actual E.57 construction is
`PartitionLeg I → BlockSuite I` and survives verbatim when its upstream obligation is limited
to exported `I`. The required edits are supersession/type-gate bookkeeping plus the genuinely
missing exporter relation; there is no downstream proof loss to justify keeping the stronger
quantifier.

### Recommendation and stop state

**RESTRICT-ANYWAY**, by a supersession twin after the C-to-E export relation is typed. Reasons:

1. the unrestricted carrier is already false on legal abstract E data
   (`lb1_resigned_not_trivial`), so a uniform arbitrary-interface strategy would need a new
   arising-block theorem realizing every numerical interface, strictly stronger than HE7.96;
2. the only landed arising pair cannot test that claim because its `μ = 1` trigger is empty;
3. no landed mathematical consumer needs arbitrary-interface strength; and
4. OLD implies the proposed NEW carrier and the `PartitionLeg` funnel closes at NEW strength,
   both machine-checked.

**GAP:** no `RealizedRungInterfaceExport`/C-to-E exporter relation exists, so the production
live predicate cannot yet be instantiated honestly. **BLOCKED-BECAUSE:** rebinding E.24's
`LadderSupply.lb1`, IFC0/IFC5, and the signed `CapstoneHypotheses.ladder` is an owner amendment,
parallel to LVT's A-I.6 gate. LS-G0 therefore changes from “find an S2 malicious interface” to
“type the realization-interface export relation and enact the LB1 supersession”; no proof fleet
may target the old unrestricted supplier.

Verification:

```bash
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/LB1G_probe.lean
```

Exit 0; zero `sorry`; every printed declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

## [MP1R 2026-08-28] Honest MP1 route: live step export + direct key criterion

**Adjudication.** The unrestricted `Ladder.MP1Carrier` is false, not merely missing a
citation: `scratch/MP1R_probe.lean` proves `unrestricted_mp1_false` at the legal abstract
pair with `B.Φ = X²`, `B.F = X⁴ - 5X² + 4`, `Λ = 4`, and
`B'.Φ = X² - 4 ∣ B.F`.  Therefore the old carrier and IFC0's
`LadderMP1Supplier` are RETIRED AS CAMPAIGN TARGETS.  They remain byte-untouched as the
tension record.  The honest replacement is a supersession twin whose extra premise is a
realization-linked **recenter-step export**, never a key/irreducibility premise added to
`CanonicalLadderConfig`.

The chosen mathematical route inside the live form is **direct**: the step export must expose
the FGMN key-polynomial predicate for the exact `B'.Φ` it produced, together with the
items-2--4 peel data.  Then the landed key bank proves irreducibility and Gauss transports it
to `FractionRing O`; `hef` remains `B'.hΦdeg.trans C.hef`.  This avoids pretending that either
[GN15] Theorem 2.3 or GMN Theorem 2.11 identifies an arbitrary divisibility-only `B'.Φ`.

### Exact proposed Lean statement

The helper below is `MidPeelEmission` with exactly the two item-5 fields `hirr` and `hef`
removed.  It is producer data, not the desired conclusion.

```lean
structure MP1StepCore {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} (B B' : Ladder.BlockData C) where
  quot : Ladder.BlockData C
  hkey : quot.Φ = B'.Φ
  hpeel : B.F = B'.Φ * quot.F
  hmass : quot.F.natDegree + C.D = B.F.natDegree
  hthr : quot.T = B.T
  iface : Ladder.RungInterface.{uO, uK, uW} C quot
```

`CanonicalMP1StepExport` is to be defined beside the other realization views.  Its witness
must be the same realization exporting the external socket data; its FGMN data share that
realization's `core.T` and `A.keys`.  In exact binder/field shape:

```lean
def CanonicalMP1StepExport
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (n : ℕ) (Λ : Polynomial O) (B' : Ladder.BlockData C) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK,
      Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    B'.Φ = B.Φ - Λ ∧
    ∃ (e' f' u' : ℕ)
      (S : Tower.FGMNSourceData core.T A.keys e' f' u'),
      Nonempty (Tower.FGMNSourceLaws core.T A.keys e' f' u' S) ∧
      S.keyPolynomial B'.Φ ∧
      Nonempty (MP1StepCore.{0, 0, uW} B B')

def MP1CarrierLive
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Λ : Polynomial O), Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C),
      B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      CanonicalMP1StepExport.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n Λ B' →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')
```

This is a restriction only: the old carrier implies the new one by forgetting the export
premise.  A production enactment should land the corresponding
`LadderMP1SupplierLive`, replace only the `mp1` field in a further `LadderSupplyLive`
supersession (preserving IFC5's already-live vartheta field), and add the old-to-new pins.
No in-place edit of E.40, IFC0, IFC5, E.24, or the signed capstone field is authorized here.

### Option 1 — citation audit and mapping

The requested citations do **not** close the live form merely from the existing realization
views.  They become applicable only after adding source-specific exporter fields, and those
fields are not present at the funnel.

| Published hypothesis/conclusion | Exact proposed Lean supplier | Result |
|---|---|---|
| [GN15] Thm 2.3: an inductive valuation `μ` equipped with a MacLane chain | `core.T`, `A.keys`, and the `FGMNSourceData`/`FGMNSourceLaws` package sharing them | GAP: the landed types model this data, but no theorem identifies an arbitrary package with the theorem's analytic objects at this socket |
| [GN15] Thm 2.3: `φ ∈ KP(μ)` and `φ ≁μ φ_r` (or the published FGMN Thm 6.4 replacement: `φ` proper) | `S.keyPolynomial B'.Φ`; **no non-equivalence/properness field** | GAP: key-polynomialhood is supplied in the proposal, properness is not |
| [GN15] Thm 2.3: monic `g ∈ O_v[x]` | `B.F.Monic`, derivable from `Ladder.BlockData.natDegree_F B`; completion/base transport is not in the socket | GAP at the analytic dictionary |
| [GN15] Thm 2.3: a selected slope `λ` and prime residual factor `ψ` of `R(g)` | no present field; a faithful cite route would add them to the step export | GAP |
| [GN15] irreducible-leaf clause: `ord_ψ(R_λ(g)) = 1` | no present field; divisibility `B'.Φ ∣ B.F` is not residual multiplicity one | GAP; this must be a new recenter-step premise if this cite route is chosen |
| [GN15] factor conclusion `g_{λ,ψ}` | no equality `B'.Φ = g_{λ,ψ}` | GAP; without this identification the theorem proves irreducibility of a different polynomial |
| [GN15] eq. (2.1): leaf `(e,f)` is the chain product | intended source for the orbit dictionary | GAP at `B'.Φ`; in Lean `MidPeelEmission.hef` is already PROVED from `B'.hΦdeg.trans C.hef`, so this cite is not needed for the current field |
| GMN Thm 2.11: a type `t` of order `r-1` with prescribed `ψ_{r-1}` and numerical data | `core.T`, `A.keys`, `S`, plus a **missing** refined-type/residual identification | GAP |
| GMN Thm 2.11: the polynomial is the theorem's constructed `φ_r` (Def 2.12 then calls this a representative) | no equality from the constructed representative to `B'.Φ` | GAP; merely satisfying recentering/divisibility is insufficient |
| GMN Thm 2.11 conclusion: constructed `φ_r` is monic, irreducible, and has the stated degree/value/order | would yield `hirr` only after the missing equality and the fraction-field dictionary | GAP |
| FGMN (J. Algebra 427 (2015)) Lemma 1.8: every `φ ∈ KP(μ)` is irreducible over the completion/fraction-field model | `S.keyPolynomial B'.Φ` | CITED-FAITHFUL once the source/field dictionary is supplied; unlike the two queued cites, this theorem targets the exact key polynomial |

Numbering warning: `docs/references/s10208-024-09646-x.pdf` is Alberich-Carramiñana--Guàrdia--Nart--Poteaux--Roé--Weimann, *Polynomial Factorization Over Henselian Fields*, Found. Comput. Math. 25 (2025).  Its **Theorem 2.11 is a tangent-direction/initial-form factor theorem**, not GMN's representative-construction theorem.  The latter is the TAMS 2012 theorem labelled `phir` in `docs/references/HigherNewton.tex` (lines 1257--1283), followed by Definition 2.12.  These identically numbered results must not be conflated.

**Funnel check.** `CanonicalLadderConfigData`/`LadderRealizationData` export only the parent
`C,B` through `SlotViewEq`/`BlockViewEq` and the gauge family through
`GaugeFamilyViewEq`.  `ChainRealization` explicitly has no FGMN fields.  The live S2 teeth
`C130sg.s2Frontier_ladder_socket` and `IFC4.s2FrontierWired_ladder_socket` likewise export
only the parent input block.  None exports a recentered successor `B'`, a quotient/interface,
a refined type, `S.keyPolynomial B'.Φ`, or residual multiplicity one.  Thus E.24
`LadderSupply → mp1` and the capstone `ladder` field cannot currently provide the new premise.

### Option 2 — direct landed mechanism

Once `CanonicalMP1StepExport` is available, the final proof is short.  Unpack its
`MP1StepCore`, `S`, and `hL`; obtain

```lean
have hirrO : Irreducible B'.Φ :=
  hL.key_irreducible B'.Φ hkeyPoly B'.hΦ
have hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O))) :=
  (B'.hΦ.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing O)).mp hirrO
```

and assemble `MidPeelEmission` from the core fields, `hirr`, and
`B'.hΦdeg.trans C.hef`.  Exact landed anchors are
`FGMNSourceLaws.key_irreducible`,
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, and the existing
`LDECProbe.midPeelEmission_of_fields` assembly pattern.

At the concrete S2/μ₃ model, `C132kp5.s2Mu3_key_irreducible` proves the same key-to-ordinary
irreducibility step directly from `S2Mu3KeyPoly`, and
`C132kp6b.s2Mu3_calculus_nonempty` supplies the completed μ₃ calculus.  This does **not**
finish MP1 at S2: no theorem proves `S2Mu3KeyPoly h2 hq B'.Φ` for a recentered successor,
and the socket exports no such successor.

Estimated Lean size: 40--80 lines for the final live-carrier assembly; 80--180 lines for a
generic direct minimality/primality lemma if the opaque `FGMNSourceLaws` route is avoided;
roughly 300--800 lines for the missing realization-linked recenter-step/quotient exporter and
its transport through the external views.  The exporter, not irreducibility, is the current
critical path.

### Option 3 — unrestricted countermodel

`leanfinal/scratch/MP1R_probe.lean` constructs the countermodel and proves
`unrestricted_mp1_false : ¬ MP1Carrier C₂ B₂`.  Verification command required by the unit:

```bash
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/MP1R_probe.lean
```

Result: exit 0, zero `sorry`; every `#print axioms` line is exactly
`[propext, Classical.choice, Quot.sound]`.

### What remains open

1. Land a new producer-side `CanonicalMP1StepExport` (or an equivalent non-circular record)
   at the actual Montes/MacLane recentering transition.
2. At each arising site, prove that the exported exact `B'.Φ` satisfies the landed
   `keyPolynomial` predicate and export the quotient/interface fields of `MP1StepCore`.
3. Enact a supersession twin for the MP1 supplier and a combined live `LadderSupply` record;
   rebinding the signed E.24/capstone `ladder` field remains owner-gated.
4. If the literature route is retained instead of the direct key bank, add and discharge the
   refined-type, properness, residual-multiplicity-one, and exact-factor/representative
   identification fields.  None may be replaced by divisibility alone or placed on the global
   ladder guard.

## [LVS 2026-08-28] The live vartheta supplier: depth-two vacuity and the exact export wall

**Verdict.** The depth-two arising-realization case is **PROVED, vacuously**.  The general
live supplier is **PROVED FROM an exact witness-attached tau-residue exporter**, and the
bridge to the signed `IFC5.LadderSupplyLive.vartheta` field is **PROVED byte-shape**.  The
exporter itself is **OPEN-LEMMA** at genuine deep sites.  In particular, the present
`ChainRealization`/`RealizedInput` fields do not imply it: CC-18's live canonical-read twist
audit rules out that inference uniformly.

The complete statement authority is `leanfinal/scratch/LVS_probe.lean` (zero `sorry`),
verified from `leanfinal/` by

```bash
timeout 580 ~/.elan/bin/lake env lean scratch/LVS_probe.lean
```

Exit `0`; every footer declaration uses only `[propext, Classical.choice, Quot.sound]` or a
subset.  The independent finite arithmetic certificate is
`verification/lvs_live_range_spot.py`.

### 1. Exact mathematics at one live index

The landed arithmetic is definitional:

```text
GaugeLive r i  <->  1 <= i and i < r
```

(`Tower.gaugeLive_iff`, `C130k.lean:48-49`).  Hence the signed intersection is

```text
3 <= i and GaugeLive r i  <->  3 <= i and i < r.
```

It is empty for every `r <= 3`.  At `r = 2`, the gauge-live range is exactly `{1}`; no
`i >= 3` is live.  The first genuine tooth is `r = 4`, `i = 3`, and at general `r >= 4`
the demanded-live indices are exactly `{3, ..., r-1}`.  This is proved for arbitrary socket
data by `LVSProbe.vartheta_live_r_two_vacuous` (`LVS_probe.lean:31-40`) and in the explicit
arising-realization shape by `vartheta_live_of_realization_depth_two` (`:44-60`).  No property
of `N`, `v`, `rho`, or `q` is used.

For a live witness, `GaugeFamilyViewEq` says precisely (`C130vw.lean:214-222`):

1. the transported normal section's `n` is the realization normalizer's `n`;
2. the dependent sigma package `(v i, rho i)` transported along `eG` equals
   `(levelHeight core.T <i,hi>, canonicalResAt X hi)`; and
3. `q i = core.T.u (i+1)`.

Thus the external site is pinned to the realization's own canonical normal section, height,
ambient canonical read, and use height.  E.61 then asks for exactly D.62's A-D.2 carrier:

```text
forall s, exists h : N.varthetaEl (q i) s in ker (v i), exists u : Kt^x,
  rho i <N.varthetaEl (q i) s, h> = algebraMap Kt L u
```

(`HVarthetaRes`, `D62.lean:81-85`; `VarthetaRes.supplied`, `E61.lean:145-148`).  Pinning the
read identifies the *datum* at which this must be proved; it does not prove the embedded-unit
claim.

The sufficient non-circular datum is the tau form already consumed by the landed theorem
`Gauge.hvarthetaRes_of_tau_letters` (`D62w.lean:94-120`): for every `s`,

```text
N.tau (s * q i) (q i) lies in ker (v i),
and its rho i value is the image of a Kt-unit.
```

D.05's recursion then multiplies these tau values to obtain every vartheta value.  The probe
packages exactly those two assertions, plus the same witness's exact family-view proof, as
`VarthetaTauLevelExport` (`LVS_probe.lean:72-91`).  It deliberately contains neither
`HVarthetaRes` nor `VarthetaRes`.  The theorem
`varthetaRes_of_live_of_exports` (`:95-109`) is the complete proof: apply
`hvarthetaRes_of_tau_letters`, then use E.61's one-field constructor.

### 2. Why today's realization exports do not fill the package

The missing claim is not hidden in `GaugeFamilyViewEq`.  `canonicalResAt` is the node's
`canonicalRes0` transported to the synchronized kernel (`C130vw.lean:195-198`).  CC-18
permits an arbitrary character twist of the node's canonical read while retaining a valid
`ChainRealization` and `RealizedInput` (`twistNode`, `twistRealization`,
`twistRealizedInput`, `C130s18.lean:407-465`).  At a gauge-live index the twist changes
`canonicalResAt` by exactly the lifted character (`canonicalResAt_twist`, `:467-474`).
`embeddedValue_not_uniform` (`:527-543`) then proves that an embedded-`Kt`-value assertion at
such a canonical-read point cannot be derived uniformly from the present carrier fields.

This audit applies **on the live range**, so A-I.6 fixes the former off-range defect but does
not supply LS-V10's residue mathematics.  Adding arena/canonical agreement would also be
wrong: `arenaAgreement_not_uniform` (`C130s18.lean:498-525`) defeats exactly that shortcut.

IFC4 does not change this conclusion.  It lands the explicit S2 wired realization and its
ladder socket (`s2FrontierWiredRealizedInput`, `IFC4.lean:176-182`;
`s2FrontierWired_ladder_socket`, `:184-199`) and proves Gentow/W laws for the separate
`towerReadFamily`.  Its own honesty theorem records that the `3 <= j < 2` demand is empty
(`s2Wired_deep_demand_still_vacuous`, `:384-398`).  The unconditional depth-two mu3 calculus
and `s2Mu3_gentow5w_two` therefore validate a local algebraic/W-window mechanism at the S2
base; they do not assert that the ambient `canonicalResAt` sends the tau/vartheta words to
embedded `Kt`-units.  The vartheta supplier at this witness is closed by arithmetic before
that question is reached.

There is one quantifier subtlety which must remain explicit.  The landed S2 witness has
`core.r = 2`, so its own supplier leg is vacuous.  But `CanonicalLadderLiveAt` is an
existential over *any* realization matching the same external socket
(`I10LadderLive.lean:57-75`).  Merely exhibiting the landed depth-two witness does not prove
that every other matching witness has depth two.  Consequently an external
`LadderSupplyLive.vartheta` proof may use the local vacuity only after unpacking a witness
whose depth is known to be two; the exact field bridge must otherwise use the general
per-witness exporter below.  A theorem silently replacing “this witness has depth two” by
“every witness inside `CanonicalLadderLiveAt` has depth two” would be invalid unless a new
depth-rigidity lemma is supplied.

### 3. Exact Lean surface and the WLE pattern

The exact general owner predicate is the probe's `VarthetaTauLiveExporter`
(`LVS_probe.lean:114-129`).  Its binder order follows the WLE design:

```lean
def VarthetaTauLiveExporter (n : Nat) : Prop :=
  forall O ... Kt E L core A X G eG N v rho q,
    GaugeFamilyViewEq X (N.transport eG)
      (fun k => (v k).comp eG.symm.toMonoidHom)
      (fun k => (rho k).comp (C130s18.kerComapAlong eG (v k))) q ->
    forall j, 3 <= j -> (hj : GaugeLive core.r j) ->
      Nonempty (VarthetaTauLevelExport X G eG N v rho q j hj)
```

As in `[WLE]`, `core`, `A`, and `X` precede the level package; the package belongs to that
explicit witness and uses its own family view.  Unlike WLE's calculus package, no
`(e',f',u')`, receiver, or positive-`f'` field is relevant here.  The exact range is the
signed intersection `3 <= j` plus `GaugeLive core.r j`; demanding exports also at shallow
indices `1` and `2` would be an unjustified strengthening.

The signed bridge is fully proved:

```lean
theorem ladderSupplyLive_vartheta_of_exports {n : Nat}
    (hExports : VarthetaTauLiveExporter n) ... :
    forall i >= 3, IFC5.CanonicalLadderLiveAt C B G Kt L N v rho q n i ->
      Ladder.VarthetaRes G Kt L N v rho q i
```

(`LVS_probe.lean:134-152`).  Its proof destructs the `CanonicalLadderLiveAt` existential,
installs its domain/DVR/field witnesses as instances, applies `hExports` to the **same**
`core/A/X/eG/hview/hgi`, and calls `varthetaRes_of_live_of_exports`.  The conclusion is
literally `LadderSupplyLive.vartheta`'s field type (`I10LadderLive.lean:89-91`).
`ladderSupplyLive_of_vartheta_exports` (`LVS_probe.lean:158-171`) places it in the record
constructor with the first three fields unchanged.

### 4. Named opens: the real `r >= 4` campaign

The bridge and all bookkeeping are closed.  The following mathematics remains.

1. **OPEN-LEMMA `LVS-CANONICAL-TAU-EXPORT`.** For every explicit arising witness `X` and
   every `j` with `3 <= j` and `GaugeLive core.r j`, prove the two fields
   `VarthetaTauLevelExport.tau_mem` and `.tau_value` for the socket data pinned by
   `GaugeFamilyViewEq`.  Equivalently, prove `VarthetaTauLiveExporter n`.  The membership
   half is expected to be exact-height/transport bookkeeping; the value half is LS-V10.
2. **OPEN-LEMMA `LVS-TAU-WORD`.** At general live depth, factor each
   `N.tau (s*q) q` into the synchronized wrap/letter generator word.  D62w's
   `deep2_tau_descent`/`deep3_tau_descent` are the fixed-depth exponent patterns; no theorem
   currently performs this for an arbitrary arising `core.T`.
3. **OPEN-LEMMA `LVS-CANONICAL-LETTERS`.** Prove that this same witness's
   `canonicalResAt X hj` sends every generator in that word to an embedded `Kt`-unit.
   `C130cr` identifies canonical reads of synchronized generator words with products of
   `wrapValue`/`letterValue`, but the general embedded-level-field dictionary is absent; this
   is the existing `OPEN-LETTERS` wall, not a consequence of the Gentow/W read.
4. **OPEN-LEMMA `LVS-DEPTH-RIGIDITY-S2` (optional, not needed once the general exporter
   lands).** If one wants a theorem that the *external S2 socket's entire signed field* is
   vacuous without invoking the general exporter, prove that every realization witnessing
   `CanonicalLadderLiveAt` for those exact external S2 views has `core.r = 2`.  No such
   theorem is landed.

Once items 2 and 3 assemble item 1, `varthetaRes_of_live_of_exports` and
`ladderSupplyLive_vartheta_of_exports` finish LS-V10 with no further mathematics.  The first
non-vacuous test must be an arising witness of depth at least four and must bite at `j = 3`;
the depth-two mu3 witness cannot serve as that test.

### 5. Numeric spot-certificate

`verification/lvs_live_range_spot.py` independently enumerates the demanded-live set for
`0 <= r <= 8` and asserts

```text
r=2: []
r=3: []
r=4: [3]
r=5: [3, 4]
...
PASS: depth 2 is empty; the first real tooth is r=4, i=3
```

It is only a finite visibility certificate; the Lean theorems above prove the depth-two
claim for arbitrary data and arbitrary index.

## [REX 2026-08-28] Producer recenter-step export and forced A-I.7

### 1. Priority adjudication: the rebound funnel is refutable through `mp1`

**YES.**  A-I.6 repaired only the `vartheta` quantifier.  The landed
`IFC5.LadderSupplyLive.mp1` field is still literally the unrestricted
`Ladder.MP1Carrier` (`I10LadderLive.lean:80-90`), and the rebound
`CapstoneHypotheses.ladder` returns that record under `CanonicalLadderConfig`
(`I10_I15_I18.lean:155-171`).  This is not merely a record-level concern: the unrestricted
counterexample passes through an inhabited landed socket.

The new machine proof is `scratch/REX_probe.lean:201-271` (line numbers before later edits
may drift).  At the landed S2 occurrence,

* `C2.D = 4`, `B2.μ = 1`, and `B2.F = B2.Φ + 1`; the last two facts come from the actual
  producer (`C130s17.s2InputPolynomial` and `s2InputData`, lines 540-584), not from an
  unrelated abstract carrier;
* `Λ = -1` is nonzero and has degree `0 < 4`;
* the legal block `B2' := recenteredAtInput B2 rfl` has `B2'.Φ = B2.F = B2.Φ - Λ`, hence
  `B2'.Φ ∣ B2.F`;
* any `MidPeelEmission B2 B2'` contains a quotient block.  Every block has
  `deg quot.F = quot.μ * D ≥ D`, while `hmass` and `B2.μ = 1` demand
  `deg quot.F + D = deg B2.F = D`, contradicting `D > 0`.

Thus the probe proves, in increasing funnel strength,

```lean
s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2
s2_ladderSupplyLive_false : ¬ IFC5.LadderSupplyLive C2 B2 ... 4
s2_canonical_ladder_config : CanonicalLadderConfig C2 B2 ... 4
capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4
```

The last theorem applies the current `CapstoneHypotheses.ladder` to the landed
`C130sg.s2Frontier_ladder_socket`, then projects `.mp1`.  There is no missing bridge and no
appeal to the off-range `vartheta` construction from AI6.  The constructed `B2'` is
deliberately **not** claimed to arise from the S2 realization: unrestricted MP1 quantifies
over every legal block satisfying only recentering and divisibility.  Excluding precisely
this fabricated successor is the purpose of the live repair.

**Forced amendment A-I.7 (plan only; not enacted here).**  Add a superseding ladder record
whose `package`, `lb1`, and A-I.6 live `vartheta` fields are unchanged and whose `mp1` field is
the `MP1CarrierLive` below, parameterized by the same `(G,Kt,L,N,v,rho,q,n)` as the socket.
Rebind `CapstoneHypotheses.ladder` to that record.  Land the conservative pin
`old unrestricted MP1 -> MP1CarrierLive`, plus the corresponding old-supply-to-new-supply
adapter.  Update the MP1 consumer to pass the producer's `RecenterStep`.  Do not modify E.40
in place: it remains the machine-refuted tension record.

### 2. Exact GN15 hypothesis fence

The published source is Guàrdia--Nart, *Genetics of polynomials over local fields*,
Contemporary Mathematics 637 (2015), Theorem 2.3.  Its exact hypothesis list is: `μ` is an
“inductive valuation equipped with a MacLane chain”; `φ ∈ KP(μ)`; `φ ≁_μ φ_r`; and `g` is a
“monic polynomial g ∈ O_v[x]”.

The theorem then indexes factors `g_{lambda,psi}` by `-lambda` running through the slopes of
`N^-_{r+1}(g)` and `psi` running through the prime factors of
`R_{r+1,lambda}(g)`.  Its final clause is exactly: if
`ord_psi(R_{r+1,lambda}(g)) = 1`, then `g_{lambda,psi}` is irreducible in `O_v[x]`.
This is the complete hypothesis/index list relevant to MP1.  In particular, ordinary
divisibility `B'.Phi ∣ B.F` is not residual multiplicity one, and the theorem says nothing
about `B'.Phi` until it is identified with its selected `g_{lambda,psi}`.

The checked primary copy is the author offprint
`https://upcommons.upc.edu/bitstream/handle/2117/28206/GeneticsCM.pdf`.  `O_v` is the
completed valuation ring in the paper; the current socket's `Polynomial O` still needs the
published-to-repository completion/base-change dictionary before a literal GN application.

### 3. Proposed producer structure

The elaborated surface is `REX_probe.GNCitePayload` plus `REX_probe.RecenterStep`
(`scratch/REX_probe.lean:37-123`).  It separates three layers:

1. `RecenterStep` existentially owns the **same** `core/A/X/eK/eG` that supplies
   `SlotViewEq`, `BlockViewEq`, and `GaugeFamilyViewEq` for the external socket.  Under that
   witness it records `Lambda != 0`, the degree bound, exact recentering, and divisibility.
2. `GNCitePayload` owns the chain/source data and every GN-specific hypothesis/index:
   `source/sourceLaws`, `keyPolynomial`, `tangentClass`, `monicInput`, `slope`, `psi`, the
   residual factorization with multiplicity one, and the selected `leaf`.
   `exactLeaf : leaf = B'.Phi` is the non-negotiable conclusion-identification bridge.
3. `MP1StepCore` owns items 2--4 of the peel emission: quotient, exact peeled key, peel and
   mass identities, inherited threshold, and quotient interface.  It contains neither
   `hirr` nor `hef`.

The multiplicity field is represented without inventing a factor-multiplicity API:

```lean
residual_factorization : residual = psi * residualQuot
residual_multiplicity_one : ¬ psi ∣ residualQuot
```

together with `psi_irreducible`; this is the producer-side UFD spelling of
`ord_psi(residual) = 1`.  A production declaration should replace the probe's abstract
residual carrier by the exact transported slope-residual operator once that analytic
dictionary is landed.

The honest carrier has the A-I.6 quantifier pattern:

```lean
def MP1CarrierLive ... : Prop :=
  forall Lambda, Lambda != 0 -> Lambda.natDegree < C.D ->
    forall B', B'.Phi = B.Phi - Lambda -> B'.Phi ∣ B.F ->
      RecenterStep C B B' G Kt L N v rho q n Lambda ->
      Nonempty (Ladder.MidPeelEmission B B')
```

All old triggers and the old conclusion remain; only a same-realization producer premise is
added.  Hence unrestricted MP1 implies live MP1 by ignoring that premise, while the converse
is intentionally absent.

### 4. Cite mapping table and S2 producer audit

| GN15 Theorem 2.3 hypothesis/index | Export field | Landed producer datum at S2/μ3 | Status |
|---|---|---|---|
| `μ` inductive, equipped with the length-`r` MacLane chain (1.1) | same-witness `core.T`, `A.keys`, `payload.source`, `payload.sourceLaws` | `C130s17.s2ArisingCore`; `C130s2.s2DepthTwoKeyChain`; `C132fd0.s2SourceDataTwo`; `s2SourceLawsTwo_of` fired by `C132rp10b.s2Mu3_hex` and `C132kp6b.s2Mu3_hconv` | **LEAN PREFIX PROVED**; analytic GN dictionary still GAP |
| `φ ∈ KP(μ)` for the exact recentered polynomial | `payload.keyPolynomial` with `phi := B'.Phi` | `C132kp4.s2Mu3KeyPoly_Φ2` proves this only for the carried `Φ2 = keyAt 2` | **GAP at actual recentered `B'`** |
| `φ` not μ-equivalent to `φ_r` | `payload.tangentClass` | none; for the only currently tied exact key `Φ2 = keyAt 2`, `s2LandedPrefix_tangentClass_impossible` proves the required negation impossible by reflexivity | **PROVED MISSING for current key** |
| monic `g ∈ O_v[x]` | `payload.monicInput`, with `g := B.F` | `C130s17.s2InputPolynomial_monic`; generically `(B.natDegree_F).2` | monicity **PROVED**; completion/base dictionary **GAP** |
| `-lambda` a slope of `N^-_{r+1}(g)` | `payload.slope`, `slope_pos`, and (production) its exact slope-residual dictionary | no recenter-step slope export in `ArisingCore`, `ChainRealization`, `RealizedInput`, or S2 frontier | **GAP** |
| `psi` a prime factor of `R_{r+1,lambda}(g)` | `psi_monic`, `psi_irreducible`, `residual_factorization` | μ3 normalized/graded residual operators are landed, but no selected slope factor for this input is exported | **GAP** |
| `ord_psi(R_{r+1,lambda}(g)) = 1` | `residual_multiplicity_one` together with the factorization | no multiplicity-one theorem/export for the recentered successor | **GAP** |
| theorem-selected factor `g_{lambda,psi}` is the polynomial MP1 discusses | `leaf`, `leaf_monic`, `leaf_dvd_input`, `exactLeaf : leaf = B'.Phi` | none | **GAP; mandatory identification** |
| actual same-chain recentering `B'.Phi = B.Phi - Lambda` | outer `RecenterStep` equality, under the same realization witness | C.110 proves generic constant-shift development identities, but no S2 realization transition exports an external `B'` | **GAP** |
| MP1 peel items 2--4 | `Nonempty (MP1StepCore B B')` | no S2 successor quotient/interface exporter | **GAP** |

`S2LandedPrefix` and `s2LandedPrefix` (`REX_probe.lean:127-157`) are the maximum honest
construction from current landed data: the depth-two chain, complete μ3 source laws, exact
carried key, its key-polynomialhood, and monicity.  The probe then machine-checks that this
carried key cannot satisfy the tangent-class hypothesis (`s2LandedPrefix_tangentClass_impossible`).
No `sorry` is used to cross the remaining rows.

### 5. GMN Theorem 2.11 boundary

GMN, *Higher Newton polygons in the computation of discriminants and prime ideal
decomposition in number fields*, Trans. AMS 364 (2012), Theorem 2.11 is the theorem labelled
`phir` in `docs/references/HigherNewton.tex`.  It says that, for the already fixed type `t`,
one can construct a particular monic polynomial `phi_r` **of that type** with
`R_{r-1}(phi_r) ~ psi_{r-1}`; that constructed polynomial is irreducible and has the stated
degree, order, and value.  It does not make an arbitrary recentering/divisor into that
polynomial.  A GMN route therefore needs both a refined-type/residual export and an equality
between its constructed representative and `B'.Phi`; neither is landed.

### 6. Probe status

Required command:

```text
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/REX_probe.lean
```

Exit 0.  Zero `sorry`; all printed declarations depend exactly on
`[propext, Classical.choice, Quot.sound]`.  No landed `.lean`, leanspec file, or existing
scratch file was edited.

## [AI7E 2026-08-28] A-I.7 ENACTED — and the campaign's next node

The REX plan above is ENACTED (`runs/wave-c/verdict_AI7E.md`): the four export-surface
declarations are production at `leanfinal/Uniformity/ChapI/I10RecenterLive.lean`
(namespace `Uniformity.Density.IFC5`, byte-identical to the probe), the superseding
record `IFC5.LadderSupplyLive₂` (ONLY `mp1` → `MP1CarrierLive`) is the capstone `ladder`
field's result record in both twins, and the S2 landed prefix + the tangent-class
impossibility are production at `I10RecenterLiveS2.lean`.  `REX_probe.lean`'s
`capstoneHypotheses_four_refuted_via_mp1` is re-pinned to the retired verbatim copy
`CapstoneHypothesesUnrestrictedMP1` (pre-rebind form archived at commit `05f067b7`).

**NAMED OPEN `S2-RECENTER-EXPORT` (the supply campaign's next node).**  Construct, at the
landed degree-4 S2 socket, an actual `IFC5.RecenterStep` instance — equivalently, land
the GAP rows of REX's cite mapping table: a recentered external `B'` whose exact key is
NOT initial-equivalent to the carried `Φ₂`; the selected slope of `N⁻_{r+1}` with its
exact slope-residual interpretation; the selected prime factor `ψ` with residual
multiplicity one; the exact GN leaf identification (`exactLeaf`); the same-chain
recentering equality under the SAME existential witness; and the peel core
(`MP1StepCore`).  `s2LandedPrefix_tangentClass_impossible` shows the currently carried
key cannot serve, so a genuinely NEW recentered key export is required.  Until this node
lands, `MP1CarrierLive` is OPEN at the S2 socket (not refuted — that is the point of the
amendment).
