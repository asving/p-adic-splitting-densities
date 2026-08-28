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
