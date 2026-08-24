# Unit F3 verdict — I.10a/I.10b against tower-instantiation freeze v2

## Verdict

Overall: **SUPPLY, not LANDED**.

| socket | verdict | reason |
|---|---|---|
| I.10a `CanonicalLadderConfig` | **BLOCKED** | Freeze-v2's proposed body quantifies over the full C.130j `ArisingInput` and its canonical export witness. C.130d and C.130g--C.130k are explicitly OPEN, and the freeze's §9 full socket inhabitant is also OPEN. Replacing any missing layer by `True`, an empty record, an arbitrary residue hom, or an uninhabited guard would respectively weaken or vacuously strengthen the socket. |
| I.10b `CanonicalDeepTwistConfig` | **BLOCKED** | It inherits every I.10a blocker, additionally needs C.130i's separate arena read and `ArenaFamilyViewEq`, and cannot support signed E.63's unbounded `∀ i, 3 ≤ i → ...` from C.83 data that are meaningful only for `i < r`. |

No public socket body was changed from `True`, and no `CapstoneHypotheses` declaration was
landed. This is intentional: freeze v2 §11 says that before either signature is adopted, all
C.130 OPEN transcriptions and the full §9 witness must elaborate. Doing otherwise would violate
F3's no-weakening invariant and the freeze's own acceptance gate.

## Lean supply landed in the worktree

New file: `leanfinal/Uniformity/ChapI/I10FreezeV2.lean`.

New declarations:

1. `Uniformity.Density.Tower.StageLive`
2. `Uniformity.Density.Tower.GaugeLive`
3. `Uniformity.Density.Tower.DeepLive`
4. `Uniformity.Density.Tower.TerminalReceiver`
5. `Uniformity.Density.Tower.ArisingCore`
6. `Uniformity.Density.Ladder.DeepTwistConjunctLive`
7. `Uniformity.Density.Ladder.deepTwistConjunctLive_iff`

`TerminalReceiver` types D-TIF-3's single coherent frozen receiver as
`T.fld r ≃+* Kt`, carries all level homomorphisms, pins the terminal map, and states the step
square. `ArisingCore` types the non-OPEN portion of D-TIF-4: the DVR/frame/tower, live stage,
terminal receiver, stage key, input, multiplicity, both degree equations, and exact E.11
`FractionRing` key-freeness. It is deliberately not named `ArisingInput`.

`DeepTwistConjunctLive r` is the corrected finite-range target. Its theorem is an `Iff.rfl`
anti-drift pin against the exact freeze matrix `3 ≤ i ∧ i < r`.

No `sorry`, new axiom, `native_decide`, or `True`-valued mathematical interface was introduced.

## Missing declarations required before the sockets can land

These are exactly the freeze's named OPEN layers, not new F3 requirements:

- C.130b/c: general-depth `stageKey`, `stageDeg`, and the transported E.10 stage carrier;
- C.130d/e: the source-transcribed `CanonicalThresholdAt` and fully bound input block;
- C.130f: synchronized level lattices, `GaugeLattice`, normal section, height family, and ULift export;
- C.130g/h: legal P-locus/node-point clauses and the canonical L-valued residue hom, excluding OM-8 L3;
- C.130i: the separate Kt-valued arena read, arenas, tower read, and peel units;
- C.130j/k: `ArisingInput`, the four live-only view equalities, shared export witness, and cross-universe transports;
- C.130gate: the complete `s2Witness`-based inhabitant of both literal socket applications and the non-swallowing audit.

## Proposed signed amendments (do not apply in F3)

### A-I.2(a): terminal common receiver — ruling, no syntax change forced

The frozen single `Kt` binder can type without a binder change precisely because
`TerminalReceiver.topEquiv : T.fld r ≃+* Kt` fixes it as the terminal common receiver. This is
the freeze's weaker common-receiver recast, not literal membership in the current `K_i`.

Therefore no signed Lean statement diff is forced if A-I.2 explicitly accepts that faithfulness
delta. If literal per-level `K_i` membership is required instead, E.61, E.24, E.63, both socket
signatures, and I.10's two fields must all be redesigned around a field family; that is not a
local F3 amendment and contradicts freeze v2's “no I.10 binder change” premise.

The exact interpretive rider proposed for the I.10a signed docstring is:

```diff
@@
 read.* The block `(C, B)` is the one chapter C's OM ladder produces for a degree-`n` input over
 `O`, and `(G, K_t, L, N, v, ρ, q)` is that tower's level data with `ρ` the CANONICAL node-point
 residue datum (OM-8's pinning; an unpinned `ρ` leaves the ϑ-conjunct undischargeable, and the
 `∀ ρ` reading makes it outright false).
+
+[A-I.2] The frozen single `K_t` is the terminal common receiver: every arising witness carries
+`T.fld r ≃+* K_t` and compatible live maps `T.fld i →+* K_t`. Thus the conclusion is the
+common-receiver recast in `K_r`, not the source's literal per-level `K_i` statement.
```

### A-I.2(b): bound E.63 and expose the tower top in I.10b

This syntax change is forced if `deepTwist` is to be dischargeable from a finite `DeepTower`.
The new local declaration in F3 means the landed implementation can switch targets without
redefining the matrix.

Signed E.63 statement diff (`leanspec/Leanspec/ChapE.lean`):

```diff
@@
-/-- **E.63** [def] The Display-A `∀ i ≥ 3` conjunct, packaged. -/
-def DeepTwistConjunct : Prop := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i
+/-- **E.63** [def] The Display-A deep conjunct on the live range of a depth-`r` tower. -/
+def DeepTwistConjunct (r : ℕ) : Prop :=
+  ∀ i, 3 ≤ i → i < r → VarthetaRes i ∧ WFrame i
```

Signed I.10b/I.10 field diff (`leanspec/Leanspec/ChapI.lean`), using F3's already-typed local
target on the landed side:

```diff
@@
 def CanonicalDeepTwistConfig {O : Type} [CommRing O] {K : Type} [Field K]
@@
-    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (n : ℕ) : Prop :=
+    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
+    (r n : ℕ) : Prop :=
   CanonicalLadderConfig C B G Kt L N v ρ q n ∧ True
@@
   deepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
@@
-      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ),
-      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w n →
-      Ladder.DeepTwistConjunct v ρ q A R w
+      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
+      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
+      Ladder.DeepTwistConjunctLive r v ρ q A R w
```

Required exact gate call-site substitutions in the same leanspec amendment:

```diff
@@ §4 gate item (5)
-#check @Uniformity.Density.Ladder.DeepTwistConjunct
+#check @Uniformity.Density.Ladder.DeepTwistConjunctLive
@@
-    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
-    (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w n) (i : ℕ) (hi : 3 ≤ i) :
+    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r i : ℕ)
+    (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n)
+    (hi : Tower.DeepLive r i) :
     Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) ∧ Ladder.WFrame A q R w i :=
-  ⟨(h.deepTwist ℤ K C B G Kt L N v ρ q A R w hcfg i hi).1.supplied,
-   (h.deepTwist ℤ K C B G Kt L N v ρ q A R w hcfg i hi).2⟩
+  ⟨(h.deepTwist ℤ K C B G Kt L N v ρ q A R w r hcfg i hi).1.supplied,
+   (h.deepTwist ℤ K C B G Kt L N v ρ q A R w r hcfg i hi).2⟩
@@ §4 gate item (5a)
-    (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w n) :
+    {r : ℕ} (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n) :
     CanonicalLadderConfig C B G Kt L N v ρ q n := hcfg.1
@@ I.24 core registry
-#axiom_core Uniformity.Density.Ladder.DeepTwistConjunct
+#axiom_core Uniformity.Density.Ladder.DeepTwistConjunctLive
```

The final real I.10b body must pin the added `r` to the same joint arising witness used by the
arena export; it may not accept an unrelated numeral.

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapI/I10FreezeV2.lean
```

Exit 0. The seven declarations print only Lean core axioms (`propext`, `Classical.choice`, and/or
`Quot.sound` as inherited from their constituent definitions).

```text
lake build Uniformity.ChapI
```

Exit 0, `Build completed successfully (8686 jobs)`.

The roll-up does not yet import this SUPPLY file, consistent with the standing rule that the
orchestrator, not a conversion unit, wires chapter roll-ups.

## Commit status

The requested commit could not be created. Both the initial attempt and the mandated retry after
five seconds failed with:

```text
fatal: Unable to create '.../.git/index.lock': Read-only file system
```

The workspace permission profile mounts `.git` read-only. Only F3's two untracked files should
be staged by the orchestrator:

```text
leanfinal/Uniformity/ChapI/I10FreezeV2.lean
runs/wave-b/verdict_F3.md
```
