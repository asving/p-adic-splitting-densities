# Verdict AI6 — adjudication of the A-I.6 fork

**Date:** 2026-08-28  
**Unit:** AI6  
**Verdict:** **REFUTED**  
**Recommendation:** **REBIND per the exact diff below. A rider is insufficient.**

## Adjudication

The current unbounded field is false at a closed landed occurrence:

```text
AI6Probe.ladderField_four_refuted : ¬ IFC0.LadderField 4
AI6Probe.capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4
```

Both declarations compile in `leanfinal/scratch/AI6_probe.lean:195-202`.  Thus this is stronger
than VAUD's guard-derivability result: the three VAUD teeth do assemble inside the field's own
quantification.  The countermodel is at `n = 4`, not `n = 2`; a single degree refutes the signed
all-degree inhabitation campaign, and the landed corpus still lacks the depth-one source needed
for a degree-two socket (`runs/wave-b/verdict_VAUD.md:82-96`).

The concrete data are:

- `O = ℤ_[2]`, with `h2_padic` and `q2_padic` (`AI6_probe.lean:27-32`);
- `Kt = K2 = (S2DepthTwo h2_padic q2_padic).fld 2`, `L = FractionRing (Polynomial K2)`,
  `G = GaugeLattice 2`, and the actual S2 carrier/block/normalizer (`AI6_probe.lean:34-54`);
- the legal threshold datum `threshold0 = ⟨0,0,rfl,0<5⟩` (`AI6_probe.lean:39-45`).  This is used
  only as a logical inhabitant of the landed socket parameter, not asserted to be the missing
  source-faithful inherited numeral (the carrier and its anonymous inhabitation disclosure are
  `C130sg.lean:155-169`);
- `(v,ρ,q)` equal to the S2 exports except at index `3`, where `v` is trivial, `ρ` sends the
  first Laurent exponent to powers of the rational-function unit `X`, and `q 3 = 1`
  (`AI6_probe.lean:89-149`).

At `q = 1, s = 2`, the S2 normal section has first Laurent exponent `-1`
(`firstExponent_vartheta`, `AI6_probe.lean:115-119`).  Therefore the ambient residue is `X⁻¹`,
which cannot be the image of a `K2` unit; this is proved by fraction-ring injectivity and the
constant coefficient at `0` (`xUnit_inv_not_constant` and `s2_junk_vartheta_negative`,
`AI6_probe.lean:121-141`).

`gauge_view_offRange_kernel_replacement` (`AI6_probe.lean:66-87`) preserves the full dependent
kernel package and `q`.  Its specialization is `s2_bad_gauge_view` (`AI6_probe.lean:151-157`),
and `s2_bad_ladder_socket` reconstructs the complete `CanonicalLadderConfig` antecedent
(`AI6_probe.lean:159-181`).  This one antecedent is exactly the antecedent of supplier 1, 2, and
3 (`IFC0.lean:74-103`); their conclusions need not be constructed to refute the result record.
The demanded fourth conclusion fails at index `3` by `s2_bad_vartheta_three`
(`AI6_probe.lean:183-191`).  Applying a hypothetical field and projecting `.vartheta 3` closes
the contradiction (`ladderField_four_refuted`, `AI6_probe.lean:193-198`).

## Claim ledger

| Label | Status | Certificate / reason |
|---|---|---|
| Closed false site over the actual S2 normal section | **PROVED** | `AI6Probe.s2_junk_vartheta_negative` (`AI6_probe.lean:132-141`) |
| Dependent off-range replacement | **PROVED** | `AI6Probe.gauge_view_offRange_kernel_replacement` (`AI6_probe.lean:66-87`) |
| Updated family still satisfies the complete ladder guard | **PROVED** | `AI6Probe.s2_bad_ladder_socket` (`AI6_probe.lean:162-181`) |
| `VarthetaRes` fails at demanded `i = 3` | **PROVED** | `AI6Probe.s2_bad_vartheta_three` (`AI6_probe.lean:184-191`) |
| `¬ IFC0.LadderField 4` | **PROVED** | `AI6Probe.ladderField_four_refuted` (`AI6_probe.lean:195-198`) |
| `¬ CapstoneHypotheses 4` at the current signed field | **PROVED** | `AI6Probe.capstoneHypotheses_four_refuted` (`AI6_probe.lean:201-202`) |
| Exact footprint | **PROVED** | All eight footer prints (`AI6_probe.lean:209-216`) report exactly `[propext, Classical.choice, Quot.sound]` |
| Degree-two countermodel | **BLOCKED-BECAUSE** | No landed depth-one `SplitNodePointSource`, hence no closed degree-two socket; unnecessary for this refutation |
| HE7A/LB1/MP1 conclusions at this socket | **GAP** | Not proved and not used: record refutation needs only their shared guard antecedent and the false fourth field |

Verification, run exactly as required:

```bash
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/AI6_probe.lean
```

Result: exit `0`, zero proof holes, and every printed declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

## Why the recommendation is forced

An interpretive rider cannot turn a false field into an honest hypothesis.  The present
anti-drift pin identifies the signed projection with the refuted unbounded field
(`IFC0.lean:57-70`), so the current signed block is machine-proved empty at degree four.  The
A-I.5 rider precedent concerned a strengthened supply route while leaving the signed field
inhabitable in principle (`leanspec/Leanspec/ChapI.lean:1000-1006`).  Here the bytes themselves
cause contradiction.  A-I.6 must rebind `CapstoneHypotheses.ladder` to the live result record.

## Exact proposed A-I.6 rebinding diff — do not enact in AI6

Directly importing `IFC5` from `I10_I15_I18.lean` would create the cycle
`I10_I15_I18 → IFC5 → IFC0 → I10_I15_I18` (imports at
`I10_I15_I18.lean:6-15`, `IFC5.lean:6`, and `IFC0.lean:6`).  The exact acyclic route is to promote the two
already-landed carrier declarations ahead of I.10, without changing their namespace or bodies.

### 1. Promote the live predicate and record to an early dependency

Create `leanfinal/Uniformity/ChapI/I10LadderLive.lean` with imports
`Uniformity.ChapC.C130s18` and `Uniformity.ChapE.E24`, namespace
`Uniformity.Density.IFC5`, and move these declarations byte-for-byte from IFC5:

```diff
diff --git a/leanfinal/Uniformity/ChapI/IFC5.lean b/leanfinal/Uniformity/ChapI/I10LadderLive.lean
@@
-def CanonicalLadderLiveAt.{uG', uKt', uL'} ... :=
-  ...
-structure LadderSupplyLive ... : Prop where
-  package : Ladder.HE7APackage.{0, 0, uW} C B
-  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
-  mp1 : Ladder.MP1Carrier.{0, 0, uW} C B
-  vartheta : ∀ i ≥ 3,
-    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
-      Ladder.VarthetaRes G Kt L N v ρ q i
+-- Exact bodies are IFC5.lean:105-123 and IFC5.lean:146-157, moved byte-for-byte.
```

Delete only those two original declaration blocks from `IFC5.lean`; its remaining declarations
keep resolving the same constants in the same namespace.  Add
`import Uniformity.ChapI.I10LadderLive` to both signed/landed I.10 sources below.

The new file's exact declaration content (apart from the standard copyright/header and axiom
prints) is:

```lean
import Uniformity.ChapC.C130s18
import Uniformity.ChapE.E24

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density

universe uW uG uKt uL

def CanonicalLadderLiveAt.{uG', uKt', uL'}
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt]
    (L : Type uL') [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n i : ℕ) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG'} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK, Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    Tower.GaugeLive core.r i

structure LadderSupplyLive {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
  package : Ladder.HE7APackage.{0, 0, uW} C B
  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
  mp1 : Ladder.MP1Carrier.{0, 0, uW} C B
  vartheta : ∀ i ≥ 3,
    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

end Uniformity.Density.IFC5
```

### 2. Rebind the signed and landed field

Apply the same result-type replacement in `leanspec/Leanspec/ChapI.lean:990-996` and
`leanfinal/Uniformity/ChapI/I10_I15_I18.lean:154-160`:

```diff
   ladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
       (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
       (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
       [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
       (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
       CanonicalLadderConfig C B G Kt L N v ρ q n →
-      Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q
+      Uniformity.Density.IFC5.LadderSupplyLive.{uW, uG, uKt, uL}
+        C B G Kt L N v ρ q n
```

Add the dated A-I.6 statement-change record at the leanspec surface.  This is a weakening of a
hypothesis and therefore a strengthening of the conditional capstone theorem; no other field or
I.15–I.18 statement changes.

### 3. Replace IFC0's stale anti-drift pin, retain the refuted old field as tension record

Replace only `IFC0.lean:57-70`'s claim that the old unbounded `LadderField` is the signed field:

```diff
-/-- The capstone `ladder` field's exact type at degree `n` ... -/
+/-- Historical unbounded tension record.  A-I.6 binds the capstone to the live record. -/
 def LadderField (n : ℕ) : Prop :=
   ... -- byte-unchanged old unbounded definition

-/-- Anti-drift pin: `LadderField` IS the field's type, definitionally. -/
+/-- A-I.6 anti-drift pin: the signed field returns the promoted live record. -/
 example {n : ℕ} (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) :
-    LadderField.{uW, uG, uKt, uL} n := h.ladder
+    ∀ (O : Type) [CommRing O] (K : Type) [Field K]
+      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
+      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
+      (L : Type uL) [Field L] [Algebra Kt L]
+      (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
+      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
+      CanonicalLadderConfig C B G Kt L N v ρ q n →
+        IFC5.LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n :=
+  h.ladder
```

`IFC0.LadderField`, `LadderVarthetaSupplier`, and their old exact split remain byte-unchanged as
the named refuted tension record.  `IFC5.LadderFieldLive` remains the corrected campaign target.

### 4. Update every actual `CapstoneHypotheses` consumer

The grep audit over `leanfinal/**/*.lean` has one constructor, one `h.ladder` anti-drift pin, and
the four I.15–I.18 projection consumers:

- `scratch/CHFD_probe.lean:118-146`: change `hladder`'s conclusion at lines 125-126 from
  `Ladder.LadderSupply ...` to `IFC5.LadderSupplyLive ... 2`; the structure literal remains
  `ladder := hladder`.
- `IFC0.lean:69-70`: replace the pin exactly as in step 3.
- `I10_I15_I18.lean:188-221`: **no code change**.  I.15–I.18 use only `.a2`/`.a0`; they never
  project `.ladder`.
- `I10_I15_I18.lean:228`: **no code change**; it projects `.a2` only.
- `scratch/AI6_probe.lean:200-202`: after enactment, remove
  `capstoneHypotheses_four_refuted` and its footer print because its purpose is to certify the
  pre-A-I.6 contradiction.  Keep `ladderField_four_refuted` as the old tension-record refuter.

The sole constructor hunk is:

```diff
     (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
       ...
       CanonicalLadderConfig C B G Kt L N v ρ q 2 →
-      Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q)
+      Uniformity.Density.IFC5.LadderSupplyLive.{uW, uG, uKt, uL}
+        C B G Kt L N v ρ q 2)
```

At the leanspec gate, change only item (4), `Leanspec/ChapI.lean:1062-1069`:

```diff
     (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n) (i : ℕ) (hi : 3 ≤ i)
+    (hLive : Uniformity.Density.IFC5.CanonicalLadderLiveAt
+      C B G Kt L N v ρ q n i) :
     Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
-  ((h.ladder ℤ K C B G Kt L N v ρ q hcfg).vartheta i hi).supplied
+  ((h.ladder ℤ K C B G Kt L N v ρ q hcfg).vartheta i hi hLive).supplied
```

Leanspec gate items (2)/(3), the LB1/MP1 projections at lines 1038-1058, are unchanged because
the first three record fields are byte-identical.  The deep-twist gate and all I.15–I.18
theorems are unchanged.  Re-run only the targeted files (`I10LadderLive.lean`,
`I10_I15_I18.lean`, `IFC0.lean`, `IFC5.lean`, `scratch/CHFD_probe.lean`, and leanspec ChapI),
never bare `lake build`.

No part of this proposed diff was enacted by AI6.
