import Uniformity

/-!
# Chapter C — THE TOWER GRAMMAR: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-C_tower_grammar.md` (127 nodes, `C.01 … C.126` + `C.56a`) that
the blueprint actually WRITES IN LEAN, landed in the isolated `leanspec` environment **before**
the chapter-C fleet fires, in blueprint node order.

**STATE: OPEN (stub gate), 2026-08-16.** Nothing of chapter C has landed in `leanfinal`, so every
theorem-shaped node here is an `axiom` stub in the UNLANDED state of the `Leanspec.lean` stub
lifecycle, and every `def`/`structure` carries a real body. **Zero `sorry`.**

## THE HEADLINE FINDING (read before using this file as a contract)

**Only 57 of the 127 nodes carry a Lean SIGNATURE at all** (`C.01`–`C.51`, `C.55`, `C.56a`,
`C.59`, `C.60`, `C.61`, `C.71`). The other **70 nodes** — `C.52`–`C.54`, `C.56`–`C.58`,
`C.62`–`C.70`, `C.72`–`C.126`, i.e. all of §§7(rest)–13 plus the tail of §6 — carry only a prose
`**SIGNATURE** (shape).` line naming a declaration, and in 20 of those not even a name. They are
**not signable** and are listed in defect **D1** below. Of the 57 written signatures, a further
**19 contain `…` ellipses** inside the Lean text (defect **D2**), so the number of chapter-C
signatures that are complete Lean declarations is **38**.

## FILE LAYOUT AND NAMESPACE

* **ONE file**, `leanspec/Leanspec/ChapC.lean` (CHAP-C §15). It is NOT added to
  `leanspec/Leanspec.lean` by this unit — the orchestrator wires the roll-up import (concurrent
  stub-gate agents share `leanspec/`). Build it with the module target `lake build Leanspec.ChapC`
  or `lake env lean Leanspec/ChapC.lean`.
* **Everything is wrapped in `namespace LeanspecC`, per CHAP-C §15 / GC-6.6** (the `LeanspecC`
  wrapper route, not chapter G's retire-to-examples route — this chapter has nothing landed to
  retire against). The blueprint's `namespace Uniformity.Density.Tower` headers inside the
  SIGNATURE blocks are therefore DROPPED and every declaration is flat inside `LeanspecC`; the
  landed-side namespace assignment (definitions → `Uniformity.Density.Tower`) is what the fleet
  must land.
* **Environments.** CHAP-C's ENV-C1 (`{O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {π : O}`) IS a section `variable` block in the blueprint, so unlike
  chapter H this file needs one; it is declared once below and is the only one. ENV-C2's
  `[IsAdicComplete (maximalIdeal O) O]` and ENV-C3's `[Finite (ResidueField O)]` are written
  inline per declaration exactly as the blueprint writes them (GC-6.4, minimal binding).
* `set_option autoImplicit false` (and `relaxedAutoImplicit false`) — so an unbound binder in a
  signed signature is a HARD ERROR. That is the gate's job, and it is what caught D3 below.

## STUB-SIDE CURES APPLIED (all minimal, all recorded; see the DEFECT LIST)

Every deviation from the blueprint text is one of:
1. the `namespace`/flattening deviation above;
2. `(hpin : _)` → the pin equation written out (D4);
3. an unbound binder given its binder (D3);
4. a name the blueprint uses but never declares, declared minimally (D5, D6, D8);
5. an ellipsis-bearing signature either completed by the unique reading the blueprint's own prose
   forces (recorded per node) or left BROKEN-IN-COMMENT (D2).

Nothing here changes a node's mathematical content. Where the content itself looks wrong, the node
is left broken-in-comment with the diagnosis, never silently repaired.

## DEFECT LIST (stage-0e gate, 2026-08-16; recorded here, NOT repaired in the blueprint)

* **D1 — 70 OF 127 NODES CARRY NO LEAN SIGNATURE (missing-signature; the chapter's dominant
  defect).** From `C.52` onward the blueprint's SIGNATURE field degrades to prose: `**SIGNATURE**
  (shape). theorem towerLocus_iff_budget …` (C.52), `**SIGNATURE/PROOF/etc.** as C.123` (C.124,
  C.125), and in twenty nodes there is no `**SIGNATURE**` field of any kind. The full roll:
  `C.52 C.53 C.54 C.56 C.57 C.58 C.62 C.63 C.64 C.65 C.66 C.67 C.68 C.69 C.70 C.72 C.73 C.74 C.75
  C.76 C.77 C.78 C.79 C.80 C.81 C.82 C.83 C.84 C.85 C.86 C.87 C.88 C.89 C.90 C.91 C.92 C.93 C.94
  C.95 C.96 C.97 C.98 C.99 C.100 C.101 C.102 C.103 C.104 C.105 C.106 C.107 C.108 C.109 C.110 C.111
  C.112 C.113 C.114 C.115 C.116 C.117 C.118 C.119 C.120 C.121 C.122 C.123 C.124 C.125 C.126`.
  Consequence: the stub gate is BLIND to §§7–13, which is exactly where the chapter's
  TERMINAL SUPPLY nodes live (C.66/C.69/C.89/C.97/C.99/C.100/C.107–C.110/C.114 are all named in
  §2's "what other chapters consume from here" table). §15's own gate order (a)–(d) is
  unsatisfiable as written: it lists `C.83`, `C.92`, `C.66`, `C.97`, `C.98` among the "fragile
  signatures to elaborate FIRST", and NONE of them has a signature.
  **Classification: missing signature (blueprint incompleteness), not an elaboration failure.**
* **D2 — 19 OF THE 57 WRITTEN SIGNATURES CONTAIN `…` INSIDE THE LEAN TEXT** (elaboration
  failure by construction): `C.26` (`theorem natDegree_dvResPoly (…same…)`), `C.28`
  (`LevelDatum.shift … := …`), `C.33`, `C.34`, `C.35`, `C.36`, `C.37`, `C.38`, `C.39`, `C.40`,
  `C.42`, `C.44`, `C.48`, `C.49`, `C.50`, `C.51`, `C.56a`, `C.61`, `C.71`. Three of them
  (`C.33`, `C.34`, `C.48`, `C.49`, `C.56a`) label themselves `**SIGNATURE** (shape)`, so the
  ellipsis is deliberate; the other fourteen do not, so the ellipsis reads as an omission the
  composer meant to return to. Disposition below, per node: where the surrounding prose forces a
  unique reading of the omitted binders (`C.26`, `C.42`, `C.50`, `C.71`, and the binder-only
  ellipses) the stub completes it and says so; where the omission is mathematical content
  (`C.33`–`C.39`, `C.44`, `C.48`, `C.49`, `C.51`, `C.56a`) the node is BROKEN-IN-COMMENT.
* **D3 — `C.08` HAS UNBOUND BINDERS `u ℓ` (elaboration failure; CURED stub-side, minimally).**
  Both signatures of C.08 (`dvOnSide_modEq`, `dvSideLen_eq`) mention `u` and `ℓ` — in `hℓ : 0 < ℓ`,
  `hcop : Nat.Coprime u ℓ`, `DvOnSide F f u ℓ j` — and ENV-C1 binds neither. With `autoImplicit`
  on (the leanspec lakefile's default) they would be silently auto-bound in an unpredictable
  ORDER; with it off they are hard errors. Cured by adding `{u ℓ : ℕ}` explicitly. Same class in
  `C.30`/`C.31`/`C.32`? No — those bind everything. Also `C.55` (`μ₂` unbound) and `C.61`
  (`μ₂`-free but `hm1` elided): `C.55`'s `μ₂` is cured the same way.
* **D4 — `(hpin : _)` APPEARS IN SEVEN SIGNATURES (elaboration failure for the theorem-shaped
  ones; CURED stub-side).** `C.03` (`stageField`), `C.19` (`stageLetter`, `stageLetter_ne_zero`),
  `C.21` (`slotRes`), `C.22` (`twistRead`), `C.23` (`slotRes_ne_zero`), `C.24` (`slotRes_image`),
  `C.25` (`dvResPoly`), `C.26`, `C.42` (`TowerDatum`). A `_` binder type is inferable in a `def`
  whose BODY pins it, but a bodyless `axiom`/`theorem` interface has nothing to infer from, so
  `C.23`/`C.24`/`C.26` would not elaborate at all. Cured by writing the pin equation out
  (`npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)`) at every
  site. **Recommendation for the blueprint: give the pin proposition a NAME** (`KeyFrame.Pin F H₀`)
  — it is written out ~30 times and is the single largest source of transcription risk in §§3–4.
* **D5 — `C.07` PROMISES `dvSideMax`/`dvSideLen`/`dvSideDeg` IN A COMMENT AND `C.08`/`C.25`/`C.26`
  CONSUME THEM (missing declaration; CURED stub-side).** C.07's signature block ends
  `-- dvSideMax, dvSideLen, dvSideDeg analogous (one file, one public cluster per B.20 precedent)`.
  They are not analogous in one respect that matters: B.20 lands `sideMin`, `sideMax`, `sideDeg`
  but **NOT `sideLen`** (`grep -rn 'sideLen' leanfinal/` is empty; B.20(d) states the length
  identity as `sideMax_eq`, not as a definition), so `dvSideLen` has no landed template and C.08's
  `dvSideLen_eq` is a statement about an object the chapter never defines. Cured here by defining
  `dvSideLen := dvSideMax - dvSideMin` (the only reading under which C.08(b) is the B.20(d)
  analogue). **The blueprint should either declare the cluster or drop `dvSideLen_eq`.**
* **D6 — `C.15` CALLS `F.slotIdx_exists`, WHICH IS DECLARED NOWHERE (missing declaration;
  CURED stub-side by a different, total body).** `noncomputable def KeyFrame.slotIdx F k :=
  Nat.find (F.slotIdx_exists k)` — the trailing comment says "packaged via the H.51 bijection; see
  C.16", but C.16 states `slotIdx_spec`/`slotIdx_unique` as CONSUMERS of `slotIdx`, so the
  existence lemma the `Nat.find` needs exists in no node. Worse, `Nat.find` needs the predicate,
  not the proof, as its elaboration driver. Cured with the standard total body
  `Nat.find (⟨…⟩ : ∃ i, i < e₁ ∧ i * h ≡ k [MOD e₁])` — **and that existence claim is FALSE
  without coprimality of `h` and `e₁`**, which `KeyFrame.hcop` supplies but which no `slotIdx`
  statement mentions: at `e₁ = 4, h = 2, k = 1` there is no `i` with `2i ≡ 1 (mod 4)`. Since
  `hcop` is a structure field the claim is fine for a `KeyFrame`, but the `Nat.find` body must be
  fed the frame's own `hcop`, i.e. the def is not the "pure arithmetic on the frame's numerals"
  ENV-C5 node the blueprint labels it (defect **D7**). Landed here as a junk-`0`-defaulting
  `Nat.findGreatest`-free total definition to keep `C.16`/`C.17`/`C.41` elaborable, with the
  existence proof discharged from `F.hcop`.
* **D7 — `C.15`/`C.16`/`C.17`/`C.41` ARE LABELLED ENV-C5 ("pure arithmetic on the frame's
  numerals") BUT ARE STATED OVER `KeyFrame O π`, WHICH BINDS THE WHOLE DVR TELESCOPE
  (environment defect, not repaired).** These four nodes use nothing of the frame but `e₁`, `f₁`,
  `h`; stating them over `KeyFrame` forces `[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]`
  into pure `Nat` lemmas, which is exactly the over-binding GC-6.4 forbids ("minimal binding is the
  law"). It also makes `slotIdx` `noncomputable` for no reason (it is `Nat.find` on a decidable
  predicate over ℕ — computable). Recommendation: restate as `slotIdx (e₁ h k : ℕ) : ℕ` with a
  `KeyFrame` abbreviation. NOT cured here (that is a statement change).
* **D8 — `C.21`'s `algebraMap _ _` DOES NOT ELABORATE: THERE IS NO
  `Algebra (ResidueField O) (stageField …)` INSTANCE (missing instance; CURED stub-side).**
  `digAt π k a : ResidueField O` and the target is `F.stageField H₀ hpin =
  AdjoinRoot (F.frameRes H₀ hpin)`, an `AdjoinRoot` over `resField Polynomial.X`, itself an
  `AdjoinRoot` over `ResidueField O`. Mathlib gives each single step an `Algebra` instance but
  does NOT compose them, so `algebraMap _ _ (digAt …)` fails instance synthesis. The blueprint
  anticipates this in prose ("the composite of the landed quotient maps; one private helper may
  name it") but the SIGNATURE it signs is the one that does not elaborate. Cured by writing the
  composite `algebraMap (resField Polynomial.X) _ (algebraMap (ResidueField O) _ (digAt …))`.
* **D9 — `C.22`'s `twistRead` USES `⁻¹` ON A RING WITH NO `Inv` INSTANCE (elaboration failure;
  CURED stub-side).** `(F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k)`: `stageField` is
  `AdjoinRoot ψ`, a `CommRing`; it is a `Field` only under `Fact (Irreducible ψ)`, which the frame
  supplies through `F.hresirr H₀ hpin` — but that is a hypothesis, not an instance, so `Inv` is not
  synthesizable at the definition site as written. Cured with a `letI := Fact.mk …` inside the
  body. **This is not cosmetic:** it means `twistRead` cannot be a `def` of the shape signed
  without the pin hypothesis being USED (the blueprint's `hpin` is otherwise inert in that
  signature), and the `⁻¹` convention interacts with the `[r1]`-vs-`[r2]` sign the node's own
  FAITHFULNESS block says is machine-refutable — the gate below executes that witness (see the
  NUMERIC section: the `(2,2,3)` row).
* **D10 — `C.27` USES `.get!` ON AN `ℕ∞` (type error; CURED stub-side).**
  `(addVal O (Algebra.norm O (AdjoinRoot.mk g C))).get!` — `ℕ∞ = ENat`, and neither `ENat.get!`
  nor a `WithTop`-level `get!` exists at the pin (`Option.get!` is not found through `ENat`'s
  irreducible wrapper). The blueprint's own parenthetical admits the plumbing is unfixed ("the stub
  stage fixes the exact `ℕ∞`-plumbing against `leanfinal`'s `addVal` API"). Cured with
  `ENat.toNat`, which agrees with the intended value on the `≠ ⊤` locus that `hC0` pins — but note
  that `Algebra.norm O (AdjoinRoot.mk g C)` also needs `Algebra O (AdjoinRoot g)` (fine) and is
  JUNK unless `g` is monic of positive degree, which `HasLabel` supplies.
* **D11 — `C.40` AND `C.61` CONSTRUCT `FactorizationType` WITH TWO COMPONENTS; IT HAS ONE FIELD
  (type error; CURED stub-side).** Both sign `typeOf … = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}, …⟩`
  (C.61: `⟨{…}, by …⟩`), but the landed `structure FactorizationType where data : Multiset (ℕ × ℕ)`
  (`Uniformity/Density/LocalData.lean:43`) has exactly one field, so the anonymous constructor is
  over-applied. Cured to `⟨{(…, …)}⟩`. Class: stale-API smell — the extra slot looks like a
  degree-conservation proof field that `FactorizationType` does not carry (GC-4 ships degree
  conservation as a separate LEMMA, `typeOf_degree`, which is exactly why the field does not exist).
* **D12 — ORDERING: §3 IS NOT IN DAG ORDER, TWICE.** (i) `C.05` (`dvHgt_degenerate`,
  `dvSupp_degenerate`) consumes `dvHgt`/`dvSupp`, which are DEFINED at `C.06`; (ii) `C.13`
  (`IsTestKey`) consumes `slotRes`, which is `C.21` — the blueprint flags (ii) itself in a ⚠
  ORDERING NOTE but not (i). `C.06`/`C.07` are hoisted above `C.05`, and `C.13`/`C.14` are placed
  after `C.21`, below; the fleet must order `leanfinal`'s `ChapC.lean` roll-up the same way.
  Additionally `C.29`'s `HasLabel` is consumed by `C.27` (`hg : HasLabel L g`), which is §4 — so
  `C.29` must also be hoisted above `C.27` (a THIRD ordering inversion, not flagged anywhere in
  the blueprint, and this one crosses a section boundary in the direction §5 → §4).
* **D13 — `C.09`'s `LevelDatum` HAS NO FIELD FOR THE MULTIPLICITY AND `C.29`'s `HasLabel`
  RE-DERIVES IT (design finding, not a typing failure).** Recorded because `C.35`'s `mult₂` is
  defined as `(blockFactor …).natDegree / L.keyDeg₂` while `C.29`'s `HasLabel` existentially
  quantifies its own `m` with `dvResPoly … = L.r ^ m`; nothing in the chapter ties the two `m`s,
  and `C.40`'s conclusion `fS'.natDegree = L.keyDeg₂ * (mult₂ L f hctx - 1)` is the node where
  they must agree. With C.35 unsignable (D2) this cannot be checked at the gate.
* **D14 — THE GATES `C.123`–`C.126` HAVE NO LEAN AND NO EXPECTED-VALUE TABLE IN MACHINE FORM,
  SO §15's GATE ORDER (c) CANNOT BE RUN AS SPECIFIED.** §15(c) says "EXECUTE the §13 gate blocks
  at `q = 2` AND `q = 3` (`C.123`–`C.125`'s `#eval` values against this file's displayed
  numbers)"; the displayed numbers exist only inside prose sentences. What IS runnable is executed
  in the NUMERIC section at the bottom of this file, and one of the blueprint's displayed numbers
  is WRONG — see **D15**.
* **D15 — `C.123`'s HT SPOT VALUE AT `q = 2` IS MIS-STATED (arithmetic error in a gate's own
  expected value; machine-checked below).** The gate says: *"HT spot values at `q = 2`
  (`(q−1)((q−1)(q−2)/2)q^{2N−8}` at `q = 2` = 0 — the degenerate census, itself a check)"*. The
  claimed value 0 is right, but for a reason the parenthetical gets wrong at the OTHER prime it is
  paired with: at `q = 3` the same expression is `2 · ((2·1)/2) · 3^{2N−8} = 2·3^{2N−8}`, and
  `C.124` describes that as *"the obstruction instance `2·1/2·q^{2N−8}`-family values"* — `2·1/2`
  is `1` in ℕ (and in ℚ), not `2`. The two gate texts disagree with each other by a factor of 2 on
  the same family. Both readings are executed below (`htSpot`, `htSpotAlt`) and neither is
  derivable from any signed node, because §11 has no signatures (D1). **Classification: suspected
  wrong statement in a gate's expected-value text; cheap counterexample = the two texts' own
  numbers at `q = 3`.**
* **D16 — `C.125` DOCUMENTS ITS OWN FAILURE TO MEET GC-11 AND THE BLUEPRINT RECORDS IT AS A
  FINDING RATHER THAN A DEFECT (statement-level; NOT repaired).** The node's STATEMENT field
  contains a live, unedited composition-time derivation ("**⚠ honesty check executed at
  composition time:** … wait, that also has `f₁d_r = 2`") ending in the conclusion that an
  unconditional `e > 1 ∧ f > 1` tower witness does not exist without `C-BOX-1`. That is honest, and
  A-6 books it as cross-read item 6 — but the *node text* is a transcript, not a signature, and a
  fleet agent cannot transcribe it. Recorded here so the gate's verdict is on record: **chapter C
  cannot satisfy GC-11's `e > 1 ∧ f > 1` clause unconditionally**, and the two-prime clause is
  met only by prose.
* **D17 — `C.31`'s `jump_floor` HAS FOUR UNUSED HYPOTHESES AND ONE UNUSED BINDER; `jump_drop`'s
  `hfS` MENTIONS `μ / ℓ` (`ℕ`-division) IN A HYPOTHESIS THE BLUEPRINT ITSELF FLAGS AS UNFIXED**
  (statement-quality finding; signed as written). `jump_floor (mr ℓ dr L μ) (hm) (hjump) (hL)
  (hLμ) : 4 ≤ L ∧ 4 ≤ μ` — the conclusion follows from `hL`/`hLμ`/`hjump`/`hm` alone, `dr` is not
  otherwise constrained, and `4 ≤ L` needs `mr * (ℓ*dr) ≥ 2*2`, i.e. it is TRUE; kept. `jump_drop`
  carries the parenthetical "the exact hypothesis plumbing … is fixed at stub stage against
  C.33/C.35's outputs" — C.33 and C.35 are both unsignable (D2), so the plumbing cannot be fixed
  here. Signed at the written type, which is what the gate can check; the `ℕ`-division `μ / ℓ`
  makes `hfS` WEAKER than the intended `deg f_S ≤ D′·L_λ` whenever `ℓ ∤ μ`, and that is a silent
  truncation of exactly the kind GC-9's counterexample discipline exists for.

## Numeric content EXECUTED at this gate (GC-11 / §15 gate order (c))

See the `#guard` block at the bottom. Chapter C's signed layer is almost entirely
`Polynomial O`-valued and `noncomputable`, so the executable surface is the ARITHMETIC layer:
C.15/C.16's `slotIdx`/`twistExp` (ENV-C5), C.17/C.18's `slotWindow`, C.28's cocycle normal form,
C.30's trichotomy, C.31/C.32's jump arithmetic, C.42/C.50's `D₂`/`E₂`/`gridWeight`, C.52's
`budgetFloor` display (transcribed from the STATEMENT, since there is no signature), and the two
HT spot-value readings of D15. Every one runs at `q = 2` **and** `q = 3` where it has a `q`.
-/

namespace LeanspecC

open Uniformity Uniformity.Density Uniformity.Density.Leaf
open IsLocalRing IsDiscreteValuationRing

-- `autoImplicit` is ON by default at this pin (the leanspec lakefile sets no `leanOptions`).
-- Turned OFF here so that ANY unbound identifier in a signed signature is a hard error: that is
-- precisely the gate's job, and it is what turned C.08's `u`/`ℓ` into defect D3.
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Every `axiom` binder is "unused" by construction.
set_option linter.unusedVariables false

/-! ## ENV-C1 — the polynomial arena over the fixed bundle (CHAP-C §0.1, verbatim)

```lean
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
-- nodes taking π carry (hπ : Irreducible π) explicitly
```
ENV-C2 adds `[IsAdicComplete (maximalIdeal O) O]`, ENV-C3 adds `[Finite (ResidueField O)]`; both
are written inline per declaration (GC-6.4), never as section variables. -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! # §3 — THE LEVEL FRAME AND THE LEVEL DICTIONARY (C.01–C.14)

Landed in the repaired order C.01 → C.02 → C.03 → C.04 → **C.06 → C.07** → C.05 → C.08 → …
(defect D12(i)); C.13/C.14 are moved after C.21 (D12(ii), which the blueprint flags itself). -/

/-! ### NODE C.01 [def] — `KeyFrame` (real body; lands in `Uniformity.Density.Tower`) -/

/-- The stage key frame `(e₁, f₁, h; Φ′)` of `EFF.HE6.08`: `Φ′` monic irreducible of degree
`D′ = e₁f₁`, one-sided of slope `h/e₁` over the order-0 key `X`, with irreducible residual
read `ψ` of degree `f₁`.  The valuation normalization is `dv := e₁·v` (C.02). -/
structure KeyFrame (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) where
  e₁ : ℕ
  f₁ : ℕ
  /-- The slope numerator.  `h = 0` (forcing `e₁ = 1`) is the DEGENERATE frame, admitted so
  that C.05's level-1 reconciliation is definitional; the corpus frame has `1 ≤ h`. -/
  h : ℕ
  key : Polynomial O
  he₁ : 0 < e₁
  hf₁ : 0 < f₁
  hcop : Nat.Coprime h e₁
  hmonic : key.Monic
  hdeg : key.natDegree = e₁ * f₁
  hirr : Irreducible key
  hpure : IsPure Polynomial.X key h e₁
  hne : (sideSet Polynomial.X key h e₁).Nonempty
  /-- The residual read of the key is irreducible of degree `f₁` (frame hypothesis
  `ψ ∈ F_Q[T]` irreducible, `EFF.HE6.08`) — pinned at `sideMin` per GC-1. -/
  hresirr : ∀ (H₀ : ℕ), npHgt Polynomial.X key (sideMin Polynomial.X key h e₁ hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π Polynomial.X key h e₁ hne H₀) ∧
    (resPoly π Polynomial.X key h e₁ hne H₀).natDegree = f₁

/-- **STUB-SIDE ABBREVIATION (D4).** The pin proposition, written out ~30 times in §§3–4 of the
blueprint as the type of an inferred binder `(hpin : _)`. It is NOT a blueprint declaration; it
exists here so the cure for D4 is one token per site instead of a 90-character copy. The fleet
should land it (or the blueprint should name it). -/
def KeyFrame.Pin (F : KeyFrame O π) (H₀ : ℕ) : Prop :=
  npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)

/-! ### NODE C.02 [def+lemma] — `stageHeight` -/

/-- `dv(A) = min_i (e₁·v(a_i) + i·h)` (`EFF.HE6.10`), realised as B's `suppVal` at the
order-0 key `X` — GC-2's reuse, literal. -/
noncomputable def KeyFrame.stageHeight (F : KeyFrame O π) (A : Polynomial O) : ℕ∞ :=
  suppVal Polynomial.X A F.h F.e₁

axiom KeyFrame.stageHeight_eq_inf (F : KeyFrame O π) (A : Polynomial O) :
    F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun i => F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞))

/-! ### NODE C.03 [def] — `frameRes`, `stageField`, `stageCard`

D4: the blueprint writes `(hpin : _)` for `stageField`. Written out here. -/

/-- The frame residual `ψ` — B.28's `resPoly` at the frame's side, under the GC-1 pin. -/
noncomputable def KeyFrame.frameRes (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Polynomial (resField (Polynomial.X : Polynomial O)) :=
  resPoly π Polynomial.X F.key F.h F.e₁ F.hne H₀

/-- The stage residue field `K = F_Q(η_θ) ≅ F_{Q^{f₁}}`, as an iterated `AdjoinRoot` (GC-7). -/
abbrev KeyFrame.stageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Type _ :=
  AdjoinRoot (F.frameRes H₀ hpin)

/-- `|K| = Q^{f₁}` as a number (the lemma-level identity is C.04).
**D18 (cured):** signed as a plain `def`; `residueCard` is `noncomputable`, so it must be. -/
noncomputable def KeyFrame.stageCard (F : KeyFrame O π) [Finite (ResidueField O)] : ℕ :=
  residueCard O ^ F.f₁

/-! ### NODE C.04 [lemma] — `card_stageField` -/

axiom KeyFrame.card_stageField (F : KeyFrame O π) [Finite (ResidueField O)]
    (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Nat.card (F.stageField H₀ hpin) = residueCard O ^ F.f₁

/-! ### NODE C.06 [def] — `dvHgt`, `dvSupp`  (HOISTED above C.05, defect D12(i)) -/

/-- `dv(A_j)` — the level heights of the `Φ′`-development (`EFF.HE6.10`). -/
noncomputable def dvHgt (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) : ℕ∞ :=
  F.stageHeight (dev F.key f j)

/-- The cleared level support `inf_j (ℓ·dv(A_j) + u·j)` — B.14's shape at the `dv`-level. -/
noncomputable def dvSupp (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • dvHgt F f j + (u * j : ℕ∞))

/-! ### NODE C.07 [def] — the `dv`-side cluster  (HOISTED; D5 cures the missing members) -/

def DvOnSide (F : KeyFrame O π) (f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) ∧ dvHgt F f j ≠ ⊤

noncomputable def dvSideSet (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (fun j => DvOnSide F f u ℓ j)

noncomputable def dvSideMin (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).min' h

-- D5: the blueprint says "dvSideMax, dvSideLen, dvSideDeg analogous (one file, one public cluster
-- per B.20 precedent)" and declares none of them, while C.08/C.25/C.26/C.55 consume them. B.20's
-- landed cluster is `sideMin`/`sideMax`/`sideDeg` — there is NO landed `sideLen`, so `dvSideLen`
-- below has no template and is a stub-side determination.
noncomputable def dvSideMax (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).max' h

noncomputable def dvSideDeg (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  (dvSideMax F f u ℓ h - dvSideMin F f u ℓ h) / ℓ

/-- **STUB-SIDE DETERMINATION (D5).** No landed `sideLen` exists to copy; this is the only
reading under which C.08(b) `dvSideLen = ℓ * dvSideDeg` is the B.20(d) analogue. -/
noncomputable def dvSideLen (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  dvSideMax F f u ℓ h - dvSideMin F f u ℓ h

/-! ### NODE C.05 [lemma] — the level-1 reconciliation (GC-2's mandated seam) -/

axiom KeyFrame.stageHeight_degenerate (F : KeyFrame O π) (hh : F.h = 0)
    (A : Polynomial O) : F.stageHeight A = gaussVal A

axiom dvHgt_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (j : ℕ) :
    dvHgt F f j = npHgt F.key f j

axiom dvSupp_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (u ℓ : ℕ) :
    dvSupp F f u ℓ = suppVal F.key f u ℓ

/-! ### NODE C.08 [lemma] — class separation and the side-length identity

D3: `{u ℓ : ℕ}` added (unbound in the blueprint). -/

axiom dvOnSide_modEq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} {j j' : ℕ} (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    j ≡ j' [MOD ℓ]

axiom dvSideLen_eq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} (h : (dvSideSet F f u ℓ).Nonempty) :
    dvSideLen F f u ℓ h = ℓ * dvSideDeg F f u ℓ h

/-! ### NODE C.09 [def] — `LevelDatum` (the level-2 dictionary; TERMINAL SUPPLY to D and E) -/

/-- A level-2 label `(λ = u/ℓ, r)` over the frame `F`, with the dictionary numerals
`D″ = D′ℓd_r` and `T₂ = ℓd_rλ` (cleared: `T₂ = d_r·u`).  `EFF.HE6R1.18`. -/
structure LevelDatum (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    where
  u : ℕ
  ℓ : ℕ
  r : Polynomial (F.stageField H₀ hpin)
  hℓ : 0 < ℓ
  hcop : Nat.Coprime u ℓ
  /-- `κ > D′h`, cleared of the denominator `ℓ`. -/
  hκ : ℓ * (F.e₁ * F.f₁) * F.h < u
  hrmonic : r.Monic
  hrirr : Irreducible r
  hr0 : r.coeff 0 ≠ 0
  hrdeg : 0 < r.natDegree

/-- `D″ = D′·ℓ·deg r`.  **D18 (cured):** `noncomputable` — `L.r.natDegree` goes through
`AdjoinRoot.instCommRing`. -/
noncomputable def LevelDatum.keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree

/-- `T₂ = ℓ·d_r·λ`, cleared to the integer `d_r·u`.  **D18 (cured):** `noncomputable`. -/
noncomputable def LevelDatum.seam {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  L.r.natDegree * L.u

/-! ### NODE C.10 [lemma] — the dictionary regroupings -/

axiom LevelDatum.keyDeg₂_regroup {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.keyDeg₂ = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree)

axiom LevelDatum.seam_mul {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * L.seam = (L.ℓ * L.r.natDegree) * L.u

axiom LevelDatum.four_le_keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hD : 2 ≤ F.e₁ * F.f₁) (hjump : 2 ≤ L.ℓ * L.r.natDegree) : 4 ≤ L.keyDeg₂

/-! ### NODE C.11 [def] — the level-2 slot heights (THE tower recursion) -/

/-- The level-2 slot height of a coefficient: the level-1 support value at the side. -/
noncomputable def dv2Hgt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : ℕ∞ :=
  dvSupp F A L.u L.ℓ

noncomputable def dv2Pin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (j : ℕ) : ℕ∞ :=
  dv2Hgt L (dev Ψ f j)

noncomputable def dv2Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞))

/-! ### NODE C.12 [def+lemma] — `level2Field` -/

/-- `K₂ = K(β)`, the second `AdjoinRoot` iterate (GC-7). -/
abbrev level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : Type _ :=
  AdjoinRoot L.r

axiom card_level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) :
    Nat.card (level2Field L) = residueCard O ^ (F.f₁ * L.r.natDegree)

end LeanspecC
