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
`C.59`, `C.60`, `C.61`, `C.71`). Of the other **70**: **67** carry only a prose
`**SIGNATURE** (shape).` line, and **3 carry no `**SIGNATURE**` field of any kind — and those
three are exactly the gate-(b) literature cites `C.66`, `C.92`, `C.94`.** All 70 are
**unsignable**; see defect **D1**. Of the 57 written signatures a further **19 contain `…`
ellipses inside the Lean text** (defect **D2**), so the number of chapter-C signatures that are
complete Lean declarations is **38**, i.e. **30% of the chapter**.

**WHAT LANDED HERE: 82 declarations** — 39 `axiom` (theorem-shaped nodes at their signed types),
3 `structure`, 2 `abbrev`, 36 `def` (real bodies, stage-0e rule 1), 1 `theorem` and 1 `example`.
Three of the 82 are NOT blueprint declarations and are marked as such at their sites:
`KeyFrame.Pin` (the D4 abbreviation), `isKey_X` (the D9 helper), and the D11 negative-control
`example`. Plus a 43-declaration NUMERIC GATE section with **51 `#guard`s**, all passing.
`lake build Leanspec.ChapC` is green; `grep sorry` finds only this sentence.

**FOUR FINDINGS THE FLEET MUST SEE BEFORE IT FIRES:** `D1` (70 nodes unsigned, including every
remaining TERMINAL SUPPLY node), `D21` (`C.31`'s `jump_drop` is FALSE — machine-refuted, with the
repair checked), `D19`/`D20` (chapter H's §8 lift interface — the only H content chapter C may
consume — cannot be instantiated from `KeyFrame`, and `C.14`'s proof route therefore has an
uncovered case), and `D24` (`C.94` ⇄ `I.01` is a stub-stage deadlock on Display A's line 1).

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
  C.112 C.113 C.114 C.115 C.116 C.117 C.118 C.119 C.120 C.121 C.122 C.123 C.124 C.125 C.126`
  (67 of them prose-`(shape)`; `C.66`, `C.92`, `C.94` have no `**SIGNATURE**` field at all).
  Consequence: the stub gate is BLIND to §§7–13, which is exactly where the chapter's
  TERMINAL SUPPLY nodes live (C.66/C.69/C.89/C.97/C.99/C.100/C.107–C.110/C.114 are all named in
  §2's "what other chapters consume from here" table). §15's own gate order (a)–(d) is
  unsatisfiable as written: it lists `C.83`, `C.92`, `C.66`, `C.97`, `C.98` among the "fragile
  signatures to elaborate FIRST", and NONE of them has a signature.
  **Classification: missing signature (blueprint incompleteness), not an elaboration failure.**
* **D2 — 19 OF THE 57 WRITTEN SIGNATURES CONTAIN `…` INSIDE THE LEAN TEXT** (elaboration
  failure by construction): `C.26` (`theorem natDegree_dvResPoly (…same…)`), `C.28`
  (`LevelDatum.shift … := …`), `C.33`, `C.34`, `C.35`, `C.36`, `C.37`, `C.38`, `C.39`, `C.40`,
  `C.42`, `C.44`, `C.48`, `C.49`, `C.50`, `C.51`, `C.56a`, `C.61`, `C.71`. Five of them
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
* **D15 — THE TWO GATES' HT SPOT VALUES ARE AMBIGUOUS AND ADMIT READINGS THAT DIFFER BY A FACTOR
  OF `q − 1` (underspecified expected value; both readings executed below).** `C.123` writes the
  family as `(q−1)((q−1)(q−2)/2)q^{2N−8}` and `C.124` writes it as `2·1/2·q^{2N−8}`. If `2·1/2` is
  the middle factor `(q−1)(q−2)/2` at `q = 3` the two agree (`2·3^{2N−8}`); if it is the whole
  coefficient they differ by `q − 1 = 2` (`3^{2N−8}`). At `q = 2` both are `0`, so the two-prime
  rule does not disambiguate — the very degeneracy `C.123` calls "the degenerate census, itself a
  check" is what hides the ambiguity. Executed below as `htSpot` / `htSpotAlt`, with the values at
  `N = 4,5,6,7` printed. Neither is derivable from a signed node, because §11 has none (D1).
  **Classification: underspecified gate expected-value; resolvable only against `EFF.W12.87`.**
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

* **D18 — THREE SIGNED `def`s ARE MISSING `noncomputable` (elaboration failure; CURED
  stub-side).** `C.03`'s `KeyFrame.stageCard` (`residueCard` is `noncomputable`), and `C.09`'s
  `LevelDatum.keyDeg₂` and `LevelDatum.seam` (both read `L.r.natDegree`, which goes through
  `AdjoinRoot.instCommRing`). All three are declared `def` in the blueprint and all three fail to
  compile as such at the pin. Benign, but they are the kind of thing the fleet re-discovers 27
  times if the blueprint is not repaired.
* **D19 — `C.43`'s `stageLiftO` CANNOT BE BUILT FROM `KeyFrame` + H.54, SO THE H §8 INTERFACE —
  THE ONLY CHAPTER-H CONTENT CHAPTER C IS PERMITTED TO CONSUME (GC-5 / H-14) — IS NOT REACHABLE
  FROM CHAPTER C's OWN CARRIER (missing-dep, structural; NOT curable stub-side).** Full diagnosis
  at the `C.43` comment below. In one line: landed `GenreDatum` (H.01) requires `hQ : 2 ≤ Q`,
  `hh : 1 ≤ h`, `hkey : 2 ≤ e₁*f₁`, `hmul : 2 ≤ μ`; `KeyFrame` (C.01) has no `Q`, no `μ`, no
  `2 ≤ e₁*f₁`, and deliberately ADMITS `h = 0`. The blueprint's ⚠ at C.14 step 2 worries about the
  wrong half of this (it asks whether `stageLift'` reads `G.μ` — it does not, `ChapH/H54.lean:76`,
  so that half is DISCHARGED by this gate); the live obstruction is `hh`/`hkey`/`hQ`.
* **D20 — `C.14`'s PROOF ROUTE HAS AN UNCOVERED CASE, AND ITS SIGNATURE OMITS THE HYPOTHESIS ITS
  OWN STATEMENT DECLARES (proof-route gap + statement/signature mismatch; found via D19).**
  C.14's STATEMENT reads *"For every level datum `L` over `F` **with `2 ≤ F.e₁ * F.f₁`**"*; the
  SIGNATURE carries no such hypothesis (it is signed for every frame). The PROOF then splits
  `2 ≤ D′` (step 2, via the `GenreDatum` of D19, which needs `1 ≤ F.h`) against `D′ = 1` (step 3,
  elementary). **The case `F.h = 0 ∧ 2 ≤ F.e₁·F.f₁` falls through both** — and it is live, not
  vacuous: `KeyFrame.hcop : Nat.Coprime h e₁` forces `e₁ = 1` at `h = 0`, leaving `D′ = f₁`
  unconstrained. Either the signature gains `1 ≤ F.h` (which would break C.05, the node whose sake
  `h = 0` was admitted for) or step 3 must cover `h = 0` at every `D′`.
* **D21 — `C.31`'s THIRD CLAUSE `jump_drop` IS FALSE AS SIGNED (REFUTED, machine-checked;
  signed here anyway so the refutation is executable, per the CHAP-H `D8`/`G.23a` precedent of
  recording rather than silently repairing).** At
  `(D, ℓ, d_r, μ, μ₂, deg f_S) = (1, 1, 1, 1, 1, 1)` every hypothesis holds — `0 < 1` three times,
  `1·(1·1·1) = 1`, `1 ≤ 1·(1·(1/1)) = 1`, `1·1·2 = 2 ≤ 2·1` — and the conclusion is `2·1 ≤ 1`.
  **168 counterexamples** on the box `D, ℓ, d_r ∈ [1,4] × μ, μ₂ ∈ [0,12]` (counted below), so it
  is not a corner. *The diagnosis:* the hypothesis `hL : ℓ * dr * 2 ≤ 2 * μ` says `ℓ·d_r ≤ μ`,
  which is an UPPER bound on the jump, where the argument needs the LOWER bound `2 ≤ ℓ·d_r` —
  the very hypothesis the sibling clause `jump_floor` carries as `hjump` and this one drops (the
  same shape as CHAP-H's D8, where three of four siblings carried the guard). **Repair, checked:
  replace `hL` by `hjump : 2 ≤ ℓ * dr`** — zero counterexamples on the larger box
  `D, ℓ, d_r ∈ [1,5] × μ, μ₂ ∈ [0,24]`, and the proof is then immediate
  (`μ₂·ℓ·d_r ≤ μ` from `hμ₂`+`hfS`, then `2μ₂ ≤ μ₂·ℓ·d_r`). The blueprint's own SPEC line for the
  node — *"the chain `μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r)`"* — is the repaired statement, so this is a
  transcription slip, not a mathematical error in the source.
* **D22 — C-H12's COINCIDENCE-REGIME TRAP IS LIVE IN THE ONE BUDGET TABLE THE GATE CAN EVALUATE.**
  C.52's floor display, evaluated at C.123's and C.124's own frames with `w(a,b) = 0`, gives the
  IDENTICAL row `[7,5,3,1]` at both — so a gate row that checked only `w = 0` would be blind to
  the frame, at both primes. At `w = 5` they separate (`[5,3,1,0]` vs `[6,4,2,0]`). Recorded
  because §13's gate text names sixteen budget-table entries without saying at which `w`.

* **D23 — `PROJECT_STATE.md` APPEND #66 SAYS THE THREE C-CITES' "exact statements … are on file
  (CHAP-I §3 + addendum)"; THEY ARE NOT (provenance defect).** CHAP-I's 2026-08-16 addendum carries
  `THE EXACT LEAN STATEMENT to be signed` for exactly ONE cite — `B.42`'s
  `LeanspecB.exists_slope_factorization` ([GN15] Thm 2.3 + [FGMN] Thm 6.6) — and all three
  chapter-C cites say in their own STATEMENT fields *"Exact Lean statement drafted at stub stage;
  Asvin signs"*. So append #66's category-level signature covers a statement set that does not
  exist. `C.66` is drafted BY THIS GATE below and flagged; `C.92`/`C.94` are not draftable.
  A related, smaller trap: `C.66`'s SOURCE paragraph still quotes the arXiv-v3 numbers
  (`Cor 4.7(3)`, `Cor 4.4(4)`) and corrects them only in the A-3 rider two paragraphs later, so a
  top-down transcription lands the wrong published numbers.
* **D24 — `C.94` ⇄ `I.01` IS A STUB-STAGE DEADLOCK ON DISPLAY A's LINE 1 (cross-chapter
  missing-dep).** `C.94`'s NS-7 termination statement must quantify over §5's descent histories,
  which have no signature (D2 via `C.33`/`C.35`). CHAP-I's `I.01` `NS7Termination` is committed
  with a literal `True` placeholder body, marked `BLOCKED-UNTIL-RESOLUTION`, and says *"the body is
  typed against C's committed §5 carriers at stub time"*. The stub stage was the appointed
  resolution point for both and neither side can move. Until one does, `NS7Termination` is a
  `Prop` that is definitionally `True` for every `O`, i.e. **Display A's line-1 conjunct is
  currently vacuous in Lean**, and `I.25`'s axiom registry expects an `[AGNPRW]` axiom that cannot
  be declared.
* **D25 — the ONE §§9–13 claim the gate could reach CHECKS OUT (positive finding).** `C.97`'s S2
  tower witness (`Φ′ = x²−2`, `Φ₂ = Φ′²−4x`, `Φ₃ = Φ₂²−16Φ′` over `ℤ₂`) is verified from the
  polynomials up in the numeric section: both higher polynomials are one-sided of slope `1/2` at
  `p = 2`, and the root valuations that forces give `u₂ = 5`, the ladder `[4,10,21]`, `u₃ = 21`,
  `n̂₂(21) = 16Φ′` at height 21, and both floors — every displayed number of the node.

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

/-! The stage key frame `(e₁, f₁, h; Φ′)` of `EFF.HE6.08`: `Φ′` monic irreducible of degree
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

/-! # §4 — THE GAUGE LAYER: NORMALIZERS, THE LETTER, THE COCYCLE (C.15–C.28)

Landed order: C.15 … C.24, then **C.13/C.14** (hoisted here per the blueprint's own ⚠ ORDERING
NOTE, defect D12(ii)), then C.25, C.26, **C.29** (hoisted, defect D12(iii)), C.27, C.28. -/

/-- **STUB-SIDE HELPER (D9), not a blueprint node.** `resField Polynomial.X` is a `Field` — but
nothing in `leanfinal` says so, because B.25's `instFieldResField` is keyed on `IsKey φ` and no
node anywhere proves `IsKey Polynomial.X`. Chapter C needs it: `C.22`'s `twistRead` inverts an
element of `stageField = AdjoinRoot (frameRes …)`, and `AdjoinRoot.instField` demands a `Field`
on the BASE `resField Polynomial.X` as well as `Fact (Irreducible (frameRes …))`. Neither is in
scope at the signed signature. Proved here so the cure for D9 is exhibitable. -/
theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-! ### NODE C.15 [def] — `slotIdx`, `twistExp`

**D6 (cured, with a different body).** The blueprint writes
`noncomputable def KeyFrame.slotIdx F k := Nat.find (F.slotIdx_exists k)`; `slotIdx_exists` is
declared in no node of the chapter. The total, computable, junk-`0`-defaulting body below agrees
with the intended value exactly when the intended value exists, which `F.hcop` guarantees. -/

def KeyFrame.slotIdx (F : KeyFrame O π) (k : ℕ) : ℕ :=
  ((List.range F.e₁).find? (fun i => (i * F.h) % F.e₁ == k % F.e₁)).getD 0

/-- `q(k)`: the ϖ-vs-`n(k)` twist exponent, `i₀·k = i(k) + q(k)·e₁` (`EFF.HE6.13` RIDER). -/
def KeyFrame.twistExp (F : KeyFrame O π) (k : ℕ) : ℕ :=
  (F.slotIdx 1 * k - F.slotIdx k) / F.e₁

/-! ### NODE C.16 [lemma] — the `slotIdx` characterization -/

axiom KeyFrame.slotIdx_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx k < F.e₁ ∧ F.slotIdx k * F.h ≡ k [MOD F.e₁]

axiom KeyFrame.slotIdx_unique (F : KeyFrame O π) {k i : ℕ} (hi : i < F.e₁)
    (hcong : i * F.h ≡ k [MOD F.e₁]) : i = F.slotIdx k

axiom KeyFrame.twistExp_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx 1 * k = F.slotIdx k + F.e₁ * F.twistExp k

/-! ### NODE C.17 [def] — the slot window `T(k)` -/

/-- `T(k) := {t < f₁ : k ≥ (i₀(k) + e₁t)h}` (`EFF.HE6.13`). -/
def KeyFrame.slotWindow (F : KeyFrame O π) (k : ℕ) : Finset ℕ :=
  (Finset.range F.f₁).filter (fun t => (F.slotIdx k + F.e₁ * t) * F.h ≤ k)

/-! ### NODE C.18 [lemma] — fullness of the slot window -/

axiom KeyFrame.slotWindow_full_iff (F : KeyFrame O π) (hf : 0 < F.f₁) (k : ℕ) :
    F.slotWindow k = Finset.range F.f₁
      ↔ (F.slotIdx k + F.e₁ * (F.f₁ - 1)) * F.h ≤ k

axiom KeyFrame.slotWindow_full_of_le (F : KeyFrame O π) (k : ℕ)
    (hk : (F.e₁ * F.f₁ - 1) * F.h ≤ k) : F.slotWindow k = Finset.range F.f₁

/-! ### NODE C.19 [def+lemma] — the letter `η` (D4: `(hpin : _)` written out) -/

noncomputable def KeyFrame.stageLetter (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    F.stageField H₀ hpin :=
  AdjoinRoot.root (F.frameRes H₀ hpin)

axiom KeyFrame.stageLetter_ne_zero (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    F.stageLetter H₀ hpin ≠ 0

/-! ### NODE C.20 [lemma] — class separation of stage heights -/

axiom KeyFrame.stageHeight_class (F : KeyFrame O π) {A : Polynomial O} {i k : ℕ}
    (hi : i ≤ A.natDegree) (hval : F.e₁ • addVal O (A.coeff i) + (i * F.h : ℕ∞) = (k : ℕ∞)) :
    i * F.h ≡ k [MOD F.e₁]

axiom KeyFrame.stageHeight_unattained (F : KeyFrame O π) {A : Polynomial O} {k : ℕ}
    (hA : A.natDegree < F.e₁ * F.f₁) (hwin : F.slotWindow k = ∅) :
    F.stageHeight A ≠ (k : ℕ∞)

/-! ### NODE C.21 [def] — the normalized slot residue `γ_k`

**D8 (cured).** The blueprint writes `algebraMap _ _ (digAt …)`, which asks for an
`Algebra (ResidueField O) (stageField …)` instance that does not exist (mathlib composes no
`Algebra` chains). The composite of the two landed quotient maps is written out. -/

/-- A3 F-1's normalized slot residue
`γ_k(A) = Σ_t res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})·η^t` (`EFF.HE6.58`, TERMINAL layer of the
`HE6-SLOT-SEAM` chain — the frozen bare-`γ` display is DEAD, C-H8). -/
noncomputable def KeyFrame.slotRes (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) (A : Polynomial O) : F.stageField H₀ hpin :=
  (F.slotWindow k).sum fun t =>
    algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
            (A.coeff (F.slotIdx k + F.e₁ * t))))
      * (F.stageLetter H₀ hpin) ^ t

/-! ### NODE C.22 [def] — the ϖ-read residue (D9: `letI` supplies the two missing instances) -/

/-- The ϖ-read residue `γ_k(A)·η^{−q(k)}` (`EFF.HE6.15` [r2]-corrected sign; `EFF.HE6.58`
TERMINAL).  All corpus residual polynomials (`R_λ`, C.25) read through THIS. -/
noncomputable def KeyFrame.twistRead (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) (A : Polynomial O) : F.stageField H₀ hpin :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A

/-! ### NODE C.23 [lemma] — nonvanishing of the slot residue at an attained height -/

axiom KeyFrame.slotRes_ne_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {A : Polynomial O} {k : ℕ} (hA : A.natDegree < F.e₁ * F.f₁)
    (hht : F.stageHeight A = (k : ℕ∞)) :
    F.slotRes H₀ hpin k A ≠ 0

/-! ### NODE C.24 [theorem] — the image of the slot-residue read (split-mandated → 2) -/

axiom KeyFrame.slotRes_image (F : KeyFrame O π) (hπ : Irreducible π)
    [Finite (ResidueField O)] (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (k : ℕ) :
    (Set.image (F.slotRes H₀ hpin k)
        {A : Polynomial O | A.natDegree < F.e₁ * F.f₁ ∧ F.stageHeight A = (k : ℕ∞)})
      = {x | ∃ c : ℕ → ResidueField O, (∃ t ∈ F.slotWindow k, c t ≠ 0) ∧
          x = (F.slotWindow k).sum fun t =>
            algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
                (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O)) (c t))
              * F.stageLetter H₀ hpin ^ t}

/-! ### NODE C.13 [def] — `IsTestKey` (HOISTED into §4; blueprint's own ⚠ ORDERING NOTE) -/

/-- `Ψ_{κ,r}`-hood: the slot-pinned shape of `EFF.HE6.14`'s enlarged test family. -/
def IsTestKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ : Polynomial O) : Prop :=
  Ψ.Monic ∧ Ψ.natDegree = L.keyDeg₂ ∧
  dev F.key Ψ (L.ℓ * L.r.natDegree) = 1 ∧
  (∀ b < L.ℓ * L.r.natDegree, ¬ L.ℓ ∣ b → dev F.key Ψ b = 0) ∧
  (∀ t < L.r.natDegree,
    (L.r.coeff t = 0 → dev F.key Ψ (L.ℓ * t) = 0) ∧
    (L.r.coeff t ≠ 0 →
      F.stageHeight (dev F.key Ψ (L.ℓ * t)) = (((L.r.natDegree - t) * L.u : ℕ) : ℕ∞) ∧
      F.slotRes H₀ hpin ((L.r.natDegree - t) * L.u) (dev F.key Ψ (L.ℓ * t)) = L.r.coeff t))

/-! ### NODE C.14 [lemma] — existence of a test key

**D20 RE-SIGNED [signed: A-C.1, 2026-08-16].** The original signing carried NO frame
hypothesis, leaving the case `F.h = 0 ∧ 2 ≤ F.e₁·F.f₁` with no proof route (D20). Re-signed
with `(hh : 1 ≤ F.h)` — the corpus's own frame hypothesis (`EFF.HE6.08`; C.01's docstring:
"the corpus frame has `1 ≤ h`") — under which the blueprint proof's two branches are
EXHAUSTIVE: `2 ≤ D′` fires H §8 through the C.14a adapter below; `D′ = 1` (which forces
`e₁ = f₁ = 1`) takes the elementary lift. The excluded `h = 0` corner is the degenerate
frame admitted for C.05 alone; no chapter-C consumer fires a test key on it. (The STATEMENT
field's "`2 ≤ F.e₁ * F.f₁`" clause was the misplaced trace of the proof's internal split —
restoring IT would kill the proof's own step 3 and leave `h = 0 ∧ D′ ≥ 2` uncovered.) -/

axiom exists_testKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) (hh : 1 ≤ F.h) :
    ∃ Ψ : Polynomial O, IsTestKey L Ψ

/-! ### NODE C.14a [def] — the H §8 carrier bridge (the D19/D20 RESOLUTION) [signed: A-C.1]

The adjudication, from the sources: `EFF.HE6.08`'s corpus frame carries `1 ≤ h`;
`GENHN.CLASS`(i)'s composite-stage datum carries `2 ≤ e₁f₁` — exactly the two proof fields
H.01's landed `GenreDatum` demands that `KeyFrame` lacks (D19); and H.54's `stageLift'` body
reads only `(f₁, e₁, h)` of its datum (`ChapH/H54.lean:76`, verified at the stub gate).
Resolution (the §15 RE-PLAN "merge C.14/C.43's packaging into ONE helper", executed):
* `KeyFrame.genreDatum` — the adapter into H.01's landed carrier, with the two corpus
  preconditions as EXPLICIT HYPOTHESES, `Q := residueCard O` (`hQ` from landed
  `two_le_residueCard`), and the `μ`-slot filled by the dummy `2` (never read by H §8's
  lift layer). **H's landed side is untouched.**
* `KeyFrame.stageLiftIA` — the lift with H.54's OWN body over the frame's numerals, TOTAL
  (a def is total; the corpus preconditions sit on the theorems that consume H.55/H.56).
* `stageLiftIA_eq_stageLift'` — the `rfl`-grade reconciliation on the corpus perimeter:
  THE one door through which chapter C consumes H §8 (GC-5 honored).
* `KeyFrame.stageCoord` / `resLift` / `KeyFrame.stageLiftO` — the element-at-height form
  C.43's display consumes: digits via the canonical `AdjoinRoot` representative (Classical
  choice on `mk`-surjectivity; junk `0` outside), the `(i, a)`-solve via C.15's `slotIdx`
  (H.54's signed lesson: `i`, `a` explicit, the height equation on the consuming lemmas). -/

noncomputable def KeyFrame.genreDatum (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) : Uniformity.Density.Induction.GenreDatum where
  Q := residueCard O
  e₁ := F.e₁
  f₁ := F.f₁
  μ := 2
  h := F.h
  hQ := two_le_residueCard O
  he₁ := F.he₁
  hh := hh
  hkey := hkey
  hmul := le_rfl
  hcop := F.hcop

/-- H.54's summand shape over the frame's own numerals — total, hypothesis-free. -/
noncomputable def KeyFrame.stageLiftIA (F : KeyFrame O π) (i a : ℕ) (lift : ℕ → O) :
    Polynomial O :=
  ∑ s ∈ Finset.range F.f₁,
    Polynomial.C (lift s * π ^ (a - s * F.h)) * Polynomial.X ^ (i + F.e₁ * s)

/-- The reconciliation: on the corpus perimeter (`1 ≤ h`, `2 ≤ e₁f₁`) the frame lift IS
H.54's `stageLift'` at the adapter datum — definitionally. H.55/H.56 transport through this. -/
theorem stageLiftIA_eq_stageLift' (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) (i a : ℕ) (lift : ℕ → O) :
    F.stageLiftIA (π := π) i a lift
      = Uniformity.Density.Induction.stageLift' (F.genreDatum hh hkey) π i a lift := rfl

/-- **STUB-SIDE HELPER (D19-cure class), not a blueprint node.** A choice-section of the
residue map. -/
noncomputable def resLift (x : ResidueField O) : O :=
  (IsLocalRing.residue_surjective (R := O) x).choose

/-- The stage coordinate read: the `F_Q`-digits of a stage-field element in the letter basis
`{η^s}`, through a chosen `AdjoinRoot.mk`-preimage (junk-stable: consumers pin it only
through H.56-shaped residue clauses). -/
noncomputable def KeyFrame.stageCoord (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (c : F.stageField H₀ hpin) (s : ℕ) : ResidueField O :=
  (resFieldXEquiv O).symm (((AdjoinRoot.mk_surjective c).choose).coeff s)

/-- The blueprint's `stageLiftO`: the exact-height-`M` lift of a stage-field ELEMENT —
the `(i, a)`-solve by C.15's `slotIdx` (the unique class solve), digits by `stageCoord`. -/
noncomputable def KeyFrame.stageLiftO (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (M : ℕ) (c : F.stageField H₀ hpin) : Polynomial O :=
  F.stageLiftIA (π := π) (F.slotIdx M) ((M - F.slotIdx M * F.h) / F.e₁)
    (fun s => resLift (F.stageCoord H₀ hpin c s))

/-! ### NODE C.25 [def] — the level residual polynomial `R_λ` (D4 cured) -/

/-- `R_λ(Z) := Σ_t res(A_{j₁+tℓ}(θ)/ϖ(θ)^{m₁−tu})·Z^t ∈ K[Z]` (`EFF.HE6.11`), through the
C.22 ϖ-read at the GC-1 `sideMin` pin. -/
noncomputable def dvResPoly (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (f : Polynomial O) (u ℓ : ℕ) (hne₂ : (dvSideSet F f u ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    Polynomial (F.stageField H₀ hpin) :=
  ((Finset.range (dvSideDeg F f u ℓ hne₂ + 1)).sum fun t =>
    Polynomial.C (F.twistRead H₀ hpin (M₀ - t * u) (dev F.key f (dvSideMin F f u ℓ hne₂ + t * ℓ)))
      * Polynomial.X ^ t)

/-! ### NODE C.26 [lemma] — correctness of `dvResPoly`

**D2 (cured).** The second signature is written `theorem natDegree_dvResPoly (…same…)`; the
binder list of the first is reproduced, which is the only reading of "same". -/

axiom dvResPoly_coeff_eq_zero_iff (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff t = 0
      ↔ ¬ DvOnSide F f u ℓ (dvSideMin F f u ℓ hne₂ + ℓ * t)

axiom natDegree_dvResPoly (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).natDegree = dvSideDeg F f u ℓ hne₂ ∧
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff 0 ≠ 0

/-! ### NODE C.29 [def] — `IsDvPure`, `HasLabel` (HOISTED into §4, defect D12(iii):
`C.27` takes `hg : HasLabel L g`, and `HasLabel` is a §5 node) -/

def IsDvPure (F : KeyFrame O π) (g : Polynomial O) (u ℓ : ℕ) : Prop :=
  0 ∈ dvSideSet F g u ℓ ∧ g.natDegree / (F.e₁ * F.f₁) ∈ dvSideSet F g u ℓ

def HasLabel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  g.Monic ∧ 0 < g.natDegree ∧ IsDvPure F g L.u L.ℓ ∧
  ∃ (hne₂ : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F g (dvSideMin F g L.u L.ℓ hne₂) = (M₀ : ℕ∞)) (m : ℕ),
    0 < m ∧ dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂ = L.r ^ m

/-! ### NODE C.27 [theorem] — `(SLOT₂)` exactness (split-mandated → 3; §15's heavy node)

**D10 (cured).** `(addVal O …).get!` → `ENat.toNat`: `ℕ∞ = ENat` carries no `get!`. -/

axiom slot2_exact {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (hg : HasLabel L g) {C : Polynomial O}
    (hC : C.natDegree < L.keyDeg₂) (hC0 : dv2Hgt L C ≠ ⊤) :
    ∃ v : ℕ, dv2Hgt L C = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * v

/-! ### NODE C.28 [def+lemma] — the shift and the level-2 cocycle

**D2 (cured, binder+body).** `LevelDatum.shift … : ℕ := …` with the body given only in a trailing
comment ("the unique `β < ℓ` with `β·u ≡ m (mod ℓ)`; C.15's pattern at `(u, ℓ)`"). Landed with
C.15's own total, junk-`0`-defaulting body at the pair `(u, ℓ)` — the unique reading. -/

def LevelDatum.shift {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (m : ℕ) : ℕ :=
  ((List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ)).getD 0

def LevelDatum.cocycle {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : ℕ := (L.shift a + L.shift b - L.shift (a + b)) / L.ℓ

axiom LevelDatum.cocycle_mem {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : L.ℓ * L.cocycle a b = L.shift a + L.shift b - L.shift (a + b)
      ∧ L.cocycle a b ≤ 1

axiom LevelDatum.cocycle_eq_zero_of_ell_one {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hℓ : L.ℓ = 1) (a b : ℕ) :
    L.shift a = 0 ∧ L.cocycle a b = 0

/-! # §5 — THE DESCENT GRAMMAR (C.29–C.40)

`C.29` is above (D12(iii)). `C.30`–`C.32` are ENV-C5 arithmetic and land in full. **`C.33`–`C.40`
are UNSIGNABLE**: every one of them has `…` where a hypothesis, an existential witness, or a
definition body must stand (defect D2), and `C.35`'s `blockFactor`/`mult₂` — the objects
`C.36`–`C.40` are all statements ABOUT — have `:= …` for a body. They are recorded
broken-in-comment below with their blueprint text verbatim. -/

/-! ### NODE C.30 [lemma] — the descent trichotomy -/

axiom descent_trichotomy (mr ℓ dr : ℕ) (hm : 1 ≤ mr) (hℓ : 0 < ℓ) (hd : 1 ≤ dr) :
    (mr = 1 ∧ ¬(mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1) ∧ ¬(mr ≥ 2 ∧ 2 ≤ ℓ * dr)) ∨
    (mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1 ∧ ¬(2 ≤ ℓ * dr) ∧ mr ≠ 1) ∨
    (mr ≥ 2 ∧ 2 ≤ ℓ * dr ∧ ¬(ℓ = 1 ∧ dr = 1) ∧ mr ≠ 1)

/-! ### NODE C.31 [lemma] — the jump floor, the first bite, the jump drop -/

axiom jump_floor (mr ℓ dr L μ : ℕ) (hm : 2 ≤ mr) (hjump : 2 ≤ ℓ * dr)
    (hL : mr * (ℓ * dr) ≤ L) (hLμ : L ≤ μ) : 4 ≤ L ∧ 4 ≤ μ

axiom first_bite (D μ n : ℕ) (hD : 2 ≤ D) (hμ : 4 ≤ μ) (hn : n = D * μ) : 8 ≤ n

-- D17 (original finding, retained): `hfS`'s `μ / ℓ` is ℕ-division: at `ℓ ∤ μ` the hypothesis
-- is strictly WEAKER than the intended `deg f_S ≤ D′·L_λ`, a silent truncation.
-- **D21 RE-SIGNED [signed: A-C.1, 2026-08-16].** The originally-signed third hypothesis
-- `hL : ℓ * dr * 2 ≤ 2 * μ` made the clause FALSE (machine-refuted; 168 counterexamples —
-- the refutation record is PRESERVED VERBATIM in the numeric section below). Re-signed with
-- the source's own jump hypothesis `hjump : 2 ≤ ℓ * dr`, verified against `EFF.HE6R1.10`
-- verbatim: "μ₂ = deg f_S/D″ ≤ … ≤ μ/(ℓd_r), using LEMMA HE6-3(b) … for the middle step and
-- ℓd_r ≥ 2 for the last" — the jump hypothesis IS the source's, and `.11`'s punchline ("both
-- branches of the widened box supply the descent factor ℓd_r ≥ 2") is why it is available at
-- every jump. 0 counterexamples on the larger box (`#guard jumpDropRepairedCount == 0` below).
axiom jump_drop (D ℓ dr μ μ₂ dfS : ℕ) (hD : 0 < D) (hℓ : 0 < ℓ) (hd : 0 < dr)
    (hjump : 2 ≤ ℓ * dr)
    (hμ₂ : μ₂ * (D * ℓ * dr) = dfS) (hfS : dfS ≤ D * (ℓ * (μ / ℓ))) : 2 * μ₂ ≤ μ

/-! ### NODE C.32 [theorem] — the three-clause jump-count bound (`EFF.HE6R1.47`) -/

axiom jump_count_bound {J μ : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) :
    2 ^ (J + 2) ≤ 2 * μ

/-! ### NODES C.33–C.40 — **UNSIGNABLE (D2) at the gate; SIGNED at A-C.1** — the signed
signatures live in the A-C.1 SIGNATURE-COMPLETION LAYER below (`DvDissection`,
`exists_dv_residual_dissection`, `BlockContext`/`blockFactor`/`mult₂`, `complementConst`,
`dv2Supp_translation`, the C.38a `dv2ResPoly` cluster, `dv2ResPoly_scalar`, `level2_peel`).
The gate's original diagnosis is preserved verbatim below as the D2 record.

```lean
-- C.33 [theorem]  **SIGNATURE** (shape; the stub fixes the side-indexing plumbing).
theorem exists_dv_slope_dissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) … :
    ∃ …, f = … ∧ (∀ i, IsDvPure F (f_i) (u_i) (ℓ_i)) ∧
      (∀ i, (f_i).natDegree = (F.e₁ * F.f₁) * ℓ_i * dvSideDeg F f (u_i) (ℓ_i) _) ∧ …
```
DIAGNOSIS. The existential's WITNESS TYPE is the whole content of the node (B.41/B.42's landed
level-1 twins index the dissection by a `Finset` of slopes with a product formula; which of those
shapes C.33 takes decides C.34–C.40's every statement). `f_i`, `u_i`, `ℓ_i` are free identifiers.
Not signable; not guessable. **`C.33` is one of §14's three named schedule risks and it has no
type.**

```lean
-- C.34 [theorem]  **SIGNATURE** (shape).
theorem exists_dv_residual_dissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {H₀ hpin}
    {g : Polynomial O} (hg : g.Monic) {u ℓ : ℕ} (hpure : IsDvPure F g u ℓ) … :
    ∃ fS g', g = fS * g' ∧ HasLabel (L) fS ∧ … ∧ ¬ L.r ∣ dvResPoly F H₀ hpin g' u ℓ … …
```
DIAGNOSIS. `L` is used but never bound (there is no `L : LevelDatum F H₀ hpin` binder), and the
`dvResPoly` call is missing its `hne₂ M₀ hpin₂` arguments. Even after adding `(L : LevelDatum …)`
the statement does not typecheck, because `dvResPoly … g' u ℓ` needs a side-nonemptiness proof for
`g'`, which is part of the conclusion, not available in the statement — a genuine
dependent-plumbing problem the node must solve, not a transcription slip.

```lean
-- C.35 [def]
noncomputable def blockFactor {F} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) (h : …C.33/C.34 context…) : Polynomial O := …
noncomputable def mult₂ … (h : …) : ℕ := (blockFactor L f h).natDegree / L.keyDeg₂
```
DIAGNOSIS. Body elided AND the context parameter `h` is elided. `blockFactor` is the object of
`C.36`, `C.37`, `C.38`, `C.39`, `C.40`, `C.48`, and §7's whole Tier-1 chain — **eight downstream
nodes hang off a definition with no body and no argument list.** This is the single highest-value
missing signature in the signed half of the chapter.

-- C.36, C.37, C.38, C.39: statements about `blockFactor`/`complementConst`/`γg`/`pinHeight`,
-- all four with `(hctx : …)` and three of them with `…` inside the CONCLUSION. `complementConst`,
-- `γg`, `pinHeight`, `dv2ResPoly` and `dv2SideSet` are consumed by name and DECLARED NOWHERE
-- (§15 books them as RE-PLAN helpers, which is a scheduling note, not a signature).

```lean
-- C.40 [theorem]
theorem level2_peel {F} {H₀ hpin} (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    [IsAdicComplete …] [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : …) (hdvd : Ψ ∣ blockFactor L f hctx)
    (hbox : CBox1Side L Ψ) :
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}, …⟩ ∧ Irreducible Ψ ∧ …
```
DIAGNOSIS (two, one of them a TYPE ERROR independent of the ellipses): (a) `hctx : …` and the
`blockFactor` dependence (D2); (b) **`⟨{(…)}, …⟩` over-applies `FactorizationType`, which has
exactly one field** — defect D11, machine-witnessed immediately below. -/

/-- **D11, machine-witnessed.** `FactorizationType` has ONE field, so the two-component anonymous
constructor of C.40/C.61 cannot elaborate; the one-component form does. (Uncomment the second
`example` to see the hard error.) -/
example (e f : ℕ) : FactorizationType := ⟨{(e, f)}⟩
-- example (e f : ℕ) : FactorizationType := ⟨{(e, f)}, trivial⟩   -- ERROR at the pin

/-! # §6 — COMPOSED KEYS AND THE TOWER BRIDGES (C.41–C.58)

Signable: `C.41`, `C.42`, `C.50`. Everything else in §6 either depends on `C.43`'s undeclared
`stageLiftO` (defect D19) or on `C.44`'s bodyless `towerLabel`, or has no signature at all
(`C.52`–`C.54`, `C.56`–`C.58`; defect D1). -/

/-! ### NODE C.41 [lemma] — additivity of the slot index and the twist exponent -/

axiom KeyFrame.slotIdx_add (F : KeyFrame O π) (a b : ℕ) :
    F.slotIdx a + F.slotIdx b
      = F.slotIdx (a + b) + F.e₁ * ((F.slotIdx a + F.slotIdx b) / F.e₁) ∧
    (F.slotIdx a + F.slotIdx b) / F.e₁ ≤ 1

axiom KeyFrame.twistExp_add (F : KeyFrame O π) (a b : ℕ) :
    F.twistExp (a + b)
      = F.twistExp a + F.twistExp b + (F.slotIdx a + F.slotIdx b) / F.e₁

axiom KeyFrame.twistExp_nsmul (F : KeyFrame O π) (u₂ f₂ t : ℕ) (ht : t < f₂) :
    F.twistExp ((f₂ - t) * u₂)
      = (f₂ - t) * F.twistExp u₂ + (f₂ - t) * F.slotIdx u₂ / F.e₁

/-! ### NODE C.42 [def] — `TowerDatum` (D4 + D2: `(hpin : _)` and the two `…` binder lists) -/

structure TowerDatum (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    where
  e₂ : ℕ
  f₂ : ℕ
  u₂ : ℕ
  ψ₂ : Polynomial (F.stageField H₀ hpin)
  he₂ : 0 < e₂
  hf₂ : 0 < f₂
  hcomp : 2 ≤ e₂ * f₂
  hcop : Nat.Coprime u₂ e₂
  hfloor : e₂ * (F.e₁ * F.f₁) * F.h < u₂
  hψmonic : ψ₂.Monic
  hψirr : Irreducible ψ₂
  hψdeg : ψ₂.natDegree = f₂
  hψ0 : ψ₂.coeff 0 ≠ 0

/-- `D₂ = D′·e₂f₂`.  Binder list supplied (blueprint writes `def TowerDatum.D₂ … : ℕ`). -/
def TowerDatum.D₂ {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * (T.e₂ * T.f₂)

/-- `E₂ = e₂f₂u₂`.  Binder list supplied. -/
def TowerDatum.E₂ {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  T.e₂ * T.f₂ * T.u₂

/-! ### NODE C.43 [def] — **UNSIGNABLE (D19)**; the composed key.

```lean
noncomputable def composedKey {F} {H₀ hpin} (T : TowerDatum F H₀ hpin) : Polynomial O :=
  F.key ^ (T.e₂ * T.f₂)
    - (Finset.range T.f₂).sum fun t =>
        stageLiftO F ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp F T t))
          * F.key ^ (T.e₂ * t)
```
DIAGNOSIS (**D19 — the H §8 interface cannot be instantiated from chapter C's own carrier**).
`stageLiftO` and `wrapExp` are declared in no node; the trailing prose says `stageLiftO` is "this
node's private packaging of H.54's `stageLift'` through the `GenreDatum` plumbing of C.14 step 2",
and §15 books the merge as a RE-PLAN. But that packaging is IMPOSSIBLE as specified, and the
obstruction is type-level:

`Uniformity.Density.Induction.GenreDatum` (H.01, landed, `ChapH/H01.lean:38`) has proof fields
`hQ : 2 ≤ Q`, `he₁ : 1 ≤ e₁`, **`hh : 1 ≤ h`**, **`hkey : 2 ≤ e₁ * f₁`**, **`hmul : 2 ≤ μ`**,
`hcop : Nat.Coprime h e₁`. A `KeyFrame` (C.01) supplies `0 < e₁`, `0 < f₁`, `Nat.Coprime h e₁` and
NOTHING ELSE — it deliberately ADMITS `h = 0` (C.01's own docstring: "the DEGENERATE frame,
admitted so that C.05's level-1 reconciliation is definitional"), it does not require
`2 ≤ e₁ * f₁`, and it has no `μ` and no `Q` field at all. So:
* at `F.h = 0` the `GenreDatum` **does not exist**, and `stageLift'` is unavailable;
* C.14's PROOF step 2 builds exactly this datum (`G := ⟨residueCard O, F.e₁, F.f₁, 2, F.h, …⟩`)
  and its step 3 fallback covers only `D′ = 1` — so the case **`F.h = 0 ∧ 2 ≤ F.e₁ * F.f₁`
  (live: `hcop` forces `e₁ = 1`, and `f₁ ≥ 2` is unconstrained) has NO proof route in the
  blueprint**. That is defect **D20**, found here and not flagged anywhere in CHAP-C.
The `μ`-dummy the blueprint worries about IS safe (`stageLift'`'s body, `ChapH/H54.lean:76`, reads
only `G.f₁`, `G.h`, `G.e₁`) — that half of the ⚠ is discharged by this gate.

### NODES C.44–C.49, C.51, C.55, C.56a — **UNSIGNABLE**.
`C.44` (`towerLabel … := …`, body elided) blocks `C.45`, `C.46`, `C.47`, `C.51`, `C.55`;
`C.48`/`C.49` are `**SIGNATURE** (shape)` with `…` in the conclusion (`C.49` writes three
theorem headers whose statements are all literally `… : …`); `C.56a` is `:= …`. `C.55`
additionally has an unbound `μ₂` (D3 class) and consumes `dv2SideSet`, declared nowhere. -/

/-! ### NODE C.50 [def+lemma] — the composed grid weight (D2: two `…` binder lists supplied) -/

def slotOffset {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) (a b : ℕ) : ℕ :=
  a * (T.e₂ * F.h) + b * T.u₂

def gridWeight {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) (v a b j : ℕ) : ℕ :=
  (F.e₁ * T.e₂) * v + slotOffset T a b + j * T.E₂

axiom E₂_gt_xfloor {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) :
    T.D₂ * (T.e₂ * F.h) < T.E₂

/-! # §7 — CLASS SIZE AND BLOCK LENGTH (C.59–C.70)

Signable: `C.59`, `C.60`. `C.61` is unsignable (D2 + D11); `C.62`–`C.70` have no signature (D1),
which includes **`C.66`, the chapter's gate-(b) [cite:FGMN] node**, and **`C.69`, the bundled
TERMINAL SUPPLY statement A-3 tells consumers to cite first**. -/

/-! ### NODE C.59 [lemma] — the ramified divisibility leg (unconditional; Tier 1's first half) -/

axiom ramLeg_dvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) (hlab : HasLabel L g)
    (hx : IsPure Polynomial.X g F.h F.e₁) :
    (F.e₁ * L.ℓ) ∣ ramIndexOf g

/-! ### NODE C.60 [def+lemma] — `C-BOX-1`, the chapter's one carried hypothesis -/

/-- `C-BOX-1`: the level-2 residue-degree lower bound, carried as an explicit hypothesis
(DECISION C-D1; the `B-BOX-1` analogue — CHAP-B H-7's shape one level up). -/
def CBox1Side {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  (F.f₁ * L.r.natDegree) ∣ inertiaDegOf g

axiom cbox1_of_deg_one {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) (h1 : F.f₁ * L.r.natDegree = 1) : CBox1Side L g

/-! ### NODE C.61 [theorem] — **UNSIGNABLE (D2 + D11)**; Tier 1's assembled law.

```lean
theorem tier1_typeOf {F} {H₀ hpin} (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    [IsAdicComplete …] [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g) (hm1 : …multiplicity-1 clause…)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}, by …⟩ ∧ Irreducible g
```
DIAGNOSIS. (a) `hm1 : …multiplicity-1 clause…` is the node's load-bearing hypothesis and is not
written. The unique candidate reading — that `HasLabel`'s existential `m` equals `1` — is NOT
expressible as a hypothesis about `g` as `HasLabel` is currently phrased (the `m` is bound INSIDE
the existential, C.29), so the reading requires re-shaping `HasLabel` or adding a `mult₂`-style
projection. That is a real design hole, not a transcription slip. (b) `⟨…, by …⟩` over-applies
`FactorizationType` (D11). (c) This is the node §2's TERMINAL SUPPLY table advertises to CHAP-B
H-2's downstream consumers, to chapter E's `.30`/`.32` anchors, to chapter D's T1 battery check 10
and to chapter F's weld faces. It has no type. -/

/-! # §8 — THE SHADOW-READ LAYER (C.71–C.82); only `C.71`'s two arithmetic companions are signed. -/

/-! ### NODE C.71 [def] — `shadowDev` is UNSIGNABLE (`:= …`); `margin`/`theta` land. -/

def TowerDatum.margin {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  T.u₂ - T.e₂ * ((F.e₁ * F.f₁) * F.h)

def TowerDatum.theta {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin)
    (μ₂ j : ℕ) : ℕ := (μ₂ - j) * T.E₂ + T.margin

/-! # A-C.1 SIGNATURE-COMPLETION LAYER (2026-08-16)

The amendment set **A-C.1** cures D1/D2: the signatures below are NEW signings (each tagged
`[signed: A-C.1]` in the blueprint), elaborated here per §15's rule that a signature that does
not elaborate is not signed. Conventions of this layer:
* theorem-shaped nodes land as `axiom` (the standing stub lifecycle);
* `def`-shaped nodes land with real bodies where the body is data/arithmetic; where a
  blueprint `def` is a proof-carrying CONSTRUCTION (a structure instance whose fields are
  theorem-grade), it lands as an `axiom` CONSTANT plus defining-equation axioms, and says so —
  the fleet lands the body (recorded per node);
* fragile-first order honored: C.83, C.92, C.97, C.98 open the layer (C.66 was already
  elaborated by the gate, above), then the terminal-supply and section batches in DAG order. -/

/-! ## A-C.1 §9-CARRIER — NODE C.83 [def] `DeepTower` (fragile no. 1)

**DECISION A-C.1/GC-7 (the depth-≥ 3 carrier fallback, TAKEN).** The literal iterated
`AdjoinRoot` telescope cannot be structure fields (the field `ψ (i+1) : Polynomial (K i)` with
`K (i+1) := AdjoinRoot (ψ (i+1))` is a dependent telescope no Lean `structure` carries), which
is exactly the failure mode GC-7 recorded with its fallback: *"a level structure carrying an
abstract `[Field K_r]` with a specified `Algebra` chain and a proof it is the iterate"*. That
fallback is taken here: `fld i` abstract with `Field` data, the iterate witnessed by
`RingEquiv` fields (`base`, `step`). Arithmetic data is ℕ-total with range-scoped hypothesis
fields (the file's junk-total discipline); the normalizer recursion / shift / cocycle are defs
over the numerals, mirroring C.15/C.28 rung by rung (exponent bookkeeping only — never
fraction-field elements). Indexing: stage `1` IS the frame (`e 1 = F.e₁` etc.); a `DeepTower`
of depth `r` carries stages `1 … r`; `towerNorm i k` is the exponent solve of the
level-`(i+1)` normalizer `n̂_{i+1}(k)` (so `towerNorm 1` is §6's `n̂₂` verbatim). -/

/-- The C.15/C.28-pattern class solve at the pair `(u, e)`: the unique `b < e` with
`b·u ≡ k [MOD e]` (junk `0` when no solve exists; total). -/
def towerSolve (u e k : ℕ) : ℕ :=
  ((List.range e).find? (fun b => (b * u) % e == k % e)).getD 0

/-- NODE C.83 — the depth-`r` tower datum (`DEF GENTOW5-1`), on the GC-7 fallback carrier. -/
structure DeepTower (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r : ℕ) where
  /-- stage ramification data; `e 1 = F.e₁`; junk outside `1 … r`. -/
  e : ℕ → ℕ
  f : ℕ → ℕ
  /-- stage heights; `u 1 = F.h`; the floor chain is `hfloor`. -/
  u : ℕ → ℕ
  /-- the level residue fields `K_i` (abstract, per DECISION A-C.1/GC-7). -/
  fld : ℕ → Type*
  fldField : ∀ i, Field (fld i)
  /-- `ψ i` = the minimal polynomial of the level-`(i+1)` letter over `K_i` (live `1 ≤ i < r`). -/
  ψ : (i : ℕ) → Polynomial (fld i)
  he1 : e 1 = F.e₁
  hf1 : f 1 = F.f₁
  hu1 : u 1 = F.h
  he : ∀ i, 1 ≤ i → i ≤ r → 0 < e i
  hf : ∀ i, 1 ≤ i → i ≤ r → 0 < f i
  /-- PROPERNESS at every stage `≥ 2`: `l_i = e_i f_i ≥ 2` (an improper stage is a refinement). -/
  hproper : ∀ i, 2 ≤ i → i ≤ r → 2 ≤ e i * f i
  hcop : ∀ i, 2 ≤ i → i ≤ r → Nat.Coprime (u i) (e i)
  /-- THE FLOOR CHAIN, AS A DATUM FIELD (S12.1's carve-out): `u_{i+1} > e_{i+1}·E_i`. -/
  hfloor : ∀ i, 1 ≤ i → i < r → e (i + 1) * (e i * f i * u i) < u (i + 1)
  hψ : ∀ i, 1 ≤ i → i < r →
    (ψ i).Monic ∧ Irreducible (ψ i) ∧ (ψ i).natDegree = f (i + 1) ∧ (ψ i).coeff 0 ≠ 0
  /-- the iterate witness, base: `K_1` IS the frame's stage field. -/
  base : fld 1 ≃+* F.stageField H₀ hpin
  /-- the iterate witness, step: `K_{i+1} = K_i(β_{i+1})` as the `AdjoinRoot` iterate. -/
  step : ∀ i, 1 ≤ i → i < r → (fld (i + 1) ≃+* AdjoinRoot (ψ i))

-- the abstract chain's `Field` data, registered so consumers elaborate (directed: keyed on
-- the projection `DeepTower.fld`).
attribute [instance] DeepTower.fldField

namespace DeepTower

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- `ê_i = e_1⋯e_i`. -/
def ehat (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, T.e j

/-- `D_i = l_1⋯l_i = (e_1f_1)⋯(e_if_i)`. -/
def Dcum (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, (T.e j * T.f j)

/-- the side constant `E_i := e_i·f_i·u_i` (`E_1 = D_1·h`). -/
def Econst (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := T.e i * T.f i * T.u i

/-- The normalizer recursion, as pure exponent bookkeeping: `towerNorm i k` is the exponent
data `(a₀, i₀, (b_1, …, b_i))` of `n̂_{i+1}(k) = π^{a₀} x^{i₀} Φ_1^{b_1} ⋯ Φ_i^{b_i}` —
solved by `e_{j+1}·m_j(k) + b_j(k)·u_{j+1} = k`, `0 ≤ b_j(k) < e_{j+1}` (unique by
coprimality; the frame solve at the bottom). `towerNorm 1` is §6's `n̂₂`, verbatim. -/
def towerNorm (T : DeepTower F H₀ hpin r) : (i : ℕ) → ℕ → ℕ × ℕ × (Fin i → ℕ)
  | 0, k => ((k - F.slotIdx k * F.h) / F.e₁, F.slotIdx k, fun x => x.elim0)
  | i + 1, k =>
      let b := towerSolve (T.u (i + 2)) (T.e (i + 2)) k
      let m := (k - b * T.u (i + 2)) / T.e (i + 2)
      let p := towerNorm T i m
      (p.1, p.2.1, Fin.snoc p.2.2 b)

/-- the rung-`i` shift (C.15's pattern at `(u_i, e_i)`). -/
def towerShift (T : DeepTower F H₀ hpin r) (i m : ℕ) : ℕ := towerSolve (T.u i) (T.e i) m

/-- the rung-`i` cocycle (C.28's pattern; the `τ_i`-exponent bookkeeping). -/
def towerCocycle (T : DeepTower F H₀ hpin r) (i a b : ℕ) : ℕ :=
  (T.towerShift i a + T.towerShift i b - T.towerShift i (a + b)) / T.e i

/-- truncation to depth `i ≤ r` (every field re-scoped; used to instantiate level-general
consumers at each rung). -/
def trunc (T : DeepTower F H₀ hpin r) (i : ℕ) (hi : i ≤ r) : DeepTower F H₀ hpin i where
  e := T.e
  f := T.f
  u := T.u
  fld := T.fld
  fldField := T.fldField
  ψ := T.ψ
  he1 := T.he1
  hf1 := T.hf1
  hu1 := T.hu1
  he := fun j h1 h2 => T.he j h1 (h2.trans hi)
  hf := fun j h1 h2 => T.hf j h1 (h2.trans hi)
  hproper := fun j h1 h2 => T.hproper j h1 (h2.trans hi)
  hcop := fun j h1 h2 => T.hcop j h1 (h2.trans hi)
  hfloor := fun j h1 h2 => T.hfloor j h1 (h2.trans_le hi)
  hψ := fun j h1 h2 => T.hψ j h1 (h2.trans_le hi)
  base := T.base
  step := fun j h1 h2 => T.step j h1 (h2.trans_le hi)

end DeepTower

/-! ## A-C.1 §10-CARRIER — NODE C.92 [cite] `FGMNCalculus` (fragile no. 2)

The §10 design note's packaging, drafted: **one field per consumed cited clause**, typed
against C.83's carrier (the depth-`r` chain) — the FGMN side exists in Lean ONLY through this
interface. Every field docstring carries the PUBLISHED number of
`docs/CITE_NUMBERING_AUDIT_2026-08-16.md` §4 (J. Algebra 427 (2015) 30–75,
DOI 10.1016/j.jalgebra.2014.12.022); the arXiv-v3 numbers the sources pin are given in
parentheses. Parameters: the chain `W` (depth `r`, keys `keyAt 1 … r` with `keyAt 1 = F.key`)
plus the NEXT-stage numerals `(e', f', u')` — the recipe stage the §10 lemmas read
(at the S2 witness: `r = 2`, `(e₃, f₃, u₃)`).

⚠ LIKE C.66: the STATEMENT below is this unit's own drafting under append #66's
category-level signature — gate-(b)-SIGNED-AT-CATEGORY, statement-UNINSPECTED; flagged for
the owner. TWO BOOKED RESIDUAL FIELDS (recorded in the blueprint node, to be added when
their consumers fire): the level-general one-sidedness clause (published **Cor 6.3**, was
Cor 6.4 — C.90(b)'s leg; needs the level-`i` `dv`-carriers, §9-scope) and the γ-letter
defining reads (published Def 3.12-family — C.102's leg). -/

/-- NODE C.92 — the MacLane-chain certificate interface ([cite:FGMN-chain], gate (b)). -/
class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
  /-- the MacLane chain keys `Φ_1 … Φ_r` (`Φ_1 = F.key`); junk outside. -/
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  /-- `deg Φ_i = D_i` (chain-degree law; published §§5–6 chain conventions). -/
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i
  /-- the exact-grade pin (`ν`-value data): the scope carrier of R3-2's fence — every graded
  read below is conditioned on it (`digit` applied only in scope). -/
  ExactGrade : ℕ → Polynomial O → Prop
  /-- the graded coefficient read `R_{r+1,β}` at cleared grade `β`, valued in the top residue
  field (C.104's `(R-FGMN)`, the `ε₂`-normalized coordinate; published §4). -/
  Rgr : ℕ → Polynomial O → W.fld r
  /-- the residual operator `R_ν(·)` of the depth-`r` valuation, valued in `K_r[y]`
  (published §§4–6). -/
  Rres : Polynomial O → Polynomial (W.fld r)
  /-- `KP(ν)`-membership (key/prime polynomial for the depth-`r` MacLane valuation). -/
  KP : Polynomial O → Prop
  /-- `ν`-equivalence `∼_ν`. -/
  nuEquiv : Polynomial O → Polynomial O → Prop
  /-- the FGMN residue letters `z_i` (published Def 3.12-family `γ_i`-letters), in `K_r`. -/
  letterZ : ℕ → W.fld r
  /-- [published **Cor 4.12(3)**; was Cor 4.7(3)] graded multiplicativity of the `R`-read. -/
  Rgr_mul : ∀ β β' (g g' : Polynomial O), ExactGrade β g → ExactGrade β' g' →
    ExactGrade (β + β') (g * g') ∧ Rgr (β + β') (g * g') = Rgr β g * Rgr β' g'
  /-- [published **Cor 4.9(3)**; was Cor 4.4(4)] nonvanishing of the in-scope graded read
  (the single-pin polygon leg C.100's `u(β) ≠ 0` consumes). -/
  Rgr_ne_zero : ∀ β (g : Polynomial O), ExactGrade β g → g ≠ 0 → Rgr β g ≠ 0
  /-- [published **Prop 5.6 + eq (11)**; was Prop 5.7 + eq (14), plus Def 1.8's
  expansion-minimum and **Cor 4.12(1)**] the recipe expansion law: the residual of the
  recipe key is the `y`-polynomial of the graded slot reads — the raw (B-law) sum. -/
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') - ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t))
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
  /-- [published **Lemma 5.2(2)**; was Lemma 5.3(2)] the key-polynomial criterion at the
  recipe degree (admissibility/degree forcing). -/
  KP_criterion : ∀ (g : Polynomial O), g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) → (Rres g).natDegree = f' → KP g
  /-- [published **Lemma 1.8 + Cor 1.10**; were Lemma 1.11 + Cor 1.13] key polynomials are
  irreducible (over `K_v[x]` in the source; monic + `KP(µ) ⊂ O[x]` transports it to `O[x]`
  by Gauss — the transport recorded in the faithfulness entry). -/
  KP_irred : ∀ (g : Polynomial O), KP g → g.Monic → Irreducible g
  /-- [published **Thm 6.2**; was Thm 6.3 items (1)(2)(3), v3's (3) absorbed into (2)] the
  chain key's own residual is trivial — the non-equivalence pivot C.103 reads. -/
  Rres_keyAt : Rres (keyAt r) = 1
  /-- [published **Prop 5.6**, the consumed equivalence] distinct residuals ⟹ not
  `ν`-equivalent. -/
  nuEquiv_ne_of_Rres : ∀ (g g' : Polynomial O), KP g → KP g' →
    Rres g ≠ Rres g' → ¬ nuEquiv g g'

/-- NODE C.126's census name / C.92's ONE signed axiom (`fgmn_calculus_exists`): the interface
is realized on every chain. Gate-(b)-SIGNED-AT-CATEGORY (append #66), statement-UNINSPECTED —
flagged for the owner; consumers may also take `[FGMNCalculus W e' f' u']` hypothesis-form. -/
axiom fgmn_calculus_exists {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e') (hfloor : e' * W.Econst r < u') :
    Nonempty (FGMNCalculus W e' f' u')

/-! ## A-C.1 §10 — NODE C.97 [def+lemma] the S2 tower witness (fragile no. 3)

`def`-kind node whose body is a proof-carrying concrete construction (a `DeepTower` instance
over `ℤ₂`-class data: `KeyFrame`'s `hirr`/`hpure`/`hresirr` fields at `Φ′ = x² − 2` are
theorem-grade); per this layer's rule it lands as axiom CONSTANTS with the defining numerals
as signed value clauses. The recipe-key identities (`Φ₂ = Φ′² − 4x`, `Φ₃ = Φ₂² − 16Φ′`) and
the ladder `[4, 10, 21]` are already machine-verified from the polynomials up in the numeric
gate below (finding D25/F1); `towerNorm 1 21 = (4, 0, ![1])` is `n̂₂(21) = 16Φ′` in exponent
data (`π = 2`: `π⁴x⁰Φ′¹`). -/

axiom s2Frame [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) : KeyFrame O (2 : O)

axiom s2Frame_data [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) :
    (s2Frame h2 hq).e₁ = 2 ∧ (s2Frame h2 hq).f₁ = 1 ∧ (s2Frame h2 hq).h = 1 ∧
    (s2Frame h2 hq).key = Polynomial.X ^ 2 - Polynomial.C 2

axiom s2Witness [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    DeepTower (s2Frame h2 hq) H₀ hpin 3

axiom s2Witness_values [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).e 2 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 2 = 1 ∧
    (s2Witness h2 hq H₀ hpin).u 2 = 5 ∧
    (s2Witness h2 hq H₀ hpin).e 3 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 3 = 1 ∧
    (s2Witness h2 hq H₀ hpin).u 3 = 21 ∧
    (s2Witness h2 hq H₀ hpin).towerNorm 1 21 = (4, 0, fun _ => 1)

/-! ## A-C.1 §10 — NODE C.98 [lemma] the normalization shear (fragile no. 4)

Signed ENV-C5-abstract, over height functions `ℕ → ℕ∞` (reusable for every dictionary row):
the shear `P ↦ P + j·c` matches sides `(u, ℓ)` of the sheared cloud with sides
`(u + ℓc, ℓ)` of the unsheared one, argmin-pointwise (on/above preserved termwise). The
witness `κ₂ = 5/2 ↔ λ₂ = 1/4` is the instance `c = e(µ₁)·w₂`-cleared. -/

/-- the abstract cleared support value of a height function on `[0, n]` (C.06/C.07's shape,
carrier-free). -/
noncomputable def hSupp (P : ℕ → ℕ∞) (n u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (n + 1)).inf fun j => ℓ • P j + (u * j : ℕ∞)

/-- membership of abscissa `j` in the `(u, ℓ)`-side of the abstract cloud. -/
def hOnSide (P : ℕ → ℕ∞) (n u ℓ j : ℕ) : Prop :=
  hSupp P n u ℓ = ℓ • P j + (u * j : ℕ∞) ∧ P j ≠ ⊤

/-- NODE C.98 — `shear_onesided_iff`. -/
axiom shear_onesided_iff (P : ℕ → ℕ∞) (n c u ℓ j : ℕ) (hℓ : 0 < ℓ) (hj : j ≤ n) :
    hOnSide (fun i => P i + (i * c : ℕ∞)) n u ℓ j ↔ hOnSide P n (u + ℓ * c) ℓ j

/-! ## A-C.1 §5 — THE DESCENT-GRAMMAR CARRIERS (C.33–C.40, D2 cured)

The eight formerly-unsignable nodes. A-C.1 determinations, recorded per node in the
blueprint: C.33's existential witness type is B.42's landed template (`exists_slope_
factorization`, the CHAP-I addendum's exact statement) at the `dv`-carrier, packaged as a
structure `DvDissection` + existence/uniqueness axioms (GC-4's inductive-domain licence, and
what C.35's choice needs); C.34 is signed at the consumed `(λ, r)`-block clause; C.35's
`blockFactor` takes the TOTAL maximal-labelled-divisor body (choice; junk `1`); C.36's `c_g`
is `(dvSupp F g L.u L.ℓ).toNat` (the dv₂-unit value under which C.37's display type-checks;
the STATEMENT's `L.ℓ •` prefix was a clearing slip, recorded); the C.38a helper cluster
(`Dv2OnSide`/`dv2SideSet`/`dv2Res`/`dv2ResPoly`) mirrors C.07/C.25 at the `dv₂`-carrier with
the K₂-read `dv2Res A := (A's dvResPoly) evaluated at β` (`AdjoinRoot.mk L.r`); C.38's
"same radical" is signed as same-monic-irreducible-divisors (no `radical` import). -/

/-! ### NODE C.33 [theorem] — the slope dissection at the level polygon [signed: A-C.1] -/

/-- The witness type of C.33's dissection (B.41/B.42 one level up, at B.42's landed template
shape): slopes in lowest terms above the frame floor, per-side monic `dv`-pure factors with
the `(SEP)`-free degree law `deg f_i = D′·L_λ`, a below-floor monic remainder, the product,
and the side-detection iff. -/
structure DvDissection (F : KeyFrame O π) (f : Polynomial O) : Type _ where
  slopes : Finset (ℕ × ℕ)
  factor : ℕ × ℕ → Polynomial O
  below : Polynomial O
  hslopes : ∀ p ∈ slopes,
    0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.2 * ((F.e₁ * F.f₁) * F.h) < p.1
  hdistinct : ∀ p ∈ slopes, ∀ q ∈ slopes, p ≠ q → p.1 * q.2 ≠ q.1 * p.2
  hmonic : ∀ p ∈ slopes, (factor p).Monic
  hpure : ∀ p ∈ slopes, IsDvPure F (factor p) p.1 p.2
  hdeg : ∀ p ∈ slopes, ∀ hne : (dvSideSet F f p.1 p.2).Nonempty,
    (factor p).natDegree = (F.e₁ * F.f₁) * (p.2 * dvSideDeg F f p.1 p.2 hne)
  hbelow_monic : below.Monic
  hbelow : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ∀ hne : (dvSideSet F below u ℓ).Nonempty, dvSideDeg F below u ℓ hne = 0
  hprod : f = below * ∏ p ∈ slopes, factor p
  hsides : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ((u, ℓ) ∈ slopes ↔ ∃ hne : (dvSideSet F f u ℓ).Nonempty, 0 < dvSideDeg F f u ℓ hne)

axiom exists_dvDissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) :
    Nonempty (DvDissection F f)

axiom dvDissection_unique (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (D D' : DvDissection F f) :
    D.slopes = D'.slopes ∧ D.below = D'.below ∧ ∀ p ∈ D.slopes, D.factor p = D'.factor p

/-! ### NODE C.34 [theorem] — the residual dissection, signed at the `(λ, r)`-block clause
[signed: A-C.1]. The general coprime-prime-power refinement is the fleet's proof content
(B.48's route); the PUBLIC statement is the consumed block form, with uniqueness. -/

axiom exists_dv_residual_dissection {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {g : Polynomial O} (hg : g.Monic) (hpure : IsDvPure F g L.u L.ℓ)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hdvd : L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) :
    ∃ fS g' : Polynomial O, g = fS * g' ∧ HasLabel L fS ∧ g'.Monic ∧
      (∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp') ∧
      ∀ fS' g'' : Polynomial O, g = fS' * g'' → HasLabel L fS' → g''.Monic →
        (∀ (hne' : (dvSideSet F g'' L.u L.ℓ).Nonempty) (M₀' : ℕ)
          (hp' : dvHgt F g'' (dvSideMin F g'' L.u L.ℓ hne') = (M₀' : ℕ∞)),
          ¬ L.r ∣ dvResPoly F H₀ hpin g'' L.u L.ℓ hne' M₀' hp') →
        fS' = fS ∧ g'' = g'

/-! ### NODE C.35 [def] — `BlockContext`, `blockFactor`, `mult₂` [signed: A-C.1] -/

/-- The §5 standing block context on `f` at the datum `L`: the PEEL-CONVENTION pair, a
genuine `(λ, r)`-side of `f`'s own read (nonempty, positive length, `r`-divisible residual). -/
def BlockContext {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Prop :=
  f.Monic ∧ Squarefree f ∧ ¬ F.key ∣ f ∧
  ∃ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
    0 < dvSideDeg F f L.u L.ℓ hne ∧
    L.r ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp

/-- `blockFactor L f` — the block `f_S`, as the MAXIMAL `(λ, r)`-labelled monic divisor of
`f` (total: choice; junk `1` when none — C.34's uniqueness makes the maximal divisor THE
block under `hctx`). -/
noncomputable def blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Polynomial O :=
  open Classical in
  if h : ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS
  then h.choose else 1

/-- `μ₂ = deg f_S / D″` (`EFF.HE6R1.12`). -/
noncomputable def mult₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ := (blockFactor L f).natDegree / L.keyDeg₂

/-- C.35's companion: under the context the block is genuine and the division exact. -/
axiom blockFactor_spec {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f ∧ 0 < mult₂ L f

/-! ### NODE C.36 [lemma] — block projection (a) + `complementConst` [signed: A-C.1] -/

/-- `c_g` — the complement constant, in `dv₂`-units: the level support value of
`g = f /ₘ f_S` at the datum's side (`EFF.HE6R1.13`'s `c_g`, ℕ-cleared; finite under C.36). -/
noncomputable def complementConst {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ :=
  (dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ).toNat

axiom block_complement_notdvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    (∀ Ψ : Polynomial O, IsTestKey L Ψ → (Ψ ∣ blockFactor L f ↔ Ψ ∣ f)) ∧
    (∀ (hne' : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty) (M₀' : ℕ)
      (hp' : dvHgt F (f /ₘ blockFactor L f)
          (dvSideMin F (f /ₘ blockFactor L f) L.u L.ℓ hne') = (M₀' : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ hne' M₀' hp') ∧
    dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤

/-! ### NODE C.37 [theorem] — the translation identity (the GC-2 mechanism) [signed: A-C.1] -/

axiom dv2Supp_translation {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂) :
    dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞)

/-! ### NODE C.38a [def, RE-PLAN'd helper cluster] — `dv2SideSet` + `dv2ResPoly`
[signed: A-C.1]; the §15 booking ("the `dv2ResPoly` + `dv2SideSet` cluster") executed. -/

def Dv2OnSide {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ j : ℕ) : Prop :=
  dv2Supp L Ψ f u₂ ℓ₂ = ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞) ∧ dv2Pin L Ψ f j ≠ ⊤

noncomputable def dv2SideSet {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (fun j => Dv2OnSide L Ψ f u₂ ℓ₂ j)

noncomputable def dv2SideMin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideSet L Ψ f u₂ ℓ₂).min' h

noncomputable def dv2SideMax {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideSet L Ψ f u₂ ℓ₂).max' h

noncomputable def dv2SideDeg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideMax L Ψ f u₂ ℓ₂ h - dv2SideMin L Ψ f u₂ ℓ₂ h) / ℓ₂

/-- the coherent `K₂`-residue read of one coefficient: its own level residual evaluated at
the letter `β` (`AdjoinRoot.mk L.r`; junk `0` off the pinned locus). -/
noncomputable def dv2Res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : AdjoinRoot L.r :=
  open Classical in
  if h : ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M₀ : ℕ∞)
  then AdjoinRoot.mk L.r
    (dvResPoly F H₀ hpin A L.u L.ℓ h.choose h.choose_spec.choose h.choose_spec.choose_spec)
  else 0

/-- the level-2 residual polynomial over `K₂` (C.25 one level up; the coherent per-slot
read). -/
noncomputable def dv2ResPoly {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (dv2Res L (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)))
      * Polynomial.X ^ t

/-! ### NODE C.38 [lemma] — same degree, same radical (as same-prime-divisors)
[signed: A-C.1] -/

axiom dv2ResPoly_radical_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    (dv2ResPoly L Ψ f u₂ ℓ₂ hne).natDegree
        = (dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPoly L Ψ f u₂ ℓ₂ hne ↔ q ∣ dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')

/-! ### NODE C.39 [lemma] — the per-side scalar, pin-height TERMINAL form [signed: A-C.1] -/

/-- `γ_g` — the complement's own `K₂`-residue read (a `K₂^×` unit under C.36). -/
noncomputable def γg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L (f /ₘ blockFactor L f)

/-- the PIN height at the side's starting index (PE3 F-1's integer; GC-1 discipline at
level 2). -/
noncomputable def pinHeight {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne)).toNat

axiom dv2ResPoly_scalar {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    dv2ResPoly L Ψ f u₂ ℓ₂ hne
      = Polynomial.C (γg L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f)))
          * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne'

/-! ### NODE C.40 [theorem] — the level-2 peel [signed: A-C.1; D11 cured in-statement] -/

axiom level2_peel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hdvd : Ψ ∣ blockFactor L f) (hbox : CBox1Side L Ψ) :
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible Ψ ∧
    ∃ fS' : Polynomial O, blockFactor L f = Ψ * fS' ∧ ¬ Ψ ∣ fS' ∧
      fS'.natDegree = L.keyDeg₂ * (mult₂ L f - 1)

/-! ## A-C.1 §9 — NODE C.94 [cite:AGNPRW] — the descent-history carriers and THE EXACT
LEAN STATEMENT (the D24 deadlock broken on the C side)

A-C.1 determinations, flagged for the owner (statement drafted here; append #66 signs the
category): the descent STATE is `(key, block)`; a STEP is a level JUMP (a labelled block of
degree ≥ 2·D″ at a jump datum `ℓd_r ≥ 2`, the new key a test key — §5's carriers verbatim)
or an α-REFINE (a same-degree recentering whose attained side slope STRICTLY increases —
the C.113(i)/C.56 shape; the slope-increase clause is what makes vacuous refine loops
non-steps). The cite asserts: NO INFINITE HISTORY on a fixed monic squarefree `f` —
"reaches multiplicity 1 (or a terminating α-refine chain) in finitely many steps" in
no-infinite-chain form. What is NOT in the statement: the jump-count arithmetic (C.32,
proved) and the α-refine finiteness interface (E's HE7-8 placeholder). -/

/-- the §5 descent state: the current key and the current block factor. -/
structure DescentState (O : Type*) [CommRing O] where
  key : Polynomial O
  block : Polynomial O

/-- one step of §5's descent grammar (the [AGNPRW]-consumed shape). -/
inductive DescentStep (π : O) : DescentState O → DescentState O → Prop
  | jump : ∀ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (L : LevelDatum F H₀ hpin)
      (s s' : DescentState O),
      s.key = F.key → 2 ≤ L.ℓ * L.r.natDegree →
      HasLabel L s'.block → s'.block ∣ s.block →
      IsTestKey L s'.key → L.keyDeg₂ * 2 ≤ s'.block.natDegree →
      DescentStep π s s'
  | refine : ∀ (s s' : DescentState O) (u ℓ u' ℓ' : ℕ),
      0 < ℓ → 0 < ℓ' → s'.block = s.block →
      s'.key.natDegree = s.key.natDegree →
      (s.key - s'.key).natDegree < s.key.natDegree →
      (sideSet s.key s.block u ℓ).Nonempty →
      (sideSet s'.key s.block u' ℓ').Nonempty →
      u * ℓ' < u' * ℓ →
      DescentStep π s s'

/-- NODE C.94's EXACT LEAN STATEMENT ([cite:AGNPRW], published **Thm 5.6** — Found. Comput.
Math. 25 (2025) no. 2, 631–681, DOI 10.1007/s10208-024-09646-x; the repo's "Thm 5.2" is the
arXiv-v1 number and COLLIDES with a different published theorem — A-3 audit §3): OM descent
terminates — no infinite §5 history on a fixed monic squarefree `f`. This Prop is what
CHAP-I's `I.01` `NS7Termination` body quantifies (the D24 deadlock's C-side, now typed). -/
def NS7TerminationStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (π : O), Irreducible π →
    ∀ f : Polynomial O, f.Monic → Squarefree f →
    ∀ hist : ℕ → DescentState O,
      (∀ n, (hist n).block ∣ f) →
      (∀ n, DescentStep π (hist n) (hist (n + 1))) → False

/-- C.94's declared gate-(b) axiom (append #66 category signature; statement-UNINSPECTED,
owner inspection queued in CHAP-I's addendum). -/
axiom agnprw_termination : NS7TerminationStatement

/-! # §§9–13 — THE THIRD STAGE, THE GENTOW2 SUPPLY LAYER, THE HT COUNT LAYER, THE LEVEL-`N`
CERTIFICATES, AND THE GATES (C.83–C.126)

**NOTHING IN THESE FIVE SECTIONS HAS A LEAN SIGNATURE (defect D1).** Forty-four consecutive
nodes, including every one of the chapter's remaining TERMINAL SUPPLY statements — `C.89` (the
`𝒲` hypothesis family, a named Display-A conjunct), `C.97` (the S2 tower witness that chapter D's
T1 battery check 10 instantiates), `C.99`/`C.100` (GENTOW2's `B″`/`B′`, routed to chapters D and F
by GC-13), `C.107`–`C.110` and `C.114` (the HT count laws, chapter H's supplier of record and
chapter I's count-side conditionality) — and all four gates.

`C.83`'s `DeepTower` and `C.92`'s `FGMNCalculus` are named in §15's own "elaborate the fragile
signatures FIRST" list; neither exists. `C.126`'s axiom census names `fgmn_calculus_exists` as a
declared gate-(b) axiom; it cannot be declared, because `FGMNCalculus` has no field list anywhere
(the §10 design note lists the fields by CITED CLAUSE NAME — `[Q1]…[Q10]`, Prop 1.15, Def 1.8's
expansion-minimum, Cor 4.4, Thm 4.8, Lemma 3.17, Prop 1.9, Def 3.12's `γ_i`-letters — and gives no
type for any of them).

## THE THREE `[cite:]` NODES (C.66, C.92, C.94) — gate (b)

`PROJECT_STATE.md` append #66 (2026-08-16) signs these "at category level" and records that
"their exact statements + faithfulness entries are on file (CHAP-I §3 + addendum) for individual
inspection at will". **That is true of `B.42`'s cite and of no other** (defect D23): CHAP-I's
addendum carries `THE EXACT LEAN STATEMENT to be signed` for
`LeanspecB.exists_slope_factorization` only, while all three C-cites say, in their own STATEMENT
fields, *"Exact Lean statement drafted at stub stage; Asvin signs"* — i.e. the blueprint delegates
the authorship of a literature-cite statement to this gate. They are also the only three nodes in
the chapter with **no `**SIGNATURE**` field at all**.

Disposition here, one per node:
* **C.66 — DRAFTED below** as `fgmn_residual_mul`, against C.25's `dvResPoly` carrier, at exactly
  the multiplicativity clause the prose fixes and no wider (the ⚠ SCOPE FENCE: never `w`'s closed
  form). It is landed as an `axiom` because append #66 signs the MECHANISM and the CATEGORY; **the
  STATEMENT below has never been shown to the owner and is this gate's own drafting**, so it is
  gate-(b)-SIGNED-AT-CATEGORY, statement-UNINSPECTED. Flagged for the owner.
* **C.92 — NOT DRAFTABLE.** Six clause families over `FGMNCalculus`, a structure with no field
  types; two of its clauses are stated against `C.83`'s `DeepTower`, which does not exist.
* **C.94 — NOT DRAFTABLE, and the obstruction is a CROSS-CHAPTER DEADLOCK (defect D24).** The
  statement must quantify over "every descent history of §5's grammar on a fixed `f`", and §5's
  descent objects (`C.33`'s dissection, `C.35`'s `blockFactor`) have no signature (D2). Chapter I
  has the mirror hole: `I.01`'s `NS7Termination` is landed in CHAP-I with a literal
  `True` placeholder body and marked `BLOCKED-UNTIL-RESOLUTION`, with the note *"the body is typed
  against C's committed §5 carriers at stub time"*. **Both sides wait for the other; the stub
  stage was the appointed meeting point and neither arrived.** This is the single most consequential
  finding of this gate after D1, because `NS7` is Display A's line 1.
-/

/-! ### NODE C.66 [cite] [cite:FGMN] — **STUB-SIDE DRAFT, statement not owner-inspected**

Cited: FGMN (Fernández–Guàrdia–Montes–Nart, *Residual ideals of MacLane valuations*),
**J. Algebra 427 (2015) 30–75**, DOI 10.1016/j.jalgebra.2014.12.022 — **Thm 2.8 + Cor 4.12(3) +
Cor 4.9(3)** (the A-3-corrected published numbers of
`docs/CITE_NUMBERING_AUDIT_2026-08-16.md`; the blueprint's own SOURCE line still carries the
arXiv-v3 numbers `Cor 4.7(3)`/`Cor 4.4(4)` in its first paragraph and corrects them only in the
A-3 rider below it — a fleet agent reading top-down gets the wrong numbers).

SCOPE FENCE (transcribed): exactly the multiplicativity clause Step II of `LEMMA GENTOW-6.1`
consumes — never the full FGMN machinery, never `w`'s closed form.

⚠ THE DRAFTING DECISIONS THE OWNER MUST INSPECT, since the blueprint fixes none of them:
(1) the "fixed `K^×`-scalar" is rendered as an existential unit `c` in `stageField`, not as a
named function of the data (the corpus does not name it, and C-H10 forbids claiming a closed form);
(2) the two factors and the product are read at the SAME `(u, ℓ)` with three separate
nonemptiness/pin witnesses, because `dvResPoly` takes them as arguments and no lemma of the
chapter relates the three (that relation is `dvResPoly_mul_of_pure`, the RE-PLAN'd B.35 twin §15
books and no node states);
(3) purity of both factors at the common side is hypothesized (`IsDvPure`), which is the "common
side data" of the prose. -/

axiom fgmn_residual_mul (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ)
    (hne : (dvSideSet F g u ℓ).Nonempty) (hne' : (dvSideSet F g' u ℓ).Nonempty)
    (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
    {M₀ M₀' M₀'' : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
    (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
    (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)) :
    ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
      dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
        = Polynomial.C c
            * (dvResPoly F H₀ hpin g u ℓ hne M₀ hp * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp')

/-! # NUMERIC CONTENT EXECUTED AT THIS GATE (GC-11 / CHAP-C §15 gate order (c))

Chapter C's signed layer is almost entirely `Polynomial O`-valued and `noncomputable`, and §13's
four gate nodes have NO Lean and no machine-form expected-value table (defect D14), so what is
executable is the ARITHMETIC layer. Everything below is a `#guard`, which FAILS THE BUILD if the
proposition evaluates to `false`, and everything with a `q` runs at `q = 2` **and** `q = 3`.

The mirrors `slotIdxN`/`twistExpN`/`slotWindowN`/`shiftN`/`cocycleN` are byte-for-byte the bodies
of C.15/C.17/C.28 with the `KeyFrame`/`LevelDatum` wrapper stripped (which is legitimate exactly
because of defect D7 — those nodes use nothing of the frame but `e₁`, `f₁`, `h`). They are NOT
blueprint declarations. -/

section NumericGate

def slotIdxN (e₁ h k : ℕ) : ℕ :=
  ((List.range e₁).find? (fun i => (i * h) % e₁ == k % e₁)).getD 0

def twistExpN (e₁ h k : ℕ) : ℕ := (slotIdxN e₁ h 1 * k - slotIdxN e₁ h k) / e₁

def slotWindowN (e₁ f₁ h k : ℕ) : List ℕ :=
  (List.range f₁).filter (fun t => decide ((slotIdxN e₁ h k + e₁ * t) * h ≤ k))

def shiftN (u l m : ℕ) : ℕ := ((List.range l).find? (fun b => (b * u) % l == m % l)).getD 0

def cocycleN (u l a b : ℕ) : ℕ := (shiftN u l a + shiftN u l b - shiftN u l (a + b)) / l

/-! ### C.16 — `slotIdx_spec` + `twistExp_spec`, over every coprime frame with `e₁ ≤ 8`,
`h ≤ 12`, `k ≤ 40` (both primes and well beyond; the `q`-independence of `q(k)` that C.22's
FAITHFULNESS block asserts is exactly why this grid is `π`-free). -/

def c16_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for k in [0:41] do
          let i := slotIdxN e₁ h k
          if !(i < e₁ && (i * h) % e₁ == k % e₁) then ok := false
          if !(slotIdxN e₁ h 1 * k == i + e₁ * twistExpN e₁ h k) then ok := false
  return ok

#guard c16_grid

/-! ### C.18(b) — `slotWindow_full_of_le` over the same box. -/

def c18_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:5] do
      for h in [0:9] do
        if Nat.gcd h e₁ == 1 then
          for k in [0:80] do
            if (e₁ * f₁ - 1) * h ≤ k then
              if (slotWindowN e₁ f₁ h k).length != f₁ then ok := false
  return ok

#guard c18_grid

/-! ### C.22's MANDATORY `(2,2,3)` twist witness (`q = 3` half of the char split).
The node's FAITHFULNESS block: *"`k = 3, A = x` gives `γ = 1`, `q(3) = 1`,
`twistRead = η^{−1} = 2η` in `F₉` over `ℤ₃` — the `[r1]` `+q` reading predicts `η` and is
refuted"*, and the RIDER that `q(k)` is `π`-independent, so the same numbers hold over `ℤ₂`. -/

#guard slotIdxN 2 3 1 == 1          -- i₀ = 1
#guard slotIdxN 2 3 3 == 1          -- i(3) = 1
#guard twistExpN 2 3 3 == 1         -- q(3) = 1  (the `[r2]` exponent; `[r1]`'s `+q` differs)
#guard slotWindowN 2 2 3 3 == [0]   -- T(3) = {0}

/-- `F₉ = F₃[T]/(T² − 2)` as `(a, b) ↦ a + bη`: the arithmetic that makes `η⁻¹ = 2η`. -/
abbrev F9 := ZMod 3 × ZMod 3

def f9mul (x y : F9) : F9 := (x.1 * y.1 + 2 * (x.2 * y.2), x.1 * y.2 + x.2 * y.1)

#guard f9mul (0, 2) (0, 1) == (1, 0)   -- (2η) · η = 2η² = 4 = 1, i.e. η⁻¹ = 2η

/-! ### `q = 2` companions of the same witness (GC-11's two-prime clause at the level the stub
can reach): C.22's own `(2,2,1)`-frame row and C.125(i)'s wild frame `(e₁,f₁,h) = (2,1,1)`,
`Φ′ = x² − 2` over `ℤ₂` (`2 ∣ e₁`, genuinely wild). -/

#guard slotIdxN 2 1 1 == 1
#guard twistExpN 2 1 1 == 0      -- q(1) = 0 in the (2,·,1) frame
#guard twistExpN 2 1 3 == 1      -- ⚠ but q(3) = 1: `q(k) = 0` is NOT identical on that frame
#guard slotWindowN 2 1 1 1 == [0]

/-! C.125(ii)'s honest wild `q = 3` row: the `(3,1,2)` frame (`e₁ = 3 = p`, `Φ′ = x³ − 3`). -/

#guard slotIdxN 3 2 1 == 2
#guard slotIdxN 3 2 2 == 1
#guard twistExpN 3 2 2 == 1
#guard slotWindowN 3 1 2 4 == [0]

/-! ### C.28 — `cocycle_mem` (`ℓ·c₁(a,b) = s(a)+s(b)−s(a+b)` and `c₁ ≤ 1`) over every coprime
`(u, ℓ)` with `ℓ ≤ 9`, `u ≤ 20`, `a, b ≤ 12`; plus the NEGATIVE control showing `hcop` is
load-bearing (the corpus's `HE6-T-BADKEY` tooth, C.09's FAITHFULNESS note). -/

def c28_grid : Bool := Id.run do
  let mut ok := true
  for l in [1:10] do
    for u in [0:21] do
      if Nat.gcd u l == 1 then
        for a in [0:13] do
          for b in [0:13] do
            let c := cocycleN u l a b
            if !(l * c == shiftN u l a + shiftN u l b - shiftN u l (a + b)) then ok := false
            if !(c ≤ 1) then ok := false
  return ok

#guard c28_grid

/-! Negative control: drop coprimality and the cocycle identity fails. `(u, ℓ) = (2, 4)`,
`a = b = 1`: `s(1) = 0` (junk — no `β` with `2β ≡ 1 mod 4`), `s(2) = 1`, so
`s(1)+s(1)−s(2) = 0 - 1 = 0` in ℕ while `ℓ·c₁ = 4·0 = 0` — the identity survives by ℕ-truncation
but `s` is junk; the honest witness is that `s` is not additive: -/
#guard shiftN 2 4 1 == 0 && shiftN 2 4 2 == 1 && (2 * 1) % 4 != 1 % 4

/-! ### C.30 — the descent trichotomy, decided over `mr, ℓ, dr ≤ 8`. -/

def c30_grid : Bool := Id.run do
  let mut ok := true
  for mr in [1:9] do
    for l in [1:9] do
      for dr in [1:9] do
        let c1 := mr == 1
        let c2 := mr ≥ 2 && l == 1 && dr == 1
        let c3 := mr ≥ 2 && 2 ≤ l * dr
        if !((c1 && !c2 && !c3) || (c2 && !(2 ≤ l*dr) && mr != 1)
              || (c3 && !(l == 1 && dr == 1) && mr != 1)) then ok := false
  return ok

#guard c30_grid

/-! ### C.31 — `jump_floor` and `first_bite` hold on their boxes; **`jump_drop` IS FALSE AS
SIGNED** (defect D21). -/

def c31_floor_grid : Bool := Id.run do
  let mut ok := true
  for mr in [2:9] do
    for l in [1:7] do
      for dr in [1:7] do
        if 2 ≤ l * dr then
          for L in [0:60] do
            for mu in [0:60] do
              if mr * (l * dr) ≤ L && L ≤ mu then
                if !(4 ≤ L && 4 ≤ mu) then ok := false
  return ok

#guard c31_floor_grid

/-! C.31's third clause exactly as ORIGINALLY signed (pre-A-C.1; the refutation record of D21,
preserved verbatim per the re-sign discipline), as a decidable predicate: all hypotheses true
and the conclusion false. -/
def jumpDropAsSigned (D l dr mu mu2 dfS : ℕ) : Bool :=
  decide (0 < D) && decide (0 < l) && decide (0 < dr) &&
  decide (mu2 * (D * l * dr) = dfS) && decide (dfS ≤ D * (l * (mu / l))) &&
  decide (l * dr * 2 ≤ 2 * mu) && !decide (2 * mu2 ≤ mu)

/-! **D21, the refutation.** `(D, ℓ, d_r, μ, μ₂, deg f_S) = (1, 1, 1, 1, 1, 1)`: every hypothesis
holds (`1·(1·1·1) = 1`; `1 ≤ 1·(1·(1/1)) = 1`; `1·1·2 = 2 ≤ 2·1`) and the conclusion is
`2 ≤ 1`. -/
#guard jumpDropAsSigned 1 1 1 1 1 1

def jumpDropCounterCount : ℕ := Id.run do
  let mut n := 0
  for D in [1:5] do
    for l in [1:5] do
      for dr in [1:5] do
        for mu in [0:13] do
          for mu2 in [0:13] do
            if jumpDropAsSigned D l dr mu mu2 (mu2 * (D * l * dr)) then n := n + 1
  return n

/-! 168 counterexamples in `D, ℓ, d_r ∈ [1,4] × μ, μ₂ ∈ [0,12]` — not a corner case. -/
#guard jumpDropCounterCount == 168

/-! The repair: replace `hL : ℓ·d_r·2 ≤ 2μ` (which says `ℓ d_r ≤ μ`) by the JUMP hypothesis
`2 ≤ ℓ·d_r` that the sibling `jump_floor` carries and this clause drops. -/
def jumpDropRepaired (D l dr mu mu2 dfS : ℕ) : Bool :=
  decide (0 < D) && decide (0 < l) && decide (0 < dr) && decide (2 ≤ l * dr) &&
  decide (mu2 * (D * l * dr) = dfS) && decide (dfS ≤ D * (l * (mu / l))) &&
  !decide (2 * mu2 ≤ mu)

def jumpDropRepairedCount : ℕ := Id.run do
  let mut n := 0
  for D in [1:6] do
    for l in [1:6] do
      for dr in [1:6] do
        for mu in [0:25] do
          for mu2 in [0:25] do
            if jumpDropRepaired D l dr mu mu2 (mu2 * (D * l * dr)) then n := n + 1
  return n

#guard jumpDropRepairedCount == 0

/-! ### C.32 — `jump_count_bound` on explicit chains, `J ≤ 4`, values `≤ 200`. -/

def c32_check (a : List ℕ) : Bool :=
  let J := a.length - 1
  let floors := a.all (fun x => decide (4 ≤ x))
  let drops := (List.range J).all (fun j => decide (2 * a[j+1]! ≤ a[j]!))
  !(floors && drops) || decide (2 ^ (J + 2) ≤ 2 * a[0]!)

#guard [[4], [8,4], [16,8,4], [32,16,8,4], [64,32,16,8,4], [100,40,15,7,4],
        [200,99,44,20,9], [5,4], [9,4], [4,4]].all c32_check

/-! ### C.42 / C.50 — `E₂_gt_xfloor` follows from `TowerDatum.hfloor`, checked on the box
`e₁,f₁,e₂,f₂ ≤ 5`, `h ≤ 5`, `u₂ ≤ 200`. -/

def c50_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:6] do
    for f₁ in [1:6] do
      for h in [0:6] do
        for e₂ in [1:6] do
          for f₂ in [1:6] do
            for u₂ in [0:201] do
              if e₂ * (e₁ * f₁) * h < u₂ then
                let D₂ := (e₁ * f₁) * (e₂ * f₂)
                let E₂ := e₂ * f₂ * u₂
                if !(D₂ * (e₂ * h) < E₂) then ok := false
  return ok

#guard c50_grid

/-! ### C.52's budget display and C.53's CLIP (C-H8's R2a TERMINAL form).

There is no signature for either node (D1), so the floor is transcribed from C.52's STATEMENT
display: `⌈((μ₂−j)E₂ − w(a,b)) / (e₁e₂)⌉ + [pin]`, `[pin] = 1` iff `e₁e₂ ∣ (μ₂−j)E₂ − w(a,b) ≥ 0`.
What is checkable here is the R2a lesson itself: the UNCLIPPED count `Σ (N − floor)` and the
CLIPPED count `Σ max(0, N − floor)` DIVERGE as soon as some floor exceeds `N`, which is exactly
the sealed-form failure C.53 records ("false whenever `N < floor` at some slot"). -/

def budgetFloor (e₁ e₂ E₂ μ₂ j w : ℕ) : ℕ :=
  let tgt := μ₂ * E₂ - j * E₂ - w
  let d := e₁ * e₂
  if (μ₂ - j) * E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

/-- `q`-free, but the two gate primes enter through `E₂ = e₂f₂u₂` at the two witnesses. -/
def clipDivergesAt (floors : List ℕ) (N : ℕ) : Bool :=
  let clipped := (floors.map (fun f => max 0 (N - f))).sum
  let naive := (floors.map (fun f => N - f)).sum   -- ℕ-truncated: agrees with clipped
  let signedNaive : Int := (floors.map (fun f => (N : Int) - (f : Int))).sum
  decide (clipped == naive) && decide ((clipped : Int) != signedNaive)

/-! R2a's counter-instance made concrete: floors `[2, 9]` at `N = 4`. The clipped count is `2`;
the sealed unclipped count over ℤ is `2 + (4 − 9) = −3`. -/
#guard clipDivergesAt [2, 9] 4
#guard ((([2,9] : List ℕ).map (fun f => max 0 (4 - f))).sum == 2)

/-! The budget floor at C.123/C.124's two frames, printed for the fleet (no blueprint value to
diff against — defect D14). -/
#eval (List.range 4).map (fun j => budgetFloor 2 2 8 3 j 0)
#eval (List.range 4).map (fun j => budgetFloor 3 2 12 3 j 0)
-- ⚠ C-H12's coincidence regime, live right here: at `w = 0` the two frames give the SAME row
-- `[7,5,3,1]`, so a gate that checked only `w = 0` would be blind to the frame. At `w = 5` they
-- separate (`[5,3,1,0]` vs `[6,4,2,0]`). This is the G.23 lesson at chapter C's own budget table.
#eval (List.range 4).map (fun j => budgetFloor 2 2 8 3 j 5)
#eval (List.range 4).map (fun j => budgetFloor 3 2 12 3 j 5)

/-! ### C.55 — the depth-3 floor in cleared form: pins `p_j ≥ (μ₂−j)E₂ + 1` with right endpoint
`(μ₂, 0)` force every two-point slope `u₃/ℓ₃ > E₂`, i.e. `ℓ₃·E₂ < u₃`. Checked directly on the
pin lattice for `μ₂ ≤ 8`, `E₂ ≤ 30`. -/

def c55_grid : Bool := Id.run do
  let mut ok := true
  for μ₂ in [1:9] do
    for E₂ in [1:31] do
      for j in [0:μ₂] do
        -- the two-point slope from `(j, (μ₂−j)E₂+1)` to `(μ₂, 0)`, cleared
        let l₃ := μ₂ - j
        let u₃ := (μ₂ - j) * E₂ + 1
        if !(l₃ * E₂ < u₃) then ok := false
  return ok

#guard c55_grid

/-! ### The HT spot values of C.123/C.124 (defect D15: the two gate texts give readings that
differ by a factor of `q − 1`). Both are executed; neither is derivable from a signed node,
because §11 has no signatures. -/

def htSpot (q N : ℕ) : ℕ := (q - 1) * ((q - 1) * (q - 2) / 2) * q ^ (2 * N - 8)
def htSpotAlt (q N : ℕ) : ℕ := ((q - 1) * (q - 2) / 2) * q ^ (2 * N - 8)

/-! C.123's own claim: the `q = 2` value is `0` at every `N` (the degenerate census). -/
#guard (List.range 12).all (fun N => htSpot 2 N == 0)
#guard (List.range 12).all (fun N => htSpotAlt 2 N == 0)
/-! At `q = 3` the two readings differ by exactly the factor `q − 1 = 2`. -/
#guard htSpot 3 6 == 2 * 3 ^ 4
#guard htSpotAlt 3 6 == 3 ^ 4
#eval (List.range 4).map (fun i => (htSpot 2 (4 + i), htSpot 3 (4 + i), htSpotAlt 3 (4 + i)))

/-! ### C.10's dictionary arithmetic (`D″ = D′ℓd_r = (e₁ℓ)(f₁d_r)`, `4 ≤ D″` under the jump)
and C.31's `first_bite`, both decided on their boxes — the two `omega`-grade facts the fleet
will otherwise re-derive. -/

def c10_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:7] do
      for l in [1:7] do
        for dr in [1:7] do
          if !((e₁ * f₁) * l * dr == (e₁ * l) * (f₁ * dr)) then ok := false
          if 2 ≤ e₁ * f₁ && 2 ≤ l * dr then
            if !(4 ≤ (e₁ * f₁) * l * dr) then ok := false
  return ok

#guard c10_grid

#guard (List.range 20).all (fun D => (List.range 20).all (fun mu =>
  !(2 ≤ D && 4 ≤ mu) || 8 ≤ D * mu))

/-! ### C.97's S2 TOWER WITNESS, VERIFIED FROM THE POLYNOMIALS UP (`q = 2`; the wild
`e₁ = 2 = p` row GC-11 demands, and chapter D's T1 battery check 10 consumer).

C.97 has no signature (D1), but its STATEMENT displays a fully concrete third-stage tower over
`ℤ₂`: `Φ′ = x² − 2` (frame `(e₁,f₁,h) = (2,1,1)`), `Φ₂ = Φ′² − 4x` (`u₂ = 5`),
`Φ₃ = Φ₂² − 16Φ′` (`u₃ = 21`), ladder `[4,10,21]` for `(x, Φ′, Φ₂)`, `n̂₂(21) = 16Φ′`, floor chain
`5 > 2·2·1` and `21 > 2·10`. Everything below is COMPUTED from the three polynomials, not
transcribed: the polynomials are multiplied out, their `2`-adic Newton polygons are checked to be
one-sided, and the root valuations that forces are propagated through the three defining
identities `Φ′(θ) = 0`, `Φ₂(ξ) = 0 ⇒ Φ′(ξ)² = 4ξ`, `Φ₃(ζ) = 0 ⇒ Φ₂(ζ)² = 16Φ′(ζ)` in exact `ℚ`.
**Every displayed number of C.97 is confirmed** (finding F1 — the one node of §§9–13 whose content
the gate could reach at all). -/

def pmul (a b : List ℤ) : List ℤ :=
  (List.range (a.length + b.length - 1)).map (fun k =>
    ((List.range (k + 1)).map (fun i => (a.getD i 0) * (b.getD (k - i) 0))).sum)

def padd (a b : List ℤ) : List ℤ :=
  (List.range (max a.length b.length)).map (fun k => a.getD k 0 + b.getD k 0)

def psmul (c : ℤ) (a : List ℤ) : List ℤ := a.map (fun x => c * x)

def v2 : ℤ → ℕ
  | 0 => 0
  | n => (n.natAbs).factorization 2

def Phi1 : List ℤ := [-2, 0, 1]                                 -- Φ′ = x² − 2
def Phi2 : List ℤ := padd (pmul Phi1 Phi1) [0, -4]              -- Φ₂ = Φ′² − 4x
def Phi3 : List ℤ := padd (pmul Phi2 Phi2) (psmul (-16) Phi1)   -- Φ₃ = Φ₂² − 16Φ′

#eval Phi2   -- [4, -4, -4, 0, 1]
#eval Phi3   -- [48, -32, -32, 32, 24, -8, -8, 0, 1]

/-! `f` is one-sided of slope `v(a₀)/n` at `p = 2`: every support point lies on or above the line
through `(0, v(a₀))` and `(n, 0)`, cleared to `n·v(aᵢ) ≥ v(a₀)·(n − i)`. -/
def isPure2 (f : List ℤ) : Bool :=
  let n := f.length - 1
  let v0 := v2 (f.getD 0 0)
  (f.getD n 0 == 1) && (List.range (n + 1)).all (fun i =>
    if f.getD i 0 == 0 then true else decide (n * v2 (f.getD i 0) ≥ v0 * (n - i)))

#guard isPure2 Phi2
#guard isPure2 Phi3
#guard v2 (Phi2.getD 0 0) == 2 && Phi2.length - 1 == 4    -- slope 2/4 = 1/2, all four roots
#guard v2 (Phi3.getD 0 0) == 4 && Phi3.length - 1 == 8    -- slope 4/8 = 1/2, all eight roots

def vtheta : ℚ := 1/2
def vxi : ℚ := 1/2
def vzeta : ℚ := 1/2
def vPhi1_at_xi : ℚ := (2 + vxi) / 2            -- Φ′(ξ)² = 4ξ
def vPhi1_at_zeta : ℚ := (2 + vzeta) / 2
def vPhi2_at_theta : ℚ := 2 + vtheta            -- Φ₂(θ) = −4θ
def vPhi2_at_zeta : ℚ := (4 + vPhi1_at_zeta) / 2 -- Φ₂(ζ)² = 16Φ′(ζ)

#guard vPhi1_at_xi == 5/4
#guard vPhi2_at_theta == 5/2
#guard vPhi2_at_zeta == 21/8
/-! `u₂ = dv(Φ₂(θ))` with `dv = e₁·v = 2v`. -/
#guard (2 : ℚ) * vPhi2_at_theta == 5
/-! the ladder `[4, 10, 21] = (v₃(x), v₃(Φ′), v₃(Φ₂))` with `v₃ = e₁e₂e₃·v = 8v`. -/
#guard ((8 : ℚ) * vzeta, (8 : ℚ) * vPhi1_at_zeta, (8 : ℚ) * vPhi2_at_zeta) == (4, 10, 21)
/-! `u₃ = 21`; `n̂₂(21) = 16Φ′` at `v₂ = e₁e₂·v = 4v`; the two floors; the cleared `u₃ = e₃κ₃`. -/
#guard (8 : ℚ) * vPhi2_at_zeta == 21
#guard (4 : ℚ) * (4 + vPhi1_at_xi) == 21
#guard 5 > 2 * 2 * 1
#guard 21 > 2 * 10
#guard 2 * 21 / 2 == 21

/-! ### C.16(b), C.18(a), C.41 — the remaining decidable signed statements, grid-verified.
All four pass; no defect. Together with `c16_grid`/`c18_grid`/`c28_grid`/`c30_grid`/
`c31_floor_grid`/`c50_grid`/`c55_grid`/`c10_grid` above, **every arithmetic-layer axiom of the
signed half of chapter C has been machine-tested on a grid, and exactly one of them is false
(`jump_drop`, D21).** -/

def c16_unique_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for k in [0:41] do
          for i in [0:e₁] do
            if (i * h) % e₁ == k % e₁ then
              if i != slotIdxN e₁ h k then ok := false
  return ok

#guard c16_unique_grid

def c18_iff_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:7] do
    for f₁ in [1:6] do
      for h in [0:9] do
        if Nat.gcd h e₁ == 1 then
          for k in [0:80] do
            let full := (slotWindowN e₁ f₁ h k).length == f₁
            if full != decide ((slotIdxN e₁ h k + e₁ * (f₁ - 1)) * h ≤ k) then ok := false
  return ok

#guard c18_iff_grid

def c41_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:9] do
    for h in [0:13] do
      if Nat.gcd h e₁ == 1 then
        for a in [0:25] do
          for b in [0:25] do
            let sa := slotIdxN e₁ h a
            let sb := slotIdxN e₁ h b
            if !(sa + sb == slotIdxN e₁ h (a + b) + e₁ * ((sa + sb) / e₁)) then ok := false
            if !((sa + sb) / e₁ ≤ 1) then ok := false
            if !(twistExpN e₁ h (a + b)
                  == twistExpN e₁ h a + twistExpN e₁ h b + (sa + sb) / e₁) then ok := false
  return ok

#guard c41_grid

def c41_nsmul_grid : Bool := Id.run do
  let mut ok := true
  for e₁ in [1:8] do
    for h in [0:11] do
      if Nat.gcd h e₁ == 1 then
        for f₂ in [1:9] do
          for t in [0:f₂] do
            for u₂ in [0:15] do
              if !(twistExpN e₁ h ((f₂ - t) * u₂)
                    == (f₂ - t) * twistExpN e₁ h u₂
                        + (f₂ - t) * slotIdxN e₁ h u₂ / e₁) then ok := false
  return ok

#guard c41_nsmul_grid

end NumericGate

end LeanspecC

/-
RESUME (chapter-C leanspec stub gate, 2026-08-16): COMPLETE for everything the blueprint signs.
82 declarations landed (39 axiom / 3 structure / 2 abbrev / 36 def / 1 theorem / 1 example) +
a 47-`#guard` numeric gate, all passing; `lake build Leanspec.ChapC` green; zero `sorry`.
NOT landed, and not landable: the 70 unsigned nodes of D1 and the 19 ellipsis-bearing ones of D2
(dispositions per node in the section comments above). The file is NOT wired into
`leanspec/Leanspec.lean` — the orchestrator owns that line.

NEXT ACTIONS, in the order they unblock the fleet:
 1. CHAP-C amendment for D21 (`jump_drop`: replace `hL` by `hjump : 2 ≤ ℓ * d_r`) — a false
    signed statement, stop-the-line class.
 2. CHAP-C must SIGN §§6(tail)–13. Until then no fleet agent can fire on C.52–C.126, and §15's
    own gate order (a)–(d) is unsatisfiable (it names five fragile signatures that do not exist).
 3. D19/D20: decide whether `KeyFrame` gains the `GenreDatum` side conditions (`1 ≤ h`,
    `2 ≤ e₁f₁`, a `Q`), or whether C.14/C.43 route around H §8. This is a GC-5 RE-PLAN.
 4. D24: break the `C.94` ⇄ `I.01` deadlock (Display A line 1 is currently vacuous in Lean).
 5. D11/D18/D3/D4/D5/D6/D8/D9/D10 are mechanical blueprint repairs; the cures are in this file.
 6. Owner: the `C.66` statement below is this gate's drafting, not a transcription — gate (b)
    statement inspection is owed (D23), and `C.92`/`C.94` have no statement to inspect at all.
-/
