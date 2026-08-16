import Uniformity

/-!
# Chapter C — THE TOWER GRAMMAR: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-C_tower_grammar.md` (127 nodes, `C.01 … C.126` + `C.56a`) that
the blueprint actually WRITES IN LEAN, landed in the isolated `leanspec` environment **before**
the chapter-C fleet fires, in blueprint node order.

**STATE: OPEN (stub gate), 2026-08-16.** Nothing of chapter C has landed in `leanfinal`, so every
theorem-shaped node here is an `axiom` stub in the UNLANDED state of the `Leanspec.lean` stub
lifecycle, and every `def`/`structure` carries a real body. **Zero `sorry`.**

**A-C.1 RIDER (2026-08-16, the SIGNATURE-COMPLETION amendment — this file extended in place
per its lifecycle).** The HEADLINE FINDING below describes the state AT THE GATE; amendment
A-C.1 (`blueprint/CHAP-C_tower_grammar.md`, A-§ block items (a)–(m)) has since SIGNED the 70
unsigned nodes and cured the 19 ellipsis signatures: the signed layer now lives in the
`A-C.1 SIGNATURE-COMPLETION LAYER` sections below (§5 carriers, §6 tail, §§7–13), the D21
`jump_drop` re-sign and the D19/D20 carrier bridge (NODE C.14a) are applied in place, the
D14/D15/D22 gate-hygiene tables are in the numeric section, and the three gate-(b) cite
axioms (`fgmn_residual_mul`, `fgmn_calculus_exists`, `agnprw_termination`) are DECLARED
under append #66's category signature (statements owner-UNINSPECTED — queued in CHAP-I's
2026-08-16 A-C.1 addendum). Four residuals are BOOKED to the fleet (C.90(b), C.91(c),
C.102's letter-read field, C.58's (b)/(d)/(e) companions), each recorded at its node.

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

Signable AT THE GATE: `C.41`, `C.42`, `C.50`. Everything else in §6 either depended on
`C.43`'s undeclared `stageLiftO` (defect D19) or on `C.44`'s bodyless `towerLabel`, or had
no signature at all (`C.52`–`C.54`, `C.56`–`C.58`; defect D1) — **all SIGNED at A-C.1**: see
the A-C.1 SIGNATURE-COMPLETION LAYER below (`wrapExp`/`composedKey`, `towerLabel`/
`levelDatum`, `towerLabelEquiv`, `composedKey_slot_residue`, `composedKey_isTestKey`,
`fullSide_block`, `towerLocus`, `budgetFloor`/`towerLocus_iff_budget`, `towerFreeCount`/
`towerLocus_fibration`, the C.54 floors, `towerLocus_depth3_floor` re-signed, `k2DigitLift`,
`refine_invariants`/`refine_kills`, `refineDom`/`refineCod`/`refine_bijection`/
`refine_transported_event`, `window_band1`/`window_consultation`, and C.49's three). -/

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

Signable AT THE GATE: `C.59`, `C.60`. `C.61` was unsignable (D2 + D11); `C.62`–`C.70` had no
signature (D1) — **all SIGNED at A-C.1** (the layer below: `tier1_typeOf`, `ComposedLabel`/
`tier1_typeOf_composed`, `classSize_separable`, `blockDeg_eq`/`mult₂_readable`,
`dv2_length_sum`, `multiplicity_tie`, `dv2Pin_translation_interior`,
`ClassSizeSupplyData`/`classSize_supply`, `side_degree_conservation`; `C.66`'s
`fgmn_residual_mul` was drafted at the gate and is ADOPTED at A-C.1). -/

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

/-! ## A-C.1 §6 — COMPOSED KEYS AND TOWER BRIDGES (C.43–C.58 completions)

Determinations recorded per node in the blueprint. The big ones: `composedKey`'s lift enters
through C.14a's `stageLiftO` (D19 resolved); `towerLabel` takes the EXPLICIT
`η^{−Qf₂}·ψ₂(η^Q Z)` form (the corpus's two presentations coincide, `EFF.HETOW.16`(a));
`towerLocus`'s residual exponent is `μ₂` (the blueprint display's `e₂f₂μ₂/e₂` was the
residual DEGREE `f₂μ₂`, not the exponent — a C-H12-class slip, caught by C.26's degree law
and recorded); `budgetFloor` is the node-level floor (the numeric mirror is renamed
`budgetFloorN` per the `N`-convention). -/

/-! ### NODE C.43 [def] — `wrapExp`, `composedKey` [signed: A-C.1; D19 resolved via C.14a] -/

/-- `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` — C.41(ii)'s wrap exponent. -/
def wrapExp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (t : ℕ) : ℕ :=
  (T.f₂ - t) * F.slotIdx T.u₂ / F.e₁

/-- The wrap-corrected composed key (`EFF.HETOW.13`, verbatim; the gauge-naive form is DEAD). -/
noncomputable def composedKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Polynomial O :=
  F.key ^ (T.e₂ * T.f₂)
    - (Finset.range T.f₂).sum fun t =>
        F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))
          * F.key ^ (T.e₂ * t)

/-! ### NODE C.44 [def+lemma] — `towerLabel`, `TowerDatum.levelDatum` [signed: A-C.1] -/

/-- HETOW-1(a)'s translated label, in the EXPLICIT form `r̃ = η^{−Qf₂}·ψ₂(η^Q Z)`. -/
noncomputable def towerLabel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Polynomial (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  Polynomial.C ((F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂))
    * T.ψ₂.comp (Polynomial.C ((F.stageLetter H₀ hpin) ^ F.twistExp T.u₂) * Polynomial.X)

axiom towerLabel_spec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (towerLabel T).Monic ∧ Irreducible (towerLabel T) ∧
    (towerLabel T).natDegree = T.f₂ ∧ (towerLabel T).coeff 0 ≠ 0

/-- the bridge datum: `⟨u₂, e₂, r̃⟩` is a `LevelDatum` (C.09's fields discharged; `hκ` is
exactly the node floor). -/
noncomputable def TowerDatum.levelDatum {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : LevelDatum F H₀ hpin where
  u := T.u₂
  ℓ := T.e₂
  r := towerLabel T
  hℓ := T.he₂
  hcop := T.hcop
  hκ := T.hfloor
  hrmonic := (towerLabel_spec T hπ).1
  hrirr := (towerLabel_spec T hπ).2.1
  hr0 := (towerLabel_spec T hπ).2.2.2
  hrdeg := by rw [(towerLabel_spec T hπ).2.2.1]; exact T.hf₂

/-! ### NODE C.45 [lemma] — `towerLabelEquiv` [signed: A-C.1; def-kind with theorem-grade
body, landed as an axiom constant per this layer's rule] -/

axiom towerLabelEquiv {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    AdjoinRoot (towerLabel T) ≃ₐ[F.stageField H₀ hpin] AdjoinRoot T.ψ₂

/-! ### NODE C.46 [lemma] — the corrected key's slot residues [signed: A-C.1; carries
`1 ≤ F.h` per the C.14a perimeter — it consumes H.56 through the reconciliation] -/

axiom composedKey_slot_residue {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    {t : ℕ} (ht : t < T.f₂) :
    F.twistRead H₀ hpin ((T.f₂ - t) * T.u₂) (dev F.key (composedKey T) (T.e₂ * t))
      = (towerLabel T).coeff t

/-! ### NODE C.47 [theorem] — HETOW-2 at the (LIFT)-form, `w = 0` [signed: A-C.1] -/

axiom composedKey_isTestKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] :
    IsTestKey (T.levelDatum hπ) (composedKey T)

/-! ### NODE C.48 [lemma] — HETOW-3's full-side block identities [signed: A-C.1; clauses
(a)+(b) signed — clause (c) is the C.47 → C.40 chain, a fleet-time re-export] -/

axiom fullSide_block {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (hdeg : f.natDegree = μ₂ * T.D₂) (hpure : IsDvPure F f T.u₂ T.e₂)
    (hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂) :
    dvHgt F f 0 ≠ ⊤ ∧ ¬ F.key ∣ f ∧
    blockFactor (T.levelDatum hπ) f = f ∧ mult₂ (T.levelDatum hπ) f = μ₂

/-! ### NODE C.51 [def] — the tower-entry locus `𝒯` [signed: A-C.1; residual exponent `μ₂`,
the display's `e₂f₂μ₂/e₂` being the residual DEGREE — determination recorded] -/

def towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) : Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = μ₂ * T.D₂ ∧ IsDvPure F f T.u₂ T.e₂ ∧
    ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂}

/-! ### NODE C.52 [theorem] — GENTOW-1(a), budget floors [signed: A-C.1] -/

/-- the composed budget floor (the r2-F2 display at `(E₂, w(a,b), e₁e₂)`); the numeric-gate
mirror is `budgetFloorN`. -/
def budgetFloor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ j a b : ℕ) : ℕ :=
  let w := slotOffset T a b
  let tgt := (μ₂ - j) * T.E₂ - w
  let d := F.e₁ * T.e₂
  if (μ₂ - j) * T.E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

axiom towerLocus_iff_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) :
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)

/-! ### NODE C.53 [theorem] — GENTOW-1(b), the fibration and the CLIPPED count
[signed: A-C.1; the clip is ℕ-subtraction, definitionally `max 0`] -/

noncomputable def towerFreeCount {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range μ₂, ∑ a ∈ Finset.range (F.e₁ * F.f₁),
    ∑ b ∈ Finset.range (T.e₂ * T.f₂), (N - budgetFloor T μ₂ j a b)

axiom towerLocus_fibration {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (μ₂ N : ℕ) (hμ₂ : 0 < μ₂) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O,
          proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂}
      = residueCard O ^ towerFreeCount T μ₂ N

/-! ### NODE C.54 [lemma] — node floors and the field floor [signed: A-C.1] -/

axiom towerLocus_node_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Pin (T.levelDatum hπ) (composedKey T) f j

axiom towerLocus_node_floor_sharp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {j : ℕ} (hj : j < μ₂) :
    ∃ f ∈ towerLocus T μ₂,
      dv2Pin (T.levelDatum hπ) (composedKey T) f j = (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞)

axiom towerLocus_field_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) (hdvd : g ∣ f) :
    ((g.natDegree * T.E₂ : ℕ) : ℕ∞)
      < (F.e₁ * T.e₂) • addVal O (Algebra.norm O (AdjoinRoot.mk g (composedKey T)))

/-! ### NODE C.55 [theorem] — the depth-3 node floor (already signed at the gate as the
pin-lattice arithmetic; RE-SIGNED here at the blueprint's own carrier now that `dv2SideSet`
exists — the D3-class unbound `μ₂` bound) -/

axiom towerLocus_depth3_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ}
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hcop : Nat.Coprime u₃ ℓ₃)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty) :
    ℓ₃ * T.E₂ < u₃

/-! ### NODE C.56a [def] — the base-resolved K₂-digit lift [signed: A-C.1; the digit
coordinates are the canonical-representative reads (choice), the inverse-twist normalization
pinned by the exact-height/residue companions at fleet time — determination recorded] -/

/-- the `K`-coordinate of a `K₂`-element in the `β`-basis (choice on the `AdjoinRoot`
representative; junk-stable). -/
noncomputable def k2Coord {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (t : ℕ) :
    F.stageField H₀ hpin :=
  (((AdjoinRoot.mk_surjective s).choose).coeff t)

/-- the `n̂₂` exponent solve `(a₀, i, b)` at height `m` (`e₁e₂a₀ + ie₂h + bu₂ = m` when it
exists; junk-total). -/
noncomputable def n2Exp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : ℕ × ℕ × ℕ :=
  let b := towerSolve T.u₂ T.e₂ m
  let m' := (m - b * T.u₂) / T.e₂
  ((m' - F.slotIdx m' * F.h) / F.e₁, F.slotIdx m', b)

/-- NODE C.56a — `k2DigitLift` (the `.62` TERMINAL display: base RE-SOLVES per flavor). -/
noncomputable def k2DigitLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (m : ℕ) : Polynomial O :=
  ∑ r ∈ Finset.range F.f₁, ∑ t ∈ Finset.range T.f₂,
    Polynomial.C
        (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r)
          * π ^ (n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1)
      * Polynomial.X
          ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1 + F.e₁ * r)
      * F.key ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2 + T.e₂ * t)

/-! ### NODE C.56 [theorem] — GENTOW-2(i)+(ii), the composed refine transfer [signed: A-C.1] -/

axiom refine_invariants {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂) :
    (composedKey T - k2DigitLift T s lam).Monic ∧
    (composedKey T - k2DigitLift T s lam).natDegree = T.D₂ ∧
    IsTestKey (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam)

axiom refine_kills {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂)
    {j : ℕ} (hj : j < μ₂) :
    (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) f j

/-! ### NODE C.57 [theorem] — R2b's bijection + the transported event [signed: A-C.1;
`DOM_N`/`COD_N` as the named strata below — R2b's completed inventory] -/

def refineDom {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∃ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1).Nonempty,
      dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1 hne
        = (Polynomial.X - Polynomial.C s) ^ μ₂}

def refineCod {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∀ j < μ₂, (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) (monicPoly a) j}

axiom refine_bijection {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (μ₂ N lam : ℕ) (hμ₂ : 0 < μ₂) (hslope : T.E₂ < lam)
    (s : AdjoinRoot (towerLabel T)) (hs : s ≠ 0) :
    Nat.card (refineDom T hπ μ₂ N lam s) = Nat.card (refineCod T hπ μ₂ N lam s)

axiom refine_transported_event {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    {g : Polynomial O} (hg : g ∈ towerLocus T μ₂)
    (hkills : ∀ j < μ₂, (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) g j)
    {j : ℕ} (hj : j < μ₂)
    (hbin : ¬ (ringChar (ResidueField O) ∣ Nat.choose μ₂ j)) :
    dv2Pin (T.levelDatum hπ) (composedKey T) g j = (((μ₂ - j) * lam : ℕ) : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (dev (composedKey T) g j)
      = (Nat.choose μ₂ j : AdjoinRoot (towerLabel T)) * (- s) ^ (μ₂ - j)

/-! ### NODE C.58 [theorem] — the composed window ledger [signed: A-C.1 at the consumed
core: BAND 1 stability (a), the consultation congruence (c); BAND-2/ragged/carry/content
clauses (b)/(d)/(e) BOOKED as fleet-time companions riding C.53's unipotence + H.53 —
recorded at the node] -/

axiom window_band1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a a' : Fin (μ₂ * T.D₂) → O}
    (hc : proj O (μ₂ * T.D₂) N a = proj O (μ₂ * T.D₂) N a')
    (ha : monicPoly a ∈ towerLocus T μ₂) {j m : ℕ} (hj : j < μ₂)
    (hm : dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j = (m : ℕ∞))
    (hband : m < F.e₁ * T.e₂ * N) :
    dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a') j = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a') j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a) j)

axiom window_consultation (d N m w : ℕ) (hd : 0 < d) (hw : w < d) (hm : m < d * N)
    (hcong : m % d = w % d) : m ≤ d * (N - 1) + w

/-! ## A-C.1 §7 — CLASS SIZE AND BLOCK LENGTH (C.61–C.70 completions) -/

/-! ### NODE C.61 [theorem] — Tier 1, the sandwich [signed: A-C.1; the `hm1` design hole
RESOLVED as the exact-residual hypothesis — no reshaping of C.29's committed `HasLabel`] -/

axiom tier1_typeOf {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g

/-! ### NODE C.62 [theorem] — Tier 1 iterated: `ComposedLabel` + the composed singleton
[signed: A-C.1; the hypothesis bundle IS the booked `ComposedLabel` structure] -/

structure ComposedLabel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (g : Polynomial O) : Type _ where
  u₃ : ℕ
  ℓ₃ : ℕ
  r₂ : Polynomial (AdjoinRoot (towerLabel T))
  hℓ₃ : 0 < ℓ₃
  hcop : Nat.Coprime u₃ ℓ₃
  hfloor : ℓ₃ * T.E₂ < u₃
  hr₂ : r₂.Monic ∧ Irreducible r₂ ∧ 0 < r₂.natDegree ∧ r₂.coeff 0 ≠ 0
  hgmonic : g.Monic
  hgdeg : g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree)
  hpure1 : IsDvPure F g T.u₂ T.e₂
  hxpure : IsPure Polynomial.X g F.h F.e₁
  hne₂ : (dv2SideSet (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃).Nonempty
  hres₂ : dv2ResPoly (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃ hne₂ = r₂

axiom tier1_typeOf_composed {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {g : Polynomial O} (C : ComposedLabel T hπ g)
    (hbox1 : ∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g')
    (hbox2 : ∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * C.r₂.natDegree) ∣ inertiaDegOf g') :
    typeOf g = ⟨{(F.e₁ * T.e₂ * C.ℓ₃, F.f₁ * T.f₂ * C.r₂.natDegree)}⟩ ∧ Irreducible g

/-! ### NODE C.63 [theorem] — Tier 1 assembled: the separable-side class-size law
[signed: A-C.1] -/

axiom classSize_separable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hg : g.Monic) (hpure : IsDvPure F g L.u L.ℓ)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hsep : (dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp).Separable) :
    ∃ (s : Finset (Polynomial (F.stageField H₀ hpin)))
      (Fac : Polynomial (F.stageField H₀ hpin) → Polynomial O),
      (∀ r ∈ s, r.Monic ∧ Irreducible r ∧ r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) ∧
      (∀ r : Polynomial (F.stageField H₀ hpin), r.Monic → Irreducible r →
        r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp → r ∈ s) ∧
      g = ∏ r ∈ s, Fac r ∧
      ∀ r ∈ s, (Fac r).Monic ∧
        (Fac r).natDegree = (F.e₁ * F.f₁) * L.ℓ * r.natDegree ∧
        ((∀ g' ∈ monicFactors (Fac r), (F.f₁ * r.natDegree) ∣ inertiaDegOf g') →
          typeOf (Fac r) = ⟨{(F.e₁ * L.ℓ, F.f₁ * r.natDegree)}⟩ ∧ Irreducible (Fac r))

/-! ### NODE C.64 [theorem] — Tier 2, the block length in read form [signed: A-C.1;
"computable from `f`" signed as the argmin-data equality] -/

axiom blockDeg_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f

axiom mult₂_readable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ f u₂ ℓ₂ hne = dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' ∧
    dv2SideDeg L Ψ f u₂ ℓ₂ hne = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne'

/-! ### NODE C.65 [lemma] — the above-seam span [signed: A-C.1 at the span form; the
summed `Σ dv2SideLen = mult₂` form is the fleet's argmin-partition corollary — recorded] -/

axiom dv2_length_sum {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f) :
    dv2Pin L Ψ (blockFactor L f) 0 ≠ ⊤ ∧
    dv2Pin L Ψ (blockFactor L f) (mult₂ L f) = (0 : ℕ∞) ∧
    ∀ u₂ ℓ₂ : ℕ, 0 < ℓ₂ → ℓ₂ * L.seam < u₂ →
      ∀ hne : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty,
        dv2SideMax L Ψ (blockFactor L f) u₂ ℓ₂ hne ≤ mult₂ L f

/-! ### NODE C.67 [theorem] — Tier 3, the multiplicity tie [signed: A-C.1; the proof
consumes C.66's `fgmn_residual_mul` BY NAME, so the landed footprint carries [cite:FGMN]] -/

axiom multiplicity_tie {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) {m : ℕ} (hm : 0 < m)
    (hmult : ∀ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
      L.r ^ m ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp ∧
      ¬ L.r ^ (m + 1) ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp) :
    (blockFactor L f).natDegree = (F.e₁ * F.f₁) * L.ℓ * (L.r.natDegree * m) ∧
    mult₂ L f = m ∧
    IsDvPure F (blockFactor L f) L.u L.ℓ ∧
    ∀ (hne : (dvSideSet F (blockFactor L f) L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F (blockFactor L f)
        (dvSideMin F (blockFactor L f) L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin (blockFactor L f) L.u L.ℓ hne M₀ hp = L.r ^ m

/-! ### NODE C.68 [lemma] — pin translation, interior equality [signed: A-C.1] -/

axiom dv2Pin_translation_interior {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {j : ℕ}
    (hj1 : dv2SideMin L Ψ f u₂ ℓ₂ hne < j) (hj2 : j < dv2SideMax L Ψ f u₂ ℓ₂ hne) :
    dv2Pin L Ψ f j = dv2Pin L Ψ (blockFactor L f) j + (complementConst L f : ℕ∞)

/-! ### NODE C.69 [theorem] — THE SUPPLY BUNDLE [signed: A-C.1 as a Prop-structure with the
three clause fields quoting the suppliers' statements — "the NAME is the contract"] -/

/-- the bundled class-size/block-length supply (clause 1 = C.63, clause 2 = C.64, clause 3 =
C.67), packaged so downstream chapters cite ONE name with per-clause hypotheses readable. -/
structure ClassSizeSupplyData {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : Prop where
  separable_side : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : Finite (ResidueField O))
    {g : Polynomial O}, g.Monic → IsDvPure F g L.u L.ℓ →
    IsPure Polynomial.X g F.h F.e₁ →
    ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      (dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp).Separable →
      ∃ (s : Finset (Polynomial (F.stageField H₀ hpin)))
        (Fac : Polynomial (F.stageField H₀ hpin) → Polynomial O),
        g = ∏ r ∈ s, Fac r ∧
        ∀ r ∈ s, (Fac r).Monic ∧ (Fac r).natDegree = (F.e₁ * F.f₁) * L.ℓ * r.natDegree ∧
          ((∀ g' ∈ monicFactors (Fac r), (F.f₁ * r.natDegree) ∣ inertiaDegOf g') →
            typeOf (Fac r) = ⟨{(F.e₁ * L.ℓ, F.f₁ * r.natDegree)}⟩ ∧ Irreducible (Fac r))
  read_form : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    {f : Polynomial O}, BlockContext L f →
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
  mixed_tie : ∀ (hπ : Irreducible π)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
    {f : Polynomial O}, BlockContext L f → ∀ {m : ℕ}, 0 < m →
    (∀ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
      L.r ^ m ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp ∧
      ¬ L.r ^ (m + 1) ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp) →
    mult₂ L f = m

axiom classSize_supply {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    ClassSizeSupplyData L

/-! ### NODE C.70 [lemma] — side-length accounting [signed: A-C.1 at the per-side core
`L_λ = ℓ·deg R`; the `Σ_r` decomposition rides C.67] -/

axiom side_degree_conservation (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {H₀ : ℕ} (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hf : f.Monic) (hpure : IsDvPure F f u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) :
    dvSideLen F f u ℓ hne = ℓ * (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree

/-! ## A-C.1 §6-tail — NODE C.49's three theorems (placed after §7: they consume C.62;
the blueprint's own forward-ref note honored) [signed: A-C.1] -/

axiom composed_dictionary {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (hsq : Squarefree f)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (hcop₃ : Nat.Coprime u₃ ℓ₃) (hfloor₃ : ℓ₃ * T.E₂ < u₃)
    (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty)
    (hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃).Separable)
    {r₂ : Polynomial (AdjoinRoot (towerLabel T))} (hr₂m : r₂.Monic) (hr₂i : Irreducible r₂)
    (hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃) :
    ∃ g : Polynomial O, g.Monic ∧ g ∣ f ∧
      g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
      ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
       (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
        typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)

axiom level3_dead_at_mult2_three (mr ℓ₃ d₃ L μ₂ : ℕ) (hμ : μ₂ = 3) (hm : 2 ≤ mr)
    (hjump : 2 ≤ ℓ₃ * d₃) (hL : mr * (ℓ₃ * d₃) ≤ L) (hLμ : L ≤ μ₂) : False

axiom tower_termination_instance (J : ℕ) (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ 6)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) : J = 0

/-! ## A-C.1 §10 — THE GENTOW2 SUPPLY LAYER (C.99–C.106)

Determinations (recorded per node in the blueprint): the §10 theorems live over the
`FGMNCalculus` interface at the CONCRETE depth-2 chain `T.deepTower hπ` (the consumed
generality — D/F's consumers are the S2 witness and depth-2/3 recipes), with the carrier
bridge `ρ : fld 2 ≃+* AdjoinRoot T.ψ₂` as an explicit hypothesis and the repo read
`repoRead := dv2Res` (C.104's determination: the coherent read IS the C.38a `K₂`-read).
Every ϑ-adjacent statement is in NORMALIZER-RATIO form (C-H6/GC-14: the D-table anchor is
cited at the nodes; no bare-ϑ orientation is committed here). -/

/-- the depth-2 chain of a tower datum (def-kind with theorem-grade fields; stub-carried as
an axiom constant + data clauses, the C.45/C.97 rule). -/
axiom TowerDatum.deepTower {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : DeepTower F H₀ hpin 2

axiom TowerDatum.deepTower_data {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (T.deepTower hπ).e 2 = T.e₂ ∧ (T.deepTower hπ).f 2 = T.f₂ ∧
    (T.deepTower hπ).u 2 = T.u₂ ∧
    Nonempty ((T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)

/-- the chain-normalizer MONOMIAL realizer: `n̂_{i+1}(k)` as an `O[x]`-polynomial from the
`towerNorm` exponent solve and the interface's chain keys. -/
noncomputable def FGMNCalculus.chainNorm {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (i k : ℕ) : Polynomial O :=
  Polynomial.C (π ^ (W.towerNorm i k).1) * Polynomial.X ^ (W.towerNorm i k).2.1
    * ∏ j : Fin i, (I.keyAt (j.1 + 1)) ^ ((W.towerNorm i k).2.2 j)

/-- the normalizer-RATIO `ϑ`-carrier (GC-14's ratio form; no orientation committed):
`res(n̂(u')^t / n̂(t·u'))` read through the interface at grade `t·u'`. -/
noncomputable def FGMNCalculus.thetaRatio {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (t : ℕ) : W.fld r :=
  I.Rgr (t * u') ((I.chainNorm r u') ^ t) * (I.Rgr (t * u') (I.chainNorm r (t * u')))⁻¹

/-- the depth-3 recipe key (the R3-3-completed display; stub-side shared abbreviation for
C.101/C.103). -/
noncomputable def recipe3 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (e' f' u' : ℕ)
    (c : ℕ → AdjoinRoot (towerLabel T)) : Polynomial O :=
  (composedKey T) ^ (e' * f')
    - ∑ t ∈ Finset.range f', k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)

/-! ### NODE C.104 [def] — the two-reads convention [signed: A-C.1; `(R-repo)` = the C.38a
coherent read — determination recorded; `(R-FGMN)` is the interface's `Rgr`] -/

noncomputable def repoRead {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L g

/-! ### NODE C.99 [theorem] — `LEMMA GENTOW2-B″`, the single-`w` slot law, ratio form
[signed: A-C.1] + the γ-calculus companion -/

axiom gentow2_Bpp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)   -- ⚠ SCOPE FENCE (A-C.1 self-catch): B″ is PROVED at depth 2 ONLY;
                   -- the general-depth form IS the OPEN [GENTOW5-W(i)] (C.89) — an
                   -- unfenced general-r signing would silently assert the open law.
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u') {t : ℕ} (ht : t < f') :
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t)

axiom theta_letter_valued {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)   -- the same depth-2 scope fence as gentow2_Bpp
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u') :
    I.thetaRatio 1 = 1 ∧
    ∀ t : ℕ, ∃ j k : ℕ, I.thetaRatio t = I.letterZ 1 ^ j * I.letterZ 2 ^ k

/-! ### NODE C.100 [theorem] — `LEMMA GENTOW2-B′`, the per-grade unit law, direction
`FGMN = u · repo` [signed: A-C.1] + the honesty companion (clause (4); its consumed
`u(β_t) = 1` form is machine-REFUTED at letter-live grades — PE4 LD2 — and DEAD) -/

axiom gentow2_Bp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    {β : ℕ} {g : Polynomial O} (hg : I.ExactGrade β g)
    (hdeg : g.natDegree < e' * f' * T.D₂) (hfree : ¬ composedKey T ∣ g) :
    I.Rgr β g
      = I.Rgr β (I.chainNorm 2 β)
        * ρ.symm ((towerLabelEquiv T hπ) (repoRead (T.levelDatum hπ) g))

axiom gentow2_Bp_unit_iff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    {β : ℕ} {g : Polynomial O} (hg : I.ExactGrade β g)
    (hdeg : g.natDegree < e' * f' * T.D₂) (hfree : ¬ composedKey T ∣ g)
    (hne0 : repoRead (T.levelDatum hπ) g ≠ 0) :
    I.Rgr β g = ρ.symm ((towerLabelEquiv T hπ) (repoRead (T.levelDatum hπ) g))
      ↔ I.Rgr β (I.chainNorm 2 β) = 1

/-! ### NODE C.101 [theorem] — `LEMMA GENTOW2-B` (r3 RESTATED): the B-law and the
multiplicative prescription [signed: A-C.1; `κ₃ > e₂f₂u₂` an EXPLICIT hypothesis, supplied
at leaves by C.55] -/

axiom gentow2_B {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0) :
    I.Rres (recipe3 T e' f' u' c)
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
              * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t

/-! ### NODE C.102 [theorem] — the letter formula [signed: A-C.1; ⚠ DETERMINATION FLAGGED
for the cross-read: the exponent `⌊ℓ₁u₂/e₁⌋` is read at `ℓ₁ = e₂` (the level-2 clearing
denominator) — verify against `EFF.GENTOW2.37` before fleet landing] -/

axiom letter_formula {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂) :
    I.letterZ 2 * I.letterZ 1 ^ (T.e₂ * T.u₂ / F.e₁) = ρ.symm (AdjoinRoot.root T.ψ₂)

/-! ### NODE C.103 [theorem] — `THEOREM GENTOW2-A`: the depth-3 key certificate
[signed: A-C.1; the `[Q10]`/(H-b) `ν`-optimality clause is STRUCK (TOWERRAT-R3-1) and is
NOT in the statement] -/

axiom gentow2_A {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
      (I.Rres (recipe3 T e' f' u' c)).natDegree = f') :
    I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
    ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T)

/-! ### NODE C.105 [lemma] — w-blindness (ENV-C4 abstract) [signed: A-C.1; "same
irreducible-factor degree pattern" via the UFD factor multiset] -/

/-- the `w`-conjugate `P^{(w)} := w^{deg P}·P(y/w)`. -/
noncomputable def wconj {K : Type*} [Field K] (w : K) (P : Polynomial K) : Polynomial K :=
  Polynomial.C (w ^ P.natDegree) * P.comp (Polynomial.C w⁻¹ * Polynomial.X)

axiom wconj_invariants {K : Type*} [Field K] (w : K) (hw : w ≠ 0) (P : Polynomial K)
    (hP : P.Monic) :
    (wconj w P).Monic ∧ (wconj w P).natDegree = P.natDegree ∧
    (wconj w P).coeff 0 = w ^ P.natDegree * P.coeff 0 ∧
    (Irreducible (wconj w P) ↔ Irreducible P) ∧
    ((wconj w P).Separable ↔ P.Separable) ∧
    Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors (wconj w P))
      = Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors P)

/-! ## A-C.1 §11 — THE HT COUNT LAYER (C.107–C.116)

A-C.1 determinations (per node in the blueprint): the tree is INDEX-ENCODED (`nodes : List`,
`parent : ℕ → ℕ`, root = 0, acyclicity `parent i < i` — no nested-inductive recursion);
`HTNode` carries the CEILED pin data (`Pceil`, ℕ-valued — the cleared argmin form), the side
set as a `Finset (ℕ × ℕ)` with a `sideType` function, and its orbit factor `kappa` as DATA
(the factorial computation rule is the corpus's, recorded; C.116's manifest keeps the
tags); the branch/global count FORMULAS land as arithmetic defs (`htBranchCount`,
`htGlobalCount`) and the count laws tie the realization strata to them.

**[re-signed: A-C.2, 2026-08-16 — the defect-repair amendment on the wave refutation
`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`].**  The A-C.1 transcription made
`L`, `sides`, the pin clause, and the arithmetic-shadow inequality FREE where the corpus
determines them; four repairs, all source-adjudicated (`EFF.W12.23`/`.24`/`.83`), all
certified (`verification/c109_ac2_cell_check.py`, 127 checks) and machine-refuted where
frozen (`C109_REFUTATION.lean.txt`, `C111_C114_REFUTATION.lean.txt`):
(1) C.108 gains the node polygon reads (`OnHull`/`IsVertex`/`NodeOnSide`/`nodeSideSet`/
`IsSide`/`nodeSideDeg`) and the well-formedness predicate `HTNode.WF`; `htCell`'s polygon
pin is re-signed to `EFF.W12.23`'s three-way law (`≥ Pceil` everywhere, `=` at vertices).
(2) C.109 takes `(hwf : v.WF)` inline; NEW node C.109a `dev_box_bridge` (the level-`N`
development ↔ coefficient-box bridge, the refutation record's named cost).
(3) C.111 is re-signed to the honest telescope: the corpus's PER-NODE inequality
(`EFF.W12.85`'s `#U_v = Q^{B_v−ΣD_u}` shadow) becomes the hypothesis `hnode`; `hvis`
dropped as dead weight.
(4) C.114's `htRealizes` pin re-signed like `htCell`'s; its two count axioms `ht_branch`/
`ht_global` are WITHDRAWN (refutable as frozen — the stratum reads none of `kappa`,
`kappa0`, `s`, non-root `sideType`s, nor child-completeness) and the node is BLOCKED
pending the realizes-refinement re-sign (A-C.3 target; clause list in the amendment).
C.110/C.112/C.113/C.115 audited: no re-sign (C.112 carries its inequality as the
hypothesis `hBD`; C.115 is formula-level, true for arbitrary `v`). -/

/-! ### NODE C.107 [def] — the residual censuses [signed: A-C.1] -/

/-- the factorization type of a polynomial (the `(deg, mult)` multiset) — stated over
`CommRing` + UFD binders so it applies at `resField φ`'s OWN ring structure (no `Field`
diamond; the instances are derivable from `IsKey φ` at every consumer). -/
noncomputable def residualTypeOf {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] (p : Polynomial K) : FactorizationType :=
  open Classical in
  ⟨(UniqueFactorizationMonoid.factors p).toFinset.val.map
    (fun q => (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))⟩

/-- `S_λ(K)` — the side census: monic, nonzero constant term, prescribed type. -/
noncomputable def sideCensus (K : Type*) [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (lam : FactorizationType) : ℕ :=
  Nat.card {p : Polynomial K // p.Monic ∧ p.coeff 0 ≠ 0 ∧ residualTypeOf p = lam}

/-- `C₀(q)` — the level-0 configuration census: distinct monic irreducibles of the
prescribed degrees. -/
noncomputable def configCensus (K : Type*) [CommRing K] [IsDomain K] (d : Multiset ℕ) : ℕ :=
  Nat.card {P : Multiset (Polynomial K) //
    P.map Polynomial.natDegree = d ∧ (∀ q ∈ P, q.Monic ∧ Irreducible q) ∧ P.Nodup}

/-! ### NODE C.108 [def] — the refinement tree and its node quantities [signed: A-C.1] -/

structure HTNode where
  /-- multiplicity `m_v`. -/
  m : ℕ
  /-- previous center depth `s_v` (0 at the root). -/
  s : ℕ
  /-- the exact polygon data, CEILED (`⌈P_v(j)⌉` — ℕ-computable from the cleared argmin). -/
  Pceil : ℕ → ℕ
  /-- the integral-boundary count `L_v`. -/
  L : ℕ
  /-- the sides `(u, ℓ)` of the node polygon. -/
  sides : Finset (ℕ × ℕ)
  /-- the per-side residual types `λ_{v,S}` (junk off `sides`). -/
  sideType : ℕ → ℕ → FactorizationType
  /-- the SIDE-TAGGED orbit factor `κ_v`, as data (the factorial rule is the corpus's
  computation; the side tag is necessary — roots on different sides cannot be permuted). -/
  kappa : ℕ

def HTNode.default0 : HTNode := ⟨0, 0, fun _ => 0, 0, ∅, fun _ _ => ⟨0⟩, 1⟩

/-- `B_v(N) = m·N − Σ_{j<m} ⌈P_v(j)⌉ − L_v`. -/
def HTNode.B (v : HTNode) (N : ℕ) : ℕ :=
  v.m * N - (∑ j ∈ Finset.range v.m, v.Pceil j) - v.L

/-- `D_v(N) = Σ_{j<m} max(N − ((m−j)s + 1), 0)` — the CLIP is ℕ-subtraction. -/
def HTNode.D (v : HTNode) (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range v.m, (N - ((v.m - j) * v.s + 1))

/- [A-C.2] the node polygon read off `Pceil` (chord tests, ℚ-free).  The lower convex hull
of the ceiled points `{(j, ⌈P(j)⌉) : j ≤ m}` IS the polygon `P`, so all reads are
ℕ-arithmetic on `Pceil`; certified against direct rational hull geometry
(`verification/c109_ac2_cell_check.py`, the `[ENC]` leg). -/

/-- [A-C.2] `(j, ⌈P_v(j)⌉)` lies on the hull: on/below every bracketing chord.  Under
`HTNode.WF` this is the corpus's "`P_v(j) ∈ ℤ`" (the integral boundary positions). -/
def HTNode.OnHull (v : HTNode) (j : ℕ) : Prop :=
  ∀ i k : ℕ, i ≤ j → j ≤ k → k ≤ v.m →
    (k - i) * v.Pceil j ≤ (k - j) * v.Pceil i + (j - i) * v.Pceil k

/-- [A-C.2] `(j, ⌈P_v(j)⌉)` is a VERTEX: strictly below every properly bracketing chord
(endpoints vacuously vertices; `IsVertex → OnHull`). -/
def HTNode.IsVertex (v : HTNode) (j : ℕ) : Prop :=
  ∀ i k : ℕ, i < j → j < k → k ≤ v.m →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k

/-- [A-C.2] B.16's `OnSide` at the node data: `j` attains the `(u, ℓ)`-support minimum. -/
def HTNode.NodeOnSide (v : HTNode) (u ℓ j : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ v.m → ℓ * v.Pceil j + u * j ≤ ℓ * v.Pceil i + u * i

/-- [A-C.2] B.16's `sideSet` at the node data: for a genuine side, its lattice abscissae. -/
noncomputable def HTNode.nodeSideSet (v : HTNode) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (v.m + 1)).filter (v.NodeOnSide u ℓ)

/-- [A-C.2] `(u, ℓ)` is a genuine side: cleared slope pair, support set of `≥ 2` points. -/
def HTNode.IsSide (v : HTNode) (u ℓ : ℕ) : Prop :=
  0 < ℓ ∧ Nat.Coprime u ℓ ∧ 2 ≤ (v.nodeSideSet u ℓ).card

/-- [A-C.2] B.20's `sideDeg` at the node data: `(sideMax − sideMin)/ℓ`, junk `0` off. -/
noncomputable def HTNode.nodeSideDeg (v : HTNode) (u ℓ : ℕ) : ℕ :=
  ((v.nodeSideSet u ℓ).max.getD 0 - (v.nodeSideSet u ℓ).min.getD 0) / ℓ

open Classical in
/-- [A-C.2] **node well-formedness** — the corpus's implicit coherence of the node datum
(`EFF.W12.83`'s `L_v = #{j < m_v : P_v(j) ∈ ℤ}` display; the census product over the sides
OF THE POLYGON): (i) monic top; (ii) ceiled-consistency (`Pceil` is pointwise the ceiling
of its own hull); (iii) the `L` law; (iv) the sides law; (v) the side-type degree law.
Every §11 count law takes it INLINE (the frozen C.109 without it is machine-refuted). -/
def HTNode.WF (v : HTNode) : Prop :=
  v.Pceil v.m = 0 ∧
  (∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ v.m → i < k →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k + (k - i)) ∧
  v.L = ((Finset.range v.m).filter v.OnHull).card ∧
  (∀ u ℓ : ℕ, ((u, ℓ) ∈ v.sides ↔ v.IsSide u ℓ)) ∧
  (∀ u ℓ : ℕ, (u, ℓ) ∈ v.sides → (v.sideType u ℓ).degree = v.nodeSideDeg u ℓ)

/-- the index-encoded finite tree: node `0` is the root; `parent i < i` is well-formedness. -/
structure HTTree where
  nodes : List HTNode
  parent : ℕ → ℕ

def HTTree.WF (t : HTTree) : Prop :=
  ∀ i, 0 < i → i < t.nodes.length → t.parent i < i

/-- the conservative cell `C_m(s)` on `ℕ∞`-height data: `v(b_j) ≥ (m−j)s + 1`. -/
def conservativeCell (m s : ℕ) : Set (ℕ → ℕ∞) :=
  {P | ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ P j}

/-- the exact node cell on members: pinned polygon + prescribed per-side residual types.
(`π` explicit — it appears only in the membership predicate; the domain/UFD instances on
`resField Φ` are derivable from `IsKey Φ` via `instFieldResField` at every consumer, taken
as binders here.)  [re-signed: A-C.2 — the polygon pin is `EFF.W12.23`'s three-way law in
ceiled form: `≥ Pceil` at every `j ≤ m`, equality exactly at the hull VERTICES; the retired
equality-everywhere pin was strictly smaller than the corpus cell at every non-vertex
position (certified: mutation M3 of `verification/c109_ac2_cell_check.py`).] -/
def htCell (π : O) (Φ : Polynomial O) [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] (v : HTNode) :
    Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = v.m * Φ.natDegree ∧
    (∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j) ∧
    (∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞)) ∧
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → (u, ℓ) ∈ v.sides →
      ∀ (hne : (sideSet Φ f u ℓ).Nonempty) (H₀ : ℕ),
        npHgt Φ f (sideMin Φ f u ℓ hne) = (H₀ : ℕ∞) →
        residualTypeOf (resPoly π Φ f u ℓ hne H₀) = v.sideType u ℓ}

/-- `(HT-branch)`'s formula as arithmetic over the tree data. -/
noncomputable def htBranchCount (Q : ℕ) (census : FactorizationType → ℕ)
    (t : HTTree) (N : ℕ) : ℕ :=
  ((List.range t.nodes.length).map (fun i =>
      let v := t.nodes.getD i HTNode.default0
      v.kappa * ∏ p ∈ v.sides, census (v.sideType p.1 p.2))).prod
    * Q ^ ((((List.range t.nodes.length).map
          (fun i => (t.nodes.getD i HTNode.default0).B N)).sum)
        - (((List.range t.nodes.length).drop 1).map
          (fun i => (t.nodes.getD i HTNode.default0).D N)).sum)

instance : Inhabited HTTree := ⟨⟨[], fun _ => 0⟩⟩

/-- the level-0 shape: branches `(d_i, m_i, tree_i)` + the level-0 orbit factor `κ₀`. -/
structure HTShape where
  branches : List (ℕ × ℕ × HTTree)
  kappa0 : ℕ

/-- `(HT-global)`'s formula (the branch censuses abstracted per branch). -/
noncomputable def htGlobalCount (S : HTShape) (q : ℕ)
    (census : ℕ → FactorizationType → ℕ) (N : ℕ) : ℕ :=
  S.kappa0
    * ((List.range S.branches.length).map (fun i =>
        let b := S.branches.getD i (0, 0, default)
        if b.2.1 = 1 then q ^ (b.1 * (N - 1))
        else htBranchCount (q ^ b.1) (census i) b.2.2 N)).prod

/-! ### NODE C.109a [lemma] — the level-`N` development ↔ coefficient-box bridge
[signed: A-C.2 — NEW node; the refutation record's named cost: "formalizing it needs the
level-`N` development↔coefficient-box bridge (`Coeff O (m·d) N ≃ Fin m → Coeff O d N`
through `dev`, well defined by B.10), which does not exist in `leanfinal` yet and is the
real cost of C.109"].  The `∃`-form pins the equivalence componentwise THROUGH `dev` at an
arbitrary lift, so level-`N` well-definedness of the development (B.10's content) is part
of the claim, not an assumption. -/

axiom dev_box_bridge {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    (m N : ℕ) :
    ∃ E : Coeff O (m * Φ.natDegree) N ≃ (Fin m → Coeff O Φ.natDegree N),
      ∀ (a : Fin (m * Φ.natDegree) → O) (j : Fin m) (i : Fin Φ.natDegree),
        E (proj O (m * Φ.natDegree) N a) j i
          = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
              ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ))

/-! ### NODE C.109 [lemma] — Step 1: the exact node cell [re-signed: A-C.2 — gains
`(hwf : v.WF)`; the frozen form (no `hwf`) is machine-refuted at
`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`; the re-signed law is certified at
13 exact-count instances, `verification/c109_ac2_cell_check.py`] -/

axiom ht_node_cell_card (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]  -- all derivable from hΦ; binders for elaboration
    (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
        ∃ a : Fin (v.m * Φ.natDegree) → O,
          proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v}
      = Nat.card (resField Φ) ^ v.B N
        * ∏ p ∈ v.sides, sideCensus (resField Φ) (v.sideType p.1 p.2)

/-! ### NODE C.110 [theorem] — Step 2: transfer at a repeated linear root [signed: A-C.1;
split → 2: the conservative-cell count + the translate-residual iff] -/

axiom ht_conservative_card (hπ : Irreducible π) [Finite (ResidueField O)]
    (d a k N : ℕ) (hd : 0 < d) (hk : 0 < k) :
    Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), (((a - i.1 / d) * k + 1 : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = residueCard O ^ (d * ∑ j ∈ Finset.range a, (N - ((a - j) * k + 1)))

axiom ht_transfer_residual_iff (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) {a k : ℕ} (ha : 2 ≤ a) (hk : 0 < k)
    (z : O) {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = a * Φ.natDegree)
    (hpure : IsPure Φ G k 1) (hne : (sideSet Φ G k 1).Nonempty) {H₀ : ℕ}
    (hp : npHgt Φ G (sideMin Φ G k 1 hne) = (H₀ : ℕ∞)) :
    (∀ j, j < a →
        (((a - j) * k + 1 : ℕ) : ℕ∞) ≤ npHgt (Φ - Polynomial.C (z * π ^ k)) G j)
      ↔ resPoly π Φ G k 1 hne H₀
          = (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) (resField Φ)
              (digAt π 0 z))) ^ a

/-! ### NODE C.111 [theorem] — Step 3: the fiber [re-signed: A-C.2 AT THE ARITHMETIC
SHADOW: the frozen form (hypotheses `hwf` + `hvis` only) is machine-refuted
(`C111_C114_REFUTATION.lean.txt`: nothing ties a child's `s` to its placement) and even
per-node `HTNode.WF` cannot rescue it (numeric leg [C111] of the certification).  The
corpus derives nonnegativity PER NODE from the fiber bijection (`EFF.W12.85`:
`#U_v(𝐑) = Q^{B_v(N)−Σ_u D_u(N)}`, "the exponent is a nonnegative integer"), so the honest
arithmetic shadow carries the per-node inequality as the hypothesis `hnode` — discharged by
the fleet's bijection at realized nodes — and keeps the telescope as the node's content.
`hvis` dropped as dead weight (the A-F.12 minimality rule); the multiplication-bijection
engine remains the booked B.37–B.40 weighted-grading RE-PLAN — recorded] -/

axiom ht_fiber_exponent_nonneg (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hnode : ∀ i, i < t.nodes.length →
      ((((List.range t.nodes.length).drop 1).filter (fun u => t.parent u == i)).map
        (fun u => (t.nodes.getD u HTNode.default0).D N)).sum
        ≤ (t.nodes.getD i HTNode.default0).B N) :
    (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum

/-! ### NODE C.112 [lemma] — Step 4: `(HT-rec)` in division-free form [signed: A-C.1] -/

axiom ht_rec (Q : ℕ) (hQ : 2 ≤ Q) (census : FactorizationType → ℕ)
    (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hBD : (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum) :
    htBranchCount Q census t N
        * Q ^ (((List.range t.nodes.length).drop 1).map
            (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      = ((List.range t.nodes.length).map (fun i =>
          let v := t.nodes.getD i HTNode.default0
          v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N)).prod

/-! ### NODE C.113 [theorem] — Step 5: termination + Ore certification [signed: A-C.1;
split → 2; (ii)'s `B-BOX-1` inheritance is the inner hypothesis, exactly B's] -/

axiom ht_depth_increase {Φ : Polynomial O} (hΦ : IsKey Φ) {G : Polynomial O} {m s : ℕ}
    (hm : 0 < m) (hpins : ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ npHgt Φ G j)
    (htop : npHgt Φ G m = (0 : ℕ∞))
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hne : (sideSet Φ G u ℓ).Nonempty) :
    ℓ * s < u

axiom ht_leaf_certified (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {φ : Polynomial O} (hφ : IsKey φ) {g : Polynomial O} (hg : g.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) {H₀ : ℕ}
    (hp : npHgt φ g (sideMin φ g u ℓ hne) = (H₀ : ℕ∞))
    (hsep : (resPoly π φ g u ℓ hne H₀).Separable)
    {r : Polynomial (resField φ)} (hrm : r.Monic) (hri : Irreducible r)
    (hdvd : r ∣ resPoly π φ g u ℓ hne H₀) :
    ∃ gr : Polynomial O, gr.Monic ∧ gr ∣ g ∧
      gr.natDegree = ℓ * (φ.natDegree * r.natDegree) ∧
      ((∀ g' ∈ monicFactors gr, (φ.natDegree * r.natDegree) ∣ inertiaDegOf g') →
        typeOf gr = ⟨{(ℓ, φ.natDegree * r.natDegree)}⟩ ∧ Irreducible gr)

/-! ### NODE C.114 [theorem] — `(HT-branch)` + `(HT-global)` [BLOCKED: A-C.2 — the two
count axioms are WITHDRAWN; `htRealizes`' pin clause re-signed (the C.108 D3 fix)].

The A-C.1 signature note had BOOKED "the per-node residual-type/side-tag refinements ride
`htCell`" to the fleet.  The A-C.2 audit shows the booking is SIGNATURE-critical, not
proof-side: as frozen, the stratum reads none of `kappa`, `kappa0`, `s`, the non-root
`sideType`s, nor the child-completeness of the tree, all of which `htBranchCount`/
`htGlobalCount` read — both axioms are machine-refuted
(`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`: `c114_branch_frozen_false`,
`c114_global_frozen_false`), so they cannot stand in this file (a refutable axiom is a live
inconsistency).  They are withdrawn pending the realizes-refinement re-sign (A-C.3 target);
the amendment records the designed clause list: per-node `HTNode.WF`; per-node cell
membership `G i ∈ htCell π (K i) (node i)` (subsumes the polygon pins and pins the types);
the `s`-pin `gaussVal (K i − K (t.parent i)) = (s_i : ℕ∞)`; sibling distinctness on a side;
child-count = the side type's repeated-linear count (completeness at the data level); and
the `(HT-orbit)` κ-rule at tree level.  The withdrawn signatures are preserved verbatim in
the refutation record (`C114BranchFrozen`, `C114GlobalFrozen`). -/

/-- `f` realizes the tree `t` at the key `Φ`: cluster factors and recentered keys per node,
child clusters dividing their parents.  [re-signed: A-C.2 — the polygon pin clause takes
the same hull form as `htCell`'s (defect D3): `≥ Pceil` everywhere, equality at vertices.
The realizes-refinement (see the node note above) will extend this carrier; the pin fix is
recorded now so downstream re-signs build on the faithful form.] -/
def htRealizes (Φ f : Polynomial O) (t : HTTree) : Prop :=
  ∃ (G K : ℕ → Polynomial O), K 0 = Φ ∧ G 0 = f ∧
    ∀ i, i < t.nodes.length →
      (G i).Monic ∧
      (G i).natDegree = (t.nodes.getD i HTNode.default0).m * (K i).natDegree ∧
      (∀ j, j ≤ (t.nodes.getD i HTNode.default0).m →
        ((t.nodes.getD i HTNode.default0).Pceil j : ℕ∞) ≤ npHgt (K i) (G i) j) ∧
      (∀ j, j ≤ (t.nodes.getD i HTNode.default0).m →
        (t.nodes.getD i HTNode.default0).IsVertex j →
        npHgt (K i) (G i) j = ((t.nodes.getD i HTNode.default0).Pceil j : ℕ∞)) ∧
      (0 < i → G i ∣ G (t.parent i) ∧
        (K i).natDegree = (K (t.parent i)).natDegree ∧
        (K i - K (t.parent i)).natDegree < (K i).natDegree)

-- [A-C.2] `axiom ht_branch` and `axiom ht_global` WITHDRAWN here (machine-refuted as
-- frozen; see the node note above and `C111_C114_REFUTATION.lean.txt`).  Node C.114 is
-- BLOCKED pending the realizes-refinement re-sign (A-C.3).

/-! ### NODE C.115 [lemma] — specializations [signed: A-C.1 at the depth-zero clause; the
obstruction-instance and L0-shape values are §13's executed `htSpot` rows (the D15 block)] -/

axiom ht_depth_zero (Q : ℕ) (census : FactorizationType → ℕ) (v : HTNode) (N : ℕ) :
    htBranchCount Q census ⟨[v], fun _ => 0⟩ N
      = v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N

/-! ### NODE C.116 — the §11 disposition manifest (documentation node) -/

section C116Manifest
#check @HTNode.B          -- the digit-budget quantity
#check @HTNode.D          -- the clipped history quantity (the C.53 discipline)
#check @HTNode.kappa      -- the side-tagged orbit factor: A MANDATORY TAG (Phase-B contract)
#check @HTNode.sideType   -- side tags: MANDATORY (roots on different sides never permute)
#check @HTNode.WF         -- [A-C.2] node well-formedness: MANDATORY on every count law
#check @htBranchCount
#check @htGlobalCount
-- [A-C.2] `#check @ht_branch` / `#check @ht_global` removed: the two axioms are WITHDRAWN
-- (machine-refuted as frozen); see NODE C.114's note and C111_C114_REFUTATION.lean.txt.
end C116Manifest

/-! ## A-C.1 §12 — LEVEL-`N` TOWER CERTIFICATES (C.117–C.122) -/

/-! ### NODE C.117 [def] — level-2 window visibility [signed: A-C.1; abscissa-0-free: the
bound is on every consulted pin, per GC-1's visibility rule] -/

def Visible₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (N : ℕ) : Prop :=
  ∀ j, j ≤ f.natDegree / L.keyDeg₂ → dv2Pin L Ψ f j ≠ ⊤ →
    dv2Pin L Ψ f j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)

axiom Visible₂_mono {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) {N N' : ℕ} (h : N ≤ N') :
    Visible₂ L Ψ f N → Visible₂ L Ψ f N'

/-! ### NODE C.118 [lemma] — visible reads are window functions [signed: A-C.1; B.77's own
split: heights half / residual half] -/

axiom dv2_read_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N) {j : ℕ} (hj : j ≤ n / L.keyDeg₂) :
    dv2Pin L Ψ (monicPoly a) j = dv2Pin L Ψ (monicPoly a') j

axiom dv2_read_congr_res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂).Nonempty) :
    dv2ResPoly L Ψ (monicPoly a) u₂ ℓ₂ hne = dv2ResPoly L Ψ (monicPoly a') u₂ ℓ₂ hne'

/-! ### NODE C.119 [theorem] — the tower certificate kernel [signed: A-C.1] -/

axiom tower_cert_kernel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a : Fin (μ₂ * T.D₂) → O}
    (hmem : monicPoly a ∈ towerLocus T μ₂)
    (hvis : Visible₂ (T.levelDatum hπ) (composedKey T) (monicPoly a) N)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (hcop₃ : Nat.Coprime u₃ ℓ₃) (hfloor₃ : ℓ₃ * T.E₂ < u₃)
    (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃).Nonempty)
    (hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃ hne₃).Separable)
    {r₂ : Polynomial (AdjoinRoot (towerLabel T))} (hr₂m : r₂.Monic) (hr₂i : Irreducible r₂)
    (hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃ hne₃) :
    ∀ b : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N b = proj O (μ₂ * T.D₂) N a →
      ∃ g : Polynomial O, g.Monic ∧ g ∣ monicPoly b ∧
        g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
        ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
         (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
          typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)

/-! ### NODE C.120 [theorem] — the tower `DecidedAt` certificate [signed: A-C.1] -/

axiom tower_decidedAt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a : Fin (μ₂ * T.D₂) → O}
    (hmem : monicPoly a ∈ towerLocus T μ₂) (hsq : Squarefree (monicPoly a))
    (hvis : Visible₂ (T.levelDatum hπ) (composedKey T) (monicPoly a) N)
    (hsep : ∀ (u₃ ℓ₃ : ℕ), 0 < ℓ₃ → Nat.Coprime u₃ ℓ₃ → ℓ₃ * T.E₂ < u₃ →
      ∀ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃).Nonempty,
        (dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃ hne).Separable)
    (hbox : ∀ g' ∈ monicFactors (monicPoly a), CBox1Side (T.levelDatum hπ) g') :
    DecidedAt O (μ₂ * T.D₂) (typeOf (monicPoly a)) N (proj O (μ₂ * T.D₂) N a)

/-! ### NODE C.121 [lemma] — existence of a certifying `N`, per member [signed: A-C.1;
per-member ONLY — GC-9.3's no-uniform-`N` law] -/

axiom exists_certifying_N {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hmem : f ∈ towerLocus T μ₂) (hsq : Squarefree f) :
    ∃ N : ℕ, Visible₂ (T.levelDatum hπ) (composedKey T) f N

/-! ### NODE C.122 [lemma] — the degenerate-stratum path [signed: A-C.1] -/

axiom tower_cert_peel_path {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a : Fin (μ₂ * T.D₂) → O}
    (hmem : monicPoly a ∈ towerLocus T μ₂)
    (hctx : BlockContext (T.levelDatum hπ) (monicPoly a))
    (hvis : Visible₂ (T.levelDatum hπ) (composedKey T) (monicPoly a) N)
    (hdvd : composedKey T ∣ monicPoly a)
    (hbox : CBox1Side (T.levelDatum hπ) (composedKey T)) :
    typeOf (monicPoly a)
      = ⟨{(F.e₁ * T.e₂, F.f₁ * T.f₂)}
          + (typeOf ((monicPoly a) /ₘ composedKey T)).data⟩

/-! ## A-C.1 §8 — THE SHADOW-READ LAYER AND PARTIAL SIDES (C.71–C.82)

Determinations: `shadowDev` gets a REAL body — the mod-`Φ′`-reduced two-variable division
tower, implemented as the `Φ₂`-adic development computed in `(O[x]/Φ′)[Z]` (`biRead` +
`devQ`, the generic monic division recursion) and mapped back through the CANONICAL
representative (`AdjoinRoot.modByMonicHom`, no choice); `TouchCert` is the `[GT3-r2]`
certificate as the exact-`Θ_j` nonvanishing of `Φ₂^{μ₂}`'s own read discrepancy. -/

/-- generic monic-division development (B.02's `dev` over any `CommRing`; stub-side helper). -/
noncomputable def devQ {R : Type*} [CommRing R] (Ψ : Polynomial R) :
    Polynomial R → ℕ → Polynomial R
  | g, 0 => g %ₘ Ψ
  | g, j + 1 => devQ Ψ (g /ₘ Ψ) j

/-- the mod-`Φ′`-reduced two-variable image `O[x] → (O[x]/Φ′)[Z]`. -/
noncomputable def biRead (F : KeyFrame O π) (g : Polynomial O) :
    Polynomial (AdjoinRoot F.key) :=
  (Finset.range (g.natDegree + 1)).sum fun b =>
    Polynomial.C (AdjoinRoot.mk F.key (dev F.key g b)) * Polynomial.X ^ b

/-! ### NODE C.71 [def] — `shadowDev` [signed: A-C.1; real body] -/

noncomputable def shadowDev {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (f : Polynomial O) (j : ℕ) : Polynomial O :=
  let S := devQ (biRead F (composedKey T)) (biRead F f) j
  (Finset.range (S.natDegree + 1)).sum fun b =>
    (AdjoinRoot.modByMonicHom F.hmonic (S.coeff b)) * F.key ^ b

/-! ### NODE C.72 [theorem] — the floor and the faithful band [signed: A-C.1] -/

axiom shadow_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    (T.theta μ₂ j : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)

axiom shadow_faithful_band {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂)
    {m : ℕ} (hm : m < T.theta μ₂ j)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)

/-! ### NODE C.73 [def+theorem] — x-free genres and exactness [signed: A-C.1; the PRIMARY
clause is the definition; the `i(u₂(f₂−t)) = 0` test is the `f₁ = 1` companion ONLY] -/

def IsXFree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Prop :=
  ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 →
    (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
      (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))).natDegree = 0

axiom shadow_exact_of_xfree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hx : IsXFree T)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (j : ℕ) :
    shadowDev T f j = dev (composedKey T) f j

axiom isXFree_iff_slot_of_f1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h) (hf1 : F.f₁ = 1) :
    IsXFree T
      ↔ ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 → F.slotIdx ((T.f₂ - t) * T.u₂) = 0

/-! ### NODE C.74 [theorem] — the three TERMINAL layers [signed: A-C.1; `TouchCert` as the
exact-`Θ_j` nonvanishing of the key power's own read discrepancy] -/

def TouchCert {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ j : ℕ) : Prop :=
  dv2Hgt (T.levelDatum hπ)
      (shadowDev T ((composedKey T) ^ μ₂) j - dev (composedKey T) ((composedKey T) ^ μ₂) j)
    = (T.theta μ₂ j : ℕ∞)

axiom shadow_attained_of_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ j : ℕ} (hj : j < μ₂) (hc : TouchCert T hπ μ₂ j) :
    dev (composedKey T) ((composedKey T) ^ μ₂) j = 0 ∧
    dv2Hgt (T.levelDatum hπ) (shadowDev T ((composedKey T) ^ μ₂) j) = (T.theta μ₂ j : ℕ∞)

axiom shadow_persistence {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ j : ℕ} (hj : j < μ₂) (hc : TouchCert T hπ μ₂ j)
    {g : Polynomial O}
    (hbudget : ∀ j' a b : ℕ, j' < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j' a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) g j') b).coeff a)) :
    ((T.theta μ₂ j + 1 : ℕ) : ℕ∞)
        ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T g j - dev (composedKey T) g j) ∧
    dv2Hgt (T.levelDatum hπ)
        (shadowDev T ((composedKey T) ^ μ₂ + g) j
          - dev (composedKey T) ((composedKey T) ^ μ₂ + g) j)
      = (T.theta μ₂ j : ℕ∞)

axiom shadow_not_sigma_function {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (hnx : ¬ IsXFree T) {μ₂ : ℕ} (hμ₂ : 2 ≤ μ₂) :
    (∃ f g : Polynomial O, f ∈ towerLocus T μ₂ ∧ g ∈ towerLocus T μ₂ ∧
      typeOf f = typeOf g ∧ ∃ j < μ₂, shadowDev T f j ≠ shadowDev T g j) ∧
    (∃ f g : Polynomial O, f ∈ towerLocus T μ₂ ∧ g ∈ towerLocus T μ₂ ∧
      (∀ j < μ₂, shadowDev T f j = shadowDev T g j) ∧ typeOf f ≠ typeOf g)

/-! ### NODE C.75 [theorem] — the entry/event band is shadow-faithful [signed: A-C.1] -/

axiom entry_band_faithful {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {j : ℕ} (hj : j < μ₂) {m : ℕ} (hm : m ≤ (μ₂ - j) * T.E₂)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)

/-! ### NODE C.76 [lemma] — the level-2 datum at PARTIAL sides [signed: A-C.1; (a)+(b) with
the frame-opening hypothesis `hopen` (the left-endpoint pin); (c) IS C.47 (side-blind,
re-export); (d) at the frame-peel core] -/

axiom partial_floor_and_datum {F : KeyFrame O π} {H₀ : ℕ} (hpin : F.Pin H₀)
    (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) (hkey : ¬ F.key ∣ f)
    (hopen : (((f.natDegree / (F.e₁ * F.f₁)) * ((F.e₁ * F.f₁) * F.h) : ℕ) : ℕ∞)
      < dvHgt F f 0)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) (hdeg : 0 < dvSideDeg F f u ℓ hne) :
    ℓ * ((F.e₁ * F.f₁) * F.h) < u ∧
    ∀ (M₀ : ℕ) (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)),
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).coeff 0 ≠ 0 ∧
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree = dvSideDeg F f u ℓ hne

axiom partial_frame_peel {F : KeyFrame O π} {H₀ : ℕ} (hpin : F.Pin H₀)
    (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) (hdvd : F.key ∣ f)
    (hbox : ∀ g' ∈ monicFactors F.key, F.f₁ ∣ inertiaDegOf g') :
    typeOf F.key = ⟨{(F.e₁, F.f₁)}⟩ ∧ ¬ F.key ^ 2 ∣ f

/-! ### NODE C.77 [theorem] — bouquet + projection at partial sides [signed: A-C.1; (i) is
the C.33+C.34 chain (re-export); (ii) at the TOWERRAT2-C monic-signature core + the block
degree; the translation clauses are C.37/C.64's, already signed] -/

axiom partial_projection {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f) :
    (dev (composedKey T) f (f.natDegree / T.D₂)).Monic ∧
    ((T.D₂ ∣ f.natDegree) → dev (composedKey T) f (f.natDegree / T.D₂) = 1) ∧
    (blockFactor (T.levelDatum hπ) f).natDegree = T.D₂ * mult₂ (T.levelDatum hπ) f

/-! ### NODE C.78 [theorem] — the per-block decision from `f`'s OWN development
[signed: A-C.1; the reads are on `f`, never on the (unexhibited) block; (iv)'s recursion
routing = C.30, re-export] -/

axiom partial_block_decision {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (hcop₃ : Nat.Coprime u₃ ℓ₃) (hfloor₃ : ℓ₃ * T.E₂ < u₃)
    (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty)
    (hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃).Separable)
    {r₂ : Polynomial (AdjoinRoot (towerLabel T))} (hr₂m : r₂.Monic) (hr₂i : Irreducible r₂)
    (hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃) :
    ∃ g : Polynomial O, g.Monic ∧ g ∣ blockFactor (T.levelDatum hπ) f ∧
      g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
      ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
       (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
        typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)

/-! ### NODE C.79 [theorem] — the `μ₂* = 2` decision table [signed: A-C.1; the five rows as
an inductive case tag (GC-4's domain licence), σ per case, boxes inside] -/

inductive Mu2TwoCase where
  | twoSides : Mu2TwoCase
  | halfInteger : Mu2TwoCase
  | inertQuadratic : Mu2TwoCase
  | split : Mu2TwoCase
  | doubleRoot : Mu2TwoCase

axiom partial_mu2star_two_decision {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f)
    (hm2 : mult₂ (T.levelDatum hπ) f = 2)
    (hbox1 : ∀ g' ∈ monicFactors (blockFactor (T.levelDatum hπ) f),
      CBox1Side (T.levelDatum hπ) g') :
    ∃ c : Mu2TwoCase,
      ((c = Mu2TwoCase.twoSides ∨ c = Mu2TwoCase.split) →
        typeOf (blockFactor (T.levelDatum hπ) f)
          = ⟨{(F.e₁ * T.e₂, F.f₁ * T.f₂), (F.e₁ * T.e₂, F.f₁ * T.f₂)}⟩) ∧
      (c = Mu2TwoCase.halfInteger →
        typeOf (blockFactor (T.levelDatum hπ) f)
          = ⟨{(2 * (F.e₁ * T.e₂), F.f₁ * T.f₂)}⟩) ∧
      (c = Mu2TwoCase.inertQuadratic →
        (∀ g' ∈ monicFactors (blockFactor (T.levelDatum hπ) f),
          (F.f₁ * T.f₂ * 2) ∣ inertiaDegOf g') →
        typeOf (blockFactor (T.levelDatum hπ) f)
          = ⟨{(F.e₁ * T.e₂, 2 * (F.f₁ * T.f₂))}⟩) ∧
      (c = Mu2TwoCase.doubleRoot →
        ∃ (lam : ℕ) (s : AdjoinRoot (towerLabel T)), T.E₂ < lam ∧ s ≠ 0 ∧
          ∃ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty,
            dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
              = (Polynomial.X - Polynomial.C s) ^ 2)

/-! ### NODE C.80 [theorem] — the tie at pure-power sides, unconditional [signed: A-C.1;
the mixed case routes to C.67 by name] -/

axiom tie_pure_power {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f)
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
        dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp
          = Polynomial.C c * (towerLabel T) ^ μ₂) :
    mult₂ (T.levelDatum hπ) f = μ₂ ∧
    (blockFactor (T.levelDatum hπ) f).natDegree = T.D₂ * μ₂

/-! ### NODE C.81 [theorem] — the `c_g`-read [signed: A-C.1; the right-endpoint identity +
the floors visible through the projection] -/

axiom cg_read {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f)
    (hnd : ¬ composedKey T ∣ blockFactor (T.levelDatum hπ) f) :
    dv2Pin (T.levelDatum hπ) (composedKey T) f (mult₂ (T.levelDatum hπ) f)
      = (complementConst (T.levelDatum hπ) f : ℕ∞) ∧
    ∀ j, j < mult₂ (T.levelDatum hπ) f →
      (((mult₂ (T.levelDatum hπ) f - j) * T.E₂ + 1
          + complementConst (T.levelDatum hπ) f : ℕ) : ℕ∞)
        ≤ dv2Pin (T.levelDatum hπ) (composedKey T) f j

/-! ### NODE C.82 [theorem] — block budgets through the projection (BUDGET half ONLY; the
LEDGER/COUNT half stays §11's — the corpus's own fence) [signed: A-C.1] -/

axiom block_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hctx : BlockContext (T.levelDatum hπ) f)
    (hnd : ¬ composedKey T ∣ blockFactor (T.levelDatum hπ) f) (N : ℕ) :
    Nat.card {c : Coeff O (T.D₂ * mult₂ (T.levelDatum hπ) f) N //
        ∃ a : Fin (T.D₂ * mult₂ (T.levelDatum hπ) f) → O,
          proj O (T.D₂ * mult₂ (T.levelDatum hπ) f) N a = c ∧
          monicPoly a ∈ towerLocus T (mult₂ (T.levelDatum hπ) f)}
      = residueCard O ^ towerFreeCount T (mult₂ (T.levelDatum hπ) f) N

/-! ## A-C.1 §9 — THE THIRD STAGE (C.84–C.93, C.95, C.96) -/

/-! ### NODE C.84 [def+lemma] — the level-`i` weight and the flavor lifts [signed: A-C.1;
`towerWeight`/`flavorMonomial` real; `towerLift` stub-carried as an axiom constant (the
multi-index digit iteration is the fleet's body) with the height clause signed] -/

def DeepTower.towerWeight {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i v a : ℕ) (J : ℕ → ℕ) : ℕ :=
  W.ehat i * v + a * (W.ehat i / W.e 1) * W.u 1
    + (∑ j ∈ Finset.Icc 1 (i - 1), J j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
    + J i * W.Econst i

noncomputable def DeepTower.flavorMonomial {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} (W : DeepTower F H₀ hpin r) (key : ℕ → Polynomial O)
    (i rr : ℕ) (t : ℕ → ℕ) (m : ℕ) : Polynomial O :=
  let Δ := F.e₁ * rr * (W.ehat i / W.e 1) * W.u 1
    + ∑ j ∈ Finset.Icc 1 (i - 1), W.e (j + 1) * t j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1)
  let p := W.towerNorm (i - 1) (m - Δ)
  Polynomial.C (π ^ p.1) * Polynomial.X ^ (p.2.1 + F.e₁ * rr)
    * ∏ j : Fin (i - 1), (key (j.1 + 1)) ^ (p.2.2 j + W.e (j + 2) * t (j + 1))

axiom DeepTower.towerLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (key : ℕ → Polynomial O) (i m : ℕ)
    (s : W.fld i) : Polynomial O

/-! ### NODE C.85 [theorem] — the graded frame and the substitution theorem [signed: A-C.1;
**A0 DROPPED per the node's own ⚠ DECISION note** ("A0 is scaffolding, not consumed
content" — the recorded formalizer option, exercised); A1 at the C-carrier
multiplicativity-defect form; (A)'s Step A as the binomial-free ring identity — the grid
leg is C.56's `refine_kills`, already signed] -/

axiom theta_dictionary {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)] :
    ∃ θ : ℕ → AdjoinRoot (T.levelDatum hπ).r,
      θ 0 = 1 ∧ θ 1 = 1 ∧ (∀ t, θ t ≠ 0) ∧
      ∀ (s t : ℕ) (A B : Polynomial O),
        dv2Res (T.levelDatum hπ) A ≠ 0 → dv2Res (T.levelDatum hπ) B ≠ 0 →
        θ (s + t) * dv2Res (T.levelDatum hπ) (A * B)
          = θ s * θ t * (dv2Res (T.levelDatum hπ) A * dv2Res (T.levelDatum hπ) B)

axiom substitution_kills {R : Type*} [CommRing R] (μ : ℕ) (s : R) :
    ((Polynomial.X - Polynomial.C s) ^ μ).comp (Polynomial.X + Polynomial.C s)
      = Polynomial.X ^ μ

/-! ### NODE C.86 [lemma] — GENTOW-2 at general `μ₂` + the level-1 rider [signed: A-C.1;
(i) is C.56/C.57's re-export at general `μ₂` (their signatures already quantify `μ₂`);
(ii) the rider as a REAL level-1 theorem over B's API] -/

axiom substitution_kills_level1 (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ lam : ℕ} (hμ : 0 < μ) (hlam : 0 < lam) {s : resField φ} (hs : s ≠ 0)
    (hne : (sideSet φ f lam 1).Nonempty) {H₀ : ℕ}
    (hp : npHgt φ f (sideMin φ f lam 1 hne) = (H₀ : ℕ∞))
    (hres : resPoly π φ f lam 1 hne H₀ = (Polynomial.X - Polynomial.C s) ^ μ) :
    ∃ φ' : Polynomial O, φ'.natDegree = φ.natDegree ∧
      (φ - φ').natDegree < φ.natDegree ∧
      ∀ j < μ, (((μ - j) * lam : ℕ) : ℕ∞) < npHgt φ' f j

/-! ### NODE C.87 [lemma] — GENTOW5-D TERMINAL, forward direction ONLY [signed: A-C.1; the
two displayed carry computations, uniform in `j`; **NO two-directional statement exists —
S11.1's withdrawal honored** (a stub matching the withdrawn closure is a defect)] -/

axiom towerCarry_interior_strict {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i j : ℕ) (hj : 1 ≤ j) (hji : j + 1 < i) (hir : i ≤ r) :
    (W.e (j + 1) * W.f (j + 1)) * ((W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
      < (W.ehat i / W.ehat (j + 2)) * W.u (j + 2)

axiom towerCarry_top_exact {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
    (W.e i * W.f i) * ((W.ehat i / W.ehat i) * W.u i) = W.Econst i

/-! ### NODE C.88 [theorem] — `(SLOT_i)`/`(LIFT_i)` up the tower [signed: A-C.1, in norm
form over the interface (C.27's carrier iterated); `boundRec` the companion] -/

def boundRec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) : ℕ → ℕ
  | 0 => 0
  | 1 => (F.e₁ * F.f₁ - 1) * F.h
  | (i + 2) => (W.e (i + 2) * W.f (i + 2) - 1) * W.u (i + 2) + W.e (i + 2) * boundRec W (i + 1)

axiom tower_slot_exact {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {β : ℕ} {C : Polynomial O} (hg : I.ExactGrade β C)
    (hdeg : C.natDegree < e' * f' * W.Dcum r)
    {g : Polynomial O} (hgm : g.Monic) (hKP : I.KP g)
    (hgdeg : g.natDegree = e' * f' * W.Dcum r) :
    (W.ehat r * e') * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat
      = g.natDegree * β

axiom tower_lift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (k : ℕ) (hk : boundRec W r < k) (s : W.fld r) (hs : s ≠ 0) :
    ∃ C : Polynomial O, C.natDegree < W.Dcum r ∧ I.ExactGrade k C ∧ I.Rgr k C = s

/-! ### NODE C.89 [def+lemma] — the `𝒲` HYPOTHESIS FAMILY [signed: A-C.1; the single-`w`
form in the RATIO carrier; (i) the `i = 2` discharge from C.99; (ii) the `i = 1` SHAPE with
the tie OPEN; (iii) `i ≥ 3` OPEN — no axiom asserts it, the definition IS the carrier] -/

def GENTOW5W {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u') : Prop :=
  ∃ w : W.fld r, w ≠ 0 ∧ ∀ t, t < f' →
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = w ^ (f' - t)

def Wle {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') (n : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ n → ∀ hi : i ≤ r, GENTOW5W (W.trunc i hi) e' f' u' (I i hi)

axiom gentow5w_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower F H₀ hpin 2) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 2 < u') :
    GENTOW5W W e' f' u' I

axiom gentow5w_one_shape {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower F H₀ hpin 1) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 1 < u') :
    ∃ k : ℕ, ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (I.chainNorm 1 ((f' - t) * u')) * I.thetaRatio (f' - t)
        = (I.letterZ 1 ^ k) ^ (f' - t)

/-! ### NODE C.90 [theorem] — GENTOW5-B (a): the key certificate at the three-regime scope
[signed: A-C.1 at clause (a); **clause (b) — the level-general one-sidedness — is the
BOOKED C.92 residual field (published Cor 6.3)**, recorded there and here] -/

axiom gentow5_key_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u')
    (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (hW : Wle W e' f' u' I r) (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (Φnext : Polynomial O) (hmon : Φnext.Monic)
    (hdeg : Φnext.natDegree = e' * f' * W.Dcum r)
    (ψ' : Polynomial ((W.trunc r le_rfl).fld r)) (hψm : ψ'.Monic) (hψd : ψ'.natDegree = f')
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f') :
    (I r le_rfl).KP Φnext ∧
    ∃ w : (W.trunc r le_rfl).fld r, w ≠ 0 ∧
      (I r le_rfl).Rres Φnext = wconj w ψ'

/-! ### NODE C.91 [theorem] — budgets/transfer/self-feeding floor [signed: A-C.1 at (d)+(e);
**(c) — the level-(i+1) entry characterization — BOOKED** (it needs the level-(i+1)
`dv`-carrier, the same §9-scope residual as C.90(b)/C.102's; recorded in the delta block)] -/

axiom gentow5_selffeed (P : ℕ → ℕ∞) (μ E : ℕ) (hμ : 0 < μ)
    (hpins : ∀ j < μ, (((μ - j) * E + 1 : ℕ) : ℕ∞) ≤ P j) (htop : P μ = (0 : ℕ∞))
    {u ℓ j : ℕ} (hℓ : 0 < ℓ) (hside : hOnSide P μ u ℓ j) :
    ℓ * E < u

/-! ### NODE C.93 [lemma] — threshold arithmetic + the `HYP.82` census [signed: A-C.1] -/

axiom tower_first_live (r μr : ℕ) (hr : 1 ≤ r) (hμ : 2 ≤ μr) (l : ℕ → ℕ)
    (hl : ∀ i, 1 ≤ i → i ≤ r → 2 ≤ l i) (D : ℕ) (hD : D = ∏ i ∈ Finset.Icc 1 r, l i) :
    2 ^ (r + 1) ≤ D * μr

section C93Census
#check @towerLocus_iff_budget   -- item (1): GENTOW-1
#check @refine_invariants       -- item (2): GENTOW-2
#check @shadow_floor            -- item (3): GENTOW-3
#check @partial_floor_and_datum -- item (4): GENTOW-4
#check @window_band1            -- item (5): GENTOW-5 (core)
#check @towerLocus_depth3_floor -- item (6)(β): DISCHARGED into (1)
#check @gentow5_key_certificate -- item (6)(α): depth-3 scope, 𝒲-conditional
end C93Census

/-! ### NODE C.95 [theorem] — the 𝒯-free cap + the attainment certificate [signed: A-C.1;
the cap at the PE2-F-2 corrected-codomain core; the certificate at its PINNED scope
(`f₁ = 1, μ₂ = 2`) with the 6.3′ `f₁ ≥ 2` variant separate] -/

axiom cap_free {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {f : Polynomial O} (hf : f.Monic)
    (hcond : f.natDegree % T.D₂ ≠ T.D₂ - 1) {j : ℕ} (hj : f.natDegree / T.D₂ < j) :
    dev (composedKey T) f j = 0 ∧ shadowDev T f j = 0

axiom attainment_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hf1 : F.f₁ = 1)
    {f : Polynomial O} (hf : f ∈ towerLocus T 2) (hnx : ¬ IsXFree T)
    {j : ℕ} (hj : j < 2) (hc : TouchCert T hπ 2 j) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)
      = (T.theta 2 j : ℕ∞)

axiom attainment_certificate' {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hf1 : 2 ≤ F.f₁)
    {f : Polynomial O} (hf : f ∈ towerLocus T 2) (hnx : ¬ IsXFree T)
    {j : ℕ} (hj : j < 2) (hc : TouchCert T hπ 2 j) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)
      = (T.theta 2 j : ℕ∞)

/-! ### NODE C.96 [theorem] — GENTOW6-BOX-1's closure at `f₁ = 1`, IF direction ONLY
[signed: A-C.1; the "iff" is WITHDRAWN — no converse statement exists] -/

axiom box1_attainment_if {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hf1 : F.f₁ = 1)
    {μ₂ : ℕ} (hμ₂ : 3 ≤ μ₂)
    (hbin : ¬ (ringChar (ResidueField O) ∣ Nat.choose μ₂ 2))
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (hnx : ¬ IsXFree T)
    (tstar : ℕ) (htstar : tstar < T.f₂ ∧ T.ψ₂.coeff tstar ≠ 0) :
    dv2Hgt (T.levelDatum hπ)
        (shadowDev T f ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂))
          - dev (composedKey T) f ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂)))
      = (T.theta μ₂ ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂)) : ℕ∞)

/-! ### NODE C.106 — the §10 supply manifest (documentation node: the `#check` suite) -/

section C106Manifest
#check @gentow2_Bpp        -- B″ = C.99 (ratio form)
#check @theta_letter_valued
#check @gentow2_Bp         -- B′ = C.100, direction FGMN = u · repo, never inverted
#check @gentow2_B          -- B-law + prescription = C.101
#check @s2Witness          -- the S2 witness = C.97
#check @shear_onesided_iff -- the shear = C.98
#check @letter_formula     -- C.102
#check @gentow2_A          -- the certificate = C.103
#check @repoRead           -- the reads/naming = C.104
#check @wconj_invariants   -- w-blindness = C.105
end C106Manifest

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

def budgetFloorN (e₁ e₂ E₂ μ₂ j w : ℕ) : ℕ :=
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
#eval (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 0)
#eval (List.range 4).map (fun j => budgetFloorN 3 2 12 3 j 0)
-- ⚠ C-H12's coincidence regime, live right here: at `w = 0` the two frames give the SAME row
-- `[7,5,3,1]`, so a gate that checked only `w = 0` would be blind to the frame. At `w = 5` they
-- separate (`[5,3,1,0]` vs `[6,4,2,0]`). This is the G.23 lesson at chapter C's own budget table.
#eval (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 5)
#eval (List.range 4).map (fun j => budgetFloorN 3 2 12 3 j 5)

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

/-! ### A-C.1 GATE HYGIENE (D14/D15/D22 cures) — NODES C.123/C.124's MACHINE-FORM
EXPECTED-VALUE TABLES, the HT reading DECIDED, and the discriminating third frame.

**D15 RESOLVED against `EFF.W12.87`** (its finding-1 record, verbatim: *"the
H = (1) → SPLITEQ(k = 2) count `(q−1)·((q−1)(q−2)/2)·q^{2N−8}` re-derived from the lemma
display"* — W12-L0's `(q−1)^t` history prefactor IS in the count): the FULL-coefficient
reading `htSpot` is the source's; C.124's `2·1/2` is the MIDDLE factor `(q−1)(q−2)/2`
evaluated at `q = 3`, so the two gate texts AGREE (`2·3^{2N−8}`) and `htSpotAlt` is DEAD.
The `q = 3` witness decides (both vanish at `q = 2`). -/

/-- C.123's machine-form expected values (`q = 2`). -/
def gateC_q2_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q2_budget_w5 : List ℕ := [5, 3, 1, 0]
def gateC_q2_nodeFloors : List (List ℕ) := [[21, 11], [29, 15], [13, 7]]
def gateC_q2_E2_splits : List (ℕ × ℕ) := [(10, 8), (14, 8), (6, 4)]
def gateC_q2_s2Ladder : List ℕ := [4, 10, 21]
def gateC_q2_htSpot : ℕ := 0    -- the degenerate census at q = 2, every N

#guard (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 0) == gateC_q2_budget_w0
#guard (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 5) == gateC_q2_budget_w5
#guard gateC_q2_E2_splits.all (fun p => p.2 < p.1)
#guard (List.range 12).all (fun N => htSpot 2 N == gateC_q2_htSpot)

/-- C.124's machine-form expected values (`q = 3`). -/
def gateC_q3_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q3_budget_w5 : List ℕ := [6, 4, 2, 0]
def gateC_q3_htSpot_atN6 : ℕ := 2 * 3 ^ 4   -- D15 DECIDED: the full-coefficient reading

#guard (List.range 4).map (fun j => budgetFloorN 3 2 12 3 j 0) == gateC_q3_budget_w0
#guard (List.range 4).map (fun j => budgetFloorN 3 2 12 3 j 5) == gateC_q3_budget_w5
#guard htSpot 3 6 == gateC_q3_htSpot_atN6
#guard htSpotAlt 3 6 ≠ gateC_q3_htSpot_atN6   -- the DEAD reading, kept as the negative control

/-! **D22 cure — the discriminating THIRD frame.** C.123/C.124's frames give the IDENTICAL
`w = 0` budget row `[7,5,3,1]` (the C-H12 coincidence). The third frame
`(e₁, e₂, E₂) = (2, 1, 10)` separates at `w = 0` from BOTH — a gate row that includes it is
frame-sensitive even at `w = 0`. -/
def gateC_frame3_budget_w0 : List ℕ := [16, 11, 6, 1]
#guard (List.range 4).map (fun j => budgetFloorN 2 1 10 3 j 0) == gateC_frame3_budget_w0
#guard gateC_frame3_budget_w0 ≠ gateC_q2_budget_w0

end NumericGate

end LeanspecC

/-
RESUME (chapter-C leanspec, 2026-08-16, POST-A-C.1): the stub gate's five NEXT ACTIONS are
EXECUTED by amendment A-C.1 (this file + the blueprint's A-§ items (a)–(m) + CHAP-I's
2026-08-16 addendum):
 1. D21 — DONE (jump_drop re-signed, source-verified at EFF.HE6R1.10; refutation record
    preserved in the numeric section).
 2. §§6(tail)–13 — SIGNED (the A-C.1 SIGNATURE-COMPLETION LAYER; §15's gate order (a)–(d)
    is now satisfiable; every signature elaborates in this file).
 3. D19/D20 — RESOLVED (NODE C.14a: the adapter with the corpus preconditions explicit;
    C.14 re-signed with `1 ≤ F.h`; H's landed side untouched).
 4. D24 — BROKEN on the C side (DescentState/DescentStep/NS7TerminationStatement +
    agnprw_termination; I.01 unblocked, see CHAP-I's addendum).
 5. D3–D18 mechanical cures — ALIGNED into the blueprint's signed half (A-C.1(m)).
STILL OWED (the fleet/owner handoff):
 a. OWNER (gate (b) statement inspection): fgmn_residual_mul (C.66), FGMNCalculus +
    fgmn_calculus_exists (C.92), agnprw_termination (C.94) — category-signed by append #66,
    statements drafted at A-C.1, per-statement inspection queued in CHAP-I's addendum;
    plus C.102's ℓ₁ = e₂ exponent reading (flagged) and the two residual print-reads of
    the A-3 audit §7.
 b. FLEET (the four BOOKED residuals): C.90(b)'s level-general one-sidedness (published
    Cor 6.3 — the C.92 residual field), C.91(c)'s entry characterization, C.102's
    letter-read field, C.58's (b)/(d)/(e) companions.
 c. ORCHESTRATOR: wire this file into leanspec/Leanspec.lean; PROJECT_STATE append #66's
    "on file" sentence is corrected by CHAP-I's addendum (D23) — mirror it in
    PROJECT_STATE at the next append; §14's DAG TSV gains C.14a/C.38a rows at re-harvest.
`lake build Leanspec.ChapC` green; zero `sorry`; every #guard passing.
-/
