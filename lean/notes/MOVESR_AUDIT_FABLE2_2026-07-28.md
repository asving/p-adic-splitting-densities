# MovesR Lean blueprint REV 3 — fresh-instance CONFIRMATION audit (Fable #2)

DATE: 2026-07-28 · AUDITOR: fresh Fable instance #2 (no prior MovesR context; not
the rev-2 auditor) · SCOPE: confirmation audit of
`MOVESR_LEAN_BLUEPRINT_2026-07-28.md` REV 3 (1058 lines, read in full), parallel
to the Codex confirmation pass; charge = `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`
(<CORPUS> = MovesR, <NOTE> = §R-LEDGER) + addenda (statements-only corpus, vacuity
= typing; FF1–FF7 repair verification, FF1 leg-by-leg against the §C display).
GROUND TRUTH: `MOVES_2026-07-24.md` 9290–9763 (§R-LEDGER rev 5) read in full;
Lemma LST's §C display located and read at 3728–3781 with surrounding §C context
(Lemma DOM close 3707–3726, Lemma TYP 3783–3831 for the in_γ/graded-piece
consumption). D8 imports verified against the Lean sources:
`Moves/DefsT.lean` (`DigitSystem`, `IsSolution` — digit-polymorphic, instantiable
at ↥(Fsub p δ)), `MovesC/Defs.lean` (`CoordPrec` on ℕ×ℕ, `IsUnitriangular`
`[Add R]`-polymorphic on `(Fin m → R) → (Fin m → R)`, `Line`,
`DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop` with
steeper/vertex_entry). The blueprint's prose was treated as claims, not evidence.
Nothing was fixed.

## 0. FF1–FF7 repair verification (against `MOVESR_AUDIT_FABLE_2026-07-28.md`)

**FF1 (crit → GENUINE), checked leg by leg against the §C display (3735–3749),
not the blueprint's summary.** The rev-2 count-stabilization Prop is gone (no
trace anywhere in rev 3); `lst` (blueprint 487–495) now types Lemma LST's three
legs over new carriers `ht/blkOf/floorC/floorB/interiorB/floorSet/wSlot`
(blueprint 429–437):
- Leg (i) TYPING. Display: "w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y_{(b,l)} ≠ 0}
  (the iterated slot-minimum)" (3738–3739). Blueprint: `K.wSlot H B x =
  (Finset.univ.filter fun i => K.blkOf H i = B ∧ x i ≠ 0).inf fun i => …ht…` —
  the slot-minimum of the absolute height over exactly the block's nonzero
  digits; `WithTop ℚ` handles the empty (all-zero) block as ⊤. MATCHES. The
  display's flanking clauses — "ht(b, l) is the K1-chain weight of the
  coordinate's basis monomial" and "in_γ(B) is a function of exactly the LEVEL
  SET L_γ(B)" (3736–3742) — reference K1-chain weights, basis monomials
  p^l·∏Φ̂_r^{…}, and D.3(e)(i) graded pieces, none of which exist in Lean; they
  are fenced with an explicit record (docstring "The K1-chain/in_γ graded
  internals stay §C-side (same fence as §B1's)"; §3 widening (iv) rewritten).
  This is exactly the rev-2 auditor's sanctioned repair shape ("retype … as the
  typable residue of Lemma LST's actual head", fence the internals citing the §C
  display).
- Leg (ii) FLOOR CONSTANCY ON THE INTERIOR. Display: "F_i(b) = old_i(slot(b)):
  ht-constant on each current block" on the factor interior (3743–3745).
  Blueprint: `∀ i, K.interiorB H (K.blkOf H i) → K.floorC H i = K.floorB H
  (K.blkOf H i)` — per-coordinate floor = per-block floor on factor-interior
  blocks, hence constant per block. MATCHES (floorB is the typed stand-in for
  old_i(slot(·)); the identification of floorB with the line object is §C-side
  DOM content, covered by widening (v), which lists floors explicitly).
- Leg (iii) SELECTION. Display: "for a factor-interior slot coefficient B with
  γ' > old_i(slot(B)), the ENTIRE level set L_{γ'}(B) lies strictly above the
  floor downset {ht ≤ F_i}" (3746–3749); proof residue "the floor downset on the
  block is {ht ≤ F_i}: disjoint" (3776–3777). Blueprint: `K.floorSet H B =
  {i | K.blkOf H i = B ∧ K.ht H i ≤ K.floorB H B}` (the engine's downset IS the
  ht-downset) `∧ ∀ γ' > floorB, ∀ i, blkOf i = B → ht i = γ' → i ∉ floorSet H B`
  (every member of the block's weight-γ' level set avoids it). MATCHES,
  including the guard γ' > old_i(slot(B)) ↦ `K.floorB H B < γ'` (legitimate via
  leg (ii)'s constancy under the same interior guard). The display's "selects
  the whole weight-γ' level set" clause consumes in_γ (TYP(c)) and sits under
  the same recorded fence.
  The rev-2 stabilization reading is correctly recorded as refuted/withdrawn
  (D4, §3(iv), §5). VERDICT: genuine repair, no silent weakening.

**FF2 (crit → GENUINE).** The free `count` field is DELETED from `REL1Counting`
(382–393 has no count field); `ReBased.count` (443–445) is DEFINED as
`Nat.card {W // ∃ f ∈ K.SHZ H Z, W = cyl p δ N f}` — literally the rev-2
finding's suggested pin — and `REL1b` (507–512) consumes the definition. The
finding's lawful-junk family (count := q^{nN} unrelated to any classifier) is
dead; surviving degenerate instances (full locus via unpinned digitLocus +
thmCa) are the honest-trivial perimeter the rev-2 auditor pre-approved. The
"classes MEETING the locus" reading is disclosed in the docstring and coincides
with the display's LHS on every instance where the display is meaningful
(level-N saturation, REL.1's own content). Genuine.

**FF3 (gap → GENUINE).** `c05PinWelldef` (468–470) gains the second leg:
`(K.pinnedIn H F Z).val.map (K.aDim H) = (K.pinnedIn H F' Z).val.map (K.aDim H)`
— frame-invariance of the pinned aDim-multiset, exactly the rev-2 finding's
"minimally, invariance of the multiset {aDim H i : i ∈ pinnedIn}" — typing BOTH
legs of "cardinality-and-status statistics" (note 9371–9373). The card conjunct
is entailed by the multiset conjunct (map preserves card) — redundant, harmless.
Genuine.

**FF4 (gap → GENUINE).** `ReBased` is now parameterized by (Sp, AD) and carries
`posOfDigit : (H) → Fin (mOf H) → AD.Pos` + `aDim_eq : aDim H i = AD.aDim δ
(posOfDigit H i)` (422–423) — the requested digit-position → Pos assignment with
agreement law; c1's exponents (474) now ARE (EQ-2)'s per the note's "|𝔸_δ| =
p^{a_δ} per (EQ-2)'s re-based-span definition" (9374–9375); EQ2law now speaks
about the exponents c1 consumes. Genuine.

**FF5 (gap → GENUINE), all three sites.** (i) REL2a gains `prodEvents` +
`prodCyl_mem` (finite-coordinate digit cylinders present) + `domIdent_meas`
(bidirectional event-algebra compatibility — the correct reading of an
identification "as a MEASURABLE product", note 9453–9455). (ii) REL2b (603–608)
gains the conjunct `(Θ ∘ domIdent) ⁻¹' W ∈ S.AmbEvents` — the Θ-measurability
half of the pushforward display (9482–9484). (iii) `massEqEntry` (707) and
`SIBOdelta` (740) both require the realization event ∈ `RB.C.V.events`, so V's
measure laws bind where "the right side a REL.1-theory mass" is asserted.
Genuine at all three sites.

**FF6 (gap → GENUINE).** `massEqEntry` (704–709) is retyped on
`RB : ReBased p Sp AD S.δabs A.dRel` and conjoins `REL1 p Sp AD S.δabs A.dRel RB`
— the F10 `_linked` pattern the rev-2 finding asked for; the vol is `RB.C.V.vol`,
never a free BoxVol. This matches (e3)'s "IS the REL.1 mass" (9516–9518) and the
note's blanket "EVERY consumer below is conditional on REL.1, displayed per
site" (9418–9419). Genuine.

**FF7 (gap → GENUINE).** (a5) gains `ambT_unitri` (CoordPrec-anchored on the
free (ℓ,i)-coordinates — exactly the rev-2 finding's requested anchor: the
offset at a coordinate depends only on strictly ≺-earlier coordinates) AND
`tgtT_unitri` (Fin-order unitriangularity on the target coefficient box). D7's
false "law fields make junk inhabitants impossible" claim is withdrawn and
replaced by the accurate free-data-relativity statement; §3 widening (v) records
the residue (transports, trees, reads, floors). I verified the target-side law
is satisfiable by the intended objects: substitution-type transports are
coefficient-polynomial maps whose offset at coefficient j depends only on
C.0-earlier (higher-index) coefficients, so with the declared top-down Fin
enumeration `tgtT_unitri` holds of them — the law is an anchor, not an
over-strengthening. Genuine.

No repair regressed a previously-clean unit (checked: R1–R11, R13–R23 statements
against their rev-2-audited forms and the note displays; the (Sp, AD)
parameterization threads consistently through REL1/REL2b_linked/massEqEntry/
SIBOdelta).

## 1. Fresh sweep (whole blueprint, rev 3 as a new text)

- R1–R5: base-index convention faithful (`relExt := O(m·δ')` sanctioned by
  "bookkeeping inside W(F̄_p)"; `cyl` = first-N Witt-coefficient agreement is
  "f mod p^N" over a perfect residue field; `qq_mul`/`βarg_eq` = the pool-size
  law and (e2), 9437–9438/9514–9515). Clean.
- R6: the card fact of "F_m is THE subfield of order p^m" (9425–9426), frozen
  provable unit. Clean.
- R7/R8: SETTING (9429–9438) absorbed into carriers-with-laws (recorded widening
  (i)); `δabs = δ·δrel` absolute; SettingsFamily = nonempty + root δ=1 + typed
  descent closure with `desc_amb : S'.δ = S.δabs` — the recursion clause's
  family half (9622–9627). Clean.
- R9: TowerData/BaseLaws/ClimbLaws = (R0-tower)'s displayed residue-tower
  content (F₁ = F_δ[x]/(φ̄), F_{k+1} = F_k[z]/(ψ_k) over the ACTUAL stage
  carriers — "built afresh" carried by the typing); StageCarrierLaws = §B1's
  typable residue, fence recorded. Clean.
- R10: BoxVol pins cylinder masses to (q_δ^{nN})⁻¹ per (R0-box) 9336–9343. Clean.
- R11/R12/R13: (REL.1-b) transcribed exactly (range (k+1), q_δ^{nN},
  ∀ N ≥ N(H,Z)) over the DEFINED count; ten clause fields = the note's clause
  list 9380–9381 (secA, secB1, secB2def, thmCa, c05PinWelldef, c1, c15ZC, lst,
  typ, dom — count verified = 10, C(b) = REL1b separately); `typ` = walk item
  (i)'s retyping verbatim (additive only, 9401–9407); `dom` = MovesC's DomData
  interface (the base-free "valuation geometry … carries over as written",
  9387–9390); c1 = (R0-ledger)'s per-constrained-digit (p^{a_δ})⁻¹ product.
  Clean.
- R14–R17: six (a)-items typed incl. the FF5(i)/FF7 additions; REL2b + guard =
  the note's own proviso (9476–9478); EQ3 = alias ("REL.2(b) verbatim", 9589);
  REL2d square + specified word/reads/verdict/posOf correspondence (9494–9507);
  REL2e (e1)–(e5) with entryFirst fixed, consumed nonempty, determines =
  singleton class, e4agrees parameterized on [3]'s exported convention,
  firstIdxCandidate named and asserted nowhere (9508–9531). Clean.
- R18–R21: EQ1 finite-syntax invariant (menu Finset, PREDICTED, hypothesis-side);
  EQ2 = unconditional span definition (card_eq) + Stable DEFINED from posLetter
  + EQ2law on the pinned per-position-class domain (the F₉ instance correctly
  not typed); EQ2law_card provable from card_eq + hypothesized law. Clean.
- R22/R23: SIBOdelta = realized-family quantifier, positive-cell guard,
  ∃-composition WITH the REL1 conjunct, event-typing + pricing verbatim
  (9613–9627); O_chain = the ring half of the recursion clause. Clean.
- Non-units (D6): REL.3 honest absence (9641–9646 "no theorem statement is
  possible here"); REL.2(c) nowhere re-stated (no ⋂/∏ anywhere — the (SIB)
  product law stays at §T.3); REL-n4 census-side; PREDICTED brackets doc-comment
  only. No axioms; no kernel discharged; every named kernel (REL1, REL2b, e3/e4/
  e5, EQ1, EQ2law, EQ3, SIBOdelta) is a hypothesis-side Prop, none proved, none
  strengthened into a definition. Hypothesis fidelity holds.
- D8 imports: verified against the sources (see header) — all four reuse targets
  exist with compatible polymorphic types; no semantic mismatch found at
  blueprint level.

## 2. Findings

None counted. Uncounted observations (each checked and judged non-findings):

- (obs-1) EQ2law types only the a_δ = δ·a conjunct of (EQ-2)'s prediction; the
  "re-based piece maps are F_δ-linear" conjunct is about engine maps that do not
  exist in Lean, and the note's OWN status lines (9587–9588, R.5 9738–9739) name
  the open kernel exactly as "the a_δ = δ·a law". The docstring quotes the full
  display. Faithful to the note's own naming of the kernel; not a silent drop.
- (obs-2) `ReBased.count` counts cylinder classes MEETING the locus; contained-
  vs-meeting coincide exactly where the display's LHS is well-defined. Disclosed
  in the docstring. Definitional disambiguation, not a weakening.
- (obs-3) p-threading nits (`Setting` uses no p-mentioning field yet is written
  `Setting p`; `E.determines p`; `S.βarg p`) — E-phase syntax under the
  skeleton's statement fence, same disposition as the rev-2 audit's.
- (obs-4) AlphabetData's Carrier has no CharP p; a card_eq-lawful inhabitant
  could be a non-elementary p-group. Law-respecting junk of exactly the kind
  widening (v) records; the typed laws (0, +, p-power card) are the note's
  unconditional part.
- (obs-5) The tgtT_unitri docstring's phrase "the target's C.0-order digit
  coordinates" is loose (Fin dRel indexes coefficients, not digit coordinates);
  the typed law itself is the correct coefficient-granularity residue and is
  satisfiable by the intended transports (checked, FF7 above).
- (obs-6) In `lst`, leg (i) is quantified over all B : ℕ (junk block numbers get
  wSlot = ⊤ by the empty inf) and leg (iii)'s disjointness conjunct is entailed
  by its downset-equation conjunct — both harmless in a hypothesis package,
  mirroring the display's own derivation order.
- (obs-7) TowerData/ReBased docstrings carry no explicit inhabitation-story
  sentence; the story lives at the consumer site (REL1's "the carrier package
  the pass must supply") and in D2/D9. Within D9's stated policy.

## 3. Counts and verdict

FF1–FF7: all 7 verified GENUINE (FF1 leg-by-leg against the §C display at MOVES
3728–3781, per the charge). Codex F1–F21 repairs spot-checked where rev 3
touched them: no regression. Fresh sweep: 0 CRITICAL / 0 GAP; 7 uncounted
observations above, none rising to the charge's classification bar.

**ACCEPT**

(Statements-only corpus: acceptance is of the STATEMENT layer only — 16
statement units + 7 provable units, no kernel discharged, statement fence in
force for E-phase. Next gate per the blueprint: the parallel Codex confirmation,
then E-phase.)
