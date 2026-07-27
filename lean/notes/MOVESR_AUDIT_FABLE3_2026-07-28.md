# MovesR blueprint REV 4 — fresh-instance CONFIRMATION AUDIT (Fable #3)

DATE: 2026-07-28 · AUDITOR: fresh Fable #3 (no prior contact with any MovesR revision)
SCOPE: rev-4 re-architecture confirmation — the CInterface (GradedCarrier + eleven §C
statement defs + CStatements/REL1), run in parallel with Codex on the identical text.
CHARGE: `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` checklist; <CORPUS> = MovesR
(statements-only: vacuity = typing); <NOTE> = §R-LEDGER.
GROUND TRUTH READ IN FULL: `MOVES_2026-07-24.md` 9290–9763 (§R-LEDGER rev 5) and the
§C displays 3600–3834 (Lemma DOM 3644–3726, Lemma LST 3728–3781, Lemma TYP 3783–3831);
blueprint `MOVESR_LEAN_BLUEPRINT_2026-07-28.md` all 1246 lines; imported reuse targets
`MovesC/Defs.lean` 210–309 (CoordPrec/IsUnitriangular/Line/DomData/LevelClause) and
`Moves/DefsT.lean` 181–201 (DigitSystem/IsSolution).

## VERDICT

**REJECT (3 crit / 4 gap).**

All three criticals sit in the NEW rev-4 CInterface layer (U26/U27 + the DOM/LST floor
seam) — i.e., exactly in the material this confirmation pass was convened to check.
The re-architecture's mechanism itself (typed statement defs over an abstract lawful
carrier instead of fences) is sound and I confirm it resolves the rev-3 split; but two
of the eleven statement bodies type the wrong map, and one display equation was
re-fenced into a free field despite the "NO FENCE" claim. Note the failure mode is the
INVERSE of the vacuity trap: LSTStmt/CStatements/REL1 as written are UNSATISFIABLE by
the faithful engine instance (TYPStmt is false for any genuine jet), so every consumer
hypothesizing `REL1` would be hypothesizing a proposition the intended HC-1
instantiation can never discharge.

---

## CRITICAL FINDINGS

### F3-1 (CRITICAL, U27 `TYPStmt` conjunct 1): additivity typed on the JET (box-point
argument) — an invented law, false for every genuine block expansion.

Spec text (blueprint 622–623):
```
(∀ H (i : Fin (K.mOf H)) (f g : Fin n → ↥(O p δ)),
  K.jet H (f + g) i = K.jet H f i + K.jet H g i) ∧
```
Note displays: walk item (i) (MOVES 9401–9404) — "over O_δ this must RETYPE to
per-digit ADDITIVE on O_δ-digit blocks … additivity is all TYP(b) consumes"; TYP(a)
(3801–3807) — "in_{γ'}(B) = Σ_{c ∈ L_{γ'}(B)} y′_c·in(m_c) … an ADDITIVE function …
of exactly the level-set digits (y_c)".

The note's additive object is the LEVEL-SET-ASSIGNMENT → graded-piece composite,
additive in the DIGIT tuple; it is never the digit-extraction map in the box-point
argument. The blueprint's clause asserts `jet` is a group hom (O_δ^n, +) →
(F_δ^{mOf}, +). This is group-theoretically impossible for any genuine digit
parameterization: O_δ/p^N ≅ (ℤ/p^N)^δ has p^N-torsion, so ANY additive map into an
elementary abelian p-group factors through f mod p — an additive jet carries level-0
information only. Combined with `ThmCaStmt` (SHZ = jet-preimage of the digit locus),
every classifier locus would be a level-1 event, contradicting the engine's strata
(and ThmCb's masses) at any determination level ≥ 2. So the conjunct is (a) not the
note's claim, and (b) unsatisfiable by the faithful instantiation. The faithful typed
form already exists in-corpus at the right place: `SecB1Stmt`'s slotCoeff additivity +
`GradedCarrier.inγ_add` give the composite's additivity in the digit vector.

### F3-2 (CRITICAL, U27 `TYPStmt` conjunct 2): the alphabet cardinality is priced on
the attainable digit-VALUE set instead of the attainable slot-image SPAN; contradicts
the note's own displayed number a = 2.

Spec text (blueprint 624–625):
```
(∀ H (i : Fin (K.mOf H)),
  Nat.card (Set.range fun f => K.jet H f i) = p ^ K.aDim H i)
```
Note displays: TYP(b) (3815–3821) — "The composite (level-set assignments) → L₀,
(y_c)_c ↦ Σ_c y′_c·R_{δ'}(in(m_c)), is additive with image = the additive span of
the slot images … = the digit's ALPHABET"; (EQ-2) (9558–9559) — "|𝔸_δ| = p^{a_δ},
a_δ := the F_p-additive-span dimension of the re-based images".

`Set.range (fun f => jet H f i)` is the set of attainable DIGIT VALUES at coordinate
i — a subset of ↥(Fsub p δ), so of cardinality ≤ p^δ; for the genuine box every digit
value is attained (Theorem C(b)'s q_δ^{nN} free residue points), giving exactly p^δ.
The note's alphabet lives in the graded piece and its dimension a_δ is NOT bounded by
δ: the note itself displays an ambient (δ = 1) position with a = 2 ("the full position
a = 2 gives each re-based branch 𝔸_δ = F₉, i.e. a_δ = 2 ≠ δ·a = 4", 9580–9582). At
such a position the clause demands a p-element-bounded range of cardinality p² —
unsatisfiable by the faithful instance; conversely a junk instance passes by setting
aDim ≡ δ, which (via `aDim_eq` and `C1Stmt`) corrupts the C.1 pricing the wiring was
built to protect. NOTE: the carrier ALREADY suffices for the faithful
cardinality-granularity form — e.g. per position i,
`Nat.card ↥(AddSubgroup.closure (Set.range fun y => K.G.inγ (K.ht H i)
(K.slotCoeff H (K.blkOf H i) (Pi.single i y)))) = p ^ K.aDim H i` — so this is a
wrong-map error in the statement body, not a missing GradedCarrier field.

### F3-3 (CRITICAL, U26 `LSTStmt` clause (ii) + U28 `DOMStmt` floor form): the
display's floor–staircase IDENTIFICATION is dropped into an unlinked free field —
a residual fence in the rev that claims "NO FENCE".

Spec text (blueprint 611): `(∀ i, K.interiorB H (K.blkOf H i) → K.floorC H i =
K.floorB H (K.blkOf H i))`, with `floorB` a free `ReBased` field connected to nothing.
Note displays: LST(ii) (3743–3745) — "F_i(b) = old_i(slot(b)): ht-constant on each
current block"; DOM (3650–3651) — "consequently the floor is the current staircase:
F_i(b) = old_i(slot(b)) there"; and "old = line_i by DEFINITION at rev 12" (3717–3719),
staircase top = "line_m at the LEFT EDGE of b's frame-(m+1) block" (3720–3722).

The display equates the floor with the CURRENT READ LINE's staircase — and the current
lines ARE in-corpus (`K.lines`, consumed by `DOMStmt`). The blueprint types only
block-CONSTANCY (floorC = floorB), replacing the display's right-hand side by fresh
free data; no law links `floorB` to `K.lines`, so an instance with `floorB ≡ 42`
satisfies LSTStmt ∧ DOMStmt while violating both displays, and LST(iii)'s guard
(`floorB H B < γ'` standing in for γ' > old_i(slot(B))) inherits the same untethering.
Unlike the (i-a)/(i-b) legs — where the displayed EQUATION is fully typed over free
carriers — here the equation itself is not typed. A faithful typing needs one small
carrier addition (a block left-edge/slot-position map, e.g. `blockEdge : ℕ → ℕ`, plus
`floorB H B = (K.lines H (K.C.kIdx H)).at (blockEdge B)` or the equation inlined into
LSTStmt (ii)); as it stands this is dropped display content — the very species of
defect the rev-4 architecture was built to eliminate (D4: LST's def "carries ALL of
(i) … plus (ii) and (iii), typed once, NO FENCE" — (ii) as typed is strictly weaker
than the cited display).

## GAP FINDINGS

### G3-1 (GAP, U19 `SecB1Stmt`): slotCoeff additivity asserted at Coeff level; the
note's additivity is at the graded-piece level.
Spec (563–564): `K.slotCoeff H B (x + y) = K.slotCoeff H B x + K.slotCoeff H B y`.
Note (3799–3801): "taking classes in the piece (the class map is additive and kills
weight > δ' — D.1)". In the engine ring, unit lifts are not additive ([x+y] ≠ [x]+[y]),
so Coeff-level additivity silently constrains HC-1 to an assignment-style Coeff model
(which LST(i)'s slot-min/level-set clauses do license). Satisfiable and consistent,
but a strengthening of the D.3(e) attachment relative to the note's display; should be
recorded (D4 or §3) as a model commitment.

### G3-2 (GAP, U26 `LSTStmt` (i-b)/(i-c)): quantification over ALL `B : ℕ` where the
note scopes to "every current-window slot coefficient B" (3737–3738). Out-of-window/
junk block indices are forced to the `w = ⊤` convention (the laws do force `w 0 = ⊤`,
so `slotCoeff := 0` off-window works), but the displayed scope is wider than the
note's; a window predicate (or a recorded convention note) would close it.

### G3-3 (GAP, U28 `DOMStmt`): types Lemma DOM via its INPUT package, not the displayed
conclusion, and collapses the per-i interiors. `DomData` (MovesC 278–283) = the strict
steeper chain + the vertex-entry endpoint inequality — the two displayed PROOF inputs
("(1)/(2)"), from which the displayed conclusion "line_i(b) ≥ line_m(b) [at] every base
index b of the factor interior [0, μ_i·D_{i+1})" (3647–3649) follows for affine lines
(base-free `C2.DOM`). Truth-equivalent on the note's realizable instances and declared
via D8, but (a) the statement shape is the premise, strictly stronger than the display,
and (b) `interiorEnd : C.Hist → ℕ` is one bound for all i ≤ kIdx where the note's
interior is per-i (benign only because interiors nest, (3) at 3683–3688 — worth one
recorded sentence).

### G3-4 (GAP, U29 `EQ2lawIfREL1`): per-instance antecedent where the note's
conditionality is on the full pass. Spec (662–664): `REL1 p Sp AD δ n K → EQ2law p AD`
— a SINGLE-instance REL1 implying the ALL-δ law. The note (9587–9588): the a_δ = δ·a
law is "OPEN, REL.1-conditional" with REL.1 the ∀δ re-scoping pass (9379–9382). The
note's eventual deliverable (∀-instances REL1 ⇒ EQ2law) does not discharge this Prop;
any consumer citing it hypothesizes more than the note grants.

---

## CHARGE-ITEM RECORD (what was verified, including the passes)

(1) **LSTStmt clause-by-clause (U26)** — (i-a) chain-weight typing `G.w (K.mono H i) =
ht i` FAITHFUL against 3736–3738 (the K1 semantics of `w` and the basis-monomial
semantics of `mono` are carried by the declared interface, per the adjudication; the
κ_r/off formula for ht is correctly LEFT OUT — §R-LEDGER 9330–9333/9353–9356 fences
height bookkeeping as (R0-tower) PREDICTED). (i-b) slot-min formula FAITHFUL modulo
G3-2 (filter = {blk = B ∧ digit ≠ 0}, inf of ht in WithTop ℚ = the iterated
slot-minimum, 3738–3739). (i-c) level-set dependence FAITHFUL: agreement on
{blk = B ∧ ht = γ} ⇒ equal in_γ is exactly "a function of exactly the LEVEL SET"
(3739–3742); graded-piece typing carried by inγ's codomain `Gr γ`, absolute-index
relabeling warranted by TYP's "the absolute scale relabels the piece index, nothing
else" (3790–3791). (ii) CRITICAL F3-3. (iii) selection FAITHFUL GIVEN (ii)'s free
`floorB` (downset pinned to {blk = B ∧ ht ≤ floorB}, level set disjoint — 3746–3749);
inherits F3-3's untethered guard. **TYPStmt**: BOTH conjuncts CRITICAL (F3-1, F3-2);
the "F_δ-linearity stays EXPECTED, walked — not asserted" fence is correctly observed
(matches 9404–9406). **DOMStmt**: G3-3.

(2) **GradedCarrier (U14)** — exactly 10 fields (Coeff, coeffAdd, Gr, grAdd, w, inγ +
4 laws). Law support: `inγ_add`/`inγ_kills` VERBATIM note-supported ("the class map is
additive and kills weight > δ' — D.1", 3799–3800); `w_add` supported (TYP(a)'s "every
surviving summand has weight ≥ γ', so w(B) ≥ γ'", 3798–3799, is iterated w_add);
`inγ_detects` supported as the defining property of D.3(e)(i)'s associated-graded class
map (consumed by C.1.5's "exact valuation γ'" clause, 3813–3815); no invented law. The
laws are mutually coherent (they FORCE w 0 = ⊤; a trivial all-⊤ instance exists, and
inhabitation is correctly D9 #check-only/HC-1). SUFFICIENCY: the carrier suffices to
type all eleven statements INCLUDING a faithful cardinality-granularity TYP (display
in F3-2) — the two TYP criticals are wrong-map errors in the statement body, not
missing carrier fields; the only genuinely missing field found is the block-edge map
of F3-3 (a ReBased field, not a GradedCarrier field). R_{δ'}/L₀ (TYP(b)'s injectivity
leg) is not typed and not claimed — consistent with the declared granularity.

(3) **Composition clause (U40)** — FAITHFUL. `desc_amb` (S'.δ = S.δabs) + `ambDeg =
S.dRel` + `HEq ambK RB` is the typed form of "the same typing applies at every
descendant branching cell inside T_j, ABSOLUTE indices throughout" + "the obligations
must COMPOSE across nested base changes" (9622–9627, 9429–9431): descendant-ambient
theory = parent-target theory across exactly the index transport desc_amb provides;
`O_chain` (U41) is the display's "literally a subring chain in W(F̄_p)" ring half,
correctly kept separate from the family half. The (SIB-Oδ) body itself re-verified:
pricing display verbatim (9620–9622), S_j-is-an-O_{δ_j}-statement typed as the
Θ-pullback identity, realization event ∈ RB.C.V.events (FF5(iii)), positive-cell guard
= the note's own proviso, one (Sp, AD) does NOT smuggle EQ-1 (menus stay per-δ).

(4) **CF triage spot-checks** — 8 folded repairs verified GENUINE against the rev-4
text: CF1 (mem_pos; note-check accurate — 9476–9477 is the note's only positivity
text), CF2 (see (3)), CF3 (menuNe really removed; R.5's "no menu/exhaustion claims"
at 9760 confirms the note-check), CF8 (interior_fresh present; supported by 3743–3744
+ the rim bullet 3616–3619), CF9 (Status carrier + pinnedIn_spec + C05's
status-multiset leg; matches "cardinality-and-status statistics" 9371–9373), CF10
(a5 quantifies over S.reframe), CF13 (firstIdxCandidate demoted, absent from D7),
CF15 (events_level = the finitely-additive reading of "(digit cylinders generate)"
9480, and it does force vol everywhere). All 3 resolved-by-rearchitecture claims
CONFIRMED: CF6 (slot maps now data with F_δ-module structure; EQ2law types both
conjuncts of 9566–9568), CF7 (LSTStmt types all previously-fenced legs — modulo the
new findings F3-3/G3-2 above, which are rev-4 defects, not the rev-3 fence), CF16
(GradedCarrier + SecB1Stmt; the localization-L/degree-1-unit-T residue is recorded,
not fenced — acceptable per the adjudication's own terms, modulo G3-1).

(5) **Vacuity sweep (41 units)** — no NEW vacuity criticals: every surviving trivial
instance is proviso-excluded or a recorded §3(v) widening (Setting/SettingsFamily/
SpeciesSyntax/AlphabetData examples check arithmetically, incl. card_eq 1 = 2^0);
BoxVol/REL2b/REL2e/_linked/SIBOdelta all carry their cylinder pins, event memberships,
REL1 conjuncts and guards as advertised (FF2/FF5/FF6 re-verified in the rev-4 text);
βarg_eq/qq_mul/O_chain/EQ2law_card/Fsub_card statements faithful and provable-shaped;
ThmCbStmt verbatim over the DEFINED count with the N ≥ N(H,Z) guard (meeting-vs-
contained cylinder readings coincide above the determination level, matching the
display's presupposition); C05Stmt/C1Stmt/C15Stmt faithful pointers; DigitSystem/
IsUnitriangular/CoordPrec/Line imports typecheck against their MovesC/DefsT
definitions. The corpus-level vacuity risk is instead the INVERSE one stated in the
verdict: with F3-1/F3-2 in the record, `CStatements`/`REL1` is falsified by the
faithful instance — strictly worse than vacuity for a hypothesis interface, and the
reason this is a REJECT rather than an accept-with-gaps.

COUNTS: 3 critical / 4 gap.
VERDICT: **REJECT (3 crit / 4 gap)**.

Repair note (not a fix, a scope estimate): all three criticals are LOCAL to U26–U28's
statement bodies + one ReBased field — the CInterface architecture itself, the carrier
laws, the composition clause, and the other nine statement defs survived a hostile
pass intact. A rev 5 repairing F3-1/F3-2 (retype TYP on inγ∘slotCoeff per the display
in F3-2), F3-3 (blockEdge field + the staircase equation), and the four gaps should be
a short re-audit, not a re-architecture.
