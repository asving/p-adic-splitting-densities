# HC-2 LEAN BLUEPRINT — the JetSetup-existence bridge (2026-07-28, rev 1)

STATUS: BLUEPRINT (phase B of the campaign gate chain B → A → E → P → V).
NOTHING in this file is declared code. In particular §3's axiom statements are
**PROPOSALS ONLY** — none may be declared without (i) a published-source citation
confirmed against the PDF, (ii) a faithfulness entry in `docs/AXIOM_FAITHFULNESS.md`,
(iii) a semantic-guardian audit pass (the process that has caught two false axioms).

## 0. Charge and ground truth

HC-2 = the second hard core of `lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`
(§1/§5 wave 5): instantiate MovesC's PROVED interface — Theorem C over `JetSetup`
(`lean/LeanUrat/MovesC/Defs.lean`, 36/36 units proved-clean, MANIFEST.json) — from the
real classifier side, and thereby discharge the MovesD rev-9 open surface
(`lean/notes/MOVESD_LEAN_BLUEPRINT_2026-07-28.md` §2): **PRESENT-EXIST**,
**PresentNorm**, **POL-PIN** (+ the W4-1 `eligible` seam definition).

Ground truth for every statement: the frozen dual-accepted text in
`lean/notes/MOVES_2026-07-24.md` — §C rev 14 (C.0–C.3, esp. C.2's presentability
"N(H,Z) := 1 + the largest BASE level occurring among the coordinates of T(H,Z)'s
equations" and C.3's realizability sentence: "the classifier reads actual hull sides,
so all three [(NA)+(HV)+(SAE)] hold on its output"), §B2-DEF (D.0–D.12, esp. D.5's
standard lift, D.7's (S6b′) offset-P-lift, D.10's recentering), §D4-R (D4-R.0's
canonical policy + L1/L2). The Lean ground truth: `MovesC/Defs.lean` (round 6),
`Moves/Defs*.lean` (Stage/TransitionCoreL/LandingCylinderL — 54/61 unit ledger),
`OM/RealInstanceV2.lean` (realF2 — the M9-rebase MODEL for this bridge).

MEMORY-RULES CARRIED: subagent staged-write discipline in every prover prompt;
plan-level adversarial pass (this file goes to a fresh verifier BEFORE E-phase);
wave-3 doctrine — "a faithful interface must be FALSE for instances the note would
reject; obligations may be open, but their TYPES must pin their content."

## 1. The discharge ledger (what HC-2 delivers, to whom)

| consumer object (owner file) | HC-2 deliverable | unit(s) |
|---|---|---|
| `MovesC.JetSetup H n N m` existence (MovesC honest boundary, Defs header "The honest boundary") | `jetSetup_of_seed` : `PresentSeed` → coherent → realizable → JetSetup | U13 (+U1–U11) |
| **PRESENT-EXIST** (MovesD §2: `∀ N ≥ P.NP pol, Nonempty (Presented p F n N (n*N) pol P)`) | reduced to SEED-EXIST (the named HC-1 graded hypothesis, §2 Wall B) + proved assembly | U14, U15, U16 |
| **PresentNorm** (MovesD §3.2, the typed two-sided dictionary) | totality (lift-swap + Galois re-rooting) + uniqueness (embedding rigidity) | U17a–c, U18 |
| **POL-PIN** (MovesD §2: the canonical-policy instance + realizer laws) | `polOM : CanonPolicy p F` + blindness + totality-on-eligible-nodes (L1 kernel-(a)) | D2, U24, U25 |
| W4-1 `TreeModel.eligible` seam (MovesD §2.5) | the f-explicit run predicate `ReadsOf` (the negotiating definition MovesT re-keys) | D4, U19–U23 |
| `ClassFiberWelldef` (MovesD §3.4; D15's `hwd`) | conditional unit, proof-first with P-3 fallback; DEFERRABLE (its consumer already carries it as a hypothesis) | U26 |
| order-0 non-vacuity (the realF2 lesson) | gates: inert-n=2 value tie, σ-separation, NP(P̂*)=5, polOM instance | U27–U30 |

NOT HC-2's to deliver (recorded so nobody silently widens scope): the graded ring
itself and the two R4.5 identifications (HC-1; here the `PresentSeed` fields, §2
Wall B); `D4R_CYL` and the MovesT tree corpus (wave 4); `hExhaust`/drainage;
anything palindromy/htameFE (out of scope by standing directive).

## 2. Architecture — three walls, and where each is handled

The M9-rebase lesson (PROJECT_STATE §2, the model this blueprint copies): bridge an
abstract interface to the real engine by (i) keeping the interface fixed (statement
fence), (ii) building the instance bottom-up with the ORDER-0 case first, (iii)
machine-checked value gates against independently recorded numbers (realF2's 1/4 at
n=2 inert; split ≠ inert at q′=3) before any generality. HC-2 repeats this pattern
one level up: `JetSetup` is to Theorem C what `DensityFoundation` was to
`goal_theorem_montes`, and U27/U28 are the analogues of the V2 gates.

**Wall A — engine → History translation.** MovesC's `Node`/`History` are keyed to
`Moves.Stage` (the §B2-DEF ledger), NOT to the OM/ engine's `M5.OMType`/
`ClusterShape` (which erase the run data: the emitted shape has no lines, no digit
tuples, no lifts). The honest translation object is therefore a RUN PREDICATE
`ReadsOf f H` — "H's recorded reads are the polygon-side data f actually produces,
frame by frame" — stated in Moves vocabulary (`IsDevelopment`, slot weights via
`σ.w`/K1, `σ.R` digits, `LandingKey`), not a function of the engine's internals.
This is deliberately the SAME semantic surface as MovesD's W4-1 `eligible` (L2's
"ALL next-node data ν = (side s, its digit tuple, ψ, canonical lift)"): HC-2 owns
the definition; MovesT re-keys `eligible` to it in wave 4. The engine's own
`classify` (OM/Classifier.lean) is tied in ONLY at the order-0 gates (U27/U28),
where its numbers are independently recorded — full engine-run ↔ ReadsOf
faithfulness at all orders is NOT an HC-2 obligation (it is the existing
order-≥2 classifier-faithfulness program, PROJECT_STATE §4).

**Wall B — the graded presentation seed (OUR math ⇒ hypothesis, NEVER axiom).**
MovesC's declared honest boundary (Defs header): the existence of the presentation
spine (`pres`, `Theta`, `Theta_uni`, `pres_total`, `pres_block`), the TYP piece
maps, and the two `History.htH` identifications are "the unbuilt graded ring
(§B2-DEF gap R4.5 items 1&3)". These are §B2-DEF/§C content — dual-accepted but
OURS and unpublished — so by the campaign axiom policy (§4) they CANNOT be axioms.
HC-2 packages exactly these fields as the structure `PresentSeed` (D5) and proves
EVERYTHING ELSE of `JetSetup` from it (U1–U13). The named hypothesis

  (SEED-EXIST)  ∀ H ∈ PrefSet n polOM P, ∀ N, P.NP polOM ≤ N →
                  Nonempty (PresentSeed H n N (n*N))

is HC-1's deliverable (its graded carriers are precisely the CStatements/
GradedCarrier raw material of the parked MovesR re-architecture). PRESENT-EXIST =
SEED-EXIST + U15; the reduction is the deliverable, the seed is the honest residue.
Optionally, proposal P-2 (§3) lets a PUBLISHED GMN citation supply the pres/Theta
half of the seed early — the "budget-saver" the campaign plan names — with the
piece-map half (TYP-SPAN) explicitly carved out as guardian-checkable-or-hypothesis.

**Wall C — published Montes content (the fenced axiom proposals).** Three places
where a published statement can honestly shortcut work that is otherwise blocked
behind HC-1 or behind new hull-geometry proofs:
  P-1 stage-transition existence (GMN's order-r apparatus = §B2-DEF D.7's
      conclusion) — unblocks Wall-A history CONSTRUCTION without HC-1's TRANS
      assembly;
  P-2 higher-order φ-adic coordinates (GMN §2's admissible φ-developments) —
      optionally supplies the pres/Theta seed half;
  P-3 OM-invariant choice-independence (GMN §1.5/Cor 1.20 + companion) — fallback
      for PresentNorm uniqueness / ClassFiberWelldef.
All three are PROPOSALS (§3), each with: exact statement, citation, faithfulness-
entry draft, carve-out warnings, a downgrade-to-hypothesis path, and mutation
probes. Declaration order of preference, per the standing policy: prove > cite >
hypothesize; an axiom is declared only where the guardian confirms the citation
says NEITHER MORE NOR LESS.

### 2.1 The one pre-declared DESIGN DEVIATION (displayed for the audit round)

`mkStratum i := (mkFresh i).sat` — the constructed stratum is the FRESH clause
content only, so `JetSetup.inh_implied` holds by `Iff.rfl`. The note's C.1(i)
("on the state cylinder, the inherited content is implied — the stratum reduces to
exactly its fresh clauses") is thereby INSTALLED rather than re-proved: the
inherited-clause content of `E(ν_i)` has no self-contained Lean carrier short of
transporting the entire previous-frame clause vocabulary, and every MovesC consumer
reaches the stratum only through `recursion` + `inh_implied`. The semantic residue
— that the constructed `Sigma` chain equals the classifier's actual per-prefix
locus — is carried by (a) the zc/fresh laws U9–U10 (which pin Sigma's geometry to
the recorded node data exactly) and (b) the value gates U27/U28. The audit round
must either RATIFY this deviation or demand the inherited carrier; if the latter,
U8 re-opens as a full C.1(i) unit (add ~1 hard unit). [Wave-3 doctrine check: with
stratum := fresh, a WRONG fresh construction still fails U9/U10/U6 — the interface
stays falsifiable; no degenerate instance slips through.]

## 3. THE AXIOM PROPOSALS — FENCED; PROPOSALS ONLY, NOTHING DECLARED

Common citation base (already pinned verbatim in `lean/notes/GMN_citations.md`):
J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic
number theory*, Trans. Amer. Math. Soc. 364 (2012) 361–416 (arXiv:0807.2620v2 —
theorem numbers below are the arXiv ones; the standing pagination caveat of
GMN_citations.md applies: confirm against the TAMS PDF before declaration).
The campaign charge names "GMN/HN papers": **"HN" is NOT yet pinned in this repo**
— candidate second sources for the uniqueness leg are J. Guàrdia, J. Montes,
E. Nart, *Okutsu invariants and Newton polygons* (Acta Arith. 145 (2010) 83–108)
and J. Guàrdia, E. Nart, *Genetics of polynomials over local fields* (Contemp.
Math. 637 (2015)); the guardian round must pin which (or correct the acronym)
BEFORE P-3 can cite it. GMN's scope fence (GMN_citations.md §0): base field a
finite extension of ℚ_p, per-fixed-p; our `ℤ_[p]` sits inside it; NO uniformity/
rationality/p-independence content may ride in any of these axioms — those are
derived, never imported.

### P-1 `AX_stage_trans` — order-r stage existence (the increment transition)

```lean
/-- PROPOSAL P-1 (NOT DECLARED). GMN order-r apparatus: an eligible increment read
on a lawful stage produces a next lawful stage with the recorded canonical Bézout
pair. Lean surface = the CONCLUSION of §B2-DEF D.7 (Prop TRANS), keyed to the
Moves corpus's own transition record. -/
axiom AX_stage_trans {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hψm : ψ.Monic) (hψd : ψ.natDegree = g)
    (hψirr : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg : 1 ≤ g)
    (zbar : Fˣ) (hroot : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat)
    (e' h' : ℕ) (s' t' : ℤ) (he' : 1 ≤ e') (hh' : 1 ≤ h')
    (hcop : Nat.gcd e' h' = 1) (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    (hwin : 0 ≤ t' ∧ t' < (e' : ℤ)) (hiaug : IAug σ Φhat e' h') :
    ∃ σ' : Stage p F, σ'.Φ = Φhat ∧ σ'.e = e' ∧ σ'.h = h' ∧ σ'.s = s' ∧ σ'.t = t' ∧
      TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ'
```

* citation map (each conjunct of the conclusion → a GMN pin): the next key exists
  and is a representative of the augmented type — Thm 2.11 (key polynomial of a
  type, "effectively construct"); the next valuation `σ'.w` with value group ℤ and
  K1 at Φhat — §2.2 (`v_{r+1}`) + Thm 2.9/Thm 3.1 (Theorem of the polygon);
  the residual map laws (hR0/hRne/hRmul/hRadd/hRlt) — Def 2.20–2.21 + Thm 2.26
  (product theorem) + Thm 3.7/Cor 3.8 (Theorem of the residual polynomial);
  residue tower `F_{r+1} = F_r[y]/ψ` finite — §2.1 (types of order r+1).
* **CARVE-OUT WARNING (the guardian's first question):** the (S6a)/(S6b) realizer
  EXACTNESS fields of `Stage` ("every parent-scale weight above the threshold is
  realized, with EVERY scalar of Kˣ") are §B2-DEF D.7's (S6b′) offset-P-lift
  DERIVATION (MOVES 2436–2465) — the guardian must check whether GMN §2.4's
  residual-coefficient computation states attainability in this strength. If NOT
  (expected), P-1 must be declared with (S6a)/(S6b) REMOVED from the packaged
  conclusion (i.e. `∃ σ'` producing a Stage-minus-(S6) structure) and the (S6)
  fields supplied by HC-1's D.7 induction, OR not declared at all (downgrade
  path: `StageTransHyp` as a named hypothesis with the same signature, consumed
  by U-layer units verbatim — zero re-statement cost, the campaign's standard
  open-kernel pattern).
* non-vacuity probe: instantiate at the base stage (`L1.baseStage_exists`,
  Moves corpus, PROVED) with the n=2 Eisenstein read (e=2, h=1, ψ = z+1, g=1) —
  the Wave-1 wild gate data; the ∃ must produce the stage the W1 chain built by
  hand. Mutation probes: drop `hiaug` → must break (the F-EMPTY family);
  `hwΦ : w Φhat = h'` mutated to `h' + 1` → must break K1 gate arithmetic.
* faithfulness-entry DRAFT (`docs/AXIOM_FAITHFULNESS.md` format):
  - VERIFIED CORE: GMN §§2–3 construct, for each type of order r and each side/
    residual-factor choice, the order-(r+1) data: key (Thm 2.11), valuation and
    polygon (§2.2, Thm 3.1), residual polynomial and its multiplicativity
    (Def 2.21, Thm 2.26, Thm 3.7). Existence-only; per fixed p.
  - SAYS NO MORE: no uniformity, no rationality, no measure/density term, no
    p-independence; conclusion is one ∃ over `Stage p F` records whose every
    field is a GMN-§2/§3 object [MINUS (S6) if the carve-out fires].
  - SAYS NO LESS: the Bézout-window pinning (`hwin`) is a convention choice
    (canonical pair), not GMN content — it rides as a hypothesis on OUR side of
    the statement (selection, not import).
  - CONSUMED BY: U-layer history construction (U19, U17a) and T_can totality;
    never by a density/counting capstone directly.

### P-2 `AX_om_present` — higher-order φ-adic coordinate presentations

```lean
/-- PROPOSAL P-2 (NOT DECLARED; the optional budget-saver for the pres/Theta seed
half). GMN §2's admissible φ-developments, iterated down a recorded key tower:
every monic degree-n integral polynomial has, at every frame i of a coherent
history H with recorded keys, a UNIQUE block-local digit presentation refining the
frame-(i+1) one. Stated as: the seed's presentation spine exists. -/
axiom AX_om_present {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (n N m : ℕ) (hm : m = n * N) (hN : 1 ≤ N)
    (keys : ℕ → Polynomial ℤ_[p])
    (hkeys : ∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))
    (hmid : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) :
    ∃ (coordOf : Fin m → Coord) (pres : ℕ → (Fin m → ZMod p) → Polynomial ℤ_[p] → Prop)
      (Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))),
      (∀ j j' : Fin m, j < j' ↔ CoordPrec (coordOf j) (coordOf j')) ∧
      (∀ j : Fin m, (coordOf j).1 < N ∧ (coordOf j).2 < n) ∧
      (∀ x f, pres 0 x f ↔ ∀ j, x j = baseDigit p (coordOf j).1 (f.coeff (coordOf j).2)) ∧
      (∀ i, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p], f.Monic → f.natDegree = n →
        ∃ x, pres i x f) ∧
      (∀ i, i < H.nodes.length → ∀ x f, pres (i+1) x f → pres i (Theta i x) f) ∧
      (∀ i, i < H.nodes.length → IsUnitriangular (Theta i)) ∧
      (∀ i, i < H.nodes.length →   -- pres_block, verbatim JetSetup shape
        ∀ (f f' : Polynomial ℤ_[p]) (x x' : Fin m → ZMod p), pres (i+1) x f → pres (i+1) x' f' →
        ∀ (B B' : ℕ → Polynomial ℤ_[p]) (Nd Nd' : ℕ),
          IsDevelopment (keys i) f B Nd → IsDevelopment (keys i) f' B' Nd' →
          ∀ c : Fin m,
            B ((coordOf c).2 / (keys i).natDegree) = B' ((coordOf c).2 / (keys i).natDegree) →
            x c = x' c)
```

* citation map: φ-adic developments of higher order and their canonicity — GMN
  §2.5 (the `φ`-expansions and the operators `R_r`; Def 2.14–2.19), existence and
  uniqueness of the development against a monic key — GMN §1.2 (order 1) + §2.5
  (order r); block-locality is the development's slot structure (Def 2.14).
* **CARVE-OUT WARNINGS:** (i) `IsUnitriangular (Theta i)` — the ≺-triangular
  DIVISION ACCOUNTING is Fact A's bookkeeping (Moves `L0_FactA_exists`/
  `L0_FactB_unique`, PROVED, ours); GMN does not state it in this coordinate
  form. Preferred split: DELETE the Theta_uni conjunct from the axiom and prove
  it in U12′ from Fact A over the axiom's pres/Theta (keeps the axiom smaller
  than the citation, never larger). (ii) The DIGIT-level chart (coefficients →
  `ZMod p` tuples through the block convention, i.e. `pres` itself as a base-p
  digit statement) rides on the K1-height reading — R4.5 item 1, OURS. If the
  guardian judges the digit-flattening not GMN-citable, P-2 collapses to the
  polynomial-level development statement and the digit chart stays in SEED-EXIST
  (HC-1). EXPECTED OUTCOME: P-2 survives only in reduced form or not at all —
  it is listed because the campaign plan names it the budget-saver; the DEFAULT
  route remains SEED-EXIST (Wall B). P-2 and SEED-EXIST are interchangeable
  suppliers of D5's spine fields; no downstream unit references either by name
  (they consume `PresentSeed` values only).
* non-vacuity probe: the root-only n=2 history — the axiom's output at i=0 must
  reproduce the literal `baseDigit` chart (pres_zero forces it). Mutation probe:
  drop `hmid` → must break (the tower would develop against unrecorded keys).
* faithfulness-entry DRAFT: VERIFIED CORE = GMN §1.2/§2.5 existence+uniqueness of
  φ-developments per key tower, per fixed p; SAYS NO MORE = existence-only, no
  counting/measure content, digit-flattening carved out per (ii); SAYS NO LESS =
  the ≺-sort and box-cutoff conjuncts are our bookkeeping conventions riding as
  conclusion shape, not GMN claims (guardian to confirm this is acceptable or
  demand their removal to lemma form); CONSUMED BY: D5-seed supply only.

### P-3 `AX_om_uniq` — OM-invariant choice-independence (uniqueness leg)

```lean
/-- PROPOSAL P-3 (NOT DECLARED; PROOF-FIRST — declare only if U18/U26 fail as
proofs). Two realizable coherent histories of the SAME polynomial through the same
shape with normalized (canonical-root, canonical-lift) presentations have EQUAL
η-data. GMN: types are non-intrinsic but their invariants are; the per-choice
factorizations correspond. -/
axiom AX_om_uniq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (H H' : History p F)
    (hrun : ReadsOf p F n f H) (hrun' : ReadsOf p F n f H')
    (hshape : shapeOfHist H = shapeOfHist H')   -- same ShapePrefix (MovesD vocabulary)
    (hcanon : (polOM p F).IsCanonPres H) (hcanon' : (polOM p F).IsCanonPres H')
    (hbr : branchChoicesOf H = branchChoicesOf H') :  -- same recorded (side, ψ) choices
    etaData (shapeOfHist H) H = etaData (shapeOfHist H') H'
```

* citation map: GMN §1.5 ("types are not intrinsical objects… the data λ, ψ(y)
  depend on this choice" WITH the per-choice factorization — already pinned as
  (P4b) in GMN_citations.md) + Cor 1.20 (the invariants (e,f) intrinsic) + the
  order-r analogues (Def 2.12 sequel, Def 3.10 remark — pinned as (P4c)); the
  "HN" companion pin (§3 header) for the invariance apparatus at all orders.
* **PROOF-FIRST INSTRUCTION:** U18 (PresentNorm uniqueness) is expected PROVABLE
  outright — normalized classes pin `zbar = canonRoot` per read, and `EtaGalEq`'s
  automorphism must fix each `fieldEnum`-least root it relates, whence fix the
  generated tower pointwise (mathlib finite-field Galois theory). P-3 exists ONLY
  as the fallback if the per-read induction hits genuinely Montes-theoretic
  content (e.g. cross-read rigidity of the recorded ψ-coefficients). U26
  (ClassFiberWelldef) is likewise proof-first via Theorem C(a) at Z = ⊤.
* mutation probe: drop `hbr` → MUST NOT be provable/declared (two same-shape
  factors give distinct branches with equal shape — the §D4-R F1 refutation
  instance; an axiom without `hbr` is FALSE). This probe is mandatory in the
  guardian charge — it is exactly the dual-bar critical that punctured §D4-R.
* faithfulness-entry DRAFT: VERIFIED CORE = per-choice factorization
  correspondence + intrinsic invariants (GMN §1.5, Cor 1.20, order-r remarks);
  SAYS NO MORE = data-equality of recorded η only, under IDENTICAL branch
  choices; no counting content; SAYS NO LESS = normalization clauses are our
  conventions (hypothesis side). CONSUMED BY: U18/U26 fallback only.

## 4. Defs skeleton — `lean/LeanUrat/MovesJ/Defs.lean` (definitions only)

Imports: `Mathlib`, `LeanUrat.MovesC.Defs`, `LeanUrat.Moves.Defs{,Core,L,T}`,
`LeanUrat.MovesD.Defs` (the E-phase core — needed for `CanonPolicy`, `Shape`,
`PrefSet`, `PresentNorm`, `Presented`, `Threshold`; HC-2 runs AFTER MovesD's core
lands, per the wave plan). Namespace `LeanUrat.MovesJ`,
`open LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD`.

DECLARATION ORDER (normative, the MovesD §3.0 discipline): D1 → D3 → D2 → D4 →
D5 → D6 → D7. NO axiom declarations in this file, ever (proposals live in §3 of
this note until their gate chain completes; if declared, they go in a dedicated
`MovesJ/Axioms.lean` behind the guardian gate, mirroring `OM/OmLeafFaithful.lean`).

### D1 `boxChart` — the ≺-sorted chart of the n×N box  [easy]

```lean
/-- The canonical ≺-sorted enumeration of the n·N coordinate box: level-major
(ℓ ascending), base-index DESCENDING within a level (CoordPrec, §C C.0). -/
def boxChart (n N : ℕ) : Fin (n * N) → Coord :=
  fun j => ((j : ℕ) / n, n - 1 - (j : ℕ) % n)
```
lemmas (same file, proved at E-phase): `boxChart_sorted : ∀ j j', j < j' ↔
CoordPrec (boxChart n N j) (boxChart n N j')` (consumes MovesC's
`C0.coordPrec_trichotomy`; arithmetic on div/mod) and `boxChart_lt : ∀ j,
(boxChart n N j).1 < N ∧ (boxChart n N j).2 < n` (needs `0 < n`; junk-guard the
`n = 0` case by `Fin (0*N)` emptiness). moves_ref: §C C.0 "(ℓ,i) ≺ (ℓ′,i′) iff
ℓ < ℓ′, or ℓ = ℓ′ and i > i′".

### D3 `RecenterLiftSpec` — the lift specification (before D2, which chooses from it)

```lean
/-- The EXACT specification of a recentering lift at node ν — verbatim the
recentering clause of MovesC's `LandingKey` (D.10's center realizer). -/
def RecenterLiftSpec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (tL : Polynomial ℤ_[p]) : Prop :=
  inC ν.σ.Φ tL ∧ tL ≠ 0 ∧ ν.σ.w tL = ν.σ.w ν.σ.Φ ∧
    ν.σ.R tL = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0
```
moves_ref: MovesC `LandingKey` first conjunct; §B2-DEF D.10 "Φ′ = Φ − t,
w(t) = w(Φ), dig(t) = c̃ (position 0)".

### D2 `polOM` — the canonical policy instance (POL-PIN's carrier)  [easy]

```lean
/-- THE canonical policy: at every node, the classically chosen realizer of
`RecenterLiftSpec` when one exists, else 0. Deterministic; reads only (σ, center)
— never the lift field — so `blind` holds. -/
noncomputable def polOM (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] :
    CanonPolicy p F where
  liftOf ν := if h : ∃ tL, RecenterLiftSpec ν tL then h.choose else 0
  blind := by
    intro ν t
    -- `{ν with lift := t}` leaves σ and center untouched; the ∃ and its choice
    -- are literally the same proposition/term.
    rfl
```
**DISPLAYED CANONICITY DEVIATION (for the audit + POL-PIN record):** the note's
canonical policy is the (S6b′) OFFSET-P FORMULA (§B2-DEF MOVES 2446–2449: anchor
slot j₀ forced by the congruence, summands t_k·Φ^{j₀+e·k}, prescribed digits);
`polOM` is instead THE choice-selected realizer of the SAME spec
(`RecenterLiftSpec` = D.10's clauses). Soundness of the substitution: every MovesD
theorem is ∀-pol; the counts are η-class-level and `etaData` EXCLUDES lifts (MovesD
§3.2 "lifts are policy-determined, so classes ↔ η's"); PresentNorm (U17/U18) is
what makes the count policy-independent — exactly the note's own dictionary
argument (MovesD reconciliation (6)). The offset-P FORMULA's Lean form (the j₀-sum
as a construction) remains HC-1 property and can later replace `h.choose` with
zero consumer changes (same spec). If the audit rejects the substitution, U25
re-keys to the formula and inherits HC-1's D.7 dependency — recorded as the
downgrade path.

### D4 `ReadsOf` — the f-explicit run predicate (Wall A; the W4-1 seam)  [def-only]

```lean
/-- "History H is a classifier run on f": per read i, f's development in frame i's
key realizes the recorded side/digit data, and the recorded landing produces the
recorded next key. THE NEGOTIATING DEFINITION for MovesD's W4-1 `eligible` seam —
MovesT re-keys `TreeModel.eligible` to per-read clauses of THIS predicate. -/
def ReadsOf (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (f : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  f.Monic ∧ f.natDegree = n ∧
  ∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧
      SideReads (H.nodes[i]'hi) B Nd
```
with the ONE per-read clause bundle (kept a separate def so U20–U22 can consume
its conjuncts by name):
```lean
/-- The recorded read data are the ACTUAL window data of the development `B`:
(i) SIDE — the recorded span slots minimize the slot weights `w(B_j) + j·w(Φ)`
    along the recorded line, all other window slots lie strictly above it
    (D.3(a)/(c): the side is a genuine lower-hull edge over the window);
(ii) DIGITS — at every span lattice slot `j = s0 + e·k`, the recorded pattern
    digit is f's actual side digit: `σ.R (B j)` is the monomial-unit with scalar
    `pat k` at the forced position (S5);
(iii) ANCHOR/ORDER — the recorded (a, Ranch, ψ, μ) tie to `R(f)` in frame i:
    HasAnchorK (frame residual of f) a Ranch ∧ OrdPsiPoly ψ Ranch μ, at the node's
    recorded fields (Node's own hRanch/hOrd make Ranch/μ pattern-determined —
    this clause ties the PATTERN to f);
(iv) DESCENT WITNESS — `ψ (zbar) = 0` selected root (already Node.hzbarRoot) and
    the landing key is realized: `LandingKey (H.nodes[i]) (nextKeyOf H i)`
    where `nextKeyOf H i` := the recorded child frame key (i+1 < len) or the
    designated final key;
(v) LIFTS — recentering nodes carry the polOM lift: `ν.lift = (polOM p F).liftOf ν`.
def SideReads {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) : Prop := …
```
E-phase duty: (i)–(iv)'s exact inequality forms are transcribed from §B2-DEF
D.3(a)/(c)+D.8's `LandingCylinderL` (Moves/DefsL.lean 247–259 ALREADY carries the
box/vertex/transport shape — reuse it verbatim for the μ-side reading rather than
re-deriving). moves_ref: §D4-R L2 "ALL next-node data ν = (side s, its digit
tuple, ψ, canonical lift) where s is an eligible side of the polygon f produces
in η's frame"; §C C.3 "the classifier reads actual hull sides".

### D5 `PresentSeed` — the graded seed (Wall B; the HC-1 interface)  [def-only]

```lean
/-- The graded-presentation SEED: exactly the fields of `JetSetup` that MovesC's
honest boundary defers to the unbuilt graded ring (§B2-DEF R4.5 items 1&3), and
NOTHING else. HC-1 (or proposal P-2, reduced form) supplies values; U13 proves
`JetSetup` from a seed. Field statements are byte-identical to `JetSetup`'s. -/
structure PresentSeed (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (H : History p F) (n N m : ℕ) where
  hm : m = n * N
  hN : 1 ≤ N
  coordOf : Fin m → Coord
  coordOf_sorted : ∀ j j' : Fin m, j < j' ↔ CoordPrec (coordOf j) (coordOf j')
  coordOf_lt : ∀ j : Fin m, (coordOf j).1 < N ∧ (coordOf j).2 < n
  keys : ℕ → Polynomial ℤ_[p]
  keys_mid : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ
  landing : ∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)
  pres : ℕ → (Fin m → ZMod p) → Polynomial ℤ_[p] → Prop
  pres_zero : ∀ x f, pres 0 x f ↔ ∀ j, x j = baseDigit p (coordOf j).1 (f.coeff (coordOf j).2)
  pres_total : ∀ i, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p],
      f.Monic → f.natDegree = n → ∃ x, pres i x f
  Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  Theta_uni : ∀ i, IsUnitriangular (Theta i)
  pres_theta : ∀ i, i < H.nodes.length → ∀ x f, pres (i+1) x f → pres i (Theta i x) f
  pres_block : (verbatim JetSetup.pres_block, at these keys)
  /-- R4.5 item 1: the graded piece map of each recorded value support — a
  TypObject with FULL alphabet (Fin S.card → ZMod p): D.3(e)(i)'s additive span +
  D.3(e)(ii)'s attainable accounting, jointly (surjectivity onto the full p^{|S|}
  alphabet IS the two identifications' consumer form). -/
  typObj : ∀ (i : ℕ) (hi : i < H.nodes.length) (S : Finset (Fin m)),
      IsValueSupport H coordOf i (H.nodes[i]'hi) S →
      TypObject p m S (Fin S.card → ZMod p)
  /-- the height law consumer form (LST(i), R4.5 item 3): the DEFINED `History.htH`
  is the presentation's own height reading — carried as the ZC-seed law the U10
  induction consumes; exact clause list fixed at E-phase against C.1.5's proof
  (the per-step exactness needs: fresh clauses cut freshly = their supports are
  UNPINNED on the prior state, and the move maps carry pin status — the first is
  a fresh-band/floor consequence (U-layer), the second is C0.pinTransport;
  whatever residue of C.1.5's step is NOT derivable from the above lands HERE as
  named seed laws, never silently). -/
  zcSeed : ZCSeedLaws H coordOf pres Theta keys
```
FENCE: `ZCSeedLaws` is a TO-BE-FIXED-AT-E-PHASE Prop bundle; the blueprint
pre-authorizes ONLY laws that are (a) stated in §C C.1.5/rev-9's display or
(b) §B2-DEF D.3(e) content — anything else added there is a statement-fence event
requiring sign-off. The audit round must check `ZCSeedLaws`'s final field list
against C.1.5's proof line by line. [This is the blueprint's declared
seam-of-least-knowledge: the exact split of the C.1.5 induction between provable
(U10) and seed (zcSeed) is the one genuinely open design point — the stuck-rule's
expected firing site.]

### D6 `mkFresh` — the fresh-data constructor  [def-only]

```lean
/-- Read i's fresh clauses, constructed from node geometry: one STRIP clause
`x c = 0` per band coordinate that is NOT a value position; one VALUE clause per
recorded span slot with nonempty exact-valuation level set, with support that
level set, codim = |support|, and constraint `typObj.φ x = vOf i j` (the emitted
value at the node's read digit — the R4.B.2 provenance boundary). -/
noncomputable def mkFresh {p F …} (H) (n N m) (S : PresentSeed p F H n N m)
    (vOf : ℕ → ℕ → …) (i : ℕ) (hi : i < H.nodes.length) : FreshData p m := …
```
Consumes MovesC's `C1.stripClause` (strip `LevelClause` constructor) and
`C1.TYP_toClause` (TypObject → LevelClause) — both PROVED units. The emitted
values `vOf` are a parameter at this layer (their provenance from the node's
pattern digits is the declared graded boundary, MovesC round-5 header "only the
emitted value v stays existential — R4.B.2"); U27/U28's gates fix them concretely
at order 0. Value supports: `levelSet i j := {c | fineSlot = j ∧ htH = slotVal j}`
as a Finset via `Fintype (Fin m)` + decidability-by-ℚ-equality (noncomputable
classical Finset is fine — counting is by `Nat.card`).

### D7 `mkSigma` / `mkStratum` — the state chain  [def-only]

```lean
noncomputable def mkStratum … (i : ℕ) : (Fin m → ZMod p) → Prop :=
  fun y => (mkFresh … i …).sat y   -- THE §2.1 DISPLAYED DEVIATION
noncomputable def mkSigma … : ℕ → Locus p m
  | 0     => fullBox        -- all pinned = false
  | i + 1 => pinTransportSystem (mkSigma i) (S.Theta i) (mkFresh … i)
```
`pinTransportSystem` = the digit-system re-presentation of
`(mkSigma i).pullback (Theta i) ∩ (fresh locus)` with pins = the transported pins
plus the fresh clauses' cut coordinates — built on MovesC's `C0.pinTransport`
(PROVED: pullback by a unitriangular move is a digit system with the SAME pinned
coordinates) + a strip/value pin-attachment constructor. The (ZC)-relevant
geometry (WHICH coordinates the value clauses pin) is settled by U9/U10, not by
this definition; the definition only fixes the digit-system CARRIER.


## 5. Unit specs (campaign §2 format; every unit ≤ ~40 expected proof lines or pre-split)

Binder conventions for all units: `variable {p : ℕ} [Fact p.Prime] {F : Type*}
[Field F] [Finite F] {n N m : ℕ} {H : History p F}`; `S : PresentSeed p F H n N m`;
`hcoh : HistoryCoherent H`; `hreal : Realizable H`; `len := H.nodes.length`.
`hypothesis_fields` lists the OPEN objects a statement carries — never silently
strengthened or dropped (campaign rule).

### Layer A — seed-independent facts

**U1 `keys_exist`** · file `MovesJ/U1_keysExist.lean` · statement:
```lean
theorem keys_exist (hcoh : HistoryCoherent H) :
    ∃ keys : ℕ → Polynomial ℤ_[p],
      (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
      (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))
```
moves_ref: MovesC `JetSetup.keys_mid`/`landing` docstrings ("ALL reads incl. the
FINAL one obey the recorded-data landing law"). deps: Moves `L3_liftExists`
(standard lift exists, PROVED), `IsRecenteringCore` (final-read recentering:
`Φ' = Φ − lift` is explicit). sketch: interior keys are recorded (coherence's
`IsNodeLift`/`IsRecenteringCore` clauses ARE the landing law there — extract);
the FINAL key: recentering → `σ.Φ − lift` literally; else `L3_liftExists` at the
node's read index gives an `IsNodeLift` witness (check: L3's lift is at the
STAGE pair; U1 needs the NODE pair (e,h,s,t) — the `IsNodeLift` reindexing; if
L3's unit is stage-keyed only, add helper `nodeLift_exists`, same proof shape,
(S6b) realizers at the node's h — the MovesC F10 lesson says DO NOT conflate).
difficulty: medium. hypothesis_fields: none.

**U2 `mkFresh_disj`** · `MovesJ/U2_freshDisj.lean` ·
`(mkFresh … i hi).clauses.Pairwise (Disjoint ·.support ·.support)`.
moves_ref: §C C.1.5′ "pairwise disjoint: the factors multiply". deps: D6. sketch:
strips are singletons at non-value coords; value supports are level sets of
distinct span slots (distinct fine blocks → disjoint) and exclude non-value
coords by definition; list construction indexes clauses by disjoint coordinate
sets. difficulty: easy-medium. hypothesis_fields: none.

**U3 `mkFresh_band`** · `MovesJ/U3_freshBand.lean` ·
`∀ cl ∈ (mkFresh … i hi).clauses, ∀ c ∈ cl.support, inFreshBand H n S.coordOf i (H.nodes[i]'hi) c`.
moves_ref: MovesC `JetSetup.fresh_band` docstring. deps: D6. sketch: strip
supports are chosen from the band; value level-set members have height = slotVal
(the band's upper edge) — membership needs `floorH < slotVal ≤ slotVal` and
`< prevRim`: the former is the band's own selection (value slots past the (γ)
crossing have empty level sets IN THE BAND — D6 constructs value clauses only at
slots with `floorH < slotVal`), the latter from D6's slot range. difficulty:
medium. hypothesis_fields: none.

**U4 `mkFresh_cover`** · `MovesJ/U4_freshCover.lean` ·
`inFreshBand … c → ∃ cl ∈ (mkFresh … i hi).clauses, c ∈ cl.support`.
moves_ref: `fresh_cover` docstring ("every band coordinate lies in SOME clause's
support — EXACTLY one, by disj"). deps: D6, U2. sketch: dichotomy on
`IsValueCoord c`: value → c is in its slot's level set = that value clause's
support; non-value → its strip clause exists by D6's strip roster (indexed by
exactly the non-value band coords). difficulty: easy-medium. hypothesis_fields:
none.

**U5 `mkFresh_assembled`** · `MovesJ/U5_freshAssembled.lean` · the
`fresh_assembled` disjunction for `mkFresh`, verbatim MovesC's field type.
moves_ref: MovesC round-5 header "exact geometric fresh-clause identification".
deps: D6, `C1.TYP_toClause` (PROVED), `IsValueSupport`. sketch: by construction —
strips carry the ¬IsValueCoord tag from their roster; value clauses carry
`IsValueSupport` (their support IS a slot level set, both directions of the iff
from D6's set-builder), `codim = card` by `C1.TYP_toClause`'s clause shape, and
the TypObject/`v` witnesses are D6's own data. difficulty: medium (iff
bookkeeping). hypothesis_fields: the emitted values `vOf` (R4.B.2 boundary —
free parameters here).

**U6 `mkFresh_mstar`** · `MovesJ/U6_mstarEq.lean` ·
`(mkFresh … i hi).mstar = Nat.card {c : Fin m // inFreshBand H n S.coordOf i (H.nodes[i]'hi) c}`.
moves_ref: `mstar_eq` docstring ("the presented fresh codimension sum equals the
FRESH-BAND count computed from node data"). deps: U2–U5. sketch: mstar = Σ codim
= Σ strips 1 + Σ value |support| = |non-value band| + |value band| (U3 supports ⊆
band, U4 cover, U2 disjoint ⇒ the supports PARTITION the band; strips contribute
1 = |{c}|, value clauses |support|); finish by `Finset.card_biUnion`.
difficulty: medium. hypothesis_fields: none.

**U7 `mkSigma_init_rec`** · `MovesJ/U7_sigmaRec.lean` · two lemmas:
`(mkSigma … 0).pinned c = false` and the `recursion` law
`(mkSigma … (i+1)).IsSolution x ↔ ((mkSigma … i).IsSolution (S.Theta i x) ∧ mkStratum … i (S.Theta i x))`.
moves_ref: `JetSetup.init`/`recursion` field types. deps: D7, `C0.pinTransport`
(PROVED), S.Theta_uni. sketch: init is definitional; recursion = pinTransport's
solution-set law + the fresh-cut attachment's solution-set law. difficulty:
medium. hypothesis_fields: none.

**U8 `mkStratum_inh`** · `MovesJ/U8_inhImplied.lean` ·
`(mkSigma … i).IsSolution y → (mkStratum … i y ↔ (mkFresh … i hi).sat y)` — by
`Iff.rfl` under D7's definition. **CARRIES THE §2.1 DEVIATION DISPLAY in its
docstring; the audit round rules.** difficulty: easy (or re-opens as hard if the
ruling demands the inherited carrier). hypothesis_fields: none.

**U11 `root_height_of_inBox`** · `MovesJ/U11_rootHeight.lean` ·
```lean
theorem root_height_of_inBox (hcoh : HistoryCoherent H) (hbox : InBox n H) :
    ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth → 1 ≤ (H.nodes[0]'hj).line.at b
```
moves_ref: MovesC `JetSetup.root_height` docstring ("D.4's ROOT case: every side
slope ≥ 1; the cluster zeros pin level 0, floor height 1"). deps: MovesD `InBox`
(E-phase core). sketch: InBox gives the root side inside the degree-n box —
intercept/slope bounds; the line at interior b ≥ its value at the right interior
edge ≥ 1 (descending line, endpoint arithmetic). RISK: if MovesD's `InBox` turns
out weaker than the height bound, this unit's hypothesis must be upgraded to the
D.4 root clause — statement-fence event, sign-off required (never prove from
junk). difficulty: medium. hypothesis_fields: `hbox`.

### Layer B — the (ZC) induction (the hard core of the hard core)

**U9 `zc_root`** · `MovesJ/U9_zcRoot.lean` ·
`ZCData (mkSigma … 1) S.coordOf (H.htH 1) (H.floorH 1) ((H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth)`
(the i = 0 instance of `JetSetup.zc`). moves_ref: §C C.2 proof "initialized at
the root (C.1.5's base = D.8 + D.11 at ν₀)". deps: U7, D6/D7, S.zcSeed, U11.
sketch: after the root read, pins = root fresh cuts; downset-exactness: a level-0
interior coordinate has htH = ℓ ≤ floor iff it is a cluster-zero strip (U3/U4's
partition + root_height puts the floor at ≥ 1); interior zeros: strips solve to
0 by construction; value pins sit at the rim by the root band's shape.
difficulty: hard (pre-split: U9a downset ⊆, U9b ⊇, U9c interior_zero).
hypothesis_fields: S.zcSeed.

**U10 `zc_step`** · `MovesJ/U10_zcStep.lean` · the inductive step: given
`ZCData (mkSigma … (i+1)) … (rim i)`, prove
`ZCData (mkSigma … (i+2)) S.coordOf (H.htH (i+2)) (H.floorH (i+2)) (rim (i+1))`.
moves_ref: §C C.1.5 (per-step conditional exactness): "(1) multiplies the mass by
exactly vol_nom(E_fresh(ν_{i+1})); (2) re-establishes (ZC)". deps: U3–U7, S
(zcSeed, Theta_uni, pres_block), `C0.pinTransport`, MovesC `C2.freshFree`,
`C3.lineDom` (PROVED consumers of the same geometry), `hreal` (the per-step
`TransitionAdmissible` via `JetSetup.realizable`'s definitional unfold — rev 14's
DOM hypothesis). sketch (C.1.5's proof, note-accepted): the move Θ_i carries pin
status (pinTransport); the new floor is the old max'd with ν_{i+1}'s staircase
(floorH_succ, PROVED); fresh cuts land strictly above the old floor and inside
the region (U3), so the downset grows by exactly the strip zeros + the sub-line
levels; (SAE)/(NA)/DOM order the lines so no old pin resurfaces above the new
floor; rim leads = the value clauses at the new rim. PRE-SPLIT (mandatory):
U10a floor-monotone downset transport; U10b fresh-cut downset exactness; U10c
interior zeros; U10d rim-lead placement. difficulty: HARD ×4 — the pre-declared
escalation-risk center. Whatever step resists derivation is a candidate zcSeed
law (D5's fence) — via the stuck rule, NEVER a silent axiom. hypothesis_fields:
S.zcSeed, hreal.

**U13 `jetSetup_of_seed`** · `MovesJ/U13_assembly.lean` ·
```lean
theorem jetSetup_of_seed (S : PresentSeed p F H n N m)
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H)
    (vOf : …) : Nonempty (JetSetup H n N m)
```
moves_ref: MovesC `JetSetup` structure (all 25 fields). deps: U1–U11 (+U9/U10 for
`zc`), D5–D7. sketch: field-by-field packaging; `coherent := hcoh`, `realizable
:= hreal`, seed fields verbatim, constructed fields with their U-layer laws.
difficulty: medium (assembly only). hypothesis_fields: S (SEED-EXIST's payload),
hbox, vOf.

### Layer C — MovesD discharge

**U14 `NP_fits`** · `MovesJ/U14_npFits.lean` · statement (against MovesD §3.3's
shape replica): for `P : Shape n`, `H ∈ PrefSet n pol P`, `N ≥ (P : ShapePrefix).NPband n`:
every coordinate of every `mkFresh` support and every `Z = ⊤` pin has base level
`< N` — i.e. the constructed system fits the box (C.2's "N ≥ N(H,Z)" largeness,
at the shape bound). moves_ref: §C C.2 "N(H,Z) := 1 + the largest BASE level
occurring among the coordinates of T(H,Z)'s equations"; MovesD W4-4 (NP-ID) —
THIS UNIT IS NP-ID's ⊆ direction; its moves_ref must carry the W4-4 pointer.
deps: U3 (supports ⊆ band), MovesD `bandS`/`NPband` (shape-level band replica,
E-phase core). sketch: band coordinates' levels are bounded by the shape's band
levels (htH arithmetic vs the line data, which are shape-pinned by MatchesHist);
NPband is 1 + their max. difficulty: medium-hard (the htH ↔ bandS arithmetic).
hypothesis_fields: none beyond PrefSet membership.

**U15 `present_exist_of_seeds`** · `MovesJ/U15_presentExist.lean` ·
```lean
theorem present_exist_of_seeds {P : Shape n}
    (hseed : ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ), P.NP (polOM p F) ≤ N →
       Nonempty (PresentSeed p F (reprOf i) n N (n * N)))
    (hnorm : PresentNorm n (polOM p F) P) :
    ∀ N : ℕ, P.NP (polOM p F) ≤ N → Nonempty (Presented p F n N (n * N) (polOM p F) P)
```
moves_ref: MovesD §2 PRESENT-EXIST row ("∀ N ≥ P.NP pol, Nonempty (Presented …) —
presentability at every level of L12's exact range (§C C.2)"). deps: U13, U14
(reprOf i ∈ PrefSet gives hcoh/hreal/hbox), U17/U18 (hnorm — or carried).
sketch: `jet i := jetSetup_of_seed (hseed i N hN).some …`; `hnorm := hnorm`.
difficulty: easy-medium. hypothesis_fields: **hseed = SEED-EXIST (HC-1)**; hnorm
(dischargeable by U17/U18, else carried).

**U16 `threshold_of_seeds`** · `MovesJ/U16_threshold.lean` ·
`… → Nonempty (Threshold p F n (polOM p F) P)` via MovesD's `TW_threshold_witness`
+ U15. moves_ref: MovesD §2 Threshold/TW row. deps: U15, MovesD TW unit.
difficulty: easy. hypothesis_fields: hseed, hnorm.

**U17a `lift_swap`** · `MovesJ/U17a_liftSwap.lean` · statement: for
`H ∈ PrefSetAny n P` there is `H'` with the SAME shape, side digits, and
ψ-coefficients per read (i.e. `etaData … H' = etaData … H`), all recentering
lifts = `polOM.liftOf`, `HistoryCoherent H'`, `Realizable H'`, `InBox n H'`.
moves_ref: MovesD §3.2 PresentNorm docstring clause (i) totality "= L1's
kernel-(a) totality + the L6-corollary + conjugation equivariance"; §B2-DEF D.10
"lift independence". deps: U25 (polOM total on eligible nodes), Moves
`L5_recLiftIndep_R4` (PROVED — D.10's lift-independence core), P-1 OR HC-1-TRANS
(swapping a lift changes the child key `Φ′ = Φ − t′`, so the DOWNSTREAM stages
must be rebuilt — stage existence enters HERE). sketch: induct along the chain;
at each recentering replace lift and rebuild the child stage by
`IsRecenteringCore` (explicit construction, Moves DefsCore 242 — check whether
the recentered stage is CONSTRUCTED by a proved Moves unit or only specified;
if specified-only, this is P-1's recentering sibling — add it to P-1's ∃ or
consume HC-1); transport the remaining reads (their data are development-side,
unchanged by the D.10 independence lemma). difficulty: HARD — escalation risk;
the one unit consuming stage RECONSTRUCTION. hypothesis_fields: stage-existence
supplier (P-1 | HC-1-TRANS | named hyp `StageTransHyp`).

**U17b `galois_normalize`** · `MovesJ/U17b_galois.lean` · statement: for coherent
realizable H there is `φ : F ≃+* F` and `H'` with `zbar`'s = `canonRoot` at every
read, `EtaGalEq (etaData … H) (etaData … H')`, coherence/realizability preserved.
moves_ref: MovesD `EtaGalEq`/`canonRoot` defs; §0.6 root-normalization gate.
deps: mathlib finite-field Galois (`ZMod.algHom_ext`-family, Frobenius closure),
MovesD `fieldEnum`. sketch: per read, the recorded `zbar` and `canonRoot ν` are
roots of the same irreducible `ψImage`; a power of Frobenius over the frame
subfield maps one to the other; compose down the tower (finite chain; the
automorphism group of a finite field is cyclic, generated by Frobenius —
extension over the recorded subfield tower is elementary Galois theory of finite
fields); transport all node data along φ (a ring-iso commutes with every clause
in Node's Prop fields — mechanical but long). difficulty: hard (pre-split:
U17b-1 single-read root swap; U17b-2 tower composition; U17b-3 data transport).
hypothesis_fields: none.

**U17c `presentNorm_total`** · `MovesJ/U17c_total.lean` · the totality clause of
`PresentNorm n (polOM p F) P` from U17a + U17b + membership bookkeeping
(`H' ∈ PrefSet` → its class is a `PrefIdx` member). difficulty: medium.
hypothesis_fields: inherits U17a's stage supplier.

**U18 `presentNorm_unique`** · `MovesJ/U18_unique.lean` · the uniqueness clause:
`H, H' ∈ PrefSet, EtaGalEq (etaData H) (etaData H') → etaData H = etaData H'`.
moves_ref: MovesD §3.2 clause (ii) "UNIQUENESS (embedding rigidity)". deps:
MovesD canonRoot/fieldEnum; mathlib. sketch: both normalized ⇒ each read's
residue root is the fieldEnum-LEAST root of its ψ-image; the EtaGalEq
automorphism φ maps ψ-coefficients to ψ′-coefficients and roots to roots; by
induction up the tower φ fixes the generated subfield (least-root pinning:
φ permutes the root set of the SAME polynomial once coefficients are fixed, and
order-preservation of the FIXED enumeration forces the least root to the least
root — φ fixes it; then the frame subfield of the next read is generated by
fixed elements). PROOF-FIRST; P-3 is the recorded fallback. difficulty: hard.
hypothesis_fields: none (or P-3 if it fails).

### Layer D — the run predicate and realizability (Wall A)

**U19 `readsOf_coherent`** · `MovesJ/U19_runCoherent.lean` ·
`ReadsOf p F n f H → HistoryCoherent H`. moves_ref: MovesC `HistoryCoherent`
docstring ("the recorded frames are linked by the ACCEPTED §B2-DEF transitions AT
THE RECORDED NODE DATA"). deps: D4; Moves L4_TRANS* (PROVED transition items).
sketch: SideReads(iv)'s landing + the recorded child stages give the
IsNodeLift/IsRecenteringCore legs; slope/γ/width ties are SideReads(i)'s line
arithmetic. NOTE: if D4 (by design) RECORDS coherence-adjacent data rather than
re-deriving it, parts collapse to projections — the E-phase decides which
clauses of HistoryCoherent are D4-recorded vs derived; the unit's statement is
fixed either way. difficulty: medium. hypothesis_fields: none.

**U20 `readsOf_NA`** · `MovesJ/U20_NA.lean` · for consecutive reads of a run
with `s0' + wSide' < μ` (non-adjacent): the (NA) strict inequality of
`TransitionAdmissible`. moves_ref: §C C.0 (NA) display; C.3 "the classifier
reads actual hull sides". deps: D4 (SideReads(i)), hull convexity (Moves
L2_widthBound/L2_strideRule + line arithmetic). sketch: the new side is a lower
hull edge of the CHILD development whose window ends strictly left of the
standing vertex; the standing vertex's value is the old line's; strict
convexity of the hull at the vertex + the side's minimality give the strict
gap at base index μ·D. difficulty: hard-ish (medium-hard). hypothesis_fields:
none.

**U21 `readsOf_HV`** · `MovesJ/U21_HV.lean` · adjacent reads: the pattern lead
equals `vtx(νp)` in F. moves_ref: §C C.0 (HV) "the data IDENTITY pattern lead of
ν_{i+1} = vtx(ν_i) with the FULL transported vertex value". deps: D4, Moves
`L5_landVertexDigit{,_repair}` + `L5_landTransport_R4` + `LandingCylinderL`
(PROVED — D.8's two-sided landing with the vertex unit). sketch: the adjacent
read's hinge digit is the transported vertex digit by D.8's (VERTEX) clause of
the landing cylinder; unfold `Node.vtx`'s scalar bookkeeping (`z̄^{a−μm̂}` — the
anchor/normalization exponents match `LandingCylinderL`'s `T(μ·m̂ − a)` unit
literally). difficulty: HARD (exponent bookkeeping across two conventions —
the MovesC F10 index lesson applies; escalation risk). hypothesis_fields: none.

**U22 `readsOf_SAE`** · `MovesJ/U22_SAE.lean` · the span-entry inequalities:
`new(j) > old(j)` at span slots `j < μ`, equality at the adjacent vertex.
moves_ref: §C rev 12 (SAE) display (MovesC `TransitionAdmissible` conjuncts
3–4). deps: D4, the parent's (ZC)-zeroed strips (the stratum's interior zeros
raise actual valuations strictly above the old line), K1 slot reading. sketch:
on the descend stratum the sub-line digits are zero, so each span coefficient's
actual weight exceeds the old line at its slot; the new line reads ACTUAL
weights (SideReads(i)), giving strictness below the vertex; at the vertex the
side passes through the standing vertex (adjacent case) — equality. difficulty:
HARD (escalation risk; this is the clause whose ABSENCE the F-EMPTY refutation
exposed — the unit's docstring must cite the F-EMPTY record). hypothesis_fields:
none.

**U23 `readsOf_realizable`** · `MovesJ/U23_runRealizable.lean` ·
`ReadsOf p F n f H → Realizable H` — assembly of U20–U22 over the per-step
dichotomy (`s0+w < μ` | `= μ`; the `> μ` case excluded by coherence's window
containment). difficulty: easy given U20–U22. hypothesis_fields: none.

**U24 `readsOf_canonical`** · `MovesJ/U24_runCanon.lean` ·
`ReadsOf p F n f H → (polOM p F).IsCanonPres H` given SideReads(v) + the
canonRoot clause added to D4 (or stated with the root-normalization hypothesis).
E-phase decision: bake `zbar = canonRoot` into SideReads(v) (making runs
normalized by definition — matches §D4-R's "the classifier is run with ONE lift
rule" + rev-6 canonRoot pinning) — then this unit is a projection. difficulty:
easy. hypothesis_fields: none.

**U25 `polOM_total`** · `MovesJ/U25_polTotal.lean` · statement: at every
recentering node ν of a coherent realizable history (i.e. every node with
`ν.species = recentering` reachable in `PrefSetAny`), `∃ tL, RecenterLiftSpec ν tL`
— hence `polOM.liftOf ν` satisfies `RecenterLiftSpec`. moves_ref: §D4-R L1
(canonical-choice totality, kernel (a) — DUAL-VERIFIED at the math level:
PROJECT_STATE "kernel parts (a)+(b) DISCHARGED"); §B2-DEF (S6b′) consumers item
(ii) "the recentering lift (D.10): W = λ″ > w(Φ̂) — (I-aug) is literally the
hypothesis". deps: `Stage.hS6b` + coherence's (I-aug) chain. sketch: the spec
demands `w tL = w Φ` with digit = center at position 0; realize via hS6b one
scale down per the (S6b′) two-line recursion. **NAMED RISK (resolve FIRST at
E-phase, before any prover runs):** the scale bookkeeping — `RecenterLiftSpec`
wants `σ.w tL = σ.w σ.Φ` while `hStretch` puts C-weights in `e·ℤ`; the note's
D.10 resolves this with the eligibility side conditions (e_read = 1 reads;
which frames admit recenterings) — the unit owner must first transcribe D.10's
eligibility EXACTLY (MOVES 2583–2671) and, if the Lean node vocabulary admits
ineligible recentering nodes that the note excludes, U25's hypothesis must name
the eligibility predicate rather than all-recenterings (statement-fence: this
is a hypothesis NARROWING, needs sign-off + a note-line citation). difficulty:
HARD (escalation risk #1 for arithmetic). hypothesis_fields: none (target), or
the named eligibility predicate (fallback).

**U26 `class_fiber_welldef`** · `MovesJ/U26_fiberWelldef.lean` ·
`ClassFiberWelldef p F n N m pol P` (MovesD §3.4's Prop) — one η-class, one
classifier locus. PROOF-FIRST route: two PrefSet representatives of one class
have equal `etaData` (U18), and `SHZ ⊤` is a function of (shape, etaData,
policy-determined lifts, seed) — the seed-dependence is the honest catch:
DIFFERENT seeds may present differently; the Prop (check MovesD's final typing
at E-phase) should be consumed at FIXED presentation data. If the Prop
quantifies over jets, prove locus-equality via Theorem C(a) (both loci = the
same transported T(H,⊤) system). DEFERRABLE: D15 carries it as `hwd`; deferral
is a recorded non-discharge, not a failure. difficulty: hard. fallback: P-3.
hypothesis_fields: possibly P-3.

### Layer E — the order-0 gates (the realF2 lesson; run FIRST at E-phase)

**U27 `gate_order0_inert`** · `MovesJ/U27_gateInert.lean` · the root-only n = 2
inert history at p = 2: construct `H₀` (one root read; the inert shape's side +
residual data), a CONCRETE `PresentSeed` (the literal `baseDigit` chart; `pres i`
for i = 0 only-history; Theta trivial-free since len = 1 uses only Θ₀), fire
`jetSetup_of_seed`, then check via MovesC `C6.thmC_b`:
`Nat.card (S(H₀,⊤) ∩ box) * 2^(totalPins) = 2^(2N)` with totalPins = the inert
shape's m* — and tie the resulting stratum mass to the independently recorded
engine value (realM2's decided count for the inert shape at n = 2; the 1/4
density anchor of `gate_v2_countingDensity_inert2`). Numeric form: an `example`
with `decide`/`Nat.card` computation at N = 2 or 3 (small!); if kernel-decide
is too heavy, the recorded-count comparison goes to `verification/` Python with
the number pinned in the docstring (census stop-the-line discipline).
difficulty: medium. hypothesis_fields: none — THIS UNIT MUST BE AXIOM- AND
SEED-HYPOTHESIS-FREE (the seed is constructed concretely; that is the point).

**U28 `gate_order0_sep`** · `MovesJ/U28_gateSep.lean` · same at q′ = 3: the split
and inert root histories yield DIFFERENT masses (σ-separation through the
bridge; the V2 gate's mirror: split 1/9 ≠ inert 1/3 at the tame prime 3 — here
as the corresponding stratum-count inequality at a fixed small N). difficulty:
medium. hypothesis_fields: none.

**U29 `gate_NP`** · `MovesJ/U29_gateNP.lean` · the MovesD gate instance: for the
worked shape P̂* (MovesD §3.3's gate row), the CONSTRUCTED system's largest
equation level + 1 = 5 = `Shape.NP` — U14's arithmetic at one census-pinned
instance (`NP(P̂*) = 1 + 4 = 5, the note's own derivation`). difficulty: easy-
medium. hypothesis_fields: none.

**U30 `gate_polOM`** · `MovesJ/U30_gatePol.lean` · a concrete recentering node
(the Case-L gate's recentering read data at p = 2, transcribed) on which
`∃ tL, RecenterLiftSpec ν tL` is PROVED by explicit witness — polOM's totality
instantiated once, axiom-free (U25's non-vacuity anchor, and the D.10-arithmetic
risk's early tripwire: if even the witness instance fails to typecheck against
`RecenterLiftSpec`, the scale-bookkeeping risk fires at day one, not at
escalation). difficulty: medium. hypothesis_fields: none.

## 6. The DAG, difficulty census, escalation-risk set

```
D1 D3 D2 D4 D5 D6 D7                     (Defs; D5's zcSeed list = E-phase design duty)
 │        │  │  │
 ├─ U1 ───┼──┼──┤          U19 ← D4      U25 ← D2,D3   (U30 tripwire first)
 ├─ U2 U3 U4 U5 U6 ← D6    U20 U21 U22 ← D4,Moves-L5
 ├─ U7 U8 ← D7             U23 ← U20–22
 ├─ U11 ← MovesD.InBox     U24 ← D4
 ├─ U9 ← U7,U11,zcSeed
 ├─ U10a–d ← U9,U3–U7,zcSeed,hreal
 └─ U13 ← U1–U11
U14 ← U3,MovesD.bandS      U27 U28 ← U13(concrete seed), MovesC.thmC_b   U29 ← U14
U15 ← U13,U14,(SEED-EXIST),(hnorm)       U16 ← U15,MovesD.TW
U17a ← U25,Moves.L5_recLiftIndep,(P-1|HC1-TRANS)   U17b   U17c ← U17a,U17b
U18 (proof-first; P-3 fallback)          U26 ← U18,thmC_a (deferrable)
```

Census, flat prover-unit granularity (pre-splits counted): D1–D7 (7) +
U1–U8 (8) + U9a–c (3) + U10a–d (4) + U11, U13, U14, U15, U16 (5) +
U17a, U17b-1..3, U17c (5) + U18 (1) + U19–U26 (8, incl. U26 deferrable) +
U27–U30 (4) = **45 units**.
Difficulty: easy 11 (D1–D7, U8, U16, U23, U24) · medium 18 (U1–U7, U11, U13,
U14, U15, U17c, U19, U20, U27–U30) · **HARD 16** (U9a–c, U10a–d, U17a,
U17b-1..3, U18, U21, U22, U25, U26) — of which the PRE-DECLARED
ESCALATION-RISK SET is: **U10 (the C.1.5 step, ×4), U25 (D.10 scale
arithmetic), U21 (D.8 exponent bookkeeping), U22 (SAE strictness), U17a (stage
reconstruction)**. Expected stuck-rule firings: U10 (→ zcSeed law extraction,
the D5 fence) and U25 (→ eligibility-predicate narrowing, statement-fence).

## 7. Process notes (binding on E/P phases)

1. **Order of battle.** E-phase elaborates D1–D7 + U27/U30 FIRST (the realF2
   lesson: the concrete order-0 seed and the polOM witness instance are the
   cheapest falsifiers of the whole design — if either fails to typecheck, the
   Defs are wrong, not the provers). Then layer A, then B, then C/D in parallel.
   Gates U27–U29 gate the corpus's acceptance exactly as RealInstanceV2Gates
   gated the V2 capstone.
2. **Statement fence.** MovesC/Defs.lean, MovesD's accepted Defs, and Moves/Defs*
   are FROZEN inputs — HC-2 adds files, never edits them. Any needed change is a
   designer-round event with sign-off. The two pre-declared displayed deviations
   (§2.1 stratum-as-fresh; D2 polOM-as-choice) and the two pre-declared possible
   hypothesis adjustments (U11 InBox strength; U25 eligibility) are the ONLY
   authorized flex points; each requires the audit round's explicit ruling.
3. **Audit charge additions (beyond the standard non-vacuity/faithfulness/
   quantifier charge):** (i) rule on §2.1 and D2's deviations; (ii) check D5's
   final `ZCSeedLaws` field list line-by-line against §C C.1.5's proof — every
   field must be a quoted note display; (iii) fire P-3's mandatory `hbr`-drop
   mutation probe; (iv) verify P-1's (S6) carve-out question against GMN §2.4;
   (v) confirm no unit consumes P-1/P-2/P-3 by name (only via supplier
   hypotheses), so declaration/downgrade decisions stay consumer-invisible.
4. **Axiom gate.** If any proposal is to be declared: pin the "HN" citation
   first (§3 header), re-extract the GMN PDF lines for each cited theorem into
   `GMN_citations.md` (§P5+ entries), write the faithfulness entry from the §3
   draft, run the guardian, and add the mutation probes as compiled `example`-
   refutation blocks next to the axiom (the `OM/QpTypeChain.lean` Block-7b
   pattern). Footprint census: `AxChk_baseline` gains a MovesJ section; the
   MovesC 36/36 and every density capstone must remain Lean-core-only — any
   declared HC-2 axiom may appear ONLY in MovesJ/MovesD-discharge footprints.
5. **Codex budget.** Per the campaign ledger (90%+ used, reset Sun Aug 02):
   this blueprint's audit round runs on fresh-Fable legs now; the Codex leg is
   the FINAL confirmation, batched post-reset with the MovesS/MovesD
   ratifications.
6. **Seam registry (who unblocks whom).** HC-1 → SEED-EXIST (D5 values) and,
   if P-1 is not declared, StageTransHyp's discharge (U17a). MovesT (wave 4) →
   re-keys W4-1 `eligible` to D4's SideReads clauses and consumes U14 as NP-ID's
   ⊆ direction. MovesD E-phase core → `CanonPolicy`/`Shape`/`PrefSet`/
   `PresentNorm`/`Presented`/`Threshold` binders used verbatim here; if its
   audited types drift during its Codex ratification, U14–U18 re-elaborate
   (statements re-generated from this blueprint's semantic specs — the specs,
   not the transcribed binders, are normative).

— end of blueprint (rev 1). Next: fresh-verifier structural pass per memory rule
"plan-level adversarial passes", then the A-round.
