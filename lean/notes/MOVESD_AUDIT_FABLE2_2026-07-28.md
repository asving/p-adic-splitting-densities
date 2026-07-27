# MOVESD BLUEPRINT REV 3 — FRESH-INSTANCE CONFIRMATION AUDIT (Fable #2)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable instance #2 (no prior context; parallel to the Codex pass on identical text)
- **Scope:** `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` REV 3 (713 lines, read in full), including a
  from-scratch re-derivation of the E1–E9 injection chain against the note's own display, the
  CanonPolicy inexpressibility question, the ∀ N ≥ Nshape quantifiers, the empty case, the
  D4R_CYL deferral, and MovesC signature usage.
- **Ground truth:** `MOVES_2026-07-24.md` §D4-R rev 9 (lines 4580–5432; DUAL-ACCEPTED record at
  6809–6830 verified present), `lean/LeanUrat/MovesC/Defs.lean` (round 6), plus
  `Moves/Defs.lean`/`DefsT.lean`/`DefsL.lean` for `OrdPsiPoly`, `Stage`, `TransitionData`,
  `TransitionCoreL`, and `C6_thmC_b.lean` for the consumed theorem signature.
- **Charge:** `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` (below-the-line checklist), <CORPUS> = MovesD,
  <NOTE> = §D4-R. Quote-and-classify; fix nothing.

## 0. Verdict

**REJECT (1 critical / 1 gap).**

The rev-3 repairs are, with one decisive exception, genuine and well-made: the E1–E9 mechanism is
the note's own L11 reconstruction ("digits give each R_anch; s_r picks ψ_r; canonical lifts are
functions of node data, L1"), the monic-lead tie is the only off-tuple input, CanonPolicy really
does make `False` inexpressible, Nshape/A′/C are genuinely N-free and reproduce the gate's
N(P̂*) = 5 exactly, the empty case is faithful, D4R_CYL is a correctly pinned deferred Prop, and
every consumed MovesC signature is exact. But the new η-CLASS construction — the enabler of the
whole rev-3 "PROVED, not assumed" headline — is at the WRONG GRANULARITY: ambient-field-valued
`etaData` distinguishes Galois-conjugate presentations of one note-η, and the note's own pinned
gate (§D4-R.6) refutes the identification numerically (corpus C = 6 vs the sealed C_P̂*(2) = 3;
corpus mult ≡ 2 where the note displays mult ≡ 1 with EV-equality). Every C-carrying mass-law
unit inherits the wrong constant.

## 1. FINDING 1 — CRITICAL: `etaData`/`PrefIdx` over-refine the note's η by the residue-root choice; C is not the note's C_P̂(p)

**Offending spec (§3.2, the construction and its taxonomy claim):**

> `def EtaData (F : Type*) (P : ShapePrefix) : Type := ∀ r : Fin P.reads.length, (Fin ((P.reads.get r).len + 1) → F) × (Fin ((P.reads.get r).g + 1) → F)`
> "Everything else in the note's η is shape-pinned (Matches), derived (line by coherence+u*; (s,t)
> the canonical Bézout pair; Ranch by hRanch), or policy-determined (lifts, L1)."

and F1's moves_ref: "lifts are policy-determined, so classes ↔ η's — F1's semantic display", plus
every unit whose statement carries `Nat.card (PrefIdx n pol P)` as "C_P̂(p)" (D10, D12, D13, D3b,
D14b, D2a's `CD_eq` reading, D15's mult).

**The defect.** The taxonomy sentence omits `Node.zbar` (and with it the residue-tower embedding
into the ambient F). `zbar` is neither shape-pinned (not in `Matches`), nor derived (MovesC:
`hzbarRoot` requires only that it be *a* root of ψ — g roots exist; `TransitionData.child_field :
σ'.K = σ.nextField zbar` consumes a CHOSEN root; §C calls it "the residue root z̄ selected by the
read (D.6/D.7 witness)" — a witness, i.e. a choice), nor policy-determined (`CanonPolicy` pins
lifts only). And it LEAKS into `etaData`: (HV) ties the next read's pattern lead to
`vtx(ν) = z̄^{a−μm̂}·(vtxPoly)(z̄)`, a zbar-dependent F-value, and ψ/pat coefficient images at
depth ≥ 1 are valued through the chosen embedding.

**The note's granularity is embedding-free.** L2: children are "ALL next-node data ν = (side s,
its digit tuple, ψ, canonical lift)" — no residue-root datum; digits range in the canonical pool
𝔸_r (L11), i.e. the abstract residue quotient F_{i+1} = F_i[z]/(ψ_i), not in an ambient field
with a chosen root.

**Witness at the note's own pinned instance (§D4-R.6, P̂*, p = 2).** Take the counted history
(ψ = z²+z+1, r = 1, root digits (0,0,1)). ν₀.zbar ∈ {ω, ω²} (both roots of ψ in the unique
order-4 subfield K₁ ⊆ F). Both choices extend to full PrefSet members: the conjugated stage
(σᶜ.R := map φ ∘ σ.R, same Φ, same K₁ — φ the Frobenius, which fixes the prime-field root data)
satisfies every Stage/Transition law by equivariance; (HV) then forces the depth-1 lead
d'₁ = z̄ − r = ω − 1 vs ω² − 1 — DISTINCT F-values, hence DISTINCT `etaData`, hence distinct
`PrefIdx` classes, for what the note counts as ONE η (the canonical d'₁ = z̄ − r ∈ F₄). The map
(class) → (note-η) is exactly 2-to-1 on this shape (read 1 is a recentering, `hspecRecCenter`
pins its zbar; read 0 contributes the g₀ = 2 orbit; no digit tuple here is Frobenius-fixed since
z̄ ∉ F₂). So:

- corpus `C` = Nat.card PrefIdx = **6**, against the note's sealed, census-verified
  **C_P̂*(2) = 3** ("C_P̂*(2) = 1·1·3 = 3"); likewise 96 vs 48 at p = 3;
- corpus `mult`(x) = #classes containing x ≡ **2** on the event (the two conjugate classes'
  fibers are the SAME f-set — reading f in either frame realizes the respective class), against
  the note's gate re-derivation "mult_P̂* ≡ 1 … D4R.1-EV/D4R.4-EV hold with EQUALITY here";
- D10/D12/D13 remain PROVABLE as stated (they are internally consistent about the doubled
  constant — Σ over 6 classes of p^{nN−A} = 6·p^{nN−A}), which is precisely the trap: a
  sorry-free corpus whose "C_P̂(p)" is not the note's display "Σ_{η∈Pref(P̂)} … = C_P̂(p)·p^{nN−A(P̂)}"
  (D4R.4-SUM), and whose "equality iff mult ≡ 1" criterion (D13) evaluates OPPOSITE to the note
  at the note's own gate.

**Classification: CRITICAL** (the statements say something different from the note's displays —
wrong constant, wrong multiplicity semantics — detectable at the pinned instance; faithfulness
breach, not a provability failure). Contaminated units: §3.2 Defs (`EtaData`/`etaData`/`PrefIdx`/
`CD`), F1 (the "classes ↔ η's" display), D2a, D3a/D3b (the bound stays TRUE a fortiori but its
"C_P̂(p)" reading is off), D10, D12, D13, D14b, D15. NOT contaminated: the E1–E9 chain itself
(the injection into the pool target is correct at whatever granularity), W1/W2, the A/Nshape
ledger, D14a (the ∅ dispatch has no classes), T1a, the D4R_CYL pin, VerdictModel.

**Repair direction (for the repairer, not applied here):** quotient the class data by the
simultaneous per-read Galois action, or — cheaper and exactly parallel to the blueprint's own
lift normalization — add a deterministic residue-root rule to the canonicity clause (e.g. the
`fieldEnum`-least root of ψImage), so that each note-η has exactly one canonical presentation
chain and classes ↔ η's becomes true. Either way the gate numbers (3/48, mult ≡ 1) are the
acceptance test.

## 2. FINDING 2 — GAP: `EligibleImage`'s displayed gloss omits the irreducibility/subfield clause; as glossed, E7 is false

**Offending spec (§3.4, the `selRank` comment block):**

> "with `ψImage ν : Polynomial F` the coefficient-image of ν.ψ, `EligibleImage` the F-side
> eligibility predicate (monic, deg g, ord_· (RanchImage ν) = μ), and `lexLt` the
> coefficient-lex order through `fieldEnum` — three small Defs."

The note's eligible set is "{ψ monic irreducible : deg ψ = g_r, ord_ψ R_anch = μ_r}" (L11), and
E6's K-side subtype carries all four clauses. The F-side gloss lists three — dropping
irreducibility exactly. Neither literal reading works:

- WITHOUT irreducibility, E7 (`selRank ν < R.mbar`) is FALSE: RanchImage with four distinct
  linear factors, g = 2, μ = 1 has SIX monic ord-1 quadratic divisors, but m̄ = ⌊4/2⌋ = 2.
- WITH Irreducible-over-F, `ψImage ν` itself generally leaves the set (a deg-g ≥ 2 image splits
  over any F ⊇ F_{p^{w·g}} — e.g. the gate's quadratic over F ⊇ F₄), killing E7's "a set … that
  CONTAINS ψ" and E8's recovery mechanism.

The intended def is evidently the TRANSPORTED predicate (∃ K-side eligible lift with this image;
equivalently coefficients in `pool` + irreducible over the pool subfield) — E7's own deps line
says "eligibility over ↥σ.K ↔ over the F-image, via E3 and the coercion ring embedding", which
is correct and makes the whole chain sound. But the displayed def-gloss contradicts it, and a
formalizer implementing the gloss literally hits an unprovable (indeed false) E7. Same cluster:
`RanchImage` is used in E8's statement and inside `EligibleImage` but is not among the "three
small Defs" listed. **Classification: GAP** (misspecified/underspecified Defs dependency on the
load-bearing proved chain; the unit's intent is stated correctly elsewhere in the same unit).

## 3. What was verified and PASSED (the charge's named checks)

1. **E1–E9 re-derivation (modulo Finding 1's granularity and Finding 2's def-gloss).** E1: subfield
   of card p^w → digits satisfy x^{p^w} = x — sound. E2: roots of the monic X^{p^w} − X — sound.
   E3: range ⊆ pool + |range| = p^w ≥ |pool| → equality — sound; this correctly substitutes the
   note's L4 common-frame reconstruction at the class level. E4: `hRanch` + `hpatTop` →
   natDegree = wSide/e = the note's ℓ_r = w'_r/e_r — exact. E5: `hOrd` + `hψdeg` + E4 → gμ ≤ ℓ —
   sound. E6: pairwise-coprime irreducible powers divide Ranch → k·gμ ≤ ℓ → k ≤ ⌊ℓ/(gμ)⌋ = the
   note's m̄_r — exact match to L11's sharper bound. E7/E8: rank-in-a-finite-total-order
   arguments — sound given the repaired EligibleImage. E9: counted digits + the ONE scoped
   `hmonic` tie recover the full tuple; tuple → RanchImage (hRanch); rank → ψImage (E8);
   subtype ext — the monic-lead tie **is the only off-tuple input**, confirmed. The chain
   consumes ONLY MovesC node Props + Matches (checklist §7.6 holds; `fieldEnum` is a classical
   def, not an assumption).
2. **§0.5 adjudication accepted.** The note's only displayed off-tuple digit is the root monic
   lead ("slot 3 = the monic lead, digit 1", §D4-R.6 — a monic-box fact); the (HV)-forced
   depth-1 lead is IN the tuple and in W ("the (HV)-forced lead makes the pool bound strict —
   slack displayed"). d_r = ℓ_r + (monicTop ? 0 : 1) reproduces d₀ = 3 (ℓ₀ = 3), d₁ = 2 (ℓ₁ = 1),
   W = 1·3 + 2·2 = 7 ✓. The blanket `offSlots_forced` is gone; the scoped `Matches.hmonic` is a
   faithful interface equality. Semantically-false `monicTop` instantiations are ordinary junk
   shape data (empty PrefSet), not a soundness hole.
3. **CanonPolicy: `False` is genuinely inexpressible.** For any `pol`, re-lifting any history by
   `ν ↦ {ν with lift := pol.liftOf ν}` is IsCanon-satisfying BECAUSE `blind` makes `liftOf`
   invariant under the rewrite — and `blind` also kills the one real attack
   (`liftOf ν := ν.lift + 1`, which would have made canonicity unsatisfiable). `liftOf` as a
   function of node data is exactly L1's "the digits t_k are FUNCTIONS of the node data … the
   policy is deterministic". WHICH policy stays an open parameter (§B2-DEF/HC-1) — no def decides
   it. The per-node junk-lift normalization is documented and harmless.
4. **∀ N ≥ Nshape quantifiers.** `Nshape := 1 + max_r ⌈intercept(lineS r)⌉₊` is a correct
   instantiation of the note's "an a priori shape bound on N(P̂) is available" (every pinned
   coordinate has level ℓ ≤ htS ≤ line value ≤ intercept, offsets ≥ 0). Gate check:
   intercepts 3 (root) and 4 (depth 1) → Nshape(P̂*) = 5 = the note's N(P̂*) = 5, exactly.
   L9s's stabilization argument is sound (levels ≥ Nshape are band-free). `C` and `A′ := A n Nshape`
   are N-free by construction; D10/D12/D13 carry `(N) (hN : Nshape ≤ N) (S : Presented … N …)` —
   D4R.4's uniform quantifier with shared constants, read through the documented HC-2
   existence boundary (Nshape ≥ N(P̂), so the claimed levels sit inside the note's envelope).
   Also reproduced from the blueprint's own defs: A(P̂*) = 9 + 2 = 11 (root band: 4+3+2 = 9 —
   the 3 cluster zeros at level 0 included via floor ⊥; depth-1 band: exactly the note's level
   set {(β₀,4),(β₁,3)} = 2), matching the note's ledger.
5. **Empty case.** `CD`'s if-branch is the note's own definition-level dispatch (Pref(∅) = {∅},
   C_∅ = 1); `Pref_empty_shape` honestly displays that the History-level set is empty (the type
   has no empty chain); `A'_nil` = A(∅) = 0; `emptyFiber = univ` = S(∅,⊤) = the full box, law by
   card arithmetic — "by L5's normalized full-box display — NOT by Theorem C(b)" respected (no
   jet, no C(b) anywhere); `hN : 1 ≤ N`, `hm : m = n·N` explicit, matching L12's "for EVERY
   N ≥ 1". D14b mirrors L12's Pref = ∅ case exactly. (D10/D12/D13 degenerate to true 0 = 0
   statements at the empty shape and do NOT impersonate the ∅-law — the decomposition mirrors the
   note's own two-mechanism proof.)
6. **D4R_CYL deferral.** The pinned Prop is L6's (D4R-CYL) "S(η,⊤) = {f : η ∈ T_can(f)}"
   transported to the corpus's per-class, finite-level vocabulary (∀ i ∀ x, x ∈ fiber i ↔
   mem (reprOf i) x, at Z = ⊤). It is a def, consumed ONLY as D15's named hypothesis; no unit
   proves or assumes it as a field; kernel (a)/(b) cited as math-discharged only; (c)/VP appears
   only in `VerdictModel`, consumed by nothing (checklist §7.3 holds).
7. **MovesC signatures.** All exact: `History`/`Node` fields incl. the rev-9 `ustar`/`gam`/`pat`;
   `JetSetup (H) (n N m)` with `hm`/`hN`/`coordOf_lt`/`coherent`/`realizable`/`mstar_eq`;
   `SHZ : Locus → Set (Fin m → ZMod p)`; `totalPins`; `C6_thmC_b (J) (Z) (hZ : AdmissibleZ
   (J.Sigma H.nodes.length) Z) : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m` —
   `topLocus` (all-unpinned `DigitSystem`) satisfies `AdmissibleZ` trivially and has
   `numPinned = 0`. The shape-side band mirror is up to date with MovesC ROUND 6's fine-slot
   boundary: `bandS`'s upper edge `(lineS r).at ((c.2 / R.Dwidth) * R.Dwidth)` =
   `slotVal ∘ fineSlot` exactly; `floorS`/`prevRimS`/`htS`/`kappaS`/`innerslotS`/`strS` are
   field-exact mirrors of `staircase`/`floorH`/`prevRim`/`htH`/`kappaH`/`innerslotH`/`strFrame`;
   `lineS`'s intercept = `ustar + slope·((s0+wSide)·Dwidth)` is exactly `hLineU` + the coherence
   slope law. W1's step inequality `s0'+wSide' ≤ μ_prev` is a literal `HistoryCoherent` clause.
8. **Sweep of the rest.** D0a–c, D1c, D2a, F1, W1/W2, D4a/b, D5a/b, D6a–e, D7a–c, D8, D9, D11a/b,
   T1a, D15 — statements faithful (modulo Finding 1 where C/mult enter), sketches adequate,
   one display per unit, deps acyclic, unit count 43 and AUX count 13 verified. Non-vacuity:
   every structure is either inhabitable (`ShapeRead`/`ShapePrefix`/`CanonPolicy`), constructed
   (`PrefIdx`/`reprOf`), or a declared open surface consumed as hypothesis data
   (`Presented.jet`, `TreeModel`, `VerdictModel`) with degenerate instantiations rendered
   harmless by the hypothesis structure (e.g. a mem-empty TreeModel cannot satisfy D4R_CYL
   against nonempty fibers, D0c). The §2 ledger matches the actual open surface. Cosmetic
   only (not counted): §1's prose "(digits, factor-rank) ↦ class" states E9's injection
   backwards (the unit has the correct direction); `mem_single`'s `(h1 : _)` and `snoc`'s `…`
   are blueprint shorthand; the `fieldEnum` lex order is A fixed order rather than literally
   D.3(e)'s residue-bases order — harmless since the encoding bound is order-invariant and the
   substitution is documented.

## 4. Counts and verdict

- CRITICAL: 1 (Finding 1 — η-class granularity vs the note's η; wrong C and mult at the pinned gate).
- GAP: 1 (Finding 2 — `EligibleImage` gloss omits irreducibility/subfield clause; `RanchImage` unlisted).

**REJECT (1 crit / 1 gap).**

The rev-3 architecture is one bounded repair away from acceptance: fix the class granularity
(Galois quotient or a deterministic residue-root canonicity rule parallel to the lift rule) and
restate `EligibleImage` as the transported predicate; everything else on this pass — including
the entire E-chain mechanism, the quantifier discipline, and every gate-number reproduction —
checked clean.
