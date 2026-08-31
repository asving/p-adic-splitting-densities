# UNIT CP2 — VERDICT: THE CONSOLIDATED FGMN CITE PACKAGE STAGED (one signing
surface, three legs, all consumers wired Lean-core, source theorem numbers PINNED
by print-read of the repo PDFs) — 2026-08-31

**Deliverable:** `leanfinal/Uniformity/ChapI/I10CitePkg.lean` (17 declarations, ZERO
sorries, zero errors, zero warnings; **17/17 `#print axioms` lines exactly Lean core
`{propext, Classical.choice, Quot.sound}`** — no axiom declared, no cite consumed;
the package is STATED, never asserted).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/I10CitePkg.lean` (6 increments, each
GREEN before the next; increments 1–5 first-try, increment 6 one trivial repair);
targeted `lake build Uniformity.ChapI.I10CitePkg` GREEN (9039 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the sanctioned one-line import
between IFCG64 and I10RungLift3W.  `docs/REVIEW_QUEUE_2026-08-26.md` row 9 REWRITTEN
in place (superseded, not appended).  IFCG65.lean untouched; no git ops.

## ★★★ THE RESULT — one signing decision replaces three separate literature walls

    def FGMNCitePackage : Prop :=
      EisensteinLegStatement ∧ UnramifiedLegStatement ∧ PureFaceResidualLegStatement

with (all in `Uniformity.Density.I10CitePkg`):

    -- LEG E (= CTS2's staged surface, BYTE-IDENTICAL consumer; row 9's old recommendation)
    def EisensteinLegStatement : Prop := ∀ D : ℕ, 2 ≤ D → IFCG48.FactorCorrespondenceAt D

    -- LEG U (MFL's named missing step; hypothesis vector READ OFF FGMN Thm 6.2(2)+6.4+Cor 6.6)
    def UnramifiedLegAt (k : ℕ) : Prop :=
      ∀ (O : Type) [5 complete-DVR instances], ∀ π, Irreducible π →
      ∀ φ, IsKey φ → ∀ [IsDomain (AdjoinRoot φ)] [IsDVR (AdjoinRoot φ)],
      ∀ g, g.Monic → g.natDegree = φ.natDegree * k →
        (∀ t < k, algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) →   -- ⟺ ḡ = φ̄^k
        Multiset.Rel (fun h H => inertiaDegOf h = φ.natDegree * inertiaDegOf H
                               ∧ h.natDegree = φ.natDegree * H.natDegree)
          (monicFactors g) (monicFactors (devT φ k g))

    -- LEG R (CN2 §7 remainder item 2's TYPE PIN; hypotheses = CN2's face vector + Thm 6.4's ord_L = 1 clause)
    def PureFaceResidualLegStatement : Prop :=
      ∀ (O : Type) [...], ∀ π, Irreducible π → ∀ m N h e', 0 < m → 0 < h → 0 < e' → Coprime h e' →
      ∀ c : Coeff O m N, NPAttains c h e' 0 → NPAttains c h e' m → NPVisibleAt c h e' →
      Squarefree (mapped classResidualPoly) → ∀ a, proj O m N a = c →
        Multiset.Rel (fun g' ψ => inertiaDegOf g' = ψ.natDegree ∧ g'.natDegree = e' * ψ.natDegree)
          (monicFactors (monicPoly a)) (normalizedFactors (mapped classResidualPoly))

where `mapped classResidualPoly` = `(classResidualPoly π c h e').map (resFieldXEquiv O).symm`
over `ResidueField O` (always a field — no instance gymnastics in the Prop; only
normalization-robust reads consumed, see caveat D).

## The source (print-read THIS UNIT, 2026-08-31, both repo PDFs via pdftotext)

FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015), author PDF
`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`:
* **Thm 6.2** (p. 25 of the author PDF): theorem of the polygon at factor level —
  `φ |_µ F ⟺ v(φ(θ)) > µ(φ)`; then `N_{µ,φ}(F)` one-sided, `F ∼_µ φ^ℓ`,
  `deg F = deg φ^ℓ`, `R(F)` a power of the maximal ideal `R(φ)`.
* **Thm 6.4** (p. 27): THE GENERALIZED-HENSEL DISSECTION —
  `g = g₀ · φ^{ord_φ(g)} · ∏_{(ν,L)} g_{ν,L}`, `deg g_{ν,L} = e_ν · ord_L(R_{µ_ν}(g)) · deg L · deg φ`,
  and `ord_L = 1 ⟹ g_{ν,L}` irreducible.  (FGMN's own words: "It has to be considered
  as a generalization of Hensel's lemma.")
* **Cor 6.6** (pp. 28–29): `e(φ) ∣ e(F)` + the canonical residue-field embedding
  `F_φ ↪ F_F` — the per-factor `(e, f)` reads.
Companion: AGNPRW, *Polynomial factorization over Henselian fields*, FoCM 2024
(`docs/references/s10208-024-09646-x.pdf`, the row-1 cite's own source): Thm 2.11
(Barnabé–Novacoski tangent-direction criterion) + Thm 4.17 (the Henselian Newton
polygon dissection).  All quotes verbatim in `I10CitePkg.lean`'s module docstring.
All three legs are instances of Thm 6.4 at an order-1 base valuation: leg E at the
Eisenstein key (slope `1/e'`, `e = e'`, `f = 1`), leg U at an unramified key lift
(`e = 1`, `f = d`), leg R at `φ = x` on a spanning face with the `ord_L = 1` clause.
HONESTY: the hypothesis vectors were read OFF the source (leg U's cell condition is
Thm 6.2(2)'s branch concentration in digit currency; leg R's Squarefree is Thm 6.4's
own irreducibility clause) — not engineered from the consumers; where the source is
BROADER than the consumers (leg R at `e' = 1` = the integer-slope/Hensel instance;
leg U at `d = 1`), the Props carry the broader source form and consumers restrict.

## Consumers, ALL wired Lean-core (the reductions — what signing buys)

| consumer | theorem in I10CitePkg | from |
|---|---|---|
| CTS2's surface, verbatim | `factorCorrespondence_of_package` | leg E (projection) |
| the complete pointwise scaling law | `cellTypeScaling_of_package` (+ `deepWildTypeScaling_of_package`) | leg E + IFCG47/48's D = 0,1 witnesses |
| DTR's decision-transport iff, every depth | `transport_decidedAt_iff_of_package` | leg E |
| ER4's D = 2 dd supply | `cellTypeScalingAt_two_of_package` | leg E |
| ★ MFL's unramified pointwise law | `unram_typeScaling_of_package` : `typeOf g = unramScaleType d (typeOf (devT φ k g))` | leg U + the NEW Lean-core multiset reduction `typeOf_eq_unramScaleType_of_rel` (the `(e,f) ↦ (e,d·f)` bookkeeping machine-checked, ring-generic; `efPair_eq_unramScale` shows `e(L/K) = e(L/K')` is pure arithmetic) |
| ★★ the mixed-tower composite | `tower_typeScaling_of_package` : `typeOf g = towerScaleType e' d (typeOf G₂)` over `O → AdjoinRoot φ → AdjoinRoot (eisKey π₁ w₁ e')` | legs U + E composed through IFCG64's `scaleType_unramScaleType_comm`; `π₁ = algebraMap π` irreducible via IFCG29 — THE `(1, d)` frame laws' missing pointwise step in exactly MFL's prescribed currency |
| ★★ the census pure-face decision socket | `decidedAt_of_squarefree_residual_of_package` : `DecidedAt O m ⟨factors.map (fun ψ => (e', deg ψ))⟩ N c` | leg R — a genuine class-level decision (classResidualPoly is lift-independent); CN2's `e' = m` criterion is its degree-1-residual instance |

Teeth (Lean-core, no cite): `unramifiedLegAt_zero` (leg U at `k = 0`, outright) and
★ `pureFaceResidualLeg_irr_instance` — leg R's conclusion DERIVED at irreducible
residual from the landed `IFCG37.decidedAt_of_spanning_irr`; this machine-validates
the Rel currency against the landed corpus (if leg R's statement were mis-shaped,
this proof would not have closed).

## FAITHFULNESS ENTRY DRAFTS (for docs/AXIOM_FAITHFULNESS.md — NOT enacted; to be
appended verbatim at signing, C66b entry format)

> ## `fgmn_cite_package` (I10CitePkg, PROPOSED — not yet declared)
>
> **Ports:** FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015)
> 30–75, DOI 10.1016/j.jalgebra.2014.12.022 — Theorem 6.2 (theorem of the polygon,
> factor level) + Theorem 6.4 (the generalized-Hensel dissection: block factorization
> indexed by the residual's maximal ideals, degree formula, ord-1 irreducibility
> clause) + Corollary 6.6 (`e(φ) ∣ e(F)`; residue-field embedding).  All three
> print-read VERBATIM 2026-08-31 against the author-posted PDF (repo copy); quotes in
> the I10CitePkg.lean module docstring.  Companion: AGNPRW FoCM 2024 Thm 2.11 +
> Thm 4.17 (repo PDF; same source as the signed row-1 `agnprw_termination`).
> **Faithfulness surface (three legs, one conjunction):** leg E = the Eisenstein-key
> instance (corpus dictionary at IFCG48: `eisKey` ↔ the degree-`e'` key at slope
> `−1/e'`; lattice+box ↔ branch concentration; Rel ↔ the OM matching with
> `(e,f) ↦ (e'e, f)`); leg U = the unramified-key instance (`IsKey φ` ↔ FGMN's
> depth-0 key polynomials; digit condition ↔ `ḡ = φ̄^k` = Thm 6.2(2)'s branch
> concentration; Rel ↔ the matching with `(e,f) ↦ (e, d·f)`, Cor 6.6(2)); leg R =
> the `φ = x` spanning-face instance (`classResidualPoly` ↔ `R_{µ_ν}(g)` up to
> normalization; `Squarefree` ↔ all `ord_L = 1`; Rel ↔ Thm 6.4's degree formula +
> irreducibility clause + Cor 6.6's `(e, f) = (e', deg L)` pin).  The import carries
> the corpus's class-visibility fences, strictly SHRINKING the source's scope — the
> safe direction — EXCEPT the two recorded fringes below.
> **Caveats requiring adjudication at signing:** (A) the `(e, f)` currencies are order
> gcd reads (`inertiaDegOf`), tied to the field invariants by the standard
> any-order-with-fraction-field-L reading — trusted, not formalized (IFCG48 caveat 1);
> (B) legs E/U quantify over inseparable/repeated-factor `g` while the classical
> statements assume separable `g` — either confirm the cells exclude the fringe or
> add a separability hypothesis (statement-shape decision; IFCG48 caveat 2); (C) the
> corpus conclusions are in `devT` transform currency while Thm 6.4 is indexed by
> residual maximal ideals — the identification is the trusted dictionary (same genre
> as the signed C66b dictionary); (D) leg R consumes only normalization-robust reads
> (degrees, squarefreeness), so FGMN's residual-normalization freedom (Cor 4.9(3))
> is harmless — recorded against the A-C.24″ twist precedent; (E) sufficiency only.
> Owner secondary review: REVIEW_QUEUE row 9 (rewritten 2026-08-31).

(If the owner prefers per-leg axioms: split the entry into
`fgmn_eisenstein_correspondence` / `fgmn_unramified_correspondence` /
`fgmn_pure_face_residual_pin`, each inheriting the shared Ports paragraph and its
leg's dictionary + caveat rows.  Consumers fire from the conjunction or any
sufficient subset — leg-E-only recovers exactly CTS2's staged reach.)

## THE POST-SIGNING MASTER (charge 3's recompute)

The census master is `IFCG62.decidedSliceAt_all_of_MASTER_MIXED`, resting on four
premises.  With `FGMNCitePackage` signed:

    ∀ n, DecidedSliceAt n   ⟸   {SIGNED: FGMNCitePackage}  +  the following, ALL cite-free:
      1. hFC   : ∀ D ≥ 2, FactorCorrespondenceAt D
                 → **CLOSES OUTRIGHT** (`factorCorrespondence_of_package` — leg E is
                 this premise verbatim).  Row 9's original gate: DONE at signing.
      2. hMixed: the per-frame `MixedFaceLaw m h e' d σ` family (composite m ≥ 6)
                 → does NOT close outright, but its remaining content is now
                 SEPARATED BY GENRE:
                 · `(1, d)` frames: pointwise step SUPPLIED (`tower_typeScaling_of_package`
                   + `unram_typeScaling_of_package`); remaining = the ZcURLim squeeze
                   assembly (IFCG51 §3 replay at the compositum with IFCG64's landed
                   transports/counts) — Lean-core work, no literature.
                 · pure-face legs with squarefree residual: decision SUPPLIED
                   (`decidedAt_of_squarefree_residual_of_package`); remaining = counts
                   + assembly — Lean-core.
                 · ⚠ `(h ≥ 2, 1)` frames (and the ramified half of `(h ≥ 2, d ≥ 2)`):
                   **NOT COVERED BY THE PACKAGE** — the slope-`h ≥ 2` deep-primary
                   recentring step has no statement currency yet (the general-slope
                   key `X^{e'} − wπ^h` generates a non-DVR order; MFL's Bézout-ring
                   route must be BUILT first).  This is the ONE surviving pointwise
                   literature-genre gap, and it is a carrier-construction gap before
                   it is a cite gap.
      3. hSD/hPD (multi-σ convolution defects): UNTOUCHED (different genre, no cite
                 content identified).
      4. hLeafSub (multi-σ leaf sub-face law): UNTOUCHED (same).

Net: post-signing, the master's row-9 premise is gone; every remaining obligation is
either Lean-core assembly (squeezes, counts, partitions), a different-genre law
(convolution/leaf), or the ONE named not-yet-statable pointwise step (slope-`h ≥ 2`
deep-primary), which is flagged in the file's honest scope, row 9, and here.

## Honest remainder (this unit's fence)

1. The package is UNSIGNED — nothing downstream fires unconditionally until the
   owner declares the axiom (or per-leg axioms) with the caveat adjudications.
2. The slope-`h ≥ 2` deep-primary recentring leg: NOT in the package (above).
3. Caveat B's separability adjudication may change leg E/U statement shapes at
   signing (as already flagged by CTS2) — the reductions were built so that a
   separability rider threads through `Multiset.Rel` untouched.
4. No `ZcURLim` assembly, count, or frame law was proved here (statement-authoring
   unit); the master is UNCHANGED until signing.

## File map (`leanfinal/Uniformity/ChapI/I10CitePkg.lean`, 17 declarations)

§1 `EisensteinLegStatement`, `UnramifiedLegAt`/`UnramifiedLegStatement`,
`PureFaceResidualLegStatement`, `FGMNCitePackage` · §2 the five leg-E consumer
wrappers · §3 `efPair_eq_unramScale`, ★ `typeOf_eq_unramScaleType_of_rel`,
★ `unram_typeScaling_of_package`, ★★ `tower_typeScaling_of_package` ·
§4 ★★ `decidedAt_of_squarefree_residual_of_package` · §5 `monicFactors_one`/
`isKey_X`/`mem_sideSet_iff'` (private replicas, corpus practice),
`residual_natDegree_of_spanning` (the spanning-face degree pin WITHOUT `MinFaceAt`'s
`h < e'` restriction), `unramifiedLegAt_zero`, ★ `pureFaceResidualLeg_irr_instance` ·
AxCheck footer (17 lines).  Imports: IFCG48 + IFCG64 + IFCG37 + IFCG29.
Aggregator: one line in `Uniformity/ChapI.lean` (IFCG64 → I10CitePkg → I10RungLift3W).

## New definitions (trust boundary — flag for review)

`UnramifiedLegAt`, `PureFaceResidualLegStatement`, `FGMNCitePackage` (statement
carriers — the whole point of the unit; reviewed via row 9).  `EisensteinLegStatement`
is definitionally IFCG48's staged form.  NO landed statement was changed; IFCG48,
IFCG23, IFCG37, IFCG64 all byte-untouched.

## Repair log (1 error round total)

1. Increment 6: `omega` couldn't see through the `sideMax` def in the spanning-face
   degree pin — `unfold sideMax` before `le_antisymm` (IFCG64's own incantation,
   initially dropped in replication).  Also increment 2 (pre-verify fixes, same
   pass): `FactorizationType` resolves unqualified inside the namespace (not
   `Uniformity.Density.FactorizationType`); an unused `hG` binder dropped from
   `typeOf_eq_unramScaleType_of_rel` (the Nat-division bookkeeping needs no
   positivity of `deg H`, so the reduction is one hypothesis leaner than IFCG48's
   ramified analogue).
