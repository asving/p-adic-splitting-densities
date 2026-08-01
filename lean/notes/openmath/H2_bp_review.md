# H2_bp_review — Codex adversarial review of HDISCHARGE_H2.md (blueprint pass 1)

**Reviewed artifact:** `lean/blueprints/HDISCHARGE_H2.md` (the (H2) = (FRESH)
discharge blueprint; swarm directive 5a624c3).
**Reviewer:** Codex (fresh context; repo-blind — full blueprint + charge pasted;
prompt archived at `/tmp/openmath/H2_bp_prompt.txt` during the run, header
reproduced below). **Charge:** quote-and-classify (CRITICAL / GAP / ADVISORY),
fix nothing; press hardest on (1) the §4 reduction spine + conditionality
neutrality, (2) clause (b)'s no-new-content retirement + the FreshReadsLaw
faithfulness, (3) the H2-U2 Lean laws under/overstating the prose, (4) the §2.3
as-built adjudication findings, (5) the door-2 verdict, (6) the numerics gates'
discriminating power; then list uncovered consumption faces.
**Run:** 2026-08-05 window (machine clock 2026-08-01), detached
`codex exec --json`; transcript `/tmp/openmath/H2_bp_review.jsonl`.

## Verbatim final report

(appended below on completion)
1. **CRITICAL — the reduction theorem omits `(ADM)-FULL`, although its own proof of (b) requires it.**

> “**(FRESH-RED)** `(GR-B) + (VTX-DEEP) ⟹ (FRESH)(a′) ∧ (b) ∧ (c)`”

But §3.2 says:

> “Given `(a′)` at `(D, ρ)`, **`(ADM)-FULL` at `D`**, and `(GR-B)`’s line clause … clause (b) follows.”

Thus the displayed reduction does not follow from its displayed hypotheses. `(ADM)-FULL` is a separate trusted hypothesis row, not part of `(GR-B)` or `(VTX-DEEP)`. This is especially consequential for Step 10/K1, which is not shown to assume `(ADM)`.

2. **CRITICAL — `(VTX-DEEP)` does not supply the height-transport content used to prove (a′).**

> “the finite-level transport in steps 2–3 is … `(VTX-DEEP)/(LEAK)`”

The actual §5 interface only asserts:

> “the level-N digit read of `a_{k_s}` … equals the `(GR-B)`-graded `k_s`-read”

and:

> “at every interior on-line slot … the parent’s realized conditions impose NO constraint on the height-`β_k` digit … beyond the floor.”

It does not assert that all parent height conditions become exact independent inequalities `w(a_k) ≥ g_k`, that no lower-digit or cross-slot conditions remain, or that the resulting set is a Cartesian product. Consequently §3.1 step 2 is outside the stated kernel, and `(GR-B)+(VTX-DEEP) ⇒ (a′)` is unsupported.

3. **GAP — triangularity and per-polynomial Newton-polygon formulas do not by themselves yield an axis-aligned product box.**

> “TRI triangularity reorganizes an order-i development monomial bound into per-`φ_{r+1}`-slot minima, and the minimum … is the floor `g_k`.”

A triangular change of coordinates can transport congruences into coupled conditions; it does not automatically turn a parent fiber into independent coordinate floors. The blueprint must assume the desired exact product-box conclusion and continue downstream. Calling the missing `r`-fold composition “expected mechanical” does not close this gap.

4. **CRITICAL — `(c-GR)` is overclaimed from `(GR-B)(3)+(4)+(P4)`.**

> “`(GR-B)(3)` … + `(GR-B)(4)` … identify the window’s `k_s` graded read with that cofactor value up to the march normalizers — a `ρ`-determined NONZERO constant.”

The quoted clauses identify an associated residual polynomial and preserve an order of divisibility. Neither statement, as described, determines the unit/cofactor value at a marked root. The argument also needs a precise theorem saying what the realization `ρ` fixes and a normalization/transport law—apparently at least the march clause `(2′)`. Indeed §5 itself calls the kernel the shadow of `(2′)/(3)/(4)+(P4)`. The claim that `(c-GR)` consumes only `(3)+(4)+(P4)` is not supported.

5. **CRITICAL — the conditionality-neutrality claim confuses campaign ownership with logical implication.**

> “`(VTX-DEEP)` itself is GD-2-at-≥2 content of the same campaign.”

> “the ledger loses one row and gains at most one named kernel INSIDE the `(H1)` row’s campaign perimeter.”

Being assigned to the same campaign does not make `(VTX-DEEP)` a consequence of `(H1)(a)`. `(GR-B)` is a per-polynomial graded dictionary; `(VTX-DEEP)` includes finite-level, fiberwise constancy and non-leak assertions. Until `(VTX-DEEP)` is proved from existing hypotheses, replacing `(FRESH)` by it is replacement of one open hypothesis with another, not zero hypothesis growth or discharge. It may be strictly stronger than anything the H1 campaign ultimately proves.

6. **CRITICAL — the retirement of (b) assumes an additional digit-level product law not obtained from (a′).**

> “`DigitsProdLaw W P J` — `fiberDigits` factorizes per-slot (the digit-level product-box face of `(a′)`, supplied at the engine seam)”

The stated `FloorsProdLaw` says only that one total cardinality equals a product of numbers. It does not construct a Cartesian decomposition of fibers and does not imply factorization after imposing digit reads. `DigitsProdLaw` is therefore extra content, not a proved consequence of the encoded (a′). H2-U5 cannot establish “no new open content” by assuming precisely the missing independence statement.

7. **GAP — the per-slot argument for (b) does not handle the relation between `g_k` and `β_k`.**

> “at an on-line slot `k` with `g_k ≤ β_k` … §5.1 … gives the per-digit count…”

Nothing establishes `g_k ≤ β_k` at every nonjunction on-line slot. If `g_k > β_k`, the claimed fresh `β_k` digit is already constrained by the stronger floor. If `g_k < β_k`, the slot factor `{w ≥ g_k}` contains elements outside `{w ≥ β_k}`, so the asserted per-digit count does not by itself partition the full slot count. The reduction silently assumes the exact admissible-domain decomposition it is supposed to prove.

8. **CRITICAL — count invariance is not the prose “affine function of one fresh digit with unit slope.”**

> “`FreshReadsLaw` … `J.fiberDigits ρ z q = J.fiberDigits ρ z' q`”

Balanced cardinalities do not imply that a read has the form `u·x+b` with `u` a unit, that it uses exactly one coordinate, or that its affine shift/carry is fixed by `ρ`. A nonlinear balanced map, or even an arbitrary table of equal counts, satisfies this law. Thus the Lean law loses the anchored-march affine/carry content and cannot faithfully shadow clause (b), particularly on the classifier face.

9. **CRITICAL — quantification over all natural-number digit vectors makes the uniformity laws either overstrong or vacuous.**

H2-U4 assumes:

> “`∀ k (z z' : ℕ), … card … = … card`”

and `FreshReadsLaw` likewise quantifies unrestricted `z,z' : … → ℕ`.

For a finite slot, some natural number is outside the read image and has fiber cardinality zero. Equality with every other natural number then forces every digit fiber to have cardinality zero. This contradicts a nonempty genuine slot. The advertised “uniform example” cannot satisfy H2-U4 as written unless the box is empty. The note that off-range counts vanish makes the defect worse, not harmless.

10. **CRITICAL — the Lean package has no seam between `fiber` and `fiberDigits`.**

> “`fiber : ℕ → ℕ → ℕ`”

> “`fiberDigits : ℕ → (↥W.onLine → ℕ) → ℕ → ℕ`”

No law states that `fiberDigits` counts subsets of `fiber`, that summing over valid vectors recovers `fiber`, or that these counts come from the same objects. Consequently all `FreshReadsLaw` and `JunctionPinLaw` counts can be set to zero while `fiber` remains arbitrary. The package does not encode the claimed factorization  
`(#ρ-fiber)·(window factors)`.

11. **CRITICAL — the laws are vacuously satisfiable and do not assert realization existence.**

> “`ρ < J.rhoCount q → …`”

There is no positivity law for `rhoCount`, no connection to actual parent-tower realizations, and no restriction to residue-field cardinalities. Taking `rhoCount q = 0` makes every law true. Even with positive `rhoCount`, taking every `fiberDigits` value to be zero makes both the fresh-read and junction-pin laws essentially automatic. This is fatal for a package advertised as the faithful census shadow of `(FRESH)`.

12. **CRITICAL — on-line slot counts are unconstrained by the floor laws.**

> “`∀ k ∈ W.boxSlots, k ∉ W.onLine → J.slotCount … = …`”

Clause (a′) imposes transported floors per slot, not merely off-line slots. `FloorsProdLaw` then multiplies the arbitrary `slotCount` values at on-line slots. Hence the encoded floor/product law permits arbitrary on-line charges and does not imply the CEN-J factors claimed in §2.1.

13. **GAP — several essential carrier invariants are only docstrings.**

Examples include:

> “`ℓ = ⌊n/m⌋`”

but the carrier has only `ℓ*m ≤ n`, with no upper bound;

> “`monicTop`”

but no law connects it to `m ∣ n` or the top slot;

and no law relates `W.onLine` to `D.onLineSlots`, requires on-line slots to be box slots, or relates `W.beta` to the census ledger. Likewise the LED scope inequality needed to interpret truncated natural subtraction is merely described, not assumed. The resulting laws can hold for data that are not O-9 windows.

14. **CRITICAL — the monic-top case of clause (c) is lost, not encoded.**

> “`JunctionPinLaw … := W.monicTop = false → …`”

> “At monic top `JunctionPinLaw` is vacuous … exactly M08’s pinned-to-1 accounting.”

Vacuity does not state that the top read equals the monicity constant. Nothing else in these carriers links monicity to `fiberDigits`. It may be legitimate for a later counting engine to erase that coordinate, but then `FreshClauses` is only a partial counting interface, not `(H2)=(FRESH)` as claimed.

For a free end, `∃ c` is correctly scoped per `(q,ρ)` and hence does express “ρ-determined” in the narrow logical sense. It still fails to assert that the `c`-fiber is nonempty.

15. **ADVISORY — the “relative LED charge” docstring and displayed law are not the same object.**

> “the per-slot height charge is the relative LED factor”

but the law gives an absolute count

> `q ^ (m*N - D.s (max β g))`.

A relative charge would require an ambient or baseline count and a ratio/factor comparison. This may be convertible in a fully specified model, but that conversion is absent from these skeletal carriers.

16. **GAP — the as-built F-2 adjudication goes beyond the quoted evidence.**

> “REPEATED … node data at two tower levels is mathematically realizable (nothing in OM theory forbids equal per-level records…)”

The mere fact that `nodes` is a list does not establish that a duplicate-node `EHist` satisfies all carrier laws, nor that such a history represents an intended OM tower. The blueprint appropriately calls the result “suspected” and queues U7; until that probe succeeds, the mathematical-realizability claim is unsupported. If `DictIII.FRESH` universally quantifies over every syntactically valid `EHist`, one compiled duplicate history would indeed make it uninhabitable.

The other two adjudications are substantially sound at the quoted level:

- F-1 really is trivial list-index existence.
- F-3 is plausible if the uniqueness predicate is literally equality to the output of an `Option`-valued function, but the exact field was not quoted, so “near-redundant” remains conditional on that omitted syntax.

17. **GAP — the door-2 survey rules out the listed pins, not the literature as a whole.**

> “a faithful literature retarget of the row does not exist.”

The summaries do justify that `(P4)–(P7)` do not themselves state the fibered finite-level theorem. Examining those selected statements, plus saying that no source is “known to this repo,” does not prove nonexistence of a result elsewhere in the Okutsu/Montes or local mass-formula literature. This does not damage the conservative door-1 choice, but the categorical verdict is stronger than the search evidence.

18. **CRITICAL — H2-N1 is neither necessary nor sufficient for clause (c).**

> “A junction-pin failure inflates exactly one `(q^d−1)/q^d`-shaped factor.”

Only a very particular failure—turning a fixed nonzero endpoint into a fully free uniform unit—has that factor. A pin may vary with window data, become zero on some fibers, or be correlated with other slots while preserving the same aggregate count. Conversely, a mismatch can arise from (a′), (b), ADM, normalization, or harness errors. Therefore:

> “any mismatch = a `(FRESH)(c)` countermodel”

is false, while an exact match does not establish or specifically discriminate (c).

19. **GAP — H2-N2 checks marginals, not the product-box assertion.**

> “measure the per-slot minimal attained `w(a_k)` … assert the measured floors AND the per-slot condition sets are `ρ`-independent”

Two fibers can have identical projections, minima, and one-slot digit distributions while differing by a cross-slot correlation. Such a failure violates the exact product-box content of (a′) and joint independence in (b), yet passes the proposed checks. Testing two realizations also does not falsify dependence appearing only on another realization. H2-N2 is useful evidence, but not a complete `(a′)` leak detector.

## Consumption faces not covered by the unit plan

- **Step 10 / Step 18 K1 / clause (R): not covered.** The faithful classifier/chain form is deferred to a future sign-off; U7 only diagnoses the placeholder. No unit states or proves the classifier-face corollary required by III-U3b.
- **Step 16 / clause (UB), including `q ↦ q^δ`: not genuinely covered.** The units quantify over arbitrary naturals and contain no complete-DVR, finite-field, prime-power, or scalar-extension semantics. Calling this “instantiation” does not provide the required construction/conformance theorem.
- **Step 14 / Step 18 K3: only nominally wired.** U8 supplies a binder shape, but the laws it packages are disconnected and vacuous as noted above; there is also no landed `engineStrata` seam.
- **The Step-10 CU leaf-label content is especially absent:** the blueprint explicitly says the chain/classifier twins “ride the §2.3 adjudication,” but no dispatchable or gated unit actually specifies those faithful twins.
## Disposition (H2 lead fold, same session; all edits re-probed `lake env lean` green)

| # | class | disposition |
|---|---|---|
| 1 | CRITICAL | ACCEPTED-FIXED: (ADM) attribution displayed at §0/§4 — (b)'s counting charge consumes (ADM) as CEN-J's own (H3) row, never smuggled into (FRESH-RED); Step-10/K1 face consumes no (ADM) |
| 2 | CRITICAL | ACCEPTED-FIXED: kernel WIDENED to (TRANS-DEEP) with three displayed clauses (F) floors/product, (L) leak, (J) junction — §5; every (VTX-DEEP) mention re-read |
| 3 | GAP | ACCEPTED-FIXED: §3.1 open points restated — the product-box CONCLUSION is (F), not derivable from TRI + per-polynomial formulas; only ledger bookkeeping stays "expected mechanical", inside H2-P2 |
| 4 | CRITICAL | ACCEPTED-FIXED: (c-GR) inputs corrected to (2′)+(3)+(4)+(P4) + an explicit what-ρ-fixes lemma duty in H2-P1; "PROVABLE NOW" downgraded to written-proof obligation |
| 5 | CRITICAL | ACCEPTED-FIXED: neutrality claim restated as a TRADE (one open row for a new narrower kernel), not discharge; campaign co-ownership labeled organizational; §5(ii) interface-minimization duty displayed |
| 6 | CRITICAL | ACCEPTED-FIXED: DigitsProdLaw promoted to a FreshClauses field (the (a′) digit-level core); cardinality-only FloorsProdLaw demoted to a U5 derived lemma; U5 reframed accordingly |
| 7 | GAP | ACCEPTED-FIXED: the CEN-J scope guard (g_k ≤ β_k at on-line slots, O-9 rev-3 GAP-4 scope) is now a displayed hypothesis of the consuming theorems (U5/U6) |
| 8 | CRITICAL | ACCEPTED-FIXED: package retitled the CENSUS-FACE COUNTING SHADOW (docstring + §0); the structural affine/carry residue was already priced at the (TRANS-DEEP) family in the pre-return §3.2 patch; classifier face routed to gated U10 |
| 9 | CRITICAL | ACCEPTED-FIXED: alphabet bounds (z k < q^d / B-bounded huni) added to FreshReadsLaw, SlotUniformLaw, and U4; re-probed green |
| 10 | CRITICAL | ACCEPTED-FIXED: FiberSumLaw (Σ over the F_{q^d}-alphabet box of fiberDigits = fiber) added as a package field; re-probed green |
| 11 | CRITICAL | PARTIAL REBUTTAL + FIX: vacuous satisfiability of skeletal law rows is the corpus's own Stratum1/StratumR/CensusValueRows design (hypothesis rows need faithfulness at instantiation, not intrinsic non-vacuity); the OVERCLAIM is fixed — retitled shadow, U6 displayed as the de-vacuifier (rhoCount = 1 canonical instance), engine-seam positivity duty displayed at U1 notes |
| 12 | CRITICAL | ACCEPTED-FIXED: FloorsChargeLaw extended to ALL box slots (on-line slots constrained at max(β_k, g_k)) |
| 13 | GAP | ACCEPTED, PARTIALLY FIXED BY DESIGN: hn2 (ℓ = ⌊n/m⌋ upper bound), hmono (monicTop ↔ m ∣ n), honLine_box, hks_top added as carrier laws; the full polygon-ledger tie (W.beta/W.onLine vs the ledger) is DISPLAYED as an engine-seam conformance duty — skeletal carriers cannot carry it (the BP_IV C0d precedent); LED-regime scope displayed on the charge law |
| 14 | CRITICAL | ACCEPTED-FIXED (pin display) + SUB-POINT REBUTTED: hks_top pins the monic-top junction to the erased top slot with the monicity-constant fact displayed as engine-seam content, and FreshClauses is retitled a PARTIAL counting interface; c-fiber NONEMPTINESS is not asserted BY DESIGN — empty ρ-fibers are legitimate under O-9's padding discipline (rebuttal recorded in the JunctionPinLaw docstring) |
| 15 | ADVISORY | ACCEPTED-FIXED: slotCount docstring states the absolute count and defines the relative (E″) charge as the ratio against the parent baseline |
| 16 | GAP | ACCEPTED-FIXED: §2.3 F-2 reworded — the witness needs only a carrier-valid duplicate-node term (FRESH quantifies raw EHist, no coherence guard), OM-realizability moot; stays SUSPECTED until H2-U7 compiles |
| 17 | GAP | ACCEPTED-FIXED: §3.6 verdict scoped to the search evidence; optional literature session H2-L1 added |
| 18 | CRITICAL | ACCEPTED-FIXED: H2-N1 rescoped to a COMPOUND gate (mismatch refutes the CEN-J compound, diagnosis owed; match = evidence sensitive to the free-unit failure mode, not proof); overclaims removed |
| 19 | GAP | ACCEPTED-FIXED: H2-N2 gains the exact JOINT digit-vector multiset test (product-of-marginals comparison); labeled evidence-grade |
| faces | — | ACCEPTED: gated H2-U10 (classifier-face twins, sign-off + III-U3b-coordination gated) added; clause-(UB) q = p^δ semantics displayed as an engine-seam duty; K3 wiring honesty paragraph added to the wave table |

**Post-fold state:** all 19 findings dispositioned (17 accepted-fixed, 2 with
recorded partial rebuttals); every touched Lean statement re-probed green
(`/tmp/openmath/H2_probe3.lean`). Under the repo's several-consecutive-clean-passes
bar this blueprint has ONE adversarial pass + fold: a confirming pass is OWED
before the prover fan-out consumes §6 verbatim (the swarm orchestrator's call;
the directive's minimum — one adversarial review, folded — is met).
