# IFK — THE INSTANCE-FAITHFULNESS KERNEL (design blueprint, 2026-07-31)

**GATE (read first): this blueprint goes to Codex plan-review BEFORE any prover
dispatch.** No Lean edits were made by this unit; every statement below is a design,
keyed to compiled carriers by file:line at HEAD. Authorization context: the /goal
standing synthesis duty (BRIDGE_ADJUDICATIONS_2026-07-30.md §AUTHORITY UPDATE) +
the Verification-Round-1 convergence record (ibid. §VERIFICATION ROUND 1, final
paragraph). Evidence corpus consumed in full: `notes/openmath/M02-count-tie_fable.md`,
`M05-exhaust_fable.md` + `V2_m05_verify.jsonl`, `M06-vp-sound_fable.md`,
`M12-cl2-route_fable.md` + `V1_m12_verify.jsonl`, `M18-realization-complete_fable.md`,
`M03-read-locality_fable.md` (fence event 25), and fence events 23–27
(BRIDGE_ADJUDICATIONS §OPEN-MATH FLEET COMPLETE).

## 0. The observation this kernel compiles

Five independent reductions, produced by five separate prover fleets and sharpened
by two adversarial Codex verifications, all terminate at the SAME missing object:

* M02 (count_tie): reduces to cylinder law CYL = open lemmas **L1–L3** — per-site
  read locality, no-new-runs-on-the-fiber, realization transfer (M02 §5).
* M05 (env_tendsto): semantic-classifier exhaustion PROVED with rate at every prime
  (verifier-confirmed core, V2 items 5–8); residual = **OL1-ii/OL2**, the agreement
  seam "the project's certification predicate accepts where the canonical OM run
  terminates" (M05 §5; V2 critical 2).
* M06 (vp_sound): after the NsFree repair (fence events 24/26, same root cause),
  reduces to **OL-1** (certified-level determinacy) + **OL-2** (assembly) + **OL-3**
  (ALIGN/GMN dictionary) + two literature legs (M06 §4, §VERDICT).
* M12 (cl2_route): assembly fully compiled (KD5/KD6/KD10); residual = engine
  interface **(X1)–(X4)** (M12 §2.1) — and V1's two criticals are exactly
  (i) an **inStratum realization theorem** (inStratum contains ONLY branch
  histories/prefixes) and (ii) the **tree/iteration correspondence** (V1 items 8–10).
* M18 (RealizationComplete): equivalent (compiled, Lean-core) to the one-step law
  **MarkGraft**, true at the instance conditional on duties **(I0)–(I3)** — realized
  fibers, faithful census, level coherence, reading coherence (M18 §2–§6).

Every one of these residuals is an instance of ONE theorem family:

> **IFK.** The built classifier instance — the run-extension tree models
> (`MovesD.canTreeModelN`, TreeCan.lean:368) with decode `canDec`, dressed to the
> bridge tower and consumed through `bridgeCanonical` (BridgeD7_canonical.lean:55),
> `bridgeTree` (BridgeD3_treeCarrier.lean:94), and the `XFamily` surface
> (`inStratum`, MovesX/Defs.lean:207) — **faithfully realizes the semantic /
> algorithmic Okutsu–Montes object** T_can(f): its reads are the OM reads at
> bounded precision, its realized runs are exactly the OM branch prefixes, and its
> halting verdicts are the true factorization data.

The kernel is stated as four faces (§1). The literature anchor for the precision
half is Bauch–Nart–Stainsby Theorem 3.13, pinned by the M05 verifier
(V2_m05_verify.jsonl item 8) — drafted as the 5th literature-axiom candidate in §3.2.

---

## 1. The statement family (the four faces, in corpus vocabulary)

Standing preconditions for all faces: p prime, n ≥ 2, f monic of degree n off
`discZero n p`; trees range over **ns-free** carriers (`MovesT.NsFree`,
MovesT/Defs.lean:1534). The NsFree restriction is load-bearing, not cosmetic:
K-RUN and K-HALT are REFUTED on ns-leaf trees by the exact-square family
(M02 §2, PARI-verified) and the (x+p)² witness (M06 §2, PARI-verified) — the
fence-event-24 carrier repair (add `MovesT.NsFree` to `bridgeTree`) is a
PREREQUISITE of the kernel, not a consequence (it awaits Asvin's naming; the
kernel design proceeds statement-side regardless).

### Face K-DICT (the dictionary carrier)

> A correspondence Θ between corpus chain histories (the `MovesT.VTree` node-data
> chains; realized runs read via `MovesJ.ReadsOf` on `canDec x`) and GMN types of
> order r (GMN Def. 2.3 / types-with-representatives, arXiv:0807.2620v2 numbering
> per `docs/GMN_citations.md`), matching invariants: (accE, accF) = (e₁⋯e_r,
> f₀f₁⋯f_r); saturation accE·accF = d ⇔ ω = 1; recentering-population nodes
> (`recT1`/`t4`) ↔ same-degree refinement steps.

Bindings: this is M06's OL-3 "dictionary debt" (M06 §4.2), verbatim the same open
object as the ALIGN dictionary carried by census item 16 / `KT.cl15_align`
(DefsLedger.lean:181; consumption seam already machine-checked in
`LeanUrat/GMNIndex.lean` per M15-x1a-align-gmn_AXIOMDRAFT_2026-07-31.md), and
verbatim V1's critical (ii) "tree/iteration correspondence unproved" (V1 item 8:
the refutation of M12's Codex proof is precisely that "same-key-degree refinement"
was matched by name, not by theorem). ONE shared carrier, never re-derived per row
(the dedup discipline: M06 §4.2 "it should be ONE shared lemma, not two").

### Face K-READ (per-site bounded read; the precision face)

> For every lawful history site (H, ν) there is a modulus L(H, ν) — computable
> from node data alone; the corpus's candidate is
> `(shapeOfH H n).Nshape ⊔ siteLevel n (some H)` (M02 §4 repair display) — such
> that whether `ReadsOf (canDec x) (H·ν)` holds depends only on x's digits below
> slot n·L(H, ν), uniformly across working levels ≥ L(H, ν) (through the compiled
> layout dressing `blockInterleave`, MovesT/ReadLocality.lean:168).

Two tiers, honestly forked:

* **K-READ-thr** (tree-intrinsic modulus, `VTree.thr`): what `seam.count_tie`
  (DefsLedger.lean:241) as typed needs — project mathematics, NOT covered by any
  citation (M02 §5 literature adjacency: "count_tie as typed pins the threshold to
  `VTree.thr`"; the discriminant-based literature bounds cover only a weaker row).
* **K-READ-δ** (discriminant-keyed modulus, δ + 1 with δ = v_p(disc f)): the
  BNS Theorem 3.13 anchor (§3.2). Sufficient for M05's OL2 and for every consumer
  that tolerates a max(thr, 2v(disc)+1)-genre threshold; NOT sufficient for
  count_tie as typed without either proving K-READ-thr or a re-key (statement
  change ⇒ sign-off).

CRITICAL SHAPE CONSTRAINT (the M03 lesson, fence event 25): the face MUST be
per-site. The all-sites-uniform closure `BridgeReadLocality`
(BridgeD5_transferRow.lean:196) is FALSE at the intended instance — M03's
Eisenstein family f_N = X² + p^N against the empty VTree (thr = 1) defeats every
tree-keyed cutoff, "no choice of tree-keyed threshold can repair the statement"
(M03 headline). Any prover unit that drifts back to a per-tree quantifier is
pre-refuted; the countermodel gate (IFK-U1, §4) compiles this fence first.

### Face K-RUN (roster/realization faithfulness)

> At every level N and box x, the realized run set on `canDec x` is EXACTLY the
> level-N truncation of the canonical semantic tree T_can(canDec x):
> (no-phantom) every realized τ-pruned history is a prefix of a genuine OM branch
> of T_can; (no-missing) every OM branch prefix whose resolution level
> (D4R.4/L12's N(η,⊤)) is ≤ N is realized; and realized fibers are nonempty loci
> (every formal fresh-assignment chain from a zc history has a witnessing
> polynomial in its digit cylinder).

Bindings — this single face is:
* V1's critical (i): the **inStratum realization theorem** — `(X.gmn p).inStratum
  f H` (MovesX/Defs.lean:207) contains ONLY branch histories/prefixes ("additional
  data, not derivable from XFamily", V1 item 9); closes the quantifier over-reach
  that killed the Codex M12 proof and gates `WeightChargeFullP`
  (MovesX/Defs.lean:372) as consumed by KD10 (Kernels/KD10.lean:60).
* M18's duties **(I0)** (realized-fiber build), **(I1)** (faithful census), and
  **(I2)** (level coherence — which is K-READ supplying finite moduli) (M18 §6.2);
  (I3) is definitional once tmark is reading-built. Through the compiled
  `realizationComplete_of_markGraft` (M18 §7) this discharges
  `RealizationComplete` (MovesV/V2_valB.lean:272).
* M02's **L2** (no new runs on the fiber, bounded) and **L3** (realization
  transfer = the `TransferRow` shape) (M02 §5).
* M12's **(X1)** (tracked cluster & resolution radius: the engine cell refines to
  a disk around a key root at radius w − C_φ — the no-phantom direction read
  through the Okutsu proximity bound) and **(X4)** (first-read wildness =
  `RecImpliesWild`, the root instance of no-phantom) (M12 §2.1, §5).
* `RunRealizerExists` (MovesD/R7_polFillReduction.lean:18) — the nonempty-locus
  clause verbatim; unblocks `canPolicyC_pin` and the R7 designer-data path.
* M05's **OL1-ii** first half: the terminated canonical run is realized/accepted
  by the built certification predicate (M05 §5).

### Face K-HALT (verdict soundness at halts)

> At an ns-free leaf of a realized run, the halting verdict is the true
> factorization data of every lift g: a (τ-hen) leaf's factor is irreducible
> unramified with (E, F) = (1, deg ψ) [(HEN-LIFT), M06 §4.1 — Hensel coprime
> lifting + unramified read-off; plausibly Mathlib-provable via
> `HenselianLocalRing`]; a (τ-irr) saturated leaf's cluster factor is irreducible
> with (e, f) = (accE, accF) [(OM-SAT), M06 §4.2 — GMN Cor. 3.8 + Def. 3.9,
> pinned in `docs/GMN_citations.md`]; and the leaves of a complete tree account
> for ALL of g: g = ∏(Hensel factors)·∏(cluster factors), so type(g) =
> typemult(T) [(ASSEMBLY) = M06's OL-2, GMN Def. 3.10/eq. (37) + Cor. 4.19 +
> defectlessness of ℚ_p].

Also binds M12's **(X3′)** (singleton certificate threshold r ≤ 2v(f′(θ)) + 1:
the Hensel–Newton certificate (D3) firing at the (τ-hen) cap N_V = 1) (M12 §2.1).

### What the kernel deliberately does NOT contain

* M12's **(X2)** lattice denominator D(n) (`dnLattice` duty) — a quantitative
  climb law, not a faithfulness statement; stays its own row (M12 §5 item 2).
* The HMC domain-factorization kernel — M18 §2 proves MarkGraft is disjoint from
  it ("domains vs. mark readings"; `witTE` separates them).
* Drainage mass accounting (ns-null, `ka4c_nsFiberUnion_null`) — already landed.
* The E0/escape spectral kernel — M05 §6 records it is NOT needed for drainage.

---

## 2. The derivation map (which residual follows from which face)

Notation: [P] = K-READ (tier noted), [R] = K-RUN, [H] = K-HALT, [D] = K-DICT.

| # | Residual (binding) | Faces | Implication sketch (evidence) |
|---|---|---|---|
| 1 | M02 L1 | [P]-thr | verbatim: L1 IS the per-site face at modulus L(H,ν) (M02 §5) |
| 2 | M02 L2 | [R] | no-phantom on the fiber: every realized run on a lift of x ∈ Φ_t(V) is a chain of V or a rostered extension — the bounded no-new-runs clause (M02 §5) |
| 3 | M02 L3 / `TransferRow` (BridgeD5_transferRow.lean) | [P]+[R] | "L1+L2 assembled" (M02 §5); `transferRow_of_readLocality` (BridgeD5:513) already runs the composition — re-point it at the per-site face |
| 4 | CYL ⇒ `seam.count_tie` (DefsLedger.lean:241) | [P]-thr+[R] | M02 §3 Theorem: CYL(V) ⇒ (SCALE_T) via the p^{n(N−t)}-to-1 projection; Lemmas A/B already reduce the row to (SCALE_T) from compiled TreePin fields. PRE-REQ: fence-event-24 NsFree carrier repair |
| 5 | `canonical_stable` supply + `VPSound` satisfiability | NsFree+[P] | M02 §2 corroboration (ii)/(iii): one repair rescues all three; stability then rides the per-tree transfer (M06 §3 post-repair sanity) |
| 6 | M05 OL1 ⇒ `BK.env_tendsto` (BridgeKernels.lean:230) general n | [R]+[P] + AX-GMN | OL1-i = GMN Cor. 4.19 termination (inside the existing trusted perimeter); OL1-ii = the run terminates with finitely many reads, all below N(f) [P], and the built predicate accepts the realized run [R]; then Prop 5.1: never-decided ⊆ {disc = 0}, Haar-null (M05 §5, with V2's correction folded in: OL1 is SUFFICIENT, not equivalent — a.e. suffices) |
| 7 | M05 OL2 (rates at general n) | [P]-δ+[D] | BNS 3.13 gives N(f) ≤ v_p(disc f) + 1 on the BNS object; [D] transports to the corpus run; then Theorem E's argument with ⌈(N−B)/A⌉ (M05 §5 OL2; V2 item 8) |
| 8 | M06 OL-1 (LOC, certified-level determinacy) | [R]+[P] | every lift realizes the same complete halted tree: [P] pins each read below its modulus, [R] forbids phantom/missing runs on the congruence class (M06 §4.3; the HC1 spine CL12_ncl/CL13_lvlDet supplies the compiled digit mechanics) |
| 9 | M06 OL-2 (ASSEMBLY) | [H] | verbatim the (ASSEMBLY) clause; fiberAt clauses (v)/(vi) give the degree checksums (M06 §4.4) |
| 10 | M06 OL-3 (dictionary) | [D] | verbatim; SHARED with cl15_align — one lemma (M06 §4.2) |
| 11 | `BK.vp_sound` (BridgeKernels.lean:235) | [R]+[H]+[D] + NsFree | (VPS, ns-free) = (LOC)+(LEAF)+(ASSEMBLY) (M06 §1, §4); (LEAF) = (HEN-LIFT)+(OM-SAT) via [D] |
| 12 | inStratum realization (V1 critical (i)) | [R] | verbatim the no-phantom clause at the XFamily surface; upgrades M12's §3 conditional count to `WeightChargeFullP` as quantified (V1 items 9–10) |
| 13 | M12 (X1) | [R]+[D] | cell ⇒ disk at radius w − C_φ: the realized cell's members track the key root — the proximity reading of no-phantom (M12 §2.1, §5 item 1) |
| 14 | M12 (X3′) | [H] | singleton cluster ⇒ Hensel–Newton certificate fires within slack κ₀ = 1 (M12 §2.1) |
| 15 | M12 (X4) / `RecImpliesWild` | [R] | root-level no-phantom: a continuing node presupposes a repeated residual factor (M12 §2.1); KD2a compiled glue |
| 16 | tree/iteration correspondence (V1 critical (ii), item 8) | [D] | the one-to-one counting theorem between `recT1`/`t4` nodes and BNS same-degree refinements — the [D] carrier extended by the population clause |
| 17 | M18 (I0)/(I1)/(I2) | [R] (+[P] for (I2)) | verbatim (M18 §6.2); (I3) definitional at reading-built tmark |
| 18 | `MarkGraft` ⇒ `RealizationComplete` (V2_valB.lean:272) | [R] | compiled `realizationComplete_of_markGraft` (M18 §7, Lean-core, scratch-checked); MarkGraft itself = re-indexing under (I0)–(I3) (M18 §6.1) |
| 19 | F-chain TV_F2–F6 (MovesV/, 10 sorries at HEAD) | via 18 | TV_F2.lean:51 names `RealizationComplete` as its blocking row |
| 20 | `RunRealizerExists` (R7_polFillReduction.lean) | [R] | nonempty-locus clause; unblocks `canPolicyC_pin` — and thence the R7 designer data that currently blocks ALL compiled countermodels at the instance (M06 caveat, M02 §2 flagged step) |

Consistency note (countermodel closure): every compiled/PARI countermodel on
record is EXPLAINED by the kernel, none contradicts it — the M02/M06 ns families
violate the NsFree precondition; M03's Eisenstein family violates only the
all-sites closure, not the per-site face; M18's `HmcToy` violates (I1) by
construction (decoupled composite censuses, M18 §1); the X1B 155,648-violation
countermodel killed per-node SUMMING, which no face performs (M12 §2.4).

---

## 3. The discharge plan

### 3.1 Provable TODAY at n = 2 from the compiled corpus

* **The MarkGraft layer, in full** — M18 §7's scratch module (`MarkGraft` def +
  `realizationComplete_of_markGraft` + `markGraft_of_realizationComplete` +
  `realizationComplete_iff_counting` + `not_realizationComplete_toy`) compiled
  Lean-core against HEAD; land verbatim (M18 §8 disposition 1). Zero new math.
* **K-RUN at length ≤ 1, n = 2, p = 2** — `TV_A5b_forge.lean` already compiles two
  realizable root nodes over `G1_toyGate`'s `toyStage` with `child_cover` EXACT
  (TV_A5b_forge.lean:479; FORGE-B record, BRIDGE_ADJUDICATIONS §FORGE ROUND):
  the first compiled instance of the no-missing clause. Extend to the kernel's
  length-1 statement over `canTreeModelN` at (n, p) = (2, 2)/(2, 3).
* **K-READ chart face** — definitionally true at the bridge instance
  (`bridgeChartStd_pin` compiled; M03 §1: "no open mathematics").
* **K-READ digit mechanics** — the HC1 carry-algebra spine `CL12_ncl`
  (no-cancellation) + `CL13_lvlDet` (level detection) is compiled (M06 §4.3);
  what remains is transport to `bridgeTm`, shared with the M03 (K1)/(K2) forms.
* **The n = 2 envelope** — `hExhaustP`'s (⌊N/2⌋+1)·p^{−(N−1)} bound is proved
  in-corpus (M05 §4.1 check), i.e. K-READ-δ's CONSEQUENCE at n = 2 is already a
  theorem; the kernel only owes the general-n statement.
* **The M12 assembly** — KD5/KD6/KD10 + KD2a compiled; the faces plug in without
  restatement (M12 §2.3 assembly, "checked against the compiled carriers").

HARD BLOCKER, stated honestly: `MovesD.canPolicy` is designer-sorried at HEAD
(M02 §2 flagged step; M06 caveat), so NO kernel face can be COMPILED-discharged
at the full bridge instance today — n = 2 discharges run at the toy/forge/
`canTreeModelN` instances, and the bridge-instance discharge waits on the R7
designer data, which itself unblocks via `RunRealizerExists` (= a K-RUN
corollary, derivation row 20). This circularity is benign — RunRealizerExists is
provable at the toy instances first — but must be sequenced (IFK-U3 before U7).

### 3.2 The BNS 3.13 literature axiom — draft (5th candidate)

Existing perimeter: AX-GMN (index theorem), `PadicMeasure.AX_cellRecursion`
(Denef–Igusa), `AX_integralClosure_dvr` (Serre, declared + guardian-PASSED
2026-07-31), and the M15 GMN-finsum face (drafted, axiom keyword WITHHELD).
Candidate 5:

> **AX_BNS_precision (DRAFT — DO NOT DECLARE; statement to be pulled from the
> published text first).** Let p be prime and f, g ∈ ℤ_p[x] monic separable of
> degree n with δ := v_p(disc f). If f ≡ g (mod p^{δ+1}) coefficient-wise, then
> every OM factorization of f is an OM factorization of g — the OM
> representations (types with their Okutsu invariants (e_i, f_i, λ_i)) attached
> to f remain valid for g; in particular the OM trees correspond and
> σ(f) = σ(g).

* **Source**: J.-D. Bauch, E. Nart, H. D. Stainsby, *Complexity of OM
  factorizations of polynomials over local fields*, LMS J. Comput. Math. 16
  (2013) 139–171, **Theorem 3.13** — pinned by the M05 Codex verifier with the
  published-PDF link (V2_m05_verify.jsonl item 8: "precision δ+1 preserves OM
  factorizations for congruent separable polynomials"); independently flagged as
  the OL2/WEIGHT-CHARGE-adjacent source by both M05 §5 and M12 §4.
* **Faithfulness skeleton** (for the `docs/AXIOM_FAITHFULNESS.md` entry):
  1. *Exact-statement debt*: every in-house citation of this paper so far is
     memory-qualified (M05 §5 "MUST be looked up"; M12 §4 same flag), and V1
     DEMONSTRATED the numbering hazard in this exact paper (published Lemma 5.11
     vs arXiv 5.12 shift, V1 items 1/5). Gate: pull the published text, transcribe
     Theorem 3.13 verbatim into the entry, before any declaration.
  2. *Object mismatch (the [D] wall)*: BNS state the theorem for THEIR OM
     representations; the corpus's `VTree`/`ReadsOf` carriers are not in the
     paper. The axiom must therefore be stated over GMN-type-side carriers and
     consumed ONLY through the K-DICT lemma — following the `GMNIndex.lean`
     pattern exactly (M15 AXIOMDRAFT: statement shape as a parameterized `def`,
     `axiom` keyword withheld until the gmn-side definitions exist, consumption
     seam machine-checked separately). An axiom typed at corpus carriers would
     smuggle K-DICT — the precise trap the M15 draft names ("an axiom over
     opaque stand-ins is not a faithful minimal transcription").
  3. *Scope*: K = ℚ_p only (dodges the AX-GMN scope caveats, cf. M06 §4.2).
  4. *What it does NOT give*: no per-site modulus and no tree-intrinsic
     threshold — K-READ-δ only. `count_tie`'s `VTree.thr` keying stays project
     math (M02 §5).
  5. *Numerics on record*: Krasner-cap surrogate 40/40 (M06 TB); scaling tests
     T1/T2 (M02, executed); envelope tests T1/T2 39/39 + 25/25 (M05, executed).
  6. *Process*: published-source citation + faithfulness entry + semantic-
     guardian Codex audit + Asvin sign-off (the policy that has caught two false
     axioms; CLAUDE.md axiom policy).

### 3.3 Stays open (genuinely, after the kernel + axiom)

* **K-DICT at order ≥ 2** — the tree/iteration counting theorem (derivation row
  16); shared with `cl15_align`; the deep-wild OM tower is standing obligation 2
  (PROJECT_STATE). This is the kernel's hardest face and the true residual.
* **K-RUN completeness at depth ≥ 2, general n** — no-missing beyond the forged
  length-1 instances; the note's D4R.4/L12 levels give the design but no Lean.
* **K-READ-thr** (tree-intrinsic modulus) — project math with no citation; if it
  stalls, the alternative is a `count_tie` re-key to a δ-keyed threshold
  (statement change ⇒ Asvin naming).
* **(X2)/dnLattice, HMC, hExhaust-general-n assembly** — adjacent, not IFK.

---

## 4. Unit decomposition (gates first; countermodel-first; ~200-line units)

Sequencing rule: U0/U1 are independent; U2 blocks U3–U7; U3 gates U4–U7 (no
consumption seam lands before its face survives the toy gate); U5 runs parallel
(docs-side). The M1 coexistence rule applies throughout: no compiled negation
witness may coexist with an un-repaired sorried universal.

* **IFK-U0 (land, ~120 lines + notes).** M18 §7 verbatim → new leaf
  `MovesV/V2_valC.lean`; keep `hRC` as ledger field per M18 §8; AxChk sweep.
* **IFK-U1 (GATE, countermodel, ~150 lines).** Compile the M03 Eisenstein
  countermodel (f_N = X² + p^N, empty VTree, M03 §2) against
  `BridgeReadLocality`'s all-sites shape — as a CONDITIONAL negation
  (`BridgeDiteOK`-genre honesty clause for the W_N witness lemma if the R7 wall
  blocks a total proof). Purpose: machine-certify that per-tree quantification is
  dead, so no IFK prover re-derives it. Also transcribe M18's
  `not_realizationComplete_toy` if U0 has not landed it.
* **IFK-U2 (statement layer, ~200 lines).** New leaf(s) `IFK/Defs.lean`: the
  K-DICT carrier (parameterized structure, GMNIndex.lean pattern), K-READ
  (per-site, both tiers as separate Props), K-RUN (three clauses: no-phantom,
  no-missing-at-level, nonempty-locus), K-HALT (three clauses: hen, irr,
  assembly). No axiom, no sorry: shape-sanity witnesses only (`face_zero_witness`
  genre). Every def carries its derivation-map row numbers in the docstring.
* **IFK-U3 (GATE, toy discharge, ~200 lines).** Prove K-RUN length ≤ 1 at the
  forge/toy instances (TV_A5b_forge child_cover transport; G1 `toyStage`);
  K-READ chart face; FIRST compile countermodel probes against any
  over-quantified variant a prover might prefer (the M03 discipline).
* **IFK-U4a–f (consumption seams, one unit each, ~150–250 lines).**
  (a) CYL ← K-READ+K-RUN and `count_tie` ← CYL (M02 §3, Lemmas A/B; NsFree-gated);
  (b) `TransferRow`/`TreeNStable` re-derivation from the per-site face (completes
  the SYN-C2 consolidation, BRIDGE_ADJUDICATIONS §SYNTHESIS PASS 1 C2/N2);
  (c) `vp_sound` ← K-RUN+K-HALT+K-DICT (M06 §4; NsFree-gated);
  (d) `MarkGraft` ← K-RUN duties at the Phase-B TE instance (M18 §6.2, or the
  biUnion build making it definitional — adjudicate which);
  (e) (X1)/(X3′)/(X4) + inStratum-realization ← faces, wired into KD10/KD5
  (M12 §2.3); (f) OL1 ← K-RUN+K-READ + AX-GMN → `env_tendsto` general n (M05 §5
  with V2's sufficiency correction).
* **IFK-U5 (axiom package, docs-side, parallel).** Pull BNS Theorem 3.13
  published text (Codex web run or library); write the face `def` + pending-
  declaration display + AXIOM_FAITHFULNESS entry per §3.2; Codex guardian audit;
  queue for Asvin sign-off. NO `axiom` keyword until K-DICT-side carriers exist.
* **IFK-U6 (numerics fleet, parallel).** Execute the preregistered suites:
  M02 T3–T5 (threshold necessity + n = 3 smoke), M05 T3–T4 (Lemma D sampling +
  OL2 shape N̂ vs δ), M06 TD (post-repair box regression), M18 Tests A–C (the
  counting tie T = T̂ at length 2 — the DIRECT K-RUN test; any T < T̂ stratum is
  a real-instance negation witness), M12 T1–T4 (radius/pair/singleton/X4).
  All scripts specified in the respective attempts' NUMERIC-TESTS sections;
  outputs to `verification/openmath/`.
* **IFK-U7 (bridge-instance transport).** After U3 + R7 designer data (via
  `RunRealizerExists`, derivation row 20): re-state U3's discharges at
  `bridgeTm`/`bridgeCanonical`. This is where the M9-Phase-B `hExhaust`/drainage
  story finally binds.

## 5. The collapse count (what retires if the kernel lands)

Census rows / ledger fields / named residuals retired or supplied
(binding · via derivation-map row):

1. `seam.count_tie` (DefsLedger.lean:241) · row 4
2. `BK.vp_sound` (BridgeKernels.lean:235) · row 11
3. `BK.env_tendsto` (BridgeKernels.lean:230), general-n residual · row 6
4. `canonical_stable` supply (IB-D8 chain) · row 5
5. `BridgeReadLocality` named hypothesis (BridgeD5:196) + queue-item-7 residual
   → replaced by the per-site face; `TransferRow` + `TreeNStable` become derived
   (SYN-C2 completes) · rows 1/3
6–8. M12 (X1), (X3′), (X4) interface rows · rows 13–15
9. inStratum-realization (the V1-critical gap gating `WeightChargeFullP` as
   quantified, hence `X3aRouteP`/KD5) · row 12
10. `cl15_align`'s dictionary half (shared OL-3; the GMN-finsum face stays the
    M15 axiom's) · rows 10/16
11. `RealizationComplete`/`hRC` (V2_valB.lean:272) → MarkGraft discharge · row 18
12. F-chain TV_F2–F6: 10 sorries at HEAD, blocked solely on row 11
    (TV_F2.lean:51; task #80) · row 19
13. `RunRealizerExists` (R7_polFillReduction.lean) → unblocks
    `canPolicyC_pin`/PolPin (queue item 13's residual) AND the R7 designer wall
    that currently blocks every bridge-instance countermodel/discharge · row 20
14. M05 OL1-ii/OL2 + M06 OL-1/OL-2/OL-3 open-lemma rosters (subsumed, not
    separate rows) · rows 6–10

Tally: **~13 named rows/hypotheses + 10 F-chain sorries**, five open-math census
items (M02, M05, M06, M12, M18) converging to the four faces + one literature
axiom + the honest §3.3 residue; three fence events (24/25/26) get their repairs
CONSUMED by kernel units rather than patched ad hoc. The kernel does not touch
fence events 23 (M01 runCount re-type) or 27 (SibJc adaptedness), nor (X2), HMC,
or the HK-06 wave (scope-fenced to its own owner).

## 6. Evidence index

M02-count-tie_fable.md (L1–L3, CYL, NsFree refutation, literature adjacency) ·
M03-read-locality_fable.md (per-site necessity, chart face, K1/K2) ·
M05-exhaust_fable.md + V2_m05_verify.jsonl (Lemmas A–E confirmed sound; OL1
sufficiency correction; OL2 + BNS 3.13 pin; T5 optimality claim WITHDRAWN per V2
critical (i) — not used here) · M06-vp-sound_fable.md ((VPS) decomposition,
HEN-LIFT/OM-SAT, ns witness) · M12-cl2-route_fable.md + V1_m12_verify.jsonl
((X1)–(X4), compiled assembly, inStratum + dictionary criticals; caterpillar
does NOT break the s = 2 cap — supported conjecture) ·
M18-realization-complete_fable.md (MarkGraft equivalences compiled, duties
(I0)–(I3), HmcToy negation) · BRIDGE_ADJUDICATIONS_2026-07-30.md (fence events
23–27, forge records, verification round 1, the convergence directive) ·
M15-x1a-align-gmn_AXIOMDRAFT_2026-07-31.md (the withheld-axiom pattern U5
follows) · docs/GMN_citations.md, docs/AXIOM_FAITHFULNESS.md (perimeter).

— IFK synthesis unit, 2026-07-31. Next step: Codex plan-review of THIS file
(charge: adversarial, quote-and-classify, fix nothing), then orchestrator
adjudication, then IFK-U0/U1 dispatch.

---

# ═══ REVISION 1 (2026-07-31, same day) — the V4 REJECT folded + the U6 probe verdict ═══

**GATE (re-armed, read first): REVISION 1 goes back to Codex re-review before ANY
prover dispatch.** Nothing below authorizes IFK-U0..U7 launches. The rev-0 text
above is preserved verbatim per record discipline; where this revision contradicts
it, the revision governs.

Inputs consumed: (a) the V4 adversarial plan-review — VERDICT: REJECT, 26 numbered
findings (`lean/notes/openmath/V4_ifk_review.jsonl`); (b) the IFK-U6 K-RUN probe —
VERDICT: SURVIVES (`verification/openmath/U6_krun_probe.py`,
`verification/openmath/results/U6_krun_results.json`, committed at fe3cda5; full log
on disk at `verification/openmath/logs/U6.log`); (c) the landed item-13 reduction
module `LeanUrat/MovesD/R7_polFillReduction.lean` at HEAD (read-only — the
MovesC/HC1/HC2/MovesD cone stays with the HK-06 wave owner).

New vocabulary introduced by this revision (all become named Props in IFK-U2):
**K-OB-A** finite-site assembly · **K-OB-B** inStratum→realized bridge ·
**K-OB-C** Okutsu proximity bound · **K-OB-D** singleton-cluster certificate-firing
(completeness) · **K-OB-E** continuing-node ⇒ repeated-residual (GMN-side) ·
**K-DICT-OB1** tree correspondence · **K-DICT-OB2** σ-invariance ·
**K-RUN clause 4** certification acceptance (OL1-ii, now face-content).

## R1. Per-finding disposition table (26 rows, no silent drops)

All 26 findings are ACCEPTED — none is rebutted. Classes: B = BLOCKER, A = ADVISORY.

| # | Finding (V4, compressed) | Disposition | Fix / argument |
|---|---|---|---|
| 1 | B: K-DICT ill-posed — Θ leaves both carriers free, function/bijection/relation ambiguous | ACCEPTED-fixed | Θ re-typed: for each fixed monic f off `discZero`, a FUNCTION Θ_f from the REALIZED runs of `canDec f` (`ReadsOf`-adapted histories, never free `VTree` data) to the GMN types of f; injectivity/surjectivity are separate named clauses. Enters U2 in this shape. |
| 2 | B: K-READ leaves H free; comparison variables unstated | ACCEPTED-fixed | Adaptation hypothesis added: (H, ν) ranges over sites realized on `canDec x`; "depends only on" is restated as an explicit two-lift comparison — for x, x′ agreeing below slot n·L(H,ν): `ReadsOf (canDec x) (H·ν) ↔ ReadsOf (canDec x′) (H·ν)`, uniformly over working levels ≥ L(H,ν). |
| 3 | B: K-READ-δ silently exceeds BNS 3.13 | ACCEPTED-fixed | Tier demoted: BNS 3.13 supplies ONLY OM-factorization stability under δ+1 congruence. K-READ-δ is restated as a DERIVED face conditional on K-DICT (incl. OB1/OB2, §R3) + K-RUN; never "directly from the citation". |
| 4 | B: K-RUN nonempty-locus clause quantifies over free formal chains | ACCEPTED-fixed (probe-informed) | Clause re-indexed at the FRESH-FRAME reading the U6 probe validated: chains whose per-step reads are menu-lawful at the frame state (h₁, μ₂) — the probe's fidelity header records the joint reading as tautological (tests nothing). Two probe canonicalizations bind U2: species = WHOLE node read; beyond-cap pooled as ('deep', k). See §R5. |
| 5 | B: K-HALT asserts verdicts for every lift g with no adaptation | ACCEPTED-fixed | Leaf-local statement is for the run's OWN polynomial; the transport corollary to lifts g is stated only for g in the leaf's read cylinder (g ≡ canDec x below the max K-READ modulus along the realized run), with K-READ+K-RUN as explicit premises. Assembly clause conditioned on a complete, polynomial-adapted tree. |
| 6 | B: row 2 needs fiber invariance, not bare no-phantom | ACCEPTED-fixed | Row 2 deps [R] → [R]+[P]: per-site pinning identifies the branch across the congruence class. §R4. |
| 7 | B: row 3 "re-point" suppresses finite-site assembly | ACCEPTED-fixed | New obligation **K-OB-A**: the finitely many sites relevant to a row share fiber agreement below the max modulus. Row 3 = [P]+[R]+K-OB-A; `transferRow_of_readLocality` is NOT merely re-pointed. |
| 8 | B: row 4 assumes CYL instead of deriving it | ACCEPTED-fixed | Row split: 4a = [P]-thr+[R] ⇒ CYL (OPEN — the real content); 4b = CYL ⇒ `count_tie` (compiled, M02 §3). Collapse credit attaches to 4a only. §R4. |
| 9 | B: row 5's K-READ cannot give roster stability / VPSound satisfiability | ACCEPTED-fixed | Deps NsFree+[P] → NsFree+[P]+[R]. §R4. |
| 10 | B: row 6 smuggles certification acceptance into K-RUN | ACCEPTED-fixed | K-RUN gains an explicit FOURTH clause (acceptance): the built certification predicate accepts exactly the realized = semantic runs — OL1-ii verbatim, now honest face-content. The face is heavier; priced in §R6. |
| 11 | B: row 7 overreads BNS (no stopping-time bound) and K-DICT (no execution transport) | ACCEPTED-fixed | Row 7 deps → [P]-δ + [D incl. **K-DICT-OB1**]: OL2's rate rides the HARDEST dictionary content and is recorded as conditional on §3.3's true residual, not on the citation. §R4. |
| 12 | B: row 8 assumes termination + a uniform complete tree | ACCEPTED-fixed | Deps [R]+[P] → [R]+[P]+AX-GMN (Cor. 4.19 termination, existing perimeter) + K-OB-A (finite-site synchronization). §R4. |
| 13 | B: row 11 omits its own [P]/LOC dependency | ACCEPTED-fixed | Deps → [R]+[P]+[H]+[D]+NsFree. §R4. |
| 14 | B: row 12 assumes the missing inStratum→realized bridge (the V1 overreach again) | ACCEPTED-fixed | New obligation **K-OB-B**: `inStratum` membership ⇒ realization — the V1-critical object ITSELF, now priced as a lemma. Row 12 = [R]+K-OB-B; no-phantom alone says nothing about arbitrary members. §R4. |
| 15 | B: row 13 derives a metric disk from mere branch membership | ACCEPTED-fixed | New obligation **K-OB-C** (Okutsu proximity: semantic-prefix membership ⇒ disk at radius w − C_φ; GMN-side, candidate cite to be pulled before U4e). Row 13 = [R]+[D]+K-OB-C. §R4. |
| 16 | B: row 14 reverses K-HALT soundness into completeness | ACCEPTED-fixed | New obligation **K-OB-D** (the certificate FIRES at singleton clusters within slack κ₀ = 1 — a completeness lemma). K-HALT stays soundness-only; (X3′) = [H]+K-OB-D. §R4. |
| 17 | B: row 15 overstates no-phantom (continuing ⇒ repeated residual is semantic) | ACCEPTED-fixed | New obligation **K-OB-E** (GMN-side: a continuing OM node presupposes a repeated residual factor). Row 15 = [R]+K-OB-E. §R4. |
| 18 | A: row 16 embeds the counting theorem in K-DICT, then projects it back | ACCEPTED-bookkeeping | Row 16 removed from collapse credit: the "population clause" IS the obligation (= K-DICT-OB1, §R3), and §3.3 already named it the true residual. §R4. |
| 19 | B: row 18 drops [P] (I2) and the reading-coherence premise | ACCEPTED-fixed | Deps [R] → [R]+[P] + named premise (I3-rc); "(I3) definitional" demoted to expected-definitional-at-reading-built-tmark, to be CERTIFIED in U4d, not assumed. §R4. |
| 20 | B: row 20 / the U3–U7 circularity is genuine — toy instances do not break it | ACCEPTED-fixed (re-scoped) | Full resolution §R2: the cycle is broken by re-attribution, not new proof — `RunRealizerExists` is an UPSTREAM supply (HC-1/JetSetup cone), partially compiled at HEAD (`canPolicyC_pin`, `interior_center_realizer_exists`); row 20 DELETED; collapse item 13 removed. |
| 21 | A: rows 1/9/10/17/19 are projections, not independent derivations | ACCEPTED-bookkeeping | Relabeled "definitional projections" in the map; zero independent collapse credit — their content is priced into the faces (§R6). |
| 22 | B: the cheapest falsification gate (U6/M18 A–C) is not first | ACCEPTED-executed | U6 was run FIRST, before this revision, and the face SURVIVED exhaustively at all four (n,p) ∈ {2,3}² incl. both wild corners. Verdict + implications on record in §R5; unit order re-cut there (U1 demoted, U0 stripped of gate status). |
| 23 | B: BNS draft adds conclusions the published theorem does not state | ACCEPTED-fixed | Axiom STRIPPED to the published δ+1 congruence clause only. §R3. |
| 24 | B: "the OM trees correspond" is a substantial strengthening (imports K-DICT into the axiom) | ACCEPTED-fixed | Clause deleted from the axiom; becomes **K-DICT-OB1** (tree correspondence), a PROOF obligation inside K-DICT. §R3. |
| 25 | B: σ(f) = σ(g) unsupported without a separate invariance theorem | ACCEPTED-fixed | Clause deleted; becomes **K-DICT-OB2** (σ-invariance under the paper's OM-factorization/Okutsu-equivalence relation), a PROOF obligation. §R3. |
| 26 | A: the core δ+1 clause itself is no stronger than the publication | ACCEPTED-confirmation | The stripped axiom (§R3) is EXACTLY this core clause; nothing else remains in it. |

Honesty note on finding 4: the U6 SURVIVES is evidence for the REPAIRED
(fresh-frame-indexed) clause, not for rev-0's free-chain wording — the probe itself
had to choose the non-tautological reading to have anything to test. V4's diagnosis
of the wording as "precisely the project's documented failure pattern" stands.

## R2. Finding 20 resolved: the K-RUN/R7 circularity — row 20 EXITS the kernel

The cycle as charged (correctly): bridge-instance discharge (U7) waits on the R7
designer data (`canPolicy`/`canPolicy_pin` designer-sorried, TreeCan.lean:485/492);
the designer data unblocks via `RunRealizerExists`; rev-0's row 20 derived
`RunRealizerExists` FROM K-RUN ([R]). A toy-instance existence theorem does not
provide the bridge-instance Prop, so "benign, sequence U3 before U7" was wrong.

Resolution — a NON-CIRCULAR supply path exists and is partially compiled at HEAD,
checked against `LeanUrat/MovesD/R7_polFillReduction.lean` (read-only; 0 sorry;
in-file `#print axioms` = Lean-core):

1. `RunRealizerExists` (R7_polFillReduction.lean:124) is quantified over
   `HistoryCoherent` histories at the MovesC carrier — NOT over `canDec`,
   `canTreeModelN`, or any bridge object. No clause of its statement mentions a
   K-RUN face. Rev-0's "= a K-RUN corollary" was a mis-attribution.
2. `canPolicyC_pin : RunRealizerExists p F → OffsetPPin (canPolicyC p F)`
   (R7:138) already reduces the ENTIRE (†15) designer pair to this one Prop —
   all five pin laws proved from it ("nothing else is missing", in-file record).
3. The coherence-derivable HALF of the Prop is PROVED with no kernel input:
   `interior_recentering_unramified` (R7:152) and
   `interior_center_realizer_exists` (R7:167) supply, at every INTERIOR
   recentering node of every coherent history, the realizer's
   nonzero/inC/weight/center clauses directly from `IsRecenteringCore.base` —
   i.e. from the HK-06 wave's re-keyed coherence, not from K-RUN or from any
   instance discharge.
4. The UNPROVED residue is exactly the module's recorded split: (a) the interior
   SUPPORT clause (monomial shape — PolPin's (S6b′) residue, owner HC-1
   lower-stage realizer export) and (b) the LAST-NODE flank (a final node carries
   no `IsRecenteringCore` record; needs `JetSetup.landing`'s threshold law, or a
   quantifier re-adjudication to the JetSetup carrier — the module's dated HK-06
   note records this flank's countermodel search as LIVE via
   `HK23_twoNodeGatePos`). Both live in the HC-1/HC2 cone, currently fenced to
   the HK-06 wave owner.

So the dependency arrow REVERSES: HC-1/JetSetup cone → `RunRealizerExists` →
`canPolicyC_pin` → compiled bridge instance → THEN bridge-instance K-RUN becomes
attemptable as a strictly stronger downstream statement. Consequences:

* Derivation row 20 is **DELETED** (not re-derived): `RunRealizerExists` is an
  upstream supply, not a kernel corollary.
* Collapse item 13 is **REMOVED** from §5's tally (§R6 recount).
* U7's precondition changes from "U3 + R7 designer data (via row 20)" to
  "U3 + `RunRealizerExists` supplied EXTERNALLY by the HC-1/JetSetup cone; IFK
  dispatches nothing at that cone while the HK-06 wave owns it".
* If flank (b) is refuted by the live countermodel search, the re-adjudicated
  quantifier feeds `canPolicyC_pin` the same way; U7 stays gated either way.

This is the honest shape: the cycle is broken by recognizing rev-0 inflated the
kernel by one row it does not own — no new mathematics is claimed here.

## R3. The BNS axiom, STRIPPED (findings 23–25)

§3.2's candidate 5 draft is SUPERSEDED. New draft — GMNIndex pattern throughout:
statement shape as a parameterized `def`, **`axiom` keyword withheld** until the
GMN-side carriers exist; published text transcribed verbatim into the
AXIOM_FAITHFULNESS entry before any declaration:

> **AX_BNS_precision (REV 1 DRAFT — NOT DECLARED).** Let p be prime and
> f, g ∈ ℤ_p[x] monic separable of common degree n, δ := v_p(disc f). If
> f ≡ g coefficient-wise mod p^{δ+1}, then every OM factorization of f is an
> OM factorization of g. [Bauch–Nart–Stainsby, *Complexity of OM factorizations
> of polynomials over local fields*, LMS J. Comput. Math. 16 (2013) 139–171,
> Theorem 3.13, pp. 154–155 — V4 pinned the published PDF.]

DELETED from the axiom (each a strengthening the published theorem does not
state, per findings 23–25): "the OM representations remain valid", "the OM trees
correspond", "σ(f) = σ(g)". These become named PROOF OBLIGATIONS inside K-DICT:

* **K-DICT-OB1 (tree correspondence).** Equality of admissible OM factorizations
  ⇒ correspondence of the refinement traces/trees the classifier produces. This
  is project math (same factorization is reachable through different
  representative choices and refinement histories — finding 24's exact point).
  OB1 ABSORBS rev-0's row-16 "population clause" and is §3.3's true residual,
  now stated once instead of hiding in an axiom and a derivation row.
* **K-DICT-OB2 (σ-invariance).** σ is invariant under the paper's
  Okutsu-equivalence / OM-factorization relation. A separate theorem; without it
  the axiom yields factorization data only, never σ(f) = σ(g).

Unchanged: faithfulness-skeleton items 1–6 of §3.2 (verbatim-transcription gate,
GMN-side typing consumed only through K-DICT, ℚ_p scope, no per-site modulus,
numerics on record, sign-off process). Finding 26 confirms the surviving clause
is no stronger than the publication — the excess strength is gone WITH the
deleted clauses, none remains in the δ+1 hypothesis itself.

## R4. Derivation-map corrections (replacement rows)

Rows 1/9/10/17/19 stand, RELABELED "definitional projection — no independent
collapse credit" (finding 21). Corrected rows (rev-0 text is superseded):

| # | Residual | Faces (corrected) | Correction |
|---|---|---|---|
| 2 | M02 L2 | [R]+[P] | fiber invariance = no-phantom + per-site pinning on the congruence class (finding 6) |
| 3 | M02 L3 / `TransferRow` | [P]+[R]+**K-OB-A** | finite-site assembly is a named lemma, not a "re-point" (finding 7) |
| 4a | [P]-thr+[R] ⇒ CYL | [P]-thr+[R] | the OPEN derivation — the row's real content (finding 8) |
| 4b | CYL ⇒ `seam.count_tie` | — | compiled (M02 §3); carries no open math |
| 5 | `canonical_stable` + `VPSound` sat. | NsFree+[P]+**[R]** | roster stability needs run faithfulness (finding 9) |
| 6 | M05 OL1 ⇒ `env_tendsto` | [R incl. clause 4]+[P]+AX-GMN | acceptance is face-content, not smuggled (finding 10) |
| 7 | M05 OL2 | [P]-δ+[D incl. **OB1**] | OL2's rate is conditional on the HARDEST dictionary content (finding 11) |
| 8 | M06 OL-1 (LOC) | [R]+[P]+AX-GMN+**K-OB-A** | termination + finite-site sync made explicit (finding 12) |
| 11 | `BK.vp_sound` | [R]+**[P]**+[H]+[D]+NsFree | the omitted LOC dependency restored (finding 13) |
| **12** | inStratum realization | [R]+**K-OB-B** | the bridge lemma IS the V1-critical object (finding 14) |
| **13** | M12 (X1) | [R]+[D]+**K-OB-C** | the proximity bound is a separate GMN-side lemma; membership alone gives no radius (finding 15) |
| **14** | M12 (X3′) | [H]+**K-OB-D** | completeness (the certificate FIRES) is not K-HALT soundness (finding 16) |
| **15** | M12 (X4) / `RecImpliesWild` | [R]+**K-OB-E** | "continuing ⇒ repeated residual factor" is a semantic GMN-side theorem, not a reading of no-phantom (finding 17) |
| **16** | tree/iteration correspondence | = **K-DICT-OB1** | an OBLIGATION inside [D], not a consequence; removed from collapse credit (finding 18) |
| **18** | `MarkGraft` ⇒ `RealizationComplete` | [R]+**[P]**+(I3-rc) | (I2) is [P]'s; reading-coherence premise NAMED, certified in U4d (finding 19) |
| **20** | `RunRealizerExists` | **DELETED** | upstream supply from the HC-1/JetSetup cone, §R2 (finding 20) |

## R5. Gate order (finding 22) + the U6 verdict on record

Revised rule: **U6-class falsifiers run FIRST** — the cheapest direct
real-instance negation criterion before any statement layer lands. And U6 has
now RUN, ahead of this revision, and the face SURVIVED its own preregistered
falsifier:

> **IFK-U6 verdict (2026-07-31): SURVIVES.** Exhaustive M18 Tests A–C at all
> four (n, p) ∈ {2,3}² — both wild corners included. Rows (r = 0 entry-cluster
> cylinder sweeps, lift-resolved precision horizons): R1 n=2 p=2 N=9 hcap=4
> (2¹⁶ boxes); R2 n=2 p=3 N=7 hcap=3 (3¹²); R3 n=3 p=2 N=7 hcap=3 μ=3 (2¹⁸);
> R4 n=3 p=3 N=5 hcap=2 μ=3 (3¹²). ZERO phantoms (no per-step-counted length-2
> chain with empty locus); the counting tie T = T̂ holds on every one of 174
> length-2 strata (369 realized chains); the D4R.4 equal-fiber law holds
> EXACTLY (all chain fibers equal and a p-power; unresolved mass 0 — no
> tolerance used). Validation gates green: V1 PARI factorpadic (e,f)-multiset
> tie via nfinit+idealprimedec, 1600 fully-decided samples, 0 mismatches (an
> earlier residue-reduction shortcut was mathematically wrong and REPLACED);
> V2 full-box cylinder/translation tie at 4 tiny boxes; V4 Hensel μ=2-in-n=3
> reduction, 796 samples, 0 mismatches; V5 N-vs-N−1 stabilization on all rows.
> Artifacts: `verification/openmath/U6_krun_probe.py`,
> `results/U6_krun_results.json` (committed at fe3cda5), `logs/U6.log` on disk.

What SURVIVES implies for the map — honestly bounded:

* SUPPORTS the repaired K-RUN face at the fresh-frame indexing (§R1 finding 4)
  and duties (I0)–(I2) at the intended p-adic semantics — at depth ≤ 2, heights
  ≤ hcap, the four probed boxes. Content confirmed: the step-2 read menu is
  independent of the step-1 arrival digits, and the full |A1| × |menu| product
  structure is realized on every stratum (all 2×2 blocks realized at the p=3
  wild cubic).
* DISCHARGES nothing: per M18 Theorem 0 the row is FALSE without instance
  structure — the probe is evidence for the instance-adapted statement, not a
  proof. K-RUN completeness at depth ≥ 2, general n, beyond the probed boxes
  stays §3.3-open, exactly as before.
* Two engine canonicalizations BIND the U2 statement layer: (i) branch species
  = the WHOLE node read (all polygon sides + residual profiles) — keying by the
  branch's own side letters (e, ℓ, h) pools configurations with different
  digit-pinning counts and SPURIOUSLY falsifies the equal-fiber law; (ii) the
  beyond-cap region pools into a single ('deep', k) marker — its internal side
  decomposition is horizon-dependent, while "k deepest roots beyond cap" is a
  clean digit-cylinder condition (pooled deep censuses verified exact p-powers).
* Carried caveat: the spec's own (2,3,6)/(3,3,4) rows under-certified their
  stated H and were re-leveled — U2's height clauses must be
  certification-driven, not aspirational.

Revised unit order: **U6 (DONE, SURVIVES) → Codex re-review of THIS revision →
U2** (statement layer, now carrying the §R1 face repairs, the two
canonicalizations, and K-OB-A..E + K-DICT-OB1/OB2 + K-RUN clause 4 as named
Props) **→ U1** (countermodel compile — demoted to post-U2: it certifies a
known fence, it does not probe the kernel) **→ U0** (MarkGraft landing, gate
status stripped — unrelated material, finding 22) **→ U3 → U4a–f → U5**
(stripped axiom package per §R3) **→ U7** (gated on the EXTERNAL
`RunRealizerExists` supply, §R2 — no IFK dispatch into the HK-06 cone).

## R6. The honest recount of the collapse

Rev-0 claimed ~13 named rows/hypotheses + 10 F-chain sorries. Corrected:

**Retired by the kernel as revised** (conditional on the four ENLARGED faces —
adapted quantifiers, K-RUN clause 4 — plus the stripped axiom):
`seam.count_tie` (via 4a+4b), `BK.vp_sound`, `BK.env_tendsto` general-n
residual, `canonical_stable` supply, `BridgeReadLocality` → per-site
(+ `TransferRow`/`TreeNStable` derived through K-OB-A), `cl15_align`'s
dictionary half, `RealizationComplete`/`hRC`, and the OL rosters (OL1-ii now
face-content). = **8 named rows + 10 F-chain sorries** (the F-chain rides row 19
unchanged).

**Retired only WITH a named auxiliary lemma each** (new pricing, findings
14–17): inStratum-realization (K-OB-B), M12 (X1) (K-OB-C), (X3′) (K-OB-D),
(X4) (K-OB-E). = 4 rows, each costing one new open lemma.

**Removed from the tally**: `RunRealizerExists` (rev-0 item 13 — upstream
supply, §R2); the row-16 counting theorem (never a collapse: it IS K-DICT-OB1,
§3.3's residual, previously double-booked as both an axiom clause and a
derivation).

**New open mass made explicit by this revision** (it was hidden inside overread
arrows and the fat axiom): K-OB-A..E, K-DICT-OB1 (the known hardest face),
K-DICT-OB2, K-RUN clause 4, the (I3-rc) premise — nine named obligations, of
which OB1 is deep-wild-tower-hard and the other eight are bounded project math.

Net verdict, stated plainly: the §0 convergence observation STANDS — five
fleets' residuals still factor through the four faces — but rev-0 overstated
the collapse by one row (RunRealizerExists), double-counted one (row 16), and
under-priced eleven arrows. The kernel is a genuine consolidation with heavier
faces than advertised, not a shortcut. The U6 SURVIVES is the first
falsification-grade evidence that the heaviest face's depth-2 content is TRUE
at the intended semantics.

— REVISION 1, IFK synthesis unit, 2026-07-31. Next step: Codex re-review of the
FULL document (rev-0 + this revision as one artifact; charge: adversarial,
quote-and-classify, fix nothing), then orchestrator adjudication. NO prover
dispatch before that verdict.
