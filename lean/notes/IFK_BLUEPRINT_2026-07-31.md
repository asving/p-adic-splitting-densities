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
