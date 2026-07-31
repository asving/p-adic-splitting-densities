# O1thr Phase-B attempt — the per-site read package: O-1(thr) + D-14 + D-15

*(2026-07-31, Phase-B prover, THE MATHEMATICAL COMPLETION campaign. Leaf cluster per
`docs/MATH_COMPLETION_TREE_2026-08-01.md` §2.4 O-1 (thr-tier) + DELTA 1 nodes D-14
(LAWFUL-SITE READ) and D-15 (CYL), attack-order slot 2 of §D1.6. Companion
self-contained package for the adversarial verifier: `O1thr_phaseB_verifybrief.md`
(ALL proofs live there; this note is the repo-facing record). Falsifier artifact:
`verification/openmath/o1thr_persite_check.py` — run FIRST per the charge; all
checks PASS.)*

## VERDICT: PARTIAL (proved at the defined mathematical machine; interface seams displayed)

All three statements are PROVED as mathematics about the machine defined in the
verify brief — the OM read machine with (R1)–(R5) clause reads in MacLane frames,
harvest-total children, saturation halts, and the (F1)–(F6) fiber conditions
mirroring the corpus's `fiberAt`. Specifically:

* **D-14 (lawful-site locality): PROVED OUTRIGHT** (verify brief Theorem 1) — for
  every LAWFUL site (H, ν), whether the run on f reads (H, ν) is determined by f's
  coefficient digits below L(H, ν) := 1 + max over the site's reads of the
  de-normalized side-line intercept ⌈I_i/E_i⌉. Quantifier over lawful sites, NOT
  realized ones — the noncircular form O-3's no-missing clause consumes. Proof
  inputs: three lemmas proved in the brief (DEV: monic-division congruence; POS:
  MacLane positivity + p-stretch; R-LOC: graded-residual locality) + the CEIL
  clause-height audit. No open lemma remains inside this proof.
* **O-1(thr) (realized tier + K2): PROVED** (brief Theorem 2) — (a) the REV-1
  finding-2 two-lift comparison over realized sites, uniform over working levels
  ≥ L, as an immediate restriction of Theorem 1; (b) K2 window closure: at every
  state of a decided ns-free tree fiber, the realized-children roster is constant
  (= the recorded roster) across ALL boxes agreeing below the tree threshold —
  deep candidates excluded via the NEW **Lemma SPAN** (full-span ledger: on a
  decided ns-free fiber every window is fully spanned by recorded reads, so slot 0
  carries an exact pin below thr; a deep side line would have to pass under that
  pin — contradiction). SPAN's proof is an elementary weight ledger
  (wt = deg Φ · window width; W-ADD says children's weights sum to deg Φ·span;
  L-SAT says τ-irr verdict degree = leaf weight; the fiber checksums (F5)/(F6)
  force zero total deficit). This is the direct proof V5 demanded — CYL/K2 not
  "implied by the other faces" but carried by its own mechanism.
* **D-15 (CYL): PROVED** (brief Theorem 3) — decided ns-free tree fibers are EXACT
  finite unions of level-thr(T) coefficient cylinders, cross-level (M ≠ M′ form
  included); fiber counts scale by p^n per level above thr; per-box tree
  uniqueness gives disjointness and the per-σ mass tie
  decided_σ(N) = p^{nN}·Σ_{thr(T)≤N} mass(T). The derivation is the M03 §6
  architecture with its two flagged gaps closed (prefix bookkeeping; ceilings of
  tree prefixes ≤ thr by definition) and (K1)/(K2) now theorems, not assumptions.

**Why PARTIAL and not PROVED:** the campaign's honest boundary. The theorems are
proved for the machine AS DEFINED in the brief; the identification of that machine
with (i) the Lean corpus's `ReadsOf`/`canTreeModel`/`fiberAt` objects and (ii) the
GMN semantic OM objects is NOT proved here and is displayed as the seam ledger
(brief §8, S-1..S-5). Per the tree's own architecture those identifications are
owned elsewhere ((i) = Lean transcription, Phase C; (ii) = O-2's dictionary). The
mathematical content of the three leaf statements is, I claim, fully delivered;
a verifier should attack the proofs AND the fidelity of the machine definition.

## §0 Grounding (what this cluster is, who consumes it)

count_tie (K-4's repair) needs: per-tree fiber counts scale by p^n per level above
the tree threshold. M02 proved rigorously that this is EQUIVALENT to a cylinder
law (CYL) and refuted the row without ns-freeness; M03 refuted every all-sites/
tree-keyed locality quantifier (Eisenstein family) and reduced the true content to
the site-keyed pair (K1)+(K2); V5 found CYL is not implied by the faces O-1 listed
(defect 2) and V6 found the O-1/O-3 quantifier seam circular (finding 14 → D-14).
This unit delivers the three statements in their DELTA-1-sharpened forms with
proofs. Consumers: K-4/K-6 repairs, O-3 (no-missing consumes D-14), O-4 (OL1-ii),
O-5, O-10, T-6 (CUT-WD/(τ-irr) cylinders), D-1(ii), T-U's bracket.

## §1 FALSIFIER FIRST — all checks PASS (executed 2026-07-31, this machine)

`verification/openmath/o1thr_persite_check.py` (python3, stdlib only) checks the
package's exact new content on the depth-1 slice, where the read machine is
computable from first principles (boxes with reduction X^n; root window = the full
Newton polygon w.r.t. X; sites = (principal face, irreducible residual factor)
pairs; ceiling L = 1 + ⌈intercept⌉ — the L(H, ν) formula at depth 1, E_0 = 1).
This executes M03's proposed-but-never-run test 4 in exhaustive form.

| (p, n, M) | boxes | sites | T-A cylinder-law violations | T-B sharp at L | T-C roster violations (closed boxes) | T-D Eisenstein |
|---|---|---|---|---|---|---|
| (2,2,5) | 256 | 10 | **0** | 10/10 | **0** (240) | PASS |
| (2,2,6) | 1024 | 13 | **0** | 13/13 | **0** (992) | PASS |
| (3,2,5) | 6561 | 30 | **0** | 30/30 | **0** (6480) | PASS |
| (2,3,4) | 512 | 13 | **0** | 12/13 | **0** (448) | PASS |
| (3,3,4) | 19683 | 49 | **0** | 47/49 | **0** (18954) | PASS |

* **T-A** (Theorem 1's depth-1 instance): every harvested site's membership set is
  an exact union of level-L(site) cylinders — 0 violations over 28,036 boxes.
* **T-B** (sharpness): 112/115 sites genuinely read digits at level L−1 — the
  ceiling formula is tight, not just sufficient.
* **T-C** (Theorem 3's depth-1 proxy): closed-polygon boxes have their full site
  roster constant on the level-t cylinder (t = max roster ceiling) — 0 violations.
* **T-D** (the charge's mandated check): the M03 Eisenstein family f = X^n + p^N
  sits OUTSIDE every claimed guard — its unique site has ceiling N+1 > N, and the
  zero box (agreeing below N) does not realize it. Simultaneously it is the
  sharpness witness: L = N+1 cannot be improved to N at any prime.

Standing corroboration folded in (not proof inputs): **U6** — the equal-fiber law
EXACT on 174/174 length-2 strata at all four (n, p) ∈ {2,3}² incl. both wild
corners (= D-15's scaling at depth 2); **N1** (bracket + drainage 20/20);
**N2** (density ties, exact n = 2 sandwich); **M02-T1** (p = 3, n = 2: every
genuine bucket scales by exactly p² from its threshold level).

## §2 The statement package (proofs in the verify brief)

All notation in the brief; L(H) := 1 + max_i ⌈I_i/E_i⌉ (I_i = side-line intercept
at slot 0 in w_i-heights, E_i = w_i(p) the stretch), thr(T) := max(1, max over
chains of L).

* **Theorem 1 (D-14).** For every LAWFUL site (H, ν) and all monic degree-n f ≡ f′
  (mod p^{L(H·ν)}): the machine reads (H, ν) on f iff on f′. (Stated for arbitrary
  f, f′ ∈ ℤ_p[X], so the box/truncation two-level forms are instances.)
* **Theorem 2 (O-1(thr)).** (a) realized-site two-lift form, uniform over working
  levels ≥ L; (b) K2: on a decided ns-free fiber, realized-children rosters at
  every tree state are constant on the level-thr agreement class — deep candidates
  excluded (via Lemma SPAN).
* **Theorem 3 (D-15).** CYL: fiber(T, ·) is invariant across boxes (any working
  levels ≥ N ≥ thr) agreeing below N; level-N fibers are exact unions of
  level-thr cylinders; counts scale c_T(N) = c_T(thr)·p^{n(N−thr)}; per-box
  uniqueness ⇒ disjoint fibers ⇒ the per-σ decided-count/mass tie.
* **New lemma of independent interest: SPAN** (full-span ledger) — decided ns-free
  fibers have fully-spanned windows at every state; slot-0 exact pin below thr.
  This is what makes K2 a THEOREM rather than a face of O-1: it converts the
  fiber's degree checksums ((F5)/(F6)) into polygon geometry. GMN-adjacent
  (their f-complete degree additivity) but proved here as pure record bookkeeping.

## §3 Fit to the tree's shape constraints (the countermodels)

* **K-5's refutation (M03 Eisenstein)** honored: every statement is per-site or
  per-decided-tree keyed; no all-sites/tree-uniform threshold anywhere. The family
  is checked to sit outside each guard (T-D) and doubles as the sharpness witness.
* **K-4's refutation (M02 exact-square/ns family)** honored: Theorems 2(b)/3
  require ns-freeness; the brief's Remark 4 displays that the ns family scales by
  p not p², so the hypothesis is NOT removable. ns loci drain to the undecided
  envelope (O-4's territory, per the M9/Phase-B design).
* **V6 finding 14 (O-1/O-3 circularity)** honored: Theorem 1's quantifier is over
  lawful sites with no realization presupposition; the proof never inspects any
  run (the site's records pin its own keys/frames — brief Remark 1). δ-tier
  explicitly excluded (one-directional, behind O-2b+O-3+D-16 per D1.2/D-16).
* **REV-1 finding 2** honored: Theorem 2(a) is literally the two-lift comparison
  over realized sites, uniform over working levels ≥ L.

## §4 Honest ledger (exact residues; = brief §8)

1. **(S-1) machine transcription** — the theorems are about the brief's machine;
   the clause-by-clause correspondence to the corpus (`SideReads` (i)–(vi) ↔
   (R1)–(R5); `Realizable`/`IsCanonPres` box-free; `fiberAt` ↔ (F1)–(F6);
   `VTree.thr`'s Nshape ⊔ siteLevel majorizes L) is displayed but NOT proved
   here — Lean-side duty, where the corpus's C.1.5 graded-presentation dictionary
   ("downsets are literal digit systems") instantiates interface (M3). This is
   exactly the residue the tree already prices at O-1 ("the open content is
   precisely the dictionary step" — M03 §5); at the mathematical machine the
   dictionary is definitional, which is why the math closes.
2. **(S-4) harvest lawfulness** — (M6)'s LAWFUL half (harvested faces satisfy the
   box-free laws) is a design invariant of the machine, used only in SPAN /
   (F1)-backward; its corpus discharge is O-3-adjacent (root_total/window
   totality). Theorem 1/D-14 does NOT use it.
3. **(S-3/S-5)** policy canonicity (D-5) and semantic identification (O-2/O-5) are
   out of scope, as the tree assigns them.
4. No claim is made about ns-carrying trees, undecided mass, rates, or the δ-tier.

## §5 Notes for the next units (consumption)

* **O-3 cluster**: D-14 is now available in the exact no-missing shape — for a
  lawful site with ceiling ≤ N, realization is a level-L cylinder event, so
  witness construction in a digit cylinder (the forge method) certifies
  realization for the WHOLE cylinder. K2 gives the stray-exclusion half of the
  level-N truncation argument.
* **K-4 repair**: Theorem 3(b)+(c) + M02 Lemmas A/B (rigorous, on file) discharge
  count_tie at the ns-free carrier; the carrier repair (NsFree in `bridgeTree`)
  remains the sanctioned statement change M02 proposed (sign-off still owed).
* **O-4 (OL1-ii)**: the agreement seam now has its O-1 half; the remaining half is
  O-3's acceptance clause at the run's sites.
* **T-6 (τ-irr) perimeter**: Lemma SPAN is the mathematical content of the
  "window closes below thr" step TB-CAP's cylinders need; the D4R.0-K(c)
  verdict-pin residue is untouched (different node).

## §6 Verification protocol note

Per §4 of the tree: this note + brief are PROVED-UNVERIFIED until ≥ 2 consecutive
clean fresh-context passes (Codex first — decorrelated blind spots; the brief is
self-contained by design, hand it with the standing quote-and-classify charge).
Numerics are corroboration, never acceptance. Suggested falsifier extensions for
the verification round: depth-2 harvesting via a recentered-frame implementation
(the T-C analogue one level down), and the n = 3 wild corner at (p, N) = (3, 5).
