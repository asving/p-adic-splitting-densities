# O5triple — O-5 + D-7a/b/c (the leaf/factor bijection triple) — Phase-B attempt

**Fable prover, 2026-07-31.** Target: tree §2.4 **O-5** (K-HALT + ASSEMBLY) and DELTA-1
**D-7a/b/c** (LEAF-DISJOINT / LEAF-COVER / LEAF-MULT), the three propositions V6
finding 16 showed are NOT consequences of O-5's previously listed inputs. Deliverable
verification target (SELF-CONTAINED): `O5triple_phaseB_verifybrief.md`. Falsifier
(ran FIRST): `verification/openmath/o5triple_check.gp` — **1341 checks, 0 failures**,
plus a load-bearing negative control.

## Outcome in one paragraph

The triple is **PROVED at a displayed interface**. The architecture: (1) an
UNCONDITIONAL semantic theorem (brief §4, Theorem A) — for every monic separable
g ∈ ℤ_p[x], the halted GMN dissection tree 𝒯(g) carries a factor system whose leaf map
is a BIJECTION onto the monic irreducible factors of g, with product identity, pinned
(e, f) invariants per leaf kind, and checksum Σ e·f = n — proved by tree induction from
the pinned literature floor only (GMN Thm 1.15/1.19/3.1/3.7, Cor 1.20/3.3/3.8,
Thm 2.11, Cor 4.19; HEN-LIFT; defectlessness), with THREE displayed transcription flags
((GMN-COH), (R-1), (R-2)/(L3+)_r — all GMN-internal reading duties, no new mathematics).
(2) The classifier triple (brief §6, Theorems B–E) follows for EVERY monic separable
lift of a decided ns-free class from interface hypotheses (I-1)–(I-3), displayed clause
by clause and priced item-by-item to the tree's upstream leaves: (I-1)(a,b) = O-3
no-phantom + acceptance ∘ O-2b trace correspondence; (I-1)(c) = O-2a invariant matching;
(I-2) = dictionary faithfulness; (I-3) = engine typing (free). Nothing else is consumed.

## The two headline mechanisms

1. **D-7b (coverage) does NOT consume O-3's no-missing clause.** The engine checksum
   Σ_ℓ e_ℓ f_ℓ = n (free, from σ's typing) + Theorem A's semantic checksum
   Σ_{leaves 𝒯(g)} e·f = n + transport injectivity force the leaf transport ONTO the
   semantic leaves by pure counting (brief Theorem B: an injection with image total =
   whole total and all terms ≥ 1 is a bijection). The V6-f.16 worry ("checksums +
   product formula don't give a bijection") is answered by making the checksum argument
   an actual proof: what it needs beyond arithmetic is exactly Theorem A's semantic
   bijection — which is where the real work now sits, and which is proved.
2. **Lemma STEEP (the corner dichotomy) is the one lift-variant leaf kind, and its
   verdict is lift-invariant.** At a corner-certified leaf, one lift of the class may
   have an EXACT key factor (φ_r | g, semantic tree has an exact-key leaf) while
   another has a steep finite length-1 side — two different semantic trees. Both
   realizations are irreducible with the SAME (e, f) = (e₁⋯e_{r−1}, f₀⋯f_{r−1})
   (REP-IRR for the exact case; Cor 3.3 with e_S = 1 for the steep case). This is the
   precise sense in which "the realized run is constant across lifts" survives the
   invisible-corner ambiguity. Falsifier T1/T2 confirm verdict constancy including a
   degree-2 Eisenstein key; the negative control (lifts BELOW the corner band: 6/10
   changed type) shows the certificate band is load-bearing, not slack.

## Decomposition vs the tree's expectations

* D-7a (disjointness): proved WITHOUT the hinted Krasner/K-OB-C distance argument — the
  route is coprimality of distinct members of one factorization of a squarefree g,
  applied at the divergence node of the two leaf paths (brief Thm A(2)inj + Thm D(a)).
  Krasner survives as intuition only; K-OB-C is NOT consumed.
* D-7b (coverage): the checksum route above; the "no-orphan-factors" bookkeeping the
  tree asked for is Theorem A's surjectivity (descend any irreducible factor down the
  tree; exactly-one-child at each node by coprimality; termination by Cor 4.19).
* D-7c (multiplicity): under ns-freeness all slot multiplicities are 1 and g squarefree
  gives factor multiplicities 1; the multiset identity is then the bijection + O-2a's
  invariant matching, and it is uniform over lifts because the leaf-side data is engine
  data (brief Thm E). HEN-LIFT/OM-SAT enter exactly where the tree said: hen slots via
  LIT-3, saturated slots via GMN Cor 3.8/Def 3.9 through the dictionary; the corner
  slots additionally need Lemma STEEP (new here).
* O-5 LEAF: brief Theorem C; O-5 ASSEMBLY: brief Theorem E, with
  type(g) = typemult(T) = σ for every separable lift — the vp_sound-repair target
  (M06 §4's (VPS, ns-free) = (LOC) + (LEAF) + (ASSEMBLY); this note supplies (LEAF) +
  (ASSEMBLY) given (LOC)-shaped interfaces).

## What is genuinely new here (vs consumed)

NEW (proved): the 𝒯(g) factor-system induction (Lemmas H0/NODE + Theorem A) — the
tree-global bijection GMN state per-type; Lemma REP-IRR's derivation (representatives
are irreducible with pinned invariants — derived from Thm 2.11 + Cor 3.8 +
defectlessness rather than cited); Lemma STEEP; the checksum-coverage counting; the
per-clause consumption ledger (brief §7 table).
CONSUMED (open, owned elsewhere): (I-1)/(I-2) = the O-3 ⊕ O-2b cluster + O-2a's
OL-2a-1..4 (rev 2 on file); (I-0)/CYL = D-15 (O1thr rev 2, context only).
DECLARED (literature transcription duties, GMN-internal): (GMN-COH) — the sprouted-type
cluster identity underlying eq. (37); (R-1) — the representative's "of type t" shape;
(R-2)/(L3+)_r — the exact-key polygon convention at order r (order-1 case already
falsifier-covered by O2a F5's 871 samples).

## Relation to standing evidence

U6/IFK-U6-FIRST (0 phantoms, 174/174 counting tie, 1600/1600 PARI (e,f) tie at length
≤ 2, all four (n,p) ∈ {2,3}² incl. wild) is exactly (I-1)-shaped evidence at depth ≤ 2 —
supports, discharges nothing. M06's TB Krasner surrogate (40/40) is (I-0)-adjacent.
The M06 countermodel ((x+p)² three-type class) sits OUTSIDE this note's perimeter by
the ns-free standing precondition — the repair this note's theorems presuppose.

## Files

* `lean/notes/openmath/O5triple_phaseB_verifybrief.md` — SELF-CONTAINED verification
  target (statements, interface, all proofs, falsifier report). Hand THIS to the next
  hostile pass.
* `verification/openmath/o5triple_check.gp` — falsifier suite (T1/T2 STEEP constancy at
  order-1 and order-2 keys + negative control; T3 checksum/mult-1, 1000 checks; T4
  per-factor single-track + one-sided polygon surrogates). ALL PASS: 1341/1341.

## Suggested checks for the verification pass

(i) Audit Theorem A's surjectivity descent: does every step really place F in EXACTLY
one child factor, and is the exact-key case (F = φ_r) forced by irreducibility alone?
(ii) Audit the (R-2)/(L3+)_r degree bookkeeping (deg f_t = m_r·j₀ + Σ m_r·ℓ(S)) against
the pinned Lemma 2.4 — this is the most citation-sensitive display. (iii) Check that
Theorem B's counting argument uses (I-1)(c) only on the IMAGE slots (it does — display
audit). (iv) Probe whether (I-2)'s displayed sufficient clauses really cover the
corner-vs-visible-side divergence case. (v) The order-2 STEEP falsifier could be
extended to degree-3 keys and p = 2 Artin–Schreier corners — the right next numeric
investment if any wobble appears.

## VERDICT

**O-5 + D-7a/b/c: PROVED at the displayed interface (I-1)–(I-3)** — semantic core
(Theorem A) unconditional over the pinned literature floor with three named
transcription flags; the triple itself conditional on exactly the upstream O-2a /
O-3 ⊕ O-2b faces it was declared to ride, now itemized per clause; dependency
sharpening: D-7b needs NO no-missing clause. Falsifiers 1341/1341 with a load-bearing
negative control. Status: PROVED-UNVERIFIED pending fresh-context hostile passes
(≥ 2 consecutive clean, model-diverse, per §4 of the tree).
