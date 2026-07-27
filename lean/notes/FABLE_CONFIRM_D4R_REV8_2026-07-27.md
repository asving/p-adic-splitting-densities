# FABLE FRESH-INSTANCE CONFIRMING PASS on §D4-R rev 8 (2026-07-27)

Verifier: fresh Fable instance, the Fable half of the dual-acceptance
shot (Codex confirm runs in parallel on the same rev-8 text; no
deference to any prior pass). Target: live §D4-R, MOVES_2026-07-24.md
lines 4587-5381 (body unaffected by a concurrent §SP/[2a] append after
line 5789 that shifted later record anchors mid-pass). Predecessor:
FABLE_VERIFY_D4R_REV7_2026-07-26.md (0 crit / 2 display gaps B1, B2).

## (a) The two one-liners — BOTH CORRECTLY APPLIED

B1 VERIFIED. New heading (line ~4748): "### D4-R.1 D4R.0 — the
digit-cell partition and its branch sets (three burdens, displayed)".
Matches the theorem beneath it verbatim in substance: "Theorem D4R.0
(CELL PARTITION + BRANCH SETS — the kernel RESTATED at rev 6 ...)";
"(three burdens, displayed)" matches the ledger's (a)/(b)/(c), with (c)
explicitly NOT a kernel part. grep confirms zero remnants of the old
"partition into prefix fibers" anywhere in the file; the rev-8 commit
diff (1b39ff0) shows exactly this heading swap and B2 as the only two
§D4-R body edits.

B2 VERIFIED. New parenthetical at D4R.1-SUM (line ~4946):
"(equivalently: at every level N ≥ N(P̂), the level-N average of mult_P̂
is C_P̂(p)·p^{−A(P̂)} — finitely many indicators, summed)". Semantics
re-derived: for N ≥ N(P̂), L12 resolves each fiber into exact level-N
classes, so mult_P̂ is well-defined per residue and its box average is
D4R.4-SUM / p^{nN} = C_P̂(p)·p^{−A(P̂)}; degenerate cases consistent
(Pref = ∅: average 0 = 0·p^{−A} at every N ≥ 1; P̂ = ∅: average 1,
N(∅) = 1 by C.2's no-equations clause).

## (b) Sweep + fresh angles (chosen: L9 volume proof; D4-R.5
## withdrawn-list completeness; independent gate/ledger arithmetic)

FRESH ANGLE 1 — L9 (shape-constant fresh volume), NOT probed as a proof
by the predecessor. The citation typechecks: §C C.3 VOLUME STRUCTURE
states verbatim "each vol(E_fresh(ν_i)) is a product of per-digit
factors (alphabet cardinality)^{−1}", each cardinality "a power of p
determined by the history's SHAPE data" (image cardinality of the
D.3(e)(i) piece map). Shape-dependence THROUGH P̂ closes structurally:
L3's F2 bullet retains the stride-position sets p_j — functions of
γ_r = e_r·u*_r + j*_r·h_r (§C C.0's DERIVED list) — so retaining them
pins γ_r and hence the side height u*_r; per-digit heights and
alphabets are recoverable from P̂'s inventory. This gives the
predecessor's "side heights are derived data" closure an explicit
witness inside the retained fields. A(P̂) := the resulting exponent is
a definition — no circularity. PASS.

FRESH ANGLE 2 — D4-R.5's REFUTED AND WITHDRAWN list audited against
the FULL rev history (pass records 1-7, dual-pass, rev-6, rev-8; all
re-read). Every withdrawal across 8 revs is accounted for: the four
F1 items are ON the list (single-run ontology, per-node exclusivity/
partition, fiber disjointness, exact event identities); D4R.3 (torus
lemma) RETIRED in-section with "FALSE ... nothing here cites it";
rev-1 "(3i) verbatim" withdrawn at D4R.2 + PLAN RECONCILIATION; the
rev-2 coarse M-formula superseded at L11 (kept only as a true coarse
chain); rev-5 "kernel part (c)" label struck at L4 + D4R.0 ledger;
completion-union struck at D4R.0(b); rev-7's wrong threshold replaced
at D4-R.6 (now "3 < 2·g₀·μ₀ = 4", correct); plan §2's "patterns are
FUNCTIONS of f" refuted + plan-rev-8 duty queued at D4-R.5. COMPLETE —
no orphaned withdrawal, no zombie claim.

FRESH ANGLE 3 — independent A(P̂)/gate arithmetic, fresh code (this
session): N₂(2) = 1, N₂(3) = 3 irreducible quadratics; the
realizability map (d₂,d₁,d₀) = (s₁−r, s₀−rs₁, −rs₀) is INJECTIVE at
both primes (1 resp. 6 distinct root tuples — so C counts prefixes
without collision); C_P̂*(2) = 3 (unique tuple (0,0,1) verbatim),
C_P̂*(3) = 48; FC8 lump count 4·3·2 − 4 = 20; A(P̂*) = 9 + 2 = 11,
A_net = 4. (HV) hand-check at (ψ = z²+1, r = 1): (R₀/ψ) mod ψ = z + 2
= z̄ − r over F₃, with m̂₀ = 0 forced by the rev-14 Bézout convention
(e₀ = 1, h₀ = 1 ⟹ t^B₀ = 0). ALL MATCH the note's displayed numbers.

CONFIRMING-DEPTH RE-CHECKS (each re-read against the rev-8 text):
D4R.1's proof (sum over the index set, empty prefix dispatched before
C(b), subadditivity, pointwise upgrade via positive-mass finite-level
cylinders); L6 both inclusions incl. the empty-prefix base; L8/L11
(enc′ injection; (NA)/(HV)/(SAE) only-remove — predicates on the
encoded tuple); L12's finite-level pointwise equivalence; D4-R.6's
mult ≡ 1 derivation; no completion-union anywhere. All sound.

RECORD NOTE (non-finding): the rev-8 commit 1b39ff0 sweeps in
concurrent [2a]/§SP draft lines (as its sibling 60d8e41 self-declares);
the §D4-R body span itself carries only the two one-liners.

## (c) §C citations vs the dual-accepted rev 14 — TYPECHECK, final
## form consumed

- REALIZABILITY CLASS (the definition that changed shape): L3 binds
  "(NA) + (HV) + (SAE)" — exactly rev-14 C.0's REALIZABLE definition
  (the FINAL form; rev 12's three data conditions, unchanged through
  rev 14). §C's rev-12 node-tuple bracket even names "the fields
  L11/§D4-R consume". CONSUMED CORRECTLY.
- TRANSITION-ADMISSIBLE (rev-13's per-step interface): NOT consumed —
  grep confirms §D4-R cites no C.1 / C.1.0(b)(iii) / C.1.5 per-step
  statement (C.1.5 is cited only for its OBJECT Σ_k); Theorem C(a)/(b)
  are full-history-quantified over REALIZABLE histories, the exact
  shape D4R.1/L6/L12 consume. No appended-read hypothesis is owed.
- Spot typechecks, all PASS: C.0's EMPTY HISTORY clause "T(∅, Z) := Z"
  (verbatim at C.0); the history quantifier beginning at ν₀ (backs the
  "NOT by Theorem C(b)" empty dispatches); C.2's N(H,Z) = 1 + largest
  base level, N := 1 with no equations; C(b)'s count formula with
  vol(⊤) = 1 (⊤ vacuously admissible); the canonical (S6b)
  offset-P-lift named in C.0's lift field; ψ_i carried as "the branch
  choice, not recoverable from the digits alone" (= L11's enlargement
  rationale); rev-14's t^B/t_i disambiguation lands D4-R's usages
  (canonical lift t₁; m̂₀ = 0) on the right fields.

REMARK R1 (staleness, favorable direction — no repair to the frozen
rev-8 body): the header still anchors "the accepted §C (Theorem C,
rev 11b, passes 12+13 CLEAN)" — an acceptance since PUNCTURED and
superseded by rev 14's dual acceptance; and L3's "(§C's own repair is
QUEUED and NOT applied here)" / D4-R.5's "conditional on that repair
landing as stated" are now DISCHARGED conditions — rev 12-14 landed
(SAE) exactly as L3 states it, and rev 14 passed the dual bar
(2026-07-27). The brackets are dated and truthful; the discharge
should be recorded in §D4-R's acceptance record, not by editing the
frozen text mid-shot.

REMARK R2 (gloss, harmless): L3/L11 gloss (SAE) as "read side strictly
above the old box line at span slots < μᵢ", omitting the adjacent
vertex-tie clause new(μᵢ) = old(μᵢ); both cite §C's definition as
source, and §C's own reduction makes the adjacent case automatic given
the vertex-anchored side height — the gloss captures the full
substantive content.

## VERDICT

(a) B1 and B2 both correctly applied; B1's new heading matches the
    theorem beneath it; commit diff shows no other body change.
(b) Fresh angles: L9's §C C.3 citation typechecks and the side-height
    shape-dependence closes via the retained stride-position sets;
    D4-R.5's withdrawn list COMPLETE against the full rev history;
    independent gate arithmetic (C = 3/48, injectivity, FC8 = 20,
    A = 11, m̂₀ = 0) exact.
(c) All §C citations typecheck against the dual-accepted rev 14; the
    final (NA)+(HV)+(SAE) class is the form consumed; the per-step
    transition-admissible interface is not owed. Two REMARKS (R1
    favorable staleness, R2 gloss), neither a gap.

COUNT: 0 CRITICAL, 0 GAPS, 2 REMARKS. CLEAN — the Fable half of the
dual-acceptance shot is met on the rev-8 text as it stands.
