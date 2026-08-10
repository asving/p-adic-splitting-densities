# SG-2 PROBE BRIEF (RCT unit S-7-SG2-probe, CODEX arm) — 2026-08-10

You are a research mathematician doing an adversarial feasibility probe in
p-adic Okutsu–Montes/Newton-polygon combinatorics. You see ONLY this brief
(you cannot read files). All statements below are pasted verbatim from a
frozen, verified corpus, with (note, commit, line) pins.

## 0. THE QUESTION

A large verified corpus proves splitting-density laws via a "weld": four
junction theorems tying a harness calculus (Φ-developments, weights, reads)
to a classifier/print calculus. WELDMASTER packages the four junctions as
five clauses (M0)–(M4) of ONE transport 𝕋 plus a coboundary theorem WM-COB.
Separately, LEMMA J-D0 proves count-layer gauge/value blindness. The lemma
LEMMA GENHN-4 (refine transfer) currently consumes COROLLARY W-9 (a face of
junction note GRTJC) DIRECTLY as its graded organizing frame (recorded as
GENHN-BOX-2). PROBE QUESTION (exactly this, no more):

  Is LEMMA GENHN-4 re-derivable from WELDMASTER's clauses (M0)–(M4) +
  WM-COB + LEMMA J-D0 ALONE (plus GENHN's own internal lemmas GENHN-2,
  GENHN-3 and classical facts) — i.e. does the weld's one-face consumption
  through WELDMASTER's stated clauses suffice, WITHOUT any direct citation
  into the junction notes (GRTJA/GRTJB/GRTJC/GRTW2) beyond what the clause
  texts themselves state?

You do NOT decide anything about retiring notes or formalization scope.
Your deliverable is the mathematical verdict only.

## 1. THE TARGET — LEMMA GENHN-4, verbatim
(GENHN_PROOF_2026-08-08.md @ 59c1966d, L865–921)

Setting: a stage-α event at dv-slope κ (the stage polygon one side
(0, μκ)–(μ, 0), integer κ > current floor S′, residual (T − s)^μ,
s ∈ K^×). Recenter Φ′ ↦ Φ′_new := Φ′ + w, w := −ŝ·n(κ)-lift (the
canonical digit lift; convention-keyed as always).

*The computation, in three layers.*
1. **Leading graded layer (the kills).** Pass to gr R = the twisted
   algebra K^c[ℤ/e₁-graded lines] (COROLLARY W-9 @ accepted pin,
   consumed HERE as the organizing frame — disclosed; GENHN-2 makes
   the passage pointwise-faithful: one K-slot per height, slot-min =
   valuation). In gr, the development transforms by the substitution
   Φ̄′ ↦ Φ̄′ + s̄ on the residual polynomial: the new residual at the
   node heights is R(T + s) where R(T) = (T − s)^μ, ALL of whose
   coefficients below degree μ vanish — the μ pins die. The twist
   powers z^{fl} (S4's cocycle: n(κ)^t = ẑ^{fl_t}n(tκ)) enter both
   the residual assembly and the carry products IDENTICALLY, so the
   graded identity holds coefficient for coefficient over K.
   [...instance reconciliation prose elided...] Both
   characteristics: the identity R(T+s) = T^μ is binomial-free as
   stated (it is a substitution identity, not an expansion).
2. **Correction layer (everything else lands deeper and in-window).**
   The non-graded corrections — products w^{i−j}A_i and the x-degree
   overflow of w·A_i reduced mod Φ′ — have dv strictly greater than
   the pinned heights: dv(w^{i−j}A_i-correction) ≥ (i−j)κ + (μ−i)κ +
   1 = (μ−j)κ + 1 (each factor exceeds its side height only in the
   correction terms; the exact-height products ARE layer 1). By
   LEMMA GENHN-3(c)(d) they land at in-window positions and move
   upward only.
3. **Bijectivity.** The map on digit spaces is triangular (each new
   digit = old digit + strictly-lower-data), injective, image inside
   the floored node {dv(A_j) > (μ−j)κ}; onto by cardinality: the
   refine slice fixes the μ pinned digits and frees exactly the
   slots above the node floors (slot strings are key-independent —
   GENHN-2), the same count as the node. Letters: |K| − 1 choices of
   s per step. ∎

Grade note (verbatim): "At μ = 2 the identity was verified pointwise-
elementarily by GENH4 [...]. At general μ, layer 1 CONSUMES the W-9 graded
frame (accepted 2/2) rather than re-deriving the carry digit-by-digit".

GENHN-BOX-2 (verbatim, L1331–1339): "LEMMA GENHN-4's layer 1 at μ ≥ 3
consumes COROLLARY W-9's twisted algebra as the carry bookkeeping (unlike
GENH4, which re-proved its μ = 2 instances elementarily). [...] An
elementary general-μ carry display (the GENH4-S5 computation at general
(e₁, f₁, μ)) would retire this box; until then the count laws at μ ≥ 3
stand on one accepted weld face."

## 2. ALLOWED INPUT A — WELDMASTER (fdf1d995), THEOREM WELD-M, L284–311

**THEOREM WELD-M.** For every tower T of the [ILN]† S0.1 class realized as
a principal-read OM type via the dictionary map T(t) (JA-PIN — the DOMAIN
identification, consumed: every class-pin clause forced by the print's own
hypotheses, lift clause = W-2), there is ONE transport 𝕋 between the
harness calculus (Φ-developments, weights w_m, reads R_m v, the ε-kit,
canonical lifts) and the classifier/print calculus (φ-adic developments,
v_{m+1}, residual operators, t(i)-twists, GMN keys), with five clauses:

    (M0) [substrate]      𝕋 is the IDENTITY on the underlying division
         arithmetic: the same canonical division chain by the same monic
         key at the admissible representative.
    (M1) [gradings]       𝕋 preserves weights in the sheared frame
         (w_m = v_{m+1}), and its induced map on polygon/grading data is
         the explicit affine shear Σ_q(i,u) = (i, e_q·u + h_q·i) — lower
         hulls to lower hulls, vertex-for-vertex, slope law s ↦ e_q s + h_q.
    (M2) [reads/operators] 𝕋 acts on packed read data by explicit PER-SLOT
         z-characters generated by ONE 1-cochain — the S0 weld cochain
         t_j/ε_j: scalar per slot exactly on the S3 perimeter, exact
         recursion ((HR-REC) genre) elsewhere. Never slot-independent
         (JA-BOX-1 inherited verbatim).
    (M3) [multiplication] 𝕋 transports multiplication up to the carry
         cocycle: on B_n coordinates the target is the twisted group
         algebra K^c[ℤ/E] with c = z̄^δ·∏_j z_j^{D_j} on the scored
         stratum, and harness-val = TC-read.
    (M4) [covariance]     𝕋 is covariant in the lift/representative
         choice: changing the representative acts on (M2)–(M3) by the
         (ξ, w) character system, with ψ-transport making the two chains
         carry the same type.

Perimeter/conditionality carried by the faces (from the note's face table,
condensed): (M0) W-2 clause 1's perimeter; byte clause on `P≤q` only.
(M1) shared-key perimeter `P<q` (one layer at `P≤q`); a u ≥ 0 membership
residue open at the unbounded-degree quantifier. (M2) per-digit proviso at
m ≥ 3 / (R-coll); (C-coll) at m ≥ 2; mod-wrap box; PER-SLOT, never scalar.
(M3) [ILN]† scored stratum; (DMULT-w) CITED / (DMULT-s) MEASURED tier
split. (M4) scalar closed form on (C-coll) only; W2-OPEN-1 (value layer)
OPEN. The note's own remark: "WELD-M is an ORGANIZING UMBRELLA [...] What
each junction note carries BEYOND its face (its closed forms, boundary
censuses, box systems) remains in that note and is NOT absorbed."

## 3. ALLOWED INPUT B — THEOREM WM-COB (same note, L344–369)

**THEOREM WM-COB.** Let (γ, γ′) be a pair with [ILN]† S0.3 data
(δ, S_j, D_j) and per-level split weights β_j := β_j(γ), β′_j := β_j(γ′),
β″_j := β_j(γ+γ′).
(i) [integer form; unconditional; ALL pairs] For every level j = 1..n:
    D_j = t_j(β″_j) − t_j(β_j) − t_j(β′_j) =: (∂t_j)(γ, γ′).
(ii) [field form] In K_j:  z_j^{D_j} = ε_j(β_j)·ε_j(β′_j)·ε_j(β″_j)^{−1}.
(iii) [composite display; scored stratum] With ∂E(γ,γ′) :=
E(γ)E(γ′)/E(γ+γ′):  c_{n+1}(γ, γ′) = z̄^δ·(∂E)(γ, γ′).
"THE ENTIRE INNER FACTOR OF THE ACCEPTED COCYCLE IS A COBOUNDARY [...] The
outer letter z̄^δ is NOT a coboundary of this cochain."

(THEOREM WM-FENCE, the note's third statement, is the value-layer
one-perimeter fence — character-triviality specializations (R-coll)/
(VD-m)/(C-coll). Available if you need it, but it is value-layer.)

## 4. ALLOWED INPUT C — LEMMA J-D0 (JD0_PROOF @ 9387eb1a, L40–57)

The carry gauge: a 1-cochain u : γ ↦ u_γ ∈ K^* acting by anchor rescaling
a_γ ↦ u_γ·a_γ; action: ledger c(γ,γ′) ↦ c·∂u; slot v ↦ u·v; residual
R(y) ↦ ξ^{−deg R}·R(ξ·y); positions, δ, D_j, grid abscissas UNCHANGED.

**LEMMA J-D0.** (i) [GAUGE-INVARIANCE] For every decided shape T, every
prime power q, and every 1-cochain u with unit values, the stratum count of
T computed through the u-gauged read equals the direct stratum count.
(ii) [VALUE-BLINDNESS] Any two towers/types with the same shape data
(d0, (e_j, h_j, g_j)_j) and residual-degree structure have EQUAL stratum
counts at every q, regardless of their letters and carry cochains.
Consequence: the stratum count is a function of the SHAPE alone.
[Proved; perimeter: unit-character gauges; the L3 × L4 count assembly.]

## 5. ALLOWED INPUTS D — GENHN's OWN lemmas (not weld faces; @ 59c1966d)

**LEMMA GENHN-2** (L699–717): A = Σ_{i<D′} a_i x^i, a_i ∈ O. Then
dv(A(θ)) = min_i (e₁·v(a_i) + i·h) EXACTLY, for every root θ of Φ′ and
every lift; min's residue class mod e₁ is i·h mod e₁ (distinct for distinct
i mod e₁, gcd(h,e₁) = 1); within-class ties assemble Σ_t res(a_{i+e₁t})·η^t
≠ 0 by F_Q-independence of {1, η, ..., η^{f₁−1}}. Each A_j carries exactly
ONE K-digit slot per integer dv-height; formal slot-min IS the valuation:
"the graded read transcribed pointwise." (Note: "W-9's dim_K 𝒜(T) = E = e₁
is this statement's graded shadow (cited as frame)" — GENHN-2 is proved
elementarily, NOT via the weld.)

The twist paragraph (L731–738, verbatim core): normalizers n(m) :=
x^{i(m)}π^{a(m)}, i(m)·h + e₁·a(m) = m; products wrap through θ^{e₁} =
(unit lift)·π^h: n(κ)^t = ẑ^{fl}·n(tκ) with explicit integer fl = the wrap
count — "W-9's cocycle, literal." Side residuals assembled with coherent
normalizers are z-power-twisted slot digits; "counts are twist-blind
(J-D0: (digits) ↦ (twisted digits) is a type-preserving bijection),
LETTERS are twisted."

**LEMMA GENHN-3** (L741–763): (a) a computed dv-value is lift-stable iff
< e₁N; (b) class-i slot string ends at e₁(N−1) + ih (ragged); (c) every
digit consulted by a readable event sits strictly inside its class's
window (congruence argument); (d) along chains every update determines new
digits at height d from old digits at heights ≤ d: carries move upward
only. [All proved elementarily in the note.]

## 6. REFERENCE ONLY — what GENHN-4 currently consumes (NOT an allowed
input except insofar as (M3)'s clause text carries it)

**COROLLARY W-9** (GRTJC @ 63091cef, L1777–1787): Given W-6, W-7, W-8:
(i) c_{m+1} descends to ℤ/E × ℤ/E → K^* and is a 2-cocycle (= associativity
of gr(w)'s multiplication); (ii) its y-degree part δ satisfies the integer
carry-cocycle identity; (iii) 𝒜(T) is the twisted group algebra K^c[ℤ/E]
of the abscissa-coset group over the carry cocycle; (iv) the E-fold orbit
product ζ_T := ∏ c(1,k) is the K-scalar tying anchor product to π-power.

The recorded scent (HE3_PROOF @ its pin, §S0, verbatim): "GENHN.A(iv)/
LEMMA GENHN-4 is NOT consumed [by HE3], hence the W-9 graded weld face
(GENHN-BOX-2) is NOT inherited: GENHN-4 is the *digit-space bijection*
used for COUNT laws; this unit needs only the *valuations and residues* of
a recentered development."

## 7. YOUR CHARGE

ATTEMPT THE DERIVATION of LEMMA GENHN-4 (all three layers) from inputs
A + B + C + D + classical facts only. Rules:
- W-9 may be used ONLY through (M3)'s clause text ("on B_n coordinates the
  target is the twisted group algebra K^c[ℤ/E] with c = z̄^δ·∏_j z_j^{D_j}
  on the scored stratum, and harness-val = TC-read") with its scored-
  stratum perimeter — not through GRTJC's internal content.
- No input may be cited that itself consumes GENHN-4 (circularity).
- Perimeter accounting is mandatory: GENHN-4 quantifies over ALL stage-α
  events at general (e₁, f₁, μ). Say explicitly whether (M3)'s scored
  stratum + (M2)'s per-slot fences cover that range, or whether the
  perimeter mismatch is itself the obstruction.
- Note that GENHN-4 is used at STAGE level (the stage-graded algebra of a
  stage-α event, slope κ, residual (T−s)^μ) — if (M0)–(M4) speak only of
  the tower/type transport at the base weld and not of the stage-internal
  graded frame, say precisely which re-instantiation would be needed.

OUTPUT FORMAT (strict):
1. VERDICT: one of DERIVABLE / NOT-DERIVABLE / NEEDS-X. If NEEDS-X, state
   X as a precise mathematical statement (the exact missing content).
2. PER-LAYER verdicts (layer 1 graded kills; layer 2 correction
   strictness; layer 3 bijectivity+count), one line each, each naming the
   inputs (M0..M4, WM-COB, J-D0, GENHN-2, GENHN-3) actually used.
3. If DERIVABLE: the full proof sketch, numbered steps, each step naming
   its input label; flag the single most falsifiable step (one that a
   machine could spot-check on a concrete stage-α event).
4. If NOT-DERIVABLE or NEEDS-X: the EXACT obstruction — which GENHN-4
   content is not present in the weld's faces (e.g. the stage-level
   twisted-algebra structure vs the tower-level K^c[ℤ/E]; the fl-twist
   cancellation in residual assembly vs carry products; the cardinality
   count of freed slots) — stated so that a follow-up unit could target
   exactly it.
5. CHECKED-CLEAN list: which parts of GENHN-4 ARE clearly recoverable from
   the allowed inputs, so the residue is minimal.
No deference: the corpus authors expect you to try to BREAK the hoped-for
derivation. An honest NOT-DERIVABLE with a sharp obstruction is worth more
than an optimistic sketch.
