# GD23 rev 3 — pass-2 hostile verification (model-diverse; Claude Fable 5, fresh context)

Charge executed: standalone read of `GD23_phaseB_verifybrief_rev3.md` ONLY (no other
project file, no prior verification reports). Quote-and-classify; fix nothing.
Audited line by line: the order-≤1 valuation/key/residual layer (§3); DEVID (§4);
the (KPirr)/BRIDGE tower composition (§5); the anchored-march (GR-B) statement pair
and its exact-match display against the quoted printed Thm 4.2 (§7.2); the properness
proviso ((GR-B)(4)); every quantifier over the arbitrary DVR; forall-by-example scan.

**VERDICT: SOUND-WITH-GAPS — 0 critical errors, 9 justification gaps (none breaking
the logical chain at the displayed perimeters; the two heaviest sit on the (GR-B)
consumption path, inside or at the boundary of the declared open package).**

Out of scope for this pass (declared, not findings): the preamble's byte-stability
claims against rev 0/rev 2 (those are other files — unverifiable standalone); the
LITUNIT/GMN/FGMN/MacLane pins themselves (declared re-checkable quotes, not flags);
the falsifier scripts (empirical record, not proof; no PROVED row rests on them).

## Positive verifications (recomputed, not merely read)

* VAL-g step (1): carry summands heavier by exactly h — recomputed; step (2) freeness
  (a content-0 deg<d₀ coefficient has NONZERO class in K₀, so the "iff every
  [u_t] = 0" clause is vacuously correct); step (3) [c_{ts}] = [a_t][b_s] with the
  carry in strictly higher weight; step (4) in(A)·in(B) ≠ 0 in the domain. Sound.
* KEY-g(ii): hom multiplicativity (exponents add slot-wise, deg(cc′) = deg c + deg c′
  in the domain K₀[z]); the lattice-line factorization δ = π̄^a Φ̄₀^b hom(c) INCLUDING
  the e = 1 corner (attack item 7: "t determined mod 1" imposes nothing, but
  a_t = a_b − κh is still forced by homogeneity — no error at e = 1); the top-term
  match forcing a+a′ = 0 and cc′ = ψ exactly; the degree block via Φ̄₀-degrees adding.
  Sound. KEY-g(ii) does prove primeness outright, i.e. (KPirr) at j = 0 as claimed.
* KEY-g(iii): in(f) = Φ̄₀^{s0}π̄^{β}hom(R) with β = u₀ − g′h recomputed from the line
  heights ℓ(s0+eκ) = u₀ − κh; the ord-transport argument (Φ̄₀ ∤ ψ_hom via ψ(0) ≠ 0,
  ψ_hom ∤ Φ̄₀ incl. the eg = 1 corner, hom-shape matching) checks.
* DEVID: the (g1)/(g2) substitution, ψ̂^m factoring in a domain, k = m isolation,
  u-invertibility, block contradiction at deg C_m < deg Φ — all check. The rev-2
  note is CORRECT: no primeness ((KPirr)) is consumed anywhere in the proof.
* BRIDGE: both directions recomputed, including the two ultrametric forcing steps
  (W(ca) = W(b)) and the representative-lift step (any coset representative c of a
  nonzero class has W(c) = γ); the b = ca corner is harmless (W(0) = ∞ convention).
  §5 applies it only at W = e_i·w_i under the (V1)_i induction hypothesis (attack
  item 1: checked — no application at a mere semivaluation).
* V1-tower: (KPirr) ⟹ Def 4.1(i) via BRIDGE twice, sound; (KPa)-block ⟺ Def 4.1(ii)
  contrapositive, sound; scaling remark (equivalence-divisibility is order-data only,
  preserved under positive scaling) sound; γ_{i+1} > e_i·w_i(Φ_i) from h_i ≥ 1. The
  (KP_{i−1}) ↔ (Φ_i, gr(w_i)) index bookkeeping (attack item 2) is consistent.
* POS-g(iv) division control: DEVID's hypotheses at (w_i, Φ_i) are exactly
  (V1)_i + (KP_{i−1})'s (KPa)-block; the slot-r bound with d-terms heavier by h_i
  recomputed; the conditional claim is honestly scoped.
* (2′) two-form internal consistency: ϕ(f)·R^{gr}(in f)(ȳ) = ϕ_α·R^{gr}_α(in f)(ȳ)
  given ord_z(R^{gr}_α(in f)) = j₀ (Cor 4.4(3) makes z^{−j₀}·R^{gr}_α a genuine
  polynomial); eq. (16) exponent arithmetic s(α) + j₀e_r = s(g), u(α) − j₀h_r = u(g)
  checks given the left endpoint on the weight-α lattice line (which holds: the
  side's initial vertex attains the minimum weight, and attaining abscissas are
  spaced e_r apart from s(α)). The order-1 instance display recomputed against
  KEY-g(iii): ϕ = Φ̄₀^{s₀}π̄^{β+g′h} = Φ̄₀^{s₀}π̄^{u₀} = ϕ_α·ȳ^{j₀} — exact; the
  ȳ^{⌊s₀/e⌋} weight-vs-side distinction is real already at order 1 as claimed.
* Properness proviso: the degree-increasing automaticity (Φ_{j+1} ∼ Φ_j ⟹
  Φ_{j+1} |_w Φ_j ⟹ deg Φ_j ≥ deg Φ_{j+1} by minimality, vs deg Φ_{j+1} =
  e_j g_j deg Φ_j) recomputed — genuine side condition exactly at e_j·g_j = 1. The
  proviso correctly targets Φ_{i+1} as key for w_{i+1} = the clause-(4) key ψ̂.
* Route A circularity probe (the §4 "WGEO re-founded" corollary lists (V2c) =
  GD3-MIN among WGEO's inputs, and Route A of GD3-MIN cites "the WGEO(b)
  factorization" — a potential cycle): the cited component is displayed with inputs
  "gr a domain + (KPa) block" only, and I re-derived that the first-attainment =
  ord_{ψ̂}(in f) claim IS provable from exactly those (each S-slot term
  in(C_k)u^kψ̂^k has ψ̂-order exactly k by the block; factor ψ̂^{min S}; if ψ̂
  divided the bracket it would divide in(C_{min S})·u^{min S}, contradiction). No
  circularity through (V2c).
* Arbitrary-DVR quantifier sweep: no proof in §§3–6 consumes completeness (no
  Hensel, no limits), perfectness (no separability anywhere; K₀ = F[X]/(φ̄) is a
  field for any F), or a multiplicative section. The §1.1 usage display is accurate
  for every PROVED row. The D-3-kill instantiation claim (O_δ, F_q[[t]]) follows.
* Forall-by-example scan: §9 is falsifier record only; the two countermodels in
  §7.2 are used existentially (to refute rev 0's deduction) — legitimate; no ∀-claim
  anywhere rests on instances.
* UNIQ, TIE (modulo pins), REC-c1: the (u1)/(u2) instantiation arithmetic
  (w_{j+1}(b) = e_j·w_j(b) on low degrees via slot-0; key values matching through
  (P-key); T-1's e_{r−1}-rescaled form matching the (u2) shape) recomputed. The
  §1.2/§6 index-dictionary constants (E_i = e₀⋯e_{i−1} = v_{i+1}(π)) check (attack
  item 6: no off-by-one found).

## Findings (quote → classify), most severe first

### F1 — JUSTIFICATION GAP: Route B / GD3-FULL apply (GR-B)'s operators outside their displayed domain; "side-supported" undefined

§7.2: "a matching PAIR of residual operators on the nonzero SIDE-SUPPORTED
homogeneous elements of gr_K(w)". §7.3 Route B: "Write in(f) = ψ̂^m·β with ψ̂ ∤ β
… Apply R^{gr}: by (1)+(3), R^{gr}(in f) ∼ ψ_i^m·R^{gr}(β), and ψ_i ∤ R^{gr}(β)
by (4)."

"Side-supported" is never defined in the brief. Route B fires clause (1) on the
pairs (ψ̂, ψ̂^{k−1}β) and clause (4) on β without establishing that β and the
intermediate ψ̂^kβ lie in the operators' domain. If "side-supported" means merely
"homogeneous" (all monomials of a homogeneous element lie on one weight line
automatically), the restriction is vacuous and the deduction is fine — but then the
adjective is dead weight inviting exactly this ambiguity; if it means anything
stronger, the displayed deduction is out of domain as written. Same issue for
GD3-FULL's "dividing in(f) by … ϕ(f) yields R^{gr}(in f)(ȳ)". Assume the vacuous
reading and continue: everything downstream survives. (FGMN's own operators are
total on nonzero g, so the source supports the vacuous reading — but the brief's
own display is what is being verified.)

### F2 — JUSTIFICATION GAP: the exact-match display silently consumes that FGMN's residual operators factor through the initial form

§7.2 match display: "in(f) ↔ H_µ(g) … R^{gr}_α ↔ R_{r,α} … The match is EXACT as a
two-form statement. The only intentional differences, both declared: (a) … (b) …
nothing else is consumed."

The printed operators R_{r,α}(g), R_r(g) take the POLYNOMIAL g as argument; (2′)'s
R^{gr}_α, R^{gr} take the graded element in f. The dictionary row "R^{gr}_α ↔
R_{r,α}" therefore consumes a third equivalence: that R_{r,α}(g) depends on g only
through H_µ(g) (true — the coefficients are residues of the attained digits, which
are exactly the data of H_µ(g) — but it is a lemma-shaped fact about the printed
Def 3.16, not a notation change). Against the display's own "check nothing ELSE is
silently consumed" (attack item 3), this is a fourth undeclared difference beyond
(a)/(b). No downstream damage; the transcription residue of (GR-B) should name it.

### F3 — JUSTIFICATION GAP: TIE's policy-pin hypothesis is dropped at the summary layer ("exactly three GMN transcriptions")

§0: "the MacLane↔GMN identification w_i = v_{i+1} (Theorem TIE) rests on exactly
three GMN transcriptions — ALL THREE now pinned". Status table: "TIE … PROVED
modulo pinned transcriptions (L2)/(L4-P2.7)/T-1".

§6's actual statement carries a further displayed hypothesis: "the policy pin (the
engine/O-1thr keys Φ₀, …, Φ_{i+1} ARE the GMN representatives φ₁, …, φ_{i+2} of the
truncated types — GD-1/OL-1(b) territory, a displayed hypothesis here)". The §0
paragraph, the status-table row, and the §8 OL-2(a) row all advertise TIE's
conditionality as the three transcriptions only. Honest in §6, under-advertised
everywhere summarized; REC-c1 and GD3-MIN Route A inherit the same omitted
hypothesis. Ledger-accuracy repair, not a chain break.

### F4 — JUSTIFICATION GAP: ord_{ψ̂} well-definedness at general order leans on (g3)'s bounding datum without displaying it

§7.3 Route B: "(m := ord, well-defined: gr a domain, §1.3 (g3))"; §1.3 (g3):
"ord_δ(α) … is well-defined in a domain for homogeneous δ of positive
weight-or-degree data bounding the chain."

A domain alone does not bound divisibility chains (δ a unit gives ∞). (g3) itself
names the needed extra datum, but at general order the brief never displays what
bounds ψ̂-chains in gr(w_{i+1}) (at order 1 it is the Φ̄₀-degree via VAL-g's explicit
ring; at orders ≥ 2 it is derivable from the (KPa) block via BRIDGE — ψ̂^k | in(f)
forces k·deg Φ_{i+1} ≤ deg f by iterated equivalence-divisibility and minimality —
but that derivation is nowhere shown). Assume and continue.

### F5 — JUSTIFICATION GAP: KEY-g(iii)/RES-1 consume (R1)/(R2), ℓ(·), side data, and R_λ as external definitions with only a gloss

§2: "(R1) at all slots and (R2) at its strides (the standing WGEO hypothesis of
O-1thr §2.5 — side support with equality only at strides, and exact digit pins at
the strides…)"; §3 KEY-g(iii) proof: "By (R1)/(R2), the w₁-minimizing slots of f's
development are exactly the on-line strides of the side, with digit classes the
residual coefficients c_κ = [b_{s0+eκ}/π^{ℓ(s0+eκ)}]".

Standalone, (R1)/(R2), the line-height function ℓ, the side tuple (e, h, s0, d),
and GMN (L3)'s R_λ are undefined imports; the proof's first sentence is read off
them. The parenthetical gloss does pin the intended content (with it, the sentence
is nearly definitional), so this is a definitional-import gap, not an error — but
KEY-g(iii) and RES-1's "PROVED" status is conditional on the O-1thr/GMN definitions
matching the gloss, which this pass cannot check.

### F6 — JUSTIFICATION GAP: VAL-g claims a valuation on K[x] but DEV-g is stated for O[x] dividends

§3 VAL-g proof (1): "By DEV-g (applied to the dividend
a_t b_s ∈ π^{w₀(a_t)+w₀(b_s)}O[x] …)". DEV-g: "B, B′ ∈ O[x] with B ≡ B′ (mod π^L)".

For A, B ∈ K[x] the contents w₀(a_t), w₀(b_s) can be negative; π^N O[x] with N < 0
is outside DEV-g's displayed hypotheses. The standard π-power clearing (rescale
A, B into O[x], use POS-g(ii)-style homogeneity of the whole computation) repairs
it in one line, but that line is not displayed. Assume and continue.

### F7 — JUSTIFICATION GAP: the properness proviso's Lemma-5.3 firing needs an undisplayed chain-completion step

§7.2 (GR-B)(4): "Under the proviso, FGMN's displayed remark 'In every MacLane
chain, all φ_i are proper key polynomials for µ_{i−1}' … applies to the extended
chain and gives Φ_{i+1} proper for w_{i+1}".

The remark speaks of MacLane chains OF a valuation µ; for Φ_{i+1} to appear as a
chain key at position i+2 one must first augment w_{i+1} at Φ_{i+1} (any admissible
value) so that (Φ₀,…,Φ_{i+1}) is a chain of the augmented valuation. Trivial
(augmentations exist by Thm 4.2, whose hypotheses the proviso's chain condition
supplies), but the step is consumed silently. Otherwise the proviso display —
automaticity at degree-increasing reads, genuine condition at e_j·g_j = 1, the
Cor 5.12 intrinsic-vs-tower-data distinction — is internally correct and honestly
owned by GD-1 with (KP).

### F8 — JUSTIFICATION GAP: §1.3 asserts π̄ invertible at semivaluation generality

§1.3: "π̄ := in(π) is then invertible, since w(π^{−1}) = −w(π) makes
in(π)·in(π^{−1}) = in(1) = 1".

For a bare semivaluation, superadditivity gives only w(1) ≥ w(π) + w(π^{−1}) (and
w(1) ≤ 0); the displayed equality w(π^{−1}) = −w(π) is an extra property, not a
consequence. Every actual consumer fires gr either at a valuation (DEVID, BRIDGE,
GAUSS-g/VAL-g) or at a w_i where constants scale exactly (POS-g(ii)), so no
downstream damage — but the vocabulary display over-claims at its stated
generality.

### F9 — JUSTIFICATION GAP: §5's Def 4.1(i) "⟺" chain skips homogeneous-prime ⟹ ring-prime

§5: "Def 4.1(i) … ⟺ (by Lemma BRIDGE, twice) in(Φ_i) is prime in gr ⟺ (u
invertible, (KPa)) ψ̂_hom^{(i−1)} is prime = (KPirr)".

BRIDGE translates Def 4.1(i) into primeness of in(Φ_i) FOR HOMOGENEOUS divisibility
(all initial forms are homogeneous); (KPirr) asserts primeness in the ring gr. The
direction the tower consumes ((KPirr) ⟹ ring-prime ⟹ homogeneous-prime ⟹
Def 4.1(i)) is sound as displayed; the reverse arrow of the "⟺" needs the standard
graded-domain lemma (homogeneous element prime on homogeneous elements is prime),
which is true over a ℤ-graded domain but not displayed. Decorative direction only;
no consumer damage.

## Attack-list disposition (rev-3 §10 list)

(1) BRIDGE: clean (see positive verifications). (2) POS-g division control: clean;
consumption note not contradicted by any §8 row I could check standalone. (3) §7.2
exact match: one silent consumption found — F2. (4) IFACE per-clause scope: §8's
rows as printed stay within the per-clause scopes; no consumer visibly reads clause
(b) outside GMN's scope (engine-side rows are residues, not claims). (5) march at
every consumption site: present at GD-3(full)/(slot law), (GR-B)(2′), GD3-FULL/OL-B,
IFACE(c), §8 CU-1 row — confirmed. (6) index dictionary: constants check; no
off-by-one found. (7) hom-descent at e = 1: sound (recomputed). (8) properness
proviso: F7 (minor); the intrinsic-data caveat is honestly displayed and owned.

## Verdict

SOUND-WITH-GAPS. 0 critical errors; 9 justification gaps (F1–F9), none of which
breaks the chain at the brief's own displayed perimeters: F1/F2/F4 sit on or at the
boundary of the declared-open (GR-B) package, F3 is summary-layer ledger accuracy,
F5–F9 are local display debts. Per the standing protocol this is one pass of the
two-pass bar; the statements remain PROVED-UNVERIFIED until the bar's acceptance
criteria are met.

— pass 2 of 2 (model-diverse), Claude Fable 5, fresh context, 2026-07-31.
