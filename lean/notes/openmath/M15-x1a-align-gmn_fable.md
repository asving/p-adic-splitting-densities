# M15-x1a-align-gmn — attempt (Fable): literature identification + faithfulness analysis

Obligation: `KT.cl15_align`, i.e. `MovesX.X1aAlignP n KC.XF ⟨true, false⟩` — for
every prime p, every monic degree-n f over ℤ_p with disc f ≠ 0, and every history
H with `inStratum f H`, the number of certified-increment nodes of H (continuing
T1-row increments and T2-row nodes) is ≤ `(gmn p).ind f`. Flagged
LITERATURE-AXIOM-ELIGIBLE. Per the literature rule, the deliverable is the exact
citation, the faithfulness analysis against the Lean row, and the residual not
covered by the citation. Everything below labeled (a) known / (b) new proof of
known / (c) claimed new.

## 1. Source verification

I re-downloaded arXiv:0807.2620v2 (J. Guàrdia, J. Montes, E. Nart, *Newton
polygons of higher order in algebraic number theory*; published Trans. Amer.
Math. Soc. 364 (2012), no. 1, 361–416) on 2026-07-31 and extracted the text with
`pdftotext` (57 pp., extraction at `/tmp/gmn_full.txt` during this session). All
quotes below are verbatim from that extraction (modulo re-typesetting of
formulas); theorem numbers are the arXiv-v2 numbers, consistent with the
project's pinned label list `docs/GMN_citations.md` (whose standing caveat —
confirm printed TAMS numbering before external use — applies here too).

Companion paper (secondary, context only): J. Guàrdia, J. Montes, E. Nart,
*Higher Newton polygons in the computation of discriminants and prime ideal
decomposition in number fields*, arXiv:0807.4065 (title verified from the arXiv
abstract page this session; journal reference — J. Théor. Nombres Bordeaux, to
the best of my knowledge — NOT verified this session, flag for lookup before
citing in print). It applies the index machinery computationally; the operative
theorem for this row lives in the TAMS paper, so I pin the citation there.

## 2. The exact literature statements [(a) known]

Base setup (arXiv:0807.2620v2 §1.2): "We fix a finite extension K of Qp as a
base field, and we denote v := v_K, O := O_K, m := m_K, F := F_K, q := |F|",
with v : ℚ̄_p → ℚ ∪ {∞} normalized by v(K*) = ℤ. (Our instance: K = ℚ_p,
O = ℤ_p, v = v_p.)

Standing convention for §4.2–4.4 (opening sentence of §4.2): "All types that we
consider are still assumed to be made up with polynomials φ_i(x) belonging to a
universally fixed family, as indicated in the last section."

**Definition of the index of an irreducible polynomial** (§4.2): for F(x) ∈ O[x]
monic irreducible, θ a root, L = K(θ): "It is well-known that
(O_L : O[θ]) = q^{ind(F)}, for some natural number ind(F) that will be called
the v-index of F(x)." And: "Recall the well-known relationship,
v(disc(F)) = 2 ind(F) + v(disc(L/K))."

**Definition 4.11** (index of a separable polynomial): "Let f(x) ∈ O[x] be a
monic separable polynomial and f(x) = F_1(x)⋯F_k(x) its decomposition into the
product of monic irreducible polynomials in O[x]. We define the index of f(x) by
the formula ind(f) := Σ_{i=1}^{k} ind(F_i) + Σ_{1≤i<j≤k} v(Res(F_i, F_j))."

**Definition 4.12** (index of a side / of a principal polygon): "Let S be a side
of negative slope, and denote E = ℓ(S), H = H(S), d = d(S). We define
ind(S) := ½(EH − E − H + d) if S has finite slope, 0 otherwise. Let
N = S_1 + ⋯ + S_g be a principal polygon, with sides ordered by increasing
slopes λ_1 < ⋯ < λ_g. We define ind(N) := Σ_i ind(S_i) + Σ_{i<j} E_i H_j. If N
has a side S_1 of slope −∞ and length E_∞ := E_1, it contributes with
E_∞ H_fin(N) to ind(N), where H_fin(N) is the total height of the finite part."

**Remark 4.13**: "ind(N) = 0 if and only if either N is reduced to a point, or N
is one-sided with slope −∞, or N is one-sided with E = 1 or H = 1."

**Remark 4.14**: the finite-slope contribution to ind(N) "is the number of
points of integer coordinates that lie below or on the finite part of N,
strictly above the horizontal line L that passes through the last point of N,
and strictly beyond the vertical line L′ that passes through the initial point
of the finite part of N." (In particular ind(N) ≥ 0, and ind(N) ≥ ind(S) for
each single side S of N, since all summands in Definition 4.12 are ≥ 0.)

**Definition 4.15** (higher-order indices): "Let P(x) ∈ O[x] be a monic and
separable polynomial. Let t be a type of order r−1 and φ_r(x) a representative
of t. We define ind_t(P) := f_0⋯f_{r−1}·ind(N_r^−(P)), where N_r(P) is the
Newton polygon of r-th order with respect to t̃. For any natural number r ≥ 1 we
define ind_r(P) := Σ_{t ∈ t_{r−1}(P)} ind_t(P)." Followed immediately by the
choice-dependence warning: "Since the Newton polygon N_r^−(P) depends on the
choice of φ_r(x), the value of ind_t(P) depends on this choice too, although
this is not reflected in the notation."

**Theorem 4.18 (Theorem of the index)**: "Let f(x) ∈ O[x] be a monic and
separable polynomial, and r ≥ 1 a natural number. Then,
(1) ind(f) ≥ ind_1(f) + ⋯ + ind_r(f), and
(2) equality holds if and only if ind_{r+1}(f) = 0."

**Corollary 4.19**: "Let f(x) ∈ O[x] be a monic and separable polynomial. There
exists r ≥ 0 such that all types in t_r(f) are f-complete, or equivalently, such
that t_{r+1}(f) = ∅."

Also relevant, **Lemma 4.16**(1): if t ∉ t_r(P) or t is P-complete then
ind_t(P) = 0.

## 3. The dictionary between the Lean table and Definition 4.12 [(b) new proof of known + executed check]

The Lean per-node quantity `ind2` (MovesX/Defs.lean) is the DOUBLED single-side
index of Definition 4.12 under the substitution E = eℓ, H = hℓ, d = ℓ (a side of
slope −h/e in lowest terms, lattice length ℓ):

  2·ind(S) = EH − E − H + d = ehℓ² − eℓ − hℓ + ℓ = ℓ(ehℓ + 1 − e − h),

which is the T1 row, and at ℓ = 1 equals (e−1)(h−1), the T2 row. This is an
exact algebra identity (two lines above); machine-checked corpus counterparts:
`ind2Region` (XA9) proves ind2 ν = 2·|region ν| with the Remark-4.14 region
(translated to initial point (s₀, u₀+hℓ), last point (s₀+eℓ, u₀): strictly
beyond x = s₀, strictly above y = u₀, on-or-below the side), and 1 ≤ ind2 at
continuing T1/T2 nodes — whence ind(S) ≥ 1 there, since ind(S) = |region| ∈ ℕ.
Executed brute-force cross-check this session (see NUMERIC-TESTS, N1): 1548
configurations, zero violations, including translation-invariance in (s₀, u₀).

Per-side positivity, un-doubled [(a) known, elementary]: at T1 (ℓ ≥ 2, e,h ≥ 1)
and T2 (ℓ = 1, e,h ≥ 2 coprime) the side satisfies ind(S) ≥ 1; at T3
(ℓ = 1, h = 1) and T4 (ℓ = 1, e = 1) the region is empty and ind(S) = 0 —
exactly Remark 4.13's "one-sided with E = 1 or H = 1" degenerate cases. So the
Lean row classification T1/T2 vs T3/T4 is precisely "the read side alone forces
ind(N) ≥ 1" vs "the single side certifies nothing".

## 4. Faithfulness analysis: what the Lean row asserts vs what Thm 4.18 says

**The covered face.** Theorem 4.18(1) + Definition 4.15 + Remark 4.14 yield,
rigorously and with no further input: for f monic separable, the family
{ind_r(f)}_{r≥1} of naturals satisfies, for every finite R ⊆ ℕ_{≥1},

  (†)  Σ_{r ∈ R} ind_r(f) ≤ Σ_{r=1}^{max R} ind_r(f) ≤ ind(f),

the first inequality because every ind_r(f) ≥ 0 (Def 4.15: a product of the
natural number f_0⋯f_{r−1} with the lattice count ind(N_r^−) ≥ 0, summed over
the finite type set t_{r−1}(f)), the second is Thm 4.18(1) at r = max R. (†) is
EXACTLY the `finsum_le` field of the proved KE8 reduction carrier
`GmnOrderAccounting` under orderInd f r := ind_r(f) (with orderInd f 0 := 0),
modulo one bookkeeping remark: (†) presupposes a CHOICE of representatives
("universally fixed family", §4.2 opening), and ind_r(f) is well-defined only
relative to that choice — the axiom must therefore be keyed to the engine's own
pinned representative family, not to a nonexistent canonical value.

**Does the Lean row state MORE than the citation? YES.** `X1aAlignP n X
⟨true,false⟩` is not a statement of the paper. The excess, itemized:

1. **Vocabulary**: Thm 4.18 speaks of GMN types t ∈ t_{r−1}(f) and the polygons
   N_r^−(f); the row speaks of the engine's node ledgers H (raw per-step frames,
   letter fields (e, h, ℓ, sel, isIncrement)) and an interface `ind` about which
   the type imposes only `p2`. The citation says nothing about histories.
2. **Placement**: the row needs each certified node of H to occupy its OWN GMN
   order, injectively across the history (distinct certified nodes ↦ distinct
   orders r with ind_r(f) ≥ 1). Not in the paper: it is a property of the
   engine's tree-building discipline (each T1/T2 increment strictly grows the
   key degree, opening a genuinely new order; re-centerings — excluded from
   `dCert` at this state — are exactly the steps for which this FAILS to be
   automatic, which is why the ⟨true,false⟩ state exists).
3. **Normalization crossing**: the node's (e, h, ℓ) are read on the engine's raw
   window polygon; ind_t(f) is computed on N_r^−(f) in the order-r valuation
   v_r's normalized coordinates (Def 2.5). The row needs: at the placed order,
   the read side data agrees with a side of N_r^−(f) with the same (e, h) and
   the same ℓ ≥ 2 / ℓ = 1 classification, so §3's positivity transfers to
   ind_{t}(f) ≥ 1, hence ind_{r}(f) ≥ 1. Not in the paper.
4. **Representative admissibility**: ind_t(f) is representative-dependent
   (Def 4.15's warning). The row needs the engine's canonical key lifts to be
   admissible GMN representatives forming one fixed family. Not in the paper
   (the paper only requires SOME universally fixed family — one admissible
   choice suffices, but that the engine's choice is admissible is engine-side).
5. **Scope of `inStratum`**: the row quantifies over EVERY H with
   `inStratum f H` and carries no history-well-formedness hypothesis. The
   citation covers no junk histories; the real instance must pin `inStratum` to
   genuine ledgers (the converse of the carried `gmnLink`), or the placement
   legs are unprovable.
6. **Hypothesis match (no excess here)**: monic ✓; separable — Lean's
   `f ∉ discZero` (disc ≠ 0 in ℤ_p) is equivalent for monic f in char 0 ✓;
   base field — the citation covers all finite K/ℚ_p, the row needs only
   K = ℚ_p, so the citation is strictly more general ✓; `ind` ℕ-valued ✓.
7. **The interface law `p2`** (2·ind f ≤ v_p(disc f)) is NOT this row, but the
   same instantiation must discharge it; it follows from Def 4.11 + the quoted
   "well-known relationship" per irreducible factor + disc(∏Fᵢ) = ∏disc(Fᵢ) ·
   ∏_{i<j}Res(Fᵢ,Fⱼ)² and v(disc(Lᵢ/K)) ≥ 0. Known (Ore-era); the paper states
   the per-factor relation with "recall", so a faithfulness entry should cite
   it as classical (e.g. Serre, Corps Locaux III §6, or Neukirch III.2) rather
   than as a GMN theorem. [(a) known]

**Axiom-scoping trap (explicit warning).** The tempting shortcut — declaring
`∀ p, Nonempty (GmnOrderAccounting n p (X.gmn p))` as THE axiom — is NOT
faithful: the carrier's `place`/`place_inj`/`place_charged` fields are items
2–4 above, which the paper does not assert. A faithful literature axiom may
cover exactly (†); the placement fields must remain engine-side proof
obligations. (This mirrors how the project's earlier uniform read-guard axiom
was caught false: over-scoping an import beyond the cited statement.)

## 5. Residual not covered by the citation — the open lemmas

At the real instance (OM engine; canonical classification tree of f), with the
engine's pinned representative family F_rep:

- **OL-1 (order placement).** For every monic separable f and every ledger H of
  a path of f's tree, there is a map r : {certified-increment nodes of H} → ℕ_{≥1}
  and types t_ν ∈ t_{r(ν)−1}(f) (built inside F_rep) with r injective.
  Expected mechanism: each T1/T2 increment strictly increases the key degree
  m_r = m_{r−1}e_{r−1}f_{r−1}, and GMN order increments track exactly these.
- **OL-2 (normalization crossing / per-order positivity).** For each certified ν,
  ind_{t_ν}(f) ≥ 1 — via: the side read at ν, transported from the engine's raw
  frame to the v_{r(ν)}-normalized frame of N_{r(ν)}^−(f), lands as a side with
  the same (e, h) and same T1/T2 class, and §3 gives ind ≥ 1; then
  ind_{r(ν)}(f) ≥ ind_{t_ν}(f) by nonnegativity of the other types' terms.
- **OL-3 (representative admissibility).** The engine's canonical lifts are
  representatives in the sense of GMN Def 2.12 and form one universally fixed
  family F_rep (so Defs 4.15/Thm 4.18 apply as stated to the engine's data).
- **OL-4 (stratum scope).** The instance's `inStratum f H` holds ONLY for
  ledgers H of actual paths of f's tree (converse direction of `gmnLink`).

OL-1–OL-3 are the project's named "(ALIGN-inc)" duty; none is a literature
statement. Given OL-1–OL-4 plus axiom (†), the row follows by the PROVED KE8
reduction `x1aAlignInc_of_orderAccounting` (machine-checked): the injective
placement turns dCert into a sum of per-order contributions ≥ 1 over the image
finset, and (†) dominates that sum by ind(f). I verified the KE8 proof term
reads exactly this argument; no hidden appeal beyond the carrier fields.

## 6. Recommended faithful axiom shape [(c) proposed formulation, not declared]

Engine-side definitions to be built first: `gmnInd p f : ℕ` (Def 4.11 at
O = ℤ_p) and `gmnOrderInd p f r : ℕ` (Def 4.15 at the engine's F_rep; value 0
at r = 0). Then the ONLY literature-covered declaration is

```lean
-- [CITE] GMN arXiv:0807.2620v2 Thm 4.18(1) + Def 4.15 (nonnegativity) + Def 4.11,
-- keyed to the engine's pinned representative family (§4.2 "universally fixed").
axiom AX_GMN_index_finsum (p : ℕ) [Fact p.Prime] {n : ℕ} (f : MonicBox n p)
    (hdz : f ∉ discZero n p) (R : Finset ℕ) :
    ∑ r ∈ R, gmnOrderInd p f r ≤ gmnInd p f
```

together with a NON-axiom instance pin `(X.gmn p).ind = gmnInd p` and separate
disposition of `p2` (classical; either its own narrow cite or a proof from
local-field discriminant theory — item 7 of §4). OL-1–OL-4 stay as engine-side
theorems feeding `GmnOrderAccounting`'s remaining fields. Per the axiom policy:
faithfulness entry in `docs/AXIOM_FAITHFULNESS.md`, guardian audit, and the
statement-side-only discipline already reserved for this slot family
(`MovesU/SlotsG8_x1aDict.lean` header).

## 7. Sanity checks executed this session

See NUMERIC-TESTS N1/N2 for specs and outputs: the Def-4.12/`ind2`/lattice-count
dictionary (1548 cases, 0 violations) and the GMN §4.3 worked family over ℤ_2
(60 samples: v_2(disc f) = 12 always; ind(f) ∈ {3, 4} exactly as the paper's
case split predicts; ind_1(f) = 2 ≤ ind(f)). The §4.3 family is also a
pencil-and-paper witness for the bookkeeping of THIS row: its order-2 step in
the v(c+2a+4) = 3 branch is a same-degree refinement (h_2 = e_2 = f_2 = 1, φ_3
of the same degree as φ_2) — a T1-row RE-CENTERING, excluded from `dCert` at
⟨true, false⟩ even though GMN's v2 bookkeeping opens a new order for it with
ind_2(f) = 1; while the certified T1/T2 increments along any branch number ≤ 2,
comfortably ≤ ind(f) = 3 or 4. The exclusion is thus visibly load-bearing and
correctly transcribed in the Lean `certified` definition.

## VERDICT

LITERATURE (scoped). The exact citation is Guàrdia–Montes–Nart, *Newton polygons
of higher order in algebraic number theory*, Trans. Amer. Math. Soc. 364 (2012)
361–416 (arXiv:0807.2620v2), **Theorem 4.18(1)** with **Definitions 4.11, 4.12,
4.15** (and Remark 4.14 for nonnegativity; Corollary 4.19 is the termination
companion, not needed for this row). It covers EXACTLY the finite-sum face (†)
= `GmnOrderAccounting.finsum_le` at orderInd := ind_r, keyed to a pinned
representative family. The Lean row states strictly MORE than the citation; the
residual is the four engine-side open lemmas OL-1 (injective order placement of
certified increments), OL-2 (raw-to-v_r-normalized side-data crossing giving
ind_{t}(f) ≥ 1 per certified node), OL-3 (the engine's canonical lifts form an
admissible universally-fixed representative family), OL-4 (`inStratum` pinned to
genuine tree ledgers). Given (†) + OL-1–4, the row follows by the already
machine-checked reduction `x1aAlignInc_of_orderAccounting` (MovesX/KE8). Do NOT
declare the KE8 carrier itself as the axiom — that would over-scope the import
beyond the cited statement (§4's axiom-scoping trap).

## NUMERIC-TESTS

- **N1 (EXECUTED, PASS — dictionary check).** For all coprime pairs 1 ≤ e, h ≤ 8,
  lengths 1 ≤ ℓ ≤ 6, offsets s₀ ∈ {0,2,5}, u₀ ∈ {0,3} (1548 configurations):
  brute-count the lattice points with s₀ < x ≤ s₀+eℓ, u₀ < y ≤ u₀+hℓ,
  h(x−s₀)+e(y−u₀) ≤ ehℓ; check 2·count = EH−E−H+d (Def 4.12 with E=eℓ, H=hℓ,
  d=ℓ) = the Lean `ind2` table row value (T1 formula at ℓ≥2, (e−1)(h−1) at
  ℓ=1 ∧ e,h≥2, 0 at the T3/T4 shapes), and count ≥ 1 exactly on T1/T2 shapes.
  Result: 0 violations. Pure python (no deps); rerun cost seconds. A violation
  would refute the Lean table's transcription of Def 4.12.
- **N2 (EXECUTED, PASS — worked-example family, PARI/GP `gp` in ~/.local/bin).**
  GMN §4.3: f = x⁴ + ax² + bx + c ∈ ℤ[x], v₂(a) ≥ 2, v₂(b) = 3, v₂(c) = 2.
  For 60 random members compute v₂(disc f) and ind₂(f) via the étale-algebra
  formula ind_p(f) = Σᵢ (v_p(disc fᵢ) − v_p(disc Kᵢ))/2 + Σ_{i<j} v_p(Res(fᵢ,fⱼ))
  over the ℚ-irreducible factors (poldisc/nfdisc/polresultant). Result:
  histogram {(12,3): 51, (12,4): 9} — v₂(disc) = 12 always and ind ∈ {3,4},
  matching the paper's case split exactly; ind₁ = 2 ≤ ind always. A value
  outside {3,4}, or v₂(disc) ≠ 12, would refute my reading of Defs 4.11/4.15
  or the paper's example.
- **N3 (PROPOSED — Thm 4.18(1) at r = 1, broad sweep).** For p ∈ {2,3,5},
  n ∈ {3,…,6}, ≥10⁴ random monic squarefree f ∈ ℤ[x] with coefficients drawn
  from [0, p⁵) (plus Eisenstein-perturbation families f = g(x) + p·h(x), g ≡ xⁿ):
  compute ind_p(f) as in N2; compute ind₁(f) = Σ_{φ̄ repeated factor of f̄ mod p}
  deg(φ̄) · ind(N_φ^−(f)) via the φ-adic development (sympy or hand-rolled
  polynomial division mod p^k, k ≈ 40; lattice count per Remark 4.14). Confirm
  ind₁(f) ≤ ind_p(f) pointwise. Any violation refutes the transcription of (†)
  (or an implementation bug); zero violations over the sweep is supporting
  evidence for the axiom face as formulated in §6.
- **N4 (PARTIALLY EXECUTED, PASS — direct probe of the ROW's bookkeeping at
  depth 2).** Two-certified-increment families with hand-derived reads:
  f = (x² − p)² − p^{2k+1}·x. Order-1 polygon: one side (0,2)–(4,0), read
  (e,h,ℓ) = (2,1,2), residual (y∓1)² repeated — a T1-increment (key x ↦ x²−p).
  Order-2 φ₂-development f = φ₂² − p^{2k+1}x, v₂-values (Def 2.5 normalization,
  e₁ = 2, v₂(φ₂) = 2, v₂(x) = 1): points (2,4) and (0,4k+3), one side of slope
  −(4k−1)/2, read (e,h,ℓ) = (2, 4k−1, 1) — a T2 node; residual degree 1,
  f-complete. So dCert = 2 and the predicted index is
  ind = ind₁ + ind₂ = 2 + (2k−1) = 2k+1. EXECUTED (gp, p ∈ {2,3,5},
  k ∈ {1,2,3}): étale-algebra ind_p(f) as in N2 equals 2k+1 in all 9 cases —
  confirming the Def 4.15 bookkeeping AND dCert = 2 ≤ 2k+1 = ind with the
  slack growing in k. (Honesty note: my first hand computation of the order-2
  side used points (i, v₂(aᵢ)) instead of (i, v₂(aᵢφ₂ⁱ)) and predicted 2k+3;
  the executed check caught it — the recorded derivation above is the
  corrected one, re-verified against GMN's §4.3 figure conventions.)
  PROPOSED extension: exhaustive n = 4, p = 2 boxes (coefficients mod 2⁸)
  using PARI `factorpadic` to locate nontrivial strata, hand-computing order-1
  and order-2 reads on the φ₂-development for the ≤ 2-increment cases. One
  violating (f, branch) with reads certified per §3's table refutes the row
  (hence blocks the axiom route).

