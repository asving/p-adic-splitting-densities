/-
# H3_omsat_brief — (OM-SAT) faithfulness brief (unit D12R-U3, HDISCHARGE_H3 §2.2)

Prover D12R-U3, HDISCHARGE_H3 division, 2026-08-01 (machine clock; ledger window
2026-08-05). Blueprint of record: `lean/blueprints/HDISCHARGE_H3.md` §2.2
"(OM-SAT) faithfulness brief (unit D12R-U3)" + §4 unit row (kind: faithfulness
brief; wave 0; gate: **TAMS pagination**). This is a DOC unit: the blueprint
assigns it NO Lean statement, so this file is a literate Lean markdown note in
the H4-M2/H4-M4/H4-M7 format with **zero declarations and zero sorry** (the
whole file is one Lean block comment). Gate command (from `lean/`):
`lake env lean notes/openmath/H3_omsat_brief.md` — green.

## 0. Charge and non-charge

The (OM-SAT) literature rider ALREADY EXISTS. `docs/ROOT_ASSEMBLY_2026-08-02.md`
§4 item 1 ([GMN] entry, lines ~1703-1712), verbatim:

> **LIT-4/(OM-SAT) rides this entry by id [added at unit TREE-GAPS, audit
> A-2]:** a realized OM branch with residual multiplicity 1 at its last read
> certifies an irreducible factor with e = e₁⋯e_r, f = f₀⋯f_r (Cor 3.8 +
> Def 3.9; order-1 instance Cor 1.20 — the pins Steps 11/12 already consume);
> audited scope **"K = ℚ_p exactly"**, consumed only through the dictionary
> node O-2; its K_δ (δ > 1) re-scope duty is exactly (UB-X)(a) content (the
> per-leaf O_δ re-base audit, §3.1) — named here rather than ridden
> generically. Status: LITERATURE-CONDITIONAL (printed-TAMS pagination
> confirmation owed — §3.3).

So this brief is NOT a new pin. Its three jobs (BP §2.2, verbatim scope):
(i) the printed-TAMS pagination confirmation (the §3.3 debt named on the row);
(ii) the clause-for-clause match display between MOVES §T.2's (OM-SAT) wording
and Cor 3.8 with Def 3.9's "f-complete/optimal type" wording; (iii) the risk
register (r-1)-(r-3). Throughout, the engine↔GMN identification is CITED at
the dictionary node O-2 (`docs/MATH_COMPLETION_TREE_2026-08-01.md` §"O-2
(K-DICT)", clauses (i)-(vi)) — this brief consumes O-2's dictionary, it does
not re-derive it, and it must not silently duplicate the (H1) pricing.

## 1. (i) THE GATE — printed-TAMS pagination confirmation: **CONFIRMED**

**Source of record (the PRINTED journal PDF, not the arXiv preprint).**
Retrieved 2026-08-01 (machine clock) from the AMS site,
`https://www.ams.org/journals/tran/2012-364-01/S0002-9947-2011-05442-5/S0002-9947-2011-05442-5.pdf`
(TAMS is free-access past 5 years). 56 pages; sha256
`4e6c66755289f57c26f755cd2b79e961ebf64cc12c23415947f6f8995aeb92f5`
(working copy at /tmp/gmn_tams.pdf; not committed — repo unchanged outside
this file). Front matter, verbatim (printed p. 361):

> TRANSACTIONS OF THE AMERICAN MATHEMATICAL SOCIETY
> Volume 364, Number 1, January 2012, Pages 361-416
> S 0002-9947(2011)05442-5
> Article electronically published on May 18, 2011
> NEWTON POLYGONS OF HIGHER ORDER IN ALGEBRAIC NUMBER THEORY
> JORDI GUARDIA, JESUS MONTES, AND ENRIC NART
> [p. 361 footnote:] Received by the editors October 31, 2008 and, in revised
> form, June 15, 2010.

VERDICT 1 (citation line): the repo citation "Trans. Amer. Math. Soc. 364
(2012), no. 1, 361-416" (`docs/GMN_citations.md` line 14, ROOT §4 item 1,
LIT-1) is EXACT.

**Per-locus confirmation for the (OM-SAT) rider (statement-level, verbatim
against the printed text; quotes in §1.1 below).** Running heads checked
(e.g. "374 | JORDI GUARDIA, ...", "398 | ...", "NEWTON POLYGONS OF HIGHER
ORDER | 399"); printed page = PDF page + 360 throughout, no offset drift.

| locus | printed page | check level |
|---|---|---|
| Corollary 1.20 | p. 374 | VERBATIM (quoted §1.1) |
| Corollary 3.8 | pp. 398-399 (statement p. 398; proof ends p. 399) | VERBATIM (quoted §1.1) |
| Definition 3.9 | p. 399 (§3.3 of the paper) | VERBATIM (quoted §1.1) |
| Definition 3.10 + eq. (37) | p. 399 | VERBATIM (quoted §1.1) |
| Lemma 3.11 (support: descent trigger + "(37) into irreducibles" closer) | p. 400 | VERBATIM (quoted §1.1) |
| base-field convention (K, O) | p. 366 | VERBATIM (quoted §1.1) |

VERDICT 2 (numbering): for ALL SIX loci above the printed numbering equals the
arXiv:0807.2620v2 numbering used across the repo — no drift. The standing
caveat of `docs/GMN_citations.md` (lines 19-22: "numbers transcribed from
arXiv v2 ... confirm against the TAMS PDF") is hereby DISCHARGED **for the
(OM-SAT) loci only**.

**Located-page map for the REST of the ROOT §4 item-1 pin list** (defining
statement located at printed page; NOT verbatim-checked by this unit — input
to the still-owed LIT-1/GD-7 printed-source session, ROOT §3.3 rows "LIT-1
printed-TAMS pagination" + "GD-7 flags", which this unit does NOT absorb):
Def 1.8 -> p. 367 · Thm 1.15 -> p. 371 · Thm 1.19 -> p. 374 · Lemma 2.2 ->
p. 377 · Prop 2.7 -> p. 379 · Thm 2.11 -> p. 383 · Lemma 2.17 -> p. 385 ·
Def 2.19 -> p. 386 · Defs 2.20/2.21 -> p. 387 · Thm 3.1 -> p. 391 · Cor 3.3
-> p. 393 · Thm 3.7 -> p. 397 · Defs 4.11/4.12 -> p. 404 · Def 4.15 ->
p. 405 · Thm 4.18 + Cor 4.19 -> p. 407.

### 1.1 The printed statements, verbatim

Transcription conventions: fi/ff ligatures expanded; accents in author names
as printed; ℚ̄_p denotes the printed "Qp with overline" (the fixed algebraic
closure); subscripts TeX-ified; otherwise word-for-word from the printed PDF.

**Base-field convention (printed p. 366, §1.2):**

> We fix a finite extension K of ℚ_p as a base field, and we denote v := v_K,
> O := O_K, m := m_K, F := F_K. We also fix a prime element π ∈ O.

**Corollary 1.20 (printed p. 374):**

> Corollary 1.20. With the notation above, let θ ∈ ℚ̄_p be a root of G_i(x),
> and L = K(θ). Then, f(L/K) is divisible by m deg ψ_i. Moreover, the number
> of irreducible factors of G_i(x) is at most a_i; in particular, if a_i = 1,
> then G_i(x) is irreducible in O[x], and f(L/K) = m deg ψ_i, e(L/K) = e.

**Corollary 3.8 (printed p. 398):**

> Corollary 3.8. With the notation above, let θ ∈ ℚ̄_p be a root of G_i(x) and
> let L = K(θ). Let f_r = deg ψ_{r,i}(y). Then, f(L/K) is divisible by
> f_0 f_1 ⋯ f_r. Moreover, the number of irreducible factors of G_i(x) is at
> most a_i; in particular, if a_i = 1, then G_i(x) is irreducible in O[x] and
> f(L/K) = f_0 f_1 ⋯ f_r, e(L/K) = e_1 ⋯ e_{r-1} e_r.

with, inside its proof (printed p. 399, the saturation degree identity):

> f(L/K)e(L/K) = deg G_i = f_0 f_1 ⋯ f_r e_1 ⋯ e_{r-1} e_r

**Definition 3.9 (printed p. 399, §3.3):**

> Definition 3.9. Let t be a type of order r - 1. We say that t is f-complete
> if ω_r(f) = 1. In this case, f_t(x) is irreducible and the ramification
> index and residual degree of the extension of K determined by f_t(x) can be
> computed in terms of some data of t, by applying Corollary 3.8 in order
> r - 1 (Corollary 1.20 if r = 2).

**Definition 3.10 + eq. (37) (printed p. 399):**

> Definition 3.10. In section 1.5, we defined two sets t_0(f), t_1(f). We
> recursively define t_r(f) to be the set of all types of order r constructed
> as above, t = (t; λ_r, ψ_r(y)), from those t ∈ t_{r-1}(f) that are not
> f-complete. [...] We denote by t_s(f)_compl the subset of the f-complete
> types of t_s(f), and we define T_r(f) := t_r(f) ∪ (⋃_{0≤s<r} t_s(f)_compl).
> Hensel's lemma and the theorems of the polygon and of the residual
> polynomial in orders 1, ..., r determine a factorization
> (37)   f(x) = f_{r,∞}(x) ∏_{t ∈ T_r(f)} f_t(x),
> where f_{r,∞}(x) is the product of the different representatives φ_i(x) (of
> the different types in T_r(f)) that divide f(x) in O[x].

**Lemma 3.11 (printed p. 400; support):**

> Lemma 3.11. The following conditions are equivalent: (1) t_{r+1}(f) = ∅.
> (2) t_r(f)_compl = t_r(f). (3) For all t ∈ t_{r-1}(f) and all λ_r ∈ ℚ⁻, the
> residual polynomial of r-th order, R_{λ_r}(f)(y), is separable.
> If these conditions are satisfied, then (37) is a factorization of f(x) into
> the product of monic irreducible polynomials in O[x], and we get arithmetic
> information about each factor by Corollary 3.8.

Faithfulness note on the repo transcription: `docs/GMN_citations.md` §2.3
condenses Def 3.9 to "f-complete if ω_r(f) = 1; then f_t is irreducible with
(e,f) computable from t by Corollary 3.8" — faithful, but it drops the printed
qualifier "in order r - 1 (Corollary 1.20 if r = 2)". Displayed here as
nuance (n-1) in §2; no repair to `docs/GMN_citations.md` is made by this unit
(file outside this unit's write scope).

## 2. (ii) Clause-for-clause match: MOVES §T.2 (OM-SAT) vs Cor 3.8 + Def 3.9

The consumed wording, verbatim (`lean/notes/MOVES_2026-07-24.md` §T.2,
VP-SOUND status block, lines ~7262-7273):

> (OM-SAT) Let η be a realized branch of T_can(f) with reads ν₀,...,ν_k,
>   accumulated invariants E = ∏_r e_r, F = ∏_r g_r, and cluster degree d
>   at its last read with E·F = d (equivalently μ = 1). Then the branch's
>   cluster factor f_η ∈ ℤ_p[x] (the track factor its chain certifies) is
>   IRREDUCIBLE over ℚ_p with ramification index e(f_η) = E and residue
>   degree f(f_η) = F. [Ore-Montes certificate soundness — the pinned
>   GMN/Montes material; CONSUMED as a cite, not derived from §B2-DEF, ...]
>   This discharges (τ-irr), and (τ-ns) MODULO (z-3)'s exact identification
>   (the factor IS Φ̂^μ; "Φ̂ irreducible with (E(Φ̂), F(Φ̂)) off the tower
>   data" is (OM-SAT) applied to the key's own chain).

The match display. Column "via": TEXT = supplied verbatim by the printed GMN
statement quoted in §1.1; O-2(k) = supplied by clause (k) of the dictionary
node O-2 (`docs/MATH_COMPLETION_TREE_2026-08-01.md`) — cited, OPEN, priced
there and at the (H1) rows, never re-derived here.

| # | (OM-SAT) clause | GMN counterpart (printed wording) | via |
|---|---|---|---|
| 1 | "realized branch η of T_can(f) with reads ν₀,...,ν_k" | a type t of order r-1 attached to f (Def 3.10's t_{r-1}(f)) together with its realized last-order read: a side of slope λ_r of N_r⁻(f) and a monic irreducible residual factor ψ_{r,i} of R_{λ_r}(f) with multiplicity a_i (Thm 3.7's notation, which Cor 3.8's "With the notation above" binds) | O-2(ii) order placement + O-2(iv) representative admissibility |
| 2 | "saturation μ = 1" (residual multiplicity one at the last read) | "a_i = 1" in Cor 3.8/Cor 1.20; equivalently "ω_r(f) = 1", i.e. t is f-complete (Def 3.9 — GMN's type-singleness hypothesis at the last order) | TEXT (the two GMN faces); engine μ = GMN a_i is O-2(i)'s saturation clause |
| 3 | "E·F = d (cluster degree at last read)" | the proof display of Cor 3.8: f(L/K)e(L/K) = deg G_i = f_0 f_1 ⋯ f_r e_1 ⋯ e_{r-1} e_r at a_i = 1 | TEXT for GMN's deg G_i; engine d = deg G_i rides row 4's identification |
| 4 | "the branch's cluster factor f_η ∈ ℤ_p[x] (the track factor its chain certifies)" | G_i(x) (the factor Thm 3.7 attaches to the side + residual-factor choice) = f_t(x) of the sprouted type in Def 3.10 / eq. (37)'s product — GMN's attached p-adic factor | O-2 — the SAME identification the dictionary node already owns (its clause (i) carrier + (v) tree correspondence at depth) |
| 5 | "IRREDUCIBLE over ℚ_p" | "G_i(x) is irreducible in O[x]" (Cor 3.8; Cor 1.20 at order 1) | TEXT, at K = ℚ_p (O = ℤ_p); see scope note below |
| 6 | "e(f_η) = E = ∏ e_r" | "e(L/K) = e_1 ⋯ e_{r-1} e_r" (Cor 3.8; "e(L/K) = e" at order 1) | TEXT; engine accE = e_1⋯e_r is O-2(i) (Thm 2.11's tower data e(t)) |
| 7 | "f(f_η) = F = ∏ g_r" (engine g₀ = order-0 residual degree) | "f(L/K) = f_0 f_1 ⋯ f_r" (Cor 3.8; "f(L/K) = m deg ψ_i" at order 1, m = deg φ_1 = f_0, deg ψ_i = f_1) | TEXT; engine accF = f_0⋯f_r is O-2(i) (Thm 2.11's f(t)) |
| 8 | "order-1 instance" (the Cor 1.20 rider clause) | Cor 1.20 verbatim (§1.1): a_i = 1 gives G_i irreducible, f = m deg ψ_i, e = e | TEXT |

**Scope note (row 5).** GMN fixes "a finite extension K of ℚ_p" (p. 366); the
printed corollaries therefore COVER K = ℚ_p, and the rider's audited scope
"K = ℚ_p exactly" is a consumption RESTRICTION, not an over-claim. The δ > 1
(O_δ-rebased) reads are exactly (UB-X)(a)'s duty — risk (r-2) below.

**Nuance (n-1) (off-by-one-order fence).** Printed Def 3.9 computes the
f-complete type's (e, f) "by applying Corollary 3.8 in order r - 1 (Corollary
1.20 if r = 2)" — the read-off sits at the type's LAST REALIZED order. This is
precisely (OM-SAT)'s "at its last read" and must not be re-indexed to order r.

**Honesty boundary (what TEXT does and does not give).** The printed
statements supply the GMN-SIDE read-off exactly: multiplicity-1 last read ⟹
attached factor irreducible with the displayed (e, f) products. Every
ENGINE-side identification in rows 1-4 and the accumulation matches in rows
6-7 are O-2 content — OPEN, with O-2's own conditionality display inherited
here. Cor 3.8 + Def 3.9 + Cor 1.20 is exactly the (OM-SAT) statement MODULO
the O-2 dictionary: the match is clause-complete with no remainder on the GMN
side and no clause consumed beyond the quoted texts.

## 3. (iii) Translation risks (BP §2.2's register, transcribed)

* **(r-1)** GMN's Cor 3.8 speaks of TYPES over (ℚ_p-pinned) f; our branches
  are engine objects — the identification is the (H1)/(GR-B)-adjacent
  dictionary at orders ≥ 2, ALREADY PRICED at the (H1) rows. This brief does
  NOT silently duplicate that pricing: it cites O-2's dictionary node
  (`docs/MATH_COMPLETION_TREE_2026-08-01.md`, clauses (i)/(ii)/(iv)/(v) as
  mapped in §2) and inherits its conditionality display (O-2 is OPEN).
* **(r-2)** The δ > 1 unramified-base reads are (UB-X)(a) content (the
  per-leaf O_δ re-base audit, named at the ROOT §4 row), not this brief's.
  Nothing here certifies any K ≠ ℚ_p consumption.
* **(r-3)** Attribution risk LOW: the GMN entry is the project's central pin,
  guardian-audited for the index theorem already; the residual debt was
  pagination confirmation only — now paid for the (OM-SAT) loci (§1).

## 4. Disposition

* **Gate (TAMS pagination): PASSED** — §1 verdicts 1-2, statement-level for
  Cor 1.20 / Cor 3.8 / Def 3.9 / Def 3.10+eq. (37) / Lemma 3.11 / the K
  convention, at printed pp. 374, 398-399, 399, 399, 400, 366.
* **Feeds D12R-U4** (ROOT D-12r row rewrite, VC-gated): the "GMN Cor 3.8 +
  Def 3.9 TAMS-confirmed" precondition is now ON FILE; D12R-U4 still waits on
  D12R-U1's (HL-a)/(HL-b)/(HL-c) dispositions and rides the next VC pass.
* **Stays open (named, not absorbed):** O-2 (the dictionary node, incl.
  OB1/OB2) — OPEN; (UB-X)(a) δ > 1 re-scope; the LIT-1-wide printed-source
  session (remaining loci + GD-7 flags, ROOT §3.3) — this unit confirmed the
  (OM-SAT) slice only and contributes the §1 located-page map to that session.
* Repo hygiene: this unit edits ONLY this file; the ROOT §4 item-1 status
  string and `docs/GMN_citations.md`'s caveat banner are for D12R-U4 / the
  LIT-1 session to rewrite under their own discipline.
-/
