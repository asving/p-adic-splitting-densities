# CITE-NUMBERING audit — publisher-side verification of the three gate-(b) cites

**Date:** 2026-08-16. **Unit:** AUDIT A-3 (`HYP.17` [CORE-SET]), the publisher-numbering
verification owed BEFORE the owner's gate-(b) signature on the three literature cites.
**Author:** fresh-context audit agent (no conversation history with the composing chapters).

**Charge.** Three cites await signature; their faithfulness entries carry theorem numbers read
from author PDFs / arXiv / search summaries. Verify every load-bearing (source, theorem number,
statement) triple against the most authoritative version reachable. **This audit is about
citation integrity, not mathematics** — a number that points at the wrong printed statement is
the failure mode being hunted, not a mathematical objection.

**Method / honesty.** Every number below was read out of a document fetched in this session
(publisher page, publisher metadata API, or PDF → `pdftotext -layout`). **The repo's own quotes
were treated as the object under audit, never as evidence.** Where the printed (publisher-
typeset) pages could not be opened, the exact surrogate is named, the surrogate's provenance
(compile date, referee status) is stated, and the residual risk is graded. Evidence ledger with
URLs, file dates and hashes is §8.

## 0. Verdict in one paragraph

**One package is clear; two are not.** **[GN15] Thm 2.3 (B.42)** is **VERIFIED** — volume/pages
confirmed from the publisher's own table of contents, and Thm 2.3's statement confirmed verbatim
in two independent copies, one of them the **post-referee** arXiv version the repo's docs never
cite (arXiv:1309.4340v2, comments: *"revised according to suggestions by a referee"*). Its
secondary display **GMN Thm 1.15** is **VERIFIED against the printed TAMS pages** (the AMS serves
the full article PDF free), which also discharges the standing arXiv-vs-printed caveat in
`docs/GMN_citations.md`. But **[AGNPRW] Thm 5.2 (C.94)** and the **[FGMN] battery (C.66/C.92)**
are both **NUMBER-DRIFT**: the repo read arXiv versions that the authors later renumbered, and
arXiv was never updated. The AGNPRW case is the dangerous kind — **published Thm 5.2 exists and
is a different theorem**, so the cite would mis-point silently rather than dangle; the OM
termination theorem is **published Thm 5.6**. The FGMN drift is systematic across §§1, 3, 4, 5, 6
(eight of the nine battery loci move, and two clause indices move with them). Both are cheap to
fix — renumber, do not re-prove — and neither statement changed: every quoted display was found
verbatim under its new number.

---

## 1. Verdict table

| # | Cite (as claimed in the repo) | Claimed locus | Verification method | Verdict | Corrected locus |
|---|---|---|---|---|---|
| 1 | **[GN15]** Guàrdia–Nart, *Genetics of polynomials over local fields* — volume/pages | Contemp. Math. **637** (2015) 207–241; DOI 10.1090/conm/637/12767 | AMS book page ToC (publisher JSON: StartPage 207 / EndPage 241) + Crossref record + zbMATH Zbl 1396.11143 | **VERIFIED** | — (optional: add book title *Algorithmic Arithmetic, Geometry, and Coding Theory*, AGCT-14, eds. Ballet et al.) |
| 2 | **[GN15] Theorem 2.3** — the side dissection with both degree laws (B.42) | Thm 2.3 | Two independent PDFs: UPCommons author copy (compiled 2014-04-29) **and arXiv:1309.4340v2 (2014-06-10, post-referee)** — statement compared clause-by-clause with the display quoted in CHAP-I | **VERIFIED** | — (printed AMS pages not read: LibLynx paywall; residual risk **LOW**) |
| 3 | **GMN Thm 1.15** (secondary display for B.42) | GMN, TAMS 364 (2012) no. 1, 361–416, Thm 1.15 | **Printed TAMS PDF** (free at ams.org), header *"Volume 364, Number 1, January 2012, Pages 361–416, S 0002-9947(2011)05442-5"* | **VERIFIED** | — |
| 4 | **[AGNPRW]** — journal metadata | "Found. Comput. Math. (2024), DOI 10.1007/s10208-024-09646-x" | Crossref record for the DOI (volume 25, issue 2, pp. 631–681, published-print April 2025, online 2024-02-21) | **METADATA-DRIFT** | **Found. Comput. Math. 25 (2025), no. 2, 631–681** (DOI unchanged; 2024 is the online-first year only) |
| 5 | **[AGNPRW] Thm 5.2** — OM termination (C.94, `HYP.15`) | Thm 5.2 | arXiv:2207.02139**v1** (only version; no journal-ref) vs two co-author-hosted copies of the accepted version (compiled 2023-12-11), cross-checked against the publisher abstract via Semantic Scholar | **NUMBER-DRIFT (severe — silent collision)** | **Thm 5.6.** Published **Thm 5.2 is a different theorem** (the `e`/`f` formula for the singled-out factor) |
| 6 | **[AGNPRW] Thm 4.4** — theorem of the polygon (NS-1 verbatim leg, cited in CHAP-I's B.42 entry) | Thm 4.4 | same | **NUMBER-DRIFT** | **Thm 4.10** (published 4.4 is a *Definition*). Confirmed by the publisher abstract itself: *"a key new result (Theorem 4.10)"* |
| 7 | **[AGNPRW] Thm 4.6** — `N⁺` additivity (NS-9 leg) | Thm 4.6 | same | **NUMBER-DRIFT** | **Thm 4.15** (published 4.6 is a *Definition*) |
| 8 | **[AGNPRW] Cor 2.9** — `R(gh) = R(g)R(h)` (NS-9 leg) | Cor 2.9 | same | **NUMBER-DRIFT** | **Cor 2.17** (published 2.9 is a *Theorem*) |
| 9 | **[FGMN]** — journal metadata | J. Algebra **427** (2015) 30–75 (arXiv:1305.0775) | zbMATH Zbl 1317.13006 + OpenAlex + citing papers' bibliographies | **VERIFIED** | — (add DOI 10.1016/j.jalgebra.2014.12.022) |
| 10 | **[FGMN] Thm 2.8** — `N⁻` additivity (C.66) | Thm 2.8 | arXiv v3 (repo-local) vs the later author version (compiled 2013-12-04, deposited under the J. Algebra record at UPCommons) + two author-side citation echoes | **VERIFIED (number stable)** | — (Thm 2.8 in both) |
| 11 | **[FGMN] Cor 4.7(1)/(3)** — R additivity / multiplicativity (C.66, C.92) | Cor 4.7(1)/(3) | same | **NUMBER-DRIFT** | **Cor 4.12(1)/(3)** (clause indices preserved) |
| 12 | **[FGMN] Cor 4.4(4)** — `deg R_i(g)`, `R_i(g)(0) ≠ 0` (C.66) | Cor 4.4(4) | same | **NUMBER-DRIFT (number + clause index)** | **Cor 4.9(3)** — v3's item (1) was dropped, so (4) → (3) |
| 13 | **[FGMN] Lemma 1.11** — key polys irreducible in `K_v[x]` (C.92) | Lemma 1.11 | same | **NUMBER-DRIFT** | **Lemma 1.8** |
| 14 | **[FGMN] Cor 1.13** — `KP(µ) ⊂ O[x]` (C.92) | Cor 1.13 | same | **NUMBER-DRIFT** | **Cor 1.10** |
| 15 | **[FGMN] Lemma 5.3(2)** — admissibility/degree forcing (C.92) | Lemma 5.3(2) | same | **NUMBER-DRIFT** | **Lemma 5.2(2)** (clause index preserved; published statement adds the explicit `r > 0`) |
| 16 | **[FGMN] Prop 5.7 + eq (14)** — residual of a key (C.92) | Prop 5.7, eq (14) | same | **NUMBER-DRIFT** | **Prop 5.6 + eq (11)** |
| 17 | **[FGMN] Thm 6.3** — the key certificate (C.92) | Thm 6.3 | same | **NUMBER-DRIFT (number + clause merge)** | **Thm 6.2**; v3's items (1)(2)(3) become (1)(2) — v3's (3) is absorbed into published (2) |
| 18 | **[FGMN] Cor 6.4** — length-`r` one-sidedness (C.92) | Cor 6.4, quoted *"for any `1 ≤ j ≤ r`"* | same | **NUMBER-DRIFT** + quote slip | **Cor 6.3**; the source reads *"for any `1 ≤ **i** ≤ r`"* in **both** versions — the index letter `j` is a repo transcription slip |

Residuals (what no verdict above rests on): the Springer-typeset AGNPRW PDF and the Elsevier-
typeset FGMN PDF were not opened — see §7 for exactly what remains and the two-minute human
checks that would close them.

---

## 2. Per-package verdicts

### 2.1 B.42 = [GN15] Thm 2.3 — **CLEAR TO SIGN on numbering grounds**

The metadata is publisher-confirmed three ways. AMS's own book page for CONM 637 lists the
chapter as `{"Title":"Genetics of polynomials over local fields","Contributors":"Jordi Guàrdia
and Enric Nart","StartPage":207,"EndPage":241,"FileUrl":"/637/12767"}`; Crossref resolves DOI
10.1090/conm/637/12767 to the same volume/pages with book title *Algorithmic Arithmetic,
Geometry, and Coding Theory*; zbMATH records it as Zbl 1396.11143, *J. Algebra*-style source line
`Contemp. Math. 637, 207–241 (2015)`. The AGNPRW published reference list (written by two of the
same authors) cites it identically.

Theorem 2.3 is **VERIFIED verbatim**, and — the point that upgrades this from "author PDF only"
to a genuinely low-risk cite — it is verified in **two independent documents that straddle the
referee round**: the UPCommons author copy (`GeneticsCM.pdf`, compiled 2014-04-29) and
**arXiv:1309.4340v2** (submitted 2014-06-10, comments field: *"revised according to suggestions
by a referee"*). The two agree character-for-character on the theorem's number, hypotheses,
product display and both degree laws, so the number survived the only revision that could have
moved it. The display quoted in the CHAP-I faithfulness entry matches the source, including
`deg g₀ = deg g − ℓ(N⁻_{r+1}(g))·deg φ` and `deg g_{λ,ψ} = e_λ·ord_ψ(R_{r+1,λ}(g))·deg ψ·deg φ`,
and the source's own closing clause (`ord_ψ = 1 ⟹ g_{λ,ψ}` irreducible) is present.

The repo's docs do not know arXiv:1309.4340 exists (`CITE_SCOPE_RESOLUTION` §6.2 says the only
reachable copy is the upcommons author PDF). **Recommendation:** cite the printed chapter and add
arXiv:1309.4340v2 as the freely checkable post-referee witness.

**Two disclosures the signature should carry.** (i) *Not print-read:* the AMS chapter itself is
behind LibLynx; risk graded LOW because the post-referee arXiv version agrees. (ii) *Non-numbering
observation, flagged to the math owner and outside this audit's verdict:* source Thm 2.3 carries
the standing hypothesis **`φ ∈ KP(µ)` with `φ ≁_µ φ_r`**, which CHAP-I's quoted display omits.
At the claimed instantiation (MacLane chain length `r = 0`) this excludes the key `φ ∼ x`. Whether
CHAP-B's `IsKey φ` implies it is a mathematical question, not a citation question — but the quote
should not silently drop a hypothesis of the theorem it quotes.
**[A-3 disposition, 2026-08-16 — ANSWERED, and the answer is NO.]** `IsKey φ ⟺ φ ∈ KP(µ₀)` is
exact and verbatim, but `IsKey` does **not** imply `φ ≁_{µ₀} φ₀ = x`: the excluded class is
`{x + a : a ∈ m}` (nonempty; `φ = x` is the import's commonest instance). The mathematics is
nevertheless sound at COVERS-ALL-O scope, on a second cite the entry did not carry — **[FGMN]
Thm 6.6** (arXiv v3), the intrinsic form of the same theorem, whose `φ`-hypothesis is "**proper**
key polynomial", satisfied by every `φ ∈ KP(µ₀)` ([FGMN] Def 5.10: *"Note that
`KP(µ₀)_str = KP(µ₀)`"*, with `KP_str ⊂ KP_pr`; independently `e₀ = m₀ = 1`). **Signature
consequence: [FGMN] Thm 6.6 must be signed co-primary with [GN15] Thm 2.3.** Full quotes and the
two properness legs: `blueprint/CHAP-I_capstone_conditionality.md`, 2026-08-16 addendum, bullet
"STANDING HYPOTHESIS ON `φ`" (mirrored at CHAP-B NODE B.42). New numbering residual added there:
[FGMN] Thm 6.6 / Def 5.10 print numbers unverified (predicted Thm 6.5 / Def 5.9 by §4's uniform
`−1` drift).

**Secondary display GMN Thm 1.15 — VERIFIED against print.** The AMS serves the complete printed
article free at `ams.org/journals/tran/2012-364-01/S0002-9947-2011-05442-5/`. Printed header:
*"TRANSACTIONS OF THE AMERICAN MATHEMATICAL SOCIETY, Volume 364, Number 1, January 2012, Pages
361–416, S 0002-9947(2011)05442-5, Article electronically published on May 18, 2011."* Printed
**Theorem 1.15 (Theorem of the polygon)** reads: *"Let `f(x) ∈ O[x]` be a monic polynomial
divisible by `φ(x)` modulo `m`. Suppose that `N⁻_φ(f) = S₁ + ⋯ + S_g` has `g` sides with slopes
`−∞ ≤ λ₁ < ⋯ < λ_g`. Then, `f_φ(x)` admits a factorization in `O[x]` into a product of `g` monic
polynomials `f_φ(x) = F₁(x)⋯F_g(x)`, such that, for all `1 ≤ i ≤ g`: (1) `N_φ(F_i)` is one-sided
and equal to `S_i` up to a translation. (2) If `S_i` has finite slope `λ_i`, then
`R_{λ_i}(F_i)(y) ∼ R_{λ_i}(f)(y)`. (3) For any root `θ ∈ Q̄_p` of `F_i(x)`, we have
`v(φ(θ)) = |λ_i|`."* This is exactly the per-slope grouping CHAP-I transcribes; note for the
record that the source factors **`f_φ`** (the `φ`-part), not `f`.

### 2.2 C.94 = [AGNPRW] Thm 5.2 — **NOT CLEAR TO SIGN as written; clear after renumbering to Thm 5.6**

The paper is correctly identified (Alberich-Carramiñana–Guàrdia–Nart–Poteaux–Roé–Weimann,
*Polynomial factorization over henselian fields*) and the cited **statement is exactly right** —
but its **number is wrong for the version of record**, and wrong in the worst way: the number is
occupied by a different theorem.

Chain of evidence. (a) arXiv:2207.02139 has **only v1** (2022-07-05) and carries **no
journal-ref**; the repo's numbers all come from v1 (`CITE_SCOPE_RESOLUTION` §6.1 says so
explicitly). (b) The two open surrogates §6.1 nominates — Weimann's own page and the UPC/IRI
repository — are **not** copies of v1: they are the accepted version (both compiled 2023-12-11),
whose abstract differs from v1's and matches the publisher abstract, which advertises *"a key new
result (Theorem 4.10)"*. (c) Semantic Scholar's publisher-derived abstract for the DOI quotes the
same sentence, so *"Theorem 4.10"* is confirmed from the publisher side, independent of the author
copies. (d) In v1 that same theorem — same hypotheses, same two items, same closing "In
particular" — is **Theorem 4.4**. So v1 → published shifts §4 by +6 and §5 by +4.

The collision. v1 **Thm 5.2** = *"If `v` is discrete of rank-one, then the OM-algorithm
terminates."* In the published version that sentence is **Theorem 5.6**, verbatim, with the same
index-finiteness proof sketch. Published **Theorem 5.2** is instead v1's Theorem 5.1: *"Let
`G ∈ Irr(K^h[x])` be the irreducible factor of `g` singled out by `(µ, φ)`. Then
`e(w_G/v) = e₀⋯e_r`, `f(w_G/v) = f₀⋯f_{r−1}·deg(R_{µ,φ_r}(φ))`."* A reader checking the signed
faithfulness entry against the journal would therefore find a plausible-looking but wrong
theorem — the exact failure the axiom policy's "published-source citation" clause exists to
prevent.

Two further corrections inside this package. (i) The repo's citation *"Found. Comput. Math.
(2024)"* should be **Found. Comput. Math. 25 (2025), no. 2, 631–681** (Crossref: published-print
April 2025; 2024-02-21 is online-first). (ii) The resolution doc's verbatim proof-sketch quote
ends *"…contributing to the total value of `ind(g)` [10, Thm. 4.8]"*; in the published version the
bracket is **[14, Thm. 4.8]** (both = GMN12, TAMS 364). **Source-side imprecision the repo
inherits, disclosed here:** GMN12 has no *Theorem* 4.8 — in both arXiv v2 and the printed TAMS,
**4.8 is a Lemma** ("The following conditions are equivalent"), and the theorem of the index is
**Thm 4.18** (with Cor 4.19). So AGNPRW's own internal reference for the load-bearing index step
does not resolve cleanly against printed GMN. This does not weaken AGNPRW Thm 5.6's *statement*
(published, refereed, at exactly our hypothesis class), but the NS-7 "only PARTIAL" caveat should
say so: the assertion-chain's last link points at a number that is a Lemma in the cited paper.

**After the renumber (5.2 → 5.6) plus the volume/page fix, this cite is clear on numbering
grounds.** Nothing mathematical changes; the imported statement is byte-identical in both
versions.

### 2.3 C.66 + C.92 = the [FGMN] battery — **NOT CLEAR TO SIGN as written; clear after the §4 remap**

The metadata is right (J. Algebra **427** (2015) 30–75; add DOI 10.1016/j.jalgebra.2014.12.022;
zbMATH Zbl 1317.13006). The nine cited **statements** all exist and all match. **Eight of the
nine numbers are wrong for the published version**, and two clause indices move as well.

Chain of evidence. (a) arXiv:1305.0775's last version is **v3 (2013-07-26)**; the repo-local print
(`docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`) is that version, and the article
appeared in J. Algebra in 2015 — arXiv was never updated. (b) A **later** author version exists
and is reachable: the UPCommons record for this article (handle 2117/28203) holds
`ResidualIdealsArxiv.pdf`, **compiled 2013-12-04** — after arXiv v3 — and it renumbers §§1, 3, 4,
5, 6. (c) Two author-side citation echoes decide which numbering the journal carries. Nart, *On
the equivalence of types* (arXiv:1409.4345), whose bibliography already lists the **published**
FGMN (*"Journal of Algebra 427 (2015), 30–75"*), cites **[1, Thm. 5.7]** for the residual-ideal
bijection and **[1, Cor. 5.3]** for the `H_µ(φ)`/`R(φ)` display; in arXiv v3 those are 5.8 and
5.4, in the later version they are exactly **5.7** and **5.3**. Moraes de Oliveira–Nart
(arXiv:1901.04937, **2019 — after publication**) cites **[1, Prop. 3.6]** for optimal-MacLane-chain
uniqueness; arXiv v3 numbers it 3.7, the later version numbers it **3.6**. Three echoes, two
papers, one of them post-publication, all agreeing with the later numbering and none with v3.

Full remap in §4. The two clause-level traps worth naming here, because they survive a naive
"add/subtract one" fix: v3 **Cor 4.4** loses its item (1) in the published version, so the cited
**(4) becomes (3)** of **Cor 4.9**; and v3 **Thm 6.3**'s three items become two in published
**Thm 6.2** (v3's item (3), *"`F ∼_µ φ^ℓ`, so `R(F)` is a power of `R(φ)`"*, is absorbed into
published item (2)). Also: C.92 quotes Cor 6.4 as saying *"for any `1 ≤ j ≤ r`"* — both versions
read *"for any `1 ≤ i ≤ r`"*; the `j` is the repo's, and since the surrounding blueprint text uses
`j` for a different index, the slip is worth fixing before it propagates into a Lean statement.

**One knock-on for the scope argument, not just the numbers.** `CITE_SCOPE_RESOLUTION` NS-12
grounds the C.92 package's COVERS-ALL-O verdict on two loci that **do not exist as numbered items
in the published version**: v3's **Definition 6.1** (the set `P` of monic irreducibles in
`O_v[x]`, "no separability restriction") is **unnumbered running prose** at the head of published
§6, and v3's **Lemma 6.2** — whose proof carries the load-bearing clause *"where `Z(F)` is the
multiset of roots of `F` in `K̄_v`, with due count of multiplicities if `F` is inseparable"* — is
published **Lemma 6.1**. The clause itself survives verbatim (verified). So the scope verdict
stands, but its citation must be re-pinned as "published §6 opening paragraph + proof of Lemma
6.1", not "Def 6.1 + Lemma 6.2".

---

## 3. [AGNPRW] arXiv-v1 → published number map (complete for every number the repo uses)

Published = the accepted version (compiled 2023-12-11), corroborated by the publisher abstract's
"Theorem 4.10". Every statement text is identical across the two versions unless noted.

| Statement | repo cite (arXiv v1) | **published** | what occupies the old number in print |
|---|---|---|---|
| *"If `v` is discrete of rank-one, then the OM-algorithm terminates."* | Thm 5.2 | **Thm 5.6** | **Thm 5.2 = a different theorem** (`e`/`f` of the singled-out factor; v1's Thm 5.1) |
| theorem of the polygon: `∀ G ∈ F_{µ,φ}(g)`, `deg G` a multiple of `deg Q`; `Σ_{G ∈ F(λ)} deg G = ℓ(S_λ(N))·deg Q` | Thm 4.4 | **Thm 4.10** | Definition 4.4 (the `φ`-expansion Newton polygon) |
| `N⁺_{µ,φ}(gh) = N⁺_{µ,φ}(g) + N⁺_{µ,φ}(h)` | Thm 4.6 | **Thm 4.15** | Definition 4.6 (the principal Newton polygon) |
| `R(gh) = R(g)R(h)` | Cor 2.9 | **Cor 2.17** | Theorem 2.9 |
| residually-transcendental key characterisation / degree law | Thm 2.10 | **Thm 2.18** | *Problem* 2.10 |
| `π = in_µ φ` for a minimal-degree key; homogeneous elements | Thm 2.7 | **Thm 2.14** | Definition 2.7 |
| `n_i = 1 ⟹ (µ_λ, ϕ_i)` singles out an irreducible factor | Prop 4.5 | **Prop 4.14** | Definition 4.5 |
| Henselian `Q ∈ KP(ν)` polygon statement | Thm 4.7 | **Thm 4.16** | Lemma 4.7 |
| Henselian `ν`, `Q ∈ KP(ν)`, `g` | Thm 4.8 | **Thm 4.17** | Lemma 4.8 |
| `e`/`f` of the factor singled out by `(µ, φ)` | Thm 5.1 | **Thm 5.2** | — |

Consumers to update: `blueprint/CHAP-C_tower_grammar.md` (node C.94 and the §-headers listing it),
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` (NS-1, NS-7, NS-9, §3 F-2, §4's audit-row map, §5, §6.1),
`blueprint/CHAP-I_capstone_conditionality.md` (the B.42 entry's "Secondary displays" line).

## 4. [FGMN] arXiv-v3 → published number map

| Statement | repo cite (arXiv v3) | **published** |
|---|---|---|
| `N⁻_{µ,φ}(gh) = N⁻_{µ,φ}(g) + N⁻_{µ,φ}(h)` | Thm 2.8 | **Thm 2.8** (unchanged) |
| `R` additivity / multiplicativity, three items | Cor 4.7(1),(3) | **Cor 4.12(1),(3)** |
| `deg R_i(g) = (s′−s)/e_i`, `R_i(g)(0) ≠ 0` | Cor 4.4(4) | **Cor 4.9(3)** |
| every `φ ∈ KP(µ)` is irreducible in `K_v[x]` | Lemma 1.11 | **Lemma 1.8** |
| `KP(µ) ⊂ O[x]` | Cor 1.13 | **Cor 1.10** |
| key-polynomial criterion, branch (2) | Lemma 5.3(2) | **Lemma 5.2(2)** |
| the five equivalences for `φ, φ′ ∈ KP(µ)` | Prop 5.7 | **Prop 5.6** |
| the equation cited in those proofs | eq (14) | **eq (11)** |
| prime-polynomial certificate `φ \|_µ F ⟺ v(φ(θ)) > µ(φ)` | Thm 6.3 (items 1,2,3) | **Thm 6.2** (items 1,2 — v3's (3) merged into (2)) |
| level-general one-sidedness, `F ∼ φ_i^{ℓ_i}`, `R_{i−1}(F) = ψ_{i−1}^{ℓ_i}` | Cor 6.4 | **Cor 6.3** (eq (23) keeps its number) |
| *(NS-12 extras, same drift class)* `Prop 1.12` · `Thm 3.11` · `Cor 5.4` · `Thm 5.8` | — | **Prop 1.9** · **Thm 3.10** · **Cor 5.3** · **Thm 5.7** |
| *(NS-12 scope pins)* `Def 6.1` (the set `P`) · `Lemma 6.2` + its inseparability clause | — | **unnumbered §6 opening paragraph** · **Lemma 6.1** (clause verbatim intact) |

Consumers to update: `blueprint/CHAP-C_tower_grammar.md` (nodes C.66, C.92),
`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` (NS-9, NS-10, NS-12), `blueprint/CHAP-I_capstone_conditionality.md`
(B.42 entry's secondary displays), and whichever GENTOW2/GENTOW5 records pin `[Q1]`–`[Q10]`
(`docs/CITE_SCOPE_RESOLUTION` NS-12 names them).

## 5. GMN — the printed-TAMS caveat, discharged

`docs/GMN_citations.md` carried an honest caveat that its numbers came from arXiv:0807.2620v2 and
that *"the printed-pagination numbers should be confirmed against the TAMS 364 (2012) PDF before
final submission."* **Confirmed, in full.** The printed article was read this session (free AMS
PDF). Every number the doc lists exists in print, with the claimed kind and content:

- **Theorems** 1.15 (theorem of the polygon), 1.19 (theorem of the residual polynomial), 2.11
  (representative of a type), 3.1 (polygon in order `r`), 3.7 (residual polynomial in order `r`),
  4.18 (theorem of the index) — all ✓.
- **Definitions** 1.21, 1.22, 2.1, 2.3, 2.5, 2.21, 3.9, 3.10 — all ✓ (printed Def 2.21 is the
  block that defines the virtual factor **and** the order-`r` residual polynomial
  `R_{λ_r}(f)(y) := c_s + c_{s+e_r}y + ⋯`, so the doc's "the residual polynomial of order `r` is
  Definition 2.21" is right).
- **Corollaries** 1.20, 3.3, 3.8, 4.19 ✓ · **Lemma** 3.11 ✓.
- Spot-check of arXiv v2 against print: numbering identical everywhere checked (1.15, 2.20, 2.21,
  2.26, 4.8, 4.18). **GMN is the one source in this audit with no arXiv-vs-print drift.**

**One correction owed to the same doc.** `GMN_citations.md` asserts *"there is **no Theorem 2.26**
in this paper"*. That is **false**: both printed TAMS and arXiv v2 contain **Theorem 2.26 (Theorem
of the product in order `r`)**: *"For any nonzero `f(x), g(x) ∈ O[x]` and any negative rational
number `λ_r` we have `N⁻_r(fg) = N⁻_r(f) + N⁻_r(g)`, `R_{λ_r}(fg)(y) = R_{λ_r}(f)(y)R_{λ_r}(g)(y)`."*
The doc's substantive point survives intact — the order-`r` *theorems of the polygon and of the
residual polynomial* are 3.1 and 3.7, not 2.26, so the old `notes/BB3_infinity.md` /
`notes/COMPLETE_PROOF.md` citation was still mis-aimed — but the parenthetical claim that the
number does not exist must go, and any future reader chasing "Thm 2.26" will land on a real
theorem (product, order `r`) that the corpus does in fact use elsewhere. *(Minor, same doc: the
parenthetical calls Def 2.19 "the truncation"; printed 2.19 defines the initial abscissas `s_j(P)`
and the integer `t_{r−1}(i)`.)*

## 6. Incidental citation-integrity findings (outside the three triples)

1. **[GMN11-IB] is published.** `CITE_SCOPE_RESOLUTION` §1 records *"journal version UNVERIFIED —
   [FGMN] and [GN15] both cite it as arXiv-only"*. It appeared as Guàrdia–Montes–Nart, *Higher
   Newton polygons and integral bases*, **J. Number Theory 147 (2015) 549–589**, DOI
   10.1016/j.jnt.2014.07.027 (Crossref; and cited in that form by arXiv:1409.4345's bibliography).
2. **GN15 has an arXiv version** — arXiv:1309.4340, **v2 = post-referee**. `CITE_SCOPE_RESOLUTION`
   §6.2's "author PDF only" premise is superseded.
3. **AGNPRW's own internal cite `[GMN12, Thm. 4.8]`** does not resolve in GMN12 (4.8 is a Lemma
   there; the index theorem is 4.18) — see §2.2.
4. The AGNPRW published reference list renders the GN15 book title as *"Arithmetic, geometry, and
   coding theory"*; AMS/Crossref/zbMATH give ***Algorithmic** Arithmetic, Geometry, and Coding
   Theory*.

## 7. What I could NOT reach (and the cheapest way to close each)

1. **Springer-typeset [AGNPRW].** `link.springer.com` 303s to an auth endpoint; the article is not
   OA. The published numbering therefore rests on the two co-author-hosted accepted-version copies
   plus the publisher abstract's own "Theorem 4.10" (via Semantic Scholar). **Residual risk: LOW**
   for 4.10 (publisher-side quote) and 5.6 (same document, same renumbering). *Closing check (≈2
   min, human browser with institutional access): confirm §5's theorem list runs 5.1, 5.2, Prop
   5.4, Def 5.5, 5.6 and that 5.6 is the termination theorem.*
2. **Elsevier-typeset [FGMN].** OpenAlex/Unpaywall mark the article **bronze OA** at
   `sciencedirect.com/science/article/pii/S0021869314007212/pdf`, but ScienceDirect returns 403 to
   automated fetches. The published numbering rests on the later author version (2013-12-04) plus
   three author-side citation echoes, one post-publication. **Residual risk: LOW-MEDIUM** — the
   direction of the shift is certain, but I cannot exclude a *further* renumbering between
   2013-12-04 and acceptance (2014-12). *Closing check (≈2 min, human browser — bronze OA means
   free to a person): open that PDF and confirm three numbers — Thm 2.8 (`N⁻` additivity),
   Cor 4.12 (R additivity/multiplicativity), Thm 6.2 (`φ |_µ F ⟺ v(φ(θ)) > µ(φ)`).*
3. **Printed AMS chapter for [GN15].** LibLynx paywall. Closed to LOW risk by arXiv:1309.4340v2
   (post-referee) agreeing with the author copy on Thm 2.3.
4. **Not audited (out of charge):** every non-numbering claim — scope arguments, the
   dictionary/shear transport, and whether the imported hypotheses match the Lean statements. The
   one hypothesis omission I noticed in passing is recorded in §2.1(ii).

## 8. Evidence ledger

Fetched 2026-08-16 into `/tmp/a3audit/` (not committed; all re-fetchable from the URLs).

| Document | Source URL | Internal compile date | sha256 (16) |
|---|---|---|---|
| AGNPRW accepted version (Weimann) | `weimann.users.lmno.cnrs.fr/HenselianFactorization.pdf` | 2023-12-11 | `9fcedcedce2cfd7d` |
| AGNPRW accepted version (UPC/IRI) | `iri.upc.edu/files/scidoc/2965-Polynomial-factorization-over-Henselian-fields.pdf` | 2023-12-11 | `ba74f3308a67e703` |
| AGNPRW arXiv v1 | `arxiv.org/pdf/2207.02139v1` | 2022-07-05 (submission) | `85f7c654ed0772c6` |
| GN15 author copy | UPCommons item 2117/28206, `GeneticsCM.pdf` | 2014-04-29 | `7df69fbb63de3be8` |
| GN15 arXiv v2 (post-referee) | `arxiv.org/pdf/1309.4340v2` | v2 submitted 2014-06-10 | `8490076d5d0f334e` |
| FGMN later author version | UPCommons item 2117/28203, `ResidualIdealsArxiv.pdf` | 2013-12-04 | `33b849ce6784f4ba` |
| FGMN arXiv v3 | repo-local `docs/references/fgmn_residual_ideals_1305.0775v3*` | v3 submitted 2013-07-26 | (repo file) |
| **GMN printed TAMS** | `ams.org/journals/tran/2012-364-01/S0002-9947-2011-05442-5/S0002-9947-2011-05442-5.pdf` | 2011-09-14 (AMS typeset) | `4e6c66755289f57c` |
| GMN arXiv v2 | `arxiv.org/pdf/0807.2620v2` | v2 submitted 2008-10-31 | `62b8f28d1839dbaa` |
| Echo: Nart, *On the equivalence of types* | `arxiv.org/pdf/1409.4345` | — | — |
| Echo: Moraes de Oliveira–Nart (2019) | `arxiv.org/pdf/1901.04937` | — | — |

Publisher metadata APIs used: Crossref (`api.crossref.org/works/{DOI}`) for AGNPRW, GN15, GMN;
AMS book page JSON (`ams.org/conm/637/`) for the CONM 637 table of contents; zbMATH Open
(`api.zbmath.org`) for GN15 (Zbl 1396.11143) and FGMN (Zbl 1317.13006); OpenAlex and Unpaywall for
FGMN's OA locations; Semantic Scholar Graph API for the AGNPRW publisher abstract.

<!-- SENTINEL: A-3 AUDIT END OF FILE -->
