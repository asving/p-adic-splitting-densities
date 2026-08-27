# THE DV-GRADED ONE-SLOPE HENSEL ENGINE — existence, uniqueness, maximality (MHENS, 2026-08-26)

**Author: unit MHENS (Fable, math-first).  [MHDISP 2026-08-27] STATUS AMENDED: design
document with a genuine critical defect in M1(2) and load-bearing justification gaps; the
engine is NOT proved and the MH transcription fleet is fenced.  Nothing in this document is
signed or landed.  This document proposes the C.34/C.35 root mechanism** (BLOCKED item 1 of
`runs/wave-b/verdict_DEC4R.md:71-78`), planned as nodes
F1.H0–F1.H3 of `docs/in-progress/BLOCKERS_PLAN_2026-08-26.md:60-66`.

## [MHDISP 2026-08-27] Dated disposition addendum

This document was written **before** amendment A-C.20 landed in commit `b59e2dd5` on
2026-08-26.  The amendment was enacted from this document's own degree-leak finding.  The
following historical/current mapping is binding everywhere below:

* the §7 degree-3 example refutes only the **pre-A-C.20 unpinned** C.34 separation shape and
  C.35 selector; it does **not** satisfy the current degree-pinned competitor hypotheses;
* current C.34 pins both block witnesses and every separation competitor by
  `HasLabel L fS ∧ (F.e₁ * F.f₁) ∣ fS.natDegree`;
* current C.35 `blockFactor` and `BlockFrontier` use that same pin.  The historical selector
  and multiplicity are preserved explicitly as `blockFactorLeaky` and `mult₂Leaky`, and the
  §7 refutation is a record about those names only.  The post-amendment `blockFactor_spec`
  packaging is **not refuted**;
* the proposed `BlockFrontier′` below is now, in substance, the landed `BlockFrontier`; it is
  no longer a pending statement repair.

The adversarial review also found a live critical defect independent of A-C.20: M1(2)'s
bare-`slotRes` multiplication law omits the carry factor caused by the slot window.  At the
landed `(e₁,f₁,h)=(2,2,3)` gate numerals, `a=b=X` gives bare reads `1`, `1`, and `η` at
heights `3`, `3`, and `6`, with `η ≠ 1`; the inverse-twist normalization cancels this carry.
The executable zero-`sorry`, zero-`axiom` mirror is
`leanfinal/scratch/MHDISP_probe.lean`.  Thus M1 as stated is false, its proof does not prove
Theorem M, and every MH node depending on M is **BLOCKED pending a correctly stated and
proved generic twist-read product law**.  The numerical certificate in §10 cannot replace
that universal proof.

**Three headline verdicts, up front.**

1. **[MHDISP 2026-08-27] The engine is designed but its mathematics is NOT proved below.**
   M1(2) is false as stated, and OPEN-1, OPEN-3, OPEN-4, plus the limit conversion are
   load-bearing for the engine/`blockFrontier_of_context` route (though the already-landed
   conditional C.35 `_of_frontier` wrappers remain valid).
   The root object is NOT a rewriting system and NOT a new weight: it is the landed
   `dvSupp`/`dvResPoly` calculus upgraded from the C130nv2 support half to a **general
   mixed residual product law** (§3), from which existence is B.41's Newton pattern and
   — better than planned — **uniqueness and maximality need NO Newton iteration at all**
   (§5–§6: a degree pigeonhole and a prime-placement argument).
2. **Honest reskin verdict** (the brief's direct question): mathlib has NO
   coprime-factorization Hensel (its `HenselianLocalRing` is simple-root lifting only,
   `Mathlib/RingTheory/Henselian.lean`); the repo's `Uniformity/HenselFactorization.lean`
   and B.39–B.41 are residue-field- resp. `IsKey`-fenced and `IsKey F.key` is FALSE at
   `F.h ≥ 1`.  The engine's *architecture* (solve → iterate → limit → perturb) is
   B.39b/B.40/B.41b's, reskinned; its *ingredients* (the stage-field read calculus, the
   mixed product law, the defect analysis) are genuinely new corpus mathematics — with
   one big exception: the LIMIT leg reuses landed monic-fenced machinery almost verbatim
   (§4.4).
3. **[MHDISP 2026-08-27] HISTORICAL STATEMENT-DEFECT RECORD.**  The §7 example refutes
   the pre-A-C.20 unpinned C.34/C.35 shapes.  A-C.20 has since pinned every load-bearing
   label; the current signed shapes are not refuted.  C.35 retains the historical objects as
   `blockFactorLeaky`/`mult₂Leaky` for this record.

Throughout: `D′ := F.e₁ * F.f₁`, `K := F.stageField H₀ hpin` ([MHDISP 2026-08-27]
the required `Field K` is reconstructible locally from `instFieldResField`, `F.hresirr`, and
`AdjoinRoot.instField`; C.04's `fieldStageField` is private and there is no exported global
instance),
`W(p) := dvSupp F p u ℓ ∈ ℕ∞` (the ℓ-cleared level weight, C.06),
`R(p) := dvResPoly F H₀ hpin p u ℓ hne M₀ hp ∈ K[Z]` (C.25, at the `dvSideMin` pin).
"Pure" always means `IsDvPure F p u ℓ` (C.29: abscissae `0` and `⌊deg p/D′⌋` both on the
side).  "Far" means the `(u,ℓ)`-side of `p` is a single point (`dvSideDeg = 0`).

---

## §1 The setting, and what is already landed

Fixed for the whole document: a frame `F : KeyFrame O π` (C.01) with `0 < F.h` (the
degenerate `h = 0` frame has `stageHeight = gaussVal`, `dvSupp = suppVal`, and its engine
IS the landed order-1 B.39–B.41 chain — nothing below is needed there); the GC-1 pin
`H₀, hpin`; an admissible direction `(u, ℓ)`: `0 < ℓ`, `Nat.Coprime u ℓ`, and the strict
floor `ℓ * (D′ * F.h) < u` (= `LevelDatum.hκ` up to associativity).  A residual label
`r : Polynomial K`, monic irreducible, `r.coeff 0 ≠ 0`, `0 < r.natDegree` (= the
`LevelDatum` fences, C.09).

### 1.1 The landed inventory the engine stands on (all Lean-core unless marked)

| fact | where | note |
|---|---|---|
| `stageHeight` is **multiplicative**: `dv(AB) = dv(A) + dv(B)` | `C130nv2.lean:203` (`stageHeight_mul`, via `suppVal_mul_univ` at `isKey_X` — `X` IS a key, so the order-1 `IsKey` chain fires at level 1) | unfenced (any `A B`, `0 < F.h`) |
| `W` superadditive: `W(g) + W(z) ≤ W(gz)` | `C130nv2.lean:645` (`dvSupp_add_le_dvSupp_mul`) | needs `hV : dv(key) = V`, `ℓV ≤ u` |
| `W(gz) = W(g) + W(z)` **given endpoint survival** `hup` | `C130nv2.lean:784` (`dvSupp_mul_eq_add_of_endpoint_le`) + `dvOnSide_mul_endpoint`, `dvSideMin_mul_le` | [MHDISP 2026-08-27] `hup` remains a missing generic ingredient; the original §3.1 discharge uses the false M1(2)/an unproved corrected carry law |
| [MHDISP 2026-08-27] generic endpoint pricing **given survival** | `C130nv3.stageHeight_dev_endpoint_le_of_surv` | requires both strict `ℓ * V < u` and an explicit `hsurv`; neither weak admissibility nor the theorem itself supplies generic survival |
| [MHDISP 2026-08-27] S2 composed-key survival bound | `C132nv3.s2_dvSupp_mul_modByComposedKey_le` | now LANDED at the S2 frame for degree `< 4`; it does **not** instantiate the arbitrary-frame MH engine and therefore does not close generic M1/MH.1 |
| convolution pricing of every double-development slot | `C130nv2.lean:500,545` (`le_line_dev_term`, `lt_line_dev_term`) | carries included |
| division calculus at the stage height | `C130nv2.lean:346-361` (`stageHeight_le_modByMonic`/`divByMonic`/`eq_min_mod_div`) | |
| ultrametric sum laws + strict stability | `C131y.lean:96-105,220` (`stageHeight_add_eq_left_of_lt`, `dvHgt_add_eq_left_of_lt`, `dvHgt_add_min`); `C131ae.lean:164-183` | the perturbation atoms |
| order-1 residual product law, **general** (no purity fence) | `B39a.lean:883` (`resPoly_mul_gen`), `B43.lean:235` | fires at `φ = X` — the level-1 in-form calculus is DONE |
| residual degree + nonzero constant term | C.26 (`natDegree_dvResPoly`) | `deg R = dvSideDeg`, `R(0) ≠ 0` |
| pure-side endpoint calculus | `C35.lean:174-199` (`dvSideMin_eq_zero_of_isDvPure`, `dvSideMax_eq_of_isDvPure`, `natDegree_div_eq_of_isDvPure`) | |
| side abscissae are genuine digit indices | `C35.lean:159` (`le_natDegree_div_of_mem_dvSideSet`) | the cap that drives the defect analysis (§6) |
| nonzero ⟹ nonempty side, finite heights | `C34.lean:115,133` (`stageHeight_ne_top`, `dvSideSet_nonempty`) | |
| `hdvd` fence, constant-complement law, single-class supply | `C34.lean:187-268` | the `R = r^m` case is DONE (`block_pair_self_of_dvResPoly_eq_pow`) |
| graded adic limit at order 1, **Monic-fenced only** | `B40.lean:203` (`exists_graded_limit`) — NO `IsKey` | the limit pattern transfers (§4.4) |
| generic bounded-degree adic limit | `HenselFactorization.lean:306` (`exists_adicLimit_of_degree_lt`) | filtration-agnostic |
| [MHDISP 2026-08-27] stage lift with exact height + prescribed read | public `KeyFrame.natDegree_stageLiftO_lt`, `slotRes_stageLiftO`, `stageHeight_stageLiftO` in C131f; public `KeyFrame.exists_twistRead_preimage` in C.14 | the helpers at C46:217–230 and C47:401–405 cited by the original text are private; use the public promoted API.  Exact `twistRead`, not bare `slotRes`, is the initialization's required supply |
| the C.33 dissection cites (slope factor, `D′`-divisible degree, factor equality) | `C33Cite.lean:76,85` (`exists_dvDissection`, `fgmn_dvDissection_factor_eq`) — cite axioms, allowlisted | consumed only by F1.H3 (§8) |
| [MHDISP 2026-08-27] B.40 valuation comparison helper | `B40.lean:121`, `inf_npHgt_le_gaussVal` | private, hence not a consumable API; moreover it does not justify the original direction of the `W`→Gauss conversion.  MH.8 needs a new public bounded-window comparison with the finite `F.h * j` loss controlled |
| exact purity closure + residual multiplicativity, **pure×pure with `D′ ∣ deg` fences** | `C66b.lean:90` (`fgmn_dv_exact_mul`) — declared cite | certifies products of existing factors; constructs nothing |

### 1.2 The two-level dictionary (why the engine is "graded")

`W/ℓ` is the MacLane augmented valuation `v₂` of the pair (level-1 valuation `v₁ = dv/e₁`
carried by `stageHeight`, key `Φ′ = F.key`, slope `u/ℓ`), cleared to `ℕ`.  The graded
pieces of the `W`-filtration on a degree window `{p : deg p < n}` are finite-dimensional
`K`-spaces, coordinatized by the twist reads: for weight `c`, the slots are the abscissae
`j ≤ (n-1)/D′` with `c − u·j ∈ ℓ·ℕ`, and the slot read is
`twistRead ((c − u·j)/ℓ) (dev F.key p j)` (C.22: `stageLetter⁻¹ ^ twistExp k * slotRes k A`).
`dvResPoly` (C.25) is exactly the weight-`W(p)` read tuple written as a polynomial in
`Z`.  Two facts make this a *graded ring* story and not just a filtration story:

* **level-1 in-forms multiply** — `stageHeight_mul` + `resPoly_mul_gen` at `isKey_X`
  (landed); and
* **the frame residual `ψ` is irreducible of degree `f₁`** (`F.hresirr`) while every
  digit (degree `< D′ = e₁f₁`) has level-1 side degree `≤ (D′−1)/e₁ < f₁` — so `ψ` can
  never divide a product of two digit residuals.  This is the FGMN no-cancellation
  argument (`C130nv3.lean` header names it), and it is what §3.1 turns into the generic
  survival theorem.

---

## §2 THE ENGINE THEOREMS (stated before any proof, per the charge)

The engine is four theorems.  A (existence) consumes completeness; B (uniqueness),
C (maximality/placement), and the product law M they both stand on are **completeness-free**.

### Theorem M (the mixed residual product law — the root)

**Hypotheses.** `hπ : Irreducible π`; frame `F` with `hh : 0 < F.h`; pin `(H₀, hpin)`;
direction `(u, ℓ)` with `hℓ : 0 < ℓ`, `hcop : Nat.Coprime u ℓ`, and admissibility
**[MHDISP 2026-08-27: corrected]** `ℓ * (D′ * F.h) < u`; `g z : Polynomial O`
**nonzero** (no monicity, no purity, no degree fence).  The original weak `≤` statement is
not proved by C130nv3: both `stageHeight_dev_endpoint_le_of_surv` and the strict pricing step
used below require `<`.  All intended engine consumers already carry the strict floor.

**Conclusion.**  With `hne_g, hne_z, hne_gz` the (automatic, `dvSideSet_nonempty`-style
for nonzero inputs — for non-monic inputs nonzero-ness still gives a nonzero digit, see
§3.4) side witnesses and `M₀(·)` the `dvSideMin`-pins:

1. `W(g·z) = W(g) + W(z)`  (in particular `W` is (the clearing of) a valuation);
2. `dvSideMin(gz) = dvSideMin(g) + dvSideMin(z)` and
   `dvSideMax(gz) = dvSideMax(g) + dvSideMax(z)`; hence
   `dvSideDeg(gz) = dvSideDeg(g) + dvSideDeg(z)`;
3. `R(gz) = τ · R(g) · R(z)` in `K[Z]`, where `τ ∈ K^×` is the **explicit twist
   cocycle unit** `τ = stageLetter^(twistExp-defect at the three pins) ·
   (slotRes composition unit)` — a unit depending only on the three height pins and the
   frame, NOT on `g, z` beyond their pins.  Under the pin-compatible normalization at
   which the owner adjudicated `fgmn_dv_exact_mul` (C66b's dictionary: "the twist is a
   fixed unit rescaling per slot, under which multiplicativity is preserved slotwise"),
   `τ = 1` on that cite's fence; the engine only ever needs `τ ∈ K^×` explicit.

This is FGMN Thm 2.8 + Cor 4.12(3) at the corpus carrier, in full mixed generality —
strictly MORE than the declared cite (which demands both factors pure with `D′ ∣ deg`).
**[MHDISP 2026-08-27] §3 does not prove this theorem:** its proposed no-cancellation lemma
contains the false M1(2).  A corrected generic twist-read product theorem may recover the
target, but that theorem is presently OPEN-CRITICAL.  Only after it is proved could M make
the cite's content a theorem; see §9.2.

### Theorem A (existence — the dv-graded one-slope Hensel lift; the F1.H1 core)

**Hypotheses.**  The §1 pack (frame, strict floor, label fences on `r` — though A is
stated for a general coprime pair, mirroring B.41); `[IsAdicComplete (maximalIdeal O) O]`;
`g : Polynomial O` with

* `hg : g.Monic`, `hgpos : 0 < g.natDegree`,
* `hpure : IsDvPure F g u ℓ`,
* **`hfd : D′ ∣ g.natDegree` (the rider — NECESSARY, see §6/§7; supplied by the C.33
  dissection at the only consumer)**,
* side data `hne`, pin `hp : dvHgt F g (dvSideMin …) = (M₀ : ℕ∞)`,
* `{G H : Polynomial K}` with `hG : G.Monic`, `hH : H.Monic`, `hGH : IsCoprime G H`,
  `hG0 : G.coeff 0 ≠ 0`, `hH0 : H.coeff 0 ≠ 0`, and
* `hprod : R(g) = G * H`  (no unit: §3.5 proves `R` of a monic pure `D′ ∣ deg`
  polynomial is itself MONIC, so the unit of any coprime factorization normalizes to 1
  exactly as in B.41's `hcu1` step).

**Conclusion.**  There exist `g₁ g₂ : Polynomial O` with

1. `g = g₁ * g₂`, `g₁.Monic`, `g₂.Monic`;
2. `g₁.natDegree = ℓ * D′ * G.natDegree` and `g₂.natDegree = ℓ * D′ * H.natDegree`
   (in particular both `D′`-riders);
3. `IsDvPure F g₁ u ℓ` and `IsDvPure F g₂ u ℓ`;
4. the left-height pins: `dvHgt F g₁ 0 = (u * G.natDegree : ℕ∞)`,
   `dvHgt F g₂ 0 = (u * H.natDegree : ℕ∞)`;
5. the **exact residual identities** `R(g₁) = G` and `R(g₂) = H` (B.41b's strengthened
   form — without which the C.35 chain has nothing to recurse/read on).

Specializing `G := r ^ m`, `H := s` where `R(g) = r^m * s` with `r ∤ s`, `m ≥ 1`
(Theorem H0 below) gives FRONTIER 1's labelled pair: `HasLabel L g₁` (clauses read off
1–5) and the complement clause for `g₂` (its residual is `s`, and `r ∤ s`; any OTHER pin
witness reads the same residual by proof irrelevance of the pin — C.25's junk-total
design).

### Theorem H0 (residual Bézout — F1.H0 verbatim)

`K` a field, `R : Polynomial K` with `R ≠ 0`, `R.coeff 0 ≠ 0`; `r` monic irreducible with
`r.coeff 0 ≠ 0`, `0 < r.natDegree`; `hdvd : r ∣ R`.  Then there are unique `m : ℕ` and
`s : Polynomial K` with `R = r ^ m * s`, `¬ r ∣ s`, `0 < m`, `s.coeff 0 ≠ 0`,
`IsCoprime (r ^ m) s`, and (for the monic-normalized form used by Theorem A)
`R.Monic → (r ^ m).Monic ∧ s.Monic`.  — UFD/field arithmetic in `K[Z]`; the plan's
35–60-line sizing stands; no frame content.

### Theorem B (uniqueness — F1.H2, completeness-free, Newton-free)

Same §1 pack, **no completeness**.  `g` monic pure with `D′ ∣ deg g`.  Suppose
`g = a * b = a' * b'` with: `a, a'` monic, pure, with exact residuals
`R(a) = r ^ m`, `R(a') = r ^ m'` (`m, m' ≥ 1`); `b, b'` monic with residuals
NOT divisible by `r` (their `∀`-pin forms, as in the signed clause).  Then
`a' = a` and `b' = b`.

Note what is NOT assumed: purity of `b, b'`, degrees of `a', b'`, any relation between
`m` and `m'`.  All of that is DERIVED (§5) — the mixed law M forces `m' = m`, the defect
analysis (§6.1) forces `D′ ∣ deg a'`, and a degree pigeonhole on `a' − a` finishes.

### Theorem C (placement/maximality — the BlockFrontier clause, DEGREE-PINNED)

Same §1 pack, no completeness.  Write `HasLabel′ L fS'` for
`HasLabel L fS' ∧ D′ ∣ fS'.natDegree` (**the degree-pinned label — the pin is NOT
optional: §7 constructs a `HasLabel` (unpinned) divisor that escapes every maximality
statement, refuting the unpinned form**).  Hypotheses: `f : Polynomial O` monic,
**`Squarefree f`**, `f = P * Q * W` with `P` monic pure, `D′ ∣ deg P`, exact residual
`R(P) = r ^ m` (`m ≥ 1`); `Q` monic pure, `D′ ∣ deg Q`, `R(Q) = s` with `r ∤ s`; `W`
monic whose `(u,ℓ)`-side is a **point** (`dvSideDeg = 0`).  Then every
`fS' : Polynomial O` with `HasLabel′ L fS'` and `fS' ∣ f` satisfies `fS' ∣ P`.

Squarefreeness is genuinely consumed (prime-by-prime placement, §6.2) and genuinely
available (`BlockContext` carries it, `C35.lean:126`).

### The assembled corollaries

* **FRONTIER 1** (`C34_BLOCKED` hex) on the `D′ ∣ deg g` stratum: Theorem H0 + A.
* **FRONTIER 2** (`hsep`) on the `D′ ∣ deg g` stratum: Theorem B.  [MHDISP 2026-08-27]
  The §7 refutation applies only to the historical unpinned `hsep`; A-C.20's current `hsep`
  competitors are pinned and are not refuted.
* **[MHDISP 2026-08-27] Current `BlockFrontier L f` from `BlockContext L f`** (F1.H3):
  the degree-pinned `BlockFrontier′` proposed here became the landed `BlockFrontier` in
  A-C.20.  The §7 example targets only the historical unpinned selector now named
  `blockFactorLeaky`; it does not refute current `BlockFrontier` or current
  `blockFactor_spec_of_frontier`.  The proof-from-context route remains BLOCKED for the
  independent engine gaps below.

---

## §3 Proof of Theorem M (the mixed residual product law)

The proof has one genuinely new lemma (M1, the slot no-cancellation), one small new
stability lemma (M1a), and is otherwise assembly of the landed C130nv2 bank.

### 3.1 M1 — the slot product law (SURV-CORE; the engine's one new atom)

**Lemma M1.**  `hπ`, frame `F`, `hh : 0 < F.h`.  For nonzero `a b : Polynomial O` with
`a.natDegree < D′`, `b.natDegree < D′`:

1. (height form)  `F.stageHeight ((a*b) %ₘ F.key) = F.stageHeight a + F.stageHeight b`;
2. **[MHDISP 2026-08-27: WITHDRAWN — FALSE]** the original read form asserted, for the
   finite heights `ka, kb`,
   `slotRes (ka+kb) ((a*b) %ₘ F.key) = slotRes ka a * slotRes kb b` in `K`.
   It omits the slot-index carry.  At `(e₁,f₁,h)=(2,2,3)`, `a=b=X`, the left side is
   `η` and the right side is `1`.  The replacement target must include the carry explicitly,
   or, preferably, be stated directly for `twistRead`; the gate computation shows that the
   inverse twist cancels the carry.  No generic replacement theorem is proved here.

*Proof.*  Write `ab = Q * F.key + E` with `E = (ab) %ₘ F.key`, `Q = (ab) /ₘ F.key`;
`deg E < D′` and `deg Q < D′` (since `deg ab < 2D′ − 1`).  All level-1 objects below are
the ORDER-1 landed calculus at the key `φ = X` (which IS a key — `isKey_X` — so the
`IsKey`-fenced B-chain fires): `dv := F.stageHeight` is `suppVal`-at-`X` weighted by
`(h, e₁)` up to the landed dictionary (`stageHeight_eq_inf`, C.02), and
`R₁(·) := resPoly π X · F.h F.e₁ …` the level-1 residual with values in
`resField X`, whose quotient by the irreducible `ψ := F.frameRes H₀ hpin`
(`F.hresirr`) IS the stage field `K` (C.03).

(a) `dv(ab) = dv(a) + dv(b)` — landed (`stageHeight_mul`, `C130nv2.lean:203`).

(b) *The ψ-degree bound.*  Any nonzero `c` with `deg c < D′` has level-1 side degree
`≤ (D′ − 1)/e₁ < f₁ = deg ψ`, so `deg R₁(c) < deg ψ` and in particular `ψ ∤ R₁(c)`
(the order-1 `natDegree_resPoly` gives `deg R₁ = sideDeg` and `R₁(0) ≠ 0`).

(c) *Height form.*  Both `dv(E) ≥ dv(ab)` and `dv(Q·key) ≥ dv(ab)` (the landed division
calculus `stageHeight_le_modByMonic` / `stageHeight_le_divByMonic`,
`C130nv2.lean:346-361`).  Suppose `dv(E) > dv(ab) = ka + kb`.  Then
`R₁(ab) = R₁(Q·key)` at the matching pins, by **M1a** (order-1 residual stability:
`R₁(x + y) = R₁(x)` at `x`'s pins when the perturbation `y` sits strictly above `x`'s
side line slotwise; proof from `resMk_add` + `resMk_eq_zero_of_lt` (B39b) plus side-set
equality — ~40–70 lines, no new mathematics; the order-1 twin of the landed
`twistRead_add_eq_left_of_lt`, `C131ae.lean:295`).  By the landed GENERAL order-1
product law (`resPoly_mul_gen`, `B39a.lean:883`):
`R₁(ab) = R₁(a) · R₁(b)` and `R₁(Q·key) = R₁(Q) · R₁(key)` (pins add;
`R₁(key) = ψ` up to the landed monic normalization — `F.hresirr` + C.03's `frameRes`).
Hence `ψ ∣ R₁(a) · R₁(b)`.  `ψ` is irreducible over the field `resField X`, so
`ψ ∣ R₁(a)` or `ψ ∣ R₁(b)` — contradicting (b).  So `dv(E) = ka + kb` exactly.  ∎(1)

(d) **[MHDISP 2026-08-27: invalid proof step.]**  Reduction modulo `ψ` does kill the
`Q·key` residual term, but it does not identify the two **bare** `slotRes` normalizations
without a unit.  Multiplying live slots changes `slotIdx`/`slotWindow`, producing a power of
the stage letter.  The assertion that the `ϖ` bookkeeping is exact silently drops that
carry.  The corrected proof obligation is a generic formula for this carry followed by a
proof that C.22's `η^{-twistExp}` normalization cancels it.  The executable gate row in
`scratch/MHDISP_probe.lean` proves the failure of the bare equality and cancellation in the
`F₉` numeral model; it is not a proof of the required arbitrary-frame theorem.  ∎

**[MHDISP 2026-08-27] Grade: BLOCKED-CRITICAL.**  M1(2) is false, not a bookkeeping
omission.  M1(1) also remains unproved because its M1a stability step has not been promoted
to a public theorem.  MH.1 must be restated and proved before any consumer can fire.

### 3.2 M clauses 1–2 (support and side additivity)

The `≥` half of clause 1 is landed (`dvSupp_add_le_dvSupp_mul`).  For the `≤` half, the
landed endpoint assembly (`dvSupp_mul_eq_add_of_endpoint_le`, `C130nv2.lean:784`) needs
exactly `hup`: the digit of `g·z` at `jmin(g) + jmin(z)` has stage value `≤ Hg + Hz`.
By the C130nv3 mechanism (its "generic half", stated there with `hsurv` as a
hypothesis): that digit is `(dev g jg · dev z jz) %ₘ key + (strictly-above terms)`
(landed `dev_mul_pow` at carry 0, `dev_zero_pin`, and `lt_line_dev_term` for every other
convolution/carry term, using the strict floor).  M1(1) prices the head at EXACTLY
`Hg + Hz`; the landed strict-stability law (`stageHeight_add_eq_left_of_lt`,
`C131y.lean:96`) then gives the digit's value = `Hg + Hz` — i.e. `hup`, with equality.
Clause 1 and `dvSideMin`-additivity follow from the landed assembly
(`dvOnSide_mul_endpoint`, `dvSideMin_mul_le`, `dvOnSide_endpoint_unique`).

`dvSideMax`-additivity (NOT in the landed bank — new, same pattern): the identical
argument at the pair `(jmax(g), jmax(z))`: the head survives at its exact value (M1
again); every convolution term at abscissa `J > jmax(g) + jmax(z)` has one factor's slot
strictly above its side line (beyond the attaining set), hence prices strictly above
(landed `le/lt_line_dev_term` shapes + the strict floor for carries).  So
`jmax(g)+jmax(z)` is on-side and nothing above it is.  `dvSideDeg` additivity follows
(both endpoints add; `ℓ`-spacing by C.08's `dvSideLen_eq`).

**[MHDISP 2026-08-27] Survival inventory correction.**
`C130nv3.stageHeight_dev_endpoint_le_of_surv` requires strict `ℓ * V < u` and an explicit
`hsurv`; it does not manufacture survival.  `C132nv3.s2_dvSupp_mul_modByComposedKey_le`
has since landed the relevant bound only at the S2 composed-key frame (degree `< 4`).  That
S2 theorem is useful evidence and closes its own specialized interface, but it cannot fill
the arbitrary-`F` hypothesis of Theorem M.  Here the generic discharge still depends on a
corrected M1 carry/twist theorem and is therefore BLOCKED.

### 3.3 M clause 3 (the residual identity)

Coefficientwise at slot `t` of `R(gz)`: the digit of `gz` at abscissa
`jmin(g)+jmin(z)+tℓ` is the double-development convolution (the landed representation in
`dvSupp_add_le_dvSupp_mul`'s proof body).  Terms split into (i) on-side pairs
`(j, i)` with `j + i = jmin(g)+jmin(z)+tℓ` — each contributes, through M1(2), the
product of the two slot reads times the pin unit; summing over `t₁ + t₂ = t` gives the
`t`-th coefficient of `R(g)·R(z)` times `τ`; (ii) every other pair or carry term prices
strictly above the line and reads 0 (**read-vanishing lemma**: `twistRead k A = 0` when
`dv(A) > k` — from `resMk_eq_zero_of_lt` through the C.22 stack; small node).  The
cocycle `τ` collects `stageLetter ^ (Σ twistExp-defects)`; it depends only on the pin
data, and the TW node (§9) computes it once; on the pure-`D′`-monic fence the
owner-adjudicated cite (`fgmn_dv_exact_mul`) asserts the exact form, which is the
consistency check `τ = 1` there.

**[MHDISP 2026-08-27] Grade: BLOCKED.**  This coefficientwise proof consumes the false
M1(2), the unproved corrected carry/twist law, read-vanishing, and the TW computation.
These are load-bearing open obligations; clause M(3) is not proved.

### 3.4 Remark — side witnesses for non-monic inputs

M is stated for nonzero (not necessarily monic) `g, z`: `dvSideSet_nonempty` (C34)
needs only `≠ 0`.  Current consumers apply it to monic inputs anyway.

### 3.5 Corollary M-monic (the monic-residual law)

For monic pure `g` with `D′ ∣ deg g`, `deg g > 0`: `M₀ = u · dvSideDeg` (the top digit
is `1` by `dev_top` (B13a — Monic-fenced only) with `stageHeight 1 = 0`), and `R(g)` is
MONIC (top slot reads `twistRead 0 1 = 1`; `twistExp 0 = 0` normalization — part of the
TW node).  This is what lets Theorem A take `hprod` without a unit, exactly as B.41's
`hcu1` step.

---

## §4 Proposed proof of Theorem A (conditional; currently BLOCKED)

**[MHDISP 2026-08-27]** This construction consumes the unproved Theorem M, the corrected
twist/carry law, read-vanishing/read-faithfulness, the lift pins, perturbation transport, and
the MH.8 limit conversion.  The argument below is a blueprint, not a completed proof.

Write `a := G.natDegree`, `b := H.natDegree`, `w₁ := u·ℓ·a`, `w₂ := u·ℓ·b`,
`w := W(g) = w₁ + w₂` (§3.5's value law).

### 4.1 The lift (initialization)

For monic `P ∈ K[Z]` of degree `d` with `P.coeff 0 ≠ 0`, the **side lift**
**[MHDISP 2026-08-27: corrected supply]** choose `B_t := 0` when `P.coeff t = 0`, and
otherwise construct `B_t` at height `M := u·(d−t)` so `deg B_t < D′`,
`stageHeight B_t = M`, and `twistRead M B_t = P.coeff t`.  Define
`Λ(P) := F.key ^ (d·ℓ) + Σ_{t < d} B_t · F.key ^ (t·ℓ)`.
An explicit `stageLiftO` formula must feed the inverse-twisted target
`stageLetter ^ twistExp(M) * κ`, not the bare `κ` displayed in the original formula.
The originally cited C.46/C.47 lemmas are private; the degree/slot/height pins have since
been publicly promoted in C131f.  Alternatively C.14 supplies the exact-`twistRead`
existential, but that theorem requires `[Finite (ResidueField O)]`, which Theorem A does not
currently assume; the transcription must either use the explicit C131f route or add that
finiteness hypothesis honestly.
Then (each still needing proof):
`Λ(P)` is monic of degree `ℓ·d·D′`; digits at abscissae `tℓ` with heights exactly
`u(d−t)` (⊤ where `P.coeff t = 0`); pure (left endpoint from `P.coeff 0 ≠ 0`, top from
monicity); `W(Λ(P)) = uℓd`, `M₀ = u·d`; `R(Λ(P)) = P` exactly.

Set `g₁⁰ := Λ(G)`, `g₂⁰ := Λ(H)`, `e₀ := g − g₁⁰·g₂⁰`.  By M clause 3 + §3.5 (`τ = 1`
on this fence) and `hprod`: `R(g₁⁰g₂⁰) = G·H = R(g)` at the same pins, so the reads of
`e₀` on the `w`-line vanish: `W(e₀) ≥ w + 1` (**read-faithfulness**: `W ≥ c` and
`read_c = 0` ⟹ `W ≥ c+1`; the cleared weight is integer-valued, so `> c` is `≥ c+1`).

### 4.2 The solve at one weight (the dv-twin of B.39, with the estimate)

**Lemma S (graded solve).**  Data: monic pure `p₁, p₂` with `D′ ∣ deg`, exact residuals
`R(p₁) = G`, `R(p₂) = H`, weights `w₁, w₂`; `IsCoprime G H`; an error `e` with
`deg e < deg p₁ + deg p₂` and `W(e) ≥ c`, where `c ≥ w₁ + w₂`.  Then there are
`U, V : Polynomial O` with

* `deg U < deg p₁`, `deg V < deg p₂`,
* `W(U) ≥ c − w₂` and `W(V) ≥ c − w₁`  (the split bounds — B.39's A-F.10 shape),
* `W(e − (p₂·U + p₁·V)) ≥ c + 1`  (**the contraction estimate: one full unit of the
  ℓ-cleared weight per step; in `v₂`-units, `1/ℓ` per step**).

*Proof.*  Read `e` on the `c`-line: `Ē := read_c(e) ∈ K[Z]` (slots `j` with
`c − uj ∈ ℓℕ`, coordinates `twistRead ((c−uj)/ℓ) (dev F.key e j)`; `deg Ē ≤ a + b − 1`
from the degree window and the digit cap).  Bézout with degree control: the K-linear map
`(Ū, V̄) ↦ H·Ū + G·V̄` from `{deg < a} × {deg < b}` to `{deg < a+b}` is injective
(`H·Ū = −G·V̄` ⟹ `G ∣ Ū` by coprimality ⟹ `Ū = 0` by degree), hence bijective (equal
finite K-dimensions).  Solve `Ē = H·Ū + G·V̄`.  Lift `U := Λ-window(Ū on the
(c−w₂)-line)`, `V := Λ-window(V̄ on the (c−w₁)-line)` (the §4.1 lift without the monic
top term).  Degrees: inside the windows ✓.  Weights: `W(U) ≥ c − w₂`, `W(V) ≥ c − w₁` ✓.
Reads of the correction, by M clause 3 applied to `p₂·U` and `p₁·V` (M is mixed — `U`
need not be pure; read-vanishing covers slots where `U`'s side is short):
`read_c(p₂·U) = H·Ū` and `read_c(p₁·V) = G·V̄` (the lifts are built through the inverse
twist so the cocycle cancels exactly).  So
`read_c(e − p₂U − p₁V) = Ē − H·Ū − G·V̄ = 0`, while `W(e − p₂U − p₁V) ≥ c` by the
ultrametric (each term `≥ c` via M clause 1).  Read-faithfulness upgrades to `≥ c+1`.  ∎

### 4.3 The iteration and its invariants

Invariant state: `g₁ᵏ, g₂ᵏ` monic of the FIXED degrees `ℓaD′, ℓbD′`, pure, with the
FIXED residuals `R(g₁ᵏ) = G`, `R(g₂ᵏ) = H` and heights `M₀ = ua, ub`; and
`W(eₖ) ≥ w + k + 1` for `eₖ := g − g₁ᵏg₂ᵏ`.

Step: Lemma S at `c := w + k + 1` (degree fence: `g` and `g₁ᵏg₂ᵏ` are monic of the SAME
degree, so `deg eₖ < ℓ(a+b)D′`).  Update `g₁ᵏ⁺¹ := g₁ᵏ + U`, `g₂ᵏ⁺¹ := g₂ᵏ + V`.

* *Invariants persist* — the **perturbation law M4** (dv-twin of B41a
  `pure_add_of_lt`; an ASSEMBLY of landed atoms: `dev_add_of_monic` (B32a),
  `dvHgt_add_eq_left_of_lt` (C131y:102), `twistRead_add_eq_left_of_lt` (C131ae:295)):
  adding `y` with `deg y < deg x`, `W(y) ≥ W(x) + 1` to monic pure `x` preserves
  monicity, degree, purity, `M₀`, and the residual.  Here `W(U) ≥ c − w₂ = w₁ + k + 1
  ≥ W(g₁ᵏ) + 1` ✓, symmetrically `V` ✓.
* *Error contracts*: `eₖ₊₁ = (eₖ − (g₂ᵏU + g₁ᵏV)) − U·V`; the first is `≥ c+1`
  (Lemma S); `W(U·V) ≥ (w₁+k+1) + (w₂+k+1) ≥ c + 1` (M clause 1).  So
  `W(eₖ₊₁) ≥ w + k + 2` ✓.

### 4.4 The limit, and exactness (the ONLY completeness consumption)

`W(g₁ᵏ⁺¹ − g₁ᵏ) = W(U_k) ≥ w₁ + k + 1 ≥ k`: Cauchy for `W` in fixed windows.  **Limit
node (dv-twin of B.40)**: the intended statement is that `deg (p k) < d` and
`W(p(k+1) − p k) ≥ k` give a limit `P`, `deg P < d`, `W(P − p k) ≥ k`.
**[MHDISP 2026-08-27: the original forward chain is invalid.]**  From
`dvHgt ≥ e₁ • gaussVal(dev)` and a lower bound on `dvHgt`, no lower bound on `gaussVal`
follows.  A valid forward conversion must use the bounded degree window to prove an upper
comparison for `stageHeight` in terms of `e₁ • gaussVal` plus a controlled finite
`F.h * j` loss, then absorb that fixed loss in the Cauchy index.  B.40's
`inf_npHgt_le_gaussVal` is also private and cannot be called by MH.8.  The reverse
coefficient-ideal transport may still be reusable, and the generic core
`exists_adicLimit_of_degree_lt` (`HenselFactorization.lean:306`) is public, but the two
required conversion lemmas are not supplied here.  MH.8 is a load-bearing OPEN node, not a
mechanical reskin.

Conditionally on MH.8, limits `g₁∞, g₂∞` would be monic of pinned degrees (leading coefficient constant along the
sequence); purity/residual transport by M4 (total perturbation has `W ≥ w₁ + 1`);
exactness: `W(g − g₁∞g₂∞) ≥ w + k + 1` for every `k` ⟹ all coefficients in
`⋂ₙ 𝔪ⁿ = 0` (`IsHausdorff` from `IsAdicComplete`): `g = g₁∞·g₂∞`.  Conclusions 1–5.  ∎

---

## §5 Proposed proof of Theorem B (conditional on M; currently BLOCKED)

Data: `g` monic pure, `D′ ∣ deg g`; `g = a·b = a'·b'` as in the statement.

**(B1) The competitor's degree is pinned (defect-vanishing).**  By M clause 2 and the
landed caps: `sideMax(g) = deg g/D′` (pure + `dvSideMax_eq_of_isDvPure`);
`sideMax(a') = ⌊deg a'/D′⌋` (`a'` pure via `HasLabel`);
`sideMax(b') ≤ ⌊deg b'/D′⌋` (`le_natDegree_div_of_mem_dvSideSet`).  Write
`deg a' = D′q_a + r_a`, `deg b' = D′q_b + r_b`, `D′ ∣ r_a + r_b`.  Additivity:
`sideMax(b') = q_b + (r_a + r_b)/D′ ≤ q_b` forces `r_a + r_b = 0`: **`D′ ∣ deg a'`**
(*the defect is the leak; `D′`-divisibility of the ambient seals it*), and
`sideMax(b') = deg b'/D′` exactly.  Then `deg a'/D′ = ℓ·deg R(a') = ℓ·m'·d_r`
(landed `natDegree_div_eq_of_isDvPure` + C.26's degree law).

**(B2) `m' = m`.**  M clause 3 on both splits:
`R(g) = τ₁·r^m·R(b) = τ₂·r^{m'}·R(b')` with `r ∤ R(b)`, `r ∤ R(b')`: unique `r`-adic
valuation in the UFD `K[Z]` gives `m' = m`, hence `deg a' = ℓD′md_r = deg a`.

**(B3) The pigeonhole.**  `δ := a' − a`, `ε := b − b'`.  From `ab = a'b'`:
`a·ε = δ·b'`.  If either of `δ, ε` is 0 the other is (monic cancellation) and we are
done; suppose both nonzero.  M clause 3 on the single polynomial `a·ε = δ·b'`:
`τ₃·r^m·R(ε) = τ₄·R(δ)·R(b')`.  `r ∤ R(b')` and `r` irreducible ⟹ `r^m ∣ R(δ)` ⟹
`deg R(δ) ≥ m·d_r`.  But `deg R(δ) = sideDeg(δ) ≤ ⌊deg δ/D′⌋/ℓ ≤ (ℓmd_r − 1)/ℓ
= md_r − 1 < m·d_r` (`deg δ < deg a` — equal-degree monics).  Contradiction.  So
`a' = a` and `b' = b`.  ∎

No completeness, no Newton, no squarefreeness.  (Cheaper than the plan's F1.H2 note
anticipated: "uniqueness in the dv-graded filtration" enters only through M.)

---

## §6 Proposed proof of Theorem C (conditional on M; currently BLOCKED)

### 6.1 Defect-vanishing inside a pinned-label factor

If `x` is monic pure with `D′ ∣ deg x` and `x = y·z` monic, the (B1) argument gives:
whenever `y` is pure, `D′ ∣ deg y` automatically, and `sideMax(z) = deg z/D′` exactly.
Consequence: **a monic pure `D′`-divisible polynomial has no far prime factor.**
Precisely: for a far (point-sided) monic prime `q ∣ x`, `sideMin`-additivity inside the
pure `x` gives `sideMin(q) = 0`, hence `sideMax(q) = 0` (point side); the (B1) cap
equality `sideMax(q) + sideMax(x/q) = deg x/D′` with `sideMax ≤ ⌊deg/D′⌋` on both then
forces both caps tight and both degrees `D′`-divisible, so
`deg q = D′·sideMax(q) = 0`: `q` is a unit — contradiction.

### 6.2 The placement

`fS'` with `HasLabel′` (pinned), `fS' ∣ f = P·Q·W`, `f` squarefree monic.

*Descent.*  Over `K₀ := FractionField O`, `K₀[x]` is a PID; `fS' ∣ f` squarefree ⟹
`fS' = ∏ᵢ qᵢ`, pairwise distinct monic `K₀[x]`-irreducibles; each `qᵢ` is a monic
`K₀`-divisor of a monic `O`-polynomial and `O` (a DVR) is integrally closed, so
`qᵢ ∈ O[x]` (Gauss descent; mathlib around `IsIntegrallyClosed` — the Lean node
performs the exact-name search; classical, not new).

*Per-prime placement.*  Each `qᵢ` divides `P·Q·W`, hence (prime) divides `P`, `Q`, or
`W`.  By §6.1 inside `fS'` (pure with the PIN `D′ ∣ deg fS'`): `qᵢ` is not far —
`sideMin(qᵢ) = 0`, `sideMax(qᵢ) = deg qᵢ/D′ > 0`, so `sideDeg(qᵢ) > 0`; and M clause 3
inside `fS'` gives `r^m = τ·R(qᵢ)·R(fS'/qᵢ)`, so `R(qᵢ) = τ'·r^{aᵢ}` with `aᵢ ≥ 1`
(positive degree).  Now:
  - `qᵢ ∣ W` ⟹ (M clause 2 inside `W`) `sideDeg(qᵢ) ≤ sideDeg(W) = 0` ✗.
  - `qᵢ ∣ Q` ⟹ (M clause 3 inside `Q`) `s = τ''·r^{aᵢ}·R(Q/qᵢ)` ⟹ `r ∣ s` ✗.
  - So `qᵢ ∣ P` for every `i`; distinct primes ⟹ `fS' = ∏ qᵢ ∣ P`.  ∎

### 6.3 Necessity notes (the constructed-counterexample charge)

* **`r` irreducible** — necessary for B/C: for reducible `r = r₁·r₂` two genuinely
  different "labelled" splits coexist at the residual level already (K[Z]-UFD);
  Lemma S's Bézout injectivity is coprimality, which for the pair `(r^m, s)` IS
  irreducibility of `r` against `r ∤ s`.
* **one-slope (purity of `g`)** — the engine's reads live on ONE line; for `g` with a
  point `(u,ℓ)`-side no labelled factor exists at all (landed
  `not_dvd_dvResPoly_of_natDegree_eq_zero`).
* **monic** — normalization only.
* **`D′ ∣ deg g`** — NECESSARY for B, not merely convenient: §7 refutes uniqueness
  without it.  For A it enters through §3.5 and the windows; defective-existence stays
  open (§9 OPEN-2) and is consumed nowhere in the F1 chain.
* **completeness** — consumed by A only (§4.4); B and C are completeness-free.
* **squarefree** — consumed by C only (prime-by-prime placement); B does not need it.

---

## §7 HISTORICAL DEFECTIVE-STRATUM REFUTATION (pre-A-C.20 only)

**[MHDISP 2026-08-27]** The arithmetic example below is retained as the evidence that led
to amendment A-C.20.  It is not a counterexample to the current signed C.34/C.35 shapes:
the degree-3 candidate fails their landed `D′ ∣ natDegree` hypothesis.  References below to
the unpinned selector mean `blockFactorLeaky`/`mult₂Leaky` in current source.

### 7.1 The instance, fully concrete (over `O = ℤ₂`, `π = 2` — absolute, C35b-style)

**Frame** `F`: `e₁ = 1`, `f₁ = 2`, `h = 1`, `D′ = 2`,
`Φ′ = F.key = x² + 2x + 4`.  Frame audit: monic ✓; X-polygon heights
`(v(4), v(2), v(1)) = (2, 1, 0)` — one-sided of slope `1 = h/e₁` with BOTH endpoints
attaining (`IsPure X key 1 1` ✓); `H₀ = 2`; frame residual
`ψ = frameRes = 1 + T + T²` over `resField X ≅ F₂` — irreducible of degree `f₁ = 2` ✓
(`hresirr`).  Irreducibility of `Φ′` over `ℤ₂`: its two roots have `v = 1` each…
[CAUTION: `x²+2x+4` has discriminant `4 − 16 = −12`, `v(−12) = 2`, `√−12 = 2√−3` and
`−3 ≡ 1 (mod 8)` makes `√−3 ∈ ℤ₂` — so `Φ′` is REDUCIBLE over ℤ₂ and `F.hirr` FAILS.
Use instead `Φ′ = x² + 2x + 2` — but that was computed non-pure.  The certificate
(§10) performs the frame search mechanically: a monic quadratic `x² + c₁x + c₀`,
`v(c₁) ≥ 1`, `v(c₀) = 2`, pure at `(1,1)` requires `v(c₁) = 1`; irreducible with
`ψ = T² + res(c₁/2)T + res(c₀/4)` irreducible over F₂ requires
`res(c₁/2) = res(c₀/4) = 1`, i.e. `c₁ ≡ 2 (mod 4)`, `c₀ ≡ 4 (mod 8)`; irreducibility
over ℤ₂ then needs disc `= c₁² − 4c₀` a non-square: `c₁ = 2, c₀ = 12`:
disc `= 4 − 48 = −44 = 4·(−11)`, `−11 ≡ 5 (mod 8)` — non-square ✓.  **The verified
frame is `Φ′ = x² + 2x + 12`** (the cert re-checks every clause; the arithmetic below
is written for a generic such frame and verified by the cert at this one).]

**Datum**: `(u, ℓ) = (3, 1)` (floor `1·2·1 = 2 < 3` ✓), `K = F₄ = F₂(θ)`,
`θ² = θ + 1`; label `r := Z + θ` (monic, irreducible, `r(0) = θ ≠ 0`, degree 1) — up to
the fixed twist normalization of the reads (the cert computes the twisted form; the
refutation is normalization-robust, §7.2).

**The block**: `fS := Φ′ + A₀` with `A₀` the height-3 digit reading `θ` (e.g.
`A₀ = 4x` at the model frame: `dv(4x) = v(4)·1 + 1 = 3`, level-1 read `T ↦ θ`).  Then
`fS` is monic pure of degree `2 = ℓD′md_r` (`m = 1`), `M₀ = 3`, `R(fS) = r` exactly.

**The far factor**: `q := x + 1`.  `deg q = 1 < D′`; single digit at abscissa 0;
`dv(x+1) = min(v(1)+0, v(1)+1) = 0`; side `= {0}` (point), `W(q) = 0`, `M₀(q) = 0`,
`R(q) = C(1)` — slot read of `x+1` at height 0 is `res(1) = 1` (the c-slot attains
alone).

**The ambient**: `g := fS·q`, monic of degree **3** (`D′ = 2 ∤ 3` — DEFECTIVE).  Hand
computation at the model frame (cert re-verifies at the audited frame):
`g = Φ′·(x + c) + E` with `dvHgt(g,0) = 3`, `dvHgt(g,1) = 0`, so
`W(g) = min(3 + 0, 0 + 3) = 3` attained at BOTH abscissae `0` and `1 = ⌊3/2⌋`:
**`IsDvPure F g 3 1` HOLDS**; and the two slot reads are `(θ, 1)` at heights `(3, 0)` —
**`R(g) = Z + θ = r` EXACTLY, so `HasLabel L g` HOLDS with `m = 1`.**

### 7.2 What it refutes

1. **[MHDISP 2026-08-27] Historical pre-A-C.20 C.34 uniqueness clause only.**  The two
   unpinned labelled splits
   `g = fS · q` (with `HasLabel fS`, `q` monic, `R(q)` a nonzero constant — the landed
   constant law gives the complement clause) and `g = g · 1` (with `HasLabel g` — §7.1
   — and complement `1`, again the landed constant law) have `fS ≠ g` (degrees 2 ≠ 3).
   Every hypothesis of the historical unpinned statement holds at this instance.  The
   current signed hypothesis additionally requires `D′ ∣ g.natDegree`, which fails because
   `2 ∤ 3`; current C.34 is therefore NOT refuted.
2. **[MHDISP 2026-08-27] Historical unpinned frontier/selector from `BlockContext`.**  For
   `f := g = fS·q`: `BlockContext L f` HOLDS (monic ✓; squarefree — `fS` has distinct
   roots (disc ≠ 0 at the audited frame; cert-checked) and `q` is coprime to it ✓;
   `Φ′ ∤ f` ✓; genuine side `sideDeg = 1 > 0` ✓; `r ∣ R(f)` ✓).  But the historical
   frontier shape is false: its witness needs `D′ ∣ deg fS₀` and `∀`-maximality over unpinned
   `HasLabel` divisors; the labelled divisors of `f` include both `fS` (deg 2) and
   `f` itself (deg 3): a witness with `D′ ∣ deg` must be `fS` (degree reasons), and
   maximality then demands `f ∣ fS` — false.  Current `BlockFrontier` pins every competitor,
   so this argument does not apply.
3. **[MHDISP 2026-08-27] Historical C.35 selector, now `blockFactorLeaky` and
   `mult₂Leaky`.**  At this `f`, the maximal unpinned
   labelled divisor EXISTS and is `f` itself (both labelled divisors divide it), so
   `blockFactorLeaky L f = f`, and the leaky multiplicity equation reads
   `3 = keyDeg₂ · mult₂Leaky = 2 · (3 / 2) = 2` — false.  This does not identify current
   `blockFactor L f` with `f` and does not refute current `blockFactor_spec` clause 3.

**Normalization-robustness.**  The slot heights of `R(fS)` and `R(g)` are the SAME pair
`(3, 0)`, and the raw slot values are the SAME pair `(θ, 1)`.  Any read normalization
(any `twistExp`, any `stageLetter` power convention) acts on the two residuals
IDENTICALLY, so `R(fS) = r ⟺ R(g) = r` under every convention: the refutation cannot be
normalized away.  (This is why no tuning is needed: `q = x + 1` has W-weight 0 and read
1 — the multiplicative identity of the graded ring.  Any monic `q` of degree `< D′`
with unit content and unit read works; `x + 1` is the simplest.)

### 7.3 Consequences and the recommended repair

* The corpus surrogate `HasLabel` (DECISION C-D1's closure-free reading) is LEAKY: it
  does not see far factors of degree `< D′` with trivial graded content.  The classical
  source pins the block's degree — LEMMA HE7-6: "`D″ | deg f_S`"
  (`spec/EFF-HE7.md:1653-1663`) — and the corpus surrogate dropped the pin.  C35b's D13
  refutation (`hasLabel_natDegree_dvd_false`) was the visible tip; the historical content
  here is that the leak made the **pre-A-C.20** conclusions false.  A-C.20 removed those
  unpinned conclusion shapes from the current signatures.
* **[MHDISP 2026-08-27] Repair R1 is LANDED as A-C.20:** pin the label everywhere it is
  load-bearing — `HasLabel′ L fS := HasLabel L fS ∧ D′ ∣ fS.natDegree` — in C.34's
  existence/uniqueness clauses (both the `fS`-witness and the `∀ fS'` competitors) and
  in `BlockFrontier`'s maximality quantifier.  A-C.20 matches the classical statement;
  §6.1 proposes why the pinned class is the "no far junk" class.
* The alternative repairs (blocking far factors via `BlockContext`, or weakening the
  uniqueness conclusion to "up to far-unit factors") are both uglier and are recorded
  only for completeness.
* The degree-pinned **statements** (§2) are not refuted by this section.  Their proposed
  proofs remain blocked by the independent M1/MH.8 gaps; “not refuted” is not “proved.”

---

## §8 Proposed F1.H3 after A-C.20: current `BlockFrontier` from `BlockContext`

**[MHDISP 2026-08-27]** A-C.20 made the proposed `BlockFrontier′` the substance of current
`BlockFrontier`: both the witness and maximality competitors are degree-pinned.  The outline
below is still BLOCKED because it consumes M, A, B, C, and X1; it is not a proof that current
`BlockContext` implies current `BlockFrontier`.  Proposed assembly, given
`hctx : BlockContext L f`:

1. `hctx` gives `f` monic, squarefree, `¬ F.key ∣ f`, a genuine `(u,ℓ)`-side
   (`0 < dvSideDeg`), and `r ∣ R(f)`.
2. The C.33 cite `exists_dvDissection` (allowlisted axiom, `C33Cite.lean:76`) gives
   `D : DvDissection F f`; its `hsides` iff fires at `(L.u, L.ℓ)` (positivity,
   coprimality, floor from `L`; the genuine side from `hctx`), so
   `G := D.factor (L.u, L.ℓ)` is monic, pure, `G ∣ f` (from `hprod`), with
   `deg G = D′·(ℓ·dvSideDeg f)` — **the `D′`-rider from provenance** (`D.hdeg`).
3. **Residual transport** (`C35_BLOCKED` obstruction 1, now discharged by M):
   `f = G · Wf` with `Wf := D.below · ∏_{p ≠ (u,ℓ)} D.factor p` monic.  Each
   other-slope factor is pure at its own slope with a genuine side THERE; a small lemma
   (**X1**: a `(u',ℓ')-pure` polynomial with `u'ℓ ≠ uℓ'` has a POINT `(u,ℓ)`-side —
   from the side geometry: two distinct tilt directions cannot both have positive
   attaining spans, by the C.08 spacing/convexity calculus) plus `D.hbelow` (point side
   at every admissible direction) plus M clause 2 (side additivity over the product)
   give `sideDeg(Wf) = 0`, i.e. `R(Wf)` is a nonzero constant.  M clause 3 then gives
   `R(f) = τ·R(G)·C(unit)`, so `r ∣ R(G)` (r nonconstant irreducible vs unit scalars).
4. Theorem H0 splits `R(G)`'s monic normalization (§3.5: `R(G)` is monic — `G` is pure
   with `D′ ∣ deg G`) as `r^m · s`, `m ≥ 1`, `r ∤ s`, coprime.
5. Theorem A splits `G = fS · g₂` with `HasLabel L fS` (exact residual `r^m`), both
   factors pure with `D′`-divisible pinned degrees.
6. `fS ∣ G ∣ f` ✓; `D′ ∣ deg fS` ✓ (conclusion 2).  Maximality over `HasLabel′`
   competitors: Theorem C at `f = fS · g₂ · Wf` gives `fS' ∣ fS` for every pinned
   labelled divisor `fS'` of `f`.  **Conditional conclusion: current `BlockFrontier L f`.**

Under landed A-C.20, `blockFactor` (defined over pinned labels) conditionally recovers all four
`blockFactor_spec` clauses through the landed packaging pattern
(`blockFactor_spec_of_frontier`, whose proof shape is unchanged).

The landed C.48 `fullSide_block` consumer is UNAFFECTED by the pin (its `f` has exact
degree `μ₂D₂` and is its own block — `D′ ∣ deg` holds there; the maximality it uses is
the trivial `fun _ _ h => h` instance, `C48.lean:105`).

---

## §9 Node decomposition (formalization-trivial pieces, wired to the plan's rows)

Naming: MH.* are this engine's nodes.  "Landed inputs" name exact declarations.
Sizings are Lean source lines, same convention as the plan.

**[MHDISP 2026-08-27] Node gate.**  `MH.1` is **BLOCKED-CRITICAL** because its read clause
is false.  `MH.0b`, `MH.0c`, `MH.2`–`MH.9`, and `MH.11`–`MH.15` are **BLOCKED** by that
critical root and/or their own load-bearing gaps (MH.8 additionally has the invalid/private
limit conversion; MH.14 is OPEN-4).  `MH.16` is **HISTORICAL-ONLY** after A-C.20 and must
target `blockFactorLeaky`/`mult₂Leaky`, not current signed declarations.  `MH.0a` and the
independent algebraic `MH.10` are not logically refuted, but they do not authorize the MH
transcription fleet to fire.

| node | statement | landed inputs | sizing | plan wiring |
|---|---|---|---|---|
| MH.0a | `stageHeight_key`: `F.stageHeight F.key = (D′ * F.h : ℕ∞)` (from `F.hpure` at `X`) — wires `L.hκ` to C130nv2's `hV/hadm` | `stageHeight_eq_inf` (C.02), `IsPure`/`sideSet` at `X` | 30–50 | feeds every M consumer |
| MH.0b | read-vanishing: `dv(A) > k → twistRead k A = 0`; and read-faithfulness on windows (`W ≥ c` ∧ all line-reads 0 → `W ≥ c+1`) | `resMk_eq_zero_of_lt` (B39b), C.22 stack | 50–90 | §3.3, §4.2 |
| MH.0c | TW: `twistExp 0 = 0`, `twistRead 0 1 = 1`, the product cocycle `τ(k,k') = stageLetter^(twistExp k + twistExp k' − twistExp (k+k'))`, and its cancellation on the §3.5 fence | C.22 defs, C.46 pins, `twistRead_one_X` (C35b) as model | 60–120 | §3.3/§3.5/§4.1 |
| MH.1 | **BLOCKED-CRITICAL:** restate M1 with the slot carry or directly as a generic `twistRead` product theorem; M1a still needs promotion/proof | `stageHeight_mul`, division bank, `resPoly_mul_gen`, `resMk_add`, `F.hresirr`; C130nv3 still takes `hsurv` | re-estimate after restatement | **the root; current read statement is false** |
| MH.2 | Theorem M clauses 1–2: unfenced `dvSupp_mul`, `dvSideMin_mul`, `dvSideMax_mul`, `dvSideDeg_mul` at frames | MH.1, `dvSupp_mul_eq_add_of_endpoint_le` + endpoint bank (C130nv2:645-810), `lt_line_dev_term`, `stageHeight_add_eq_left_of_lt` (C131y) | 120–200 | kills `C35_BLOCKED` obstr. 1's support half; NV-4 generalizes for free |
| MH.3 | Theorem M clause 3: `dvResPoly_mul_gen` — `R(gz) = τ·R(g)·R(z)` with τ from MH.0c | MH.1–MH.2, `dev_mul_pow`/`dev_finsetSum` (B35a), MH.0b | 250–450 (the largest node; B39a's level-2 twin) | subsumes the blueprint's `dvResPoly_mul_of_pure` RE-PLAN; **makes `fgmn_dv_exact_mul` provable** (§9.2) |
| MH.4 | §3.5 M-monic (monic residual, `M₀ = u·d`, `τ = 1` fence) | MH.0c, MH.3, `dev_top` (B13a), C.26 | 40–80 | B.41's `hcu1` twin |
| MH.5 | **BLOCKED:** corrected side lift `Λ` + its five clause lemmas (§4.1) | public C131f `stageLiftO` degree/slot/height pins or C.14 `exists_twistRead_preimage` (with its finiteness hypothesis), `sum_dev_eq`, `dev_eq_zero_of_lt` | re-estimate | F1.H1 init; private C.46/C.47 helpers are not inputs |
| MH.6 | perturbation law M4 (dv `pure_add_of_lt`) | `dev_add_of_monic` (B32a), `dvHgt_add_eq_left_of_lt` (C131y:102), `twistRead_add_eq_left_of_lt` (C131ae:295), `dvHgt_add_min` (C131y:220) | 80–140 | F1.H1 invariants; ALSO the plan's F3.3 mechanism (same shape — coordinate) |
| MH.7 | **BLOCKED:** Lemma S incl. the K-linear Bézout iso | MH.0b, MH.3, MH.5; locally reconstruct `Field K` (C.04 exports no instance) | re-estimate | F1.H1 core |
| MH.8 | **BLOCKED-GAP:** dv graded limit + two correct bounded-window conversion lemmas | public `exists_adicLimit_of_degree_lt`; reprove/promote any needed B.40 comparison (line-121 helper is private) and control the `F.h*j` loss | re-estimate | F1.H1 limit; original logical direction invalid |
| MH.9 | Theorem A assembled (`exists_dv_graded_factorization`, B.41-shaped conclusion incl. exact residuals) | MH.4–MH.8 | 120–200 | **F1.H1** (revised total: the plan's 140–240 was under; realistic 300–500 across MH.5–MH.9 alone) |
| MH.10 | Theorem H0 (`dvResidualBezout`) | field `K[Z]` UFD arithmetic | 35–60 | **F1.H0** (unchanged) |
| MH.11 | Theorem B (`dv_oneSlope_split_unique`, pinned form) | MH.2, MH.3, landed C.35 endpoint lemmas, C.26 degree law | 100–160 | **F1.H2** (mechanism CHANGED: no filtration induction; degree pigeonhole) |
| MH.12 | §6.1 defect-vanishing + no-far-primes; Gauss descent (mathlib `IsIntegrallyClosed` search) | MH.2; mathlib | 60–110 | feeds MH.13 |
| MH.13 | Theorem C placement | MH.2, MH.3, MH.12, `Squarefree` API | 100–170 | the maximality half of **F1.H3** |
| MH.14 | **BLOCKED / OPEN-4:** X1 + transport step 3 of §8 | MH.2, MH.3, C.08 spacing, `D.hbelow` | unknown until proved | **F1.H3** |
| MH.15 | **BLOCKED:** §8 assembly of current `BlockFrontier_of_context` | C.33 cites, MH.9–MH.14 | re-estimate | **F1.H3**; A-C.20 already supplied the pinned target signature |
| MH.16 | **HISTORICAL-ONLY:** §7 pre-A-C.20 leak record | current targets must be `blockFactorLeaky`/`mult₂Leaky` | optional | not a refutation of current C.34/C.35 |

**Revised F1 pricing** (vs `BLOCKERS_PLAN` §F1): H0 unchanged; H1 = MH.5–MH.9
≈ 520–880 lines (plan said 140–240 — under-priced because the mixed product law MH.1–MH.3
was hidden inside "use `fgmn_dv_exact_mul` only to certify exact product reads", which
is impossible: the solve and the transport need MIXED reads the cite does not cover);
H2 = MH.11 (100–160, plan 100–180 ✓ but mechanism changed); H3 = MH.12–MH.15 (310–530,
plan 70–120 — under-priced for the same reason).  **[MHDISP 2026-08-27] The former owner
statement-gate R1 is no longer part of this price because it landed as A-C.20.**
MH.1–MH.3 (520–910 lines) are the shared root serving H1, H2, H3 at once.

### 9.1 Ordering recommendation

**[MHDISP 2026-08-27] The fleet may not follow the original order.**  A-C.20 has already
resolved the signature gate; MH.16 is optional historical maintenance at the `*Leaky` names.
First redesign and prove the corrected generic carry/`twistRead` root replacing MH.1, under
the strict floor, then prove the bounded-window limit comparisons for MH.8 and X1 for MH.14.
Only after those gates are green should downstream MH.2–MH.9/MH.11–MH.15 be rescheduled.
The independent algebraic MH.10 can be scoped separately but does not un-fence the fleet.

### 9.2 Strategic note: the cite becomes a theorem

**[MHDISP 2026-08-27: conditional only.]**  If corrected MH.3 + MH.2 are proved, they would
prove strictly more than `fgmn_dv_exact_mul` asserts (mixed vs pure×pure;
the purity-closure clause is MH.2's endpoint additivity + the landed C.35 endpoint
lemmas).  Once MH.3 lands, the cite can be RETIRED (axiom → theorem), shrinking the
declared-cite allowlist by one — the axiom-policy direction this repo prizes.  Until
then the engine does NOT consume the cite anywhere load-bearing (it is used only as the
consistency check for the TW normalization, §3.3), so there is no circularity in
retiring it afterwards.

### 9.3 Named OPEN/BLOCKED items (load-bearing status corrected)

* **OPEN-CRITICAL (corrected M1 read law)** — [MHDISP 2026-08-27] replace the false bare
  `slotRes` equality by a generic carry formula or direct `twistRead` multiplicativity
  theorem.  Load-bearing for M and every downstream engine node.
* **OPEN-1 (M1a order-1 stability)** — stated §3.1(c); private-needs-promotion/reproof and
  load-bearing for M1(1), not merely routine bookkeeping.
* **OPEN-2 (defective existence)** — FRONTIER 1 on `D′ ∤ deg g`: expected true
  (classical FGMN covers all `f`); not consumed by F1 (the dissection factor is
  `D′`-divisible).  [MHDISP 2026-08-27] A-C.20 has repaired C.34; any extension of the
  engine to the defective ambient stratum should still be re-examined (the witness `fS` can be
  pinned; the SPLIT still exists classically with the far part in the complement — the
  engine extension would need windows with a non-monic top digit).
* **OPEN-3 (the C.22 definitional chases)** — MH.0b/0c and the corrected M1 walk through
  `slotRes`/`twistExp`; now known to contain a nontrivial carry.  Load-bearing for M(3),
  initialization, solve, and monic normalization.
* **OPEN-LIMIT (MH.8)** — prove public bounded-window `W`/Gauss comparisons in the correct
  directions; B.40's private helper cannot be consumed.  Load-bearing for Theorem A.
* **OPEN-4 (X1)** — the other-slope point-side lemma; unproved and load-bearing for §8
  residual transport/`BlockFrontier_of_context`.

---

## §10 The numeric certificate (`verification/dv_hensel_cert.py`)

Examples-first, per the standing rules.  Exact ℤ arithmetic (truncated 2-adics at
`2^60`), a faithful model of `stageHeight`/`dvSupp`/`dvSideSet`/raw slot reads at the
audited frame of §7.1 (`O = ℤ₂`, `Φ′ = x² + 2x + 12`, `(u,ℓ) = (3,1)`, `K = F₄`).
Model caveat: reads are computed in the RAW normalization (no twist); every certified
claim is either twist-invariant (weights, side sets, degrees) or
normalization-robust in the §7.2 sense (equal slot-height patterns).

1. **Frame audit** — the §7.1 clauses of `Φ′ = x² + 2x + 12`: purity at `(1,1)`, `ψ`
   irreducible, disc a non-square (2-adic square test).
2. **M clauses 1–2** (the root, falsifiable): random nonzero pairs `(g, z)` through
   degree 10 (mixed strata: pure, far, multi-slope): check
   `W(gz) = W(g) + W(z)`, `jmin/jmax` additivity.  Preregistered falsifier: ANY strict
   inequality kills MH.2 as stated.
3. **M clause 3** (raw form): `R_raw(gz) = R_raw(g)·R_raw(z)` in `F₄[Z]` on the same
   sample (raw-τ is trivial at this frame's pin pattern; recorded as such).
4. **The Newton engine end-to-end** (Theorem A): `r = Z + θ`, `s = Z + θ²` (coprime);
   `g := Λ(r·s) + perturbations` of weight `> W`; run init + iterate; check the
   CONTRACTION (error weight climbs by ≥ 1 per step, and by EXACTLY 1 generically),
   convergence to `g = g₁g₂` mod `2^50`, invariants (degrees, monicity, purity,
   residuals) at every step.  Negative controls: `r = s` (Bézout fails — expected
   crash), two-slope `g` (reads misbehave — expected invariant failure).
5. **The §7 refutation**: verify `HasLabel`-shape for BOTH `fS` and `fS·(x+1)` (purity,
   side sets, `R_raw = Z + θ` for both — the equal-slot-height pattern that makes it
   normalization-robust), and `BlockContext` for the ambient; verify no
   `D′`-divisible-degree labelled divisor is divided by `fS·(x+1)`.
6. **Uniqueness pigeonhole spot-check** (Theorem B): on `D′`-divisible pure ambients,
   randomized search for a second labelled split (expected: none — falsifier for B).

### 10.1 RESULTS (run 2026-08-26, `verification/dv_hensel_cert.log`) — **ALL PASS**

**2832 checks, 0 FAILS.**  Highlights:

* Sec 2/3 (Theorem M): 600 random pairs across mixed strata (non-monic, far, defective,
  multi-slope): `W`-additivity, `sideMin`/`sideMax`-additivity, and raw residual
  multiplicativity `R_raw(gz) = R_raw(g)·R_raw(z)` held on EVERY pair (2400 checks).
  The preregistered falsifier (any strict inequality) did not fire.
* Sec 4 (Theorem A): the engine converged in 50 steps from a perturbed ambient; the
  error-weight trajectory was `10, 11, 12, …, 60` — the contraction bound `≥ +1` held
  at every step AND was attained with EQUALITY at every step (the certified law is the
  sharp estimate, not a slack bound).  All window/monicity/purity/exact-residual
  invariants held at every step.  Negative controls fired as predicted (`gcd(r,r)` not
  a unit; the point-sided ambient has constant residual).
* Sec 5 (the §7 refutation): CONFIRMED — `fS = x² + 6x + 12` has `R_raw = Z + θ = r`;
  the defective ambient `fS·(x+1)` (degree 3) is PURE with `R_raw = Z + θ = r` exactly;
  the two slot-height patterns are the identical `(3, 0)` (normalization-robustness
  machine-checked); every `BlockContext` clause holds at the ambient.
* Sec 6 (Theorem B spot-check): brute search over 2¹⁴ monic quadratics dividing the
  `D′`-divisible pure ambient mod `2¹²`: exactly the engine's own factor carries the
  label — no second labelled split.

Honest scope: one frame (`ℤ₂`, `Φ′ = x²+2x+12`, `(u,ℓ) = (3,1)`, `K = F₄`), raw reads,
bounded degrees/coefficients.  **[MHDISP 2026-08-27]** The certificate is exploratory
evidence only.  It did not exercise the nontrivial `(2,2,3)` slot carry and therefore did
not falsify the false M1(2); it cannot certify M, the contraction proof, the historical
refutation as a current-signature refutation, or any universally quantified Lean statement.

### 10.2 Elaboration probe (`leanfinal/scratch/MHENS_probe.lean`) — GREEN

`lake env lean scratch/MHENS_probe.lean` exits 0 (run 2026-08-26).  Prop-shape
definitions (the C35b `D13Statement` pattern — no assertions, zero `sorry`, zero
`axiom`) of: `HasLabelPinned` (= §2's `HasLabel′`), `BlockFrontierPinned`,
`MixedSupportLawStatement` (M clauses 1–2), `MixedResidualLawStatement` (M clause 3,
∃-τ form), `EngineExistenceStatement` (Theorem A), `EngineUniquenessStatement`
(Theorem B) — every binder elaborates against the landed C.06/C.07/C.25/C.29/C.35
vocabulary; plus one PROVED theorem `blockFrontierPinned_of_blockFrontier` (the repair
only shrinks the maximality quantifier).  All seven footprints are exactly
`[propext, Classical.choice, Quot.sound]`.

### 10.3 [MHDISP 2026-08-27] Disposition probe and final status

`lake env lean scratch/MHDISP_probe.lean` exits 0 with zero `sorry` and zero `axiom`.
It checks the current A-C.20 pinned signatures and `*Leaky` historical names, the explicit
`hsurv`/strict-floor shape of C130nv3, the S2-only C132nv3 survival theorem, the public C131f
lift pins, exact inverse-twisted lift construction, local reconstruction of `Field K`, and
the nontrivial `F₉` slot carry/cancellation row.  Printed footprints are exactly
`[propext, Classical.choice, Quot.sound]`.

**Final document status:** genuine design progress, but **ENGINE NOT PROVED**.
**Fleet status:** **DO NOT FIRE** MH.1–MH.9 or MH.11–MH.15 until the corrected generic
twist-read product law, MH.8 conversion lemmas, and X1 are proved.  Current pinned C.34/C.35
are not refuted; they remain blocked on construction/proof, not on statement consistency.
