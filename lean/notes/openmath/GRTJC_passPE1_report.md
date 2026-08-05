# GRTJC pass PE1 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` (J-C, W-6..W-9, attempt
0/2), runner `verification/openmath/grt_jc_checks.py`, two-commit seal
`6ad01d1` → `8f07904`.
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
**Pass date:** 2026-08-05 wallclock (campaign 2026-08-08).

## VERDICT

**2 CRITICAL · 8 GAPS.** Both CRITICALs have ONE root cause and ONE localized
repair: the note's coordinate calculus (§2.10's `(COORD)` and the cited input
`(IN-3)(c)` = FGMN Thm 4.2) is asserted on the pieces `gr_λ(w)` of the
**un-localized** graded ring, where it is **refuted by the note's own objects and
by its own roster** — MacLane/FGMN freeness over `Δ ≅ K_m[y]` lives on the
**post-TC-1** pieces `B_n` (the note's own JC-DOM writes them down). Machine
counter-instance below, on a row the note's battery scores. The digit-level
theorems (JC-SPAN, JC-LOAD, JC-PSIKER's witness, JC-SCAL, JC-PER, JC-FIB,
JC-ANCHMON, JC-GAUGE) survive the pass **re-derived and correct**; what fails is
the passage from digit polynomials to "A_ν is a 1-dimensional K-space", i.e.
exactly OB-4 / W-7's bijectivity / JC-F1's dimension count.

Machine leg: **fully reproduced, exit 0** (details in §M).

---

## CRITICAL 1 — `(COORD)`'s surjectivity half and `(IN-3)(c)` are FALSE on the note's own `gr(w)`; §2.10's uniform display is refuted on the note's own roster

**Offending passages (verbatim).** §2.10:

> **(COORD)** For λ ∈ W the digit map 𝑅_λ : gr_λ(w) → Δ := K_m[y] is a K_m-linear
> **isomorphism**, carrying in(φ_λ) to a nonzero constant a_λ ∈ K_m^*
> (JC-ANCHMON(c)). Injectivity is definitional (§1: 𝑅_λ(f) = 0 ⟺ w(f) > λ);
> surjectivity/rank-one is (IN-3)(c) — FGMN Thm 4.2's freeness of gr_λ over Δ on
> the anchor basis.

and, same section:

>     gr_λ/(𝔦 ∩ gr_λ)  ≅  Δ/(ψ_m)  =  K_{m+1} = K       (via y ↦ z̄)
>
> a ONE-dimensional K-space with basis the image of in(φ_λ).

and the cited input, §0 (IN-3):

>     (c) gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y] on the anchor basis
>         in(φ_γ) at attained γ  [Thm 4.2];

**Why it is false.** §1 builds `w = w_{m+1}` from `w_0 = ` the coefficientwise
π-valuation on **integral** polynomials (the window `W := {γ : u_1(γ) ≥ 0}` and
"anchors φ_γ := π^{u_1}∏Φ_j^{s_{j+1}} for γ ∈ W" exist precisely to keep the
π-exponent ≥ 0). Hence every Φ_m-digit `A_a` of an f in the note's ring has
`w_m(A_a) ≥ 0`, and an on-line abscissa at level λ must satisfy
`e_m·w_m(A_a) + a·γ_{m+1} = λ`, so `a ≤ λ/γ_{m+1}`: **`gr_λ` is a
finite-dimensional K_m-space**, of K_m-dimension at most
`1 + ⌊(⌊λ/γ_{m+1}⌋ − s_{NR}(λ))/e_m⌋`. A finite-dimensional K_m-space is not
free of rank one over `K_m[y]`, and `𝑅_λ` cannot be onto `K_m[y]`. FGMN's
`Δ ≅ K_m[y]` is the degree-0 part of the graded algebra of a MacLane valuation on
`K[x]` (π **inverted**) — i.e. of `B := gr(w)[in(π)^{-1}]`, the object the note's
own JC-DOM constructs one page earlier.

**Machine counter-instance (row C2I, on the battery's own roster; script
`/tmp/pe1_gr4.py`, read-only, imports `grt_jc_probe`).** C2I: m = 1, E = 4,
g_m = 2, e_m = 2, γ_{m+1} = 5, wΦ_NR = 20, window base G0 = 4 (the battery's own
representative base, `inW(4) = True`):

```
integral f with w(f) = 4: 3072 sampled;  union of on-line slots = [0]
ideal (Phi_{m+1}) meets gr_lam only via gr_{lam - wPhi_NR}; lam - wPhi_NR = -16 < 0 => intersection 0
```

So at λ = G0 = 4 ∈ W: `𝑅_λ(gr_λ) ⊆ K_m` (constants only — surjectivity onto
`K_m[y]` fails), `𝔦 ∩ gr_λ = 0`, and therefore
`gr_λ/(𝔦 ∩ gr_λ) = gr_λ ≅ K_m`, **which is not a 1-dimensional K-space** —
`[K : K_m] = g_m = 2` here, so it is not even a K-module. The same slot-bound
computation gives `maxslot(G0) = 0` on **29/29 roster rows** (script
`/tmp/pe1_dim.py`), so the display fails at the note's chosen representatives on
every row, not just at a corner.

**What breaks (chain, stop-checking downstream of these):**
* §3.1 "Every A_ν is 1-dimensional over K after TC-3 (§2.10), so Ψ maps the
  ν-summand onto A_ν's K-line";
* §3.4 THEOREM JC-IND's step "By §2.10 each A_ν (after TC-3) is a 1-dimensional
  K-space with basis [φ_{γ_ν}] — the base change of the free rank-one Δ-module
  gr_{γ_ν}" — the module whose base change is taken does not exist as claimed;
* hence **OB-4 (independence) and W-7's bijectivity of Ψ**;
* §5 FINDING JC-F1's K-basis/dimension count (it counts E K-lines);
* `(MULT)`'s "unique anchor cocycle A(λ,μ) ∈ Δ" for arbitrary α, β (the Δ-action
  used to write α = ρ_λ(α)·in φ_λ is the localized structure, not gr's).

**What does NOT break** (checked independently, each uses only injectivity of
`𝑅_λ` plus explicit digit arithmetic): JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD,
JC-PSIKER's witness computation, and W-8's `(†)` read identity.

**Fence misdrawn, not merely unmet.** JC-BOX-3 boxes the wrong risk:

> **JC-BOX-3 (the literature leg, and citation precision owed).** (COORD)'s
> surjectivity/rank-one half is FGMN Thm 4.2 at composite order, quoted from the
> corpus's own pinned quotation … and **not re-verified against a printed source
> in this session** … If the composite-order instance of Thm 4.2 failed,
> §§2.7–3.4 fail together.

The defect is not "Thm 4.2 might be false at composite order"; it is that Thm 4.2
(true, and about `K[x]`) has been **transported to the wrong ambient object**, and
its transported conclusion is refuted by the note's own §1 arithmetic. The
repair is visible inside the note (JC-DOM: `B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}`)
— restate `(COORD)`/`(MULT)`/§2.10 on `B_n`, i.e. strictly after TC-1 — but it is
a re-derivation of §2.10 → §3.4, not a wording change, and the grade line
"**PROVED at general m** … with the single located exception of the **top-flat
corner e_m = 1 ∧ g_m = 1**" is defeated as written.

## CRITICAL 2 — COROLLARY JC-PSIKER's universal kernel claim is false at every λ ∈ W below wΦ_NR (29/29 rows at the note's own base)

**Offending passage (verbatim), §2.9:**

> Hence TC-3 has a nonzero kernel on every graded piece (namely ψ_m·Δ under the
> anchor coordinate) and **cannot be a relabeling of scalars.**

**Why it is false.** `𝔦 := in(Φ_{m+1})·gr(w)` is homogeneous with generator of
degree `wΦ_NR`, so `𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`, which is **0** whenever
`λ < wΦ_NR` (weights are ≥ 0 in the note's ring). Machine (`/tmp/pe1_dim.py`):
`G0 < wΦ_NR` on **all 29 rows** (e.g. C2A 4 < 10, C2I 4 < 20, C3G 200 < 222,
C4C 312 < 346, C4H 60 < 81, I4A 156 < 204). So on every row, at the anchor
representatives the note actually uses, TC-3's kernel on `gr_λ` is **zero**.

**Scope note in the target's favour:** W-6(v) states the fenced version
correctly — "the level-NR read is non-injective **on a graded piece**, with the
classifier's own next key Φ_{m+1} as the kernel witness" — and the witness
computation itself is CORRECT (re-derived: `wΦ_{m+1} = e_mg_mγ_{m+1} = λ`,
`s_{NR}(λ) = 0` since `e_m | λ`, abscissas `e_mk` ↦ slots k, digits = ψ_m's
coefficients, `read = ψ_m(z̄) = 0`, and `w(Φ_{m+1}+φ_λ) = λ` with equal reads and
different classes). The defect is the *universal* generalization in the closing
sentence, and §2.10 consumes exactly that universal form
("Hence for every λ ∈ W …"). Same root cause and same repair as CRITICAL 1
(the statement is plausible for `B_n`, false for `gr_λ`).

## GAP 1 — W-6(ii) claims `A_ν ≅ gr_n(w)`; JC-GAUGE delivers `A_ν ≅ B_n`, and `B_n ⊋ gr_n`

**Offending passage (verbatim), W-6(ii):**

> (ii) the gauged ring A(T) := gr(w)[in(π)^{-1}]/(in(π) − 1) is **ℤ/E-graded**,
> with A_ν ≅ gr_n(w)-piece for any n ≡ ν

LEMMA JC-GAUGE(iii) proves `B_n ≅ A_ν`, and JC-DOM defines
`B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}`. `B_n = gr_n` would require
`in(π)·gr_n = gr_{n+E}` (surjectivity), which fails: on C2I the slot bound along
`λ + kE` (λ = 4, E = 4) is

```
[(0,0),(1,0),(2,1),(3,1),(4,2),(5,2),(6,2),(7,3),(8,3),(9,4),(10,4),(11,4)]
```

— strictly increasing infinitely often, so `dim_{K_m} gr_{n+(k+1)E} > dim gr_{n+kE}`
for infinitely many k and the (injective) transition maps are not onto. `B_n` is
the strictly larger colimit. The lemma is right; the theorem statement quoting it
is not. (This is also where the localization does the real work — `B_n`, not
`gr_n`, is the plausible home of `Δ ≅ K_m[y]`.)

## GAP 2 — the central object `𝒜(T)` is defined in "the degree-0 component", which contradicts the note's own OB-4 proof (and makes W-7 dimensionally false)

**Offending passages (verbatim).** §1: "**𝒜(T)** := the K-span of the anchor
classes in the degree-0 component of the TC-transported gr(w)"; W-7 repeats:
"Let 𝒜(T) be the K-span of the anchor classes [φ_{γ_ν}] in the degree-0
component of the TC-transported gr(w) (§2.10)."

But §3.4's proof reads:

> By JC-GAUGE the transported ring is ℤ/E-graded and [φ_{γ_ν}] ∈ A_ν
> with ν = γ_ν mod E pairwise distinct (JC-FIB). A relation Σ_ν c_ν[φ_{γ_ν}] = 0
> … therefore splits into c_ν[φ_{γ_ν}] = 0 in A_ν for each ν.

The anchor class of γ sits in `A_{γ mod E}`, which is the degree-0 component only
for ν = 0; under the literal definition the entire degree-separation argument is
unavailable, and W-7's `Ψ` would map an E-dimensional carrier onto the single
K-line `A_0` (false for E > 1). The wording is inherited verbatim from
`GRW2_TIE_DESIGN` S2.2, the blueprint S2.3 and the brief, so this is a corpus-wide
display defect — but the note flags its *other* inherited-display correction
(JC-F1) explicitly and silently uses the corrected reading here. As written, the
defined object and the proved theorem are different objects.

## GAP 3 — the JC8 "every structure constant is a UNIT" check is unfalsifiable, so §9.2's power-basis evidence claim is unsupported

`grt_jc_checks.py` builds the constant table in the JC7 block:

```python
v = S.cval(ga, gb, S.ph[r], S.ph[s], base)
if v is None or K.is_zero(v):
    continue
cval[(r, s)] = v
```

and then JC8 scores:

```python
for k, v in cval.items():
    note('JC8')
    if K.is_zero(v):
        viol('JC8', S.spec['id'], 'structure constant 0 at %s' % (k,))
```

Zero (and undefined) constants are filtered out **before** the table exists, so
the violation branch is unreachable by construction: all 869 JC8 constant samples
are vacuous on this predicate, and the skipped pairs are never censused. §9.2's
verdict cell therefore overstates its own evidence:

> | JC8 | JC-CYC + JC-F1 | 898 | **0** | GREEN — every structure constant a unit
> (so JC-F1's power basis exists on every row); no CYCLIC verdict off the
> collapse geography |

The only real machine evidence for JC-F1's power basis is the E-fold chain, which
covers the **15 rows with E ≤ 8** and even there *silently skips* on a zero
(`if v is None or K.is_zero(v): ok = False; break`, then nothing is scored).
Mathematically the unit property is PROVED in §3.2 (u, a_λ ∈ K_m^*, z̄ a unit), so
this is an evidence defect, not a math defect — but "on every row" is not what was
tested.

## GAP 4 — §7's case-split table mislabels two rows' g_m (the note's own runner contradicts it)

**Offending passage (verbatim), §7 row 1:**

> | 1 | g_m ≥ 2, δ = 0 | C2B/C2I/C3I/C4I…; the majority of pairs on those rows |

The runner's own per-row print (reproduced this pass) gives `g_m = 1` for **C2B**
and **C3I**; only C2I and C4I have g_m = 2 — consistent with the note's own rows 3
and 4 ("the 27 g_m = 1 stages", 29 − 2). The mislabel is inherited from the
instrument's M5 ("Both designated g_m = 2 rows that were decidable came back
NOT-CYCLIC"), which the note *did* correct in §6(d) ("The decidable designated
g_m = 2 row came back NOT-CYCLIC (C2I)") and did not correct in §7. Since the
brief makes "the case list matches the observed genre list" a deliverable, the
genre column's row assignment is part of the claim.

## GAP 5 — §2.8(c) promotes an unfenced 29-row/669-pair machine set identity to "a THEOREM" while JC-LOAD is fenced at e_m ≥ 2

THEOREM JC-LOAD opens "Fix a pair (γ,γ′) as above with **e_m ≥ 2**", and
JC-BOX-4 boxes the e_m = 1 row open. Consequence (c) nevertheless reads:

>     (c) the sealed set identity {no pre-TC-3 scalar} = {δ ≥ g_m} of the
>         instrument (0/29 set-mismatches, 134/669 pairs) is a THEOREM, not an
>         observation.

The instrument's 29 rows / 669 pairs include C4H (e_m = 1), which the theorem does
not cover; on the note's own accounting the theorem covers 28 rows. The fence
exists at the theorem head, so this is scope slop in the consequence display, not
a false theorem.

## GAP 6 — §3.4's OB-4 census drops the instrument's disclosed skip count

**Offending passage (verbatim), §3.4 table row 2:**

> | monomial perturbations (SPAN-M) | **328 certified / 0 zero-class / 0 failed** |
> coordinate = (unit)·y^k reducing into K ⟹ certifies; 0 genre rows, so no case is owed |

The instrument's own verdict row reads "**328 certified / 0 zero-class / 0
FAILED** (606 skipped for non-integrality)". 606 of 934 perturbations untested is
the same species of resolution limit the note discloses scrupulously elsewhere
(MT3's 9 escapes; JC-BOX-5's "only 2 of 29 rows lie off the collapse geography"),
and it is dropped in the one place where the conclusion drawn is "no case is
owed". JC-BOX-3's honest rider mentions only the unmeasured Δ-rank refinement,
not the skipped 606.

## GAP 7 — §4.1's remark (a) asserts two identifications it does not prove

**Offending passage (verbatim):**

> *Two remarks the design note asked for.* (a) The a_λ's — the anchor's own digit
> constants, i.e. the ε-normalization the harness carries — **cancel** because both
> reads in c_val sit on the SAME line λ; this is why no coboundary condition is
> needed, and it is the general-m form of the ε-collapse J-B proved
> unconditionally (JB-EPS).

Two unproved steps: (i) `a_λ = 𝑅_λ(φ_λ)` is *identified with* "the ε-normalization
the harness carries" (asserted by apposition); (ii) the cancellation is called
"the general-m form of" JB-EPS, whose statement is about a different object — the
print-twist cocycle, `t_m(V+V′) − t_m(V) − t_m(V′) = ε′` (GRTJB §5, unconditional
at every m ≥ 1, scope verified this pass). Charge item (5) asked whether "both
reads sit on the same line" is proved rather than inherited: **it is proved**, and
trivially so — both reads in `c_val` are at λ = γ+γ′ *by the definition of c_val* —
so W-8's proof does not need either identification. Display-only, but the sentence
imports J-B's authority for a step that is not J-B's.

## GAP 8 (low) — fence hygiene: the note's own battery calls `Tower.constants` and `Tower.read`, and only the c_val half is disclosed

§3.5 offers as the tautology fence's machine bracket:

> while `Tower.constants` (c_T) and `Tower.read` (the harness val) are **never
> called inside the determination or the certification**

correctly attributed to the *instrument*. The note's own battery does call both:
`T.constants(ga, gb)['delta']` supplies δ in JC3, JC7 and MJ1, and `T.read` is
called in JC6/JC7/JC8. Nothing circular follows — `constants()` computes
`delta = (sa['s'][NR] + sb['s'][NR]) // e[NR-1]`, pure split data identical to §1's
definition, and the gr-side quantity (the slot set / digit polynomial) comes from
`read_coeffs` — but §9.2 discloses only the c_val-vs-c_gr point, not the δ source.
A hostile reader must derive the non-circularity themselves.

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

**Own battery `verification/openmath/grt_jc_checks.py` — reproduced exactly,
exit 0, elapsed 2.0 s, 29 rows.** Every §9.2 cell matches:

| family | §9.2 samples/viol | re-run | match |
|---|---|---|---|
| EXT-GATE | 1 / 0 | 1 / 0 | ✓ |
| JC1 | 2,594 / 0 | 2594 / 0 | ✓ |
| JC2 | 570 / 0 | 570 / 0 | ✓ |
| JC3 | 2,484 / 0 | 2484 / 0 | ✓ |
| JC3-FLAT | 24 / 0 | 24 / 0 | ✓ |
| JC4 | 443 / 0 | 443 / 0 | ✓ |
| JC5 | 855 / 0 | 855 / 0 | ✓ |
| JC6 | 116 / 0 | 116 / 0 | ✓ |
| JC7 | 581 / 0 | 581 / 0 | ✓ |
| JC8 | 898 / 0 | 898 / 0 | ✓ |
| MJ1 | 103 firings / 333 tested | 103 / 333 | ✓ |
| MJ2 | 285 / 285 | 285 / 285 | ✓ |
| MJ3 | 4 / 6 | 4 / 6 | ✓ |
| MJ4 | 29 / 29 | 29 / 29 | ✓ |
| MJ5 | 633 / 633 | 633 / 633 | ✓ |

Totals check: 8,566 scored samples (sum of the ten families) and 1,054 tooth
firings (103+285+4+29+633) — both as printed in the note. Also reproduced:
"slot set == {δ} on 609/609 pairs", "0 of 24 pairs have a slot > 0" (C4H census),
"261 cocycle triples", E-fold chain on exactly the 15 rows with E ≤ 8,
CYCLIC 6 / NOT-CYCLIC 14 / UNDECIDED 9 with cyclic rows C2A/C2E/C2G/C2J/C3A/C4A,
and the 13 NOT-CYCLIC collapse rows named in §9.2 finding 1 (incl. nvals = 7 on
I4C). `total violations 0; silent teeth NONE`.

**Seal.** `git merge-base --is-ancestor 6ad01d1 8f07904` → true. Runner md5
`adb555e1134d3ae0b0174d62e8b3446c` **identical** at 6ad01d1, 8f07904 and HEAD (so
the sealed runner is the run runner). Note md5 differs seal→HEAD, as expected;
`git diff 6ad01d1 8f07904 -- <note>` is **only** the disclosed edits: header
verdict paragraph, §6(d) one-directional restatement, JC-BOX-5, §9.2 (was
"[PENDING — battery not yet run at seal time.]"), and the §10.1 cyclic-fence row.
**No clause of §§2–5 was touched between seal and verdict**; the post-run edits are
confined to §6(d)/JC-BOX-5/§10.1 and are exactly the two findings §9.2 declares
("TWO BATTERY-DRIVEN FINDINGS, applied above"). §9.1's "no clause of §§2–6 was
edited because of it" is scoped to the *pre-seal build smoke*, and that scoping is
correct — the §6(d) weakening came from the full run and is disclosed as such, not
smuggled.

**Tautology fence, code-level spot check.** No check family computes the gr-side
digit data via `c_T`: slot sets/digits come from `T.read_coeffs`, and
`T.constants` is used only for the integer δ (definitionally
`(s_a+s_b)//e_m`) — see GAP 8. MJ1's RAW predicate is faithful to §2.8's (RAW):
`raw_cert` tests `w(LHS − Λ_N(c)·base) > target`, i.e. equality of digit
polynomials at the line, searched **exhaustively over K** (EXH_CAP = 512 ≥ every
row's |K| ≤ 25), and MJ1 probes both directions (103 load pairs all fail, 230
non-load pairs all succeed).

**Teeth — genuinely wrong inputs, all five:** MJ2 `φ_{γ+E} == π²φ_γ` (truth:
π¹); MJ3 `slots(Λ_N(c)) ⊆ {0}` (false for g_m ≥ 2 with c_1 ≠ 0 — 2 of 3 nonzero
c per g_m = 2 row, matching the note's "2 of the 6 opportunities are the c's whose
slot 1 is genuinely empty"); MJ4 `read(wΦ,Φ_{m+1}) ≠ 0` (truth: = 0); MJ5
`slot set == {δ+1}`; MJ1 "RAW solvable on every pair". All are mutations of the
*claim*, tested against the honest computation — but note none mutates the
*computed side* (no MT3-analogue rescaling inside this battery); §3.5 leans on the
instrument's MT3 for that, and the instrument's 9 escapes are disclosed.

**Instrument re-run `grt_jc_probe.py`: exit 0, 18.4 s, `total violations 0`** —
reproduces MT3 197/206, rival-reading failures H-B 215 / H-C 73 / H-D 138 of 669,
MT2 NOT-CYCLIC 14 / CYCLIC 6 / UNDECIDED 9, MT1 0/79, MT4 0/557. Every instrument
figure the note quotes (0/285 P0-OB2, 0/174 P2-REP, 0/138 P0-LIFT, 0/293 P0-SCAL,
0/116 P2-OFF, 0/669 P5-OB6, 0/29 P4-DEG, 134/669 with 0/29 set-mismatches, 27
eligible g_m = 1 stages, κ ∈ {1,z̄,z̄²,z̄³,z̄⁴}, k-distribution {0:669}) checks out
against `GRTJC_PROBE_2026-08-08.md` — **no stale machine quote found** except the
dropped skip count of GAP 6 and the g_m mislabel of GAP 4.

**Auxiliary read-only scripts written for this pass** (outside the repo, nothing
staged): `/tmp/pe1_dim.py` (per-row γ_{m+1}, wΦ_NR, G0, slot bounds),
`/tmp/pe1_gr4.py` (the C2I gr_λ sweep behind CRITICAL 1/2).

---

## §C WHAT SURVIVED THE PASS (re-derived, hostile, no defect found)

1. **LEMMA JC-GAUGE (TC-2), charge item (1) — CLEAN, and the unit hypothesis is
   satisfied in the right order.** Re-derived in full: (i) `(ϑ−1)B` splits along
   the E residue classes because `(ϑ−1)b ∈ B^{(n mod E)}` for homogeneous b;
   (iii) `σ(Σ_k b_{n+kE}) := Σ_k ϑ^{-k}b_{n+kE}` is additive, surjective (k = 0),
   kills `(ϑ−1)B^{(ν)}` (`σ(ϑb − b) = ϑ^{-(k+1)}ϑb − ϑ^{-k}b = 0`), and
   `x ≡ σ(x)` mod `(ϑ−1)B^{(ν)}` since `ϑ^{-k}b(ϑ^k − 1) ∈ (ϑ−1)B` for k of
   either sign; hence `ker σ = (ϑ−1)B^{(ν)}` and `B_n ≅ A_ν`, with `B_0 → A_0` a
   ring map. `ϑ^{-k}` requires ϑ to be a **unit in B**, and the note applies the
   lemma only to `B` from JC-DOM ("Take B from JC-DOM and ϑ := in(π) ∈ B_E (a
   unit after TC-1 …)") — TC-1 strictly before TC-2, as it must be. `w(π) = E` is
   proved (`w_{j+1}(π) = e_jw_j(π)`, `w_0(π) = 1`) and machine-confirmed on 29/29
   rows. The C13 answer ("quotient by a non-homogeneous principal ideal whose
   ideal splits along the E residue classes") is exactly what the proof shows.
2. **THEOREM JC-SPAN, charge item (2) — CLEAN.** δ ∈ {0,1} follows from
   `s_{NR} ≡ l_mγ (mod e_m)` additive with values in `[0,e_m)`. Lower end uses
   (IN-3)(e) within its hypotheses: `s(φ_γ) = s_{NR}(γ)` because JC-ANCHMON(b)
   makes the anchor a single on-line digit, so Cor 2.7's additivity applies to the
   *minimal on-line abscissa* as quoted. Upper end re-derived: JC-ANCHMON(d) gives
   `deg(φ_γφ_{γ′}) < (s+s′+2)degΦ_m` ⟹ max abscissa ≤ s+s′+1 ⟹ slot
   `k ≤ δ + 1/e_m` ⟹ `k ≤ δ` for e_m ≥ 2, `k ≤ 1` at e_m = 1. Telescoping in
   JC-ANCHMON(a) is correct (`s_{j+1}degΦ_j ≤ degΦ_{j+1} − degΦ_j`, sum
   `≤ degΦ_m − degΦ_0`).
3. **THEOREM JC-LOAD's iff, charge item (2) — CLEAN in both directions.**
   Reworking (‡) with (MULT) on both sides, the `A(λ,N)` and `a_N` factors cancel
   and the equation is `(u/a_λ)y^δ = c̃(y)` with `c̃` the canonical degree-<g_m
   representative; solvable in `K^*` iff δ < g_m (⟸ needs `y` invertible mod ψ_m,
   which holds since ψ_m(0) ≠ 0). The note's phrasing "the RHS ranges exactly over
   𝑅(X_N)·{polynomials of degree < g_m}" carries the wrong constant (`a_λ` vs
   `𝑅(X_N)`) but both are units, so the conclusion is unaffected.
4. **COROLLARY JC-PSIKER's witness, charge item (3) — CLEAN** (hand-checked; see
   CRITICAL 2 for the one sentence that overreaches).
5. **Charge item (4), the zero-class genre — CLEAN as stated.** §2.10 gives a
   biconditional ("a class dies in TC-3 iff its Δ-coordinate ∈ (ψ_m)"), so "the 60
   are exactly that kernel" is a legitimate reading of the 60 measured deaths, and
   SPAN-S sums are correctly ruled irrelevant to anchor independence. The
   *independence* argument is about classes downstairs, not representatives
   upstairs (the relation is split in the quotient's own ℤ/E-grading, and
   `[φ_{γ_ν}] ≠ 0` because `a_λ ∈ K_m^*` is not divisible by ψ_m) — the charge's
   suspicion does not land; what lands is CRITICAL 1's input failure.
6. **W-9 + FINDING JC-F1, charge item (6) — algebra CLEAN given JC-IND.**
   `v^k = β_k[φ_{γ_k}]`, `β_k = ∏_{i<k}c(1,i) ∈ K^*` (equal to `∏c(i,1)` by
   commutativity of gr), `v^E = ζ_T·[φ_0] = ζ_T` with `φ_0 = 1` (0 ∈ W since
   `u_1(0) = 0`), the K-algebra map `K[v]/(v^E − ζ_T) → 𝒜(T)` is well defined
   (polynomial ring → commutative K-algebra), surjective by the basis and
   injective by dimension count. The unit input is PROVED (§3.2), not merely
   measured. **Consistency with the byte-frozen record holds and is, if anything,
   understated:** the ledger's own 2026-08-08 STRATA PROBE entry says
   "abstract crossed-product cyclicity displayed as **automatic/not-tested**" —
   i.e. the frozen adjudication never claimed abstract non-cyclicity, exactly
   JC-F1's reading. The 22/28 record is quoted unamended, no row re-scored, and
   JC-F1 is marked REVIEW-OWED in JC-BOX-5.
7. **Charge item (7), the stack — complete for what is consumed**, with two
   observations: (IN-2) (CARRY-1/D-REAL) is declared but never actually consumed
   in §§2–5 (over-declaration is safe), and the FGMN numbering flag names all
   three load-bearing numbers (Thm 4.2 / Thm 4.8 / Cor 2.7) — honest. §3.3's
   `c_val = c_T` composition is legitimate: `ITERLAWN_PROOF_2026-08-08.md` §S0.2
   defines `c_{n+1}(γ,γ′) := val(φ_γ·φ_{γ′}) / val(φ_{γ+γ′})` on the same window,
   i.e. the note's `c_val` — the identification §3.3 needs is real, though the
   note never states it.
8. **Consumer displays — accurate.** `gateJS1_cocycle_assoc` does carry
   `(hTrack : D.OuterTrackAdd)` and `gateJS2_dreal_degeneration` exists in
   `Scaffold/HDischarge/H1/DIterCarrier.lean`; no `.lean` file is touched by
   either seal commit; no gate fires or retires; J3b is displayed as standing.
9. **Charge item (8), general-m hygiene — no clause leans on the m ≤ 3 battery**
   for its proof: every general-m claim has an algebraic proof (correct except as
   in CRITICAL 1/2), and the two measured-only claims (§7 case 5 top-flat sharp
   form; §6(d)'s inclusion) are boxed as MEASURED with JC-BOX-4/JC-BOX-5. The
   boxed set is *smaller* than the set lacking proof only because of CRITICAL 1/2.

## §R RECOMMENDATION

Not clean. The J-C composition needs one structural repair, not a wording pass:
restate `(COORD)`, `(MULT)` and all of §2.10 on the **post-TC-1** pieces
`B_n = ∪_k in(π)^{-k}gr_{n+kE}` (where FGMN's `Δ ≅ K_m[y]` genuinely lives),
re-derive §3.1/§3.4/§5 from that, fix W-6(ii) and JC-PSIKER's closing sentence,
re-word `𝒜(T)`'s definition away from "degree-0 component" (and flag it as an
inherited-display correction, as JC-F1 is flagged), and re-cut JC-BOX-3 to box
*applicability* rather than literature truth. GAPs 3–8 are local: an added
census/violation branch for JC8's filtered constants, two data fixes (§7 row 1,
§3.4's 606), and three fence re-statements. Counter stays 0/2; PE2 should re-open
CRITICAL 1's repair first, since OB-4 / W-7 / JC-F1 all hang from it.

— GRTJC pass PE1, hostile verifier unit (fresh context), fixes nothing.
