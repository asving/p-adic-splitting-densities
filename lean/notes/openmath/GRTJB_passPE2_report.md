# GRTJB-PE2 — hostile verification pass on the post-r1 J-B tree-junction note

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` **at HEAD**, i.e. the
r0 note (composed 5a72b62, sealed 7f6759d, verdict f5578d0) **plus repair round
r1**: `4c97649` (r1 commit 1 — F1 re-fence at 4 sites + G-1..G-9 applied +
`grt_jb_printwalk.py` SEALED UNRUN + `grt_jb_r1_levelcensus.py` RUN) and
`46f9452` (r1 commit 2 — the printwalk verdict).
**Sealed runner:** `verification/openmath/grt_jb_checks.py`
(md5 `55f4911eaddd8524fd91368b30ed71bd`).
**New r1 instruments:** `verification/openmath/grt_jb_r1_levelcensus.py` ·
`verification/openmath/grt_jb_printwalk.py`.
**Verifier:** Fable, fresh context, read-only, fixes NOTHING. Genre:
quote-and-classify (CRITICAL ERROR = breaks the logical chain, stop checking
dependents; JUSTIFICATION GAP = assume the conclusion and keep verifying).
Pass date 2026-08-05 (wallclock). Prior pass **JB-PE1** (85a8dc9 — 1 CRITICAL +
9 gaps, NOT CLEAN) read in full before this pass; both r1 diffs read.

---

## §0. VERDICT

**0 CRITICAL, 7 JUSTIFICATION GAPS.**

    GRTJB-PE2 FINDINGS: 0 critical, 7 gaps / VERDICT: NOT CLEAN (F1 CURED)

**F1 (PE1's CRITICAL) IS CURED.** I grepped every occurrence of `VD-`,
`JA-RES`, `JA-VDIND`, `uncond` in the note and walked all 22 hits: the (VD-m)
perimeter now reads *unconditional at m ≤ 1 only; conditional at every m ≥ 2 on
JA-VDIND's absolute character-triviality (⊇ (R-coll)/JA-BOX-2 at m ≥ 3)*
consistently at **all** of the grade cap (L30–40), the §5 theorem parenthetical
(L538–550), the §5 grade line (L600–606), JB-BOX-2 (L640–649), §7.2's claims
row (L786), §7.1's census sentence (L734–748) and §7.3's consequence display
(L800–808). **No surviving sentence consumes (VD-2) or an m = 2 unconditional
stratum**; every remaining "unconditional at m = 2" is explicitly re-attributed
to the PER-SLOT law JA-RES with the non-transfer stated (L261–274, L112–113).
JB-EPS's separate unconditionality is intact and correct.

The seven gaps, most-severe first:

* **G2-1** — §7.2's claims table and §7.3's consequence display were re-fenced
  for F1 but **not** for G-9: JB-VTX still grades "at the W2-C1 representative"
  with no `qcap` perimeter, and §7.3 still supplies "W-3 **in full**" after the
  quantifier was narrowed from 0 ≤ q ≤ n to 0 ≤ q ≤ qcap. The grade surface
  downstream units read is the one PE1's G-9 named.
* **G2-2** — the new print-key walker's PW-XFRAME family is a **bit-identical
  re-execution of PW-DIV on 27 of its 72 walks** (the 9 rows with
  `chain_eq ∧ chat_eq`: identical multiplicand, identical divisor, same pure
  functions) — the exact defect G-1 diagnosed in the sealed leg, reproduced
  inside the instrument written to repair it, and undisclosed.
* **G2-3** — §7.4's boldface verdict "including on **every** junction the
  sealed battery left unchecked" is false: the sealed print-key leg also never
  ran on **8 chamber walks** (`T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2,
  `byteeq` false, 2 walks each), which the walker does not reach.
* **G2-4** — the (VD-2) failure geography is mis-characterised in NEW r1 text:
  "the e₀ ≥ 2 character-visible towers" and "exactly where
  A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses" are both **refuted by the note's
  own roster** (T3E has e₀ = 2 and scores 6/6; T3D and T3E share e₀ = 2, g₀ = 2
  and A_1 ≠ 0 yet split).
* **G2-5** — G-5's "discharge" of JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso is an
  assertion, not a derivation: nothing shows a level-m weight of a nonzero
  polynomial in the window satisfies J-A's sufficient bound
  V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}), and at small V that bound plainly fails.
* **G2-6** — §1's own definition of the shared-key perimeter (`for all j ≤ q`)
  contradicts the r1 text that cites it (`keys shared strictly below q`,
  `j < q`); the two differ by exactly the one level q = qcap on which the r1
  restatement rests.
* **G2-7** — census labelling: "scored 104 (**66 roster** + 38 chamber)" and
  r1's "**56 roster** rows" name the same census with the same word (66 =
  56 roster + 2 QO + 8 d₀); and "458 samples" for the walker counts 96
  bookkeeping-counter increments (law samples are 362).

Everything PE1 charged as G-2..G-9 was **applied, and applied correctly**
except as recorded in G2-1/G2-5/G2-6 above; each application was
re-verified numerically or verbatim against its source (§3). All three machine
legs reproduce **bit-identically** (§1).

---

## §1. MACHINE LEG (mandatory — all three runners RUN, exit 0)

Run from `verification/openmath/`, python3, no arguments, nothing edited; the
repo is byte-clean after the pass (`git status --short` shows only this report).

| runner | exit | reproduction vs committed artifact |
|---|---|---|
| `grt_jb_checks.py` (sealed) | **0** | `git diff verification/openmath/` after the re-run: **EMPTY** — the regenerated `grt_jb_checks_results.json` is byte-identical to the committed one, `elapsed_s` included (0.7 both times; PE1 saw 0.8) |
| `grt_jb_r1_levelcensus.py` | **0** | output identical to committed `grt_jb_r1_levelcensus_output.txt`, line for line, zero diff |
| `grt_jb_printwalk.py` | **0** | output identical to committed `grt_jb_printwalk_output.txt`, line for line; `_results.json` regenerated with no diff |

**Sealed-runner figures vs the note's §7.1** — 18/18 families GREEN, 0
violations, **6,700** samples, elapsed 0.7 s; per-family
1 / 893 / 25 / 893 / 893 / 34 / 79 / 194 / 955 / 28 / 79 / 5 / 4 / 2,480 and
teeth 3/3/3/3 all caught; censuses **scored 104 | boundary 21 | v=0 0 | R=0 0 |
off-perimeter tree rows 0**. Every figure the note quotes matches.

**Seal integrity at HEAD** (`git show <commit>:<path> | md5sum`):

    grt_jb_checks.py       55f4911eaddd8524fd91368b30ed71bd   at 4c97649 = 46f9452 = HEAD  ✓
    grt_jb_printwalk.py    f53e23e8d1c79f084a1e34eee857e37c   at 4c97649 = 46f9452 = HEAD  ✓
    grt_jb_r1_levelcensus  2bcb44fdbf839d367f0e11033a5d3fd7   at 4c97649 = 46f9452 = HEAD  ✓

The printwalk **mini two-commit seal HOLDS**: `git show --stat 4c97649` adds
`grt_jb_printwalk.py` **only** (no `_output.txt`, no `_results.json`), and
`46f9452` adds exactly those two artifacts plus the note's §7.4 — so the script
was on record before its artifacts existed, and its md5 is unchanged across
both commits and HEAD. The note's claim at L855–859 is accurate.

### 1.1 Derived figures recomputed by me from the committed sealed JSON

| §7.4 / §7.1 claim | my recount | verdict |
|---|---|---|
| walker COVERAGE prediction "79 = 16-tower roster 69 + QO leg 2 + d0 leg 8" | JSON `tree`: roster rows 15 towers / 23 (tower,m) rows / **69** walks · QO 1 row / **2** · d0 4 rows / **8** · chambers 15 rows / 46 | **EXACT** |
| "the 12 byte-unequal walks are exactly the sealed rows with byteeq = false: T3A m=2 (3) · T3C m=2 (3) · T3D m=2 (3) · T3E m=2 (3)" | JSON byteeq-false base rows: exactly `Zp,p=2,T3A m=2`, `Zp,p=3,T3C m=2`, `Fpt,p=2,T3D m=2`, `Zp,p=2,T3E m=2`, 3 walks each = 12 | **EXACT** — *but see G2-3: four CHAMBER rows are also byteeq-false* |
| coverage cause "+1 QO, +4 d0 because the sealed QO/d₀ legs use `small=True` (2 samples)" | `run_tower_families(..., small=True)` at both QO (L805) and d₀ (L829) legs; tree pool truncated by `fpool[:(2 if small else 3)]` (L754); walker uses `sample_pool(T, small=False)` and `[:3]` | **CONFIRMED** (1 QO row +1, 4 d₀ rows +4 = +5 → 84) |
| G-2 "22 samples across 14 distinct towers over 21 teeth-positive rows (14 base + 7 chamber); 15 base + 7 chamber" | teeth-positive rows 21 = 14 base + 7 chamber; samples 15 + 7 = 22; distinct towers **14** and the list matches the note's list element-for-element (I4B, JD3A, JD3C, JD5A, T2A, T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F) | **EXACT** |
| G-3 "q = 1 byte-equal on 22 of 25 rows, other 3 vacuous (T.n = 0)" | re-run byte census: `QO:x3-3/Q3 {}`, `QO:x4+2x2+2/Q2 {}`, `QO:x4-2/Q2 {}`; the other 22 all carry `"1": true` | **EXACT** |
| §7.1 "scored 104 (66 roster + 38 chamber), boundary 21" | scored: roster16 **56** + QO **2** + d0 **8** = 66 non-chamber, chamber **38**; boundary: roster16 **13** + QO 0 + d0 0 + chamber **8** = 21 | **arithmetically EXACT, labelling slip — G2-7** |
| boundary-positive rows | T3A 3 · T3B 3 · T3C 1 · T3D 3 · I4B 3 (base) · T3A/tw 2 · T3B/tw 2 · T3D/tw 2 · I4B/tw 2 (chamber). `T3C/tw` carries **none** | subset of the note's claimed set — **TRUE as stated** |
| walker PW-ID samples 38 | Σ over the 28 walker rows of m (20 rows at m=1, 6 at m=2 ⇒ 12, 2 at m=3 ⇒ 6) = **38** | **EXACT** |
| walker "458 samples" | law families 38+84+84+84+72 = **362**; +`PW-UNEQUAL-WALKS` 12 +`PW-CHAIN-DIVERGENT` 12 +`PW-XFRAME-AGREE` 72 = 458 | **inflated aggregate — G2-7** |

### 1.2 The level census, recounted independently — **13 = 0/10/3 and 56 = 45/8/3 CONFIRMED without touching `vd_eval`**

The sealed JSON's `cread` block is per-TOWER only, so the level split cannot be
read off it directly — which is the whole reason the r1 census exists. But it
**can** be *derived* from the sealed JSON alone plus one structural fact, with
no re-execution of the evaluator. Two sealed facts make this work: (i)
`run_tower_families` computes `fpool` once per (tower, m) and hands the *same*
list to `jb_tree` and `jb_cread`, so the JSON's per-(tower, m) `tree.walks` **is**
the per-(tower, m) cread sample count; (ii) `cread` records per-tower
scored/boundary/v0 totals. The structural fact is the one the note's own
re-fence keeps: **(VD-1) = W2-L3 is unconditional, so no m = 1 row can be a
boundary row.** Everything then forces:

    tower   levels (walks)   cread scored / bd     ⇒ forced per-level split
    T2A..G  {1:3} ×7          3 / 0  each           m1: 21 scored,  0 bd
    T3A     {1:3, 2:3}        3 / 3                 m1 3 sc ; m2 0 sc, 3 bd
    T3B     {1:3, 2:3}        3 / 3                 m1 3 sc ; m2 0 sc, 3 bd
    T3C     {1:3, 2:3}        5 / 1                 m1 3 sc ; m2 2 sc, 1 bd
    T3D     {1:3, 2:3}        3 / 3                 m1 3 sc ; m2 0 sc, 3 bd
    T3E     {1:3, 2:3}        6 / 0                 m1 3 sc ; m2 3 sc, 0 bd
    T3F     {1:3, 2:3}        6 / 0                 m1 3 sc ; m2 3 sc, 0 bd
    I4A     {1:3, 3:3}        6 / 0                 m1 3 sc ; m3 3 sc, 0 bd
    I4B     {1:3, 3:3}        3 / 3                 m1 3 sc ; m3 0 sc, 3 bd
    I4C     —                 —                     (no eligible level)

    ⇒ m=1: scored 45, boundary  0
      m=2: scored  8, boundary 10   (T3A 3, T3B 3, T3C 1, T3D 3)
      m=3: scored  3, boundary  3   (I4B 3)
      roster totals: scored 56, boundary 13

**Every one of the note's level figures is reproduced exactly**, including the
per-(tower, m) boundary table `T3A m=2: 3 · T3B m=2: 3 · T3C m=2: 1 ·
T3D m=2: 3 · I4B m=3: 3`. This derivation shares **no** code with
`vd_eval`/`grt_jb_r1_levelcensus.py` — it uses only the committed sealed JSON
and the unconditionality of (VD-1) — so F1's factual core now has a
decorrelated leg it did not have in PE1 or in r1. (The QO/d₀ rows carry 2
samples each at m = 1 only, 2 + 8 = 10 scored and 0 boundary, which is what
makes 66 = 56 + 10 — see G2-7.)

`R = 0: 0` and `v = 0: 0` are confirmed directly by my re-run of the sealed
runner (it prints both censuses). The split of the 13 boundary rows into
**scope-out vs eval-false** (0 / 13) is the one figure that exists only inside
`grt_jb_r1_levelcensus.py`; I verified it reproduces bit-identically and that
the branch order it replays matches `jb_cread` line for line (§2.3), but I did
**not** obtain it from a second instrument. A from-scratch loop of my own was
drafted for that purpose and **NOT RUN** (the sandbox refused Bash repeatedly
during this pass on the model-availability path); I record it as not-run rather
than claim it. The derivation above is what carries the level split
independently, and it does not need the scope-out/eval-false distinction.

---

## §2. THE FOUR CHARGED AUDITS

### 2.1 Charge (1) — is the new (VD-m) perimeter consistent at ALL sites?

**YES. F1 is cured.** I enumerated every hit of `VD-`, `JA-RES`, `JA-VDIND`,
`uncond` in the note (22 sites) and classified each:

| site | text | status |
|---|---|---|
| L16–19 grade cap, JB-DEV's residual layer | "the PER-SLOT law JA-RES unconditional at read level 2 … **which is NOT the evaluated dictionary (VD-2)**" | consistent |
| L30–40 grade cap, JB-CREAD | r0 struck; "**UNCONDITIONAL AT m ≤ 1 ONLY** … at every m ≥ 2 conditional on JA-VDIND's absolute character-triviality (⊇ (R-coll)/per-digit at m ≥ 3, JA-BOX-2)" | consistent |
| L40, L522, L785 JB-EPS | "unconditional" | correct and *separate* from (VD-m) |
| L112–119 r1 block F1 | per-slot vs evaluated split; "(VD-m) unconditional at m ≤ 1 only" | consistent |
| L255–259 §2(iii)(RES) | "unconditional at m = 2, per-digit proviso at m ≥ 3 **[JA-RES, consumed]**" | consistent (per-slot, source-attributed) |
| L261–274 §2(iii) new fence | "(RES)'s 'unconditional at m = 2' is a statement about JA-RES, the PER-SLOT … law. It does **NOT** transfer to the EVALUATED dictionary (VD-m)" | consistent — this is the missing fence, now present |
| L538–550 §5 theorem | r0 parenthetical struck; honest perimeter displayed | consistent |
| L600–606 §5 grade line | "(VD-m) is free only at m ≤ 1 … no unconditional stratum above m = 1" | consistent |
| L640–649 JB-BOX-2 | r0 "at m ≥ 3" struck; "the (VD-m) conditionality bites **from m = 2 UP**" | consistent |
| L734–748 §7.1 census | r0 "exactly the JA-BOX-2/(VD-m)-proviso geography" struck; level split displayed | consistent (but see G2-4) |
| L786 §7.2 claims row | "uncond. m ≤ 2" struck → "uncond. m ≤ 1 ONLY; CONDITIONAL at every m ≥ 2" | consistent |
| L800–808 §7.3 consequence | "free of extra hypotheses only at m = 1 … Downstream units that read 'unconditional at m ≤ 2' from r0 … must re-read this line" | consistent |

**No surviving sentence consumes (VD-2) or an m = 2 unconditional stratum.** The
one wording over-reach is L274 "**nothing above m = 1 is unconditional**",
which taken out of its (VD-m) bracket contradicts JB-EPS's own grade
("unconditional", every m ≥ 1); in context it plainly means "nothing
(VD-m)-dependent", so I record it as wording, not a finding.

### 2.2 Charge (2) — is the print-key walker genuinely independent?

**Code audit result: independent for LEG A; PARTLY VACUOUS for LEG B (G2-2).**

Confirmed independence properties (all verified in
`verification/openmath/grt_jb_printwalk.py`):

* `grep -n import` shows `iterlawn_pe_reimpl`, `grt_weld_probe`,
  `grt_ja_checks` and **nothing else** — `grt_jb_checks` is never imported, so
  `fresh_divmod` is never reachable. ✓ (contrast: the level census *does*
  import it, and says so).
* **keys** are `G.phi[...]` from `GWP.gmn_from_tower`'s own `_thm_phir`/
  `construct` recursion — the print chain, not `T.Phi`. ✓
* **correction digits** come from `print_corr`, which is literally
  `my_dev(φ_{i+2}, φ_{i+1})` — dividing print keys — with the (ID) grid
  structure checked in the same loop. No `realize`/`eps`/`psi` call anywhere in
  the walk. ✓
* **multiplicand** `Chat = P.sub(G.phi[m+2], P.pow(G.phi[m+1], G.e[m+1]))` —
  print keys and the print's own e. ✓ (the note displays it in harness indices
  as φ_{m+2} − φ_{m+1}^{e_m}; equal by the §1 dictionary).
* **divisor** `key = G.phi[m+1]`; **division** is the file's own `my_divmod`,
  a top-down Horner/running-remainder-window loop — **structurally distinct**
  from `fresh_divmod`'s in-place elimination loop and from
  `PolyO.divmod_monic`; every call certified by `cdivmod` (reassembly +
  degree bound), and PW-DIV additionally compares against `divmod_monic` as a
  third leg. ✓
* **scope** `print_elig` is computed from `G.f[m+1] == 1` and
  `G.f[0] == 1 or all(G.e[i+1] >= 2 …)` — print-side, no `qcap` cut. ✓ In fact
  the sealed run's off-perimeter counter is 0, so the two instruments cover the
  *same* level set; the walker claims no extra levels and none exist.
* the only harness inputs are `T.P`/`T.R` (ring arithmetic), the sample
  polynomials, the degree filter, and — in leg B — `T.Phi` and `Chat_har`.
  The docstring discloses all of these except the ring layer, which carries no
  key or division content.

**Coverage-note honesty (84 vs predicted 79): HONEST and mechanically
CONFIRMED.** The cause the note gives is exactly right: the sealed runner calls
`run_tower_families(..., small=True)` on its QO leg (L805) and d₀ leg (L829),
and the tree pool is cut by `fpool[:(2 if small else 3)]` (L754), while the
walker uses `sample_pool(T, small=False)` and `[:3]` uniformly. One QO tree row
(+1) and four d₀ rows (+4) ⇒ +5 ⇒ 84. Leg B likewise 67 → 72. The
mis-prediction is disclosed, in the direction of more evidence, with the cause
named. The one thing the note's phrasing hides is that `small` also changes the
pool *content* (`window_reps(T, 3 if small else 4)`, the `taus`/`db` ranges), so
the 5 extra walks are not a strict superset of the sealed ones — the counts are
right, the "walk-for-walk" gloss holds only on the roster rows (where both use
`small=False`). Too small to score separately; recorded here.

**Mini-seal: HOLDS** (§1 above). **Prediction accounting: the five law
predictions hit exactly (0/38, 0/84, 0/84, 0/84, 0/72), and the number G-1
turns on — 12 walks at byte-unequal junctions — hit its prediction on the nose
and is GREEN.** That much of §7.4 is real evidence and it does close the
substance of G-1 on the base rows.

### 2.3 Charge (3) — the level census's 13/10/3 split

*(numeric recount at §1.2; logic audit here.)* `cread_levelkeyed` replays
`jb_cread`'s branch order **exactly**: `R = 0` → `v = 0` → `vdf is None`
(scope-out) → `not vdf` → `vdR is None` → `not vdR` → SCORED, with the sealed
runner's single `vdf is None or not vdf` bucket *split* into two so the
scope-out count is separable. Same towers (`GWP.TOWERS`), same pool
(`sample_pool(T, small=False)`), same `elig_ms`/`qcap_of` cuts, same `[:3]`
truncation, same `chat_of`/`fresh_divmod`/`vd_eval`. It is therefore a faithful
re-keying, **not** an independent evaluation: `vd_eval`'s faithfulness as an
evaluator of (VD-m) is shared with the sealed runner and is nowhere
decorrelated. Since F1's conclusion is a *retraction* (more conditionality),
the shared-evaluator risk points the safe way, and the note discloses the
import ("imports the sealed runner verbatim"). Two decorrelated consistency
checks do hold: **m = 1 boundary = 0** (as (VD-1) = W2-L3 unconditional
demands), and the per-tower boundary totals match the sealed JSON exactly.

### 2.4 Charge (4) — were G-2..G-9 applied, and correctly?

| PE1 gap | applied at | correct? |
|---|---|---|
| **G-1** print-key leg | §4 machine bracket L474–484 + §7.1 table row L721, plus the whole §7.4(B) walker | **YES** — the corrected wording states precisely what `fresh_divmod`-on-equal-tuples establishes. (The r1 commit message also claims a "§4 grade line" edit; §4's grade line contains no print-key claim, so there was nothing there to fix — message imprecision only.) |
| **G-2** 14 towers | §7.1 L766–772 | **YES, EXACT** — 14 towers, list element-for-element, 21 rows = 14+7, 22 = 15+7 (§1.1) |
| **G-3** 22 of 25 | §7.1 L717 | **YES, EXACT**, with the vacuity mechanism (`range(1, T.n+1)`, `cen.get(1, True)`) quoted correctly |
| **G-4** JB-VTX(e) subject | §3(e) L372–384 | **YES** — subject moved to Φ_{q+1}^har, whose Φ_q-development *is* one-sided on i ≤ e_q g_q with support {0, e_q g_q} ∪ grid slots; and the proof line L389 now reads "(e) W2-C1a consumed at f = Φ_{q+1}^har" |
| **G-5** JA-GRID(a) proviso | §2(iii) L276–285 + JB-BOX-2 L652–660 | **NAMED, NOT DISCHARGED — G2-5** |
| **G-6** 12 shared junctions | §7.1 L750–760 | **YES, and the arithmetic closes**: probe F1 walks r = 3..NR+1 (30 junctions over 21 rows); `jb_keyeq` walks q = 1..T.n ⇒ r = 2..NR; overlap r ∈ [3, NR] = 6 (T3× at r=3) + 6 (I4× at r=3,4) = **12**; top junctions r = NR+1 = 16 on the 16 towers + 2 on the two QO rows with T.n = 1 ⇒ 12 + 16 + 2 = **30** ✓ |
| **G-7** three symbols | m_{q+1}^GMN L214–220; (B-READ) L573–578; s_m split L503–520 | **YES, all three, and all three check against source.** deg φ_{q+1} = d₀·∏_{j<q} e_j g_j is exactly the print recursion under the P-index dictionary ✓. (B-READ) is verbatim [RMG] `**Lemma L-CELL** … (ii) [B-READ]` (RMENGINE line 419/422) ✓, and the inequality step is sound in both cases of β* vs w_m(R) ✓. The s_m^wt/s_m^ini split is used consistently: JB-EPS and ε′ are stated with s^wt only (weight arguments), (VD-m)/τ_m with s^ini, and no step of §5 mixes them ✓ |
| **G-8** T-F + seal erratum | §1 L198–206 + §7.1 L698–711 | **YES** — instrument re-attributed to the O1thr rev-3 runner, and the erratum states the immutable-message problem and the seal property that does hold |
| **G-9** qcap quantifiers | §2(iii) L240–249, JB-VTX theorem L321–329, JB-VTX grade L390–398, JB-BOX-2 L661–664, grade cap L16–24 | **PARTLY.** The `qcap` formula and range are **exactly** the runner's: `qcap_of(T,G) = min(T.n, GJA.shared_upto(T,G) + 1)` with docstring "keys shared **strictly below** q", and every family loops `for q in range(0, qcap_of(T,G) + 1)` i.e. **0 ≤ q ≤ qcap** ✓; and the note's extra claim that the (d) print-side min ties are further restricted to q ≤ `shared_upto` is exactly the `if q <= L:` guard around `minU != G.vgen(q+1,f)` in `jb_shear_vtx` ✓. **But** §7.2/§7.3 were not re-fenced (**G2-1**) and §1's own perimeter definition contradicts the restatement (**G2-6**). |

---

## §3. FINDINGS

### G2-1 — JUSTIFICATION GAP (grade surface). G-9's re-fence never reached §7.2 or §7.3; the claims table still grades JB-VTX with no `qcap` perimeter and the consequence display still supplies "W-3 in full"

The r1 round re-fenced F1 at **six** surfaces including §7.2's claims row and
§7.3's consequence display. G-9 was re-fenced at **five** body surfaces and at
**neither** of those two. §7.2 (line 783) still reads verbatim:

> | JB-VTX | window/development polygon = Σ_q(N_{q+1}(f)) vertex-for-vertex;
> slope/length translation; min/read ties; window clause | PROVED (attempt
> grade), **at the W2-C1 representative** |

and line 781 grades JB-DEV "PROVED (attempt grade 0/2), consumptions at their
own grades" with no mention of the shared-key perimeter, although the note's own
§2(iii) now says of that clause's (VAL) layer: "Off that perimeter the print
frame is computed with keys that differ from Φ_0..Φ_{q−1}, and (VAL) is then
**FALSE, not merely unproved**." PE1's G-9 was stated as exactly this defect:
"the theorem-level display **and the grade line** name only W-2 clause 1".

§7.3 (line 792) then says:

> **What J-B now supplies (at attempt grade, hostile passes owed):** the
> blueprint's **W-3 in full** (expansion + polygon identities, shear explicit)

after JB-VTX's quantifier was narrowed from 0 ≤ q ≤ n to 0 ≤ q ≤ qcap and
JB-DEV(iii)'s to q ≤ qcap. §7.3 carries a fresh `[r1, F1]` bracket for
(C-READ) — so the composer did revisit this paragraph — and added nothing for
G-9. A downstream unit that reads §7.2/§7.3 alone (which is what a claims table
and a consequence display are *for*) gets the pre-G-9 perimeter back. Mitigation:
"in full" is ambiguous between "both halves of W-3" and "at every q", and the
narrower reading is displayed in the body and in the grade cap. Classification:
gap, not critical — but it is the same grade-surface/body divergence that made
F1 critical, so it is the finding a repair should take first.

### G2-2 — JUSTIFICATION GAP (machine evidence). PW-XFRAME is a bit-identical re-execution of PW-DIV on 27 of its 72 walks — the very defect G-1 named, reproduced inside the repair instrument

`grt_jb_printwalk.py` gates leg B on `chain_eq` alone (lines 373–376):

    if not chain_eq:
        row['frames_differ'] += 1 ; ... ; continue
    note('PW-XFRAME') ; row['xframe_rows'] += 1
    wkh = pwalk(T, G, m, f, Chat_har, Pl, corr, tag)
    ...
    Qh, Rh = cdivmod(P, R, fCh, tuple(T.Phi[m]), tag, fam='PW-XFRAME')

`chain_eq` is `all(T.Phi[j] == G.phi[j+1] for j in range(0, m+1))`, which at
j = m gives `tuple(T.Phi[m]) == key`. So on any leg-B row the **divisor is
byte-equal to the print key**. On the subset where additionally
`chat_eq` (i.e. `Chat == Chat_har`) the leg-B call is
`pwalk(..., Chat_har, ...)` with arguments **byte-equal** to leg A's
`pwalk(..., Chat, ...)`, and `cdivmod(fCh, T.Phi[m])` with arguments byte-equal
to leg A's `cdivmod(fC, key)`. `pwalk`/`my_divmod` are deterministic functions of
those arguments, so PW-XFRAME on those rows **cannot fail unless PW-DIV
already did** — precisely G-1's diagnosis, transplanted.

Counted from the committed `grt_jb_printwalk_results.json`, the rows with
`chain_eq: true` **and** `chat_eq: true` are

    Zp,p=3,T2B|m=1 · Zp,p=2,T2E|m=1 · Fpt,p=3,T2F|m=1 · Zp,p=3,T3B|m=1 ·
    Zp,p=3,T3F|m=1 · Zp,p=2,I4A|m=1 · Zp,p=2,I4A|m=3 · Zp,p=3,I4B|m=1 ·
    QO:x4+4x+4/Q2|m=1                                     — 9 rows × 3 = 27 walks

so **27 of the 72 PW-XFRAME samples carry no content beyond PW-DIV**; the
remaining 45 (chain-equal, `chat_eq: false`) do carry content — the print-keyed
tree on a genuinely different multiplicand Ĉ_m^har. The docstring's own smoke
disclosure shows the author was alert to this failure mode ("the first draft
gated the cross-frame family on (chain byte-equal through m) AND
(Chat^cls == Chat^har), which fired on ZERO smoke rows — a vacuous check,
exactly the disease G-1 reports"); the re-gating *dropped* the `chat_eq`
conjunct instead of **negating** it, which admits the vacuous subset rather
than excluding it. Neither the script nor §7.4 discloses the 27/45 split, and
§7.4's table advertises PW-XFRAME at 72 samples. LEG A (84 walks, all five law
predictions green) is unaffected and is the evidence that actually closes G-1's
substance.

### G2-3 — JUSTIFICATION GAP (coverage over-claim in transcription). "including on every junction the sealed battery left unchecked" is false: eight byte-unequal CHAMBER walks are unchecked by both instruments

§7.4's boldface verdict (lines 861–864):

> **VERDICT (r1 commit 2, transcribed from `grt_jb_printwalk_output.txt`;
> exit 0, elapsed 0.1 s, 458 samples, seal commit 4c97649):
> ALL FIVE FAMILIES GREEN — the print-key tree identity HOLDS at print keys,
> including on every junction the sealed battery left unchecked.**

The sealed `tree` block's `byteeq: false` entries are **eight**, not four:

    Zp,p=2,T3A    m=2  3 walks      Zp,p=2,T3A/tw   m=2  2 walks   CHAMBER
    Zp,p=3,T3C    m=2  3 walks      Zp,p=3,T3C/tw   m=2  2 walks   CHAMBER
    Fpt,p=2,T3D   m=2  3 walks      Fpt,p=2,T3D/tw  m=2  2 walks   CHAMBER
    Zp,p=2,T3E    m=2  3 walks      Zp,p=2,T3E/tw   m=2  2 walks   CHAMBER

The walker's `main()` iterates `GWP.TOWERS` + the QO shapes + `GJA.D0_SPECS`
and builds **no chambers**, so the 8 chamber walks at byte-unequal junctions are
print-unchecked by the sealed leg *and* by the walker. Note that the script's
own verdict string is honest — "including **off the byte-equal set**" — and the
note escalated it to "every junction" while calling the line "transcribed
from" that output. The note does disclose the chamber exclusion 40 lines later
("It does NOT buy: … any claim about chambers (the walker runs the base rows
only)"), so the note contains both the over-claim and its correction; the
boldface verdict is the sentence a downstream reader quotes.

### G2-4 — JUSTIFICATION GAP (mechanism claim refuted by the note's own roster). The (VD-2) failure set is NOT "the e₀ ≥ 2 character-visible towers", and it is NOT "exactly where A_{m−1} collapses"

Two NEW r1 sentences characterise the m = 2 boundary geography. §5, line 550:

> on the sealed roster (VD-2) is machine-evaluated FALSE at 10 of 13 boundary
> rows (T3A/T3B/T3C/T3D — **the e₀ ≥ 2 character-visible towers**)

and §7.1, lines 743–746:

> the geography is the JA-VDIND COLLAPSE BOUNDARY at m = 2 (the e₀ ≥ 2 towers
> with a nontrivial z₁: T3A e = 2,2,2; T3B e = 3,2,2; T3C e = 2,3,2; T3D
> F₂[[t]] e = 2,2,2 — while the level-flat T3 rows T3E (e₁ = 1) and T3F
> (e₀ = 1) score 6/6, **exactly where A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1}
> collapses**)

The e-vectors are correct, but both characterisations are refuted by the
roster the note is describing (printed from `GWP.TOWERS` / `ITL.build_tower`):

    T3A  Zp  p=2  e=[2,2,2] h=[1,1,1] g=[1,1,1] d0=2     boundary at m=2
    T3B  Zp  p=3  e=[3,2,2] h=[1,1,1] g=[1,1,1] d0=1     boundary at m=2
    T3C  Zp  p=3  e=[2,3,2] h=[1,2,1] g=[1,1,1] d0=1     boundary at m=2
    T3D  Fpt p=2  e=[2,2,2] h=[1,1,1] g=[2,1,1] d0=1     boundary at m=2
    T3E  Zp  p=2  e=[2,1,2] h=[1,1,3] g=[2,1,1] d0=1     SCORES 6/6
    T3F  Zp  p=3  e=[1,3,2] h=[2,1,1] g=[2,1,1] d0=1     SCORES 6/6

* **T3E has e₀ = 2**, so "the e₀ ≥ 2 towers" is not the failure set: e₀ ≥ 2
  holds on five of the six T3 towers and only four fail.
* At m = 2 the note's own sufficient condition for collapse is
  "A_{m−1} = 0, i.e. e_{m−2} = 1", i.e. **A_1 = ℓ₀g₀γ₁ = 0 iff e₀ = 1**. That
  holds only for T3F. **T3D and T3E have the same (e₀, g₀) = (2, 2)** and hence
  the same nonzero A_1 shape, yet T3D fails and T3E scores. So "exactly where
  A_{m−1} collapses" is false as a characterisation of the scoring set; the
  actual discriminator must be the *order* of z₁ against A_1 (or the abscissa
  condition), which the note asserts nowhere and the machine does not report.

Consequence: F1's factual core survives untouched (it rests on the census, not
the mechanism), but the note's explanation of *why* the boundary sits where it
does is an unsupported causal claim presented as established — "the geography
**is** the JA-VDIND COLLAPSE BOUNDARY … exactly where …". A consumer using it
to predict which towers are free at m = 2 would be misled. (PE1 made the same
attribution; it is in the note at HEAD, so it scores here.)

### G2-5 — JUSTIFICATION GAP. G-5's "discharge" of the JA-GRID(a) `[JA-r1]` proviso is an assertion, and its stated bound fails in exactly the small-V regime the proviso exists for

The note claims a discharge twice — §2(iii) L276–285 and JB-BOX-2 L652–660:

> It is now named in JB-BOX-2 **with its discharge**: at every consumption site
> here the argument V is a level-m weight of a nonzero polynomial in the tower's
> own window, so V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) — J-A's own hypothesis for
> u ≥ 0 — and the runner's `s_geo` leg recomputes s from the geometry with no ℓ
> at all.

J-A's own text (`GRTJA_PROOF_2026-08-08.md` L197–201) is:

> Fix a read (e, h), gcd(e, h) = 1, h, e ≥ 1, and V ∈ ℤ_{≥0} with
> u := (V − s·h)/e ≥ 0 — the proviso holds at every consumption site by the
> print's own hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) (tex 1167–1168); for
> small V off it the print-side T has no such point (e.g. (e,h) = (2,3),
> V = 1 ⟹ u = −1).

J-A grounds the bound in the *print's* hypothesis at the site where `construct`
is invoked. J-B replaces that by an implication of its own — "V is a level-m
weight of a nonzero polynomial in the tower's own window **so**
V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})" — and supplies no argument for it. It is not
plausible as stated: §2's own quantifier is "f ∈ O[x] nonzero" and §4/§5's is
"deg f < deg Φ_m", both of which admit units, whose level-m weight is 0, while
e_{r−1}f_{r−1}v_r(φ_{r−1}) is positive at r ≥ 2. (At V = 0 one still gets
u = 0 ≥ 0, so no counterexample to the *proviso* is exhibited here — but the
note's *route* to it is broken, and the small positive weights that J-A's own
counterexample (e,h) = (2,3), V = 1 lives at are not excluded by anything the
note says.) The `s_geo` remark is a red herring: `s_geo` computes s
geometrically, which is precisely the "unconditionally-true integer-ordinate
characterization" J-A says its machine leg checks — it does not certify u ≥ 0.
So the honest status is **named in a box, not discharged**; G-5 was reported to
Asvin's ledger as "now named in JB-BOX-2 with its discharge argument".

### G2-6 — JUSTIFICATION GAP (definition). §1's "shared-key perimeter at level q" (j ≤ q) is not the perimeter the r1 restatement cites it as (j < q), and the two differ by exactly the level the restatement rests on

§1, line 182 (untouched by r1):

> **Shared-key perimeter at level q**: Φ_j^har = φ_{j+1}^cls byte-for-byte for
> all **j ≤ q**.

The r1 restatements, §2(iii) L243–244 and the JB-VTX theorem L322–324:

> levels q with Φ_j^har = φ_{j+1}^cls byte-for-byte for all **j < q**, i.e.
> q ≤ qcap := min(n, shared_upto + 1) — the runner's own `qcap_of(T, G)`
> quantifier

> 0 ≤ q ≤ qcap, where qcap := min(n, shared_upto + 1) is **the SHARED-KEY
> perimeter of §1** (keys shared **strictly below** q)

The runner side is unambiguous and agrees with the *second* reading:
`shared_upto` is "max L ≥ 0 with Φ_q == φ_{q+1} for all 1 ≤ q ≤ L"
(`grt_ja_checks.py` L155–156), `qcap_of` returns `min(T.n, shared_upto + 1)`
with docstring "keys shared **strictly below** q", and the loops run
`range(0, qcap+1)`. So q = qcap = L+1 is in scope, and at that q the keys are
**not** shared at j = q — i.e. q = qcap is *outside* §1's own perimeter. The
theorem therefore cites §1 for a set §1 does not define, and the discrepancy is
not decorative: it is exactly the one level (the first divergence) whose
inclusion is the whole point of `+1`. Either §1's definition should have been
split (perimeter *through* q vs *below* q) or the theorem should not have said
"of §1".

### G2-7 — JUSTIFICATION GAP (record/labelling), two items

* **"66 roster" vs "56 roster".** §7.1 line 731 (r0, retained) says JB-CREAD
  "**scored 104 (66 roster + 38 chamber)**"; the r1 bracket 10 lines later says
  "Scored: **56 roster** rows at m = 1: 45, m = 2: 8, m = 3: 3". Recount from
  the committed JSON: non-chamber scored 66 = **roster-16 towers 56 + QO 2 +
  d₀ 8**. Both numbers are right; the word "roster" means two different things
  within one paragraph, and nothing in the note says the 66 includes the QO and
  d₀ legs. The same conflation is printed by the level census itself
  ("non-chamber boundary 13 (16-tower roster part 13)" — equal only because QO
  and d₀ contribute 0 boundary rows, which the note does not state).
* **"458 samples".** §7.4's verdict line quotes 458 as the walker's sample
  count. `TOTAL samples` is `sum(COUNTS.values())`, which adds the three
  coverage counters `PW-UNEQUAL-WALKS` (12), `PW-CHAIN-DIVERGENT` (12) and
  `PW-XFRAME-AGREE` (72) to the five law families (38+84+84+84+72 = **362**).
  So 96 of the 458 are bookkeeping increments, not law checks. The per-family
  table in §7.4 discloses the real counts, so this is a headline-figure
  inflation only.

---

## §4. CHECKED AND CLEAN (so this pass's coverage is auditable)

* **F1's cure is complete and the retraction is honest**, including the parts
  that hurt: "JB-CREAD has **NO** unconditional stratum above m = 1" appears
  four times, r0's wrong text is struck rather than deleted at every site, and
  §7.3 explicitly tells downstream consumers ("the W-5 row; the J-C germ of §5's
  remark; the weld ledger's J-B entry") that they must re-read the line. The
  §5 remark's germ ρ_m(R) = −z_{m+1}·ρ_m(f) is correctly said to keep its form
  and inherit the conditionality.
* **No §2–§5 identity moved in r1.** I diffed the mathematical content:
  JB-EPS's two displayed lines, JB-CREAD's five-line chain, JB-VTX(a)–(d),
  JB-DEV(i)–(iv), JB-AFF and JB-TREE(i)–(iv) are unchanged apart from the
  s_m^wt/s_m^ini renaming (which changes no value: s^wt is what JB-EPS always
  meant, being (ℓV) mod e = the runner's `s_geo`). PE1's four surviving
  re-derivations are therefore still the current text's, and I re-checked the
  two load-bearing ones: the ε′ telescope (only ℤ-linearity of ℓ·(·) plus
  JA-GRID(c), which J-A grades PROVED/unconditional and whose proof — three
  s-values in [0,e) congruent mod e — I re-derived) and the ε-cancellation
  ε(λ+γ)ε(λ)^{−1}ε(γ)^{−1} = z^{−ε′} against z^{+ε′} from (C-READ).
* **G-7's three definitions all check against source** (§2.4 table): the key
  degree recursion, (B-READ) = L-CELL(ii) verbatim in RMENGINE, and the s_m
  split, whose "differ by ν·e_{m−1}" claim matches J-A's own s₀ = s(β) + νe.
* **The (B-READ) step is sound under either reading of L-CELL(ii)'s
  β* ≤ w_m(x) hypothesis**: if λ+γ_{m+1} ≤ w_m(R) the lemma applies and gives a
  cell at that line, so w_m(R) ≤ λ+γ_{m+1} by clause (i); if
  λ+γ_{m+1} > w_m(R) the desired inequality is immediate. So the step does not
  depend on resolving the hypothesis direction.
* **The level census is a faithful re-keying of `jb_cread`** (branch order,
  towers, pool, cuts, evaluator all identical; the `vdf is None or not vdf`
  bucket split into scope-out vs eval-false), it reproduces bit-identically, and
  its reason split (R EVAL-FALSE 10 / f EVAL-FALSE 3 / SCOPE-OUTS 0) is
  arithmetically consistent with its own per-tower table.
* **The printwalk's LEG A is real, decorrelated evidence** (§2.2): print keys,
  print correction digits by dividing print keys, print multiplicand, print
  divisor, own certified Horner division, third leg against
  `PolyO.divmod_monic`, sealed runner never imported. Its 12 byte-unequal walks
  are exactly the sealed base rows with `byteeq: false` and they are GREEN — so
  G-1's substance *is* closed on the base rows, which the note claims and I
  confirm.
* **The build-phase smoke disclosure is exemplary honesty**: the note's
  instrument discloses a pre-seal reduced run, its scale (T2A+T3A, 9 walks), and
  the one design defect it caught (a vacuous first cross-frame gating) — the
  disclosure is what let me find G2-2 quickly.
* **`I4C` as the scope fence, from both sides**: `elig_ms(I4C) = []` in the
  sealed runner and `print_elig(I4C) = []` in the walker (computed from `G.f`,
  `G.e`), so its absence from both artifacts is a fence firing, not a silent
  drop; the sealed off-perimeter counter is 0, so no eligible level was skipped
  anywhere and the walker's "no qcap cut" bought no extra levels (and it claims
  none).
* **G-8's seal erratum is the right shape**: it states the immutable-message
  defect, then states the seal property that does hold, and both halves check
  (`git show --stat 7f6759d` = runner only; predictions in prose at 5a72b62;
  md5 frozen seal→verdict→HEAD).
* **Grade-cap and acceptance-counter honesty**: "attempt grade, acceptance
  counter 0/2, ONE hostile pass RUN … r1 applied; the next acceptance attempt is
  a fresh hostile pass" is consistent at all four places it appears (L8–11,
  L168–171, L689, L906–907); "a repair round is not a pass" is stated
  explicitly; §7.3's NOT-supplied list is unchanged and accurate; no gr/carrier
  or density claim appears; the r1 block correctly labels both new instruments
  "POST-SEAL SUPPLEMENTARY … evidence for a REPAIR, not sealed predictions".
* **No stale machine quote anywhere.** Every figure in §7.1/§7.4 that I could
  recount (23 of them, §1.1) reproduces, and the two coverage mis-predictions
  are disclosed as mis-predictions with the cause named.

---

## §5. WHAT A REPAIR WOULD HAVE TO DO (for the composer, not this verifier)

1. **G2-1** — carry the `qcap` perimeter into §7.2's JB-VTX and JB-DEV rows and
   into §7.3's "W-3 in full" (one clause each).
2. **G2-2** — either re-gate PW-XFRAME on `chain_eq ∧ ¬chat_eq` (which is what
   makes it cross-frame) or report it as "72 walks, of which 45 carry a
   multiplicand the print frame does not supply and 27 are a re-execution of
   PW-DIV". This is a *disclosure* fix; no result changes.
3. **G2-3** — replace "every junction the sealed battery left unchecked" with the
   script's own "off the byte-equal set (base rows)", and name the 8 chamber
   walks still print-unchecked.
4. **G2-4** — downgrade the geography sentences to what the machine shows
   (which towers, which levels) and drop the "e₀ ≥ 2" / "exactly where A_{m−1}
   collapses" mechanism, or supply the z₁-order computation that separates T3D
   from T3E.
5. **G2-5** — either derive the u ≥ 0 bound at J-B's own consumption sites or
   downgrade JB-BOX-2's wording from "with its discharge" to "carried, discharge
   owed".
6. **G2-6** — split §1's definition (perimeter *through* q vs *strictly below*
   q) and point the theorem at the right one.
7. **G2-7** — say "non-chamber 66 = roster 56 + QO 2 + d₀ 8", and quote the
   walker's law-sample total (362) rather than 458.

---

## §6. Divergences from JB-PE1 (read before this pass, judged independently)

* **PE1's F1 is CURED**; I confirm its factual core independently (§1.2) and I
  confirm its four charged re-derivations still stand in the post-r1 text.
* **PE1's G-1 is closed on the base rows** by real evidence — but PE1's own
  diagnosis recurs inside the repair instrument (G2-2), which PE1 could not have
  seen (the walker did not exist).
* **PE1's G-6 arithmetic, which I initially suspected** (12 shared + 16 top = 28
  vs 30 walked), **closes**: the two remaining F1 junctions are the top
  junctions of the two QO rows with `T.n = 1`, and "16 **roster** F1 junctions"
  correctly counts the 16 towers only. No finding.
* **PE1's G-2/G-3/G-8 corrections are exact** and I re-derived all their numbers
  from the committed JSON rather than from PE1.
* **New in this pass** (PE1 did not raise them): G2-1 (G-9 not carried to the
  claims table / consequence display), G2-2, G2-3, G2-4, G2-5, G2-6, G2-7.
* **PE1's own §1.3 mechanism gloss** ("precisely where A_{m−1} =
  ℓ_{m−2}g_{m−2}γ_{m−1} collapses") was imported into the note by r1 and is
  **refuted by the roster** (G2-4). This is a case of a verifier's unforced
  explanatory claim becoming note text; the repair should not treat PE1 as a
  source.
* **PE1's md5-vs-`elapsed_s` caution is worth revising**: my sealed re-run
  produced a JSON with **zero** diff (elapsed 0.7 both times), so the artifact
  *can* regenerate md5-identically on this machine; the honest formula is
  "identical, `elapsed_s` timing-dependent", which is what PE1 recommended.

---

## §7. Pass hygiene

Nothing was edited: the sealed runner, both r1 instruments, all committed
artifacts and the note are byte-untouched (`git status --short` shows only this
report and another agent's in-flight `GRTJC_PROOF_2026-08-08.md`, which this
pass never read, touched or staged). Only `verification/openmath/__pycache__`
was written by the interpreter, and the three re-runs left every committed
artifact byte-identical, so `git diff` on `verification/` is empty.

One leg is **NOT RUN** and is marked as such above: my own from-scratch
level-keyed loop (§1.2). It was blocked repeatedly by the sandbox's
model-availability refusal path, not by a permission denial; the level split it
would have re-confirmed is instead carried by the JSON-only derivation of §1.2,
which is strictly more decorrelated (it does not call `vd_eval` at all).

— GRTJB-PE2, Fable, fresh context, 2026-08-05. Acceptance counter for the note
remains **0/2**: this pass returns findings, so it is not a clean pass.
