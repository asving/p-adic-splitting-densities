# LIFTCORNER passPE3 — hostile verification report (fresh context, post-r2; FIRST ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD**, i.e.
including repair round **r1** (commit b2dc120, the lexicographic (m, deg a)
descent that cured PE1's F1 CRITICAL) and repair round **r2** (commits a3112dc
= generator assertion A7 + regenerated table, e5b3faf = the note's five
[r2, G#] strike-and-replace brackets).
**Arc read:** `LIFTCORNER_passPE1_report.md` (30e570c, 1 CRITICAL + 3 gaps),
`LIFTCORNER_passPE2_report.md` (3367f3c, 0 CRITICAL + 5 gaps), and both repair
diffs (`git show b2dc120`, `git show a3112dc`, `git show e5b3faf`).
**Machine legs:** (a) sealed runner `verification/openmath/liftcorner_checks.py`;
(b) post-hoc children generator
`verification/openmath/liftcorner_tailstab_children.py` + its committed table.
**Charge:** quote-and-classify, fix nothing; honesty defects graded (claims
stronger than evidence, stale machine quotes, un-superseded refuted text,
misattributed verification credit); fences and honest boxes read as part of the
statement. As the third hostile reader I was directed at the veins nobody has
mined: **S2/S3** (measurement design + corner statement), the **(TAIL-STAB)
interface** between r1's proof and its original downstream consumers, the **r2
patches themselves**, and the **S5/grade-box arithmetic of the whole arc**.

**VERDICT: 0 CRITICAL ERRORS / 5 JUSTIFICATION GAPS.**

The mathematics holds. I re-derived, independently and from scratch: all eight
per-digit ω-gain bounds of the (A) table (including rows 3 and 7b as instructed);
the 2e₀+3 branching arithmetic and its parenthetical; the counter-instance's two
expansion passes and its independent double-development tie
(xΦ₀² = (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) — I re-multiplied it, exact); the whole
S2 applicability arithmetic (16 twistable instances → 48 twisted towers → 56
gate checks → 656 AV / 4,176 pair / 3,816 WRONGLET counts, and 25,409 as their
sum); and the (TAIL-STAB) consumer interface at every downstream site. Both
machine legs are clean: the sealed runner is byte-untouched with the claimed
md5, exits 0 at 25,409/0; the children generator regenerates its committed
table **byte-identically** and all four A7 legs pass (752 nodes / 5,336
children / 0 / 0 / 0 / 0).

The five gaps, in severity order: one **machine-assertion honesty defect on
exactly the clause r1's F4 repair produced** — the ψ₁-carryover assert the note
promotes as the substantive leg is a tautology on one object and cannot fail
(§2 F-A, source-verified); one **non-realizable displayed witness** for r2's
G4 strike (§2 F-B); one **overstated machine quote attributed to PE2**, whose
own report explicitly carried the qualification the note drops (§2 F-C); one
**internal inconsistency in the r2 grade-box/status-line accounting** of what
PE2 audited (§2 F-D); and one **vacuous prediction family** reported as a
result (§2 F-E). None breaks the chain, and none touches the (TAIL-STAB) proof
or the S3 measurement. Three of the five land in the veins nobody had mined —
S2's disclosure (c), the r2 patches' own justifications, and the arc's grade
accounting; A7 itself does exactly what the note says it does, and I
spot-audited its leg (i) against source (§1(b′)).

---

## 1. Machine legs (mandatory, two parts) — BOTH RUN, BOTH CLEAN

### (a) The SEALED runner — exit 0, seal intact, byte-untouched

```
$ md5sum verification/openmath/liftcorner_checks.py
ccb4351c92573f5f962cae4ae952d8dd     <- = the note's S3/header claim (2 sites)
$ git diff dafc0b5 HEAD -- verification/openmath/liftcorner_checks.py | wc -c
0                                    <- 0-byte diff vs the seal commit
$ git show dafc0b5:verification/openmath/liftcorner_checks.py | md5sum
ccb4351c92573f5f962cae4ae952d8dd     <- md5 at the seal == md5 at HEAD
$ python3 liftcorner_checks.py ; echo EXIT=$?
... VERDICT: ALL GREEN ... TOTAL checks 25409  elapsed 4.3s ... EXIT=0
```

Family table from my re-run: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 ·
INT 0/4176 · LOC 0/0 · CHI 0/4176 · COV 0/0 · WRONGLET 0/3816 · TRS 0/4176 ·
ENGGATE 0/1 · CERT 0 (internal T1/T2(nf=4)+T5) · WRONGLET total fires 1576 ·
gate-passed 56 · coverage min d1-pairs 6 · teeth min 6.

**Every S3 figure in the note matches** these observations. **No stale machine
quotes in S3** (the one wording defect I do raise, F-C, is about how the note
describes PE2's *re-run*, not about S3's own figures).

**Independent count re-derivation (my own leg, not read off the runner).** From
the S2 roster (rows CA–CF, E₂ ∈ {4,6,8,6,10,3}, d₀ = 2 on CB/CD only; rings
{ℤ₂,ℤ₃,F₂[[t]],F₃[[t]]}):

| figure | my derivation | verdict |
|---|---|---|
| 16 twistable (ring,row) | twists exist iff \|K₀\| = p^{d₀} > 2: d₀=2 rows × 4 rings = 8, plus d₀=1 rows × p=3 rings = 8 → **16** | MATCH |
| 48 twisted towers | d₀=2: 2 rows×4 rings×2 draws×2 variants = 32; d₀=1: 4 rows×2 rings×1 draw×2 variants = 16 → **48** | MATCH |
| 56 GATE | 48 twisted + (CB,CF)×4 rings ξ=1 dense controls = 8 → **56** | MATCH |
| 656 AV (2E₂ per tower) | twisted 384+200 = 584; controls 48+24 = 72 → **656** | MATCH |
| 4,176 pairs (2E₂² per tower) | twisted 1152+1152+128+512+800+72 = 3,816; controls 288+72 = 360 → **4,176** | MATCH |
| 3,816 WRONGLET | twisted blocks only (the runner's `if not xi1_is_one` guard) → **3,816** | MATCH |
| 25,409 total | 56+656+4176+4176+4176+0+4176+0+3816+4176+1 = **25,409** | MATCH |

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe3_children_table.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe3_children_table.txt liftcorner_tailstab_children_table.txt
(empty)  -> TABLE BYTE-IDENTICAL TO COMMITTED
$ git status --short          (only the GRTJC composer's untracked files; I edited nothing)
```

§7 of the regenerated table, verbatim:

```
assertion failures: 0
A1 ... PASS   A2 ... PASS   A3 ... PASS   A4 ... PASS   A5 ... PASS   A6 ... PASS
A7 [r2] the enumerated children RECONSTRUCT the object A6 walks: PASS
   nodes reconciled: 752   children enumerated: 5336
   (i)   sum(children a' Phi0^m' Phi'^j') == X exactly: mismatches 0
   (ii)  every child in shape (deg a' < d0, m' >= 0): violations 0
   (iii) digit-wise dev-linearity (children's digits == X's digits): mismatches 0
   (iv)  branching <= 2e0+3: violations 0; observed max children per node by e0:
         {2: 7, 3: 9, 4: 11, 5: 13, 6: 15}  (2e0+3 = {2: 7, 3: 9, 4: 11, 5: 13, 6: 15})
ANY CHILD DROPPING NEITHER COORDINATE: NO
OVERALL: ALL GREEN
```

**Regeneration-discipline claim CONFIRMED by git, not by the note's word:**

```
$ git diff b2dc120 a3112dc --numstat -- .../liftcorner_tailstab_children_table.txt
7  0    <- 7 insertions, 0 deletions
$ git diff b2dc120 a3112dc -- .../liftcorner_tailstab_children_table.txt | grep -c '^-[^-]'
0       <- 0 deleted/modified lines
```

exactly the note's "**7 pure INSERTIONS** (one provenance line in the header,
six A7 verdict lines in §7) with **0 deleted and 0 modified lines**". The
inserted header line sits *above* §1, so "§§1–6 come back BYTE-IDENTICAL" is
literally true.

Independently re-derived from my own parse of the regenerated file: 29 towers,
p ∈ {2,3,5}, d₀ ∈ {1,2,3}, e₀ ∈ {2,3,4,5,6}, genres {dense, midonly, pure,
tailonly}, CTR = PE1's instance verbatim (ℤ₂, d₀=2, e₀=2, h₀=1, Φ₀=x²+x+1,
b₀=2, b₁=2x, Φ′=x⁴+4x³+5x²+4x+3); **Σ_inst(d₀+1) = 94** hand-summed from the
roster, × 4 m-values × 2 j-values = **752** nodes; 2,668 j=0 child rows
(genre counts 200+376+208+316+376+220+328+268+376 = 2,668) and 2×2,668 = **5,336**
children reconciled by A7; §5 LEDGER 752 probes / 4,438 digits / min slack 0;
§3 shows `b0-main-r` as the unique label with gain set exactly {0} and
`mid[TOP=e0-1]-q` as the unique label whose 220 rows are all `degA-DROP`, every
other label 100% `m-DROP`. All match the note.

### (b′) A7 leg (i) — spot-audit of the code against its stated meaning

The note's claim for leg (i) is that X is "built by direct multiplication from
Φ₀ and Φ′ — **not from the pass identity** — so a missing or a spurious branch
fails the check", over "the SAME 752 (a, m, j) probes A6 walks". Source read
(`liftcorner_tailstab_children.py`):

```python
def bigX(inst, a, m, j):
    """... Shared by A6 (ledger_check) and A7 (reconcile_children) so that the two
    assertions provably speak about the same polynomial."""
    return pmul(a, pmul(ppow(inst['Phi0'], m), ppow(inst['Phip'], j)))

def reconcile_children(inst, a, m, j):
    X = bigX(inst, a, m, j)
    chs = children(inst, a, m, j)
    for ch in chs:
        C = bigX(inst, ch['coef'], ch['m'], ch['j'])
        S = padd(S, C)
        ...
        for slot, dg in double_dev_digits(inst, C).items():
            agg[slot] = padd(agg.get(slot, []), dg)
    ok_sum = not ptrim(psub(S, X))
    ...
    return ok_sum, bad_shape, agg == double_dev_digits(inst, X), len(chs)
```

**The claim is accurate.** (1) `bigX` is a bare `pmul/ppow` of Φ₀ and Φ′ — no
pass identity, no b₀-split, no redigit. (2) `ledger_check` (A6) walks
`double_dev_digits(inst, bigX(inst, a, m, j))` and `reconcile_children` (A7)
compares against `double_dev_digits(inst, X)` with `X = bigX(inst, a, m, j)` —
*the same pure function on the same arguments*, called from the same
`run()` loop iteration, so A7 is **not** a parallel recomputation of a different
object; it is tied to the very digits A6 walks. (3) The tie is arithmetically
non-trivial: dropping any one branch from `children()` (say the k = e₀−1 mid, or
the q-digit of the b₀-tail) changes `S` by a nonzero polynomial and leg (i)
would fire, because the r/q children carry the sign (`pscal(-1, r)`,
`pscal(-1, q)`) that makes
Σ = aΦ₀^{m−e₀}Φ′^{j+1} − a(ĉ′π^{h₀}+t₀)Φ₀^{m−e₀}Φ′^j − Σ_k ab_kΦ₀^{m−e₀+k}Φ′^j
collapse to aΦ₀^mΦ′^j only when the branch list is exactly right. So G3's
decorrelation gap (a second leg pinned to the first transcription) is genuinely
cured: `bigX` and `children()` share no code path.
(4) Leg (iii) additionally checks that the slot-wise sum of the *children's*
double developments equals X's — which is precisely (C)(i)'s "polynomial devs
carry no carries" additivity step, as the note claims.

Honest limits, as the note itself discloses and I confirm: A7 is instance-level
(752 nodes); it says nothing about the genre LABELS; and the battery probes only
m ∈ {e₀, e₀+1, 2e₀, 2e₀+1} with ĉ′ of degree ≤ 1 and mids/tails at exactly
their minimal w₀. The note's fence — "The table is evidence for the case split,
not a substitute for (A)–(C)" — is accurate.

---

## 2. FINDINGS

### F-A — JUSTIFICATION GAP / HONESTY DEFECT (source-verified): the ψ₁-carryover assert the r1 F4 repair promotes as the substantive leg is a TAUTOLOGY on one object and cannot fail

Offending passage (S2, disclosure (c), inside the `[r1, F4 — corrected
wording]` bracket):

> "**[r1, F4 — corrected wording]** the runner asserts, before any comparison,
> (i) full ψ₁-BYTE carryover (`[tuple(c) for c in T.psi1] == psi1_base`) and
> (ii) a single-element byte check on the K₂ table
> (`C.K2["one"] == C0.K2["one"]`) — (ii) is a SMOKE CHECK on one element, NOT an
> assertion that the K₂ arithmetic representation is shared, as the r0 text's
> parenthesis … implied."

The bracket's whole rhetorical structure is a CONTRAST: (i) is the genuine
machine leg, (ii) is downgraded to a smoke check. **The contrast is backwards.**
Source (`liftcorner_checks.py:31–53`, verbatim, the only writer of `psi1_base`):

```python
def make_orbit_tower(kind, p, d0, r0, r1, tag, c0p, spec):
    T = LC.make_tower(kind, p, d0, r0, r1, tag)
    psi1_base = [tuple(c) for c in T.psi1]      # <- snapshot of THIS SAME T
    K0 = T.K0
    T.psi0 = [c0p, K0["one"]]                   # the ledger override
    T.K1 = mk_field_ext(K0, T.psi0)
    T.z1 = T.K1["z"]
    ...
    LC.apply_pert(T, spec)               # sets T.Phi1, rebuilds T.Phi2
    # carryover soundness assertions (disclosure (c) of the sheet)
    assert [tuple(c) for c in T.psi1] == psi1_base, "psi1 byte drift"
    return T
```

`psi1_base` is snapshotted **from the same object `T`** that is then mutated,
and **nothing between the snapshot and the assert writes `T.psi1`**:

* `T.psi1` is assigned exactly once, in `Tower.__init__`
  (`grb_order2_check.py:515`: `self.psi1 = self._psi1_override if ... else
  pick_irreducible(self.K1, self.g1, idx=(self.h0) % 2)`) — i.e. **before**
  `make_orbit_tower` ever sees `T`;
* `apply_pert` (`iterlawlift_corner.py:145–155`) writes **only** `T.Phi1` and
  `T.Phi2` — its own docstring says so ("Sets T.Phi1 (and rebuilds T.Phi2 for
  hygiene)");
* `build_Phi2` only *reads* `self.psi1` (`grb_order2_check.py:651`).

So assert (i) compares `T.psi1` against a copy of itself, taken from the same
object, across code that provably never touches it. It is **structurally
incapable of failing** under the intended semantics, and it certifies **nothing
about carryover** — "carryover" in disclosure (c) means from the base ledger
(ψ₀ = y + c₀) to the transported one (ψ₀ ↦ y + c′), and no base-tower ψ₁ is
ever in scope at that assert. By the same measure, (ii) — the clause the note
DEMOTES — is the one that actually compares two *distinct* objects
(`C.K2` on the transported tower vs `C0.K2` on the base tower). The note's
evidential ranking of its own two asserts is inverted.

**Failure scenario (what the note claims the machine rules out but doesn't).**
Suppose the transported ψ₁ were NOT byte-equal to the base ψ₁ (e.g. if
`pick_irreducible`'s enumeration over `_field_elems(K1)` depended on the
modulus, so that recomputing ψ₁ on the transported K₁ gave different bytes).
Every orbit tower in the battery would then be carrying a **stale** ψ₁ built on
the wrong K₁, every K₂ = `mk_field_ext(T.K1, T.psi1)` in `SP.Composite` would be
built from it, and assert (i) would still pass silently — it never recomputes
ψ₁ at all. At most (i) is a *regression guard* against some future edit making
`apply_pert`/`build_Phi2` recompute ψ₁; it is not the check the note describes.

**What is NOT broken (why this is a GAP, not CRITICAL).** The note itself
relocates the soundness away from the asserts, correctly and in the same
paragraph: "The modulus-independence itself is verified by READING
`mk_field_ext`: at g = 1 its reduction loop `range(len(out)-1, g-1, -1)` is
empty, so products never touch the reducer — that is where the override's
soundness lives … not in the runner's asserts". I re-verified that reading
independently and it is correct, and I checked the consequence the note needs:
at g₀ = 1 the K₁ elements are 1-tuples over K₀ with modulus-free
multiplication, `_field_elems(K1)` enumerates them in a c₀-independent order, so
`pick_irreducible(K1, g1, idx)` really does return the same bytes for every
residue c′ — the transported ψ₁ *is* the base ψ₁. So the mathematics of the
override holds and the S3 measurement is unaffected. The defect is confined to
the description of the machine leg — which is exactly the clause PE1's F4 flagged
and r1 "corrected", making this a **repair that landed on the wrong half of its
own sentence**. PE2 verified only that the quoted source line exists verbatim
("`liftcorner_checks.py:52` `assert [tuple(c) for c in T.psi1] == psi1_base`
(full ψ₁-byte carryover)"), i.e. a text match, not a semantic one — so the
overstatement has now survived two passes. **Note also PE1's own F4 wording is
implicated**: "(i) `[tuple(c) for c in T.psi1] == psi1_base` — **genuine**, full
ψ₁-byte carryover". Misattributed verification credit, per this pass's charge.

### F-B — JUSTIFICATION GAP: the witness r2's G4 displays for the stricken r-to-q identity is NOT realizable as a branch product in its own stated setting

Offending passage (S4.1, *The ω-gains*, inside the `[r2, G4]` bracket):

> "The ultrametric only forces min(w₀(r), w₀(q)) = w₀(a·b), so the other digit
> may sit strictly higher — over ℤ₂ with Φ₀ = x²+x+1, **a·b = 4x²+2** gives
> q = 4 and r = −4x−2, so w₀(q) = 2 > 1 = w₀(r) = w₀(a·b) (PE2 G4's witness),
> and there gain(q) − gain(r) = e₁[e₀·1 + h₀] ≠ e₁h₀."

The division arithmetic is right (4x²+2 = 4Φ₀ − 4x − 2; w₀ = 1, 2, 1). But the
note writes the dividend as "**a·b**", i.e. as a level-0 branch coefficient of
the lemma — and in this very setting (Φ₀ = x²+x+1 ⟹ d₀ = 2) the lemma's own
constraints are deg a < d₀ and b ∈ {1, ĉ′π^{h₀}, t₀, b₁, …, b_{e₀−1}} with
deg b < d₀ (S1), i.e. **deg a ≤ 1 and deg b ≤ 1**. No such factorization
exists: writing a = αx+β, b = γx+δ forces αγ = 4, βδ = 2, αδ + βγ = 0, hence
(αδ)(βγ) = 8 and αδ = −βγ, so (αδ)² = −8 — and v₂(−8) = 3 is odd, so −8 is not
a square in ℚ₂. **4x²+2 is not a·b for any a, b ∈ ℤ₂[x] of degree ≤ 1.**

So the displayed object cannot occur at any branch of any d₀ = 2 instance, and
the passage as written does not exhibit the phenomenon *at a branch* — it
exhibits it for a general dividend. PE2, which authored the witness, hedged
exactly here ("Witness for the **arithmetic phenomenon**"); the note drops the
hedge and re-labels the polynomial "a·b". Since the note's very next sentence
attaches a branch-level conclusion to it ("and there gain(q) − gain(r) =
e₁[e₀·1 + h₀] ≠ e₁h₀"), the hedge was load-bearing.

**Why this is a GAP, not CRITICAL.** (a) The phenomenon *is* realizable at a
legal branch, so the strike is right on the merits — witness, at e₀ = 2, h₀ = 1,
d₀ = 2, Φ₀ = x²+x+1 over ℤ₂: take a = x (deg 1 < d₀) and the mid
b₁ = 4x+2 (deg 1 < d₀, w₀ = 1 = amin(1), so a legal mid). Then
a·b₁ = 4x²+2x = 4Φ₀ − 2x − 4, giving q = 4, r = −2x−4, w₀(a·b₁) = 1,
**w₀(q) = 2 > 1 = w₀(r)** — the inequality realized at a legal mid branch.
(Both divisions and the non-factorization criterion machine-checked this pass in
exact integer arithmetic: `4x²+2 → q=[4], r=[-2,-4]`, w₀ = 1/2/1 reproducing the
note's numbers; `x·(4x+2) → q=[4], r=[-4,-2]`, w₀ = 1/2/1; v₂(−8) = 3.)
(b) Nothing consumes the identity: the note's replacement derivation (CONTENT
applied separately to r and to q) is independently valid — I re-derived all
eight per-digit bounds from it, §3(3) below — and the note says so ("no step
below consumes it"). The defect is that the note's *justification for striking*
rests on a display that its own hypotheses exclude.

### F-C — JUSTIFICATION GAP (honesty, machine quote): "both machine legs re-ran bit-identically at PE2" overstates what PE2 recorded, at two sites

Offending passages (r2 header bracket, and the r2 STATUS LINE):

> "and both machine legs re-ran **bit-identically** at PE2 (i.e. on the pre-r2
> artifacts, before this round's A7 amendment to the children generator)."

> "S3's corner measurement and both machine legs re-ran **bit-identically** at
> PE2 (sealed runner 25,409/0, md5 `ccb4351c…` intact and still intact at r2;
> children table's data sections byte-identical under the A7 amendment)."

PE2's own report says something weaker for the sealed leg, explicitly:

> "Family table vs the committed `liftcorner_checks_output.txt`: **identical
> line-for-line modulo the `elapsed`/per-block timestamp fields only** (diff of
> the two outputs with timing normalised is empty)."

and PE2's transcript records `elapsed 4.3s` against the committed artifact's
`TOTAL checks 25409  elapsed 4.4s` (I confirmed both: the committed
`liftcorner_checks_output.txt:40` reads `elapsed 4.4s`; my own re-run this pass
printed `elapsed 4.3s`). The sealed runner's *output file* is therefore
demonstrably **not** bit-identical across runs — it carries wall-clock fields —
and the verifier the note cites for the claim wrote the qualification into its
report. The children-generator leg IS bit-identical (I re-confirmed: `diff`
empty), so the defect is the word "both".

This is the mildest class of honesty defect (a strengthened paraphrase of a
cited verifier's qualified finding, on a fact that is true in substance), but it
is a stale machine quote of the kind this pass is charged to grade, it occurs at
**two** sites, and the correct phrasing was available verbatim in the source
report. For the record, the substance is sound: violation counts, family counts,
fires, coverage minima and md5 are all identical across PE1's, PE2's and my runs.

### F-D — JUSTIFICATION GAP (internal inconsistency in the arc accounting): the r2 STATUS LINE labels charge items (1)–(2) "unaudited" in the same sentence that credits PE2 with auditing them

Offending passage (S5, `STATUS LINE [r2]`):

> "**(TAIL-STAB) is PROVED by S4.1 as repaired at r1 and confirmed at PE2 —
> 0 CRITICAL** on the r1 argument, with PE2 independently re-deriving the 9 ↦ 7
> genre mapping (total, disjoint), row 7b's degree drop at every boundary …, the
> two emptiness strata as PROVED rather than measured, and the ρ depth
> function's strict drop on every child edge. … Which steps are unaudited is now
> the grade box's charge **(1)–(2) and (7)**, plus the r2 edits themselves."

Charge item **(1)** is "the S4.1 seven-genre child census's COMPLETENESS … and
the row-7b degree drop"; item **(2)** is "the lex-order finiteness argument
((C)(ii): finite branching + the ρ depth bound)". Both are precisely what the
same sentence says PE2 re-derived — PE2's §3 answers them as charged questions
(1)/(2) ("mapping TOTAL and DISJOINT … CONFIRMED"; "Row 7b's degree drop: both
ingredients used correctly, no off-by-one … CONFIRMED") and (4) ("Both
consumers: the lex order DOES well-found them; ρ really bounds the recursion …
CONFIRMED"), and PE2 additionally re-derived census completeness from the
algebra by hand. So (1)–(2) are in exactly the evidential state the note
describes *correctly* for item (7) two hundred lines earlier:

> "Their audit status after r2, stated plainly: displayed at r1, re-derived
> ONCE by a hostile pass (PE2), and now named in the charge list — **one
> independent re-derivation, no acceptance credit, PE3 owed**."

The note therefore applies **two different labels to one evidential state**:
item (7) gets the accurate "re-derived once, no acceptance credit"; items
(1)–(2), equally re-derived once by PE2, get "unaudited". The defect
UNDER-states the evidence rather than over-stating it, and the charitable
reading ("unaudited *in their r2 form*", since G1 rewrote (2)'s branching count
and A7 re-based (1)'s completeness leg) is available — but the note forecloses
it by listing "plus the r2 edits themselves" as a *separate* clause, which
implies (1)–(2) are unaudited independently of the r2 edits. The clause is also
the direct successor of the r1 sentence it supersedes ("the r1 argument itself
has NEVER been hostile-read, and the grade box's charge (1)–(2) names exactly
which of its steps are unaudited"), i.e. r1's wording was carried forward with
its scope word intact while its factual premise was being retracted in the same
breath. The grade box is the instrument the arc is tracked by, so an inconsistent
label there has cost.

### F-E — JUSTIFICATION GAP (minor, disclosure): Q6 LOC is a derived counter that cannot fire independently, and S3 omits the one family count that is zero

Offending passages (S2 sheet row, and S3's verdict bullet):

> "| Q6 LOC | δ₁ = 0 sub-violations (lift-form-free legs; bug detector) | 0 |"

> "Q4 PV / Q5 INT / TRS 4,176/0 each; **Q6 LOC 0 (no δ₁ = 0 anomaly)**;"

In the runner, `note("LOC")` is **never called** — `LOC` has no check counter at
all — and `viol("LOC", …)` appears only *nested inside* the violation branches
of PV, INT and TLAW (`if d1 == 0:` under `if shape_bad is not None or v != predA
…`, under `if num % T.e0 != 0`, under `if cf is None or c != cf`). So (a) LOC's
check count is structurally 0 — the committed artifact reads
`LOC       pred 0  obs     0  (     0)  GREEN`, and LOC contributes 0 of the
25,409 — and (b) "LOC = 0" is *logically implied* by PV/INT/TLAW being green: it
carries no information the other families do not already carry.

That design is defensible for a diagnostic ("bug detector", as S2 says), and the
claim is TRUE. The defect is presentational and asymmetric: S3 gives an explicit
sample count for every other family it reports (56/56, 656/0, 4,176/0 ×4,
3,816, 1,576 fires) and gives none for the single family whose count is zero,
writing instead "Q6 LOC 0 (no δ₁ = 0 anomaly)" — which reads as an affirmative
observation on a probed stratum. A reader tallying S2's thirteen prediction
families as thirteen independent legs is over-counting by one.
(COV also has count 0 but is *not* implicated: its violation check
`if ncov == 0` / `if … nteeth == 0` can fire independently of every other
family, and S3 reports its substance — "min 6 δ₁ = 1 pairs and min 6 teeth
pairs" — explicitly.)

---

## 3. The four directed veins — results

### (a) S2/S3 — the measurement design and the corner statement

**S2's applicability arithmetic: fully independent-derived, EXACT.** See the
table in §1(a): every one of the seven figures (16 twistable instances, 48
twisted towers, 56 gate checks, 656 AV, 4,176 pairs, 3,816 WRONGLET, 25,409
total) re-derives from the roster and the runner's own draw logic
(`twists = [c for c in K0 elements if nonzero and != c0][:2]`, so |K₀| = 2 gives
0 twists, |K₀| = 3 gives 1, |K₀| ≥ 4 gives 2), and 25,409 is exactly the sum of
the eleven family counters plus CERT's internal leg. S2's "Twists exist iff
|K₀| > 2" is correct (|K₀| = 2 has one nonzero element and it is c₀).

**Q7 CHI really is measured-against-measured, and it is NOT implied by Q3.**
I checked the code path: `base_cc[(ga,gb)]` comes from `measured_cocycle(T0,C0,…)`
on the *base standard* tower, and the base towers are never subjected to
TLAW/PV/INT/TRS in this runner (they get only `G.T1_T2`/`G.T5` and the χ-cache
extraction). So CHI validates the base cocycle against the twisted one; it is not
a corollary of the twisted tower's TLAW. The note's parenthetical "(no closed
form in the comparison)" is accurate for the compared *values*; the exponent D₁
is taken from `LC.closed_form(…)`'s integer output `num//T.e0`, which is the
note's own S1 integer datum, not a value prediction — no finding.

**The corner statement of S1: re-derived, correct.** ψ₀^{(ξ)} := ξ⁻¹ψ₀(ξy) =
ξ⁻¹(ξy + c₀) = y + c₀/ξ = y + c′ at ξ = c₀/c′ ✓. z₁ = −c₀ = ξ·(−c′) = ξ·z₁′ ✓.
The χ-ratio is then forced: c_base = z̄^{δ₂}z₁^{D₁} = z̄^{δ₂}(ξz₁′)^{D₁} =
ξ^{D₁}·c′(γ,γ′) ✓, matching COR 2's display. The orbit parametrization
(Φ′ = Φ₀^{e₀} + Σ_{k<e₀}b_kΦ₀^k with w₀(b₀) = h₀ exactly, c′ ≠ 0,
w₀(b_k) ≥ amin(k)) is complete for monic degree-e₀d₀ lifts, and "strict-above
automatic, gcd(e₀,h₀) = 1" is correct because e₀ ∤ kh₀ for 1 ≤ k < e₀.

**Observation, NOT counted as a finding: `c′` carries two distinct meanings in
one load-bearing display.** In S1's CANDIDATE and in COR 2, `c′` is both the
*residue scalar* res(b₀/π^{h₀}) and the *cocycle on the Φ′-tower*:
"for every orbit member Φ′ with residue **c′** and ξ := c₀/**c′**,
c_base(γ,γ′) = **c′**(γ,γ′)·ξ^{D₁}". A reader can parse `c′(γ,γ′)` as the scalar
applied to a pair. Both PE1 and PE2 read through it, and no step is wrong; but
the collision sits inside the unit's headline identity and should be renamed
(e.g. `c^{Φ′}(γ,γ′)`). Recorded here rather than numbered, to avoid severity
inflation.

**S2 vs S3 scope, checked, no finding:** Q1's sheet wording is "every generated
tower passes the lawfulness gate", and the runner gates only the 56 orbit towers
(`note("GATE")` sits inside the `draws` loop), not the 24 base towers. S3
discloses the actual scope in the same breath ("56/56 **orbit** towers … 48
twisted + 8 ξ = 1 dense controls"), and gating a standard base tower for its own
ψ₀ would be a different assertion anyway. Accurate as reported.

### (b) The (TAIL-STAB) interface: did r1 silently change what the consumers may assume?

**No. The consumers are all satisfied by the byte-unchanged statement, and the
repaired PROOF adds no hypothesis a consumer violates.** Site by site:

1. **READ-EQ (S4.2)** uses it once: "Φ′-only children (t₀, mids): ledger
   ≥ Γ+1, and **by TAIL-STAB** every digit they generate stays > Γ". Those
   children are −π^U t₀·Φ₀^{S₁″}K^{S₂} and −π^U b_k·Φ₀^{S₁″+k}K^{S₂}, i.e.
   of the lemma's shape a′Φ₀^{m′}Φ′^{j′} with deg a′ ≤ d₀−1 (S1's deg b_k < d₀)
   and m′ ≥ 0. The lemma applies verbatim, and delivers exactly "digits ≥
   ω(child) ≥ Γ+1". **Interface intact.** Note the pleasant coincidence I
   checked: READ-EQ's parent coefficient is π^U of degree 0, so its one pass
   sits entirely in (B)'s deg a = 0 stratum where the repaired proof shows there
   are *no* q-children at all — the r1 repair's new machinery is not even
   exercised at READ-EQ, which is why F1 could never have propagated there in
   the form PE1 feared.
2. **THEOREM (S4.3)** consumes READ-EQ, not TAIL-STAB. **COR 1**, **COR 2**
   consume the THEOREM. **PROP** consumes COR 1 plus [ILN]'s propagation, never
   TAIL-STAB. No further sites: I grepped the note; "TAIL-STAB" occurs at
   S4.1's header, the READ-EQ use above, the F1 boxes, the charge list and the
   status lines — no other consumer.
3. **The one hypothesis the repaired proof leans on that the statement does not
   display is e₀ ≥ 2** (rows 1–5's "1st coord" column). It is a *section*
   hypothesis, stated in S4's Setting line and re-flagged in the m′ column
   ("Rows 1–5 use e₀ ≥ 2 (the S4 setting; e₀ = 1 is COR-3's degeneration, out
   of scope)"), and **every** consumer lives inside S4. No leak. (Incidentally
   the lex repair is robust at e₀ = 1 too: there row 3 becomes m-preserving but
   still drops deg a by ≥ 1, so only the *labelling* of the descent column, not
   the argument, is e₀ ≥ 2-specific.)
4. **(C)(i)'s induction does not consume (C)(ii).** Well-founded induction on
   the lex order needs only that each child is lex-below; the one-pass
   dev-linearity sum is finite by inspection (≤ 2e₀+3 summands). So (C)(ii)'s
   König/finiteness paragraph is belt-and-braces, and G1's false branching
   count could never have broken anything — precisely what the note claims
   ("ONLY FINITENESS of this count is consumed … no step anywhere uses the
   count's VALUE"). Verified, no finding.
5. **The statement's second half** ("Hence w₂(X) ≥ ω(X), and for any read
   weight Γ < ω(X) every level-2 read of X at Γ contributes 0 …") is untouched
   by r1 and is what READ-EQ actually needs. Verified.

### (c) The r2 patches themselves

**G1 — the 2e₀+3 arithmetic: CORRECT, and its parenthetical really does sum
that way.** 1 (row 1) + 4 (rows 2–5 counted per digit) + (e₀−1) (row 6) +
(e₀−1) (rows 7a+7b) = **2e₀+3** ✓, and the r1 parenthetical the note quotes
("row 1, rows 2–5, and ≤ e₀−1 realizations each of rows 6 and 7") does sum to
1+4+(e₀−1)+(e₀−1) = 2e₀+3, so the note's diagnosis of the r1 error (rows 2–5
counted as two branches while 6/7 were counted as digits) is right. Attainment
re-confirmed from my regenerated table: max children per node = {2:7, 3:9,
4:11, 5:13, 6:15} = 2e₀+3 at every e₀ ✓, and A7(iv) asserts it per node
(`if nch > 2*e0+3`) with 0 violations.

**G3 / A7 — the completeness leg: it really does tie `children()` to the digits
A6 walks.** Full audit in §1(b′): `bigX` is a bare `pmul/ppow` of Φ₀ and Φ′;
A6 and A7 call the *same* `double_dev_digits(inst, bigX(inst,a,m,j))` from the
same loop iteration, so A7(iii) is not a parallel recomputation; and the signed
children collapse to X only if the branch list is exactly right, so a missing or
spurious branch fires leg (i). G3's decorrelation complaint is genuinely cured —
`bigX` and `children()` share no code path.

**The per-digit CONTENT replacement bounds — re-derived from scratch, all eight
correct; rows 3 and 7b in full as directed.** With ω(a′Φ₀^{M′}Φ′^{j}) − ω(aΦ₀^mΦ′^j)
= e₁[e₀(w₀(a′) − w₀(a)) + (M′−m)h₀], M = m−e₀+k, and CONTENT giving
w₀(a′) − w₀(a) ≥ β for **either** digit:

* general r-digit (M′ = M): gain ≥ e₁[e₀β − (e₀−k)h₀] ✓ (the note's display);
* general q-digit (M′ = M+1): gain ≥ e₁[e₀β − (e₀−k)h₀ + h₀] ✓;
* **row 3** (b₀-main q; β = h₀ since w₀(ĉ′) = 0, k = 0, M′ = m−e₀+1):
  gain ≥ e₁[e₀h₀ − e₀h₀ + h₀] = **e₁h₀** ✓ — matches the table entry exactly;
* **row 7b** (top mid q; k = e₀−1, β = amin(e₀−1)):
  gain ≥ e₁[e₀·amin(e₀−1) − h₀ + h₀] = e₁e₀·amin(e₀−1), and
  e₀·amin(k) ≥ (e₀−k)h₀ + 1 (strict because e₀ | kh₀ ⟺ e₀ | k, impossible for
  1 ≤ k < e₀ at gcd(e₀,h₀) = 1) gives at k = e₀−1: e₀·amin ≥ h₀+1, hence
  gain ≥ **e₁(h₀+1)** ✓ — matches;
* row 1 = γ₂ − e₁e₀h₀ = **h₁** exactly ✓; row 2 (β = h₀, k = 0) = **0** ✓ and it
  is the unique 0 (every other row's bound is > 0 given e₁,h₀,h₁ ≥ 1) ✓;
  row 4 (β = h₀+1, k = 0) ≥ **e₁e₀** ✓; row 5 ≥ **e₁e₀+e₁h₀** ✓;
  row 6 ≥ **e₁** ✓; row 7a ≥ **e₁(h₀+1)** ✓.

The G4 strike itself is therefore sound in substance and the "ω-gain ≥" column
is unchanged, exactly as the note says — the only defect is the display of the
witness (F-B). The 896 figure is consistent with the table (the four q-labels'
counts 200+208+220+268 = 896), and the OBSERVATION is correctly fenced
("no step below consumes it").

**G5 — the named instances check out.** `A12` = (p=2, d₀=2, e₀=2, h₀=1, genre
`pure`) and `B14` = (p=2, d₀=2, e₀=5, h₀=1, genre `pure`) both appear in the
regenerated roster exactly as described, and `make_instance`'s `pure` branch sets
`b.append([])` for every k ≥ 1, so all mids (including b_{e₀−1}) vanish — row 7b
is absent for every a, and neither instance contributes a row to §4's m′ = m
stratum. The weakening (d₀ = 1 sufficient, not necessary) is correct, and the
consumed content ("d₀ = 1 rows cannot exhibit the defect, so the
counter-instance has to sit at d₀ ≥ 2") survives.
*Wording nit, not counted:* the note says the r0 clause "also holds **VACUOUSLY**
at any node with no m-preserving child" — at such a node the clause holds
*substantively* (children exist and all drop m); it is not vacuous. Harmless.

**G2 — the corrected attribution is now accurate.** PE1's verbatim scope
("all four ω-gain rows of the branch table …") is quoted correctly from its F1
repair observation; the eight per-digit entries are correctly identified as new
at r1 (rows 3, 5, 7a, 7b) and credited to PE2, whose G2 does re-derive all eight
in the terms the note reproduces. Charge item (7) exists. APPLIED, accurately.

### (d) The S5 / grade-box arithmetic of the whole arc

Checked line by line; everything reconciles **except F-D**:

* PE1 = 1 CRITICAL + 3 gaps at commit **30e570c** ✓ (matches the report's own
  verdict line and `git log`); the "three r1 gap repairs" list (F2/F3/F4) is
  1 + 3 = 4 dispositions ✓.
* PE2 = 0 CRITICAL + 5 gaps at commit **3367f3c** ✓; the "five r2 repairs" list
  (G1–G5) is complete and each item's one-line summary matches PE2's finding ✓.
* Both cited ledger entries exist at HEAD in
  `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`: "PE1 VERDICTS" (line 10467)
  and "LIFT PE2: THE REPAIR HOLDS (0 critical / 5 gaps)" (line 10571) ✓.
* **The r1/r2 naming collision is handled honestly**, not silently: r1's closing
  sentence used "round r2" for the next *pass*, and the r2 bracket leaves that
  sentence standing and disambiguates it in place ("the hostile pass on the r1
  text was **PE2**; **r2 is this REPAIR round**; the next acceptance attempt is
  **PE3**"). Arc display "PE1 → r1 → PE2 → r2 → PE3" is consistent at all four
  sites where it appears.
* Counter **0/2** at every site, with the correct reason each time (a repair
  round is not a pass; PE2 was a pass but returned gaps) ✓. No acceptance credit
  is claimed anywhere. The W-2 cap ("GRTW2 is itself 0/2") and the honest
  decoupling fact ("the COR 1 chain … is W-2-free") are both stated and, on
  PE1's dependency trace which I re-checked, correct.
* Charge list has exactly seven items, (7) marked `[r2, G2]` ✓, and the r2
  status line's own summary of what is owed is where F-D lands.
* **Superseded text discipline: clean, and checked against the diff, not the
  prose.** `git show e5b3faf` on the note is 221 insertions / **12 deletions**;
  I read all twelve removed lines. Three carry refuted content, and each is
  quoted verbatim inside the bracket that replaces it: the r1 gain identity
  ("… and gain(q-digit) = gain(r-digit) + e₁h₀") → quoted and STRICKEN in
  [r2, G4]; "≤ 2e₀+1 children per node (row 1, rows 2–5, and ≤ e₀−1
  realizations each of rows 6 and 7)" → quoted verbatim in [r2, G1]; "valid
  **exactly** on the flat corner d₀ = 1" → the in-place edit replaces "exactly"
  with "on the whole", and [r2, G5] quotes the old wording and calls it false.
  The remaining nine deletions are grade-box/trailer lines extended in place
  (charge parenthetical, date line), carrying no refuted claim. Likewise the r0
  strict-descent clause and the r0 "settled in full" sentence survive only
  inside the F1 box and the superseded STATUS LINE that refute them, and the
  "UNCHANGED … re-verified by PE1" attribution survives only inside [r2, G2]. I
  found **no un-superseded refuted text** anywhere in the note.
* S5's conditional consequence display is still correctly fenced ("ONCE THIS
  NOTE'S ARC CLOSES (and not before — no ledger or accepted text is edited
  now)") and the "NOT covered, said plainly" exclusion (deeper-level
  non-canonical lifts, the g_m = 1 analogue) is intact.

---

## 4. Verified perimeter (re-checked this pass, no findings)

- **The counter-instance chain, re-computed by hand end to end.** Φ′ = Φ₀² +
  b₁Φ₀ + b₀ = x⁴+4x³+5x²+4x+3 with Φ₀ = x²+x+1, b₀ = 2, b₁ = 2x ✓; γ₂ = 3;
  ω(X) = 2 at X = xΦ₀². First pass: key a′ = x at (0,1) ω = 3 gain +1 = h₁;
  b₀-main r a′ = −2x at (0,0) ω = 2 gain 0; mid[1] from 2x² = 2Φ₀ − 2x − 2
  giving r-child a′ = 2x+2 at (1,0) ω = 3 gain +1 = e₁ and q-child a′ = −2 at
  **(2,0), i.e. m′ = m with deg a′ = 0 < 1 = deg a** ω = 4 gain +2 = e₁(h₀+1).
  Second pass on (a,m) = (−2,2): key a′ = −2 at (0,1) ω = 5; b₀-main r a′ = 4 at
  (0,0) ω = 4 gain 0; mid[1] r a′ = 4x at (1,0) ω = 5; **no mid q-child**
  because a·b₁ = −4x has degree 1 < 2 = d₀ ✓ — exactly (B)'s prediction.
  8 nodes, 6 leaves all at m ≤ 1 < e₀, depth 2 ≤ ρ(root) = m·d₀+d₀−1 = 5 ✓.
  Every displayed number matches.
- **The independent tie, re-multiplied:**
  (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) = x⁵+2x⁴+3x³+2x²+x = x·(x²+x+1)² = xΦ₀² ✓
  exact. Digit weights: (1,0)→3, (0,1)→3, (0,0)→2 against ω(X) = 2, slacks
  1, 1, 0, equality thread at (0,0) = row 2's gain-0 thread ✓.
- **CONTENT sub-lemma.** Division by a *monic* Φ never divides by a non-unit, so
  every coefficient of q and r lies in the O-module generated by the
  coefficients of F; hence w₀(q), w₀(r) ≥ w₀(F). The note's one-line induction
  is the right argument. (It remains charge item (3); nothing changed at r2.)
- **(A)'s one-pass identity and the two-digits-per-branch bound.**
  X = aΦ₀^{m−e₀}Φ′^{j+1} − ab₀Φ₀^{m−e₀}Φ′^j − Σ_{k≥1}ab_kΦ₀^{m−e₀+k}Φ′^j is
  exact from Φ₀^{e₀} = Φ′ − Σ_{k<e₀}b_kΦ₀^k ✓; deg(a·b) ≤ (d₀−1)+(d₀−1) =
  2d₀−2 < 2d₀ forces deg q ≤ d₀−2 and forbids a redigit cascade ✓. Machine-tied
  by A7(i) at 752 nodes.
- **Base case.** m < e₀ ⟹ deg(aΦ₀^m) ≤ (d₀−1)+(e₀−1)d₀ = e₀d₀−1 < deg Φ′, so
  dev uniqueness gives the single digit a at (i,j) = (m,j), (LEDGER) at
  equality ✓.
- **(B)'s two emptiness strata are PROVED, not measured** (deg a = 0 ⟹
  deg(a b_{e₀−1}) ≤ d₀−1 < d₀ ⟹ q = 0; d₀ = 1 ⟹ deg(a·b) = 0 < 1 for every
  branch factor) ✓, and (B)(i)'s "at most deg a ≤ d₀−1 consecutive
  m-preserving steps" follows since each such step drops deg a by ≥ 1 and
  deg a = 0 admits none ✓.
- **ρ(m, deg a) := m·d₀ + max(deg a, 0) strictly drops on every edge** (an
  m-drop of ≥ 1 costs ≥ d₀ and restores ≤ d₀−1; an m-preserving edge is row 7b
  and drops the second coordinate by ≥ 1), and the lex order on
  ℕ × ({−∞} ∪ {0,…,d₀−1}) is a well-order (ℕ well-ordered × a finite chain) ✓.
- **READ-EQ's δ₁ = 1 leg, re-derived.** g₀ = 1 ⟹ s₁+s₁′ ≤ 2e₀−2 so exactly one
  overflow ✓; ω(P) = γ+γ′ from the split identity (I re-expanded both sides) ✓;
  the key child sits at Γ+h₁ ✓; the b₀-main digit sits **exactly on** Γ (its
  gain is row 2's 0) and is nonzero since w₀(ĉ′) = 0, pinning w₂(P) = Γ on both
  towers ✓; the ĉ′ − lift(c′) difference sits at ≥ Γ+e₁e₀ ✓; tail/mid children
  at ≥ Γ+e₁ ≥ Γ+1 with TAIL-STAB closing their whole subtrees ✓. Sound.
- **THEOREM / COR 1 / COR 2 / PROP.** Φ″ = Φ₀^{e₀} + lift(c′)π^{h₀} is a
  standard-lift instance at ψ₀^{(ξ)} = y + c′ (monic degree 1, irreducible,
  nonzero constant term) ✓; COR 1's ξ = 1 slice is the lawful class ✓; COR 2's
  algebra is the two-line ξ^{D₁} consequence ✓; PROP's rung-≥2 clause-(ii)
  census is explicitly a VERIFY-TARGET, cited not proved ✓. F3's rescope is
  intact: I grepped W2-OPEN-1 / "RESTRICTED" / "base junction" and every
  remaining occurrence is a disclosure (source cite, r1 header, F3 box, charge
  item (6)) — no consumer.
- **Fences.** No commit in the r1/r2 range touches ILNRES / ITERLAWN / the
  wave-18 note or runner; the sealed runner is 0-byte-diff from its seal; no
  Lean change; the r2 generator amendment adds assertions only (7 pure
  insertions, 0 deletions in the table). The FENCES paragraph holds in the repo
  state.

## 5. Bottom line

**Not a clean pass: 0 CRITICAL, 5 gaps.** The (TAIL-STAB) proof is in good
shape — after three hostile readings its case list is complete, its descent is
well-founded, its eight per-digit gain bounds all re-derive, its two emptiness
strata are proved rather than measured, and its completeness leg is now carried
by a committed assertion (A7) that genuinely decorrelates from the prose
transcription. The S3 measurement is untouched machine fact, and the arc's
bookkeeping is unusually disciplined: no un-superseded refuted text anywhere,
the r1/r2 naming collision handled in place rather than silently, the counter
honestly frozen at 0/2.

What this pass found is that the *evidence-description* layer has not kept pace
with the mathematics. The single most consequential item is **F-A**: the
ψ₁-carryover assert that S2's disclosure (c) presents as the substantive machine
leg — and contrasts favourably against the K₂ "smoke check" — is a tautology on
one object that provably cannot fail. That clause is precisely what PE1's F4
flagged and r1 "corrected", so r1's repair fixed the wrong half of its own
sentence, and both PE1 and PE2 signed off on the unfixed half (PE1 called it
"genuine"; PE2 checked only that the source line matched verbatim). **F-B** is
the same species one layer up: r2's G4 strike is right, but the witness it
displays to justify striking cannot arise at a branch under the lemma's own
degree hypotheses (a realizable substitute exists and is displayed above).
**F-C**, **F-D** and **F-E** are precision defects in, respectively, a machine
quote attributed to PE2, the grade box's own audit accounting, and a
zero-count prediction family reported as a result.

Nothing here weakens "(TAIL-STAB) PROVED at attempt grade, argument re-read
twice, no acceptance credit" as a description of the note. The five items above
are owed, and the acceptance count remains **0/2** — a clean pass has not yet
occurred, so none has started.

— passPE3, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-05).
Machine legs: **(a)** sealed runner `liftcorner_checks.py` exit 0,
`VERDICT: ALL GREEN`, `TOTAL checks 25409`, 0 violations in every counted
family, md5 `ccb4351c92573f5f962cae4ae952d8dd` = the note's claim = the md5 at
seal commit dafc0b5, `git diff dafc0b5 HEAD` on it is **0 bytes**;
**(b)** children generator `liftcorner_tailstab_children.py` exit 0, regenerated
table **byte-identical** to the committed one (`diff` empty), A7 all four legs
PASS (752 nodes / 5,336 children; sum-identity 0, shape 0, digit-wise 0,
branching 0 with observed max = 2e₀+3 at every e₀), A1–A6 PASS, "ANY CHILD
DROPPING NEITHER COORDINATE: NO", and leg (i) spot-audited against source
(§1(b′)). Nothing in the repo was edited by this pass except this report.
