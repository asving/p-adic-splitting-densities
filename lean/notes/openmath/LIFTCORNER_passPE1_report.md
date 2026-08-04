# LIFTCORNER passPE1 — hostile verification report (fresh context)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` (NR-1 / (ITER-LAW-LIFT)
corner discharge via the W-2 shift-descent route).
**Runner:** `verification/openmath/liftcorner_checks.py`.
**Commits audited:** dafc0b5 (seal) / 987ffb7 (verdict) / dc278ce (compose);
ledger tail b312716.
**Charge:** quote-and-classify, fix nothing; honesty defects graded; scope
fences and honest boxes read as part of the statement. Special attention:
(1) the (TAIL-STAB) ledger double induction in full; (2) the wrong-letter
control's exact set-equivalence and the independence of the two computed
sets; (3) the ξ = 1 core chain's claimed W-2-freeness; (4) S5's
rider-rewrite display touching no ledger/accepted text.

**VERDICT: 1 CRITICAL ERROR / 3 JUSTIFICATION GAPS.** The machine leg is
clean (bit-identical re-run, exit 0, every figure matches; seal verified).
The critical error is in the S4.1 (TAIL-STAB) proof — the strict-descent
claim its induction and termination both ride is FALSE as written (explicit
counter-instance below). The lemma is plausibly true and a local repair
exists, but the note's headline "(TAIL-STAB) PROVED" is not supported by
the recorded argument. Everything downstream of TAIL-STAB (READ-EQ,
THEOREM, COR 1/2, PROP, S5) was verified under the assume-the-conclusion
protocol and is sound GIVEN TAIL-STAB.

---

## 1. Machine leg (mandatory) — CLEAN, all figures match

Re-run 2026-08-04 (this pass, fresh shell):
`python3 liftcorner_checks.py` from `verification/openmath/` →
**exit code 0**, `VERDICT: ALL GREEN`, `TOTAL checks 25409  elapsed 4.4s`.
Family table identical to the committed `liftcorner_checks_output.txt`
line-for-line: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 · INT 0/4176
· LOC 0/0 · CHI 0/4176 · COV 0/0 · WRONGLET 0/3816 · TRS 0/4176 ·
ENGGATE 0/1 · CERT 0 · wrong-letter fires 1576 · gate-passed 56 ·
min d1-pairs 6 · min teeth 6. The committed JSON
(`liftcorner_checks_results.json`) agrees: `violations: []`, same counts,
`cert_violations 0`, `sp_bugdetector 0`, `lc_counts 0`, fires 1,576 over
48 blocks, 56 cov blocks / 48 teeth blocks. `--shakedown` re-run: 1,590
checks ALL GREEN exit 0, matching the seal commit message.

Every S3 figure in the note matches the artifacts and the re-run:
25,409 / 0; Q1 56/56 (48 twisted + 8 ξ=1); Q2 656/0; Q3 4,176/0;
Q7 4,176/0; Q9 3,816 samples, 1,576 fires; Q8 min 6/6; elapsed 4.4 s;
SP bug-detector 0. **No stale machine quotes.**

**Count re-derivation (independent leg).** From `iterlawlift_corner.ROWS`
(CA–CF, r0 third component = 1 in all rows, so all g₀ = 1; E₂ = e₀e₁ =
4/6/8/6/10/3 — the S2 roster line is exact; d₀ = 2 on CB/CD only):
twistable instances = 2 rows × 4 rings (d₀=2, |K₀| ≥ 4) + 4 rows × 2 rings
(d₀=1, p=3 only) = **16**, exactly S2's figure; twisted towers = 8·2·2 +
8·1·2 = **48**; + CB/CF × 4 rings ξ=1 dense controls = **56** gate checks.
Pairs 2E₂² per tower: twisted 128+512+800+72+1152+1152 = 3,816; ξ=1
288+72 = 360; total **4,176** = TLAW/PV/INT/TRS/CHI count; WRONGLET =
3,816 (twisted only, per the runner's ξ≠1 guard). AV = Σ2E₂ = 584+72 =
**656**. All of S2's "deterministic applicability" arithmetic checks out.

**Two-commit seal — VERIFIED.** dafc0b5 (2026-08-04 23:02:12, note
skeleton + runner) precedes 987ffb7 (23:03:14, verdict + artifacts)
precedes dc278ce (23:06:20, compose, note-only). Runner md5 at the seal =
`ccb4351c92573f5f962cae4ae952d8dd` = the note's S3 claim = the working
tree; `git diff dafc0b5 dc278ce -- liftcorner_checks.py` is empty
(byte-untouched through the arc). No commit since the seal touches
ILNRES / ITERLAWN / the wave-18 note / the wave-18 runner (fences
respected); b312716 touches only `BRIDGE_ADJUDICATIONS_2026-07-30.md`
(append-only tail entry, marked pending-arc).

---

## 2. FINDINGS

### F1 — CRITICAL ERROR: the S4.1 (TAIL-STAB) strict-descent claim is false; the induction and the termination claim both ride it

Offending passage (S4.1, the step case):

> "Every child is again of the lemma's shape with m′ ≤ m−1 (strict
> descent; termination), and the ledger GAINS per branch …"

and the closing line that inherits it:

> "The ONLY 0-gain branch is b₀-main's r-digit, which also strictly drops
> m: the ω(X)-thread terminates in ≤ ⌈m/e₀⌉ passes. ∎"

**The claim is false at the mid-branch top q-digit.** The note's own
branch table displays the mid child at "(m−e₀+k (+1), j)": re-digiting
ab_k = r + qΦ₀ puts the q-child at m′ = m−e₀+k+1, which at k = e₀−1
equals **m′ = m** — no descent. Strong induction on m gives the IH only
for m′ < m, so the proof cannot close on that child as written, and the
"termination" assertion (needed for the dev-linearity line "the double
dev of X is the digit-wise sum of the children's" to be a finite sum)
rides the same false claim.

**Explicit counter-instance** (hand-checkable): O = ℤ₂, d₀ = 2, e₀ = 2,
h₀ = 1, Φ₀ = x²+x+1; lawful orbit member with b₀ = 2 (c′ = 1), b₁ = 2x
(w₀ = 1 = amin(1)). Take X = aΦ₀^mΦ′^j with a = x, m = 2, j = 0. The
k = 1 = e₀−1 mid child is −ab₁Φ₀^{m−e₀+k} = −2x²Φ₀; re-digit
2x² = 2Φ₀ − 2x − 2, so the q-child is **−2Φ₀² at m′ = 2 = m**. (At
d₀ = 1 no q-children exist — deg(ab_k) = 0 < d₀ — so the flaw fires only
at d₀ ≥ 2; the roster's CB/CD rows are d₀ = 2, i.e. inside scope.)

**Blast radius.** (TAIL-STAB) is consumed by READ-EQ ("by TAIL-STAB every
digit they generate stays > Γ"), hence by the S4.3 THEOREM, COR 1, COR 2,
PROP, the S5 consequence display, the dc278ce commit message
("(TAIL-STAB) PROVED (ledger double induction, the wave-18 open step
closed)"), and the b312716 ledger tail ("with (TAIL-STAB) PROVED").
**Honesty defect attached:** "PROVED" (S4.1 ∎, S5 "The wave-18 sketch's
one open step (TAIL-STAB) is CLOSED by S4.1", commit + ledger wording) is
stated stronger than the recorded evidence — the recorded argument is
broken at its load-bearing bookkeeping step, and closing exactly this
step was the unit's headline. Note also that the grade box's self-charge
list ("the CONTENT sub-lemma's base-fact status; the READ-EQ
on-line-content/ultrametric close; PROP's census cite") does NOT name
this step — the owed arc was pointed away from the actual flaw.

**For the record (verifier's repair observation, not a fix):** the lemma
is plausibly true and the repair looks local. Only mid-branch q-children
can keep m′ = m, and for those deg q ≤ deg a + deg b_k − d₀ ≤ deg a − 1
strictly drops, while every other child has m′ ≤ m−1 (e₀ ≥ 2); so
lexicographic induction on (m, deg a) is well-founded and the recursion
terminates without any convergence argument. All OTHER components of
S4.1 verify: the base case (m < e₀: dev uniqueness gives the single digit
at (m, j), ledger equality — checked); the one-pass identity (checked
algebraically); all four ω-gain rows of the branch table (checked, using
e₀·amin(k) ≥ (e₀−k)h₀+1 which I re-derived from gcd(e₀,h₀) = 1: e₀ ∤ kh₀
for 1 ≤ k < e₀); the CONTENT sub-lemma (induction through the division
step — sound); dev-linearity (no carries in polynomial devs — sound,
GIVEN finiteness); the (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill
close (sound). The ⌈m/e₀⌉ bound for the ω-equality thread is itself
correct — but it is not the termination of the whole recursion.

### F2 — JUSTIFICATION GAP (minor): ĉ′ and t₀ used in load-bearing displays without in-note definition

S4.1 branch table rows "b₀-main ĉ′π^{h₀}, r/q digit" and "b₀-tail t₀
(w₀ ≥ h₀+1)", and S4.2's "−π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} … w₀(ĉ′−lift(c′)) ≥ 1
(both lift c′)". The decomposition b₀ = ĉ′π^{h₀} + t₀ with res(ĉ′) = c′
is never displayed in this note; it is wave-18 S1's notation
(ITERLAWLIFT_CORNER_2026-08-08.md, a listed source of record — which is
why this is a gap, not an error). S1 here defines only w₀(b₀) = h₀ and
c′ = res(b₀/π^{h₀}). One-line cure. (Other inherited symbols — γ₂, δ₂,
s₁″, ℓ₀ — are corpus-standard from the accepted ITER-LAW display and are
used before their in-note bindings; same genre, subsumed here.)

### F3 — JUSTIFICATION GAP: COR 2's identification with "W2-OPEN-1 restricted to the base junction at the corner" is asserted, not derived

Offending passage (S4.3 COR 2):

> "This is W-2 clause 3's value-layer statement (W2-OPEN-1) RESTRICTED to
> the base junction at the corner — now PROVED at this note's grade there,
> upgraded from instance-confirmed."

W2-OPEN-1 as recorded (GRTW2 §5.3) quantifies over "the committed value/
cocycle battery — K5 … K6 … K7 … K12 = π-shift/ρ-monodromy, K1–K4/K13
riding — … with the TRANSPORTED classifier lifts substituted for the
harness lifts." COR 2 proves the χ-covariance of the 2-read display
across the HARNESS monic-lift orbit. The tie between the two needs
(a) that the transported classifier key at the base junction is an S1
orbit member (monic, deg e₀d₀, w₁ = e₀h₀, order-1 residual y + c′) —
plausible from GMN key-polynomial properties plus W2-C3(ii), but no
bridging display is given; and (b) an account of the battery legs beyond
the display/anchor families (e.g. K12) under the restriction — not
addressed. As written, "is … RESTRICTED to" over-identifies what was
proved with a slice of W2-OPEN-1's statement. The W-2 grade cap is
honest and unaffected; the finding is the unproven equivalence claim.

### F4 — JUSTIFICATION GAP (minor, honesty/precision): the disclosed soundness assertion is described stronger than what the runner asserts

S2 disclosure (c): "the runner asserts this (ψ₁ bytes equal, K₂
arithmetic representation shared) before any comparison". The runner
asserts (i) `[tuple(c) for c in T.psi1] == psi1_base` — genuine, full
ψ₁-byte carryover — and (ii) `C.K2["one"] == C0.K2["one"]` — a single
element's byte equality, a smoke check, not an assertion that the K₂
arithmetic representation is shared. The MATHEMATICAL claim behind the
override is verified (I read `mk_field_ext`: at g = 1 the reduction loop
`range(len(out)-1, g-1, -1)` is empty, so products never touch the
reducer — exactly the note's "mk_field_ext at g = 1: products never
touch the reducer"; hence K₁-arithmetic is modulus-independent and K₂'s
construction from byte-identical ψ₁ is structurally shared). So the
soundness is real; only the description of the MACHINE assertion
overstates its coverage.

---

## 3. Special-attention items — results

**(1) (TAIL-STAB) double induction.** Base VERIFIED; ledger/ω-gain
descent VERIFIED in all four branches (including the gcd argument for
e₀·amin(k) ≥ (e₀−k)h₀+1); m-descent REFUTED at the mid-branch q-child —
finding F1 (critical).

**(2) Wrong-letter control set-equivalence.** CONFIRMED independent: per
pair the runner computes `mism = (c != wrong)` from the MEASURED cocycle
c against the wrong-letter form z̄^{δ₂}·z₁_old^{D₁} built from the CACHED
BASE letter (`results["z1_base"][itag]`, keyed correctly by the instance
tag), and `pred = (ξ^{D₁} != 1)` from ξ and D₁ alone; it checks
`mism == pred` pairwise (3,816 checks) and separately requires total
fires > 0 (1,576 observed; toothlessness would flip the verdict RED).
The two sets are computed by disjoint code paths from different data.
Exact set-equivalence claim ACCURATE. (Caveat for the record: given Q3,
the equivalence is mathematically implied by z₁ = ξ·z₁′ — the control's
independent value is that mism uses the measured c, so it cross-checks
Q3+CHI rather than adding a fourth independent law.)

**(3) ξ = 1 core W-2-freeness.** CONFIRMED. Dependency trace of the
COR 1 chain: (TAIL-STAB) — pure division-algorithm/w₀ bookkeeping, GRTW2
cited only in a bracketed structural REMARK ("This IS the shift-descent
bookkeeping … (GRTW2 §3.4 rem. 1)"), no consumption; READ-EQ — base
facts [IL S1]/[ILN] S0.2 + CONTENT + TAIL-STAB only; accepted ITER-LAW —
accepted 2026-08-03, pre-W-2; the S1 orbit parametrization — wave-18
S1's three elementary steps with c₀ → c′, no W-2 input. The W-2
consumption sits exactly where the grade box says it does (COR 2's and
S1's clause-3 FRAMING); the cap is if anything conservative — the
general-ξ THEOREM chain is also W-2-free on this trace, since
ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy) is self-contained. Conservative capping is not
a defect.

**(4) S5 rider-rewrite display.** CONFIRMED clean. The display is
conditional ("ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or
accepted text is edited now)") and factually accurate: dc278ce touches
only the note; b312716 is an append-only ledger tail entry that itself
carries "own arc 0/2" and "(pending arc)". The quoted rider is an
assembly of the ledger acceptance line ("(ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1") and ITERLAWN S0.1's sentence ("nothing is claimed for
any non-canonical lawful lift at any level") — both verified verbatim in
their sources. The discharge matches NR-1 AS RECORDED in ILNRES S1/S5.1:
the S5.1 spec (extend at g₀ = 1 ∧ δ₁ = 1, ride S0.1's verbatim
propagation, one note + sealed battery, no accepted text edited) is
exactly what the note delivers (route swapped from direct L7-Case-II
extension to orbit transport — a route substitution inside the same
deliverable, disclosed by the note's own S4 structure). The "NOT covered,
said plainly" exclusion (deeper-level non-canonical lifts) is consistent
with (ITER-LAW-LIFT)'s displayed statement of record (wave-18 S0 /
ITERLAW S7: "every lawful monic lift Φ₁") — the fence is correctly drawn.

---

## 4. Verified perimeter (checked, no findings)

- **S1 orbit frame:** ψ₀^{(ξ)} = ξ^{−1}ψ₀(ξy) = y + c₀/ξ = y + c′ at
  ξ = c₀/c′ (checked); matches GRTW2 §5.1's ψ^tw at g = 1; the
  re-coordination (a_i) ↦ (a_iξ^i) is the identity on 1-tuples, so
  "clause-3 re-coordination vacuous / deeper bytes identical" is the
  clause-3 prescription on the nose. z₁ = ξ·z₁′ checked. The orbit
  parametrization (w₀(b₀) = h₀ forced, c′ ≠ 0, mids strictly above via
  gcd) re-derived; the c₀ → c′ generalization of wave-18 S1 carries.
- **Runner semantics vs sheet:** lawful gate runs against the tower's
  OWN ψ₀′ (`lawful_check` reads `T.psi0`, post-override) — the Q1 claim
  is accurate; TLAW's closed form uses `C.z1_2` = the transported letter
  −c′; AV compares against transported ε₁; Φ″ = Φ₀^{e₀} + lift(c′)π^{h₀}
  is what `make_orbit_tower` builds (checked term-by-term) and
  `apply_pert` spans exactly the S1 freedom (tails/mids at amin) and
  rebuilds Φ₂ on the current (transported) ledger; CHI is
  measured-vs-measured (base cache vs twisted measured × ξ^{D₁}); the
  twists are a deterministic ≤ 2 enumeration; seed 20260911; CERT =
  T1/T2(nf=4)+T5 with the PARI-reuse disclosure accurate (no T11 call);
  ENG-GATE full=False as disclosed.
- **READ-EQ (given TAIL-STAB):** anchor/δ₁ = 0 leg (single K-slot digit,
  byte-identical) checked; the δ₁ = 1 one-pass comparison checked —
  ω(P) = γ+γ′ via the split identity (re-derived), key child at Γ+h₁ on
  both towers, b₀-main difference (ĉ′ − lift(c′)) at ledger ≥ Γ+e₁e₀,
  Φ′-only children ≥ Γ+1 with TAIL-STAB closing their descendants,
  slot-collision handling by the ultrametric, w₂ = Γ pinned by the
  nonzero on-line b₀-main digit on both sides. Sound given TAIL-STAB.
- **THEOREM/COR 1 (given READ-EQ):** Φ″ is a standard-lift instance of
  the accepted class at ψ₀ ↦ y + c′ (class admits any monic irreducible
  ψ₀ with ψ₀(0) ≠ 0); the accepted 2-read package (incl. ANCHOR-VAL) is
  consumed on it; the ξ = 1 slice is the lawful class (wave-18 S1 step 3
  degeneration to equality) so COR 1's scope = (ITER-LAW-LIFT)'s corner
  statement exactly. COR 2's χ-ratio algebra is a two-line consequence.
- **PROP:** honest — the rung-≥2 clause-(ii) census is explicitly a
  VERIFY-TARGET for the arc, cited not re-proved; clause (i) data shared
  by orbit members checked (deg, w₁, monic at g₀ = 1).
- **Q10 mapping observation (no finding):** Q10 has no dedicated counter;
  it rides TLAW/CHI on the 8 ξ = 1 control towers. The family-to-counter
  mapping was fixed at the seal (sheet + runner in one commit), so no
  post-hoc re-keying; the S3 Q10 bullet is a fair transcription.
- **Dating and grade language:** wallclock/campaign dates disclosed;
  ATTEMPT 0/2 + W-2 cap stated up front; "nothing here closes NR-1's
  ledger entry until this note's own acceptance arc runs" — respected in
  the repo state.

## 5. Bottom line

The instrument and its seal are exemplary — every number re-derives from
the roster and the re-run is bit-identical. The compose is one real step
short of its headline: (TAIL-STAB)'s recorded proof is broken at the
strict-descent line (F1), which is the exact step wave-18 left open. A
local repair (lexicographic (m, deg a); the mid-q-child drops coefficient
degree) appears available and would restore the whole S4 chain as
verified here, but until it is written and passed, "(TAIL-STAB) PROVED" /
"NR-1 DISCHARGED at attempt grade" stand on a defective argument, not
merely an unaudited one.

— passPE1, fresh hostile context, 2026-08-04 (campaign 2026-08-08).
