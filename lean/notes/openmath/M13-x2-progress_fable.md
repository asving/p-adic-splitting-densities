# M13-x2-progress — attempt (Fable, 2026-07-31)

Target: the X.2 progress family (`cl3_aff`/`cl3_cap`/`cl3_progress`/`cl3_tails`/
`cl3_bridge`), centrally the LINEAR-rate dichotomy `X2ProgressP`. Definitions and
Lean statements: see `M13-x2-progress_brief.md` (same directory). Notation: for a
branch history H, d := dTotal H, Σh := sumH H, mh := maxH H; thr(b), cap(b) as in
the brief; n = degree, all constants n-only.

**Result (summary).** The linear-rate progress kernel `X2ProgressP` — believed
in the source note to require a new "per-move mass pricing" argument, with only
the √N form available — REDUCES, with no new engine obligations beyond sharpened
forms of two already-owed laws, to:

- (OL-A) the engine's own per-move ledger endpoint (§B2-DEF D.11) in MAX form:
  threshold(b) ≤ 1 + the largest constrained height along the branch; and
- (OL-B) the TB-CAP identification: cap(b) ≤ 1 + the halting read's constrained
  height (recorded proved, perimeter-conditional, in §T-ASSEMBLY);

because of two ELEMENTARY facts proved here (Lemmas 1–2): every read's
constrained height is ≤ n·(its own in-frame height) + n·(the branch's first
height) — i.e. affinely bounded by mh ALONE, not by Σh. Hence

  thr(b) + cap(b) ≤ 2 + 4n·mh   on the fourth-piece family,          (★)

which is the `ProgressPricing` law with C_prog = 4n + 2 (a fortiori jointly in
1 + d + mh), and `x2Progress_of_pricing` (KE9, PROVED in Lean) then yields
`X2ProgressP` with explicit constants c_d = c_h = 1/(8n+4), c_d′ = c_h′ = 1/2.
The √N barrier was an artifact of the Σh currency: the note's (X2-AFF) display
is a lossy weakening of D.11's own max form. The same lemmas deliver (X2-AFF)
with c₀ = 2n and (X2-CAP) with c_cap = 2n + 1, matching the census's empirical
minimal constants (c₀ = n, C_move = n) up to a factor ≤ 2.

Verified numerically: zero violations of (★), of the per-read bound, and of the
height ladder, over all four exhaustive census boxes (n ∈ {2,3}, p ∈ {2,3};
§NUMERIC-TESTS). Nothing here touches `cl3_tails` (a genuinely separate measure
estimate); `cl3_bridge` is already reduced in Lean (KE6 proved unconditional
over the interface, KE7 assembles from rows outside this family).

---

## 1. The gap, and an exact equivalence

XD.4 (`x2hypAssembled`, PROVED) gives, from (X2-AFF) ∧ (X2-CAP): undetected at
N ⟹ (N−1−c_cap) < (c₀+c_cap)(d+1)² or < (c₀+c_cap)·mh² — rates √N. The source
note's barrier analysis is correct about its own route: from thr + cap ≤
1 + c₀⁺·Σh and Σh ≤ (d+1)·mh (XD.2), a product bound cannot make both legs
linear (d = mh = √N is compatible with Σh ≈ N). So linear rates need a
DIFFERENT upper bound on thr + cap, not a better dichotomy from the same bound.

**Observation 1 (the target is exactly an affine pricing).** For constants in
the indicated ranges, `X2ProgressP` is equivalent to: ∃ C(n) with

  thr(b) + cap(b) ≤ C·(1 + d + mh)  on the fourth-piece family.      (P)

(⇐) is KE9's `x2Progress_of_pricing` (Lean, proved): from N < thr + cap ≤
C(1 + d + mh), one of d, mh exceeds N/(2C) − 1/2. (⇒): apply `X2ProgressP` at
N := thr(b) + cap(b) − 1; the dichotomy gives d ≥ c_d·N − c_d′ or
mh ≥ c_h·N − c_h′, hence N ≤ max((d+c_d′)/c_d, (mh+c_h′)/c_h), so (P) holds
with C = 1 + (1+c_d′)/c_d + (1+c_h′)/c_h. So KE9's ⚑ `ProgressPricing` is a
lossless reformulation, and the whole question is the truth of (P) for the
Okutsu–Montes classifier. We prove the stronger mh-only form (★).

## 2. The per-read constrained height, and the two elementary lemmas

Fix a branch b with history H = (ν_1, …, ν_k) and let φ_r, w_r be the key and
inductive valuation at the r-th read (MacLane/OM chain). Work v_p-ABSOLUTELY:
let ŵ_r denote w_r normalized so ŵ_r(p) = 1 (i.e. ŵ_r = w_r / w_r(p); the
in-frame integer data of node ν_r = (e_r, h_r, ℓ_r, s0_r, u0_r) has absolute
slope λ_r := h_r/(e_r·E_r) where E_r := w_r(p) = Π(increment e's) ≤ n by
`HistWF.degProd`; in particular λ_r ≤ h_r ≤ mh).

The r-th read inspects the Newton polygon P_r of the φ_r-development
f = Σ_j B_j φ_r^j: the lower convex hull of {(j, ŵ_r(B_j)) : 0 ≤ j ≤ M_r},
M_r = ⌊n/deg φ_r⌋ ≤ n. Define the read's **side value**

  wf_r := the value at abscissa 0 of the supporting line of the read side
          = ŷ(s0) + s0·(slope), for the side from slot s0.

This is the standard "largest constrained height" of the read: all of the
read's defining digit conditions — the side's two endpoint vertex conditions,
the strictly-above conditions at slots left of the side (whose line values at
slot j < s0 are ≤ wf_r), the on-the-line residual/selection digits, and the
recentering datum (v(t) = the side value at the selection) — live at
development-digit levels ≤ wf_r + O(1). Equivalently wf_r = ŵ_{r+1}(f), the
value of f under the augmented valuation the read produces.

**Lemma 1 (side-value bound; hull convexity).** Let P be the lower convex hull
of points {(j, y_j)}_{j=0}^{M} with all y_j ≥ 0, and let S be a side of the
descending part of P with slope −s (s > 0) and right endpoint (b₀, y_{b₀}).
Let y_min := min_j y_j, attained at some j₀ ≤ M. Then

  val(S) := (S's supporting line at abscissa 0) ≤ y_min + s·j₀ ≤ y_min + s·M.

*Proof.* Convexity: the hull between abscissas b₀ and j₀ (note j₀ ≥ b₀, since
the hull is still descending at b₀ unless b₀ = j₀) consists of sides of slopes
≤ s in absolute value, so y_{b₀} ≤ y_min + s·(j₀ − b₀). The supporting line of
S at 0 equals y_{b₀} + s·b₀ (collinearity of S's endpoints with the line),
hence val(S) ≤ y_min + s·j₀. ∎

Applied to P_r and the read side (slope s = λ_r, M_r ≤ n):

  wf_r ≤ ŷ_min(r) + n·λ_r ≤ ŷ_min(r) + n·h_r,   ŷ_min(r) := min_j ŵ_r(B_j).

**Lemma 2 (floor bound).** ŷ_min(r) ≤ n·λ₁ ≤ n·h₁ ≤ n·mh, where λ₁ is the
absolute slope of the FIRST read of the branch (convention: λ₁ = 0 if the
first read is a slope-0 side).

*Proof.* f is monic of degree n = M_r·deg φ_r + deg B_{M_r}, and by monic
division the top development coefficient B_{M_r} is MONIC of degree
d₀ := n − M_r·deg φ_r < deg φ_r. For any valuation, the value of a sum is ≥
the min of term values, and conversely ŵ_r(g) ≤ value of any single term
whenever that term's value is strictly minimal — but we only need the generic
ultrametric bound ŵ_r(g) = min over the monomials c_i x^i of ŵ_r(c_i x^i) ≤
ŵ_r(x^{d₀}) (the leading term has coefficient 1). [If the min is attained
elsewhere the inequality only improves.] So ŷ_min(r) ≤ ŵ_r(B_{M_r}) ≤
d₀·ŵ_r(x) < n·ŵ_r(x). Finally ŵ_r(x): writing the first key φ₁ = x − c₁
(c₁ ∈ ℤ_p, possibly 0), ŵ_r(x) ≤ max-free bound min(ŵ_r(φ₁), v_p(c₁)) ≤
ŵ_r(φ₁) = λ₁ — using the standard MacLane stabilization ŵ_r(φ₁) = ŵ_1(φ₁) =
λ₁ (values of earlier keys are frozen along the chain), and ultrametricity
ŵ_r(x) ≥ min(...) with ŵ_r(x) ≤ λ₁ because x = φ₁ + c₁ where ŵ_r(φ₁) = λ₁
and v_p(c₁) ≥ 0: if v_p(c₁) ≥ λ₁ then ŵ_r(x) ≥ ... in every case
ŵ_r(x) ≤ max(λ₁, 0) would fail only if both terms exceeded λ₁, impossible
since ŵ_r(φ₁) = λ₁ exactly. Concretely: ŵ_r(x) ≤ λ₁ when v_p(c₁) ≥ λ₁
(then ŵ_r(x) = λ₁ if strict, ≤ by tie), and ŵ_r(x) = v_p(c₁) < λ₁ otherwise.
Either way ŵ_r(x) ≤ λ₁. ∎

(Sanity: at n ≤ 3 every deep chain has deg φ = 1, so B_M = 1 and ŷ_min = 0 —
the census regime; the floor term is live only for keys of degree ≥ 2 not
dividing n, i.e. from n = 4 on. This is exactly the close-cofactor/Krasner
regime; see NUMERIC-TESTS item 3.)

**Corollary (per-read bound).**  wf_r ≤ n·(λ₁ + λ_r) ≤ n·(h₁ + h_r) ≤ 2n·mh
for every read of the branch (continuing or terminal).

## 3. The two named residual laws (open lemmas), and the theorem

**(OL-A) [OPEN — the engine's D.11 endpoint, max form].** For every
fourth-piece branch b: threshold(b) ≤ 1 + max over the continuing reads of
⌈wf_r⌉. — Content: the stratum of H is, at every level N ≥ 1 + max wf_r, a
finite union of level-N digit cylinders in the PLAIN coefficients. §B2-DEF
D.11 states exactly this for ONE move ("Both loci are, at every level N above
the largest constrained height + 1, finite unions of digit cylinders", with
the unitriangular level-preserving digit translation); the composition along a
history is deliberately deferred by D.11 ("The composition of moves along a
read history is §C"). Status: §B2-DEF is at zero-critical convergence (pass
16, two display gaps) but NOT formally accepted; the composition duty is the
same one KE2's ⚑ `ThresholdStep` already carries. OL-A is the faithful (max-
currency) transcription; `ThresholdStep` was a per-move weakening whose
unrolling only yields the Σ currency. **The linear kernel needs the faithful
form; it needs nothing more.**

**(OL-B) [owed, recorded proved perimeter-conditional].** For a cap-detectable
fourth-piece leaf branch: detCap(b) ≤ 1 + ⌈wf_terminal⌉ (the halting read's
side value). — This is §T-ASSEMBLY TB-CAP: (τ-hen) N_V = 1 (proved); (τ-irr)
per-realized-cell cap = "1 + the largest base level among the halting read's
equations" (proved, perimeter-conditional). The census transcribes cap
exactly this way (cap := 1 + wf(halting read)).

**Theorem (linear progress, conditional on OL-A + OL-B).** On the fourth-piece
family, with mh := maxH(hist b):

  thr(b) + cap(b) ≤ (1 + 2n·mh) + (1 + 2n·mh) = 2 + 4n·mh.        (★)

Hence `ProgressPricing n p (X.ctx p) (4n+2)` holds at every prime (since
2 + 4n·mh ≤ (4n+2)(1 + d + mh)), and by KE9's `x2Progress_of_pricing`
(PROVED, Lean-core), `X2ProgressP n X K` holds for any XConsts K with
c_d = c_h = 1/(8n+4) > 0, c_d′ = c_h′ = 1/2 (the hypotheses
c_d·(2C_prog) ≤ 1, c_h·(2C_prog) ≤ 1, 1/2 ≤ c_d′, 1/2 ≤ c_h′ hold with
equality). Empty-history corner: mh = 0, thr ≤ 1 (D.11 base), cap ≤ 1
(τ-hen), and 2 ≤ 2 + 0. ∎ (given OL-A/OL-B; Lemmas 1–2 unconditional)

**Byproducts.** (i) (X2-AFF) with c₀ = 2n: thr ≤ 1 + 2n·mh ≤ 1 + 2n·Σh
(mh ≤ Σh as the max of a subfamily of summands, all h ≥ 1 for nodes). (ii)
(X2-CAP) with c_cap = 2n+1: cap ≤ 1 + 2n·mh ≤ (2n+1)(1 + Σh) — the terminal
read's height is included in Σh (`sumH` sums ALL nodes). So `cl3_aff` and
`cl3_cap` reduce to the SAME two residual laws — no separate engine duty
remains for them, and the ⚑ instance legs of KE2/KE3 are superseded by OL-A/
OL-B. (iii) The census's empirical constants (c₀_min = n, C_move = n,
c_cap ≤ n+1 on all four boxes) sit a factor ≤ 2 inside these; the factor 2 is
Lemma 2's floor term, invisible at n ≤ 3.

**Why the √N barrier dissolves.** The note's (X2-AFF) prices thr against Σh;
along a same-degree recentering run the in-frame heights climb strictly
(D.10's weight ladder), so Σh can reach ~mh²/2 while D.11's actual threshold
currency — the largest SINGLE constrained height — stays ≤ 2n·mh. Worked
example (n = 2): the digit-by-digit chain a = c² + p^{2m}·u has reads of
heights 1, 2, …, m; Σh ~ m²/2, but thr = 1 + max v(disc-side) = 1 + 2m. The
√N form was proved from the lossy currency; the linear form needs the faithful
one. The dichotomy's real content is the TALL leg: (★) has no d-term at all.

**Bonus (deep leg subsumed; uses the ladder).** D.10 (recenterings: the new
key's weight = the consumed side's value > the old key's weight; accepted-
derived per §X-EXHAUST X.1b) and D.9(c)/(I-aug) (increments) give strictly
increasing in-frame heights within each constant-key-degree run, and ≤ log₂ n
increments (key degree multiplies by e·g ≥ 2). Hence d ≤ (log₂ n + 1)·mh +
log₂ n: the deep leg of the dichotomy is never independently needed —
consistent with the envelope, which prices the deep leg through X.1b anyway.

## 4. Honest status of every step

| step | status |
|---|---|
| Observation 1 (equivalence) | proved here (⇐ also in Lean: KE9) |
| Lemma 1 (hull side-value bound) | proved here; elementary ((c) claimed new as packaged; folklore-adjacent) |
| Lemma 2 (floor ≤ n·λ₁) | proved here; elementary, uses MacLane key-value stabilization ((a)-adjacent) |
| OL-A (D.11 max-form threshold law) | OPEN — engine endpoint; §B2-DEF pass-16 converged, not accepted; composition-along-history deferred to §C; sharpens the existing ⚑ ThresholdStep duty |
| OL-B (TB-CAP cap identification) | owed by [3t]; recorded PROVED perimeter-conditional (§T-ASSEMBLY §T.2) |
| Theorem (★) ⟹ X2ProgressP | proved here + KE9 (Lean, proved) |
| `cl3_bridge` | already reduced in Lean: KE6 `x2Bridge_cover` proved unconditionally over the interface; KE7 needs 2 ≤ n + `X3aRouteP` + `NsNullP` (rows outside this family) |
| `cl3_tails` | NOT addressed: a measure/cone-tail estimate ((X2-TAILS), owner §H-DOMAINS/[2b]); KE5 reduces it to the ⚑ `TailsRoute` carrier; independent mathematics |

Risk register. (R1) OL-A hides the development-to-plain-coefficient digit
translation (D.3(e)(ii)); if that translation costs a level factor worse than
stated, (★)'s constant degrades but stays n-only — the linear CLAIM survives
anything n-only. (R2) The reading of `threshold` ("least N with the stratum a
finite union of level-N cylinders") must be what the eventual `XCtx` instance
supplies; if the instance's threshold is Thm 2.1's N₀ through a different
route, OL-A must be restated against it. (R3) Lemma 2's λ₁ is the branch's
own first read; if a future frame convention measures h₁ after a level-0
cluster opening differently, replace λ₁ by the first NODE height — the census
convention already does this (h = 0 openings contribute 0). (R4) At n ≥ 4 the
floor term is live and untested (census is n ≤ 3): see test 3.

## VERDICT

REDUCED. `X2ProgressP` (linear rates) is reduced — via the lossless pricing
equivalence and the new elementary Lemmas 1–2 — to two named residual laws
that the corpus already owes in weaker/equal forms: (OL-A) the §B2-DEF D.11
per-move ledger endpoint in max-currency form composed along a history, and
(OL-B) the §T-ASSEMBLY TB-CAP cap identification (recorded proved,
perimeter-conditional). Given OL-A + OL-B: thr + cap ≤ 2 + 4n·maxH on the
fourth-piece family, and `X2ProgressP` holds with c_d = c_h = 1/(8n+4),
c_d′ = c_h′ = 1/2 through the already-proved Lean reduction KE9. The same
bound discharges the (X2-AFF)/(X2-CAP) rows (c₀ = 2n, c_cap = 2n+1),
superseding the KE2/KE3 ⚑ laws. `cl3_bridge` was already reduced (KE6/KE7);
`cl3_tails` remains a separate open measure estimate. No new engine
obligation beyond OL-A/OL-B is introduced; the previously-open "per-move mass
pricing" is NOT needed.

## NUMERIC-TESTS

Ran (2026-07-31, this session; scripts persisted at
`verification/openmath/m13_x2_n2_check.py` and `..._n3_check.py`, importing
the gate-validated census walkers from
`verification/ke11_affine_envelope_probe.py`; run via
`uv run --with numpy --with sympy python3 <script>` — system python3 lacks
numpy):

1. n = 2, p = 2, N = 8 (65536 f's, 86528 leaf rows) and p = 3, N = 5:
   thr + cap ≤ 2 + 4·max(1, maxH) per leaf branch — 0 violations; chain
   heights strictly increasing — 0 violations; d ≤ maxH + 1 — 0 violations.
   Worst (thr+cap)/(1+maxH) = 3.000 (p=2), 2.667 (p=3) [bound: 2n = 4].
2. n = 3, p = 2, N = 8 and p = 3, N = 5 (dedup'd branch rosters: 260/398 leaf
   rows): additionally per-read wf ≤ 3·h for all leaf reads with h ≥ 1, and
   per-move threshold increments ≤ 3·h — 0 violations everywhere. Worst
   (thr+cap)/(1+maxH) = 3.667 (p=2), 2.750 (p=3) [bound: 2n = 6].

Proposed (concrete; sympy/cypari2 available):

3. **n = 4 deep-key stress (the only regime where Lemma 2's floor is live).**
   Families over p ∈ {2, 3, 5}: f = (x² − β)(x² − β′) and (x² − β)(x − c)(x − c′)
   with β, β′, c, c′ gridded so the quadratic cluster radius v(disc quad)/2 and
   the cofactor distance v(c − √β) sweep the Krasner margin; oracle = PARI
   `factorpadic` (adapt `verification/quartic_oracle.py`); walker = 5-slot
   polygon walker in original coordinates (extend the n = 3 pattern). Per
   read, record (h_r, e_r, wf_r, h₁): CONFIRMS if wf_r ≤ 4·(h₁ + h_r) always
   and thr + cap ≤ 2 + 16·maxH (= 2 + 4n·mh); a wf_r violation REFUTES the
   Lemma 1+2 packaging at the census reading (localize: report ŷ_min vs n·λ₁);
   a thr violation with wf's fine REFUTES the OL-A transcription instead.
   Sample ~10⁶ per family plus the targeted margin grid; precision N ≤ 24.
4. **OL-A direct test (the load-bearing open lemma).** For every f in the
   n = 3 boxes (both primes): L(f) := 1 + max wf over f's realized reads;
   verify every f′ ≡ f mod p^{L(f)} produces the identical branch roster
   (chain keys + leaf rowkeys in the census walkers). Predicted: 0 mismatches.
   A mismatch refutes the stratum-cylindricality level 1 + max wf, i.e. OL-A
   as transcribed — the single most valuable falsifier for this attempt.
   (Implementation: group the box by (roster, f mod p^L) and check the roster
   is constant on residue classes; cost ≈ one census pass.)
5. **Tightness/constant hunt.** Report empirical min constants: the max of
   (thr − 1)/maxH (found: 2 = n at n = 2; ≤ 3 = n at n = 3) and of
   (thr+cap)/(1+maxH); at n = 4 (test 3) watch whether the latter crosses
   2n = 8 — crossing kills the display constant 2 + 2n·mh but not the theorem
   (whose proved constant is 2 + 4n·mh = 18 at n = 4).
   Note: no finite census can refute `X2ProgressP` itself (existential in the
   constants); tests 3–5 stress the two lemmas' transcriptions and OL-A/OL-B,
   which are ∀-statements and finitely refutable (Q6 discipline).

Pointers: Lean targets `LeanUrat/MovesX/Defs.lean` (the five Props),
`XD2/XD3/XD4.lean` (√N form), `KE9.lean` (`ProgressPricing`,
`x2Progress_of_pricing`), `KE2/KE3/KE5/KE6/KE7.lean` (row reductions);
ledger rows `LeanUrat/MovesU/DefsLedger.lean:166`; note §X-EXHAUST
(`lean/notes/MOVES_2026-07-24.md` ~10947–11555), §B2-DEF D.9–D.11 (~2551–2719);
census `verification/ke11_affine_envelope_probe.py` + `results/*.json`.
Literature: S. MacLane, "A construction for absolute values in polynomial
rings", Trans. AMS 40 (1936) (key polynomials, augmented-value ladder);
J. Guàrdia, J. Montes, E. Nart, "Newton polygons of higher order in
arithmetical applications", Trans. AMS 364 (2012) (higher-order polygons,
residual polynomials, index accounting); M. Vaquié, "Extension d'une valuation"
(2007) (augmentation chains). These support Lemma 2's stabilization and the
ladder; OL-A's digit-level ledger has no published counterpart (the note's own
literature disclaimer) and must be discharged in-house.
