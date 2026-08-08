# HE7 passPE1 — hostile verification report (fresh context, zero prior stake)

**VERDICT: UNREFUTED / NOT CLEAN — 0 CRITICAL, 1 GAP, 3 MINOR (+3 remarks).
Machine leg bit-identical re-run GREEN (1,587 members / 0 violations / 6 teeth;
results JSON leaf-diff vs committed artifact = 0, including the supp peel leg
8/8 + 2/2 + 2/2). Fresh route GREEN: 2,552/2,552 PARI agreements on a NEW
n = 12, mu2 = 3 peel family at HE7-BOX-5's named coverage hole, 0 violations,
sigma(Psi) oracle 8/8.**

Target: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` at HEAD 0089f9b (r1
complete at 2970615; seal 1956151, verdict 4c42f9d, r1 commits
aafb481/d58680e/2970615). First hostile pass on this note. Prime surface per
HE7-BOX-1: the r1 text (widened HE7.A(3)/HE7.C, the Psi nmid f_S convention,
the S4.3 use-site display, S8's fifth row) and the three consumed
reconciliation lemmas HE6R1-1/2/3 (never attacked). Protocol:
quote-and-classify, fix nothing.

Attack order executed: (1) the (SLOT2)/(LIFT2) proofs S3/S4 re-derived line
by line; (2) the r1 widened jump condition — both S7 displays re-derived from
scratch to test the "l >= 2 -> l·d_r >= 2" substitution; (3) the convention +
peel: consumption-site sweep, peel/ladder composition, "at most once";
(4) S4.3's margin chain re-derived; (5) the termination induction re-derived
(n = 8, n = 16 threshold); (6) free hunt on the interfaces + both machine
instruments audited + LEMMA HE6R1-1/2/3 statements read at source
(`HE6R1_RECON_2026-08-08.md` S3.3/S3.4/S3.4b) and their HE7-side
restatements checked against them.

---

## FINDINGS

### F-1 [GAP] The read is continued through the alpha-refine on a key the
### S5 package is never proved for

**Location:** THEOREM HE7.A(3) (S2), S8 dictionary row 5, LEMMA HE7-8's
consumption (S7); the sealed battery takes this path on 41 members.

**Quote (S2, HE7.A(3)):** "the level-2 α-refine Ψ ↦ Ψ − ŝ₂·n₂(λ₂) exists —
(LIFT₂) supplies ŝ₂ with residue s₂ **because s₂ ∈ K₂** — and the refine
chain is FINITE (LEMMA HE7-8), so the read continues"

**Quote (S8, row 5):** "one side, λ₂ ∈ ℤ, R₂ = (Z−s₂)² — α-refine
(LEMMA HE7-8) → one of the above"

**The defect.** "The read continues" means THEOREM HE7.A's clauses (polygon,
twisted residual, dictionary rows 1–4, class sizes) are applied to the
REFINED key Ψ⁽¹⁾ = Ψ − w (dv₂(w) = λ₂ > T₂), and iteratively to Ψ⁽ʲ⁾. But
Ψ⁽ʲ⁾ is **not of DEFINITION HE6-1's form**, and the S5 package that feeds
HE7.A is proved only for DEFINITION HE6-1 keys: LEMMA HE7-4 (disk criterion)
is proved by citing "LEMMA HE6-2 multiplied by ℓ" and "LEMMA HE6-1 Step 1" —
both statements about the literal family Ψ_{κ,r}; LEMMA HE7-7 (ξ-side of the
test family, needed for the counting LEMMAS HE7-9/HE7-10 that give clause (1)
and the class sizes at the post-refine node) consumes HE7-4 for the key in
Step 1. No lemma of the note states the package for perturbed keys, and S8
explicitly declines the GENHN.C citation that could have covered μ₂ = 2 ("We
do not *cite* GENHN.C at level 2 … we re-derive the same five cases from
THEOREM HE7.A") — so the post-refine rows rest on HE7.A alone, i.e. on an
instance of HE7.A the note has not proved. The same unproved step recurs
inside LEMMA HE7-8's hypothesis ("each step at a node whose polygon is the
single side …"), which presumes the polygon/residual read is valid at every
Ψ⁽ʲ⁾, and in the strictly-increasing-slope clause (λ₂⁽⁰⁾ < λ₂⁽¹⁾ < ⋯), which
is the standard post-recentring slope jump but is asserted as part of the
chain's definition rather than derived for the read's actual chain.

**Why it is a GAP and not a CRITICAL (the repair is in the note's own
toolkit).** dv₂(w) = λ₂ > T₂ forces every Φ′-slot of w strictly above T₂,
while every occupied Φ′-slot of Ψ (including the top) sits at exactly T₂; so
Ψ⁽ʲ⁾ has the SAME slot values (d_r − t)u and the SAME slot residues (the
coefficients of r) as Ψ, plus above-the-line content. The disk criterion and
ξ-side arguments are slot-min arguments, and the S5.3 two-offset estimate
applies verbatim to the above-the-line content (its GAIN coefficients exceed
its DEFICIT coefficients, as the S5.3 remark itself observes) — I checked
that the estimate dv₂(w(ξ)) − dv₂(Ψ(ξ)) ≥ (λ₂ − T₂) + ε₁ − ℓ(D′−1)ε₀ > 0
closes in all three offset cases, so off-disk dv₂(Ψ⁽ʲ⁾(ξ)) = dv₂(Ψ(ξ)) and
the package extends. But that derivation is MINE, not the note's: as written
the chain HE7.A(3) → S8 rows at a refined key is unproven text.

**Failure scenario (of the text, not the math):** a reader granting only the
note's displayed lemmas cannot decide σ on the 41 sealed refine-path members
(e.g. Q1's ALPHA2 rows list refine firings on every prime); the verdict's
"the level-2 read decides σ" is underived exactly there. Downstream (assuming
the conclusion): everything checks — machine 41/41 with PARI, and my fresh
route's math-level check of the estimate above.

### F-2 [MINOR] (S5.2)'s ε₀ = 0 clause states a false dichotomy
### (not load-bearing)

**Location:** S5.3, display (S5.2).

**Quote:** "ε₁ = ℓ(λ − D′h) + ℓD′ε₀ ; if ε₀ = 0 then ε₁ ≥ ℓ(λ − D′h) > 0
unless δ ≥ λ, in which case ε₁ = 0. (S5.2)"

**Counter-instance:** ε₀ = 0 with D′h < δ < λ gives 0 < ε₁ = ℓ(λ − δ) <
ℓ(λ − D′h) — the claimed dichotomy (ε₁ ≥ ℓ(λ−D′h) or ε₁ = 0) misses the
whole middle band. Concretely at (e₁,f₁,h) = (2,1,1), λ = 5/2: any ξ with
dv(ξ) ≥ h and dv(Φ′(ξ)) = 9/4 ∈ (2, 5/2) has ε₀ = 0, ε₁ = 1/2 < 1 =
ℓ(λ−D′h). **Not load-bearing:** the final case analysis of S5.3 uses only
ε₁ > 0 (giving (κ₂−T₂) + ε₁ > 0) vs ε₁ = 0, and the ε₀ > 0 branch uses the
first (correct) half of (S5.2). Conclusion unaffected; the display is wrong.

### F-3 [MINOR] "μ₂ ≤ μ/2 ≤ 3" is literally false at μ = 7; integrality is
### used silently

**Location:** S2, THEOREM HE7.A(3) non-propagation paragraph (and the same
arithmetic shape in COROLLARY HE7.B(i)).

**Quote:** "at every n ≤ 15 (COROLLARY HE7.B(i): D′ ≥ 2 gives μ ≤ 7 and
THEOREM HE7.C gives μ₂ ≤ μ/2 ≤ 3)"

At μ = 7, μ/2 = 3.5 ≰ 3. The conclusion μ₂ ≤ 3 is correct but needs
μ₂ ∈ ℤ_{≥1} (μ₂ ≤ 3.5 ⟹ μ₂ ≤ 3), which the displayed chain does not invoke.
Pure display slip; every consumer only needs μ₂ ≤ 3.

### F-4 [MINOR] §S6 [r1](ii) cites (LIFT_i) for the level-i recentring
### constant; in HE7.D's own indexing that is (LIFT_{i−1})

**Location:** S6, "[r1] Both r1 items are level-generic" clause (ii).

**Quote:** "the α-refine case being ℓ_i = deg r_i = 1 (where (LIFT_i)
supplies the recentring constant because its residue lies in K_i)"

THEOREM HE7.D declares "(LIFT_i) surjectivity above bound_{i+1}" with
residues in K_{i+1} (so (LIFT₂) = (LIFT_1): level-0 datum has ℓ_0 = e₁,
K_1 = K, bound_1 = (D′−1)h, bound_2 = (‡₂) — checked). A refine at the
level-i node (r_i ∈ K_i[Z], slope λ_i) needs a residue in K_i at a height
< the level-i degree, i.e. (LIFT_{i−1}), exactly as the level-2 instance in
HE7.A(3) uses (LIFT₂) = (LIFT_1) for s₂ ∈ K₂. Off-by-one naming only; the
level-2 instance and the bound recursion are correct.

---

## REMARKS (not findings)

* **R-a (runner comment self-describes wrongly).** `he7_checks.py` line 140:
  "WIP = False  # commit 1 sealed this True (smoke only); commit 2 flips it"
  — the runner is byte-identical at seal 1956151 and verdict 4c42f9d (git
  shows an empty diff), i.e. WIP was already False at the seal and no flip
  ever happened in-history. The smoke record is disclosed in the docstring,
  so the preregistration is honest; the comment is stale about itself.
* **R-b (silent PARI-drop guard).** `run_row` drops a PARI job that fails to
  parse (`if g is None: continue`) without a violation; a systematic oracle
  failure would deflate `pari` rather than fire. Audited: every row has
  PARI = read-OK members (the one 124/122 row is exactly the 2 key-divides
  members, which never reach the oracle), so no drops occurred in the sealed
  artifacts.
* **R-c (redundant degenerate test).** Reader line 300:
  `any(v >= BIG for v in dv2s[:mu2]) and dv2s[0] >= BIG` ≡ `dv2s[0] >= BIG`.
  Harmless.

---

## CLEAN CHARGES (attacked and survived)

1. **(SLOT₂) S3 re-derived in full**: class separation is exactly
   gcd(u,ℓ) = 1 + integrality of dv(c_s); the within-class residue sum is
   nonzero because {1,β,…,β^{d_r−1}} is a K-basis of K₂ and attaining γ_t are
   unit-residues; cross-class terms sit strictly above the min; clause (c)'s
   inequality checked. The boundary case of the charge (δ₂ = κ₂ in HE7-7
   Step 2) is the CONCLUSION of the dichotomy, not a hole: min at t = 0
   (unique because r₂(0) ≠ 0 forces C₀ ≠ 0) for δ₂ > κ₂ incl. δ₂ = ∞, min at
   t = d₂ (monic) for δ₂ < κ₂ — both make Ψ₂(ξ) ≠ 0.
2. **(LIFT₂) S4.2**: the residue clause is DERIVED (via (SLOT₂)(b)'s γ-
   formula matching the prescribed lifts), not assumed by analogy; the
   (‡₂) ⟹ (†₂) arithmetic is exact; LEMMA HE7-L1's T(k) set, the sharp
   threshold, max_k = (D′−1)h, and both F1 counter-frames ((3,1,2): k = 1
   unattained; (2,2,1): k = 0,1 reach only F_Q) verified by hand.
3. **The r1 widened jump condition is verbatim-valid**: both S7 displays
   re-derived — μ ≥ L_λ = ℓ·deg R_λ ≥ m(ℓd_r) ≥ 4 and
   μ₂ ≤ n_λ/(D′ℓd_r) = deg R_λ/d_r ≤ μ/(ℓd_r) — no step uses ℓ ≥ 2
   structurally (no two-distinct-factor use); matches LEMMA HE6R1-1 at
   source. Iteration 4 ≤ μ_J ≤ μ/2^{J−1} ⟹ J ≤ log₂μ − 1 ≤ log₂n − 2;
   n = 8 forces D′ = 2, μ = 4, μ₂ ≤ 2, level 3 needs μ₂ ≥ 4 (re-derived at
   level 2, widened form) — degenerate; first J = 2 at n = 16. All checked.
4. **The Ψ ∤ f_S convention + peel**: the standing S1 CONVENTION covers
   S2–S8 and is displayed at all four named consumption sites (HE7.A,
   HE7-7″, S5.5, S8 row 5); HE7-9/HE7-10 sit inside the standing scope.
   Peel/ladder composition is exact: Ψ·(Σ A′_jΨ^j) IS the Ψ-development of
   f_S with A_j = A′_{j−1}, so the polygon shifts by one block and "every
   statement below applied to f_S′ at μ₂ − 1" is a shift, not a re-proof.
   "At most once" is PROVED (disc f_S ≠ 0 + Ψ irreducible ⟹ simple factor).
   LEMMA HE6R1-3's own proof (read at source): roots of gcd are level-2
   points (HE6-1 ξ-side at κ = λ) ⟹ orbit ≥ D″ (HE6-0′ forcing, incl. the
   e₁ℓ | e step via gcd(u,ℓ) = 1 which I re-derived) ⟹ gcd = Ψ, one orbit,
   (e,f) sandwich — sound.
5. **S4.3's margin chain re-derived**: k > T₂ strict at every use site
   (u₂ > ℓ₂T₂ ≥ T₂; α-refine at λ₂ > T₂ by HE7-9(a));
   m₀ > (d_r−1)u + λ from k > T₂ and s₀ ≤ ℓ−1; m_t > λ > D′h > (D′−1)h with
   margin > h ≥ 1; ℓ = 1 rerun gives the same chain with s₀ = 0. Exact.
6. **The S1 cocycle and DEFINITION HE7-3's inverse twist**: verified
   symbolically — s(k)+s(k′) ≡ s(k+k′) (mod ℓ) so c ∈ ℤ, Δm = −uc, quotient
   = (Φ′^ℓ/ϖ^u)^c; the telescoped exponent c_t = (s((d₂−t)u₂) + t·s(u₂) −
   s(d₂u₂))/ℓ; and the S5.3 Step-2 assembly Σ_t ι(c_{2,t}β^{c_{d₂}})β₂^t =
   ι(β^{c_{d₂}})·ι(r₂)(β₂) closes (the t = d₂ term is consistent at
   c_{2,d₂} = 1). My fresh leg's twist (c = w mod 2 at integer slope w,
   b₀ ↦ b₀s^{−c}) was derived from the note's cocycle alone and PARI
   confirmed it on 716 twist-live odd-slope members.
7. **S5.6 counting**: (RES₂) both-sides evaluation, the degree-(μ₂+1)
   blocker r₂,₀ (min-poly degree argument kills excess on both displays),
   the affine sampling in (T₂, λ₂,min) and the gaps, and the strict-excess
   nonemptiness comparison — all re-derived; multiplicity of Ψ₂'s roots is
   harmless (resultant counts with multiplicity, HE7-7 is per-root).
8. **S5.5 + LEMMA HE6R1-2 consumption**: r ∤ R_λ^{(g)} follows from level-1
   nonemptiness on g + disjointness of label classes; constancy of dv₂(g(ξ))
   and the h-function translation re-derived via generic test points; the
   note's claim chain is coherent (the lemma itself is HE6R1's, consumed).
9. **S6 deficit recursion**: (S6.1)–(S6.3) checked at j = 1 against S5.3
   (exact match, ρ₁ = ℓ[(λ₁−T₁) + ρ₀]); the ε-cascade (ε_{j−1} > 0 ⟹
   ε_j > 0 via δ_j = T_j − L_{j−1}ε_{j−1} < λ_j) rules out the ρ_j < 0
   corner, and the note displays the cascade ingredient.
10. **LEMMA HE7-8**: the completeness/limit argument (node condition +
    λ⁽ʲ⁾ → ∞ ⟹ coefficients → 0 ⟹ W converges ⟹ f_S = (Ψ−W)^{μ₂},
    contradicting disc ≠ 0) is sound and characteristic-free as claimed; the
    "(SLOT₂) forces O-coefficients → 0" step checked (both mins are over
    finitely many slots). (Its per-step polygon hypothesis is F-1's gap, not
    a defect of this lemma.)
11. **S8 fifth row + THEOREM HE7.A′ [r1]**: the peel at n = 8 re-derived
    (deg f′ = 4 = D″ + HE6-0′ forcing ⟹ f′ irreducible (4,1); σ third
    letter; alphabet closed at three values). COROLLARY HE7.B's scope
    sentence is consistent with the WIDENED HE6.B [r1] box (μ ≤ 7 at n ≤ 15
    via D′ ≥ 2; the ℓ = 1/deg r ≥ 2 branch consumed as the recon's literal
    instance; proper blocks via HE6R1-2 first live at n ≥ 10 — inside the
    clause's region as claimed). Q1's table sums re-checked: 1337 char-0
    members = 1335 PARI + 2 key-divides; 1587 total; READ2 = 1579 = 1587−8;
    supp distribution 2/3/2/1 reproduced in my sandbox re-run.
12. **HE7-BOX-2/BOX-5 honesty**: coverage claims audited against the runner
    (d_r = 1 asserted in the reader constructor and disclosed; the P3 leg
    genuinely runs f₁ ≥ 2, d_r ≥ 2, ≥ 3 frames incl. (3,1,2,2,3,13) and
    (1,2,1,3,2,11)). BOX-5's "peel at μ₂ ≥ 3 not exercised" was TRUE at HEAD
    and is now partially discharged by this pass's fresh leg (everything-
    block only; peel at a PROPER block remains proof-only, as the box says).

---

## MACHINE LEG (integrity)

* **Pins.** `he7_checks.py` md5 `688adbe88447b570104e379b1fa11cd5` identical
  at worktree = HEAD 0089f9b = seal 1956151 = r1 2970615, matching §S11's
  displayed pin. Artifacts `he7_checks_output.txt` `b2d095a2556a…`,
  `he7_checks_results.json` `f5bedab2ecda…` match §S11. `he7r1_supp.py`
  `24ece42e453865b4ebb1835007037fe4`; its pins (he7_checks.py 688adbe88447,
  results f5bedab2ecda, he6_checks.py 321fa4d4990e) verified in-run.
  The runner is byte-identical between seal and verdict commits (empty git
  diff) — the artifacts were produced by the sealed code.
* **Isolated re-run** (sandbox `/tmp/he7_pe1_sandbox`, committed artifacts
  untouched, full transitive import closure copied at HEAD): GREEN, 191.6 s,
  legs {READ2 1579, SLOT2 12632, GEN2 4259, SEP2 191, SIG2 1335, SEP2-inf 5,
  LIFT1 5, LIFT2 5}, VIOLATIONS 0, all six teeth FIRED; **results JSON
  leaf-diff vs committed artifact = 0** (bit-identical, timing included).
  Supp leg re-run in the same sandbox: 1,587 members reproduced, 8
  key-divides (distribution 2/3/2/1 = §S11 [r1]'s table), A1–A5 all 8/8 &
  2/2 & 2/2, 0 violations, 3.3 s.
* **Instrument audit.** The reader (`level2_read`) is PARI-free: Ψ-adic
  development, slot-min dv₂, hull, residual with explicit β-power twist,
  F_p factorization, dictionary — predictions are computed and stored BEFORE
  the PARI batch and compared string-independently; no tautological
  consumption. Teeth are real: WITHHOLD tests the reader's refusal path;
  BADTWIST is a genuine ablation (use_twist=False) scored against PARI;
  LIFT2SHARP enumerates reachable sets (W1/V1/W2) independently of the
  closed forms it checks; SLOT2TIE uses genuinely broken frames
  (gcd(u,ℓ) ≠ 1). Disclosed limitations honest (d_r = 1 reader assert =
  BOX-2's disclosure; oracle asymmetry = BOX-3). See remarks R-a/R-b/R-c.

## FRESH ROUTE (disclosed; differs from all prior routes)

Prior routes: (a) the sealed 1,587-member n = 8 battery; (b) HE6R1's
682-member ℓ = 1/d_r = 2 n = 8 battery; (c) r1's 8-member peel supp leg.
**This route: a NEW constructed family at the hole HE7-BOX-5 names as
unexercised — a peel at μ₂ = 3, degree n = 12** (also the first machine
contact of the level-2 read at μ = 6 ≥ 5 / n ≥ 10; block = everything, so
proper blocks stay unexercised — disclosed). Runner
`verification/openmath/he7_pe1_fresh.py` + artifacts (output txt, results
json): an INDEPENDENT reader written from the note's text alone (own exact
polynomial arithmetic, slot-min, level-1 polygon + residual check, level-2
polygon, twisted μ₂ = 2 residual from the S1 cocycle, S8 dictionary — no
import of he6/he7 code) and a cypari2 oracle (factorpadic +
nfinit/idealprimedec per factor; not the gp-subprocess path of the sealed
runners). Members f = Ψ³ + BΨ² + CΨ over ℤ_p, p ∈ {3,5,7}, s ∈ {1,2,3},
Ψ = (x²−p)² − sp²x, slot-prescribed B, C plus random noise; per member:
own level-1 read must give the single side (0,15)–(6,0) with residual
exactly (Z−s)³ (0 discards occurred), peel arithmetic A₀ = 0 / A₁ ≠ 0
exact, prediction σ(f) = {(4,1)} ⊔ dictionary(f_S′ at μ₂′ = 2).

**Result: 2,704 members, 2,552 predicted (152 repeated-residual members
skipped rather than refined — disclosed; the refine path gets no new machine
exercise from this route, cf. F-1), 2,552/2,552 PARI agreements, 0
violations; all six genres populated: {(8,1)} 792, inert even-slope 396,
split even-slope 320, inert ODD-slope (twist live) 396, split ODD-slope
(twist live) 320, two-sides 328; σ(Ψ) = {(4,1)} direct PARI 8/8 frames.**
This is the first machine confirmation of LEMMA HE6R1-3's peel composing
with a NONTRIVIAL level-2 read (letters {(8,1)}, {(4,2)} and splits behind
the peel, vs the committed legs' μ₂′ = 1 forced letter), of the μ₂ = 2
dictionary at n = 12, and of the twist at fresh slopes w ∈ {12, 13}.

## GRADE

0 CRITICAL. The composed results ((SLOT₂), (LIFT₂), the widened
HE7.A/HE7.C, TERMINATION, the peel, the n = 8 closure) all survived
re-derivation, and both machine instruments plus a fresh constructed family
corroborate them. But F-1 is a real justification gap on the never-attacked
surface (the post-refine read is underived text on a path 41 sealed members
take), so this pass is **NOT CLEAN**: the 2-clean count does not start.
HE7-BOX-1 stays **attempt grade 0/2**; owed next: an r2 that displays the
refined-key package (slot-domination + the S5.3 estimate suffice) and the
strict slope increase along the refine chain, plus fixes for F-2/F-3/F-4;
then a fresh hostile pass.
