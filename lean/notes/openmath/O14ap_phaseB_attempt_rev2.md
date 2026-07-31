# O-14a′ Phase-B attempt, REV 2 — the RunRealizerExists residue: the (S6b′) interior support clause + the last-node flank

**Leaf** (docs/MATH_COMPLETION_TREE_2026-08-01.md, D-10 split of O-14): the open residue of
`RunRealizerExists` — (a) the (S6b′) monomial-shape support clause at deg Φ > 1, (b) the
last-node (terminal) flank, where bare coherence carries no recentering record.
**Charge**: prove the interior support law as stage-tower mathematics, and analyze the
terminal node — prove it or name exactly the missing datum and whether coherence supplies it.
**Round-2 repair** (2026-07-31) responding to the hostile verification V11
(`V11_o14ap.jsonl`; verdict UNSOUND as a package, with §§2–4 and §5.1–5.2 individually
CONFIRMED sound — one CRITICAL error and one JUSTIFICATION GAP, both confined to the
§5.3–5.4 replacement-law section). This rev supersedes rev 1 (`O14ap_phaseB_attempt.md`)
as the statement of record; rev 1 is retained for the audit trail. All round-1-confirmed
sections are byte-identical to rev 1. Companion self-contained verifier package:
`O14ap_phaseB_verifybrief_rev2.md`.
**Author**: Phase-B prover unit O14ap. **No Lean edits**; math only.
**Falsifier suite**: `O14ap_check.py` (same directory) — ALL PASS (10/10; rev 1's checks
A–D byte-unchanged, round-2 checks added: E — the threaded slot law and the un-MacLane
regrade slopes at the HK23-gate numbers; F — the stretched-frame display void; G —
general-g sharpness, exhaustive at g = 3 over 𝔽₂₇, all unit offsets).

---

## Round-2 disposition table (every V11 finding; no silent drops, no rebuttals)

| # | V11 finding (gist, quoted) | Class | Disposition |
|---|---|---|---|
| 1 | "The recursion confuses the lower stage's wPrev-scale with its w-scale … the slot-minimum which creates wPrev_r uses e·w_{r−1}(t_k) + (j₀+ek)h, not e·wPrev_{r−1}(t_k) + (j₀+ek)h. By (STR), w_{r−1}(t_k) = σ_{r−1}.e·wPrev_{r−1}(t_k) … The proof works only under an additional σ_{r−1}.e = 1 condition, which §5.4 does not impose." | CRITICAL | **REPAIRED** (§5.3–§5.4). The law is rebuilt with the parent-frame stretch e★ := σ_{r−1}.e THREADED: the conversion law (THR) displays exactly the factor the verifier identified, and the recursion now prescribes every level's target in that level's wPrev/regrade scale, converting through (THR) at each ascent. (The Lean corpus independently compiled this mechanism: `HC2/HK52_stretchGate.lean`, `hk52_qform_stretch` — σ′.w B = e′·σV.w B — cited as compiled evidence of the corrected shape.) The verifier's condition e★ = 1 is ADOPTED as the per-level scope (class (U), §5.3) and shown not to defeat the general law: §5.6 proves the complement of (U) is a definitional VOID of the current clause triple — at a stretched frame no (n2) standard-lift display exists at all — so (U) is the entire statable domain, not a retreat. Falsifier checks E, F. |
| 2 | "Section 5.2 proves only a g = 2 instance … It does not prove the general assertion that, for arbitrary extension degree g, all g progression positions can be necessary. A basis argument could potentially support that claim, but it is not supplied." | JUSTIFICATION GAP | **REPAIRED** (§5.4.2). The basis argument is supplied: Θ(P) := z̄^{m(W)}·P(z̄) is a K_{r−1}-linear bijection from degree-< g polynomials onto K_r (unit multiple of a power basis), so the digit target with full-support P forces ALL g progression slots in every shaped realizer — sharpness at every g, within the same shaped class rev 1's tightness claim addressed (scope note displayed). Machine check G (exhaustive, g = 3 over 𝔽₂₇, all offsets). The g = 2 F₉ instance (§5.1–5.2) stands byte-stable as the S = {0,1} case. |

Both findings are accepted as stated; nothing is rebutted. The three round-1-CONFIRMED
results — the last-node closure (§3), the prime-field collapse (§2), the conditional F₉
refutation (§5.1–5.2) — and their §§1–4 apparatus are byte-identical to rev 1 below.

---

## 0. Verdict summary (the leaf re-cut; rev 2)

Let `RRE(p, F)` denote the compiled residual law (§1.5 below): *at every recentering node
of every coherent history over ambient residue field F, a realizer satisfying the three
CanRealizes clauses exists.* The results, most important first:

1. **THEOREM 3 (the last-node flank): CLOSED POSITIVELY, from bare coherence alone.**
   At every coherent history whose final node is a recentering, a center realizer (the
   CR clauses) exists. No extra datum is needed: the threshold `wPrev(Φ) < h` that the
   item-13 record named as the missing ingredient is DERIVABLE — at a run-anchor from the
   slope/width/stretch clauses of coherence itself (Lemma 3.1), and along a recentering
   run by transport through the `coeff_R` field of the recentering record plus a
   bare-Stage no-jump argument (Lemma 3.2). The anticipated StageCore-grade requirement
   dissolves. **Prediction: the LIVE flank countermodel search terminates empty**; the
   named "3-node extension of H₂ram by a recentering" target is moreover UNRECORDABLE
   (§3.4 scholium: the RG-2 fence blocks any third node after a ramified-pair read).
   [V11: CONFIRMED, no critical error.]
2. **THEOREM 1 (prime-field collapse) + COROLLARY 4: `RRE(p, ZMod p)` — the exact Prop
   the critical path consumes (TreeCan's (†15) pair runs at F = ZMod p) — is PROVED**
   for every prime p, under the current (RG-2-fenced) coherence predicate. Mechanism:
   over the ambient prime field every subfield is 𝔽_p, so every node's descend degree is
   g = 1 and every frame key is linear; the support clause is then automatically
   satisfied by ANY center realizer (all realizers are constants). The interior half was
   already on file; Theorem 3 supplies the terminal half; Theorem 1 supplies the support
   clause. The (†15) pair `canPolicy`/`canPolicy_pin` becomes fully dischargeable
   (fill recipe §4.2). [V11: CONFIRMED, no critical error.]
3. **THEOREM 5 (general ambient F, deg Φ > 1): the compiled singleton-support clause is
   REFUTED-AS-STATED at the intended stage semantics** — an explicit inert-quadratic
   countermodel at p = 3, F ⊇ 𝔽₉, center of multiplicative order 8 (§5.1; falsifier
   checks A1–A4; V11: arithmetic CONFIRMED, conditionality-flag confirmed honest). The
   FAITHFUL law is now the rev-2 **(S6b′-SUPP-2)** (§5.3): the carry-algebra support law
   with the parent-frame stretch factor e★ = σ_{r−1}.e THREADED through the recursion —
   the slot minimum consumes e·e★·(lower wPrev-scale target) + j·h, per the conversion
   law (THR), the mechanism the Lean corpus compiled independently as
   `hk52_qform_stretch`. It is PROVED on class (U) — all frames below the consumer
   unstretched (§5.4.1): the entire RG-2-recordable perimeter, all root- and
   post-recentering frames, and the §5.1/§5.5 instance class. General-g sharpness is
   PROVED by a basis argument (§5.4.2). The complement of (U) is proved to be a
   definitional void of the current clause triple (§5.6), so (U) is the entire statable
   domain. Rev 1's un-threaded law and g = 2-only sharpness claim (V11 findings 1, 2)
   are superseded; disposition table above.
4. **Scope fence (honesty, load-bearing):** result 2 RIDES the RG-2 recording fence
   (interior non-recentering reads pinned to e = 1). If that fence is ever lifted
   (post-§B2-FINAL), `RRE(p, ZMod p)` becomes refutable again by an explicit
   weight-lattice mechanism over a unit-shifted root key (§5.5; falsifier check D) —
   so the support clause must be re-adjudicated to the faithful law of §5.3 BEFORE any
   fence lift. Statement changes are sign-off items; none is performed here.
5. **NEW (round 2, §5.6): the stretched-frame void.** At every stretched frame
   (σ.e = e ≥ 2 — the configuration behind the RG-2 fence), the (n2) display's weight
   law σ.w(t_k) = h·(g−k) clashes with (STR)'s e·ℤ-valued coefficient weights whenever
   e ∤ (g−k) — in particular always at k = 0 when e ∤ g — so the tower cannot extend
   past such a frame under the current definitions at all (displayed instance: the
   compiled `ramifiedStage` at pair (2,5), g = 1; falsifier check F). Consequence: a
   fence lift must re-adjudicate the regrade/display weight laws themselves, not only
   (CR2) — §5.6, strengthening §5.5's forward obligation.

Grade requested: **REPAIRED** for the leaf as a whole (round 2: both V11 findings
repaired — the replacement law rebuilt with the stretch threaded and proved on its
entire statable domain (U), sharpness proved at every g by the basis argument; the
round-1-confirmed results are byte-stable; the consumed-instance statement
`RRE(p, ZMod p)` and the flank are PROVED outright).

---

## 1. Setting — the compiled objects restated as mathematics

All results below are theorems about the following structures; they mirror the compiled
definitions exactly (Moves/Defs.lean `Stage`/`IsRecentering`, Moves/DefsCore.lean
`IsRecenteringCore`/`ratRes`, Moves/DefsT.lean `TransitionData`, MovesC/Defs.lean
`Node`/`History`/`HistoryCoherent`/`RegradeOf`, MovesD/R7_polFillReduction.lean
`CanRealizes`/`RunRealizerExists`). The brief (`O14ap_phaseB_verifybrief.md`) restates
everything self-containedly; here I fix notation and list ONLY the clauses consumed.

### 1.1 Stages (the fields used)

Fix a prime p and a finite ambient field F. A **stage** σ over (p, F) carries: a pair
(e, h) ∈ ℕ² with e, h ≥ 1, gcd(e,h) = 1, a Bézout pair (s, t) with es + ht = 1 and the
pinning **(P2)** e = 1 → t = 0 (hence s = 1 by Bézout); a monic key Φ ∈ ℤ_p[X] with
deg Φ ≥ 1; valuation-like maps w, wPrev : ℤ_p[X] → ℤ; a subfield K ≤ F (current residue
field) with base subfield F_Q ≤ K; a residual map R : ℤ_p[X] → K[z^{±1}] (Laurent
polynomials over K, variable z = T 1). Write C_Φ := {B : deg B < deg Φ} (the coefficient
space). Axioms consumed:

* **(S1)** w(fg) = w(f) + w(g) and min(w f, w g) ≤ w(f+g) on nonzero (and nonzero-sum)
  arguments. [`hwmul`, `hwult`] Consequence used freely: w(1) = 0, w(−f) = w(f).
* **(wΦ)** w(Φ) = h. [`hwΦ`]
* **(STR)** for nonzero B ∈ C_Φ: w(B) = e·wPrev(B). [`hStretch`]
* **(R×)** R(fg) = R(f)R(g) (nonzero args); **(R<)** if w(f) < w(g), f, g, f+g ≠ 0 then
  R(f+g) = R(f); **(R0)** R(f) ≠ 0 for f ≠ 0. [`hRmul`, `hRlt`, `hRne`]
* **(RΦ)** R(Φ) = z^s (coefficient 1). [`hRΦ`]
* **(S6b)** for every ν ∈ ℤ with wPrev(Φ) < ν and every a ∈ Kˣ there is B ≠ 0, B ∈ C_Φ,
  wPrev(B) = ν, R(B) = a·z^{−tν}. [`hS6b`]

At an e = 1 stage, (P2) gives t = 0 and s = 1: coefficient digits sit at z-position 0
and R(Φ) = z.

### 1.2 Nodes (the fields used)

A **node** ν carries: a species (root / increment / recentering); a frame stage ν.σ; the
read pair (ν.e, ν.h) coprime, ≥ 1, with canonical Bézout (0 ≤ ν.t < ν.e); descend data
(ψ, g, μ) with ψ ∈ (ν.σ.K)[z] monic irreducible of degree g ≥ 1, μ ≥ 1; a residue root
z̄ ∈ Fˣ with ψ(z̄) = 0 [`hzbarRoot`]; block width Dwidth = deg(ν.σ.Φ) [`hDwidth`]; a read
line (rational intercept/slope, evaluated Line.at(b) = intercept − slope·b); recorded
center ∈ ν.σ.K and lift ∈ ℤ_p[X]. Species laws: an increment has e·g > 1; a recentering
has e = 1 ∧ g = 1 [`hspecRec`], ψ = z − center, and z̄ = center as elements of F
[`hspecRecCenter`] — since z̄ is a UNIT of F, **every recentering node's center is
nonzero** (used at the terminal node, where no coherence record supplies it).

### 1.3 Histories and coherence (the clauses used, labelled)

A **history** H is a nonempty node list with species = root exactly at index 0
[`root_iff`]. STR_i := ∏_{j<i} ν_j.e (the stretch of frame i); D_i := ν_i.Dwidth.
**HistoryCoherent H** consists of (guards as compiled):

* **(C1)** deg(σ₀.Φ) = 1 (the root frame is linear).
* **(C2)** for every i < len: slope_i · (ν_i.e · STR_i · D_i) = ν_i.h (the absolute-scale
  slope law). Since the right side is ≥ 1 and the multiplier is > 0: every slope_i > 0.
* **(C3)** the γ-tie (not consumed below).
* For every i with i+1 < len:
  * **(C4-rec)** if ν_i is a recentering: IsRecenteringCore σ_i σ_{i+1} (ν_i.center)
    (ν_i.lift), which bundles [`IsRecentering` + records]:
    (r1) σ_i.e = 1; (r2) σ_{i+1}.e = 1; (r3) center ≠ 0; (r4) lift ∈ C_{σ_i.Φ}, ≠ 0;
    (r5) σ_i.w(lift) = σ_i.w(σ_i.Φ); (r6) σ_i.R(lift) = C(center)·T 0;
    (r7) σ_{i+1}.Φ = σ_i.Φ − lift; (r8) σ_{i+1}.w = σ_i.w and σ_{i+1}.wPrev = σ_i.wPrev
    (pointwise); (r9) σ_{i+1}.K = σ_i.K, σ_{i+1}.FQ = σ_i.FQ; (r10) **coeff_R**: for all
    B ∈ C_{σ_i.Φ}: σ_{i+1}.ratRes(B) = σ_i.ratRes(B), where ratRes embeds R(B) into the
    rational-function field F(X) by z ↦ X through K ↪ F.
  * **(C4-non)** if ν_i is NOT a recentering: **ν_i.e = 1 (the RG-2 fence)**, and there
    is a regrade σV with RegradeOf σ_i (ν_i.e) (ν_i.h) σV — in particular σV.w is the
    (ν_i.e, ν_i.h)-slot-minimum weight over σ_i.w on σ_i.Φ-developments — and
    IsNodeLift ν_i (σ_{i+1}.Φ) — the standard-lift display σ_{i+1}.Φ = Φ^{eg} +
    Σ_{k<g, ψ_k≠0} t_k Φ^{ek} with t_k ∈ C_{σ_i.Φ}, t_k ≠ 0, σ_i.w(t_k) = ν_i.h·(g−k) —
    and TransitionCoreL σV σ_{i+1} (σ_{i+1}.Φ) (ν_{i+1}.e) (ν_{i+1}.h) (ν_i.z̄), whose
    TransitionData part supplies **(T1)** σ_{i+1}.e = ν_{i+1}.e, **(T2)** σ_{i+1}.h =
    ν_{i+1}.h, **(T3)** σ_{i+1}.wPrev = σV.w pointwise, **(T4)** σ_{i+1}.Φ is the
    IsNodeLift target (child_key).
  * **(C5)** window containment (not consumed); **(C6)** D_{i+1} = ν_i.e · ν_i.g · D_i;
    **(C7)** slope_i < slope_{i+1} (strict steepening).

### 1.4 The realizer clauses

**CanRealizes ν t** (t ∈ ℤ_p[X]):
* **(CR1)** t ≠ 0;
* **(CR2)** [the support clause under adjudication] ∃ j₀ ∈ ℕ with j₀ ≡ bezT(ν.e, ν.h)·ν.gam
  (mod ν.e), such that every X-exponent in the support of t is of the form j₀ + k·ν.e
  with k < ν.g. *At a recentering (e, g) = (1, 1): t must be an X-monomial (singleton
  support), the congruence being vacuous mod 1.*
* **(CR3)** if ν is a recentering: t ∈ C_{ν.σ.Φ} ∧ ν.σ.w(t) = ν.σ.w(ν.σ.Φ) ∧
  ν.σ.R(t) = C(ν.center)·T 0.

### 1.5 The residual law

**RRE(p, F)** [`RunRealizerExists p F`]: for every coherent history H over (p, F), every
index i, if ν_i is a recentering then ∃ t, CanRealizes ν_i t.

The compiled reduction on file (`canPolicyC_pin`) turns any proof of RRE(p, ZMod p) into
a full discharge of the (†15) pair; the interior CR3-half is on file
(`interior_center_realizer_exists`). What follows is the mathematics of the residue.

---

## 2. Theorem 1 (prime-field collapse) — the support clause is free at F = 𝔽_p

**Theorem 1.** Let F = 𝔽_p (the compiled `ZMod p`). Then for every coherent history H:
(i) every node has g = 1; (ii) every frame key is linear: deg(σ_i.Φ) = 1 for all i;
(iii) at every recentering node ν, ANY t satisfying (CR1) + (CR3) also satisfies (CR2).

*Proof.* (i) The only subfield of the prime field 𝔽_p is 𝔽_p itself (a subfield contains
1 and is closed under addition, hence contains the prime subfield, which is everything).
So every stage has K = 𝔽_p, and the inclusion K ↪ F is an isomorphism. Each node carries
ψ ∈ K[z] irreducible with a root z̄ ∈ F = K (clause `hzbarRoot` transported through the
isomorphism): then (z − z̄) divides ψ in K[z]; ψ irreducible and (z − z̄) a non-unit force
ψ = (z − z̄)·(unit), so deg ψ = 1, i.e. g = 1 (clause `hψdeg`). This holds for every
node, every species. — (ii) Induction on i. Base: D₀ = deg(σ₀.Φ) = 1 by (C1) + `hDwidth`.
Step: by (C6), D_{i+1} = ν_i.e·ν_i.g·D_i. Here ν_i.g = 1 by (i); and ν_i.e = 1 — by
`hspecRec` if ν_i is a recentering, by the RG-2 fence in (C4-non) otherwise (i is
interior since i+1 < len; the root node also passes through (C4-non)). So D_{i+1} = D_i
= 1, and `hDwidth` at node i+1 gives deg(σ_{i+1}.Φ) = D_{i+1} = 1. — (iii) By (CR3),
t ∈ C_{σ.Φ} means deg t < deg σ.Φ = 1: t is a nonzero constant, so its X-support is {0}.
Take j₀ = 0: the congruence mod ν.e = 1 is vacuous (every integer reduces to 0 mod 1),
and 0 = j₀ + 0·1 with 0 < g = 1. ∎

**Remark (scope, load-bearing).** Step (ii) consumes the RG-2 fence. The fence is a
disclosed definitional scope restriction of the current coherence predicate (interior
non-recentering reads recorded only at stride e = 1); Theorem 1(ii) is exactly as
conditional as the fence. See §5.5 for what happens if it lifts. Step (i) and (iii) are
fence-free.

**Remark (thinness, disclosed).** Theorem 1(ii) says the compiled tree model at
F = ZMod p records only linear-key towers (root read + recentering chains + at most a
terminal increment). This is not a defect introduced here — it is the compiled typing's
consequence (subfield-tracked residues inside a prime ambient field + the fence), and it
is consistent with the project's disclosed order-0-slice scope. It should be REPORTED
whenever the (†15) discharge is cited: the pin becomes real, at this recorded scope.

---

## 3. Theorem 3 (the last-node flank) — terminal center realizers from bare coherence

Throughout §3, H is coherent with len ≥ 1 nodes, and the FINAL node ν_T (index
T = len − 1) is a recentering. Since index 0 has species root, T ≥ 1. Let b ≤ T be the
least index such that ν_b, ν_{b+1}, …, ν_T are all recenterings (the maximal terminal
recentering run); then b ≥ 1 and ν_{b−1} is NOT a recentering. Write σ_i := ν_i.σ,
h_i := ν_i.h, e_i := ν_i.e, g_i := ν_i.g.

**Theorem 3.** There exists t with (CR1) ∧ (CR3) at ν_T. Combined with Theorem 1(iii),
at F = 𝔽_p there exists t with CanRealizes ν_T t.

The proof is Lemmas 3.1–3.3.

### 3.1 Lemma (run-anchor threshold, from bare coherence)

**Lemma 3.1.** σ_b.e = 1, σ_b.t = 0, and the (S6b) threshold holds at σ_b:
σ_b.wPrev(σ_b.Φ) < σ_b.h. Moreover σ_b.h = h_b and σ_b.wPrev(σ_b.Φ) = e_{b−1}·h_{b−1}·g_{b−1}.

*Proof.* The transition at i = b−1 exists (b−1+1 = b ≤ T < len) and takes the
(C4-non) leg (ν_{b−1} is not a recentering). It supplies (T1)–(T4), the regrade σV, and
IsNodeLift ν_{b−1} (σ_b.Φ).

(a) *Pair:* σ_b.e = ν_b.e = 1 by (T1) + `hspecRec` at ν_b; then σ_b.t = 0 by (P2), and
σ_b.h = h_b by (T2).

(b) *The lift's regraded weight.* Write (e, h, g) := (e_{b−1}, h_{b−1}, g_{b−1}) and
Φ := σ_{b−1}.Φ. By IsNodeLift, σ_b.Φ = Φ^{eg} + Σ_{k<g, ψ_k≠0} t_k Φ^{ek} with each
present t_k ∈ C_Φ, t_k ≠ 0, σ_{b−1}.w(t_k) = h(g−k). This display IS a Φ-development of
σ_b.Φ: slot eg carries the constant 1, slot ek carries t_k (present k), all other slots 0
— all coefficients of degree < deg Φ (deg Φ ≥ 1). The developed polynomial is nonzero
(monic of degree eg·deg Φ: the top slot dominates, every other summand has strictly
smaller degree). RegradeOf's slot-minimum law evaluates σV.w on it: occupied slot
weights are e·σ_{b−1}.w(coefficient) + (slot)·h, i.e.

    slot eg:  e·w(1) + eg·h = 0 + egh = e·h·g        (w(1) = 0 by (S1))
    slot ek:  e·h(g−k) + ek·h = e·h·g                 (present k < g).

Every occupied slot weighs exactly ehg and at least one (slot eg) is occupied, so the
attained minimum is σV.w(σ_b.Φ) = e·h·g. By (T3), σ_b.wPrev(σ_b.Φ) = σV.w(σ_b.Φ) = ehg.

(c) *The strict inequality h_b > e·h·g, from the slope clauses.* By (C2) at i = b−1 and
i = b, and positivity of slopes:

    h_{b−1} = slope_{b−1} · (e_{b−1} · STR_{b−1} · D_{b−1}),
    h_b     = slope_b · (e_b · STR_b · D_b),   with e_b = 1.

By definition STR_b = STR_{b−1}·e_{b−1}, and by (C6) D_b = e_{b−1}·g_{b−1}·D_{b−1}. So

    h_b = slope_b · (STR_{b−1}·e) · (e·g·D_{b−1})
        > slope_{b−1} · e·STR_{b−1}·D_{b−1} · (e·g)          [(C7); the multiplier
                                                              e²·g·STR_{b−1}·D_{b−1} > 0]
        = h_{b−1} · e · g = e·h·g.

(All quantities are positive naturals/rationals: e, g, h ≥ 1 by node typing, STR ≥ 1 as
a product of e's, D ≥ 1 since D = deg(frame key) ≥ 1.) Hence
σ_b.wPrev(σ_b.Φ) = ehg < h_b = σ_b.h. ∎

*Falsifier check C (100k random instances of the (C2)/(C6)/(C7)/stretch laws): zero
violations of the derived inequality.*

**Note.** Lemma 3.1 is fence-INDEPENDENT: the computation in (b)–(c) is written for
general e_{b−1} and survives a future fence lift. It is also exactly the compiled probe's
missing ingredient: `centerRealizer_exists_of_unramified_threshold` needed precisely
(a) + the threshold, both now derived from coherence.

### 3.2 Lemma (transport along the recentering run)

**Lemma 3.2.** For every r with b ≤ r ≤ T:
(i) σ_r.e = 1 (hence σ_r.t = 0, σ_r.s = 1);
(ii) σ_r.w = σ_b.w and σ_r.wPrev = σ_b.wPrev pointwise; σ_r.K = σ_b.K;
(iii) deg(σ_r.Φ) = deg(σ_b.Φ), and σ_r.w(σ_r.Φ) = σ_b.w(σ_b.Φ) =: H (= h_b);
(iv) for every B ∈ C_{σ_b.Φ}: σ_r.R(B) = σ_b.R(B) (equal Laurent polynomials over the
common K).

*Proof.* Induction on r; everything is trivial at r = b ((i): Lemma 3.1(a); (iii):
σ_b.w(σ_b.Φ) = σ_b.h = h_b by (wΦ)). For the step r → r+1 (r ≤ T−1, so the transition at
i = r exists and takes the (C4-rec) leg, ν_r being a recentering):

(i) (r2) gives σ_{r+1}.e = 1; then (P2) and Bézout give t = 0, s = 1.

(ii) (r8), (r9) + induction.

(iii) Write Φ_r := σ_r.Φ, t_r := ν_r.lift, H := σ_r.w(Φ_r) (induction: = h_b). By (r7),
Φ_{r+1} = Φ_r − t_r, of the same degree (t_r ∈ C_{Φ_r}, Φ_r monic) — hence also
C_{Φ_{r+1}} = C_{Φ_r} as degree conditions. **No-jump claim:** σ_r.w(Φ_r − t_r) = H.
Indeed w(t_r) = H by (r5) and w(−t_r) = w(t_r) (from (S1): w(1) = 0, w(−1) = 0). Both
Φ_r and −t_r are nonzero, and Φ_r − t_r ≠ 0 (monic of degree ≥ 1). By (S1)-ultrametric,
w(Φ_r − t_r) ≥ min(H, H) = H. Suppose w(Φ_r − t_r) > H. Apply (R<) to the decomposition
Φ_r = t_r + (Φ_r − t_r), whose first summand has the strictly smaller weight:
R(Φ_r) = R(t_r). But R(Φ_r) = z^{σ_r.s} = z¹ by (RΦ) + (i), while R(t_r) = C(center_r)·T 0
by (r6) — a z-degree-1 monomial with coefficient 1 versus a nonzero constant: comparing
coefficients at exponent 0 gives 0 = center_r ≠ 0 (r3), contradiction. So
σ_{r+1}.w(σ_{r+1}.Φ) = σ_r.w(Φ_r − t_r) = H (using (r8) for the w-identification).

(iv) For B ∈ C_{σ_b.Φ} = C_{σ_r.Φ}: (r10) gives σ_{r+1}.ratRes(B) = σ_r.ratRes(B).
ratRes embeds K[z^{±1}] into F(X) by z ↦ X through the (common, by (ii)) inclusion
K ↪ F; this embedding is INJECTIVE: if Σ_{k=−N}^{M} c_k X^k = 0 in F(X), multiply by X^N
to get a polynomial identity over the field F, so all c_k = 0 in F, so all c_k = 0 in K
(the inclusion is injective). Hence σ_{r+1}.R(B) = σ_r.R(B) as Laurent polynomials, and
the induction closes. ∎

### 3.3 Proof of Theorem 3

The center c := ν_T.center is nonzero (§1.2: `hspecRecCenter` + z̄ ∈ Fˣ — this is the one
datum the flank needed that NO coherence record supplies, and node typing supplies it).
By Lemma 3.2(ii), c ∈ σ_T.K = σ_b.K, and c ≠ 0 makes it a unit of the field σ_b.K.

Apply (S6b) at σ_b with ν := σ_b.h = H and scalar c: since σ_b.wPrev(σ_b.Φ) < H
(Lemma 3.1), there is B ≠ 0, B ∈ C_{σ_b.Φ}, σ_b.wPrev(B) = H, and
σ_b.R(B) = C(c)·T(−σ_b.t·H) = C(c)·T 0 (σ_b.t = 0).

By (STR) at σ_b (e = 1): σ_b.w(B) = σ_b.wPrev(B) = H. Now transport to the terminal
frame by Lemma 3.2: B ∈ C_{σ_T.Φ} (equal degree conditions), σ_T.w(B) = σ_b.w(B) = H =
σ_T.w(σ_T.Φ) (Lemma 3.2(iii)), and σ_T.R(B) = σ_b.R(B) = C(c)·T 0 (Lemma 3.2(iv); the
case T = b is Lemma 3.1 + (S6b) directly, with no transport). So t := B satisfies (CR1)
and (CR3) at ν_T. ∎

### 3.4 Scholium (the LIVE countermodel search; the H₂ram target)

Theorem 3 predicts the flank countermodel search finds nothing. Independently, its named
"natural target" — a 3-node extension of the ramified-pair 2-node gate by a recentering
read — is UNRECORDABLE under the current predicate: in any 3-node coherent history the
middle node is interior, so it either is a recentering (pair e = 1 by `hspecRec`) or
passes the (C4-non) leg, whose RG-2 fence pins its e to 1; a middle node with read pair
e = 2 (the ramified-pair gate's second node) admits neither leg. So the search space for
that target is empty for reachability reasons — and by Theorem 3 every other target is
empty for mathematical reasons. The item-13 record's fallback ("a countermodel would
re-adjudicate the quantifier to the JetSetup carrier") is therefore NOT needed: the bare
`HistoryCoherent` quantifier stands, now with a proof.

---

## 4. Corollary 4 — RRE(p, ZMod p) is PROVED; the (†15) fill recipe

**Corollary 4.** For every prime p, `RunRealizerExists p (ZMod p)` holds — i.e. at every
recentering node of every coherent history over the prime ambient field, a CanRealizes
witness exists — under the current (RG-2-fenced) coherence predicate.

*Proof.* Let ν_i be a recentering node of a coherent H.
* If i + 1 < len (INTERIOR): the (C4-rec) record at i hands over the recorded lift
  t := ν_i.lift with (CR1) from (r4), and (CR3) from (r4)+(r5)+(r6) — this is exactly
  the on-file interior lemma (`interior_center_realizer_exists`). (CR2) holds by
  Theorem 1(iii).
* If i = len − 1 (TERMINAL): Theorem 3 supplies t with (CR1)+(CR3); (CR2) again by
  Theorem 1(iii). ∎

### 4.2 Lean fill recipe (NOT executed here — no Lean edits in this unit)

The compiled reduction `canPolicyC_pin : RunRealizerExists p F → OffsetPPin (canPolicyC p F)`
is on file with 0 sorries. Corollary 4's proof formalizes along these seams:
1. `subfield_eq_top : ∀ K : Subfield (ZMod p), K = ⊤` (prime-field collapse, Thm 1(i) —
   a Mathlib-adjacent lemma), then `g_eq_one : ν.g = 1` via `hψirr`/`hzbarRoot`/`hψdeg`
   through the `Subfield.subtype` isomorphism;
2. `frame_deg_one` : induction over the width chain (C6) with the fence + `hspecRec`
   (Thm 1(ii)); then (CR2) from `Polynomial.eq_C_of_degree_le_zero`;
3. `anchor_threshold` (Lemma 3.1): the σV.w evaluation via `IsSlotMinWeight` on the
   `IsNodeLift` display + the ℚ-inequality chain from (C2)/(C6)/(C7)/`strFrame`;
4. `run_transport` (Lemma 3.2): list induction on the terminal run; the no-jump step via
   `hRlt` + `hRΦ` + Laurent coefficient comparison; `coeff_R` + injectivity of
   `LaurentPolynomial.eval₂` at `RatFunc.X` (a self-contained lemma);
5. assemble as in Corollary 4; then `canPolicy p := canPolicyC p (ZMod p)`,
   `canPolicy_pin p := canPolicyC_pin (proof)`, discharging the (†15) pair and the
   D-group `sorryAx`.
Estimated scale: one new module (~300–450 lines), no statement changes anywhere.

---

## 5. Theorem 5 — the support clause at general ambient F: refutation and the faithful law

### 5.1 The countermodel (intended semantics, p = 3, F ⊇ 𝔽₉)

Take the intended (MacLane/GMN order-1) stage pair over ℚ₃, ambient F = 𝔽₉ = 𝔽₃(i),
i² = −1:
* σ₀ — the base stage at pair (1, 1): key Φ₀ = X, w₀(Σ a_j X^j) = min_j (v₃(a_j) + j),
  K₀ = 𝔽₃ ≤ F, R₀ the Gauss residual (digit of a constant u = 3^m·û is û mod 3 at
  z-position 0; s₀ = 1, t₀ = 0). This is the compiled base-stage construction; all §1.1
  axioms hold for it (dual-accepted §A/§B1 content).
* Root read ν₀: species root, pair (e₀, h₀) = (1, 1), descend ψ₀ = z² + 1 ∈ 𝔽₃[z]
  (irreducible; z̄₀ := i), g₀ = 2, μ₀ = 1, side slots 0..2 with pattern (1, 0, 1)
  (Ranch₀ = ψ₀, ord_{ψ₀} = 1), s0 = 0, wSide = 2, D₀ = 1, slope₀ = 1.
* Standard lift: σ₁.Φ = Φ₀² + t₀' with t₀' = 9 (the (k = 0)-realizer: w₀(9) = 2 = h₀·g₀,
  digit 1 = ψ₀-coefficient at position 0). So σ₁.Φ = X² + 9 — genuinely the inert
  quadratic frame over ℚ₃ (PARI: irreducible, one degree-2 factor; e = 1, f = 2;
  falsifier check B).
* σ₁ — the child stage at pair (1, 3): K₁ = 𝔽₉, w₁ = the (1,3)-slot-minimum over w₀ on
  Φ̂-developments (the MacLane augmentation assigning the key value 3), wPrev₁ = σV.w =
  w₀-regraded (here σV.w = w₀ on coefficients since e₀ = 1); R₁ the order-1 residual:
  for B = aX + b ∈ C_{Φ̂} with both Φ₀-slots at the w₀-minimum,
  R₁(B) = C((b̄ + ā·i)·i^{m})·T 0 for a fixed exponent m = m(w₀-weight) (the transition's
  frame-unit offset; ā, b̄ the leading 𝔽₃-digits). All §1.1 axioms hold: this is the
  standard order-1 residual apparatus (in particular (S6b) at σ₁ holds BECAUSE two-slot
  coefficients realize every scalar: {b̄ + ā·i} covers 𝔽₉ ∖ {0} — falsifier check A4).
* Terminal recentering ν₁: pair (1, 3) (slope₁ = 3/2 > 1 = slope₀, satisfying (C2)/(C7):
  h₁ = slope₁·(1·1·2) = 3 > e₀h₀g₀ = 2 — Lemma 3.1's arithmetic, consistently), center
  c̃ := (1 + i)·i^{m(3)} ∈ 𝔽₉ˣ, ψ₁ = z − c̃, z̄₁ = c̃, μ = 1, s0 = 0, wSide = 1, pattern
  (−c̃, 1), recorded lift t = 9û₁·X + 27û₂ with ā = b̄ = 1 (v₃(a) = 2, v₃(b) = 3:
  w₀-weight 3 in both slots,
  digit (1 + i)·i^{m(3)} = c̃ ✓). The remaining node data (γ-tie, anchor, window
  containment s0+wSide = 1 ≤ μ₀ = 1, hbezCanon, hLineU) are satisfiable by direct
  choice; the two-node history H = [ν₀, ν₁] is coherent — the (C4-non) leg at i = 0 is
  exactly the σV/IsNodeLift/TransitionCoreL package displayed above.

**Claim.** No t with singleton X-support satisfies (CR1)+(CR3) at ν₁. Hence RRE(3, F)
FAILS for every ambient F ⊇ 𝔽₉ at the intended stages, and the compiled (CR2) is
unfaithful at deg Φ > 1.

*Proof.* A singleton-support candidate is t = u·X^j, u ∈ ℤ₃ ∖ {0}, j ∈ {0, 1} (from
(CR3): deg t < 2). By (R×): R₁(t) = R₁(u)·R₁(X)^j. Both factors have MONOMIAL residuals
whose scalars lie in the subgroup G := 𝔽₃ˣ·⟨i⟩ ≤ 𝔽₉ˣ: R₁(u) has scalar ū·i^{m(w)} with
ū ∈ 𝔽₃ˣ (a constant's leading digit is a prime-field unit; the transition offset is a
power of i), and R₁(X) = R₁(Φ₀) has scalar i^{m'} (the old key's residual has
coefficient 1 at the base, by (RΦ); the transition multiplies by a power of i). So the
scalar of R₁(t) lies in G, |G| = 4 = {±1, ±i}. But (CR3) forces that scalar to equal
c̃ = (1+i)·i^{m(3)}, which has multiplicative order 8 and therefore lies OUTSIDE G
(falsifier checks A1–A3). Contradiction. Meanwhile (CR1)+(CR3) ARE satisfiable — by the
recorded two-slot lift — so the failure is exactly and only (CR2). ∎

*Status of this construction:* the σ₀/σ₁ instances are the standard order-1 objects of
the dual-accepted tower (§A/§B1/§B2-DEF layers); their axiom-compliance is asserted on
that basis, with the two load-bearing computations (the digit coset G; the coverage of
𝔽₉ˣ by two-slot digits) machine-checked in the falsifier suite. A COMPILED Lean
countermodel would additionally require building these stages as `Stage 3 F` instances
(bStage-scale work; recommended falsifier follow-up, not attempted here — the F = ZMod p
consumer is unaffected, per Corollary 4).

### 5.2 The recorded-lift form is also unprovable

The task charge's literal form — "the RECORDED lift's support satisfies (S6b′)" — is
refutable even at the faithful support law: coherence constrains the recorded lift only
through (r4)–(r6), which are insensitive to adding junk of strictly higher weight in any
slot. Concretely, if t is a lawful recorded lift and s ∈ C_Φ is nonzero with
w(s) > w(t), then t + s is an equally lawful recorded lift ((r5) by (S1)-strict
triangle — derivable from (S1) via the recombination t = (t+s) − s — and (r6) by (R<)),
with support anywhere. The true statement is EXISTENTIAL: the canonical realizer
(§5.3–5.4) has the lawful support; the recorded lift need not. This matches the compiled
∃-shape of `RunRealizerExists` and re-cuts the task phrasing accordingly.

