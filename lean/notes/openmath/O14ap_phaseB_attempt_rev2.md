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
**Falsifier suite**: `O14ap_check.py` (same directory) — ALL PASS (14/14; rev 1's checks
A1–A4/B/C/D byte-unchanged, round-2 checks added: E1–E3 — the threaded slot law and the
un-MacLane regrade slopes at the HK23-gate numbers; F1–F2 — the stretched-frame display
void; G0–G1 — general-g sharpness, exhaustive at g = 3 over 𝔽₂₇, all unit offsets).

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

### 5.3 The faithful (S6b′) support law — REV 2: the stretch-threaded statement

*(Round-2 rebuild; supersedes rev 1's §5.3. Rev 1 carried a scale error — V11 CRITICAL
finding, disposition table above: the recursion prescribed lower-stage realizers in the
wPrev_{r−1}-scale but fed them to a slot minimum that consumes the σ_{r−1}.w-scale;
these differ by the stretch factor σ_{r−1}.e. Rev 2 threads that factor explicitly. The
compiled corpus independently carries the exact mechanism — `HC2/HK52_stretchGate.lean`,
`hk52_qform_stretch`: σ′.w B = e′·σV.w B on child-key coefficients — cited as compiled
evidence of the corrected shape, not as proof; the proof below is a one-line (STR)
application.)*

Notation as in rev 1: a stage σ_r of the intended tower with frame key Φ_r built by the
read (e, h, g) := (e_{r−1}, h_{r−1}, g_{r−1}) from the previous key Φ_{r−1};
coefficients t ∈ C_{Φ_r} develop in the previous key, t = Σ_{j<eg} B_j·Φ_{r−1}^j with
deg B_j < deg Φ_{r−1}. The parent scale of stage r is wPrev_r = the read-regrade
slot-minimum of §1.3's (C4-non) (σV.w there, tied by (T3); throughout §5.3–5.6 we write
**(n1)** for that slot-minimum law and **(n2)** for the standard-lift display
`IsNodeLift`, matching the companion brief's labels), displayed at level r as:

    (n1-r)   wPrev_r(t) = min over occupied slots j of ( e·σ_{r−1}.w(B_j) + j·h ).

**The stretch.** e★ := σ_{r−1}.e, the parent FRAME's ramification entry. On coherent
histories e★ ∈ {1, e}: e★ = 1 when frame r−1 is the base/root frame (intended base:
pair (1,1)) or was created by a recentering transition ((r2)); e★ = e when frame r−1
was created by a non-recentering transition — (T1) ties the frame pair to its own
node's read pair, and that node's read IS the read (e, h) creating stage r. Every
RG-2-fenced recorded frame, every root- and post-recentering frame, and every frame of
the §5.1 tower has e★ = 1.

**(THR) The threaded slot law.** For every occupied slot j, (STR) at σ_{r−1} gives
σ_{r−1}.w(B_j) = e★·wPrev_{r−1}(B_j) (B_j ∈ C_{Φ_{r−1}}, B_j ≠ 0), hence

    (THR)   wPrev_r(t) = min over occupied slots j of ( e·e★·wPrev_{r−1}(B_j) + j·h ).

A lower-stage realizer supplied at wPrev_{r−1}-scale target W_k therefore enters the
level-r slot minimum at weight e·e★·W_k + j·h. Rev 1 wrote e·W_k + j·h — correct only
at e★ = 1. This one-line conversion is the whole repair mechanism; everything below is
its bookkeeping.

**Forced class and progression, threaded.** Write E := e·e★. Since gcd(e, h) = 1 and
e★ ∈ {1, e}, also gcd(E, h) = 1, so every W ∈ ℤ has a unique forced class
j₀(W) ∈ [0, E) with h·j₀ ≡ W (mod E); the forced progression is
P(W) := { j₀(W) + E·k : k ∈ ℕ } ∩ [0, eg); the lower targets are
W_k := (W − (j₀ + Ek)·h)/E ∈ ℤ. At e★ = 1: E = e, j₀ < e, and P(W) =
{ j₀ + e·k : 0 ≤ k < g } — exactly g slots. At e★ = e ≥ 2: E = e², and §5.6 proves the
configuration is a definitional void of the current clause triple — no (n2) display
exists at any stretched frame — so the law below is stated at e★ = 1 per level, which
§5.6 shows is the ENTIRE statable domain of the current definitions, not a retreat.

> **(S6b′-SUPP-2)** (the repaired law; supersedes rev 1's (S6b′-SUPP)). Let σ_r be a
> stage of a coherent intended tower satisfying
> **(U)**: every frame strictly below r is unstretched — σ_m.e = 1 for all m < r.
> (Equivalently: every key-creating read below r either sits at a root/post-recentering
> frame or has stride 1. All RG-2-recordable towers, and the §5.1 and §5.5 instance
> classes, satisfy (U).)
> Then e★ = 1 at every level below r, and for every parent-scale weight
> W > wPrev_r(Φ_r) = e·h·g and every digit scalar c̃ ∈ K_rˣ there is a realizer t ≠ 0,
> t ∈ C_{Φ_r}, with wPrev_r(t) = W and digit scalar c̃ at the forced position, such
> that:
> (i) [level r−1] the Φ_{r−1}-slot support of t is contained in the forced progression
> P(W) = { j₀(W) + e·k : 0 ≤ k < g };
> (ii) [recursion, in the regrade scale] each occupied slot's coefficient B_{j₀+ek} is
> itself an (S6b′-SUPP-2) realizer one stage down, at the wPrev_{r−1}-SCALE target
> W_k = (W − (j₀+ek)·h)/e — every level's target is prescribed in THAT level's
> wPrev/regrade scale, and (THR) is the conversion consumed at each ascent — down to
> the base stage, where realizers are p^m·û with û a unit lift of the prescribed
> base-field residue (support {0} for the linear base key).
>
> Recentering steps create no level: (r8)–(r10) transport w, wPrev, and coefficient
> residuals unchanged (Lemma 3.2), and the per-slot strict ultrametric gives
> wPrev(Φ − lift) = wPrev(Φ) (Remark 5.3.1), so "the creating read" of a
> post-recentering frame means the last non-recentering read below it, with the same
> (e, h, g), the same threshold, and the same forced progression.
>
> At a recentering read (the CanRealizes consumer): W = w(Φ_r) = the key weight (the
> consumer's frame has σ_r.e = 1, so w = wPrev on C_{Φ_r}), the threshold is
> Lemma 3.1's inequality, and the progression (i) has the frame-creating read's stride
> e and length g — NOT the recentering node's own (e, g) = (1, 1). The compiled (CR2)
> reads the progression at (ν.e, ν.g) and in X-monomial vocabulary: two independent
> transcription divergences, each separately fatal at deg Φ > 1 (§5.1, §5.5).
> (S6b′-SUPP-2) is the statement the fence event should re-adjudicate (CR2) to. In
> X-vocabulary (i) specializes correctly ONLY at towers whose keys are X-power-pure
> (e.g. root key X with all lower realizers constants).

**Remark 5.3.1 (recentering transport of the threshold).** Let ν be a recentering at
frame σ with lift t, so ((r5) + hStretch at σ.e = 1) wPrev(t) = σ.w(t) = σ.w(σ.Φ) =
σ.h, and let (e′, h′, g′) be the creating read of σ.Φ. Develop Φ′ = σ.Φ − t in the
previous key: the development subtracts slot-wise. Every occupied slot of σ.Φ's
display weighs exactly e′h′g′ ((n1)+(n2), the Lemma 3.1(b) computation), while every
occupied slot of t weighs ≥ wPrev(t) = σ.h > e′h′g′ (Lemma 3.1(c)/5.4.0). On a slot
where both are present, the (S1) strict ultrametric keeps the display slot's weight
(the two per-slot σ-weights differ); slots occupied by t alone weigh > e′h′g′; and the
top display slot (index e′g′, coefficient 1) is untouched since deg t < deg σ.Φ
confines t to slots < e′g′. So the minimum is still attained at a display slot:
wPrev(Φ′) = e′h′g′ = wPrev(σ.Φ). The CLEARING inequality also survives a recentering
run: along recenterings e_i = g_i = 1, so STR and D are constant; with b′ the run's
first index and r−1 the node reading onward, (C2) gives
h_{r−1} = slope_{r−1}·(e_{r−1}·STR·D) and h_{b′} = slope_{b′}·(STR·D), chained (C7)
gives slope_{r−1} > slope_{b′}, hence h_{r−1} > e_{r−1}·h_{b′} > e_{r−1}·e′h′g′ (the
last step is Lemma 5.4.0 at the creating read, index b′−1, where e_{b′} = 1) — the
transported threshold still clears: e′h′g′ < h_{r−1}/e_{r−1}. ∎

### 5.4 Proofs — REV 2: the threshold lemma, the law on (U), sharpness at every g

#### 5.4.0 Lemma (general steepening; retires rev 1's flagged (F2))

**Lemma 5.4.0.** In a coherent history, for every i with i + 1 < len, writing
(e_i, h_i, g_i) := (ν_i.e, ν_i.h, ν_i.g): h_{i+1} > e_{i+1}·e_i·h_i·g_i. Consequently,
when ν_i is a non-recentering (so the Lemma 3.1(b) slot computation applies verbatim at
index i): wPrev_{i+1}(Φ_{i+1}) = e_i·h_i·g_i < h_{i+1}/e_{i+1}.

*Proof.* By (C2) at i and at i+1, STR_{i+1} = STR_i·e_i (definition of STR), and (C6)
D_{i+1} = e_i·g_i·D_i:

    h_{i+1} = slope_{i+1} · (e_{i+1} · STR_{i+1} · D_{i+1})
            = slope_{i+1} · e_{i+1} · (STR_i·e_i) · (e_i·g_i·D_i)
            > slope_i · e_{i+1} · e_i² · g_i · STR_i · D_i        [(C7); the multiplier
                                                                   is a positive integer]
            = e_{i+1} · e_i · g_i · ( slope_i · (e_i · STR_i · D_i) )
            = e_{i+1} · e_i · g_i · h_i.                                   ∎

(Lemma 3.1(c) is the e_{i+1} = 1 case. Rev 1 consumed the corollary as the flagged fact
(F2), "the previous stage satisfies its own threshold inequality wPrev(Φ) < h/e"; it is
now derived from (C2)/(C6)/(C7) alone, and the flag is retired. (F1) — the consecutive
residual positions of the progression slots, position(j₀ + ek) = m(W) + k — remains the
one consumed-and-flagged intended-apparatus fact, per level, unchanged from rev 1.)

#### 5.4.1 Theorem (the law holds on class (U))

**Theorem 5.4.1.** (S6b′-SUPP-2) holds as stated in §5.3.

*Proof.* Strong induction on r ≥ 1. Fix W > ehg and c̃ ∈ K_rˣ. By (U), e★ = σ_{r−1}.e
= 1, so E = e and the forced progression is { j₀ + ek : k < g }, j₀ = j₀(W) < e.

(1) *Class arithmetic.* On the progression the lower targets W_k = (W − (j₀+ek)h)/e are
integers (choice of j₀); off the class j ≡ j₀ (mod e), no slot can sit at total weight
W, since by (THR) with e★ = 1 every occupied slot j weighs e·wPrev_{r−1}(B_j) + j·h ≡
j·h (mod e) and h·j ≡ W (mod e) forces j ≡ j₀.

(2) *Design.* By (F1), the progression slots j₀, j₀+e, …, j₀+e(g−1) sit at consecutive
residual positions m(W), m(W)+1, …, m(W)+g−1 of the previous stage's residual variable.
K_r = K_{r−1}(z̄) = K_{r−1}[z]/(ψ) has K_{r−1}-basis 1, z̄, …, z̄^{g−1}, and z̄^{m(W)} is
a unit, so there is a UNIQUE P ∈ K_{r−1}[z] with deg P < g and z̄^{m(W)}·P(z̄) = c̃;
P ≠ 0 since c̃ ≠ 0. Set

    t := Σ_{k < g, P_k ≠ 0}  t_k · Φ_{r−1}^{j₀ + e·k},

with t_k the SHAPED realizer at stage r−1 of digit scalar P_k ∈ K_{r−1}ˣ at the
wPrev_{r−1}-scale target W_k, supplied by the induction hypothesis at r−1 ≥ 1, and at
r = 1 by the base realizer t_k := p^{W_k}·û_k (û_k a unit lift of P_k; the base key is
linear, so C_{Φ₀}-coefficients are constants and the support is {0}).

(3) *The recursive call is licensed.* W_k ≥ (W − (eg−1)h)/e > (ehg − (eg−1)h)/e = h/e.
At r ≥ 2, Lemma 5.4.0 one stage down gives wPrev_{r−1}(Φ_{r−1}) = e′h′g′ < h/e for the
creating read (e′, h′, g′) of stage r−1 (a post-recentering frame has the same
threshold by Remark 5.3.1), so W_k clears the lower threshold; and (U) restricted to
m < r−1 is (U) for the lower call. At r = 1, W_k > h/e > 0 suffices (the base needs no
threshold; W_k ≥ 1).

(4) *Weight — the repaired seam.* Each summand's slot weight is

    e·e★·W_k + (j₀+ek)·h  =  e·1·W_k + (j₀+ek)·h  =  W :

by (STR) at σ_{r−1} and e★ = 1, the lower realizer's σ_{r−1}.w-weight EQUALS its
wPrev_{r−1}-scale target W_k, which is what (n1-r) consumes. [This is the exact point
where rev 1 broke at e★ ≥ 2: there the consumed weight is e·e★·W_k ≠ e·W_k.] All
occupied slots weigh exactly W and at least one slot is occupied (P ≠ 0), so the
attained minimum gives wPrev_r(t) = W; and t ≠ 0 (a development with a nonzero slot,
unique for monic Φ_{r−1}).

(5) *Digit.* By (F1) the slot digits assemble as Σ_k P_k·z^{m(W)+k} = z^{m(W)}·P(z) in
the previous residual variable; ψ-reduction/evaluation at z̄ (the passage into K_r)
gives the digit scalar z̄^{m(W)}·P(z̄) = c̃ at the forced position. At a recentering
consumer (frame pair e = 1, Bézout t = 0) the position is 0 and R_r(t) = C(c̃)·T 0,
matching (CR3) exactly.

(6) *Support.* Clause (i) is the literal index set of the sum; clause (ii) is the
construction of the t_k in (2). ∎

*Consistency witness (the §5.1 instance).* At σ₁ of the countermodel ((e, h, g) =
(1, 1, 2) creating read, W = 3, e★ = 1): j₀ = 0, progression {0, 1}, W₀ = 3, W₁ = 2 —
exactly the recorded lift's slot weights (v₃ = 3 and 2 with slot-1 total 2 + 1 = 3),
confirming the repaired bookkeeping reproduces the machine-checked instance.

#### 5.4.2 Proposition (sharpness at every g — the basis argument; repairs V11 finding 2)

**Proposition 5.4.2.** In the setting of Theorem 5.4.1, fix W > ehg and let
Θ : { P ∈ K_{r−1}[z] : deg P < g } → K_r, Θ(P) := z̄^{m(W)}·P(z̄). Then:
(a) Θ is a K_{r−1}-linear bijection.
(b) For every nonempty S ⊆ {0, …, g−1}, the scalar c̃_S := Θ(P_S), P_S := Σ_{k∈S} z^k,
is a unit of K_r, and EVERY (S6b′-SUPP-2)-shaped realizer of (W, c̃_S) — any t
assembled per §5.3 (i)+(ii), i.e. progression-supported with equal slot weights and
nonzero slot digit scalars at the occupied slots — has slot support EXACTLY
{ j₀(W) + e·k : k ∈ S }.
(c) In particular (S = {0, …, g−1}): all g progression slots are simultaneously
necessary. The progression length g is sharp for every g ≥ 1, and no single-monomial
strengthening of the law is available at any g ≥ 2: single-slot shaped realizers reach
only ∪_{k<g} K_{r−1}ˣ·z̄^{m(W)+k} — the union of the g basis lines — which for g ≥ 2
misses every c̃_S with |S| ≥ 2.

*Proof.* (a) Θ is K_{r−1}-linear and maps the basis 1, z, …, z^{g−1} of the domain to
z̄^{m}, z̄^{m+1}, …, z̄^{m+g−1}, which is the unit z̄^{m} times the K_{r−1}-basis
1, z̄, …, z̄^{g−1} of K_r = K_{r−1}[z]/(ψ) (deg ψ = g), hence itself a basis. A linear
map carrying a basis to a basis of spaces of equal finite dimension is a bijection.
(b) c̃_S = Θ(P_S) ≠ 0 since P_S ≠ 0 and Θ is injective; K_r is a field, so c̃_S ∈ K_rˣ.
A shaped realizer t of (W, c̃_S) assembles, by (F1) exactly as in Theorem 5.4.1(5), the
digit Θ(P_t), where (P_t)_k = the digit scalar of slot j₀+ek when occupied and 0
otherwise; occupied slots carry NONZERO scalars, so support(P_t) = the occupied k-set.
Θ(P_t) = c̃_S = Θ(P_S) forces P_t = P_S by (a), so the occupied set is exactly S.
(c) is (b) at S = {0, …, g−1}; the single-slot digit set is the k-indexed union of the
images of the coordinate lines, Θ(K_{r−1}ˣ·z^k) = K_{r−1}ˣ·z̄^{m+k}, and any c̃_S with
|S| ≥ 2 lies outside every one of them by uniqueness of P. ∎

*Scope note (unchanged claim class, now proved).* 5.4.2 is sharpness WITHIN the shaped
class — the same scope as rev 1's tightness claim; it consumes (F1) and nothing else.
An arbitrary-realizer strengthening (any t with wPrev_r(t) = W and digit c̃_S has its
minimal-weight slot stratum supported on exactly the S-progression) would additionally
need the graded fact that a coefficient's digit reads off its minimal-weight slot
stratum by the same (F1) assembly; that fact is intended-apparatus content consumed by
NOTHING here and is recorded as OPEN, not claimed.

*Instances.* The rev-1 F₉ refutation (§5.1–5.2, byte-stable; V11-confirmed) is the case
g = 2, S = {0, 1}, K_{r−1} = 𝔽₃, z̄ = i: c̃_S = (1+i)·i^m has order 8 and lies outside
the union 𝔽₃ˣ·⟨i⟩ of the two basis lines — falsifier checks A1–A4. The general-g
mechanism is machine-checked exhaustively at g = 3 over 𝔽₂₇ = 𝔽₃[z]/(z³−z−1) for every
unit offset m (check G): Θ is a bijection at every m; the full-support target is missed
by every one-slot and every two-slot digit set.

### 5.5 The fence-lift flag (forward obligation, at F = ZMod p)

If the RG-2 fence is lifted (interior reads with stride e ≥ 2 recorded — the open
carry-algebra interior, §B2-FINAL territory), Theorem 1(ii) fails and (CR2) regains
content at F = ZMod p — and it is then REFUTABLE at the intended stages by a pure
weight-lattice mechanism: over a unit-shifted root key Φ₀ = X − a₀ (a₀ ≢ 0 mod p), X is
a w-unit, so X-monomials u·X^j realize only weights in STR·ℤ (STR = the accumulated
stretch), while a recentering after one interior e = 2 read can require the odd key
weight h ∉ 2ℤ (e.g. h = 3, slope 3/4 > 1/2: lawful under (C2)/(C7)); the faithful
progression realizer t = d·Φ₀ (slot 1, weight 2v₃(d)+1) exists, but its X-support
{0, 1} is not a singleton, and no X-monomial has the required weight at all (falsifier
check D). CONSEQUENCE: the (CR2) re-adjudication to (S6b′-SUPP) is a PREREQUISITE of any
fence lift, not an optional cleanup. Recorded here as a named forward obligation.

### 5.6 Scholium (NEW, round 2): the stretched-frame void — the complement of (U)

**Proposition 5.6.** Let σ be a stage at a STRETCHED frame of a coherent history:
σ.e = e ≥ 2 (by (T1), this is exactly a frame created by a non-recentering transition
whose own node reads at stride e ≥ 2 — the configuration behind the RG-2 fence, whose
frame pair equals its read pair). Consider any attempted non-recentering read at σ with
descend polynomial ψ of degree g (the read pair is the frame's own (e, h), per (T1)).
If ψ_k ≠ 0 for some k with e ∤ (g − k) — in particular WHENEVER e ∤ g, since ψ₀ ≠ 0
for every irreducible ψ ≠ z — then NO (n2) standard-lift display exists: there is no
t_k ∈ C_{σ.Φ}, t_k ≠ 0, with σ.w(t_k) = h·(g − k) at all.

*Proof.* By (STR) at σ, every nonzero t_k ∈ C_{σ.Φ} has σ.w(t_k) = e·σ.wPrev(t_k) ∈
e·ℤ (wPrev is ℤ-valued). The display demands σ.w(t_k) = h·(g−k). Since gcd(e, h) = 1:
e ∣ h·(g−k) ⟺ e ∣ (g−k). ∎

*(Non-vacuity of the statement: under the current fence, an INTERIOR read at a
stretched frame is already unrecordable for the independent reason that (C4-non)
demands ν_i.e = 1 while the frame ties ν_i.e = σ.e ≥ 2; the proposition quantifies
over the display equation itself, so it rules the UNFENCED variant — exactly the
fence-lift scenario — void as well, this time by arithmetic rather than by fiat.)*

**Displayed instance (the compiled gate).** The corpus's own ramified frame
`R7Forge.ramifiedStage` (the HC2/HK23 positive gate: child of the p = 2 base pin under
the (2, 5) read; σ.e = 2, key fq = X² + 2X + 4) admits NO onward (n2) display for any
odd g — at g = 1: k = 0 demands σ.w(t₀) = 5·1 = 5 ∉ 2ℤ. Falsifier check F. Independently, the (n1) regrade scale at this frame is not
a MacLane augmentation at all: it evaluates p ↦ 4 and fq ↦ 5 (key slope 5/4), while
the frame's own w has p ↦ 2 and fq ↦ 5 (slope 5/2) — no rescaling matches both
(falsifier check E3). So above a stretched frame the current clause triple
{(n1) regrade, (n2) display, (STR) stretch} records NOTHING: the complement of class
(U) is definitionally empty territory, and Theorem 5.4.1's (U)-scope is the entire
statable domain of the current definitions — the honest content of the verifier's
"works only under σ_{r−1}.e = 1".

**What the faithful e ≥ 2 interior should say** is §B2-FINAL adjudication territory.
The classical-normalization design option — display weights e·h·(g−k) instead of
h·(g−k), and the child's parent scale taken as the frame's OWN w on coefficients, under
which the stride-e/length-g law of Theorem 5.4.1 recurs verbatim at every stretch — is
NAMED here as **(S6b′-DEEP)**, conjecture-level, claimed nowhere in this note.

**Consequence (strengthens §5.5).** A lift of the RG-2 fence must re-adjudicate not
only (CR2) → (S6b′-SUPP-2) (§5.5's obligation) but the regrade/display weight laws
themselves — the (n1)/(n2)/(STR) triple at e ≥ 2, i.e. the never-ratified D.7(i)–(v)
addendum named in the compiled `RegradeOf` docstring. The compiled HK-52 record
(finding F4: the ν_{i+1}.e ≥ 2 disposition is an adjudication item) points at the same
seam from the Lean side; Proposition 5.6 adds the display-level obstruction, previously
unrecorded on either side.

---

## 6. Honest-scope ledger (rev 2)

* **Proved outright (bare coherence + node/stage typing, no extra hypotheses):**
  Theorem 1 (at F = ZMod p; part (ii) exactly as conditional as the RG-2 fence),
  Lemma 3.1, Lemma 3.2, Theorem 3, Corollary 4 [all V11-CONFIRMED, byte-stable]; round
  2 adds Lemma 5.4.0 (general steepening — retires rev 1's flagged (F2)), Remark 5.3.1
  (recentering transport of the threshold), and Proposition 5.6 (the stretched-frame
  display void). These consume ONLY the §1 clauses; every use is cited by label.
* **Proved at the intended tower (consuming T-1's dual-accepted stage constructions +
  the flagged position fact (F1), per level):** Theorem 5.4.1 — (S6b′-SUPP-2) on class
  (U), the stretch-threaded law — and Proposition 5.4.2 (sharpness at every g, shaped
  class). The statements quantify over stages of coherent towers built by the accepted
  §B2-DEF transitions (the same scope as T-1), now with the (U) frame-stretch
  hypothesis DISPLAYED and proved to exhaust the statable domain (§5.6).
* **Refutations:** §5.1 (semantic countermodel at (3, 𝔽₉); stage-instance
  axiom-compliance asserted as standard order-1 apparatus + machine-checked arithmetic;
  compiled-instance build named as follow-up falsifier) [V11-CONFIRMED]; §5.2
  (recorded-lift form; complete); §5.5 (conditional on fence lift; arithmetic
  machine-checked); §5.6 (the stretched-frame void — unconditional, current clause
  triple).
* **Open / not claimed:** the e ≥ 2 interior law (S6b′-DEEP) — named as a design option
  in §5.6, conjecture-level, blocked on the §B2-FINAL/D.7 adjudication; the
  arbitrary-realizer strengthening of sharpness (§5.4.2 scope note). Not done here:
  Lean edits (per charge); the compiled 𝔽₉ Stage instances; the formalization of
  Corollary 4 (recipe §4.2).
* **Known/new labels:** Theorem 1 — new observation (elementary, load-bearing).
  Theorem 3 — NEW theorem (closes the leaf's main open flank positively). Theorem 5
  refutation — NEW countermodel. (S6b′-SUPP-2) — content of the dual-accepted
  T-1/(S6b′) construction with the support clause made explicit AND the stretch factor
  threaded (label (b): new packaging of accepted material + the round-2 threading
  repair). Lemma 5.4.0 — new, elementary. Proposition 5.4.2 — new proposition.
  Proposition 5.6 — NEW observation, previously unrecorded on the math or Lean side.
* **Predictions falsifiable now:** (P1) the LIVE flank countermodel search returns
  empty; (P2) a Lean prover following §4.2 discharges the (†15) pair with no statement
  changes; (P3) any attempt to compile the §5.1 stages as `Stage 3 F` instances
  succeeds and empties the singleton-(CR2) fiber at ν₁; (P4, NEW) any attempt to build
  an `IsNodeLift` display at a stretched frame with e ∤ g — e.g. any g = 1 onward read
  at `R7Forge.ramifiedStage` — fails on the Proposition 5.6 arithmetic (a compiled
  emptiness lemma is a cheap falsifier follow-up).

## 7. Consumed tree nodes and compiled evidence

T-1 (§B2-DEF stage laws + the (S6b′) construction — for §5.3–5.4 only; §§2–4 consume
nothing above the compiled definitions' mathematical content); the D-10/O-14a′ leaf
statement; evidence artifacts cited for provenance only (item-13 record, HK23/HK25
gates, U6, and — round 2 — `HC2/HK52_stretchGate.lean` (`hk52_qform_stretch`, the
compiled stretch mechanism that (THR) mirrors) and `MovesD/R7_ramifiedForge.lean`
(`ramifiedStage`, Proposition 5.6's displayed instance) — none load-bearing: every
proof stands on the §1 clauses plus the flagged (F1)). No other leaf is consumed; in
particular NOTHING here depends on O-1/O-2/O-3, so this unit sits at the top of the
§D1.6 critical path as required (V6 finding 22 honored: O-14a′ before O-3).
