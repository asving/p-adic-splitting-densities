# FORGE junc_bundle STAGE 2 — the first compiled e ≥ 2 junction attempt ADJUDICATES THE BUNDLE INSTANCE-FALSE: the parity wall (no e = 2 recording exists), the Φ₂-landing wall (char-2, all species/degree faces), the D0 flag CONFIRMED in Lean (gate hbundle unsatisfiable), clause (iii) POSITIVELY derivable at the read-pair pins

**Unit:** FORGE junc_bundle stage 2 (wave 11; charter = stage 1's §S5 spec,
`JUNCFORGE_S1_2026-08-08.md`).  **Artifact:**
`lean/LeanUrat/Scaffold/HDischarge/H1/JuncForge.lean` — NEW declarations only; no
existing statement touched (`gate_glue_junction`/`gate_glue_conditional` displayed,
not edited); `lake env lean` green; every theorem `#print axioms` = Lean core
`{propext, Classical.choice, Quot.sound}`; zero sorries.
**Row-A data compiled:** f = X² + 4X + 28, Φ₁ = X + 2, Φ₂ = X² + 4X + 12 over ℤ₂;
the deep development f = 24 + Φ₁² (slots (24, 0, 1)) as `fA_eq`/`BA_dev`.

## S1. VERDICT — the §S5 discharge is IMPOSSIBLE: `junc_bundle` at row A is instance-false

Executing the stage-1 spec against the Lean `SideReads` transcription did not
produce the chartered first compiled e ≥ 2 junction — it PROVED no such instance
can exist, at any stage, for any recorded node data:

| theorem | statement | scope |
|---|---|---|
| `juncforge_no_e2_junction` | any `SideReads` of f at a Φ₁-keyed frame has ν.e = 1 | any finite F, any Φnext — char-free |
| `juncforge_deep_wall` (+ `_F4`) | no `SideReads` of f at a Φ₁-keyed frame lands Φ₂ | any finite F with (2 : F) = 0; instantiated at F4 |
| `juncforge_junc_bundle_false` | the `junc_bundle` core ∃ (dev + interior pin + SideReads) is FALSE at every continuation H₂ with base key Φ₁ and node-1 key Φ₂ | packaged form |
| `juncforge_clauseIII_derivable` | clause (iii) alone IS derivable at the (2,3)-graded pins — the harness shape exact | positive fragment, conditional on the pins |
| `juncforge_D0_instanceFalse` | `gate_glue_junction`'s `hbundle` is unsatisfiable (byte-identical negation) | the flagged D0 adjudication |

## S2. THE MECHANISM — the two-scale law becomes a PARITY contradiction inside one node

**(a) The parity wall (e = 2).**  Clause (ii)'s functional equalities at the stride
slots {0, 2} force `gam = 2·σ.w(24) = 2·ν.h`, so `σ.w(24) = ν.h` with
`gcd(2, ν.h) = 1` — ODD.  The key-power slot carries `σ.w(Φ₁²) = 2·σ.h` — EVEN.
The slots can never tie; `hRlt` collapses σ.R f to a single monomial (hS5 digit or
T^{2s}); clause (iii)'s anchored `Ranch = pat₀ + pat₁·z` (hpat0/hpatTop force BOTH
digits nonzero at width wSide/e = 1) needs two Laurent positions
(`monomial_ne_anchor`).  ⊥.  This is the e₁ = 2 ramification itself: w₁(24) = 3 is
odd, the flat tie needs it even — no ℤ-valued stage scale hosts clause (ii)'s
window functional and clause (iii)'s graded residual simultaneously.  The support
forcing (s0 = 0, wSide = 2) is itself derived (clause (ii) endpoints must sit on
the development support {0, 2}; wSide = 0 dies by hOrd against a constant Ranch).

**(b) The landing wall (e = 1, Φnext = Φ₂).**  With ν.e = 1 forced: recentering
face — Φ₂ = Φ₁ − lift has degree 1 ≠ 2; g = 1 lift face — Φ₁ + t₀ has degree
1 ≠ 2; g = 2 lift face — clause (ii) at k = 1 forces pat₁ = 0 (B₁ = 0 by Fact B),
so Ranch = pat₀ + pat₂·z², ψ ∣ Ranch at equal degree pins ψ.coeff 1 = 0, and
ψ = z² + c₀ is (X + √c₀)² over the finite char-2 residue field (squaring is
bijective — proved self-contained, no Frobenius API) — contradicting `hψirr`.
g ≤ 2 comes from ψ^μ ∣ Ranch with deg Ranch ≤ 2.

**(c) What remains OPEN (honest scope).**  `DIterJunctionSupplier` is NOT refuted:
its Φnext is existential, and Φnext-free e = 1 refinement-shaped recordings
(MacLane key improvement, the D4 stratum) are not excluded by (a)+(b).  The wall's
g = 2 leg is proved at the faithful char-2 ambient only; odd-residue-char
pathological stages (the interface does not tie char F to p) are out of scope and
displayed as such.  No claim at towers other than row A/ℤ₂.

## S3. THE D0 ADJUDICATION (the stage-1 §S2(c) flag) — DECIDED: INSTANCE-FALSE

`juncforge_D0_instanceFalse` negates the `hbundle` hypothesis of
`gate_glue_junction` VERBATIM: at the compiled seam the junction frame's key IS the
classificand (f = fq = σ₁rec.Φ — the degenerate f-equals-key stratum), the unique
fq-adic development of fq has B₀ = 0 (`L0_FactB_unique` against the self-development
`BselfJ`), and clause (ii) at the recorded `hpat0` (pat 0 = −rcCenter ≠ 0,
`RCWitness.lean`) demands B₀ ≠ 0.  **`gate_glue_conditional` is therefore VACUOUS
at its compiled instance.**  Stage 1's flag is CONFIRMED, not refuted.  Per the
charter fence the gates are NOT edited — their DISPOSITION (display text, possible
re-instancing at a non-degenerate seam) is an orchestrator/ROOT matter.

## S4. THE SUPPORT KERNEL AND THE POSITIVE FRAGMENT

* **Development uniqueness (Fact A/B, priced by stage 1): PROVED — pre-existing.**
  The needed kernel is exactly `Moves.L0_FactB_unique` (already on file, Lean-core);
  this unit consumes it (`dev_pin`, D0).  No new sorry, no displayed hypothesis.
* **Clause (iii) is honest at the read-pair scale** (`juncforge_clauseIII_derivable`):
  at any stage with pins Φ = Φ₁, h = 3, (s,t) = (−1,1), wPrev(24) = 3, w(24) = 6,
  the interface derives σ.R f = C(c)·T⁻³ + T⁻² = T⁻³·(c + z) — consecutive
  positions −3/−2, anchor −3, ord_{z+c}(c+z) = 1 — the §S5 display exactly, from
  hS5 + hRΦ + hRmul + hRadd + hK1.  The stage-1 two-scale law survives in Lean;
  the contradiction is strictly the CO-HABITATION with clause (ii) in one node.
  The existence of a stage with these pins (the concrete (2,3)-graded junction
  stage) remains the open construction — moot for the bundle (S1), retained as the
  honest conditional.

## S5. WHAT junc_bundle's STATUS BECOMES

* At row A (and by the parity mechanism, at any genuinely ramified deep read with
  odd in-carrier parent weight): **`junc_bundle` is INSTANCE-FALSE as transcribed**
  — the E-PHASE FLAG (HC2/Defs clause (iii) "may over-strengthen") lands as a
  proved INTER-CLAUSE CONTRADICTION ((ii) ⊥ (iii) at e = 2; (ii)+(iv) ⊥ at e = 1),
  not an over-strengthening of one clause.
* The C-e escapee is EXPLAINED: GlueRun's "no compiled e ≥ 2 instance exists on
  file to feed it" is now "none CAN exist" (`juncforge_no_e2_junction`).
* The RG-2 fence is unbreached and now double-walled at the seam: the glued-base
  (L₁ = 1) hosting of an e ≥ 2 junction read, the one shape the glue theorem
  permits, has no inhabitant.
* Any repair (re-scaling clause (ii)'s functional to the parent scale at graded
  frames, or re-keying clause (iii)'s residual) is a STATEMENT change on
  `SideReads` — ROOT authority, not this unit.

## S6. WHAT THIS UNIT DOES NOT CLAIM

No edit to any existing statement (gates displayed only); no repair proposal
adopted; no refutation of `DIterJunctionSupplier` (S2(c)); no odd-char claim; no
orders ≥ 3 claim; ITER-LAW untouched (never reached — the bundle dies before any
digit algebra fires; the stage-2 gate is ITER-LAW-free as the spec predicted, but
by falsity rather than degeneration).  The capstone path is untouched (new file
only; no existing module recompiled).

— FORGE junc_bundle stage 2, 2026-08-08 (wallclock 2026-08-03).
