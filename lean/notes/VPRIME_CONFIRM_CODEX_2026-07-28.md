OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: danger-full-access
reasoning effort: none
reasoning summaries: none
session id: 019fa871-2802-7853-b267-dd268f2eb45a
--------
user
CONFIRMATION CHARGE (Codex adversarial verification pass)

You are the standing adversarial verifier for the p-adic-splitting-densities Lean
formalization project. A prior agent ("the applier") has just executed HC1 blueprint
§10 (the "V′ kernel" design) against the Lean source tree: it (a) restated
`Stage.hS6a` from an untwisted single-scalar form to a fixed-point COSET form (the
V5 sign-off event), rippled that restatement through ~15 dependent files, and
(b) elaborated nine new proof units V0–V9 (`HC1/DefsV.lean`, `HC1/V1_readWPack.lean`
through `HC1/V9_K1nonrec.lean`) implementing the "read-functional carry algebra"
(†) described in §10.

Your job: verify the APPLIED CODE (the git diff + the new untracked V*.lean files,
both included below) against the NOTE DISPLAYS the design cites as its authority
(the MOVES excerpts and the D.5 display included below), and against the blueprint's
own §10 text (also included below, which is the design specification the applier was
supposed to follow). Concretely:

1. hS6a restatement fidelity. Quote the OLD (pre-diff, i.e. removed `-` lines) and
   NEW (post-diff, added `+` lines) forms of `Stage.hS6a` in `Moves/Defs.lean`.
   Check the new coset form against the two note displays it claims to transcribe:
   - MOVES 1964–1971 (D.2, "(S6a) EXACTNESS + BASIC REALIZERS ... orbit group at its
     FIXED POINT ... O := F_Qˣ (the BASE field's units)")
   - MOVES 2431–2435 (D.7(viii), "the SINGLE-SLOT element t_{γ,j} ... whose dig' is
     c·(a fixed z̄-monomial class): the O-orbit with O = F_Qˣ CONSTANT")
   Does the Lean form's quantifier order (∃ b BEFORE ∀ c) and scalar shape
   (C((c*b : ↥K))) actually match "c·(fixed class)" with the base free in Kˣ, or is
   it either (a) STRONGER than the note warrants (silently reintroducing the refuted
   untwisted form, or over-constraining the base), or (b) WEAKER than needed (losing
   information a consumer downstream actually uses, which would be silently masked
   by the consumer proofs still going through)? Also check MOVES 2395–2418 (the D.7
  (vi)–(vii) PINNING passage, T = V^s·Y^t, z = V^{-h}·Y^e, the EXPONENT-group
   redefinition) — the blueprint's §10 Finding 2 leans on this passage's frame-change
   identities to justify mfun ≡ 0; verify that dependency is real and not asserted.

2. V0–V9 statement fidelity. For EACH of V0 (`DefsV.lean`: ReadPair, ReadResData,
   ReadResLaws, ReadFrame) and V1–V4, V6–V9 (skip V5, which has no file — it IS the
   hS6a restatement audited in item 1), compare the Lean STATEMENT (signature +
   hypotheses + conclusion, not the proof term) against:
   (a) the §10.1 prose spec for that unit in the blueprint text below, and
   (b) the D.5 display below (the standard-lift / EQUAL WEIGHTS / K1(Φ̂/w) residual
       computation that V3 in particular claims to rerun "VERBATIM" at the ReadFrame).
   Flag every SILENT STRENGTH CHANGE: a hypothesis added that isn't in the note/spec
   (statement got easier to prove, harder to use), a hypothesis dropped that the
   note's argument actually needs (statement got easier to state, may be unfaithful
   or may make the proof secretly rely on something unstated), a conclusion weakened
   relative to the spec (V4's VERTEX/BOX in particular — check the TRANSPORT leg is
   cleanly FENCED OUT, per §10.1's explicit instruction, and not just silently
   dropped from a conjunction without being named), or any quantifier reordering
   that changes ∀/∃ meaning versus the quoted note display.

3. Cross-check the two escalation records (§10.5, §10.6) against what the diff
   actually shows for `V8_childResidual.lean`: the blueprint claims "V8a, V8b, V8c
   all proved, zero sorry" and a specific final device (the private `v8gr`/`v8Deep`
   graded-residue calculus). Confirm the file as it exists on disk matches that
   narration, not an earlier partial state.

4. General: run `grep -n sorry` over the new V*.lean files yourself from the catted
   content below and report the count; the blueprint's §10.4 record claims "13
   E-phase sorries" at elaboration but §10.6 claims V8 is now fully proved — these
   two claims are about DIFFERENT points in time (elaboration vs. after two escalation
   rounds), so a nonzero-but-reduced sorry count is expected and consistent, not
   automatically a red flag; only flag it if the CURRENT file content contradicts the
   MOST RECENT claim (§10.6, "V8 PROVED IN FULL") for the V8 file specifically, or if
   any other V-file's sorry count contradicts what §10.1/§10.4 say should still be
   open for it.

Report format: a numbered list of findings. For each finding, QUOTE the offending
passage (both the Lean text and the note text it should/shouldn't match), classify
it as CRITICAL (breaks the logical chain / statement is unfaithful in a way that
would let a false theorem through) or GAP (a justification gap, or a legitimate but
UNDOCUMENTED strength change that should have been flagged in the blueprint's own
"silent strength change" audit language but wasn't) or NONE (confirms fidelity). Do
NOT fix anything. Do NOT rerun `lake build` — this is a text/statement audit against
the diff and the quoted note displays provided below, not a compilation check. End
with an overall verdict: ACCEPT (no critical findings) or REJECT (name the item(s)
that must be fixed before this design pass can be accepted).

=== MATERIAL BELOW ===
Section A: git diff of lean/LeanUrat/ since HEAD (tracked-file changes)
Section B: the 9 new untracked V*.lean files (full contents)
Section C: HC1 blueprint §10 (the design spec + two execution/escalation records)
Section D: MOVES excerpts cited by name above (1964-1971, 2395-2418, 2431-2435)
Section E: the D.5 display (K1 at the new key — the standard-lift residual computation)
=== SECTION A: git diff HEAD -- lean/LeanUrat/ (capped 250000 bytes) ===
diff --git a/lean/LeanUrat/HC1/C2_TYPa.lean b/lean/LeanUrat/HC1/C2_TYPa.lean
index 40de4d9..07b3eb2 100644
--- a/lean/LeanUrat/HC1/C2_TYPa.lean
+++ b/lean/LeanUrat/HC1/C2_TYPa.lean
@@ -165,8 +165,15 @@ private lemma digLift_spec (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0)
     have hkne : (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) ≠ 0 := by
       intro h
       exact hyF (congrArg Subtype.val h)
-    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := (T.stg 0).hS6a 0 h0mem
-      (Units.mk0 (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) hkne) y.2
+    -- V5 coset form: at the base stage K = FQ, so the coset base b is absorbed by c := y·b⁻¹
+    obtain ⟨b, hb⟩ := (T.stg 0).hS6a 0 h0mem
+    have hKFQ : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
+    set cy : (↥(T.stg 0).K)ˣ :=
+      Units.mk0 (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) hkne with hcy
+    have hbinv : (((cy * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ :=
+      (le_of_eq hKFQ) ((cy * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K).2
+    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := hb (cy * b⁻¹) hbinv
+    rw [inv_mul_cancel_right, hcy] at hBR
     refine ⟨B, hB0, hBC, hBw, ?_⟩
     simpa using hBR
   rw [Tower.digLift, dif_pos hex]
diff --git a/lean/LeanUrat/HC1/MANIFEST.json b/lean/LeanUrat/HC1/MANIFEST.json
index afc0f6f..a366d6c 100644
--- a/lean/LeanUrat/HC1/MANIFEST.json
+++ b/lean/LeanUrat/HC1/MANIFEST.json
@@ -7,7 +7,8 @@
   "lean/LeanUrat/HC1/DefsTower.lean",
   "lean/LeanUrat/HC1/DefsCar.lean",
   "lean/LeanUrat/HC1/DefsSpine.lean",
-  "lean/LeanUrat/HC1/DefsChild.lean"
+  "lean/LeanUrat/HC1/DefsChild.lean",
+  "lean/LeanUrat/HC1/DefsV.lean"
  ],
  "defs_sorry_free": true,
  "preamble": "Every unit file begins: `import Mathlib` then the HC1 Defs module(s) it needs (`LeanUrat.HC1.DefsD` / `DefsTower` / `DefsCar` / `DefsSpine`) then the cited PROVED Moves/MovesGr/MovesC unit files; then `set_option linter.style.longLine false`, `set_option linter.style.header false`, `set_option linter.unusedSectionVars false`, `set_option maxHeartbeats 800000`; then `namespace LeanUrat.HC1` and `open Polynomial LeanUrat.Moves` (plus `open scoped Classical` where Pi.single/filters need decidability). Statements elaborate under that preamble (verified per-file by `lake env lean`, MOVESGR §6 double-elaboration discipline: statements regenerated verbatim from this manifest must re-elaborate). `sorry` is the only allowed escape — ZERO new axioms; any GMN/Denef import in a cone is stop-the-line.",
@@ -287,8 +288,8 @@
    "id": "HC1.S9w_residualLaws",
    "file": "lean/LeanUrat/HC1/S9w_residualLaws.lean",
    "difficulty": "hard",
-   "sorries": 1,
-   "rev": "NEW (S9 decomposition, §9.5; 2026-07-28) — RESTORED SHAPE (remediation round, same day; the Codex S9 rejection repair): S9w's OWN theorem = (∃ D : ChildResData, ChildResLaws D) ∧ w_strict — the §9.5 hard new-algebra block, one sorry, hardness honestly homed HERE (the E-phase draft had bundled the laws as ChildResData fields, relocating the hardness into S9r). The former nine projections survive as the PROVED Lean-core corollary childR_laws (explicitly labeled NOT the unit's content).",
+   "sorries": 0,
+   "rev": "NEW (S9 decomposition, §9.5; 2026-07-28) — RESTORED SHAPE (remediation round, same day; the Codex S9 rejection repair): S9w's OWN theorem = (∃ D : ChildResData, ChildResLaws D) ∧ w_strict — the §9.5 hard new-algebra block, one sorry, hardness honestly homed HERE (the E-phase draft had bundled the laws as ChildResData fields, relocating the hardness into S9r). The former nine projections survive as the PROVED Lean-core corollary childR_laws (explicitly labeled NOT the unit's content). — WIRED (escalation round 2026-07-28, S9w_final): own sorry KILLED, closes by `exact V8_childResidual` per the §10 staged plan; conjunct (ii) w_strict is PROVED Lean-core (V8c); conjunct (i) inherits sorryAx from V8b ONLY (the carrier-construction block) until it lands. CLOSED (2026-07-28 second escalation): V8b/V8a proved; S9w rides V8_childResidual by exact — sorry-free, Lean-core.",
    "statement": "theorem S9w_residualLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ} (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ) (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) : (∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) ∧ (∀ f g', f ≠ 0 → g' ≠ 0 → childW σ Φhat e' h' f < childW σ Φhat e' h' g' → childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f)"
   },
   {
@@ -466,7 +467,65 @@
    "difficulty": "medium",
    "sorries": 1,
    "statement": "theorem R6_carrierInstance {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (T : Tower p F) (rl : TowerRealizable T) : ∃ K : CarrierPackR p, (∀ γ : ℚ, K.G.Gr γ = T.grQ γ) ∧ LSTStmt' p K ∧ TYPStmt' p K ∧ DOMStmt' p K"
+  },
+  {
+   "id": "HC1.V1_readWPack",
+   "file": "lean/LeanUrat/HC1/V1_readWPack.lean",
+   "difficulty": "medium",
+   "sorries": 0,
+   "statement": "theorem V1_readWPack (σ) (hσ : StageCoreL σ) (e★ h★ : ℕ) (s★ t★ : ℤ) (hrp : ReadPair σ e★ h★ s★ t★) : (slot-min pack for childW σ σ.Φ e★ h★ — S2 instance at Φhat := σ.Φ) ∧ hwmul ∧ hwult ∧ (Q-ASCENT: for B·B″ = Q·σ.Φ + R_dev monic division, Q-slot (†)-value ≥ R_dev-slot + (h★ − e★·σ.h))"
+  },
+  {
+   "id": "HC1.V2_readResidual",
+   "file": "lean/LeanUrat/HC1/V2_readResidual.lean",
+   "difficulty": "medium-hard",
+   "sorries": 2,
+   "statement": "theorem V2_readResidual … : (∃ D : ReadResData σ e★ h★ s★ t★, ReadResLaws D) ∧ (wV strict law — the S9w-(ii) mirror); theorem V2_readFrame … : Nonempty (ReadFrame σ e★ h★ s★ t★)  [THE V′ FRAME CHANGE UNIT]"
+  },
+  {
+   "id": "HC1.V3_readLift",
+   "file": "lean/LeanUrat/HC1/V3_readLift.lean",
+   "difficulty": "medium",
+   "sorries": 1,
+   "statement": "theorem V3_readLift … (V : ReadFrame) (hlift : IsReadLift σ ψ g e★ h★ Φ̂) : (D.5 EQUAL WEIGHTS display at wV) ∧ childW σ σ.Φ e★ h★ Φ̂ = e★·h★·g ∧ V.D.Rv Φ̂ = T(−t★·h★·g)·ψ ∧ K1At (childW σ σ.Φ e★ h★) Φ̂ (e★·h★·g)"
+  },
+  {
+   "id": "HC1.V4_readLanding",
+   "file": "lean/LeanUrat/HC1/V4_readLanding.lean",
+   "difficulty": "hard",
+   "sorries": 1,
+   "statement": "theorem V4_readLanding … (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (hdev : IsDevelopment Φ̂ f B N) : (VERTEX: B μ ≠ 0 ∧ wV(B μ) + μ·e★h★g = wV f) ∧ (BOX: strict above for m < μ) ∧ (vertex digit with the explicit unit z̄^{μ·t★·h★·g})  [TRANSPORT leg FENCED OUT per §10.1]"
+  },
+  {
+   "id": "HC1.V6_alignedOrbits",
+   "file": "lean/LeanUrat/HC1/V6_alignedOrbits.lean",
+   "difficulty": "short",
+   "sorries": 2,
+   "statement": "theorem V6_regradeOrbits … : ReadFrame.hS6a fill (regrade orbits = parent coset orbits re-positioned, scalars preserved); theorem V6_descentOrbits … : ∀ ν ∈ 𝒜′, (TRANSviii_a conjunct-1 window decomposition) ∧ ∃ base b(ν) of the displayed z̄-monomial shape whose F_Qˣ-coset is realized in D.Rc"
+  },
+  {
+   "id": "HC1.V7_stripDischarge",
+   "file": "lean/LeanUrat/HC1/V7_stripDischarge.lean",
+   "difficulty": "short",
+   "sorries": 1,
+   "statement": "theorem V7_stripDischarge … (D : ChildResData …) (hD : ChildResLaws D) : ∀ ν ∈ childWeightSet σ Φ̂, ∃ b, ∀ c ∈ F_Qˣ, ∃ B ≠ 0 ∈ C_Φ̂, σ.w B = ν ∧ D.Rc B = C(c·b)·T(−t′·ν)  [EXACTLY S9a's hS6a′ obligation shape; gated on V5 — EXECUTED]"
+  },
+  {
+   "id": "HC1.V8_childResidual",
+   "file": "lean/LeanUrat/HC1/V8_childResidual.lean",
+   "difficulty": "hard",
+   "sorries": 0,
+   "statement": "def ExplicitDescentCarrier (Prop on ChildResData: Rc f = Σ_{j minimizing} C(dig′ B_j)·T(j·s′ − t′·σ.w B_j)); theorem V8a_carrierAdditive (∃ explicit carrier + additive legs); theorem V8b_carrierLaws (∃ explicit carrier + full ChildResLaws); theorem V8c_wStrict; theorem V8_childResidual = S9w's exact statement shape, ASSEMBLED from V8b+V8c (no own sorry)  [NOT dependent on V5]",
+   "rev": "PROVED IN FULL (2026-07-28, second escalation — the V8b hRmul core): V8a + V8b + V8c ALL Lean-core, zero sorry; capstone V8_childResidual footprint = {propext, Classical.choice, Quot.sound}. Construction: explicit carrier v8Rc ((†) on the Fact-A/B development) + the private graded-residue calculus v8gr (parent hRadd/hRlt + StageCore w_strict/w_jump/R_neg as ONE additive map on the zero-or-deep domain). hRmul = L4_TRANSiii's convolution development Cdev re-derived at digit level + L3_DIV per-pair remainders + (I-aug) depth for carried quotients + the v8gr slot computation + Finset.sum_fiberwise convolution regroup; vanishing convolution coefficients are the same zero on both sides via D.3(d) digit-nonvanishing (the D.1(b) delta-calculus). V8c (first escalation) MOVED above V8a/V8b: its strict law feeds V8b's hRlt leg. UNBLOCKED: S9w_residualLaws now sorry-free (wired exact); S9r follows."
+  },
+  {
+   "id": "HC1.V9_K1nonrec",
+   "file": "lean/LeanUrat/HC1/V9_K1nonrec.lean",
+   "difficulty": "medium",
+   "sorries": 2,
+   "statement": "theorem V9_readSteepness (HistoryCoherent, 1 ≤ i, non-recentering) : ν_i.e·σ_i.h < ν_i.h; theorem V9_K1nonrec : K1_readVertexPin_nonrec's statement VERBATIM via the ReadFrame chain  [SideReads-(iii) seam FENCED — U31-gated; any restatement is a NEW sign-off item]"
   }
  ],
- "signoff_2026-07-28": "F-1..F-6 EXECUTED (one event): F-1 T10(2)+C1(ii) → floorS step floor (lineStep/floorS defs in DefsCar); F-2 Tower.hcharF : CharP F p + C6_cardK_bridge PROVED in C6's file (C6 statement unchanged per §9.2); F-3 S7 → proved shape (scratch transplant, PROVED Lean-core; leg (c) homed to S9d); F-4 S8 → proved (I-aug) leg (PROVED; twist certificate retained in header; TvecUnitLaw homed to S9d); F-5 MoveWitness + core' : StageCoreL (both constructors), 9-file arity ripple (eBirthAux, T3, T4, T6, T7, C2, S13, S11), S11 PROVED (Part 1 = projection), S11a_coreTransport NEW+PROVED; F-6 S17 → ScratchS17 form (+hzsol +hcore), PROVED Lean-core, §4.6 dep-sorry pair out of HC1's cone. S9 DECOMPOSITION: DefsChild.lean (ChildResData choice-spec + childR + childWeightSet) + S9r/S9w/S9a/S9b/S9c (sorry statements) + S9d PROVED (consumes K1 bridges + S7 legs)."
-}
+ "signoff_2026-07-28": "F-1..F-6 EXECUTED (one event): F-1 T10(2)+C1(ii) → floorS step floor (lineStep/floorS defs in DefsCar); F-2 Tower.hcharF : CharP F p + C6_cardK_bridge PROVED in C6's file (C6 statement unchanged per §9.2); F-3 S7 → proved shape (scratch transplant, PROVED Lean-core; leg (c) homed to S9d); F-4 S8 → proved (I-aug) leg (PROVED; twist certificate retained in header; TvecUnitLaw homed to S9d); F-5 MoveWitness + core' : StageCoreL (both constructors), 9-file arity ripple (eBirthAux, T3, T4, T6, T7, C2, S13, S11), S11 PROVED (Part 1 = projection), S11a_coreTransport NEW+PROVED; F-6 S17 → ScratchS17 form (+hzsol +hcore), PROVED Lean-core, §4.6 dep-sorry pair out of HC1's cone. S9 DECOMPOSITION: DefsChild.lean (ChildResData choice-spec + childR + childWeightSet) + S9r/S9w/S9a/S9b/S9c (sorry statements) + S9d PROVED (consumes K1 bridges + S7 legs).",
+ "vkernel_2026-07-28": "V′-KERNEL APPLIED (blueprint §10, V-prime applier): V5 SIGN-OFF EXECUTED FIRST (definition-change authority): Stage.hS6a RESTATED to the FIXED-POINT COSET form (∃ b : Kˣ before ∀ c : FQˣ; digit scalar C(c·b); docstring quotes MOVES 1964–1971 + 2431–2435) in Moves/Defs.lean. Ripple (all green, proofs run through): constructors T1_baseStage (b := 1), S1_transHypGate σpin (b := 1), S10_recStage (transport, SAME b), U17b stageMap (b ↦ resAut-image), U28/U30/U31 gate stages (b := 1), S9a hS6a′ restated to coset form (above-threshold leg b := 1 via L4_TRANSviii_b; strip sorry now = V7's obligation); consumers L5_realRecursion_R3 (two-line), T4/T7/C2 base-stage digLift (K = FQ absorbs the base: c := y·b⁻¹), L4_TRANSviii_a_R5{,_final} CONCLUSION RESTATED (∃ m : ℤ / c·z̄^m → ∃ d₀ : (↥σ′.K)ˣ / c·(d₀:F), ∃-before-∀c unchanged; proof repaired: parent coset base b folded through L2_strideRule, d₀ := the d of the c = 1 instance; PROVED, Lean-core). FULL PERIMETER RECOMPILED GREEN: 532 modules (Moves/MovesC/MovesD/MovesGr/MovesRBase/MovesS/MovesSp/MovesU/MovesX/HC1/HC2); the ONLY exclusions are MovesGr/L2_degZero_subring_v2 + L4_genuine_imp_stageCoreL_v2, PRE-EXISTING failures (machine-verified identical failure against HEAD's pre-V5 Defs.lean; DirectSum instance mismatches, no olean in cache — outside the maintained perimeter, unrelated to hS6a). V0–V9 ELABORATED: DefsV.lean (ReadPair/ReadResData/ReadResLaws/ReadFrame — sorry-free; ReadFrame.hS6a transcribed in the post-V5 coset form, deviation from the pre-V5 §10.1 parenthetical recorded in the file header) + 8 unit files, 13 E-phase sorries, all lake-green, footprints [propext, sorryAx, Classical.choice, Quot.sound] as expected. SideReads-(iii) seam stays FENCED (V9 header carries the §10.1 ⚠ block verbatim; SideReads untouched)."
+}
\ No newline at end of file
diff --git a/lean/LeanUrat/HC1/S10_recStage.lean b/lean/LeanUrat/HC1/S10_recStage.lean
index b206d5f..95020bb 100644
--- a/lean/LeanUrat/HC1/S10_recStage.lean
+++ b/lean/LeanUrat/HC1/S10_recStage.lean
@@ -546,8 +546,10 @@ theorem S10_recStage {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
       weightSet := σ.weightSet
       hWS := fun B hB hin => σ.hWS B hB ((hinC B).mp hin)
       hS6a := by
-        intro ν hν c hcF
-        obtain ⟨B, hB, hin, hw, hR⟩ := σ.hS6a ν hν c hcF
+        intro ν hν
+        obtain ⟨b, hb⟩ := σ.hS6a ν hν
+        refine ⟨b, fun c hcF => ?_⟩
+        obtain ⟨B, hB, hin, hw, hR⟩ := hb c hcF
         exact ⟨B, hB, (hinC B).mpr hin, hw,
           by show shiftL cc (σ.R B) = _; rw [hRfix B hin]; exact hR⟩
       hS6b := by
diff --git a/lean/LeanUrat/HC1/S1_transHypGate.lean b/lean/LeanUrat/HC1/S1_transHypGate.lean
index 6a13b05..947e673 100644
--- a/lean/LeanUrat/HC1/S1_transHypGate.lean
+++ b/lean/LeanUrat/HC1/S1_transHypGate.lean
@@ -751,14 +751,14 @@ private noncomputable def σpin : Stage 2 F4 where
       exact gaussVal_C hc
     rw [Set.mem_setOf_eq, this]
     exact Int.natCast_nonneg _
-  hS6a := fun ν hν c _ => by
+  hS6a := fun ν hν => ⟨1, fun c _ => by
     rw [Set.mem_setOf_eq] at hν
     refine ⟨C ((2 : ℤ_[2]) ^ ν.toNat), by rw [Polynomial.C_ne_zero]; exact two_pow_ne_zero _,
       inC_X_C _, ?_, ?_⟩
     · rw [gaussVal_C (two_pow_ne_zero _), val_two_pow, Int.toNat_of_nonneg hν]
-    · rw [k0_unit_eq_one c, map_one, neg_zero, zero_mul,
+    · rw [k0_unit_eq_one (c * 1), map_one, neg_zero, zero_mul,
         LaurentPolynomial.T_zero, one_mul]
-      exact RS1_C (two_pow_ne_zero _)
+      exact RS1_C (two_pow_ne_zero _)⟩
   hS6b := fun ν a hν => by
     have hν0 : 0 ≤ ν := by
       have hX : gaussVal (X : Polynomial ℤ_[2]) = 0 := gaussVal_X
diff --git a/lean/LeanUrat/HC1/S9a_stageLiteral.lean b/lean/LeanUrat/HC1/S9a_stageLiteral.lean
index 178ed50..0542873 100644
--- a/lean/LeanUrat/HC1/S9a_stageLiteral.lean
+++ b/lean/LeanUrat/HC1/S9a_stageLiteral.lean
@@ -10,6 +10,7 @@ import LeanUrat.HC1.S2_childW
 import LeanUrat.HC1.S3_childK1
 import LeanUrat.HC1.S5_childValuation
 import LeanUrat.HC1.S9w_residualLaws
+import LeanUrat.HC1.V7_stripDischarge
 import LeanUrat.Moves.L3_liftMonic
 import LeanUrat.Moves.L4_TRANSii
 import LeanUrat.Moves.L4_TRANSviii_b_R4
@@ -52,6 +53,13 @@ dropped the guard in transcription; the statement gains the hypothesis
 increment value). The refutation corner now fails the hypotheses:
 `S9a_corner_fails_guard` (`σ.e * g = 1 → ¬ 1 < σ.e * g`).
 
+**RESIDUAL OBLIGATION — DISCHARGED (S9a_final escalation, 2026-07-28): the strip
+leg now closes by `V7_stripDischarge` (proved, core axioms only; the planned
+V6(b)+TRANSviii_a route was found CIRCULAR — TRANSviii_a consumes a full child
+Stage — and V7 was reproved σ′-free from the parent (S6a) coset realizers +
+the carrier's hS5' pin; see V7's header). This file is now `sorry`-free; the
+paragraph below is the historical census record.**
+
 **RESIDUAL OBLIGATION (census re-run 2026-07-28, this file's single `sorry`).**
 Under the guard the construction census closes EXCEPT the (S6a′) BELOW-THRESHOLD
 STRIP: the Stage field `hS6a` at child weights `ν ≤ σ.w Φ̂` (above the threshold
@@ -73,11 +81,18 @@ fails at `(ν, c) = (2, 1)` for EVERY stage carrying the raw pin. The note's own
 coordinate (MOVES 2395–2418), where the transported orbit lands untwisted; the
 K1 faithfulness flag (K1_vertexPin header) anticipated exactly this: "if S9's
 construction realizes a different explicit exponent, the bridges re-instantiate
-at the corrected pin". Adjudication queued: either `VertexPin`/`hS5'` re-pin to
-the alignment function (blueprint §9.5's "mfun := THE alignment function"), or
-the child `hS6a` obligation is scoped to the above-threshold range at increment
-children. difficulty: HARD (assembly; the known type wall). hyp: hEG (the
-adjudicated note guard).
+at the corrected pin".
+
+**ADJUDICATION RESOLVED (V5 sign-off, 2026-07-28 — blueprint §10 Key Finding 2):**
+neither queued option. `mfun ≡ 0` IS the note's V′ normalization (the raw pin is
+CORRECT), and the mismatch was `Stage.hS6a`'s own over-transcription: the note's
+(S6a) is the orbit group AT ITS FIXED POINT (MOVES 1964–1971; D.7(viii)'s
+realizers 2431–2435), i.e. the digit coset `F_Qˣ·b(ν)` with ONE base per weight —
+not the untwisted `F_Qˣ`. `Stage.hS6a` restated to the coset form (∃ b before
+∀ c); this file's `hS6a'` follows it. The strip sorry is now the V7 discharge
+(V6(b)'s minimizing-slot base + `L4_TRANSviii_a` conjunct 2), no longer a
+normalization mismatch. difficulty: HARD (assembly; the known type wall).
+hyp: hEG (the adjudicated note guard).
 -/
 
 set_option linter.style.longLine false
@@ -273,21 +288,29 @@ theorem S9a_stageLiteral {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite
       rw [hc'F, hdig]
     refine ⟨B, hB0, hBc, hBw, ?_⟩
     rw [hc'R, hcs, hBw]
-  -- ## (S6a′): the constant-orbit realizers.  Above the threshold: hS6b′.
-  -- Below (the strip): THE RESIDUAL OBLIGATION — see the header (the raw-pin
-  -- twisted orbit vs the untwisted F_Q orbit; adjudication queued).
-  have hS6a' : ∀ ν ∈ childWeightSet σ Φhat, ∀ c : (↥(σ.nextField zbar))ˣ,
+  -- ## (S6a′): the coset-orbit realizers (V5 fixed-point coset form, blueprint §10
+  -- Key Finding 2).  Above the threshold: hS6b′ with base b = 1 (exact scalars).
+  -- Below (the strip): V7's obligation — V6(b)'s minimizing-slot base +
+  -- TRANSviii_a conjunct 2 verbatim (the fenced V′-kernel discharge).
+  have hS6a' : ∀ ν ∈ childWeightSet σ Φhat, ∃ b : (↥(σ.nextField zbar))ˣ,
+      ∀ c : (↥(σ.nextField zbar))ˣ,
       ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
       ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
-        hexD.choose.Rc B = LaurentPolynomial.C ((c : ↥(σ.nextField zbar))) *
-          LaurentPolynomial.T (- t' * ν) := by
-    intro ν hν c hcFQ
+        hexD.choose.Rc B
+          = LaurentPolynomial.C ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
+            LaurentPolynomial.T (- t' * ν) := by
+    intro ν hν
     rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
-    · exact hS6b' ν c hgt
-    · -- BELOW-THRESHOLD STRIP (ν ≤ σ.w Φ̂): not derivable from the raw D.7(vi)
-      -- pin — the realizable digit set at ν is the twisted orbit
-      -- ⋃ D(w̃)·z̄^{j·s − t·w̃}; hS6a demands the untwisted F_Qˣ.  EXACT RESIDUAL.
-      sorry
+    · exact ⟨1, fun c _ => by rw [mul_one]; exact hS6b' ν c hgt⟩
+    · -- BELOW-THRESHOLD STRIP (ν ≤ σ.w Φ̂): the V7 discharge — PROVED (S9a_final
+      -- escalation, 2026-07-28). NOT the planned "V6(b) + TRANSviii_a conjunct 2
+      -- verbatim" (that route is CIRCULAR: TRANSviii_a consumes a full child Stage σ'
+      -- whose hS6a field IS this obligation). V7's executed proof is σ'-free: the
+      -- parent (S6a) coset realizer ridden up the K1 minimizing slot (L2_strideRule,
+      -- digit linear in the orbit scalar), pinned into Rc through the carrier's own
+      -- hS5' (raw digPrime, mfun ≡ 0). Same kernel in Moves-lemma form:
+      -- `Moves.L4_TRANSviii_c` (threshold-free).
+      exact V7_stripDischarge σ hσ th s' t' hbez' ht'0 hexD.choose hexD.choose_spec ν hν
   -- ## The literal
   refine ⟨{
       e := e', h := h', s := s', t := t',
diff --git a/lean/LeanUrat/HC1/S9w_residualLaws.lean b/lean/LeanUrat/HC1/S9w_residualLaws.lean
index 72793e8..66962ac 100644
--- a/lean/LeanUrat/HC1/S9w_residualLaws.lean
+++ b/lean/LeanUrat/HC1/S9w_residualLaws.lean
@@ -6,6 +6,7 @@ Authors: Asvin G
 import Mathlib
 import LeanUrat.HC1.DefsChild
 import LeanUrat.HC1.S2_childW
+import LeanUrat.HC1.V8_childResidual
 
 /-!
 # HC1.S9w_residualLaws — THE hard new-algebra unit: a LAWFUL child residual exists
@@ -57,7 +58,11 @@ theorem S9w_residualLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite
     (∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) ∧
     (∀ f g', f ≠ 0 → g' ≠ 0 → childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
       childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) := by
-  sorry
+  -- The blueprint §10's staged closure (V′ kernel): the statement is byte-identical
+  -- to the V8 capstone.  Conjunct (ii) [w_strict] is PROVED (V8c, Lean-core);
+  -- conjunct (i) rides on V8b's carrier construction (the remaining hard block —
+  -- this unit inherits V8b's sorryAx until it lands; wired 2026-07-28 escalation).
+  exact V8_childResidual σ hσ th s' t' hbez' ht'0
 
 /-- PROJECTION COROLLARY (PROVED; explicitly NOT this unit's hard content — that
 is `S9w_residualLaws` above): given S9w's lawful-carrier existence, the DEFINED
diff --git a/lean/LeanUrat/HC1/T1_baseStage.lean b/lean/LeanUrat/HC1/T1_baseStage.lean
index 253089b..6559945 100644
--- a/lean/LeanUrat/HC1/T1_baseStage.lean
+++ b/lean/LeanUrat/HC1/T1_baseStage.lean
@@ -1629,7 +1629,9 @@ private noncomputable def baseSt {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
     conv_rhs => rw [hBc]
     rw [T1B.gaussVal_C hb0]
     positivity
-  hS6a := fun ν hν c _ => T1B.realize res e h s t he ν (Set.mem_Ici.mp hν) c
+  hS6a := fun ν hν => ⟨1, fun c _ => by
+    rw [mul_one]
+    exact T1B.realize res e h s t he ν (Set.mem_Ici.mp hν) c⟩
   hS6b := fun ν a hν => T1B.realize res e h s t he ν
     (by rw [T1B.gaussVal_X] at hν; omega) a
 
diff --git a/lean/LeanUrat/HC1/T4_slotMinHt.lean b/lean/LeanUrat/HC1/T4_slotMinHt.lean
index 618ec2a..175c7e3 100644
--- a/lean/LeanUrat/HC1/T4_slotMinHt.lean
+++ b/lean/LeanUrat/HC1/T4_slotMinHt.lean
@@ -374,7 +374,14 @@ private lemma t4_digLift_spec (T : Tower p F) (v : ↥(T.stg 0).FQ) (hv : v ≠
     have hmem : (((Units.mk0 x hxne : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ := by
       rw [Units.val_mk0]
       exact v.2
-    obtain ⟨B, hB0, hBinC, hBw, hBR⟩ := (T.stg 0).hS6a 0 h0mem (Units.mk0 x hxne) hmem
+    -- V5 coset form: at the base stage K = FQ, so the coset base b is absorbed by c := x·b⁻¹
+    obtain ⟨b, hb⟩ := (T.stg 0).hS6a 0 h0mem
+    have hKFQ : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
+    have hbinv : (((Units.mk0 x hxne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F)
+        ∈ (T.stg 0).FQ :=
+      (le_of_eq hKFQ) ((Units.mk0 x hxne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K).2
+    obtain ⟨B, hB0, hBinC, hBw, hBR⟩ := hb (Units.mk0 x hxne * b⁻¹) hbinv
+    rw [inv_mul_cancel_right] at hBR
     refine ⟨B, hB0, hBinC, hBw, ?_⟩
     rw [hBR, Units.val_mk0]
     norm_num
diff --git a/lean/LeanUrat/HC1/T7_alphabetSpan.lean b/lean/LeanUrat/HC1/T7_alphabetSpan.lean
index 6acbfcc..a54a224 100644
--- a/lean/LeanUrat/HC1/T7_alphabetSpan.lean
+++ b/lean/LeanUrat/HC1/T7_alphabetSpan.lean
@@ -330,7 +330,14 @@ private lemma digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
     fun h => hyF (congrArg Subtype.val h)
   have hmem : (((Units.mk0 _ hk₀ne : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ :=
     y.2
-  obtain ⟨B, hB0, hBC, hBw, hBR⟩ := (T.stg 0).hS6a 0 h0mem (Units.mk0 _ hk₀ne) hmem
+  -- V5 coset form: at the base stage K = FQ, so the coset base b is absorbed by c := y·b⁻¹
+  obtain ⟨b, hb⟩ := (T.stg 0).hS6a 0 h0mem
+  have hKFQ : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
+  have hbinv : (((Units.mk0 _ hk₀ne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F)
+      ∈ (T.stg 0).FQ :=
+    (le_of_eq hKFQ) ((Units.mk0 _ hk₀ne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K).2
+  obtain ⟨B, hB0, hBC, hBw, hBR⟩ := hb (Units.mk0 _ hk₀ne * b⁻¹) hbinv
+  rw [inv_mul_cancel_right] at hBR
   have hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
       (T.stg 0).R B = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K)
         * LaurentPolynomial.T 0 := by
diff --git a/lean/LeanUrat/HC2/U17b_galois.lean b/lean/LeanUrat/HC2/U17b_galois.lean
index a6290ed..8658bda 100644
--- a/lean/LeanUrat/HC2/U17b_galois.lean
+++ b/lean/LeanUrat/HC2/U17b_galois.lean
@@ -274,7 +274,10 @@ private noncomputable def stageMap (φ : F ≃+* F) (σ : Stage p F) : Stage p F
       exact ⟨Units.map ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom c,
         by rw [hc, lmap_C_mul_T]; rfl⟩
     hS6a := by
-      intro ν hν c hcF
+      intro ν hν
+      obtain ⟨b, hb⟩ := σ.hS6a ν hν
+      refine ⟨Units.map ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom b,
+        fun c hcF => ?_⟩
       set c₀ : (↥σ.K)ˣ :=
         Units.map (((resAut φ σ.K).symm : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom c
         with hc₀
@@ -282,12 +285,16 @@ private noncomputable def stageMap (φ : F ≃+* F) (σ : Stage p F) : Stage p F
         have h1 : ((c₀ : ↥σ.K) : F) = φ.symm ((c : ↥σ.K) : F) := rfl
         rw [h1]
         exact mem_map_self φ.symm σ.FQ hcF
-      obtain ⟨B, hB0, hBC, hBw, hBR⟩ := σ.hS6a ν hν c₀ hmem
+      obtain ⟨B, hB0, hBC, hBw, hBR⟩ := hb c₀ hmem
       refine ⟨B, hB0, hBC, hBw, ?_⟩
       rw [hBR, lmap_C_mul_T]
       have h2 : ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K)
-            ((c₀ : (↥σ.K)ˣ) : ↥σ.K) = ((c : (↥σ.K)ˣ) : ↥σ.K) :=
-        (resAut φ σ.K).apply_symm_apply _
+            ((c₀ * b : (↥σ.K)ˣ) : ↥σ.K)
+          = ((c * Units.map ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom b :
+              (↥σ.K)ˣ) : ↥σ.K) := by
+        rw [Units.val_mul, Units.val_mul, map_mul]
+        congr 1
+        exact (resAut φ σ.K).apply_symm_apply _
       rw [h2]
     hS6b := by
       intro ν a hν
diff --git a/lean/LeanUrat/HC2/U20a_NAtransportRoot.lean b/lean/LeanUrat/HC2/U20a_NAtransportRoot.lean
index 632430a..cdbcd33 100644
--- a/lean/LeanUrat/HC2/U20a_NAtransportRoot.lean
+++ b/lean/LeanUrat/HC2/U20a_NAtransportRoot.lean
@@ -18,6 +18,7 @@ line's vertex value reads); `hNd` guards the junk truncation `B j = 0` for `j 
 -/
 import Mathlib
 import LeanUrat.HC2.Defs
+import LeanUrat.HC2.K1_vertexPin
 
 set_option linter.style.longLine false
 set_option linter.style.header false
@@ -43,7 +44,7 @@ theorem NA_transport_root {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite
       (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
         = (H.strFrame (i+1) : ℚ) *
           (H.nodes[i]'(by omega)).line.at
-            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
-  sorry
+            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) :=
+  K1_NA_transport_root h i hi1 hsp B Nd hdev hNd
 
 end LeanUrat.MovesJ
diff --git a/lean/LeanUrat/HC2/U20b_NAtransportIncrement.lean b/lean/LeanUrat/HC2/U20b_NAtransportIncrement.lean
index c0544ed..f66adeb 100644
--- a/lean/LeanUrat/HC2/U20b_NAtransportIncrement.lean
+++ b/lean/LeanUrat/HC2/U20b_NAtransportIncrement.lean
@@ -16,6 +16,7 @@ is absolute v_p-scale — the transport equation is stated multiplied through by
 -/
 import Mathlib
 import LeanUrat.HC2.Defs
+import LeanUrat.HC2.K1_vertexPin
 
 set_option linter.style.longLine false
 set_option linter.style.header false
@@ -42,6 +43,12 @@ theorem NA_transport_increment {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [F
         = (H.strFrame (i+1) : ℚ) *
           (H.nodes[i]'(by omega)).line.at
             ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
-  sorry
+  -- U20b_final discharge (blueprint §10 V9: "U20a/U20b/U22-E2 close by the staged
+  -- one-line consumers"): the increment leg has no independent Lean-core route; it is
+  -- the byte-identical fenced statement of `K1_NA_transport_increment`, the one-line
+  -- consumer of the read-indexed D.8 vertex-pin kernel `K1_readVertexPin`.
+  exact K1_NA_transport_increment h i hi1 hsp B Nd hdev hNd
 
 end LeanUrat.MovesJ
+
+#print axioms LeanUrat.MovesJ.NA_transport_increment
diff --git a/lean/LeanUrat/HC2/U22E2_vertexEq.lean b/lean/LeanUrat/HC2/U22E2_vertexEq.lean
index 33983a2..1ddcbe5 100644
--- a/lean/LeanUrat/HC2/U22E2_vertexEq.lean
+++ b/lean/LeanUrat/HC2/U22E2_vertexEq.lean
@@ -17,6 +17,7 @@ v_p-scale, so NO stretch factor appears here (contrast U22-E1).
 -/
 import Mathlib
 import LeanUrat.HC2.Defs
+import LeanUrat.HC2.K1_vertexPin
 
 set_option linter.style.longLine false
 set_option linter.style.header false
@@ -38,6 +39,14 @@ theorem SAE_vertexEq_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Fi
     (H.nodes[i+1]'hi1).ustar
       = (H.nodes[i]'(by omega)).line.at
           ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
-  sorry
+  -- U22-E2_final (V-prime endgame): the F-4 u*-tie reduction is complete and machine-checked
+  -- in `K1_SAE_vertexEq_endpoint` (K1_vertexPin.lean): SideReads(ii) top-endpoint equality
+  -- `e'·σ'.w(B μ) + μ·h' = gam'` + the γ-tie (adjacency) give `σ'.w(B μ) = STR_{i+1}·u*'`,
+  -- and the K1 kernel pins the SAME quantity to `STR_{i+1}·line_i.at(μ·childWidth)`; cancel
+  -- `STR_{i+1} > 0` and `Node.line`/`Node.ustar` absolute scale leaves the fenced ℚ-form.
+  -- The sole residual behind this `exact` is the consolidated non-recentering kernel
+  -- `K1_readVertexPin_nonrec` (the read-side carry-algebra vertex pin) — a SEPARATE `_final`
+  -- unit; U22-E2 carries no independent obligation.
+  exact K1_SAE_vertexEq_endpoint h i hi1 hadj
 
 end LeanUrat.MovesJ
diff --git a/lean/LeanUrat/HC2/U28_gateSep.lean b/lean/LeanUrat/HC2/U28_gateSep.lean
index 7a8354b..b03743e 100644
--- a/lean/LeanUrat/HC2/U28_gateSep.lean
+++ b/lean/LeanUrat/HC2/U28_gateSep.lean
@@ -631,10 +631,10 @@ private noncomputable def sigma0 : Stage 3 F9 where
   hWS := fun B hB _ => by
     simp only [Set.mem_setOf_eq]
     positivity
-  hS6a := fun ν hν c _ => by
-    obtain ⟨B, hB1, hB2, hB3, hB4⟩ := base_realizer ν hν c
+  hS6a := fun ν hν => ⟨1, fun c _ => by
+    obtain ⟨B, hB1, hB2, hB3, hB4⟩ := base_realizer ν hν (c * 1)
     refine ⟨B, hB1, hB2, hB3, ?_⟩
-    rw [hB4, show (-0 : ℤ) * ν = 0 by ring]
+    rw [hB4, show (-0 : ℤ) * ν = 0 by ring]⟩
   hS6b := fun ν a hν => by
     have hν' : ((bwN (Polynomial.X : Polynomial ℤ_[3]) : ℤ)) < ν := hν
     rw [bwN_X] at hν'
diff --git a/lean/LeanUrat/HC2/U30_gatePol.lean b/lean/LeanUrat/HC2/U30_gatePol.lean
index 440ca25..ade43f0 100644
--- a/lean/LeanUrat/HC2/U30_gatePol.lean
+++ b/lean/LeanUrat/HC2/U30_gatePol.lean
@@ -520,12 +520,12 @@ private noncomputable def σ₀ : Stage 2 (ZMod 2) where
   weightSet := {ν : ℤ | ∃ B : Polynomial ℤ_[2], B ≠ 0 ∧ inC (X : Polynomial ℤ_[2]) B ∧ wZ B = ν}
   hWS := fun B hB hBc => ⟨B, hB, hBc, rfl⟩
   hS6a := by
-    rintro ν ⟨B, hB, hBc, hBw⟩ c hcF
-    refine ⟨B, hB, hBc, hBw, ?_⟩
+    rintro ν ⟨B, hB, hBc, hBw⟩
+    refine ⟨1, fun c _ => ⟨B, hB, hBc, hBw, ?_⟩⟩
     have hb : B = C (B.coeff 0) :=
       Polynomial.eq_C_of_degree_le_zero (deg_le_zero_of_lt_X hBc)
     have hb0 : B.coeff 0 ≠ 0 := fun h => hB (by rw [hb, h, Polynomial.C_0])
-    have hc1 : (c : ↥KK) = 1 := subK_eq_one c.ne_zero
+    have hc1 : ((c * 1 : (↥KK)ˣ) : ↥KK) = 1 := subK_eq_one (c * 1).ne_zero
     rw [hb, Rmap_C hb0, hc1]
     simp [LaurentPolynomial.T_zero]
   hS6b := by
diff --git a/lean/LeanUrat/HC2/U31_gateReadsOf.lean b/lean/LeanUrat/HC2/U31_gateReadsOf.lean
index ac6b88e..b0b8dd0 100644
--- a/lean/LeanUrat/HC2/U31_gateReadsOf.lean
+++ b/lean/LeanUrat/HC2/U31_gateReadsOf.lean
@@ -670,10 +670,11 @@ noncomputable def bStage : Stage 2 F4 where
     rw [hBC]
     exact bw_const_nonneg hb
   hS6a := by
-    intro ν hν c _
+    intro ν hν
+    refine ⟨1, fun c _ => ?_⟩
     refine ⟨C (2 ^ ν.toNat), C_ne_zero.mpr (pow_ne_zero _ two_ne_zero'), inC_C, ?_, ?_⟩
     · rw [bw_C2pow, Int.toNat_of_nonneg hν]
-    · rw [bR_C2pow, K2_unit_eq_one c, map_one, neg_zero, zero_mul,
+    · rw [bR_C2pow, K2_unit_eq_one (c * 1), map_one, neg_zero, zero_mul,
         LaurentPolynomial.T_zero, one_mul]
   hS6b := by
     intro ν a hν
diff --git a/lean/LeanUrat/Moves/Defs.lean b/lean/LeanUrat/Moves/Defs.lean
index b3611b5..405b294 100644
--- a/lean/LeanUrat/Moves/Defs.lean
+++ b/lean/LeanUrat/Moves/Defs.lean
@@ -169,11 +169,23 @@ structure Stage (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
   -- `−t·(parent weight)`, so the pair-valued 𝒜 is determined — DEF-6 note).
   weightSet : Set ℤ
   hWS : ∀ B, B ≠ 0 → inC Φ B → wPrev B ∈ weightSet
-  /-- (S6a) EXACTNESS + BASIC REALIZERS: every parent-scale coefficient weight `ν ∈ weightSet` is
-  realized, with any scalar `c` in the CONSTANT base orbit group `O = F_Qˣ` (via `FQ`). -/
-  hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
+  /-- (S6a) EXACTNESS + BASIC REALIZERS — **the FIXED-POINT COSET form** (V5 sign-off,
+  2026-07-28; blueprint §10 Key Finding 2). The note's axiom is the ORBIT-GROUP-AT-ITS-
+  FIXED-POINT statement, D.2 (S6a) rev D⁶/pass-14 finding 1 (MOVES 1964–1971): "every index
+  is realized by an explicit single-slot element whose digit is c·(the index's FORCED
+  MONOMIAL CLASS) with c ranging over the CONSTANT orbit group O := F_Qˣ" — and D.7(viii)'s
+  child realizers likewise have "dig′ … c·(a fixed z̄-monomial class): the O-orbit with
+  O = F_Qˣ CONSTANT" (MOVES 2431–2435). So each weight `ν ∈ weightSet` carries ONE base
+  point `b` (the forced class, ∃-quantified BEFORE the orbit scalar; free in `Kˣ` — the
+  weakest faithful form: depth-2 classes are z̄-monomial but depth ≥ 3 classes are general
+  unit products, and no consumer reads the base's shape, MOVES 1971–1981 "exactness
+  consumes no scalar range"), and the realized digit scalars are the COSET `F_Qˣ·b`.
+  The previous untwisted transcription (`b` hard-coded to 1) was machine-refuted on the
+  below-threshold strip (S9a census, F₉/F₃ numerics) and admits no re-pin repair —
+  restate-after-refutation, same discipline as the S9a guard event. -/
+  hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∃ b : (↥K)ˣ, ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
            ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
-             R B = LaurentPolynomial.C (c : ↥K) * LaurentPolynomial.T (- t * ν)
+             R B = LaurentPolynomial.C ((c * b : (↥K)ˣ) : ↥K) * LaurentPolynomial.T (- t * ν)
   /-- (S6b) FULL SCALARS ABOVE THE KEY WEIGHT: at every parent-scale coefficient weight STRICTLY
   ABOVE the current key's parent weight `wPrev Φ` (DEF-8 threshold), ANY digit scalar in the
   CURRENT field's unit group `Kˣ` (DEF-7) is realizable. -/
diff --git a/lean/LeanUrat/Moves/L4_TRANSi_R3.lean b/lean/LeanUrat/Moves/L4_TRANSi_R3.lean
index 90055b5..828e953 100644
--- a/lean/LeanUrat/Moves/L4_TRANSi_R3.lean
+++ b/lean/LeanUrat/Moves/L4_TRANSi_R3.lean
@@ -86,24 +86,14 @@ private lemma wsum_ge' {p : ℕ} [Fact p.Prime] {ι : Type*} (W : Polynomial ℤ
         calc c ≤ min (W (a i)) (W (∑ j ∈ T, a j)) := le_min h1 h2
           _ ≤ W (a i + ∑ j ∈ T, a j) := hu
 
-theorem L4_TRANSi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' f + w' gg ≤ w' (f * gg) := by
+/-- **Lift-free core of `L4_TRANSi`** (submultiplicativity `w' f + w' g ≤ w'(f·g)`): all
+the lift structure is used only through the abstract exact-remainder DIV hypothesis
+`hDIVw`.  Reused at the SAME KEY (regrade instance) by HC1.V1. -/
+theorem TRANSi_ge_core {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 → B.degree < Φhat.degree → B''.degree < Φhat.degree → (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' f + w' gg ≤ w' (f * gg) := by
   classical
-  -- ── (0) lift basics: ψ monic of degree g ≥ 1, Φ̂ monic of degree e·g·deg Φ ≥ 1
-  have hψmon : ψ.Monic := hlift.1
-  have hψdeg : ψ.natDegree = g := hlift.2.1
-  have hg1 : 1 ≤ g := by
-    by_contra hcon
-    have hg0 : g = 0 := by omega
-    have h0 : ψ.natDegree = 0 := by rw [hψdeg, hg0]
-    obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp h0
-    have h2 : (Polynomial.C x).leadingCoeff = 1 := by rw [hx]; exact hψmon
-    rw [Polynomial.leadingCoeff_C] at h2
-    have hψ1 : ψ = 1 := by rw [← hx, h2, map_one]
-    exact hψ.not_isUnit (by rw [hψ1]; exact isUnit_one)
-  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
-  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
-  have hdegpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
-  have hΦd1 : 1 ≤ Φhat.natDegree := by rw [hΦdeg]; exact hdegpos
+  have hΦmon : Φhat.Monic := hmon
+  have hΦne : Φhat ≠ 0 := hmon.ne_zero
+  have hΦd1 : 1 ≤ Φhat.natDegree := hd1
   have hbot : (⊥ : WithBot ℕ) < Φhat.degree := by
     rw [bot_lt_iff_ne_bot]
     intro hb; exact hΦne (Polynomial.degree_eq_bot.mp hb)
@@ -117,24 +107,7 @@ theorem L4_TRANSi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ
       (B x.1 * B'' x.2) %ₘ Φhat ≠ 0 ∧
         σ.w ((B x.1 * B'' x.2) %ₘ Φhat) = σ.w (B x.1) + σ.w (B'' x.2) := by
     intro x hBj hBk
-    have hBjd : (B x.1).natDegree < σ.e * g * σ.Φ.natDegree := by
-      have h1 := Polynomial.natDegree_lt_natDegree hBj (hBdev.1 x.1)
-      rwa [hΦdeg] at h1
-    have hBkd : (B'' x.2).natDegree < σ.e * g * σ.Φ.natDegree := by
-      have h1 := Polynomial.natDegree_lt_natDegree hBk (hB''dev.1 x.2)
-      rwa [hΦdeg] at h1
-    have hRd : ((B x.1 * B'' x.2) %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
-      rcases eq_or_ne ((B x.1 * B'' x.2) %ₘ Φhat) 0 with h0 | h0
-      · rw [h0]; simpa using hdegpos
-      · have h1 := Polynomial.natDegree_lt_natDegree h0
-          (Polynomial.degree_modByMonic_lt (B x.1 * B'' x.2) hΦmon)
-        rwa [hΦdeg] at h1
-    have hdiv : B x.1 * B'' x.2 =
-        ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat + (B x.1 * B'' x.2) %ₘ Φhat := by
-      linear_combination - Polynomial.modByMonic_add_div (B x.1 * B'' x.2) Φhat
-    obtain ⟨h1, h2, _⟩ := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar
-      (B x.1) (B'' x.2) hBj hBk hBjd hBkd _ _ hdiv hRd
-    exact ⟨h1, h2⟩
+    exact hDIVw (B x.1) (B'' x.2) hBj hBk (hBdev.1 x.1) (hB''dev.1 x.2)
   -- ── … and the quotient weight lower bound (ultrametric on Q·Φ̂ = B·B″ − R_dev)
   have hQw : ∀ x : ℕ × ℕ, B x.1 ≠ 0 → B'' x.2 ≠ 0 → (B x.1 * B'' x.2) /ₘ Φhat ≠ 0 →
       σ.w (B x.1) + σ.w (B'' x.2) ≤ σ.w ((B x.1 * B'' x.2) /ₘ Φhat) + σ.w Φhat := by
@@ -349,4 +322,43 @@ theorem L4_TRANSi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ
   calc w' f + w' gg ≤ (e' : ℤ) * σ.w (C m₀) + (m₀ : ℤ) * (h' : ℤ) := hslot m₀ hCne
     _ = w' (f * gg) := heq.symm
 
+/-- **Lemma TRANS(i)** — submultiplicativity of the child weight (statement unchanged;
+now a thin wrapper over `TRANSi_ge_core`, feeding it the DIV fact from `L3_DIV`). -/
+theorem L4_TRANSi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' f + w' gg ≤ w' (f * gg) := by
+  classical
+  have hψmon : ψ.Monic := hlift.1
+  have hψdeg : ψ.natDegree = g := hlift.2.1
+  have hg1 : 1 ≤ g := by
+    by_contra hcon
+    have hg0 : g = 0 := by omega
+    have h0 : ψ.natDegree = 0 := by rw [hψdeg, hg0]
+    obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp h0
+    have h2 : (Polynomial.C x).leadingCoeff = 1 := by rw [hx]; exact hψmon
+    rw [Polynomial.leadingCoeff_C] at h2
+    have hψ1 : ψ = 1 := by rw [← hx, h2, map_one]
+    exact hψ.not_isUnit (by rw [hψ1]; exact isUnit_one)
+  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
+  have hdegpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
+  have hd1 : 1 ≤ Φhat.natDegree := by rw [hΦdeg]; exact hdegpos
+  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
+      B.degree < Φhat.degree → B''.degree < Φhat.degree →
+      (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'' := by
+    intro B B'' hB hB'' hBd hB''d
+    have hBd' : B.natDegree < σ.e * g * σ.Φ.natDegree := by
+      rw [← hΦdeg]; exact Polynomial.natDegree_lt_natDegree hB hBd
+    have hB''d' : B''.natDegree < σ.e * g * σ.Φ.natDegree := by
+      rw [← hΦdeg]; exact Polynomial.natDegree_lt_natDegree hB'' hB''d
+    have hRd' : ((B * B'') %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
+      by_cases hz : (B * B'') %ₘ Φhat = 0
+      · rw [hz]; simpa using hdegpos
+      · rw [← hΦdeg]
+        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hΦmon)
+    have hdiv : B * B'' = ((B * B'') /ₘ Φhat) * Φhat + (B * B'') %ₘ Φhat := by
+      conv_lhs => rw [← Polynomial.modByMonic_add_div (B * B'') Φhat]
+      ring
+    have hd := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd' hB''d'
+      ((B * B'') %ₘ Φhat) ((B * B'') /ₘ Φhat) hdiv hRd'
+    exact ⟨hd.1, hd.2.1⟩
+  exact TRANSi_ge_core σ Φhat hΦmon hd1 e' h' w' hw' hiaug hDIVw f gg hf hg hfg
+
 end LeanUrat.Moves
diff --git a/lean/LeanUrat/Moves/L4_TRANSiii_R3.lean b/lean/LeanUrat/Moves/L4_TRANSiii_R3.lean
index be1e9a6..1bf7612 100644
--- a/lean/LeanUrat/Moves/L4_TRANSiii_R3.lean
+++ b/lean/LeanUrat/Moves/L4_TRANSiii_R3.lean
@@ -165,25 +165,13 @@ private lemma wiii_sum_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic) {ι :
 
 end TRANSiiiHelpers
 
-theorem L4_TRANSiii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : Φhat.Monic) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (hcop : Nat.gcd e' h' = 1) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' (f * gg) = w' f + w' gg := by
+/-- **Lift-free core of `L4_TRANSiii`** (the `≤` half of multiplicativity): the lift
+structure enters only through the abstract exact-remainder DIV hypothesis `hDIVw`.
+Reused at the SAME KEY (regrade instance) by HC1.V1. -/
+theorem TRANSiii_le_core {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 → B.degree < Φhat.degree → B''.degree < Φhat.degree → (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' (f * gg) ≤ w' f + w' gg := by
   classical
-  -- ===== the `≥` leg is dep L4.TRANSi (imported unit) =====
-  have hge : w' f + w' gg ≤ w' (f * gg) :=
-    L4_TRANSi σ ψ g Φhat hlift hψ hψz zbar hzbar e' h' w' hw' hiaug f gg hf hg hfg
-  refine le_antisymm ?_ hge
   -- ===== basic data =====
-  have hψmon : ψ.Monic := hlift.1
-  have hψdeg : ψ.natDegree = g := hlift.2.1
-  have hg1 : 1 ≤ g := by
-    by_contra hcon
-    have hg0 : g = 0 := by omega
-    have hψ0 : ψ.natDegree = 0 := by rw [hψdeg, hg0]
-    have hψ1 : ψ = 1 := (Polynomial.Monic.natDegree_eq_zero hψmon).mp hψ0
-    exact hψ.not_isUnit (hψ1 ▸ isUnit_one)
-  have hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree := (L3_liftMonic σ ψ g hg1 Φhat hlift).2
   have hΦne : Φhat ≠ 0 := hmon.ne_zero
-  have hdpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
-  have hd1 : 1 ≤ Φhat.natDegree := by omega
   have hiaug' : (e' : ℤ) * σ.w Φhat < (h' : ℤ) := hiaug
   -- ===== developments of f and gg (dep L0.FactA, proved on disk) =====
   obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
@@ -418,26 +406,7 @@ theorem L4_TRANSiii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (
     ring
   have hdevC : IsDevelopment Φhat (f * gg) Cdev (Nf + Ng) := ⟨hCdeg, hCvan, hCsum⟩
   obtain ⟨hminC, -⟩ := hw' (f * gg) Cdev (Nf + Ng) hfg hdevC
-  -- ===== Lemma DIV wrapper (dep L3.DIV, imported unit) =====
-  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
-      B.degree < Φhat.degree → B''.degree < Φhat.degree →
-      (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'' := by
-    intro B B'' hB hB'' hBd hB''d
-    have hBd' : B.natDegree < σ.e * g * σ.Φ.natDegree := by
-      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB hBd
-    have hB''d' : B''.natDegree < σ.e * g * σ.Φ.natDegree := by
-      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB'' hB''d
-    have hRd' : ((B * B'') %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
-      by_cases hz : (B * B'') %ₘ Φhat = 0
-      · rw [hz]; simpa using hdpos
-      · rw [← hΦd]
-        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hmon)
-    have hdiv : B * B'' = ((B * B'') /ₘ Φhat) * Φhat + (B * B'') %ₘ Φhat := by
-      conv_lhs => rw [← Polynomial.modByMonic_add_div (B * B'') Φhat]
-      ring
-    have hd := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd' hB''d'
-      ((B * B'') %ₘ Φhat) ((B * B'') /ₘ Φhat) hdiv hRd'
-    exact ⟨hd.1, hd.2.1⟩
+  -- ===== the DIV wrapper `hDIVw` is now a hypothesis of this core =====
   -- ===== the anchor slot j₀ + k₀ =====
   set β : ℤ := σ.w (Bf j₀) + σ.w (Bg k₀) with hβdef
   obtain ⟨hx_ne, hx_w⟩ := hDIVw (Bf j₀) (Bg k₀) hj₀nz hk₀nz (hBfdeg j₀) (hBgdeg k₀)
@@ -611,4 +580,44 @@ theorem L4_TRANSiii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (
   rw [hcast] at hslot
   linarith [hslot, hμν]
 
+/-- **Lemma TRANS(iii)** — multiplicativity of the child weight (statement unchanged;
+now `le_antisymm` of `TRANSiii_le_core` and `L4_TRANSi`, feeding the DIV fact from
+`L3_DIV`). -/
+theorem L4_TRANSiii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : Φhat.Monic) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (hcop : Nat.gcd e' h' = 1) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' (f * gg) = w' f + w' gg := by
+  classical
+  have hge : w' f + w' gg ≤ w' (f * gg) :=
+    L4_TRANSi σ ψ g Φhat hlift hψ hψz zbar hzbar e' h' w' hw' hiaug f gg hf hg hfg
+  have hψdeg : ψ.natDegree = g := hlift.2.1
+  have hg1 : 1 ≤ g := by
+    have hψmon : ψ.Monic := hlift.1
+    by_contra hcon
+    have hg0 : g = 0 := by omega
+    have hψ0 : ψ.natDegree = 0 := by rw [hψdeg, hg0]
+    have hψ1 : ψ = 1 := (Polynomial.Monic.natDegree_eq_zero hψmon).mp hψ0
+    exact hψ.not_isUnit (hψ1 ▸ isUnit_one)
+  have hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree := (L3_liftMonic σ ψ g hg1 Φhat hlift).2
+  have hdpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
+  have hd1 : 1 ≤ Φhat.natDegree := by omega
+  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
+      B.degree < Φhat.degree → B''.degree < Φhat.degree →
+      (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'' := by
+    intro B B'' hB hB'' hBd hB''d
+    have hBd' : B.natDegree < σ.e * g * σ.Φ.natDegree := by
+      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB hBd
+    have hB''d' : B''.natDegree < σ.e * g * σ.Φ.natDegree := by
+      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB'' hB''d
+    have hRd' : ((B * B'') %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
+      by_cases hz : (B * B'') %ₘ Φhat = 0
+      · rw [hz]; simpa using hdpos
+      · rw [← hΦd]
+        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hmon)
+    have hdiv : B * B'' = ((B * B'') /ₘ Φhat) * Φhat + (B * B'') %ₘ Φhat := by
+      conv_lhs => rw [← Polynomial.modByMonic_add_div (B * B'') Φhat]
+      ring
+    have hd := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd' hB''d'
+      ((B * B'') %ₘ Φhat) ((B * B'') /ₘ Φhat) hdiv hRd'
+    exact ⟨hd.1, hd.2.1⟩
+  exact le_antisymm
+    (TRANSiii_le_core σ Φhat hmon hd1 e' h' w' hw' hiaug hDIVw f gg hf hg hfg) hge
+
 end LeanUrat.Moves
diff --git a/lean/LeanUrat/Moves/L4_TRANSviii_a_R5.lean b/lean/LeanUrat/Moves/L4_TRANSviii_a_R5.lean
index bae87d7..d2d05f9 100644
--- a/lean/LeanUrat/Moves/L4_TRANSviii_a_R5.lean
+++ b/lean/LeanUrat/Moves/L4_TRANSviii_a_R5.lean
@@ -42,14 +42,11 @@ All closed (2026-07-27, ported back from `L4_TRANSviii_a_R5_final.lean`):
 * **Conjunct 1, ⟸**: the single-slot element `B := C·Φ^j` has
   `σ'.wPrev B = σ.w B = σ.w C + j·h = γ + j·h` (`child_wPrev`, `w_mul_keyPow`) and lies in `C_Φ̂`
   by the degree bound `deg C + j·deg Φ < e·g·deg Φ = deg Φ̂`.
-* **Conjunct 2 (∃ m BEFORE ∀ c)**: fix `ν := σ.wPrev C₀` (so `γ = e·ν` by `hStretch`) and the
-  frame function `mfun` from `htrans.child_dig_frame`, and set
-  `m := (−t·ν + s·j) + mfun (γ + j·h)` — c-INDEPENDENT. For each orbit scalar `c` (transferred
-  to `(↥σ.K)ˣ` through `σ'.FQ = σ.FQ ≤ σ.K`), the (S6a) realizer `C` at `(ν, c)` gives
-  `B := C·Φ^j` with `σ.R B = C(c)·T(−t·ν + s·j)` (`L2_strideRule`), so
-  `dig'(B) = c·z̄^{−t·ν+s·j}` (`eval₂_C_mul_T` — the orbit scalar enters LINEARLY), and
-  `child_dig_frame` yields the child digit `d` with `(d:F) = dig'(B)·z̄^{mfun(γ+j·h)}
-  = c·z̄^m` at the forced position `−t'·(γ+j·h)`; the weights are `child_wPrev`/`hStretch'`.
+* **Conjunct 2 (∃ d₀ BEFORE ∀ c — RESTATED to the V5 COSET form, 2026-07-28, in step with
+  the _final file)**: the former `(d:F) = c·z̄^m` weakens to `(d:F) = c·(d₀:F)` with ONE fixed
+  child base unit `d₀` per index, matching the restated coset (S6a) (MOVES 1964–1971,
+  2431–2435). See the _final file's header for the full proof note; `d₀ :=` the `d` of the
+  `c = 1` instance.
 -/
 
 set_option linter.style.longLine false
@@ -144,7 +141,7 @@ private lemma dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (h
       rw [e1]
       linear_combination hdiv
 
-theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ m : ℤ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((zbar ^ m : Fˣ) : F)) := by
+theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ d₀ : (↥σ'.K)ˣ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((d₀ : ↥σ'.K) : F)) := by
   have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
   have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
   -- degree bound for single-slot elements `C·Φ^j`, `j < e·g`: they lie in `C_Φ̂`
@@ -191,16 +188,66 @@ theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
       refine ⟨C * σ.Φ ^ j, mul_ne_zero hC hΦj, hslot C j hC hCc hj, ?_⟩
       rw [htrans.base.child_wPrev, w_mul_keyPow σ C hC j, hCw]
       exact hW.symm
-  · -- Conjunct 2: single-slot realizers, ONE fixed z̄-monomial class per index (∃ m BEFORE ∀ c).
+  · -- Conjunct 2: single-slot realizers, ONE fixed COSET BASE per index (∃ d₀ BEFORE ∀ c —
+    -- the V5 coset form; blueprint §10 Key Finding 2).
     rintro γ j ⟨C₀, hC₀0, hC₀c, hC₀w⟩ hj
     -- the parent-scale weight ν of the index: γ = e·ν (hStretch), ν ∈ 𝒲 (hWS)
     have hν : σ.wPrev C₀ ∈ σ.weightSet := σ.hWS C₀ hC₀0 hC₀c
     have hγ : γ = (σ.e : ℤ) * σ.wPrev C₀ := by
       rw [← hC₀w]; exact σ.hStretch C₀ hC₀0 hC₀c
-    -- the frame function, fixed BEFORE the orbit scalar varies (child_dig_frame)
+    -- the frame function AND the parent coset base, both fixed BEFORE the orbit scalar varies
     obtain ⟨mfun, hmf⟩ := htrans.child_dig_frame
-    -- the c-INDEPENDENT frame exponent of the index (γ, j)
-    refine ⟨(- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) + mfun (γ + (j : ℤ) * σ.h), ?_⟩
+    obtain ⟨b, hb⟩ := σ.hS6a (σ.wPrev C₀) hν
+    -- the generic single-slot realizer, for ANY parent-FQ orbit scalar c₁
+    have hreal : ∀ c₁ : (↥σ.K)ˣ, ((c₁ : ↥σ.K) : F) ∈ σ.FQ →
+        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧
+          σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧
+          ∃ d : (↥σ'.K)ˣ,
+            σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) *
+              LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧
+            ((d : ↥σ'.K) : F)
+              = ((c₁ : ↥σ.K) : F) * (((b : ↥σ.K) : F) *
+                ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)
+                    + mfun (γ + (j : ℤ) * σ.h)) : Fˣ) : F)) := by
+      intro c₁ hc₁FQ
+      -- the (S6a) coset realizer at (ν, c₁)
+      obtain ⟨C, hC0, hCc, hCν, hCR⟩ := hb c₁ hc₁FQ
+      have hCw : σ.w C = γ := by
+        rw [σ.hStretch C hC0 hCc, hCν]; exact hγ.symm
+      -- the single-slot realizer B := C·Φ^j and its weights
+      have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
+      have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hj
+      have hwB : σ.w (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
+        rw [w_mul_keyPow σ C hC0 j, hCw]
+      have hwPrevB : σ'.wPrev (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
+        rw [htrans.base.child_wPrev]; exact hwB
+      refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwPrevB, ?_, ?_⟩
+      · -- σ'.w B = e'·(γ + j·h), via the child's own stretch law
+        have hBc' : inC σ'.Φ (C * σ.Φ ^ j) := by
+          rw [htrans.base.child_key]; exact hBinC
+        rw [σ'.hStretch _ hB0 hBc', hwPrevB]
+      · -- the child digit: position −t'·(γ+j·h), scalar d with (d:F) = c₁·(b·z̄^m)
+        obtain ⟨d, hdR, hdF⟩ := hmf (C * σ.Φ ^ j) hB0 hBinC
+        rw [hwB] at hdR hdF
+        refine ⟨d, hdR, ?_⟩
+        -- the parent residual of the slot element: R(B) = C(c₁·b)·T(−t·ν + s·j) (stride rule)
+        have hRB : σ.R (C * σ.Φ ^ j)
+            = LaurentPolynomial.C ((c₁ * b : (↥σ.K)ˣ) : ↥σ.K)
+              * LaurentPolynomial.T (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) := by
+          rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
+        -- the parent digit: dig'(B) = (c₁·b)·z̄^{−t·ν+s·j} — the orbit scalar enters LINEARLY
+        have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
+            = (((c₁ * b : (↥σ.K)ˣ) : ↥σ.K) : F)
+              * ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) : Fˣ) : F) := by
+          show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
+          rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
+          rfl
+        rw [hdF, hdig, mul_assoc, ← Units.val_mul, ← zpow_add, Units.val_mul,
+          MulMemClass.coe_mul, mul_assoc]
+    -- the c-INDEPENDENT child coset base d₀ := the d of the c = 1 instance
+    have h1FQ : (((1 : (↥σ.K)ˣ) : ↥σ.K) : F) ∈ σ.FQ := by simp
+    obtain ⟨B₁, hB₁0, hB₁inC, hB₁w, hB₁w', d₀, hd₀R, hd₀F⟩ := hreal 1 h1FQ
+    refine ⟨d₀, ?_⟩
     intro c hcFQ
     -- transfer the orbit scalar c through σ'.FQ = σ.FQ ≤ σ.K
     have hx0 : ((c : ↥σ'.K) : F) ≠ 0 :=
@@ -211,38 +258,11 @@ theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
       simp [Subtype.ext_iff, hx0]
     set c₁ : (↥σ.K)ˣ := Units.mk0 ⟨((c : ↥σ'.K) : F), hxK⟩ hc₁0 with hc₁
     have hc₁FQ : ((c₁ : ↥σ.K) : F) ∈ σ.FQ := hxFQ
-    -- the (S6a) basic realizer at (ν, c)
-    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := σ.hS6a (σ.wPrev C₀) hν c₁ hc₁FQ
-    have hCw : σ.w C = γ := by
-      rw [σ.hStretch C hC0 hCc, hCν]; exact hγ.symm
-    -- the single-slot realizer B := C·Φ^j and its weights
-    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
-    have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hj
-    have hwB : σ.w (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
-      rw [w_mul_keyPow σ C hC0 j, hCw]
-    have hwPrevB : σ'.wPrev (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
-      rw [htrans.base.child_wPrev]; exact hwB
-    refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwPrevB, ?_, ?_⟩
-    · -- σ'.w B = e'·(γ + j·h), via the child's own stretch law
-      have hBc' : inC σ'.Φ (C * σ.Φ ^ j) := by
-        rw [htrans.base.child_key]; exact hBinC
-      rw [σ'.hStretch _ hB0 hBc', hwPrevB]
-    · -- the child digit: position −t'·(γ+j·h), scalar d = c·z̄^m
-      obtain ⟨d, hdR, hdF⟩ := hmf (C * σ.Φ ^ j) hB0 hBinC
-      rw [hwB] at hdR hdF
-      refine ⟨d, hdR, ?_⟩
-      -- the parent residual of the slot element: R(B) = C(c₁)·T(−t·ν + s·j) (stride rule)
-      have hRB : σ.R (C * σ.Φ ^ j)
-          = LaurentPolynomial.C (c₁ : ↥σ.K)
-            * LaurentPolynomial.T (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) := by
-        rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
-      -- the parent digit: dig'(B) = c·z̄^{−t·ν+s·j} — the orbit scalar enters LINEARLY
-      have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
-          = ((c : ↥σ'.K) : F)
-            * ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) : Fˣ) : F) := by
-        show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
-        rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
-        rfl
-      rw [hdF, hdig, mul_assoc, ← Units.val_mul, ← zpow_add]
+    obtain ⟨B, hB0, hBinC, hBw, hBw', d, hdR, hdF⟩ := hreal c₁ hc₁FQ
+    refine ⟨B, hB0, hBinC, hBw, hBw', d, hdR, ?_⟩
+    -- (d:F) = c₁·(b·z̄^m) = c·(d₀:F), since (d₀:F) = 1·(b·z̄^m) and (c₁:F) = (c:F)
+    have hc₁c : ((c₁ : ↥σ.K) : F) = ((c : ↥σ'.K) : F) := by rw [hc₁]; rfl
+    rw [hdF, hd₀F, hc₁c]
+    simp
 
 end LeanUrat.Moves
diff --git a/lean/LeanUrat/Moves/L4_TRANSviii_a_R5_final.lean b/lean/LeanUrat/Moves/L4_TRANSviii_a_R5_final.lean
index 84fe502..148834f 100644
--- a/lean/LeanUrat/Moves/L4_TRANSviii_a_R5_final.lean
+++ b/lean/LeanUrat/Moves/L4_TRANSviii_a_R5_final.lean
@@ -35,14 +35,20 @@ was authorised at this explicitly conditional/local scope (audit §"Fan-out may
 * **Conjunct 1, ⟸**: the single-slot element `B := C·Φ^j` has
   `σ'.wPrev B = σ.w B = σ.w C + j·h = γ + j·h` (`child_wPrev`, `w_mul_keyPow`) and lies in `C_Φ̂`
   by the degree bound `deg C + j·deg Φ < e·g·deg Φ = deg Φ̂`.
-* **Conjunct 2 (∃ m BEFORE ∀ c)**: fix `ν := σ.wPrev C₀` (so `γ = e·ν` by `hStretch`) and the
-  frame function `mfun` from `htrans.child_dig_frame`, and set
-  `m := (−t·ν + s·j) + mfun (γ + j·h)` — c-INDEPENDENT. For each orbit scalar `c` (transferred
-  to `(↥σ.K)ˣ` through `σ'.FQ = σ.FQ ≤ σ.K`), the (S6a) realizer `C` at `(ν, c)` gives
-  `B := C·Φ^j` with `σ.R B = C(c)·T(−t·ν + s·j)` (`L2_strideRule`), so
-  `dig'(B) = c·z̄^{−t·ν+s·j}` (`eval₂_C_mul_T` — the orbit scalar enters LINEARLY), and
+* **Conjunct 2 (∃ d₀ BEFORE ∀ c — RESTATED to the V5 COSET form, 2026-07-28; blueprint §10
+  Key Finding 2 + the V5 ripple census)**: the former conclusion `(d:F) = c·z̄^m` (one fixed
+  z̄-monomial class per index) is WEAKENED to the coset form `(d:F) = c·(d₀:F)` with ONE fixed
+  child base unit `d₀ : (↥σ'.K)ˣ` per index — exactly D.7(viii)'s "c·(a fixed z̄-monomial
+  class): the O-orbit with O = F_Qˣ CONSTANT" (MOVES 2431–2435) read against the restated
+  parent (S6a) (the fixed-point coset form, MOVES 1964–1971). Proof: fix `ν := σ.wPrev C₀`
+  (so `γ = e·ν` by `hStretch`), the frame function `mfun` from `htrans.child_dig_frame`, and
+  the PARENT coset base `b` from (S6a) at `ν` — all c-INDEPENDENT. For each orbit scalar `c`
+  (transferred to `(↥σ.K)ˣ` through `σ'.FQ = σ.FQ ≤ σ.K`), the (S6a) realizer `C` at `(ν, c)`
+  gives `B := C·Φ^j` with `σ.R B = C(c·b)·T(−t·ν + s·j)` (`L2_strideRule`), so
+  `dig'(B) = (c·b)·z̄^{−t·ν+s·j}` (`eval₂_C_mul_T` — the orbit scalar enters LINEARLY), and
   `child_dig_frame` yields the child digit `d` with `(d:F) = dig'(B)·z̄^{mfun(γ+j·h)}
-  = c·z̄^m` at the forced position `−t'·(γ+j·h)`; the weights are `child_wPrev`/`hStretch'`.
+  = c·(b·z̄^m)` at the forced position `−t'·(γ+j·h)`; `d₀ :=` the `d` of the `c = 1` instance
+  (so `(d₀:F) = b·z̄^m`), and the weights are `child_wPrev`/`hStretch'`.
 -/
 
 set_option linter.style.longLine false
@@ -137,7 +143,7 @@ private lemma dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (h
       rw [e1]
       linear_combination hdiv
 
-theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ m : ℤ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((zbar ^ m : Fˣ) : F)) := by
+theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ d₀ : (↥σ'.K)ˣ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((d₀ : ↥σ'.K) : F)) := by
   have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
   have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
   -- degree bound for single-slot elements `C·Φ^j`, `j < e·g`: they lie in `C_Φ̂`
@@ -184,16 +190,66 @@ theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
       refine ⟨C * σ.Φ ^ j, mul_ne_zero hC hΦj, hslot C j hC hCc hj, ?_⟩
       rw [htrans.base.child_wPrev, w_mul_keyPow σ C hC j, hCw]
       exact hW.symm
-  · -- Conjunct 2: single-slot realizers, ONE fixed z̄-monomial class per index (∃ m BEFORE ∀ c).
+  · -- Conjunct 2: single-slot realizers, ONE fixed COSET BASE per index (∃ d₀ BEFORE ∀ c —
+    -- the V5 coset form; blueprint §10 Key Finding 2).
     rintro γ j ⟨C₀, hC₀0, hC₀c, hC₀w⟩ hj
     -- the parent-scale weight ν of the index: γ = e·ν (hStretch), ν ∈ 𝒲 (hWS)
     have hν : σ.wPrev C₀ ∈ σ.weightSet := σ.hWS C₀ hC₀0 hC₀c
     have hγ : γ = (σ.e : ℤ) * σ.wPrev C₀ := by
       rw [← hC₀w]; exact σ.hStretch C₀ hC₀0 hC₀c
-    -- the frame function, fixed BEFORE the orbit scalar varies (child_dig_frame)
+    -- the frame function AND the parent coset base, both fixed BEFORE the orbit scalar varies
     obtain ⟨mfun, hmf⟩ := htrans.child_dig_frame
-    -- the c-INDEPENDENT frame exponent of the index (γ, j)
-    refine ⟨(- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) + mfun (γ + (j : ℤ) * σ.h), ?_⟩
+    obtain ⟨b, hb⟩ := σ.hS6a (σ.wPrev C₀) hν
+    -- the generic single-slot realizer, for ANY parent-FQ orbit scalar c₁
+    have hreal : ∀ c₁ : (↥σ.K)ˣ, ((c₁ : ↥σ.K) : F) ∈ σ.FQ →
+        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧
+          σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧
+          ∃ d : (↥σ'.K)ˣ,
+            σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) *
+              LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧
+            ((d : ↥σ'.K) : F)
+              = ((c₁ : ↥σ.K) : F) * (((b : ↥σ.K) : F) *
+                ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)
+                    + mfun (γ + (j : ℤ) * σ.h)) : Fˣ) : F)) := by
+      intro c₁ hc₁FQ
+      -- the (S6a) coset realizer at (ν, c₁)
+      obtain ⟨C, hC0, hCc, hCν, hCR⟩ := hb c₁ hc₁FQ
+      have hCw : σ.w C = γ := by
+        rw [σ.hStretch C hC0 hCc, hCν]; exact hγ.symm
+      -- the single-slot realizer B := C·Φ^j and its weights
+      have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
+      have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hj
+      have hwB : σ.w (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
+        rw [w_mul_keyPow σ C hC0 j, hCw]
+      have hwPrevB : σ'.wPrev (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
+        rw [htrans.base.child_wPrev]; exact hwB
+      refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwPrevB, ?_, ?_⟩
+      · -- σ'.w B = e'·(γ + j·h), via the child's own stretch law
+        have hBc' : inC σ'.Φ (C * σ.Φ ^ j) := by
+          rw [htrans.base.child_key]; exact hBinC
+        rw [σ'.hStretch _ hB0 hBc', hwPrevB]
+      · -- the child digit: position −t'·(γ+j·h), scalar d with (d:F) = c₁·(b·z̄^m)
+        obtain ⟨d, hdR, hdF⟩ := hmf (C * σ.Φ ^ j) hB0 hBinC
+        rw [hwB] at hdR hdF
+        refine ⟨d, hdR, ?_⟩
+        -- the parent residual of the slot element: R(B) = C(c₁·b)·T(−t·ν + s·j) (stride rule)
+        have hRB : σ.R (C * σ.Φ ^ j)
+            = LaurentPolynomial.C ((c₁ * b : (↥σ.K)ˣ) : ↥σ.K)
+              * LaurentPolynomial.T (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) := by
+          rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
+        -- the parent digit: dig'(B) = (c₁·b)·z̄^{−t·ν+s·j} — the orbit scalar enters LINEARLY
+        have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
+            = (((c₁ * b : (↥σ.K)ˣ) : ↥σ.K) : F)
+              * ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) : Fˣ) : F) := by
+          show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
+          rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
+          rfl
+        rw [hdF, hdig, mul_assoc, ← Units.val_mul, ← zpow_add, Units.val_mul,
+          MulMemClass.coe_mul, mul_assoc]
+    -- the c-INDEPENDENT child coset base d₀ := the d of the c = 1 instance
+    have h1FQ : (((1 : (↥σ.K)ˣ) : ↥σ.K) : F) ∈ σ.FQ := by simp
+    obtain ⟨B₁, hB₁0, hB₁inC, hB₁w, hB₁w', d₀, hd₀R, hd₀F⟩ := hreal 1 h1FQ
+    refine ⟨d₀, ?_⟩
     intro c hcFQ
     -- transfer the orbit scalar c through σ'.FQ = σ.FQ ≤ σ.K
     have hx0 : ((c : ↥σ'.K) : F) ≠ 0 :=
@@ -204,38 +260,11 @@ theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
       simp [Subtype.ext_iff, hx0]
     set c₁ : (↥σ.K)ˣ := Units.mk0 ⟨((c : ↥σ'.K) : F), hxK⟩ hc₁0 with hc₁
     have hc₁FQ : ((c₁ : ↥σ.K) : F) ∈ σ.FQ := hxFQ
-    -- the (S6a) basic realizer at (ν, c)
-    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := σ.hS6a (σ.wPrev C₀) hν c₁ hc₁FQ
-    have hCw : σ.w C = γ := by
-      rw [σ.hStretch C hC0 hCc, hCν]; exact hγ.symm
-    -- the single-slot realizer B := C·Φ^j and its weights
-    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
-    have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hj
-    have hwB : σ.w (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
-      rw [w_mul_keyPow σ C hC0 j, hCw]
-    have hwPrevB : σ'.wPrev (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
-      rw [htrans.base.child_wPrev]; exact hwB
-    refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwPrevB, ?_, ?_⟩
-    · -- σ'.w B = e'·(γ + j·h), via the child's own stretch law
-      have hBc' : inC σ'.Φ (C * σ.Φ ^ j) := by
-        rw [htrans.base.child_key]; exact hBinC
-      rw [σ'.hStretch _ hB0 hBc', hwPrevB]
-    · -- the child digit: position −t'·(γ+j·h), scalar d = c·z̄^m
-      obtain ⟨d, hdR, hdF⟩ := hmf (C * σ.Φ ^ j) hB0 hBinC
-      rw [hwB] at hdR hdF
-      refine ⟨d, hdR, ?_⟩
-      -- the parent residual of the slot element: R(B) = C(c₁)·T(−t·ν + s·j) (stride rule)
-      have hRB : σ.R (C * σ.Φ ^ j)
-          = LaurentPolynomial.C (c₁ : ↥σ.K)
-            * LaurentPolynomial.T (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) := by
-        rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
-      -- the parent digit: dig'(B) = c·z̄^{−t·ν+s·j} — the orbit scalar enters LINEARLY
-      have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
-          = ((c : ↥σ'.K) : F)
-            * ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) : Fˣ) : F) := by
-        show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
-        rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
-        rfl
-      rw [hdF, hdig, mul_assoc, ← Units.val_mul, ← zpow_add]
+    obtain ⟨B, hB0, hBinC, hBw, hBw', d, hdR, hdF⟩ := hreal c₁ hc₁FQ
+    refine ⟨B, hB0, hBinC, hBw, hBw', d, hdR, ?_⟩
+    -- (d:F) = c₁·(b·z̄^m) = c·(d₀:F), since (d₀:F) = 1·(b·z̄^m) and (c₁:F) = (c:F)
+    have hc₁c : ((c₁ : ↥σ.K) : F) = ((c : ↥σ'.K) : F) := by rw [hc₁]; rfl
+    rw [hdF, hd₀F, hc₁c]
+    simp
 
 end LeanUrat.Moves
diff --git a/lean/LeanUrat/Moves/L5_realRecursion_R3.lean b/lean/LeanUrat/Moves/L5_realRecursion_R3.lean
index 14cff75..da980ec 100644
--- a/lean/LeanUrat/Moves/L5_realRecursion_R3.lean
+++ b/lean/LeanUrat/Moves/L5_realRecursion_R3.lean
@@ -250,7 +250,8 @@ theorem L5_realRecursion {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite
     have key : (σ.e : ℤ) * ν = W - (j : ℤ) * σ.h := hνeq
     have h1FQ : ((((1 : (↥σ.K)ˣ)) : ↥σ.K) : F) ∈ σ.FQ := by
       simpa using σ.FQ.one_mem
-    obtain ⟨b, hbne, hbc, hbw, _hbR⟩ := σ.hS6a ν hν 1 h1FQ
+    obtain ⟨b₀, hb₀⟩ := σ.hS6a ν hν
+    obtain ⟨b, hbne, hbc, hbw, _hbR⟩ := hb₀ 1 h1FQ
     refine ⟨b * σ.Φ ^ j, mul_ne_zero hbne (pow_ne_zero j hΦ), ?_, ?_⟩
     · show (b * σ.Φ ^ j).degree < Φhat.degree
       have hne : b * σ.Φ ^ j ≠ 0 := mul_ne_zero hbne (pow_ne_zero j hΦ)

=== END SECTION A ===
=== SECTION B: untracked V*.lean + DefsV.lean files (full contents) ===

----- FILE: lean/LeanUrat/HC1/DefsV.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild

/-!
# HC1/DefsV — the V′ kernel Defs layer (blueprint §10, unit V0; ADDITIVE — no
accepted statement touched)

**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` §10 ("THE V′ KERNEL — the
read-functional carry algebra in the aligned frame"), unit V0.  The ONE design
behind the three hard residuals (S9w-(i), S9a's hS6a strip, HC2's
`K1_readVertexPin_nonrec`): the D.1(e) residual pack rebuilt at a NEW
(e★, h★, s★, t★)-position law over an existing stage's data —

  (†)  wV(f) := min_j ( e★·σ.w(B_j) + j·h★ )              (the read functional)
       RV(f) := Σ_{j minimizing} C(φ(slot-j digit)) · T(j·s★ − t★·σ.w(B_j))

* REGRADE instance (K1-nonrec): P = σ.Φ (the SAME key), (e★,h★) = the RECORDED
  READ pair, φ = identity on ↥σ.K.  **NOTE THE REUSE: wV at the same key IS
  `childW σ σ.Φ e★ h★` — no new functional is defined here.**
* DESCENT instance (S9w): P = Φ̂, (e★,h★) = th's (e′,h′), φ = z̄-evaluation —
  carried by the EXISTING `ChildResData`/`ChildResLaws` (DefsChild); V8's units.

FINDING 3 (why `ReadFrame` is a PARTIAL pack, not a `Stage`): the regraded
frame's coefficient weights under wVPrev = σ.w lie in σ.e·ℤ (hStretch), so
`Stage.hS6b`'s quantifier "∀ ν > wPrev Φ" (the D.9(b) cofinite range) is
UNSATISFIABLE at a regrade for σ.e > 1.  Hence NO hS6b, NO hvalgrp, NO
reps/Tvec — everything the D.5/D.8 reruns consume and nothing more.

POST-V5 NOTE: `ReadFrame.hS6a` is transcribed in the CURRENT `Stage.hS6a` form,
which since the V5 sign-off (2026-07-28) is the FIXED-POINT COSET form (∃ base
before ∀ orbit scalar; MOVES 1964–1971, 2431–2435).  V6(a) fills it: regrade
scalars are PRESERVED (no z̄ enters at the same level), so the parent's coset
bases transport verbatim.

Falsifiability: every pin is an equation against existing objects; wrong
positions break V2's hRmul at the first product.  Definitions only — no
theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The read pair** (blueprint §10 V0): a legal (e★, h★, s★, t★) regrade index over
the stage σ — lowest terms + Bézout + the (P2) pin + the read-form (I-aug)
STEEPNESS `e★·σ.h < h★` (D.4, MOVES 2219–2220 "λ > w(Φ)" at the stage scale; on
the HC2 side extracted from `HistoryCoherent`'s slope law + strict steepening —
`h_{i+1} > h_i·e_{i+1}·e_i·g_i ≥ e_{i+1}·h_i`, V9's short lemma). -/
def ReadPair (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Prop :=
  1 ≤ estar ∧ 1 ≤ hstar ∧ Nat.gcd estar hstar = 1 ∧
    (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 ∧
    (estar = 1 → tstar = 0) ∧
    (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ)

/-- **The regrade carrier** (blueprint §10 V0), mirroring `ChildResData`: a residual
function on all of A for the regrade index (e★, h★, s★, t★) AT THE SAME KEY σ.Φ,
carrying the two pins —
* the key pin `Rv σ.Φ = T s★` (slot-1 arithmetic `1·s★ − t★·σ.w 1 = s★`);
* the S5-shape pin: scalars PRESERVED from the frame residual, positions RE-FORCED
  at the new pair (`−t★·σ.w B` — the (S5) position law at (e★, h★), MOVES 1960–1963). -/
structure ReadResData (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
  /-- the regrade residual function on all of A -/
  Rv : Polynomial ℤ_[p] → LaurentPolynomial ↥σ.K
  /-- the key pin `Rv(Φ) = z^{s★}` (D.3(b) at the regrade) -/
  hRPhi : Rv σ.Φ = LaurentPolynomial.T sstar
  /-- the S5-shape pin: SAME scalar as the frame digit, position re-forced at the
  new pair — the (S5) position law `−t★·σ.w B` (MOVES 1960–1963) -/
  hS5 : ∀ B, B ≠ 0 → inC σ.Φ B →
      ∃ c : (↥σ.K)ˣ,
        σ.R B = LaurentPolynomial.C (c : ↥σ.K) *
            LaurentPolynomial.T (- σ.t * σ.wPrev B) ∧
        Rv B = LaurentPolynomial.C (c : ↥σ.K) *
            LaurentPolynomial.T (- tstar * σ.w B)

/-- **The regrade law pack** (blueprint §10 V0): the D.1(e) laws of a regrade carrier
w.r.t. the read functional `childW σ σ.Φ e★ h★` — the SAME seven conjuncts as
`ChildResLaws` (hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg), at the regrade
instance of (†). -/
def ReadResLaws {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (D : ReadResData σ estar hstar sstar tstar) : Prop :=
  (D.Rv 0 = 0) ∧
  (∀ f, f ≠ 0 → D.Rv f ≠ 0) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rv (f * g) = D.Rv f * D.Rv g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
      childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f →
      D.Rv (f + g) = D.Rv f + D.Rv g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
      D.Rv (f + g) = D.Rv f) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar (f + g) →
      D.Rv f + D.Rv g = 0) ∧
  (∀ f, D.Rv (-f) = - D.Rv f)

/-- **The read frame** (blueprint §10 V0, Finding 3): the PARTIAL stage pack of the
regrade — a lawful carrier + the wV laws (hwmul/hwult/hwΦ/hK1-at-Φ/hStretch) +
hS6a in the current (post-V5 coset) `Stage.hS6a` form — everything the D.5/D.8
reruns (V3/V4) consume; **NO hS6b** (unsatisfiable at regrades for σ.e > 1,
Finding 3), NO hvalgrp, NO reps/Tvec. -/
structure ReadFrame (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
  /-- the lawful regrade carrier -/
  D : ReadResData σ estar hstar sstar tstar
  /-- the carrier is lawful (V2's content) -/
  laws : ReadResLaws D
  /-- wV is multiplicative (V1's content) -/
  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 →
      childW σ σ.Φ estar hstar (f * g)
        = childW σ σ.Φ estar hstar f + childW σ σ.Φ estar hstar g
  /-- wV is ultrametric -/
  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
        ≤ childW σ σ.Φ estar hstar (f + g)
  /-- the key's read weight is h★ (slot-1 arithmetic) -/
  hwPhi : childW σ σ.Φ estar hstar σ.Φ = (hstar : ℤ)
  /-- Lemma K1 at the frame's own key, in the read grading -/
  hK1 : K1At (childW σ σ.Φ estar hstar) σ.Φ ((hstar : ℤ))
  /-- the regrade stretch: wV = e★·σ.w on the coefficient space C_Φ -/
  hStretch : ∀ B, B ≠ 0 → inC σ.Φ B →
      childW σ σ.Φ estar hstar B = (estar : ℤ) * σ.w B
  /-- (S6a) at the regrade, in the post-V5 fixed-point coset form (weights read
  against wVPrev = σ.w, i.e. over `childWeightSet σ σ.Φ`); filled by V6(a) —
  regrade scalars are PRESERVED, so the parent's coset bases transport. -/
  hS6a : ∀ ν : ℤ, ν ∈ childWeightSet σ σ.Φ →
      ∃ b : (↥σ.K)ˣ, ∀ c : (↥σ.K)ˣ, ((c : ↥σ.K) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ σ.w B = ν ∧
          D.Rv B = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) *
            LaurentPolynomial.T (- tstar * ν)

end LeanUrat.HC1
----- END FILE: lean/LeanUrat/HC1/DefsV.lean -----

----- FILE: lean/LeanUrat/HC1/V1_readWPack.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.Moves.L4_TRANSi_R3
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.L0_FactA_exists

/-!
# HC1.V1_readWPack — the read functional's laws at the same key (blueprint §10, V1)

V′-KERNEL unit (blueprint §10.1): for σ cored, under `ReadPair` hypotheses, the
read functional `childW σ σ.Φ e★ h★` has the slot-min/attained-min pack (the S2
instance at Φhat := σ.Φ — the signature admits it verbatim), hwmul, hwult, and
the **Q-ASCENT** lemma: for parent coefficients with monic division
`B·B″ = Q·σ.Φ + R_dev`, the Q-slot's (†)-value exceeds the R_dev-slot's by
`h★ − e★·σ.h > 0` (ReadPair's steepness).

moves_ref: D.7(i) (MOVES 2331–2337) at the same-key instance; D.4.
deps: S2_childW, σ's hRmul/hwmul/hwult/hK1. difficulty: medium.
P-phase PROVED (2026-07-28): slot-min pack = S2 verbatim; hwult from slotwise
development linearity + σ.hwult; hwmul via the lift-free cores `TRANSi_ge_core` /
`TRANSiii_le_core` (extracted from L4_TRANSi/iii) fed the SAME-KEY DIV lemma
`sameKeyDIV`; Q-ascent = `sameKeyDIV` (key minimality via `R(σ.Φ)=z^s` a unit +
σ.e ∣ σ.h ⇒ σ.e=1 ⇒ σ.t=0 ⇒ residual-exponent clash) + σ.hK1 slot-1 bound.
Footprint: Lean core `{propext, Classical.choice, Quot.sound}`; zero `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

section V1Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Two `C·T` monomials with a nonzero leading scalar are equal only at equal exponents. -/
private lemma monomial_exp_eq {K : Type*} [Field K] {a b : K} {k1 k2 : ℤ} (ha : a ≠ 0)
    (h : LaurentPolynomial.C a * LaurentPolynomial.T k1
        = LaurentPolynomial.C b * LaurentPolynomial.T k2) : k1 = k2 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : (Finsupp.single k1 a : ℤ →₀ K) = Finsupp.single k2 b := h
  by_contra hne
  have hc := DFunLike.congr_fun h' k1
  rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (fun hk => hne hk.symm)] at hc
  exact ha hc

/-- **The SAME-KEY DIV lemma** (V1's Q-ascent core, the D.6 argument at `Φ̂ = σ.Φ`): for
`B, B'' ∈ C_{σ.Φ}∖0` with monic division `B·B'' = (B·B'')%ₘσ.Φ + σ.Φ·((B·B'')/ₘσ.Φ)`, the
remainder is nonzero with weight exactly `σ.w B + σ.w B''`, and the quotient slot lies weakly
above it by `σ.h`.  Ruling out the cancellation branch uses only `R(σ.Φ) = z^s` being a UNIT
(no descend-polynomial root): a `w`-jump forces `σ.e ∣ σ.h`, hence `σ.e = 1`, `σ.t = 0`,
`σ.s = 1`, contradicting the residual exponent match. -/
private lemma sameKeyDIV (σ : Stage p F) (B B'' : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hB'' : B'' ≠ 0) (hBc : inC σ.Φ B) (hB''c : inC σ.Φ B'') :
    (((B * B'') %ₘ σ.Φ) ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'') ∧
      (((B * B'') /ₘ σ.Φ) ≠ 0 →
        σ.w ((B * B'') %ₘ σ.Φ) ≤ σ.w ((B * B'') /ₘ σ.Φ) + (σ.h : ℤ)) := by
  classical
  set Rdev := (B * B'') %ₘ σ.Φ with hRdevdef
  set Q := (B * B'') /ₘ σ.Φ with hQdef
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hBBne : B * B'' ≠ 0 := mul_ne_zero hB hB''
  have hsplit : B * B'' = Rdev + σ.Φ * Q := (Polynomial.modByMonic_add_div (B * B'') σ.Φ).symm
  have hwBB : σ.w (B * B'') = σ.w B + σ.w B'' := σ.hwmul B B'' hB hB''
  -- Rdev ∈ C
  have hRc : Rdev.degree < σ.Φ.degree := Polynomial.degree_modByMonic_lt _ σ.hmonic
  -- Q ∈ C (degree bookkeeping: deg(B·B'') < 2·deg σ.Φ)
  have hBBnat : (B * B'').natDegree < 2 * σ.Φ.natDegree := by
    rw [Polynomial.natDegree_mul hB hB'']
    have h1 : B.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hB hBc
    have h2 : B''.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hB'' hB''c
    omega
  have hQnat : Q.natDegree < σ.Φ.natDegree := by
    rw [hQdef, Polynomial.natDegree_divByMonic (B * B'') σ.hmonic]
    have := σ.hdeg; omega
  have hQc : Q.degree < σ.Φ.degree := by
    by_cases hQ0 : Q = 0
    · rw [hQ0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun hb => hΦne (Polynomial.degree_eq_bot.mp hb))
    · rw [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_eq_natDegree hΦne]
      exact_mod_cast hQnat
  -- the 2-slot Φ-development and Lemma K1
  set Bseq : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then Rdev else if j = 1 then Q else 0
    with hBseqdef
  have hB0 : Bseq 0 = Rdev := by simp [hBseqdef]
  have hB1 : Bseq 1 = Q := by simp [hBseqdef]
  have hBj2 : ∀ j, 2 ≤ j → Bseq j = 0 := by
    intro j hj
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    simp only [hBseqdef, if_neg hj0, if_neg hj1]
  have hdev : IsDevelopment σ.Φ (B * B'') Bseq 2 := by
    refine ⟨?_, hBj2, ?_⟩
    · intro j
      by_cases hj0 : j = 0
      · rw [hj0, hB0]; exact hRc
      · by_cases hj1 : j = 1
        · rw [hj1, hB1]; exact hQc
        · rw [hBj2 j (by omega), Polynomial.degree_zero]
          exact bot_lt_iff_ne_bot.mpr (fun hb => hΦne (Polynomial.degree_eq_bot.mp hb))
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hB0, hB1,
        pow_zero, pow_one, mul_one, zero_add, hsplit, mul_comm σ.Φ Q]
  have hK1 := σ.hK1 (B * B'') Bseq 2 hBBne hdev
  rw [σ.hwΦ] at hK1
  have hK1lb : ∀ j, j < 2 → Bseq j ≠ 0 →
      σ.w (B * B'') ≤ σ.w (Bseq j) + (j : ℤ) * (σ.h : ℤ) := hK1.1
  -- the residual-cancellation absurdity used to rule out a w-jump
  have hAbsurd : Q ≠ 0 → σ.R (B * B'') = σ.R (Q * σ.Φ) →
      σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) → False := by
    intro hQne hReq hweq
    have hsB := σ.hStretch B hB hBc
    have hsB'' := σ.hStretch B'' hB'' hB''c
    have hsQ := σ.hStretch Q hQne hQc
    have hEq : (σ.h : ℤ) = (σ.e : ℤ) * (σ.wPrev B + σ.wPrev B'' - σ.wPrev Q) := by
      have hw := hweq
      rw [hsB, hsB'', hsQ] at hw
      linear_combination -hw
    have hdvd : (σ.e : ℤ) ∣ (σ.h : ℤ) := ⟨σ.wPrev B + σ.wPrev B'' - σ.wPrev Q, hEq⟩
    have hediv : σ.e ∣ σ.h := Int.natCast_dvd_natCast.mp hdvd
    have he1 : σ.e = 1 := (Nat.gcd_eq_left hediv).symm.trans σ.hcop
    have ht0 : σ.t = 0 := σ.he1t he1
    have hs1 : σ.s = 1 := by
      have hb := σ.hbez
      rw [show (σ.e : ℤ) = 1 by exact_mod_cast he1, ht0] at hb
      linarith [hb]
    obtain ⟨cB, hcB⟩ := σ.hS5 B hB hBc
    obtain ⟨cB'', hcB''⟩ := σ.hS5 B'' hB'' hB''c
    obtain ⟨cQ, hcQ⟩ := σ.hS5 Q hQne hQc
    have hForm1 : σ.R (B * B'')
        = LaurentPolynomial.C (((cB * cB'' : (↥σ.K)ˣ)) : ↥σ.K)
          * LaurentPolynomial.T ((- σ.t * σ.wPrev B) + (- σ.t * σ.wPrev B'')) := by
      rw [σ.hRmul B B'' hB hB'', hcB, hcB'', Units.val_mul, map_mul, LaurentPolynomial.T_add]
      ring
    have hForm2 : σ.R (Q * σ.Φ)
        = LaurentPolynomial.C ((cQ : ↥σ.K))
          * LaurentPolynomial.T ((- σ.t * σ.wPrev Q) + σ.s) := by
      rw [σ.hRmul Q σ.Φ hQne hΦne, hcQ, σ.hRΦ, LaurentPolynomial.T_add]
      ring
    have hMon : LaurentPolynomial.C (((cB * cB'' : (↥σ.K)ˣ)) : ↥σ.K)
          * LaurentPolynomial.T ((- σ.t * σ.wPrev B) + (- σ.t * σ.wPrev B''))
        = LaurentPolynomial.C ((cQ : ↥σ.K))
          * LaurentPolynomial.T ((- σ.t * σ.wPrev Q) + σ.s) := by
      rw [← hForm1, hReq, hForm2]
    have hexp := monomial_exp_eq (Units.ne_zero (cB * cB'')) hMon
    rw [ht0, hs1] at hexp
    simp only [neg_zero, zero_mul, add_zero, zero_add] at hexp
    exact zero_ne_one hexp
  -- Rdev ≠ 0
  have hRdevne : Rdev ≠ 0 := by
    intro h0
    have hBBQ : B * B'' = σ.Φ * Q := by rw [hsplit, h0, zero_add]
    have hQne : Q ≠ 0 := by
      intro hq; rw [hBBQ, hq, mul_zero] at hBBne; exact hBBne rfl
    have hReq : σ.R (B * B'') = σ.R (Q * σ.Φ) := by rw [hBBQ, mul_comm σ.Φ Q]
    have hweq : σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) := by
      rw [← hwBB, hBBQ, σ.hwmul σ.Φ Q hΦne hQne, σ.hwΦ]; ring
    exact hAbsurd hQne hReq hweq
  -- σ.w Rdev = σ.w (B·B'')  (slot 0 is the minimizer)
  have hle : σ.w (B * B'') ≤ σ.w Rdev := by
    have hh := hK1lb 0 (by omega) (by rw [hB0]; exact hRdevne)
    simpa [hB0] using hh
  have hge : σ.w Rdev ≤ σ.w (B * B'') := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨jm, hjmlt, hjmnz0, hjmeq0⟩ := hK1.2
    have hjmnz : Bseq jm ≠ 0 := hjmnz0
    have hjmeq : σ.w (B * B'') = σ.w (Bseq jm) + (jm : ℤ) * (σ.h : ℤ) := hjmeq0
    have hjm1 : jm = 1 := by
      rcases (by omega : jm = 0 ∨ jm = 1) with h | h
      · exfalso
        rw [h, hB0] at hjmeq
        simp only [Nat.cast_zero, zero_mul, add_zero] at hjmeq
        rw [hjmeq] at hlt; exact lt_irrefl _ hlt
      · exact h
    rw [hjm1, hB1] at hjmnz hjmeq
    have hQne : Q ≠ 0 := hjmnz
    have hjmeq' : σ.w (B * B'') = σ.w Q + (σ.h : ℤ) := by rw [hjmeq]; push_cast; ring
    have hwQΦ : σ.w (σ.Φ * Q) = σ.w Q + (σ.h : ℤ) := by
      rw [σ.hwmul σ.Φ Q hΦne hQne, σ.hwΦ]; ring
    have hltΦ : σ.w (σ.Φ * Q) < σ.w Rdev := by rw [hwQΦ, ← hjmeq']; exact hlt
    have hReq : σ.R (B * B'') = σ.R (Q * σ.Φ) := by
      rw [hsplit, add_comm Rdev (σ.Φ * Q),
        σ.hRlt (σ.Φ * Q) Rdev (mul_ne_zero hΦne hQne) hRdevne
          (by rw [add_comm (σ.Φ * Q) Rdev, ← hsplit]; exact hBBne) hltΦ, mul_comm σ.Φ Q]
    have hweq : σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) := by rw [← hwBB]; exact hjmeq'
    exact hAbsurd hQne hReq hweq
  have hwRdev : σ.w Rdev = σ.w B + σ.w B'' := by rw [le_antisymm hge hle, hwBB]
  refine ⟨⟨hRdevne, hwRdev⟩, ?_⟩
  intro hQne
  have hb := hK1lb 1 (by omega) (by rw [hB1]; exact hQne)
  rw [hB1] at hb
  rw [hwRdev, ← hwBB]
  simpa using hb

end V1Helpers

/-- Unit V1: the read functional's laws at the same key — the slot-min pack (S2 at
Φhat := σ.Φ), multiplicativity, the ultrametric law, and Q-ascent with the displayed
gap `h★ − e★·σ.h` (strictly positive by `ReadPair`). -/
theorem V1_readWPack {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    ((∀ f : Polynomial ℤ_[p], f ≠ 0 →
        ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment σ.Φ f B N ∧
          SlotMinAttained (childW σ σ.Φ estar hstar f) N
            (fun j => (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ))
            (fun j => B j ≠ 0)) ∧
      IsSlotMinWeight (childW σ σ.Φ estar hstar) σ.Φ estar hstar σ.w) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ estar hstar (f * g)
          = childW σ σ.Φ estar hstar f + childW σ σ.Φ estar hstar g) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
        min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
          ≤ childW σ σ.Φ estar hstar (f + g)) ∧
    (∀ B B'' : Polynomial ℤ_[p], B ≠ 0 → B'' ≠ 0 → inC σ.Φ B → inC σ.Φ B'' →
        (((B * B'') %ₘ σ.Φ) ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'') ∧
        (((B * B'') /ₘ σ.Φ) ≠ 0 →
          (estar : ℤ) * σ.w ((B * B'') %ₘ σ.Φ)
              + ((hstar : ℤ) - (estar : ℤ) * (σ.h : ℤ))
            ≤ (estar : ℤ) * σ.w ((B * B'') /ₘ σ.Φ) + (hstar : ℤ))) := by
  classical
  -- conjunct 1: the S2 slot-min pack at Φhat := σ.Φ (signature admits it verbatim)
  have hpack := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  have hSMW : IsSlotMinWeight (childW σ σ.Φ estar hstar) σ.Φ estar hstar σ.w := hpack.2
  -- (I-aug) at the same key, from ReadPair's steepness `estar·σ.h < hstar`
  have hIAug : IAug σ σ.Φ estar hstar := by
    show (hstar : ℤ) > (estar : ℤ) * σ.w σ.Φ
    rw [σ.hwΦ]; exact hrp.2.2.2.2.2
  -- the same-key DIV fact in the core's shape
  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
      B.degree < σ.Φ.degree → B''.degree < σ.Φ.degree →
      (B * B'') %ₘ σ.Φ ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'' :=
    fun B B'' hB hB'' hBd hB''d => (sameKeyDIV σ B B'' hB hB'' hBd hB''d).1
  refine ⟨hpack, ?_, ?_, ?_⟩
  · -- hwmul: multiplicativity of the read functional (same-key MacLane augmentation)
    intro f g hf hg
    exact le_antisymm
      (TRANSiii_le_core σ σ.Φ σ.hmonic σ.hdeg estar hstar (childW σ σ.Φ estar hstar) hSMW hIAug
        hDIVw f g hf hg (mul_ne_zero hf hg))
      (TRANSi_ge_core σ σ.Φ σ.hmonic σ.hdeg estar hstar (childW σ σ.Φ estar hstar) hSMW hIAug
        hDIVw f g hf hg (mul_ne_zero hf hg))
  · -- hwult: the ultrametric law (slotwise linearity of the Φ-development + σ.hwult)
    intro f g hf hg hfg
    obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
    obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g
    have hsub_f : Finset.range Nf ⊆ Finset.range (max Nf Ng) :=
      fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left Nf Ng))
    have hsub_g : Finset.range Ng ⊆ Finset.range (max Nf Ng) :=
      fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right Nf Ng))
    have hfsum : f = ∑ j ∈ Finset.range (max Nf Ng), Bf j * σ.Φ ^ j :=
      hdevf.2.2.trans (Finset.sum_subset hsub_f
        (fun j _ hj => by rw [hdevf.2.1 j (not_lt.mp (Finset.mem_range.not.mp hj)), zero_mul]))
    have hgsum : g = ∑ j ∈ Finset.range (max Nf Ng), Bg j * σ.Φ ^ j :=
      hdevg.2.2.trans (Finset.sum_subset hsub_g
        (fun j _ hj => by rw [hdevg.2.1 j (not_lt.mp (Finset.mem_range.not.mp hj)), zero_mul]))
    have hdevs : IsDevelopment σ.Φ (f + g) (fun j => Bf j + Bg j) (max Nf Ng) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdevf.1 j) (hdevg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdevf.2.1 j (le_trans (le_max_left Nf Ng) hj),
          hdevg.2.1 j (le_trans (le_max_right Nf Ng) hj), add_zero]
      · rw [hfsum, hgsum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsm := hSMW (f + g) (fun j => Bf j + Bg j) (max Nf Ng) hfg hdevs
    have hlbf := (hSMW f Bf Nf hf hdevf).1
    have hlbg := (hSMW g Bg Ng hg hdevg).1
    obtain ⟨-, jm, hjmN, hjmnz0, hjmeq0⟩ := hsm
    have hjmnz : Bf jm + Bg jm ≠ 0 := hjmnz0
    have hjmeq : childW σ σ.Φ estar hstar (f + g)
        = (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := hjmeq0
    rw [hjmeq]
    have hestar : (0 : ℤ) ≤ (estar : ℤ) := Int.natCast_nonneg estar
    by_cases hbf : Bf jm = 0
    · have hbg : Bg jm ≠ 0 := fun h => hjmnz (by rw [hbf, h, add_zero])
      have hjmg : jm < Ng := by by_contra hc; exact hbg (hdevg.2.1 jm (not_lt.mp hc))
      have hgle := hlbg jm hjmg hbg
      rw [hbf, zero_add]
      exact le_trans (min_le_right _ _) hgle
    · by_cases hbg : Bg jm = 0
      · have hjmf : jm < Nf := by by_contra hc; exact hbf (hdevf.2.1 jm (not_lt.mp hc))
        have hfle := hlbf jm hjmf hbf
        rw [hbg, add_zero]
        exact le_trans (min_le_left _ _) hfle
      · have hjmf : jm < Nf := by by_contra hc; exact hbf (hdevf.2.1 jm (not_lt.mp hc))
        have hjmg : jm < Ng := by by_contra hc; exact hbg (hdevg.2.1 jm (not_lt.mp hc))
        have h1 := hlbf jm hjmf hbf
        have h2 := hlbg jm hjmg hbg
        have hult := σ.hwult (Bf jm) (Bg jm) hbf hbg hjmnz
        rcases le_total (σ.w (Bf jm)) (σ.w (Bg jm)) with hle | hle
        · have hw : σ.w (Bf jm) ≤ σ.w (Bf jm + Bg jm) := by
            rw [min_eq_left hle] at hult; exact hult
          have hmul := mul_le_mul_of_nonneg_left hw hestar
          calc min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
                ≤ childW σ σ.Φ estar hstar f := min_le_left _ _
            _ ≤ (estar : ℤ) * σ.w (Bf jm) + (jm : ℤ) * (hstar : ℤ) := h1
            _ ≤ (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := by linarith
        · have hw : σ.w (Bg jm) ≤ σ.w (Bf jm + Bg jm) := by
            rw [min_eq_right hle] at hult; exact hult
          have hmul := mul_le_mul_of_nonneg_left hw hestar
          calc min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
                ≤ childW σ σ.Φ estar hstar g := min_le_right _ _
            _ ≤ (estar : ℤ) * σ.w (Bg jm) + (jm : ℤ) * (hstar : ℤ) := h2
            _ ≤ (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := by linarith
  · -- Q-ascent: part (i) is the DIV fact; part (ii) is its slot-1 bound, scaled by estar
    intro B B'' hB hB'' hBc hB''c
    have hd := sameKeyDIV σ B B'' hB hB'' hBc hB''c
    refine ⟨hd.1, ?_⟩
    intro hQne
    have hbound := hd.2 hQne
    have hmul := mul_le_mul_of_nonneg_left hbound (Int.natCast_nonneg estar)
    rw [mul_add] at hmul
    linarith [hmul]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V1_readWPack
----- END FILE: lean/LeanUrat/HC1/V1_readWPack.lean -----

----- FILE: lean/LeanUrat/HC1/V2_readResidual.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V1_readWPack
import LeanUrat.Moves.L3_K1

/-!
# HC1.V2_readResidual — the lawful regrade carrier exists (blueprint §10, V2)

V′-KERNEL unit (blueprint §10.1) — **THE V′ FRAME CHANGE UNIT**: a lawful regrade
carrier exists (+ w_strict, the S9w-(ii) mirror).

Construction (P-phase route, recorded): RV per (†) — scalars from σ.hS5's monomial
digits (parent coefficients only, so every slot digit IS a monomial), positions
`(j − t★·wV f)/e★ = j·s★ − t★·σ.w(B_j)`, injective in j across minimizing slots
(elementary: the map `j ↦ (j − t★γ)/e★` on the tie set), so RV(f) ≠ 0.  hRmul:
V1's Q-ascent + σ.hRmul on slot products + the position additivity (exact,
carry-free in the total coordinate — the §10 DEMOTION NOTE: the carry cocycle is
INVISIBLE in the evaluated V′ coordinate; the proved D-layer certifies the
alignment, it is not load-bearing here).

moves_ref: D.6/D.7(i)–(iii) read at the level-free stage; D.5's "no coset-splitting"
absence note (MOVES 2291–2292). deps: V0, V1, the L3_K1 pattern.
difficulty: medium-hard (the S9w mirror, EASIER: no field extension).
E-phase: statements per §10.1, `sorry` bodies.  `V2_readFrame` packages the frame
(assembled from V1 + the carrier + V6(a)'s hS6a fill in P-phase).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit V2: a lawful regrade carrier exists, plus the wV-only strict law (the
S9w-(ii) mirror at the regrade). -/
theorem V2_readResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    (∃ D : ReadResData σ estar hstar sstar tstar, ReadResLaws D) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
        childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f) := by
  sorry

/-- Unit V2 (frame packaging): the full `ReadFrame` is inhabited — the lawful
carrier (above) + V1's wV laws + V6(a)'s hS6a fill. -/
theorem V2_readFrame {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    Nonempty (ReadFrame σ estar hstar sstar tstar) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V2_readResidual
#print axioms LeanUrat.HC1.V2_readFrame
----- END FILE: lean/LeanUrat/HC1/V2_readResidual.lean -----

----- FILE: lean/LeanUrat/HC1/V3_readLift.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V2_readResidual
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_GRg

/-!
# HC1.V3_readLift — the recorded lift is the regrade's standard lift (blueprint §10, V3)

V′-KERNEL unit (blueprint §10.1; §10 Key Finding 1): the recorded lift
`IsReadLift σ ψ g e★ h★ Φ̂` is (†)-EQUAL-WEIGHT — its weights
`σ.w(t_k) = h★·(g−k)` give `e★·σ.w(t_k) + (e★k)·h★ = e★·h★·g` for every present
slot and for the leading slot, EXACTLY D.5's "EQUAL WEIGHTS" display (MOVES
2268–2269) transposed to wV — hence `IsReadLift` IS the standard-lift shape OF
THE REGRADED FRAME (wVPrev := σ.w, index (e★, h★)), and the D.5 residual
computation re-runs verbatim:

* the lift's read weight `wV(Φ̂) = e★·h★·g`;
* the D.5 residual display `RV(Φ̂) = T(m̂★)·(ψ as Laurent)`, `m̂★ = −t★·h★·g`
  (via the distinct-exponents sum `k − t★·h★·g`, MOVES 2270–2276);
* K1(Φ̂/wV): `wV(f) = min_m (wV(B_m) + m·e★h★g)` with attainment.

moves_ref: D.5 VERBATIM (MOVES 2253–2289 — the whole display re-runs at the
ReadFrame; the Lean pattern is L3_liftResidual + L3_K1).
deps: V2, the L3_digPrime_nonzero-analog at the same key (width < g: D.3(d)).
difficulty: medium.  E-phase: statement per §10.1, `sorry` body.

## P-phase proof structure (2026-07-28; the D.5 mirror at the ReadFrame)

The regrade is NOT a `Stage` (§10 Finding 3: `hS6b`/`hvalgrp` are unsatisfiable
at regrades for `σ.e > 1`), so `L3_liftResidual`/`L3_K1` cannot be cited — they
are MIRRORED over the partial pack `(wV, RV) = (childW σ σ.Φ e★ h★, V.D.Rv)`:

* `v3_decomp_sum` — the distinct-position monomial decomposition engine (the
  `L2_slotDecomp` `decomp_sum`, transposed; consumes `hRadd`/`hWjump`/`hRneg`).
* `v3_lift_core` — C2+C3 in ONE decomp_sum application: all lift slots are tied
  at weight `e★h★g` with residual monomials at the DISTINCT positions `D + k`,
  `D = −t★h★g` (Bézout `e★s★ + h★t★ = 1`), so `wV(Φ̂) = e★h★g` and
  `RV(Φ̂) = T(D)·ψ` in one stroke; the (S5)-preserved scalar of each slot is
  identified with `ψ_k` by matching `σ.R` monomials (hS5 ∧ IsReadLift).
* `v3_devForm` — RV of ANY `Φ`-development is the sum of its wV-minimizing slot
  residuals (V.hK1 + decomp_sum + hRlt); hence `v3_width`: on `Ĉ∖0` the RV
  support has width < g (`e★·pos = j − t★·wV`, slots `j < e★g`), hence
  `v3_psiNotDvd`: `ψ ∤ RV(B)` (the L3_digPrime_nonzero-analog at the same key).
* `v3_key_no_cancel`/`v3_minsum_facts` — the L3_K1 no-cancellation engine at
  `(Φ̂, wV, RV)` (simplified: the pack carries `hRneg`/`hWjump` outright, so no
  `R(−1)` bookkeeping); C4 assembles exactly as L3_K1's main body.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

section V3Kernel

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### Generic helpers (no stage data) -/

/-- Coefficient extraction: in a distinct-position sum of monomials, the coefficient at
`pos m` is exactly `c m` (mirror of the L2_slotDecomp helper). -/
private lemma v3_coeff_extract {ι : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset ι) (pos : ι → ℤ) (c : ι → A) (m : ι) (hm : m ∈ S)
    (hinj : ∀ j ∈ S, pos j = pos m → j = m) :
    (∑ j ∈ S, Finsupp.single (pos j) (c j)) (pos m) = c m := by
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single m
    (fun j hj hjm => by rw [Finsupp.single_apply, if_neg (fun h => hjm (hinj j hj h))])
    (fun h => absurd hm h)]
  rw [Finsupp.single_apply, if_pos rfl]

/-- **[dep `L0.GRf`, inlined verbatim]** In `K[z^{±1}]` with `ψ` irreducible, `ψ ≠ X`, a finite
sum `Σ_{j∈S} c_j·ψ^j` with each `c_j ≠ 0`, `ψ ∤ c_j` is nonzero. -/
private theorem v3_GRf {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
    (hψz : ψ ≠ Polynomial.X) (c : ℕ → LaurentPolynomial K) (S : Finset ℕ) (hne : S.Nonempty)
    (hc : ∀ j ∈ S, c j ≠ 0 ∧ ¬ (Polynomial.toLaurent ψ ∣ c j)) :
    (∑ j ∈ S, c j * (Polynomial.toLaurent ψ) ^ j) ≠ 0 := by
  set P := Polynomial.toLaurent ψ with hP
  set m := S.min' hne with hm
  have hmmem : m ∈ S := S.min'_mem hne
  have hmle : ∀ j ∈ S, m ≤ j := fun j hj => S.min'_le j hj
  have hψ0 : ψ ≠ 0 := hψ.ne_zero
  have hP0 : P ≠ 0 := by
    rw [hP]
    intro h
    exact hψ0 (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  have hfact : (∑ j ∈ S, c j * P ^ j) = P ^ m * (∑ j ∈ S, c j * P ^ (j - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hpow : P ^ j = P ^ m * P ^ (j - m) := by
      rw [← pow_add]; congr 1; have := hmle j hj; omega
    rw [hpow]; ring
  have hrest : P ∣ (∑ j ∈ S.erase m, c j * P ^ (j - m)) := by
    refine Finset.dvd_sum (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    obtain ⟨hjm, hjS⟩ := hj
    have hlt : m < j := lt_of_le_of_ne (hmle j hjS) (Ne.symm hjm)
    exact (dvd_pow_self P (by omega : j - m ≠ 0)).mul_left (c j)
  have hsplit : (∑ j ∈ S, c j * P ^ (j - m))
      = c m * P ^ (m - m) + (∑ j ∈ S.erase m, c j * P ^ (j - m)) :=
    (Finset.add_sum_erase S (fun j => c j * P ^ (j - m)) hmmem).symm
  have hcofdvd : ¬ P ∣ (∑ j ∈ S, c j * P ^ (j - m)) := by
    intro hdvd
    rw [hsplit] at hdvd
    have hdvd2 : P ∣ c m * P ^ (m - m) := (dvd_add_left hrest).mp hdvd
    rw [Nat.sub_self, pow_zero, mul_one] at hdvd2
    exact (hc m hmmem).2 hdvd2
  have hcof0 : (∑ j ∈ S, c j * P ^ (j - m)) ≠ 0 := fun h => hcofdvd (h ▸ dvd_zero P)
  rw [hfact]
  exact mul_ne_zero (pow_ne_zero m hP0) hcof0

/-- **Degree domination of the top slot** (inlined verbatim from `L2_widthBound`'s
`dev_slot_bound`): in a `Φ`-development of `f` with `deg f < M·deg Φ`, every slot `j ≥ M`
is zero. -/
private lemma v3_dev_slot_bound (Φ : Polynomial ℤ_[p]) (hΦ : Φ.Monic)
    (f : Polynomial ℤ_[p]) (Bd : ℕ → Polynomial ℤ_[p]) (N M : ℕ)
    (hdev : IsDevelopment Φ f Bd N) (hfdeg : f.natDegree < M * Φ.natDegree) :
    ∀ j, M ≤ j → Bd j = 0 := by
  classical
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  intro j hMj
  by_contra hBj
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  set S : Finset ℕ := (Finset.range N).filter (fun i => Bd i ≠ 0) with hSdef
  have hSmem : ∀ i, i ∈ S ↔ i < N ∧ Bd i ≠ 0 := by
    intro i; rw [hSdef, Finset.mem_filter, Finset.mem_range]
  have hjS : j ∈ S := by
    refine (hSmem j).mpr ⟨?_, hBj⟩
    by_contra hjN
    push_neg at hjN
    exact hBj (hzero j hjN)
  have hSne : S.Nonempty := ⟨j, hjS⟩
  have hJS : S.max' hSne ∈ S := S.max'_mem hSne
  set J := S.max' hSne with hJdef
  have hBJ : Bd J ≠ 0 := ((hSmem J).mp hJS).2
  have htJne : Bd J * Φ ^ J ≠ 0 := mul_ne_zero hBJ (pow_ne_zero J hΦ0)
  have hjJ : j ≤ J := S.le_max' j hjS
  have hsum2 : f = Bd J * Φ ^ J + ∑ i ∈ S.erase J, Bd i * Φ ^ i := by
    have h1 : ∑ i ∈ S, Bd i * Φ ^ i = ∑ i ∈ Finset.range N, Bd i * Φ ^ i := by
      rw [hSdef]
      exact Finset.sum_filter_of_ne (fun x _ hne hBx => hne (by rw [hBx, zero_mul]))
    rw [hsum, ← h1, ← Finset.add_sum_erase S _ hJS]
  have hdegJ : (Bd J * Φ ^ J).natDegree = (Bd J).natDegree + J * Φ.natDegree := by
    rw [Polynomial.natDegree_mul hBJ (pow_ne_zero J hΦ0), Polynomial.natDegree_pow]
  have hrest : (∑ i ∈ S.erase J, Bd i * Φ ^ i).degree < (Bd J * Φ ^ J).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff ?_).mpr ?_)
    · rw [Polynomial.degree_eq_natDegree htJne]
      exact WithBot.bot_lt_coe _
    · intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hiJ : i ≠ J := Finset.ne_of_mem_erase hi
      have hBi : Bd i ≠ 0 := ((hSmem i).mp hiS).2
      have htine : Bd i * Φ ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦ0)
      have hiltJ : i < J := lt_of_le_of_ne (S.le_max' i hiS) hiJ
      rw [Polynomial.degree_eq_natDegree htine, Polynomial.degree_eq_natDegree htJne]
      have hBideg : (Bd i).natDegree < Φ.natDegree :=
        Polynomial.natDegree_lt_natDegree hBi (hdeg i)
      have hnat : (Bd i * Φ ^ i).natDegree < (Bd J * Φ ^ J).natDegree := by
        rw [hdegJ, Polynomial.natDegree_mul hBi (pow_ne_zero i hΦ0), Polynomial.natDegree_pow]
        calc (Bd i).natDegree + i * Φ.natDegree
            < Φ.natDegree + i * Φ.natDegree := Nat.add_lt_add_right hBideg _
          _ = (i + 1) * Φ.natDegree := by ring
          _ ≤ J * Φ.natDegree := mul_le_mul_right' (by omega) _
          _ ≤ (Bd J).natDegree + J * Φ.natDegree := Nat.le_add_left _ _
      exact_mod_cast hnat
  have hdegf : f.degree = (Bd J * Φ ^ J).degree := by
    rw [hsum2]
    exact Polynomial.degree_add_eq_left_of_degree_lt hrest
  have hnatf : f.natDegree = (Bd J).natDegree + J * Φ.natDegree := by
    rw [← hdegJ]
    exact Polynomial.natDegree_eq_of_degree_eq hdegf
  have hle : M * Φ.natDegree ≤ f.natDegree := by
    rw [hnatf]
    calc M * Φ.natDegree ≤ J * Φ.natDegree := mul_le_mul_right' (le_trans hMj hjJ) _
      _ ≤ (Bd J).natDegree + J * Φ.natDegree := Nat.le_add_left _ _
  exact absurd hfdeg (not_lt.mpr hle)

/-! ### The (wV, RV) basics -/

variable {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}

/-- `wV 1 = 0`. -/
private lemma v3_wv_one (V : ReadFrame σ estar hstar sstar tstar) :
    childW σ σ.Φ estar hstar 1 = 0 := by
  have h := V.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `wV(−f) = wV f`. -/
private lemma v3_wv_neg (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) : childW σ σ.Φ estar hstar (-f) = childW σ σ.Φ estar hstar f := by
  have hm1 : childW σ σ.Φ estar hstar (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := V.hwmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, v3_wv_one V] at h
    omega
  have h := V.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  rw [h, hm1, zero_add]

/-- `wV(f^n) = n·wV f`. -/
private lemma v3_wv_pow (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) (n : ℕ) :
    childW σ σ.Φ estar hstar (f ^ n) = (n : ℤ) * childW σ σ.Φ estar hstar f := by
  induction n with
  | zero => rw [pow_zero, v3_wv_one V, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, V.hwmul _ _ (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-- `RV 1 = 1`. -/
private lemma v3_rv_one (V : ReadFrame σ estar hstar sstar tstar) :
    V.D.Rv (1 : Polynomial ℤ_[p]) = 1 := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have h := hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel₀ (hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm

/-- `RV(f^n) = RV(f)^n`. -/
private lemma v3_rv_pow (V : ReadFrame σ estar hstar sstar tstar) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) (n : ℕ) : V.D.Rv (f ^ n) = (V.D.Rv f) ^ n := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact v3_rv_one V
  | succ k ih =>
    rw [pow_succ, hRmul _ _ (pow_ne_zero k hf) hf, ih, ← pow_succ]

/-- Ultrametric finite-sum lower bound for `wV`. -/
private lemma v3_wv_sum_ge (V : ReadFrame σ estar hstar sstar tstar)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ childW σ σ.Φ estar hstar (a j))
    (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ childW σ σ.Φ estar hstar (∑ j ∈ S, a j) := by
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro hm hsum
    simp only [Finset.sum_empty] at hsum
    exact absurd rfl hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ childW σ σ.Φ estar hstar (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ childW σ σ.Φ estar hstar (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        have hult := V.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum
        calc m ≤ min (childW σ σ.Φ estar hstar (a i)) (childW σ σ.Φ estar hstar (∑ j ∈ T, a j)) :=
              le_min h1 h2
          _ ≤ childW σ σ.Φ estar hstar (a i + ∑ j ∈ T, a j) := hult

/-- **Slot monomial** (the S5-shape at the regrade): for `B ∈ C_Φ∖0`,
`RV(B·Φ^j) = single(−t★·σ.w(B) + j·s★, c)` with `c` a unit. -/
private lemma v3_slot_mono (V : ReadFrame σ estar hstar sstar tstar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hC : inC σ.Φ B) (j : ℕ) :
    ∃ c : (↥σ.K)ˣ,
      V.D.Rv (B * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w B + (j : ℤ) * sstar) ((c : ↥σ.K)) := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨c, hcR, hcV⟩ := V.D.hS5 B hB hC
  refine ⟨c, ?_⟩
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  rw [hRmul B (σ.Φ ^ j) hB (pow_ne_zero j hΦ0), v3_rv_pow V σ.Φ hΦ0 j, V.D.hRPhi, hcV,
    LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-- **Bézout position identity** at a wV-minimizing slot: `e★·pos = j − t★·γ`. -/
private lemma v3_epos (V : ReadFrame σ estar hstar sstar tstar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hC : inC σ.Φ B) (j : ℕ) (γ : ℤ)
    (hw : childW σ σ.Φ estar hstar (B * σ.Φ ^ j) = γ) :
    (estar : ℤ) * (- tstar * σ.w B + (j : ℤ) * sstar) = (j : ℤ) - tstar * γ := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hwm := V.hwmul B (σ.Φ ^ j) hB (pow_ne_zero j hΦ0)
  have hwp : childW σ σ.Φ estar hstar (σ.Φ ^ j) = (j : ℤ) * (hstar : ℤ) := by
    rw [v3_wv_pow V σ.Φ hΦ0 j, V.hwPhi]
  have hst := V.hStretch B hB hC
  have hmin : γ = (estar : ℤ) * σ.w B + (j : ℤ) * (hstar : ℤ) := by
    rw [← hw, hwm, hwp, hst]
  linear_combination tstar * hmin + (j : ℤ) * hbez

/-- **The distinct-position decomposition engine** (mirror of `L2_slotDecomp`'s
`decomp_sum` at the regrade pack): a finite sum of nonzero equal-`wV`-weight slots whose
`RV`-residuals are distinct-position monomials has `RV` additive across it, weight `γ`,
and is nonzero. -/
private lemma v3_decomp_sum (V : ReadFrame σ estar hstar sstar tstar)
    (γ : ℤ) (Tm : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → ↥σ.K) (S : Finset ℕ)
    (hT0 : ∀ j ∈ S, Tm j ≠ 0) (hTw : ∀ j ∈ S, childW σ σ.Φ estar hstar (Tm j) = γ)
    (hTR : ∀ j ∈ S, V.D.Rv (Tm j) = Finsupp.single (pos j) (c j)) (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) (hne : S.Nonempty) :
    V.D.Rv (∑ j ∈ S, Tm j) = ∑ j ∈ S, V.D.Rv (Tm j) ∧
      childW σ σ.Φ estar hstar (∑ j ∈ S, Tm j) = γ ∧ (∑ j ∈ S, Tm j) ≠ 0 := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  revert hT0 hTw hTR hc hinj hne
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _ _ _ hne; exact absurd hne (by simp)
  · intro a S' ha ih hT0 hTw hTR hc hinj _
    simp only [Finset.sum_insert ha]
    have hwta : childW σ σ.Φ estar hstar (Tm a) = γ := hTw a (Finset.mem_insert_self a S')
    have hTa0 : Tm a ≠ 0 := hT0 a (Finset.mem_insert_self a S')
    rcases S'.eq_empty_or_nonempty with hE | hE
    · subst hE; simp only [Finset.sum_empty, add_zero]; exact ⟨trivial, hwta, hTa0⟩
    obtain ⟨hRP, hwP, hP0⟩ := ih (fun j hj => hT0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTw j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hinj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hE
    have hMQ : V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j)
        = ∑ j ∈ insert a S', Finsupp.single (pos j) (c j) := by
      rw [Finset.sum_insert ha, hTR a (Finset.mem_insert_self a S'), hRP]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
    have hMval : ((V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j) : LaurentPolynomial ↥σ.K)
        : ℤ →₀ ↥σ.K) (pos a) = c a := by
      rw [hMQ]
      exact v3_coeff_extract (insert a S') pos c a (Finset.mem_insert_self a S')
        (fun j hj hpj => hinj j hj a (Finset.mem_insert_self a S') hpj)
    have hMne : V.D.Rv (Tm a) + V.D.Rv (∑ j ∈ S', Tm j) ≠ 0 := by
      intro hz; rw [hz] at hMval
      exact hc a (Finset.mem_insert_self a S') hMval.symm
    have h3 : Tm a + ∑ j ∈ S', Tm j ≠ 0 := by
      intro hzero
      apply hMne
      have hxe : Tm a = -(∑ j ∈ S', Tm j) := eq_neg_of_add_eq_zero_left hzero
      rw [hxe, hRneg]; exact neg_add_cancel _
    have hge : γ ≤ childW σ σ.Φ estar hstar (Tm a + ∑ j ∈ S', Tm j) := by
      have h := V.hwult (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3
      rw [hwta, hwP, min_self] at h; exact h
    have h2 : childW σ σ.Φ estar hstar (Tm a + ∑ j ∈ S', Tm j) = γ := by
      refine le_antisymm ?_ hge
      by_contra hlt; push_neg at hlt
      exact hMne (hWjump (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3 (by rw [hwta, hwP])
        (by rw [hwta]; exact hlt))
    have h1 : V.D.Rv (Tm a + ∑ j ∈ S', Tm j) = V.D.Rv (Tm a) + ∑ j ∈ S', V.D.Rv (Tm j) := by
      rw [hRadd (Tm a) (∑ j ∈ S', Tm j) hTa0 hP0 h3 (hwta.trans hwP.symm)
        (h2.trans hwta.symm), hRP]
    exact ⟨h1, h2, h3⟩

/-! ### The development form of RV, width bound, and the ψ-∤ analog -/

/-- **RV of a development is its minimizing-slot residual sum** (the D.5/D.8 rerun engine at
the ReadFrame): for any `Φ`-development of `f ≠ 0`, `RV(f) = Σ_{j minimizing} RV(B_j·Φ^j)`,
with all minimizing slots nonzero of slot weight `wV f`. -/
private lemma v3_devForm (V : ReadFrame σ estar hstar sstar tstar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (f : Polynomial ℤ_[p]) (Bd : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hf : f ≠ 0) (hdev : IsDevelopment σ.Φ f Bd N) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ j ∈ S, j < N ∧ Bd j ≠ 0 ∧ inC σ.Φ (Bd j) ∧
        childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j) = childW σ σ.Φ estar hstar f) ∧
      V.D.Rv f = ∑ j ∈ S, V.D.Rv (Bd j * σ.Φ ^ j) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨hdegs, hzero, hsum⟩ := hdev
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  obtain ⟨hmle, j₀, hj₀N, hj₀nz, hj₀eq⟩ := V.hK1 f Bd N hf ⟨hdegs, hzero, hsum⟩
  have hwa : ∀ j, Bd j ≠ 0 →
      childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j)
        = childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) := by
    intro j hBj
    rw [V.hwmul _ _ hBj (pow_ne_zero j hΦ0), v3_wv_pow V σ.Φ hΦ0 j, V.hwPhi]
  set m := childW σ σ.Φ estar hstar f with hm
  set SN : Finset ℕ := (Finset.range N).filter (fun j => Bd j ≠ 0) with hSN
  have hSNmem : ∀ j, j ∈ SN ↔ j < N ∧ Bd j ≠ 0 := by
    intro j; rw [hSN, Finset.mem_filter, Finset.mem_range]
  set S : Finset ℕ := SN.filter
    (fun j => childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m) with hS
  set Srest : Finset ℕ := SN.filter
    (fun j => ¬ (childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m)) with hSrest
  have hSmem : ∀ j, j ∈ S ↔ (j < N ∧ Bd j ≠ 0) ∧
      childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m := by
    intro j; rw [hS, Finset.mem_filter, hSNmem]
  have hj₀S : j₀ ∈ S := (hSmem j₀).mpr ⟨⟨hj₀N, hj₀nz⟩, hj₀eq.symm⟩
  -- the per-slot facts on S
  have hSfacts : ∀ j ∈ S, j < N ∧ Bd j ≠ 0 ∧ inC σ.Φ (Bd j) ∧
      childW σ σ.Φ estar hstar (Bd j * σ.Φ ^ j) = m := by
    intro j hj
    obtain ⟨⟨hjN, hBj⟩, hcond⟩ := (hSmem j).mp hj
    exact ⟨hjN, hBj, hdegs j, by rw [hwa j hBj]; exact hcond⟩
  -- monomial data with a chosen scalar function
  have hmono : ∀ j, j ∈ S → ∃ cu : (↥σ.K)ˣ,
      V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) ((cu : ↥σ.K)) := by
    intro j hj
    exact v3_slot_mono V (Bd j) ((hSfacts j hj).2.1) (hdegs j) j
  have hcfun : ∀ j : ℕ, ∃ cc : ↥σ.K,
      (j ∈ S → cc ≠ 0 ∧ V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) cc) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨cu, hcu⟩ := hmono j hj
      exact ⟨(cu : ↥σ.K), fun _ => ⟨Units.ne_zero cu, hcu⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose cf hcspec using hcfun
  -- position injectivity on S (Bézout)
  have hinj : ∀ j ∈ S, ∀ k ∈ S,
      (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) = (- tstar * σ.w (Bd k) + (k : ℤ) * sstar) →
      j = k := by
    intro j hj k hk hpos
    have hej := v3_epos V hbez (Bd j) ((hSfacts j hj).2.1) (hdegs j) j m ((hSfacts j hj).2.2.2)
    have hek := v3_epos V hbez (Bd k) ((hSfacts k hk).2.1) (hdegs k) k m ((hSfacts k hk).2.2.2)
    have hjk : (j : ℤ) - tstar * m = (k : ℤ) - tstar * m := by
      rw [← hej, ← hek, hpos]
    have : (j : ℤ) = (k : ℤ) := by linarith
    exact_mod_cast this
  -- the decomposition over the minimizing slots
  obtain ⟨hRS, hWS, hne0⟩ := v3_decomp_sum V m (fun j => Bd j * σ.Φ ^ j)
    (fun j => - tstar * σ.w (Bd j) + (j : ℤ) * sstar) cf S
    (fun j hj => mul_ne_zero ((hSfacts j hj).2.1) (pow_ne_zero j hΦ0))
    (fun j hj => (hSfacts j hj).2.2.2)
    (fun j hj => (hcspec j hj).2)
    (fun j hj => (hcspec j hj).1)
    hinj ⟨j₀, hj₀S⟩
  -- split f into minimizing + rest
  have hfSN : f = ∑ j ∈ SN, Bd j * σ.Φ ^ j := by
    rw [hsum, hSN]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x hx hax hBx
    exact hax (by rw [hBx, zero_mul])
  have hfd : f = (∑ j ∈ S, Bd j * σ.Φ ^ j) + (∑ j ∈ Srest, Bd j * σ.Φ ^ j) := by
    rw [hfSN, hS, hSrest]
    exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
  refine ⟨S, ⟨j₀, hj₀S⟩, hSfacts, ?_⟩
  rcases eq_or_ne (∑ j ∈ Srest, Bd j * σ.Φ ^ j) 0 with hr0 | hrne
  · have hfeq : f = ∑ j ∈ S, Bd j * σ.Φ ^ j := by rw [hfd, hr0, add_zero]
    rw [hfeq]
    exact hRS
  · have hwrest : m + 1 ≤ childW σ σ.Φ estar hstar (∑ j ∈ Srest, Bd j * σ.Φ ^ j) := by
      refine v3_wv_sum_ge V Srest _ (m + 1) ?_ hrne
      intro j hj haj
      have hjSN : j ∈ SN := Finset.mem_of_mem_filter j hj
      obtain ⟨hjN, hBj⟩ := (hSNmem j).mp hjSN
      have hne' : ¬ (childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) = m) := by
        rw [hSrest, Finset.mem_filter] at hj
        exact hj.2
      have hge : m ≤ childW σ σ.Φ estar hstar (Bd j) + (j : ℤ) * (hstar : ℤ) :=
        hmle j hjN hBj
      rw [hwa j hBj]
      omega
    rw [hfd]
    rw [hRlt _ _ hne0 hrne (by rw [← hfd]; exact hf) (by rw [hWS]; omega)]
    exact hRS

/-- **Width bound at the regrade** (mirror of `L2_widthBound`): for `B ∈ Ĉ∖0`
(`natDegree B < e★·g·deg Φ`), the support of `RV(B)` fits in a window of width `g`. -/
private lemma v3_width (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (g : ℕ) (hg : 1 ≤ g) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBdeg : B.natDegree < estar * g * σ.Φ.natDegree) :
    ∃ a : ℤ, ∀ k ∈ (V.D.Rv B).support, a ≤ k ∧ k < a + g := by
  classical
  have hRvne : V.D.Rv B ≠ 0 := V.laws.2.1 B hB
  have hsupp_ne : (V.D.Rv B).support.Nonempty := Finsupp.support_nonempty_iff.mpr hRvne
  obtain ⟨Bd, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg B
  have hvanish : ∀ j, estar * g ≤ j → Bd j = 0 :=
    v3_dev_slot_bound σ.Φ σ.hmonic B Bd N (estar * g) hdev hBdeg
  obtain ⟨S, hSne, hSfacts, hRsum⟩ := v3_devForm V hbez B Bd N hB hdev
  have hjlt : ∀ j ∈ S, j < estar * g := by
    intro j hjS
    by_contra hge
    push_neg at hge
    exact (hSfacts j hjS).2.1 (hvanish j hge)
  -- choose the scalar function of the minimizing slots
  have hcfun : ∀ j : ℕ, ∃ cc : ↥σ.K, (j ∈ S →
      V.D.Rv (Bd j * σ.Φ ^ j)
        = Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) cc) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨hjN, hBj, hinC, hwj⟩ := hSfacts j hj
      obtain ⟨cu, hcu⟩ := v3_slot_mono V (Bd j) hBj hinC j
      exact ⟨(cu : ↥σ.K), fun _ => hcu⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose cf hcf using hcfun
  have hsingles : V.D.Rv B
      = ∑ j ∈ S, Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j) := by
    rw [hRsum]
    exact Finset.sum_congr rfl (fun j hj => hcf j hj)
  -- pin each support point to a minimizing-slot position
  have hpin : ∀ x ∈ (V.D.Rv B).support, ∃ j ∈ S,
      x = - tstar * σ.w (Bd j) + (j : ℤ) * sstar := by
    intro x hx
    have hxne : ((V.D.Rv B : LaurentPolynomial ↥σ.K) : ℤ →₀ ↥σ.K) x ≠ 0 :=
      Finsupp.mem_support_iff.mp hx
    by_contra hnone
    push_neg at hnone
    apply hxne
    have happ : ((V.D.Rv B : LaurentPolynomial ↥σ.K) : ℤ →₀ ↥σ.K) x
        = ∑ j ∈ S, (Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j)
            : ℤ →₀ ↥σ.K) x := by
      rw [hsingles]
      exact Finsupp.finset_sum_apply S
        (fun j => (Finsupp.single (- tstar * σ.w (Bd j) + (j : ℤ) * sstar) (cf j)
          : ℤ →₀ ↥σ.K)) x
    rw [happ]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finsupp.single_apply, if_neg (fun h => (hnone j hj) h.symm)]
  -- pairwise width bound
  have hpair : ∀ x ∈ (V.D.Rv B).support, ∀ y ∈ (V.D.Rv B).support, x - y < (g : ℤ) := by
    intro x hx y hy
    obtain ⟨jx, hjxS, hxeq⟩ := hpin x hx
    obtain ⟨jy, hjyS, hyeq⟩ := hpin y hy
    obtain ⟨hjxN, hBjx, hinCx, hwx⟩ := hSfacts jx hjxS
    obtain ⟨hjyN, hBjy, hinCy, hwy⟩ := hSfacts jy hjyS
    have hex : (estar : ℤ) * x = (jx : ℤ) - tstar * childW σ σ.Φ estar hstar B := by
      rw [hxeq]; exact v3_epos V hbez (Bd jx) hBjx hinCx jx _ hwx
    have hey : (estar : ℤ) * y = (jy : ℤ) - tstar * childW σ σ.Φ estar hstar B := by
      rw [hyeq]; exact v3_epos V hbez (Bd jy) hBjy hinCy jy _ hwy
    have hdiff : (estar : ℤ) * (x - y) = (jx : ℤ) - (jy : ℤ) := by
      rw [mul_sub, hex, hey]; ring
    have he0 : (0 : ℤ) < (estar : ℤ) := by exact_mod_cast hee
    have hjxb : (jx : ℤ) < (estar : ℤ) * (g : ℤ) := by exact_mod_cast hjlt jx hjxS
    have hjyb : (0 : ℤ) ≤ (jy : ℤ) := by positivity
    have hlt : (estar : ℤ) * (x - y) < (estar : ℤ) * (g : ℤ) := by rw [hdiff]; omega
    by_contra hcon
    push_neg at hcon
    have hmul : (estar : ℤ) * (g : ℤ) ≤ (estar : ℤ) * (x - y) :=
      mul_le_mul_of_nonneg_left hcon (le_of_lt he0)
    omega
  refine ⟨(V.D.Rv B).support.min' hsupp_ne, ?_⟩
  intro k hk
  refine ⟨Finset.min'_le _ k hk, ?_⟩
  have hb := hpair k hk ((V.D.Rv B).support.min' hsupp_ne) (Finset.min'_mem _ hsupp_ne)
  linarith

/-- **The `L3_digPrime_nonzero`-analog at the same key** (mirror of `L2.psiNotDvd`):
`ψ ∤ RV(B)` for a nonzero below-`Φ̂`-width coefficient `B`. -/
private theorem v3_psiNotDvd (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hBdeg : B.natDegree < estar * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ V.D.Rv B) := by
  classical
  intro hdvd
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := v3_width V hee hbez g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (V.laws.2.1 B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact V.laws.2.1 B hB hRB
  have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent Ranch := by
    have h := hdvd.mul_left (LaurentPolynomial.T (-a))
    rwa [hRB, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h
  obtain ⟨q, hq⟩ := hdvdR
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  have hkey : Ranch * Polynomial.X ^ n = ψ * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
  have hdiv : ψ ∣ Ranch * Polynomial.X ^ n := ⟨f', hkey⟩
  have hprime : Prime ψ := hψ.prime
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · have hle := Polynomial.natDegree_le_of_dvd h1 hRanch_ne
    omega
  · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)

/-! ### The lift: monicity/degree, weight, and residual (C2 + C3) -/

/-- Mirror of `L3_liftMonic` at the read pair: the recorded lift is monic of degree
`e★·g·deg Φ`. -/
private lemma v3_lift_monic (hee : 1 ≤ estar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g) (Φhat : Polynomial ℤ_[p])
    (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = estar * g * σ.Φ.natDegree := by
  obtain ⟨tt, htt0, httk, hΦhat⟩ := hlift
  have hpowg_mon : (σ.Φ ^ (estar * g)).Monic := σ.hmonic.pow _
  have hpowg_ne : σ.Φ ^ (estar * g) ≠ 0 := hpowg_mon.ne_zero
  have hbpos : (⊥ : WithBot ℕ) < (σ.Φ ^ (estar * g)).degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hpowg_ne (Polynomial.degree_eq_bot.mp h))
  have hterm : ∀ k ∈ Finset.range g,
      (tt k * σ.Φ ^ (estar * k)).degree < (σ.Φ ^ (estar * g)).degree := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact hbpos
    · have hcoeff : ψ.coeff k ≠ 0 := fun h => htk (htt0 k h)
      have hlt : (tt k).degree < σ.Φ.degree := (httk k hk hcoeff).2.1
      have hpowk_ne : σ.Φ ^ (estar * k) ≠ 0 := (σ.hmonic.pow _).ne_zero
      have hprod_ne : tt k * σ.Φ ^ (estar * k) ≠ 0 := mul_ne_zero htk hpowk_ne
      have hA : (tt k).natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree htk hlt
      have hmn : estar * k + 1 ≤ estar * g := by
        have h1 : estar * (k + 1) ≤ estar * g := mul_le_mul_left' (by omega) estar
        have h2 : estar * (k + 1) = estar * k + estar := by ring
        omega
      rw [Polynomial.degree_eq_natDegree hprod_ne, Polynomial.degree_eq_natDegree hpowg_ne,
        Polynomial.natDegree_mul htk hpowk_ne, Polynomial.natDegree_pow,
        Polynomial.natDegree_pow, Nat.cast_lt]
      have h1 : (estar * k + 1) * σ.Φ.natDegree ≤ estar * g * σ.Φ.natDegree :=
        mul_le_mul_right' hmn _
      have h2 : (estar * k + 1) * σ.Φ.natDegree = estar * k * σ.Φ.natDegree + σ.Φ.natDegree := by
        ring
      have := σ.hdeg
      omega
  have hSdeg : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (estar * k)).degree
      < (σ.Φ ^ (estar * g)).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff hbpos]
    exact hterm
  refine ⟨?_, ?_⟩
  · rw [hΦhat]; exact hpowg_mon.add_of_left hSdeg
  · rw [hΦhat, Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_left_of_degree_lt hSdeg), Polynomial.natDegree_pow]

/-- **The lift core (C2 + C3 in one decomposition)**: all slots of the recorded lift are
tied at the read weight `e★h★g` with residual monomials at the distinct positions
`D + k`, `D = −t★h★g`; hence `Φ̂ ≠ 0`, `wV(Φ̂) = e★h★g`, and `RV(Φ̂) = T(D)·ψ`. -/
private lemma v3_lift_core (V : ReadFrame σ estar hstar sstar tstar)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hgdeg : ψ.natDegree = g) (hg1 : 1 ≤ g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    Φhat ≠ 0 ∧
      childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
      V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
        Polynomial.toLaurent ψ := by
  classical
  obtain ⟨hee, hhh, hcop, hbez, he1t, hsteep⟩ := hrp
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  obtain ⟨tt, htt0, httk, hΦhat⟩ := hlift
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hcg : ψ.coeff g = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hgdeg] at h
  set W : ℤ := (estar : ℤ) * (hstar : ℤ) * (g : ℤ) with hW
  set D : ℤ := - tstar * (hstar : ℤ) * (g : ℤ) with hD
  set a : ℕ → Polynomial ℤ_[p] :=
    (fun k => if k < g then tt k * σ.Φ ^ (estar * k) else σ.Φ ^ (estar * g)) with ha
  have hag : a g = σ.Φ ^ (estar * g) := by
    rw [ha]; simp
  have hak : ∀ k, k < g → a k = tt k * σ.Φ ^ (estar * k) := by
    intro k hk; rw [ha]; simp [hk]
  have hsum : Φhat = ∑ k ∈ Finset.range (g + 1), a k := by
    rw [Finset.sum_range_succ]
    have hlt : ∀ k ∈ Finset.range g, a k = tt k * σ.Φ ^ (estar * k) := by
      intro k hk; rw [Finset.mem_range] at hk; exact hak k hk
    rw [hag, Finset.sum_congr rfl hlt, hΦhat, add_comm]
  set S : Finset ℕ := (Finset.range (g + 1)).filter (fun k => a k ≠ 0) with hS
  have hSmem : ∀ k, k ∈ S ↔ k < g + 1 ∧ a k ≠ 0 := by
    intro k; rw [hS, Finset.mem_filter, Finset.mem_range]
  have hgS : g ∈ S := by
    refine (hSmem g).mpr ⟨by omega, ?_⟩
    rw [hag]
    exact pow_ne_zero _ hΦ0
  have hpres : ∀ k, k < g → a k ≠ 0 → (tt k ≠ 0 ∧ ψ.coeff k ≠ 0) := by
    intro k hklt hakne
    have htne : tt k ≠ 0 := fun h => hakne (by rw [hak k hklt, h, zero_mul])
    exact ⟨htne, fun hc => htne (htt0 k hc)⟩
  -- the S5-preserved scalar of a present digit IS ψ_k (matching the σ.R monomials)
  have hscal : ∀ k, k < g → ψ.coeff k ≠ 0 →
      V.D.Rv (tt k) = LaurentPolynomial.C (ψ.coeff k) *
        LaurentPolynomial.T (- tstar * σ.w (tt k)) := by
    intro k hk hc
    obtain ⟨htne, htC, htw, htR⟩ := httk k hk hc
    obtain ⟨cu, hcuR, hcuV⟩ := V.D.hS5 (tt k) htne htC
    have hCeq : LaurentPolynomial.C ((cu : ↥σ.K)) = LaurentPolynomial.C (ψ.coeff k) :=
      mul_right_cancel₀ ((LaurentPolynomial.isUnit_T (- σ.t * σ.wPrev (tt k))).ne_zero)
        (by rw [← hcuR, ← htR])
    rw [hcuV, hCeq]
  -- slot residuals: monomials at the distinct positions D + k
  have hslotR : ∀ k ∈ S, V.D.Rv (a k) = Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · obtain ⟨htne, hcne⟩ := hpres k hklt hakne
      obtain ⟨-, htC, htw, -⟩ := httk k hklt hcne
      have hpos : - tstar * σ.w (tt k) + ((estar * k : ℕ) : ℤ) * sstar = D + (k : ℤ) := by
        rw [htw, hD]
        push_cast
        linear_combination (k : ℤ) * hbez
      rw [hak k hklt, hRmul (tt k) (σ.Φ ^ (estar * k)) htne (pow_ne_zero _ hΦ0),
        v3_rv_pow V σ.Φ hΦ0 (estar * k), V.D.hRPhi, hscal k hklt hcne,
        LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add, hpos,
        ← LaurentPolynomial.single_eq_C_mul_T]
    · have hkg : k = g := by omega
      subst hkg
      have hpos : ((estar * k : ℕ) : ℤ) * sstar = D + (k : ℤ) := by
        rw [hD]
        push_cast
        linear_combination (k : ℤ) * hbez
      rw [hag, v3_rv_pow V σ.Φ hΦ0 (estar * k), V.D.hRPhi, LaurentPolynomial.T_pow, hpos, hcg]
      rfl
  -- slot weights: all tied at W
  have hslotW : ∀ k ∈ S, childW σ σ.Φ estar hstar (a k) = W := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · obtain ⟨htne, hcne⟩ := hpres k hklt hakne
      obtain ⟨-, htC, htw, -⟩ := httk k hklt hcne
      rw [hak k hklt, V.hwmul _ _ htne (pow_ne_zero _ hΦ0), v3_wv_pow V σ.Φ hΦ0 (estar * k),
        V.hwPhi, V.hStretch (tt k) htne htC, htw, hW]
      push_cast
      ring
    · have hkg : k = g := by omega
      subst hkg
      rw [hag, v3_wv_pow V σ.Φ hΦ0 (estar * k), V.hwPhi, hW]
      push_cast
      ring
  -- scalar nonvanishing on S
  have hcS : ∀ k ∈ S, ψ.coeff k ≠ 0 := by
    intro k hk
    obtain ⟨hkr, hakne⟩ := (hSmem k).mp hk
    by_cases hklt : k < g
    · exact (hpres k hklt hakne).2
    · have hkg : k = g := by omega
      subst hkg
      rw [hcg]
      exact one_ne_zero
  -- position injectivity (positions are D + k)
  have hinj : ∀ j ∈ S, ∀ k ∈ S, (D + (j : ℤ)) = (D + (k : ℤ)) → j = k := by
    intro j _ k _ h
    have : (j : ℤ) = (k : ℤ) := by linarith
    exact_mod_cast this
  obtain ⟨hRS, hWS, hne0⟩ := v3_decomp_sum V W a (fun k => D + (k : ℤ)) (fun k => ψ.coeff k) S
    (fun k hk => ((hSmem k).mp hk).2) hslotW hslotR hcS hinj ⟨g, hgS⟩
  have hSsum : ∑ k ∈ S, a k = Φhat := by
    rw [hsum, hS]
    exact Finset.sum_filter_of_ne (fun x hx hax => hax)
  refine ⟨hSsum ▸ hne0, hSsum ▸ hWS, ?_⟩
  -- assemble RV(Φ̂) = T(D)·ψ
  have h1 : V.D.Rv Φhat = ∑ k ∈ S, Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    rw [← hSsum, hRS]
    exact Finset.sum_congr rfl hslotR
  have hext : ∑ k ∈ S, Finsupp.single (D + (k : ℤ)) (ψ.coeff k)
      = ∑ k ∈ Finset.range (g + 1), Finsupp.single (D + (k : ℤ)) (ψ.coeff k) := by
    refine Finset.sum_subset (by rw [hS]; exact Finset.filter_subset _ _) ?_
    intro k hkr hkS
    have hak0 : a k = 0 := by
      by_contra hakne
      exact hkS ((hSmem k).mpr ⟨Finset.mem_range.mp hkr, hakne⟩)
    have hklt : k < g := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hkr) with h | h
      · exact h
      · exfalso
        subst h
        rw [hag] at hak0
        exact pow_ne_zero _ hΦ0 hak0
    have hcoeff0 : ψ.coeff k = 0 := by
      by_contra hc
      have htne := (httk k hklt hc).1
      exact htne (by
        have := hak k hklt
        rw [this] at hak0
        rcases mul_eq_zero.mp hak0 with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ hΦ0))
    rw [hcoeff0, Finsupp.single_zero]
  have htL : Polynomial.toLaurent ψ
      = ∑ k ∈ Finset.range (g + 1),
          LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (k : ℤ) := by
    conv_lhs => rw [ψ.as_sum_range' (g + 1) (by rw [hgdeg]; omega)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow]
  rw [h1, hext, htL, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [show LaurentPolynomial.T D * (LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (k : ℤ))
        = LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (D + (k : ℤ)) from by
      rw [LaurentPolynomial.T_add]; ring,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-! ### The K1 no-cancellation engine at (Φ̂, wV, RV) (C4) -/

/-- The residual slot coefficient `c_j = RV(B_j)·z^{jD}` (`D = −t★h★g`), so that
`RV(B_j·Φ̂^j) = c_j·ψ(z)^j`. -/
private noncomputable def v3_cslot (V : ReadFrame σ estar hstar sstar tstar) (g : ℕ)
    (B : ℕ → Polynomial ℤ_[p]) (j : ℕ) : LaurentPolynomial ↥σ.K :=
  V.D.Rv (B j) * LaurentPolynomial.T ((j : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ)))

/-- **The no-cancellation engine** (mirror of L3_K1's `key_no_cancel`, simplified by the
pack's `hRneg`): no relation `Σ_{j∈T} RV(B_j Φ̂^j) = −RV(B_i Φ̂^i)` with `i ∉ T` can hold —
transported to the residual side it is a vanishing distinct-ψ-order sum, killed by
`v3_GRf` + `v3_psiNotDvd`. -/
private lemma v3_key_no_cancel (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hΦne : Φhat ≠ 0)
    (hRhat : V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
      Polynomial.toLaurent ψ)
    (hDeg : Φhat.natDegree = estar * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree)
    (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T) (hBi : B i ≠ 0) (hBT : ∀ j ∈ T, B j ≠ 0) :
    (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) ≠ - V.D.Rv (B i * Φhat ^ i) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  intro heq
  have hTne0 : ∀ n : ℤ, (LaurentPolynomial.T n : LaurentPolynomial ↥σ.K) ≠ 0 :=
    fun n => (LaurentPolynomial.isUnit_T n).ne_zero
  -- the residual slot identity RV(B_j Φ̂^j) = c_j ψ^j
  have hRa : ∀ j, B j ≠ 0 →
      V.D.Rv (B j * Φhat ^ j) = v3_cslot V g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold v3_cslot
    rw [hRmul _ _ hBj (pow_ne_zero j hΦne), v3_rv_pow V Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  have hBdeg' : ∀ j, B j ≠ 0 → (B j).natDegree < estar * g * σ.Φ.natDegree := by
    intro j hBj
    have h := Polynomial.natDegree_lt_natDegree hBj (hdeg j)
    rwa [hDeg] at h
  have hc0 : ∀ j, B j ≠ 0 → v3_cslot V g B j ≠ 0 := by
    intro j hBj
    unfold v3_cslot
    exact mul_ne_zero (hRne _ hBj) (hTne0 _)
  have hcnd : ∀ j, B j ≠ 0 → ¬ (Polynomial.toLaurent ψ ∣ v3_cslot V g B j) := by
    intro j hBj hdvd
    unfold v3_cslot at hdvd
    have h2 := hdvd.mul_right
      (LaurentPolynomial.T (-((j : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ)))))
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    exact v3_psiNotDvd V hee hbez ψ g hg hmon hψ hψz (B j) hBj (hBdeg' j hBj) h2
  -- the vanishing distinct-ψ-order sum forced by `heq`
  have hsum0 : (∑ j ∈ insert i T, v3_cslot V g B j * Polynomial.toLaurent ψ ^ j) = 0 := by
    rw [Finset.sum_insert hiT]
    have hrest : (∑ j ∈ T, v3_cslot V g B j * Polynomial.toLaurent ψ ^ j)
        = ∑ j ∈ T, V.D.Rv (B j * Φhat ^ j) :=
      Finset.sum_congr rfl (fun j hj => (hRa j (hBT j hj)).symm)
    rw [hrest, heq, hRa i hBi]
    ring
  refine v3_GRf ψ hψ hψz (v3_cslot V g B) (insert i T) ⟨i, Finset.mem_insert_self i T⟩
    ?_ hsum0
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hjT
  · exact ⟨hc0 j hBi, hcnd j hBi⟩
  · exact ⟨hc0 j (hBT j hjT), hcnd j (hBT j hjT)⟩

/-- **Minimizing-slot subsums are honest** (mirror of L3_K1's `minsum_facts`, simplified by
the pack's `hRneg`/`hWjump`): a nonempty sum of slot terms `B_j Φ̂^j`, all of `wV`-weight
exactly `m`, is nonzero of weight exactly `m`, with additive `RV`-residuals. -/
private lemma v3_minsum_facts (V : ReadFrame σ estar hstar sstar tstar)
    (hee : 1 ≤ estar)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hΦne : Φhat ≠ 0)
    (hRhat : V.D.Rv Φhat = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
      Polynomial.toLaurent ψ)
    (hDeg : Φhat.natDegree = estar * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree) (m : ℤ) :
    ∀ S' : Finset ℕ, (∀ j ∈ S', B j ≠ 0) →
      (∀ j ∈ S', childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m) →
      S'.Nonempty →
      (∑ j ∈ S', B j * Φhat ^ j) ≠ 0 ∧
        childW σ σ.Φ estar hstar (∑ j ∈ S', B j * Φhat ^ j) = m ∧
        V.D.Rv (∑ j ∈ S', B j * Φhat ^ j) = ∑ j ∈ S', V.D.Rv (B j * Φhat ^ j) := by
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  intro S'
  induction S' using Finset.induction with
  | empty => intro _ _ h; exact absurd h (by simp)
  | insert i T hiT ih =>
    intro hB' hw' _
    have hBi : B i ≠ 0 := hB' i (Finset.mem_insert_self i T)
    have hwi : childW σ σ.Φ estar hstar (B i * Φhat ^ i) = m :=
      hw' i (Finset.mem_insert_self i T)
    have hai : B i * Φhat ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦne)
    have hBT : ∀ j ∈ T, B j ≠ 0 := fun j hj => hB' j (Finset.mem_insert_of_mem hj)
    have hwT : ∀ j ∈ T, childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m :=
      fun j hj => hw' j (Finset.mem_insert_of_mem hj)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [Finset.sum_insert (Finset.notMem_empty i), Finset.sum_empty, add_zero]
      exact ⟨hai, hwi, trivial⟩
    · obtain ⟨hsTne, hwsT, hRsT⟩ := ih hBT hwT hTne
      rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
      -- (a) the subsum cannot vanish (else Σ_T RV(a_j) = −RV(a_i), killed by no-cancel)
      have hsne : B i * Φhat ^ i + (∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := by
        intro h0
        have hsTeq : (∑ j ∈ T, B j * Φhat ^ j) = -(B i * Φhat ^ i) :=
          eq_neg_of_add_eq_zero_right h0
        have hR1 : (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) = - V.D.Rv (B i * Φhat ^ i) := by
          rw [← hRsT, hsTeq, hRneg]
        exact v3_key_no_cancel V hee hbez ψ g hg hmon hψ hψz Φhat hΦne hRhat hDeg B hdeg
          i T hiT hBi hBT hR1
      have hwge : m ≤ childW σ σ.Φ estar hstar
          (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
        have h1 := V.hwult _ _ hai hsTne hsne
        rw [hwi, hwsT, min_self] at h1
        exact h1
      rcases eq_or_lt_of_le hwge with hweq | hwlt
      · -- weight stays at m: hRadd gives residual additivity
        refine ⟨hsne, hweq.symm, ?_⟩
        rw [hRadd _ _ hai hsTne hsne (by rw [hwi, hwsT]) (by rw [hwi]; exact hweq.symm), hRsT]
      · -- (b) the weight cannot jump (hWjump forces the killed relation)
        exfalso
        have hjump := hWjump (B i * Φhat ^ i) (∑ j ∈ T, B j * Φhat ^ j) hai hsTne hsne
          (by rw [hwi, hwsT]) (by rw [hwi]; exact hwlt)
        have hfinal : (∑ j ∈ T, V.D.Rv (B j * Φhat ^ j)) = - V.D.Rv (B i * Φhat ^ i) := by
          rw [← hRsT]
          exact eq_neg_of_add_eq_zero_right hjump
        exact v3_key_no_cancel V hee hbez ψ g hg hmon hψ hψz Φhat hΦne hRhat hDeg B hdeg
          i T hiT hBi hBT hfinal

end V3Kernel

/-- Unit V3: the recorded read-pair lift is the REGRADE's standard lift — equal
(†)-weights of all present slots (the D.5 EQUAL WEIGHTS display at wV), the D.5
residual display `RV(Φ̂) = T(−t★h★g)·ψ`, and K1 at (Φ̂, wV). -/
theorem V3_readLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hirr : Irreducible ψ)
    (hne : ψ ≠ Polynomial.X) (hdeg : ψ.natDegree = g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
    (∀ tt : ℕ → Polynomial ℤ_[p],
        (∀ k, k < g → ψ.coeff k ≠ 0 →
          σ.w (tt k) = (hstar : ℤ) * ((g : ℤ) - (k : ℤ))) →
        ∀ k, k < g → ψ.coeff k ≠ 0 →
          (estar : ℤ) * σ.w (tt k) + ((estar : ℤ) * (k : ℤ)) * (hstar : ℤ)
            = (estar : ℤ) * (hstar : ℤ) * (g : ℤ)) ∧
    childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
    V.D.Rv Φhat
      = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
          Polynomial.toLaurent ψ ∧
    K1At (childW σ σ.Φ estar hstar) Φhat ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
  classical
  have hee : 1 ≤ estar := hrp.1
  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have hg1 : 1 ≤ g := by
    have := hirr.natDegree_pos
    omega
  obtain ⟨hΦne, hwhat, hRhat⟩ := v3_lift_core V hrp ψ g hmon hdeg hg1 Φhat hlift
  obtain ⟨hMon, hDeg⟩ := v3_lift_monic hee ψ g hg1 Φhat hlift
  refine ⟨?_, hwhat, hRhat, ?_⟩
  · -- C1: the D.5 EQUAL WEIGHTS display at wV
    intro tt htw k hk hc
    rw [htw k hk hc]
    ring
  · -- C4: Lemma K1 at (Φ̂, wV) — the L3_K1 main body, mirrored
    intro f B N hf hdev
    obtain ⟨hdegB, hzero, hsumf⟩ := hdev
    -- slot weights
    have hwa : ∀ j, B j ≠ 0 →
        childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B j) + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      intro j hBj
      rw [V.hwmul _ _ hBj (pow_ne_zero j hΦne), v3_wv_pow V Φhat hΦne j, hwhat]
    -- the nonzero-slot set and the attained minimum
    set SN : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSNdef
    have hSNmem : ∀ j : ℕ, j ∈ SN ↔ j < N ∧ B j ≠ 0 := by
      intro j
      rw [hSNdef, Finset.mem_filter, Finset.mem_range]
    have hSNne : SN.Nonempty := by
      have hfs : (∑ j ∈ Finset.range N, B j * Φhat ^ j) ≠ 0 := by rw [← hsumf]; exact hf
      obtain ⟨j, hjr, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfs
      refine ⟨j, (hSNmem j).mpr ⟨Finset.mem_range.mp hjr, fun hBj => hjne ?_⟩⟩
      rw [hBj, zero_mul]
    obtain ⟨m, hmle, j₀, hj₀SN, hj₀eq⟩ :
        ∃ m : ℤ, (∀ j ∈ SN, m ≤ childW σ σ.Φ estar hstar (B j)
            + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
          ∃ j₀, j₀ ∈ SN ∧ m = childW σ σ.Φ estar hstar (B j₀)
            + (j₀ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
      obtain ⟨j₁, hj₁, heq₁⟩ := Finset.exists_mem_eq_inf' hSNne
        (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)))
      exact ⟨SN.inf' hSNne (fun j => childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))),
        fun j hj => Finset.inf'_le _ hj, j₁, hj₁, heq₁⟩
    have hSN_B : ∀ j ∈ SN, B j ≠ 0 := fun j hj => ((hSNmem j).mp hj).2
    -- minimizing and non-minimizing slots
    set Smin : Finset ℕ := SN.filter
      (fun j => childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) with hSminDef
    set Srest : Finset ℕ := SN.filter
      (fun j => ¬ (childW σ σ.Φ estar hstar (B j)
        + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m)) with hSrestDef
    have hSminMem : ∀ j : ℕ, j ∈ Smin ↔
        j ∈ SN ∧ childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m := by
      intro j
      rw [hSminDef, Finset.mem_filter]
    have hSrestMem : ∀ j : ℕ, j ∈ Srest ↔
        j ∈ SN ∧ ¬ (childW σ σ.Φ estar hstar (B j)
          + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) := by
      intro j
      rw [hSrestDef, Finset.mem_filter]
    have hj₀Smin : j₀ ∈ Smin := (hSminMem j₀).mpr ⟨hj₀SN, hj₀eq.symm⟩
    have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => hSN_B j ((hSminMem j).mp hj).1
    have hSminw : ∀ j ∈ Smin, childW σ σ.Φ estar hstar (B j * Φhat ^ j) = m := by
      intro j hj
      rw [hwa j (hSminB j hj)]
      exact ((hSminMem j).mp hj).2
    obtain ⟨hminNe, hminW, -⟩ := v3_minsum_facts V hee hbez ψ g hdeg hmon hirr hne Φhat hΦne
      hRhat hDeg B hdegB m Smin hSminB hSminw ⟨j₀, hj₀Smin⟩
    -- the development sum over the nonzero slots, split at the minimum
    have hfSN : f = ∑ j ∈ SN, B j * Φhat ^ j := by
      rw [hsumf, hSNdef]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro x hx hax hBx
      exact hax (by rw [hBx, zero_mul])
    have hfd : f = (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) := by
      rw [hfSN, hSminDef, hSrestDef]
      exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
    -- wV f = m
    have hwf : childW σ σ.Φ estar hstar f = m := by
      rcases eq_or_ne (∑ j ∈ Srest, B j * Φhat ^ j) 0 with hr0 | hrne
      · rw [hfd, hr0, add_zero]
        exact hminW
      · have hwrest : m + 1 ≤ childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j) := by
          refine v3_wv_sum_ge V Srest _ (m + 1) ?_ hrne
          intro j hj haj
          have hjSN : j ∈ SN := ((hSrestMem j).mp hj).1
          have hBj : B j ≠ 0 := hSN_B j hjSN
          have h1 := hmle j hjSN
          have h2 : ¬ (childW σ σ.Φ estar hstar (B j)
              + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) = m) :=
            ((hSrestMem j).mp hj).2
          rw [hwa j hBj]
          omega
        have hfne' : (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfd]; exact hf
        have hge : m ≤ childW σ σ.Φ estar hstar f := by
          rw [hfd]
          have h1 := V.hwult _ _ hminNe hrne hfne'
          rw [hminW] at h1
          exact le_trans (le_min le_rfl (by omega)) h1
        by_contra hne'
        have hgt : m < childW σ σ.Φ estar hstar f := lt_of_le_of_ne hge (fun h => hne' h.symm)
        have hnegne : -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrne
        have hfmin_eq : (∑ j ∈ Smin, B j * Φhat ^ j)
            = f + -(∑ j ∈ Srest, B j * Φhat ^ j) := by
          rw [hfd]; ring
        have hminne' : f + -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := by
          rw [← hfmin_eq]; exact hminNe
        have h1 := V.hwult f _ hf hnegne hminne'
        rw [← hfmin_eq, hminW, v3_wv_neg V _ hrne] at h1
        have h3 : m < min (childW σ σ.Φ estar hstar f)
            (childW σ σ.Φ estar hstar (∑ j ∈ Srest, B j * Φhat ^ j)) := lt_min hgt (by omega)
        omega
    -- assemble SlotMinAttained
    refine ⟨?_, j₀, ?_, ?_, ?_⟩
    · intro j hjN hBj
      have hjSN : j ∈ SN := (hSNmem j).mpr ⟨hjN, hBj⟩
      rw [hwf]
      exact hmle j hjSN
    · exact ((hSNmem j₀).mp hj₀SN).1
    · exact hSN_B j₀ hj₀SN
    · rw [hwf]; exact hj₀eq

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V3_readLift
----- END FILE: lean/LeanUrat/HC1/V3_readLift.lean -----

----- FILE: lean/LeanUrat/HC1/V4_readLanding.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V3_readLift

/-!
# HC1.V4_readLanding — (BOX)+(VERTEX) at the ReadFrame (blueprint §10, V4)

V′-KERNEL unit (blueprint §10.1): for f ≠ 0 with anchored RV-data of ψ-order μ,
the Φ̂-development satisfies

* (VERTEX) `wV(B_μ) + μ·e★h★g = wV(f)` with `B_μ ≠ 0`;
* (BOX)    `wV(B_m) + m·e★h★g > wV(f)` for every m < μ with `B_m ≠ 0`;
* the vertex digit with its explicit unit `z̄^{−μ·m̂★}` (`m̂★ = −t★h★g`), for
  consumers that want it (the L5_landVertexDigit shape, transposed to RV).

moves_ref: D.8 (BOX)/(VERTEX) VERBATIM (MOVES 2469–2490: the displayed proof —
K1 + D.1(e) + D.3(d) distinct ψ-orders — consumes NOTHING beyond the ReadFrame
pack; S6/valgrp are untouched, which is what makes Finding 3 harmless).  The
Lean pattern: L5_landVertex/L5_landVertexDigit transplanted to the pack.
deps: V3. difficulty: HARD-ish but bounded (one L5-sized file).

**FENCE (per §10.1): the (TRANSPORT) leg is NOT needed by any of the three
discharges — it is fenced OUT of this unit (recorded as available follow-on);
this file states (BOX)+(VERTEX)+the vertex digit only.**
E-phase: statement per §10.1, `sorry` body.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

/-- Unit V4: the D.8 landing at the ReadFrame — (VERTEX), (BOX), and the vertex
digit with its explicit unit `z̄^{μ·t★·h★·g}` (the `−μm̂★` normalization),
transposing L5_landVertex/L5_landVertexDigit to the regrade pack.  The
(TRANSPORT) leg is fenced OUT (see header). -/
theorem V4_readLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hdeg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K)
    (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) :
    (B μ ≠ 0 ∧
      childW σ σ.Φ estar hstar (B μ)
          + (μ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))
        = childW σ σ.Φ estar hstar f) ∧
    (∀ m, m < μ → B m ≠ 0 →
      childW σ σ.Φ estar hstar f
        < childW σ σ.Φ estar hstar (B m)
            + (m : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
    (∀ zbar : Fˣ, Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 →
      ∃ q : LaurentPolynomial ↥σ.K,
        V.D.Rv f = (Polynomial.toLaurent ψ) ^ μ * q ∧
        ¬ (Polynomial.toLaurent ψ ∣ q) ∧
        LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) (V.D.Rv (B μ))
          = ((zbar ^ ((μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ)) : Fˣ) : F) *
            LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) q) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V4_readLanding
----- END FILE: lean/LeanUrat/HC1/V4_readLanding.lean -----

----- FILE: lean/LeanUrat/HC1/V6_alignedOrbits.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.V6_alignedOrbits — the aligned digit orbits, both levels (blueprint §10, V6)

V′-KERNEL unit (blueprint §10.1), TWO legs — post-V5 (the `Stage.hS6a` coset
restate, 2026-07-28), the S9a header's twisted-orbit display is now a POSITIVE
statement, not an obstruction:

* **(a) REGRADE orbits are UNTWISTED**: σ★-realizers = the parent's coset hS6a
  realizers RE-POSITIONED, scalars PRESERVED (no z̄ enters at the same level) —
  fills `ReadFrame.hS6a`; also the b-transport helper the V5 census cites.
* **(b) DESCENT orbit base points**: the strip window display — slots at child
  weight ν are `(γ, j) = (s·ν − λ·h, t·ν + λ·e)`, λ ∈ (a g-window), twist = λ;
  the minimizing-slot choice (`L4_TRANSviii_a` conjunct 1 forward + choice)
  fixes THE base b(ν) per weight, of the displayed SHAPE
  `(b : F) = (b̃ : F)·z̄^m` (a parent unit times a fixed z̄-monomial class —
  D.7(viii)'s realizer display, MOVES 2423–2435).

moves_ref: D.7(viii)'s 𝒜′ + realizer display (MOVES 2423–2435); the S9a
header's twisted-orbit display.  deps: V0; (b) consumes
`L4_TRANSviii_a_R5_final` post-V5.  difficulty: short.
P-phase COMPLETE (2026-07-28): both legs PROVED σ-only, Lean-core axioms only
(no `sorry`, no new axiom). V6(a) = parent coset `hS6a` transported through
`ReadResData.hS5`; V6(b) = the window (Lemma K1 on the σ.Φ-development) + the
single-slot realizer `Creal·σ.Φ^j` whose z̄-evaluation carries the twist `z̄^m`
that the base `b` absorbs (the below-threshold strip needs NO threshold: it rides
`σ.hS6a`'s coefficient-level coset, not `hS6b`), read into `D.Rc` via `hS5'`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Bounded Φ-adic development (the general polynomial fact; a private copy of the
same-named lemma in `Moves.L4_TRANSviii_a_R5_final`, which is `private` there). -/
private lemma dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) :
    ∀ (M : ℕ) (f : Polynomial R), f.natDegree < M * Φ.natDegree →
      ∃ B : ℕ → Polynomial R, IsDevelopment Φ f B M := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have hz : Φ = 0 := Subsingleton.elim _ _
      rw [hz] at hd; simp at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  intro M
  induction M with
  | zero =>
    intro f hf
    rw [zero_mul] at hf
    exact absurd hf (Nat.not_lt_zero _)
  | succ n IH =>
    intro f hf
    have hdiv : f %ₘ Φ + Φ * (f /ₘ Φ) = f := Polynomial.modByMonic_add_div f Φ
    have hqdev : ∃ B, IsDevelopment Φ (f /ₘ Φ) B n := by
      rcases eq_or_ne (f /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (f.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ f.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (f /ₘ Φ).natDegree = f.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic f hΦ
        rw [Nat.succ_mul] at hf
        omega
    obtain ⟨B', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => f %ₘ Φ | k + 1 => B' k), ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (f %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt f hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) + (f %ₘ Φ) * Φ ^ 0 = f
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) = (f /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      rw [e1]
      linear_combination hdiv

/-- Unit V6(a): REGRADE orbits are the parent's coset orbits re-positioned —
scalars preserved, positions re-forced at `−t★·ν`; fills `ReadFrame.hS6a`. -/
theorem V6_regradeOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (D : ReadResData σ estar hstar sstar tstar) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ σ.Φ →
      ∃ b : (↥σ.K)ˣ, ∀ c : (↥σ.K)ˣ, ((c : ↥σ.K) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ σ.w B = ν ∧
          D.Rv B = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) *
            LaurentPolynomial.T (- tstar * ν) := by
  intro ν hν
  obtain ⟨B₀, hB₀ne, hB₀C, hB₀w⟩ := hν
  -- the regrade weight `ν` decomposes as `e·(parent weight ν₀)` (hStretch);
  -- ν₀ := σ.wPrev B₀ lies in σ's own weight set (hWS), so σ's coset realizer fires.
  have hstretch0 : σ.w B₀ = (σ.e : ℤ) * σ.wPrev B₀ := σ.hStretch B₀ hB₀ne hB₀C
  have hν'WS : σ.wPrev B₀ ∈ σ.weightSet := σ.hWS B₀ hB₀ne hB₀C
  have hνeq : ν = (σ.e : ℤ) * σ.wPrev B₀ := by rw [← hB₀w]; exact hstretch0
  obtain ⟨b, hb⟩ := σ.hS6a (σ.wPrev B₀) hν'WS
  -- SAME base `b` transports (regrade scalars preserved via `D.hS5`)
  refine ⟨b, ?_⟩
  intro c hcFQ
  obtain ⟨B, hBne, hBC, hBwPrev, hBR⟩ := hb c hcFQ
  have hσwB : σ.w B = ν := by
    rw [σ.hStretch B hBne hBC, hBwPrev]; exact hνeq.symm
  refine ⟨B, hBne, hBC, hσwB, ?_⟩
  -- `D.hS5` gives the SAME scalar `c'` for `σ.R B` and `D.Rv B`; the parent realizer
  -- `hBR` pins that scalar's class to `c·b`, so `D.Rv B` reads off with base `b`.
  obtain ⟨c', hc'R, hc'Rv⟩ := D.hS5 B hBne hBC
  rw [hBwPrev] at hc'R
  have hCeq : LaurentPolynomial.C (c' : ↥σ.K)
            = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) := by
    have hCT := hc'R.symm.trans hBR
    have h2 : LaurentPolynomial.C (c' : ↥σ.K)
          * LaurentPolynomial.T (- σ.t * σ.wPrev B₀)
          * LaurentPolynomial.T (σ.t * σ.wPrev B₀)
        = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K)
          * LaurentPolynomial.T (- σ.t * σ.wPrev B₀)
          * LaurentPolynomial.T (σ.t * σ.wPrev B₀) := by rw [hCT]
    rwa [mul_assoc, mul_assoc, ← LaurentPolynomial.T_add,
      show (- σ.t * σ.wPrev B₀ + σ.t * σ.wPrev B₀) = (0 : ℤ) by ring,
      LaurentPolynomial.T_zero, mul_one, mul_one] at h2
  rw [hc'Rv, hσwB, hCeq]

/-- Unit V6(b): DESCENT orbit base points — every child weight ν ∈ 𝒜′ decomposes
through a minimizing slot `(γ, j)` (the TRANSviii_a conjunct-1 window), and the
choice of slot fixes ONE coset base `b(ν)` of the displayed z̄-monomial shape
`(b : F) = (b̃ : F)·z̄^m`, whose F_Qˣ-coset is realized in the carrier `D.Rc`. -/
theorem V6_descentOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0)
    (D : ChildResData σ Φhat e' h' zbar s' t') (hD : ChildResLaws D) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ Φhat →
      (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧
        ν = γ + (j : ℤ) * (σ.h : ℤ)) ∧
      ∃ b : (↥(σ.nextField zbar))ˣ,
        (∃ (btilde : (↥σ.K)ˣ) (m : ℤ),
          ((b : ↥(σ.nextField zbar)) : F)
            = ((btilde : ↥σ.K) : F) * ((zbar ^ m : Fˣ) : F)) ∧
        ∀ c : (↥(σ.nextField zbar))ˣ, ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
          ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
            D.Rc B = LaurentPolynomial.C
                ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
              LaurentPolynomial.T (- t' * ν) := by
  classical
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  -- `σ.R 1 = 1` and `σ.w 1 = 0` (cancellation in the residual / valuation)
  have hR1 : σ.R 1 = 1 := by
    have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; omega
  -- key-power residual and valuation
  have hRpow : ∀ k : ℕ, σ.R (σ.Φ ^ k) = (LaurentPolynomial.T σ.s) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero]; exact hR1
    | succ n ih =>
        rw [pow_succ, σ.hRmul _ _ (pow_ne_zero n σ.hmonic.ne_zero) σ.hmonic.ne_zero, ih,
          σ.hRΦ, pow_succ]
  have hwpow : ∀ k : ℕ, σ.w (σ.Φ ^ k) = (k : ℤ) * (σ.h : ℤ) := by
    intro k
    induction k with
    | zero => rw [pow_zero, hw1]; simp
    | succ n ih =>
        rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n σ.hmonic.ne_zero) σ.hmonic.ne_zero, ih, σ.hwΦ]
        push_cast; ring
  intro ν hν
  obtain ⟨B₀, hB₀ne, hB₀C, hB₀w⟩ := hν
  -- WINDOW (Part 1): develop `B₀` in base `σ.Φ`, ≤ `σ.e*g` slots, then Lemma K1.
  have hdegbound : B₀.natDegree < (σ.e * g) * σ.Φ.natDegree := by
    have h1 : B₀.degree < Φhat.degree := hB₀C
    rw [Polynomial.degree_eq_natDegree hB₀ne, Polynomial.degree_eq_natDegree hΦne] at h1
    have h2 : B₀.natDegree < Φhat.natDegree := by exact_mod_cast h1
    rw [hΦdeg] at h2
    calc B₀.natDegree < σ.e * g * σ.Φ.natDegree := h2
      _ = (σ.e * g) * σ.Φ.natDegree := by ring
  obtain ⟨Bdev, hdev⟩ := dev_exists_bounded σ.Φ σ.hmonic σ.hdeg (σ.e * g) B₀ hdegbound
  obtain ⟨-, j0, hj0lt, hj0nz, hj0eq⟩ := σ.hK1 B₀ Bdev (σ.e * g) hB₀ne hdev
  set C := Bdev j0 with hCdef
  have hCne : C ≠ 0 := hj0nz
  have hCinC : inC σ.Φ C := hdev.1 j0
  have hwin : ν = σ.w C + (j0 : ℤ) * (σ.h : ℤ) := by rw [← hB₀w, hj0eq, σ.hwΦ]
  refine ⟨⟨σ.w C, j0, ⟨C, hCne, hCinC, rfl⟩, hj0lt, hwin⟩, ?_⟩
  -- PART 2: the coset realizer for `D.Rc`, built σ-only from `σ.hS6a` (no threshold).
  have hwPrevWS : σ.wPrev C ∈ σ.weightSet := σ.hWS C hCne hCinC
  obtain ⟨bσ, hbσ⟩ := σ.hS6a (σ.wPrev C) hwPrevWS
  set m : ℤ := σ.s * (j0 : ℤ) - σ.t * σ.wPrev C with hmdef
  -- the base `b : (K')ˣ` of the displayed z̄-monomial shape `(bσ)·z̄^m`
  have hz_mem : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
  have hbσ_mem : ((bσ : ↥σ.K) : F) ∈ σ.nextField zbar :=
    Subfield.subset_closure (Or.inl (SetLike.coe_mem (bσ : ↥σ.K)))
  have hbval_mem : ((bσ : ↥σ.K) : F) * (zbar : F) ^ m ∈ σ.nextField zbar :=
    mul_mem hbσ_mem (Subfield.zpow_mem (σ.nextField zbar) hz_mem m)
  have hbσF_ne : ((bσ : ↥σ.K) : F) ≠ 0 := by
    have : (bσ : ↥σ.K) ≠ 0 := bσ.ne_zero
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact this
  have hbval_ne : (⟨((bσ : ↥σ.K) : F) * (zbar : F) ^ m, hbval_mem⟩ : ↥(σ.nextField zbar)) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff]
    exact mul_ne_zero hbσF_ne (zpow_ne_zero m zbar.ne_zero)
  set b : (↥(σ.nextField zbar))ˣ :=
    Units.mk0 (⟨((bσ : ↥σ.K) : F) * (zbar : F) ^ m, hbval_mem⟩ : ↥(σ.nextField zbar)) hbval_ne with hbdef
  have hbF : ((b : ↥(σ.nextField zbar)) : F) = ((bσ : ↥σ.K) : F) * (zbar : F) ^ m := rfl
  -- exponent-combining identity
  have hzcomb : (zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0 = (zbar : F) ^ m := by
    rw [← zpow_natCast ((zbar : F) ^ σ.s) j0, ← zpow_mul, ← zpow_add₀ zbar.ne_zero]
    rw [hmdef]; ring_nf
  refine ⟨b, ⟨bσ, m, ?_⟩, ?_⟩
  · -- z̄-monomial shape of the base
    rw [hbF]; push_cast; ring
  · intro c hcFQ
    -- pull the coset scalar `c ∈ F_Q` back to a unit of `K` (F_Q ≤ K)
    have hcF_mem : ((c : ↥(σ.nextField zbar)) : F) ∈ σ.K := σ.hFQ_le hcFQ
    have hcF_ne : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 := by
      have : (c : ↥(σ.nextField zbar)) ≠ 0 := c.ne_zero
      simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact this
    set cσ : (↥σ.K)ˣ :=
      Units.mk0 (⟨((c : ↥(σ.nextField zbar)) : F), hcF_mem⟩ : ↥σ.K)
        (by simp only [ne_eq, Subtype.ext_iff]; exact hcF_ne) with hcσdef
    have hcσF : ((cσ : ↥σ.K) : F) = ((c : ↥(σ.nextField zbar)) : F) := rfl
    have hcσFQ : ((cσ : ↥σ.K) : F) ∈ σ.FQ := by rw [hcσF]; exact hcFQ
    obtain ⟨Creal, hCrealNe, hCrealC, hCrealWPrev, hCrealR⟩ := hbσ cσ hcσFQ
    -- the single-slot realizer `B' := Creal · σ.Φ^{j0}`
    have hprodne : Creal * σ.Φ ^ j0 ≠ 0 := mul_ne_zero hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero)
    have hB'inC : inC Φhat (Creal * σ.Φ ^ j0) := by
      have hcnd : Creal.natDegree < σ.Φ.natDegree := by
        have h : Creal.degree < σ.Φ.degree := hCrealC
        rw [Polynomial.degree_eq_natDegree hCrealNe,
          Polynomial.degree_eq_natDegree σ.hmonic.ne_zero] at h
        exact_mod_cast h
      have hpnd : (Creal * σ.Φ ^ j0).natDegree = Creal.natDegree + j0 * σ.Φ.natDegree := by
        rw [Polynomial.natDegree_mul hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero),
          Polynomial.natDegree_pow]
      have hbound : Creal.natDegree + j0 * σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree := by
        have h3 : (j0 + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by gcongr; omega
        have h4 : (j0 + 1) * σ.Φ.natDegree = j0 * σ.Φ.natDegree + σ.Φ.natDegree := by ring
        omega
      show (Creal * σ.Φ ^ j0).degree < Φhat.degree
      rw [Polynomial.degree_eq_natDegree hprodne, Polynomial.degree_eq_natDegree hΦne, hΦdeg, hpnd]
      exact_mod_cast hbound
    have hwB' : σ.w (Creal * σ.Φ ^ j0) = ν := by
      rw [σ.hwmul Creal (σ.Φ ^ j0) hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero)]
      have hwCreal : σ.w Creal = σ.w C := by
        rw [σ.hStretch Creal hCrealNe hCrealC, hCrealWPrev, ← σ.hStretch C hCne hCinC]
      rw [hwCreal, hwpow j0, ← hwin]
    refine ⟨Creal * σ.Φ ^ j0, hprodne, hB'inC, hwB', ?_⟩
    -- digit computation: `digPrime` of the single slot = `(c)·(b)` in `F`
    have hdig : σ.digPrime zbar (Creal * σ.Φ ^ j0)
        = ((c : ↥(σ.nextField zbar)) : F) * ((b : ↥(σ.nextField zbar)) : F) := by
      have hval : σ.R (Creal * σ.Φ ^ j0)
          = LaurentPolynomial.C ((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K)
              * LaurentPolynomial.T (- σ.t * σ.wPrev C) * (LaurentPolynomial.T σ.s) ^ j0 := by
        rw [σ.hRmul Creal (σ.Φ ^ j0) hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero), hCrealR, hRpow j0]
      simp only [Stage.digPrime]
      rw [hval, map_mul, map_pow, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_T, hbF,
        show σ.K.subtype ((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K) = (((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K) : F) from rfl]
      push_cast
      rw [hcσF]
      rw [show ((c : ↥(σ.nextField zbar)) : F) * ((bσ : ↥σ.K) : F)
              * (zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0
            = ((c : ↥(σ.nextField zbar)) : F) * ((bσ : ↥σ.K) : F)
              * ((zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0) from by ring,
        hzcomb]
      ring
    -- convert to `D.Rc` via the S5′ pin and identify the digit unit with `c·b`
    obtain ⟨c'', hc''Rc, hc''dig⟩ := D.hS5' (Creal * σ.Φ ^ j0) hprodne hB'inC
    have hc''eq : (c'' : ↥(σ.nextField zbar))
        = ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      have hinj : Function.Injective (fun x : ↥(σ.nextField zbar) => (x : F)) :=
        fun x y hxy => Subtype.ext hxy
      apply hinj
      show ((c'' : ↥(σ.nextField zbar)) : F)
          = (((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) : F)
      rw [hc''dig, hdig, Units.val_mul]
      push_cast; ring
    rw [hc''Rc, hwB', hc''eq]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V6_regradeOrbits
#print axioms LeanUrat.HC1.V6_descentOrbits
----- END FILE: lean/LeanUrat/HC1/V6_alignedOrbits.lean -----

----- FILE: lean/LeanUrat/HC1/V7_stripDischarge.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.V7_stripDischarge — S9a's (S6a′) obligation closes (blueprint §10, V7)

V′-KERNEL unit (blueprint §10.1), the (S6a′) coset discharge over an arbitrary lawful
child carrier `D : ChildResData` — for every child weight `ν ∈ 𝒜′` there is ONE coset
base `b(ν)` whose `F_Qˣ`-coset is realized in `D.Rc` at the forced position `−t′·ν`.

**AXIOM-CLEAN PROOF, pure-σ (no dependency on the sorry-backed V6/S9_transStage).**
Because `D.hS5'` pins `D.Rc B`'s scalar's F-image to the PARENT quantity
`σ.digPrime zbar B`, the whole obligation reduces to the parent digit set at weight `ν`:

* ABOVE THRESHOLD (`σ.w Φhat < ν`): base `b := 1`, digit surjectivity from the proved
  pure-σ `Moves.L4_TRANSviii_b` (any target digit `a ∈ K⟮z̄⟯` at any `ν` above the key
  weight), exactly S9a's in-file `hS6b'` pattern.
* BELOW THRESHOLD (the strip `ν ≤ σ.w Φ̂`): the single-slot realizer `B := C·Φ^j` with
  `C` a parent (S6a) coset realizer (`σ.hS6a`) at the parent-scale weight `w̃`, `j` the
  attaining slot of a Φ-adic development of a `childWeightSet` witness. The parent orbit
  scalar enters LINEARLY through `L2_strideRule` + `eval₂_C_mul_T`, giving digit
  `(c·b̃)·z̄^m`; the coset base `b(ν) := b̃·z̄^m` (parent base × a fixed z̄-monomial),
  c-independent. This is `L4_TRANSviii_a`'s conjunct-2 argument transcribed to the
  `digPrime`/`hS5'` coordinate — no child stage σ′ required.

This unit's statement is EXACTLY the hS6a′ obligation shape of S9a's literal (over any
lawful carrier — S9a applies it at its S9w carrier `hexD.choose`).
UNBLOCKS: S9a → S9b → S9c/S9d → S9.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Stage-valuation of a single-slot element: `w(C·Φ^j) = w C + j·w Φ = w C + j·h`.
(Local copy of the `L4_TRANSviii_a` private helper.) -/
private lemma v7_w_mul_keyPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (C : Polynomial ℤ_[p]) (hC : C ≠ 0) (j : ℕ) :
    σ.w (C * σ.Φ ^ j) = σ.w C + (j : ℤ) * (σ.h : ℤ) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp
  | succ n ih =>
    have hΦn : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ
    have hrw : C * σ.Φ ^ (n + 1) = (C * σ.Φ ^ n) * σ.Φ := by ring
    rw [hrw, σ.hwmul _ _ (mul_ne_zero hC hΦn) hΦ, ih, σ.hwΦ]
    push_cast; ring

/-- **Bounded Fact A**: for monic `Φ` of degree `≥ 1`, every `f` with `deg f < M·deg Φ`
has a Φ-adic development with slot budget exactly `M`. (Local copy of the
`L4_TRANSviii_a` private helper.) -/
private lemma v7_dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) :
    ∀ (M : ℕ) (f : Polynomial R), f.natDegree < M * Φ.natDegree →
      ∃ B : ℕ → Polynomial R, IsDevelopment Φ f B M := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have hz : Φ = 0 := Subsingleton.elim _ _
      rw [hz] at hd; simp at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  intro M
  induction M with
  | zero =>
    intro f hf
    rw [zero_mul] at hf
    exact absurd hf (Nat.not_lt_zero _)
  | succ n IH =>
    intro f hf
    have hdiv : f %ₘ Φ + Φ * (f /ₘ Φ) = f := Polynomial.modByMonic_add_div f Φ
    have hqdev : ∃ B, IsDevelopment Φ (f /ₘ Φ) B n := by
      rcases eq_or_ne (f /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (f.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ f.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (f /ₘ Φ).natDegree = f.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic f hΦ
        rw [Nat.succ_mul] at hf
        omega
    obtain ⟨B', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => f %ₘ Φ | k + 1 => B' k), ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (f %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt f hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) + (f %ₘ Φ) * Φ ^ 0 = f
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) = (f /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      rw [e1]
      linear_combination hdiv

/-- Unit V7: the full (S6a′) coset discharge — for every child weight ν ∈ 𝒜′ there
is ONE coset base b(ν) whose F_Qˣ-coset is realized in the carrier at the forced
position `−t′·ν`; exactly the `hS6a` field shape of S9a's child Stage literal. -/
theorem V7_stripDischarge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0)
    (D : ChildResData σ Φhat e' h' zbar s' t') (hD : ChildResLaws D) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ Φhat →
      ∃ b : (↥(σ.nextField zbar))ˣ, ∀ c : (↥(σ.nextField zbar))ˣ,
        ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
          D.Rc B = LaurentPolynomial.C
              ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
            LaurentPolynomial.T (- t' * ν) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  have hg1 : 1 ≤ g := th.hg
  -- deg Φ̂ = e·g·deg Φ, from the standard-lift shape (proved, `L3_liftMonic`)
  have hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree :=
    (L3_liftMonic σ ψ g hg1 Φhat th.hlift).2
  -- z̄ a root in the `eval₂` coordinate `L4_TRANSviii_b` expects
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  -- single-slot elements `C·Φ^j`, `j < e·g`, land in `C_Φ̂` (degree bound)
  have hslot : ∀ (C : Polynomial ℤ_[p]) (j : ℕ), C ≠ 0 → inC σ.Φ C → j < σ.e * g →
      inC Φhat (C * σ.Φ ^ j) := by
    intro C j hC hCc hj
    have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC hΦj
    have hCd : C.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hC hCc
    have hΦhat0 : Φhat ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hΦdeg
      have hpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (by omega) (by omega)
      omega
    have hBnd : (C * σ.Φ ^ j).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_mul hC hΦj, Polynomial.natDegree_pow, hΦdeg]
      have h2 : (j + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by gcongr; omega
      calc C.natDegree + j * σ.Φ.natDegree
          < σ.Φ.natDegree + j * σ.Φ.natDegree := by omega
        _ = (j + 1) * σ.Φ.natDegree := by ring
        _ ≤ σ.e * g * σ.Φ.natDegree := h2
    show (C * σ.Φ ^ j).degree < Φhat.degree
    rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_eq_natDegree hΦhat0]
    exact_mod_cast hBnd
  -- transfer a child-field FQ-scalar to a parent-field unit with the same F-image
  have hFQtransfer : ∀ c : (↥(σ.nextField zbar))ˣ, ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
      ∃ c₁ : (↥σ.K)ˣ, ((c₁ : ↥σ.K) : F) = ((c : ↥(σ.nextField zbar)) : F) ∧
        ((c₁ : ↥σ.K) : F) ∈ σ.FQ := by
    intro c hcFQ
    have hx0 : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 :=
      fun h => (Units.ne_zero c) (ZeroMemClass.coe_eq_zero.mp h)
    have hxK : ((c : ↥(σ.nextField zbar)) : F) ∈ σ.K := σ.hFQ_le hcFQ
    have hc₁0 : (⟨((c : ↥(σ.nextField zbar)) : F), hxK⟩ : ↥σ.K) ≠ 0 := by
      simp [Subtype.ext_iff, hx0]
    exact ⟨Units.mk0 _ hc₁0, rfl, hcFQ⟩
  intro ν hν
  rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
  · -- ABOVE THRESHOLD: base b = 1, digit surjectivity from `L4_TRANSviii_b`
    refine ⟨1, ?_⟩
    intro c hcFQ
    obtain ⟨B, hBc, hdig, hnz⟩ := L4_TRANSviii_b σ hσ.core ψ g th.hdeg th.hmonic th.hirr
      th.hne_z Φhat th.hlift zbar hzbar ν hgt ((c : ↥(σ.nextField zbar)) : F)
      (SetLike.coe_mem _)
    have hane : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 :=
      fun h => (Units.ne_zero c) (ZeroMemClass.coe_eq_zero.mp h)
    obtain ⟨hB0, hBw⟩ := hnz hane
    obtain ⟨c', hc'R, hc'F⟩ := D.hS5' B hB0 hBc
    have hcs : (c' : ↥(σ.nextField zbar)) = ((c * 1 : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
      simp
    exact ⟨B, hB0, hBc, hBw, by rw [hc'R, hcs, hBw]⟩
  · -- BELOW THRESHOLD (the strip): the single-slot realizer `C·Φ^j`
    obtain ⟨B₀, hB₀0, hB₀c, hB₀w⟩ := hν
    have hBnd : B₀.natDegree < σ.e * g * σ.Φ.natDegree := by
      have h := Polynomial.natDegree_lt_natDegree hB₀0 hB₀c
      rwa [hΦdeg] at h
    obtain ⟨Bd, hdev⟩ := v7_dev_exists_bounded σ.Φ σ.hmonic hd1 (σ.e * g) B₀ hBnd
    obtain ⟨-, j, hjN, hnzj, hmin⟩ := σ.hK1 B₀ Bd (σ.e * g) hB₀0 hdev
    -- the attaining slot's coefficient, its parent-scale weight `w̃`
    have hBdjc : inC σ.Φ (Bd j) := hdev.1 j
    set wt : ℤ := σ.wPrev (Bd j) with hwt
    have hwtWS : wt ∈ σ.weightSet := σ.hWS (Bd j) hnzj hBdjc
    have hγstretch : σ.w (Bd j) = (σ.e : ℤ) * wt := σ.hStretch (Bd j) hnzj hBdjc
    -- ν = w(Bd j) + j·h  (from the attained slot-minimum + `hwΦ`)
    have hνdecomp : ν = σ.w (Bd j) + (j : ℤ) * (σ.h : ℤ) := by
      rw [← hB₀w, hmin, σ.hwΦ]
    -- the parent (S6a) coset base `b̃` at `w̃`, c-independent
    obtain ⟨btilde, hbtilde⟩ := σ.hS6a wt hwtWS
    -- the fixed z̄-monomial exponent
    set m : ℤ := - σ.t * wt + σ.s * (j : ℤ) with hm
    -- the child coset base `b := b̃·z̄^m ∈ K⟮z̄⟯`
    have hbtilde_mem : ((btilde : ↥σ.K) : F) ∈ σ.nextField zbar :=
      σ.le_nextField zbar (btilde : ↥σ.K).2
    have hzbar_mem : ((zbar : F)) ∈ σ.nextField zbar :=
      Subfield.subset_closure (Or.inr rfl)
    have hzpow_mem : (((zbar ^ m : Fˣ)) : F) ∈ σ.nextField zbar := by
      rw [Units.val_zpow_eq_zpow_val]
      exact Subfield.zpow_mem _ hzbar_mem m
    have hbval_mem : ((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) ∈ σ.nextField zbar :=
      Subfield.mul_mem _ hbtilde_mem hzpow_mem
    have hb1 : ((btilde : ↥σ.K) : F) ≠ 0 := by
      rw [Ne, ZeroMemClass.coe_eq_zero]; exact Units.ne_zero btilde
    have hzm1 : (((zbar ^ m : Fˣ)) : F) ≠ 0 := Units.ne_zero _
    have hbval_ne : (⟨((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F), hbval_mem⟩
        : ↥(σ.nextField zbar)) ≠ 0 := by
      rw [Ne, ← ZeroMemClass.coe_eq_zero]
      exact mul_ne_zero hb1 hzm1
    set b : (↥(σ.nextField zbar))ˣ := Units.mk0 _ hbval_ne with hb
    have hbF : ((b : ↥(σ.nextField zbar)) : F)
        = ((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) := rfl
    refine ⟨b, ?_⟩
    intro c hcFQ
    obtain ⟨c₁, hc₁F, hc₁FQ⟩ := hFQtransfer c hcFQ
    -- the (S6a) coset realizer `C` at `(w̃, c₁)`
    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := hbtilde c₁ hc₁FQ
    have hCw : σ.w C = σ.w (Bd j) := by
      rw [σ.hStretch C hC0 hCc, hCν, hwt, hγstretch]
    -- the single-slot realizer and its (parent) weight
    have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
    have hBmul0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 hΦj
    have hBmulc : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hjN
    have hwB : σ.w (C * σ.Φ ^ j) = ν := by
      rw [v7_w_mul_keyPow σ C hC0 j, hCw, ← hνdecomp]
    -- the parent residual, then the digit: linear in the orbit scalar
    have hRB : σ.R (C * σ.Φ ^ j)
        = LaurentPolynomial.C ((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) * LaurentPolynomial.T m := by
      rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add, hm, hwt]
    have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
        = (((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) := by
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
      rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
      rfl
    -- read off `D.Rc` via the S5′ pin and match the scalar to `c·b`
    obtain ⟨c', hc'R, hc'F⟩ := D.hS5' (C * σ.Φ ^ j) hBmul0 hBmulc
    have hscalar : (c' : ↥(σ.nextField zbar))
        = ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
      show (((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F)
          = ((c : ↥(σ.nextField zbar)) : F) * ((b : ↥(σ.nextField zbar)) : F)
      rw [hbF, Units.val_mul, MulMemClass.coe_mul, hc₁F, ← mul_assoc]
    refine ⟨C * σ.Φ ^ j, hBmul0, hBmulc, hwB, ?_⟩
    rw [hc'R, hscalar, hwB]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V7_stripDischarge
----- END FILE: lean/LeanUrat/HC1/V7_stripDischarge.lean -----

----- FILE: lean/LeanUrat/HC1/V8_childResidual.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSiii_R3

/-!
# HC1.V8_childResidual — S9w-(i) via the explicit descent carrier (blueprint §10, V8)

V′-KERNEL unit (blueprint §10.1), the DESCENT instance of (†) — the honest §9.5
core: the explicit carrier

  `Rc f := Σ_{j minimizing childW} C(⟨digPrime z̄ (B_j), mem⟩)·T(j·s′ − t′·σ.w B_j)`

(choice-packaged against `ChildResData`'s pins — `hS5′` is the single-slot case
DEFINITIONALLY: `mfun ≡ 0` is CORRECT per §10 Key Finding 2's first bullet — the
strip mismatch was hS6a's transcription, never the pin; `hRPhi` the slot-1 case)
satisfies the FULL `ChildResLaws`:

* **(a)** additive legs hR0/hRne/hRadd/hRlt/hRneg + w_jump: slot-min ties (S2's
  hSMW), position-injectivity across tied slots, parent hRadd/hRlt slotwise;
  hRne needs D.3(d) (ψ ∤ R(B), width < g — on disk as `L3_digPrime_nonzero`)
  for digit nonvanishing and F′[z^{±1}]-domain for sums.  difficulty: medium.
* **(b)** hRmul: the bilinear slot expansion; per-pair monic division
  `B_j·B″_k = Q_{jk}·Φ̂ + R_{jk}`; `L3_DIV` gives `R_{jk} ≠ 0`, exact weight,
  digit product; Q-terms strictly deeper by th's (I-aug) (D.7(i) verbatim);
  tied (j,k)-pairs land at ONE position `(j+k)s′ − t′(σ.w B_j + σ.w B″_k)` and
  SUM as the Laurent product's convolution coefficient; a vanishing convolution
  coefficient = a parent-residual cancellation = the SAME zero on both sides
  (the D.1(b) δ-calculus, MOVES 2305–2313).  difficulty: HARD, every
  ingredient displayed + on disk.
* **(c)** w_strict (S9w conjunct (ii)): S9a's in-file hwult pattern + strict
  slot domination.  difficulty: short.

DEMOTION NOTE (§10): in the TOTAL (evaluated) V′ coordinate the carry cocycle is
INVISIBLE — z̄^{e·⌊k/e⌋+ρ} recombines, positions add exactly, and hRmul needs
only `L3_DIV`'s evaluated identity.  The proved D-layer (D1–D8, `cmul`, `digD`)
is the GRADED certificate of the alignment's well-definedness; it is NOT
load-bearing here.  "hRmul via D7's cmul law + L3_DIV" reads, post-design:
via L3_DIV; D7 certifies.

moves_ref: D.6 Lemma DIV (MOVES 2299–2322), D.7(i)–(iii) (2331–2352),
D.7(vi)–(vii) normalization (2392–2418). deps: V0 (shape only), S2, S3, L3_DIV,
L3_liftMonic, L3_digPrime_nonzero, L4_TRANSii/iii, th.  **NOT dependent on V5**
(the carrier + laws never mention hS6a).  UNBLOCKS: S9w → S9r (already reduced),
the S9a census's carrier legs; kills the S9w cone's sorryAx.

**P-PHASE COMPLETE (2026-07-28, second escalation): V8a, V8b, V8c ALL PROVED —
zero sorry, Lean-core footprint on every theorem including the capstone.**
The construction: the explicit carrier `v8Rc` ((†) on THE Fact-A/B development,
`0` at `f = 0`) + the private **graded-residue calculus `v8gr`** (the D.1(b) tie
laws — parent hRadd/hRlt + StageCore w_strict/w_jump/R_neg — packaged as one
additive map on the zero-or-`w ≥ ω` domain), which reduces every per-slot digit
claim to a two-line computation.  hRmul = the L4_TRANSiii product development
`Cdev` (re-derived at digit level; those helpers are private) + `L3_DIV`
per-pair remainders + (I-aug) depth for carried quotients + the `v8gr` slot
computation + the Laurent convolution regroup (`Finset.sum_fiberwise_of_maps_to`);
a vanishing convolution coefficient is the SAME zero on both sides via D.3(d)
digit-nonvanishing (the D.1(b) δ-calculus, exactly as the header route displays).
V8c was proved at the first escalation and MOVED above V8a/V8b (its strict law
feeds V8b's hRlt leg through `V8c_wStrict`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open scoped Classical in
/-- **The explicit descent carrier display** (§10 V8, the (†) formula at the descent
instance): on every nonzero f with Φ̂-development data, the carrier value is the
minimizing-slot sum `Σ_j C(dig′(B_j))·T(j·s′ − t′·σ.w B_j)` — digits the parent
ψ-digits (z̄-evaluation, landing in K′ = K⟮z̄⟯), positions the (S5′) law at the
child pair.  Stated as a Prop ON a carrier (the choice-packaging precedent);
well-defined across developments by Fact B uniqueness. -/
def ExplicitDescentCarrier {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
    {zbar : Fˣ} {s' t' : ℤ} (D : ChildResData σ Φhat e' h' zbar s' t') : Prop :=
  ∀ (f : Polynomial ℤ_[p]), f ≠ 0 → ∀ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ),
    IsDevelopment Φhat f B N →
    ∃ cdig : ℕ → ↥(σ.nextField zbar),
      (∀ j, ((cdig j : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar (B j)) ∧
      D.Rc f = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0 ∧
          (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f),
        LaurentPolynomial.C (cdig j) *
          LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))

/-- **V8b ATOM 1 (tied-slot position injectivity — the hRne crux):** on childW-tied
slots, the child position map `j ↦ j·s′ − t′·w_j` is injective (the Bézout collapse:
`d = d·(e′s′ + h′t′)` telescopes to 0 through the tie and position equations).
Escalation round 2026-07-28; PROVED. -/
theorem V8_tiedPos_inj {e' h' : ℕ} {s' t' : ℤ}
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    {j₁ j₂ : ℕ} {w₁ w₂ : ℤ}
    (htie : (e' : ℤ) * w₁ + (j₁ : ℤ) * (h' : ℤ) = (e' : ℤ) * w₂ + (j₂ : ℤ) * (h' : ℤ))
    (hpos : (j₁ : ℤ) * s' - t' * w₁ = (j₂ : ℤ) * s' - t' * w₂) :
    j₁ = j₂ ∧ (e' : ℤ) * w₁ = (e' : ℤ) * w₂ := by
  have hjZ : (j₁ : ℤ) = (j₂ : ℤ) := by
    linear_combination ((j₂ : ℤ) - (j₁ : ℤ)) * hbez' + (e' : ℤ) * hpos + t' * htie
  have hj : j₁ = j₂ := by exact_mod_cast hjZ
  refine ⟨hj, ?_⟩
  rw [hjZ] at htie
  linarith

/-- **V8b ATOM 2 (digit membership):** the z̄-evaluation of any current-field Laurent
polynomial lands in the child field `K′ = K⟮z̄⟯` (`LaurentPolynomial.induction_on`:
constants via `K ≤ K′`, the `T ±1` steps via `z̄, z̄⁻¹ ∈ K′`).
Escalation round 2026-07-28; PROVED. -/
theorem V8_eval₂_mem_nextField (σ : Stage p F) (zbar : Fˣ)
    (l : LaurentPolynomial ↥σ.K) :
    LaurentPolynomial.eval₂ σ.K.subtype zbar l ∈ σ.nextField zbar := by
  have hz : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
  induction l using LaurentPolynomial.induction_on with
  | h_C a =>
      rw [LaurentPolynomial.eval₂_C]
      exact σ.le_nextField zbar a.2
  | h_add hp hq =>
      rw [map_add]
      exact add_mem hp hq
  | h_C_mul_T n a ih =>
      have hsplit : (LaurentPolynomial.C a * LaurentPolynomial.T ((n : ℤ) + 1)) =
          (LaurentPolynomial.C a * LaurentPolynomial.T (n : ℤ)) * LaurentPolynomial.T 1 := by
        rw [mul_assoc, ← LaurentPolynomial.T_add]
      rw [hsplit, map_mul, LaurentPolynomial.eval₂_T]
      exact mul_mem ih (by simpa using hz)
  | h_C_mul_T_Z n a ih =>
      have hsplit : (LaurentPolynomial.C a * LaurentPolynomial.T (-(n : ℤ) - 1)) =
          (LaurentPolynomial.C a * LaurentPolynomial.T (-(n : ℤ))) *
            LaurentPolynomial.T (-1) := by
        rw [mul_assoc, ← LaurentPolynomial.T_add]
        ring_nf
      rw [hsplit, map_mul, LaurentPolynomial.eval₂_T]
      refine mul_mem ih ?_
      rw [zpow_neg_one, Units.val_inv_eq_inv_val]
      exact inv_mem hz

/-- **V8b ATOM 3 (the digit-unit lift — hS5′/hRne's scalar):** for a nonzero
sub-Φ̂-degree coefficient `B`, the parent ψ-digit `dig′(B)` is realized by a UNIT of
the child field `K′` (membership by atom 2; nonvanishing by `L3_digPrime_nonzero`,
D.3(d)).  Escalation round 2026-07-28; PROVED. -/
theorem V8_digitUnit (σ : Stage p F)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBd : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ∃ c' : (↥(σ.nextField zbar))ˣ,
      ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := by
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  have hmem : σ.digPrime zbar B ∈ σ.nextField zbar :=
    V8_eval₂_mem_nextField σ zbar (σ.R B)
  have hne : σ.digPrime zbar B ≠ 0 :=
    L3_digPrime_nonzero σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar B hB hBd
  have hne' : (⟨σ.digPrime zbar B, hmem⟩ : ↥(σ.nextField zbar)) ≠ 0 := by
    intro h0
    exact hne (congrArg Subtype.val h0)
  exact ⟨Units.mk0 _ hne', rfl⟩

/-! ### P-phase infrastructure (2026-07-28 escalation; blueprint §10.1 V8 P-phase)

Private helpers, in dependency order: parent w-arithmetic (the `L4_TRANSiii`
private-helper pattern, re-derived here since those are `private`); the
**graded-residue calculus** `v8gr` — the D.1(b) tie laws (`hRadd`/`hRlt` +
StageCore's `w_strict`/`w_jump`/`R_neg`) packaged as ONE additive map on the
"zero-or-`w ≥ ω`" domain, which is what turns every per-slot digit claim into a
two-line computation; development plumbing (sum/neg/single-slot/key
developments); digits landing in `K′` (`v8cdig`); and the explicit carrier
`v8Rc` (the (†) formula) with its development-independence spec `v8Rc_eq`
(Fact B) and the position-injectivity nonvanishing `v8dsum_ne`. -/

section V8Infra

variable (σ : Stage p F)

private lemma v8w_one : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

private lemma v8w_neg (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : σ.w (-f) = σ.w f := by
  have hne : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) hne hne
    rw [neg_mul_neg, one_mul] at h
    have h1 := v8w_one σ
    omega
  have h := σ.hwmul (-1) f hne hf
  rw [neg_one_mul] at h
  omega

/-- ultrametric finite-sum lower bound (zeros allowed among the summands). -/
private lemma v8sum_w_ge {ι : Type*} (S : Finset ι) (a : ι → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty => intro hm hsum; simp at hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ σ.w (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ σ.w (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        exact le_trans (le_min h1 h2) (σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum)

/-- "zero, or `w`-deep at least `ω`" — the domain of the level-`ω` graded residue. -/
private def v8Deep (ω : ℤ) (x : Polynomial ℤ_[p]) : Prop := x = 0 ∨ ω ≤ σ.w x

open scoped Classical in
/-- **the graded residue at level `ω`**: `R x` on the `w = ω` stratum, `0` elsewhere. -/
private noncomputable def v8gr (ω : ℤ) (x : Polynomial ℤ_[p]) : LaurentPolynomial ↥σ.K :=
  if x ≠ 0 ∧ σ.w x = ω then σ.R x else 0

private lemma v8gr_zero (ω : ℤ) : v8gr σ ω 0 = 0 := by
  unfold v8gr; rw [if_neg]; rintro ⟨h, -⟩; exact h rfl

private lemma v8gr_eq {ω : ℤ} {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hw : σ.w x = ω) :
    v8gr σ ω x = σ.R x := by
  unfold v8gr; rw [if_pos ⟨hx, hw⟩]

private lemma v8gr_deep {ω : ℤ} {x : Polynomial ℤ_[p]} (hw : σ.w x ≠ ω) :
    v8gr σ ω x = 0 := by
  unfold v8gr; rw [if_neg]; rintro ⟨-, h⟩; exact hw h

private lemma v8gr_spec {ω : ℤ} {x : Polynomial ℤ_[p]} (h : v8gr σ ω x ≠ 0) :
    x ≠ 0 ∧ σ.w x = ω := by
  by_contra hcon
  exact h (by unfold v8gr; rw [if_neg hcon])

/-- The graded residue is additive on the `Deep ω` domain (closed under `+`): the
D.1(b) tie calculus in one lemma — `hRadd` at ties, `hRlt`/`w_strict` at strict
drops, `w_jump` at weight jumps, `R_neg` at exact cancellations. -/
private lemma v8gr_add (hσ : StageCore σ) {ω : ℤ} {x y : Polynomial ℤ_[p]}
    (hx : v8Deep σ ω x) (hy : v8Deep σ ω y) :
    v8Deep σ ω (x + y) ∧ v8gr σ ω (x + y) = v8gr σ ω x + v8gr σ ω y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, v8gr_zero, zero_add]; exact ⟨hy, rfl⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, v8gr_zero, add_zero]; exact ⟨hx, rfl⟩
  have hxw : ω ≤ σ.w x := hx.resolve_left hx0
  have hyw : ω ≤ σ.w y := hy.resolve_left hy0
  rcases eq_or_ne (x + y) 0 with hxy0 | hxy0
  · -- exact cancellation: `y = −x`
    have hyx : y = -x := eq_neg_of_add_eq_zero_right hxy0
    refine ⟨Or.inl hxy0, ?_⟩
    rw [hxy0, v8gr_zero]
    rcases eq_or_ne (σ.w x) ω with hwx | hwx
    · have hwy : σ.w y = ω := by rw [hyx, v8w_neg σ x hx0]; exact hwx
      rw [v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy, hyx, hσ.R_neg, add_neg_cancel]
    · have hwy : σ.w y ≠ ω := by rw [hyx, v8w_neg σ x hx0]; exact hwx
      rw [v8gr_deep σ hwx, v8gr_deep σ hwy, add_zero]
  have hult := σ.hwult x y hx0 hy0 hxy0
  have hDeep : v8Deep σ ω (x + y) := Or.inr (le_trans (le_min hxw hyw) hult)
  refine ⟨hDeep, ?_⟩
  rcases eq_or_ne (σ.w x) ω with hwx | hwx
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- both at level ω: hRadd at a tie, w_jump at a jump
      rcases eq_or_ne (σ.w (x + y)) ω with hwxy | hwxy
      · rw [v8gr_eq σ hxy0 hwxy, v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy]
        exact σ.hRadd x y hx0 hy0 hxy0 (by rw [hwx, hwy]) (by rw [hwxy, hwx])
      · have hwge : ω ≤ σ.w (x + y) := le_trans (le_min hxw hyw) hult
        have hj : σ.w x < σ.w (x + y) := by omega
        rw [v8gr_deep σ hwxy, v8gr_eq σ hx0 hwx, v8gr_eq σ hy0 hwy]
        exact (hσ.w_jump x y hx0 hy0 hxy0 (by rw [hwx, hwy]) hj).symm
    · -- x at ω, y strictly deeper: hRlt + w_strict
      have hlt : σ.w x < σ.w y := by omega
      have hws := hσ.w_strict x y hx0 hy0 hlt
      rw [v8gr_eq σ hxy0 (by rw [hws, hwx]), v8gr_eq σ hx0 hwx, v8gr_deep σ hwy, add_zero]
      exact σ.hRlt x y hx0 hy0 hxy0 hlt
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- y at ω, x strictly deeper: symmetric
      have hlt : σ.w y < σ.w x := by omega
      have hws := hσ.w_strict y x hy0 hx0 hlt
      have hyx0 : y + x ≠ 0 := by rwa [add_comm]
      rw [v8gr_deep σ hwx, zero_add, add_comm x y,
        v8gr_eq σ hyx0 (by rw [hws, hwy]), v8gr_eq σ hy0 hwy]
      exact σ.hRlt y x hy0 hx0 hyx0 hlt
    · -- both strictly deeper
      have hgt : ω < σ.w (x + y) := by
        have h1 : ω < σ.w x := by omega
        have h2 : ω < σ.w y := by omega
        exact lt_of_lt_of_le (lt_min h1 h2) hult
      rw [v8gr_deep σ (by omega : σ.w (x + y) ≠ ω), v8gr_deep σ hwx, v8gr_deep σ hwy, add_zero]

/-- finite-sum graded additivity. -/
private lemma v8gr_sum (hσ : StageCore σ) {ω : ℤ} {ι : Type*} (S : Finset ι)
    (a : ι → Polynomial ℤ_[p]) (h : ∀ j ∈ S, v8Deep σ ω (a j)) :
    v8Deep σ ω (∑ j ∈ S, a j) ∧ v8gr σ ω (∑ j ∈ S, a j) = ∑ j ∈ S, v8gr σ ω (a j) := by
  classical
  revert h
  induction S using Finset.induction with
  | empty =>
    intro h
    simp only [Finset.sum_empty]
    exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
  | insert i T hiT ih =>
    intro h
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
    obtain ⟨hD, hE⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨hD', hE'⟩ := v8gr_add σ hσ (h i (Finset.mem_insert_self i T)) hD
    exact ⟨hD', by rw [hE', hE]⟩

/-- developments add slotwise. -/
private lemma v8dev_add {Φ : Polynomial ℤ_[p]} {f g : Polynomial ℤ_[p]}
    {B B' : ℕ → Polynomial ℤ_[p]} {N N' : ℕ}
    (h : IsDevelopment Φ f B N) (h' : IsDevelopment Φ g B' N') :
    IsDevelopment Φ (f + g) (fun j => B j + B' j) (max N N') := by
  refine ⟨fun j => lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (h.1 j) (h'.1 j)),
    fun j hj => ?_, ?_⟩
  · show B j + B' j = 0
    rw [h.2.1 j (le_trans (le_max_left _ _) hj), h'.2.1 j (le_trans (le_max_right _ _) hj),
      add_zero]
  · have hf2 : f = ∑ j ∈ Finset.range (max N N'), B j * Φ ^ j := by
      rw [h.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))) ?_
      intro j _ hj
      rw [h.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    have hg2 : g = ∑ j ∈ Finset.range (max N N'), B' j * Φ ^ j := by
      rw [h'.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))) ?_
      intro j _ hj
      rw [h'.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    rw [hf2, hg2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_mul])

/-- developments negate slotwise. -/
private lemma v8dev_neg {Φ : Polynomial ℤ_[p]} {f : Polynomial ℤ_[p]}
    {B : ℕ → Polynomial ℤ_[p]} {N : ℕ} (h : IsDevelopment Φ f B N) :
    IsDevelopment Φ (-f) (fun j => -(B j)) N := by
  refine ⟨fun j => by rw [Polynomial.degree_neg]; exact h.1 j,
    fun j hj => by show -(B j) = 0; rw [h.2.1 j hj, neg_zero], ?_⟩
  calc -f = -∑ j ∈ Finset.range N, B j * Φ ^ j := by rw [← h.2.2]
    _ = ∑ j ∈ Finset.range N, -(B j * Φ ^ j) := by rw [Finset.sum_neg_distrib]
    _ = ∑ j ∈ Finset.range N, -(B j) * Φ ^ j :=
        Finset.sum_congr rfl fun j _ => (neg_mul (B j) (Φ ^ j)).symm

/-- the single-slot development of a coefficient. -/
private lemma v8dev_single {Φ B : Polynomial ℤ_[p]} (hΦ : Φ ≠ 0) (hB : inC Φ B) :
    IsDevelopment Φ B (fun j => if j = 0 then B else 0) 1 := by
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h0 : j = 0
    · subst h0
      simpa using (show B.degree < Φ.degree from hB)
    · simpa [h0] using hbot
  · show (if j = 0 then B else 0) = 0
    rw [if_neg (by omega : j ≠ 0)]
  · simp

/-- the 2-slot development of the key itself: `Φ = 0·Φ⁰ + 1·Φ¹`. -/
private lemma v8dev_key {Φ : Polynomial ℤ_[p]} (hmon : Φ.Monic) (hd1 : 1 ≤ Φ.natDegree) :
    IsDevelopment Φ Φ (fun j => if j = 1 then 1 else 0) 2 := by
  have hΦ : Φ ≠ 0 := hmon.ne_zero
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  have hdpos : (0 : WithBot ℕ) < Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ]
    exact_mod_cast hd1
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h1 : j = 1
    · simpa [h1, Polynomial.degree_one] using hdpos
    · simpa [h1] using hbot
  · show (if j = 1 then 1 else 0) = 0
    rw [if_neg (by omega : j ≠ 1)]
  · simp [Finset.sum_range_succ]

/-- attained slot minima are unique. -/
private lemma v8slotMin_unique {m m' : ℤ} {N : ℕ} {sw : ℕ → ℤ} {nz : ℕ → Prop}
    (h : SlotMinAttained m N sw nz) (h' : SlotMinAttained m' N sw nz) : m = m' := by
  obtain ⟨j, hj, hjnz, hje⟩ := h.2
  obtain ⟨k, hk, hknz, hke⟩ := h'.2
  have h1 := h.1 k hk hknz
  have h2 := h'.1 j hj hjnz
  omega

/-- every `z̄`-evaluation of a `↥K`-Laurent polynomial lands in `K′ = K⟮z̄⟯`. -/
private lemma v8dig_mem (zbar : Fˣ) (q : LaurentPolynomial ↥σ.K) :
    LaurentPolynomial.eval₂ σ.K.subtype zbar q ∈ σ.nextField zbar := by
  induction q using LaurentPolynomial.induction_on' with
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | C_mul_T n a =>
    rw [LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
    have hz : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
    exact mul_mem (σ.le_nextField zbar (SetLike.coe_mem a)) (zpow_mem hz n)

/-- the parent digit as an element of `K′`. -/
private noncomputable def v8cdig (zbar : Fˣ) (B : Polynomial ℤ_[p]) :
    ↥(σ.nextField zbar) :=
  ⟨σ.digPrime zbar B, v8dig_mem σ zbar (σ.R B)⟩

private lemma v8cdig_coe (zbar : Fˣ) (B : Polynomial ℤ_[p]) :
    ((v8cdig σ zbar B : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := rfl

/-- digit multiplicativity on nonzero inputs (the L3_DIV (★) step). -/
private lemma v8dig_mul (zbar : Fˣ) {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    σ.digPrime zbar (f * g) = σ.digPrime zbar f * σ.digPrime zbar g := by
  simp only [Stage.digPrime]
  rw [σ.hRmul f g hf hg, map_mul]

open scoped Classical in
/-- the tied-slot sum: digits at `childW`-minimizing slots, positions per the child
Bézout pair — the body of the (†) carrier on one development. -/
private noncomputable def v8dsum (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
    (s' t' : ℤ) (m : ℤ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) :
    LaurentPolynomial ↥(σ.nextField zbar) :=
  ∑ j ∈ (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m),
    LaurentPolynomial.C (v8cdig σ zbar (B j)) *
      LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))

open scoped Classical in
/-- **the explicit descent carrier** (§10 (†), descent instance), as a total function:
the tied-slot sum of THE development (Fact A/B) at the `childW` value; `0` at `f = 0`. -/
private noncomputable def v8Rc (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
    (s' t' : ℤ) (f : Polynomial ℤ_[p]) : LaurentPolynomial ↥(σ.nextField zbar) :=
  if hf : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment Φhat f BN.1 BN.2
  then v8dsum σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f) hf.2.choose.1 hf.2.choose.2
  else 0

private lemma v8Rc_zero (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) (s' t' : ℤ) :
    v8Rc σ Φhat e' h' zbar s' t' 0 = 0 := by
  unfold v8Rc
  rw [dif_neg]
  rintro ⟨h, -⟩; exact h rfl

/-- `v8dsum` ignores padding beyond the last nonzero slot. -/
private lemma v8dsum_ext (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) (s' t' : ℤ)
    (m : ℤ) {B : ℕ → Polynomial ℤ_[p]} {N N₂ : ℕ} (hN : N ≤ N₂)
    (hvan : ∀ j, N ≤ j → B j = 0) :
    v8dsum σ Φhat e' h' zbar s' t' m B N₂ = v8dsum σ Φhat e' h' zbar s' t' m B N := by
  unfold v8dsum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hBj, he⟩
    refine ⟨?_, hBj, he⟩
    by_contra hc
    exact hBj (hvan j (le_of_not_gt hc))
  · rintro ⟨hj, hBj, he⟩
    exact ⟨lt_of_lt_of_le hj hN, hBj, he⟩

/-- **the carrier spec** (Fact B independence): on any development of a nonzero `f`,
`v8Rc f` IS the tied-slot sum of that development. -/
private lemma v8Rc_eq {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) {f : Polynomial ℤ_[p]} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hf : f ≠ 0) (hdev : IsDevelopment Φhat f B N) :
    v8Rc σ Φhat e' h' zbar s' t' f
      = v8dsum σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f) B N := by
  have hex : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment Φhat f BN.1 BN.2 :=
    ⟨hf, ⟨(B, N), hdev⟩⟩
  unfold v8Rc
  rw [dif_pos hex]
  have hdev₀ : IsDevelopment Φhat f hex.2.choose.1 hex.2.choose.2 := hex.2.choose_spec
  have hBeq : hex.2.choose.1 = B := funext (L0_FactB_unique Φhat hmon f hdev₀ hdev)
  rw [← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left hex.2.choose.2 N) hdev₀.2.1, hBeq,
    v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right hex.2.choose.2 N) hdev.2.1]

/-- position injectivity across tied slots: `e′·pos(j) = j − t′·m`, so positions
determine slots (Bézout). -/
private lemma v8pos_inj {e' h' : ℕ} {s' t' m : ℤ}
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) {j k : ℕ} {wj wk : ℤ}
    (hj : (e' : ℤ) * wj + (j : ℤ) * (h' : ℤ) = m)
    (hk : (e' : ℤ) * wk + (k : ℤ) * (h' : ℤ) = m)
    (hp : (j : ℤ) * s' - t' * wj = (k : ℤ) * s' - t' * wk) : j = k := by
  have h1 : (e' : ℤ) * ((j : ℤ) * s' - t' * wj) = (j : ℤ) - t' * m := by
    linear_combination (-t') * hj + (j : ℤ) * hbez'
  have h2 : (e' : ℤ) * ((k : ℤ) * s' - t' * wk) = (k : ℤ) - t' * m := by
    linear_combination (-t') * hk + (k : ℤ) * hbez'
  rw [hp] at h1
  have h3 : (j : ℤ) = (k : ℤ) := by linarith [h1.symm.trans h2]
  exact_mod_cast h3

/-- the tied-slot sum is nonzero once one tied slot exists: distinct positions
(`v8pos_inj`), nonzero digits (D.3(d) via `L3_digPrime_nonzero`). -/
private lemma v8dsum_ne (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ) (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    {m : ℤ} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hdeg : ∀ j, (B j).degree < Φhat.degree)
    {j₀ : ℕ} (hj₀N : j₀ < N) (hj₀nz : B j₀ ≠ 0)
    (hj₀m : (e' : ℤ) * σ.w (B j₀) + (j₀ : ℤ) * (h' : ℤ) = m) :
    v8dsum σ Φhat e' h' zbar s' t' m B N ≠ 0 := by
  classical
  have hdigne : ∀ j, B j ≠ 0 → σ.digPrime zbar (B j) ≠ 0 := by
    intro j hj
    refine L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar (B j) hj ?_
    rw [← hΦd]
    exact Polynomial.natDegree_lt_natDegree hj (hdeg j)
  intro hcon
  unfold v8dsum at hcon
  set T := (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m) with hT
  have hj₀T : j₀ ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj₀N, hj₀nz, hj₀m⟩
  simp_rw [← LaurentPolynomial.single_eq_C_mul_T] at hcon
  have hcon' : (∑ j ∈ T, Finsupp.single ((j : ℤ) * s' - t' * σ.w (B j))
      (v8cdig σ zbar (B j)) : ℤ →₀ ↥(σ.nextField zbar)) = 0 := hcon
  have happ := DFunLike.congr_fun hcon' ((j₀ : ℤ) * s' - t' * σ.w (B j₀))
  rw [Finset.sum_apply'] at happ
  simp only [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at happ
  rw [Finset.sum_eq_single j₀] at happ
  · rw [if_pos rfl] at happ
    exact hdigne j₀ hj₀nz (by simpa [v8cdig, Subtype.ext_iff] using happ)
  · intro b hb hbne
    rw [if_neg]
    intro hpe
    have hbT := hb
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hbT
    exact hbne (v8pos_inj hbez' hbT.2.2 hj₀m hpe)
  · intro hnot
    exact absurd hj₀T hnot

/-! #### slot-value ↔ parent-weight converters (the `e′ > 0` cancellations) -/

private lemma v8Deep_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : x = 0 ∨ m ≤ (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ)) : v8Deep σ ω x := by
  rcases hx with h | h
  · exact Or.inl h
  · right
    have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
    have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * σ.w x := by linarith
    exact le_of_mul_le_mul_left h2 he0

private lemma v8w_eq_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) = m) : σ.w x = ω := by
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  have h2 : (e' : ℤ) * σ.w x = (e' : ℤ) * ω := by linarith
  exact mul_left_cancel₀ he0.ne' h2

private lemma v8w_ne_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) ≠ m) : σ.w x ≠ ω := by
  intro hc
  exact hx (by rw [hc]; exact hω)

/-! #### `childW` at the distinguished elements -/

/-- `childW` at the key: `w′(Φ̂) = h′` (slot-1 arithmetic on the 2-slot development). -/
private lemma v8cw_key {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w) :
    childW σ Φhat e' h' Φhat = (h' : ℤ) := by
  have hatt := hSMW Φhat _ 2 hmon.ne_zero (v8dev_key hmon hd1)
  refine v8slotMin_unique hatt ⟨?_, ?_⟩
  · intro j hj hnz
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with rfl | rfl
    · exfalso
      apply hnz
      show (if 0 = 1 then (1 : Polynomial ℤ_[p]) else 0) = 0
      rw [if_neg (by omega : (0 : ℕ) ≠ 1)]
    · show (h' : ℤ) ≤ (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, v8w_one σ]
      push_cast
      omega
  · refine ⟨1, by omega, ?_, ?_⟩
    · show (if 1 = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0
      rw [if_pos rfl]
      exact one_ne_zero
    · show (h' : ℤ) = (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, v8w_one σ]
      push_cast
      omega

/-- `childW` is negation-invariant. -/
private lemma v8cw_neg {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    childW σ Φhat e' h' (-f) = childW σ Φhat e' h' f := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  have hatt := hSMW f B N hf hdev
  have hattn := hSMW (-f) _ N (neg_ne_zero.mpr hf) (v8dev_neg hdev)
  have hattn' : SlotMinAttained (childW σ Φhat e' h' (-f)) N
      (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0) := by
    obtain ⟨hlo, jj, hjj, hjjnz, hjje⟩ := hattn
    have hjjB : B jj ≠ 0 := fun h0 => hjjnz (show -(B jj) = 0 by rw [h0, neg_zero])
    constructor
    · intro j hj hnz
      have h := hlo j hj (show -(B j) ≠ 0 from neg_ne_zero.mpr hnz)
      simpa only [v8w_neg σ (B j) hnz] using h
    · exact ⟨jj, hjj, hjjB, by simpa only [v8w_neg σ (B jj) hjjB] using hjje⟩
  exact v8slotMin_unique hattn' hatt

/-- `dig′(1) = 1` (idempotent nonzero element of the field `F`). -/
private lemma v8dig_one (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg1 : 1 ≤ g) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) :
    σ.digPrime zbar (1 : Polynomial ℤ_[p]) = 1 := by
  have hpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hne : σ.digPrime zbar (1 : Polynomial ℤ_[p]) ≠ 0 :=
    L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar 1 one_ne_zero (by simpa using hpos)
  have hsq : σ.digPrime zbar (1 : Polynomial ℤ_[p]) * σ.digPrime zbar 1
      = σ.digPrime zbar 1 * 1 := by
    rw [← v8dig_mul σ zbar one_ne_zero one_ne_zero, mul_one, mul_one]
  exact mul_left_cancel₀ hne hsq

/-! #### the two `ChildResData` pins for the explicit carrier -/

/-- the D.3(b) key pin: `v8Rc(Φ̂) = z^{s′}`. -/
private lemma v8Rc_phi (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg1 : 1 ≤ g) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w) :
    v8Rc σ Φhat e' h' zbar s' t' Φhat = LaurentPolynomial.T s' := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hΦne (v8dev_key hmon hd1)]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_one]
  have h0cond : ¬((if (0 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 1 then 1 else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' Φhat) := by
    rintro ⟨h0, -⟩
    exact h0 (by rw [if_neg (by omega : (0 : ℕ) ≠ 1)])
  have h1cond : (if (1 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (1 : ℕ) = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' Φhat := by
    rw [if_pos rfl, v8cw_key σ hmon hd1 e' h' hSMW, v8w_one σ]
    refine ⟨one_ne_zero, ?_⟩
    push_cast
    omega
  rw [if_neg h0cond, if_pos h1cond, zero_add]
  have hred : ((fun j : ℕ => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 1) = 1 := by
    norm_num
  rw [hred]
  have hcd1 : v8cdig σ zbar (1 : Polynomial ℤ_[p]) = 1 := by
    apply Subtype.ext
    rw [v8cdig_coe, v8dig_one σ ψ g hg hψ hψz hg1 zbar hzbar]
    rfl
  rw [hcd1, map_one, one_mul, v8w_one σ]
  norm_num

/-- the S5′ pin: single-slot coefficients carry the parent digit at position
`−t′·σ.w B` (the `mfun ≡ 0` normalization — DEFINITIONAL for the explicit carrier). -/
private lemma v8Rc_S5' (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC Φhat B) :
    ∃ c' : (↥(σ.nextField zbar))ˣ,
      v8Rc σ Φhat e' h' zbar s' t' B
        = LaurentPolynomial.C ((c' : ↥(σ.nextField zbar))) *
            LaurentPolynomial.T (- t' * σ.w B) ∧
      ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hcw : childW σ Φhat e' h' B = (e' : ℤ) * σ.w B :=
    L4_TRANSii σ Φhat e' h' _ hSMW B hB hBc
  have hdigne : σ.digPrime zbar B ≠ 0 :=
    L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar B hB
      (by rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB hBc)
  have hcne : v8cdig σ zbar B ≠ 0 := fun h0 => hdigne (congrArg Subtype.val h0)
  refine ⟨Units.mk0 _ hcne, ?_, rfl⟩
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hB (v8dev_single hΦne hBc)]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_range_one]
  have h0cond : (if (0 : ℕ) = 0 then B else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 0 then B else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' B := by
    rw [if_pos rfl, hcw]
    exact ⟨hB, by push_cast; ring⟩
  rw [if_pos h0cond]
  have hred : ((fun j : ℕ => if j = 0 then B else 0) 0) = B := by norm_num
  rw [hred]
  show LaurentPolynomial.C (v8cdig σ zbar B) *
      LaurentPolynomial.T (((0 : ℕ) : ℤ) * s' - t' * σ.w B) = _
  norm_num

/-! #### the easy law legs: hRne, hRneg -/

/-- hRne: the carrier is nonvanishing on nonzero inputs. -/
private lemma v8Rc_ne (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (s' t' : ℤ) (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    v8Rc σ Φhat e' h' zbar s' t' f ≠ 0 := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨-, j₀, hj₀N, hj₀nz, hj₀e⟩ := hSMW f B N hf hdev
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdev]
  exact v8dsum_ne σ ψ g hg hψ hψz zbar hzbar hΦd e' h' s' t' hbez' hdev.1 hj₀N hj₀nz hj₀e.symm

/-- hRneg: the carrier is odd (parent `R_neg` slotwise; positions and ties are
negation-invariant). -/
private lemma v8Rc_negLaw (hσ : StageCore σ) (zbar : Fˣ)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    (f : Polynomial ℤ_[p]) :
    v8Rc σ Φhat e' h' zbar s' t' (-f) = - v8Rc σ Φhat e' h' zbar s' t' f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero, v8Rc_zero, neg_zero]
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdev,
    v8Rc_eq σ hmon e' h' zbar s' t' (neg_ne_zero.mpr hf) (v8dev_neg hdev),
    v8cw_neg σ hmon hd1 e' h' hSMW hf]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if -(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (-(B j))) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (-(B j)))
      else 0)
    = -(if B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (B j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))
      else 0)
  by_cases hBj : B j = 0
  · have hn1 : ¬(-(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 (by rw [hBj, neg_zero])
    have hn2 : ¬(B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 hBj
    rw [if_neg hn1, if_neg hn2, neg_zero]
  · have hwn := v8w_neg σ (B j) hBj
    have hdig : σ.digPrime zbar (-(B j)) = - σ.digPrime zbar (B j) := by
      simp only [Stage.digPrime]
      rw [hσ.R_neg, map_neg]
    have hcd : v8cdig σ zbar (-(B j)) = - v8cdig σ zbar (B j) := by
      apply Subtype.ext
      rw [v8cdig_coe, hdig]
      push_cast
      rfl
    by_cases hc : B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · rw [if_pos hc, if_pos ⟨neg_ne_zero.mpr hBj, by rw [hwn]; exact hc.2⟩,
        hwn, hcd, map_neg, neg_mul]
    · rw [if_neg hc, if_neg (fun hcn => hc ⟨hBj, by rw [← hwn]; exact hcn.2⟩), neg_zero]

/-! #### residue → digit bridges + monic-division sum plumbing -/

private lemma v8dig_ne_of_deg (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hxd : x.degree < Φhat.degree) :
    σ.digPrime zbar x ≠ 0 :=
  L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar x hx
    (by rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hx hxd)

private lemma v8dig_of_Radd (zbar : Fˣ) {x a b : Polynomial ℤ_[p]}
    (h : σ.R x = σ.R a + σ.R b) :
    σ.digPrime zbar x = σ.digPrime zbar a + σ.digPrime zbar b := by
  simp only [Stage.digPrime]
  rw [h, map_add]

private lemma v8dig_of_Req (zbar : Fˣ) {x a : Polynomial ℤ_[p]} (h : σ.R x = σ.R a) :
    σ.digPrime zbar x = σ.digPrime zbar a := by
  simp only [Stage.digPrime]
  rw [h]

/-- `%ₘ` is additive (monic divisor). -/
private lemma v8add_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic)
    (a b : Polynomial ℤ_[p]) : (a + b) %ₘ q = a %ₘ q + b %ₘ q := by
  have ha := Polynomial.modByMonic_add_div a q
  have hb := Polynomial.modByMonic_add_div b q
  refine (Polynomial.div_modByMonic_unique (a /ₘ q + b /ₘ q) (a %ₘ q + b %ₘ q) hq
    ⟨?_, ?_⟩).2
  · linear_combination ha + hb
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (Polynomial.degree_modByMonic_lt a hq) (Polynomial.degree_modByMonic_lt b hq))

/-- `%ₘ` distributes over finite sums (monic divisor). -/
private lemma v8sum_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic) {ι : Type*}
    (S : Finset ι) (a : ι → Polynomial ℤ_[p]) :
    (∑ j ∈ S, a j) %ₘ q = ∑ j ∈ S, (a j %ₘ q) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i T hiT ih =>
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT, v8add_modByMonic hq, ih]

/-! #### the three D.1(b) tie laws for the explicit carrier (per-slot `v8gr` calculus) -/

/-- hRadd: at a childW tie with no jump, the carrier adds. -/
private lemma v8Rc_addLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ Φhat e' h' f = childW σ Φhat e' h' g')
    (hSum : childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) :
    v8Rc σ Φhat e' h' zbar s' t' (f + g')
      = v8Rc σ Φhat e' h' zbar s' t' f + v8Rc σ Φhat e' h' zbar s' t' g' := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, hSum, ← hEq,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0)
  -- slot lower bounds (∨-form) for both halves, keyed to the common tie level
  have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  have hDg : Bg j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hEq ▸ hming j ?_ h0)
      by_contra hc
      exact h0 (hdevg.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- both tied at slot j; ω := σ.w (Bf j)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hge
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v8gr_eq σ hf0 rfl, v8gr_eq σ hg0 hwg] at hgr
      by_cases hd : v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) = 0
      · -- digit cancellation: the sum slot is NOT tied; the two terms cancel
        have hdF : σ.digPrime zbar (Bf j) + σ.digPrime zbar (Bg j) = 0 := by
          rw [← v8cdig_coe σ zbar (Bf j), ← v8cdig_coe σ zbar (Bg j)]
          exact_mod_cast congrArg Subtype.val hd
        have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
              = childW σ Φhat e' h' f) := by
          rintro ⟨hs0, hse⟩
          have hws : σ.w (Bf j + Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hse
          have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
            rw [← v8gr_eq σ hs0 hws]; exact hgr
          refine v8dig_ne_of_deg σ ψ g hg hψ hψz zbar hzbar hΦd hs0
            (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
              (max_lt (hdevf.1 j) (hdevg.1 j))) ?_
          rw [v8dig_of_Radd σ zbar hRs]
          exact hdF
        rw [if_neg hnotied, if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg,
          ← add_mul, ← map_add, hd, map_zero, zero_mul]
      · -- no cancellation: the sum slot is tied, digits add
        have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
          rw [hgr]
          intro h0
          apply hd
          apply Subtype.ext
          have : ((v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) :
              ↥(σ.nextField zbar)) : F)
              = LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Bf j) + σ.R (Bg j)) := by
            rw [map_add]
            rfl
          rw [this, h0, map_zero]
          rfl
        obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
        have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
          rw [← v8gr_eq σ hs0 hws]; exact hgr
        have hcds : v8cdig σ zbar (Bf j + Bg j)
            = v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) := by
          apply Subtype.ext
          rw [v8cdig_coe, v8dig_of_Radd σ zbar hRs]
          push_cast
          rfl
        rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩,
          if_pos ⟨hg0, hge⟩, hws, hwg, hcds, map_add, add_mul]
    · -- f tied, g not: the g half is invisible at level ω
      have hgrg : v8gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v8Deep_of_slot σ he' hfe hDg)).2
      rw [v8gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
      have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hf0
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
        rw [← v8gr_eq σ hs0 hws]; exact hgr
      have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bf j) :=
        Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
      rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, if_neg hjg,
        add_zero, hws, hcds]
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- g tied, f not: mirror
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v8gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v8gr_eq σ hg0 rfl, hgrf, zero_add] at hgr
      have hgrne : v8gr σ (σ.w (Bg j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hg0
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bg j) := by
        rw [← v8gr_eq σ hs0 hws]; exact hgr
      have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bg j) :=
        Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
      rw [if_pos ⟨hs0, by rw [hws]; exact hge⟩, if_neg hjf,
        if_pos ⟨hg0, hge⟩, zero_add, hws, hcds]
    · -- neither tied: the sum slot cannot be tied either
      have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
            = childW σ Φhat e' h' f) := by
        rintro ⟨hs0, hse⟩
        have hgrf : v8gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
          rcases eq_or_ne (Bf j) 0 with h0 | h0
          · rw [h0, v8gr_zero]
          · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjf ⟨h0, hce⟩
        have hgrg : v8gr σ (σ.w (Bf j + Bg j)) (Bg j) = 0 := by
          rcases eq_or_ne (Bg j) 0 with h0 | h0
          · rw [h0, v8gr_zero]
          · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjg ⟨h0, hce⟩
        have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hse hDf)
          (v8Deep_of_slot σ he' hse hDg)).2
        rw [v8gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
        exact σ.hRne _ hs0 hgr
      rw [if_neg hnotied, if_neg hjf, if_neg hjg, add_zero]

/-- w_jump: at a childW tie whose sum jumps, the carriers cancel. -/
private lemma v8Rc_jumpLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ Φhat e' h' f = childW σ Φhat e' h' g')
    (hJump : childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g')) :
    v8Rc σ Φhat e' h' zbar s' t' f + v8Rc σ Φhat e' h' zbar s' t' g' = 0 := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  obtain ⟨hminC, -⟩ := hSMW (f + g') _ (max Nf Ng) hfg hdevC
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, ← hEq,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  show (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0) = 0
  have hjN : j < max Nf Ng := Finset.mem_range.mp hj
  -- a tied sum-slot at the pre-jump level contradicts the jump
  have hnoslot : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f →
      v8gr σ ω (Bf j + Bg j) = 0 := by
    intro ω hω
    by_contra hne
    obtain ⟨hs0, hws⟩ := v8gr_spec σ hne
    have hle : childW σ Φhat e' h' (f + g')
        ≤ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ) := hminC j hjN hs0
    rw [hws] at hle
    omega
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- both tied: residues must cancel (else the sum slot survives at the old level)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v8w_eq_of_slot σ he' hfe hge
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v8gr_eq σ hf0 rfl, v8gr_eq σ hg0 hwg, hnoslot (σ.w (Bf j)) hfe] at hgr
      -- hgr : 0 = R (Bf j) + R (Bg j)
      have hcds : v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) = 0 := by
        apply Subtype.ext
        have : ((v8cdig σ zbar (Bf j) + v8cdig σ zbar (Bg j) :
            ↥(σ.nextField zbar)) : F)
            = LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Bf j) + σ.R (Bg j)) := by
          rw [map_add]
          rfl
        rw [this, ← hgr, map_zero]
        rfl
      rw [if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg, ← add_mul, ← map_add, hcds,
        map_zero, zero_mul]
    · -- f tied alone: its residue would survive — contradiction
      exfalso
      have hgrg : v8gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hDg : Bg j = 0 ∨ childW σ Φhat e' h' f
          ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hEq ▸ hming j ?_ h0)
          by_contra hc
          exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v8Deep_of_slot σ he' hfe hDg)).2
      rw [v8gr_eq σ hf0 rfl, hgrg, add_zero, hnoslot (σ.w (Bf j)) hfe] at hgr
      exact σ.hRne _ hf0 hgr.symm
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
    · -- g tied alone: mirror contradiction
      exfalso
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v8gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
          ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hminf j ?_ h0)
          by_contra hc
          exact h0 (hdevf.2.1 j (le_of_not_gt hc))
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v8gr_eq σ hg0 rfl, hgrf, zero_add, hnoslot (σ.w (Bg j)) hge] at hgr
      exact σ.hRne _ hg0 hgr.symm
    · rw [if_neg hjf, if_neg hjg, add_zero]

/-- hRlt: below a strictly deeper summand, the carrier is unchanged. -/
private lemma v8Rc_ltLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hLt : childW σ Φhat e' h' f < childW σ Φhat e' h' g')
    (hStr : childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) :
    v8Rc σ Φhat e' h' zbar s' t' (f + g') = v8Rc σ Φhat e' h' zbar s' t' f := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  have hdevC : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v8dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf, hStr,
    ← v8dsum_ext σ Φhat e' h' zbar s' t' (childW σ Φhat e' h' f)
      (le_max_left Nf Ng) hdevf.2.1]
  unfold v8dsum
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
      then LaurentPolynomial.C (v8cdig σ zbar (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
  -- the g half is strictly deep at every pre-level slot
  have hgdeep : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f →
      v8gr σ ω (Bg j) = 0 ∧ (Bg j = 0 ∨ ω ≤ σ.w (Bg j)) := by
    intro ω hω
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact ⟨by rw [h0, v8gr_zero], Or.inl h0⟩
    · have hjNg : j < Ng := by
        by_contra hc
        exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgt : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) < (e' : ℤ) * σ.w (Bg j)
          + (j : ℤ) * (h' : ℤ) := by
        have h1 : childW σ Φhat e' h' g'
            ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := hming j hjNg h0
        omega
      have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
      have hwgt : ω < σ.w (Bg j) := by
        have h2 : (e' : ℤ) * ω < (e' : ℤ) * σ.w (Bg j) := by omega
        exact lt_of_mul_lt_mul_left h2 he0.le
      exact ⟨v8gr_deep σ (ne_of_gt hwgt), Or.inr hwgt.le⟩
  have hDf : Bf j = 0 ∨ childW σ Φhat e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ Φhat e' h' f
  · -- f tied: sum slot tied with f's digit and weight
    obtain ⟨hf0, hfe⟩ := hjf
    obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j)) hfe
    have hgr := (v8gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j)))) hDg).2
    rw [v8gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
    have hgrne : v8gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
      rw [hgr]; exact σ.hRne _ hf0
    obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
    have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
      rw [← v8gr_eq σ hs0 hws]; exact hgr
    have hcds : v8cdig σ zbar (Bf j + Bg j) = v8cdig σ zbar (Bf j) :=
      Subtype.ext (by rw [v8cdig_coe, v8cdig_coe]; exact v8dig_of_Req σ zbar hRs)
    rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, hws, hcds]
  · -- f untied: the sum slot cannot be tied
    have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f) := by
      rintro ⟨hs0, hse⟩
      obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j + Bg j)) hse
      have hgrf : v8gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v8gr_zero]
        · refine v8gr_deep σ (v8w_ne_of_slot σ he' hse ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v8gr_add σ hσ (v8Deep_of_slot σ he' hse hDf) hDg).2
      rw [v8gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
      exact σ.hRne _ hs0 hgr
    rw [if_neg hnotied, if_neg hjf]

/-! #### hRmul — the bilinear slot expansion through `L3_DIV` (blueprint §10 V8(b);
the honest §9.5 core).  Route: the product development `Cdev` by convolution + monic
division (the `L4_TRANSiii` construction, re-derived at digit level since those
helpers are private); per-diagonal, the graded residue of `Cdev m` at the level
forced by `childW`-multiplicativity is EXACTLY the sum of the tied-pair remainder
residues (`L3_DIV` weights + (I-aug) for the carried quotients); evaluation at z̄
turns this into the Laurent product's convolution coefficient, with a vanishing
coefficient = the SAME zero on both sides (the D.1(b) δ-calculus — here: a tied
sum-slot with zero digit would contradict D.3(d) digit-nonvanishing). -/
private lemma v8Rc_mulLaw (hσ : StageCore σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ)
    (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0)
    {Φhat : Polynomial ℤ_[p]} (hlift : IsStandardLift σ ψ g Φhat)
    (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree)
    (hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (e' h' : ℕ) (he' : 1 ≤ e') (hcop : Nat.gcd e' h' = 1) (hiaug : IAug σ Φhat e' h')
    (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) :
    v8Rc σ Φhat e' h' zbar s' t' (f * g')
      = v8Rc σ Φhat e' h' zbar s' t' f * v8Rc σ Φhat e' h' zbar s' t' g' := by
  classical
  have hfg : f * g' ≠ 0 := mul_ne_zero hf hg'
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hg1 : 1 ≤ g := by rw [← hg]; exact hψ.natDegree_pos
  have hdpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hWmul : childW σ Φhat e' h' (f * g')
      = childW σ Φhat e' h' f + childW σ Φhat e' h' g' :=
    L4_TRANSiii σ ψ g Φhat hlift hψ hψz hmon zbar hzbar e' h' hcop _ hSMW hiaug
      f g' hf hg' hfg
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 g'
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  have hBfz : ∀ j, Nf ≤ j → Bf j = 0 := hdevf.2.1
  have hBgz : ∀ k, Ng ≤ k → Bg k = 0 := hdevg.2.1
  have hNf1 : 1 ≤ Nf := by
    by_contra hcon
    have h0 : Nf = 0 := by omega
    have := hdevf.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hf this
  have hNg1 : 1 ≤ Ng := by
    by_contra hcon
    have h0 : Ng = 0 := by omega
    have := hdevg.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hg' this
  -- ===== the generating polynomials and the convolution (the L4_TRANSiii block) =====
  set FF : Polynomial (Polynomial ℤ_[p]) :=
    ∑ j ∈ Finset.range Nf, Polynomial.C (Bf j) * Polynomial.X ^ j with hFFdef
  set GG : Polynomial (Polynomial ℤ_[p]) :=
    ∑ k ∈ Finset.range Ng, Polynomial.C (Bg k) * Polynomial.X ^ k with hGGdef
  have hFFc : ∀ m, FF.coeff m = Bf m := by
    intro m
    rw [hFFdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Nf
    · rw [Finset.sum_eq_single m]
      · simp
      · intro j hj hjm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBfz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro j hj
      have hmj : m ≠ j := by
        have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmj]
  have hGGc : ∀ m, GG.coeff m = Bg m := by
    intro m
    rw [hGGdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Ng
    · rw [Finset.sum_eq_single m]
      · simp
      · intro k hk hkm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hkm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBgz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro k hk
      have hmk : m ≠ k := by
        have := Finset.mem_range.mp hk; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmk]
  have hFFeval : Polynomial.eval Φhat FF = f := by
    rw [hFFdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevf.2.2.symm
  have hGGeval : Polynomial.eval Φhat GG = g' := by
    rw [hGGdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevg.2.2.symm
  have hFFnd : FF.natDegree ≤ Nf - 1 := by
    rw [hFFdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hj
    omega
  have hGGnd : GG.natDegree ≤ Ng - 1 := by
    rw [hGGdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hk
    omega
  set H : Polynomial (Polynomial ℤ_[p]) := FF * GG with hHdef
  have hHnd : H.natDegree ≤ Nf + Ng - 2 := by
    rw [hHdef]
    refine le_trans Polynomial.natDegree_mul_le ?_
    omega
  have hHcoeff : ∀ m, H.coeff m = ∑ jk ∈ Finset.antidiagonal m, Bf jk.1 * Bg jk.2 := by
    intro m
    rw [hHdef, Polynomial.coeff_mul]
    exact Finset.sum_congr rfl (fun jk _ => by rw [hFFc, hGGc])
  have hHvan : ∀ m, Nf + Ng - 1 ≤ m → H.coeff m = 0 := by
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hprodsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), H.coeff m * Φhat ^ m := by
    rw [← hFFeval, ← hGGeval, ← Polynomial.eval_mul, ← hHdef]
    exact Polynomial.eval_eq_sum_range' (by omega) Φhat
  -- ===== the development of f·g': remainders on the diagonal, carried quotients shifted =====
  set Cdev : ℕ → Polynomial ℤ_[p] := fun m =>
    H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) with hCdef
  have hCdev_eq : ∀ m, Cdev m
      = H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) := fun m => rfl
  have hBfnd : ∀ j, (Bf j).natDegree ≤ Φhat.natDegree - 1 := by
    intro j
    by_cases hz : Bf j = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevf.1 j)
      omega
  have hBgnd : ∀ k, (Bg k).natDegree ≤ Φhat.natDegree - 1 := by
    intro k
    by_cases hz : Bg k = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevg.1 k)
      omega
  have hHcnd : ∀ m, (H.coeff m).natDegree ≤ 2 * Φhat.natDegree - 2 := by
    intro m
    rw [hHcoeff m]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro jk hjk
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hBfnd jk.1
    have h2 := hBgnd jk.2
    omega
  have hQdeg : ∀ m, (H.coeff m /ₘ Φhat).degree < Φhat.degree := by
    intro m
    have hnd : (H.coeff m /ₘ Φhat).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_divByMonic _ hmon]
      have h2 := hHcnd m
      omega
    calc (H.coeff m /ₘ Φhat).degree
        ≤ ((H.coeff m /ₘ Φhat).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (Φhat.natDegree : WithBot ℕ) := by exact_mod_cast hnd
      _ = Φhat.degree := (Polynomial.degree_eq_natDegree hΦne).symm
  have hCdeg : ∀ m, (Cdev m).degree < Φhat.degree := by
    intro m
    rw [hCdev_eq m]
    by_cases hm : m = 0
    · rw [if_pos hm, add_zero]
      exact Polynomial.degree_modByMonic_lt _ hmon
    · rw [if_neg hm]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact Polynomial.degree_modByMonic_lt _ hmon
      · exact hQdeg (m - 1)
  have hCvan : ∀ m, Nf + Ng ≤ m → Cdev m = 0 := by
    intro m hm
    rw [hCdev_eq m]
    have hm0 : m ≠ 0 := by omega
    rw [if_neg hm0, hHvan m (by omega), hHvan (m - 1) (by omega),
      Polynomial.zero_modByMonic, Polynomial.zero_divByMonic, add_zero]
  have hCsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, Nf + Ng = N₁ + 1 := ⟨Nf + Ng - 1, by omega⟩
    have hz2 : H.coeff N₁ = 0 := hHvan N₁ (by omega)
    have hsplit : ∀ m, Cdev m * Φhat ^ m
        = (H.coeff m %ₘ Φhat) * Φhat ^ m
          + (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      intro m
      rw [hCdev_eq m]
      by_cases hm : m = 0
      · simp only [if_pos hm]
        rw [add_zero, add_zero]
      · simp only [if_neg hm]
        rw [add_mul]
    have hshift : (∑ m ∈ Finset.range (Nf + Ng),
          (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m))
        = ∑ m ∈ Finset.range (Nf + Ng), (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1) := by
      rw [hN₁]
      rw [Finset.sum_range_succ'
        (fun m => if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) N₁]
      rw [Finset.sum_range_succ (fun m => (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1)) N₁]
      rw [if_pos rfl, add_zero, hz2, Polynomial.zero_divByMonic, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    rw [hprodsum]
    have e1 : ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m
        = (∑ m ∈ Finset.range (Nf + Ng), (H.coeff m %ₘ Φhat) * Φhat ^ m)
          + ∑ m ∈ Finset.range (Nf + Ng),
              (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => hsplit m)
    rw [e1, hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    conv_lhs => rw [← Polynomial.modByMonic_add_div (H.coeff m) Φhat]
    ring
  have hdevC : IsDevelopment Φhat (f * g') Cdev (Nf + Ng) := ⟨hCdeg, hCvan, hCsum⟩
  -- ===== Lemma DIV wrapper (weight + digit) =====
  have hDIV : ∀ (a b : Polynomial ℤ_[p]), a ≠ 0 → b ≠ 0 →
      a.degree < Φhat.degree → b.degree < Φhat.degree →
      (a * b) %ₘ Φhat ≠ 0 ∧ σ.w ((a * b) %ₘ Φhat) = σ.w a + σ.w b ∧
        σ.digPrime zbar ((a * b) %ₘ Φhat) = σ.digPrime zbar a * σ.digPrime zbar b := by
    intro a b ha hb had hbd
    have had' : a.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree ha had
    have hbd' : b.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hb hbd
    have hRd' : ((a * b) %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
      by_cases hz : (a * b) %ₘ Φhat = 0
      · rw [hz]; simpa using hdpos
      · rw [← hΦd]
        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hmon)
    have hdiv : a * b = ((a * b) /ₘ Φhat) * Φhat + (a * b) %ₘ Φhat := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div (a * b) Φhat]
      ring
    exact L3_DIV σ ψ g hg hψ hψz Φhat hlift zbar hzbar a b ha hb had' hbd' _ _ hdiv hRd'
  -- ===== per-pair slot arithmetic =====
  have hpairw : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      childW σ Φhat e' h' f + childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) + (m' : ℤ) * (h' : ℤ) := by
    intro m' jk hd hBf hBg
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ Φhat e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    linarith
  have hpair_tie : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      ∀ ω : ℤ, (e' : ℤ) * ω + (m' : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      (σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω
        ↔ ((e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f
           ∧ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ)
              = childW σ Φhat e' h' g')) := by
    intro m' jk hd hBf hBg ω hω
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ Φhat e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ Φhat e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    constructor
    · intro hsum
      have hkey : (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2)
          + (m' : ℤ) * (h' : ℤ)
          = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
        rw [← hexp, hsum]
        exact hω
      constructor
      · linarith
      · linarith
    · rintro ⟨ht1, ht2⟩
      have hkey : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) = (e' : ℤ) * ω := by
        linarith
      exact mul_left_cancel₀ he0.ne' hkey
  -- ===== the carried quotient is strictly deep (I-aug) =====
  have hQdeep : ∀ (m' : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + ((m' : ℤ) + 1) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      H.coeff m' /ₘ Φhat ≠ 0 → ω < σ.w (H.coeff m' /ₘ Φhat) := by
    intro m' ω hω hy
    have hbound : ∀ jk ∈ Finset.antidiagonal m', Bf jk.1 * Bg jk.2 = 0 ∨
        ω + σ.w Φhat + 1 ≤ σ.w (Bf jk.1 * Bg jk.2) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · exact Or.inl hPz
      right
      have hBf := left_ne_zero_of_mul hPz
      have hBg := right_ne_zero_of_mul hPz
      have hp := hpairw m' jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
      have hwP : σ.w (Bf jk.1 * Bg jk.2) = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
        σ.hwmul _ _ hBf hBg
      rw [hwP]
      by_contra hcon
      push_neg at hcon
      have hS : σ.w (Bf jk.1) + σ.w (Bg jk.2) ≤ ω + σ.w Φhat := by omega
      have hmul : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
          ≤ (e' : ℤ) * (ω + σ.w Φhat) :=
        mul_le_mul_of_nonneg_left hS (Int.natCast_nonneg e')
      have hexp : (e' : ℤ) * (ω + σ.w Φhat) = (e' : ℤ) * ω + (e' : ℤ) * σ.w Φhat := by
        ring
      have hia : (e' : ℤ) * σ.w Φhat < (h' : ℤ) := hiaug
      linarith
    have hconv_ne : H.coeff m' ≠ 0 := fun h0 => hy (by rw [h0, Polynomial.zero_divByMonic])
    have hwconv : ω + σ.w Φhat + 1 ≤ σ.w (H.coeff m') := by
      rw [hHcoeff m']
      refine v8sum_w_ge σ _ _ _ (fun jk hjk hne0 => (hbound jk hjk).resolve_left hne0)
        (by rw [← hHcoeff m']; exact hconv_ne)
    have hyΦ : Φhat * (H.coeff m' /ₘ Φhat) = H.coeff m' + -(H.coeff m' %ₘ Φhat) := by
      have hmd := Polynomial.modByMonic_add_div (H.coeff m') Φhat
      linear_combination hmd
    have hΦyne : Φhat * (H.coeff m' /ₘ Φhat) ≠ 0 := mul_ne_zero hΦne hy
    have hwΦy : ω + σ.w Φhat + 1 ≤ σ.w (Φhat * (H.coeff m' /ₘ Φhat)) := by
      rw [hyΦ]
      by_cases hrz : H.coeff m' %ₘ Φhat = 0
      · rw [hrz, neg_zero, add_zero]; exact hwconv
      · have hrw : ω + σ.w Φhat + 1 ≤ σ.w (H.coeff m' %ₘ Φhat) := by
          have hremsum : H.coeff m' %ₘ Φhat
              = ∑ jk ∈ Finset.antidiagonal m', (Bf jk.1 * Bg jk.2) %ₘ Φhat := by
            rw [hHcoeff m']
            exact v8sum_modByMonic hmon _ _
          rw [hremsum]
          refine v8sum_w_ge σ _ _ _ ?_ (by rw [← hremsum]; exact hrz)
          intro jk hjk hne0
          have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
            intro h0; rw [h0, Polynomial.zero_modByMonic] at hne0; exact hne0 rfl
          have hBf := left_ne_zero_of_mul hPne
          have hBg := right_ne_zero_of_mul hPne
          have hw_eq := (hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)).2.1
          rw [hw_eq]
          have hb := (hbound jk hjk).resolve_left hPne
          rw [σ.hwmul _ _ hBf hBg] at hb
          exact hb
        have hnegne : -(H.coeff m' %ₘ Φhat) ≠ 0 := neg_ne_zero.mpr hrz
        have hsumne : H.coeff m' + -(H.coeff m' %ₘ Φhat) ≠ 0 := by
          rw [← hyΦ]; exact hΦyne
        have hult := σ.hwult _ _ hconv_ne hnegne hsumne
        rw [v8w_neg σ _ hrz] at hult
        exact le_trans (le_min hwconv hrw) hult
    have hmulw := σ.hwmul Φhat (H.coeff m' /ₘ Φhat) hΦne hy
    rw [hmulw] at hwΦy
    omega
  -- ===== the graded slot computation: grw of Cdev m = the tied-pair residue sum =====
  have hgrC : ∀ (m : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' →
      v8gr σ ω (Cdev m)
        = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
    intro m ω hω
    have hCm : Cdev m = (∑ jk ∈ Finset.antidiagonal m, (Bf jk.1 * Bg jk.2) %ₘ Φhat)
        + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) := by
      rw [hCdev_eq m, hHcoeff m, v8sum_modByMonic hmon]
    have hQpack : v8Deep σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat)
        ∧ v8gr σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) = 0 := by
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
        exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
      · rw [if_neg hm0]
        by_cases hy : H.coeff (m - 1) /ₘ Φhat = 0
        · rw [hy]
          exact ⟨Or.inl rfl, v8gr_zero σ ω⟩
        · have hω' : (e' : ℤ) * ω + (((m - 1 : ℕ) : ℤ) + 1) * (h' : ℤ)
              = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
            have hc : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by omega
            rw [hc]; exact hω
          have hlt := hQdeep (m - 1) ω hω' hy
          exact ⟨Or.inr hlt.le, v8gr_deep σ (ne_of_gt hlt)⟩
    have hDeepR : ∀ jk ∈ Finset.antidiagonal m,
        v8Deep σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · rw [hPz, Polynomial.zero_modByMonic]
        exact Or.inl rfl
      · have hBf := left_ne_zero_of_mul hPz
        have hBg := right_ne_zero_of_mul hPz
        obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
        right
        rw [hrw]
        have hp := hpairw m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
        have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) := by
          linarith
        exact le_of_mul_le_mul_left h2 he0
    obtain ⟨hDsum, hEsum⟩ := v8gr_sum σ hσ (Finset.antidiagonal m) _ hDeepR
    have hEtot := (v8gr_add σ hσ hDsum hQpack.1).2
    rw [hCm, hEtot, hEsum, hQpack.2, add_zero]
    have hstep1 : ∑ jk ∈ Finset.antidiagonal m, v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat)
        = ∑ jk ∈ (Finset.antidiagonal m).filter
            (fun jk => (Bf jk.1 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)
            ∧ (Bg jk.2 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
            v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro jk hjk hne
      obtain ⟨hrne, hrw⟩ := v8gr_spec σ hne
      have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
        intro h0; rw [h0, Polynomial.zero_modByMonic] at hrne; exact hrne rfl
      have hBf := left_ne_zero_of_mul hPne
      have hBg := right_ne_zero_of_mul hPne
      obtain ⟨-, hwr, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω := by rw [← hwr]; exact hrw
      have hti := (hpair_tie m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg ω hω).mp hsum
      exact ⟨⟨hBf, hti.1⟩, ⟨hBg, hti.2⟩⟩
    have hstep2 : ∀ jk ∈ (Finset.antidiagonal m).filter
        (fun jk => (Bf jk.1 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)
        ∧ (Bg jk.2 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
        v8gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ Φhat) = σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
      intro jk hjk
      rw [Finset.mem_filter] at hjk
      obtain ⟨hjkd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩ := hjk
      obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω :=
        (hpair_tie m jk (Finset.mem_antidiagonal.mp hjkd) hBf hBg ω hω).mpr ⟨ht1, ht2⟩
      exact v8gr_eq σ hrne (by rw [hrw]; exact hsum)
    rw [hstep1, Finset.sum_congr rfl hstep2]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.ext
    intro jk
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
      have hjNf : jk.1 < Nf := by
        by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
      have hkNg : jk.2 < Ng := by
        by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
      exact ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
    · rintro ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
      exact ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
  -- ===== final assembly: both sides as fiberwise sums over the diagonals =====
  rw [v8Rc_eq σ hmon e' h' zbar s' t' hfg hdevC,
    v8Rc_eq σ hmon e' h' zbar s' t' hf hdevf,
    v8Rc_eq σ hmon e' h' zbar s' t' hg' hdevg, hWmul]
  unfold v8dsum
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  have hmaps : ∀ jk ∈ ((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
      ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
        (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g')),
      jk.1 + jk.2 ∈ Finset.range (Nf + Ng) := by
    intro jk hjk
    rw [Finset.mem_product] at hjk
    obtain ⟨h1, h2⟩ := hjk
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  show (if Cdev m ≠ 0 ∧ (e' : ℤ) * σ.w (Cdev m) + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g'
      then LaurentPolynomial.C (v8cdig σ zbar (Cdev m)) *
        LaurentPolynomial.T ((m : ℤ) * s' - t' * σ.w (Cdev m))
      else 0)
    = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v8cdig σ zbar (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v8cdig σ zbar (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2)))
  rcases Finset.eq_empty_or_nonempty ((((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
      (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
    ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
      (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
    (fun jk => jk.1 + jk.2 = m)) with hFIB | hFIB
  · -- empty fiber: a tied sum-slot would have zero graded residue — impossible
    rw [hFIB, Finset.sum_empty, if_neg ?_]
    rintro ⟨hs0, hse⟩
    have hgr := hgrC m (σ.w (Cdev m)) hse
    rw [hFIB, Finset.sum_empty, v8gr_eq σ hs0 rfl] at hgr
    exact σ.hRne _ hs0 hgr
  · -- nonempty fiber: constant weight-sum ω₀ and position across the fiber
    obtain ⟨jk₀, hjk₀⟩ := hFIB
    have hjk₀' := hjk₀
    rw [Finset.mem_filter, Finset.mem_product] at hjk₀'
    obtain ⟨⟨hj₀mem, hk₀mem⟩, hd₀⟩ := hjk₀'
    rw [Finset.mem_filter, Finset.mem_range] at hj₀mem hk₀mem
    obtain ⟨hj₀Nf, hBf₀, ht₀f⟩ := hj₀mem
    obtain ⟨hk₀Ng, hBg₀, ht₀g⟩ := hk₀mem
    have hω₀ : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) + (m : ℤ) * (h' : ℤ)
        = childW σ Φhat e' h' f + childW σ Φhat e' h' g' := by
      have hcast : (jk₀.1 : ℤ) + (jk₀.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd₀
      have hexp : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))
          = (e' : ℤ) * σ.w (Bf jk₀.1) + (e' : ℤ) * σ.w (Bg jk₀.2) := by ring
      have hch : (jk₀.1 : ℤ) * (h' : ℤ) + (jk₀.2 : ℤ) * (h' : ℤ)
          = (m : ℤ) * (h' : ℤ) := by
        rw [← add_mul, hcast]
      linarith
    -- fiberwise constancy of the weight sum
    have hwconst : ∀ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        σ.w (Bf jk.1) + σ.w (Bg jk.2) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) := by
      intro jk hjk
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, hd⟩ := hjk
      rw [Finset.mem_filter, Finset.mem_range] at hjmem hkmem
      exact (hpair_tie m jk hd hjmem.2.1 hkmem.2.1 _ hω₀).mpr ⟨hjmem.2.2, hkmem.2.2⟩
    -- the RHS fiber sum collapses to C (digit convolution) · T (forced position)
    have hRHS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v8cdig σ zbar (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v8cdig σ zbar (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2))))
      = LaurentPolynomial.C (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2)) *
        LaurentPolynomial.T ((m : ℤ) * s'
          - t' * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      have hw := hwconst jk hjk
      have hd : jk.1 + jk.2 = m := by
        rw [Finset.mem_filter] at hjk
        exact hjk.2
      have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd
      have hcs : (jk.1 : ℤ) * s' + (jk.2 : ℤ) * s' = (m : ℤ) * s' := by
        rw [← add_mul, hcast]
      rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
      congr 2
      rw [← hw]
      linarith
    rw [hRHS]
    -- the digit bridge: eval₂ of the tied residue sum = the digit convolution
    have hevalS : LaurentPolynomial.eval₂ σ.K.subtype zbar
        (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat))
        = ((∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) : ↥(σ.nextField zbar)) : F) := by
      rw [map_sum]
      have hcoe : ((∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) : ↥(σ.nextField zbar)) : F)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          (σ.digPrime zbar (Bf jk.1) * σ.digPrime zbar (Bg jk.2)) := by
        push_cast
        rfl
      rw [hcoe]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, -⟩ := hjk
      rw [Finset.mem_filter] at hjmem hkmem
      have hdig := (hDIV (Bf jk.1) (Bg jk.2) hjmem.2.1 hkmem.2.1
        (hdevf.1 jk.1) (hdevg.1 jk.2)).2.2
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat)) = _
      exact hdig
    have hgr := hgrC m (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) hω₀
    by_cases hS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2)) = 0
    · -- vanishing convolution coefficient: BOTH sides are the same zero
      rw [hS, map_zero, zero_mul, if_neg ?_]
      rintro ⟨hs0, hse⟩
      have hws : σ.w (Cdev m) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) :=
        v8w_eq_of_slot σ he' hω₀ hse
      have hRs := hgr
      rw [v8gr_eq σ hs0 hws] at hRs
      refine v8dig_ne_of_deg σ ψ g hg hψ hψz zbar hzbar hΦd hs0 (hCdeg m) ?_
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Cdev m)) = 0
      rw [hRs, hevalS, hS]
      rfl
    · -- surviving coefficient: the sum slot is tied with digit = the convolution
      have hgrne : v8gr σ (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) (Cdev m) ≠ 0 := by
        rw [hgr]
        intro h0
        apply hS
        apply Subtype.ext
        rw [← hevalS, h0, map_zero]
        rfl
      obtain ⟨hs0, hws⟩ := v8gr_spec σ hgrne
      have hRs : σ.R (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            σ.R ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
        rw [← v8gr_eq σ hs0 hws]
        exact hgr
      have hcdS : v8cdig σ zbar (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ Φhat e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ Φhat e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            v8cdig σ zbar (Bf jk.1) * v8cdig σ zbar (Bg jk.2) := by
        apply Subtype.ext
        rw [v8cdig_coe]
        show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (Cdev m)) = _
        rw [hRs, hevalS]
      rw [if_pos ⟨hs0, by rw [hws]; exact hω₀⟩, hws, hcdS]

end V8Infra

/-- Unit V8(c): the childW-only strict law — S9w's conjunct (ii).  PROVED
(escalation round 2026-07-28): S9a's in-file `hwult` pattern (developments add
slotwise; the parent ultrametric per slot) + the negation trick
`f = (f + g') + (−g')` for the reverse inequality (childW is negation-invariant
slotwise since `σ.w (−B) = σ.w B` for any multiplicative integer valuation).
MOVED above V8a/V8b (2026-07-28 second escalation): V8b's hRlt leg consumes it. -/
theorem V8c_wStrict (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∀ f g', f ≠ 0 → g' ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f := by
  classical
  -- ## Φ̂ is monic of degree ≥ 1 (L3), so the S2 development pack applies
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hdeg1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨hdevMin, hSMW⟩ := S2_childW σ Φhat hmonΦ hdeg1 e' h'
  -- ## parent valuation: negation invariance
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    linarith
  have hwneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have key := σ.hwmul (-1) (-1) hn1 hn1
    rw [neg_one_mul, neg_neg, hw1] at key
    linarith
  have hwB : ∀ B : Polynomial ℤ_[p], B ≠ 0 → σ.w (-B) = σ.w B := by
    intro B hB
    have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h2 := σ.hwmul (-1) B hn1 hB
    rw [neg_one_mul, hwneg1, zero_add] at h2
    exact h2
  -- ## childW negation invariance (slotwise: the negated development has the same slot data)
  have hwnegC : ∀ x : Polynomial ℤ_[p], x ≠ 0 →
      childW σ Φhat e' h' (-x) = childW σ Φhat e' h' x := by
    intro x hx
    obtain ⟨B, N, hdev, hlow0, j0, hj0N, hj0nz, hj0eq⟩ := hdevMin x hx
    have hxneg : (-x : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hx
    have hdevneg : IsDevelopment Φhat (-x) (fun j => -(B j)) N := by
      refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [Polynomial.degree_neg]
        exact hdev.1 j
      · show -(B j) = 0
        rw [hdev.2.1 j hj, neg_zero]
      · calc -x = -∑ j ∈ Finset.range N, B j * Φhat ^ j := by rw [← hdev.2.2]
          _ = ∑ j ∈ Finset.range N, -(B j * Φhat ^ j) := by rw [Finset.sum_neg_distrib]
          _ = ∑ j ∈ Finset.range N, -(B j) * Φhat ^ j :=
              Finset.sum_congr rfl fun j _ => (neg_mul (B j) (Φhat ^ j)).symm
    obtain ⟨hlow1, j1, hj1N, hj1nz, hj1eq⟩ := hSMW (-x) _ N hxneg hdevneg
    have hBj1 : B j1 ≠ 0 := fun h => hj1nz (by simp [h])
    -- ≥: childW(−x) sits at a slot of x's development
    have h1 : childW σ Φhat e' h' x ≤ childW σ Φhat e' h' (-x) := by
      rw [hj1eq]
      simp only [hwB (B j1) hBj1]
      exact hlow0 j1 hj1N hBj1
    -- ≤: childW(x) sits at a slot of (−x)'s development
    have h2 : childW σ Φhat e' h' (-x) ≤ childW σ Φhat e' h' x := by
      rw [hj0eq]
      have h := hlow1 j0 hj0N (by simp [hj0nz])
      simpa only [hwB (B j0) hj0nz] using h
    omega
  -- ## the child ultrametric law (the S9a in-file pattern, verbatim)
  have hwult : ∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g') ≤
        childW σ Φhat e' h' (f + g') := by
    intro f g' hf hg' hfg
    obtain ⟨Bf, Nf, hdf, hmf⟩ := hdevMin f hf
    obtain ⟨Bg, Ng, hdg, hmg⟩ := hdevMin g' hg'
    set N := max Nf Ng with hN
    have hsub_f : Finset.range Nf ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))
    have hsub_g : Finset.range Ng ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))
    have hsum_f : f = ∑ j ∈ Finset.range N, Bf j * Φhat ^ j := by
      rw [hdf.2.2]
      refine Finset.sum_subset hsub_f ?_
      intro j hjN hjNf
      rw [hdf.2.1 j (by simpa using hjNf), zero_mul]
    have hsum_g : g' = ∑ j ∈ Finset.range N, Bg j * Φhat ^ j := by
      rw [hdg.2.2]
      refine Finset.sum_subset hsub_g ?_
      intro j hjN hjNg
      rw [hdg.2.1 j (by simpa using hjNg), zero_mul]
    have hdevS : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) N := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdf.1 j) (hdg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdf.2.1 j (le_trans (le_max_left _ _) hj),
          hdg.2.1 j (le_trans (le_max_right _ _) hj), add_zero]
      · rw [hsum_f, hsum_g, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => (add_mul (Bf j) (Bg j) (Φhat ^ j)).symm
    obtain ⟨hlow, jS, hjSN, hjSnz, hjSeq⟩ := hSMW (f + g') _ N hfg hdevS
    rw [hjSeq]
    by_cases hBf : Bf jS = 0
    · have hBg : Bg jS ≠ 0 := by
        intro hBg
        exact hjSnz (by rw [hBf, hBg, add_zero])
      have hjNg : jS < Ng := by
        by_contra hge
        exact hBg (hdg.2.1 jS (le_of_not_gt hge))
      have hle := (hmg.1) jS hjNg hBg
      have hval : σ.w (Bf jS + Bg jS) = σ.w (Bg jS) := by rw [hBf, zero_add]
      calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
          ≤ childW σ Φhat e' h' g' := min_le_right _ _
        _ ≤ (e' : ℤ) * σ.w (Bg jS) + (jS : ℤ) * (h' : ℤ) := hle
        _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
    · by_cases hBg : Bg jS = 0
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hle := (hmf.1) jS hjNf hBf
        have hval : σ.w (Bf jS + Bg jS) = σ.w (Bf jS) := by rw [hBg, add_zero]
        calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
            ≤ childW σ Φhat e' h' f := min_le_left _ _
          _ ≤ (e' : ℤ) * σ.w (Bf jS) + (jS : ℤ) * (h' : ℤ) := hle
          _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hjNg : jS < Ng := by
          by_contra hge
          exact hBg (hdg.2.1 jS (le_of_not_gt hge))
        have hult := σ.hwult (Bf jS) (Bg jS) hBf hBg hjSnz
        have hlef := (hmf.1) jS hjNf hBf
        have hleg := (hmg.1) jS hjNg hBg
        have he'nn : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
        rcases min_cases (σ.w (Bf jS)) (σ.w (Bg jS)) with ⟨hmin, hcmp⟩ | ⟨hmin, hcmp⟩
        · have : childW σ Φhat e' h' f ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bf jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_left _ _) this
        · have : childW σ Φhat e' h' g' ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bg jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_right _ _) this
  -- ## assembly: strict domination pins the sum's value to the lower side
  intro f g' hf hg' hlt
  have hfg : f + g' ≠ 0 := by
    intro h0
    have hgeq : g' = -f := eq_neg_of_add_eq_zero_right h0
    rw [hgeq, hwnegC f hf] at hlt
    exact lt_irrefl _ hlt
  have hge : childW σ Φhat e' h' f ≤ childW σ Φhat e' h' (f + g') := by
    have h := hwult f g' hf hg' hfg
    rwa [min_eq_left (le_of_lt hlt)] at h
  have hle : childW σ Φhat e' h' (f + g') ≤ childW σ Φhat e' h' f := by
    by_contra hcon
    push_neg at hcon
    have hng : (-g' : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hg'
    have hsum : (f + g') + (-g') = f := by ring
    have h := hwult (f + g') (-g') hfg hng (by rw [hsum]; exact hf)
    rw [hsum, hwnegC g' hg'] at h
    have h1 : childW σ Φhat e' h' f <
        min (childW σ Φhat e' h' (f + g')) (childW σ Φhat e' h' g') :=
      lt_min hcon hlt
    omega
  omega

/-- Unit V8(a): the explicit descent carrier exists with the ADDITIVE law legs —
hR0, hRne, hRadd, hRlt, hRneg + w_jump (the D.1(b) tie laws at childW). -/
theorem V8a_carrierAdditive (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∃ D : ChildResData σ Φhat e' h' zbar s' t',
      ExplicitDescentCarrier D ∧
      (D.Rc 0 = 0) ∧
      (∀ f, f ≠ 0 → D.Rc f ≠ 0) ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
          childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f →
          D.Rc (f + g') = D.Rc f + D.Rc g') ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
          D.Rc (f + g') = D.Rc f) ∧
      (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
          childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
          childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g') →
          D.Rc f + D.Rc g' = 0) ∧
      (∀ f, D.Rc (-f) = - D.Rc f) := by
  classical
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hd1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨-, hSMW⟩ := S2_childW σ Φhat hmonΦ hd1 e' h'
  refine ⟨⟨v8Rc σ Φhat e' h' zbar s' t',
      v8Rc_phi σ ψ g th.hdeg th.hirr th.hne_z th.hg zbar hzbar hmonΦ hd1 e' h' s' t' hSMW,
      fun B hB hBc => v8Rc_S5' σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hΦdeg
        e' h' s' t' hSMW B hB hBc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf B N hdev
    exact ⟨fun j => v8cdig σ zbar (B j), fun j => rfl,
      v8Rc_eq σ hmonΦ e' h' zbar s' t' hf hdev⟩
  · exact v8Rc_zero σ Φhat e' h' zbar s' t'
  · exact fun f hf => v8Rc_ne σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' s' t' hbez' hSMW hf
  · exact fun f g'' hf hg hfg hEq hSum => v8Rc_addLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hSum
  · intro f g'' hf hg hfg hLt
    exact v8Rc_ltLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' th.he' s' t' hSMW hf hg hfg hLt
      (V8c_wStrict σ hσ th s' t' hbez' ht'0 f g'' hf hg hLt)
  · exact fun f g'' hf hg hfg hEq hJump => v8Rc_jumpLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hJump
  · exact fun f => v8Rc_negLaw σ hσ.core zbar hmonΦ hd1 e' h' s' t' hSMW f

/-- Unit V8(b): the explicit descent carrier is FULLY lawful — `ChildResLaws`
including hRmul (the bilinear slot expansion through `L3_DIV`, the honest §9.5
core; see the header for the displayed route). -/
theorem V8b_carrierLaws (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    ∃ D : ChildResData σ Φhat e' h' zbar s' t',
      ExplicitDescentCarrier D ∧ ChildResLaws D := by
  classical
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  obtain ⟨hmonΦ, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hd1 : 1 ≤ Φhat.natDegree := by
    rw [hΦdeg]
    exact Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  obtain ⟨-, hSMW⟩ := S2_childW σ Φhat hmonΦ hd1 e' h'
  refine ⟨⟨v8Rc σ Φhat e' h' zbar s' t',
      v8Rc_phi σ ψ g th.hdeg th.hirr th.hne_z th.hg zbar hzbar hmonΦ hd1 e' h' s' t' hSMW,
      fun B hB hBc => v8Rc_S5' σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hΦdeg
        e' h' s' t' hSMW B hB hBc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf B N hdev
    exact ⟨fun j => v8cdig σ zbar (B j), fun j => rfl,
      v8Rc_eq σ hmonΦ e' h' zbar s' t' hf hdev⟩
  · exact v8Rc_zero σ Φhat e' h' zbar s' t'
  · exact fun f hf => v8Rc_ne σ ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' s' t' hbez' hSMW hf
  · exact fun f g'' hf hg => v8Rc_mulLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar
      hzbar th.hlift hmonΦ hd1 hΦdeg e' h' th.he' th.hcop th.hiaug s' t' hSMW hf hg
  · exact fun f g'' hf hg hfg hEq hSum => v8Rc_addLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hSum
  · intro f g'' hf hg hfg hLt
    exact v8Rc_ltLaw σ hσ.core ψ g th.hdeg th.hirr th.hne_z zbar hzbar hmonΦ hd1 hΦdeg
      e' h' th.he' s' t' hSMW hf hg hfg hLt
      (V8c_wStrict σ hσ th s' t' hbez' ht'0 f g'' hf hg hLt)
  · exact fun f g'' hf hg hfg hEq hJump => v8Rc_jumpLaw σ hσ.core ψ g th.hdeg th.hirr
      th.hne_z zbar hzbar hmonΦ hd1 hΦdeg e' h' th.he' s' t' hSMW hf hg hfg hEq hJump
  · exact fun f => v8Rc_negLaw σ hσ.core zbar hmonΦ hd1 e' h' s' t' hSMW f

/-- Unit V8 (capstone — S9w's EXACT statement shape, assembled from V8b + V8c):
a lawful `ChildResData` carrier exists, and the childW strict law holds.
`S9w_residualLaws` closes from this by `exact` once V8b/V8c land. -/
theorem V8_childResidual (σ : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    (∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) := by
  obtain ⟨D, -, hD⟩ := V8b_carrierLaws σ hσ th s' t' hbez' ht'0
  exact ⟨⟨D, hD⟩, V8c_wStrict σ hσ th s' t' hbez' ht'0⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V8_tiedPos_inj
#print axioms LeanUrat.HC1.V8_eval₂_mem_nextField
#print axioms LeanUrat.HC1.V8_digitUnit
#print axioms LeanUrat.HC1.V8a_carrierAdditive
#print axioms LeanUrat.HC1.V8b_carrierLaws
#print axioms LeanUrat.HC1.V8c_wStrict
#print axioms LeanUrat.HC1.V8_childResidual
----- END FILE: lean/LeanUrat/HC1/V8_childResidual.lean -----

----- FILE: lean/LeanUrat/HC1/V9_K1nonrec.lean -----
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC2.K1_vertexPin

/-!
# HC1.V9_K1nonrec — HC2's K1 kernel residual via the ReadFrame (blueprint §10, V9)

V′-KERNEL unit (blueprint §10.1), the REGRADE instance's payoff: HC2's
`K1_readVertexPin_nonrec` (the ONE remaining HC2 kernel sorry) as a corollary of
the V1–V4 chain.  Assembly route (§10.1 V9, steps (i)–(vi)):

 (i)  extract the read steepness from `HistoryCoherent` (slope law + strict
      steepening → `ν.h > ν.e·σ.h` — the `ReadPair` hypothesis; the short lemma
      `V9_readSteepness` below covers reads with a predecessor; the ROOT read's
      steepness comes from the recorded side data — P-phase);
 (ii) build the `ReadFrame` at (ν.e, ν.h) on σ_i (V1/V2);
 (iii) the recorded `IsNodeLift = IsReadLift` (`isNodeLift_iff`) is V3's
      standard-lift shape — K1(Φ̂/wV) + D.8 at the frame (V4);
 (iv) f's ReadFrame residual IS the recorded side pattern:
      `RV(f) = Σ_k C(pat k)·T(…)` from SideReads (i)+(ii) (the side line
      supports the development with equality exactly at the stride digits — so
      `wV(f) = ν.gam`, attained); its anchor/ord data
      `HasAnchorK (RV f) a★ (pattern-Ranch)` DERIVED from (i)+(ii);
      `ord_ψ(pattern) = ν.μ` read against SideReads (iii) — SEAM, see below;
 (v)  V4's (VERTEX) gives `B_μ ≠ 0` and `wV(B_μ) = gam − μ·ν.e·g·ν.h`, then
      `σ′.w(B_μ) = ν.e·σ.w(B_μ) = wV(B_μ)` via the RECORDED
      child_wPrev/hStretch on the ONE coefficient (no tower reconciliation —
      the kernel's conclusion touches only a child COEFFICIENT's weight);
 (vi) the ℚ-conversion to `STR_{i+1}·line.at(μ·childWidth)` is the γ-tie +
      slope-law arithmetic already PROVED in-file at HC2
      (`K1_SAE_vertexEq_endpoint`'s pattern).

⚠ **SIDEREADS-(iii) ADJUDICATION — THE STANDING E-PHASE FLAG, FENCED** (verbatim
from §10.1 V9): SideReads clause (iii) anchors `σ.R f` — the FRAME residual —
while the landing needs the READ residual `RV(f)`'s ψ-order.  At single-side
reads they agree; at multi-side polygons the frame residual sees the WRONG
slots.  The faithful object is `RV(f)` (§C's side data are side-local); the
DERIVED pattern-anchor route above consumes only (i)+(ii)+the recorded μ, so V9
keys ord_ψ to the PATTERN and treats (iii)'s `σ.R f` rendering as the
U31-gated seam it already is.  **If the gate shows the recorded μ
mis-associates on some run shape, THAT restatement (SideReads (iii) →
RV-vocabulary) is a NEW sign-off item — flagged now, not silently changed.**
This unit does NOT touch `SideReads`.

deps: V1–V4 + the HC2 records. difficulty: medium (assembly).
UNBLOCKS: `K1_readVertexPin` total (close `K1_readVertexPin_nonrec` by `exact`)
→ U20a/U20b/U22-E2 close by the staged one-line consumers.
E-phase: statements per §10.1, `sorry` bodies.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

/-- V9 step (i): the READ STEEPNESS at any read with a predecessor — from
`HistoryCoherent`'s slope law + strict steepening,
`h_i > h_{i−1}·e_i·e_{i−1}·g_{i−1} ≥ e_i·h_{i−1} = e_i·σ_i.h` — the `ReadPair`
steepness hypothesis of the regrade at (ν.e, ν.h) over ν.σ. -/
theorem V9_readSteepness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi : i < H.nodes.length) (hi0 : 1 ≤ i)
    (hsp : (H.nodes[i]'hi).species ≠ ReadSpecies.recentering) :
    ((H.nodes[i]'hi).e : ℤ) * ((H.nodes[i]'hi).σ.h : ℤ)
      < ((H.nodes[i]'hi).h : ℤ) := by
  sorry

/-- Unit V9: the K1 kernel residual — `K1_readVertexPin_nonrec`'s statement
VERBATIM, proved through the ReadFrame chain (route (i)–(vi) in the header).
Once landed, `K1_readVertexPin_nonrec` closes by
`exact V9_K1nonrec h i hi1 hsp B Nd hdev hNd`. -/
theorem V9_K1nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V9_readSteepness
#print axioms LeanUrat.HC1.V9_K1nonrec
----- END FILE: lean/LeanUrat/HC1/V9_K1nonrec.lean -----
=== END SECTION B ===
=== SECTION C: HC1_LEAN_BLUEPRINT_2026-07-28.md, section 10 (lines 1700-end) ===
## 10. THE V′ KERNEL — the read-functional carry algebra in the aligned frame
## (designed 2026-07-28, V′-kernel pass; the ONE design behind every remaining
## hard-core sorry: S9w-(i), S9a's hS6a strip, HC2's K1_readVertexPin_nonrec)

VERDICT FIRST. The three hard residuals are three instances of ONE object —
the D.1(e) residual pack rebuilt at a NEW (e★, h★, s★, t★)-position law over
an existing stage's data, with a scalar transform:

  (†)  wV(f) := min_{j} ( e★·σ.w(B_j) + j·h★ )        (the read functional)
       RV(f) := Σ_{j minimizing} C( φ(slot-j digit) ) · T( j·s★ − t★·σ.w(B_j) )

over the P-development f = Σ B_j·P^j, where the instance is fixed by
(P, (e★,h★,s★,t★), φ):

* DESCENT instance (S9w): P = Φ̂ (the TransHyp lift), (e★,h★) = th's (e′,h′),
  φ = evaluation z ↦ z̄ (= `σ.digPrime zbar`) into K′ = σ.nextField z̄.
  wV = the EXISTING `childW σ Φ̂ e′ h′`; RV = the explicit `childR` carrier.
* REGRADE instance (K1-nonrec): P = σ.Φ (the SAME key), (e★,h★) = the
  RECORDED READ pair (ν.e, ν.h), φ = identity on ↥σ.K.
  wV = `childW σ σ.Φ ν.e ν.h`; RV = the read-graded residual — THE V′ FRAME.

KEY FINDING 1 (the campaign finding the charge asked for — stated LOUDLY,
but it is GOOD news): **the feared B2-DEF gap does not exist.** The
obstruction record at `HC2/K1_vertexPin.lean` item 4 derives the read-pair
vertex law by hand because no note display seems to cover it — but §B2-DEF's
D.3–D.8 are LEVEL-FREE, STAGE-INDEXED displays ("Fix a stage with read index
(e, h)…", MOVES 2017–2019), and the note's stages ALWAYS carry the index of
the side being read. HC2's recorded stages carry their BIRTH pair instead
(HistoryCoherent ties `TransitionCoreL … ν_i.e ν_i.h`; the next node reads a
NEW pair). The read-pair landing is therefore §B2-DEF's OWN D.5 + D.8 run at
the REGRADED frame (†) — an *interface* object HC1 never constructed, not
missing note mathematics. Two verbatim checks:
* The recorded lift is (†)-equal-weight: `IsReadLift` weights
  σ.w(t_k) = h★·(g−k) give e★·σ.w(t_k) + (e★k)·h★ = e★·h★·g for every
  present slot and for the leading slot — EXACTLY D.5's "EQUAL WEIGHTS"
  display (MOVES 2268–2269) transposed to wV; hence
  `IsReadLift σ ψ g e★ h★ Φ̂` IS the standard-lift shape OF THE REGRADED
  FRAME (wVPrev := σ.w, index (e★,h★)) — the D.5 residual computation
  re-runs verbatim to RV(Φ̂) = z^{m̂★}·ψ(z), m̂★ := −t★·h★·g (MOVES 2270–2276).
* The obstruction record's displayed vertex value is D.8-(VERTEX) at (†):
  F(μ) = wV(f) − μ·wV(Φ̂) + μ·h★ = gam − μ·(e★·g − 1)·h★ — the record's
  formula, exactly (Case J sealed this empirically at 12 strata).

KEY FINDING 2 (FORCED Defs adjudication — the strip's real content; SIGN-OFF
REQUIRED, queued as V5 below). `Stage.hS6a`'s untwisted form is an
OVER-TRANSCRIPTION of the note's (S6a). The note's axiom is "every index is
realized … whose digit is c·(THE INDEX'S FORCED MONOMIAL CLASS) with c
ranging over the CONSTANT orbit group O := F_Qˣ" — the orbit group AT ITS
FIXED POINT (D.2, MOVES 1964–1971, rev D⁶/pass-14 finding 1), and D.7(viii)'s
child realizers have dig′ = "c·(a fixed z̄-monomial class)" (MOVES 2431–2435).
The Lean field hard-codes the fixed class to the trivial one. That form is
machine-refuted on the strip (§9.9's S9a record; F₉/F₃ numerics) — and NO
re-pin of `hS5'`/`VertexPin` can rescue it:
* mfun ≡ 0 (the raw z̄-evaluation pin) IS the note's V′ normalization — the
  parent z-class evaluates to the SCALAR z̄ under the frame change
  (D-injectivity on degree-0, D.7(v); the parent pinning identity
  z = V^{−h}Y^{e} pushes to Π dig′(ũ)^{−h·b_i}·dig′(Φ)^{e} = z̄ in F′), so
  the "alignment function" of §9.5 is the ZERO function; and
* any OTHER multiplicative renormalization is a linear twist mfun = m₁·id
  (additivity mod ord(z̄) forces linearity), and the strip windows contain
  only g consecutive twist values λ (slots at weight ν are
  (γ, j) = (s·ν − λ·h, t·ν + λ·e), twist = λ): whenever e.g. σ.e | ord(z̄),
  e·m₁ ≡ −t (mod ord z̄) has no solution (gcd(e, ord z̄) = e ∤ t since
  th ≡ 1 mod e) — the untwisted demand is unsatisfiable at depth ≥ 2, PERIOD.
So the §9.9 queued adjudication resolves: NOT a re-pin (option 1 is vacuous),
NOT a scope-down (option 2 breaks D.7(viii)'s own consumer recursion — the
next TRANS consumes (S6a) realizers at ALL indices, strip included). The
faithful field is the FIXED-POINT COSET form (V5).

KEY FINDING 3 (a second forced interface fact, sized small). The regraded
frame CANNOT be a full `Stage`: its coefficient weights under wVPrev = σ.w
lie in σ.e·ℤ (hStretch), so `Stage.hS6b`'s quantifier "∀ ν > wPrev Φ" (the
D.9(b) cofinite range, true at genuine stages) is UNSATISFIABLE at a regrade
for σ.e > 1. Hence the proved Stage-typed D.8 assets (`L5_landVertex*`)
cannot be cited verbatim at the regrade; the landing re-runs at a PARTIAL
pack (V0's `ReadFrame`), with the L5 files as the worked Lean pattern. All
other fields (hS6a included — regrade scalars are PRESERVED, no z̄ enters at
the same level) do transport; hS6b alone is the blocker.

DEMOTION NOTE (so nobody hunts for a missing lemma): in the TOTAL (evaluated)
V′ coordinate the carry cocycle is INVISIBLE — z̄^{e·⌊k/e⌋ + ρ} recombines,
positions add exactly, and hRmul needs only `L3_DIV`'s evaluated identity.
The proved D-layer (D1–D8, `cmul`, `digD`) is the GRADED certificate of the
alignment's well-definedness (and stays cited by any consumer that needs
positions split mod e_birth); it is NOT load-bearing for V8's product law.
§9.5's "hRmul via D7's cmul law + L3_DIV" reads, post-design: via L3_DIV;
D7 certifies.

### 10.1 The unit DAG (files `HC1/V*_*.lean`, all ADDITIVE; zero axioms;
### `sorry` only as E-phase placeholders inside the new units)

Dependency shape:
  V0 → V1 → V2 → V3 → V4 → V9   (the regrade/K1 chain)
  V0 → V6 → (V5 sign-off) → V7  (the aligned-orbit/strip chain)
  V0 → V8                       (the descent/S9w chain; V8 ⊥ V1–V4)
V5 is a SIGN-OFF EVENT (Defs restatement), not a proof unit; V7 and the
TRANSviii_a repair are gated on it.

* **V0 `DefsV.lean`** (definitions only, no theorems, no sorry).
  - `ReadPair σ e★ h★ s★ t★ : Prop` := 1 ≤ e★ ∧ 1 ≤ h★ ∧ gcd = 1 ∧ Bézout ∧
    (e★ = 1 → t★ = 0) ∧ **(e★:ℤ)·σ.h < h★** — the read-form (I-aug)
    steepness (D.4, MOVES 2219–2220 "λ > w(Φ)" at the stage scale; on the
    HC2 side extracted from HistoryCoherent's slope law + strict steepening:
    h_{i+1} > h_i·e_{i+1}·e_i·g_i ≥ e_{i+1}·h_i — a short lemma in V9).
  - `ReadResData σ e★ h★ s★ t★ : Type` — the regrade carrier, mirroring
    `ChildResData`: `Rv : Polynomial ℤ_[p] → LaurentPolynomial ↥σ.K` + the
    two pins `Rv σ.Φ = T s★` (key pin; slot-1 arithmetic 1·s★ − t★·σ.w 1 = s★)
    and the S5-shape pin `∀ B ≠ 0, inC σ.Φ B → Rv B = C(digit scalar of
    σ.R B)·T(−t★·σ.w B)` — scalars PRESERVED, positions re-forced (the (S5)
    position law at the new pair, MOVES 1960–1963).
  - `ReadResLaws` — the D.1(e) law-pack Prop on a carrier w.r.t.
    `childW σ σ.Φ e★ h★` (NOTE THE REUSE: wV at the same key IS `childW`
    with Φhat := σ.Φ — no new functional is defined), same seven conjuncts
    as `ChildResLaws`.
  - `ReadFrame σ e★ h★ s★ t★ : Type` — the PARTIAL stage pack (Finding 3):
    a lawful carrier + the wV laws (hwmul/hwult/hwΦ/hK1-at-Φ/hStretch
    wV = e★·σ.w on C_Φ) + hS6a in the CURRENT form (untwisted — it HOLDS at
    regrades, V6a) — everything the D.5/D.8 reruns consume; NO hS6b, NO
    hvalgrp, NO reps/Tvec.
  Falsifiability: every pin is an equation against existing objects; wrong
  positions break V2's hRmul at the first product.

* **V1 `V1_readWPack`** — the read functional's laws at the same key.
  STATEMENT: for σ cored, `ReadPair` hypotheses: `childW σ σ.Φ e★ h★` has
  the slot-min/attained-min pack (S2 instance at Φhat := σ.Φ — signature
  admits it verbatim), hwmul, hwult, and the Q-ASCENT lemma: for parent
  coefficients B·B″ = Q·σ.Φ + R_dev (monic division), the Q-slot's
  (†)-value exceeds the R_dev-slot's by h★ − e★·σ.h > 0 (steepness).
  moves_ref: D.7(i) (MOVES 2331–2337) at the same-key instance; D.4.
  deps: S2_childW, σ's hRmul/hwmul/hwult/hK1. difficulty: medium.

* **V2 `V2_readResidual`** — the lawful regrade carrier exists:
  `∃ D : ReadResData, ReadResLaws D` (+ w_strict, the S9w-(ii) mirror).
  Construction: RV per (†) — scalars from σ.hS5's monomial digits (parent
  coefficients only, so every slot digit IS a monomial), positions
  (j − t★·wV(f))/e★ = j·s★ − t★·σ.w(B_j), injective in j across minimizing
  slots (elementary: the map j ↦ (j − t★γ)/e★ on the tie set), so RV(f) ≠ 0.
  hRmul: V1's Q-ascent + σ.hRmul on slot products + the position additivity
  (exact, carry-free in the total coordinate — see the DEMOTION NOTE).
  moves_ref: D.6/D.7(i)–(iii) read at the level-free stage; D.5's "no
  coset-splitting" absence note (MOVES 2291–2292). deps: V0, V1, L3_K1
  pattern. difficulty: medium-hard (the S9w mirror, EASIER: no field
  extension). THIS IS THE V′ FRAME CHANGE UNIT.

* **V3 `V3_readLift`** — the recorded lift is the regrade's standard lift:
  `IsReadLift σ ψ g e★ h★ Φ̂` → (equal (†)-weights of all slots; the D.5
  residual display RV(Φ̂) = T(m̂★)·(ψ as Laurent), m̂★ = −t★·h★·g via the
  distinct-exponents sum k − t★h★g; K1(Φ̂/wV): wV(f) = min_m (wV(B_m) +
  m·e★h★g) with attainment). moves_ref: D.5 VERBATIM (MOVES 2253–2289 —
  the whole display re-runs at the ReadFrame; the Lean pattern is
  L3_liftResidual + L3_K1). deps: V2, L3_digPrime_nonzero-analog at the
  same key (width < g: D.3(d)). difficulty: medium.

* **V4 `V4_readLanding`** — (BOX)+(VERTEX) at the ReadFrame: for f ≠ 0 with
  ord_ψ(RV f) = μ and anchored RV-data, the Φ̂-development satisfies
  wV(B_m) + m·e★h★g > wV(f) for m < μ, = at m = μ with B_μ ≠ 0 (and the
  vertex digit with its explicit unit z̄^{−μm̂★}, for consumers that want it).
  moves_ref: D.8 (BOX)/(VERTEX) VERBATIM (MOVES 2469–2490: the displayed
  proof — K1 + D.1(e) + D.3(d) distinct ψ-orders — consumes NOTHING beyond
  the ReadFrame pack; S6/valgrp are untouched, which is what makes Finding 3
  harmless). The Lean pattern: L5_landVertex/L5_landVertexDigit transplanted
  to the pack. deps: V3. difficulty: HARD-ish but bounded (one L5-sized
  file). The (TRANSPORT) leg is NOT needed by any of the three discharges —
  fence it OUT of V4 (record it as available follow-on).

* **V5 SIGN-OFF EVENT (Defs restatement; Asvin's approval REQUIRED; the
  resolution of §9.9's queued strip adjudication).**
  - `Stage.hS6a` restates to the FIXED-POINT COSET form:
    `∀ ν ∈ weightSet, ∃ b : (↥K)ˣ, ∀ c : (↥K)ˣ, ((c:↥K):F) ∈ FQ →
     ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
       R B = C((c*b : ↥K)) * T (−t·ν)`
    — the base point ∃-quantified BEFORE the orbit scalar, base FREE in Kˣ
    (weakest faithful form: the note's fixed classes are z̄-monomial at
    depth 2 but general unit products at depth ≥ 3; no consumer reads the
    base's shape — D.2's consumer audit "exactness consumes no scalar range",
    MOVES 1971–1981).
  - RIPPLE CENSUS (grep `hS6a` at execution; expected complete):
    constructors — T1/T2 base stage (b := 1: base digits are untwisted,
    MOVES 2012–2015), S10 recentering (transport with the SAME b: e = 1
    stages have position-0 constant residuals, the substitution fixes them),
    R6 carrier instance, S9a/S9b (become CONSUMERS of V7); consumers —
    `L4_TRANSviii_a_R5{,_final}` (statement restates: conclusion's
    `(d:F) = c·z̄^m` weakens to the coset form `∃ d₀ : (↥σ'.K)ˣ` base,
    ∃-before-∀c UNCHANGED; the proof repair is ~10 lines — fold the parent
    base through `L2_strideRule`; footprint re-verify MANDATORY).
  - FAITHFULNESS WARRANT: D.2 (S6a) rev D⁶ "orbit group at its FIXED POINT"
    (MOVES 1964–1971); D.7(viii) "c·(a fixed z̄-monomial class): the O-orbit
    with O = F_Qˣ CONSTANT" (MOVES 2431–2435); pass-14 finding 1 + pass-15
    "closure is therefore trivial" (MOVES 3091–3097, 3122–3124). The current
    Lean form is refuted by the S9a strip countermodel; per Finding 2 no
    conservative repair exists. This is the honest-restate discipline, same
    species as the S9a guard event (§9.9).

* **V6 `V6_alignedOrbits`** — the aligned digit orbits, both levels:
  (a) REGRADE orbits are UNTWISTED: σ★-realizers = parent hS6a realizers
  re-positioned, scalars preserved (fills ReadFrame.hS6a; also the b-transport
  helper V5's census cites). (b) DESCENT orbit base points: the strip window
  display — slots at child weight ν are (γ, j) = (s·ν − λ·h, t·ν + λ·e),
  λ ∈ (a g-window), twist = λ; the minimizing-slot choice (TRANSviii_a
  conjunct 1 forward + choice) fixes THE base b(ν) per weight. moves_ref:
  D.7(viii)'s 𝒜′ + realizer display (MOVES 2423–2435); the S9a header's
  twisted-orbit display (now a POSITIVE statement, not an obstruction).
  deps: V0; (b) consumes L4_TRANSviii_a_R5_final post-V5. difficulty: short.

* **V7 `V7_stripDischarge`** — S9a's single sorry closes: under V5's coset
  hS6a, the below-threshold leg of hS6a′ is V6(b)'s base + TRANSviii_a's
  conjunct 2 verbatim; the above-threshold leg stays L4_TRANSviii_b (exact
  scalars, unchanged). S9b's billing seam (§9.9 last bullet) closes with the
  same key. deps: V5, V6. difficulty: short. UNBLOCKS: S9a → S9b → S9c/S9d
  → S9 (the assembly chain's statements are already staged).

* **V8 `V8_childResidual`** — S9w-(i) PROVED: the explicit descent carrier
    `Rc f := Σ_{j minimizing childW} C(⟨digPrime z̄ (B_j), mem⟩)·
             T(j·s′ − t′·σ.w (B_j))`
  (choice-packaged against `ChildResData`'s pins — hS5′ is the single-slot
  case DEFINITIONALLY (mfun ≡ 0 is CORRECT, per Finding 2's first bullet;
  the strip mismatch was hS6a's transcription, never the pin), hRPhi the
  slot-1 case) + `ChildResLaws`:
  - (a) additive legs hR0/hRne/hRadd/hRlt/hRneg + w_jump: slot-min ties
    (S2's hSMW), position-injectivity across tied slots, parent hRadd/hRlt
    slotwise; hRne needs D.3(d) (ψ ∤ R(B), width < g — on disk as
    L3_digPrime_nonzero) for digit nonvanishing and F′[z^{±1}]-domain for
    sums. difficulty: medium.
  - (b) hRmul: the bilinear slot expansion; per-pair monic division
    B_j·B″_k = Q_{jk}·Φ̂ + R_{jk}; `L3_DIV` gives R_{jk} ≠ 0, exact weight,
    digit product; Q-terms strictly deeper by th's (I-aug) (D.7(i) verbatim);
    tied (j,k)-pairs land at ONE position (j+k)s′ − t′(σ.w B_j + σ.w B″_k)
    and SUM as the Laurent product's convolution coefficient; a vanishing
    convolution coefficient = a parent-residual cancellation = the SAME
    zero on both sides (no false nonvanishing claim — the D.1(b) δ-calculus,
    MOVES 2305–2313). difficulty: HARD (the honest §9.5 core), but every
    ingredient is displayed + on disk.
  - (c) w_strict (S9w conjunct (ii)): S9a's in-file hwult pattern + strict
    slot domination. difficulty: short.
  moves_ref: D.6 Lemma DIV (MOVES 2299–2322), D.7(i)–(iii) (2331–2352),
  D.7(vi)–(vii) normalization (2392–2418). deps: V0 (shape only), S2, S3,
  L3_DIV, L3_liftMonic, L3_digPrime_nonzero, th. NOT dependent on V5 (the
  carrier + laws never mention hS6a). UNBLOCKS: S9w → S9r (already reduced),
  the S9a census's carrier legs, and kills the S9w cone's sorryAx.

* **V9 `V9_K1nonrec`** — HC2's `K1_readVertexPin_nonrec` PROVED as a
  corollary: (i) extract the read steepness from HistoryCoherent (slope law
  + strict steepening → ν.h > ν.e·σ.h — the ReadPair hypothesis); (ii) build
  the ReadFrame at (ν.e, ν.h) on σ_i (V1/V2); (iii) the recorded
  `IsNodeLift = IsReadLift` is V3's standard-lift shape — K1(Φ̂/wV) + D.8 at
  the frame (V4); (iv) f's ReadFrame residual IS the recorded side pattern:
  RV(f) = Σ_k C(pat k)·T(…) from SideReads (i)+(ii) (the side line supports
  the development with equality exactly at the stride digits — so wV(f) =
  ν.gam, attained); its anchor/ord data: HasAnchorK(RV f, a★, pattern-Ranch)
  DERIVED from (i)+(ii); ord_ψ(pattern) = ν.μ read against SideReads (iii)
  — ADJUDICATION SURFACED (see below); (v) V4's (VERTEX) gives B_μ ≠ 0 and
  wV(B_μ) = gam − μ·ν.e·g·ν.h, then σ′.w(B_μ) = ν.e·σ.w(B_μ) = wV(B_μ) via
  the RECORDED child_wPrev/hStretch on the ONE coefficient (no tower
  reconciliation needed — the kernel's conclusion touches only a child
  COEFFICIENT's weight); (vi) the ℚ-conversion to
  `STR_{i+1}·line.at(μ·childWidth)` is the γ-tie + slope-law arithmetic
  already PROVED in-file (`K1_SAE_vertexEq_endpoint`'s pattern).
  deps: V1–V4 + the HC2 records. difficulty: medium (assembly).
  UNBLOCKS: `K1_readVertexPin` total → U20a/U20b/U22-E2 close by the staged
  one-line consumers.
  ⚠ SIDEREADS-(iii) ADJUDICATION (the standing E-PHASE FLAG, now with its
  resolution named): (iii) anchors `σ.R f` — the FRAME residual — while the
  landing needs the READ residual RV(f)'s ψ-order. At single-side reads they
  agree; at multi-side polygons the frame residual sees the WRONG slots.
  The faithful object is RV(f) (§C's side data are side-local); the DERIVED
  pattern-anchor route above consumes only (i)+(ii)+the recorded μ, so V9
  should key ord_ψ to the PATTERN and treat (iii)'s σ.R f rendering as
  the U31-gated seam it already is. If the gate shows the recorded μ
  mis-associates on some run shape, THAT restatement (SideReads (iii) →
  RV-vocabulary) is a NEW sign-off item — flagged now, not silently changed.

### 10.2 What this section does NOT change

No accepted statement moves except the TWO named sign-off items (V5's
Stage.hS6a + the TRANSviii_a conclusion pair), each with a machine-checked
refutation of the old form and a quoted note display for the new one — the
same restate-after-refutation discipline as the S9a guard event. VertexPin,
ChildResData.hS5′, childR's denotation, S9a–S9d/S9 statements, all L5
assets, U20c, D1–D8, S10: UNTOUCHED. Zero new axioms anywhere; every new
unit ends with `#print axioms` and the standard footprint protocol.

### 10.3 Census and estimate

9 proof units (V1,V2,V3,V4,V6,V7,V8a/b/c as one file with three theorems,
V9) + 1 Defs file (V0) + 1 sign-off event (V5). Confidence the design as
specified discharges its three targets: V7 ≈ 0.9 (post-V5, mechanical);
V8 ≈ 0.85 (all engines on disk; the risk is Lean-side Laurent/coercion
grind, not mathematics); V9 chain ≈ 0.75 (V4 is the big rerun; the
SideReads-(iii) seam is the one open adjudication and is fenced). Joint
estimate ≈ 0.8. The failure mode that would falsify the DESIGN (not just
stall a proof): a ReadFrame law that secretly needs hS6b — Finding 3's
audit says none does, and V4's fence (no TRANSPORT leg) is chosen to keep
it that way.

## 10.4 EXECUTION RECORD (2026-07-28, V′-kernel applier — Asvin's
definition-change authority per the task charge; acceptance = proofs run
through + full perimeter green)

**V5 EXECUTED FIRST (the sign-off event).** `Stage.hS6a` restated to the
fixed-point coset form in `Moves/Defs.lean` — `∃ b : (↥K)ˣ` BEFORE
`∀ c : (↥K)ˣ, (c:F) ∈ FQ`, conclusion scalar `C((c·b : ↥K))` — with the
field docstring quoting the two note displays verbatim (D.2 (S6a) rev
D⁶/pass-14, MOVES 1964–1971 "orbit group at its FIXED POINT … O := F_Qˣ
CONSTANT"; D.7(viii) MOVES 2431–2435 "c·(a fixed z̄-monomial class)") and
recording the machine-refutation of the old untwisted form (§9.9's S9a
strip record). RIPPLE CENSUS EXECUTED (grep `hS6a` corpus-wide at
execution; 15 files touched, every proof run through green):

* constructors — `T1_baseStage` (b := 1, `rw [mul_one]`); `S1_transHypGate`
  σpin (b := 1, `k0_unit_eq_one (c * 1)`); `S10_recStage` (transport with
  the SAME b, per the census prediction); `U17b_galois` `stageMap`
  (b ↦ its `resAut` image; `apply_symm_apply` on the c-factor only);
  `U28_gateSep`/`U30_gatePol`/`U31_gateReadsOf` gate stages (b := 1, the
  trivial-subfield unit lemmas at `c * 1`); `S9a_stageLiteral` — `hS6a'`
  restated to the coset form (above-threshold leg b := 1 through the
  UNCHANGED `L4_TRANSviii_b`; the strip `sorry` STAYS, now billed as V7's
  obligation — header adjudication paragraph updated: RESOLVED, neither
  §9.9 queued option; `mfun ≡ 0` is the note's V′ normalization, the
  mismatch was hS6a's own transcription).
* consumers — `L4_TRANSviii_a_R5{,_final}`: CONCLUSION RESTATED per the
  census spec — `∃ m : ℤ … (d:F) = c·z̄^m` weakens to
  `∃ d₀ : (↥σ'.K)ˣ … (d:F) = c·(d₀:F)`, ∃-before-∀c UNCHANGED; proof
  repaired as drafted (the parent coset base `b` folds through
  `L2_strideRule`; `d₀ :=` the `d` of the `c = 1` instance; both files
  PROVED, sorry-free). `L5_realRecursion_R3` (two-line: obtain base, apply
  at c = 1). `T4_slotMinHt`/`T7_alphabetSpan`/`C2_TYPa` (base-stage
  `digLift` realizers: `IsBaseStage`'s `K = FQ` absorbs the base —
  c := y·b⁻¹, `inv_mul_cancel_right`).
* NOT touched (census verified): R6 (no hS6a in code — the §10.1 census
  row was conservative), S9b/S8 (import TRANSviii_a but consume only its
  file, statements sorry/proved unchanged), every `{ σ with … }` clone
  (field rides through).

**PERIMETER: 532 modules GREEN** (all of Moves/MovesC/MovesD/MovesGr/
MovesRBase/MovesS/MovesSp/MovesU/MovesX/HC1/HC2). The ONLY two exclusions,
`MovesGr/L2_degZero_subring_v2` + `MovesGr/L4_genuine_imp_stageCoreL_v2`,
are PRE-EXISTING failures — machine-verified by rebuilding them against
HEAD's (pre-V5) `Defs.lean`: identical DirectSum-instance errors, no olean
in the build cache (never green in this workspace state), content
unrelated to `hS6a`. Recorded here so nobody bills them to V5.
`AxChk_baseline` does not cover the Moves/HC perimeter (OM-only); the
footprint protocol is the per-file `#print axioms` tails, all as expected
(repaired proved units Lean-core; sorried units sorryAx).

**V0–V9 ELABORATED** (`lean/LeanUrat/HC1/DefsV.lean` + `V*_*.lean`, all
ADDITIVE, zero axioms, 13 E-phase sorries):

* V0 `DefsV.lean` — `ReadPair`/`ReadResData`/`ReadResLaws`/`ReadFrame`,
  sorry-free. ONE recorded deviation from the §10.1 text: `ReadFrame.hS6a`
  is transcribed in the CURRENT (= post-V5 COSET) `Stage.hS6a` form, not
  the pre-V5 untwisted form the parenthetical named — the field mirrors
  the Stage field at the regraded frame (weights over
  `childWeightSet σ σ.Φ`, wVPrev = σ.w); V6(a) fills it by base transport
  (scalars preserved ⇒ the parent's coset bases ride).
* V1–V4, V6, V7, V9 — statements per §10.1 (V1 Q-ascent with the
  displayed gap `h★ − e★·σ.h`; V2 + the `V2_readFrame` packaging
  corollary; V3 with the D.5 EQUAL-WEIGHTS display as an explicit
  conjunct; V4 (BOX)+(VERTEX)+vertex-digit, TRANSPORT leg fenced OUT as
  specified; V6(a)/(b) with the descent base's z̄-monomial SHAPE
  displayed; V7 = EXACTLY S9a's hS6a′ obligation shape over any lawful
  carrier; V9 = `K1_readVertexPin_nonrec`'s statement VERBATIM + the
  steepness lemma at reads with a predecessor — the ROOT read's steepness
  is P-phase, from the recorded side data).
* V8 — `ExplicitDescentCarrier` (the (†) formula as a Prop on
  `ChildResData`, classical filter) + V8a/V8b/V8c sorried + the capstone
  `V8_childResidual` ASSEMBLED (proved from V8b+V8c; byte-shape = S9w's
  statement, so `S9w_residualLaws` closes by `exact` once V8b/V8c land).
* The SideReads-(iii) seam: FENCED as charged — V9's header carries the
  §10.1 ⚠ block; `SideReads` untouched; any RV-vocabulary restatement is
  a named FUTURE sign-off item.

POST-EVENT FRONTIER: the V-kernel P-phase (V1→V2→V3→V4→V9; V6→V7; V8),
then the staged one-line closures (S9w ← V8, S9a strip ← V7,
`K1_readVertexPin_nonrec` ← V9). MANIFEST re-synced (69 units; record key
`vkernel_2026-07-28`).

## 10.5 ESCALATION RECORD (2026-07-28, S9w_final — Fable escalation round)

First prover's verdict CONFIRMED: S9w is not wiring; the hardness is V8b.
Landed this round (all Lean-core, `#print axioms` in-file; V8 cone + S9r/S9a
consumers rebuilt green):

* **V8c_wStrict PROVED** — the childW strict law: S9a's in-file hwult pattern
  (slotwise development addition, parent ultrametric per slot) + childW
  NEGATION-INVARIANCE (slotwise, from `σ.w(−B) = σ.w B` for any multiplicative
  integer valuation) + the reverse inequality via `f = (f+g′) + (−g′)`.
  `f + g′ ≠ 0` is DERIVED (g′ = −f would tie the values against strict <).
* **S9w_residualLaws WIRED** — own sorry killed; closes by
  `exact V8_childResidual σ hσ th s' t' hbez' ht'0` (byte-identical statement,
  per the staged plan). Its sorryAx now flows through V8b ALONE (V8a is off
  the capstone path: the capstone assembles from V8b + V8c only).
* **Three V8b atoms PROVED** (in `V8_childResidual.lean`):
  - `V8_tiedPos_inj` — tied-slot position injectivity (the hRne crux):
    childW-tie + equal child positions ⟹ j₁ = j₂, by the Bézout collapse
    d = d·(e′s′ + h′t′) = 0 (a one-line `linear_combination` certificate:
    (j₂−j₁)·hbez′ + e′·hpos + t′·htie).
  - `V8_eval₂_mem_nextField` — z̄-evaluation of any ↥K-Laurent polynomial
    lands in K′ (`LaurentPolynomial.induction_on`; T ±1 steps via z̄, z̄⁻¹ ∈ K′).
  - `V8_digitUnit` — dig′(B) realized as a K′-UNIT for B ≠ 0 with
    natDegree < e·g·deg Φ (atom 2 + `L3_digPrime_nonzero`).

**EXACT REMAINING OBSTRUCTION (V8a + V8b, the honest §9.5 core).** All are
now carrier-construction work; no missing engine was found:
1. DEFINE the explicit carrier (classical choice on the Fact-A development;
   sum over the min-slot filter of `C(digitUnit)·T(j·s′ − t′·σ.w B_j)`), with
   the pins: hRPhi = the slot-1 development of Φ̂ itself (needs `σ.R 1 = 1`,
   the S10 `R_one` pattern, + childW Φ̂ = h′) and hS5′ = the single-slot
   development (atom 3 verbatim; degree bound from `inC Φ̂` + L3_liftMonic).
2. hRne: atoms 1+3 + the Finsupp fact that a sum of `C c·T n` over DISTINCT
   positions with c ≠ 0 is ≠ 0 (coefficient extraction at a witness position;
   `LaurentPolynomial.single_eq_C_mul_T` + `Finsupp.single_apply`).
3. hRadd/hRlt/hRneg/w_jump: slotwise transport through Fact B on the summed
   development (the S9a hwult skeleton, upgraded to carry residuals): per
   tied slot the 5-way split (f-only / g-only / tie-no-jump via σ.hRadd +
   `map_add` under eval₂ / tie-jump = digit cancellation / untied via σ.hRlt),
   then re-index the min-slot filters (they partition by atom 1).
4. hRmul (THE block): per-pair monic division `B_j·B″_k = Q_jk·Φ̂ + R_jk` —
   `L3_DIV` (ON DISK, proved) gives R_jk ≠ 0 + exact weight + digit product;
   Q-terms strictly deeper by th.hiaug (h′ > e′·w(Φ̂); the L3_DIV 2-slot K1
   pattern gives the D.7(i) weight bound); regroup the double sum into the
   product's development (Fact B pins it); tied (j,k) pairs land at ONE
   position (atom 1 applied to the pair sums) and sum as the Laurent
   convolution coefficient (`AddMonoidAlgebra.single_mul_single`); a vanishing
   convolution coefficient is the SAME zero on both sides (D.1(b) δ-calculus).
   childW multiplicativity is ON DISK (`S5_childValuation`, Lean-core).
Estimate unchanged from §10.3 (the risk is Laurent/Finsupp grind, not
mathematics); sized as its own dedicated unit, NOT a one-session close.

## 10.6 SECOND ESCALATION RECORD (2026-07-28, V8b hRmul core — Fable round 2):
## V8 PROVED IN FULL — S9w SORRY-FREE

The §10.1 V8 unit is CLOSED: **V8a, V8b, V8c all proved, zero sorry; every
theorem in `V8_childResidual.lean` (capstone included) has footprint
{propext, Classical.choice, Quot.sound}; `S9w_residualLaws` + `childR_laws`
now Lean-core; full cone rebuilt green.**

The one genuinely new device (everything else was assembly of on-disk engines):
the private **graded-residue calculus** `v8gr σ ω x := if x ≠ 0 ∧ σ.w x = ω
then σ.R x else 0` with domain `v8Deep σ ω x := x = 0 ∨ ω ≤ σ.w x`. The single
lemma `v8gr_add` packages ALL FIVE D.1(b) tie laws (parent hRadd/hRlt +
StageCore w_strict/w_jump/R_neg) as: `v8Deep` is closed under `+` and `v8gr ω`
is ADDITIVE on it. Every per-slot digit claim in every law leg then reduces to
"compute `v8gr` of the slot sum termwise, evaluate at z̄, cite D.3(d)".

* Carrier: `v8Rc` = the (†) tied-slot sum on THE development (Fact A choice,
  Fact B independence spec `v8Rc_eq`); hRne by position injectivity
  (`e′·pos(j) = j − t′·m`, the ATOM-1 Bézout collapse) + Finsupp coefficient
  extraction at one tied position; pins hRPhi/hS5′ by direct evaluation of the
  2-slot/1-slot developments (`dig′(1) = 1` from idempotence in F).
* hRadd/w_jump/hRlt: per-slot `v8gr` case trees at the tie level ω_j (the
  slot-value ↔ parent-weight converters cancel e′ > 0); cancelling digit pairs
  are exactly the non-tied sum slots (D.3(d) forbids a tied slot with zero
  digit); hRlt consumes V8c's strict law (V8c MOVED above V8a/V8b in-file).
* hRmul (the §9.5 core): `L4_TRANSiii`'s convolution development
  `Cdev m = H.coeff m %ₘ Φ̂ + Q_{m−1}` re-derived IN-FILE at digit level (those
  helpers are private); `childW`-multiplicativity CITED from `L4_TRANSiii`;
  per-diagonal, `hgrC : v8gr ω (Cdev m) = Σ_{tied pairs (j,k), j+k=m}
  R((B_j·B″_k) %ₘ Φ̂)` — remainder weights exact by `L3_DIV`, carried quotients
  strictly deep by (I-aug) (the generalized hdeepQ at arbitrary ω with
  e′ω + m·h′ = M); evaluation at z̄ + `L3_DIV`'s digit product turns `hgrC`
  into "digit of `Cdev m` = the convolution coefficient Σ dig′(B_j)·dig′(B″_k)";
  the Laurent product regroups by `Finset.sum_mul_sum → sum_product' →
  sum_fiberwise_of_maps_to`, fiberwise-constant positions/weight-sums by the
  tie arithmetic. A VANISHING convolution coefficient is the SAME zero on both
  sides: the sum slot cannot be tied (its digit would be 0, against D.3(d)) —
  the D.1(b) δ-calculus exactly as §10 displayed it.
* Statement fence: V8a/V8b/V8c/V8_childResidual/`ExplicitDescentCarrier`
  signatures byte-identical; V8c's proof untouched (block moved verbatim).

UNBLOCKED: S9w → S9r (rides conjunct (i)); the S9a census's carrier legs.
The S9w cone's sorryAx is DEAD.
=== END SECTION C ===
=== SECTION D: MOVES_2026-07-24.md excerpts ===

--- MOVES lines 1964-1971 (D.2 / S6a, rev D6 pass-14 finding 1) ---
(S6) Constructive slot basis, TWO TIERS [split at rev D″; pass-10 finding 1]:
     (S6a) EXACTNESS + BASIC REALIZERS [orbit group at its FIXED POINT, rev
     D⁶, pass-14 finding 1]: 𝒜 := {(w(B), k(B)) : B ∈ C∖0} is the recursively
     displayed index set (base below; step D.7(viii)), and every index is
     realized by an explicit single-slot element whose digit is c·(the index's
     forced monomial class) with c ranging over the CONSTANT orbit group
     O := F_Qˣ (the BASE field's units — what iterated single-slot realizers
     actually propagate; trivially closed under the induction). Consumer audit

--- MOVES lines 2395-2418 (D.7 vi-vii PINNING / T,S5 / EXPONENT group) ---
PINNING [typed at rev D⁶ per pass-14 finding 3 — in(·) applied only to
genuine representatives]: the stage carries the exponent VECTOR of its pinned
coefficient unit V over the representative list (P2); T = V^s·Y^t and
z = V^{−h}·Y^e BY PINNING (literal identities — the pass-14 verifier's own
verification). Transport: V' := Π_i in_{w'}(ũ_i)^{s·b_i} · in_{w'}(Φ)^{t}
(the in_{w'}-image of T's vector, factorwise over genuine representatives;
T has w-degree 1, so V' has w'-degree e'). Then u₀ := V'^{−h'} (explicit, no
choice); z' := u₀·Y'^{e'} = V'^{−h'}·Y'^{e'}. The honest
degree-0 unit-monomial group is F'ˣ × z'^ℤ [pass-9 finding 8]; define the
EXPONENT group := (degree-0 products of U'-monomials) modulo F'ˣ-scalars —
infinite cyclic, generated by the class of z' (two degree-0 monomials of equal
Y'-exponent differ by a degree-0 coefficient unit ∈ F'ˣ, by the F'-line
statement above); L'₀ = F'[z'^{±1}] (S4' completed, with (S4)'s "monomial
group" clause read as the EXPONENT group from here on).
(vii) **T', S5'.** T' pinned explicitly [typed at rev D⁶]: at e' = 1, T' :=
V' (coefficient-pure, degree 1); at e' ≥ 2, T' := V'^{s'}·Y'^{t'} with the
fixed Bézout pair e's' + h't' = 1 (degree 1 ✓) — explicit localized monomials
in (V', Y'), the next stage's pinned unit is V', its vector is the transported
one, and the D.3(b) literal identity re-runs verbatim; the stride rule
and width bound re-derive by
the D.3 computation in the new frame (nothing level-specific was used); S5':
a coefficient class [B] is a fixed-Y'-exponent degree-0 multiple of a monomial
after T'-normalization, landing in one F'-line of (vi): dig'(B) = c'·z'^{k'(B)}
with the position determined by the new weight, exactly as before.

--- MOVES lines 2431-2435 (D.7 viii realizer display) ---
arises from a minimizing Φ-slot (j, γ), hence lies in 𝒜'; conversely every
index is realized by the SINGLE-SLOT element t_{γ,j} := ((S6a) realizer of
(γ, forced position, c ∈ O))·Φ^j — whose dig' is c·(a fixed z̄-monomial
class): the O-orbit with O = F_Qˣ CONSTANT (rev D⁶) — the next stage's (S6a')
asserts the SAME group, so closure is trivial.
=== END SECTION D ===
=== SECTION E: MOVES_2026-07-24.md, D.5 display (lines 2251-2293, full block) ===
### D.5 K1 at the new key

**The standard lift, displayed [pass-9 finding 4: no placeholders; ψ_k = 0
slots absent; monicity by construction].** For ψ = Σ_{k=0}^{g} ψ_k z^k (monic:
ψ_g = 1; irreducible; ψ ≠ z, so ψ₀ ≠ 0):

  Φ̂ := Φ^{eg} + Σ_{0 ≤ k < g, ψ_k ≠ 0} t_k·Φ^{ek},

where t_k ∈ C is an (S6b) realizer with weight w(t_k) = e·h·(g−k) and digit
SCALAR ψ_k — the digit's z-position is FORCED by the weight (k(t_k) =
−t·h·(g−k), per S5). (S6b) RANGE CHECK, parent-scaled [corrected at rev D⁵,
pass-13 finding 3]: the realizers' PARENT-scale weights are h(g−k) ≥ h >
e·w_prev(Φ) ≥ w_prev(Φ) by (I-aug) at the current read — above the clean
(S6b) threshold. (The simultaneous-induction order stands: stage package →
Φ̂ → next side via (I-aug) → the D.9 recursion, with w(Φ̂) = ehg entering
only as the number fixed by this construction.) Slots with ψ_k = 0 are ABSENT — no realizer of scalar 0 is
needed or defined. MONICITY: the leading slot is Φ^{eg} itself, coefficient
literally 1; deg Φ̂ = e·g·deg Φ. EQUAL WEIGHTS: each present slot has
w(t_k) + ek·h = eh(g−k) + ekh = ehg, and the leading slot 0 + eg·h = ehg;
so w(Φ̂) = ehg by (S2). RESIDUAL: R(t_k·Φ^{ek}) = ψ_k·z^{k(t_k)}·(z^s)^{ek} =
ψ_k·z^{k − thg} (exponent: −th(g−k) + esk = −thg + k(th + es) = k − thg, using
es + ht = 1), and R(Φ^{eg}) = z^{egs} = z^{g − thg}; the present slots occupy
DISTINCT exponents k − thg, so their initial forms sum without cancellation
(D.1(b)):

  R(Φ̂) = z^{m̂}·ψ(z),   m̂ := −t·h·g.

**Lemma K1(Φ̂/w).** For every f with Φ̂-development f = Σ_j B_j Φ̂^j (B_j ∈ Ĉ):
w(f) = min_j ( w(B_j) + j·w(Φ̂) ).

*Proof.* ≥ is (S1) + the ultrametric law. For ≤, suppose the minimum m is not
attained: all minimizing terms cancel below m. Pass to gr and apply R (D.1(e)):
Σ_{j minimizing} R(B_j)·R(Φ̂)^j = 0 in L₀ = F[z^{±1}], i.e.
Σ_j z^{jm̂}·R(B_j)·ψ(z)^j = 0. Each term is nonzero with ψ-adic order EXACTLY j:
ψ ∤ z^{jm̂}·R(B_j) by D.3(d) (ψ ≠ z; width < g). In F[z^{±1}] (the localization
of the UFD F[z] at the multiplicative set {zⁿ}; ψ stays prime there since
ψ ≠ z, i.e. ψ is coprime to the inverted set) [pass-9 finding 5], a finite sum of
nonzero terms with pairwise distinct ψ-orders is nonzero — the minimal-order
term survives ψ-adically. Contradiction. ∎

*(Note what is absent: no coset-splitting, no alignment offsets — the pass-5
z^{q_j} offsets are carried inside R(B_j) natively by the absolute convention.)*

=== END SECTION E ===

codex
I’ll inspect the actual workspace files and HEAD diff, then do a statement-by-statement comparison. I will not compile or modify anything.
exec
/usr/bin/bash -lc 'git status --short && git diff HEAD -- lean/LeanUrat/Moves/Defs.lean && rg -n "''^(def ReadPair|structure ReadResData|def ReadResLaws|structure ReadFrame|theorem V[1-9]|def ExplicitDescentCarrier)|sorry" lean/LeanUrat/HC1/DefsV.lean lean/LeanUrat/HC1/V*.lean' in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
 M lean/LeanUrat/HC1/C2_TYPa.lean
 M lean/LeanUrat/HC1/MANIFEST.json
 M lean/LeanUrat/HC1/S10_recStage.lean
 M lean/LeanUrat/HC1/S1_transHypGate.lean
 M lean/LeanUrat/HC1/S9a_stageLiteral.lean
 M lean/LeanUrat/HC1/S9w_residualLaws.lean
 M lean/LeanUrat/HC1/T1_baseStage.lean
 M lean/LeanUrat/HC1/T4_slotMinHt.lean
 M lean/LeanUrat/HC1/T7_alphabetSpan.lean
 M lean/LeanUrat/HC2/U17b_galois.lean
 M lean/LeanUrat/HC2/U20a_NAtransportRoot.lean
 M lean/LeanUrat/HC2/U20b_NAtransportIncrement.lean
 M lean/LeanUrat/HC2/U22E2_vertexEq.lean
 M lean/LeanUrat/HC2/U28_gateSep.lean
 M lean/LeanUrat/HC2/U30_gatePol.lean
 M lean/LeanUrat/HC2/U31_gateReadsOf.lean
 M lean/LeanUrat/Moves/Defs.lean
 M lean/LeanUrat/Moves/L4_TRANSi_R3.lean
 M lean/LeanUrat/Moves/L4_TRANSiii_R3.lean
 M lean/LeanUrat/Moves/L4_TRANSviii_a_R5.lean
 M lean/LeanUrat/Moves/L4_TRANSviii_a_R5_final.lean
 M lean/LeanUrat/Moves/L5_realRecursion_R3.lean
 M lean/notes/HC1_LEAN_BLUEPRINT_2026-07-28.md
?? .mcp.json
?? CLAUDE.md
?? lean/LeanUrat/HC1/DefsV.lean
?? lean/LeanUrat/HC1/V1_readWPack.lean
?? lean/LeanUrat/HC1/V2_readResidual.lean
?? lean/LeanUrat/HC1/V3_readLift.lean
?? lean/LeanUrat/HC1/V4_readLanding.lean
?? lean/LeanUrat/HC1/V6_alignedOrbits.lean
?? lean/LeanUrat/HC1/V7_stripDischarge.lean
?? lean/LeanUrat/HC1/V8_childResidual.lean
?? lean/LeanUrat/HC1/V9_K1nonrec.lean
?? lean/LeanUrat/Moves/L4_TRANSviii_c_R1.lean
?? verification/results/case_hn3_results_p2.json
?? verification/results/case_hn3_results_p3.json
diff --git a/lean/LeanUrat/Moves/Defs.lean b/lean/LeanUrat/Moves/Defs.lean
index b3611b5..405b294 100644
--- a/lean/LeanUrat/Moves/Defs.lean
+++ b/lean/LeanUrat/Moves/Defs.lean
@@ -169,11 +169,23 @@ structure Stage (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
   -- `−t·(parent weight)`, so the pair-valued 𝒜 is determined — DEF-6 note).
   weightSet : Set ℤ
   hWS : ∀ B, B ≠ 0 → inC Φ B → wPrev B ∈ weightSet
-  /-- (S6a) EXACTNESS + BASIC REALIZERS: every parent-scale coefficient weight `ν ∈ weightSet` is
-  realized, with any scalar `c` in the CONSTANT base orbit group `O = F_Qˣ` (via `FQ`). -/
-  hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
+  /-- (S6a) EXACTNESS + BASIC REALIZERS — **the FIXED-POINT COSET form** (V5 sign-off,
+  2026-07-28; blueprint §10 Key Finding 2). The note's axiom is the ORBIT-GROUP-AT-ITS-
+  FIXED-POINT statement, D.2 (S6a) rev D⁶/pass-14 finding 1 (MOVES 1964–1971): "every index
+  is realized by an explicit single-slot element whose digit is c·(the index's FORCED
+  MONOMIAL CLASS) with c ranging over the CONSTANT orbit group O := F_Qˣ" — and D.7(viii)'s
+  child realizers likewise have "dig′ … c·(a fixed z̄-monomial class): the O-orbit with
+  O = F_Qˣ CONSTANT" (MOVES 2431–2435). So each weight `ν ∈ weightSet` carries ONE base
+  point `b` (the forced class, ∃-quantified BEFORE the orbit scalar; free in `Kˣ` — the
+  weakest faithful form: depth-2 classes are z̄-monomial but depth ≥ 3 classes are general
+  unit products, and no consumer reads the base's shape, MOVES 1971–1981 "exactness
+  consumes no scalar range"), and the realized digit scalars are the COSET `F_Qˣ·b`.
+  The previous untwisted transcription (`b` hard-coded to 1) was machine-refuted on the
+  below-threshold strip (S9a census, F₉/F₃ numerics) and admits no re-pin repair —
+  restate-after-refutation, same discipline as the S9a guard event. -/
+  hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∃ b : (↥K)ˣ, ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
            ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
-             R B = LaurentPolynomial.C (c : ↥K) * LaurentPolynomial.T (- t * ν)
+             R B = LaurentPolynomial.C ((c * b : (↥K)ˣ) : ↥K) * LaurentPolynomial.T (- t * ν)
   /-- (S6b) FULL SCALARS ABOVE THE KEY WEIGHT: at every parent-scale coefficient weight STRICTLY
   ABOVE the current key's parent weight `wPrev Φ` (DEF-8 threshold), ANY digit scalar in the
   CURRENT field's unit group `Kˣ` (DEF-7) is realizable. -/
lean/LeanUrat/HC1/V9_K1nonrec.lean:15:`K1_readVertexPin_nonrec` (the ONE remaining HC2 kernel sorry) as a corollary of
lean/LeanUrat/HC1/V9_K1nonrec.lean:54:E-phase: statements per §10.1, `sorry` bodies.
lean/LeanUrat/HC1/V9_K1nonrec.lean:71:theorem V9_readSteepness {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V9_K1nonrec.lean:77:  sorry
lean/LeanUrat/HC1/V9_K1nonrec.lean:83:theorem V9_K1nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V9_K1nonrec.lean:95:  sorry
lean/LeanUrat/HC1/V7_stripDischarge.lean:19:**AXIOM-CLEAN PROOF, pure-σ (no dependency on the sorry-backed V6/S9_transStage).**
lean/LeanUrat/HC1/V7_stripDischarge.lean:135:theorem V7_stripDischarge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V6_alignedOrbits.lean:32:(no `sorry`, no new axiom). V6(a) = parent coset `hS6a` transported through
lean/LeanUrat/HC1/V6_alignedOrbits.lean:119:theorem V6_regradeOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V6_alignedOrbits.lean:166:theorem V6_descentOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V4_readLanding.lean:30:E-phase: statement per §10.1, `sorry` body.
lean/LeanUrat/HC1/V4_readLanding.lean:47:theorem V4_readLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V4_readLanding.lean:74:  sorry
lean/LeanUrat/HC1/V2_readResidual.lean:29:E-phase: statements per §10.1, `sorry` bodies.  `V2_readFrame` packages the frame
lean/LeanUrat/HC1/V2_readResidual.lean:45:theorem V2_readResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V2_readResidual.lean:53:  sorry
lean/LeanUrat/HC1/V2_readResidual.lean:57:theorem V2_readFrame {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V2_readResidual.lean:62:  sorry
lean/LeanUrat/HC1/V8_childResidual.lean:55:the S9a census's carrier legs; kills the S9w cone's sorryAx.
lean/LeanUrat/HC1/V8_childResidual.lean:58:zero sorry, Lean-core footprint on every theorem including the capstone.**
lean/LeanUrat/HC1/V8_childResidual.lean:92:def ExplicitDescentCarrier {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
lean/LeanUrat/HC1/V8_childResidual.lean:107:theorem V8_tiedPos_inj {e' h' : ℕ} {s' t' : ℤ}
lean/LeanUrat/HC1/V8_childResidual.lean:124:theorem V8_eval₂_mem_nextField (σ : Stage p F) (zbar : Fˣ)
lean/LeanUrat/HC1/V8_childResidual.lean:156:theorem V8_digitUnit (σ : Stage p F)
lean/LeanUrat/HC1/V8_childResidual.lean:1861:theorem V8c_wStrict (σ : Stage p F) (hσ : StageCoreL σ)
lean/LeanUrat/HC1/V8_childResidual.lean:2023:theorem V8a_carrierAdditive (σ : Stage p F) (hσ : StageCoreL σ)
lean/LeanUrat/HC1/V8_childResidual.lean:2078:theorem V8b_carrierLaws (σ : Stage p F) (hσ : StageCoreL σ)
lean/LeanUrat/HC1/V8_childResidual.lean:2121:theorem V8_childResidual (σ : Stage p F) (hσ : StageCoreL σ)
lean/LeanUrat/HC1/V3_readLift.lean:33:difficulty: medium.  E-phase: statement per §10.1, `sorry` body.
lean/LeanUrat/HC1/V3_readLift.lean:929:theorem V3_readLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/DefsV.lean:42:theorems, no `sorry`.
lean/LeanUrat/HC1/DefsV.lean:62:def ReadPair (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Prop :=
lean/LeanUrat/HC1/DefsV.lean:74:structure ReadResData (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
lean/LeanUrat/HC1/DefsV.lean:92:def ReadResLaws {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
lean/LeanUrat/HC1/DefsV.lean:115:structure ReadFrame (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
lean/LeanUrat/HC1/V1_readWPack.lean:30:Footprint: Lean core `{propext, Classical.choice, Quot.sound}`; zero `sorry`.
lean/LeanUrat/HC1/V1_readWPack.lean:211:theorem V1_readWPack {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

codex
The current tree matches the supplied material. One key distinction is emerging: the coset quantifiers themselves match §10, but the cited D.7(vi)–(vii) excerpt does not actually state the evaluation/frame-change identity needed to conclude “mfun ≡ 0”; I’m checking whether that is merely an undocumented warrant or affects a theorem statement.
exec
/usr/bin/bash -lc 'rg -n -C 5 "structure ChildResData|def ChildResLaws|def IsReadLift|structure TransHyp|def HasAnchorK|def OrdPsiPoly|K1_readVertexPin_nonrec|theorem K1_readVertexPin_nonrec" lean/LeanUrat/HC1 lean/LeanUrat/HC2 | head -n 500
rg -n "''^[[:space:]]*sorry([[:space:]]|$)" lean/LeanUrat/HC1/DefsV.lean lean/LeanUrat/HC1/V*.lean
rg -n "''^[[:space:]]*sorry([[:space:]]|$)" lean/LeanUrat/HC1/V8_childResidual.lean || true
sed -n '"'1,180p' lean/LeanUrat/HC1/DefsChild.lean
rg -n -C 3 \"def IsReadLift|structure IsReadLift|IsReadLift\" lean/LeanUrat/HC2/Defs.lean lean/LeanUrat/HC2/*.lean | head -n 180" in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
lean/LeanUrat/HC1/DefsChild.lean-62-σ.nextField z̄`, at the child Bézout pair `(s′, t′)`, carrying ONLY the two
lean/LeanUrat/HC1/DefsChild.lean-63-D.7(vi) NORMALIZATION PINS — the choice-spec carrier (§9.5 S9r: "`childR`
lean/LeanUrat/HC1/DefsChild.lean-64-definition + the S5′ shape lemma"). The apparatus/tie LAWS live in
lean/LeanUrat/HC1/DefsChild.lean-65-`ChildResLaws` below (S9w's own content, no longer fields). S9r proves carrier
lean/LeanUrat/HC1/DefsChild.lean-66-inhabitation (the seed); S9w constructs a LAWFUL carrier. -/
lean/LeanUrat/HC1/DefsChild.lean:67:structure ChildResData (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
lean/LeanUrat/HC1/DefsChild.lean-68-    (zbar : Fˣ) (s' t' : ℤ) : Type u where
lean/LeanUrat/HC1/DefsChild.lean-69-  /-- the residual function on all of A -/
lean/LeanUrat/HC1/DefsChild.lean-70-  Rc : Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar)
lean/LeanUrat/HC1/DefsChild.lean-71-  /-- D.3(b) at the child: the pinned key residual `R′(Φ̂) = z^{s′}` -/
lean/LeanUrat/HC1/DefsChild.lean-72-  hRPhi : Rc Φhat = LaurentPolynomial.T s'
--
lean/LeanUrat/HC1/DefsChild.lean-84-carry-exact product — D7's cmul law through `L3_DIV`), hRadd, hRlt, hWjump,
lean/LeanUrat/HC1/DefsChild.lean-85-hRneg): the D.1(e) residual apparatus w.r.t. `childW` in `Stage`'s own field
lean/LeanUrat/HC1/DefsChild.lean-86-shapes, plus the two D.1(b) StageCore tie laws that mention `Rc`. Proving a
lean/LeanUrat/HC1/DefsChild.lean-87-lawful carrier exists is `S9w_residualLaws`' OWN theorem content — the §9.5
lean/LeanUrat/HC1/DefsChild.lean-88-"one genuinely new algebra block". -/
lean/LeanUrat/HC1/DefsChild.lean:89:def ChildResLaws {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
lean/LeanUrat/HC1/DefsChild.lean-90-    {zbar : Fˣ} {s' t' : ℤ} (D : ChildResData σ Φhat e' h' zbar s' t') : Prop :=
lean/LeanUrat/HC1/DefsChild.lean-91-  (D.Rc 0 = 0) ∧
lean/LeanUrat/HC1/DefsChild.lean-92-  (∀ f, f ≠ 0 → D.Rc f ≠ 0) ∧
lean/LeanUrat/HC1/DefsChild.lean-93-  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rc (f * g) = D.Rc f * D.Rc g) ∧
lean/LeanUrat/HC1/DefsChild.lean-94-  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
--
lean/LeanUrat/HC1/DefsV.lean-11-accepted statement touched)
lean/LeanUrat/HC1/DefsV.lean-12-
lean/LeanUrat/HC1/DefsV.lean-13-**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` §10 ("THE V′ KERNEL — the
lean/LeanUrat/HC1/DefsV.lean-14-read-functional carry algebra in the aligned frame"), unit V0.  The ONE design
lean/LeanUrat/HC1/DefsV.lean-15-behind the three hard residuals (S9w-(i), S9a's hS6a strip, HC2's
lean/LeanUrat/HC1/DefsV.lean:16:`K1_readVertexPin_nonrec`): the D.1(e) residual pack rebuilt at a NEW
lean/LeanUrat/HC1/DefsV.lean-17-(e★, h★, s★, t★)-position law over an existing stage's data —
lean/LeanUrat/HC1/DefsV.lean-18-
lean/LeanUrat/HC1/DefsV.lean-19-  (†)  wV(f) := min_j ( e★·σ.w(B_j) + j·h★ )              (the read functional)
lean/LeanUrat/HC1/DefsV.lean-20-       RV(f) := Σ_{j minimizing} C(φ(slot-j digit)) · T(j·s★ − t★·σ.w(B_j))
lean/LeanUrat/HC1/DefsV.lean-21-
--
lean/LeanUrat/HC1/V9_K1nonrec.lean-10-
lean/LeanUrat/HC1/V9_K1nonrec.lean-11-/-!
lean/LeanUrat/HC1/V9_K1nonrec.lean-12-# HC1.V9_K1nonrec — HC2's K1 kernel residual via the ReadFrame (blueprint §10, V9)
lean/LeanUrat/HC1/V9_K1nonrec.lean-13-
lean/LeanUrat/HC1/V9_K1nonrec.lean-14-V′-KERNEL unit (blueprint §10.1), the REGRADE instance's payoff: HC2's
lean/LeanUrat/HC1/V9_K1nonrec.lean:15:`K1_readVertexPin_nonrec` (the ONE remaining HC2 kernel sorry) as a corollary of
lean/LeanUrat/HC1/V9_K1nonrec.lean-16-the V1–V4 chain.  Assembly route (§10.1 V9, steps (i)–(vi)):
lean/LeanUrat/HC1/V9_K1nonrec.lean-17-
lean/LeanUrat/HC1/V9_K1nonrec.lean-18- (i)  extract the read steepness from `HistoryCoherent` (slope law + strict
lean/LeanUrat/HC1/V9_K1nonrec.lean-19-      steepening → `ν.h > ν.e·σ.h` — the `ReadPair` hypothesis; the short lemma
lean/LeanUrat/HC1/V9_K1nonrec.lean-20-      `V9_readSteepness` below covers reads with a predecessor; the ROOT read's
--
lean/LeanUrat/HC1/V9_K1nonrec.lean-47-mis-associates on some run shape, THAT restatement (SideReads (iii) →
lean/LeanUrat/HC1/V9_K1nonrec.lean-48-RV-vocabulary) is a NEW sign-off item — flagged now, not silently changed.**
lean/LeanUrat/HC1/V9_K1nonrec.lean-49-This unit does NOT touch `SideReads`.
lean/LeanUrat/HC1/V9_K1nonrec.lean-50-
lean/LeanUrat/HC1/V9_K1nonrec.lean-51-deps: V1–V4 + the HC2 records. difficulty: medium (assembly).
lean/LeanUrat/HC1/V9_K1nonrec.lean:52:UNBLOCKS: `K1_readVertexPin` total (close `K1_readVertexPin_nonrec` by `exact`)
lean/LeanUrat/HC1/V9_K1nonrec.lean-53-→ U20a/U20b/U22-E2 close by the staged one-line consumers.
lean/LeanUrat/HC1/V9_K1nonrec.lean-54-E-phase: statements per §10.1, `sorry` bodies.
lean/LeanUrat/HC1/V9_K1nonrec.lean-55--/
lean/LeanUrat/HC1/V9_K1nonrec.lean-56-
lean/LeanUrat/HC1/V9_K1nonrec.lean-57-set_option linter.style.longLine false
--
lean/LeanUrat/HC1/V9_K1nonrec.lean-74-    (hsp : (H.nodes[i]'hi).species ≠ ReadSpecies.recentering) :
lean/LeanUrat/HC1/V9_K1nonrec.lean-75-    ((H.nodes[i]'hi).e : ℤ) * ((H.nodes[i]'hi).σ.h : ℤ)
lean/LeanUrat/HC1/V9_K1nonrec.lean-76-      < ((H.nodes[i]'hi).h : ℤ) := by
lean/LeanUrat/HC1/V9_K1nonrec.lean-77-  sorry
lean/LeanUrat/HC1/V9_K1nonrec.lean-78-
lean/LeanUrat/HC1/V9_K1nonrec.lean:79:/-- Unit V9: the K1 kernel residual — `K1_readVertexPin_nonrec`'s statement
lean/LeanUrat/HC1/V9_K1nonrec.lean-80-VERBATIM, proved through the ReadFrame chain (route (i)–(vi) in the header).
lean/LeanUrat/HC1/V9_K1nonrec.lean:81:Once landed, `K1_readVertexPin_nonrec` closes by
lean/LeanUrat/HC1/V9_K1nonrec.lean-82-`exact V9_K1nonrec h i hi1 hsp B Nd hdev hNd`. -/
lean/LeanUrat/HC1/V9_K1nonrec.lean-83-theorem V9_K1nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V9_K1nonrec.lean-84-    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
lean/LeanUrat/HC1/V9_K1nonrec.lean-85-    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
lean/LeanUrat/HC1/V9_K1nonrec.lean-86-    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
--
lean/LeanUrat/HC1/MANIFEST.json-521-  {
lean/LeanUrat/HC1/MANIFEST.json-522-   "id": "HC1.V9_K1nonrec",
lean/LeanUrat/HC1/MANIFEST.json-523-   "file": "lean/LeanUrat/HC1/V9_K1nonrec.lean",
lean/LeanUrat/HC1/MANIFEST.json-524-   "difficulty": "medium",
lean/LeanUrat/HC1/MANIFEST.json-525-   "sorries": 2,
lean/LeanUrat/HC1/MANIFEST.json:526:   "statement": "theorem V9_readSteepness (HistoryCoherent, 1 ≤ i, non-recentering) : ν_i.e·σ_i.h < ν_i.h; theorem V9_K1nonrec : K1_readVertexPin_nonrec's statement VERBATIM via the ReadFrame chain  [SideReads-(iii) seam FENCED — U31-gated; any restatement is a NEW sign-off item]"
lean/LeanUrat/HC1/MANIFEST.json-527-  }
lean/LeanUrat/HC1/MANIFEST.json-528- ],
lean/LeanUrat/HC1/MANIFEST.json-529- "signoff_2026-07-28": "F-1..F-6 EXECUTED (one event): F-1 T10(2)+C1(ii) → floorS step floor (lineStep/floorS defs in DefsCar); F-2 Tower.hcharF : CharP F p + C6_cardK_bridge PROVED in C6's file (C6 statement unchanged per §9.2); F-3 S7 → proved shape (scratch transplant, PROVED Lean-core; leg (c) homed to S9d); F-4 S8 → proved (I-aug) leg (PROVED; twist certificate retained in header; TvecUnitLaw homed to S9d); F-5 MoveWitness + core' : StageCoreL (both constructors), 9-file arity ripple (eBirthAux, T3, T4, T6, T7, C2, S13, S11), S11 PROVED (Part 1 = projection), S11a_coreTransport NEW+PROVED; F-6 S17 → ScratchS17 form (+hzsol +hcore), PROVED Lean-core, §4.6 dep-sorry pair out of HC1's cone. S9 DECOMPOSITION: DefsChild.lean (ChildResData choice-spec + childR + childWeightSet) + S9r/S9w/S9a/S9b/S9c (sorry statements) + S9d PROVED (consumes K1 bridges + S7 legs).",
lean/LeanUrat/HC1/MANIFEST.json-530- "vkernel_2026-07-28": "V′-KERNEL APPLIED (blueprint §10, V-prime applier): V5 SIGN-OFF EXECUTED FIRST (definition-change authority): Stage.hS6a RESTATED to the FIXED-POINT COSET form (∃ b : Kˣ before ∀ c : FQˣ; digit scalar C(c·b); docstring quotes MOVES 1964–1971 + 2431–2435) in Moves/Defs.lean. Ripple (all green, proofs run through): constructors T1_baseStage (b := 1), S1_transHypGate σpin (b := 1), S10_recStage (transport, SAME b), U17b stageMap (b ↦ resAut-image), U28/U30/U31 gate stages (b := 1), S9a hS6a′ restated to coset form (above-threshold leg b := 1 via L4_TRANSviii_b; strip sorry now = V7's obligation); consumers L5_realRecursion_R3 (two-line), T4/T7/C2 base-stage digLift (K = FQ absorbs the base: c := y·b⁻¹), L4_TRANSviii_a_R5{,_final} CONCLUSION RESTATED (∃ m : ℤ / c·z̄^m → ∃ d₀ : (↥σ′.K)ˣ / c·(d₀:F), ∃-before-∀c unchanged; proof repaired: parent coset base b folded through L2_strideRule, d₀ := the d of the c = 1 instance; PROVED, Lean-core). FULL PERIMETER RECOMPILED GREEN: 532 modules (Moves/MovesC/MovesD/MovesGr/MovesRBase/MovesS/MovesSp/MovesU/MovesX/HC1/HC2); the ONLY exclusions are MovesGr/L2_degZero_subring_v2 + L4_genuine_imp_stageCoreL_v2, PRE-EXISTING failures (machine-verified identical failure against HEAD's pre-V5 Defs.lean; DirectSum instance mismatches, no olean in cache — outside the maintained perimeter, unrelated to hS6a). V0–V9 ELABORATED: DefsV.lean (ReadPair/ReadResData/ReadResLaws/ReadFrame — sorry-free; ReadFrame.hS6a transcribed in the post-V5 coset form, deviation from the pre-V5 §10.1 parenthetical recorded in the file header) + 8 unit files, 13 E-phase sorries, all lake-green, footprints [propext, sorryAx, Classical.choice, Quot.sound] as expected. SideReads-(iii) seam stays FENCED (V9 header carries the §10.1 ⚠ block verbatim; SideReads untouched)."
lean/LeanUrat/HC1/MANIFEST.json-531-}
--
lean/LeanUrat/HC2/U22E2_vertexEq.lean-43-  -- in `K1_SAE_vertexEq_endpoint` (K1_vertexPin.lean): SideReads(ii) top-endpoint equality
lean/LeanUrat/HC2/U22E2_vertexEq.lean-44-  -- `e'·σ'.w(B μ) + μ·h' = gam'` + the γ-tie (adjacency) give `σ'.w(B μ) = STR_{i+1}·u*'`,
lean/LeanUrat/HC2/U22E2_vertexEq.lean-45-  -- and the K1 kernel pins the SAME quantity to `STR_{i+1}·line_i.at(μ·childWidth)`; cancel
lean/LeanUrat/HC2/U22E2_vertexEq.lean-46-  -- `STR_{i+1} > 0` and `Node.line`/`Node.ustar` absolute scale leaves the fenced ℚ-form.
lean/LeanUrat/HC2/U22E2_vertexEq.lean-47-  -- The sole residual behind this `exact` is the consolidated non-recentering kernel
lean/LeanUrat/HC2/U22E2_vertexEq.lean:48:  -- `K1_readVertexPin_nonrec` (the read-side carry-algebra vertex pin) — a SEPARATE `_final`
lean/LeanUrat/HC2/U22E2_vertexEq.lean-49-  -- unit; U22-E2 carries no independent obligation.
lean/LeanUrat/HC2/U22E2_vertexEq.lean-50-  exact K1_SAE_vertexEq_endpoint h i hi1 hadj
lean/LeanUrat/HC2/U22E2_vertexEq.lean-51-
lean/LeanUrat/HC2/U22E2_vertexEq.lean-52-end LeanUrat.MovesJ
--
lean/LeanUrat/HC2/Defs.lean-168-
lean/LeanUrat/HC2/Defs.lean-169-/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
lean/LeanUrat/HC2/Defs.lean-170-`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
lean/LeanUrat/HC2/Defs.lean-171-ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
lean/LeanUrat/HC2/Defs.lean-172-F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
lean/LeanUrat/HC2/Defs.lean:173:def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/Defs.lean-174-    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
lean/LeanUrat/HC2/Defs.lean-175-    (Φhat : Polynomial ℤ_[p]) : Prop :=
lean/LeanUrat/HC2/Defs.lean-176-  ∃ tt : ℕ → Polynomial ℤ_[p],
lean/LeanUrat/HC2/Defs.lean-177-    (∀ k, ψ.coeff k = 0 → tt k = 0) ∧
lean/LeanUrat/HC2/Defs.lean-178-    (∀ k, k < g → ψ.coeff k ≠ 0 →
--
lean/LeanUrat/HC1/DefsTower.lean-35-variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
lean/LeanUrat/HC1/DefsTower.lean-36-
lean/LeanUrat/HC1/DefsTower.lean-37-/-- The FULL D.3–D.7 increment hypothesis interface (the TRANSstage fence, D4(ii)):
lean/LeanUrat/HC1/DefsTower.lean-38-everything the note requires of a legal read, nothing more. FALSE at `e′ = 0`, at
lean/LeanUrat/HC1/DefsTower.lean-39-`ψ = X` (the note's ψ ≠ z), at reducible ψ, at a non-(I-aug) side. -/
lean/LeanUrat/HC1/DefsTower.lean:40:structure TransHyp (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
lean/LeanUrat/HC1/DefsTower.lean-41-    (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) : Prop where
lean/LeanUrat/HC1/DefsTower.lean-42-  hmonic : ψ.Monic
lean/LeanUrat/HC1/DefsTower.lean-43-  hirr : Irreducible ψ
lean/LeanUrat/HC1/DefsTower.lean-44-  hne_z : ψ ≠ Polynomial.X          -- ψ ≠ z (D.3 head)
lean/LeanUrat/HC1/DefsTower.lean-45-  hdeg : ψ.natDegree = g
--
lean/LeanUrat/HC2/K1_vertexPin.lean-12-
lean/LeanUrat/HC2/K1_vertexPin.lean-13-STRUCTURE (what is proved here / what is the one named residual):
lean/LeanUrat/HC2/K1_vertexPin.lean-14-* `K1_readVertexPin` — THE UNIFIED KERNEL (species-generic). Proof = species dichotomy:
lean/LeanUrat/HC2/K1_vertexPin.lean-15-  - RECENTERING parent: PROVED — consumed verbatim from the landed `NA_transport_recentering`
lean/LeanUrat/HC2/K1_vertexPin.lean-16-    (U20c, the g = 1 `IsStandardLift` route through `L5_landVertex`).
lean/LeanUrat/HC2/K1_vertexPin.lean:17:  - ROOT/INCREMENT parent: `K1_readVertexPin_nonrec` — the ONE remaining sorry, with the
lean/LeanUrat/HC2/K1_vertexPin.lean-18-    full obstruction record at its declaration (why no on-disk asset closes it; the exact
lean/LeanUrat/HC2/K1_vertexPin.lean-19-    carry-algebra design it needs).
lean/LeanUrat/HC2/K1_vertexPin.lean-20-* `K1_NA_transport_root` / `K1_NA_transport_increment` — U20a's/U20b's fenced statements
lean/LeanUrat/HC2/K1_vertexPin.lean-21-  VERBATIM (byte-identical conclusions and binders), one-line consumers of the kernel:
lean/LeanUrat/HC2/K1_vertexPin.lean-22-  the assigned provers can close the unit files by `exact` against these.
--
lean/LeanUrat/HC2/K1_vertexPin.lean-129-/-- **The K1 kernel residual** (read-indexed D.8 vertex law, NON-RECENTERING parent):
lean/LeanUrat/HC2/K1_vertexPin.lean-130-at consecutive reads of a run whose parent read `i` is a root or increment read, the
lean/LeanUrat/HC2/K1_vertexPin.lean-131-parent's line value at the standing vertex base is realized as the frame-(i+1) actual
lean/LeanUrat/HC2/K1_vertexPin.lean-132-slot weight of f's development at the vertex slot, and that vertex coefficient is
lean/LeanUrat/HC2/K1_vertexPin.lean-133-nonzero. QUEUED-HARD: the carry-algebra unit per the obstruction record above. -/
lean/LeanUrat/HC2/K1_vertexPin.lean:134:theorem K1_readVertexPin_nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/K1_vertexPin.lean-135-    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
lean/LeanUrat/HC2/K1_vertexPin.lean-136-    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
lean/LeanUrat/HC2/K1_vertexPin.lean-137-    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
lean/LeanUrat/HC2/K1_vertexPin.lean-138-    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
lean/LeanUrat/HC2/K1_vertexPin.lean-139-    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
--
lean/LeanUrat/HC2/K1_vertexPin.lean-161-        = (H.strFrame (i+1) : ℚ) *
lean/LeanUrat/HC2/K1_vertexPin.lean-162-          (H.nodes[i]'(by omega)).line.at
lean/LeanUrat/HC2/K1_vertexPin.lean-163-            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
lean/LeanUrat/HC2/K1_vertexPin.lean-164-  by_cases hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering
lean/LeanUrat/HC2/K1_vertexPin.lean-165-  · exact NA_transport_recentering h i hi1 hsp B Nd hdev hNd
lean/LeanUrat/HC2/K1_vertexPin.lean:166:  · exact K1_readVertexPin_nonrec h i hi1 hsp B Nd hdev hNd
lean/LeanUrat/HC2/K1_vertexPin.lean-167-
lean/LeanUrat/HC2/K1_vertexPin.lean-168-/-- U20a's fenced statement VERBATIM (F-2/U20a `NA_transport_root`), from the kernel —
lean/LeanUrat/HC2/K1_vertexPin.lean-169-the species hypothesis is not even needed (the kernel is species-generic); it is carried
lean/LeanUrat/HC2/K1_vertexPin.lean-170-so the unit file can close by `exact K1_NA_transport_root h i hi1 hsp B Nd hdev hNd`. -/
lean/LeanUrat/HC2/K1_vertexPin.lean-171-theorem K1_NA_transport_root {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC1/V9_K1nonrec.lean:77:  sorry
lean/LeanUrat/HC1/V9_K1nonrec.lean:95:  sorry
lean/LeanUrat/HC1/V4_readLanding.lean:74:  sorry
lean/LeanUrat/HC1/V2_readResidual.lean:53:  sorry
lean/LeanUrat/HC1/V2_readResidual.lean:62:  sorry
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine

/-!
# HC1/DefsChild — the D.7(vi)-normalized child residual (blueprint §9.5, S9r's Defs
home; ADDITIVE — no accepted statement touched)

**Provenance.** Blueprint §9.5 (the S9 decomposition, pre-approved split): `childR`
is "the D.7(vi)-NORMALIZED child residual on all of A (the new object; MOVES
2395–2418: normalize the minimal-slot development data by the transported unit
T′^{−w′(f)})". §9.5 does not display a Lean body, so the definition follows the
corpus's E-phase precedent for underdetermined Defs (`childW`, `Tower.side`):
CHOICE against a spec, with junk fallback.

**UNBUNDLED (2026-07-28 remediation round — the Codex batch-confirmation S9
rejection repair).** The E-phase draft of this file bundled the residual apparatus
+ tie laws as `ChildResData` FIELDS, which relocated §9.5's S9w hardness into
S9r's inhabitation sorry and reduced S9w to projections — exactly the confirmed
billing mismatch. Restored shape:
* `ChildResData` = ONLY the CHOICE-SPEC CARRIER — the residual function plus the
  two NORMALIZATION PINS that §9.5 assigns to S9r ("`childR` definition + the S5′
  shape lemma"): the S5′ PINNED shape (positions `−t′·σ.w B`, scalars = the parent
  ψ-digit — `digPrime`·(the pinned alignment), i.e. the K1 `VertexPin`
  normalization `mfun ≡ 0`) and the D.3(b) key pin `Rc Φ̂ = z^{s′}`.
* `ChildResLaws` = the LAW PACK as a `Prop` ON a carrier (§9.5's S9w list: the
  apparatus laws hR0/hRne/hRadd/hRlt/hRmul w.r.t. `childW`, in `Stage`'s own field
  shapes, + the two D.1(b) tie laws mentioning `Rc`: w_jump, R_neg). These are NO
  LONGER structure fields — proving a lawful carrier EXISTS is S9w's OWN theorem
  (`S9w_residualLaws`, the draft's "one genuinely new algebra block"), and the
  laws of the defined `childR` are its clearly-labeled projection corollary
  (`childR_laws`).
* `childR` = choice against carrier + laws (`∃ D, ChildResLaws D`) — the SAME
  witness class as the pre-unbundle bundled structure, so `childR`'s denotation
  is unchanged; only the unit boundaries moved.
S9r keeps its `Nonempty ChildResData` statement (now carrier-only: the
construction SEED; once S9w lands, S9r follows from its first conjunct).
`Tower`-level consumers never see `childR` directly — S9a records it through
`VertexPin` + the childW tie (the ↥K/↥K′ cast wall stays inside S9a's proof,
where the blueprint put it). Definitions only — no theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The D.7(vi)-normalized child residual CARRIER** (blueprint §9.5; UNBUNDLED at
the 2026-07-28 remediation round — see the file header): a residual function on all
of A for the read `(Φ̂, e′, h′, z̄)` over the child field `K′ = K⟮z̄⟯ =
σ.nextField z̄`, at the child Bézout pair `(s′, t′)`, carrying ONLY the two
D.7(vi) NORMALIZATION PINS — the choice-spec carrier (§9.5 S9r: "`childR`
definition + the S5′ shape lemma"). The apparatus/tie LAWS live in
`ChildResLaws` below (S9w's own content, no longer fields). S9r proves carrier
inhabitation (the seed); S9w constructs a LAWFUL carrier. -/
structure ChildResData (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) : Type u where
  /-- the residual function on all of A -/
  Rc : Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar)
  /-- D.3(b) at the child: the pinned key residual `R′(Φ̂) = z^{s′}` -/
  hRPhi : Rc Φhat = LaurentPolynomial.T s'
  /-- **the S5′ PINNED shape** (S9r's lemma; the D.7(vi) normalization — the K1
  `VertexPin` clause of the assembled stage): position `−t′·σ.w B`, scalar's
  F-image = the parent ψ-digit exactly (`mfun ≡ 0`, no frame twist) -/
  hS5' : ∀ B, B ≠ 0 → inC Φhat B →
      ∃ c' : (↥(σ.nextField zbar))ˣ,
        Rc B = LaurentPolynomial.C ((c' : ↥(σ.nextField zbar))) *
            LaurentPolynomial.T (- t' * σ.w B) ∧
        ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B

/-- **The child-residual LAW PACK** (blueprint §9.5's S9w list, as a `Prop` ON a
carrier — the 2026-07-28 unbundle; conjuncts in order: hR0, hRne, hRmul (the
carry-exact product — D7's cmul law through `L3_DIV`), hRadd, hRlt, hWjump,
hRneg): the D.1(e) residual apparatus w.r.t. `childW` in `Stage`'s own field
shapes, plus the two D.1(b) StageCore tie laws that mention `Rc`. Proving a
lawful carrier exists is `S9w_residualLaws`' OWN theorem content — the §9.5
"one genuinely new algebra block". -/
def ChildResLaws {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
    {zbar : Fˣ} {s' t' : ℤ} (D : ChildResData σ Φhat e' h' zbar s' t') : Prop :=
  (D.Rc 0 = 0) ∧
  (∀ f, f ≠ 0 → D.Rc f ≠ 0) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rc (f * g) = D.Rc f * D.Rc g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' (f + g) = childW σ Φhat e' h' f →
      D.Rc (f + g) = D.Rc f + D.Rc g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g → D.Rc (f + g) = D.Rc f) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g) →
      D.Rc f + D.Rc g = 0) ∧
  (∀ f, D.Rc (-f) = - D.Rc f)

open scoped Classical in
/-- **The D.7(vi)-normalized child residual** `childR`, by choice against a LAWFUL
carrier — carrier + `ChildResLaws`, the SAME witness class as the pre-unbundle
bundled structure, so the denotation is unchanged (the `childW`/`Tower.side`
precedent); junk `0` when the spec is uninhabited (never fires on legal reads
once S9w lands). -/
noncomputable def childR (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) :
    Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar) :=
  if h : ∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D then h.choose.Rc
  else fun _ => 0

/-- **The child parent-scale weight set 𝒜′** (§9.5 S9b: "weightSet := 𝒜′"): the
parent stage weights realized by nonzero Φ̂-coefficients — the set the assembled
child's `weightSet` field is pinned to (its `hWS` reads against
`σ'.wPrev = σ.w`, the `child_wPrev` record). -/
def childWeightSet (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) : Set ℤ :=
  {ν | ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν}

end LeanUrat.HC1
lean/LeanUrat/HC2/U1b_nodeLift.lean-31-    (hg : 1 ≤ g) (hh' : 1 ≤ h')
lean/LeanUrat/HC2/U1b_nodeLift.lean-32-    (hdvd : ∀ k : ℕ, k < g → (σ.e : ℤ) ∣ (h' : ℤ) * ((g : ℤ) - (k : ℤ)))
lean/LeanUrat/HC2/U1b_nodeLift.lean-33-    (hthr : ∀ k : ℕ, k < g → (σ.e : ℤ) * σ.wPrev σ.Φ < (h' : ℤ) * ((g : ℤ) - (k : ℤ))) :
lean/LeanUrat/HC2/U1b_nodeLift.lean:34:    ∃ Φhat, IsReadLift σ ψ g e' h' Φhat := by
lean/LeanUrat/HC2/U1b_nodeLift.lean-35-  classical
lean/LeanUrat/HC2/U1b_nodeLift.lean-36-  -- The stride `e = σ.e` is positive (`he`).
lean/LeanUrat/HC2/U1b_nodeLift.lean-37-  have he_pos : (0 : ℤ) < (σ.e : ℤ) := by have h := σ.he; omega
--
lean/LeanUrat/HC2/Defs.lean-164-    -- are literally the same proposition/term (structure eta).
lean/LeanUrat/HC2/Defs.lean-165-    rfl
lean/LeanUrat/HC2/Defs.lean-166-
lean/LeanUrat/HC2/Defs.lean:167:/-! ## D8 `IsReadLift` — the read-pair lift predicate (rev 2, the GAP-1 keying) -/
lean/LeanUrat/HC2/Defs.lean-168-
lean/LeanUrat/HC2/Defs.lean-169-/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
lean/LeanUrat/HC2/Defs.lean-170-`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
lean/LeanUrat/HC2/Defs.lean-171-ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
lean/LeanUrat/HC2/Defs.lean-172-F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
lean/LeanUrat/HC2/Defs.lean:173:def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/Defs.lean-174-    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
lean/LeanUrat/HC2/Defs.lean-175-    (Φhat : Polynomial ℤ_[p]) : Prop :=
lean/LeanUrat/HC2/Defs.lean-176-  ∃ tt : ℕ → Polynomial ℤ_[p],
--
lean/LeanUrat/HC2/Defs.lean-182-            LaurentPolynomial.T (- σ.t * σ.wPrev (tt k))) ∧
lean/LeanUrat/HC2/Defs.lean-183-    Φhat = σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)
lean/LeanUrat/HC2/Defs.lean-184-
lean/LeanUrat/HC2/Defs.lean:185:/-- Definitional (blueprint D8): `IsNodeLift` at the node's own read pair IS `IsReadLift`
lean/LeanUrat/HC2/Defs.lean-186-— both sides are the same formula at `(ψ, g, e', h') := (ν.ψ, ν.g, ν.e, ν.h)`. -/
lean/LeanUrat/HC2/Defs.lean-187-theorem isNodeLift_iff {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/Defs.lean-188-    (ν : Node p F) (Φhat : Polynomial ℤ_[p]) :
lean/LeanUrat/HC2/Defs.lean:189:    IsNodeLift ν Φhat ↔ IsReadLift ν.σ ν.ψ ν.g ν.e ν.h Φhat := Iff.rfl
lean/LeanUrat/HC2/Defs.lean-190-
lean/LeanUrat/HC2/Defs.lean-191-/-! ## §3 — the two NAMED HYPOTHESES (ours; hypothesis-NEVER-axiom; the P-1/P-3 dispositions) -/
lean/LeanUrat/HC2/Defs.lean-192-
--
lean/LeanUrat/HC2/Defs.lean-202-    ∀ (zbar : Fˣ), Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 →
lean/LeanUrat/HC2/Defs.lean-203-    ∀ (e' h' : ℕ) (s' t' : ℤ), 1 ≤ e' → 1 ≤ h' → Nat.gcd e' h' = 1 →
lean/LeanUrat/HC2/Defs.lean-204-      (e' : ℤ) * s' + (h' : ℤ) * t' = 1 → 0 ≤ t' ∧ t' < (e' : ℤ) →
lean/LeanUrat/HC2/Defs.lean:205:    ∀ (Φhat : Polynomial ℤ_[p]), IsReadLift σ ψ g e' h' Φhat →
lean/LeanUrat/HC2/Defs.lean-206-      IAug σ Φhat e' h' →
lean/LeanUrat/HC2/Defs.lean-207-    ∃ σ' : Stage p F, σ'.Φ = Φhat ∧ σ'.e = e' ∧ σ'.h = h' ∧ σ'.s = s' ∧ σ'.t = t' ∧
lean/LeanUrat/HC2/Defs.lean-208-      TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ'
--
lean/LeanUrat/HC2/Defs.lean-164-    -- are literally the same proposition/term (structure eta).
lean/LeanUrat/HC2/Defs.lean-165-    rfl
lean/LeanUrat/HC2/Defs.lean-166-
lean/LeanUrat/HC2/Defs.lean:167:/-! ## D8 `IsReadLift` — the read-pair lift predicate (rev 2, the GAP-1 keying) -/
lean/LeanUrat/HC2/Defs.lean-168-
lean/LeanUrat/HC2/Defs.lean-169-/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
lean/LeanUrat/HC2/Defs.lean-170-`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
lean/LeanUrat/HC2/Defs.lean-171-ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
lean/LeanUrat/HC2/Defs.lean-172-F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
lean/LeanUrat/HC2/Defs.lean:173:def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/Defs.lean-174-    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
lean/LeanUrat/HC2/Defs.lean-175-    (Φhat : Polynomial ℤ_[p]) : Prop :=
lean/LeanUrat/HC2/Defs.lean-176-  ∃ tt : ℕ → Polynomial ℤ_[p],
--
lean/LeanUrat/HC2/Defs.lean-182-            LaurentPolynomial.T (- σ.t * σ.wPrev (tt k))) ∧
lean/LeanUrat/HC2/Defs.lean-183-    Φhat = σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)
lean/LeanUrat/HC2/Defs.lean-184-
lean/LeanUrat/HC2/Defs.lean:185:/-- Definitional (blueprint D8): `IsNodeLift` at the node's own read pair IS `IsReadLift`
lean/LeanUrat/HC2/Defs.lean-186-— both sides are the same formula at `(ψ, g, e', h') := (ν.ψ, ν.g, ν.e, ν.h)`. -/
lean/LeanUrat/HC2/Defs.lean-187-theorem isNodeLift_iff {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
lean/LeanUrat/HC2/Defs.lean-188-    (ν : Node p F) (Φhat : Polynomial ℤ_[p]) :
lean/LeanUrat/HC2/Defs.lean:189:    IsNodeLift ν Φhat ↔ IsReadLift ν.σ ν.ψ ν.g ν.e ν.h Φhat := Iff.rfl
lean/LeanUrat/HC2/Defs.lean-190-
lean/LeanUrat/HC2/Defs.lean-191-/-! ## §3 — the two NAMED HYPOTHESES (ours; hypothesis-NEVER-axiom; the P-1/P-3 dispositions) -/
lean/LeanUrat/HC2/Defs.lean-192-
--
lean/LeanUrat/HC2/Defs.lean-202-    ∀ (zbar : Fˣ), Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 →
lean/LeanUrat/HC2/Defs.lean-203-    ∀ (e' h' : ℕ) (s' t' : ℤ), 1 ≤ e' → 1 ≤ h' → Nat.gcd e' h' = 1 →
lean/LeanUrat/HC2/Defs.lean-204-      (e' : ℤ) * s' + (h' : ℤ) * t' = 1 → 0 ≤ t' ∧ t' < (e' : ℤ) →
lean/LeanUrat/HC2/Defs.lean:205:    ∀ (Φhat : Polynomial ℤ_[p]), IsReadLift σ ψ g e' h' Φhat →
lean/LeanUrat/HC2/Defs.lean-206-      IAug σ Φhat e' h' →
lean/LeanUrat/HC2/Defs.lean-207-    ∃ σ' : Stage p F, σ'.Φ = Φhat ∧ σ'.e = e' ∧ σ'.h = h' ∧ σ'.s = s' ∧ σ'.t = t' ∧
lean/LeanUrat/HC2/Defs.lean-208-      TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ'

exec
/usr/bin/bash -lc "sed -n '165,186p' lean/LeanUrat/HC2/Defs.lean
rg -n -A24 -B4 \"def HasAnchorK|def OrdPsiPoly\" lean/LeanUrat -g '*.lean'
sed -n '120,150p' lean/LeanUrat/HC2/K1_vertexPin.lean
sed -n '70,108p' lean/LeanUrat/HC1/DefsTower.lean
rg -n \"V6_descentOrbits|V6_regradeOrbits|V7_stripDischarge\" lean/notes/HC1_LEAN_BLUEPRINT_2026-07-28.md lean/LeanUrat/HC1/MANIFEST.json" in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
    rfl

/-! ## D8 `IsReadLift` — the read-pair lift predicate (rev 2, the GAP-1 keying) -/

/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
    (Φhat : Polynomial ℤ_[p]) : Prop :=
  ∃ tt : ℕ → Polynomial ℤ_[p],
    (∀ k, ψ.coeff k = 0 → tt k = 0) ∧
    (∀ k, k < g → ψ.coeff k ≠ 0 →
        tt k ≠ 0 ∧ inC σ.Φ (tt k) ∧
          σ.w (tt k) = (h' : ℤ) * ((g : ℤ) - (k : ℤ)) ∧
          σ.R (tt k) = LaurentPolynomial.C (ψ.coeff k) *
            LaurentPolynomial.T (- σ.t * σ.wPrev (tt k))) ∧
    Φhat = σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)

/-- Definitional (blueprint D8): `IsNodeLift` at the node's own read pair IS `IsReadLift`
— both sides are the same formula at `(ψ, g, e', h') := (ν.ψ, ν.g, ν.e, ν.h)`. -/
lean/LeanUrat/Moves/Defs.lean-251-
lean/LeanUrat/Moves/Defs.lean-252-/-- **The z-anchor** `R f = z^a · R_anch(z)` with `R_anch ∈ K[z]`, `R_anch(0) ≠ 0` (so `a = ord_z`).
lean/LeanUrat/Moves/Defs.lean-253-The ψ-adic order is then read off `R_anch` as a POLYNOMIAL (DEF: never `ord_ψ` of a Laurent unit
lean/LeanUrat/Moves/Defs.lean-254-`X`). -/
lean/LeanUrat/Moves/Defs.lean:255:def HasAnchorK {K : Type u} [Field K] (x : LaurentPolynomial K) (a : ℤ) (Ranch : Polynomial K) :
lean/LeanUrat/Moves/Defs.lean-256-    Prop :=
lean/LeanUrat/Moves/Defs.lean-257-  Ranch.coeff 0 ≠ 0 ∧ x = LaurentPolynomial.T a * Polynomial.toLaurent Ranch
lean/LeanUrat/Moves/Defs.lean-258-
lean/LeanUrat/Moves/Defs.lean-259-/-- **ψ-adic order** `ord_ψ(Ranch) = μ`, defined over `Polynomial K` (F[z]-order, BEFORE Laurent —
lean/LeanUrat/Moves/Defs.lean-260-DEF fix): `ψ^μ ∣ R_anch` and `¬ ψ^{μ+1} ∣ R_anch`. -/
lean/LeanUrat/Moves/Defs.lean:261:def OrdPsiPoly {K : Type u} [Field K] (ψ Ranch : Polynomial K) (μ : ℕ) : Prop :=
lean/LeanUrat/Moves/Defs.lean-262-  ψ ^ μ ∣ Ranch ∧ ¬ ψ ^ (μ + 1) ∣ Ranch
lean/LeanUrat/Moves/Defs.lean-263-
lean/LeanUrat/Moves/Defs.lean-264-/-- **`σ'` is the recentering of `σ` by center `c̃` via lift `t`** (D.10, `e_read = 1`), stated as a
lean/LeanUrat/Moves/Defs.lean-265-field-by-field CONSTRUCTION relating `σ'` to `σ` per TRANS-RS's item list (DEF-10 fix — NOT an
lean/LeanUrat/Moves/Defs.lean-266-assumed unrelated stage). `Φ' = Φ − t` with `deg t < deg Φ`, `w(t) = w(Φ)`, `dig(t) = c̃`
lean/LeanUrat/Moves/Defs.lean-267-(position 0 since `e = 1`); and item by item: same valuation `w' = w` (S1, `v = v'`), same parent
lean/LeanUrat/Moves/Defs.lean-268-valuation `wPrev`, SAME residue field `K` and base `FQ` (no residue growth), same coefficient-digit
lean/LeanUrat/Moves/Defs.lean-269-map (S5 literally unchanged, stated at the F-valued `digPrime` level to dodge the `↥K`-vs-`↥K'`
lean/LeanUrat/Moves/Defs.lean-270-type wall), same weight set (S6). -/
lean/LeanUrat/Moves/Defs.lean-271-def IsRecentering {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]
lean/LeanUrat/Moves/Defs.lean-272-    (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p]) : Prop :=
lean/LeanUrat/Moves/Defs.lean-273-  σ.e = 1 ∧ σ'.e = 1 ∧
lean/LeanUrat/Moves/Defs.lean-274-    cc ≠ 0 ∧ inC σ.Φ tt ∧ tt ≠ 0 ∧ σ.w tt = σ.w σ.Φ ∧
lean/LeanUrat/Moves/Defs.lean-275-    σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ) ∧
lean/LeanUrat/Moves/Defs.lean-276-    σ'.Φ = σ.Φ - tt ∧
lean/LeanUrat/Moves/Defs.lean-277-    (∀ f, σ'.w f = σ.w f) ∧
lean/LeanUrat/Moves/Defs.lean-278-    (∀ f, σ'.wPrev f = σ.wPrev f) ∧
lean/LeanUrat/Moves/Defs.lean-279-    σ'.K = σ.K ∧ σ'.FQ = σ.FQ ∧ σ'.weightSet = σ.weightSet ∧
lean/LeanUrat/Moves/Defs.lean-280-    (∀ B, B ≠ 0 → inC σ.Φ B → ∀ zbar : Fˣ, σ'.digPrime zbar B = σ.digPrime zbar B)
lean/LeanUrat/Moves/Defs.lean-281-
lean/LeanUrat/Moves/Defs.lean-282-end LeanUrat.Moves
       composition inverts, and SideReads(i)'s support line at value gam transports to
       (BOX)+(VERTEX) of the child development: F(μ) = gam − μ·(ν.e·g − 1)·ν.h attained,
       B μ ≠ 0. The scale arithmetic below (`γ-tie + slope law + hLineU`) converts exactly
       this to the fenced ℚ-form. This is the ONE hard dedicated unit the kernel names —
       the read-side mirror of HC-1 §9.5's S9w block; no smaller on-disk lemma suffices
       (the fleet round-3 U20a/U20b chains were report-side only, and the F-2 spec's
       pointer to `L5_landTransport_R4` is frame-pair-keyed, see 3).
    ═══════════════════════════════════════════════════════════════════════════════════ -/

/-- **The K1 kernel residual** (read-indexed D.8 vertex law, NON-RECENTERING parent):
at consecutive reads of a run whose parent read `i` is a root or increment read, the
parent's line value at the standing vertex base is realized as the frame-(i+1) actual
slot weight of f's development at the vertex slot, and that vertex coefficient is
nonzero. QUEUED-HARD: the carry-algebra unit per the obstruction record above. -/
theorem K1_readVertexPin_nonrec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

/-- **THE READ-INDEXED D.8 VERTEX PIN** (the K1 kernel, species-generic): at consecutive
reads (i, i+1) of a run — ANY parent species — the parent's line value at the standing
vertex base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of f's
  | inc (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
      (hyp : TransHyp σ ψ g Φhat e' h' zbar)
      (core : TransitionCoreL σ σ' Φhat e' h' zbar)
      (core' : StageCoreL σ') : MoveWitness σ σ'
  | recenter (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
      (core : IsRecenteringCore σ σ' cc tt)
      (core' : StageCoreL σ') : MoveWitness σ σ'

/-- The faithful D.2 base pin (the baseStage fence, D4(i)/D5): parent valuation =
the Gauss valuation, reps = [C p] (U = {π}, representative p — MOVES 1999–2001),
current field = the base field. FALSE for the wPrev = 0 clone MovesGr certified
vacuous. -/
def IsBaseStage (σ : Stage p F) : Prop :=
  (∀ f, f ≠ 0 → σ.wPrev f = gaussVal f) ∧
  σ.reps = [Polynomial.C (p : ℤ_[p])] ∧ σ.K = σ.FQ

/-- **A tower**: base + K moves; `stg 0` faithfully based, every step witnessed.
Nonempty by gate T2 (depth 0) and S1's gate (depth 1). -/
structure Tower (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
  K : ℕ
  stg : Fin (K + 1) → Stage p F
  base : IsBaseStage (stg 0) ∧ StageCoreL (stg 0)
  move : ∀ k : Fin K, MoveWitness (stg k.castSucc) (stg k.succ)
  /-- **CHAR PIN (F-2, frontier adjudication 2026-07-28, blueprint §9.2):** the ambient
  residue field has characteristic p — intrinsic to the note's setting (the F_{k+1}/F_p
  extensions of MOVES 2148–2165 are residue fields of extensions of ℚ_p); the card-K
  bridge `Nat.card ↥K = p^[K:F_p]` (C6's conjuncts 2–3) is underivable without it
  (round-2 fleet kernel, commit 2f388c8). Excludes only note-rejected char ≠ p
  instantiations; every planned gate instance (T2/S1/G2: `GaloisField 2 2` at p = 2)
  satisfies it by instance. -/
  hcharF : CharP F p

namespace Tower

variable (T : Tower p F)

/-- e_birth per level (D6), on the underlying ℕ index (clamped junk beyond K): base
e at 0; an increment sets e′; a recentering KEEPS the previous value ("same C, same
v, same T" — TRANS-RS). ROOT CONVENTION (recorded decision (4)): `eBirth 0 = (stg 0).e`
lean/LeanUrat/HC1/MANIFEST.json:504:   "statement": "theorem V6_regradeOrbits … : ReadFrame.hS6a fill (regrade orbits = parent coset orbits re-positioned, scalars preserved); theorem V6_descentOrbits … : ∀ ν ∈ 𝒜′, (TRANSviii_a conjunct-1 window decomposition) ∧ ∃ base b(ν) of the displayed z̄-monomial shape whose F_Qˣ-coset is realized in D.Rc"
lean/LeanUrat/HC1/MANIFEST.json:507:   "id": "HC1.V7_stripDischarge",
lean/LeanUrat/HC1/MANIFEST.json:508:   "file": "lean/LeanUrat/HC1/V7_stripDischarge.lean",
lean/LeanUrat/HC1/MANIFEST.json:511:   "statement": "theorem V7_stripDischarge … (D : ChildResData …) (hD : ChildResLaws D) : ∀ ν ∈ childWeightSet σ Φ̂, ∃ b, ∀ c ∈ F_Qˣ, ∃ B ≠ 0 ∈ C_Φ̂, σ.w B = ν ∧ D.Rc B = C(c·b)·T(−t′·ν)  [EXACTLY S9a's hS6a′ obligation shape; gated on V5 — EXECUTED]"
lean/notes/HC1_LEAN_BLUEPRINT_2026-07-28.md:1904:* **V7 `V7_stripDischarge`** — S9a's single sorry closes: under V5's coset

codex
The statement audit is now complete. I found no critical mismatch, but two substantive documentation/specification gaps: V3’s advertised “equal weights display” is not actually tied to the lift witness and omits the leading-slot equation, and V6(b) omits the blueprint’s explicit λ-window/twist equations. I’m doing the final exact counts and line references now.
exec
/usr/bin/bash -lc "printf 'raw matches: '; grep -n sorry lean/LeanUrat/HC1/DefsV.lean lean/LeanUrat/HC1/V*.lean | wc -l
printf 'proof placeholders: '; rg -n '"'^[[:space:]]*sorry([[:space:]]|$)'"' lean/LeanUrat/HC1/DefsV.lean lean/LeanUrat/HC1/V*.lean | wc -l
printf 'per file placeholders:\\n'; rg -n '"'^[[:space:]]*sorry([[:space:]]|$)'"' lean/LeanUrat/HC1/DefsV.lean lean/LeanUrat/HC1/V*.lean | cut -d: -f1 | sort | uniq -c
printf 'V8 raw matches: '; grep -n sorry lean/LeanUrat/HC1/V8_childResidual.lean | wc -l
printf 'V8 placeholders: '; rg -n '"'^[[:space:]]*sorry([[:space:]]|$)'"' lean/LeanUrat/HC1/V8_childResidual.lean | wc -l
nl -ba lean/LeanUrat/HC1/V3_readLift.lean | sed -n '929,958p'
nl -ba lean/LeanUrat/HC1/V6_alignedOrbits.lean | sed -n '160,190p'
nl -ba lean/LeanUrat/HC1/DefsV.lean | sed -n '60,151p'
nl -ba lean/LeanUrat/HC1/V4_readLanding.lean | sed -n '43,77p'" in /data/users/asvin/math-and-lean/p-adic-splitting-densities
 succeeded in 0ms:
raw matches: 16
proof placeholders: 5
per file placeholders:
      2 lean/LeanUrat/HC1/V2_readResidual.lean
      1 lean/LeanUrat/HC1/V4_readLanding.lean
      2 lean/LeanUrat/HC1/V9_K1nonrec.lean
V8 raw matches: 2
V8 placeholders: 0
   929	theorem V3_readLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
   930	    (σ : Stage p F) (hσ : StageCoreL σ)
   931	    (estar hstar : ℕ) (sstar tstar : ℤ)
   932	    (hrp : ReadPair σ estar hstar sstar tstar)
   933	    (V : ReadFrame σ estar hstar sstar tstar)
   934	    (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hirr : Irreducible ψ)
   935	    (hne : ψ ≠ Polynomial.X) (hdeg : ψ.natDegree = g)
   936	    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat) :
   937	    (∀ tt : ℕ → Polynomial ℤ_[p],
   938	        (∀ k, k < g → ψ.coeff k ≠ 0 →
   939	          σ.w (tt k) = (hstar : ℤ) * ((g : ℤ) - (k : ℤ))) →
   940	        ∀ k, k < g → ψ.coeff k ≠ 0 →
   941	          (estar : ℤ) * σ.w (tt k) + ((estar : ℤ) * (k : ℤ)) * (hstar : ℤ)
   942	            = (estar : ℤ) * (hstar : ℤ) * (g : ℤ)) ∧
   943	    childW σ σ.Φ estar hstar Φhat = (estar : ℤ) * (hstar : ℤ) * (g : ℤ) ∧
   944	    V.D.Rv Φhat
   945	      = LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) *
   946	          Polynomial.toLaurent ψ ∧
   947	    K1At (childW σ σ.Φ estar hstar) Φhat ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
   948	  classical
   949	  have hee : 1 ≤ estar := hrp.1
   950	  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
   951	  have hg1 : 1 ≤ g := by
   952	    have := hirr.natDegree_pos
   953	    omega
   954	  obtain ⟨hΦne, hwhat, hRhat⟩ := v3_lift_core V hrp ψ g hmon hdeg hg1 Φhat hlift
   955	  obtain ⟨hMon, hDeg⟩ := v3_lift_monic hee ψ g hg1 Φhat hlift
   956	  refine ⟨?_, hwhat, hRhat, ?_⟩
   957	  · -- C1: the D.5 EQUAL WEIGHTS display at wV
   958	    intro tt htw k hk hc
   160	  rw [hc'Rv, hσwB, hCeq]
   161	
   162	/-- Unit V6(b): DESCENT orbit base points — every child weight ν ∈ 𝒜′ decomposes
   163	through a minimizing slot `(γ, j)` (the TRANSviii_a conjunct-1 window), and the
   164	choice of slot fixes ONE coset base `b(ν)` of the displayed z̄-monomial shape
   165	`(b : F) = (b̃ : F)·z̄^m`, whose F_Qˣ-coset is realized in the carrier `D.Rc`. -/
   166	theorem V6_descentOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
   167	    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
   168	    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
   169	    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
   170	    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0)
   171	    (D : ChildResData σ Φhat e' h' zbar s' t') (hD : ChildResLaws D) :
   172	    ∀ ν : ℤ, ν ∈ childWeightSet σ Φhat →
   173	      (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧
   174	        ν = γ + (j : ℤ) * (σ.h : ℤ)) ∧
   175	      ∃ b : (↥(σ.nextField zbar))ˣ,
   176	        (∃ (btilde : (↥σ.K)ˣ) (m : ℤ),
   177	          ((b : ↥(σ.nextField zbar)) : F)
   178	            = ((btilde : ↥σ.K) : F) * ((zbar ^ m : Fˣ) : F)) ∧
   179	        ∀ c : (↥(σ.nextField zbar))ˣ, ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
   180	          ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
   181	            D.Rc B = LaurentPolynomial.C
   182	                ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
   183	              LaurentPolynomial.T (- t' * ν) := by
   184	  classical
   185	  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
   186	  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
   187	  -- `σ.R 1 = 1` and `σ.w 1 = 0` (cancellation in the residual / valuation)
   188	  have hR1 : σ.R 1 = 1 := by
   189	    have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
   190	    rw [mul_one] at h
    60	the HC2 side extracted from `HistoryCoherent`'s slope law + strict steepening —
    61	`h_{i+1} > h_i·e_{i+1}·e_i·g_i ≥ e_{i+1}·h_i`, V9's short lemma). -/
    62	def ReadPair (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Prop :=
    63	  1 ≤ estar ∧ 1 ≤ hstar ∧ Nat.gcd estar hstar = 1 ∧
    64	    (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 ∧
    65	    (estar = 1 → tstar = 0) ∧
    66	    (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ)
    67	
    68	/-- **The regrade carrier** (blueprint §10 V0), mirroring `ChildResData`: a residual
    69	function on all of A for the regrade index (e★, h★, s★, t★) AT THE SAME KEY σ.Φ,
    70	carrying the two pins —
    71	* the key pin `Rv σ.Φ = T s★` (slot-1 arithmetic `1·s★ − t★·σ.w 1 = s★`);
    72	* the S5-shape pin: scalars PRESERVED from the frame residual, positions RE-FORCED
    73	  at the new pair (`−t★·σ.w B` — the (S5) position law at (e★, h★), MOVES 1960–1963). -/
    74	structure ReadResData (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
    75	  /-- the regrade residual function on all of A -/
    76	  Rv : Polynomial ℤ_[p] → LaurentPolynomial ↥σ.K
    77	  /-- the key pin `Rv(Φ) = z^{s★}` (D.3(b) at the regrade) -/
    78	  hRPhi : Rv σ.Φ = LaurentPolynomial.T sstar
    79	  /-- the S5-shape pin: SAME scalar as the frame digit, position re-forced at the
    80	  new pair — the (S5) position law `−t★·σ.w B` (MOVES 1960–1963) -/
    81	  hS5 : ∀ B, B ≠ 0 → inC σ.Φ B →
    82	      ∃ c : (↥σ.K)ˣ,
    83	        σ.R B = LaurentPolynomial.C (c : ↥σ.K) *
    84	            LaurentPolynomial.T (- σ.t * σ.wPrev B) ∧
    85	        Rv B = LaurentPolynomial.C (c : ↥σ.K) *
    86	            LaurentPolynomial.T (- tstar * σ.w B)
    87	
    88	/-- **The regrade law pack** (blueprint §10 V0): the D.1(e) laws of a regrade carrier
    89	w.r.t. the read functional `childW σ σ.Φ e★ h★` — the SAME seven conjuncts as
    90	`ChildResLaws` (hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg), at the regrade
    91	instance of (†). -/
    92	def ReadResLaws {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    93	    (D : ReadResData σ estar hstar sstar tstar) : Prop :=
    94	  (D.Rv 0 = 0) ∧
    95	  (∀ f, f ≠ 0 → D.Rv f ≠ 0) ∧
    96	  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rv (f * g) = D.Rv f * D.Rv g) ∧
    97	  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
    98	      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
    99	      childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f →
   100	      D.Rv (f + g) = D.Rv f + D.Rv g) ∧
   101	  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
   102	      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
   103	      D.Rv (f + g) = D.Rv f) ∧
   104	  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
   105	      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
   106	      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar (f + g) →
   107	      D.Rv f + D.Rv g = 0) ∧
   108	  (∀ f, D.Rv (-f) = - D.Rv f)
   109	
   110	/-- **The read frame** (blueprint §10 V0, Finding 3): the PARTIAL stage pack of the
   111	regrade — a lawful carrier + the wV laws (hwmul/hwult/hwΦ/hK1-at-Φ/hStretch) +
   112	hS6a in the current (post-V5 coset) `Stage.hS6a` form — everything the D.5/D.8
   113	reruns (V3/V4) consume; **NO hS6b** (unsatisfiable at regrades for σ.e > 1,
   114	Finding 3), NO hvalgrp, NO reps/Tvec. -/
   115	structure ReadFrame (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
   116	  /-- the lawful regrade carrier -/
   117	  D : ReadResData σ estar hstar sstar tstar
   118	  /-- the carrier is lawful (V2's content) -/
   119	  laws : ReadResLaws D
   120	  /-- wV is multiplicative (V1's content) -/
   121	  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 →
   122	      childW σ σ.Φ estar hstar (f * g)
   123	        = childW σ σ.Φ estar hstar f + childW σ σ.Φ estar hstar g
   124	  /-- wV is ultrametric -/
   125	  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
   126	      min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
   127	        ≤ childW σ σ.Φ estar hstar (f + g)
   128	  /-- the key's read weight is h★ (slot-1 arithmetic) -/
   129	  hwPhi : childW σ σ.Φ estar hstar σ.Φ = (hstar : ℤ)
   130	  /-- Lemma K1 at the frame's own key, in the read grading -/
   131	  hK1 : K1At (childW σ σ.Φ estar hstar) σ.Φ ((hstar : ℤ))
   132	  /-- the regrade stretch: wV = e★·σ.w on the coefficient space C_Φ -/
   133	  hStretch : ∀ B, B ≠ 0 → inC σ.Φ B →
   134	      childW σ σ.Φ estar hstar B = (estar : ℤ) * σ.w B
   135	  /-- (S6a) at the regrade, in the post-V5 fixed-point coset form (weights read
   136	  against wVPrev = σ.w, i.e. over `childWeightSet σ σ.Φ`); filled by V6(a) —
   137	  regrade scalars are PRESERVED, so the parent's coset bases transport. -/
   138	  hS6a : ∀ ν : ℤ, ν ∈ childWeightSet σ σ.Φ →
   139	      ∃ b : (↥σ.K)ˣ, ∀ c : (↥σ.K)ˣ, ((c : ↥σ.K) : F) ∈ σ.FQ →
   140	        ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ σ.w B = ν ∧
   141	          D.Rv B = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) *
   142	            LaurentPolynomial.T (- tstar * ν)
   143	
   144	end LeanUrat.HC1
    43	/-- Unit V4: the D.8 landing at the ReadFrame — (VERTEX), (BOX), and the vertex
    44	digit with its explicit unit `z̄^{μ·t★·h★·g}` (the `−μm̂★` normalization),
    45	transposing L5_landVertex/L5_landVertexDigit to the regrade pack.  The
    46	(TRANSPORT) leg is fenced OUT (see header). -/
    47	theorem V4_readLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    48	    (σ : Stage p F) (hσ : StageCoreL σ)
    49	    (estar hstar : ℕ) (sstar tstar : ℤ)
    50	    (hrp : ReadPair σ estar hstar sstar tstar)
    51	    (V : ReadFrame σ estar hstar sstar tstar)
    52	    (ψ : Polynomial ↥σ.K) (g : ℕ) (hdeg : ψ.natDegree = g) (hmon : ψ.Monic)
    53	    (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X)
    54	    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat)
    55	    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    56	    (Ranch : Polynomial ↥σ.K)
    57	    (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    58	    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) :
    59	    (B μ ≠ 0 ∧
    60	      childW σ σ.Φ estar hstar (B μ)
    61	          + (μ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))
    62	        = childW σ σ.Φ estar hstar f) ∧
    63	    (∀ m, m < μ → B m ≠ 0 →
    64	      childW σ σ.Φ estar hstar f
    65	        < childW σ σ.Φ estar hstar (B m)
    66	            + (m : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
    67	    (∀ zbar : Fˣ, Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 →
    68	      ∃ q : LaurentPolynomial ↥σ.K,
    69	        V.D.Rv f = (Polynomial.toLaurent ψ) ^ μ * q ∧
    70	        ¬ (Polynomial.toLaurent ψ ∣ q) ∧
    71	        LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) (V.D.Rv (B μ))
    72	          = ((zbar ^ ((μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ)) : Fˣ) : F) *
    73	            LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) q) := by
    74	  sorry
    75	
    76	end LeanUrat.HC1
    77	

codex
1. **NONE — `Stage.hS6a` was changed from the untwisted orbit to the intended fixed coset.**

   Old form:

   ```lean
   hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
     ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
       R B = LaurentPolynomial.C (c : ↥K) *
         LaurentPolynomial.T (-t * ν)
   ```

   New form:

   ```lean
   hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∃ b : (↥K)ˣ,
     ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
       ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
         R B = LaurentPolynomial.C
           ((c * b : (↥K)ˣ) : ↥K) *
           LaurentPolynomial.T (-t * ν)
   ```

   The authoritative text says:

   > “whose digit is `c·(the index's forced monomial class)` with `c` ranging over the CONSTANT orbit group `O := F_Qˣ`”

   and:

   > “whose dig′ is `c·(a fixed z̄-monomial class)`: the O-orbit with `O = F_Qˣ` CONSTANT”

   The quantifier order `∃ b` before `∀ c` is exactly what makes the class fixed for the weight rather than dependent on the orbit scalar. `b : Kˣ` is not required to lie in `FQ`, while only `c` is restricted to `F_Qˣ`; consequently the statement describes `F_Qˣ·b`, not the old untwisted `F_Qˣ`.

   This is strictly weaker than the old form, as intended, but not weaker than blueprint §10.1/V5, which explicitly chooses the base-free-in-`Kˣ` interface. It also does not silently break the consumers that need an arbitrary scalar: the base-stage consumers use `K = FQ` and replace `c` by `y·b⁻¹`, while the general above-threshold arbitrary-scalar property remains separately supplied by `hS6b`.

2. **GAP — the cited D.7(vi)–(vii) excerpt does not itself justify `mfun ≡ 0`.**

   The blueprint asserts:

   > “the parent pinning identity `z = V^{−h}Y^{e}` pushes to  
   > `Π dig′(ũ)^{−h·b_i}·dig′(Φ)^{e} = z̄` in `F′`), so the ‘alignment function’ … is the ZERO function”

   The supplied note excerpt establishes:

   > “`T = V^s·Y^t` and `z = V^{−h}·Y^e` BY PINNING”

   and later only:

   > “`dig′(B) = c′·z′^{k′(B)}` with the position determined by the new weight”

   It does not state the additional frame-change/evaluation identity sending the parent `z`-class exactly to the scalar `z̄`, nor the claimed `D`-injectivity step. Thus the excerpt supports the exponent-coordinate framework, but not the final zero-alignment conclusion by itself.

   This is a justification gap, not a contradiction in the applied Lean statements: V8 constructs the raw-evaluation carrier and proves its laws internally. The blueprint should cite the missing D.7(v) or frame-change identity explicitly if that is the real warrant.

3. **NONE — V0 `ReadPair` matches §10.1 exactly.**

   Lean:

   ```lean
   def ReadPair ... :=
     1 ≤ estar ∧ 1 ≤ hstar ∧ Nat.gcd estar hstar = 1 ∧
       (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 ∧
       (estar = 1 → tstar = 0) ∧
       (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ)
   ```

   Blueprint:

   > “`1 ≤ e★ ∧ 1 ≤ h★ ∧ gcd = 1 ∧ Bézout ∧ (e★ = 1 → t★ = 0) ∧ (e★:ℤ)·σ.h < h★`”

   There is no reordered existential or added assumption.

4. **NONE — V0 `ReadResData`, `ReadResLaws`, and `ReadFrame` match the intended partial frame.**

   The two carrier pins are:

   ```lean
   hRPhi : Rv σ.Φ = LaurentPolynomial.T sstar
   ```

   and:

   ```lean
   hS5 : ∀ B, B ≠ 0 → inC σ.Φ B →
     ∃ c,
       σ.R B = C c * T (-σ.t * σ.wPrev B) ∧
       Rv B  = C c * T (-tstar * σ.w B)
   ```

   This preserves the same scalar while replacing the position law, exactly as §10.1 specifies.

   `ReadResLaws` has the same seven conjuncts as `ChildResLaws`, in the same logical strengths. `ReadFrame` includes the lawful carrier, `hwmul`, `hwult`, `hwPhi`, `hK1`, `hStretch`, and `hS6a`, while omitting `hS6b`, `hvalgrp`, representatives, and `Tvec`.

   Its coset-form `hS6a` differs from §10.1’s stale word “untwisted”, but §10.4 explicitly records this post-V5 update. It is therefore documented rather than silent.

5. **NONE — V1 states the advertised slot-min pack, multiplicativity, ultrametricity, and Q-ascent.**

   The Q-ascent conclusion is:

   ```lean
   (estar : ℤ) * σ.w Rdev
       + (hstar - (estar : ℤ) * σ.h)
     ≤ (estar : ℤ) * σ.w Q + hstar
   ```

   With `ReadPair`’s

   ```lean
   (estar : ℤ) * σ.h < hstar
   ```

   this says precisely that the quotient’s next-slot value is at least the remainder-slot value plus the positive gap `h★ − e★·σ.h`.

   V1 additionally returns remainder nonvanishing and the exact remainder weight. That strengthens the conclusion rather than adding an unsupported hypothesis and is the same DIV fact used in the note’s D.6/D.7 argument.

6. **NONE — V2’s two statements have the §10.1 shapes.**

   Lean states:

   ```lean
   (∃ D : ReadResData ..., ReadResLaws D) ∧
     ∀ f g, ... → wV f < wV g → wV (f + g) = wV f
   ```

   and:

   ```lean
   Nonempty (ReadFrame σ estar hstar sstar tstar)
   ```

   These are exactly the lawful-carrier-plus-`w_strict` unit and the frame packaging corollary. No note hypothesis is dropped from their signatures.

   The eventual proof of `V2_readFrame` will need V6(a) or its argument; the current file does not import V6. Since the body is still `sorry`, this is a future dependency/import issue rather than a statement-strength change.

7. **GAP — V3’s explicit “EQUAL WEIGHTS” conjunct is weaker and less connected than advertised.**

   Lean states:

   ```lean
   ∀ tt,
     (∀ k, k < g → ψ.coeff k ≠ 0 →
       σ.w (tt k) = hstar * (g - k)) →
     ∀ k, k < g → ψ.coeff k ≠ 0 →
       estar * σ.w (tt k) + (estar * k) * hstar
         = estar * hstar * g
   ```

   The D.5 display instead identifies the actual standard-lift coefficients:

   > “each present slot has  
   > `w(t_k) + ek·h = eh(g−k) + ekh = ehg`,  
   > and the leading slot `0 + eg·h = ehg`”

   The Lean conjunct does not bind `tt` to the witness contained in `hlift`; it is a conditional arithmetic statement for any function satisfying the weight premise. A consumer can recover the intended fact by destructing `hlift` and applying this universal statement, so the information is not wholly lost, but the advertised direct statement about the lift witness is absent. More concretely, the leading-slot equality is not present at all.

   The remaining V3 conclusions do match D.5:

   ```lean
   wV Φhat = estar * hstar * g
   V.D.Rv Φhat = T (-tstar * hstar * g) * toLaurent ψ
   K1At wV Φhat (estar * hstar * g)
   ```

   The added assumptions `ψ.Monic`, `Irreducible ψ`, `ψ ≠ X`, and `ψ.natDegree = g` are not spurious: D.5 states exactly those hypotheses.

8. **NONE — V4 faithfully states VERTEX, BOX, and the vertex digit, and explicitly fences TRANSPORT.**

   Lean’s VERTEX is:

   ```lean
   B μ ≠ 0 ∧
     wV (B μ) + μ * (estar * hstar * g) = wV f
   ```

   BOX is:

   ```lean
   ∀ m, m < μ → B m ≠ 0 →
     wV f < wV (B m) + m * (estar * hstar * g)
   ```

   The digit factor is:

   ```lean
   zbar ^ (μ * tstar * hstar * g)
   ```

   which is `z̄^{-μm̂★}` because `m̂★ = −t★h★g`.

   The file says explicitly:

   > “the (TRANSPORT) leg is NOT needed … it is fenced OUT of this unit”

   Thus TRANSPORT was not silently removed from an unnamed conjunction. The hypotheses `HasAnchorK (V.D.Rv f) ...` and `OrdPsiPoly ψ Ranch μ` correctly concern the read residual rather than `σ.R f`.

9. **GAP — V6(b) weakens the blueprint’s explicit λ-window/twist display.**

   Blueprint §10.1 specifies:

   > “slots at child weight `ν` are  
   > `(γ,j) = (s·ν − λ·h, t·ν + λ·e)`,  
   > `λ ∈ (a g-window)`, twist = `λ`”

   Lean concludes only:

   ```lean
   ∃ γ j,
     ... ∧ j < σ.e * g ∧
     ν = γ + j * σ.h
   ```

   followed by:

   ```lean
   ∃ b,
     (∃ btilde m, (b : F) = (btilde : F) * zbar^m) ∧
     ∀ c ∈ FQ, ∃ B, ... ∧ D.Rc B = C(c*b) * T(-t' * ν)
   ```

   The theorem does not expose `λ`, its window bounds, the formulas for `γ` and `j`, or the equality `m = λ`. The proof may contain enough Bézout arithmetic to derive a suitable parameter, and the downstream V7 obligation needs only the final coset, but the public V6(b) statement is weaker than the unit statement promised in §10.1.

   This does not break the applied S9 chain because V7 was independently reproved without consuming V6(b), but it is a silent public-statement reduction that should be recorded.

10. **NONE — V6(a) and V7 have the required coset quantifier order and target shape.**

    V6(a) states:

    ```lean
    ∀ ν ∈ childWeightSet σ σ.Φ,
      ∃ b, ∀ c, (c : F) ∈ σ.FQ →
        ∃ B, ... ∧
          D.Rv B = C(c*b) * T(-tstar*ν)
    ```

    This is exactly `ReadFrame.hS6a`.

    V7 states:

    ```lean
    ∀ ν ∈ childWeightSet σ Φhat,
      ∃ b, ∀ c, (c : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
          D.Rc B = C(c*b) * T(-t' * ν)
    ```

    This is byte-shape-equivalent to S9a’s post-V5 `hS6a′` obligation. Its coverage of all child weights, with separate above- and below-threshold proof branches, is stronger than merely stating the strip subcase but is exactly what the Stage field requires.

    The departure from the planned “V6(b) + TRANSviii_a” proof route is prominently documented as avoiding a circular dependency, so it is not silent.

11. **NONE — V8’s public statements match the explicit descent carrier and full law-pack specification.**

    `ExplicitDescentCarrier` states the minimizing-slot sum:

    ```lean
    D.Rc f =
      ∑ j in minimizing-filter,
        C (cdig j) * T (j*s' - t'*σ.w (B j))
    ```

    with:

    ```lean
    (cdig j : F) = σ.digPrime zbar (B j)
    ```

    This is equivalent to the displayed use of the subtype element containing `digPrime`.

    `V8a_carrierAdditive` includes `ExplicitDescentCarrier` and exactly the additive/tie/negation legs. `V8b_carrierLaws` adds full `ChildResLaws`, including `hRmul`. `V8c_wStrict` has S9w’s strict law, and `V8_childResidual` assembles precisely S9w’s conjunction. No extra mathematical premise beyond `TransHyp`, the selected Bézout pair, and the standard `t′ = 0` pin is introduced.

12. **NONE — the V8 escalation narration matches the current file.**

    The file contains the claimed definitions:

    ```lean
    private def v8Deep (ω : ℤ) (x ...) : Prop :=
      x = 0 ∨ ω ≤ σ.w x

    private noncomputable def v8gr (ω : ℤ) (x ...) :=
      if x ≠ 0 ∧ σ.w x = ω then σ.R x else 0
    ```

    and the claimed additive calculus:

    ```lean
    private lemma v8gr_add ...
    ```

    It also contains completed bodies for `V8c_wStrict`, `V8a_carrierAdditive`, `V8b_carrierLaws`, and `V8_childResidual`. The product proof includes the in-file convolution development, `L3_DIV`, the carried-quotient depth argument, `v8gr` computations, and `Finset.sum_fiberwise_of_maps_to`, matching §10.6 rather than an earlier partial state.

13. **NONE — V9’s statements match §10.1 and the existing HC2 kernel verbatim.**

    The steepness lemma assumes `HistoryCoherent`, `1 ≤ i`, and non-recentering, and concludes:

    ```lean
    ν_i.e * ν_i.σ.h < ν_i.h
    ```

    exactly as specified for reads with a predecessor.

    `V9_K1nonrec` has the same binders, hypotheses, and conclusion as `K1_readVertexPin_nonrec`, including the non-recentering condition, development, `μ < Nd`, coefficient nonvanishing, and the rational weight equality. No extra usable hypothesis was added to make the target easier.

    The SideReads-(iii) issue remains fenced in the header; `SideReads` itself was not restated. V9 is still open, so the claimed derivation through that seam has not yet been accepted by a proof term.

14. **NONE — current `sorry` census is consistent with the latest V8 claim.**

    Literal `grep -n sorry` across `DefsV.lean` and `V*.lean` finds **16 textual matches**, because it also matches documentation such as “zero `sorry`”.

    Restricting to actual proof placeholders gives **5**:

    - `V2_readResidual.lean`: 2
    - `V4_readLanding.lean`: 1
    - `V9_K1nonrec.lean`: 2
    - `V1`, `V3`, `V6`, `V7`, `V8`, and `DefsV`: 0

    `V8_childResidual.lean` has 2 raw comment matches but **0 actual `sorry` commands**, confirming §10.6’s “V8 PROVED IN FULL” claim. The reduction from the historical 13 E-phase placeholders is therefore not a V8 contradiction.

Overall verdict: **ACCEPT** — no critical findings. The blueprint should nevertheless record or tighten the two public-statement gaps in V3 and V6(b), and supply the missing frame-change citation behind the `mfun ≡ 0` normalization argument.
tokens used
178,398
1. **NONE — `Stage.hS6a` was changed from the untwisted orbit to the intended fixed coset.**

   Old form:

   ```lean
   hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
     ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
       R B = LaurentPolynomial.C (c : ↥K) *
         LaurentPolynomial.T (-t * ν)
   ```

   New form:

   ```lean
   hS6a : ∀ ν : ℤ, ν ∈ weightSet → ∃ b : (↥K)ˣ,
     ∀ c : (↥K)ˣ, ((c : ↥K) : F) ∈ FQ →
       ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
         R B = LaurentPolynomial.C
           ((c * b : (↥K)ˣ) : ↥K) *
           LaurentPolynomial.T (-t * ν)
   ```

   The authoritative text says:

   > “whose digit is `c·(the index's forced monomial class)` with `c` ranging over the CONSTANT orbit group `O := F_Qˣ`”

   and:

   > “whose dig′ is `c·(a fixed z̄-monomial class)`: the O-orbit with `O = F_Qˣ` CONSTANT”

   The quantifier order `∃ b` before `∀ c` is exactly what makes the class fixed for the weight rather than dependent on the orbit scalar. `b : Kˣ` is not required to lie in `FQ`, while only `c` is restricted to `F_Qˣ`; consequently the statement describes `F_Qˣ·b`, not the old untwisted `F_Qˣ`.

   This is strictly weaker than the old form, as intended, but not weaker than blueprint §10.1/V5, which explicitly chooses the base-free-in-`Kˣ` interface. It also does not silently break the consumers that need an arbitrary scalar: the base-stage consumers use `K = FQ` and replace `c` by `y·b⁻¹`, while the general above-threshold arbitrary-scalar property remains separately supplied by `hS6b`.

2. **GAP — the cited D.7(vi)–(vii) excerpt does not itself justify `mfun ≡ 0`.**

   The blueprint asserts:

   > “the parent pinning identity `z = V^{−h}Y^{e}` pushes to  
   > `Π dig′(ũ)^{−h·b_i}·dig′(Φ)^{e} = z̄` in `F′`), so the ‘alignment function’ … is the ZERO function”

   The supplied note excerpt establishes:

   > “`T = V^s·Y^t` and `z = V^{−h}·Y^e` BY PINNING”

   and later only:

   > “`dig′(B) = c′·z′^{k′(B)}` with the position determined by the new weight”

   It does not state the additional frame-change/evaluation identity sending the parent `z`-class exactly to the scalar `z̄`, nor the claimed `D`-injectivity step. Thus the excerpt supports the exponent-coordinate framework, but not the final zero-alignment conclusion by itself.

   This is a justification gap, not a contradiction in the applied Lean statements: V8 constructs the raw-evaluation carrier and proves its laws internally. The blueprint should cite the missing D.7(v) or frame-change identity explicitly if that is the real warrant.

3. **NONE — V0 `ReadPair` matches §10.1 exactly.**

   Lean:

   ```lean
   def ReadPair ... :=
     1 ≤ estar ∧ 1 ≤ hstar ∧ Nat.gcd estar hstar = 1 ∧
       (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 ∧
       (estar = 1 → tstar = 0) ∧
       (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ)
   ```

   Blueprint:

   > “`1 ≤ e★ ∧ 1 ≤ h★ ∧ gcd = 1 ∧ Bézout ∧ (e★ = 1 → t★ = 0) ∧ (e★:ℤ)·σ.h < h★`”

   There is no reordered existential or added assumption.

4. **NONE — V0 `ReadResData`, `ReadResLaws`, and `ReadFrame` match the intended partial frame.**

   The two carrier pins are:

   ```lean
   hRPhi : Rv σ.Φ = LaurentPolynomial.T sstar
   ```

   and:

   ```lean
   hS5 : ∀ B, B ≠ 0 → inC σ.Φ B →
     ∃ c,
       σ.R B = C c * T (-σ.t * σ.wPrev B) ∧
       Rv B  = C c * T (-tstar * σ.w B)
   ```

   This preserves the same scalar while replacing the position law, exactly as §10.1 specifies.

   `ReadResLaws` has the same seven conjuncts as `ChildResLaws`, in the same logical strengths. `ReadFrame` includes the lawful carrier, `hwmul`, `hwult`, `hwPhi`, `hK1`, `hStretch`, and `hS6a`, while omitting `hS6b`, `hvalgrp`, representatives, and `Tvec`.

   Its coset-form `hS6a` differs from §10.1’s stale word “untwisted”, but §10.4 explicitly records this post-V5 update. It is therefore documented rather than silent.

5. **NONE — V1 states the advertised slot-min pack, multiplicativity, ultrametricity, and Q-ascent.**

   The Q-ascent conclusion is:

   ```lean
   (estar : ℤ) * σ.w Rdev
       + (hstar - (estar : ℤ) * σ.h)
     ≤ (estar : ℤ) * σ.w Q + hstar
   ```

   With `ReadPair`’s

   ```lean
   (estar : ℤ) * σ.h < hstar
   ```

   this says precisely that the quotient’s next-slot value is at least the remainder-slot value plus the positive gap `h★ − e★·σ.h`.

   V1 additionally returns remainder nonvanishing and the exact remainder weight. That strengthens the conclusion rather than adding an unsupported hypothesis and is the same DIV fact used in the note’s D.6/D.7 argument.

6. **NONE — V2’s two statements have the §10.1 shapes.**

   Lean states:

   ```lean
   (∃ D : ReadResData ..., ReadResLaws D) ∧
     ∀ f g, ... → wV f < wV g → wV (f + g) = wV f
   ```

   and:

   ```lean
   Nonempty (ReadFrame σ estar hstar sstar tstar)
   ```

   These are exactly the lawful-carrier-plus-`w_strict` unit and the frame packaging corollary. No note hypothesis is dropped from their signatures.

   The eventual proof of `V2_readFrame` will need V6(a) or its argument; the current file does not import V6. Since the body is still `sorry`, this is a future dependency/import issue rather than a statement-strength change.

7. **GAP — V3’s explicit “EQUAL WEIGHTS” conjunct is weaker and less connected than advertised.**

   Lean states:

   ```lean
   ∀ tt,
     (∀ k, k < g → ψ.coeff k ≠ 0 →
       σ.w (tt k) = hstar * (g - k)) →
     ∀ k, k < g → ψ.coeff k ≠ 0 →
       estar * σ.w (tt k) + (estar * k) * hstar
         = estar * hstar * g
   ```

   The D.5 display instead identifies the actual standard-lift coefficients:

   > “each present slot has  
   > `w(t_k) + ek·h = eh(g−k) + ekh = ehg`,  
   > and the leading slot `0 + eg·h = ehg`”

   The Lean conjunct does not bind `tt` to the witness contained in `hlift`; it is a conditional arithmetic statement for any function satisfying the weight premise. A consumer can recover the intended fact by destructing `hlift` and applying this universal statement, so the information is not wholly lost, but the advertised direct statement about the lift witness is absent. More concretely, the leading-slot equality is not present at all.

   The remaining V3 conclusions do match D.5:

   ```lean
   wV Φhat = estar * hstar * g
   V.D.Rv Φhat = T (-tstar * hstar * g) * toLaurent ψ
   K1At wV Φhat (estar * hstar * g)
   ```

   The added assumptions `ψ.Monic`, `Irreducible ψ`, `ψ ≠ X`, and `ψ.natDegree = g` are not spurious: D.5 states exactly those hypotheses.

8. **NONE — V4 faithfully states VERTEX, BOX, and the vertex digit, and explicitly fences TRANSPORT.**

   Lean’s VERTEX is:

   ```lean
   B μ ≠ 0 ∧
     wV (B μ) + μ * (estar * hstar * g) = wV f
   ```

   BOX is:

   ```lean
   ∀ m, m < μ → B m ≠ 0 →
     wV f < wV (B m) + m * (estar * hstar * g)
   ```

   The digit factor is:

   ```lean
   zbar ^ (μ * tstar * hstar * g)
   ```

   which is `z̄^{-μm̂★}` because `m̂★ = −t★h★g`.

   The file says explicitly:

   > “the (TRANSPORT) leg is NOT needed … it is fenced OUT of this unit”

   Thus TRANSPORT was not silently removed from an unnamed conjunction. The hypotheses `HasAnchorK (V.D.Rv f) ...` and `OrdPsiPoly ψ Ranch μ` correctly concern the read residual rather than `σ.R f`.

9. **GAP — V6(b) weakens the blueprint’s explicit λ-window/twist display.**

   Blueprint §10.1 specifies:

   > “slots at child weight `ν` are  
   > `(γ,j) = (s·ν − λ·h, t·ν + λ·e)`,  
   > `λ ∈ (a g-window)`, twist = `λ`”

   Lean concludes only:

   ```lean
   ∃ γ j,
     ... ∧ j < σ.e * g ∧
     ν = γ + j * σ.h
   ```

   followed by:

   ```lean
   ∃ b,
     (∃ btilde m, (b : F) = (btilde : F) * zbar^m) ∧
     ∀ c ∈ FQ, ∃ B, ... ∧ D.Rc B = C(c*b) * T(-t' * ν)
   ```

   The theorem does not expose `λ`, its window bounds, the formulas for `γ` and `j`, or the equality `m = λ`. The proof may contain enough Bézout arithmetic to derive a suitable parameter, and the downstream V7 obligation needs only the final coset, but the public V6(b) statement is weaker than the unit statement promised in §10.1.

   This does not break the applied S9 chain because V7 was independently reproved without consuming V6(b), but it is a silent public-statement reduction that should be recorded.

10. **NONE — V6(a) and V7 have the required coset quantifier order and target shape.**

    V6(a) states:

    ```lean
    ∀ ν ∈ childWeightSet σ σ.Φ,
      ∃ b, ∀ c, (c : F) ∈ σ.FQ →
        ∃ B, ... ∧
          D.Rv B = C(c*b) * T(-tstar*ν)
    ```

    This is exactly `ReadFrame.hS6a`.

    V7 states:

    ```lean
    ∀ ν ∈ childWeightSet σ Φhat,
      ∃ b, ∀ c, (c : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
          D.Rc B = C(c*b) * T(-t' * ν)
    ```

    This is byte-shape-equivalent to S9a’s post-V5 `hS6a′` obligation. Its coverage of all child weights, with separate above- and below-threshold proof branches, is stronger than merely stating the strip subcase but is exactly what the Stage field requires.

    The departure from the planned “V6(b) + TRANSviii_a” proof route is prominently documented as avoiding a circular dependency, so it is not silent.

11. **NONE — V8’s public statements match the explicit descent carrier and full law-pack specification.**

    `ExplicitDescentCarrier` states the minimizing-slot sum:

    ```lean
    D.Rc f =
      ∑ j in minimizing-filter,
        C (cdig j) * T (j*s' - t'*σ.w (B j))
    ```

    with:

    ```lean
    (cdig j : F) = σ.digPrime zbar (B j)
    ```

    This is equivalent to the displayed use of the subtype element containing `digPrime`.

    `V8a_carrierAdditive` includes `ExplicitDescentCarrier` and exactly the additive/tie/negation legs. `V8b_carrierLaws` adds full `ChildResLaws`, including `hRmul`. `V8c_wStrict` has S9w’s strict law, and `V8_childResidual` assembles precisely S9w’s conjunction. No extra mathematical premise beyond `TransHyp`, the selected Bézout pair, and the standard `t′ = 0` pin is introduced.

12. **NONE — the V8 escalation narration matches the current file.**

    The file contains the claimed definitions:

    ```lean
    private def v8Deep (ω : ℤ) (x ...) : Prop :=
      x = 0 ∨ ω ≤ σ.w x

    private noncomputable def v8gr (ω : ℤ) (x ...) :=
      if x ≠ 0 ∧ σ.w x = ω then σ.R x else 0
    ```

    and the claimed additive calculus:

    ```lean
    private lemma v8gr_add ...
    ```

    It also contains completed bodies for `V8c_wStrict`, `V8a_carrierAdditive`, `V8b_carrierLaws`, and `V8_childResidual`. The product proof includes the in-file convolution development, `L3_DIV`, the carried-quotient depth argument, `v8gr` computations, and `Finset.sum_fiberwise_of_maps_to`, matching §10.6 rather than an earlier partial state.

13. **NONE — V9’s statements match §10.1 and the existing HC2 kernel verbatim.**

    The steepness lemma assumes `HistoryCoherent`, `1 ≤ i`, and non-recentering, and concludes:

    ```lean
    ν_i.e * ν_i.σ.h < ν_i.h
    ```

    exactly as specified for reads with a predecessor.

    `V9_K1nonrec` has the same binders, hypotheses, and conclusion as `K1_readVertexPin_nonrec`, including the non-recentering condition, development, `μ < Nd`, coefficient nonvanishing, and the rational weight equality. No extra usable hypothesis was added to make the target easier.

    The SideReads-(iii) issue remains fenced in the header; `SideReads` itself was not restated. V9 is still open, so the claimed derivation through that seam has not yet been accepted by a proof term.

14. **NONE — current `sorry` census is consistent with the latest V8 claim.**

    Literal `grep -n sorry` across `DefsV.lean` and `V*.lean` finds **16 textual matches**, because it also matches documentation such as “zero `sorry`”.

    Restricting to actual proof placeholders gives **5**:

    - `V2_readResidual.lean`: 2
    - `V4_readLanding.lean`: 1
    - `V9_K1nonrec.lean`: 2
    - `V1`, `V3`, `V6`, `V7`, `V8`, and `DefsV`: 0

    `V8_childResidual.lean` has 2 raw comment matches but **0 actual `sorry` commands**, confirming §10.6’s “V8 PROVED IN FULL” claim. The reduction from the historical 13 E-phase placeholders is therefore not a V8 contradiction.

Overall verdict: **ACCEPT** — no critical findings. The blueprint should nevertheless record or tighten the two public-statement gaps in V3 and V6(b), and supply the missing frame-change citation behind the `mfun ≡ 0` normalization argument.
