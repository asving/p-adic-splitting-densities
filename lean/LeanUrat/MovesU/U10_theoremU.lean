/-
Unit U10.theoremU  (MovesU campaign)  [capstone — THE one structure-carrying theorem]
[ROUND-2 RETYPE 2026-07-29, commit 3728b00 (date corrected 2026-07-30; original record
 mis-dated 2026-07-31) per notes/MOVESU_RATIFICATION_ROUNDS_2026-07-30.md ROUND 2 — the
 durable archive of /tmp/leanratify_u2/verdict.txt (REJECT 6/1) — the warrant]
moves_ref: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
           prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p), and
           ρ_σ(p) IS the splitting density of type σ over ℤ_p — the undecided
           complement has mass 0 and the classifier verdicts are the true
           factorization types … Σ_σ R_σ = 1 identically in q (RS.4). … The
           quantifier 'for EVERY prime p' reads: every p satisfying (REG-p)."
deps: U6, U7, U11.
ROUND-2 deltas (each per a verdict finding):
  * CRITICAL 1: the bare-`Prop` pack `UpstreamKernelStatements` is RETIRED. Typed
    p-uniform rows ride `UpstreamTyped`/`Cl7Kernel` (over the carried MovesX/
    MovesRBase/MovesV corpora); the per-p (SIB)/(JC-multi) rows ride
    `UInstance.sibjc` at the pinned MovesT instance. The GENUINELY
    vocabulary-less rows are EXPLICIT named `Prop` parameters below — visible in
    the signature, never a bundled tag.
  * CRITICAL 2: `UInstance.Tpin` — the tree/classifier identification premise.
  * CRITICAL 3/4: `RegP` is the exact (r1)∧(r2) schema over the extended `RegPin`.
  * CRITICAL 5: the ℤ_p clause reads the (ramIdx, resDeg)-pinned bridge.
  * CRITICAL 6: the decided-family bound is the p-UNIFORM `K7.Tbound`.
  * GAP 1: the evaluated checksum is DERIVED (`SolveSeam.rs4_eval`).
hypothesis_fields: the COMPLETE retyped ledger via `UInstance` at every prime +
        explicit `RegP` per adjudicated p. At a p failing (REG-p): NO CLAIM (D8).
ROUND-3 deltas (executed 2026-07-29, commit 00b03aa; warrant
    notes/MOVESU_RATIFICATION_ROUNDS_2026-07-30.md ROUND 3 — the durable archive of
    /tmp/finalratify_u/verdict.txt, REJECT 4/0):
  * CRITICAL 1: `TreePin.chart` guarded to positive levels (the N = 0
    uninhabitability killed; witness `chartWitness`).
  * CRITICAL 3: `TreePin.vt_surj` — the completeness direction onto the
    realizable complete canonical `MovesT.VTree` corpus.
  * CRITICAL 4: `RegPin.legEquiv`/`legSt_pin` — the β-leg labels biject onto
    the REAL consumed roster (`LegRoster`), targets read by `legTarget`.
  * CRITICAL 2 (ADJUDICATED — record only): the WAVE-4 BOUNDARY paragraph in
    the docstring below.
-/
import Mathlib
import LeanUrat.MovesU.U6_un_bracket
import LeanUrat.MovesU.U7_squeeze
import LeanUrat.MovesU.U11_identification

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- THEOREM U (CONDITIONAL — on the round-2 retyped capstone ledger; SQ.4). "For
    each splitting type σ of degree n … there is ONE fixed rational function
    R_σ ∈ ℚ(q)" — the ∃ binds ONE family BEFORE the prime quantifier (F11), and
    the conclusion PINS it: `R = S.R`, the solve's family (tied to the real
    RS.1-SH output by `ssrc.r_is_solve`). At EVERY prime p satisfying (REG-p):
    the two-sided (U-n) bracket at every level; ρ_σ(p) exists and equals the
    literal R_σ(p); the TRUE-type density is the same limit; the ℤ_p-READ density
    (every monic ℤ_p lift factors to σ with the (e, f) = (ramIdx, resDeg)-pinned
    reading — round-2 CRITICAL 5) is the same limit; the undecided complement has
    mass 0. Σ_σ R_σ = 1 identically in ℚ(q). At a p failing (REG-p): NO CLAIM (D8).

    THE RESIDUAL BARE ROWS (round-2 CRITICAL 1's rule: a row with GENUINELY no
    built vocabulary stays a bare `Prop` ONLY as an explicit parameter, visible
    here — each named, with owner; every typed face that DOES exist is asserted
    at `UpstreamTyped`/`Cl7Kernel`/`sibjc` instead):
    * `rel1`, `rel2a`, `rel2b`, `rel2d`, `rel2e`, `rel3` — CL-8's six REL rows
      (owner [2r]; the typed (EQ-2) face is `KT.cl8_eq2`; (e)'s operative trace is
      the carried `C.chain.legs_read`);
    * `rs0Lump` — CL-9(α) RS.0 lumpability (owner [3]);
    * `trackRule` — CL-7a's (t1)/(t2) key/branch recognitions + the (c1)
      assignment map (owner [4]; the (t3) restart face and the L(n) bound are
      typed at `K7.track_restarts`);
    * `dnLattice` — CL-7b's key-weight lattice duty (all key weights in
      (1/D(n))·ℤ, candidate D(n) | n!) + the per-node strict-increment sub-claim
      (owner [4]; the D(n) constant and the budget/genuine bounds are typed at
      `K7`);
    * `m1m5Echo` — CL-14, the [2a] M1+M5 catalogue echo row (closed upstream;
      the instance tie to this seam is unbuilt);
    * `x1aDict` — CL-15's per-species GMN index dictionary beyond the typed
      ALIGN face `KT.cl15_align` (owner [5]);
    * `m4bConst` — CL-16, M4b height-translation constancy + M4b-T equivariance
      (owner [1v]/[2b]);
    * `jcInvHist` — CL-19's h_ent/history-invariance residue beyond the typed
      `cl19_rep` face (owner [2b]).

    THE WAVE-4 BOUNDARY RECORD (round-3 CRITICAL 2, ADJUDICATED —
    notes/MOVESU_RATIFICATION_ROUNDS_2026-07-30.md ROUND 3, the durable archive
    of /tmp/finalratify_u/verdict.txt: "A caller can instantiate every one with
    `True` and provide `True.intro` … Visibility is not semantic pinning"): the
    13 explicit `Prop` parameters above are the WAVE-4 BOUNDARY — the owner
    vocabulary for these rows is ABSENT from the built corpus, and wave-D
    discharges them by building their carriers. These 13 premises are UNPINNED
    (True-instantiable) pending the wave-D carriers; the conditionality claim
    of record must say so: any statement of Theorem U's conditionality MUST
    list these 13 rows as UNPINNED named assumptions (no typed mathematical
    obligation is imposed by them yet), NEVER as discharged or typed rows.

    UNUSED-HYPOTHESIS INVENTORY (2026-07-30 verify-2 fold-in): beyond the 13
    bare-Prop rows above, the fidelity binder `hn : 2 ≤ n` is ALSO unused by
    the proof body (masked by this file's `linter.unusedVariables false`) —
    14 unused hypotheses total. `hn` is statement-fenced: it transcribes the
    note's degree-n ≥ 2 quantifier and stays in the signature. -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n)
    (KT : UpstreamTyped n KC)
    (rel1 rel2a rel2b rel2d rel2e rel3 : Prop)
    (rs0Lump trackRule dnLattice : Prop)
    (m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b) (hrel2d : rel2d)
    (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrk : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst) (hjc : jcInvHist)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    ∃ R : SplittingType n → RatFunc ℚ,
      R = S.R ∧
      (∑ σ, R σ = 1) ∧
      ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
        -- (U-n): the exported two-sided bracket
        (∀ (σ : SplittingType n) (N : ℕ),
          (evalℝ ⟨R⟩ σ p - (inst p hp).X.env N) * (p : ℝ) ^ (n * N)
              ≤ ((inst p hp).X.decided σ N : ℝ) ∧
            ((inst p hp).X.decided σ N : ℝ)
              ≤ evalℝ ⟨R⟩ σ p * (p : ℝ) ^ (n * N))
        -- (i) the classifier-keyed density (the note's ρ_σ(p) = R_σ(p), T_can-keyed)
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.dmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii) the identification corollary (U11; via cl10_vpsound : VPSound X)
        ∧ (∀ σ : SplittingType n,
          Tendsto ((inst p hp).X.trueDmass σ) atTop (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (ii-ℤ_p) the SAME limit for the ℤ_p-READ density (the NAMED bridge:
        --     classes whose every monic lift factors to σ over ℚ_p, the pair
        --     read as (ramIdx, resDeg) — round-2 CRITICAL 5)
        ∧ (∀ σ : SplittingType n,
          Tendsto (@ZpBridge.zpDmass n p ⟨hp⟩ _ (inst p hp).bridge σ) atTop
            (𝓝 (evalℝ ⟨R⟩ σ p)))
        -- (iii) the undecided complement has mass 0
        ∧ Tendsto (inst p hp).X.env atTop (𝓝 0) := by
  -- Witness: the solve's fixed rational family, EXPORTED as such (GAP 2).
  refine ⟨S.R, rfl, (inst 2 Nat.prime_two).L.rs4_checksum, ?_⟩
  intro p hp hreg
  set U := inst p hp with hU
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- the (U-n) bracket at every (σ, N), from U6 on the ledger's typed seams
  -- (the evaluated checksum now DERIVED from `rs4_checksum` — round-2 GAP 1).
  have hbr : ∀ (σ : SplittingType n) (N : ℕ),
      (evalℝ ⟨S.R⟩ σ p - U.X.env N) * (p : ℝ) ^ (n * N) ≤ (U.X.decided σ N : ℝ) ∧
      (U.X.decided σ N : ℝ) ≤ evalℝ ⟨S.R⟩ σ p * (p : ℝ) ^ (n * N) :=
    fun σ N => un_bracket U.L.seam U.L.ssrc U.Dpin U.L.rs4_checksum hreg hp σ N
  -- clause (i): U7 squeeze on the bracket + env → 0.
  have hi : ∀ σ : SplittingType n,
      Tendsto (U.X.dmass σ) atTop (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ =>
    squeeze_limit U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ (hbr σ) U.L.cl4_env_tendsto
  -- clause (ii): U11 identification (VP-SOUND + env → 0).
  have hii : ∀ σ : SplittingType n,
      Tendsto (U.X.trueDmass σ) atTop (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ =>
    identification U.X hp.one_lt (evalℝ ⟨S.R⟩ σ p) σ
      U.L.cl10_vpsound (hi σ) U.L.cl4_env_tendsto
  -- clause (ii-ℤ_p): the bridge equates the ℤ_p-read density with the true density.
  haveI : Fact p.Prime := ⟨hp⟩
  have hzp : ∀ σ : SplittingType n,
      Tendsto (@ZpBridge.zpDmass n p ⟨hp⟩ _ U.bridge σ) atTop
        (𝓝 (evalℝ ⟨S.R⟩ σ p)) := fun σ => by
    rw [ZpBridge.zpDmass_eq_trueDmass]
    exact hii σ
  exact ⟨hbr, hi, hii, hzp, U.L.cl4_env_tendsto⟩

end LeanUrat.MovesU
