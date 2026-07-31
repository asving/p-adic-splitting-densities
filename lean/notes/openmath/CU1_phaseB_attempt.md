# CU-1 — no-missing + interior adequacy + state binding — Phase-B attempt, unit record (Fable, 2026-07-31)

Unit "CU1" per the ACCEPTED plan (`O3adj_adjudication.md` §3.1/§3.4/§3.5;
`SYNTHESIS_PASS4_2026-08-01.md` §2.3; ledger dbccbc1). Charge: RUN THE GATE
FIRST — the depth-3 falsifier O3adj promoted to CU-1's primary gate (extend
`o1thr_rev3_depth2_check.py` to depth 3 at order-2 states, where (V1)/(V2)
are genuinely consumed); if it fires, report and STOP; on survival, write
the CU-1 proof + verify brief. Both halves executed.

## 1. The gate: T-G at depth 3 — SURVIVES (with one convention finding)

**New falsifier:** `verification/openmath/o1thr_depth3_check.py`. Per
(box, depth-1 site, depth-2 site): builds the order-1 state (standard key
Φ₁, sloped valuation w₁ — the T-F-verified layer), harvests depth-2 sites
from the sloped window hull with residuals computed in K₁ = 𝔽_p[z]/ψ(z)
(new 𝔽_q arithmetic + factorization), builds the order-2 frame
w₂(B) = min_j (e₁·w₁(c_j) + j·γ₂) (§1.1's MacLane composite at i = 1) and
the standard level-2 key Φ₂ from the harvested ψ₁, and checks the FULL
Φ₂-development geometry: T-G.0 (R1)-support, T-G.1a/b/c (WGEO(a), (V2b)
at f, the vertex law with first attainment at μ₁ + the VTX pin), T-G.2/3
((M6c)(i)/(ii) at the order-2 state), T-G.4 (VTX chain, (V2b)-at-level-1),
T-G.5 (DIRECT (V1) multiplicativity probes on product pairs), T-G.6
(DIRECT (V2b) development-identity probes). This is exactly the per-site
kernel of CU-1's step, probed where the O-1thr rev-4 perimeter is
citation-grade rather than proved.

**Result (2026-07-31, this machine, exact integer arithmetic; log
`verification/openmath/logs/o1thr_depth3_run_20260731_151242.log`):**
configs (2,4,4), (3,4,3), (2,6,3), (3,3,4), (2,6,4), (2,8,3) —

    470,736 order-2 instances, ZERO violations of all nine checks.
    Coverage: 122,577 with beyond-window slots; 10,935 growth steps
    (e₁g₁ ≥ 2); 16,472 extension-field parents (g ≥ 2); 2,091 children
    with g₁ ≥ 2; saturated parents included (state-hypothesis-free laws).

**GATE SURVIVES → the CU-1 spec was licensed and executed (§2).**

**The finding (falsifier-first discipline paying out):** the checker's
first version normalized level-1 residues slot-fresh ("naive" fresh-t₀
reading) and FIRED — 60 vertex-law violations at (3,3,3). Hand-verifying
the first instance (f = X³+3X²+3X, p = 3, site (e,h,ψ,μ) = (2,1,z+1,1),
face (0,4)–(1,3)) showed a CHECKER-CONVENTION defect, not a package
countermodel: the naive residual selects ψ₁ = z′+2, whose standard lift
X²+6X+3 is a non-improving recentering (v(Φ₂(θ)) = 3/2), while the
COHERENT convention (slot normalizers marching by the fixed weight-γ₂
step monomial, class wraps folded into K₁ through x̄^e = ȳ·p̄^h) selects
ψ₁ = z′+1, whose lift X²+3X+3 is the TRUE ℚ₃-factor — and under it the
vertex law holds. The coherent reading is pinned in the checker (docstring
= the pin's spec); the naive reading is retained as a REPORT and is
refuted 1,818 times in the production run (1,827 differing instances),
ALL where the twist unit ȳ ≠ 1 — it is INVISIBLE at p = 2 with g = 1,
which is why no depth-1/2 suite could see it. This is the depth-3 sibling
of rev 3's sloped-vs-plain pin and a machine countermodel shaping GD-3's
slot-twist (z-power) clause: any OL-2a-3/GD-3 statement or Lean
transcription that reads order-2 residuals slot-fresh is refuted. Also
reported: the naive mixed-units order-2 (N4)-lower comparison fails in
470,057/470,736 instances — the order-2 lower band must not be stated as
w₁(D_{μ₁}) ≥ u_{k₁} (statement-shaping for (M6b)(ii) at depth).

## 2. The proof: `CU1_phaseB_verifybrief.md` (rev 1, self-contained)

**Theorem CU-1** (brief §2): for every well-formed all-continuing
Cons_f-chain 𝐇 with N ≥ N*(𝐇) — (i) REALIZED(f, 𝐇) and the canonical
level-N run visits its state (via REAL≡); (ii) the engine's frame state
after 𝐇 equals the stage data of Θ(𝐇) (the OL-2a-6 binding carried as an
IH clause). **Corollary CU-1-ADEQ**: interior adequacy per step ((C4) is
definitionally two-sided; no global ADEQ object). Proof = ONE ordinary
induction on chain length (brief §3): base = O-2a Theorem 1 + OL-2a-5-min
+ OL-2a-6(a) + the O-1thr root kernel, grades displayed verbatim; step =
IH + state identification (OL-2a-1/2-min/3) + menu-lawfulness
((M6c)/WGEO + the dictionary) + harvest ((M6a)) + record match (Lemma R
against the emitted-record clauses — the P2-1 lesson consumed correctly)
+ level-N transfer (O-1thr Theorem 1 = D-14 + (N\*-MAJ)) + REAL≡, then
OL-2a-6(b) rebinds the next stage for clause (ii). N* is consumed through
the SINGLE displayed majorant property (N\*-MAJ) (brief §1). Full
consumption map with per-input statuses: brief §4 (16 rows). Honesty
ledger and the not-the-rejected-design audit: brief §§5–6. Verification
checklist (9 charges, including the two seams I consider weakest — the
window-width tie inside step 2, and the record-match circularity check):
brief §8.

**Grade: PROVED-UNVERIFIED conditional composition.** No new per-site
mathematics; open residue = exactly OL-2a-1..6 + O-1thr's (M6b)(ii−)/
(iii)/(V1)(V2) + the pending verification passes of the base packages +
the cluster-owned N\* discharge — nothing added, nothing strengthened
(brief §5, R-1..R-5).

## 3. Files

* `verification/openmath/o1thr_depth3_check.py` — NEW depth-3 gate
  (T-G; coherent convention pinned, naive reading reported-refuted).
* `verification/openmath/results/o1thr_depth3_run_20260731.txt` (tracked) —
  production run (6 configs, totals above, OVERALL: GATE SURVIVES).
* `lean/notes/openmath/CU1_phaseB_verifybrief.md` — the self-contained
  rev-1 brief (hand THIS to the hostile pass).
* Depth-1/2 suites (`o1thr_persite_check.py`, `o1thr_rev2_checks.py`,
  `o1thr_rev3_depth2_check.py`) UNCHANGED — the new checker imports them.

## 4. Handoff notes (for the orchestrator)

1. The convention finding (§1) should flow to the GD campaign: GD-3's
   statement must carry the coherent slot normalization; the depth-3
   harness is its standing falsifier (SYNTH4 §3.2 step 3 asked for exactly
   this order-≥2 extension).
2. The (N4)-lower report shapes the order-2 (M6b)(ii) band statement.
3. CU-1's verification should follow the two-pass hostile protocol;
   checklist charges in brief §8. Suggested priority: charges 2 and 3.
4. Numeric perimeter honesty: T-G probes the standard-lift policy over
   degree-1 root keys (as T-E/T-F); general-d₀ root keys remain outside
   the numeric perimeter (brief §8 charge 9).
