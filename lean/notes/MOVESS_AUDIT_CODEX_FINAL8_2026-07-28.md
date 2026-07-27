# MovesS-CORE — Codex final-confirmation pass 8 (rev 11, the closing sweep)

*(2026-07-27. Corpus: MovesS-CORE (93-unit core, §W4-SYNC seam out of scope).
Note: §S-RESUM (frozen note text, lines 11557–12377 of MOVES_2026-07-24.md,
trailing PASS RECORD blocks for §H-DOMAINS/§X-EXHAUST trimmed). Blueprint:
lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md, REV 11. Verdict:
**REJECT (2 crit / 3 gap)**.)*

1. **CRITICAL — the per-cell polynomial burden is weakened and the aggregate law is mathematically wrong.**

   Offending Defs unit:

   > `countS_cells : ... countS = ∏ c ∈ {c | cellOut c = o}, cellP e τ c`

   and gate unit:

   > `n2_activity ... cellP ≡ 1 per cell + ... countS_cells + act_iff`

   The note requires each cell's size polynomial to be **valued correctly at every prime power**, while branching mass is a **sum over cells, each once**. The blueprint provides no field equating `cellP.eval q₀` with the actual cell count/cardinality; `act_iff` records only zero versus nonzero. Thus constant polynomials can satisfy the burden despite incorrect cell counts. Moreover, an outcome aggregate should be formed from the relevant cell contributions, not their product. The rev-11 cure correctly makes activity per-cell, but does not faithfully encode per-cell `(iv)-POLY`/`J-RAT`.

2. **CRITICAL — E0 is silently strengthened from relevant pools to every active pool.**

   Offending unit:

   > `U-22 rs3_det_symbolic ... (hact : ∀ e ∈ Icc 1 n, ∀ q₀ ∈ allActivePools M, Nonempty (PoolHyp ... q₀))`

   and structure field:

   > `pools_e0 : ∀ e ∈ Finset.Icc 1 n, ∀ q₀ ∈ allActivePools M, Nonempty (PoolHyp ... q₀)`

   The note quantifies E0 over base pools and the base-change indices actually consumed by split or shallow legs. It does not require E0 at every prime-power pool in `M.Pools`. The new faithful base-prime unit

   > `U-22c allActive_cofinite_primes`

   is not consumed by U-22; U-22 still depends on U-22b's unrestricted-pool infinitude. Consequently the Lean theorem requires a strictly stronger E0 hypothesis than the displayed RS.3 argument.

3. **GAP — U-28 omits the open CL-17(ii) hypothesis from its core hypothesis structure.**

   Offending unit:

   > `U-28 rs4_rational_step (C : RS4Chain ...) ...`

   with the claim:

   > `C.WshP/wsh_ok (CL-17(ii))`

   `wsh_ok` only establishes denominator regularity. The core `RS4Chain` contains no proof field for production from C.1.5 volumes, CTS counts, XHD-s height sums, and the `(SIB)` count face. Those premises occur only in the out-of-scope seam's `W17ii`. The frozen note explicitly says RS.4 inherits CL-17(ii), so U-28's `hypothesis_fields` are incomplete.

4. **GAP — `n2_shallow_device` remains a bundled multi-lemma unit.**

   Offending unit:

   > `n2_shallow_device ... WshP ... WshVal ... shDom ... shEvtH/visH/shEvt ... and the laws wshval_bdd/shDom_ne/sh_realized/shevt_grouping/shweight_card/wsh_ok/wsh_interp`

   This introduces several carrier families and proves at least seven independent laws, including realization and eventual card identities. It is not a one-display unit and its advertised medium sketch cannot cover the complete statement.

5. **GAP — the core build scope retains a stale unit count.**

   Offending scope specification:

   > `E-PHASE SCOPE ... §2.A–2.D + the 85 §3 units`

   The same revision repeatedly declares a 93-unit core. This leaves the exact E-phase build set ambiguous despite the claimed stale sweep.

Counts: **2 CRITICAL / 3 GAP**

**REJECT (2 crit / 3 gap)**
