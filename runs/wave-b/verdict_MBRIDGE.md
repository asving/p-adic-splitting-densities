# Verdict — unit MBRIDGE (RB3's upward budget→height bridge, plan F3.6/F3.8)

**Verdict: bridge PROVED (informal, Codex-audited, certificate-first) — under a REQUIRED
amendment: the signed `shadow_persistence` is REFUTABLE as stated and must gain
`(hdeg : g.natDegree < μ₂ * T.D₂)`.** Deliverables: `verification/rb3_bridge_cert.py`
(+ `rb3_bridge_cert.log`, **210 PASS / 0 FAIL**) and
`docs/in-progress/RB3_BRIDGE_PROOF_2026-08-26.md` (proof + node table). No Lean edited,
no commits.

## 1. STOP-THE-LINE: the signed statement is false as signed

`leanspec/Leanspec/ChapC.lean:3482-3494` quantifies `hbudget` over `j' < μ₂` only, with
no degree hypothesis on `g`. Take `g := (composedKey T)^μ₂`: its Φ₂-digits below μ₂ all
vanish (`dev_pow_self` — C123r's drain facts), so `hbudget` holds VACUOUSLY
(`addVal 0 = ⊤`); clause 1 then demands `θ_j+1 ≤ dv2Hgt(D_j(Φ₂^μ₂))` while the statement's
own hypothesis `hc : TouchCert` says that height is EXACTLY `θ_j` (finite) — `False`.
TouchCert is non-vacuous: the certificate instantiates it at (s2Tower, μ₂=2, j=0)
(discrepancy `16·Φ′`, height 21 = θ₀; hand-verified independently of the code), at
(s2Tower, μ₂=3, j=1), and at the margin-3 variant. The amendment `hdeg` is automatic for
the intended `g = f − Φ₂^μ₂` (mirrors `towerLocus_iff_budget`'s own `hdeg`), excludes the
defeat (deg Φ₂^μ₂ = μ₂D₂ ⊀ μ₂D₂), and is exactly what the proof consumes. Falls under the
standing honest statement-change authority; flagged for the owner queue regardless.

## 2. The certificate (ran FIRST, per the plan's examples-first mandate)

Six (frame, μ₂) blocks: s2Tower (p=2, Φ′=x²−2, Φ₂=Φ′²−4x, E₂=10, δ=1) at μ₂∈{2,3}; a
margin-3 (u₂=7) variant; a lift-unit (resLift(1)=3) variant; a p=3 mirror at μ₂∈{2,3}.
Landed cross-checks reproduced (s2Witness digit height 31; budgetFloor(3,0,1,1)=6 tight).
Mechanism read off the tables:

* **The +1's origin (P0):** both `budgetFloor` branches equal `⌈(tgt+1)/d⌉`, the least v
  with `d·v + w(a,b) ≥ (μ₂−j')E₂ + 1` — hbudget ⟺ every nested slot strictly above the
  entry line. Verified over the whole grid.
* **Bridge (P1):** every degree-bounded budgeted g (single tight slots, all-slot sums,
  unit mixes, slack +1/+2) has `dv2Hgt(D_j(g)) ≥ θ_j+1` at all j < μ₂.
* **Tightness (P2):** single-slot heights EQUAL the mechanism floor
  `(μ₂−j₀)E₂ + ε + (j₀−j)E₂ + δ` (ε = d − tgt mod d) wherever one paid carry dominates —
  ultrametric equality-off-ties; θ_j+1 is attained exactly at the excess-1 inner-top
  lanes (a,b)=(D′−1,e₂f₂−1), j₀=μ₂−1; the margin-3 frame has no tight slot (δ overshoot).
* **Controls (N1):** one valuation unit below floor breaks hbudget at exactly that slot
  and drops carrying slots below θ_j+1 (e.g. 22→18) — the floor genuinely bites.
* **Clause 2 (P4):** `dv2Hgt(D_j(Φ₂^μ₂+g)) = θ_j` exactly at every TouchCert coordinate.

## 3. The proof and its Lean pricing

Clause 1 (amended F3.6) = five nodes, ~155–260 lines, ALL on landed w-abstract machinery
(no new ledger mathematics — RB3's "opposite direction, not reusable" diagnosis was too
pessimistic: `quotDigit_floor_of_le`, `dv2Hgt_dev_floor`, `le_dv2Hgt_of_eval`,
`WT_paidLift` are already floor-abstract; only the landed `dv2Hgt_censusOverflow_floor`
WRAPPER hardcodes `μ₂E₂`, a textual generalization):
AR (budget→strict wtCoeff, ceiling arithmetic, 25–45) → EN1 (`eval_xNF`, 10–20) →
EN (the P-lift `Σ xNF(dev Φ₂ g j')·K_T^{j'}` + `WT_mul`/`le_WT_K_T_pow` +
`le_dv2Hgt_of_eval`: hbudget+hdeg ⟹ `dv2Hgt g ≥ μ₂E₂+1`; hdeg consumed exactly once, at
the range-μ₂ digit reconstruction, 60–100) → CE (census floor at abstract w: +δ, 30–45)
→ SP (shadow_discrepancy splice + `dv2Hgt_dev_floor` pays jE₂: θ_j+1, 30–50).
Clause 2 (F3.8.AM, 25–45) = discrepancy additivity (BW1's F3.5 `shadowDev_add`) +
`dv2Hgt_add_eq_left_of_lt`. Optional F3.8.TC (60–100): land s2's TouchCert instance
(the 16Φ′ computation, C131uf-style) making the §1 refutation an unconditional Lean
theorem and giving `shadow_attained_of_certificate` its first live instance.

## 4. Verification discipline

Codex adversarial pass (fresh context, quote-and-classify): **no critical error**; three
justification gaps — two were already the doc's own named OPENs (OPEN-TC-LEAN: TouchCert
instance not Lean-landed; OPEN-F3.5: clause 2 waits on BW1's `shadowDev_add`), the third
(EN's out-of-grid vanishing misattributed to hdeg instead of the monic-division digit
bound `natDegree_dev_lt`, C130in.lean:113) fixed in place. Certificate arithmetic is
exact (Fraction); dv2Hgt/dvHgt ranges mirror the Lean `Finset.range (natDegree+1)` defs.

Files: `verification/rb3_bridge_cert.py`, `verification/rb3_bridge_cert.log`,
`docs/in-progress/RB3_BRIDGE_PROOF_2026-08-26.md`, this verdict. Nothing else touched.
