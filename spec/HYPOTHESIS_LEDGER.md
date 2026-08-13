# PHASE-0b — HYPOTHESIS-CLOSURE LEDGER (v3)

Scope: surviving conditions on the path from `leanfinal`’s `UniformityStatement` through W12/GENIND, the T-unit chain, low-degree checks, tightness census, eight generality audits, and cited external mathematics. This is enumeration and classification only; it resolves none of the listed mathematics. CARRY means keep the condition visible until a named node closes it; MATH is missing proof work and must not be disguised as a field hypothesis; NODE is bounded audit, transcription, citation, interface, or proof-packaging work; MERGED remains indexed but is represented by another row and is not counted twice; CLOSED means a named instrument or run has discharged the row and the reference is recorded in the row itself.

v3 folds the Phase-0b completeness sub-sweep’s fifteen delta items (`runs/qgen/HYPLEDGER_deltas.md`, TIER-1/2/3). Every delta quote was re-verified against its source file and line before transcription. Items that are actions rather than conditions are in `MAINTENANCE QUEUE`, not in the row list; TIER-3 off-path items are one line each in `OFF-PATH`.

## Ledger

### Capstone and low-degree interface

HYP.01  `typeOf` faithfulness
WHERE: `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md`, STATUS/trust-boundary discussion.
STATEMENT: On the `disc ≠ 0` locus, the gcd-defined `typeOf` agrees with the classical ramification-degree/residue-degree multiset.
CONSUMED BY: `genuineDensity`, `UniformityStatement`, and every classical-to-Lean splitting-type transfer.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — formal faithfulness review and packaging; `typeOf_degree` is landed.

HYP.02  `eq_of_add_mul_eq`
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §6.1.
STATEMENT: The degree-bounded map (u,v) ↦ hu+gv is injective, hence bijective with landed surjectivity; this is uniqueness of exact solve S3, not uniqueness in a congruence class.
CONSUMED BY: optional injectivity refinements of two-block Hensel; the n=3 consumer does not obviously need it.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — equal-rank finite-free-module/Orzech proof unit.

HYP.03  n-fold Hensel factorization
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §§6.2–7.
STATEMENT: A finite pairwise-coprime residual factorization lifts to the corresponding finite monic factorization.
CONSUMED BY: general-degree factorization and n≥4 splitting-type assembly.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — induction from the landed two-block theorem using `IsCoprime.prod_right`.

HYP.04  strong Hensel inequality
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: If monic F has v(F(x₀))>2v(F′(x₀))=2w with w≥1, some root r has v(r−x₀)>w.
CONSUMED BY: repeated-root cubic recursion and `CertRam3`.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — medium formal proof absent from the corpus.

HYP.05  `typeOf` shift invariance
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: Integral translation X↦X+c preserves `typeOf`.
CONSUMED BY: cubic recentering at c≠0.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — small formal lemma absent at the `typeOf` level.

HYP.06  `typeOf` scale invariance
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: Under X=πᵐY, the normalized polynomial has the splitting-type relation asserted by the recursion.
CONSUMED BY: cubic depth reduction and recurrence.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — medium formal work.

HYP.07  nonintegral-slope `CertRam3`
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: The nonintegral Newton-slope branch has the asserted cubic ramification type.
CONSUMED BY: cubic menu exhaustiveness and exact cubic densities.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — norm/valuation proof absent.

HYP.08  cubic tail recurrence
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §9.4.
STATEMENT: u(N) ≤ q^(−N/2)+q^(−5)u(N−3).
CONSUMED BY: drainage of the cubic triple-root branch.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — stated but not derived.

HYP.09  cubic triple-root drainage
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, STATUS and §§8–12.
STATEMENT: After finite classified cubic strata are removed, the infinite triple-root recursion has null complement.
CONSUMED BY: `UndecidedVanishes O 3 σ`, `drainage_three_of_triple`, and exact cubic assembly.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MATH — depends on HYP.04–HYP.08 and remains unproved.

HYP.10  exactly five cubic splitting types
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§8–12.
STATEMENT: Every separable monic cubic has one of the five listed (e,f)-multisets.
CONSUMED BY: converse drainage and cubic sum-to-one.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — finite multiset enumeration from landed `typeOf_degree`; LOW-CONFIDENCE until checked in Lean.

HYP.11  exact cubic densities
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§8, 10.3, 12; W12 HMENU3/HEX3 perimeter.
STATEMENT: Each cubic splitting type has the asserted rational density in q.
CONSUMED BY: degree-three `UniformityStatement`.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — resultant-weighted peeling, drainage, and DEEP-X/B1/B2/B3 tiers remain.

HYP.12  ordering convention for (e,f)
WHERE: `N3_CHECK_2026-08-13.md`, §§3,8; `GENUINE_DENSITY_2026-08-13.md`.
STATEMENT: Implemented ordering and multiset normalization agrees with the classical convention.
CONSUMED BY: exact-event equality with `typeOf`.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — human definitional audit; needs-Asvin question 4.

### Citation and theorem-scope residue

HYP.13  all-O citation swap
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.
STATEMENT: About thirteen imported facts must cite all-complete-DVR sources rather than narrower p-adic surrogates.
CONSUMED BY: external-reference layer.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — replacement sources are identified.

HYP.14  `NS-6` stopping criterion
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-6.
STATEMENT: The tower stops at order r iff every order-r residual is separable; descent continues iff some is inseparable.
CONSUMED BY: higher-degree descent/drainage.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — short GN15/AGNPRW corollary.

HYP.15  `NS-7` termination
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-7 and §5 Stage 3.
STATEMENT: The project’s MacLane/Okutsu construction terminates over every complete DVR in scope.
CONSUMED BY: finite certificates, GENIND termination, finite menu/drain descriptions.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: CARRY — owner choice between recommended citation and internal F-2 proof; needs-Asvin question 1.

HYP.16  `NS-15` finite-depth bound
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-15/F-3.
STATEMENT: If retained, replace B(n,p) by depth ≤ ½v(disc f).
CONSUMED BY: `L5fix(b)` and finite certificates; capstone needs finiteness, not this constant.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — available only with HYP.15’s internal F-2 branch; the citation gives no explicit constant.

HYP.17  publisher-number verification
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.
STATEMENT: Check AGNPRW, GN15, and Kuhlmann theorem numbering against publisher versions.
CONSUMED BY: bibliography and attribution.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — bibliographic only.

HYP.18  `AX-DEFECT` correction
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-14.
STATEMENT: Use discreteness for defectlessness and state the separability fence: only inseparable extensions need characteristic zero; uses are on disc≠0.
CONSUMED BY: external field-theory layer.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — Kuhlmann Theorem 3.3 with corrected scope.

### W12 and general induction

HYP.19  `[W12-H]`
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-08.md`, §4.2 L1132–1167.
STATEMENT: Only order≥2 clause (i), hence n≥4 composite stages, depends on [H-a]–[H-e]; n=2 is unconditional and n=3 has menu/exhaustion only.
CONSUMED BY: W12 composite stages and n≥4 capstone.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — aggregate only; omit when children are expanded.

HYP.20  `[H-a]` / JC warrant
WHERE: `W12_PROOF_2026-08-08.md`, §4.2.
STATEMENT: GRTJC supplies the composite-stage warrant with its own displayed conditionality retained.
CONSUMED BY: W12 composite partition.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — child conditions such as DMULT-S remain separate.

HYP.21  `[H-b]` / JB row 12
WHERE: `W12_PROOF_2026-08-08.md`, §4.2 L1143–1145.
STATEMENT: JB row-12’s u≥0 membership proviso holds on the unbounded grid.
CONSUMED BY: W12 JB face.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — not identical to four-row JB-NOLEG; needs-Asvin question 2.

HYP.22  `[H-c]` / J-D1 value package
WHERE: `W12_PROOF_2026-08-08.md`, §§4.2,5.
STATEMENT: J-D1 is conditional on the six weld notes’ boxes plus Σ-law, including VD-m, C-coll, R-coll, DMULT-S, and PERIM-μ.
CONSUMED BY: exact measure assignments and stage power sums.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — aggregate of HYP.74, 76, 77, 83–86, and reachable T4 residue.

HYP.23  `[H-d]` residual censuses
WHERE: `W12_PROOF_2026-08-08.md`, §4.2.
STATEMENT: Once [H-a]–[H-c] identify the reads, universal residual-tower censuses hold level by level.
CONSUMED BY: W12 weights and GENIND counts.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — conditioned finite-field census nodes.

HYP.24  `[H-e]` decision plus window pinning
WHERE: `W12_PROOF_2026-08-08.md`, §4.2 L1153–1167; GENIND CS-3.
STATEMENT: Separable order≥2 residuals decide σ for all disc≠0 lifts, and all consumed read data are pinned inside the stage window by the [H-a]/[H-b] leg.
CONSUMED BY: W12/GENIND leaves and composite-stage A0.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — GMN supplies only decision; project-internal pinning remains.

HYP.25  `A0` lift well-posedness
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: Every window-decided core-family member has all disc≠0 O-lifts of the read’s type.
CONSUMED BY: W12.D and capstone measure identity.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — fixed-n public assumption with load-bearing fence.

HYP.26  `A1` exact core menu
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: For fixed n and all q simultaneously, a finite disjoint q-independent family list carries internal σ_F labels and exact weights; σ is not an A1 binder.
CONSUMED BY: W12.D for every degree-n type.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — public fixed-n interface.

HYP.27  `A2` drainage
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: For fixed n, the mass outside visible core families, including undecided and boundary families, has r(N)/q^(nN)→0.
CONSUMED BY: exhaustion and capstone equality.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — n≥4 supplier is DRAIN-N4/CS-1Q.

HYP.28  `hMenu3` / `W12-BOX-2`
WHERE: `W12_PROOF_2026-08-08.md`, boxes.
STATEMENT: Cubic cases form the stated finite disjoint menu.
CONSUMED BY: degree-three W12.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — HMENU3 perimeter; HYP.11 records unproved deeper tiers.

HYP.29  `hExhaust3` / `W12-BOX-3`
WHERE: `W12_PROOF_2026-08-08.md`, boxes.
STATEMENT: Cubic menu exhausts the separable event up to a null set.
CONSUMED BY: degree-three W12.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — HEX3 perimeter; ANNEX-2 correction remains indexed. TAIL-CERT=HEX3-BOX-1=HM3-BOX-1 is NO LONGER index-only: it is promoted to its own row HYP.137 because it has a named live consumer (GENIND’s S8.2 W-12.B consistency clause). Its `hExhaust3` non-consumption is preserved — see HYP.137 (v3 delta item 2).

HYP.30  `W12-BOX-4` / `DRAIN-N4`
WHERE: `W12_PROOF_2026-08-08.md`; `TIGHTNESS_CENSUS_2026-08-11.md`, I-1.
STATEMENT: For every n≥4, the unclassified complement of the general finite menu is null.
CONSUMED BY: A2 and n≥4 capstone.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — lower supplier HYP.36; distinct from GENIND-BOX-4.

HYP.31  `[GENIND-H]`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S1 L186–227 and L3081–3084.
STATEMENT: Empty for n≤3; for n≥4 contains CS-1/2/3/EXACT, with GENHN-HE first live n=6 and GENHN-TOW-1 additionally at n≥8.
CONSUMED BY: general menu and drainage.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — aggregate only.

HYP.32  `CS-1` count-fibration
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1123–1146.
STATEMENT: Every composite/mixed stage has the asserted exact count-fibration and product transport.
CONSUMED BY: GENIND recursion, A1, and Step-4/A2 drainage rate.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — uniform embedded/mixed transport unproved.

HYP.33  `CS-2` stage bracket
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1147–1168.
STATEMENT: Each stage has the claimed mass-normalized bracket.
CONSUMED BY: measure recursion and exact weights.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — no general-genre proof identified.

HYP.34  `CS-3`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1169–1171.
STATEMENT: Separable stage residuals decide σ with (eE,f[K-ext]) for all disc≠0 lifts, with HYP.24 window pinning.
CONSUMED BY: GENIND leaves.
CLASS: named-obligation
PROPOSED DISPOSITION: MERGED — exactly HYP.24 at GENIND layer.

HYP.35  `CS-EXACT`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1172–1190.
STATEMENT: CS-1+CS-2 deliver an exact finite q-power sum for every stage menu and stage drain, not asymptotic or bound-only laws.
CONSUMED BY: induction’s fourth member and rational extraction.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — bound-only drainage does not close induction.

HYP.36  `(CS-1Q)`
WHERE: `GENIND_PROOF_2026-08-08.md`, §C2-G1 L3592–3722.
STATEMENT: Both clauses hold: M_G≥e(N−1−H)−Δ_G, and the displayed digit-loss rate follows; the rate does not by itself assert all residual mass is zero.
CONSUMED BY: DRAIN-N4/A2.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — embedded/mixed affine ledgers are not universally checked.

HYP.37  `GENIND-BOX-2`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S8 L1357–1360.
STATEMENT: Displayed schema expands faithfully to every induction route.
CONSUMED BY: partition auditability.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — presentation debt.

HYP.38  `FGMN-MAIN` Lean declaration
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-3.
STATEMENT: Declare the cited FGMN theorem faithfully and wire consumers.
CONSUMED BY: higher-order leaves and factorization.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — declaration/wiring.

HYP.39  `JD0-BAR`
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-5.
STATEMENT: J-D0 gauge-blindness is PROVED grade with 68,523/0 machine evidence but below process bar because the two-clean hostile arc has not run.
CONSUMED BY: JD0 inside [H-c].
CLASS: grade-cap
PROPOSED DISPOSITION: NODE — owner chooses hostile arc or machine-grade sign-off; question 6.

HYP.40  single-w B″ transport
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-2; `GENTOW5_WI_2026-08-10.md`; SOL certification row 18.
STATEMENT: The single-w monomial B″ transport at i≥3 is certified 2/2; surviving work is S12.1 scope re-verification, not pending PE2 and not a “window lemma.”
CONSUMED BY: GENTOW5-B(a) residual/certificate legs, FGMN displays, and all deep towers.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — scope audit; does not discharge HYP.63.

### T2 carrier obligations and grade

HYP.41  `(LB1)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, §S1.7B L2214 and acceptance.
STATEMENT: Every triggered level-one state has monic-side and label blocks with full developments, single-side hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data.
CONSUMED BY: clause 4, S4.1, and S4.2 exclusions.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — one of exactly two standing T2 obligations.

HYP.42  `(MP1)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, §S1.8A L2423–2438 and acceptance.
STATEMENT: Whenever the recentered key divides its block, quotient G′ satisfies WINDOW, full development/ACCOUNT/S1.7 and height/lift/frame/origin/degree data, and the peeled key has certified orbit/(e,f) decomposition—items 2–5.
CONSUMED BY: clause 5, S1.8 induction, and RANK item 3.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — the other standing T2 obligation.

HYP.43  `(SEC-RANK)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L2341–2353, L2391, L4496.
STATEMENT: Secondary rank σ_C into a well-founded W_C strictly decreases at each product-1 linear recentering and has no requirement at other transitions.
CONSUMED BY: third RANK component; its descent yields termination and exhaustion.
CLASS: carrier-hypothesis
PROPOSED DISPOSITION: NODE — stipulated carrier data, explicitly not a ledger obligation and fencing no read.

HYP.44  `(RISE)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L3329–3333, L3357, L4497.
STATEMENT: At refine/product-1 recentering, d(Φ_new(ρ))>λ for every refined-class root; HT with k=λ is derived.
CONSUMED BY: refine-step HT, not termination.
CLASS: carrier-hypothesis
PROPOSED DISPOSITION: NODE — stipulated, not a ledger obligation.

HYP.45  `(GRADE)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L4503.
STATEMENT: HE3 is simultaneously attempt grade 0/2 and clean count 1/2; this caps any level-two chain consuming an HE3 pin through S1.8C.
CONSUMED BY: level-one and affected level-two proof-status claims.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE — evidence completion only.

### T1/T3/T5 supplier conditions

HYP.46  canonical-letter scope
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, §1.1 R2-1 L1388–1432 and §5 item 1.
STATEMENT: T1 proves value zero but no arbitrary-depth preceding-letter monomial or terminating reduction; such a description needs `(H-JA-CONJ)_i`, while level two is unconditional.
CONSUMED BY: T1 canonical-form consumers.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — narrow carrier claim and expose supplier.

HYP.47  `C3-ladder-multiplicativity`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2413–2430 and §5 item 2.
STATEMENT: For consumed s, R_(i+1,sκ̄_i)(N^s)=R_(i+1,κ̄_i)(N)^s.
CONSUMED BY: B-law and higher-depth residual comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise supplier; level-general name requires verification.

HYP.48  `C3-slot-grade`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2457–2470 and §5 item 2.
STATEMENT: With s=f_(i+1)−t, β_t=sκ̄_i=(f_(i+1)−t)κ̄_i.
CONSUMED BY: B-law and slot comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise grade identity.

HYP.49  `C3-graded-scalar-covariance`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2432–2441 and §5 item 2.
STATEMENT: For consumed homogeneous ladder X and permitted value-zero g, R_(i+1,β)(Xg)=R_(i+1,β)(X)res(g); no all-homogeneous claim.
CONSUMED BY: B-law and canonical comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise read supplier.

HYP.50  `C3-zero-read`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2993–3002.
STATEMENT: R_(i+1,β)(0)=0; a zero coherent digit is a zero homogeneous component, not a value-zero factor with zero residue.
CONSUMED BY: zero-digit B-law branches.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise zero read.

HYP.51  `C3-ladder-nonvanishing`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L3315–3330 and §5 items 2/19.
STATEMENT: The base ladder read is nonzero independently of multiplicativity, covariance, and zero-read.
CONSUMED BY: w_i≠0, rescaling, factor-pattern transport.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — discharged at i=2; explicit level-general supplier required for i≥3.

HYP.52  `C3-read-codomain`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, R11-1 L3655–3672 and §5 item 22.
STATEMENT: Every consumed grade-β read is K_i-scalar-valued, not merely valued in gr(μ_i).
CONSUMED BY: w_i∈K_i×, y↦y/w_i, rescaled key, and factor-pattern transport.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — i=2 is supplied; i≥3 rides an unverified level-general package and is not inferred by T1.

HYP.53  `(H-JA-CONJ_i)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1388–1411 and §5 item 1.
STATEMENT: A specified Laurent monomial J_i satisfies res(n̂_i(u_(i+1))/π_(i+1)^(u_(i+1)))=J_i(z₁,…,z_i).
CONSUMED BY: arbitrary-depth preceding-letter specialization.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — imported JA hypothesis; T1 names no discharged supplier/pin.

HYP.54  `(H-JA-RES-CONJ)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1448–1479.
STATEMENT: For nonzero H,P,Q, H=y^νQ and P=aQ(by) with a,b units, so support translates by ν and degree shifts by ν.
CONSUMED BY: residual-support/degree comparison.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — exact JA supplier interface. CORRECTED (v3, delta item 7): T1 names “the accepted harness/print conjugation formula” but supplies no grep-verifiable external designation — `spec/EFF-T1-s1of3.md` OPEN-CALL 2, which also refuses the `JA-EPS-CORR` conflation (that unit verifies the origin correction, not this whole-polynomial supplier). The interface has no named source yet; see HYP.141.

HYP.55  `(H-GENHN-CLEAR)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1554–1577.
STATEMENT: For r=f₂−t, M=ru₂, u₂>e₂D′h, every product clears by at least r(u₂−e₂D′h)/e₁>0, and collection/Φ′-carry only cancels or moves upward.
CONSUMED BY: outer-side residual computation.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — exact GENHN supplier interface. CORRECTED (v3, delta item 7): the designation T1 cites is refuted. `spec/EFF-T1-s1of3.md` OPEN-CALL 3 — “T1 calls it the accepted `T(b)'(i)` site, but fixed-string grep for that designation in `GENHN_PROOF_2026-08-08.md` returns zero” — re-verified here: `grep -c "H-GENHN-CLEAR" lean/notes/openmath/GENHN_PROOF_2026-08-08.md` = 0. `GENHN-LIFT` covers the lift and must not be invented as the clearance theorem. See HYP.141.

HYP.56  `(H-HETOW-LOCAL)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2590–2633.
STATEMENT: HETOW supplies the displayed normalizers, carry data, local bridge, second-level carry equations, and τ(k)=η^(−Q(m(k))).
CONSUMED BY: T1 A2 transport.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — complete local supplier interface.

HYP.57  `(H-VARTHETA-RES_i)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L3523–3541/§5 item 21; T5 honesty item 13.
STATEMENT: For i≥3 and s≥0, res(n̂_i(u_(i+1))^s/n̂_i(su_(i+1)))∈K_i.
CONSUMED BY: T1 B-law and C3-key, T5 consumers, and general tower path.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — technical unit to adjudicate whether T5 S11.2 §S2.1 implies it; not an owner question.

HYP.58  integral K₁ lift range
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, acceptance standing conditionality.
STATEMENT: Full integral K₁ lift is asserted only for M>D′h.
CONSUMED BY: corresponding lift branch.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — retain strict domain.

HYP.59  `WELD-M-PKG` boundary
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, C7 L726–759 and §5 item 11.
STATEMENT: Five heterogeneous fields assert no single cross-face map, coherence, map uniqueness, or gauge uniqueness beyond anchors.
CONSUMED BY: weld consumers and [H-c].
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — enforce narrow interface.

HYP.60  raw/canonical equality
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, §5 item 5.
STATEMENT: Equality is iff z^ν=1, not iff ν=0 without an order hypothesis.
CONSUMED BY: equality/cancellation tests.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — correct consumers.

HYP.61  dv_i codomain
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L4239–4241 and L4416.
STATEMENT: dv_i lies in (e(μ_i)/e(μ_r))ℤ generally; only enumerated nonzero consumed arguments are integral, while dv_i(0)=+∞.
CONSUMED BY: valuation and zero-lift branches; gates no C1–C7 conclusion.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — scope typing.

HYP.62  `T3-JOINT-OPEN`
WHERE: `T3_COCYCLE_TELESCOPE_2026-08-12.md`, §8.5 L1065–1081.
STATEMENT: Machine suite lacks a realized p-adic B″ frame with Θ≠1 and w≠1.
CONSUMED BY: realized regression coverage only.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — not merged with HYP.135’s finite graded model.

HYP.63  `[GENTOW5-W(i)]` / 𝒲_(≤i)
WHERE: `T5_WFRAME_2026-08-12.md`, L616, L926–930, L1499–1500; `Q4_output.log`.
STATEMENT: Cumulative 𝒲_(≤i) required by frozen GENTOW5 holds for every i≥3.
CONSUMED BY: T3/T5 higher-depth laws and G5-COND ride list.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — WI proves only the induction step, not induction from empty base.

HYP.64  `WFRAME OPEN-1`
WHERE: `T5_WFRAME_2026-08-12.md`, L388.
STATEMENT: No structural formula/criterion for w_i, including w_i=1, is proved.
CONSUMED BY: no current capstone leg.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — keep stronger claim out.

HYP.65  `WFRAME OPEN-2`
WHERE: `T5_WFRAME_2026-08-12.md`, L390 and L1185–1193.
STATEMENT: Either identify S11.3’s fixed letter-power unit with w₁ or retain distinct normalizations; no u₁=w₁ claim.
CONSUMED BY: entire i=1 stratum, presently excluded.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — normalization interface.

HYP.66  `WFRAME OPEN-3`
WHERE: `T5_WFRAME_2026-08-12.md`, L283–286, L392.
STATEMENT: Avatar value can differ from intrinsic WF-w; open task is exact gap, not equality.
CONSUMED BY: avatar bookkeeping.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — quantify known nontrivial gap if needed; the gap is now MEASURED, not merely known (v3, delta item 11): GENTOW2 S6.1 row 23, the avatar = w identification this row is gated on, is DESCRIPTIVE-status and “is now measured to GAP at LW3” (`GENTOW5_WI_2026-08-10.md:480`). See HYP.145.

### T4 boxes and tightness suspects

HYP.67  `GENTOW6-BOX-1`
WHERE: `T4_CERTIFICATE_WITNESS_2026-08-12.md`, §S7 L526–539; upstream GENTOW6.
STATEMENT: Lower-coordinate classification at μ₂≥3, including f₁≥2 compound face, is incomplete.
CONSUMED BY: potentially [H-c].
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — if reachable; scheduling/scope is question 2.

HYP.68  `GENTOW6-BOX-2`
WHERE: T4 §S7; upstream GENTOW6.
STATEMENT: Product-measure count is open already at FULL sides; budget half is proved and only ledger/count half remains.
CONSUMED BY: potentially [H-c].
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — if reachable.

HYP.69  `GENTOW6-BOX-3`
WHERE: T4 §S7; upstream GENTOW6.
STATEMENT: Entry-driven/non-top-overflow cases lack exhaustive classification.
CONSUMED BY: potentially W12 value partition.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — if reachable.

HYP.70  `GENTOW6-BOX-4` residue
WHERE: T4 §S7 L533–535/L2105–2109; `GENTOW6_PROOF_2026-08-09.md` L1249–1255.
STATEMENT: Sealed-row ask is DISCHARGED at HEAD, GREEN 265/0 at four x-ful rows including f₁=2; only theorem-grade all-f₁≥2 widening remains unsealed.
CONSUMED BY: a widened theorem, not the discharged box.
CLASS: theorem-strength-residue
PROPOSED DISPOSITION: MATH — no OPEN-CALL; keep battery discharge distinct from widening.

HYP.71  `GENTOW3-BOX-1`
WHERE: T4 §S7; upstream GENTOW3.
STATEMENT: Neither genre-general nonvanishing nor battery witnesses for entry-driven overflow with self-power below D′ are delivered.
CONSUMED BY: potentially [H-c].
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — if reachable.

HYP.72  disc≠0 downstream fence
WHERE: `T4_CERTIFICATE_WITNESS_2026-08-12.md`, L1827–1860.
STATEMENT: disc≠0 is not T4 membership; later decided-leaf σ consumers import it alongside membership.
CONSUMED BY: W12/other σ consumers; T4 consumes no σ-content.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — thread downstream.

HYP.73  `WELD-FACE-AUDIT`
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, S-4.
STATEMENT: Check unresolved weld-face reachability.
CONSUMED BY: chartered HYP.74–77 only; widening to HYP.21/22/67–71 needs explicit scope.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — question 2.

HYP.74  `JD0-BOX-2`
WHERE: census S-5.
STATEMENT: JD0 unit-character warrant is synthesis, not proved theorem.
CONSUMED BY: JD0 in [H-c].
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — unless audit signs non-reachability.

HYP.75  `JB-NOLEG`
WHERE: census S-6; `GRTJB_PROOF_2026-08-08.md` §0M.
STATEMENT: Open no-machine-leg cells are row 4 GRID, row 5 RES, row 12 d4/u≥0, and row 22 v=0.
CONSUMED BY: broader JB frontier; only row 12 is [H-b].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — pending audit.

HYP.76  `W2-VALUE`
WHERE: census S-7.
STATEMENT: W2 value formula and two side conditions hold on every claimed face.
CONSUMED BY: [H-c].
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — pending audit.

HYP.77  `DMULT-S`
WHERE: census S-8; GRTJC JC-BOX-3.
STATEMENT: Exact ω=1 multiplicity tier satisfies claimed formula beyond measured cases.
CONSUMED BY: [H-a] and [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — measurement is not proof.

HYP.78  `S8.1-MEMBER`
WHERE: census S-1.
STATEMENT: Above-floor divergence cases have complete membership classification.
CONSUMED BY: drainage/value decomposition.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — pending RCT hard unit; no OPEN-CALL/HYP.73 dependency.

HYP.79  `P-BINOM`
WHERE: census S-2.
STATEMENT: If p divides binom(m,2), floor attainment and lower-coordinate cases are classified.
CONSUMED BY: compound value branch.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — rider on HYP.78; no OPEN-CALL.

HYP.80  `COMPOUND-6.5′`
WHERE: census S-3.
STATEMENT: f₁≥2, μ₂≥3 compound case has required classification and measure law.
CONSUMED BY: compound genre under [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — proof+machine unit; no OPEN-CALL/HYP.73 dependency.

### Completeness additions from the adjudication

HYP.81  `[GENHN-HE(μ ≥ 3)]`
WHERE: W12 L437; GENIND L3081–3084.
STATEMENT: Stage leaves of multiplicity μ≥3 have required σ-decision; first live n=6.
CONSUMED BY: W12/GENIND from n=6.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — independent leaf obligation. SCOPE SPLIT ADDED (v3, delta item 9): HE3 proves THEOREM HE3.A and [GENHN-HE(μ)] UNCONDITIONAL for μ≤3 — exactly the first-live n=6,7 case — while at μ≥4 (n≥8) COROLLARY HE3.B rides the open HE3-BOX-6 ramified branch (ii). The conjunct is unchanged; its supplier is conditional above μ=3. See HYP.143.

HYP.82  `[GENHN-TOW-1]`
WHERE: GENIND L3081–3084.
STATEMENT: n≥8 tower leg satisfies additional GENHN supplier law.
CONSUMED BY: GENIND at n≥8, in addition to HYP.81 and [GENIND-H].
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY.

HYP.83  `(VD-m)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Value-decomposition law holds for m≥2; unconditional only m≤1, while VD-2 is false on 10/13 roster boundaries.
CONSUMED BY: JB-CREAD and [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY.

HYP.84  `(C-coll)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Claimed collection law holds at order≥2 value layer.
CONSUMED BY: [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY.

HYP.85  `(R-coll)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Claimed residual collection law holds at order≥2 value layer.
CONSUMED BY: [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY.

HYP.86  `PERIM-μ`
WHERE: W12 L219–221; weld value ledgers.
STATEMENT: Multiplicity perimeter law holds on all claimed order≥2 faces.
CONSUMED BY: [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY.

HYP.87  `GENIND-BOX-3`
WHERE: GENIND §S8 L1361–1366.
STATEMENT: All-prime-power and d≥2 scope rests on proof q-uniformity; battery covers d=1 at prime q only.
CONSUMED BY: all-prime-power GENIND.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — generality/corroboration audit.

HYP.88  `GENIND-BOX-4`
WHERE: GENIND §S8 L1367–1372.
STATEMENT: Simple-slice β-bookkeeping compression for n≥4 drainage is proved on every route.
CONSUMED BY: GENIND drainage; distinct from HYP.30.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — separate bookkeeping proof.

HYP.89  `GENIND-BOX-5`
WHERE: GENIND §S8 L1373–1420.
STATEMENT: Clean count for the conditional general-degree structure has not started.
CONSUMED BY: GENIND acceptance grade.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE.

HYP.90  `GENIND-BOX-6`
WHERE: GENIND §S8 L1421–1425.
STATEMENT: Machine oracle is mixed-characteristic only; equal-characteristic conventions/coverage remain unaudited.
CONSUMED BY: all-characteristic GENIND.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.91  `GENIND-5` / `OB-a…OB-d`
WHERE: GENIND obstruction section.
STATEMENT: Four displayed obstructions and their routing are represented in the induction DAG.
CONSUMED BY: branch completeness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — expand/map, do not compress silently.

HYP.92  `ANNEX-LEMMA GENIND-C2Q`
WHERE: GENIND C2Q annex.
STATEMENT: Annex quantitative lemma has exactly HYP.36’s hypotheses/rate.
CONSUMED BY: CS-1Q/A2.
CLASS: named-obligation
PROPOSED DISPOSITION: MERGED — supplier node under HYP.36.

HYP.93  `GENIND-6`
WHERE: GENIND §S4.3 L814–825.
STATEMENT: Clause (d)’s stage-side content is [GENIND-H]’s and not discharged here.
CONSUMED BY: stage-side induction.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MERGED — represented by HYP.31 and children.

HYP.94  `UniformityStatement` signature
WHERE: `GENUINE_DENSITY_2026-08-13.md`, §2.5.
STATEMENT: Freeze universe of O, q-evaluation/coercion, and per-O denominator nonvanishing; old σ.degree point is superseded by `typeOf_degree`.
CONSUMED BY: phase 0d.
CLASS: owner-definition-decision
PROPOSED DISPOSITION: NODE — question 3.

HYP.95  Haar bridge
WHERE: `GENUINE_DENSITY_2026-08-13.md` §3B.4; `N2_EXACT_2026-08-13.md` §7.
STATEMENT: Limit of decided proportions equals Haar measure of the type locus.
CONSUMED BY: informal W-12.D Haar conclusion, not weaker Lean definition.
CLASS: optional-theorem-leg
PROPOSED DISPOSITION: MATH — live optional bridge; question 5.

HYP.96  `AX-CELLREC` / `AX-LEAF`
WHERE: census L-3.
STATEMENT: Draft faithfulness entries gate the older Lean capstone path.
CONSUMED BY: theorem-strength older realization.
CLASS: owner-axiom-decision
PROPOSED DISPOSITION: NODE — question 7.

HYP.97  `RealInstanceAt.faithful`
WHERE: census L-4; `Stage2/UniformityTarget.lean`.
STATEMENT: True-placeholder consumption at theorem strength is illegitimate before gates.
CONSUMED BY: older Stage2 realization, not automatically new Lean-core projects.
CLASS: owner-axiom-decision
PROPOSED DISPOSITION: NODE — question 7.

HYP.98  `DEFINITION-AUDIT`
WHERE: census L-5; GENUINE_DENSITY definition audit.
STATEMENT: Frozen event, density, type, evaluation, and convention definitions match the mathematical capstone.
CONSUMED BY: phase 0d.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — includes HYP.12/94/111 interfaces.

HYP.99  T3/T5 frame staleness
WHERE: T5 rider m-2; T3 frame; T1 r12–r13.
STATEMENT: T5 pins T1 through r10 and T3 pins no revision, while r12 adds two-clause w_i∈K_i× gate and T3 consumes higher-depth data without both fences.
CONSUMED BY: T3/T5 higher-depth soundness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — cross-note HEAD audit.

HYP.100  contradictory T5 sentence
WHERE: T5 stale L299 versus governing L616.
STATEMENT: Stale text says WI discharges the conjuncts; governing text says it does not.
CONSUMED BY: extraction of HYP.63 status.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — strike/append stale sentence.

HYP.101  HE7.A source suite
WHERE: T2 §S4.1 L1167.
STATEMENT: Every instance supplies ACCOUNT, RES-DEG, nonemptiness, exhaustion, and root-preserving continuation.
CONSUMED BY: HE7.A instantiation; naming a carrier is insufficient.
CLASS: source-obligation-suite
PROPOSED DISPOSITION: CARRY — SEC-RANK/RISE do not replace the suite.

HYP.102  `(MID-PEEL)` items 2–5
WHERE: T2 L2415/S1.8.
STATEMENT: Items 2–5 are standing clause hypotheses discharged per instance; only item 1 is master-proved.
CONSUMED BY: mid-peel instances.
CLASS: source-obligation-suite
PROPOSED DISPOSITION: NODE — record each discharge.

HYP.103  T2 S4.2 non-claims
WHERE: T2 §S4.2 L1171–1184.
STATEMENT: Twelve exclusions, including partial-side budget and density laws, bound T2.
CONSUMED BY: downstream density use.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE — preserve list.

HYP.104  `C3-lift-coefficient-space`
WHERE: T1 L3228–3311; §5 item 18.
STATEMENT: Every C3-key coefficient is bounded, especially deg k̂_t<deg Φ_i; height/residue do not imply it.
CONSUMED BY: corrected key formation/monicity.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — independent site obligation.

HYP.105  factor patterns need tower correctness
WHERE: T1 §5 item 9.
STATEMENT: Gauge-invariant residual factor patterns become splitting types only via surrounding tower correctness.
CONSUMED BY: T1-to-capstone transfer.
CLASS: interface-obligation
PROPOSED DISPOSITION: NODE — but ROUTED TO 0d (v3, delta item 7): both Phase-0a shards escalate this row to an owner decision. `spec/EFF-T3.md:1610` heads it “**OPEN-CALL 1 — FOR-0d — NEEDS ASVIN**” and states “Neither T3 nor the identical T1 fence names that theorem… Phase 0d must decide the trust-boundary theorem connecting residual factor patterns to splitting types”; `spec/EFF-T1-s1of3.md` OPEN-CALL 4 records the same missing designation. It is not a new owner question — it is the naming half of the trust boundary already inside question 4’s definitions package. See HYP.141.

HYP.106  nonzero-digit lift contract
WHERE: T1 §5 items 15–16.
STATEMENT: Exact height is for nonzero digits; zero lifts to zero with zero residue and no finite-height term.
CONSUMED BY: key height/zero branch.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.107  A2 binary carry
WHERE: T1 §5 item 17.
STATEMENT: A2 HETOW pin is restricted to stated binary-carry regime.
CONSUMED BY: A2 absorption.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.108  A6 provenance
WHERE: T1 §5 item 20/r9.
STATEMENT: Scalar read is HE6 F-1; lift is GENTOW6 S6.1; GENTOW6 alone has no scalar display.
CONSUMED BY: A6 absorption.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.109  T-unit grade caveats
WHERE: T1/T4 acceptance and T1 PE reports.
STATEMENT: T1’s 2/2 is minors-only with unreviewed riders/note-internal pin audit and newly scored teeth; T4 adds no fresh machine computation.
CONSUMED BY: T-unit evidence claims.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE.

HYP.110  `W12-BOX-5`
WHERE: W12 boxes.
STATEMENT: Lean omCount is order-0 and W-2/LIFTCORNER lift-convention seam is unconsumed.
CONSUMED BY: Phase-B evaluator and convention audit.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.111  `W12-BOX-7`
WHERE: W12 boxes.
STATEMENT: “Decided” means certified from window digits for all disc≠0 lifts; conventions can differ on deep-tail TRP.
CONSUMED BY: leaf events/0d definitions.
CLASS: owner-definition-decision
PROPOSED DISPOSITION: NODE — question 4.

HYP.112  T4 μ₂≥3 candidate fence
WHERE: T4 acceptance/candidate.
STATEMENT: Candidate implies neither ω_j≠0, touched j, nor threshold attainment; consumption banned.
CONSUMED BY: attempted widening.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.113  T4.2(c) exposure premise
WHERE: T4.2(c).
STATEMENT: f₁≥2 clause applies only under displayed full-exposure premise.
CONSUMED BY: T4.2(c).
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE.

HYP.114  T4.2(d) provenance exclusion
WHERE: T4.2(d).
STATEMENT: All-provenance case is excluded.
CONSUMED BY: T4.2(d).
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.115  T4 fail-closed pins
WHERE: T4 pin/critical record.
STATEMENT: Missing or mismatched pins fail closed.
CONSUMED BY: all T4 imported premises.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.116  `GENTOW3-BOX-2`
WHERE: upstream GENTOW3; T4 residue-home omission.
STATEMENT: Five committed families cover only f₁=1 and η=1.
CONSUMED BY: GENTOW3 evidence claims.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.117  `(G5-COND)` ride list
WHERE: T3 G5 conditionality.
STATEMENT: At n≥3, key membership, primality, admissibility, non-equivalence, exact values, P_(n+1)-membership, clause (c), and clause (e) ride HYP.63.
CONSUMED BY: all eight T3 objects.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MERGED — consumer map for HYP.63.

HYP.118  T3 narrowed delivery
WHERE: T3 scope record.
STATEMENT: Two absorptions plus one non-instance are delivered; GENTOW-6.4 remains additive, triangular, unabsorbed.
CONSUMED BY: absorption claims.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.119  HENSEL branch-(ii) residue
WHERE: `HENSEL_FACT_2026-08-13.md`, §7.
STATEMENT: Residual trigger, finite-level class determinacy with loss c, and counting step are named; trigger/count appear superseded by N3B, determinacy is unadjudicated.
CONSUMED BY: branch-(ii) uses outside N3B.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — reconcile without assuming determinacy superseded.

HYP.120  eight-audit coverage debt
WHERE: `Q1_brief.txt` through `Q8_brief.txt`; cite-scope resolution.
STATEMENT: v1 read Q4 only; cite-scope closes H6, not separate INTERFACE rows.
CONSUMED BY: all-O DAG completeness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — umbrella for HYP.121–134.

HYP.121  `GENIND-1` all-O
WHERE: Q1 W12-4.
STATEMENT: GENIND-1, essential to W12-HT Step 3 and termination/compatibility, is valid over arbitrary complete DVRs.
CONSUMED BY: history transfer.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.122  `[RMG]` all-O
WHERE: audit INTERFACE rows.
STATEMENT: RM-m, L-CELL, L-LINE, L-EXACT, L-CANON hold over arbitrary complete/henselian DVRs.
CONSUMED BY: reduction machine.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.123  `[ILN]†` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Standard lifts/realization satisfy laws over F_q[[t]] as well as mixed characteristic.
CONSUMED BY: GRTJB/GRTJC.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.124  `GRB` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Ladder and last-read carry algebra do not rely on finite v(p), odd p, or characteristic zero.
CONSUMED BY: GRB branches.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.125  `ITER-LAW` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Iteration law holds over every complete DVR in scope.
CONSUMED BY: tower/history iteration.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.126  `W-1/W-2/J-A/J-B` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Weld/J suppliers are characteristic-general at every use.
CONSUMED BY: [H-a]–[H-c].
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — explicit generality edge even where aggregate covers substance.

HYP.127  `DU lemma` all-O
WHERE: audit INTERFACE rows.
STATEMENT: DU lemma holds over all complete DVRs in scope.
CONSUMED BY: tower/value consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.128  `W-10` all-O
WHERE: audit INTERFACE rows; census O-11.
STATEMENT: Consumed W-10 instances are characteristic-general; this does not revive stronger W10-GEN.
CONSUMED BY: W-10 instance consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.129  `J-D0` all-O
WHERE: audit INTERFACE rows.
STATEMENT: J-D0 mathematics is characteristic-general.
CONSUMED BY: [H-c] JD0 branch.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — distinct from grade HYP.39.

HYP.130  `L2core` all-O
WHERE: audit INTERFACE rows.
STATEMENT: L2core holds over arbitrary complete DVRs.
CONSUMED BY: low-level core.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.131  HUMAN_PROOF all-O
WHERE: audit INTERFACE rows.
STATEMENT: L1_proof, M6_lemma, BB3_infinity, L5fix_complete are all-O.
CONSUMED BY: named consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.132  local-integrals all-O
WHERE: audit INTERFACE rows/paper lemma.
STATEMENT: Lemma stated only unramified p-adic extends to capstone scope if used.
CONSUMED BY: retained measure route.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — removable only by explicit route exclusion.

HYP.133  `(CONV)=α⁻¹` bridge
WHERE: audit INTERFACE rows.
STATEMENT: Monic/projective convention bridge is correct and characteristic-general.
CONSUMED BY: projective-to-monic transfer.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.134  GENHN count all-O
WHERE: Q5 out-of-slice INTERFACE.
STATEMENT: GENHN count supplier is correct in mixed and equal characteristic.
CONSUMED BY: GENHN counts/general capstone.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.135  `F4-JOINT` graded model
WHERE: T1 §4.1 battery.
STATEMENT: A finite graded-carrier frame has f₁=2, η=ω≠1, w=ω≠1 and scored predictions, but is not an explicit Q_p-polynomial realization.
CONSUMED BY: T1 battery, not HYP.62’s realized demand.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — keep supply model separate.

### v3 additions from the completeness sub-sweep

Twelve rows folded from `runs/qgen/HYPLEDGER_deltas.md`. Delta items 6, 12, 13 were actions and are in `MAINTENANCE QUEUE`; delta item 16’s six sub-items are in `OFF-PATH`. Every quote below was re-verified at its cited file and line.

HYP.136  `S-0` statement-ledger tripwire
WHERE: `verification/openmath/statement_ledger.py --check`; `runs/qgen/s0_check_postcampaign.txt`; `docs/PROJECT_STATE.md` append #45a L4485.
STATEMENT: The compression campaign never weakened a statement — the instrument guarding that guarantee, flagged stale by the sub-sweep (baseline `head_commit 788bba26…`, 178 statements, 20 later commits touching `lean/notes/openmath/`), has now been run against the working tree at HEAD.
CONSUMED BY: every ledger row whose source quote is a post-compression statement — i.e. the trust of this file’s own transcriptions.
CLASS: instrument-tripwire
PROPOSED DISPOSITION: **CLOSED** — GREEN post-campaign. `runs/qgen/s0_check_postcampaign.txt`: “CHECK: 178 baseline statements; 0 changed, 0 deleted, 2 added. / GREEN: every baseline statement byte-stable (normalized)”, both additions ADDED-allowed (HETOW-4 #2, GENTOW2-B″ #2). Recorded at PROJECT_STATE #45a. Not an open obligation; retained as the reference that closes it. (v3 delta item 1.)

HYP.137  `HEX3-BOX-1` tail-σ-certification lemma
WHERE: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` L437, L681–693; `GENIND_PROOF_2026-08-08.md` L1498; `TIGHTNESS_CENSUS_2026-08-11.md` O-10 L93.
STATEMENT: The exact law for the σ-undecided mass is not derived — “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” (HEX3 L437) — because the TRP tail-σ transport loses ghost digits.
CONSUMED BY: GENIND’s S8.2 W-12.B consistency clause, pinned open at HEAD: “r3 b6a1d69 (17:53: the S8.2 W-12.B consistency clause conditionalized on the open HEX3-BOX-1 tail-σ lemma)”. Failure price displayed at HEX3 L684–686: undecided(3,q,N)·q^(−2N) diverges linearly in N and “W-12.B would be FALSE at n = 3”. NOT consumed by drainage: HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split; only this aside’s W-12.B corroboration is conditional on it.”
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MATH — the tail-σ lemma is unproved and now has a named live consumer, so it is no longer index-only under HYP.29. **The delta’s framing is corrected here**: census O-10 (OUT-OF-CONE, “open (refinement)”, “Drainage consumes only the proved conservative upper bound U₃^conv”) and GENIND’s pin record are BOTH accurate and do not contradict — they name different consumers (drainage vs. the n=3 W-12.B corroboration aside). Carry-vs-node is owner question 9. (v3 delta item 2.)

HYP.138  N3_CHECK §6d HEX3 reconciliation
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md` L359, L366, L372.
STATEMENT: An unresolved corpus-side reconciliation, dated after the census: “### 6d. ⚠ A reconciliation item for the corpus side (reported, not resolved)”; the two readers’ numbers are “**not measuring the same set**, so these runs neither confirm nor refute THEOREM HEX3.A”; “Reconciling the two readers’ conventions (per-centre vs whole-space…)” is left “a task for whoever next touches HEX3.”
CONSUMED BY: the same HEX3 supplier as HYP.29 — the machine corroboration of `hExhaust3`, not its proof.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — convention reconciliation between the two readers; until it lands, neither reader’s count may be cited as confirming or refuting HEX3.A. (v3 delta item 3.)

HYP.139  `W-1` transport
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131.
STATEMENT: After the FGMN-WELD cite was PDF-verified and DISCHARGED (2026-08-12), the residue is not citational: “Residue is NOT the cite but the transport: **W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT**, unchanged by this unit” (I-4); §5 — “the FGMN residue that remains is the W-1 transport (ATTEMPT), which is **a proof obligation, not a citation one**.”
CONSUMED BY: I-4’s own consumer chain — W-9 (proved GIVEN W-6..W-8) → GENHN-4’s layer-1 carry bookkeeping at μ≥3 (GENHN-BOX-2) → count laws at μ≥3; hence under HYP.23 ([H-d] censuses) and HYP.81.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — an in-cone ATTEMPT-grade proof obligation the v2 sweep dropped while folding census rows I-1/I-2/I-3/I-5. (v3 delta item 4.)

HYP.140  `GENTOW5_WI` stale grade box
WHERE: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md` L2 and S7 L465; `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-2 L46; `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 18.
STATEMENT: Three grades coexist in the corpus for the same unit. The note’s own S7 box at HEAD still reads “**Grade: 0/2 (composed; hostile arc owed)**” (title line L2 likewise), census I-2 reads “arc at **1/2** (PE1 CLEAN; PE2 in flight, skeleton committed)”, and the SOL certification ledger row 18 reads “WI ([GENTOW5-W(i)]) … **CERTIFIED 2026-08-12** — R10 pass 3: zero findings on all five charges, sol verdict ‘CERTIFIED 2/2’ (runs/cert/R10_wi_pass3_output.log)”.
CONSUMED BY: extraction of HYP.40’s and HYP.63’s grade status — a reader landing on the note alone reads 0/2.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — strike/append the stale S7 box and title line, exactly as HYP.100 handles the stale T5 sentence. **The delta’s conclusion is corrected here**: this is NOT a contradiction of HYP.40 or HYP.63. HYP.40’s “certified 2/2” is right at HEAD-of-record (SOL row 18, 2026-08-12, which also postdates census I-2), and the note carries an r1 append of 2026-08-12 that itself “Repairs the Codex passPE2 finding G-1” (L528) — so PE2 demonstrably ran. The delta’s other half, that the ledger “disposes [GENTOW5-W(i)] as NODE”, was already absorbed: v2 re-dispositioned HYP.63 NODE→CARRY (COR-32/33). (v3 delta item 5.)

HYP.141  Phase-0a shard source-designation refutations
WHERE: `spec/EFF-T3.md` L1599, L1610; `spec/EFF-T1-s1of3.md` §8 L1644–1670 (OPEN-CALLs 1–5).
STATEMENT: The Phase-0a effective shards, written after the v2 sweep’s inputs, carry live calls that refute source designations this ledger’s dispositions lean on. Two bite: OPEN-CALL 3 for `(H-GENHN-CLEAR)` — “fixed-string grep for that designation in `GENHN_PROOF_2026-08-08.md` returns zero” (re-verified: count 0) — and OPEN-CALL 2 for `(H-JA-RES-CONJ)`, which supplies no external unit designation and refuses the `JA-EPS-CORR` conflation.
CONSUMED BY: HYP.54 and HYP.55, whose dispositions are corrected above; and HYP.105, routed to 0d by EFF-T3 OPEN-CALL 1 / EFF-T1 OPEN-CALL 4.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — keep the shard OPEN-CALLs and this ledger’s rows in one register; every future disposition citing “the accepted <X> site” must carry a grep-verifiable designation or be marked undesignated. ALREADY ABSORBED and not re-folded: OPEN-CALL 1 (`(H-JA-CONJ)_i`) is v2 HYP.53, whose COR-23 correction already removed the nonexistent accepted supplier; OPEN-CALL 4 is v2 HYP.105; OPEN-CALL 5 is v2 HYP.52/HYP.57. (v3 delta item 7.)

HYP.142  `GENHN-ERR-1` dual disposition
WHERE: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` L2593, L2624; `HE6R1_RECON_2026-08-08.md` L926, L1031.
STATEMENT: Two un-reconciled records at HEAD. Settled side: “**GENHN-ERR-1 is settled.** The ordinary μ=2 stage law is the (2,K)-law at B=D′h, not at the old numeric node S=e₁h” (L2593), with “a final transcription-confirmation rides the next queue” (L2624). Un-retracted side: “Repairing the completion statement without weakening it **requires a new lemma** re-running GENHN’s f₁≥2 count argument on the corrected region” (HE6R1 L926), and the dated re-display heads “R7 finding 1 closed under the owner’s directive; **finding 2 routed to a proof unit**” (L1031).
CONSUMED BY: GENHN count laws at f₁≥2, hence the n≥8 leg (HYP.82) and the μ≥3 censuses (HYP.23).
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — reconcile the two records and say which governs; escalates to MATH if the HE6R1 reading governs, since that reading owes a new count lemma. (v3 delta item 8.)

HYP.143  `HE3-BOX-6` ramified branch (ii)
WHERE: `lean/notes/openmath/HE3_PROOF_2026-08-08.md` L1334–1361, L1694.
STATEMENT: “**HE3-BOX-6 (THE ONE SURVIVING GAP** — found by this unit’s own review, before any hostile pass; it localizes to μ≥4, so μ=3 is unconditional).” LEMMA HE3-4 branch (ii) has no test key at a non-integer dv height, and the substitute ramified base change O ↝ O[Π]/(Π^ℓ−π) is “stated too cheaply: **Φ′ need not remain irreducible over O₂**”, so the SLOT LEMMA and HE3-1’s norm computation are unavailable there. Post-R8: “**Only the ramified branch (ii) remains in HE3-BOX-6.**” The repair route (higher-degree test polynomials at fractional heights, i.e. the higher-order Montes construction) is “IDENTIFIED REPAIR ROUTE (**not executed here**)”.
CONSUMED BY: COROLLARY HE3.B for μ≥4, i.e. degree n ≥ e₁f₁μ ≥ 8 — the supplier under HYP.81’s conjunct above μ=3, alongside HYP.82. HE3.A and [GENHN-HE(μ)] stay UNCONDITIONAL for μ≤3 and every n≤7.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — named repair route, not executed. Supplier-side only: it refines HYP.81 rather than adding a conjunct. (v3 delta item 9.)

HYP.144  `GENTOW4-BOX-1/-2/-4`
WHERE: `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` L577–584, L585–590, L614–618.
STATEMENT: BOX-1 (mixed-side multiplicity tie) — the tie mu2*(r) = m_r “is UNPROVED here (S4; Ore-II/FGMN Lemma 2.17 content — a faithful-cite unit in GENTOW2’s pattern would retire it)”; READ and σ are unaffected, what is lost is the level-1 prediction of block length. BOX-2 (partial-side entry budgets) — the budget fibration is proved only on the FULL-side locus 𝒯; “the item-(4) **COUNT layer stays open**”. BOX-4 (grade) — “**0/2 attempt**, composed this session, no hostile arc”, over a conditionality stack including HETOW-1/2 (HETOW 0/2) and the HE6R1 0/2-grade annex stack.
CONSUMED BY: partial-side count laws feeding the same μ≥3 count layer as HYP.139 and HYP.142.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — BOX-2’s open COUNT layer is the binding residue; BOX-1 is retirable by a faithful-cite unit; BOX-4 is a standing grade cap on all three. (v3 delta item 10.)

HYP.145  GENTOW2 S6.1 rows 23–24
WHERE: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` L1342; `GENTOW5_WI_2026-08-10.md` L480.
STATEMENT: “Status disclosure: rows 23-24 enter at DESCRIPTIVE / record-interpretation status, **not consumed status** — a future round elevating either cite to consumed status **owes** the S6.1 two-leg method.” Row 23’s content, the avatar = w identification, “is NOT consumed and is now **measured to GAP at LW3**.”
CONSUMED BY: HYP.66 (`WFRAME OPEN-3`), which is gated on exactly this row; and any future consumed-status use of rows 23–24.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE — preserve the descriptive fence and the two-leg debt attached to elevating it. (v3 delta item 11.)

HYP.146  `W11-BOX-1`
WHERE: `lean/notes/openmath/W11_PROOF_2026-08-08.md` L474.
STATEMENT: “**W11-BOX-1 (n = 2 only).** The general W-11 — the menu tie at all degrees and orders — is **NOT proved**: S4.3 is a program with named owed inputs (S_λ(q) censuses, JB row-12 residue, JC warrant, uniform drainage).”
CONSUMED BY: any W-11 use above n=2; its named owed inputs are HYP.21 (JB row 12), HYP.20 (JC warrant), and the drainage rows HYP.27/HYP.30.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — a program, not a proof. Distinct from HYP.128 (`W-10` all-O), which is an instance-generality edge, not a menu tie. (v3 delta item 14.)

HYP.147  `exists_anisotropic`
WHERE: `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md` L697, L704.
STATEMENT: “What is **fenced out**: the *general-`O`* inert lower bound … the `gate_bracket_*` payoff is therefore stated at `q = 2, 3` rather than for all `O`.” The missing declaration is displayed: `theorem exists_anisotropic (O) [bundle] : ∃ a : Fin 2 → O, Anisotropic a`.
CONSUMED BY: the general-`O` reading of the `gate_bracket_*` payoff; the q=2,3 statement stands without it.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — declaration/proof-packaging; re-verified absent from both trees (`grep -rn exists_anisotropic leanfinal/ leancheck/ --include=*.lean` returns nothing), plausibly reachable from leancheck’s `card_aniPairSet` / `2A + q = q²` but not landed. (v3 delta item 15.)

## MAINTENANCE QUEUE (owner: orchestrator)

Actions, not conditions. These are NOT hypotheses and are not counted in the row tallies; they are recorded here so the completeness sub-sweep’s action items are not lost by being un-foldable as HYP rows.

MQ-1  **n=2 adversarial pass.** `leancheck/notes/N2_EXACT_2026-08-13.md:327` — “**No independent adversarial (Codex) pass was run on this unit.**” This unit supplies the capstone’s entire degree-2 leaf (ram = 1/(q+1), split = inert = q/(2(q+1))), which the preview calls unconditional. Already in PROJECT_STATE #45a’s queued batch (“the n=2 codex pass”). (v3 delta item 6.)

MQ-2  **Consumption checks + dated appends.** `runs/qgen/EFFT3_crossread.md:149` — “GENTOW5-W consumption check was never run and its dated append never landed”; `spec/EFF-T3.md:1599` — ABS-G5W “marked ‘check + append outstanding.’”; `lean/notes/openmath/T4_CERTIFICATE_WITNESS_2026-08-12.md:2241` — “Consumption checks + the absorbed notes’ dated appends” ride the next queue. Already in PROJECT_STATE #45a’s queued batch. (v3 delta item 12.)

MQ-3  **[GMN12] §4 characteristic audit — unperformed.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §6 item 5 L481–482: “**[GMN12] §4 (theorem of the index) characteristic-audit.** I did **not** read GMN §4 line by line. §3 F-2’s claim that its argument is characteristic-free is *a plan, not a verified fact*.” This bears on owner question 1: it qualifies the internal-F-2 branch of HYP.15’s choice, which is offered as the alternative to citing. Not in the PROJECT_STATE #45a batch — new. (v3 delta item 13.)

## OFF-PATH (v3 TIER-3, one line each)

Recorded for completeness; none is on the capstone path, and none is counted in the tallies.

- `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md:614` — the n=3 Python leg “needs a `ℚ_p`-factorization oracle; left as an open verification item.”
- `leanfinal/verification/EQUALCHAR_PROBE_2026-08-13.md:141` — the char-2 classifier fix “was validated empirically (exact match to Z_p) at N≤4, **not proved complete** in general.”
- `docs/TIGHTNESS_CENSUS_2026-08-11.md:97` (O-14 RIDER-DEBT) — minor acceptance riders owed per appends; “Some may have landed in B-wave folds; **not re-verified here**.”
- `lean/notes/openmath/WFRAME_NOTE_2026-08-10.md:374` — OPEN-4 (“w = 1 as a question, correctly housed”); the v2 dedup section already folds it into OPEN-1, so it is indexed, not new.
- `lean/notes/openmath/HE7_PROOF_2026-08-08.md:1304` — “(PE3) on the post-r3 text” — **SUPERSEDED at HEAD**: ANNEX F-1 (L1603–1605) records “HE7 was **ACCEPTED 2/2** at PE3”, so the pass the delta reports as owed has run.
- `lean/LeanUrat/Stage2/UniformityTarget.lean:92,107` — two `sorry`s in the superseded quarry capstone, by design and disclosed in the file header (“it contains exactly two `sorry`s — the two target theorems’ bodies — per the E-phase precedent”); distinct from the clean `leanfinal`/`leancheck` result.

## Deduplication and non-deduplication

- A0/A1/A2 are W12.D’s public fixed-n interface. [W12-H] and [GENIND-H] are lower suppliers, not extra conjuncts when expanded.
- Drainage levels are linked but not identical: A2 ← W12-BOX-4/DRAIN-N4 ← GENIND-(CS-1Q) for n≥4. Cubic Lean names are `UndecidedVanishes O 3 σ` and `drainage_three_of_triple`. GENIND-BOX-4 is a distinct bookkeeping box.
- CS-1 is a count-fibration with both menu and drainage consumers, CS-2 is a bracket, and CS-EXACT forbids bound-only laws; A1 is their public compression.
- [H-e]=CS-3 only when both the citable GMN decision and project-internal window pinning are included; at composite stages it supplies A0.
- [H-b] is JB row 12 only. JB-NOLEG is the strict four-row superset 4/5/12/22. They are not merged.
- [H-c] aggregates VD-m, C-coll, R-coll, PERIM-μ, DMULT-S, JD0-BOX-2, W2-VALUE, and reachable T4 residue. DMULT-S is double-parented through [H-a]/GRTJC and [H-c].
- GENTOW5-W(i), Q4’s conditional, and 𝒲_(≤i) are one live cumulative premise. WI certification proves an induction step, not the premise.
- W12-BOX-2/hMenu3 and W12-BOX-3/hExhaust3 are the HMENU3/HEX3 perimeter. TAIL-CERT=HEX3-BOX-1=HM3-BOX-1; ANNEX-2’s disc≠0 correction remains.
- Strong Hensel HYP.04 is not coprime-factor Hensel: X·X² is not coprime.
- `typeOf` shift/scale invariance is stronger than certificate-local lemmas such as `RamAt_shift`.
- T3-JOINT-OPEN and F4-JOINT are opposite objects—realized p-adic demand versus finite graded-carrier supply—and are not merged.
- WFRAME OPEN-1 absorbs the older “can w=1?” question.
- GENTOW6-BOX-1 overlaps COMPOUND-6.5′ on f₁≥2,μ₂≥3; P-BINOM and S8.1-MEMBER are adjacent proof units, not identical.
- `RealInstanceAt.faithful` and the Haar bridge are live indexed items, not superseded plans; only the Denef route remains superseded.
- MP1′ removes only an extra frame-level obligation: it is retired relative to the same LB1/MP1 triggers, which remain.
- GENIND-BOX-1 is coextensive with [GENIND-H]; GENIND-6 and ANNEX-LEMMA GENIND-C2Q are indexed under parent rows rather than counted as new public conjuncts.

v3 additions to this section:

- HEX3-BOX-1 (HYP.137) is promoted out of HYP.29’s index because it has a named live consumer, but the two rows are not merged and not duplicates: HYP.29 is the `hExhaust3` menu-exhaustion box, HYP.137 is the tail-σ law it explicitly does not need. Census O-10 (drainage) and GENIND’s S8.2 pin (W-12.B corroboration) name different consumers and are both correct.
- HE3-BOX-6 (HYP.143) is a supplier under HYP.81, not a new conjunct: [GENHN-HE(μ≥3)] is unconditional at μ≤3 (n=6,7) and rides HE3-BOX-6 only at μ≥4 (n≥8), where HYP.82 also lives. It is not merged with HYP.82 — a tower leg and a branch gap are different objects.
- W11-BOX-1 (HYP.146) and HYP.128 (`W-10` all-O) are distinct: a general menu tie versus an instance-generality edge.
- The GENTOW5_WI grade box (HYP.140) is a corpus-consistency row, the sibling of HYP.100, and does NOT correct HYP.40 or HYP.63 — SOL certification row 18 (2026-08-12) is HEAD-of-record and postdates both the note’s S7 box and census I-2.
- W-1 (HYP.139), GENHN-ERR-1 (HYP.142), and GENTOW4-BOX-2 (HYP.144) all feed the same μ≥3 count layer but are three separate obligations: a transport, a record reconciliation, and a partial-side count layer.
- Delta items already absorbed by v2 and deliberately not re-folded: the GENTOW5_WI NODE-disposition complaint (cured by v2’s COR-32/33 NODE→CARRY on HYP.63) and EFF-T1 OPEN-CALLs 1/4/5 (v2 HYP.53, HYP.105, HYP.52/57).

## Coverage statement

The v2 sweep incorporates the full cross-read and quoted loci. The W12 locator is corrected to `W12_PROOF_2026-08-08.md`; T1 rows cite §1.1/§5 rather than a nonexistent “effective hypothesis list”; GENIND rows cite §S1/§S7.1/§S8/§C2-G1; census labels are hyphenated. Coverage includes all T-unit acceptance records, W12/GENIND, low-degree Lean notes, citation-scope resolution, tightness census, Project State through the ledger append, GENTOW5_WI, and all eight qgen audits’ INTERFACE rows.

v3 extends coverage to the completeness sub-sweep’s sources: HEX3/HE3/W11/GENHN/GENTOW2/GENTOW4/GENTOW5_WI/HE6R1 proof notes at HEAD, census rows I-4 and O-10, N3_CHECK §6d, N2_EXACT §7 grade disclosure, CITE_SCOPE §6, the Phase-0a shards `spec/EFF-T3.md` and `spec/EFF-T1-s1of3.md`, the SOL certification ledger, and the S-0 instrument with its post-campaign green run. The 2026-08-12 SOL certification ledger is HEAD-of-record for unit grades and supersedes both in-note grade boxes and the 2026-08-11 census where they disagree.

Deliberate exclusions: `htameFE`; closed quadratic STATUS items; stronger quadratic rate/sharpness questions; X-LEMMA; stronger out-of-cone W10-GEN; TAIL-CERT as a separate row because indexed under HYP.29; rider debt/pure coverage disclosures without a consumer; nonexistent GENTOW6-BOX-5; and retired MP1′. The 2026-08-11 census headline is chronologically superseded for ledger purposes by the 2026-08-12 CS-1Q correction and 2026-08-13 Lean notes.

## Capstone-conditionality preview

A dagger marks an owner decision, not every proof unit. Parent aggregates appear once. Displays A and B are alternatives and must never be conjoined. The n=2 W-12.D case is unconditional; n=3 is conditional only on the cubic HMENU3/HEX3 proof perimeter.

### Display A — public interface

For n≥4 and every complete DVR O with residue field size q, assume uniformly in O:

[
  NS7(O)†
  ∧ LB1 ∧ MP1
  ∧ HE7A[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]
  ∧ ∀ i≥3, ((H-VARTHETA-RES)_i ∧ 𝒲_(≤i))
  ∧ A0_n[disc≠0] ∧ A1_n ∧ A2_n
  ∧ JB-NOLEG(rows 4,5,12,22)†
  ∧ [H-c]† = JD1ValuePackage[
       VD-m, C-coll, R-coll, PERIM-μ,
       DMULT-S†, JD0-BOX-2†, W2-VALUE†]
  ∧ (H-e)-window-pinning
  ∧ ([GENHN-HE(μ≥3)] if n≥6)
  ∧ ([GENHN-TOW-1] if n≥8)
  ∧ AllOInterfaces[
       GENIND-1, RMG, ILN, GRB, ITER-LAW, W/J, DU, W-10,
       J-D0, L2core, HUMAN_PROOF, local-integrals, CONV, GENHN-count]
]
  ⇒ ∀ σ with deg σ=n,
       ∃ num, den ∈ ℤ[q], independent of O,
         genuineDensity_O(σ)=num(q)/den(q)
         [Haar and Σ_σ=1 are decided by needs-Asvin question 5].

### Display B — expanded suppliers

Display B is identical except that

    A0_n[disc≠0] ∧ A1_n ∧ A2_n

is replaced, never supplemented, by

    ∀ G ∈ Genres(n),
      CS1_G ∧ CS2_G ∧ CS3_G[disc≠0, window-pinning]
      ∧ CSExact_G ∧ CS1Q_G.

CSExact means an exact finite q-power-sum menu and an exact stage drain, not asymptotic bounds; CS1 serves both menu and drainage. In both displays O,q are bound on the hypothesis side, A0–A2 are fixed-n, and σ is quantified only in the conclusion. The window law, GENHN thresholds, pinning half, all four JB rows, four restored value hypotheses, HE7.A suite, and all-O supplier interfaces are visible. MATH rows remain proof blockers; where a public aggregate is carried, they are not falsely declared absent from its supplier DAG.

## THE 0d PACKAGE — eight owner questions

1. **Trusted base (HYP.15, `NS-7`).** Do we cite [AGNPRW] Thm 5.2 for OM termination over every complete DVR — accepting that its index step is itself discharged by citation to ℚ_p-scope sources, recorded honestly in `AXIOM_FAITHFULNESS.md` — or spend F-2's 2–4 pages proving index-descent internally on the `L4` lattice machinery? *(The source recommends citing. Coupling: the cite branch forfeits the `≤ ½ v(disc f)` depth bound that HYP.16 assumes — COR-13.)*
2. **Scheduling + scope (collapses 10 open calls).** Run the `WELD-FACE-AUDIT` (census S-4, one session) before the 0d freeze, so the weld residues are carried only if reachable — and if so, do we widen its charter from the four rows the census assigns it (HYP.74–77) to also cover HYP.21, 22, 67, 68, 69, 71 (COR-41)?
3. **Capstone signature (MISS-04).** Sign off `UniformityStatement`'s three live points: `∀ 𝒪` over `Type` (universe 0); the rational function evaluated at `(q : ℚ)` with equality read in `ℝ` by coercion; `den.eval q ≠ 0` demanded per-`𝒪` rather than globally. *(The note's fourth point, `σ.degree = n` doing no work, is self-superseded — `typeOf_degree` landed as gate G13.)*
4. **Definitions (HYP.12, MISS-13, MISS-04).** The `(e,f)` ordering/multiset convention *"deserves a human read"*; `W12-BOX-7`'s σ-convention at the TRP tail (two conventions can disagree on deep-tail members); and `HENSEL_FACT` §4's faithfulness paragraphs, headed *"FLAGGED FOR ASVIN'S REVIEW"*.
5. **What the theorem claims (MISS-05, DEF-07).** Does the frozen capstone assert the **Haar density** — as W-12.D and the census do — or only the limit of decided proportions, which is what Lean's `genuineDensity` is and which `GENUINE_DENSITY` §3B.4 records the bridge to as unformalized? And is `Σ_σ R_σ = 1` inside the frozen statement?
6. **Grade (COR-08).** `JD0-BAR`: run JD0's 2-clean hostile arc, or sign off the 68,523/0 machine grade as the bar? *(The census offers both; the ledger silently chose the first.)*
7. **Axioms (MISS-06).** `AX-CELLREC`/`AX-LEAF` faithfulness entries are **DRAFT, PENDING ASVIN REVIEW** and the census says they *"gate the LEAN capstone claim"*. Are they on the `leanfinal` path at all, or is `leanfinal` Lean-core-only? Same question for census **L-4**, the `RealInstanceAt.faithful` placeholder.
8. **Display shape (DEF-01).** Freeze **Display A** (public interface A0–A2) or **Display B** (expanded CS-* supplier list) — not both.
9. **[v3] `HEX3-BOX-1` carry-vs-node (HYP.137).** The tail-σ-certification lemma is unproved and `hExhaust3` provably never needed it (HEX3 L692–693), yet GENIND's r3 pin conditionalizes the S8.2 W-12.B consistency clause on it and HEX3 displays the price as "W-12.B would be FALSE at n = 3" — so do we CARRY it as a named n=3 conjunct in the preview, or keep it a NODE-grade refinement indexed under HYP.29 on the strength of the census's OUT-OF-CONE reading?

## CHANGES-FROM-v1

- HYP.01 corrected: restored the disc≠0 faithfulness locus (MISS-04/06 context).
- HYP.02 corrected: exact-solve injectivity, not congruence uniqueness (COR-11).
- HYP.10 re-dispositioned MATH→NODE, LOW-CONFIDENCE (COR-10).
- HYP.11 re-dispositioned NODE→MATH and restored prerequisites (COR-09).
- HYP.12 corrected into the owner definitions package (row verification/owner Q4).
- HYP.14 corrected stop/continue polarity (COR-12).
- HYP.16 corrected coupling to HYP.15’s F-2 branch (COR-13).
- HYP.18 corrected with separability fence (COR-14).
- HYP.19 corrected: W12 filename and n≥4 composite-stage scope (COR-01/COR-03).
- HYP.20 corrected: W12 filename and child-conditionality fence (COR-01/D-06).
- HYP.21 corrected: W12 filename and refusal of the JB-NOLEG merge (COR-01/D-05).
- HYP.22 corrected: W12 filename and restored value-layer children (COR-01/MISS-02).
- HYP.23 corrected: W12 filename and [H-a]–[H-c] conditioning (COR-01/COR-07).
- HYP.24 corrected/re-dispositioned NODE→CARRY: window-pinning half and fences restored (COR-01/COR-04/COR-30).
- HYP.25 corrected: window-decided core family and disc≠0 fence restored (COR-01/COR-05).
- HYP.26 corrected: σ removed from A1’s binder and simultaneous all-q scope restored (COR-01/COR-06).
- HYP.27 corrected: W12 filename and exact remainder scope restored (COR-01).
- HYP.28 corrected: W12 filename and deeper-tier perimeter exposed (COR-01/COR-09).
- HYP.29 corrected: W12 filename and tail aliases/correction indexed (COR-01/D-08).
- HYP.30 corrected: W12 filename, I-1 label, and GENIND-BOX-4 nonmerge (COR-01/COR-02/D-02).
- HYP.31 corrected: real GENIND loci, n≤3 vacuity, and n≥6/8 conjuncts (COR-28/COR-31/MISS-01).
- HYP.32 corrected: real locus and dual menu/drainage consumer (COR-28/D-03).
- HYP.33 corrected: real GENIND locus (COR-28).
- HYP.34 corrected/merged: separability, disc≠0, and pinning restored; represented by HYP.24 (COR-04/COR-28/COR-30/D-04).
- HYP.35 corrected: exact menu and exact drain, not bounded/asymptotic (COR-27/COR-28).
- HYP.36 corrected: both CS-1Q clauses restored without overstated conclusion (COR-28/COR-29).
- HYP.37 corrected: real §S8 locator (COR-28).
- HYP.38 corrected: census label I-3 (COR-02).
- HYP.39 corrected: PROVED/machine grade, process sub-bar, and owner option (COR-02/COR-08).
- HYP.40 corrected: real name, certified grade, scope residue, and deep consumers (COR-02/COR-15/COR-34).
- HYP.41 corrected full LB1 trigger/consequent/consumers (COR-18).
- HYP.42 corrected own locator and MP1 items 2–5/consumers (COR-19).
- HYP.43 corrected/reclassified as SEC-RANK carrier hypothesis with termination consumer (COR-16).
- HYP.44 corrected/reclassified as RISE carrier hypothesis with HT consumer (COR-17).
- HYP.45 corrected simultaneous 0/2 and 1/2 grades plus level-two consumer (COR-20).
- HYP.46 corrected: removed deleted arbitrary-depth terminating reduction (COR-21/COR-26).
- HYP.47 corrected: real T1 locus and ladder formula (COR-21/COR-26).
- HYP.48 corrected: real T1 locus and slot-grade identity (COR-21/COR-26).
- HYP.49 corrected: consumed-ladder/value-zero restrictions restored (COR-21/COR-26).
- HYP.50 corrected: zero-component formula and fence restored (COR-21/COR-26).
- HYP.51 corrected: independent nonvanishing and i=2/i≥3 supplier split (COR-21/COR-26).
- HYP.52 corrected: scalar K_i codomain and false general discharge removed (COR-21/COR-22).
- HYP.53 corrected: real locus and nonexistent accepted supplier removed (COR-21/COR-23).
- HYP.54 corrected: exact polynomial/support/degree formulas restored (COR-21/COR-26).
- HYP.55 corrected: hypothesis, clearance bound, and carry clause restored (COR-21/COR-26).
- HYP.56 corrected: complete HETOW data/formulas restored (COR-21/COR-26).
- HYP.57 corrected/re-dispositioned: vartheta membership, loci/consumers, and technical CARRY unit (COR-24/open-call adjudication).
- HYP.58 corrected: real T1 locus and strict domain retained (COR-21/COR-26).
- HYP.59 corrected: real T1 locus and forbidden strengthenings enumerated (COR-21/COR-26).
- HYP.60 corrected: real T1 locus and exact iff criterion retained (COR-21/COR-26).
- HYP.61 corrected: zero argument and “gates no C1–C7” consumer status (COR-21/COR-26).
- HYP.62 corrected/split from HYP.135 and moved to T3 §8.5 (COR-25/COR-40/D-11).
- HYP.63 re-dispositioned NODE→CARRY under governing T5 text (COR-32/33).
- HYP.65 corrected notation/disjunction/i=1 consumer (COR-38).
- HYP.66 corrected: equality fails; exact gap is open (COR-37).
- HYP.67 corrected: real T4/upstream locus and no false HYP.73 dependency (COR-35/COR-41).
- HYP.68 corrected: full-side openness and proved-budget/open-ledger split (COR-35/COR-40).
- HYP.69 corrected: real locus and no false HYP.73 dependency (COR-35/COR-41).
- HYP.70 corrected/re-dispositioned: sealed ask DISCHARGED; widening residue separated; OPEN-CALL removed (COR-35/COR-36).
- HYP.71 corrected: missing battery-witness conjunct and no false HYP.73 dependency (COR-35/COR-40/COR-41).
- HYP.72 corrected downstream, not T4, fence consumer (COR-39).
- HYP.73 corrected charter to HYP.74–77 (COR-41).
- HYP.74 corrected: S-5 label and owner call collapsed into question 2 (COR-02/open-call adjudication).
- HYP.75 corrected: four JB rows restored and [H-b] merge refused (COR-02/D-05).
- HYP.76 corrected: S-7 label and owner call collapsed into question 2 (COR-02/open-call adjudication).
- HYP.77 corrected: S-8 label, double parentage, and owner-call collapse (COR-02/D-06/open-call adjudication).
- HYP.78 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.79 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.80 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.81 added: GENHN-HE multiplicity≥3 conjunct (MISS-01).
- HYP.82 added: GENHN-TOW-1 n≥8 conjunct (MISS-01).
- HYP.83 added: VD-m value-layer hypothesis (MISS-02).
- HYP.84 added: C-coll value-layer hypothesis (MISS-02).
- HYP.85 added: R-coll value-layer hypothesis (MISS-02).
- HYP.86 added: PERIM-μ value-layer hypothesis (MISS-02).
- HYP.87 added: GENIND-BOX-3 (MISS-03).
- HYP.88 added: GENIND-BOX-4, distinct from W12-BOX-4 (MISS-03).
- HYP.89 added: GENIND-BOX-5 grade cap (MISS-03).
- HYP.90 added: GENIND-BOX-6 conventions (MISS-03).
- HYP.91 added: GENIND-5 obstruction list (MISS-03).
- HYP.92 added/merged: ANNEX-LEMMA GENIND-C2Q under HYP.36 (MISS-03).
- HYP.93 added/merged: GENIND-6 under HYP.31 (MISS-03).
- HYP.94 added: capstone signature sign-off (MISS-04).
- HYP.95 added: Haar bridge (MISS-05/D-14).
- HYP.96 added: census L-3 AX-CELLREC/AX-LEAF row (MISS-06).
- HYP.97 added: census L-4 RealInstanceAt placeholder (MISS-06).
- HYP.98 added: census L-5 DEFINITION-AUDIT (MISS-06).
- HYP.99 added: T3/T5 frame staleness (MISS-07).
- HYP.100 added: contradictory T5 HEAD sentence (MISS-08).
- HYP.101 added: HE7.A source suite (MISS-09).
- HYP.102 added: MID-PEEL items 2–5 (MISS-10).
- HYP.103 added: T2 S4.2 nonclaims (MISS-10).
- HYP.104 added: C3 lift coefficient-space obligation (MISS-11).
- HYP.105 added: tower-correctness splitting-type gate (MISS-11).
- HYP.106 added: nonzero-digit exact-lift contract (MISS-11).
- HYP.107 added: binary-carry restriction (MISS-11).
- HYP.108 added: A6 provenance split (MISS-11).
- HYP.109 added: T-unit evidence caveats (MISS-12).
- HYP.110 added: W12-BOX-5 code/convention seam (MISS-13).
- HYP.111 added: W12-BOX-7 σ-convention (MISS-13).
- HYP.112 added: T4 μ₂≥3 candidate fence (MISS-14).
- HYP.113 added: T4.2(c) full-exposure premise (MISS-14).
- HYP.114 added: T4.2(d) provenance exclusion (MISS-14).
- HYP.115 added: T4 fail-closed pin convention (MISS-14).
- HYP.116 added: GENTOW3-BOX-2 coverage (MISS-14).
- HYP.117 added/merged: G5-COND consumer list under HYP.63 (MISS-15).
- HYP.118 added: T3 delivered-scope narrowing (MISS-15).
- HYP.119 added: Hensel branch-(ii) reconciliation (MISS-16).
- HYP.120 added: seven unread audit slices/INTERFACE class (MISS-17).
- HYP.121 added: GENIND-1 all-O interface (MISS-18).
- HYP.122 added: RMG all-O interface (MISS-18).
- HYP.123 added: ILN all-O interface (MISS-18).
- HYP.124 added: GRB all-O interface (MISS-18).
- HYP.125 added: ITER-LAW all-O interface (MISS-18).
- HYP.126 added: W-1/W-2/J-A/J-B all-O interfaces (MISS-18).
- HYP.127 added: DU lemma all-O interface (MISS-18).
- HYP.128 added: W-10 instance all-O interface (MISS-18).
- HYP.129 added: J-D0 all-O interface (MISS-18).
- HYP.130 added: L2core all-O interface (MISS-18).
- HYP.131 added: HUMAN_PROOF subproof all-O interfaces (MISS-18).
- HYP.132 added: local-integrals all-O interface (MISS-18).
- HYP.133 added: CONV monic/projective bridge (MISS-18).
- HYP.134 added: GENHN count all-O interface (MISS-18).
- HYP.135 added: F4-JOINT separated from realized T3 demand (COR-40/D-11).
- Dedup section corrected: all nine adjudicated defects are reflected, including wrong JB and joint merges, live GENTOW5-W, partial H-e merge, and live RealInstance/Haar rows (DEDUP audit).
- Preview recomputed as alternative public/expanded displays with correct binders, fences, thresholds, windows, restored components, and conclusion choices (DEF-01–07 plus MISS-18).

## CHANGES-FROM-v2 (v3 completeness-delta fold)

Source: `runs/qgen/HYPLEDGER_deltas.md`, fifteen items in three tiers. Every quoted line was re-verified at its cited file and line before transcription; **zero items were rejected for misquotation** — all fifteen quotes are accurate. Two items were folded with their *adjudication* corrected (HYP.137, HYP.140); the quotes in both were sound, the inferences drawn from them were not.

TIER-1 (items 1–7):
- HYP.136 added: S-0 statement-ledger tripwire, **CLOSED** — the sub-sweep reported it stale; the orchestrator then ran it GREEN post-campaign (178/178 byte-stable, 2 allowed additions), recorded at PROJECT_STATE #45a. Folded as a closed row with its green-run reference, not as an open obligation (delta item 1).
- HYP.137 added: HEX3-BOX-1 promoted from index-only to its own MATH row on a named live consumer; HYP.29 corrected to point at it. Delta framing corrected: census O-10 and GENIND's pin are not in contradiction — different consumers (delta item 2).
- HYP.138 added: N3_CHECK §6d reader-convention reconciliation, unresolved and dated after the census (delta item 3).
- HYP.139 added: the W-1 transport, census row I-4's ATTEMPT-grade proof obligation, missed when v2 folded I-1/I-2/I-3/I-5 (delta item 4).
- HYP.140 added: the GENTOW5_WI stale S7 grade box (0/2 at HEAD vs SOL row 18's CERTIFIED 2/2). Delta conclusion corrected: HYP.40 and HYP.63 are NOT contradicted; the NODE-disposition half was already absorbed by v2's COR-32/33 (delta item 5).
- HYP.141 added, HYP.54/HYP.55/HYP.105 corrected: Phase-0a shard source-designation refutations, including the re-verified grep-zero for `(H-GENHN-CLEAR)`'s cited site. EFF-T1 OPEN-CALLs 1/4/5 were already absorbed by HYP.53/105/52+57 and were not re-folded (delta item 7).
- MQ-1 queued: the n=2 unit's missing adversarial pass (delta item 6).

TIER-2 (items 8–15):
- HYP.142 added: GENHN-ERR-1's two un-reconciled dispositions at HEAD (delta item 8).
- HYP.143 added, HYP.81 corrected with its scope split: HE3-BOX-6's ramified branch (ii), unconditional at μ≤3, conditional at μ≥4 / n≥8 (delta item 9).
- HYP.144 added: GENTOW4-BOX-1/-2/-4, with BOX-2's open COUNT layer as the binding residue (delta item 10).
- HYP.145 added, HYP.66 corrected: GENTOW2 S6.1 rows 23–24 descriptive-status fence; row 23 now measured to GAP at LW3 (delta item 11).
- HYP.146 added: W11-BOX-1 — the general W-11 menu tie is a program, not a proof (delta item 14).
- HYP.147 added: `exists_anisotropic`, re-verified absent from both Lean trees (delta item 15).
- MQ-2, MQ-3 queued: consumption checks + dated appends; the unperformed [GMN12] §4 characteristic audit, which qualifies the internal-F-2 branch of owner question 1 (delta items 12–13).

TIER-3 (item 16): six sub-items placed in `OFF-PATH`, one line each. One is superseded at HEAD — HE7's owed PE3 pass has run (ANNEX F-1, ACCEPTED 2/2).

- **Capstone-conditionality preview: UNCHANGED.** No folded delta adds, removes, or re-binds a conjunct in Display A or Display B. The two rows that touch the preview act on the supplier side only: HYP.143 refines the supplier of the existing `[GENHN-HE(μ≥3)]` conjunct above μ=3, and HYP.139 sits under the existing count-law/census suppliers. HYP.137 lies inside the preview's existing carve-out that "n=3 is conditional only on the cubic HMENU3/HEX3 proof perimeter"; whether it should be *named* there is owner question 9, and until that is answered the displays are left byte-unchanged.
- The eight v2 owner questions are carried verbatim; question 9 is appended and marked [v3].

HYPLEDGER v3: 147 rows / 43 carry / 22 math / 9 needs-Asvin
(dispositions: 43 CARRY · 22 MATH · 77 NODE · 4 MERGED · 1 CLOSED; plus 3 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows)
Superseded tally — HYPLEDGER v2: 135 rows / 43 carry / 17 math / 8 needs-Asvin
