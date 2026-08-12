# CONSUMPTION MAP — informal corpus → Lean scoping (2026-08-12)

**Node vocabulary** (targets in column (b)): leansimp **D3** collapses `Moves*`/`HC*`/`Kernels` into five proof nodes — `Reduction`, `Induction`, `StageLaws`, `Ladder`, `Towers` (as `Stage2/<Node>/*.lean`); leansimp **D4** adds the gauge package `Gauge/{Defs,Cocycle,Transport}.lean` (corrected key `ĉ = lift(c·η^W)`, letter recursion, θ-recursion, wrap composition, normalization laws; Towers consume only exported cocycle/transport theorems). Blueprint §4 (`docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md`) fixes the per-target Lean shape; the leansimp corpus map assigns: LIFTCORNER/GRT*/WELDMASTER/W11 → `Gauge/*` + transport support, W12 → `Reduction/*`, HMENU3/HEX3/GENIND → `Induction/*`, GENH4/GENHN → `StageLaws/*`, HE3/HE6/HE7/HE6R1/HETOW → `Ladder/*`, GENTOW1–6 → `Towers/*`.

---

## T1 — LEMMA GAUGE-COCYCLE (`lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md`)

**(a) Statement.** Over a discretely valued base with uniformizer π, residue field 𝐅_Q, and a MacLane/Okutsu tower with level-i residue fields K_i — level-1 data e₁,f₁,h ≥ 1, gcd(e₁,h)=1, D′=e₁f₁, η = res(x^{e₁}/π^h), base letter z₁:=η, exact-height normalizers n̂ᵢ(m) with n̂ᵢ(0)=1, stage data (e_{i+1}, f_{i+1}, u_{i+1}, ψ_{i+1}), and a monic stage key Φᵢ (r8) — the lemma proves seven clauses. **(C1)** letter recursion z_{i+1} = η_{i+1}·ρᵢ with the unconditional level-2 closed form z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}; arbitrary-depth monomial form only under the named supplier hypothesis (H-JA-CONJ)ᵢ. **(C2)** the wrap identity n̂₁(a)n̂₁(b) = n̂₁(a+b)(x^{e₁}/π^h)^{wrap(a,b)}, the normalized two-cocycle law for τᵢ(a,b), the telescope unit ϑ_{i,s} = res(n̂ᵢ(u)^s/n̂ᵢ(su)) with its recursion, and the level-1 value ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋} (positive sign: wrap correction η^{W(t)}, W(t)=⌊(f₂−t)i(u₂)/e₁⌋). **(C3)** the coherent/multiplicative digit dictionary Γ_t = c_t·ϑ_{i,f−t}; the corrected composed key Φ_{i+1} = Φᵢ^{ef} − Σ k̂_t Φᵢ^{et} with k̂_t = liftᵢ(c_t·ϑ; (f−t)u), deg k̂_t < deg Φᵢ (r8 coefficient-space bound); the B-law u(β_t) = Θᵢ(t)·wᵢ^{f−t} (Θ = ϑ^{−1}), conditional on sitewise graded read facts (C3-ladder-multiplicativity, slot-grade β_t=(f−t)κ̄ᵢ, graded scalar covariance, zero-read R(0)=0); the three-reads display with canonical residual ψ^{(w)} = w^f ψ(y/w), preserving factor patterns. **(C4)** attained-origin bridge z^{t_Def} = z^ν·ε(β), raw = canonical iff z^ν = 1; support/degree translation by ν only under (H-JA-RES-CONJ). **(C5)** the HE6 normalized slot coefficient γ_k(A) (coefficient normalizers mandatory; bare residues rejected), the canonical-normalizer read with factor η^{−q(k)}, and the carry law q(a+b) = q(a)+q(b)+wrap(a,b). **(C6)** the explicit integral K₁-lift L_M(λ) = Σ λ̃_r x^{i+e₁r}π^{a−rh} on the live domain M > D′h (fixed residue section σ, σ(0)=0): integral, deg < D′, exact height M for λ≠0, residue ι_θ(λ), x-free ⟺ i(M)=0 ∧ λ∈𝐅_Q; clearance only under (H-GENHN-CLEAR). **(C7)** WELD-M-PKG interface fence: T1 organizes the five fields (M0–M4) around one cocycle; no cross-face coherence, no gauge uniqueness (fixed-coboundary gauges are a character torsor).

**(b) Lean node.** The `Gauge/` package (D4): C1/C2 → `Gauge/Cocycle.lean`; the corrected key, W(t), lift L_M, γ_k, residue section → `Gauge/Defs.lean`; C3 dictionary + C4 origin bridge + C5 reads → `Gauge/Transport.lean`. Blueprint §4: an algebraic identity over an abstract graded unit structure (ring + distinguished unit + floor arithmetic — omega/ring territory), **formalize the LEMMA, not the seven annexes**; each annex = `GaugeCocycle.instance_at (params)`. Migration step 7 (leansimp): replace the seven annex-local wrap compositions with the shared laws, replay each annex theorem as a short corollary.

**(c) Replaces (instance list = the §3 absorption map, A1–A7, r2-re-scoped to pinned gauge subclaims).** A1 GENHN (GENHN-LIFT verbatim on M>D′h; corrected T(b)′ coefficient L_M(c_tη^{W(t)})); A2 HETOW (wrap/carry preamble, telescope + corrected key — via imported (H-HETOW-LOCAL) with binary carry w₂∈{0,1}); A3 GENTOW1 (corrected coefficient pin, zero-lift branch; budgets/floors fenced); A4 GENTOW3 (gauge-annex corrected key; x-free rescope); A5 GENTOW4 (S0 naive key, 4.1(c)/S3 bridge with z^ν, BOX-3 no-η axis, S4 residue-one — η=1 ⟹ f₁=1 under the carrier); A6 GENTOW6 (corrected coefficient/full support with explicit x-support set; 6.3 scalar read materially adapted to γ_k(A)·η^{−q(k)}); A7 GENTOW2 (S5.1 letter formula, S5.2 B-law at discharged sites, factor-pattern invariance). Plus supporting rows: GENTOW5's w/ψ^{(w)} definitions, GRTJA's JA-EPS-CORR (C4), HE6-0″'s normalized coefficient, and the WELD-M-PKG interface (fence only, not a stronger theorem).

**(d) Arc grade.** **Attempt grade, arc live at r8.** The note folds r1–r7 (base letter z₁=η; n̂ᵢ(0)=1; H-JA-CONJ / H-JA-RES-CONJ / H-GENHN-CLEAR / H-HETOW-LOCAL supplier fences; graded scalar covariance + slot grade; zero-lift/zero-read branches; residue section for L_M). The comp11 T1R8 run (run of record committed) delivered 2 further repairs — the corrected-key coefficient-space bound (C3-lift-coefficient-space / C3-corrected-coefficient-bound) and the previously unsupported nonvanishing of the canonical ladder unit — not yet folded into the note file. Counter resets on every repair; zero clean passes credited; two consecutive clean hostile passes owed.

---

## T2 v2 — THEOREM HE7.A, the σ-LADDER MASTER (`T2_SIGMA_LADDER_MASTER_2026-08-12.md`)

**(a) Statement.** Fix one complete DVR O with fraction field K₀, uniformizer π, finite residue field k₀=𝐅_Q; valued points live in a fixed K̄₀, residual labels in k̄ — never identified. A **σ-ladder carrier** over O consists of: a finite residue-label extension K/k₀ with compatible embeddings ι_ξ; a **monic** key Φ ∈ O[x] of degree D>0 with **no irreducibility hypothesis** (NO-IRR — essential, since the level-2 key is the HE6 test polynomial); inherited invariants e_𝒞, f_𝒞 > 0 with the explicit hypothesis D = e_𝒞·f_𝒞 (DEG-EF); a value d, threshold T, point class Pt; exact slots h(A), dig(A) with (SLOT-V)/(SLOT-R) (level 1: dig = γ_k(A), print seam res(A/ϖ^k) = ι(γ_k(A))·η^{−q(k)}); normalizer-**defined** cocycle τ(a,b) = res(n(a)n(b)/n(a+b)) — at HE7 level two the genuine twist β^c, never trivialized; legal lifts only at full heights, with the visible domain obligation H_lift ⊆ Full (OCC — no all-height lift). A **key-free σ-block** is monic separable F = Φ^μ + Σ_{j<μ} A_jΦ^j (deg A_j < D) with gcd_{K₀[x]}(F,Φ)=1 (KEY-FREE), finite window T < d(Φ(ρ)) < ∞ on all roots, WindowSafe/CapSafe, the residual-degree bridge (RES-DEG: deg R_λ = L_λ/e′), the Newton accounting identity (ACCOUNT), frame/origin bridges (FRAME, ORIGIN: raw = Y^ν·a·norm(bY)), and root-preserving, invariant-transporting, well-founded continuation with mass bound μ_child ≤ μ/(e′deg r′) ≤ μ/2 (MASS). **Conclusions:** all hull slopes > T with ΣL_λ = μ; for separable R_λ, each irreducible factor r′ determines one Galois orbit S_{λ,r′} of size De′·deg r′ = the root set of one monic irreducible factor of F, with (e,f) = (e_𝒞e′, f_𝒞·deg r′); repeated r′ branches on e′·deg r′ = 1 (certified linear recentering via a legal lift) versus ≥ 2 (child carrier over the same O); mixed residuals are processed per Galois-stable label block (r1: the S1.7A label-block decomposition theorem); the recursion terminates with pairwise-disjoint exhaustive terminal factors multiplying to F and invariants composed multiplicatively. Companion **T2.KEY-BOUNDARY**: a non-key-free input decomposes by monicGCD(F,Φ) into certified boundary factors P_i plus key-free residual blocks — replacing the invalid one-factor "Φ-peel". Five span-pinned instances: HE3.A, HE6, HE7+HE6R1 (level 2), HETOW (full inner sides), GENTOW4 (partial sides, per block). Consumption grade law: grade(I) = min(g_master, g_carrier, g_frame, g_local).

**(b) Lean node.** The **Ladder node spine** — this theorem plus the S-5 carrier signature IS the design of `Stage2/Ladder/{Base, FractionalKeys, StrictDescent, Exhaustiveness}.lean` (leansimp: HE3/HE6/HE7/HE6R1/HETOW → `Ladder/*`), with the HETOW/GENTOW4 instance frames feeding `Towers/*`. Blueprint §4: "the carrier abstraction IS the Lean design: a structure `LadderCarrier` + one theorem, instances for base/composed carriers; write the Lean signature AT COMPOSE TIME" — done by the S-5 probe (final section below). S-5's red line: an implementation via "complete DVR stage quotient" flips the verdict to NO-GO; the first consumption check is building the HE7 level-2 carrier with `keyIrreducible` absent from all generated obligations.

**(c) Replaces.** The five per-note σ-decision arguments as instance records: HE3.A (base-stage resolvent read, (e,f)=(e₁e_s,f₁f_s)), HE6 (enlarged fractional-height tests Ψ_{κ,r}), HE7+HE6R1 (level two: key Ψ_{λ,r}, D″=D′ℓd_r, n₂-normalizers, β^c cocycle, FULL2 lift domain), HETOW (composed key Φ₂, HETOW-4 frame bridge, transported letter β = η^{−Q(u₂)}η₂), GENTOW4 (bouquet blocks f_S, c_g-translated projected hull, μ₂* from the hull). Blueprint: "the difference between formalizing 4 bridge layers and 1 theorem." Excluded: count-side mixed-multiplicity ties, partial-side budgets, density laws.

**(d) Arc grade.** **Attempt grade 0/2 (v2), arc live at r1.** The v2 re-composition closed the P1–P3 defects of the withdrawn v1 (reducible-key peel → KEY-FREE + boundary theorem; marker-delimited pins; no formal-gate claim). The comp11 T2R1v2 run (run of record committed) delivered 3 repairs (including the S1.7A mixed-residual label-block theorem), not yet folded. Every composed instance stays at min(grade) = 0/2 until the master's own arc closes; suppliers HE6/HE7/HE6R1/HETOW/GENTOW4 are each accepted 2/2 at their pinned HEADs.

---

## T3 — LEMMA COCYCLE-TELESCOPE (`T3_COCYCLE_TELESCOPE_2026-08-12.md`)

**(a) Statement.** Two ports over the imported T1 interface (normalized cocycle τ_N, telescope ϑ_N with ϑ_N(0)=ϑ_N(1)=1, inverse orientation Θ_N = ϑ_N^{−1}, digit dictionary — imported, not re-proved). **Boundary-read port:** given source-local hypotheses (BR1)–(BR5) — peel ct R_{β_s}(N(q)^s) = wᵢ^s; expansion additivity; positive-degree elimination; exact constant digit ct R(Q₀) = U_i(β_s)·digit(Q₀); evaluation digit digit(Q₀) = ϑ_N(s;q) — conclude the B-law endpoint **U_i(β_s) = Θ_N(s;q)·wᵢ^s** (T3-BR), with the endpoint derived, never supplied (anti-circularity: T1's conditional B-law is not cited as premise). **Descending bracket telescope** (T3-BKT): ∏_{r<t} τ_N(H_{r+1},q) = N(H_t)N(q)^t/N(H₀) for H_t = H₀−tq. **Two-section comparison port:** for sections N, N̂ with pointwise ratio χ(k) = res(N̂(k)/N(k)), the coboundary law χ(a)χ(b)/χ(a+b) = res(τ_N̂·τ_N^{−1}) (T3-COB — χ need NOT be a character); assembled coefficients satisfy ρ_t = ρ̂_t·χ(H₀)δ^{−t} and R(Z) = χ(H₀)·R̂(Z/δ), δ = χ(q) (T3-CMP); monic factor routing r(Z) = δ^m·r̂(Z/δ), roots ŝ ↦ δŝ, preserving separability and the multiset of irreducible-factor degrees/multiplicities (T3-ROUTE). Absorptions: GENTOW2-B″ (unconditional at i=2), HETOW-4 clauses (b)-shape/(c)/(d) (floor arithmetic τ_H(k)=η^{−Q(m(k))} stays source-side), [GENTOW5-W(i)] at i≥3 (downstream consumers retain the cumulative hypothesis 𝒲_{≤n} exactly per G5-COND; corrected twist index ψ_j^{(ω_{j−1})}). **GENTOW-6.4 is a displayed NON-instance** — additive, filtration-triangular, no multiplicative cocycle.

**(b) Lean node.** `Gauge/Cocycle.lean` (blueprint §4: "Finset.prod telescope over a height ladder — mechanical Lean once stated; no cite"), with the section-comparison/routing block exported through `Gauge/Transport.lean` for consumption by `Towers/TwistedTransport.lean`.

**(c) Replaces.** GENTOW2-B″'s local four-step proof (ABS-G2, closed display including the residual rescaling w^{f₃}P(y/w)); HETOW-4's coefficient telescope, polynomial rescaling, and factor/root routing (ABS-HE4 + HE4-COB); the level-general [GENTOW5-W(i)] boundary-read shape (ABS-G5W). Explicitly NOT GENTOW-6.4, which keeps its own certified additive proof.

**(d) Arc grade.** **ACCEPTED 2/2 (2026-08-12)** — the only accepted T-unit. Arc: composed → revised vs certified seam → T3P1 (0C+1G, FRAME-C comparison-port arithmetic) → r1 → T3P2 CLEAN → T3P3 CLEAN. Post-acceptance consumption checks (S-2 protocol, runs/comp5): GENTOW2-B″ PASS, HETOW-4 PASS, GENTOW-6.4 confirmed NOT ABSORBED. **Scope of record: two absorptions + one documented non-instance** (the blueprint's third target honestly narrowed at revision); the ABS-G5W port stands inside the accepted lemma with its 𝒲_{≤n} conditionality.

---

## T4 — THE CERTIFICATE WITNESS (`T4_CERTIFICATE_WITNESS_2026-08-12.md`)

**(a) Statement.** In the full-side tower setting shared by GENTOW-3 and GENTOW-6 (D′=e₁f₁, E₂=e₂f₂u₂, δ=u₂−e₂D′h ≥ 1, thresholds Θ_j = (μ₂−j)E₂+δ, corrected-gauge key coefficients ĉ_t = lift(c_tη^{W(t)})): with C_j and ShC_j the two **linear** division operators on the dividend module 𝒟_{≤μ₂} (r1/r2: honest composed development vs stage-shadow K₂(x,Y)-division over Ô[x]/(Φ′)), Δ_j = ShC_j − C_j, and gr_m the canonical **assembled** digit at dv₂-height m (all branches, carries, recarries summed before the class is taken; unambiguous by GENHN-2′), define the **certificate witness** ω_j := gr_{Θ_j}(Δ_j(Φ₂^{μ₂})); coordinate j is *touched* iff ω_j ≠ 0. **LEMMA T4.2**, under the member-general discrepancy floor (FLOOR: gr_m(Δ_j(f)) = 0 for every member f and m < Θ_j): (a) touched ⟺ ν_j(f_key) = Θ_j (first-discrepancy height, min ∅ = +∞); (b) perturbation stability — for g ∈ 𝒟_{<μ₂} with gr_{Θ_j}(Δ_j(g)) = 0 (in particular in-budget g via GENTOW-3 S8.1's Θ_j+1 margin), gr_{Θ_j}(Δ_j(f_key+g)) = ω_j; (c) **fully-exposed** assembled-slot criterion (r3: exposure must exclude every assembled-slot input — other branch terms and incoming carries/recarries, not merely single-extraction uniqueness) ⟹ ω_j ≠ 0; (d) no-source criterion ⟹ ω_j = 0 — **currently gapped** (see (d) below). Instances: `GT3-THRESHOLD` (GENTOW-3(iv)'s "touched coordinate" = Def T4.1; attainment = T4.2(a); S8.1 persistence = T4.2(b)) and `GT6-CERT-TOP` (GENTOW-6.3(b) at f₁=1, μ₂=2; 6.3′ corrected-lift f₁-general; the μ₂≥3 binomial computation downgraded to a *candidate* pending (EXPOSE-6.5)). Byte-literal fail-closed pin convention on both source stacks.

**(b) Lean node.** `Towers/*` — the Θ_j threshold/discrepancy combinatorics belongs with `Stage2/Towers/Windows.lean`/`Cap.lean` (leansimp: GENTOW1–6 → `Towers/*`). Blueprint §4: "Digit/threshold combinatorics over ℕ; the touched-coordinate predicate is decidable — decide/omega friendly; formalizing this early fences the four count-grade sub-boxes as explicit hypotheses rather than prose residues."

**(c) Replaces.** GENTOW-3's local definition of "touched coordinate(s)" and its floor-attainment inference (→ `GT3-THRESHOLD`); GENTOW-6.3(b)'s implication from the CERT-TOP slot to threshold attainment (→ `GT6-CERT-TOP`); GENTOW-6.3′'s exposed-slot inference within its corrected-lift scope. The sources keep their witness-computing algebra (top-slot exposure calculation, corrected-lift support, higher-μ₂ binomial); the boxes GENTOW6-BOX-1/2/3/4 and GENTOW3-BOX-1 become named residue homes / explicit hypotheses.

**(d) Arc grade.** **Attempt 0/2, r1–r3 folded, pass 4 NOT CLEAN — repairs owed (r4).** Rounds r1/r2 were blocked on pin validation by the bubblewrap-less executor (fail-closed UNRESOLVED records); comp11's T4P4 pasted the sources to resolve pins and returned **1 CRITICAL + 2 GAP + 2 minor**: (C) GT6 pin 4's BEGIN/END are reversed in the actual GENTOW6 source, so the BOX-4 span — and hence `GT6-CERT-TOP` — fails closed; (G) T4.2(d)'s no-source implication is unjustified after r3 widened ω_j's assembly to all provenances; (G) the GT3 pin stacks do not cover the FR-GL and FR5X configurations the instance cites.

---

## T5 — THE w-FRAME NOTE (`T5_WFRAME_2026-08-12.md`)

**(a) Statement.** At tower level i with T1 data (frame of record: T1 with r1–r3), define once: the **cross-frame unit** wᵢ := R_{i+1,κ̄ᵢ}(n̂ᵢ(u_{i+1})) ∈ Kᵢ^×, κ̄ᵢ = u_{i+1}/e(μᵢ) (WF-w), and the **twist** P^{(wᵢ)}(y) = wᵢ^f·P(y/wᵢ), so ψ_{i+1}^{(wᵢ)}(y) = y^f − Σ c_t wᵢ^{f−t} y^t (WF-psi). "Cross-frame" = converts the multiplicative residual frame to the canonical one; NOT a uniformizer avatar. **LEMMA W-FRAME-LAW** (r1 scoping): at the base rung i=2, **unconditionally** (supplier GENTOW2-B″), u₂(β_t) = Θ₂(t)w₂^{f₃−t}; for every permitted 3 ≤ i < r, only under the explicit cumulative hypothesis 𝒲_{≤i} = ⋀_{3≤q≤i}[GENTOW5-W(q)]: uᵢ(β_t) = Θᵢ(t)wᵢ^{s_t}. **Realized-residual corollary:** R_{ν₂}(Φ₃) = ψ₃^{(w₂)} unconditionally; 𝒲_{≤i} ⟹ R_{νᵢ}(Φ_{i+1}) = ψ_{i+1}^{(wᵢ)} at i≥3. No i=1 version (the S11.3 letter-power tie is OPEN-2). Corrected twist index (WF-index): R_{j−1}(Φ_{n+1}) = (ψ_j^{(ω_{j−1})})^{l_{j+1}···l_{n+1}}, ω₁ = S11.3's unit, ω_q = w_q for q ≥ 2; the top term uses w_n, never w_{n+1}. Instance records I1–I5: T1 C3 frame; GENTOW2-B″; GENTOW2-PE6 (six primes with w₂ ≠ 1 — refutes universal w=1; avatars z₁, z₁², z₂², z₂ measured only); GENTOW5-PE3 (seventh prime, ψ₃^{(w₂)}(Y)=0); the conditional [GENTOW5-W(i)] supplier with the notation bridge k̄ᵢ = κ̄ᵢ (r2). LW3 kills the theta-free law and shows avatar ≠ intrinsic w (w₃=1 vs w_av=2). Open: a structural/closed-form criterion for wᵢ, incl. wᵢ=1 (OPEN-1).

**(b) Lean node.** Definition → `Gauge/Defs.lean`; the law + realized residual → `Towers/TwistedTransport.lean` (leansimp unit 15, "windows and w-twisted transport"). Blueprint §4: "Definitional; one structure + the measured record as instance-keyed facts. The w=1 open question becomes a named hypothesis — the honest-`sorry` analogue at statement level." 𝒲_{≤i} likewise enters as an explicit hypothesis, never discharged silently.

**(c) Replaces.** The per-note w/ψ^{(w)} riders across GENTOW2/GENTOW5 (one canonical definition instead of per-note redefinitions); the PE6/PE3/LW3 measured records (as instance-keyed facts); the [GENTOW5-W(i)] companion's statement home as the conditional i≥3 supplier; the S12.1 conditionality chain (WF-chain) as the single dependency display.

**(d) Arc grade.** **Attempt 0/2, r1–r3 folded, pass 4 NOT CLEAN — 0C + 2G + 0m; repairs owed.** comp11's T5P4 (sources pasted): (G1) T5's *description of the companion* is not source-faithful — the WI note claims "[GENTOW5-W(i)] is PROVED, unconditionally at i≥3" while treating clause (b)/P-membership as unconditional, which S12.1 expressly withdraws (T5's own conditional formulation is safe; the characterization is not); (G2) the acceptance-evidence census (T1 C3/A7, GENTOW2-B″, PE6, PE3, repo hashes, WI 60/60) remains independently unverified — the bwrap executor blocker persists, so no hostile-pass credit under r3's own gate.

---

## Campaign lemmas (the four SOL-certification-campaign additions; all live as dated proof completions inside accepted, byte-frozen notes)

### LEMMA W12-HT — all-degree order-1 history transfer (`W12_PROOF_2026-08-08.md` tail)

**(a)** For a window-visible decided order-1 shape (window N, residue size Q_i; order-≥2 keys excluded, staying under [W12-H]): at each node v of the refinement tree, after fixing the actual normalized residual polynomial on every side, there is a finite-window bijection ℰ_v(𝐑) ≃ 𝒰_v(𝐑) × ∏_{u child} C_{m_u}(s_u) (HT-fiber), compatible with recentering and coprime branch fracture (GENIND-1 fracture permanence consumed), with #𝒰_v(𝐑) = Q_i^{B_v(N)−Σ_u D_u(N)} independent of the residual letters — built from block-unitriangular translations and coprime multiplication isomorphisms, valid in every characteristic and at every finite window. Consequently the node census obeys the recursion (HT-rec) with side censuses S_λ(Q_i) and the **side-local** orbit factor κ_v = ∏_{S,a} r_{v,S,a}!/∏_H r_{v,S,a,H}! (side tag mandatory); termination via convexity (child depth s_u ≥ s_v+1) at separable Ore leaves yields the branch law (HT-branch) and the global law #T(N) = κ₀(T)·C₀(q)·∏_{m_i=1} q^{d_i(N−1)}·∏_{m_i≥2} ℋ_i(T,N) (HT-global). This restores W-12.A's full order-1 coverage and closes the dated obstruction (B_root = D_child = 2N−5 instance recomputed exactly).

**(b)** `Stage2/Reduction/W12.lean` (leansimp: W12 → `Reduction/*`; units 2–4 W-12.A/C/D). The note's own Phase-B rider: a history-resolved order-1 menu entry must implement (HT-rec) with complete child-history multisets, side tags, D_v, κ_v, κ₀.

**(c)** Replaces the per-degree order-1 cell laws as instances: W-12.A's display (= depth-zero specialization of HT-global), W12-L0 (multiplicity-2 telescope, (q−1)^t factor, six leaf laws), W12-L1 (quadratic block + unit-scaled letters), HM3.A's cubic α/β species.

**(d)** **Certified / obligation DISCHARGED** (ledger row 12): machine certificate GREEN (`verification/openmath/w12_history_law_check.py` — 1,196 per-key comparisons, 0 mismatches, n∈{3,4}, q∈{2,3}, N≤6; teeth fired 302/22/370/1,136; 300 translation-rank + 322 coprime-rank tests green); composed by the P1 certification run, orchestrator-verified, transcribed unaltered into the accepted W12 note.

### LEMMA GENHN-CAP-GEN — general finite-window boundary projection (`GENHN_PROOF_2026-08-08.md`, R4 F-1)

**(a)** For any ordinary stage genre (e₁,f₁,μ) and truncated coefficient state, with V_m ⊆ K the 𝐅_Q-span of the η^t basis components whose digits sit below their coordinate windows and comp(m) = dim V_m: the finite-window stage reader (1) returns UND whenever an unread coefficient can undercut the provisional minimum; (2) otherwise the value is exact (GENHN-2), and a decided leaf is returned exactly when the dictionary output is constant on the full completion set Comp(z), else UND; (3) refines recursively only on complete visible K-pins. Output is a function of the truncated data; no unread digit is consulted; a nonzero visible boundary pin has census Q^{comp(m)}−1 (= ERRATUM E2). Rider: "the ragged band is never consulted" everywhere means the *unread component cells*, not the band heights; GENHN-3(a)'s "iff < e₁N" becomes the interior criterion plus this exact boundary criterion.

**(b)** `Stage2/StageLaws/OrderOne.lean` (leansimp: GENHN → `StageLaws/*`; count transport into `FiniteGenres.lean`).

**(c)** Replaces the genre-by-genre boundary handling: GENHN.A(iii)/S5/OB-a ragged-band clauses (rider re-readings), GENHN-3(a)/(b)'s boundary criterion, the [r2] (e₁,μ)=(1,2) rule (its specialization), extending CS-1/CS-2 to ordinary f₁≥2, μ≥3, and mixed genres without a new box.

**(d)** **Proved** — dated correction 2026-08-12 folded into the accepted GENHN note, with in-note proof; consumed as a pillar by GENHN-COUNT-RERUN.

### LEMMA GENHN-LIFT — the exact-height K-lift (`GENHN_PROOF_2026-08-08.md`, R4 F-3)

**(a)** For M > D′h = e₁f₁h, with i = i(M) ∈ [0,e₁) determined by ih ≡ M (mod e₁), a = (M−ih)/e₁, and λ = Σ_{s<f₁} λ_sη^s ∈ K written in the fixed basis: L_M(λ) := Σ_s λ̃_s·x^{i+e₁s}π^{a−sh} lies in Ô[x], has degree < D′, every nonzero summand at exact dv-height M, and res(L_M(λ)(θ)/n(M)(θ)) = λ (GENHN-2 independence prevents cancellation). Application: replacing the gauge-naive coefficient in T(b)′ by L_{ru₂}(c_tη^{W(t)})Φ′^{e₂t} makes the multiplicative coefficient exactly c_t, hence the inner residual exactly ψ₂.

**(b)** `Gauge/Defs.lean` — this is byte-for-byte T1's (C6) on the live domain (T1 absorption row A1: "Verbatim on M > D′h"); StageLaws/Towers consume it through the Gauge export.

**(c)** Replaces the in-note lift usage of GENHN T(b)′(i) and every corrected-coefficient site downstream; via T1 it is the single lift underlying A1/A4/A6 and T4's ĉ_t.

**(d)** **Proved** — dated proof completion 2026-08-12 in the accepted GENHN note; already absorbed verbatim into T1 (C6) with the r7 residue-section refinement.

### LEMMA GENHN-COUNT-RERUN — μ=2, corrected node (`GENHN_PROOF_2026-08-08.md` tail)

**(a)** For genre G = (Q; e₁,f₁,2; h, entry) with gcd(e₁,h)=1, D′=e₁f₁, K = 𝐅_{Q^{f₁}}, corrected node B = D′h, and any component-complete stage cap M: the GENHN-2 slot map is a bijection 𝒩_B(M) = {(A₁,A₀): dv(A₁)>B, dv(A₀)>2B, heights ≤ M} ≅ K^{{B+1..M}} × K^{{2B+1..M}} (CR-1); under it (1) the finite-stage reader is exactly the finite-window (2,K)-cluster reader at node B; (2) the RAM/2SIDED/SPLTAIL/SPLITEQ/INERT/α-refined per-key cardinalities are the standard (2,K) cell-law counts; (3) each fixed α-letter slice at height κ recenters bijectively onto 𝒩_κ(M) (uses GENHN-LIFT at κ > B, GENHN-4 triangularity, GENHN-3 cap respect), giving #α-states = (|K|−1)|𝒩_κ(M)| (CR-2); (4) boundary pins carry census Q^{comp(m)}−1 governed by GENHN-CAP-GEN (CR-3). Hence every ordinary μ=2 count display survives the floor correction S = e₁h ⇝ B = D′h, the literal S-node law surviving uniformly iff f₁ = 1 (volume ratio q_K^{3(B−S)}, B−S = e₁h(f₁−1)). Settles GENHN-ERR-1, resolves the sealed α-mismatch (totals attached to the wrong child key), restores HE6R1's completion clause with no wording change.

**(b)** `Stage2/StageLaws/OrderOne.lean` / `FiniteGenres.lean` (μ=2 stage counting laws on the corrected node).

**(c)** Replaces GENHN's μ=2 count displays at the old S-node (GENHN.A(v), S6.2 re-read at B) and the sealed alpha-child tables; supplies the count-side transport HE6R1's completion statement rides on.

**(d)** **Certified / obligation DISCHARGED** (ledger row 15): machine certificate `verification/openmath/genhn_f2_count_check.py` — measured = predicted on every key at (1,2,2) and the first mixed-genre contact (2,2,2); sealed S-node child displays refuted exactly as predicted (0/1024 vs 768/256; 0/16384 vs 12288/4096); P2 certification run, orchestrator-verified, transcribed into the accepted GENHN note.

### (RM-1-TRANSPORT) — LIFTCORNER annex AC-5 (`LIFTCORNER_2026-08-08.md`)

**(a)** Let Φ₁′, Φ₁″ be lawful monic level-1 keys with the same residue package at g₀=1; d = e₀d₀, W = w₁Φ₁′ = w₁Φ₁″ = e₀h₀, Δ = Φ₁′−Φ₁″. Then: **(T1)** ν(Δ) ≥ W+1 (strictness from the residue pin at k=0 plus gcd(e₀,h₀)=1 forcing the ceiling amin(k) to add ≥1 for 0<k<e₀); **(T2)** monic division H = A + BK by any lawful key satisfies ν(A) ≥ ν(H), ν(B) ≥ ν(H)−W (via ITERLAWN's m=1 DIGIT-SPLIT + DEV-1 reduction, shown terminating on the lexicographic (m, deg a) measure including the flat e₀=1 case); and for every (RM-1) input f (deg f < d, λ = w₁(f), v = R_{1,λ}(f), μ = λ+γ₂), with the shared correction digit Ĉ₁′ = Ĉ₁″, the transported remainder/quotient R′ = R″−A, Q′ = Q″−B (where Q″Δ = A + BΦ₁′, ν(Q″Δ) ≥ μ+1 by T1+T4) satisfy all four consumed interface clauses: deg R′, deg Q′ < d; w₁(R′) ≥ μ; w₁(Q′) ≥ μ−W; prescribed read R_{1,μ}(R′) = z₁^{ε′}vτ₁ (READ-ADD's strict-above kill). Hence ITER-PKG-2 is constructed **for every lawful same-residue Φ₁′** — full proof-data equality of (R,Q) is explicitly false and unnecessary; only the degree/weight/read interface is invariant. Discharges the (Φ₁)-OPACITY residual: LIFTCORNER PROP's rung-≥2 suspension is lifted, S5's every-n rider on the Φ₁ axis becomes unconditional, FC-2's rider rewrite is reinstated; ITERLAWN's DCX/(RM-m, m≥2) conditional ledger is unchanged.

**(b)** `Gauge/Transport.lean` (leansimp: LIFTCORNER → "`Gauge/*` and tower transport support") — it is a key-change transport law for the division interface, exactly the Transport module's charge.

**(c)** Replaces the (Φ₁-OPACITY) conditional fences threaded through LIFTCORNER PROP / S5 / FC-2 and the would-be per-key re-derivations of the rung-2 package; completes the AC-1 (containment) → AC-4 (narrowing) → AC-5 (discharge) program.

**(d)** **PROVED** — 2026-08-12 certifier annex, orchestrator verification recorded (T1 strictness, the (T4) crux ν(Q″Δ) ≥ μ+1, the R′/Q′ bookkeeping against (T2), the rung-≥3 sweep against AC-4); ledger row 19 discharged.

---

## Final section — the S-5 Lean signature sketch, verbatim

From `runs/comp1/S5_output.log`, section "## 3. Lean signature sketch" (the T2 design probe; S-6 gate verdict on it: **GO**, with the red line that a "complete DVR stage quotient" implementation flips to NO-GO, and the first consumption check being that `keyIrreducible` must appear in no generated obligation):

```lean
universe uO uK uκ uΩ

open Polynomial

/-- The complete DVR remains the original coefficient ring. -/
class CompleteDVRData
    (O : Type uO) (K₀ : Type uK) (k₀ : Type uκ) : Type _ where
  valuation       : K₀ → WithTop ℤ
  uniformizer     : O
  residue         : O →+* k₀
  complete        : Prop
  isComplete      : complete
  -- fraction-field, DVR, and residue-field laws omitted from the sketch

structure SigmaLadderCarrier
    (O : Type uO) (K₀ : Type uK)
    (k₀ Kres : Type uκ) (Ω : Type uΩ)
    [CommRing O] [Field K₀] [Field k₀] [Field Kres] where
  dvr             : CompleteDVRData O K₀ k₀

  key             : Polynomial O
  keyMonic        : key.Monic
  keyDegree       : ℕ
  keyDegree_pos   : 0 < keyDegree
  key_degree_eq   : key.natDegree = keyDegree
  -- Deliberately no `Irreducible key`.

  threshold       : ℤ
  point           : Ω → Prop
  residueEmbed    : ∀ ξ, point ξ → Kres →+* Ω

  normalizer      : ℤ → RationalFunction K₀
  normalizer_zero : normalizer 0 = 1
  normalizerValue : ∀ k, /* value (normalizer k) = k */

  slotValue       : Polynomial O → ℤ
  slotDigit       : Polynomial O → Kres
  slotExact       :
    ∀ A ξ (hA : A.natDegree < keyDegree) (hξ : point ξ),
      /* value (A.eval ξ) = slotValue A */
  slotResidue     :
    ∀ A ξ (hA : A.natDegree < keyDegree) (hξ : point ξ),
      /* res (A ξ / normalizer (slotValue A) ξ)
           = residueEmbed ξ hξ (slotDigit A) */

  fullHeight      : ℤ → Prop
  lift            : ∀ k, fullHeight k → Kres → Polynomial O
  lift_degree     :
    ∀ k hk c, (lift k hk c).natDegree < keyDegree
  lift_value      :
    ∀ k hk c, c ≠ 0 → slotValue (lift k hk c) = k
  lift_digit      :
    ∀ k hk c, slotDigit (lift k hk c) = c
  lift_zero       :
    ∀ k hk, lift k hk 0 = 0

  cocycle         : ℤ → ℤ → Kresˣ
  cocycle_normal  : ∀ a, cocycle 0 a = 1 ∧ cocycle a 0 = 1
  cocycle_law     :
    ∀ a b c,
      cocycle a b * cocycle (a + b) c =
      cocycle b c * cocycle a (b + c)

structure SigmaBlock
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω) where
  poly            : Polynomial O
  monic           : poly.Monic
  separable       : Discriminant poly ≠ 0

  multiplicity    : ℕ
  multiplicity_pos : 0 < multiplicity
  degree_eq       :
    poly.natDegree = multiplicity * C.keyDegree

  coeff           : Fin multiplicity → Polynomial O
  development     :
    poly =
      C.key ^ multiplicity +
        ∑ j, coeff j * C.key ^ (j : ℕ)
  coeff_degree    :
    ∀ j, (coeff j).natDegree < C.keyDegree

  proper          : ¬ C.key ∣ poly
  rootsArePoints  : ∀ ρ, /* ρ root of poly */ → C.point ρ
  aboveThreshold  :
    ∀ ρ, /* ρ root of poly */ →
      C.threshold < /* value (C.key.eval ρ) */

  occupiedHeights : Finset ℤ
  liftHeights     : Finset ℤ
  occupied_spec   : Prop
  lift_domain     :
    ∀ k, k ∈ liftHeights → C.fullHeight k

  windowSafe      : Prop
  capSafe         : Prop
  window_ok       : windowSafe
  cap_ok          : capSafe

  /-- Includes `Γ = c * ϑ`, `Θ = ϑ⁻¹`, the `w`-scaling,
      and `raw = Y^ν * a * normalized (bY)`. -/
  frameBridge     : Prop
  frameBridge_ok  : frameBridge

  testFamily      : BaseChangeFreeTestFamily C poly
  stepData        : SigmaStepData C poly
  step_wf         : WellFounded stepData.next

structure HE7AResult
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω)
    (B : SigmaBlock C) : Prop where
  slopes_gt_threshold : Prop
  side_lengths_sum    : Prop

  separable_factor_classes :
    Prop
    -- |S_{λ,r}| = D * denominator(λ) * degree(r),
    -- one irreducible O-factor, with multiplied e and f.

  repeated_linear_refines :
    Prop
    -- multiplicity ≥ 2 and denominator * degree = 1.

  repeated_non_linear_jumps :
    Prop
    -- multiplicity ≥ 2 and denominator * degree ≥ 2.

  recursion_terminates :
    Prop

theorem HE7_A_master
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω)
    (B : SigmaBlock C) :
    HE7AResult C B
```

S-5's accompanying design points (same log, immediately after the block): "The important design point is that `proper`, `lift_domain`, `windowSafe`, `capSafe`, `frameBridge`, the test family, and termination are visible hypotheses. They must not be hidden inside a broad assertion such as '`B` is a valid tower block.'" And the peel stays a separate generic lemma:

```lean
theorem sigma_peel
    (hdiv : C.key ∣ B.poly) :
    PeelResult C B
```

"After peeling, `HE7_A_master` applies to the proper remainder." — Note this sketch predates T2 v2's S2.1 correction: v2 replaced the one-factor peel by the gcd/orbit **T2.KEY-BOUNDARY** decomposition (KEY-FREE via gcd_{K₀[x]}(F,Φ)=1, not mere non-divisibility), so the stage-2 encoding must upgrade `proper : ¬ C.key ∣ poly` and `sigma_peel` accordingly; v2's S7 stage-2 gate list is the binding contract.

---

**Grade summary (one line each, as of comp11 close 2026-08-12):** T1 attempt/arc-live at r8 (2 repairs delivered, unfolded) · T2 v2 attempt 0/2, r1 (3 repairs delivered, unfolded) · **T3 ACCEPTED 2/2** (2 absorptions of record + GENTOW-6.4 non-instance) · T4 attempt 0/2, P4 NOT CLEAN (1C: GT6 pin 4 reversed; +2G+2m) · T5 attempt 0/2, P4 not clean (0C+2G: supplier-scope characterization; evidence census) · W12-HT, GENHN-CAP-GEN, GENHN-LIFT, GENHN-COUNT-RERUN, RM-1-TRANSPORT all proved/certified inside their accepted host notes.
