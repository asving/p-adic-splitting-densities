# HDISCHARGE_H1 — discharge blueprint for (H1): the graded-dictionary open family at OM orders ≥ 2

**REVISION 2 (2026-08-05):** the pass-1 Codex adversarial review (BLUEPRINT-UNSOUND,
9 crit/6 gap — `lean/notes/openmath/H1_bp_review.md`) is FOLDED IN PLACE; every
repair tagged `[REV 2, finding N]` at its site; disposition table at §7. Headline
repairs: the §0 tower ladder de-circularized via the (GR-B-STR)/(GR-B-KEY) split;
KEY1-SITE gains the run-data hypothesis; `kp_step`/`GrBKeyLaws` restated (re-probed);
the sorry/DevBound discipline corrected. Fresh re-review owed at wave 0.

H1 DISCHARGE LEAD deliverable (Asvin directive 2026-08-05, ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` tail: the hypothesis-discharge swarm —
one lead per (ROOT-C) hypothesis, blueprint → Codex adversarial review → parallelizable
Lean units). Authority for WHAT (H1) is: `docs/ROOT_ASSEMBLY_2026-08-02.md` (ROOT-C)
block + the §3.1 (H1) row (REVISION 12 text). Sources of mathematical truth per member:
the VERIFIED leaf `lean/notes/openmath/GD23_phaseB_verifybrief_rev4.md` (leaf #4; (GR-B)
displayed at its §7.2, (KP)/(KPirr) at §2, KEY-g/RES-1/DEVID/BRIDGE proved),
`O2a_phaseB_verifybrief_rev4.md` (OL-2a-1 = its OL-1; OL-2a-6 = its OL-6, exact
statements quoted below), `O1thr_phaseB_verifybrief_rev4.md` ((V1)/(V2) key-compliance
block, WGEO's consumed form), and `LITUNIT_2026-08-01.md` §5/§7/§8 (the verbatim FGMN
pins). Lean reuse surface: `LeanUrat/Moves/Defs.lean` (`Stage`, `HasAnchorK`,
`OrdPsiPoly`), `LeanUrat/MovesGr/Defs.lean` (`SideVal`, `GradedRingStr`,
`GenuineStageModel`) + MovesGr L0–L4 units, `LeanUrat/MovesC/Defs.lean` (`Node`,
`History`, `HistoryCoherent`), `LeanUrat/HC2/Defs.lean` (`IsNodeLift`, `SideReads`,
`ReadsOf`, `KeysLawful`, `TransitionCoreL`, `StageTransHyp`).

## 0. Charter, the four members, and the ground rules

**(H1), verbatim shape (ROOT §3.1):** the graded-dictionary open family at OM orders
≥ 2, FOUR members — order ≤ 1 PROVED over an arbitrary complete DVR for all four faces;
the ≥ 2 layer open:

* **(a) (GR-B)** — the anchored-march residue-structure package at state order i+1 ≥ 2
  (GD-2/GD-3's one open input), modeled on printed FGMN Thm 4.2 (both pairings),
  EXCLUDING the properness-proviso leg (e·g = 1 side condition), whose SOLE home is the
  §3.3 (KP)/(KPirr) [T] row pinned at FGMN Lemma 5.3. Enters ROOT Steps 10, 14, 16,
  18 (K3), 18b ((S1)).
* **(b) GD-1 beyond order 1** = O-2a's OL-2a-1 (lift admissibility + normalization,
  cumulative joint induction): the canonical key lifts form one GMN-admissible
  representative family at every order. Enters Steps 10–12.
* **(c) GD-6 conformance instances at orders ≥ 2** = OL-2a-6's consumed face (run
  decomposition + chain binding), held on proof-by-construction ROUTES on record, which
  are not proofs. Enters Step 10's conditionality line.
* **(d) the order-≥ 2 KEY1 block** — KEY1's conclusion block (d1)–(d3) asserted at EVERY
  realized site of Step 6's machine at OM READ ORDER ≥ 2, key degree IRRELEVANT
  (e·g = 1 refinement chains included; the VC8-1 requantification). = O-1thr's
  (V1)/(V2) key-compliance block beyond its proved order-≤ 1 slice — the block Lemma
  WGEO consumes. Enters Step 6, propagating with Step 6's deliveries.

**Ground rules (binding).** (i) Hypothesis content stays hypothesis until PROVED and
passed — no fiat discharge anywhere in this blueprint; every Lean hypothesis row is a
named `structure`/`def`, NEVER an axiom. (ii) This is a BLUEPRINT-ONLY unit: no
`Scaffold/HDischarge/H1/*.lean` files land with it (prover fan-outs run separately);
every Lean statement below was nonetheless COMPILE-PROBED verbatim against the built
corpus (2026-08-05, `lake env lean` on a scratch probe: clean, one expected `sorry`
warning) — the BP_IV/BP_VI lesson. (iii) Statement-fence: theorem statements of landed
corpus units are untouched; parked items 22–29 untouched. (iv) One-home discipline: the
properness-proviso leg belongs to the §3.3 (KP)/(KPirr) [T] row (FGMN Lemma 5.3) — this
blueprint CONSUMES it as a displayed pinned input and never re-prices it. (v)
Falsifier-first: each numerics gate runs BEFORE the math unit it guards is written up.

**The architecture in one display (the tower induction) [REV 2 — Codex finding 1: the
rev-1 ladder was index-circular; repaired by the STR/KEY split below].** GD23's (KP_j)
indexing: the block of key Φ_{j+1} lives in gr(w_{j+1}) — the state the read ν_j
creates and its key inhabits (KEY-g is the j = 0 instance, in gr(w₁)). For the
discharge, (GR-B) at state order j+1 SPLITS into two halves with different inputs
(the packaging GD23 displays as one is consumed here in two steps):
**(GR-B-STR)_{j+1}** = clauses (0)/(0′)/(0″)+(1)+(2′) — the structure of gr(w_{j+1})
in the CHAIN's data (Δ = K_j[ȳ], anchors, operators): FGMN states these for the
inductive valuation w_{j+1} with chain (Φ₀, …, Φ_j), consuming the chain keys' blocks
(KP)_{≤ j−1} ONLY — never the state key Φ_{j+1}. **(GR-B-KEY)_{j+1}** = clauses
(3)+(4) — about ψ̂ = the state key's initial form — consuming additionally (KP_j)
(Φ_{j+1} ∈ KP(w_{j+1}), which is what FGMN §5's operators/faithfulness quantify over).
The well-founded ladder, base j = 0 proved (VAL-g gives (V1)₁ + gr(w₁)'s explicit
structure; KEY-g gives (KP₀)):

    (V1)_{≤ j+1} + (KP)_{≤ j−1}                      [induction state]
      ⟹ (GR-B-STR)_{j+1}                             [member (a), FGMN retarget]
      ⟹ (KP)_j at the standard lift Φ_{j+1}          [member (b): KP-STEP, door 1 —
                                                       proved IN gr(w_{j+1})]
      ⟹ (GR-B-KEY)_{j+1}                             [member (a), FGMN §5 pins]
      ⟹ (V1)_{j+2}                                   [from (KP)_j: GD23 §5 BRIDGE +
        MacLane 1936 Thm 4.2 — the AUGMENTATION theorem, GD23 §2's pin (ML), printed
        scope cleared at LITUNIT §3, corroborated by FGMN Prop 1.9's cite "[10,
        Thms. 4.2, 5.1]"; DISTINCT from FGMN Thm 4.2 (the two-form residual identity)
        — ON FILE, reuse, not re-proved]
    (d) = the (KP)_i block + GD3-MIN read off at every realized order-≥ 2 site,
          PLUS the site's run data (§4.2 (iv) — the F7 repair)
    (c) = engine-side run/read binding — parallel strand, no dependence on (a)/(b)

No circularity [Codex Q1 re-answered]: (GR-B-STR)_{j+1} needs (KP) strictly below the
state key; KP-STEP runs in gr(w_{j+1}) — the ring (V1)_{j+1} already supplies — and
never in gr(w_{j+2}); (GR-B-KEY)_{j+1} consumes (KP)_j pointing backward; (V1)_{j+2}
closes the rung. The base of everything is the proved order-≤ 1 layer (GD23 Theorems
GAUSS-g/VAL-g/KEY-g/RES-1, any d₀, any complete DVR O).

---

## 1. Member (a) — (GR-B). DOOR: LITERATURE-RETARGET (FGMN), plus the composed-march write-up

**1.1 The exact object.** (GR-B) at state order i+1 ≥ 2 (GD23 rev 4 §7.2, the display
of record; ψ̂ := ψ̂_hom^{(i)} the creating read's key initial form, prime by (KPirr);
w := w_{i+1}): existence of
(0) a distinguished degree-0 generator ȳ with Δ = K_i[ȳ] a polynomial ring
    [structure clause];
(0′) the invertible anchor-monomial PAIR: weight-indexed ϕ_α and side-anchored
    ϕ(f) = ϕ_α·ȳ^{j₀(f)}, j₀(f) = ⌊s₀(f)/e_i⌋, whose degree-0 sub-step structure
    realizes the carry algebra 𝒟 = F[u]/(u^{e_b} − ζ) of [F.0];
(0″) the residual-operator PAIR R^{gr}_α / R^{gr}, TOTAL on nonzero homogeneous
    elements, valued in K_i[z] ∖ {0};
with the four laws: **(1)** multiplicativity up to K_i^×; **(2′)** the anchored-march
identity in(f) = ϕ_α·R^{gr}_α(in f)(ȳ) = ϕ(f)·R^{gr}(in f)(ȳ) (two printed forms,
CORRECTLY paired — the V28-1 conflation and the V26-2 slot-fresh reading are the two
displayed refuted variants), with R^{gr}(in f) ∼ R_λ(f); **(3)** R^{gr}(ψ̂) ∼ ψ_i;
**(4)** faithfulness ord_{ψ_i}(R^{gr}(α)) = ord_{ψ̂}(α) — properness proviso EXCLUDED
(consumed from the §3.3 [T] pin where clause (4) fires at e·g = 1 refinement keys).
**Discharge split [REV 2, finding 1]:** clauses (0)/(0′)/(0″)+(1)+(2′) form
(GR-B-STR) (chain-data only, inputs (V1)_{≤ i+1} + (KP)_{≤ i−1}); clauses (3)+(4)
form (GR-B-KEY) (about the state key, additional input (KP_i)) — the §0 ladder's two
(a)-steps. GD23's single-package display is unchanged; the SPLIT is a property of the
derivation order, recorded in the write-up's S5/S6 sectioning.

**1.2 Faithfulness brief (the door-2 charge: exact candidate printed statement ↔ what
must match in OUR language ↔ translation risk).** Source paper: J. Fernández,
J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane valuations*, J. Algebra 427
(2015) 30–75 — scope verbatim "Let K be a field equipped with a discrete valuation v"
(ARBITRARY discretely valued field; completeness unused for the pinned statements —
LITUNIT §5). Per-clause table:

| our clause | printed candidate (verbatim locus, LITUNIT §5) | what must match in our carry-algebra/dictionary language |
|---|---|---|
| (0) structure | **Thm 4.8** "R_{r,0} : ∆ → F_r[y] is an isomorphism … ∆ = F_r[y_r]" + **Cor 4.9** (F_{i+1} = F_i[z_i], deg ψ_i = f_i) | Δ = K_i[ȳ] with ȳ ↔ y_r; K_i ↔ F_r at depth r = i+1 (index dictionary GD23 §1.2: w_i ↔ v/µ at depth i+1, e_r = e_i, h_r = h_i) |
| (0′) anchors | **Lemma 4.1**'s ϕ_r(α)/ϕ_r(g) pair (ϕ_r(α) = x_r^{s(α)}p_r^{u(α)}, eq. (12), 0 ≤ s(α) < e_r) | ϕ_α ↔ ϕ_r(α), ϕ(f) ↔ ϕ_r(g); the two-form consistency ϕ(f) = ϕ_α·ȳ^{j₀} ↔ printed eq. (16) at j = j₀; the carry algebra 𝒟 = F[u]/(u^{e_b} − ζ) realized by the degree-0 sub-steps of the monomial system (the MOVES pass-7 object) |
| (0″) operators | **Def 3.16** (R_{r,α}, slot j at abscissa s(α) + je_r) + **Def 3.18** (R_r = R_{r,α}/y^{j₀}) | R^{gr}_α ↔ R_{r,α}, R^{gr} ↔ R_r; slot-κ read abscissae s₀(f) + κe_i; z-order j₀ = Cor 4.4(3) |
| (1) | **Thm 4.2** (H_µ, ϕ_r multiplicative; via Lemma 4.1/Cor 2.7); **Lemma 5.13** (R(gh) = R(g)R(h), g µ-proper) as CORROBORATION ONLY [REV 2, finding 4: Lemma 5.13's properness hypothesis cannot supply the TOTAL clause; the rev-1 row over-priced it — a defect ALSO latent in GD23's own (GR-B)(1) citation line, flagged to the write-up] | multiplicativity up to K_i^×, TOTAL on homogeneous elements — DERIVED in S6 as obligation **TR-7**: from Thm 4.2's identity, H(gh) = H(g)H(h) and the anchor arithmetic (eq. (12)/(16): s(g)+s(h) = s(gh)+e·δ, δ ∈ {0,1}) give R^{gr}(gh) ∼ R^{gr}(g)R^{gr}(h) with the δ-wrap absorbed through the p-exponent — the CARRY-WRAP computation (the same eq (12)/(16) arithmetic as OP-A2's 𝒟-clause), written out, never cited |
| (2′) | **Thm 4.2** verbatim: "H_µ(g) = ϕ_r(α)R_{r,α}(g)(y_r) = ϕ_r(g)R_r(g)(y_r)" + **Cor 4.4(2)(3)** slot granularity | the anchored-march identity, BOTH pairings; exact-match check against the printed two-form EXECUTED and displayed at GD23 §7.2 rev 3 (V28-1) — the retarget pass re-verifies it, never re-derives it |
| (3) | **Cor 5.6(2)** verbatim: "R_i(φ_{i+1}) = ψ_i, the minimal polynomial of z_i over F_i" | (KPb) transported; reads the extended chain — properness-proviso territory shared with (4). [REV 2, finding 5:] the printed operator takes the POLYNOMIAL φ_{i+1}, ours the graded ψ̂ — this row consumes TR-4's factor-through-initial-form lemma AT THIS CLAUSE explicitly (TR-4's scope now names it), not as unlabeled notation |
| (4) | **Prop 5.14 / Cor 5.15** verbatim: "ord_ψ(R_r(g)) = ord_{µ,φ}(g) for any non-zero g" (φ proper) | ord_{µ,φ}(g) = graded ψ̂-divisibility order (GD23 Lemma BRIDGE); the PROPER hypothesis is the excluded [T] leg (FGMN Lemma 5.3 + the two-step completion display at GD23 §7.2 (4)) |
| corroboration | MacLane 1936 Thm 10.2/Lemma 10.1/Lemmas 11.1–11.2/Thm 12.1/Cor 12.2 (commensurable case, automatic here) | independent pin of the structure clause; GMN Thm 2.26 (Theorem of the product) corroborates (1)+(2′) at GMN's own normalization |

**Translation risks (each an explicit lemma-shaped obligation of the write-up; the
tame-FE retargeting FAILURE is the standing precedent — a printed statement that
targets a DIFFERENT normalization of the same words cannot be consumed, so each TR
below must be DISCHARGED IN WRITING, not waved):**

* **TR-1 (sign mirror).** FGMN's augmentation adds λ ∈ ℚ_{>0} to µ(φ); our slopes are
  λ = −h/e. One displayed sign dictionary, applied consistently at every slope-indexed
  object (LITUNIT §5 caveat (i)).
* **TR-2 (value normalization).** FGMN's µ is ℚ-valued chain-normalized; our w_i is
  ℤ-valued (w_i(π) = E_i = e₀⋯e_{i−1}). The graded ring is invariant under value-group
  dilation up to index re-labeling — this needs a two-paragraph rescaling lemma
  (gr_γ(w) = gr_{γ/E}(w/E)), NOT a citation (caveat (iii)).
* **TR-3 (twist conventions).** FGMN's R_i differ from GMN Defs 2.19–2.21 residuals by
  the internal twist normalization; the identification "∼ up to K_i^× per side" is
  exactly what (2′) prices; a finite definitional comparison, written out once.
* **TR-4 (argument type).** The printed R_{r,α}(g)/R_r(g) take the POLYNOMIAL g; our
  R^{gr} takes the graded element in(f). The lemma-shaped fact consumed: the printed
  operators factor through H_µ(g) (true of Def 3.16 — its coefficients are residues of
  the attained digits, exactly H_µ(g)'s data; recomputed at GD23 pass 2, F2). Must be
  STATED and proved as a lemma, not treated as notation.
* **TR-5 (index dictionary).** Depth r = i+1; Φ_i ↔ φ_{i+1}, w_i ↔ v_{i+1}/µ at chain
  position i+1, K_i ↔ F_{i+1}^{GMN} = F_r^{FGMN}, ψ_i ∈ K_i[z] ↔ ψ_r ∈ F_r[y]. The
  standing off-by-one hazard: every consumption site carries the dictionary line
  (the GD23 §6 discipline).
* **TR-6 (properness one-home).** Clause (4)'s printed hypothesis "φ proper" is NEVER
  discharged inside (GR-B): at e·g ≥ 2 sites the extended chain is optimal and
  properness automatic (displayed at GD23 §7.2); at e·g = 1 refinement sites the
  discharge is the §3.3 [T] pin (FGMN Lemma 5.3 via the augment-then-complete step).
  The write-up displays WHERE the proviso fires and cites the [T] row — it does not
  re-prove or re-classify it.

**1.3 The write-up unit (the actual discharge artifact).** New leaf
`lean/notes/openmath/GRB_order2_attempt.md` + self-contained
`GRB_order2_verifybrief.md` (the GD23-cycle continuation named in the §3.1 owner
column), sections:
(S1) setting + TR-5 index dictionary + the standing (R1)/(R2) hypothesis display;
(S2) TR-2 rescaling lemma, proved; (S3) TR-3 twist dictionary, written as a finite
comparison table FGMN-Def-3.16 ↔ GMN-Def-2.20/2.21; (S4) TR-4 factorization lemma,
proved; (S5) clauses (0)/(0′)/(0″) from Thm 4.8 + Lemma 4.1 + Defs 3.16/3.18 through
TR-1..TR-5, INCLUDING the carry-algebra realization display (𝒟 = F[u]/(u^{e_b} − ζ)
from the anchor system's degree-0 sub-steps — the [F.0] tie the engine consumes);
(S6) laws (1)/(2′)/(3)/(4) from the pinned Thm 4.2/Cor 4.4/Cor 5.6(2)/Prop 5.14/
Cor 5.15, with (2′)'s two-form pairing check re-verified against the GD23 §7.2
display, TR-6 cited at (3)/(4), and TR-4 cited AT clause (3) [REV 2, finding 5];
(S6a) [REV 2, findings 4/6] the eq (12)/(16) exponent-arithmetic section proving
BOTH the clause-(1) TOTAL multiplicativity carry-wrap (TR-7; Lemma 5.13 =
corroboration at proper g only) AND the 𝒟-realization clause (OP-A2); (S7) the
order-1 instance cross-check —
the composed statement must REPRODUCE GD23's proved order-1 display (in(f) =
ϕ·R_λ(f)(ȳ) with ȳ = Φ̄₀^e π̄^{−h}, e_b = 1, 𝒟 = K₀) verbatim, the non-vacuity gate of
the whole retarget; (S8) honesty ledger + attack list.
**Honest open points, named now:** (OP-A1) TR-2's rescaling lemma is unwritten (easy
but load-bearing); (OP-A2) the 𝒟-realization clause has no printed home — it is OUR
gloss of Thm 4.8/Cor 4.9's sub-step structure and MUST be PROVED from them in S5 [REV
2, finding 6: the rev-1 "else dropped" escape is RETRACTED — the clause is consumed by
[F.2]'s reading, so if S5's proof fails it becomes a DISPLAYED OPEN SUB-MEMBER of (a)
with its own §3.1-row consequence, never silently dropped]; (OP-A3) FGMN state their
operators for a MacLane chain of µ — our tower reaches w_{i+1} through the policy's
chain; that the policy's chain IS a MacLane chain of w_{i+1} is (KP)-territory
(member (b)), consumed as the induction state, and the write-up must display this
dependence rather than silently assuming it **[REV 3, GRB-leaf R5.2 sync
(2026-08-02): the MacLane-chain condition here is the GRB leaf's (H-CHAIN), whose
(b)-part — the chain conditions Φ_{j+1} ≁_{w_{j+1}/E_{j+1}} Φ_j — runs over the
FULL range 0 ≤ j ≤ i−1 per FGMN Def 3.1 (φ_{k+1} ≁_{µ_k} φ_k for EVERY 1 ≤ k < r,
under the index dictionary r = i+1, φ_k ↔ Φ_{k−1}), NOT the "internal steps only"
range 1 ≤ j ≤ i−1, which is EMPTY at order 2 (i = 1) and omits the required
Φ₁ ≁_{w₁/E₁} Φ₀. Member (b)'s KP-STEP supplies the (a)-part level-by-level;
the (b)-part is automatic at degree-increasing steps and stays [T]-pinned at
degree-preserving (e·g = 1) refinement steps — NOW INCLUDING j = 0]**; (OP-A4 = TR-7) [REV 2, finding 4] the
clause-(1) TOTAL multiplicativity carry-wrap derivation (§1.2's (1)-row): the printed
supply covers it only up to the δ-wrap, and the wrap absorption is the same eq
(12)/(16) computation as OP-A2 — one section (S6a) proves both or both stand open.

**1.4 Verification protocol.** Falsifier N-1 (§5.4) runs BEFORE S5/S6 are written.
Then the standard cycle: fresh hostile pass (Codex, literature access, LITUNIT
extractions named) with charge items = the TR-1..TR-6 discharges + OP-A1..A3 + the S7
reproduction check; bar = 2 consecutive clean passes (the leaf-#4 criterion). On
acceptance the §3.1 (H1)(a) face flips to a pinned-and-WRITTEN package riding the
GRB leaf's [V] row; the (H1) row itself retires only when (a)–(d) all land.

---

## 2. Member (b) — GD-1/OL-2a-1 beyond order 1. DOOR: PROVE (door 1), GMN retarget as backup (door 2)

**2.1 The exact statement (O-2a rev 4 §4, verbatim core).** OL-1 (lift admissibility +
normalization), ONE JOINT statement by strong induction on the order (the P2-4
repair): for every well-formed chain datum c of order i ≥ 1, with t = its type over
F_rep: (a) Lift_i(c) is monic in O[x] of degree m_{i+1} = m_i e_i f_i; (b) Lift_i(c)
is of type t with R_i(Lift_i(c)) ∼ ψ̂_i — a Def-2.12 representative of t;
(c) v_{i+1}(Lift_i(c)) = e_i f_i·v_{i+1}(Lift_{i−1}(c′)), equivalently V_{i+1} =
e_i f_i(e_i V_i + h_i). [GMN Thm 2.11 proves EXISTENCE of a representative with
(a)–(c); the open content is that the pinned Lift_i satisfies the same.] In GD23's
carrier language the per-level content is the (KP_j) block: **(KPa)** in(Φ_{j+1}) =
u·ψ̂_hom^{(j)} + the degree block ψ̂_hom^{(j)} ∤ in(B) for nonzero deg B < deg Φ_{j+1};
**(KPirr)** ψ̂_hom^{(j)} PRIME in gr(w_{j+1}); **(KPb)** R_j(Φ_{j+1}) ∼ ψ_j. Proved at
j = 0 for the standard lift at any d₀ over any O (Theorem KEY-g). The properness LEG
stays [T] (§0 rule (iv)).

**2.2 Door 1 — Theorem KP-STEP (the S-1 "same method": KEY-g's weighted-Gauss/
homogenization argument transported one level up) [REV 2 — findings 1/2/14 folded:
indices corrected to the §0 split ladder; the circular s6 alternative deleted; the
localization-avoidance step displayed].** Statement: fix the induction state
((V1)_{≤ i+1}, (KP)_{≤ i−1}) and (GR-B-STR)_{i+1}; let the read ν_i creating the
state (GD23 §1.2: performed at the frame (Φ_i, w_i, K_i)) carry (e, h) := (e_i, h_i)
coprime ≥ 1 and ψ := ψ_i ∈ K_i[z] monic irreducible of degree g ≥ 1 with ψ(0) ≠ 0
[TR-5 line displayed at the unit]; let Φ_{i+1} := Σ_κ ψ̂_κ·M_κ be the standard key
lift (ψ̂_κ the coefficient lifts, M_κ the marched monomial normalizers from
(GR-B-STR)(0′)). Then (KPa)+(KPirr)+(KPb) hold at (KP_i) — the block of Φ_{i+1} IN
gr(w_{i+1}), the ring (V1)_{i+1} already supplies. Proof plan, section-by-section
(each a numbered section of the unit note `KPSTEP_attempt.md`):
* (s1) *The marched homogenization.* hom^m_{e,h} : K_i[z] → gr(w_{i+1}),
  c(z) = Σ c_κ z^κ ↦ Σ [ĉ_κ]·ϕ·ȳ^κ-shaped sums — multiplicative and injective.
  Inputs: (GR-B-STR)_{i+1}(0)/(0′) (Δ = K_i[ȳ] polynomial ring: injectivity; anchor
  invertibility + march linearity in κ: multiplicativity — exponents add slot-wise as
  at order 1).
* (s2) *Weight/degree bookkeeping of the standard lift.* Every nonzero monomial of
  Φ_{i+1} at one w_{i+1}-weight; in(Φ_{i+1}) = hom^m(ψ) up to the anchor unit — the
  (KPa) initial-form identity. Input for the development weights: DEVID at the PARENT
  level (w_i with key Φ_i — GD23 §4, on file, consuming (V1)_i + (KPa)_{i−1}, both in
  the induction state).
* (s3) *Factor collection.* Every homogeneous δ in the localized gr(w_{i+1}) factors
  as (invertible anchor monomial)·hom^m(c) with c(0) ≠ 0. Input: (GR-B-STR)(0′) +
  Thm 4.2's rank-one statement (P_α/P_α⁺ = ϕ_r(α)Δ free of rank one) — the order-1
  proof's "collect the least Φ̄₀-exponent" step, with (π̄, Φ̄₀)-monomials replaced by
  the anchor system.
* (s4) *Primeness.* ψ irreducible in K_i[z] ⟹ hom^m(ψ) prime in gr(w_{i+1}). TWO
  displayed steps [REV 2, finding 14]: (s4a) *localization avoidance* — hom^m(ψ) is
  divisible by NO inverted element beyond units: ψ(0) ≠ 0 and deg ψ ≥ 1 against the
  anchor-monomial group (the KEY-g "Φ̄₀ ∤ ψ_hom, π̄-unit-free top term" argument
  transported), so primeness in the localization pulls back along the domain
  injection gr ↪ gr_loc; (s4b) the order-1 UFD argument verbatim in Δ-localized =
  K_i[ȳ][anchors^{±1}]: suppose hom^m(ψ) = δδ′, collect anchors (s3), use injectivity
  (s1) + irreducibility of ψ. This is (KPirr) at the state — the clause V26-1 taught
  us is a genuinely additional input, so it gets its own section, not a remark.
* (s5) *Degree block.* deg_x B < deg Φ_{i+1} ⟹ ψ̂_hom ∤ in(B) in gr(w_{i+1}). The
  order-1 proof used the slot bound "top Φ₀-slot < eg". At the state the
  corresponding step is the ȳ-degree comparison: **(OP-B1, the honest open point of
  door 1)** deg_x B < deg Φ_{i+1} bounds the ȳ-degree of in(B) below e·g — the graded
  shadow of MacLane's minimal-degree clause. Candidate printed supply: FGMN §5's
  key-polynomial minimality characterizations (Prop 5.7's equivalent forms) — pin TO
  BE VERIFIED against the extraction (do NOT cite a numbered clause until re-read;
  the LITUNIT discipline). If no printed form matches, (s5) is proved directly from
  the development structure (DEVID at the parent + slot bookkeeping), the same shape
  as order 1 — expected mechanical but MUST be written.
* (s6) *(KPb).* R_i(Φ_{i+1}) ∼ ψ_i: the DIRECT computation ONLY [REV 2, finding 2:
  the rev-1 "(GR-B)(3) at the NEXT state" alternative is DELETED as circular —
  (GR-B-KEY) sits downstream of (KP) in the §0 ladder]: read (s2)'s initial form
  in(Φ_{i+1}) = (unit)·hom^m(ψ) through (GR-B-STR)(0″)/(2′)'s operators — the slot-κ
  reads of hom^m(ψ) are ψ's coefficients by (s1)'s construction, so the operator
  returns ψ up to the declared twist, exactly as (KPb) "is KEY-g's construction" at
  order 1. Consumes (2′) at the key itself (an (R1)/(R2)-conforming element by (s2))
  and NO properness (TR-6 untouched: properness enters only (GR-B-KEY)).
* (s7) *The family clause.* The per-level blocks assemble into OL-1's joint
  statement. [REV 2, finding 15 — expanded from the rev-1 one-liner:] B-M2's
  statement, displayed: by strong induction on i, (a) monicity + deg Φ_{i+1} =
  e_i g_i deg Φ_i are the lift CONSTRUCTION's top term (s2's bookkeeping: the κ = g
  monomial is M_g·Φ_i^{e·g}-shaped with unit normalizer, lower κ strictly smaller
  degree); (b) "Lift_i(c) is a Def-2.12 representative of its type" from
  (KPb)+(KPirr) at (KP_i) through GMN Def 2.12's normalization (the ∼-insensitive
  reading, TR-B3); (c) the value recursion V_{i+1} = e_i f_i(e_i V_i + h_i) is (s2)'s
  weight arithmetic at the top monomial (γ̂_i = w_{i+1}(Φ_{i+1}) = e_i·g_i·γ_{i+1} in
  GD23's constants; the K_i-degree f_i enters through deg ψ = g_i and the residue
  tower Cor 4.9). Clause (b)'s "type over F_rep" is well-defined level-by-level
  exactly because the induction is cumulative (P2-4's display). Output shape = OL-1
  verbatim, so O-2a's Theorem 2 consumption fires unchanged.

**2.3 Door 2 — literature retarget (backup + corroboration), faithfulness brief.**
Candidate printed statement: **GMN Thm 2.11 + Def 2.12** (existence of a Def-2.12
representative of every truncated type, with the (a)–(c) normalization — already
pinned at the O-2a brief's literature list) plus **MacLane Def 4.1 / FGMN §5
(Prop 5.7, Thm 5.8)** for the key-polynomial characterization. What must match in our
language: GMN's representative is SOME monic lift with the right residual — OUR
statement pins THE canonical Lift_i (the engine's standard lift built through the
marched monomials). The printed theorems therefore CANNOT discharge OL-1 alone: the
missing content is precisely "the standard lift is ONE OF the Def-2.12
representatives", which is door 1's (s2)+(s6). Translation risks: (TR-B1) GMN's
standing scope is K/ℚ_p finite — the arbitrary-DVR claim rides FGMN's scope (as at
member (a)), so door 2 alone would SHRINK the generality GD23 already proves at
order ≤ 1; (TR-B2) Def-2.12's normalization "∼" hides the twist convention — same
TR-3 dictionary; (TR-B3) the equivalence-vs-equality of representatives (GMN types
are equivalence classes; our lifts are pinned polynomials) — consume GMN Prop 5.7/Thm
5.8's key-equivalence only through the ∼-insensitive clauses (a)–(c). VERDICT: door 2
is the corroborating pin and the existence supply inside (s7); door 1 is the
discharge route. This matches the §3.1 owner note ("the §3.3 S-1 row's 'same method'
note prices the intended proof ROUTE").

---

## 3. Member (c) — GD-6/OL-2a-6 conformance instances at orders ≥ 2. DOOR: CONSTRUCTION-CONFORMANCE

**3.1 The exact statement (O-2a rev 4 §4 OL-6, verbatim core).** For every monic
f ∈ O[x] with disc f ≠ 0 and every complete run of the engine's stage flow on f with
emitted dressed history 𝐇 = (ρ₀; ν₁, …, ν_k): for every 1 ≤ j ≤ k with ν_j CONTINUING,
the j-th emitted record IS the record emitted by the engine's level-j read on f over
the chain of its emitted prefix — (a) j = 1: the base read over ρ₀ with key
φ₁ = Lift₀(ψ̂₀); (b) j = i+1 ≥ 2: the stage read over c := Θ(𝐇_{≤i}) with key
Φ̂_{i+1} = Lift_i(c). The §3.1 (H1)(c) face = the order-≥ 2 INSTANCES of this that
Step 10's conditionality line consumes.

**3.2 What "construction-conformance" means here (route → proof).** The
proof-by-construction ROUTE on record says: the implemented engine literally computes
its level-j read on the emitted prefix's chain, so each instance holds by inspecting
the construction. VC5's ruling stands: a route is not a proof. The discharge is
two-legged, and both legs are ALREADY-TYPED corpus objects:
* **Lean leg.** The corpus's f-explicit run predicate `ReadsOf p F n f H`
  (`HC2/Defs.lean`: HistoryCoherent + per-read development realization `SideReads` +
  the `Φnext` chain pin) IS OL-2a-6's per-level binding, Lean-typed; `keys_exist_of_run`
  (HC2/U1) already extracts the lawful key tower from it. The conformance theorem to
  land: every history the counted corpus consumes at orders ≥ 2 carries a `ReadsOf`
  witness — unit H1-U12/U13 (§5.3). The realization DIRECTION (every lawful run is some
  f's run) is on file Lean-core at the wired instance (`MovesD/R7_runRealizer.lean`,
  `runRealizerExists_zmod` — O-14a′); the conformance direction is what this member
  adds.
* **Numerics leg.** The O-3 design's G-EMIT/U6 gate (O-2a rev 4 §4 records the
  falsifier home): instrument a run; check each emitted record equals the stage read
  recomputed over Θ(emitted prefix), depth ≥ 2 — gate N-2 (§5.4).

**3.3 Honest scope split.** OL-2a-6 as stated is about O-2a's ABSTRACT engine; the
Lean corpus theorem is about the IMPLEMENTED classifier. The identification of the two
is the S-1 transcription/composition audit — a §3.3 [T] row, NOT this member, and this
blueprint does not touch it. Discharging (c) therefore means: (i) the abstract OL-2a-6
proved for the abstract stage flow (a short induction on the run once the stage
interface's c-parameter is bound — O-2a rev 4 already displays the binding; expected
LOW difficulty, unit C-M1), AND (ii) the corpus conformance theorem at the wired
instance (H1-U13) + N-2 green, with the S-1 audit cited as the bridge's [T] home.

---

## 4. Member (d) — the order-≥ 2 KEY1 block. DOOR: PROVE by assembly (the S-1 same-method route)

**4.1 The exact statement (ROOT §3.1, the VC8-1 requantified form).** At EVERY realized
site of Step 6's machine at OM READ ORDER ≥ 2 — membership by read order alone, key
degree irrelevant, e·g = 1 refinement chains INCLUDED — for the STANDARD key lift
Φ_{i+1} assigned at the site with read side (e, h) and residual factor ψ of degree
g ≥ 1 (ord_ψ(R_i) = μ):
(d1) in(Φ_{i+1}) = u·ψ̂_hom in gr(w_{i+1}), u invertible homogeneous, ψ̂_hom irreducible;
(d2) ψ̂_hom ∤ in(B) for every nonzero B with deg B < deg Φ_{i+1};
(d3) ord_{ψ̂_hom}(in f) = ord_ψ(R_i(f)) = μ.
This is O-1thr's (V1)/(V2) key-compliance block beyond its proved order-≤ 1 slice —
the block Lemma WGEO consumes at those sites (O-1thr rev 4 §2.5, the G2-repaired
form: (V2a) restated as exactly (d1)+(d2) with the bridge sentence, (V2c) = (d3)).

**4.2 The assembly theorem (KEY1-SITE) — no new VALUATION THEORY beyond (a)+(b);
four genuine assembly obligations [REV 2 — findings 7/9: the rev-1 "no new
mathematics" headline is RETRACTED and the missing run-data hypothesis added].**
(d1)+(d2) at a site = member (b)'s (KPa)+(KPirr) at the site's creating read (KP-STEP's
conclusion instantiated); (d3) = GD3-MIN at the site, whose route B is proved FROM
(GR-B) at GD23 §7.3 (on file, general order), APPLIED AT the site's f. So:

    KEY1-SITE: (GR-B-STR/KEY)_{i+1} + KP-STEP at the site's creating read
      + the site's REALIZED-READ DATA on f   [the finding-7 hypothesis: f develops on
        ν's side with the recorded anchored residual — O-1thr's (R1)/(R2) + REALIZED
        vocabulary; corpus face: SideReads(iii)'s HasAnchorK tie + the node's hOrd]
      ⟹  (d1)–(d3) at the site, with (d3)'s μ the site's RECORDED μ.

The unit note `KEY1SITE_attempt.md` proves this as an assembly with FOUR displayed
obligations (each a real proposition, not formatting): (i) *coverage arithmetic* —
sites keyed by READ ORDER; the proved slice is exactly order ≤ 1 (GD23 + O-1thr
(V1)/(V2) there); the theorem covers the complement; NO key-degree/order
identification is consumed anywhere (the VC8-1 lesson, restated as a check the
verifier must tick); (ii) *the site-to-tower reading* — every realized machine site
at read order ≥ 2 presents as a tower instance ((Φ_i, w_i, K_i) frame + read ν_i) in
O-1thr's realized-state vocabulary: a THEOREM connecting machine sites to tower
instances (O-1thr §1/§2.5's REALIZED definitions are the supply; the note WRITES the
connection, never assumes it); (iii) *the e·g = 1 corner* — KP-STEP's proof pattern
covers refinement reads (at order 1, KEY-g allows eg = 1: ψ = z − c, Φ₁ = Φ₀ + ĉπ^h;
the marched analogue is Φ_{i+1} = Φ_i + ĉ·M₀), BUT the (s5) degree block at eg = 1 is
exactly OP-B1's hardest corner (deg Φ_{i+1} = deg Φ_i) and the properness proviso
enters (d3) via (GR-B-KEY)(4), consumed as the §3.3 [T] pin — both displayed, one
home each; (iv) *the run-to-anchor identification* — (d3)'s RHS ord_ψ(R_i(f)) = μ is
about the SITE's f and recorded μ: the note consumes the realized-read data
hypothesis displayed above (math side: (R1)/(R2) + the anchored-march reading; Lean
face: `HasAnchorK (ν.σ.R f) ν.a ν.Ranch` + `ν.hOrd`), supplied at wired sites by
member (c)'s binding and at math sites by O-1thr's REALIZED definition. Also
displayed: *the WGEO delivery shape* — the block is emitted in O-1thr rev 4's exact
consumed form ((V2a): unit·ψ̂_hom + the degree block with the "deg B < eg ⟹
x̄-degree < eg" bridge sentence; (V2c): first-attainment ord tie), so WGEO and
Theorems 1–3's all-site scope fire with NO restatement. Dependence display: (d)
retires when (a) and (b) land AND KEY1-SITE (with its four obligations) passes — it
is the SITE-INSTANTIATION face of the group, priced separately by ROOT because Step 6
consumes it in this shape.

**4.3 What (d) adds beyond (a)+(b), exactly [REV 2, finding 9].** The four §4.2
obligations — coverage, site-to-tower reading, the eg = 1/OP-B1 corner, and the
run-to-anchor identification — plus the delivery-shape conformance. These are
assembly-LAYER propositions (no new valuation theory), but they are genuine
mathematics: exactly where VC7-1/VC8-1 found the consumed-without-a-home defects, so
they are WRITTEN and pass-gated, never waved.

---

## 5. LEAN UNIT SPECS (all compile-probed 2026-08-05; target `lean/LeanUrat/Scaffold/HDischarge/H1/`; namespace `LeanUrat.Scaffold.HDischarge.H1`)

Probe record: the §5.1 statements compiled verbatim against the built corpus (single
scratch file, `lake env lean`, clean; only `kp_step`'s intended `sorry` warned); the
REV-2 forms (`GrBKeyLaws` with link fields + `faithful_at`; `DevBound`; the enlarged
`kp_step`) RE-PROBED 2026-08-05, same result.
Imports per file: `LeanUrat.MovesGr.Defs`, `LeanUrat.MovesC.Defs`, `LeanUrat.HC2.Defs`
(+ `LeanUrat.Moves.Defs` transitively). Ground rules of BP_II §0 apply (no new axioms;
hypothesis rows as named structures; provers may adjust implicit binders, never
content). The Lean layer is stated at the wired instance O = ℤ_p (`Polynomial ℤ_[p]`,
the corpus's carrier); the arbitrary-DVR generality lives in the math leaves, whose
proofs are ring-free (GD23 §1.1 discipline) — the Lean units are the corpus FACE of
the discharge, not its scope ceiling.

### 5.1 `Defs.lean` — the hypothesis rows (wave 0)

**H1-U1** — the module shell: imports (`LeanUrat.MovesGr.Defs`, `LeanUrat.MovesC.Defs`,
`LeanUrat.HC2.Defs`), namespace `LeanUrat.Scaffold.HDischarge.H1`, the `universe u` +
variable block below, and a module docstring citing this blueprint + the §3.1 (H1) row.
LOW. U2–U4 land inside it:

```lean
universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- H1-U2 — the key-compliance block (KPa)+(KPirr) = (H1)(d1)+(d2), at a stage σ'
carrying the state key, over a genuine graded model M (MovesGr). Hypothesis ROW at
orders ≥ 2; THEOREM target at the base (H1-U5) and at KP-STEP's conclusion (H1-U8). -/
structure KPBlock (σ' : Stage p F) (M : GenuineStageModel σ') where
  ψhom : M.S.Gr
  homog : ∃ (γ : ℤ) (x : M.S.grPiece γ), ψhom = DirectSum.of (fun γ => M.S.grPiece γ) γ x
  kpa_init : letI := M.Rg.ring; ∃ u : (M.S.Gr)ˣ, M.S.initialForm σ'.Φ = (u : M.S.Gr) * ψhom
  kpirr : letI := M.Rg.ring; Prime ψhom
  kpa_block : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
    B.natDegree < σ'.Φ.natDegree → ¬ ψhom ∣ M.S.initialForm B

/-- H1-U3 — (GR-B-KEY) clauses (3)+(4) keyed to the creating read ν (MovesC.Node: ν.σ
the parent stage, ν.ψ the residual factor over ↥ν.σ.K) and the state model, WITH the
ν↔σ' link laws as fields [REV 2, finding 8: the rev-1 row carried no compatibility
between ν, σ', M, KB and asserted the ∀f (total Cor-5.15) law — over-quantified for a
hypothesis row; the row now carries the LINK plus the RECORDED-SITE law only (what
WGEO consumption needs, supplied by SideReads(iii)'s HasAnchorK witness + ν.hOrd);
the TOTAL form is the SEPARATE gated extension H1-U14, never a row field]. -/
structure GrBKeyLaws (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (KB : KPBlock σ' M) : Prop where
  link_e : σ'.e = ν.e
  link_h : σ'.h = ν.h
  link_prev : σ'.wPrev = ν.σ.w
  link_key : IsNodeLift ν σ'.Φ
  key_res : ∃ (c : (↥ν.σ.K)ˣ) (k : ℤ),
    ν.σ.R σ'.Φ = LaurentPolynomial.C (c : ↥ν.σ.K) * LaurentPolynomial.T k *
      Polynomial.toLaurent ν.ψ
  faithful_at : letI := M.Rg.ring; ∀ f : Polynomial ℤ_[p], f ≠ 0 →
    HasAnchorK (ν.σ.R f) ν.a ν.Ranch →
    (KB.ψhom ^ ν.μ ∣ M.S.initialForm f ∧ ¬ KB.ψhom ^ (ν.μ + 1) ∣ M.S.initialForm f)

/-- H1-U4 — the (H1)(d) site block: what Step 6's Lean consumers fire per order-≥ 2
site. Site-realization is the CONSUMER's predicate (Step-6 wiring supplies it);
membership here is by the (ν, σ', M) data alone — read order, never key degree. -/
def Key1SiteBlock (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') : Prop :=
  ∃ KB : KPBlock σ' M, GrBKeyLaws ν σ' M KB
```

Difficulty: LOW (statements only; land with docstrings citing this blueprint's §1/§2/§4
and the §3.1 row). Semantic-guardian flag: `GrBKeyLaws.faithful_at`'s guard choice is
the E-PHASE-flagged σ.R-rendering of the frame residual (HC2 `SideReads` (iii) note) —
the same convention U31's gate adjudicated; any strengthening to the total form goes
through H1-U14's falsifier gate first. [REV 2: `faithful_at` + link fields re-probed
2026-08-05 — compile-clean; the `DevBound` row of §5.3 lands in this file too.]

### 5.2 `Order1.lean` — the proved-slice instances (wave 1; the non-vacuity gates)

* **H1-U5 (`kpBlock_base`)** — MEDIUM-HARD. At a base stage (the corpus's base
  carrier, `MovesC`/HC1 base-stage builders; d₀ = 1 first, matching O-1thr's KEY1):
  construct `KPBlock σ₁ M₁`. Math source: GD23 Theorem KEY-g (i)(ii) — the
  homogenization-primeness proof in 𝔽_p[x̄, p̄^{±1}]; Lean route: through
  `GenuineStageModel`'s Θ into `LTwo ↥σ.K` where primeness is Laurent-polynomial
  irreducibility (mathlib UFD API), pulled back along `IsLocalization` injectivity
  (gr a domain — reuse `L1_gr_domain_iff_val` + `Stage.hwmul`). VERBATIM TARGET:
  `theorem kpBlock_base (σ : Stage p F) (M : GenuineStageModel σ) (h... : <base-stage
  hypotheses, prover-probed against the HC1/HC2 base builders>) :
  Nonempty (KPBlock σ M)` — the binder block is PROBE-FIRST (base-carrier names vary;
  candidates: HC1 S9 builders, HK13/HK14 `bStageCore` families).
* **H1-U6 (`grb_key_laws_base`)** — MEDIUM. The order-1 `GrBKeyLaws` instance: math
  source GD23 RES-1 + KEY-g(iii); Lean inputs `L3_residual_mul`,
  `L4_grRes_eq_genuine`, `Stage.hRmul`, the node's `hOrd`/`hRanch` fields.
* **H1-U7 (`key1SiteBlock_base`)** — LOW. `Key1SiteBlock` at the base from U5+U6
  (packaging).

### 5.3 `TowerStep.lean`, `SiteBlock.lean`, `RunBinding.lean` (waves 2–3)

* **H1-U8 (`kp_step`)** — HARD (the door-1 core; math source §2.2 KP-STEP). [REV 2,
  finding 10: the rev-1 shape omitted the mathematical hypotheses and claimed the
  block for ANY genuine model + matching lift parameters — more than the plan proves;
  the "prover discretion to enlarge to `TransitionCoreL`" line is WITHDRAWN (a
  hypothesis-block change is a statement change: E-phase sign-off only).] Statement,
  RE-PROBED 2026-08-05 with the DevBound row:
  `theorem kp_step (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
  (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h)
  (hprev : σ'.wPrev = ν.σ.w) (D : DevBound ν σ' M) :
  Nonempty (KPBlock σ' M)` — `M`'s `Θ`/`isLoc`/`discharge` fields ARE the Lean face
  of (GR-B-STR) (the math leaf A-M2 is what makes `M` instantiable at depth ≥ 2: the
  non-vacuity chain), and `DevBound` is the (s5)/OP-B1 degree-block input as its own
  probed row (Defs addition):
  `structure DevBound (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') :
  Prop where block : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
  B.natDegree < σ'.Φ.natDegree → ¬ (M.S.initialForm σ'.Φ ∣ M.S.initialForm B)` —
  the KEY-INITIAL-FORM divisibility block stated directly (equivalent to the ψ̂hom
  block modulo the `kpa_init` unit; the ȳ-degree DERIVATION of this row is OP-B1's
  math, and the row RETIRES into a proved lemma when OP-B1 lands — until then it is
  an explicit hypothesis of `kp_step`, displayed, never silently assumed). Staged as
  U8a (primeness transport: `Irreducible ν.ψ` → `Prime ψhom` via Θ/`isLoc`, WITH the
  (s4a) localization-avoidance lemma displayed [REV 2, finding 14]), U8b (degree
  block from `DevBound` + `kpa_init`), U8c (assembly).
* **H1-U9 (`grbKeyLaws_step`)** — HARD. (GR-B-KEY)(3)/(4) at the state from the math
  leaf (§1.3 S6): Lean face constructs `GrBKeyLaws ν σ' M KB` from the model's
  `discharge` + `key_res` inputs. [REV 2, finding 12 — the sorry discipline
  CORRECTED:] until the GRB math leaf passes, U9 does NOT land in any form — a
  `sorry`-backed theorem carries `sorryAx` and satisfies consumers as if proved,
  which would violate hypothesis-never-axiom; consumers meanwhile take `GrBKeyLaws`
  as an EXPLICIT BINDER (the corpus pattern), and the AxChk zero-`sorryAx` census is
  the gate.
* **H1-U10 (`key1SiteBlock_step`)** — LOW-MEDIUM. `Key1SiteBlock` from U8+U9 (the
  KEY1-SITE assembly, §4.2), PLUS the consumption lemma [REV 2, findings 7/8]: from
  `Key1SiteBlock ν σ' M` and a `SideReads`-realized run of f at ν (which supplies the
  `HasAnchorK (ν.σ.R f) ν.a ν.Ranch` witness per SideReads(iii)), conclude the
  WGEO-shaped (d1)–(d3) at (f, ν.μ) — the lemma WGEO's Lean consumers actually fire.
* **H1-U11 (`key1_along_history`)** — MEDIUM, PROBE-FIRST. The history-fold: along a
  `HistoryCoherent` chain with per-level models, `Key1SiteBlock` holds at every index
  ≥ 2 given the wave-2 units at each step (induction over `H.nodes`; the model-chain
  carrier is the probe risk — candidates: HC1 V1_readWPack/V34_readKernel packagings).
* **H1-U12 (`CountedRunBinding`)** — LOW (statement). Member (c)'s row:
  `def CountedRunBinding (n : ℕ) (corpus : Set (Polynomial ℤ_[p] × History p F)) : Prop :=
  ∀ fH ∈ corpus, ReadsOf p F n fH.1 fH.2` — the OL-2a-6 face over the corpus's counted
  set; the CONCRETE `corpus` binder is wired at E-phase to the classifier's counted
  boxes (candidates: TreeSeam/`MovesT.treeN` fibers; the M04 §5.5 K1 route). NOT
  probed at the concrete corpus — E-PHASE-FLAGGED.
* **H1-U13 (`countedRunBinding_wired`)** — HARD, PROBE-FIRST. The wired conformance
  theorem at the classifier instance (the (c) discharge; route: construction
  conformance — the engine's emitted records ARE stage reads). [REV 2, finding 13:
  the rev-1 "keys_exist_of_run's extraction inverted" route is DELETED — a theorem
  extracting keys FROM `ReadsOf` cannot be inverted to construct `ReadsOf`; the ONLY
  route is direct induction on the wired run builder, whose per-level emission law
  (emitted record = stage read on the emitted prefix) is the probe-first duty: name
  the builder, check the law is definitional or prove it by run induction.]
  Falsifier N-2 must be green BEFORE this unit is attempted.
* **H1-U14 (`faithful_total`)** — MEDIUM, GATED. The total (Cor 5.15) form: the ∀f
  per-anchor-witness law (the RETIRED rev-1 `faithful` field: ∀ f a Rf, HasAnchorK
  (ν.σ.R f) a Rf → ∀ μf, OrdPsiPoly ν.ψ Rf μf ↔ ψhom-order μf) as a THEOREM from the
  row + the math leaf: stated only if N-1's total-form check runs 0-violation at
  order-2 samples (including improper/e·g = 1 corners); otherwise the recorded-site
  form stands alone and this unit is CLOSED-NEGATIVE with the harness citation.
  **[STATED 2026-08-02 (gate positive: T8 0/2,400, preregistered, executed
  2026-08-08): `FaithfulTotal` [M]-row (displayed + consumed, never proved —
  supplier = the open GRB leaf, finding-12 discipline; no theorem can land until
  the leaf does) + PROVED Lean-core consumers `faithful_at_of_total` (the row
  recovers `faithful_at` via `ν.hOrd`) and `faithful_total_consume` (the U10
  SideReads-keyed total consumption, ∀ μf), in `H1/SiteBlock.lean` §U14; Cor 5.15
  verified ǫ-free (ideal-order statement — the REV-11 Def-3.15 twist correction
  enters nowhere), so no corrupted-extraction exposure.]**

### 5.4 Numerics/falsifier gates (run before their math units; `verification/openmath/`)

* **N-1 (`grb_order2_check.py`)** — extends `gd23_check.py` to the queued perimeter
  (GD23 §3: "depth-3 harness; d₀ ≥ 2 depth-2 harness — would exercise (GR-B)'s order-2
  instance numerically"): exact-arithmetic order-2 towers over ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]],
  d₀ ∈ {1, 2}; checks per sample: the anchored-march identity (2′) two-form agreement
  (weight-anchor vs side-anchor, discrepancy exactly ȳ^{j₀}), clause (1)
  multiplicativity, (3) key residual, (4)/(d3) guarded ord tie, the (d1)/(d2) block at
  j = 1 keys (including e·g = 1 refinement reads), AND the total-form faithfulness
  (U14's gate). Predictions, preregistered: 0 violations on every clause EXCEPT
  possibly the total form (unknown — that is what the gate decides); any march-clause
  violation refutes (GR-B)(2′) as stated and stops §1.3 S5/S6.
  **[EXECUTED 2026-08-08: ALL GREEN — 40 towers, 33,547 samples, 15 families incl.
  PARI (e,f) oracle; TOTAL FORM 0/2,400 ⟹ U14's gate DECIDES POSITIVE (U14 may be
  stated). Headline side-finding: the GRB leaf's Def-3.15 ǫ quote is an extraction
  artifact (true exponent ǫᵢ(α) = zᵢ^{ℓ′ᵢs−ℓᵢu}, triple-pinned incl. a PARI
  kill-shot); S3.2's geometric-discrepancy law refuted against the true operator
  (at e₀ = 1, FGMN = GMN on the nose) — GRB display fold owed. Record: GRB note
  §N-1 EXECUTED.]**
* **N-2 (`gemit_conformance_check.py`)** — the G-EMIT/U6 gate (O-2a rev 4 §4's named
  falsifier home): instrument depth-≥ 2 runs; emitted record == stage read recomputed
  over Θ(emitted prefix), per level; 0 violations predicted; any violation refutes the
  construction-conformance route for (c) and re-opens it as genuine mathematics.

### 5.5 Wave order (dependencies; parallel within a wave)

| wave | units | blocked by |
|---|---|---|
| W0 | A-M1 faithfulness-brief consolidation (§1.2 → the GRB leaf's §S0); N-1; N-2; Lean U1–U4 (Defs) | — |
| W1 | Lean U5, U6, U7; A-M2 = GRB_order2 attempt+brief (§1.3) | U1–U4; A-M2 also N-1 green |
| W2 | B-M1 = KPSTEP attempt+brief (§2.2); Lean U8a–c, U9; C-M1 (abstract OL-2a-6, §3.3(i)) | A-M2 (structure clause consumed). [REV 2, finding 11:] U8b runs AGAINST the displayed `DevBound` hypothesis row as STAGING; this discharges NOTHING — member (b)'s retirement requires OP-B1 PROVED (the row derived), §6 |
| W3 | D-M1 = KEY1SITE note (§4.2); B-M2 = the OL-1 family clause (§2.2 s7) **[EXECUTED 2026-08-06 as the engine-lift conformance unit — REV 4 record below]**; Lean U10, U11, U12; U14 (gated) | B-M1 **[VERIFIED 2026-08-06, 2-clean]**; U14 gated on N-1's total-form verdict |
| W4 | Lean U13 (wired conformance); hostile passes on A-M2/B-M1/D-M1/C-M1 (Codex, fresh context, 2-clean bar each, sequential per the fleet throttle) | W2/W3; U13 also N-2 green |

Unit count: 4 math leaves (A-M2, B-M1(+B-M2), C-M1, D-M1) + 14 Lean units (U1–U14)
+ 2 numerics gates + 1 brief consolidation = 21 units.

---

## 6. Retirement conditions (what exactly flips the §3.1 row) and honesty invariants

* **(a)** retires its [M] face when GRB_order2's brief passes 2 consecutive fresh
  hostile passes (the GD23-cycle bar) — the row's residue then = its named [V] pass
  debts + the standing [T] pins (properness at FGMN Lemma 5.3; the S-1 transcription
  audit). The TR-1..TR-7 discharges are IN the brief (TR-7 = the clause-(1)
  carry-wrap derivation, REV 2 finding 4), so no transcription residue survives
  outside [T]; if S5's 𝒟-clause proof fails, (a) retires MINUS a displayed open
  sub-member (OP-A2's REV-2 rule), not in full.
* **(b)** retires when KPSTEP + the family clause pass the same bar, WITH OP-B1
  PROVED — the `DevBound` row derived, never assumed [REV 2, finding 11: a
  DevBound-conditional U8b is staging, not discharge]; its OL-1 consumption sites
  (O-2a Theorem 2, Steps 10–12) fire unchanged because §2.2(s7) emits OL-1 verbatim.
* **(c)** retires when BOTH legs land: C-M1 (abstract, passed) + H1-U13 green with N-2,
  with the S-1 [T] bridge cited — never by the route alone.
* **(d)** retires when (a)+(b) have retired AND KEY1SITE passes with its FOUR §4.2
  obligations (coverage, site-to-tower reading, the eg = 1/OP-B1 corner, run-to-anchor
  identification) + the WGEO delivery shape — Step 6's conditionality line then cites
  the KEY1SITE leaf instead of (H1)(d).
* **Row-level:** the (H1) §3.1 row is edited only at a ROOT revision with the ledger
  updated; the composed theorem's (ROOT-C) display drops (H1) only when all four flip.
  Lean units NEVER substitute for the math passes (the corpus face is evidence of
  statement-shape and non-vacuity, not of the paper proofs). [REV 2, finding 12 — the
  sorry discipline, corrected:] hypothesis rows are consumed ONLY as explicit
  structure/def binders; NO sorried instance of a row is ever landed (a `sorry`-backed
  theorem carries `sorryAx` and satisfies consumers as if proved — the opposite of
  hypothesis-grade); prover-branch sorries never reach the corpus path, and the AxChk
  zero-`sorryAx` census is the standing gate.
* **Failure modes to watch (from this group's own history):** V26-2 (slot-fresh
  reading — refuted 1,818×; any march statement must carry the anchored march
  IN-STATEMENT); V28-1 (mixed two-form pairing — the ȳ^{j₀} discrepancy); V26-1
  ((KPirr) is NOT free with (KPa)); P2-1/V14-1 (unbound chain parameters at engine
  seams — (c)'s statements bind c = Θ(prefix) explicitly); VC8-1 (never identify key
  degree with read order).

---

## 7. Codex adversarial review + fold record (the directive's verification step)

**Pass 1 (2026-08-05, fresh-context Codex, full blueprint pasted; report archived
verbatim at `lean/notes/openmath/H1_bp_review.md`): BLUEPRINT-UNSOUND — 9 critical /
6 gap.** All 15 findings folded IN PLACE the same day (this file = REV 2); each
edit is tagged `[REV 2, finding N]` at its site. Dispositions:

| # | class | finding (compressed) | disposition |
|---|---|---|---|
| 1 | CRIT | §0/§2.2 tower indices incompatible — (KP)_{j+1} in gr(w_{j+2}) needs the structure the ladder obtains only later | **ACCEPTED — the deepest catch.** §0 ladder REWRITTEN: (GR-B) split into (GR-B-STR) (chain-data clauses, inputs (KP)_{≤ i−1}) and (GR-B-KEY) (state-key clauses (3)/(4), input (KP_i)); KP-STEP re-indexed to prove (KP)_i IN gr(w_{i+1}); §2.2 statement + (s1)–(s6) re-indexed to match |
| 2 | CRIT | §2.2(s6) offers a circular (KPb) route ("(GR-B)(3) at the NEXT state") | ACCEPTED; the alternative DELETED — s6 is the direct computation only, with its consumed inputs displayed |
| 3 | GAP | "MacLane Thm 4.2" unpinned / possibly misattributed | REBUTTED WITH DISPLAY: MacLane 1936 Thm 4.2 IS the augmentation theorem — GD23 §2's pin (ML), scope cleared at LITUNIT §3, corroborated by FGMN Prop 1.9's printed cite "[10, Thms. 4.2, 5.1]"; the reviewer's four corners lacked the (ML) pin (my prompt omitted it). §0 now disambiguates the two Thm-4.2s in place |
| 4 | CRIT | §1.2 clause (1) mispriced: Lemma 5.13 carries a properness hypothesis; the total clause is not discharged by the cited pins | ACCEPTED; clause-(1) row re-priced — Lemma 5.13 demoted to corroboration; NEW obligation **TR-7** (= OP-A4): the total multiplicativity carry-wrap derivation via eq (12)/(16) exponent arithmetic, written in S6a. Latent-gap flag recorded: GD23's own (GR-B)(1) citation line carries the same over-pricing — to be repaired at the GRB write-up, leaf verdicts untouched ((GR-B) was OPEN there) |
| 5 | GAP | clause (3) is polynomial-vs-graded, not a literal Cor 5.6(2) match | ACCEPTED; TR-4's scope now names clause (3) explicitly (S6 edit) |
| 6 | GAP | carry-algebra clause has no printed home; "prove or drop" underpriced | ACCEPTED; OP-A2's drop-escape RETRACTED — failure makes it a displayed open sub-member of (a); proved in S6a alongside TR-7 (same computation) |
| 7 | CRIT | KEY1-SITE omits the run data needed for (d3) | ACCEPTED; §4.2's implication gains the REALIZED-READ DATA hypothesis (math: (R1)/(R2)+REALIZED; Lean: SideReads(iii)'s HasAnchorK + ν.hOrd), obligation (iv) added |
| 8 | CRIT | `GrBKeyLaws.faithful` over-quantifies (≈ total Cor 5.15, no ν↔σ′ compatibility); consumption lemma missing | ACCEPTED; row restructured: link fields (link_e/h/prev/key) added; `faithful` → `faithful_at` (recorded-site form at (ν.a, ν.Ranch, ν.μ)); the total form demoted to gated H1-U14; the SideReads-keyed consumption lemma added to U10. Re-probed compile-clean |
| 9 | CRIT | §4.2–4.3 "no new mathematics" underprices refinement-site content | ACCEPTED; retitled "no new VALUATION THEORY; four genuine assembly obligations" (coverage, site-to-tower reading, eg = 1/OP-B1 corner, run-to-anchor identification), each displayed |
| 10 | CRIT | `kp_step` omits its mathematical hypotheses; "prover discretion" not content-preserving | ACCEPTED; statement enlarged (hprev + DevBound binders; M's Θ/isLoc/discharge displayed as (GR-B-STR)'s Lean face); the discretion line WITHDRAWN; re-probed |
| 11 | CRIT | DevBound-conditional U8b masquerades as discharge | ACCEPTED; wave table + §6(b) now state: DevBound is staging only; member (b) retires only with OP-B1 PROVED |
| 12 | CRIT | sorry-backed rows contradict hypothesis-never-axiom | ACCEPTED; U9 landing rule rewritten (no sorried row instances EVER land; explicit binders until the math passes; AxChk zero-sorryAx gate); §6 sentence corrected |
| 13 | GAP | `keys_exist_of_run` cannot be "inverted" | ACCEPTED; route deleted; U13 = direct induction on the wired builder with named probe duties |
| 14 | GAP | primeness-after-localization needs an avoidance invariant | ACCEPTED; (s4) split into (s4a) localization avoidance + (s4b) UFD argument; U8a carries it |
| 15 | GAP | OL-1's monicity/degree/V-recursion not derivable from the block alone | ACCEPTED; §2.2(s7)/B-M2 expanded to a displayed induction statement with per-clause inputs |

**REV 3 (2026-08-02, single-site sync):** the GRB leaf's REV-5 (H-CHAIN) range
correction (GRB_ORDER2 §R5.2, pass-4 gap 2, verifier-confirmed at pass 5) is
synchronized into §1.3's (OP-A3) — member (b)'s consumed chain condition now
displays the full range 0 ≤ j ≤ i−1 (nonempty at order 2), retiring the owed
blueprint sync recorded at the leaf's R5.2. No other content touched.

**Standing after the fold:** REV 2 carries all repairs in place; the two REBUT-class
items (3, partially) are display-only. The blueprint's next gate is a FRESH Codex
pass on the REV-2 text (the fold is my own edit — same-context self-review does not
advance the bar); that pass rides the wave-0 dispatch. Codex budget at review time:
2% of the 7-day window.

**REV 4 (2026-08-06, unit records — additive only, no spec text changed):**
* **B-M1 VERIFIED (2-clean, model-diverse):** `lean/notes/openmath/H1_BM1_2026-08-06.md`
  REVISION 3 — pass 3 (Codex) CLEAN + pass 4 (Fable) CLEAN. Theorem KP-STEP holds at
  the degree-conformant class (K0)+(K1)+(K2) (the REV-2 restriction; consumer
  alignment displayed at its §S8); OP-B1 PROVED there (fixed bound; minimality
  (K0)-gated). Deviations from this blueprint's §2.2 sketch (all recorded in the
  leaf): (s4a) localization-avoidance VOID (FGMN Thm 4.13 presents Gr(µ) itself);
  FGMN Prop 5.7 REJECTED as the (s5) pin (key-equivalence, not the low-degree
  block) — the direct fallback route executed; DEVID parent-level consumption
  evaporates (development-form weights definitional).
* **B-M2 EXECUTED (wave 3, the engine-lift conformance unit):**
  `lean/notes/openmath/H1_BM2_2026-08-06.md` (Theorem LIFT-CONF — every lift the
  wired engine fires is (SL-top)-shaped with marched (SL-dev) DATA [definitional,
  D8 `IsReadLift`] and (K0)-conformant [theorem: shape + `Stage.hmonic`]; OL-1
  per-clause assembly: (a) DISCHARGED, (c) supplied by B-M1 §S3.2 on the class,
  (b) conditional on the graded-reading seam + TR-3-ORD-X) + compiled corpus face
  `lean/LeanUrat/Scaffold/HDischarge/H1/Conformance.lean` (sorry-free, per-file
  gate clean: `K0Conformant`, `isReadLift_K0` [PAR-MON's step, the read-pair
  transport of `Moves/L3_liftMonic`], site corollaries at `IsNodeLift` /
  `LandingKey` / `HistoryCoherent` both legs / `ReadsOf`). NOTE: this lands a
  `Scaffold/HDischarge/H1/*.lean` file — the §0 rule (ii) blueprint-only fence
  bound the BLUEPRINT unit itself and expired with the prover fan-outs (Defs/
  Order1/TowerStep/SiteBlock/RunBinding already landed at waves 0–2). Residue
  per the unit's §S4: its own 0/2 bar; the graded (SL-dev) reading (model seam,
  A-M2); S-1 [T]; TR-3-ORD-X; GRB inheritance; the `DevBound` row STANDS (its
  Lean derivation still needs the graded reading — finding-11/12 discipline
  unchanged). Member (b) retirement now waits on: B-M2's bar + the GRB leaf's
  bar (counter 0/2 at record time — pass-8 gaps folded at its rev 7).
