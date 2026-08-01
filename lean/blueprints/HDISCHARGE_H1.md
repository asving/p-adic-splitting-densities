# HDISCHARGE_H1 — discharge blueprint for (H1): the graded-dictionary open family at OM orders ≥ 2

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

**The architecture in one display (the tower induction).** All four members hang on one
well-founded ladder, indexed by state order j+1 (base j = 0 proved = GD23):

    (V1)_{≤ j+1} + (KP)_{≤ j}                        [induction state]
      ⟹ (GR-B)_{j+1}                                 [member (a): FGMN retarget]
      ⟹ (KP)_{j+1} at the standard lift              [member (b): KP-STEP, door 1]
      ⟹ (V1)_{j+2}                                   [GD23 §5: BRIDGE + MacLane Thm 4.2,
                                                       ON FILE — reuse, not re-proved]
    (d) = the (KP)_{i+1} block + GD3-MIN read off at every realized order-≥ 2 site
    (c) = engine-side run/read binding — parallel strand, no dependence on (a)/(b)

No circularity: (GR-B)_{j+1} is a statement about gr(w_{j+1}), which exists once
(V1)_{j+1} holds; (KP)_{j+1} feeds only (V1)_{j+2}. The base of everything is the
proved order-≤ 1 layer (GD23 Theorems GAUSS-g/VAL-g/KEY-g/RES-1, any d₀, any complete
DVR O).

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
| (1) | **Thm 4.2** (H_µ, ϕ_r multiplicative; via Lemma 4.1/Cor 2.7) + **Lemma 5.13** (R(gh) = R(g)R(h), g µ-proper) | multiplicativity up to K_i^× — the unit twist θ_{α,β} is OURS to carry, the printed identity is exact in its own normalization |
| (2′) | **Thm 4.2** verbatim: "H_µ(g) = ϕ_r(α)R_{r,α}(g)(y_r) = ϕ_r(g)R_r(g)(y_r)" + **Cor 4.4(2)(3)** slot granularity | the anchored-march identity, BOTH pairings; exact-match check against the printed two-form EXECUTED and displayed at GD23 §7.2 rev 3 (V28-1) — the retarget pass re-verifies it, never re-derives it |
| (3) | **Cor 5.6(2)** verbatim: "R_i(φ_{i+1}) = ψ_i, the minimal polynomial of z_i over F_i" | (KPb) transported; reads the extended chain — properness-proviso territory shared with (4) |
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
Cor 5.15 + Lemma 5.13, with (2′)'s two-form pairing check re-verified against the
GD23 §7.2 display and TR-6 cited at (3)/(4); (S7) the order-1 instance cross-check —
the composed statement must REPRODUCE GD23's proved order-1 display (in(f) =
ϕ·R_λ(f)(ȳ) with ȳ = Φ̄₀^e π̄^{−h}, e_b = 1, 𝒟 = K₀) verbatim, the non-vacuity gate of
the whole retarget; (S8) honesty ledger + attack list.
**Honest open points, named now:** (OP-A1) TR-2's rescaling lemma is unwritten (easy
but load-bearing); (OP-A2) the 𝒟-realization clause has no printed home — it is OUR
gloss of Thm 4.8/Cor 4.9's sub-step structure and must be PROVED from them in S5, else
dropped from the package statement (it is consumed by [F.2]'s reading, so dropping it
re-opens an engine-seam obligation — flag to the verifier); (OP-A3) FGMN state their
operators for a MacLane chain of µ — our tower reaches w_{i+1} through the policy's
chain; that the policy's chain IS a MacLane chain of w_{i+1} is (KP)-territory
(member (b)), consumed as the induction state, and the write-up must display this
dependence rather than silently assuming it.

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
homogenization argument transported one level up).** Statement: fix the induction
state ((V1)_{≤ j+1}, (KP)_{≤ j}, (GR-B)_{j+1}); let the order-(j+1) read (GD23 §1.2
indexing: performed at the frame (Φ_{j+1}, w_{j+1}, K_{j+1})) carry (e, h) := 
(e_{j+1}, h_{j+1}) coprime ≥ 1 and ψ := ψ_{j+1} ∈ K_{j+1}[z] monic irreducible of
degree g ≥ 1 with ψ(0) ≠ 0 [TR-5 line displayed at the unit]; let Φ_{j+2} :=
Σ_κ ψ̂_κ·M_κ be the standard key lift (ψ̂_κ the coefficient lifts, M_κ the marched
monomial normalizers from (GR-B)(0′)). Then (KPa)+(KPirr)+(KPb) hold at j+1.
Proof plan, section-by-section (each a numbered section of the unit note
`KPSTEP_attempt.md`):
* (s1) *The marched homogenization.* hom^m_{e,h} : K[z] → gr(w_{j+2})-candidates,
  c(z) = Σ c_κ z^κ ↦ Σ [ĉ_κ]·ϕ·ȳ^κ-shaped sums — multiplicative and injective. Inputs:
  (GR-B)_{j+1}(0)/(0′) (Δ = K[ȳ] polynomial ring: injectivity; anchor invertibility +
  march linearity in κ: multiplicativity — exponents add slot-wise as at order 1).
* (s2) *Weight/degree bookkeeping of the standard lift.* Every nonzero monomial of
  Φ_{j+2} at one w_{j+2}-weight; in(Φ_{j+2}) = hom^m(ψ) up to the anchor unit — the
  (KPa) initial-form identity. Input: DEVID at the state (GD23 §4, on file, consumes
  (V1)+(KPa) one level down) for the development weights.
* (s3) *Factor collection.* Every homogeneous δ ∈ gr(w_{j+1})-localized factors as
  (invertible anchor monomial)·hom^m(c) with c(0) ≠ 0. Input: (GR-B)(0′) + Thm 4.2's
  rank-one statement (P_α/P_α⁺ = ϕ_r(α)Δ free of rank one) — the order-1 proof's
  "collect the least Φ̄₀-exponent" step, with (π̄, Φ̄₀)-monomials replaced by the anchor
  system.
* (s4) *Primeness.* ψ irreducible in K[z] ⟹ hom^m(ψ) prime: the order-1 UFD argument
  runs verbatim in Δ-localized = K[ȳ][anchors^{±1}] (weighted UFD via (0)/(0′));
  suppose hom^m(ψ) = δδ′, collect anchors, use injectivity + irreducibility. This is
  (KPirr) at j+1 — the clause V26-1 taught us is a genuinely additional input, so it
  gets its own section, not a remark.
* (s5) *Degree block.* deg_x B < deg Φ_{j+2} ⟹ ψ̂_hom ∤ in(B). The order-1 proof used
  the slot bound "top Φ₀-slot < eg". At order j+1 the corresponding step is the
  ȳ-degree comparison: **(OP-B1, the honest open point of door 1)** deg_x B <
  deg Φ_{j+2} bounds the ȳ-degree of in(B) below eg — the graded shadow of MacLane's
  minimal-degree clause. Candidate printed supply: FGMN §5's key-polynomial minimality
  characterizations (Prop 5.7's equivalent forms) — pin TO BE VERIFIED against the
  extraction (do NOT cite a numbered clause until re-read; the LITUNIT discipline).
  If no printed form matches, (s5) is proved directly from the development structure
  (DEVID + slot bookkeeping at the state), the same shape as order 1 — expected
  mechanical but MUST be written.
* (s6) *(KPb).* R_{j+1}(Φ_{j+2}) ∼ ψ_{j+1}: read (s2)'s initial form through
  (GR-B)(2′)/(3)'s operators. Input: (GR-B)(3) at the NEXT state or the direct
  computation from (2′) — the unit picks whichever composes without consuming the
  properness leg at a degree-increasing site (automatic there, TR-6).
* (s7) *The family clause.* The per-level blocks assemble into OL-1's joint statement:
  clause (b)'s "type over F_rep" is well-defined level-by-level exactly because the
  induction is cumulative (P2-4's display); clause (c)'s V-recursion is (s2)'s weight
  arithmetic. Output shape = OL-1 verbatim, so O-2a's Theorem 2 consumption fires
  unchanged.

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

**4.2 The assembly theorem (KEY1-SITE) — no new mathematics beyond (a)+(b).**
(d1)+(d2) at a site = member (b)'s (KPa)+(KPirr) at the site's creating read (KP-STEP's
conclusion instantiated); (d3) = GD3-MIN at the site, whose route B is proved FROM
(GR-B) at GD23 §7.3 (on file, general order). So:

    KEY1-SITE: (GR-B)_{i+1} + KP-STEP at the site  ⟹  (d1)–(d3) there.

The unit note `KEY1SITE_attempt.md` proves this as a two-page assembly with three
displayed checks: (i) *coverage arithmetic* — sites keyed by READ ORDER; the proved
slice is exactly order ≤ 1 (GD23 + O-1thr (V1)/(V2) there); the theorem covers the
complement; NO key-degree/order identification is consumed anywhere (the VC8-1
lesson, restated as a check the verifier must tick); (ii) *the e·g = 1 corner* —
KP-STEP's proof pattern covers refinement reads (at order 1, KEY-g allows eg = 1:
ψ = z − c, Φ₁ = Φ₀ + ĉπ^h; the marched analogue is Φ_{i+2} = Φ_{i+1} + ĉ·M₀), and the
properness proviso enters ONLY (d3) via (GR-B)(4), consumed as the §3.3 [T] pin —
displayed, one home; (iii) *the WGEO delivery shape* — the block is emitted in
O-1thr rev 4's exact consumed form ((V2a): unit·ψ̂_hom + the degree block with the
"deg B < eg ⟹ x̄-degree < eg" bridge sentence; (V2c): first-attainment ord tie), so
WGEO and Theorems 1–3's all-site scope fire with NO restatement. Dependence display:
(d) retires when (a) and (b) land and KEY1-SITE passes — it is the SITE-INSTANTIATION
face of the group, priced separately by ROOT only because Step 6 consumes it in this
shape.

**4.3 What (d) adds beyond (a)+(b), exactly.** Two things only: the site
quantification (every REALIZED site of Step 6's machine — a machine-side notion, so
the note must consume O-1thr's realized-state vocabulary, not invent one) and the
delivery-shape conformance (4.2(iii)). Both are assembly, not new mathematics — but
both are exactly where VC7-1/VC8-1 found the consumed-without-a-home defects, so they
are WRITTEN, not waved.

---

## 5. LEAN UNIT SPECS (all compile-probed 2026-08-05; target `lean/LeanUrat/Scaffold/HDischarge/H1/`; namespace `LeanUrat.Scaffold.HDischarge.H1`)

Probe record: the §5.1 statements compiled verbatim against the built corpus (single
scratch file, `lake env lean`, clean; only `kp_step`'s intended `sorry` warned).
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

/-- H1-U3 — (GR-B) clauses (3)+(4) keyed to the creating read ν (MovesC.Node: ν.σ the
parent stage, ν.ψ the residual factor over ↥ν.σ.K) and the state model. `key_res` =
(KPb)/clause (3) in the corpus's Laurent normalization (unit = C c · T^k); `faithful` =
(d3)'s consumed face, GUARDED by the anchored-frame-residual tie (`HasAnchorK` at the
per-f witness (a, Rf)) — the U31-adjudicated rendering of "f is read on ν's side";
the TOTAL (Cor 5.15) form is the H1-U14 extension, gated by numerics N-1. -/
structure GrBKeyLaws (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (KB : KPBlock σ' M) : Prop where
  key_res : ∃ (c : (↥ν.σ.K)ˣ) (k : ℤ),
    ν.σ.R σ'.Φ = LaurentPolynomial.C (c : ↥ν.σ.K) * LaurentPolynomial.T k *
      Polynomial.toLaurent ν.ψ
  faithful : letI := M.Rg.ring; ∀ (f : Polynomial ℤ_[p]) (a : ℤ) (Rf : Polynomial ↥ν.σ.K),
    f ≠ 0 → HasAnchorK (ν.σ.R f) a Rf →
    ∀ μf : ℕ, OrdPsiPoly ν.ψ Rf μf ↔
      (KB.ψhom ^ μf ∣ M.S.initialForm f ∧ ¬ KB.ψhom ^ (μf + 1) ∣ M.S.initialForm f)

/-- H1-U4 — the (H1)(d) site block: what Step 6's Lean consumers fire per order-≥ 2
site. Site-realization is the CONSUMER's predicate (Step-6 wiring supplies it);
membership here is by the (ν, σ', M) data alone — read order, never key degree. -/
def Key1SiteBlock (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') : Prop :=
  ∃ KB : KPBlock σ' M, GrBKeyLaws ν σ' M KB
```

Difficulty: LOW (statements only; land with docstrings citing this blueprint's §1/§2/§4
and the §3.1 row). Semantic-guardian flag: `GrBKeyLaws.faithful`'s guard choice is the
E-PHASE-flagged σ.R-rendering of the frame residual (HC2 `SideReads` (iii) note) — the
same convention U31's gate adjudicated; any strengthening to the total form goes
through H1-U14's falsifier gate first.

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

* **H1-U8 (`kp_step`)** — HARD (the door-1 core; math source §2.2 KP-STEP). Probed
  statement shape:
  `theorem kp_step (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
  (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h) :
  Nonempty (KPBlock σ' M)` — staged as U8a (primeness transport: `Irreducible ν.ψ` →
  `Prime ψhom` via Θ/`isLoc`; the (s3)/(s4) content), U8b (degree block from the
  development bound; the (s5)/OP-B1 content — carries a displayed `DevBound` hypothesis
  row until OP-B1's math lands; row shape:
  `structure DevBound (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ') : Prop
  where bound : letI := M.Rg.ring; ∀ B : Polynomial ℤ_[p], B ≠ 0 →
  B.natDegree < σ'.Φ.natDegree → <ȳ-degree reading of M.S.initialForm B through M.Θ>
  < ν.e * ν.g` — the ȳ-degree reading is fixed at E-phase through Θ's codomain
  (`LTwo ↥σ'.K`); INTENT-ONLY sketch, NOT probed, E-PHASE-FLAGGED (the one displayed
  non-verbatim row of this blueprint), U8c (assembly). U8's hypothesis block may need enlargement to
  `TransitionCoreL`-linked pairs (probed arity:
  `TransitionCoreL σV σ' Φhat e' h' zbar`) — prover discretion, content-preserving.
* **H1-U9 (`grbKeyLaws_step`)** — HARD. (GR-B)(3)/(4) at the state from the math
  leaf (§1.3 S6): Lean face constructs `GrBKeyLaws ν σ' M KB` from the model's
  `discharge` + `key_res` inputs; until GRB_order2 passes, lands as a sorry-statement
  behind the row (never an axiom).
* **H1-U10 (`key1SiteBlock_step`)** — LOW. `Key1SiteBlock` from U8+U9 (the KEY1-SITE
  assembly, §4.2).
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
  conformance — the engine's emitted records ARE stage reads; Lean pattern:
  `keys_exist_of_run`'s extraction inverted, or direct induction on the wired run
  builder). Falsifier N-2 must be green BEFORE this unit is attempted.
* **H1-U14 (`faithful_total`)** — MEDIUM, GATED. The total (Cor 5.15) strengthening of
  `GrBKeyLaws.faithful` (drop the recorded-side guard): stated only if N-1's total-form
  check runs 0-violation at order-2 samples; otherwise the guarded form stands and this
  unit is CLOSED-NEGATIVE with the harness citation.

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
* **N-2 (`gemit_conformance_check.py`)** — the G-EMIT/U6 gate (O-2a rev 4 §4's named
  falsifier home): instrument depth-≥ 2 runs; emitted record == stage read recomputed
  over Θ(emitted prefix), per level; 0 violations predicted; any violation refutes the
  construction-conformance route for (c) and re-opens it as genuine mathematics.

### 5.5 Wave order (dependencies; parallel within a wave)

| wave | units | blocked by |
|---|---|---|
| W0 | A-M1 faithfulness-brief consolidation (§1.2 → the GRB leaf's §S0); N-1; N-2; Lean U1–U4 (Defs) | — |
| W1 | Lean U5, U6, U7; A-M2 = GRB_order2 attempt+brief (§1.3) | U1–U4; A-M2 also N-1 green |
| W2 | B-M1 = KPSTEP attempt+brief (§2.2); Lean U8a–c, U9; C-M1 (abstract OL-2a-6, §3.3(i)) | A-M2 (structure clause consumed); U8b also OP-B1 or its DevBound row |
| W3 | D-M1 = KEY1SITE note (§4.2); B-M2 = the OL-1 family clause (§2.2 s7); Lean U10, U11, U12; U14 (gated) | B-M1; U14 gated on N-1's total-form verdict |
| W4 | Lean U13 (wired conformance); hostile passes on A-M2/B-M1/D-M1/C-M1 (Codex, fresh context, 2-clean bar each, sequential per the fleet throttle) | W2/W3; U13 also N-2 green |

Unit count: 4 math leaves (A-M2, B-M1(+B-M2), C-M1, D-M1) + 14 Lean units (U1–U14)
+ 2 numerics gates + 1 brief consolidation = 21 units.

---

## 6. Retirement conditions (what exactly flips the §3.1 row) and honesty invariants

* **(a)** retires its [M] face when GRB_order2's brief passes 2 consecutive fresh
  hostile passes (the GD23-cycle bar) — the row's residue then = its named [V] pass
  debts + the standing [T] pins (properness at FGMN Lemma 5.3; the S-1 transcription
  audit). The TR-1..TR-6 discharges are IN the brief, so no transcription residue
  survives outside [T].
* **(b)** retires when KPSTEP + the family clause pass the same bar; its OL-1
  consumption sites (O-2a Theorem 2, Steps 10–12) fire unchanged because §2.2(s7)
  emits OL-1 verbatim.
* **(c)** retires when BOTH legs land: C-M1 (abstract, passed) + H1-U13 green with N-2,
  with the S-1 [T] bridge cited — never by the route alone.
* **(d)** retires when (a)+(b) have retired AND KEY1SITE passes (assembly + coverage +
  e·g = 1 corner + WGEO delivery shape) — Step 6's conditionality line then cites the
  KEY1SITE leaf instead of (H1)(d).
* **Row-level:** the (H1) §3.1 row is edited only at a ROOT revision with the ledger
  updated; the composed theorem's (ROOT-C) display drops (H1) only when all four flip.
  Lean units NEVER substitute for the math passes (the corpus face is evidence of
  statement-shape and non-vacuity, not of the paper proofs); `sorry`-backed rows stay
  hypothesis-grade by construction.
* **Failure modes to watch (from this group's own history):** V26-2 (slot-fresh
  reading — refuted 1,818×; any march statement must carry the anchored march
  IN-STATEMENT); V28-1 (mixed two-form pairing — the ȳ^{j₀} discrepancy); V26-1
  ((KPirr) is NOT free with (KPa)); P2-1/V14-1 (unbound chain parameters at engine
  seams — (c)'s statements bind c = Θ(prefix) explicitly); VC8-1 (never identify key
  degree with read order).
