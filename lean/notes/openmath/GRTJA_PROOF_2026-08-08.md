# GRTJA — J-A, THE DICTIONARY JUNCTION: type data → tower data, the four operator equalities, and the covariance-corrected residual tie

**Unit:** J-A COMPOSER (weld dependency order: consumes W-2 clause 1 at attempt
grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S2.1/S3.1
rows W-0/W-1/W-4). **Genre: PROOF NOTE at attempt grade (acceptance counter
0/2; no gate fires; no acceptance arc opened), with sealed-runner machine
brackets** (`verification/openmath/grt_ja_checks.py`, two-commit seal).

**Grade cap (read first).** J-A-PIN (§2) is PROVED at attempt grade (its legs
are the print's own definitions plus one one-line argument), with its lift
clause consumed from W-2 clause 1 AT ATTEMPT GRADE and W-2's conditionality
carried verbatim. Of the four operator equalities (§3): (i) w = v and (iii)
ε = the print twist are PROVED unconditionally on the shared-key perimeter;
(iv) the grid/carry tie is PROVED unconditionally; (ii) the residual
dictionary is PROVED at m = 1 (= W2-L3, consumed) and at m = 2
(unconditional per-slot character-gauge law, new here), and at m ≥ 3 is
PROVED under the displayed per-digit collapse proviso — outside it the exact
law is the recursion, W-2 §3.3(c) genre. One blueprint display is CORRECTED:
the J-A(ii) "slot-independent c" form is false at m ≥ 2 (JA-BOX-1). Nothing
here fires any gate, touches any accepted text, makes any gr/carrier (J-C)
claim, or advances any density (J-D) statement.

**Literature consumption (faithfulness discipline).** The classifier side is
the GMN print `docs/references/HigherNewton.tex` ("Newton polygons of higher
order in algebraic number theory"), consumed as literature with tex anchors
per formula, through the SEALED probe transcription `grt_weld_probe.GmnLeg`
(no new print transcription in this unit; the fresh legs of the runner are
integer/geometric recomputations, not new print readings). Anchors used:
sides/slopes in lowest terms (tex 220, 828, 912); order-one and order-r type
data ψ monic irreducible ≠ y, F_r := F_{r−1}[y]/(ψ_{r−1}) (tex 829, 882);
principal polygon = negative-slope sides (tex 449, 1377); residual polynomials
never divisible by y (tex 1149); Proposition `construct` (tex 1166–1258,
hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})); Theorem `phir` + eq `vrphir`
(tex 1257–1283); the representative definition = the project's "Def 2.12"
(tex 1285); Bézout ℓ_r h_r − ℓ′_r e_r = 1 with NO pinned representative
(tex 1291); Proposition `propertiesv` items 3/4 (tex 1028); Definitions
`t(i)`/`rescoeff`/`defresidual` (tex 1431/1447/1497 and the order-one base
tex ~460/534). The FGMN print enters ONLY through the accepted N-1 base case
(§5) — a second, independent print of the same operators.

**Machine bracket:** `grt_ja_checks.py` — both sides of every §2/§3 equality
computed on the weld probe's 16-tower roster + the 5 concrete wild
polynomials (fresh QO extraction) + 4 FRESH d₀ ≥ 2 shapes (d₀ = 3 root keys
and a p = 5 row, certified through `engine_ext` per its standing rule),
LAW-KEYED with teeth. Verdict in §7 (commit 2).

---

## §1. Setting and indexing (fixed once)

Harness: the [ILN]† S0.1 class pin verbatim (DVR O, uniformizer π, reads
(e_j, h_j, g_j) for j = 0..n with e_j, h_j, g_j ≥ 1 and gcd(e_j, h_j) = 1;
normalized Bézout ℓ_j h_j + ℓ′_j e_j = 1 with 0 ≤ ℓ_j < e_j; residue chain
K_{j+1} = K_j[z_{j+1}]/(ψ_j), ψ_j monic irreducible, ψ_j(0) ≠ 0; weights
γ₁ = h₀, γ_{j+1} = e_j·w_jΦ_j + h_j, w_jΦ_j = e_{j−1}g_{j−1}γ_j; the
standard lift Φ₁, the canonical ε-corrected lifts Φ_{m+1}, the units
ε_m(β) = z_m^{ℓ′_{m−1}s − ℓ_{m−1}u} with (s, u) = eq12(β; e_{m−1}, h_{m−1}),
the level-m weights w_m and reads R_m v of S0.2). Classifier: the GMN print
objects, as transcribed in the sealed probe leg.

**The P-index dictionary** (probe pins, restated once; W-2 §1.2): GMN level
i = harness read i−1: (e_i, h_i, f_i)^GMN = (e_{i−1}, h_{i−1}, g_{i−1})^har;
ψ_i^GMN = ψ_{i−1}^har; F_i = K_{i−1}; z_i^GMN = z_i^har; ℓ_i^GMN ≡ ℓ_{i−1}^har
under (P-ell); GMN keys φ_i = harness Φ_{i−1}; GMN valuations v_i = harness
w_{i−1} (THEOREM JA-VAL below is exactly this pin proved); in particular
v_i(φ_i) = w_{i−1}Φ_{i−1} and v_{i+1}(φ_i) = γ_i^har. The GMN order-q
residual operator R_q (φ_q-adic dev) pairs with the harness level-q read
R_q v. Convention pins (P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the
probe docstring. **Shared-key perimeter at level m**: Φ_q^har = φ_{q+1}^cls
byte-for-byte for all q ≤ m−1 (all operators at level m consume only keys
that deep). The read-data quantities of W-2, reused throughout:

    A_m := ℓ_{m−1}·g_{m−1}·γ_m ∈ ℤ_{≥0}   (m ≥ 1; A_m = 0 ⟺ e_{m−1} = 1),
    W_m := w_mΦ_m = e_{m−1}g_{m−1}γ_m     (so A_m = ℓ_{m−1}W_m/e_{m−1}).

---

## §2. THEOREM JA-PIN (= blueprint W-0): the dictionary map and the class-pin membership, clause by clause

**Definition (the dictionary map T).** For a realized principal-read OM type
t of order r on a separable monic f ∈ O[x], O ∈ {ℤ_p, F_p[[t]]} — GMN data
(φ_i, λ_i = −h_i/e_i, ψ_i)_{i≤r}, f_i = deg ψ_i, φ₁ the order-0 key — set

    T(t) := ( Φ₀ := φ₁;  reads (e_j, h_j, g_j) := (e_{j+1}, h_{j+1}, f_{j+1})^GMN,
              j = 0..r−1;  residue chain K_{j+1} := K_j[z_{j+1}]/(ψ_j),
              ψ_j := ψ_{j+1}^GMN;  weights by the harness recursion ).

**THEOREM JA-PIN.** T(t) satisfies every clause of the [ILN]† S0.1 class pin
EXCEPT the lift clause, each clause forced by the print's own hypotheses:

1. **DVR base.** O = ℤ_p is the print's own base (𝒪 the valuation ring of a
   local field); the F_p[[t]] instance is the displayed equal-characteristic
   deferral (JA-BOX-4) — construction-identical, machine-covered, no PARI leg.
2. **e_j ≥ 1, h_j ≥ 1, gcd(e_j, h_j) = 1.** The print DEFINES every side
   slope as λ = −h/e "with h, e positive coprime integers" (tex 220 order
   one; tex 828 type datum; tex 912 order r). Positivity of h is the
   PRINCIPAL restriction: types are built from the principal polygon
   N_r^−(f), the negative-slope sides only (tex 449, 1377). Slope-0 legs
   never enter a type; they are dispatched by Hensel/L1 at order 0 (the
   machine-checked capstone leg), so the weld quantifies over principal
   reads only — displayed, blueprint pin honored.
3. **g_j ≥ 1.** g_j = f_{j+1} = deg ψ_{j+1}; ψ monic irreducible forces
   deg ≥ 1 (tex 829/882).
4. **ψ_j monic irreducible.** Verbatim print hypothesis (tex 829 order one,
   tex 882 order r).
5. **ψ_j(0) ≠ 0.** The print requires ψ ≠ y (tex 829/882; used again at tex
   1149: "the residual polynomials are never divisible by y, and
   ψ_{r−1}(y) ≠ y"). One line: if ψ(0) = 0 then y | ψ, and ψ monic
   irreducible forces ψ = y — excluded. ∎
6. **Residue chain.** F_{r} := F_{r−1}[y]/(ψ_{r−1}(y)) is the print's own
   definition (tex 882); under F_i = K_{i−1} and z_i^GMN = z_i^har this IS
   the pin's chain K_{j+1} = K_j[z_{j+1}]/(ψ_j).
7. **Weights.** The print's v_{i+1}(φ_i) = e_i v_i(φ_i) + h_i and
   v_{i+1}(φ_{i+1}) = e_i f_i v_{i+1}(φ_i) (Prop `propertiesv` tex 1028; eq
   `vrphir` tex 1259) transcribe under P-index to EXACTLY the pin's
   γ_{j+1} = e_j·w_jΦ_j + h_j and w_{j+1}Φ_{j+1} = e_j g_j γ_{j+1}, with
   base v₁(φ₁) = 0, v₂(φ₁) = h₁^GMN = h₀ = γ₁ (the uniformizing
   convention). Integer identity, machine family JA-PIN.
8. **THE LIFT CLAUSE (the sole exception) = W-2, consumed at attempt
   grade.** GRTW2_PROOF_2026-08-08.md supplies it in the corrected
   three-clause form: Φ_{m+1}^har is a strict GMN Def-2.12 representative
   (tex 1285) of the ξ-CONJUGATE type under the pinned (P-ell) convention
   (W2-C1, proved on the §3 perimeter there), and of the TRANSPORTED type
   t^tw strictly at every level (W2-C3, attempt grade, machine 44/44/44).
   Conditionality carried verbatim: the (C-coll)/recursion split, the §4.3
   ℓ-orbit convention fence, and W2-OPEN-1 (value layer) OPEN.

*Proof.* Clauses 1–7 are the cited definitions plus the displayed one-line
arguments; clause 8 is consumption. ∎ Grade: PROVED at attempt grade; the
Bézout normalization 0 ≤ ℓ < e is OURS not the print's (tex 1291 pins
nothing — JA-BOX-3). [Machine: JA-PIN — every clause re-verified by fresh
integer/field computations on every roster + QO + d₀ ≥ 2 level.]

<!-- SECTIONS 3-7 COMPOSED BELOW -->
— J-A COMPOSER unit, campaign date 2026-08-08.
