# FABLE FRESH-INSTANCE VERIFY — §H-DOMAINS rev 5 (2026-07-27)

Verifier: fresh Fable instance (dual bar, Codex passes 5+6 already clean).
Text: MOVES_2026-07-24.md lines 9890–10772 (§H-DOMAINS rev 5). Charge:
quote-and-classify, fix nothing; hardest on H-LIST (break attempt with own
(TRI) instance); machine-check the displayed examples + the H-n3 seal;
XHD-w walk vs C.1.5(1)/TYP(b); demand/delivery table vs V.0; fresh sweep.

## A. H-LIST break attempt (own instances, machine-checked)

**FINDING 1 — CRITICAL (H.2.2, step (4), both FIX sites). The fifth
instance-break.** Quote (floor-dominated side): "enumerate and FIX each
admissible cell-lattice tuple (finitely many; substituting constants keeps
(TRI) and the strides — step (1))". The claim "keeps (TRI)" is FALSE
whenever a FIXED coordinate itself carries an affine bound citing
still-LIVE earlier coordinates: fixing h_k = t turns h_k ≥ φ_k(h_{<k})+1
into the UPPER bound φ_k ≤ t−1 on the live coordinates — a constraint the
(TRI) data model has no slot for (class (TRI) forbids upper bounds).
Breaking instance, in class (TRI) by the rev-4/5 definition (one lower
bound per coordinate, slopes +1 ≥ 0, constants unrestricted, no upper
bounds, floors 0, no congruences):
    (E5)  y ≥ x + 1;  z ≥ y − 5   (φ_y = x, φ_z = y − 6), (x,y,z) ∈ ℕ³.
At level z the floor-dominated side ⌈φ_z⌉ ≤ −2 ⟺ y ≤ 4 is NONEMPTY
(y ∈ {1..4}); fixing y = t leaves live x with the unrepresentable upper
bound x ≤ t−1. A spec-faithful implementation (drop what the data model
cannot hold) emits STRAYS — machine-checked (/tmp/hlist_check.py): points
(x, t, z) with x ≥ t listed but ∉ S, e.g. (5, 1, 0) violates y ≥ x+1;
box-20 census: literal mode 10 pieces WITH strays, zero orphans. The same
cascade hits the slab's below-part (fixing a cited coordinate that carries
its own bound). REPAIR (mechanical, verified): transitively enumerate —
each induced upper bound confines its positively-cited coordinates to
finite ranges at STRICTLY EARLIER levels (terminates); and a slab
floor-raise on an already-affine-resolved coordinate must re-run the split
WITH THE ORIGINAL BOUND (the note's re-split sentence does say this).
With the cascade added, the four-stage construction is EXACT on (E5) and
on 400 randomized in-class systems (D ∈ {2,3}, rational slopes ≤ 3/1,
congruence unions, constants in [−6,3], floors {0,1}; box 20/24): union =
brute force, zero duplicates (disjointness), zero strays/orphans, 405/405.
SCOPE NOTE (verified): campaign adjacent-only censuses never fire the
cascade — (I-aug)'s φ ≥ 1 makes the floor side empty and the slab
threshold ≤ the floor lift (no below-part), so the GATE SEAL IS UNTOUCHED;
the break is against the LEMMA's full class-(TRI) claim, which H.3/XHD-s
consume for arbitrary in-class templates.
No further break found: steps (1)-(3), (5), (6) survived every probe
(integerization constants, tie handling — the step-(5) consistency assert
never fired in 405 runs — periods in ℕ^D, injectivity, disjointness).

## B. Displayed example resolutions (machine re-derivation)

All four displayed resolutions verified independently (/tmp, exact):
- Refuting instance (y ≥ x/2+1, x ≡ y ≡ 0 mod 2): S_x = 4 confirmed; two
  cells, bases (0,2)/(2,2), y_min = x/2+2 and x/2+1 — matches the display;
  union = brute force, disjoint.
- (E3) (y ≥ x/2 − 1/2): two parity cells, bases (0,0)/(1,0), y_min
  sequence 0,0,1,1,2,2 at x = 0..5 — exact, x = 0 the tie as displayed.
- (E1) (y ≥ x−2): three pieces, bases (0,0),(1,0),(2,0) — exact, disjoint.
- (E2) (y ≥ 1−x, out-of-class display): the three displayed pieces
  partition {y ≥ max(0, 1−x)} exactly (brute force, box 20).
Gate family: H-LIST emits exactly L((1,3);{(2,4),(0,2)}) ⊔
L((2,5);{(2,4),(0,2)}); displayed lists = brute force on box 40, disjoint;
coarse set L((1,3);{(1,2),(0,2)}) = the union; the coarse bijection
n₁ = h₀−1, n₂ = (h₁−2h₀−1)/2 is integral/nonneg on every census point.

## C. Gate H-n3 seal recomputation (all confirmed; gate stays UNRUN)

- E walk re-added per (b)'s pin roster: 3h₀ + (h₁−2h₀) + ((h₁−1)/2 − h₀)
  = (3h₁−1)/2, h₀-free — confirmed; census E = 4, 7, 7, 10, 10, 10 at the
  six sealed points; w_E = (0, 3/2); margins ⟨w_E,(1,2)⟩ = ⟨w_E,(0,2)⟩ = 3,
  ⟨w_E,(2,4)⟩ = 6, all ≥ 1 (E-POS display stands; h₀-weight exactly 0).
- Ladder: exponent identity (3h₁−1)/2 − k = h₀+h₁ (k = (h₁−1)/2 − h₀)
  verified symbolically over the domain; independent elementary crosscheck
  at (1,3), p = 3: full digit enumeration of {v(β)=1 pinned-u, v(δ)=3 free
  nonzero} gives 4/81 = T·q^{−E} = 4·3^{−4} exactly — an independent
  numerical confirmation of the walk's scale/direction conventions.
- T = (p−1)²: 4 at p=3, 1 at p=2; determination N = h₁+1 → caps O(2⁸)
  (max h₁ = 7) and O(3⁶) (max h₁ = 5) — both correct.
- Component list + coarse bijection: machine-exact (section B).

## D. XHD-w derivation vs §C C.1.5(1)/TYP(b) (walk verified)

- Conditioning direction correct: C.1.5(1) displays mass(Σ_i ∩ stratum) =
  mass(Σ_i)·vol_nom(E_fresh); H.1.1 consumes it as the conditional mass of
  ONE fresh assignment given Σ_i — same direction, no inversion.
- Hypotheses carried verbatim: realizable prefix ((NA)+(HV)+(SAE), rev 12/
  13) + (ZC) + TRANSITION-ADMISSIBLE read — all three appear in XHD-w-FIX.
- Species intervals match C.1's census exactly: (α) OPEN strip + on-lattice
  digit at new(j) (whole content zeros at off-lattice slots); (β)/(γ)
  HALF-OPEN (old, new], zero pin at top, no value digit; (γ) implied at
  and beyond j×; non-adjacent endpoint strip + nonzero digit fresh.
- (w-3) matches C.1: E_inh implied per species; adjacent hinge = (HV) data
  identity pinning nothing (emptiness excluded by transition-admissibility);
  "(NA)/(SAE) equations of NO E" is C.1(ii)'s three-data-conditions clause
  verbatim; rim no-fresh-pin is C.1's rim bullet verbatim.
- TYP(b): additive surjection → equal-size kernel cosets → |𝔸|^{−1}, 𝔸 =
  piece-map image (attainable, D.3(e)(i)/(ii)) — consumed exactly; AUD-E's
  no-F_Q-module-structure quote matches TYP's rev-11 typing verbatim.

## E. Demand/delivery table vs V.0 (item-by-item: faithful)

All six rows checked against V.0's displayed package: no clause silently
weakened; every divergence carried in the row (per-period positivity;
per-component E; TRI-only lists; count faces fenced; factorization not
addressed; (ENT-U) conditional). (ENT-U)'s spec is per listed linear set
in §V (V.5(3), owner [2b] M4b) — H.4.4 delivers exactly that form, and
INIT-RAT indeed sums per component (no cross-component claim needed).
V.5(1) assigns (XHD-u) to [2b] — H.0's charge line accurate. H.6's kernel
list = exactly the six fences named in the body + the three SPEC-SYNC
flags, each of which appears at its body site. "[1v]-FULL CANNOT BE
RECORDED" present and consistent with the open fences. No mismatch.

## F. Fresh sweep

- Gate slope justification checked: (I-aug) φ = e₁e₀h₀g₀ gives slope 2 at
  the gate — matches H.2.2's campaign-justification numbers.
- H.1.2(ii-a)'s admissible-lattice typing is sound (integer-valued E per
  class + strict growth ⟹ increment ≥ 1); no raw ≥ 1 consumed anywhere.
- Bézout claim (t^B constant per (C1) class) correct: t^B ≡ h_i^{−1} mod e_i.
- H.2.3 tag discipline correct: NO ORPHAN needs no (C3) tag (forward
  direction); NO STRAY carries [GIVEN M4b-T-AUD] at the hinge — right way.
- COSMETIC: H.1 statement "E equals the per-assignment C.1.5 fresh-volume
  ratio" — E is the negated log_q of the ratio (the displayed monomial
  q^{−E} is correct; wording only).
- H.0 proof-order compliance spot-checked: H.1–H.4 cite only §C/§B2-DEF/
  B1.1/D.4-D.10/M4a/M4b-T(tagged); no CTS-M G-clause found before H.5.

## VERDICT: NOT CLEAN — 1 CRITICAL, 0 gaps, 1 cosmetic note

The critical is Finding 1 (H.2.2 step (4): the FIX steps' "keeps (TRI)"
claim fails on in-class bound-chain systems with nonempty enumeration
sides; instance (E5), machine-checked strays; repair identified and
machine-verified exact on 405 systems). Localized: no other clause of the
note consumes the broken step for the gate family or any adjacent-only
template (cascade provably never fires there), and the lemma's CONCLUSION
survived every repaired-construction probe — but the PROOF as displayed is
wrong on class (TRI), which is exactly the delivery H.2.2/H.3 claim.
Divergent from Codex passes 5+6 (clean on identical text); the instance is
concrete and reproducible (/tmp/hlist_check.py, literal vs cascade modes).
