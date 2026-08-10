# THE w-FRAME NOTE — the cross-frame unit w and the twisted residual ψ^{(w)}, once
## RCT unit T5-w-frame-note (FABLE arm) — 2026-08-10 — grade 0/2, hostile arc follows

**Charge (blueprint T5, as amended by Plan revision R.2 S-4 re-scope).**
One citable home for the cross-frame unit w and the w-twisted realized
residual ψ^{(w)}, in the w-inclusive canonical frame, absorbing the
rider scatter: GENTOW2's (B-law)/B″ statement of w, GENTOW5's ψ^{(w)}
re-scope, the w ≠ 1 measurement records at 7 primes, and the
[GENTOW5-W(i)] fence. This note DEFINES and CONSOLIDATES; it proves no
new mathematics. Every law displayed in §2 is PROVED in the accepted
corpus and carries its source statement's S-0 ledger label (or, for
material with no ledger row, a (commit, line-range) span pin per the
R.1(a) span-pin rule). Per R.2 S-4 rules: "light" is withdrawn — §5
carries the frame-equivalence leg for each transferred fact; the
measured w ≠ 1 instances stay UNCONDITIONAL records; no absorbed
statement gains a w-hypothesis anywhere in this note (§6 audit).
This note also lands the owed "w ≠ 1 as-of note" (blueprint append
#16): §4 is that record's single home.

**Standing conditionality, named up front.** The single-w form is
unconditionally proved at level i = 2 only (the landed GENTOW2 r3
B-law). At i = 1 the SHAPE is proved with the tie u1 = w₁ OPEN
(GENTOW5 S11.3); at i ≥ 3 the form is OPEN behind the named lemma
[GENTOW5-W(i)] (GENTOW5 S11.2). §5 fences both. The T1 gauge-cocycle
frame (unit S-1) is NOT consumed here — S-1 is in flight on its own
RCT arm and unaccepted at this writing; this note is self-contained
on the accepted corpus.

**Sections.** §1 definitions · §2 the basic laws (proved, sourced) ·
§3 the level ladder (what holds at which i) · §4 the measurement
record (enumerative) · §5 open items, fenced · §6 consumption
(three-leg checks per R.1) · §7 machine leg (sealed instrument) ·
§8 as-of ledger.

---

## §1. DEFINITIONS (the w-inclusive canonical frame)

Ambient setting (the accepted towerrat frame, fixed for this note):
K/ℚ_p a p-adic base, a type chain µ₀ < µ₁ < ... < µ_i with key
polynomials Φ₁, ..., Φ_i, stage data (e_j, f_j, u_j), residue letters
z_j ∈ K_j (K_j the level-j residue field), n̂_j(m) the level-j ladder
monomial at dv_j-height m, π_{j+1} the Def 3.12 level-(j+1)
uniformizer (µ_{j+1}(π_{j+1}) = 1/e(µ_j), Lemma 3.13(1)), and
R_{j+1,β}(·) the FGMN canonical-homogeneous-frame residual read at
grade β. All symbols as in GENTOW2_PROOF (@ 33f86204) and
GENTOW5_PROOF (@ b0e5c648); nothing is re-founded here.

**DEF W-1 (the cross-frame unit w — GENTOW2's object, verbatim at
i = 2; GENTOW5's level-i quote).** At level i with next-stage data
(e_{i+1}, f_{i+1}, u_{i+1}):

    w_i := R_{i+1, κ̄_i}(n̂_i(u_{i+1})) ∈ K_i^×,
    κ̄_i := u_{i+1}/e(µ_i)   (the top slot's grade).

At i = 2 this is GENTOW2's w := R_{3,κ̄}(n̂₂(u₃)), κ̄ := u₃/e(µ₂)
(LEMMA GENTOW2-B″'s display, ledger row GENTOW2 #4). w_i is a single
SLOT-INDEPENDENT unit: one value per (tower, level, u_{i+1}), not one
per recipe slot. Unit-hood is Cor 4.4(1) (single-point polygon,
degree < m_{i+1} — inside B′'s proof, ledger row GENTOW2 #3). The
definition builds in NOTHING about w's value: w = 1 is a possible
value of this definition, decided only by measurement or derivation
(§4, §5).

**DEF W-2 (the w-twisted residual ψ^{(w)}).** For ψ ∈ K_i[y] monic of
degree f with ψ(0) ≠ 0, and a unit w ∈ K_i^×:

    ψ^{(w)} := w^{f} · ψ(y/w).

Equivalently, coefficientwise: if ψ = y^f − Σ_{t<f} a_t y^t then
ψ^{(w)} = y^f − Σ_{t<f} a_t w^{f−t} y^t. The map ψ ↦ ψ^{(w)} is the
grade-covariant substitution y ↦ wy followed by the monic
renormalization; it preserves monicity, degree, irreducibility,
factor degrees, and the nonzero constant term (ψ^{(w)}(0) =
w^f ψ(0) ≠ 0) — LAW W-A below. GENTOW5's display
ψ_{i+1}^{(w_i)} := w_i^{f_{i+1}} ψ_{i+1}(y/w_i) is this definition
at ψ = ψ_{i+1}, w = w_i (span pin: GENTOW5_PROOF @ b0e5c648,
L780–796).

**DEF W-3 (the n̂-cocycle ϑ — the slot-varying twin, for contrast).**
For slot t < f_{i+1} (level-i recipe geometry):

    ϑ_i(t) := res((n̂_i(u_{i+1}(f_{i+1}−t)) / n̂_i(u_{i+1})^{f_{i+1}−t})(x₀)) ∈ K_i^×,

GENTOW2's ϑ(t) at i = 2 (inside ledger row GENTOW2 #2's display).
ϑ_i is grade-determined, x₀-free, LETTER-VALUED (a z-letter monomial
by the γ-calculus, §2 LAW W-E), and ϑ_i(f_{i+1}−1) = 1. The
division of labor this note fixes as vocabulary: ϑ is the
SLOT-VARYING letter cocycle (measurable from verdict-level data);
w is the SINGLE slot-independent cross-frame unit (verdict-blind,
measurable only in the canonical frame — §4).

**DEF W-4 (the w-inclusive canonical frame — the reading
convention).** A statement is "in the w-inclusive canonical frame"
when its residual displays are read at the FGMN canonical
homogeneous frame WITHOUT quotienting by the unit w_i — i.e. realized
residuals are displayed as ψ^{(w_i)}, never silently identified with
ψ. The opposite convention ("on the nose", u ≡ 1, the old B-2) is
REFUTED at letter-live grades (PE4, machine; §4 row R-5). Every law
in §2 is stated in this frame.

---

## §2. THE BASIC LAWS (each PROVED in the accepted corpus; source labeled)

(filled in commit 2)

---

## §3. THE LEVEL LADDER (what holds at which i)

(filled in commit 2)

---

## §4. THE MEASUREMENT RECORD (enumerative; no universal claims)

(filled in commit 3)

---

## §5. OPEN ITEMS, FENCED

(filled in commit 3)

---

## §6. CONSUMPTION — three-leg checks per R.1

(filled in commit 4)

---

## §7. MACHINE LEG (sealed instrument, two-commit seal)

(instrument seal + verdict, commits 5–6)

---

## §8. AS-OF LEDGER

(filled in commit 4)
