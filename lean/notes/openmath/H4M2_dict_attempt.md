/-
# H4-M2 — the (a6)/(EQ-1) matching dictionary at this group's slice + (R4) + Lemma 4 — attempt (Fable prover H4-M2, 2026-08-01)

Unit H4-M2 of `lean/blueprints/HDISCHARGE_H4.md` (§M table + §2's (R4) plan).
This file is a LITERATE LEAN MARKDOWN NOTE: the prose lives in doc-comment
blocks and every Lean declaration compiles. Gate command (from `lean/`):
`lake env lean notes/openmath/H4M2_dict_attempt.md` — green, zero sorry.

CHARGE (blueprint §M row, verbatim): "the (a6)/(EQ-1) matching dictionary at
this group's slice + (R4) + Lemma 4 proved | §2's (R4) plan items (i)–(iv);
M14 §7.2/§8.2 constraints hard-coded | consumes: M14 Lemma 4;
Lidl–Niederreiter 3.46 (pinned); (EQ-1) text | MED | gate: hostile pass ×1 +
N-K3's gcd table."

CHARGE detail (blueprint §2 (R4) plan, verbatim): "(R4) is definitional GIVEN
the (a6)/(EQ-1) matching dictionary (the owed REL.1 artifact defining 'the
matched position' and `posLetter δ`). H4-M2 writes the dictionary AT THE SLICE
THIS GROUP NEEDS: (i) TWO objects, kept rigorously apart (Codex fold, finding
5 — the REL.1 rule: the O_δ classifier's OWN tower is RECONSTRUCTED over F_q,
never scalar-extended): (i-a) the re-based classifier's own tower (the
construction — REL.1's object, consumed, not defined here), and (i-b) the
same-keys COMPARISON tower (ℤ_p-tower keys viewed in O_δ[x], residuals read
along F_k ↪ F_k·F_q) — a comparison DEVICE; the dictionary's central display
is WHEN the two coincide at a matched prefix (expected: exactly at
prefix-stable positions — a lemma to prove, not a definition to decree);
(ii) `posLetter δ x` with the M14 §7.2 constraint hard-coded — prefix
stability via a designated off-domain letter — PLUS the equivalence PROVED,
not assumed (Codex fold, finding 12): the letter grammar is injective on the
encoded prefix data (`SpeciesSyntax.shape`/side data — the note's
`letter_det` typing) and the off-domain letter is outside the grammar's
range, so that Lean `Stable` ⟺ (R4) is a displayed lemma; (iii) Lemma 4's
gcd(m, δ) = 1 characterization upgraded from 'test-design tool' to a proved
lemma of the dictionary (inputs (F1) Lidl–Niederreiter 3.46 and (F2)
compositum degrees, pinned literature); (iv) the worked F₉ instance
re-derived as the out-of-domain example."

SOURCES consumed: `M14-eq2-alphabet_attempt.md` (Lemma 4, §7.2, the (R)
package, the F₉/T3 instance data); `M14-eq2-alphabet_brief.md` (the species
and stability text); `MOVES_2026-07-24.md` lines ~9368–9560 ((a6), (EQ-1)
verbatim); `LeanUrat/MovesRBase/Defs.lean` (`SpeciesSyntax`/`AlphabetData`/
`Stable`, imported VERBATIM, never re-transcribed); wave-0
`LeanUrat/Scaffold/HDischarge/H4/Defs.lean`.

POINTER RESOLUTION, flagged honestly: the blueprint charge says "M14
§7.2/§8.2 constraints". The M14 attempt has NO §8.2 — its §1 contains a
dangling internal reference "(§8.2 records why the instance MUST encode this
in `posLetter` …)" whose content is exactly §7.2's constraint plus the F₉
evidence that letter-only stability is insufficient. Both constraints are
hard-coded below (§2); the dangling pointer is reported, not papered over.

VERDICT (summary): all four charge items delivered. (i) the two objects are
defined and kept apart, with the coincidence-at-stable-prefixes display
proved as DICT-1 (math lemma, two NAMED inputs: the H4-M1/REL.1 (R1)-slice
at the device, and (U) MacLane-chain essential uniqueness — pinned
literature, flagged for pin precision). (ii) `posLetter` per §7.2 +
`Stable ⟺ (R4)` PROVED, in Lean, from exactly finding 12's two hypotheses
(grammar injectivity + off-domain letter outside the range) — theorem
`DictModel.stable_iff_R4` below, wired to the corpus `AlphabetData.Stable`
verbatim by `alphabetData_stable_iff_R4`. (iii) Lemma 4 PROVED as a lemma of
the dictionary: the arithmetic core `lemma4_arith` is UNCONDITIONAL Lean; the
field-theoretic inputs (F1)/(F2) are named structure rows (`GcdSlice`), and
`GcdSlice.stable_iff_coprime` chains everything: Stable ⟺ gcd(m, δ) = 1.
(iv) the F₉ instance re-derived: math + a compiled split witness over the
concrete F₉ = F₃[i] and the decide-checked gcd table (N-K3 seed).

RISK, displayed (per the blueprint): this dictionary is ALSO consumed by the
(UB-X)(b) adjudication (H4-M4) and by Route A of H4-M5 — it is the shared
gate unit of the blueprint. Nothing here discharges (UB-X)(b); the dictionary
only makes it WELL-POSED at this slice.
-/

import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.Scaffold.HDischarge.H4.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H4.Dict

open MovesRBase Polynomial

/-!
## §1. Item (i) — the two objects, kept rigorously apart

Throughout: p prime, δ ≥ 1, q := p^δ, F_q := the subfield of F̄_p of order
p^δ (the corpus's `Fsub p δ`), O_δ := W(F_q) (the corpus's `O p δ`; ABSOLUTE
base indices per the standing convention). The input is one monic
f ∈ ℤ_p[x] ⊆ O_δ[x]; the matching of inputs is the literal inclusion — that
is the (a6) slice this group needs (nothing about Θ_j-coordinates, frames, or
measure transport — (a1)–(a5) — is defined or consumed here; (a6) is quoted
at its READ-DICTIONARY clause only: "letter-for-letter transport of b_j's
continuation READS to O_δ-classifier reads ((EQ-1)'s dictionary), displayed
per read field").

The base-side data at a ledger position class x: the accepted ℤ_p tower
prefix through stage k — keys Φ_1, …, Φ_k ∈ ℤ_p[x], read indices (e_j, h_j)
with gcd(e_j, h_j) = 1, residue fields F_1 ⊆ … ⊆ F_{k+1} inside F̄_p with
[F_1 : F_p] = d and F_{j+1} = F_j[z]/(ψ_j), ψ_j the stage-j residual,
irreducible over F_j of degree g_j.

### (i-a) The RECONSTRUCTED tower — REL.1's object, consumed, not defined here

The O_δ classifier's OWN run on f: stages built over the base O_δ, keys
chosen in O_δ[x], residue fields RECONSTRUCTED over F_q, residual polynomials
factored over the reconstructed fields and every stage residual irreducible
BY CONSTRUCTION. Per the REL.1 rule (Codex fold, finding 5) this tower is
NEVER the scalar extension of the ℤ_p tower and is NEVER obtained by
substituting a cardinality; its existence and its (S1)–(S6)/D.0 stage package
over O_δ are exactly the (R1)–(R3) slice that unit H4-M1 re-scopes — this
note CONSUMES that object and defines nothing about its internals.

### (i-b) The SAME-KEYS COMPARISON tower — a device, not a classifier

DEFINITION (this note's artifact). The comparison device C^{(δ)} at the
prefix of x: take the ℤ_p-side keys Φ_1, …, Φ_k VERBATIM as elements of
O_δ[x], with the same read indices (e_j, h_j); equip O_δ[x] with the
inductive (MacLane-augmented) valuations w_j^{comp} defined by the same
augmentation data over the Gauss valuation of O_δ (which extends the Gauss
valuation of ℤ_p; O_δ/ℤ_p is unramified, v(p) = 1 on both sides); read the
stage-j residual data along the compositum F_j ↪ F_j·F_q inside F̄_p: the
device's stage-j residue field is DEFINED as F_j^{comp} := F_j·F_q, and the
transported residual is ψ_j itself, read in (F_j·F_q)[z].

STATUS OF THE DEVICE, displayed: C^{(δ)} is a well-defined valuation-theoretic
object (augmentation chains need no irreducibility to be defined), but it is a
CLASSIFIER TOWER only where every transported residual stays irreducible — at
a stage where ψ_j splits over F_j·F_q, the augmentation is not a legal OM
stage (keys must carry irreducible residuals) and the device stops being a
tower of the theory. That is exactly why (i-a) and (i-b) must be kept apart:
the device is a COMPARISON instrument whose agreement with (i-a) is a THEOREM
with a domain, not an identification.

### The matching, at this slice

Matched position: same input f, same prefix keys (via the inclusion
ℤ_p[x] ⊆ O_δ[x]), same height γ. `posLetter δ x` (§2) reads the letter the
device realizes at the matched position, with the §7.2 off-domain clause.
This is the (a6)/(EQ-1) dictionary AT THE SLICE THIS GROUP NEEDS; the full
(a6) artifact (all read fields, plus the (a1)–(a5) frame data) remains an
owed REL.1 artifact and is NOT claimed here.

### DICT-1 — the coincidence display (the central lemma, proved, with named inputs)

**Lemma DICT-1.** At the matched prefix through stage k, the following are
equivalent:

(1) [prefix stability = (R4)] the matched prefix realizes equal stage tuples
(e_j, h_j, g_j) for j ≤ k and equal base degree d, with every re-based
residual irreducible of the matched degree;

(2) [split-freeness of the device] the transported base residual (degree d,
read over F_q) and every transported ψ_j (read over F_j·F_q) remain
irreducible;

(3) [ledger coincidence] the reconstructed tower's prefix ledger data equal
the device's: same stage tuples, w_j^{recon} = w_j^{comp} as valuations on
O_δ[x], and F_j^{(δ)} = F_j·F_q for all j ≤ k+1.

NAMED INPUTS (never silently absorbed): [IN-R1] the device's stages satisfy
the (S1)–(S6)/D.0 package over O_δ where (2) holds — this is a face of the
(R1)-slice, H4-M1's re-scoping charge (REL.1; open, consumed as a
hypothesis); [IN-U] essential uniqueness of MacLane/OM augmentation chains:
two chains realizing the same inductive valuation on the same base have equal
numerical invariants (e_j, h_j, g_j) and isomorphic residue towers, stagewise
(MacLane 1936, "A construction for absolute values in polynomial rings",
TAMS 40; modern forms: Vaquié 2007; GMN's Okutsu-equivalence framework —
PIN-PRECISION FLAGGED: the exact printed theorem number is a LITUNIT-roster
duty, not asserted here).

*Proof.* (2) ⇒ (3): under (2) every augmentation step of the device uses a
monic key whose residual is irreducible over the current residue field, so
C^{(δ)} is a LEGAL OM chain over O_δ (key axioms are valuation-numeric and
transport verbatim with the numerical data; the graded/stage bookkeeping is
[IN-R1]). The reconstructed tower (i-a) at the matched position is an OM
chain realizing the same inductive valuation (same input, same position, and
the classifier's read is determined by the valuation data). By [IN-U] the two
chains have equal stage tuples and residue towers; the device's residue
fields are F_j·F_q by construction, so F_j^{(δ)} = F_j·F_q.

(3) ⇒ (1): the reconstructed residuals are irreducible by construction;
under (3) their degrees are the matched g_j and the stage tuples equal the
transported (= base-side) integers, which is (1) verbatim.

(1) ⇒ (2): suppose some transported residual fails; let j₀ be the FIRST
failing stage (base stage included, with residual of degree d over F_q). The
sub-prefix through j₀ − 1 is split-free, so (2) ⇒ (3) applies to it and the
reconstructed stage-j₀ read sees the same residual ψ_{j₀} over
F_{j₀}^{(δ)} = F_{j₀}·F_q, where it factors into gcd > 1 conjugate factors of
equal smaller degree ((F1), §3). The classifier's stage-j₀ key must carry an
irreducible factor, of degree g_{j₀}/gcd < g_{j₀}: the realized letter's g
drops, so the stage tuples do NOT match — contradicting (1). ∎

The equivalence (1) ⟺ (2) is the "coincide exactly at prefix-stable
positions" display the blueprint demanded as a lemma. Its Lean shadow at the
model layer: the (2) ⇒ (3) leg appears as the NAMED row `coincide` of
`GcdSlice` below (pdata level), and the (1) ⇐ (2) packaging is what licenses
row `l4_persist` reading stability through the device.
-/

/-!
## §2. Item (ii) — `posLetter` with §7.2 hard-coded, and Stable ⟺ (R4) PROVED

M14 §7.2, verbatim, hard-coded here: "`Stable` must entail prefix stability.
The Theorem's induction consumes stability of every sub-position; with
letter-only stability at x the induction hypothesis is unavailable, and the
note's F₉ instance shows interior splitting genuinely redistributes alphabet
dimensions. The instance should make `posLetter δ x` encode the matched
prefix (e.g. return a designated off-domain letter when any prefix residual
splits), so that the Lean `Stable` ⟺ (R4). An instance with a coarser
`posLetter` is NOT covered by this proof and is expected to admit
countermodels."

The dictionary model below is the DEFINITIONAL layer: `Data` is the encoded
matched-prefix data (the stage-tuple list (e_j, h_j, g_j)_{j≤k}, the base
degree d, and the letter grammar's side/polygon data — i.e. what (EQ-1) says
a letter is defined by), `pdata δ x` is the data the device realizes at the
matched position over O_δ, and `splitFree δ x` is DICT-1's clause (2). These
carry the [M]-semantic content and stay NAMED STRUCTURE ROWS (never axioms).
`splitFree_one` is the base-side tautology (over δ = 1 nothing is
transported; every residual is irreducible by the accepted base theory).

Finding 12's two hypotheses are the rows `henc` (the letter grammar is
injective on encoded prefix data) and `hoff` (the designated off-domain
letter is outside the grammar's range on encoded data). They are NOT decreed:
lemmas `enc_injective_of_faithful` and `off_not_mem_range_of_reserved` below
DERIVE them from the grammar level (`SpeciesSyntax.shape`/`side`/`poly`
fields), and `letter_unique_of_triple` displays the `letter_det` typing (the
grammar triple determines the letter — no collisions).
-/

/-- The (a6)/(EQ-1) matching-dictionary MODEL at this group's slice.
[M]-semantic rows (named, never discharged by fiat): `splitFree` = DICT-1(2)
at the matched prefix of x over O_δ; `pdata` = the prefix data the device
realizes; `splitFree_one` = the base-side tautology. Grammar rows: `henc`,
`hoff` per finding 12 (derivable via `enc_injective_of_faithful` /
`off_not_mem_range_of_reserved`). -/
structure DictModel (Sp : SpeciesSyntax) (Pos : Type) where
  /-- encoded matched-prefix data: stage tuples, base degree, side/polygon data -/
  Data : Type
  /-- the letter the grammar assigns to a prefix datum -/
  enc : Data → Sp.Letter
  /-- finding 12(a): the grammar is injective on encoded prefix data -/
  henc : Function.Injective enc
  /-- §7.2's designated off-domain letter -/
  offLetter : Sp.Letter
  /-- finding 12(b): the off-domain letter is outside the grammar's range -/
  hoff : offLetter ∉ Set.range enc
  /-- [M] DICT-1(2): every transported prefix residual stays irreducible -/
  splitFree : ℕ+ → Pos → Prop
  /-- [M] the prefix data realized at the matched position over O_δ -/
  pdata : ℕ+ → Pos → Data
  /-- [M] base-side tautology: at δ = 1 the prefix is split-free -/
  splitFree_one : ∀ x : Pos, splitFree 1 x

/-- `letter_det` displayed: the grammar triple (shape, side, poly) determines
the letter — the dictionary's letter assignment has no collisions. -/
theorem letter_unique_of_triple {Sp : SpeciesSyntax} {l l' : Sp.Letter}
    (h : (Sp.shape l, Sp.side l, Sp.poly l) = (Sp.shape l', Sp.side l', Sp.poly l')) :
    l = l' :=
  Sp.letter_det h

/-- finding 12(a) DERIVED at the grammar level: if the letters assigned to
prefix data carry the data faithfully into the grammar triple via an
injective interpretation ι, the encoding is injective. -/
theorem enc_injective_of_faithful {Sp : SpeciesSyntax} {Data : Type}
    (enc : Data → Sp.Letter)
    (ι : Data → (ℕ × ℕ × ℕ × ℕ) × Sp.SideData × Sp.PolyConv)
    (hι : Function.Injective ι)
    (hfaith : ∀ d, (Sp.shape (enc d), Sp.side (enc d), Sp.poly (enc d)) = ι d) :
    Function.Injective enc := by
  intro d d' h
  apply hι
  rw [← hfaith d, ← hfaith d', h]

/-- finding 12(b) DERIVED at the grammar level: an off-domain letter whose
grammar triple is reserved (realized by no encoded prefix datum) lies outside
the encoding's range. -/
theorem off_not_mem_range_of_reserved {Sp : SpeciesSyntax} {Data : Type}
    (enc : Data → Sp.Letter)
    (ι : Data → (ℕ × ℕ × ℕ × ℕ) × Sp.SideData × Sp.PolyConv)
    (hfaith : ∀ d, (Sp.shape (enc d), Sp.side (enc d), Sp.poly (enc d)) = ι d)
    (off : Sp.Letter)
    (hres : ∀ d, ι d ≠ (Sp.shape off, Sp.side off, Sp.poly off)) :
    off ∉ Set.range enc := by
  rintro ⟨d, hd⟩
  exact hres d (by rw [← hd]; exact (hfaith d).symm)

attribute [local instance] Classical.propDecidable

/-- §7.2 HARD-CODED: the dictionary's `posLetter` — the encoded matched-prefix
letter when the whole prefix persists, the designated off-domain letter the
moment ANY prefix residual splits. -/
noncomputable def DictModel.posLetterD {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) : Sp.Letter :=
  if M.splitFree δ x then M.enc (M.pdata δ x) else M.offLetter

/-- (R4) at the model, verbatim M14 §2: the matched prefix persists
(split-free) AND realizes the base-side prefix data. -/
def DictModel.R4 {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) : Prop :=
  M.splitFree δ x ∧ M.pdata δ x = M.pdata 1 x

theorem DictModel.posLetterD_one {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (x : Pos) :
    M.posLetterD 1 x = M.enc (M.pdata 1 x) :=
  if_pos (M.splitFree_one x)

/-- **Item (ii), PROVED (finding 12): Lean `Stable` ⟺ (R4)** at the §7.2
`posLetter`. The proof consumes EXACTLY the two finding-12 hypotheses:
`henc` (injectivity on encoded prefix data) kills collisions in the stable
direction, and `hoff` (off-domain letter outside the range) makes a split
prefix visibly unstable. -/
theorem DictModel.stable_iff_R4 {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) :
    M.posLetterD δ x = M.posLetterD 1 x ↔ M.R4 δ x := by
  rw [M.posLetterD_one]
  unfold DictModel.posLetterD
  by_cases h : M.splitFree δ x
  · rw [if_pos h]
    constructor
    · intro he
      exact ⟨h, M.henc he⟩
    · rintro ⟨-, hd⟩
      rw [hd]
  · rw [if_neg h]
    constructor
    · intro he
      exact absurd ⟨M.pdata 1 x, he.symm⟩ M.hoff
    · rintro ⟨hsf, -⟩
      exact absurd hsf h

/-- DICT-1's (1) ⇒ (2) contrapositive shadow at the model: a split prefix is
never Stable (the ⇒ leg of the coincidence display, model level). -/
theorem DictModel.not_stable_of_not_splitFree {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) {δ : ℕ+} {x : Pos} (h : ¬ M.splitFree δ x) :
    M.posLetterD δ x ≠ M.posLetterD 1 x :=
  fun he => h ((M.stable_iff_R4 δ x).mp he).1

/-- The §7.2-conformance row tying a corpus `AlphabetData` instance to the
dictionary model: its `posLetter` IS the dictionary's. -/
def Encodes (p : ℕ) [Fact p.Prime] {Sp : SpeciesSyntax}
    (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AD.posLetter δ x = M.posLetterD δ x

/-- **The corpus-verbatim form: `AlphabetData.Stable` ⟺ (R4)** at any
§7.2-conforming instance (the displayed lemma the blueprint demanded; the
corpus `Stable` is imported, never re-transcribed). -/
theorem alphabetData_stable_iff_R4 (p : ℕ) [Fact p.Prime] {Sp : SpeciesSyntax}
    (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos) (hE : Encodes p AD M)
    (δ : ℕ+) (x : AD.Pos) :
    AlphabetData.Stable p AD δ x ↔ M.R4 δ x := by
  unfold AlphabetData.Stable
  rw [hE δ x, hE 1 x]
  exact M.stable_iff_R4 δ x

/-!
## §3. Item (iii) — Lemma 4's gcd(m, δ) = 1 characterization, PROVED

M14 Lemma 4 (verbatim statement): "Same-keys transport setting: the re-based
read is of the same input data with the ℤ_p-tower keys viewed in O_δ[x] (the
natural matching the (a6)/(EQ-1) dictionary is owed to produce), so that
residual polynomials transport verbatim along F_k ↪ F_k·F_q. Let
m := d·g₁···g_k be the accumulated residue degree through x's letter. Then x
is δ-stable iff gcd(m, δ) = 1, and in that case F_j^{(δ)} = F_j·F_q for all
j ≤ k+1."

UPGRADE EXECUTED HERE (charge item (iii)): M14 recorded Lemma 4 as
"CONDITIONAL on the same-keys transport identity … a REL.1/(a6)-dictionary
fact, flagged, not proved". This note IS that dictionary at the needed slice:
§1 DEFINES the same-keys matching ((i-b)) and PROVES the transport identity
as DICT-1 ((2) ⇒ (3): at split-free prefixes the reconstructed run realizes
the verbatim-transported residuals, given [IN-R1]/[IN-U]). With the setting
supplied, Lemma 4's own induction is field arithmetic from two pinned inputs:

(F1) Lidl–Niederreiter, *Finite Fields* (2nd ed., CUP 1997), Theorem 3.46:
an irreducible ψ of degree g over a finite field E stays irreducible over the
degree-δ′ extension E′ iff gcd(g, δ′) = 1; in general it factors into
gcd(g, δ′) conjugate irreducible factors of degree g/gcd(g, δ′). [PINNED]

(F2) compositum degrees of finite fields inside F̄_p:
[E·F_q : E] = δ / gcd(δ, [E : F_p]). [standard; e.g. Lidl–Niederreiter §2.1
subfield lattice]

MATH PROOF (M14's, re-run here now unconditional relative to (F1)/(F2) +
DICT-1): induct up the prefix, writing m_1 := d, m_{j+1} := m_j·g_j (so the
base stage is the j = 0 step with current degree m_0 := 1 and "residual
degree" d over F_p). At each step the current field F_j has
[F_j : F_p] = m_j; by (F2) the compositum extension F_j·F_q/F_j has degree
δ/gcd(δ, m_j); by (F1) the transported ψ_j persists iff
gcd(g_j, δ/gcd(δ, m_j)) = 1. Direction (⇐): if gcd(m, δ) = 1 with
m = d·g₁···g_k then every m_j is coprime to δ, each relative degree is
exactly δ, and each gcd(g_j, δ) = 1 gives persistence. Direction (⇒): if all
stages persist then inductively gcd(m_j, δ) = 1 (base: persistence of the
degree-d residual over F_q forces gcd(d, δ) = 1 since the relative degree is
δ; step: relative degree δ again, so persistence forces gcd(g_j, δ) = 1 and
m_{j+1} stays coprime). At the first failure the residual splits ((F1)'s
factor count gcd > 1), the species letter changes (g drops), x is out of
domain. Hence: δ-stable ⟺ gcd(m, δ) = 1, and along the way
F_j^{(δ)} = F_j·F_q with relative degree δ. ∎

LEAN FACE. The induction's entire arithmetic skeleton is proved
UNCONDITIONALLY below (`persistsFrom_iff`, `lemma4_arith` — no hypotheses at
all, not even positivity). The two field-theoretic inputs enter as the NAMED
row `l4_persist` of `GcdSlice` (reading `splitFree` through the
(F1)/(F2)-criterion chain), and DICT-1's transport identity as the NAMED row
`coincide`. The chained theorems `splitFree_iff_coprime`,
`stable_iff_coprime`, `alphabetData_stable_iff_coprime` are then PROVED.
-/

/-- (F2) as bookkeeping: the relative degree of the compositum,
[E·F_q : E] = δ / gcd(δ, [E : F_p]). -/
def relDeg (δ m : ℕ) : ℕ := δ / Nat.gcd δ m

theorem relDeg_eq_of_coprime {δ m : ℕ} (h : Nat.Coprime m δ) : relDeg δ m = δ := by
  have h' : Nat.gcd δ m = 1 := Nat.coprime_comm.mp h
  simp [relDeg, h']

/-- The per-stage persistence chain of Lemma 4's induction: at current
accumulated degree m, the next residual of degree g persists iff
gcd(g, relDeg δ m) = 1 (this is (F1) read at (F2)'s relative degree), then
recurse at m·g. `persistsFrom δ 1 (d :: gs)` is "the whole prefix persists"
(base stage = first entry, current degree 1). -/
def persistsFrom (δ : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | m, g :: gs => Nat.Coprime g (relDeg δ m) ∧ persistsFrom δ (m * g) gs

theorem coprime_list_prod_left_iff (δ : ℕ) :
    ∀ gs : List ℕ, Nat.Coprime gs.prod δ ↔ ∀ g ∈ gs, Nat.Coprime g δ
  | [] => by simp
  | g :: gs => by
    rw [List.prod_cons, Nat.coprime_mul_iff_left, List.forall_mem_cons]
    exact and_congr_right fun _ => coprime_list_prod_left_iff δ gs

/-- The induction of Lemma 4, arithmetic skeleton (UNCONDITIONAL): from a
coprime current degree, the persistence chain is exactly stagewise
coprimality to δ. -/
theorem persistsFrom_iff (δ : ℕ) :
    ∀ (gs : List ℕ) (m : ℕ), Nat.Coprime m δ →
      (persistsFrom δ m gs ↔ ∀ g ∈ gs, Nat.Coprime g δ)
  | [], m, _ => by simp [persistsFrom]
  | g :: gs, m, hm => by
    simp only [persistsFrom, List.forall_mem_cons]
    rw [relDeg_eq_of_coprime hm]
    constructor
    · rintro ⟨hg, htail⟩
      exact ⟨hg, (persistsFrom_iff δ gs (m * g) (Nat.Coprime.mul_left hm hg)).mp htail⟩
    · rintro ⟨hg, htail⟩
      exact ⟨hg, (persistsFrom_iff δ gs (m * g) (Nat.Coprime.mul_left hm hg)).mpr htail⟩

/-- **Lemma 4, arithmetic core (UNCONDITIONAL Lean)**: the full prefix (base
residual degree d, then residual degrees gs) persists iff
gcd(d·g₁···g_k, δ) = 1. -/
theorem lemma4_arith (δ d : ℕ) (gs : List ℕ) :
    persistsFrom δ 1 (d :: gs) ↔ Nat.Coprime (d * gs.prod) δ := by
  rw [persistsFrom_iff δ (d :: gs) 1 (Nat.coprime_one_left δ),
    List.forall_mem_cons, Nat.coprime_mul_iff_left, coprime_list_prod_left_iff δ gs]

/-- The gcd slice of the dictionary: per position, the prefix degree data
(d; g₁, …, g_k) the device transports, plus the two [M]-rows. `l4_persist`
is (F1)+(F2) read stagewise at the slice (Lidl–Niederreiter 3.46 + compositum
degrees, PINNED literature); `coincide` is DICT-1's (2) ⇒ (3) leg at pdata
level (proved in §1 relative to [IN-R1]/[IN-U]). Both stay NAMED rows. -/
structure GcdSlice {Sp : SpeciesSyntax} {Pos : Type} (M : DictModel Sp Pos) where
  /-- base residual degree d = [F₁ : F_p] at x's prefix -/
  dDeg : Pos → ℕ
  /-- the residual degrees g₁, …, g_k up x's prefix -/
  gDegs : Pos → List ℕ
  /-- [M] (F1)+(F2): split-freeness is the stagewise persistence chain -/
  l4_persist : ∀ (δ : ℕ+) (x : Pos),
    M.splitFree δ x ↔ persistsFrom (δ : ℕ) 1 (dDeg x :: gDegs x)
  /-- [M] DICT-1 (2) ⇒ (3) at pdata: split-free prefixes realize the
  transported (= base-side) prefix data -/
  coincide : ∀ (δ : ℕ+) (x : Pos), M.splitFree δ x → M.pdata δ x = M.pdata 1 x

/-- **Lemma 4 at the dictionary (item (iii) PROVED)**: x's prefix is
split-free iff gcd(m, δ) = 1 with m = d·g₁···g_k. -/
theorem GcdSlice.splitFree_iff_coprime {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.splitFree δ x ↔ Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [G.l4_persist δ x, lemma4_arith]

/-- With the transport identity, (R4) collapses to split-freeness (the data
clause comes for free at split-free prefixes — DICT-1's content). -/
theorem GcdSlice.R4_iff_splitFree {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.R4 δ x ↔ M.splitFree δ x :=
  ⟨fun h => h.1, fun h => ⟨h, G.coincide δ x h⟩⟩

/-- **The full chain: Stable ⟺ gcd(m, δ) = 1** at the dictionary's
posLetter. -/
theorem GcdSlice.stable_iff_coprime {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.posLetterD δ x = M.posLetterD 1 x ↔
      Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [M.stable_iff_R4 δ x, G.R4_iff_splitFree δ x, G.splitFree_iff_coprime δ x]

/-- **Corpus-verbatim: `AlphabetData.Stable` ⟺ gcd(m, δ) = 1** at any
§7.2-conforming instance carrying the gcd slice. -/
theorem alphabetData_stable_iff_coprime (p : ℕ) [Fact p.Prime]
    {Sp : SpeciesSyntax} (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos)
    (G : GcdSlice M) (hE : Encodes p AD M) (δ : ℕ+) (x : AD.Pos) :
    AlphabetData.Stable p AD δ x ↔
      Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [alphabetData_stable_iff_R4 p AD M hE δ x, G.R4_iff_splitFree δ x,
    G.splitFree_iff_coprime δ x]

/-!
## §4. Item (iv) — the worked F₉ instance, re-derived as the out-of-domain example

The recorded instance (M14 brief "Status in the corpus"; M14 attempt Lemma 4
status + T3): p = 3, base key x (so d = 1, F₁ = F₃), stage-1 read
(e₁, h₁) = (2, 1), residual ψ = z² + 1 over F₃ (g₁ = 2, irreducible since −1
is not a square mod 3), δ = 2.

Lemma-4 read: the accumulated residue degree through the stage-2 letter is
m = d·g₁ = 1·2 = 2, and gcd(m, δ) = gcd(2, 2) = 2 ≠ 1 — OUT OF DOMAIN. By
(F1) the transported residual splits into gcd(2, 2) = 2 conjugate factors of
degree 2/2 = 1 over F₉ = F₃·F_q: concretely F₉ = F₃[i] with i² = −1, and
z² + 1 = (z − i)(z + i). The realized letters at the two branch positions
have g = 1 ≠ 2: the species changes, `posLetterD` returns the off-domain
letter, `Stable` fails — consistent with `stable_iff_coprime` (gcd ≠ 1) and
with `not_stable_of_not_splitFree`. Per-branch continuation field is F₉ and
the per-branch full-height alphabet is F₉ (a_branch = 2 ≠ δ·a₁ = 4): interior
splitting genuinely redistributes alphabet dimensions — the §7.2 evidence,
re-derived. (Numerics: M14 T3 re-ran exactly these numbers, PASS.)

Lean witnesses: the split is compiled below over the CONCRETE model
F9 := F₃[z]/(z² + 1) (the root i and the factorization are theorems; that
z² + 1 is irreducible over F₃ — so that F9 IS the field F₉ — is classical
and stays prose). The Lemma-4/gcd reads and the N-K3 table seed are
decide-checked.
-/

/-- F₉ modeled concretely: F₃[i] = F₃[z]/(z² + 1). -/
abbrev F9 : Type := AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))

/-- i ∈ F₉, the adjoined root of z² + 1. -/
noncomputable def imag : F9 := AdjoinRoot.root (X ^ 2 + 1 : Polynomial (ZMod 3))

theorem imag_sq_add_one : imag ^ 2 + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : Polynomial (ZMod 3))
  simpa [imag] using h

theorem imag_sq : imag ^ 2 = -1 :=
  eq_neg_of_add_eq_zero_left imag_sq_add_one

/-- **The split witness**: over F₉ the transported residual z² + 1 factors,
z² + 1 = (z − i)(z + i) — the F₉ instance is out of domain exactly as Lemma
4's gcd read predicts. -/
theorem f9_residual_splits :
    (X - C imag) * (X + C imag) = (X ^ 2 + 1 : Polynomial F9) := by
  have h : (C imag) ^ 2 = C (-1 : F9) := by rw [← C_pow, imag_sq]
  calc (X - C imag) * (X + C imag) = X ^ 2 - (C imag) ^ 2 := by ring
    _ = X ^ 2 + 1 := by rw [h, map_neg, map_one, sub_neg_eq_add]

/-- The F₉ instance's Lemma-4 read: m = d·g₁ = 1·2 = 2, δ = 2,
gcd(2, 2) = 2 ≠ 1 — the persistence chain FAILS. -/
theorem f9_out_of_domain : ¬ persistsFrom 2 1 [1, 2] := by
  rw [show ([1, 2] : List ℕ) = 1 :: [2] from rfl, lemma4_arith]
  decide

/-- The in-domain contrast (M14 T1's δ = 3 run): same prefix, δ = 3,
gcd(2, 3) = 1 — the chain persists. -/
theorem f9_delta3_in_domain : persistsFrom 3 1 [1, 2] := by
  rw [show ([1, 2] : List ℕ) = 1 :: [2] from rfl, lemma4_arith]
  decide

/-!
### The N-K3 gcd-table seed

M14 T3's prediction family, now READ THROUGH THE PROVED LEMMA (the table
N-K3 consumes when it enumerates the n = 3 pack's realized δ > 1 pools; a
realized pool violating its row kills Route A's cheap match — blueprint §3.2).
Rows: (g, δ) with d = 1, flag = stable iff gcd(g, δ) = 1.

  (2, 2) split · (2, 3) stable · (2, 4) split · (2, 5) stable ·
  (3, 3) split · (3, 2) stable

plus the N-T4 two-stage row (d = 1, g₁ = 2, g₂ = 3, δ = 5: m = 6,
gcd(6, 5) = 1 — stable; M14's Test-4 tower).
-/

theorem nk3_gcd_table :
    ¬ Nat.Coprime 2 2 ∧ Nat.Coprime 2 3 ∧ ¬ Nat.Coprime 2 4 ∧
      Nat.Coprime 2 5 ∧ ¬ Nat.Coprime 3 3 ∧ Nat.Coprime 3 2 := by
  decide

theorem nk3_stability_table :
    ¬ persistsFrom 2 1 [1, 2] ∧ persistsFrom 3 1 [1, 2] ∧
      ¬ persistsFrom 4 1 [1, 2] ∧ persistsFrom 5 1 [1, 2] ∧
      ¬ persistsFrom 3 1 [1, 3] ∧ persistsFrom 2 1 [1, 3] := by
  simp only [lemma4_arith]
  decide

theorem nt4_two_stage_stable : persistsFrom 5 1 [1, 2, 3] := by
  rw [show ([1, 2, 3] : List ℕ) = 1 :: [2, 3] from rfl, lemma4_arith]
  decide

/-!
## §5. Consumption map, risk, and the honest residue

WHAT DOWNSTREAM UNITS READ FROM HERE. H4-M4 (the (UB-X)(b)/(K3-δ) precision
step) reads: the matching definition (§1), `stable_iff_coprime` (the
refutation-pressure quantifier: a realized pool whose accumulated residue
degrees share a factor with δ is UNSTABLE under this matching), and the risk
note below. H4-M5 Route A reads: DICT-1 + `GcdSlice` (the per-pool
matched-prefix letter-equality obligation is exactly `stable_iff_coprime`'s
left-to-right reading at the pool's data). H4-M1 reads nothing from here
(this unit is downstream of M1's (R1)-slice via [IN-R1] only). The eventual
Lean instance (fenced H4-F1/H4-F6) must supply `Encodes` (§7.2 conformance)
and the `GcdSlice` rows — per M14 §7.2, an instance with a coarser
`posLetter` is NOT covered and is expected to admit countermodels.

RISK (blueprint §2, displayed): H4-M2 is the SHARED GATE unit — both the
(H4a) retirement chain and the §3.2 adjudication consume this dictionary. A
hostile pass overturning DICT-1's named inputs or the §7.2 encoding ripples
into both.

HONEST RESIDUE (what this note does NOT prove):
1. [IN-R1] — the device's (S1)–(S6)/D.0 package over O_δ at split-free
   prefixes: a face of REL.1's tower slice, H4-M1's charge. NAMED, open.
2. [IN-U] — MacLane-chain essential uniqueness: pinned to MacLane 1936 /
   Vaquié / GMN's Okutsu framework, exact printed theorem number FLAGGED for
   the LITUNIT roster. NAMED, literature.
3. The rows `l4_persist` ((F1) LN 3.46 + (F2) compositum degrees, read at
   the slice) and `coincide` (DICT-1 (2) ⇒ (3) at pdata) are [M]-rows of
   `GcdSlice`: their MATH proofs are §3 and §1 above (modulo 1–2), their
   Lean discharge waits on the H4-F6 carriers.
4. The FULL (a6) dictionary (all read fields, (a1)–(a5) frames, measure
   transport) is NOT built here — only the slice this group needs. (EQ-1)
   itself ("no species definition consumes q") stays H4-M1 step 8's walk.
5. Whether the O_δ classifier's REALIZED ledger contains a matched position
   with gcd(m, δ) > 1 at a given (n, p, δ) is the OPEN realization question
   of blueprint §3.2 — N-K3's empirical probe, nothing here settles it.

DECLARATION LIST (all in `LeanUrat.Scaffold.HDischarge.H4.Dict`, this file,
zero sorry): `DictModel`, `letter_unique_of_triple`,
`enc_injective_of_faithful`, `off_not_mem_range_of_reserved`,
`DictModel.posLetterD`, `DictModel.R4`, `DictModel.posLetterD_one`,
`DictModel.stable_iff_R4`, `DictModel.not_stable_of_not_splitFree`,
`Encodes`, `alphabetData_stable_iff_R4`, `relDeg`, `relDeg_eq_of_coprime`,
`persistsFrom`, `coprime_list_prod_left_iff`, `persistsFrom_iff`,
`lemma4_arith`, `GcdSlice`, `GcdSlice.splitFree_iff_coprime`,
`GcdSlice.R4_iff_splitFree`, `GcdSlice.stable_iff_coprime`,
`alphabetData_stable_iff_coprime`, `F9`, `imag`, `imag_sq_add_one`,
`imag_sq`, `f9_residual_splits`, `f9_out_of_domain`, `f9_delta3_in_domain`,
`nk3_gcd_table`, `nk3_stability_table`, `nt4_two_stage_stable`.

AXIOM FOOTPRINT (checked 2026-08-01, external `#print axioms` run over all
key theorems): Lean-core only — {propext, Classical.choice, Quot.sound};
the arithmetic core (`lemma4_arith`, `f9_out_of_domain`, the tables, the
grammar lemmas) is even choice-free: {propext, Quot.sound}.

STATEMENT-FENCE RECORD: the blueprint has NO §L Lean spec for H4-M2 (it is a
§M math-note unit); the charge text is transcribed verbatim in the header
above and each item is fulfilled at its stated strength. The corpus carriers
(`SpeciesSyntax`, `AlphabetData`, `AlphabetData.Stable`) are consumed by
IMPORT, verbatim, never re-transcribed or weakened; every new declaration
here is dictionary-layer vocabulary of this unit, colliding with nothing
(fresh namespace `LeanUrat.Scaffold.HDischarge.H4.Dict`).
-/

end LeanUrat.Scaffold.HDischarge.H4.Dict
