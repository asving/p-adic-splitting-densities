# M14-eq2-alphabet — problem brief (neutral, self-contained)

## One-line statement

Prove the "(EQ-2) alphabet law": for every prime p and every degree δ ≥ 1, at
each digit position of the Okutsu–Montes digit ledger whose *species* is
stable under the unramified base change ℤ_p → W(F_{p^δ}), (i) the re-based
per-position slot map is F_{p^δ}-linear, and (ii) the re-based attainable
digit alphabet has F_p-dimension exactly δ times the ℤ_p-side one — or refute
it / identify the exact hypotheses under which it holds.

## Context: what the ledger is

The corpus formalizes a uniformity theorem: for each degree n and splitting
type σ, the density of monic degree-n polynomials over ℤ_p factoring over ℚ_p
with type σ is one rational function R_σ(q) at q = p, for all p. The engine is
an Okutsu–Montes / MacLane classifier that reads a polynomial through a tower
of Newton-polygon stages, and a *digit ledger* that converts every classifier
event into conditions on finitely many "digits" of the coefficients, each
constrained digit contributing a mass factor |𝔸|⁻¹ where 𝔸 is that digit
position's *attainable alphabet*.

### The tower and its digits (base ℤ_p; this is proved in the corpus)

A *stage* of the classifier (accepted note §B2-DEF, in
`lean/notes/MOVES_2026-07-24.md` from line 1849) is a tuple
σ = (w, Φ, C, U, T, F, z): a ℤ-valued valuation w on A = ℤ_p[x], a monic key Φ
with coefficient space C = {deg_x < deg_x Φ}, a finite field F, and graded-ring
data (a degree-1 unit T in a localization L of gr_w(A), a degree-0 unit z with
L₀ = F[z^{±1}]), subject to stage axioms (S1)–(S6). The residual map is
R(f) := [f]·T^{−w(f)} ∈ L₀ ([f] = the initial form of f in gr_w(A)); for
B ∈ C∖0 the *digit* is dig(B) := R(B) = c·z^{k(B)} with c ∈ Fˣ (axiom S5).

Under one read the stages form a tower k = 1, …, K: stage k has coefficient
space C_k (C₁ = {deg_x < d}; C_{k+1} = stage k's next coefficient space, with
Φ_k-development B = Σ_j B_j Φ_k^j, B_j ∈ C_k, 0 ≤ j < e_k·g_k), residue field
F_k ([F₁ : F_p] = d, the degree of the first key's irreducible residue;
F_{k+1} = F_k[z]/(ψ_k), g_k := deg ψ_k, ψ_k the stage's irreducible residual
polynomial), read index (e_k, h_k) with gcd(e_k, h_k) = 1 (the side slope
h_k/e_k), Bézout t_k (h_k·t_k ≡ 1 mod e_k), and weight set
𝒲_k := w_k(C_k∖0) ⊆ e_k·ℤ.

For B ∈ C_k and a height γ with w_k(B) ≥ γ, the height-γ digit is
d_γ(B) ∈ F_k := 0 if w_k(B) > γ, else the (S5) digit scalar of B. The corpus's
proved recursion (§B2-DEF D.3(e)(ii), display (ii.2)) computes digits of
B ∈ C_{k+1} from the digits of its Φ_k-slots:

  d_γ(B) = u(γ) · Σ_{i∈I(γ)} d_{γ_i}(B_{j₀+i·e_k}) · z̄^i,   u(γ) ∈ F_{k+1}ˣ
  forced by the stage data and γ alone,

where γ* := γ/e_{k+1} (the scale stretch; γ* = γ at the top space), j₀ ∈
{0, …, e_k − 1} is the anchor slot j₀ ≡ t_k·γ* (mod e_k), the slot heights are
γ_i := γ* − (j₀ + i·e_k)·h_k for 0 ≤ i < g_k, and

  I(γ) := { i < g_k : γ_i ∈ 𝒲_k }

is the *attainable index set* (for i ∉ I(γ) no coefficient of weight γ_i
exists and the summand is absent). The *attainable alphabet* at (stage k+1,
height γ) is the value set

  𝔸(γ) := { d_γ(B) : B ∈ C_{k+1}, w_{k+1}(B) ≥ γ } ⊆ F_{k+1},

and the corpus proves (same display):

  𝔸(γ) = u(γ)·{ Σ_{i∈I(γ)} c_i·z̄^i : c_i ∈ 𝔸_k(γ_i) },   an F_p-subspace of
  F_{k+1} of cardinality Π_{i∈I(γ)} |𝔸_k(γ_i)|

(distinct attainable tuples give distinct values since (1, z̄, …, z̄^{g_k−1})
is an F_k-basis of F_{k+1}). Base case: 𝔸₁(e₁v) = F₁ for every v ≥ 0 (the
base digit map is onto). So |𝔸(γ)| = p^{a(γ)} for a well-defined
a(γ) := dim_{F_p} 𝔸(γ), equal to [F_{k+1} : F_p] exactly when every height in
γ's slot tree is attainable, and strictly smaller at shallow heights. Also
proved: the per-stage weight sets satisfy the recursion (§B2-DEF D.9(a))

  𝒲_{k+1} = e_{k+1} · ⋃_{0 ≤ j < e_k·g_k} (𝒲_k + j·h_k),   𝒲₁ = e₁·ℤ≥0.

### The re-based theory (base W(F_{p^δ}); this is the OPEN layer)

Fix an algebraic closure F̄_p once; F_m is THE subfield of order p^m and
O_m := W(F_m) ⊂ W(F̄_p) (so O₁ = ℤ_p). The corpus's relative layer re-runs the
whole classifier + ledger over O_δ: the ambient ring is O_δ[x], the Gauss
valuation is unchanged (O_δ/ℤ_p is unramified), and every residue-theoretic
object — base residue field (now F_δ := F_{p^δ}), residual polynomials, tower
fields, attainable alphabets — is RECONSTRUCTED over F_δ, never obtained by
substituting a cardinality: the re-based tower is NOT the scalar extension of
the ℤ_p tower, because residual polynomials irreducible over a ℤ_p-tower field
can split after re-basing. The statement that the whole accepted theory holds
over O_δ mutatis mutandis is the corpus's named open kernel **REL.1** (note
§ [2r], `MOVES_2026-07-24.md` line ~9379); it is a standing open obligation
with its own planned verification pass, and the present obligation is
explicitly recorded as conditional on it.

### Species letters and δ-stability

A *species letter* is finite syntax describing one classifier read: the stage
tuple (e, h, g, μ), side/lattice data, and polygon conventions — a grammar
parameterized by integers and residual-degree data, never by the residue
field's size. Under re-basing the letter set is unchanged; what can change is
which letter a given position realizes (a residual factor can split, changing
g and the branch structure). A ledger position is *δ-stable* when its realized
species letter over O_δ equals its realized letter over ℤ_p, matched through
the species dictionary. (In the intended reading a position class carries its
whole tower-prefix shape — the stage tuples of all stages below it — so
stability of the position's letter entails the matched re-based prefix has the
same numerical stage data (e_k, h_k, g_k) with all residual polynomials still
irreducible of the same degrees.) At a position whose residual factor splits
under re-basing the comparison is NOT well-posed (the old alphabet
re-distributes across new branch species) and the position is out of domain.

### The carry-algebra presentation (equivalent packaging)

The MOVES pass-7/8 records specify the same digit structure as a *carry
algebra* 𝒟 := F[u]/(u^e − z̄) = ⊕_{ρ∈ℤ/e} F·u_ρ, u_ρ·u_σ =
z̄^{⌊(ρ+σ)/e⌋}·u_{(ρ+σ) mod e} — a strongly graded twisted algebra whose
homogeneous components F·u_ρ ≅ F carry the digits (ρ = the anchor coset, the
F-part = the aligned residual class). The accepted §B2-DEF realizes this
structure inside the graded localization L (each homogeneous z-position is one
component); alphabets sit inside one homogeneous component, i.e. inside the
tower field F_{k+1}, exactly as above. The per-prime obligation below is
stated for these alphabets; the two packagings carry the same information.

## The precise obligation

Lean statements (`lean/LeanUrat/MovesRBase/Defs.lean`); here `Fsub p δ` is
F_{p^δ} ⊂ F̄_p and the structures are stated per prime p:

```lean
structure AlphabetData (Sp : SpeciesSyntax) where
  Pos : Type                              -- shape position classes
  posNe : Nonempty Pos
  Carrier : ℕ+ → Pos → Type               -- the re-based receiving group
  [carrierGrp : ∀ δ x, AddCommGroup (Carrier δ x)]
  [carrierMod : ∀ δ x, Module ↥(Fsub p δ) (Carrier δ x)]
  SlotDom : ℕ+ → Pos → Type               -- the re-based slot maps' domain
  [slotDomGrp : ∀ δ x, AddCommGroup (SlotDom δ x)]
  [slotDomMod : ∀ δ x, Module ↥(Fsub p δ) (SlotDom δ x)]
  slotMap : ∀ δ x, SlotDom δ x → Carrier δ x
  alpha : ∀ δ x, Set (Carrier δ x)        -- 𝔸_δ
  alpha_attain : ∀ δ x,
    alpha δ x = ↑(AddSubgroup.closure (Set.range (slotMap δ x)))
  aDim : ℕ+ → Pos → ℕ                     -- a_δ: F_p-additive-span dimension
  card_eq : ∀ δ x, Nat.card (alpha δ x) = p ^ aDim δ x
  posLetter : ℕ+ → Pos → Sp.Letter        -- the realized species letter

def AlphabetData.Stable {Sp} (AD : AlphabetData p Sp) (δ : ℕ+) (x : AD.Pos) : Prop :=
  AD.posLetter δ x = AD.posLetter 1 x

def EQ2law {Sp} (AD : AlphabetData p Sp) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
    IsLinearMap ↥(Fsub p δ) (AD.slotMap δ x) ∧
    AD.aDim δ x = (δ : ℕ) * AD.aDim 1 x
```

The obligation is the hypothesis row (`lean/LeanUrat/MovesU/DefsLedger.lean`,
inside `structure UpstreamTyped`, where `KC.AD p` is a carried per-prime
`AlphabetData`):

```lean
  cl8_eq2 : ∀ (p : ℕ) [Fact p.Prime], MovesRBase.EQ2law p (KC.AD p)
```

In standard language:

> **(EQ-2).** For every prime p, every δ ≥ 1, and every ledger position class
> x whose species is δ-stable: the re-based slot map at x over O_δ — the map
> whose additively generated image is the attainable alphabet 𝔸_δ(x) — is
> F_{p^δ}-linear (for the carried module structures), and
> dim_{F_p} 𝔸_δ(x) = δ · dim_{F_p} 𝔸₁(x), i.e. |𝔸_δ(x)| = |𝔸₁(x)|^δ.

The intended concrete reading of the abstract fields: `Pos` = ledger digit
position classes (tower-prefix shape, stage index, height γ); `Carrier δ x` =
the re-based receiving group of the digit at x (the tower field F^{(δ)}-side
value group); `SlotDom δ x` = the domain of the re-based slot map at x (the
weight-γ coefficient data feeding the digit); `slotMap δ x` = the re-based
digit/residual reading; `alpha δ x` = the attainable alphabet 𝔸_δ(x);
`aDim δ x` = log_p |𝔸_δ(x)|; `posLetter δ x` = the species letter realized at
the matched position over O_δ. No Lean instance of `AlphabetData` exists yet;
the Lean statement layer (quoted above) is normative for the SHAPE of the
claim, and the mathematical content is (EQ-2) at this intended instance.

## Status in the corpus

- §B2-DEF (the base-ℤ_p tower, digits, alphabets, recursion displays quoted
  above) is ACCEPTED (dual verification, 20+ passes; `MOVES_2026-07-24.md`).
- The re-based-span DEFINITION of 𝔸_δ and |𝔸_δ| = p^{a_δ} are recorded
  UNCONDITIONAL; the law "(EQ-2): F_δ-linearity + a_δ = δ·a on the δ-stable
  domain" is recorded OPEN and REL.1-conditional (note §R.1 (EQ-2),
  `MOVES_2026-07-24.md` ~line 9550), with the comparison domain pinned per
  position class as above.
- Worked instance on record (same section): p = 3, δ = 2, ψ = z² + 1 over F₃
  splits over F₉ — both affected positions change species, so the comparison
  is out-of-domain there; no in-domain instance is worked in the note.
- A sealed numeric gate (REL-n4: p = 2, n = 4, δ = 2 conditioning on an
  irreducible quadratic root read) is OUTLINED but not yet specced/run.
- Lean side: `EQ2law` and its row `cl8_eq2` are built and consumed
  (`UpstreamTyped`, and the per-digit wiring `aDim_eq` in
  `MovesU/SlotsG1_cinterface.lean` reads each digit position's exponent as
  `AD.aDim δ (posOfDigit H i)`). Nothing about the row is proved; there is no
  countermodel on record.

## What a proof must deliver

1. A precise statement of the re-based objects it consumes (which parts of
   the open REL.1 layer, as explicit hypotheses — the obligation is recorded
   REL.1-conditional, so conditionality on clearly displayed re-based stage
   facts is acceptable and expected; hidden use of "the theory transfers" is
   not), and of the δ-stability hypothesis actually used.
2. Proof of both conjuncts on the pinned domain — F_δ-linearity of the slot
   map, and a_δ = δ·a₁ — or a counterexample/obstruction with its exact
   location (which position class, which re-basing, which conjunct).
3. A faithfulness check against the quoted Lean forms: the Lean statement is
   normative; in particular `Stable` is letter-equality at x, `alpha` is the
   additive closure of the slot-map range, and `card_eq` forces |𝔸_δ| to be
   an exact p-power. Any mismatch between the intended instance and these
   forms must be flagged.
