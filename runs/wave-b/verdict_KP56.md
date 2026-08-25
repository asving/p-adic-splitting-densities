# Verdict — unit KP56 (nodes KP-5 + KP-6)

**COMPLETE.** One new file `leanfinal/Uniformity/ChapC/C130kp5.lean`, built green
(`lake build Uniformity.ChapC.C130kp5`, 8757 jobs), zero `sorry`, all 6 `#print axioms`
footprints Lean-core `{propext, Classical.choice, Quot.sound}`. Imports C130kp3 (KP-0..KP-4
+ RP chain), C130lb (CC-15's Gauss transport), C78adj (`composedKey_s2Tower`) only.

## NODE KP-5 — `Φ′` irreducible in `Polynomial O`, bridge stated explicitly

The abstract `FGMNSourceLaws.key_irreducible` field is universal over every key polynomial
and needs published Lemma 1.8 in full — out of scope for one node (matches CC-15's own
verdict). What lands: the landed key `Φ′ = x² − 2` IS irreducible in `Polynomial O`, proved
**directly** via mathlib's classical Eisenstein criterion (`Polynomial.
irreducible_of_eisenstein_criterion`) at `P = IsLocalRing.maximalIdeal O`: leading coeff `1
∉ P`, `coeff 0 = −2 ∈ P` but `∉ P² = (4)` (else `2` would be a unit), `coeff 1 = 0 ∈ P` —
★ `s2Key_eisenstein_irreducible` (+ `_spelled`, `_at_frame`). **The bridge, explicit**: CC-15's
Gauss leg (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) is an iff; read
FORWARD at this (monic) key, the just-proved `O[x]` result upgrades for free to the
fraction-field statement any faithful Lemma-1.8 realization would need — ★
`s2Key_irreducible_map_fractionRing`, for an arbitrary fraction field `Kv` of `O`. NOT
claimed: irreducibility of `composedKey`/the degree-four lift — their Newton polygon has a
single slope `−1/2` segment with `gcd(4,2)=2`, so no single-prime Eisenstein (shifted or not)
decides it; C78adj's own docstring already flags the closely related `g₄` case as open.

## NODE KP-6 — the tower's own `keyAt 2 = composedKey`, computed

`carried_key_is_key`/`carried_key_residual` at the landed `r = 1` anchoring (`keyAt 1 = Φ′`)
were ALREADY closed elsewhere (`s2KeyPoly_key` in C130kp1, `s2NormRes_key` in C130rp8) —
nothing to redo. The row's open question was the tower's OWN `composedKey (s2Tower h2 hq) =
Φ′² − C(4w)·X` (C78adj, `w = entryW h2 hq` a noncanonical UNIT, not literally `1`) — a genuine
generalization of RP-11/RP-12's fixed witness `Φ′² + 4x`. Generalized the `C4X` grade-tie
tooth bank (private `…cX` lemmas) from the literal scalar `4` to any nonzero `c` of valuation
exactly `2`, re-derived the recipe via RP-11's `s2_normalized_recipe`, and forced the residual
scalar to `1` by the two-element `K₂` collapse (no recomputation of `4w`'s actual `twistRead`
needed). Result: ★ `s2NormRes_composedKey : s2NormRes h2 hq (composedKey (s2Tower h2 hq)) =
X + 1` and ★★ `s2KeyPoly_composedKey : S2KeyPoly h2 hq (composedKey (s2Tower h2 hq))` — **yes,
the tower's own composed key IS an `S2KeyPoly`** — via KP-4's `s2_key_criterion` (monic:
C47; degree 4: C78adj; irreducible residual `X+1`, degree 1, nonzero constant: proved above).

## Honesty scope / flags

No universal `key_irreducible` field; no irreducibility claim for `composedKey`/the lift; no
literal `r = 2` `FGMNSourceData`/`FGMNSourceLaws` instance reading `composedKey` as its OWN
carried key (`s2NormRes_composedKey`/`s2KeyPoly_composedKey` are honest analogous statements
at the landed μ₂ engine, computed at the literal tower polynomial — the same genre RP-11/KP-3
already established); no `initial_iff_residual`, no FD-0 assembly. Flagged for human review
(new statements): `s2Key_eisenstein_irreducible`, `s2Key_irreducible_map_fractionRing`, the
`…cX` generalization bank, `s2NormRes_composedKey`, `s2KeyPoly_composedKey`.
