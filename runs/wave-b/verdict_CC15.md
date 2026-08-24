# CC-15 verdict — FGMN laws B, class-facing

**LANDED** (all seven law groups; no BLOCKED, no SUPPLY — every needed source field is
carried by CC-13's `FGMNSourceLaws` in C130fg).

## Deliverable

One new file: `leanfinal/Uniformity/ChapC/C130lb.lean` (imports only landed `C130fg`).
No other file touched; roll-ups, leanspec, and in-flight unit files untouched; nothing
committed. (`C130s6.lean` in the worktree is CC06's in-flight file, not mine.)

## Per-law status (namespace `Uniformity.Density.Tower`, all `theorem`s)

| law (node list) | declaration | scope (U9) | status |
|---|---|---|---|
| recipe expansion | `FGMNSourceLaws.Rres_recipe` | scalar slots inlined as `(gradedResidual β g).coeff 0` (Q2); slots fenced `deg < deg keyAt r` | LANDED (transport of `normalized_recipe`) |
| existence law | `FGMNSourceLaws.Rres_exists` | **`Irreducible ψ`** required (§10) + `ψ.Monic`, `natDegree = f'`, `coeff 0 ≠ 0`; fenced `0 < r` (Q4) | LANDED (transport of `normalized_exists`) |
| key criterion | `FGMNSourceLaws.KP_criterion` | carries the **nonzero-constant leg** `(Rres g).coeff 0 ≠ 0` (§4.1) | LANDED (transport of `key_criterion`) |
| irreducibility over O[x] | `irreducible_of_fraction_map_irreducible` + `FGMNSourceData.key_irreducible_of_fraction_map` + `FGMNSourceLaws.KP_irred` | Gauss transport **EXECUTED** (Q5/§7): proved from mathlib `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (name re-verified by rg at `Mathlib/RingTheory/Polynomial/GaussLemma.lean:149`; `IsIntegrallyClosed O` resolves from the DVR instances). `key_irreducible_of_fraction_map` derives the full source field from Lemma 1.8's genuine `K_v[x]` statement — OPEN-GAUSS is a theorem, not a hypothesis; a realization owes only Lemma 1.8 + the `K_v`-to-fraction-field dictionary (U9 §7). | LANDED |
| key's own residual | `FGMNSourceLaws.KP_keyAt` (Prop 1.7(4)), `FGMNSourceLaws.Rres_keyAt` (eq (11)) | both fenced `0 < r` (Q4) | LANDED (transports) |
| ν-equivalence ↔ residual | `FGMNSourceLaws.nuEquiv_iff_Rres` + derived corollary `nuEquiv_ne_of_Rres` (the direction C.103 consumes) | both `KP` hypotheses retained (§4.1); unfenced per A-C.11 §11 (adding `0 < r` would drift against the enacted class field and break CC-16) | LANDED |
| letter nonvanishing | `FGMNSourceLaws.letterZ_ne_zero` | live range `1 ≤ i ≤ r` (empty at `r = 0` — Q4's letter fencing) | LANDED (transport of `letter_ne_zero`) |

Honesty: the law theorems are TRANSPORTS pinning the A-C.11 shapes; the source obligations
remain genuine `FGMNSourceLaws` hypotheses. Newly PROVED content: the Gauss leg (mathlib)
and the `nuEquiv_ne_of_Rres` corollary. No scalar `Rgr` definition was added (CC-16 stays
the sole packaging site; avoids collision with in-flight CC-14).

## Verification

```
cd leanfinal
lake env lean Uniformity/ChapC/C130lb.lean       # exit 0
lake build Uniformity.ChapC.C130lb               # Build completed successfully (8631 jobs)
```

`#print axioms` (in-file, all ELEVEN new declarations): `[propext, Classical.choice,
Quot.sound]` — Lean core only. No `sorry`, no new axiom, no `unsafe`.

Anti-drift fit probe (`/tmp/cc15_fit_probe.lean`, NOT landed): each of the eight A-C.11 §11
class-field types, written verbatim under the §7 packaging dictionary, is filled
**point-free** (`:= hL.Rres_recipe` etc.) — exit 0. The CC-16 record fill is therefore eta
for every B-side field.
