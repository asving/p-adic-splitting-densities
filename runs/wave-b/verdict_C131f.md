# Unit C131f verdict

## C.131f′ — LANDED

Public lift-pin fence landed without naming any private C.46/C.47 helper:

- `KeyFrame.natDegree_stageLiftO_lt`
- `KeyFrame.slotRes_stageLiftO`
- `KeyFrame.stageHeight_stageLiftO`

The corresponding proofs are reconstructed locally from the public lift definitions and are
then exported in the stable `Uniformity.Density.Tower.KeyFrame` namespace.  No specialized
negative-lift residue theorem is exported: the v2 blueprint explicitly says not to export that
second specialization unless Lean forces it, and this unit does not need it.

## C.131g′ — LANDED

Declarations proved:

- `C131f.K_T`
- `C131f.coeff_K_T`
- `C131f.composedKey_monomial_floor`
- `C131f.K_T_monomial_floor`
- `C131f.WT_K_T`

The monomial floor and equality `WT T (K_T T) = (T.E₂ : ℕ∞)` use only the four public C.47
composed-key clauses, the landed C.131a weight vocabulary, and C.131p's public
`stageHeight_eq_coeff_inf`.  Zero slots and off-lattice slots are eliminated; every nonzero
lattice slot is priced by its exact public stage height; the top digit supplies equality.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C131f.lean
```

Result: success.  Every printed declaration has only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` and the file contains no `sorry`, new axiom, or `unsafe`
declaration.
