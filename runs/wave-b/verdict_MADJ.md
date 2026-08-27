# MADJ verdict — Outcome A: the required instance is `(21,2)`

## Adjudication

M3-NV4 needs

```lean
Dv2ResSurv ((s2Tower h2 hq).levelDatum h2)
  (s2DepthTwoKeyAt h2 hq 2) 21 2
```

at S2. The `(5,2)` numerals do occur, but only **inside** the level datum's digit-height
read: `dv2Hgt L A = dvSupp (s2Frame h2 hq) A 5 2`
(`leanfinal/Uniformity/ChapC/C132nv3b.lean:114-118`). They are not the explicit outer
`(u₂,ℓ₂)` arguments of `Dv2ResSurv`. Thus this is Outcome A, not Outcome C: both
survival clauses are consumed at outer `(21,2)`; both clauses evaluate their digits by the
inner μ₂ height encoded in `L`.

## Consumption trace

1. The endpoint being made multiplicative is definitionally the μ₃ table
   `s2Hgt₃ g = toZ (dv2Supp L Φ₂ g 21 2)`
   (`leanfinal/Uniformity/ChapC/C132nv1.lean:70-80`), and its key tooth is likewise proved
   at `dv2Supp ... 21 2` (`C132nv1.lean:178-189`). The campaign blueprint fixes exactly
   this table at M3-NV1 and asks M3-NV4 to prove its product law
   (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md:234-237`). The depth audit independently
   assigns `5` to depth 1 and `21` to depth 2
   (`docs/in-progress/PACKAGING_ROUTE_2026-08-25.md:40-52`).

2. `Dv2ResSurv L Ψ u₂ ℓ₂` leaves digit values as `dv2Hgt L`; only its carry
   inequality inserts the explicit outer `ℓ₂` and `u₂`
   (`leanfinal/Uniformity/ChapC/C132nv2.lean:227-233`). The convolution bank then uses the
   *same* explicit pair in `dv2Supp`, side membership, weights, and the survival hypothesis
   (`C132nv2.lean:253-258`). Therefore those arguments must match the outer table being
   priced, namely `(21,2)`.

3. The final C132nv2 theorem is explicitly labeled “NV-4 consumption shape.” Its premise,
   side/minimizer data, and product-law conclusion all share one `u₂,ℓ₂`
   (`C132nv2.lean:626-635`). Instantiating that theorem at `(21,2)` therefore yields the
   product law for the support occurring in `s2Hgt₃`; `(5,2)` would instead prove a law
   about a different outer support table.

4. C132nv3b supplies exactly what this instantiation needs. Slot 0 is independent of the
   explicit outer numerals (`leanfinal/Uniformity/ChapC/C132nv3b.lean:172-180`), while the
   landed slot-1 theorem has the literal outer carry `2·height + 21`
   (`C132nv3b.lean:270-300`). These combine into the full `(21,2)` hypothesis. The failed
   `(5,2)` analysis remains a valid diagnostic for the wrong outer table; it does not block
   M3-NV4.

## Machine pin

`leanfinal/scratch/MADJ_probe.lean:31-34` constructs the complete
`s2_dv2ResSurv_at_21`. Lines `38-51` apply it to
`C132nv2.dv2Supp_mul_eq_add_of_endpoint_le`, with every support and side argument visibly
instantiated at `21 2`. Lines `55-65` unfold `s2Hgt₃` and obtain the blueprint's carrier
conclusion

```lean
s2Hgt₃ h2 hq (g * z) = s2Hgt₃ h2 hq g + s2Hgt₃ h2 hq z.
```

Verification from `leanfinal/`:

```text
lake env lean scratch/MADJ_probe.lean
```

exits 0 with no diagnostics. The probe contains zero `sorry` and zero `axiom` declarations.

## Suggested C132nv2 clarification (record only)

No theorem change is needed. In the `Dv2ResSurv` docstring near
`C132nv2.lean:220-226`, add: “The explicit `u₂,ℓ₂` are the **outer** `dv2Supp`
slope numerals threaded through the convolution bank; the inner slope used to value digits
is already fixed by `L` through `dv2Hgt L`.” This would prevent the inner `(5,2)` read from
being mistaken for M3-NV4's outer instance.
