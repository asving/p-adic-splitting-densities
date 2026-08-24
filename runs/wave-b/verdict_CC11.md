# Unit CC11 verdict — chain-carrier node CC-11 (the separate Kt-valued arena layer)

## Verdict: **LANDED**

New file: `leanfinal/Uniformity/ChapC/C130ar.lean` (freeze-v2 layer C.130i; design §4.2/§8
row C.130i/§10 row CC-11). Zero `sorry`, no new axiom, no `unsafe`, no `True` body; all 26
declarations print Lean-core axioms only (`propext`/`Classical.choice`/`Quot.sound`);
`lake build Uniformity.ChapC.C130ar` completed (8683 jobs).

## Declarations (26, namespace `Uniformity.Density.Tower`)

**Lattice plumbing:** `arenaLiveProj` (+`_apply` pin), `gaugeLive_exists_iff` (the family
hypothesis `1 < r` is PROVED minimal — gauge range nonempty iff `1 < r`),
`levelHeight0_comp_arenaLiveProj` (rfl tie to C.130f), `arenaKerProj` (+`_coe` pin).

**Arena-leg normalizer sections (over CC-4's `LaurentNormalizer`):**
`LaurentNormalizer.arenaNormSectionAt` (+`_n` pin), `LaurentNormalizer.arenaNormSection0`
(+`_n` pin) — per-level and synchronized D.01 `NormSection`s; the arena leg rides the
Laurent carrier because C130B proved C.83's truncated `towerNorm` cannot satisfy the
arena's exact-height field.

**The arenas (D.07 `GaugeArena`, res = the SEPARATE `arenaRead` source field, verbatim):**
`NodePointSource.gaugeArenaAt` (+`_v`/`_res` rfl pins), `NodePointSource.arenaRead0`
(+`_apply` pin), `NodePointSource.gaugeArena0At` (+`_v`/`_res` rfl pins),
`NodePointSource.gaugeArenaFamily0` (socket shape `ℕ → GaugeArena (GaugeLattice0 r) Kt N`
under minimal `1 < r`; +`_live` non-swallowing lemma and `_junk` off-range pin).

**W-leg exports (D.44 shapes):** `NodePointSource.towerReadFamily0` (+`_live`/`_junk`),
`NodePointSource.peelUnitFamily` (+`_eq` rfl pin).

**Teeth:** the literal CC-4 `DeepTower.laurentNormalizer` feeds every constructor; the
arena's exact-height fires at a numeral; D.62's `varthetaEl_mem_ker` (kernel arithmetic
only, no residue claim) consumes the arena; the S2 depth-two (CC-2) family, tower-read, and
peel-unit exports elaborate with no obstruction.

## Audit result: NO canonical/arena agreement — PASS

* The arenas' residue read is the separate `arenaRead` field BY CONSTRUCTION, `rfl`-pinned
  (`gaugeArenaAt_res`/`gaugeArena0At_res`/`arenaRead0_apply`); no declaration relates it to
  the ambient L-valued read, the `Kt → L` embedding, or any Kt-preimage/descent datum; no
  declaration produces an `Lˣ`-valued residue datum; no D.44 B-law instance is claimed.
  The D.62/D62w discharge traps (arena-agreement, τ-letters) remain inapplicable: unpacking
  a socket still leaves exactly the descent/agreement goal, per freeze v2 §8.
* Mechanical grep-tooth (in the file's AUDIT section, self-excluding via character classes):

  ```
  rg -n "canonical[R]ead|[H]VarthetaRes|hvartheta[R]es|algebra[M]ap" \
    leanfinal/Uniformity/ChapC/C130ar.lean
  ```

  returned NO output (exit 1) — the trap-lemma names, the sitewise carrier, the ambient
  read's field name, and the coefficient embedding never occur anywhere in the file.

## Verification

From `leanfinal/`:

```
lake env lean Uniformity/ChapC/C130ar.lean     # exit 0, 26 Lean-core axiom prints
lake build Uniformity.ChapC.C130ar             # Build completed successfully (8683 jobs)
```

Co-import smoke test green: `C130ar` + `C130pt` + `C130tr` + `C130th` import together with
no name collisions (all new names are arena-prefixed or `NodePointSource`-namespaced to
stay decorrelated from in-flight CC-10/CC-12).

## Supply notes for downstream nodes

* CC-12: `gaugeArenaFamily0_live` + the `_v`/`_res` pins are the intended `ArenaViewEq j`
  feeders; the `ULift`/cross-universe arena transport and the use-height family `q` are
  deliberately NOT here (CC-12's remit). `towerReadFamily0`/`peelUnitFamily` are the
  `R`/`w` socket arguments.
* CC-17: the S2 instance must supply `NodePointSource` (incl. the three W-leg source
  fields); every CC-11 constructor then applies with `NL := (s2DepthTwo …).laurentNormalizer`
  and `hr : 1 < 2` (teeth already elaborate this path).
