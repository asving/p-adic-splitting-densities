# Codex FINAL#6 audit — MovesD REV 7 (§D4-R), sixth final-confirmation pass, 2026-07-28
Detached `codex exec` run (model gpt-5.6-sol, sandbox danger-full-access) against the rev-7 blueprint, the frozen §D4-R note + addendum, and MovesC/Defs.lean; full prompt/raw transcript archived at `/tmp/leanaudit_d7/` on the run machine.

1. **CRITICAL — `ShapeWF` still admits structurally impossible residue-degree shapes.**

   Offending spec:

   > `structure ShapeWF (n : ℕ) (P : ShapePrefix) : Prop where`
   >
   > `...`
   >
   > `def Shape (n : ℕ) : Type := {P : ShapePrefix // ShapeWF n P}`

   `ShapeRead.w` is L3's retained residue degree, but `ShapeWF` contains neither the root law `w₀ = 1` nor the transition law relating successive residue degrees (`w_{r+1} = w_r·g_r` at an increment and unchanged at a recentering). A root-only record with `w = 2` can satisfy every displayed certificate clause even though the root digits must lie in `F_p`, not `F_{p²}`. It therefore enters `Shape n`, while `Matches` is impossible and `PrefIdx` is empty. This recreates the degenerate-shape escape that the subtype was intended to eliminate.

2. **CRITICAL — SW1 assumes one of the certificate obligations it claims to derive.**

   Offending unit:

   > `theorem ShapeWF_of_matches ... (hmt : Q.MonicTie n) : ShapeWF n Q`

   The quoted `moves_ref` says every note-history shape is in the dictionary image and hence satisfies `ShapeWF`. But `MonicTie` is itself a component of `ShapeWF`, and SW1 assumes it rather than deriving it from matching, coherence, and the degree-`n` box. Indeed, `ShapeRead.Matches` only has

   > `(R.monicTop = true → ν.sideDigit R.len = 1)`

   so a full-span root can match a shape with `monicTop = false`. SW1 therefore does not establish the advertised "nothing of the note's universe is lost" bridge; its statement is strictly weaker than that claim.

3. **CRITICAL — L11/D4R.2 still lose the empty prefix.**

   Offending units:

   > `theorem encIdx_inj ... : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`

   > `theorem D4R2' ... : Nat.card (PrefIdx n pol P) ≤ ...`

   > `theorem D4R2'_full ... : Nat.card (PrefIdx n pol P) ≤ ... ∧ ...`

   For the empty shape, `PrefIdx` is empty because it is constructed from nonempty `History`, while the note has `Pref(∅) = {∅}` and `C_∅ = 1`. `PresentNorm` is vacuously satisfiable there, so `hnorm` does not repair this. Consequently E9 proves injectivity of an empty function rather than L11's singleton-to-unit encoding, and D3a/W3 prove a bound for `0` rather than the displayed bound for `C_∅ = 1`. F3 and `Shape.CD` model the singleton elsewhere, but these units do not use them or restrict themselves to nonempty shapes.

4. **GAP — the normative declaration order cannot elaborate.**

   Offending order/spec combination:

   > group (1): `... ShapeWF, Shape`
   >
   > group (2): `the shape replicas §3.3 IN FULL — strS ...`

   Yet `ShapeWF.gamTie` contains:

   > `(P.strS r : ℚ)`

   Lean has no forward declarations for this definition. `ShapePrefix.strS` must already exist when `ShapeWF` is declared. The claimed normative file order is therefore not Lean-plausible as written.

5. **GAP — `TreeModel` still lacks a typed exhaustive-child/cell-data law.**

   Offending spec:

   > `structure TreeModel ... where`
   >
   > `mem : Option (History p F) → Box p m → Prop`
   >
   > `child : Option (History p F) → Node p F → Box p m → Prop`
   >
   > `root_mem ...`
   >
   > `mem_single ...`
   >
   > `mem_snoc ...`
   >
   > `mem_realizable ...`

   L2 requires the children to be **all and only** eligible `(side, ψ)` continuations computed from the fixed digit cell. The displayed fields impose only recursive consistency between arbitrary `mem` and `child` relations. `D4R_CYL` constrains membership for the selected fixed-shape representatives but does not state exhaustive eligibility or exclude extra children. The essential L2/kernel-(b) dependency remains prose-only rather than a named hypothesis-field.

6. **GAP — the VerdictModel cure remains degenerate and does not express a uniform cap.**

   Offending fields:

   > `hCellFin : Finite Cell`

   > `cell_local : ... → cellOf o x = cellOf o x'`

   > `cap : V → ℕ`

   `Box p m` is already finite, so `Cell := Box p m` still satisfies `hCellFin`. Taking every `cap v > N` makes the locality premise require equality of every coordinate, allowing `cellOf := id`; alternatively constant cells remain possible when the verdict maps are constant. Nothing identifies `cellOf` with L5's full polygon/digit outcome or makes its fibers the exhaustive value-cell partition.

   Moreover, `VerdictModel` is parameterized by a single `N`, so `cap` can always depend implicitly on that level. This does not encode the addendum's **uniform per-class detection cap** across finite levels. Both the semantic cell tie and cross-level uniformity remain missing typed hypotheses.

Counts: **3 CRITICAL / 3 GAP**

**REJECT (3 crit / 3 gap)**
