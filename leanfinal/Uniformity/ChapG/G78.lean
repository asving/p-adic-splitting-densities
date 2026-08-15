/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG

/-!
# Uniformity.ChapG.G78 — CHAPTER G'S AXIOM-FOOTPRINT CENSUS

**Chapter G, NODE G.78** (`blueprint/CHAP-G_base_cases_menus.md` §10). Not a proof — a
build-time census, in the style of the landed `Gates.lean:589` and `Drainage.lean:1160`
blocks. One `#print axioms` line per PUBLIC declaration of chapter G: **155 declarations**
across **95** node modules. Every line must report `[propext, Classical.choice, Quot.sound]`
or a subset of it; anything else is a stop-the-line event (repo `CLAUDE.md`: "Ground truth
for the trusted base").

The lines below are harvested from the per-node `section AxCheck` blocks, so this census
cannot drift from the node files. The chapter's eight PURE-DEFINITION nodes (G.01, G.05,
G.09, G.15, G.19, G.22, G.62, G.64) carry no `AxCheck` block of their own — a `#print axioms`
on a plain `def` is vacuous — so their definitions are censused here directly, which is why
this file, and not the union of the node blocks, is the chapter's complete footprint record.
`private` declarations are deliberately absent — they are not part of the chapter contract.

DEPENDS: every node (via the `Uniformity.ChapG` roll-up).

## Status

Sorry-free, axiom-free (Lean core only) — which is exactly what the lines below assert.
-/

section AxCheck

-- G01
#print axioms Uniformity.Density.Menu.ExactVal

-- G02
#print axioms Uniformity.Density.Menu.exactVal_iff_addVal
#print axioms Uniformity.Density.Menu.exactVal_unique

-- G03
#print axioms Uniformity.Density.Menu.readEquiv

-- G04
#print axioms Uniformity.Density.Menu.readEquiv_proj

-- G05
#print axioms Uniformity.Density.Menu.CertFamily
#print axioms Uniformity.Density.Menu.CertFamily.set

-- G06
#print axioms Uniformity.Density.Menu.CertFamily.decidedAt

-- G07
#print axioms Uniformity.Density.Menu.CertFamily.card

-- G08
#print axioms Uniformity.Density.Menu.CertFamily.decidedDensity_ge

-- G09
#print axioms Uniformity.Density.Menu.tangSet

-- G10
#print axioms Uniformity.Density.Menu.tang_shift

-- G11
#print axioms Uniformity.Density.Menu.tang_centre_unique

-- G12
#print axioms Uniformity.Density.Menu.tang_of_proj_eq

-- G13
#print axioms Uniformity.Density.Menu.mem_tangSet_iff
#print axioms Uniformity.Density.Menu.tangSet_antitone

-- G14
#print axioms Uniformity.Density.Menu.card_dvdSet
#print axioms Uniformity.Density.Menu.card_exactSet_add

-- G15
#print axioms Uniformity.Density.Menu.tangAdm

-- G16
#print axioms Uniformity.Density.Menu.card_tangAdm

-- G17
#print axioms Uniformity.Density.Menu.card_tangSet

-- G18
#print axioms Uniformity.Density.Menu.mem_dvdSet_iff_dvd
#print axioms Uniformity.Density.Menu.tangCert

-- G19
#print axioms Uniformity.Density.Menu.depthSet

-- G20
#print axioms Uniformity.Density.Menu.card_depthSet

-- G21
#print axioms Uniformity.Density.Menu.residualPair

-- G22
#print axioms Uniformity.Density.Menu.resStratum

-- G23R1
#print axioms Uniformity.Density.Menu.prodResFactor
#print axioms Uniformity.Density.Menu.card_preimage_prodResFactor

-- G23R2
#print axioms Uniformity.Density.Menu.residue_eq_of_mk_pow_mul_eq
#print axioms Uniformity.Density.Menu.mk_pow_mul_eq_of_residue_eq

-- G23R3
#print axioms Uniformity.Density.Menu.transPair
#print axioms Uniformity.Density.Menu.TransInvariant
#print axioms Uniformity.Density.Menu.aniForm_transInvariant
#print axioms Uniformity.Density.Menu.sepPair_transInvariant
#print axioms Uniformity.Density.Menu.aniForm_not_dblPair
#print axioms Uniformity.Density.Menu.sepPair_not_dblPair

-- G23R4
#print axioms Uniformity.Density.Menu.resTop
#print axioms Uniformity.Density.Menu.resAdm
#print axioms Uniformity.Density.Menu.resClassSet
#print axioms Uniformity.Density.Menu.resAdm_eq_preimage

-- G23R5
#print axioms Uniformity.Density.Menu.card_resTop

-- G23R6
#print axioms Uniformity.Density.Menu.card_resAdm

-- G23R7
#print axioms Uniformity.Density.Menu.resAdm_read_iff

-- G23R8
#print axioms Uniformity.Density.Menu.resCert

-- G23R9
#print axioms Uniformity.Density.Menu.card_resClassSet

-- G23R10
#print axioms Uniformity.Density.Menu.residualPair_eq
#print axioms Uniformity.Density.Menu.mem_resClassSet_iff_residualPair

-- G23R11
#print axioms Uniformity.Density.Menu.resClassSet_subset_depthSet

-- G23R12
#print axioms Uniformity.Density.Menu.residue_eq_zero_iff_dvd
#print axioms Uniformity.Density.Menu.aniso_iff_aniForm
#print axioms Uniformity.Density.Menu.sepPair_iff_exists_simple_root

-- G24
#print axioms Uniformity.Density.Menu.certRam_of_depth_odd

-- G25
#print axioms Uniformity.Density.Menu.decidedAt_ram_of_depth_odd

-- G26
#print axioms Uniformity.Density.Menu.depth_even_dichotomy

-- G27
#print axioms Uniformity.Density.Menu.decidedAt_inert_of_ani

-- G28
#print axioms Uniformity.Density.Menu.decidedAt_split_of_sep

-- G29
#print axioms Uniformity.Density.Menu.decidedAt_of_depth_lt

-- G30
#print axioms Uniformity.Density.Menu.depth_type

-- G30a
#print axioms Uniformity.Density.Menu.depthSet_odd_eq_empty

-- G31
#print axioms Uniformity.Density.Menu.decidedSet_ram_eq

-- G32
#print axioms Uniformity.Density.Menu.exists_aniForm_of_ne_zero

-- G33
#print axioms Uniformity.Density.Menu.exists_split_lift

-- G34
#print axioms Uniformity.Density.Menu.exists_inert_lift_of_ne_zero
#print axioms Uniformity.Density.Menu.exists_inert_lift

-- G35
#print axioms Uniformity.Density.Menu.undecidedSet_eq_tangSet

-- G36
#print axioms Uniformity.Density.undecidedCount_two_eq

-- G37
#print axioms Uniformity.Density.undecidedSeq_two_eq
#print axioms Uniformity.Density.gapSeq_two_le

-- G38
#print axioms Uniformity.Density.Menu.two_mul_card_aniForm

-- G39
#print axioms Uniformity.Density.Menu.two_mul_card_sepPair

-- G40
#print axioms Uniformity.Density.Menu.dblPair_inj
#print axioms Uniformity.Density.Menu.card_dblPair
#print axioms Uniformity.Density.Menu.pair_trichotomy

-- G41
#print axioms Uniformity.Density.Menu.card_biUnion_range_of_disjoint
#print axioms Uniformity.Density.Menu.depthSet_disjoint
#print axioms Uniformity.Density.Menu.stratum_eq_resClassSet
#print axioms Uniformity.Density.Menu.inertStratum_eq
#print axioms Uniformity.Density.Menu.decidedSet_inert_eq
#print axioms Uniformity.Density.Menu.card_inertStratum

-- G42
#print axioms Uniformity.Density.Menu.splitStratum_eq
#print axioms Uniformity.Density.Menu.decidedSet_split_eq
#print axioms Uniformity.Density.Menu.card_splitStratum

-- G43
#print axioms Uniformity.Density.decidedCount_split_eq_inert

-- G44
#print axioms Uniformity.Density.decidedSeq_two_ram_eq
#print axioms Uniformity.Density.decidedSeq_two_inert_eq

-- G45
#print axioms Uniformity.Density.Menu.tendsto_geom_partial

-- G46
#print axioms Uniformity.Density.decidedDensity_two_ram_eq

-- G47
#print axioms Uniformity.Density.decidedDensity_two_inert_eq
#print axioms Uniformity.Density.decidedDensity_two_split_eq
#print axioms Uniformity.Density.decidedDensity_two_split_eq_of_total

-- G48
#print axioms Uniformity.Density.genuineDensity_two_exact

-- G49
#print axioms Uniformity.Density.gate_two_padic_two_exact
#print axioms Uniformity.Density.gate_two_padic_three_exact

-- G50
#print axioms Uniformity.Density.degree_two_type_cases

-- G51
#print axioms Uniformity.Density.uniformityStatement_two

-- G52
#print axioms Uniformity.Density.c3_degrees
#print axioms Uniformity.Density.c3_pairwise_ne

-- G53
#print axioms Uniformity.Density.typeOf_three_cases

-- G54
#print axioms Uniformity.Density.coveringMenu_three
#print axioms Uniformity.Density.genuineDensity_three_eq_zero

-- G55
#print axioms Uniformity.Density.typeOf_split3_of_residue

-- G56
#print axioms Uniformity.Density.typeOf_linInert_of_residue

-- G57
#print axioms Uniformity.Density.typeOf_inert3_of_irreducible_map

-- G58
#print axioms Uniformity.Density.typeOf_ram3_of_eisenstein

-- G59
#print axioms Uniformity.Density.typeOf_linRam_of_residue

-- G60
#print axioms Uniformity.Density.Menu.three_mul_card_noRootCubic
#print axioms Uniformity.Density.Menu.two_mul_card_linAni
#print axioms Uniformity.Density.Menu.six_mul_card_split3

-- G61
#print axioms Uniformity.Density.lowers_three

-- G61I
#print axioms Uniformity.Density.decidedDensity_ge_of_inj
#print axioms Uniformity.Density.sub_mem_of_residue_eq
#print axioms Uniformity.Density.isUnit_sub_of_residue_ne
#print axioms Uniformity.Density.Menu.res1Equiv
#print axioms Uniformity.Density.Menu.res1Equiv_mk
#print axioms Uniformity.Density.Menu.liftRes1
#print axioms Uniformity.Density.Menu.liftRes1_injective
#print axioms Uniformity.Density.Menu.residue_comp_of_proj_liftRes1
#print axioms Uniformity.Density.Menu.unitSet
#print axioms Uniformity.Density.Menu.card_dvdSet_two
#print axioms Uniformity.Density.Menu.card_exactSet_two
#print axioms Uniformity.Density.Menu.card_unitSet_two
#print axioms Uniformity.Density.Menu.dvd_of_mem_dvdSet
#print axioms Uniformity.Density.Menu.mem_dvdSet_of_dvd

-- G61a
#print axioms Uniformity.Density.typeOf_split3_of_deep
#print axioms Uniformity.Density.split3_decided
#print axioms Uniformity.Density.gate_split3_lower

-- G61b
#print axioms Uniformity.Density.linInert_decided_res
#print axioms Uniformity.Density.gate_linInert3_lower

-- G61c
#print axioms Uniformity.Density.inert3_decided
#print axioms Uniformity.Density.gate_inert3_lower

-- G61d
#print axioms Uniformity.Density.linRam_decided
#print axioms Uniformity.Density.gate_linRam3_lower

-- G61e
#print axioms Uniformity.Density.ram3_decided
#print axioms Uniformity.Density.gate_ram3_lower

-- G62
#print axioms Uniformity.Density.Menu.CubicFamilyIndex
#print axioms Uniformity.Density.Menu.CubicFamilyIndex.schema

-- G63
#print axioms Uniformity.Density.Menu.card_cubicFamilyIndex
#print axioms Uniformity.Density.Menu.schema_surjective

-- G64
#print axioms Uniformity.Density.Menu.hex3R

-- G65
#print axioms Uniformity.Density.Menu.hex3R_rec

-- G66
#print axioms Uniformity.Density.Menu.hex3U

-- G67
#print axioms Uniformity.Density.Menu.hex3U_rec

-- G68
#print axioms Uniformity.Density.Menu.two_mul_hex3R_le

-- G69
#print axioms Uniformity.Density.Menu.hex3U_le

-- G70
#print axioms Uniformity.Density.Menu.hex3U_div_tendsto_zero

-- G71
#print axioms Uniformity.Density.drainage_three_of_hex3_bound

-- G72
#print axioms Uniformity.Density.totalMass_three_of_drainage
#print axioms Uniformity.Density.one_le_sum_three

-- G73
#print axioms Uniformity.Density.Menu.card_species3

-- G74
#print axioms Uniformity.Density.exists_split3_lift

-- G75
#print axioms Uniformity.Density.exists_ram3_lift

-- G76
#print axioms Uniformity.Density.card_le_undecidedCount_three

-- G77
#print axioms Uniformity.Density.gate_three_padic_two
#print axioms Uniformity.Density.gate_three_hmenu3_containment_two

end AxCheck
