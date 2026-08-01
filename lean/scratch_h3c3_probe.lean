-- I-H3c3 scratch probe: verify mathlib API names (NOT part of the corpus)
import Mathlib

open MeasureTheory

-- (1) eval-cons compatibility with finSuccEquiv
#check @MvPolynomial.eval_eq_eval_mv_eval'
-- (2) product-measure null-section theorem (first-factor sections)
#check @MeasureTheory.Measure.measure_prod_null
-- (3) swap
#check @MeasureTheory.Measure.prod_swap
#check @MeasureTheory.Measure.map_apply
#check @measurable_swap
-- (4) cast distribution over Fin.cons
#check @Fin.comp_cons
-- (5) aeval = eval over the base ring
#check @MvPolynomial.aeval_eq_eval
-- (6) ae / null tools
#check @MeasureTheory.measure_mono_null
#check @Filter.eventuallyEq_of_mem
#check @MeasureTheory.ae_iff
