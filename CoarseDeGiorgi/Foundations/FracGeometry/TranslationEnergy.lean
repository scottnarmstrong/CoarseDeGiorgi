import CoarseDeGiorgi.Foundations.FracGeometry.CutoffPointwise
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem measurable_translationDifference {F : Vec d → ℝ} (hF : Measurable F)
    (r : ℝ) : Measurable (fun zx : Vec d × Vec d =>
      ENNReal.ofReal (|F (zx.2 + zx.1) - F zx.2| ^ r)) := by
  simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.add_apply, id_eq] using (((hF.comp (measurable_snd.add measurable_fst)).sub
    (hF.comp measurable_snd)).norm.pow measurable_const).ennreal_ofReal

theorem measurable_euclidKernel (β r : ℝ) {F : Vec d → ℝ} (hF : Measurable F) :
    Measurable (Euclid.euclidKernel β r F) := by
  change Measurable (fun xy : Vec d × Vec d =>
    ENNReal.ofReal (|F xy.1 - F xy.2| ^ r / Euclid.eDist2 xy.1 xy.2 ^ β))
  simpa only [Euclid.euclidKernel, Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using ((((hF.comp measurable_fst).sub (hF.comp measurable_snd)).norm.pow
    measurable_const).div (Euclid.continuous_eDist2.measurable.pow
      measurable_const)).ennreal_ofReal

end

end CoarseDeGiorgi.Foundations.FracGeometry
