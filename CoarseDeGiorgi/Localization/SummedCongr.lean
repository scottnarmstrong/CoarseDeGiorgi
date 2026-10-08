import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.FracKernel
import CoarseDeGiorgi.Statements.FracSeminorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # The fractional norms only depend on the a.e. class -/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ}

theorem fracSeminorm_congr_ae {V : Set (Vec d)} {α r : ℝ} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict V] g) : fracSeminorm V α r f = fracSeminorm V α r g := by
  unfold fracSeminorm
  congr 1
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ p : Vec d × Vec d ∂((volume.restrict V).prod (volume.restrict V)), f p.1 = g p.1 :=
    Measure.quasiMeasurePreserving_fst.ae h
  have h2 : ∀ᵐ p : Vec d × Vec d ∂((volume.restrict V).prod (volume.restrict V)), f p.2 = g p.2 :=
    Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [h1, h2] with p hp1 hp2
  simp only [fracKernel, fracKernelWithDimension, hp1, hp2]

theorem fracNorm_congr_ae {V : Set (Vec d)} {α r : ℝ} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict V] g) : fracNorm V α r f = fracNorm V α r g := by
  unfold fracNorm
  rw [eLpNorm_congr_ae h, fracSeminorm_congr_ae h]

end
end CoarseDeGiorgi.Localization
