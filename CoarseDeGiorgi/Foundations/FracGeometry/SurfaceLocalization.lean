import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSupport
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceVolume

namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory Set
open scoped ENNReal
noncomputable section

def powerIntegral {d : ℕ} (r : ℝ) (g : Vec d → ℝ) (μ : Measure (Vec d)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|g x| ^ r) ∂μ

theorem measurable_power {d : ℕ} (r : ℝ) {g : Vec d → ℝ} (hg : Measurable g) :
    Measurable (fun x => ENNReal.ofReal (|g x| ^ r)) := by
  simpa only [Real.norm_eq_abs] using (hg.norm.pow measurable_const).ennreal_ofReal

end
end CoarseDeGiorgi.Foundations.FracGeometry
