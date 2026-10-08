import CoarseDeGiorgi.Foundations.Euclid.Kernel
import Homogenization.Sobolev.Fractional.Definitions

namespace CoarseDeGiorgi.Foundations.Euclid

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The unnormalized Euclidean fractional seminorm on an arbitrary set. -/
def eFracSeminorm (A : Set (Vec d)) (α r : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ xy, euclidKernel ((d : ℝ) + α * r) r u xy
    ∂((volume.restrict A).prod (volume.restrict A))) ^ (1 / r)

end

end CoarseDeGiorgi.Foundations.Euclid
