module

public import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyBlocks
public import CoarseDeGiorgi.Foundations.Reconstruction.AssemblySeries

/-! # Explicit inputs: the block bounds and the smoothing convergence

All objects use the existing reconstruction kernels and reflected averages.
Neither input contains a fractional seminorm conclusion. The finite-series
premise in the tail bound is exactly the case used in the assembly.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The precise nonnegative series on the right of `e.fractional.reconstruction`. -/
def assemblySourceSeries {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    (Dw : Vec d → Vec d) (α r : ℝ) : ℝ≥0∞ :=
  ∑' k : {k : ℤ // m ≤ k},
    ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
      eLpNorm (fun x => CoarseDeGiorgi.euclidNorm
        (CoarseDeGiorgi.auxAverage m k.1 z Dw x))
        (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z))

/-- The `L^r` size `A_j` of the reflected gradient average at level `j` (Euclidean length). -/
def assemblyAverageSize {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    (Dw : Vec d → Vec d) (r : ℝ) (j : ℕ) : ℝ≥0∞ :=
  eLpNorm (fun x => euclidNorm (reflectedAverage m j z Dw x))
    (ENNReal.ofReal r) (volume.restrict (reflectionBox m))

/-- The exact gradient-average tail in `AssemblyTailBounds`; no norm of `Dw` appears. -/
def assemblyGradientTail {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    (Dw : Vec d → Vec d) (r : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, if j ≤ k then ENNReal.ofReal (auxSide (m + k)) *
    assemblyAverageSize m z Dw r k else 0

/-- The block bounds: the `L^r` and translation bounds with a uniform positive constant.
Steps 4–7 produce this from the physical kernels and both cancellation bounds. -/
def AssemblyTailBounds (d : ℕ) (α r : ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (Dw : Vec d → Vec d),
      HasWeakGradientOn (CoarseDeGiorgi.auxCube m z) w Dw →
      IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume →
      IntegrableOn Dw (CoarseDeGiorgi.auxCube m z) volume →
      MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) →
      assemblySourceSeries m z Dw α r < ∞ →
      ∀ j : ℕ,
        eLpNorm (assemblyBlock m z w j) (ENNReal.ofReal r)
          (volume.restrict (reflectionBox m)) ≤
            ENNReal.ofReal C₁ * assemblyGradientTail m z Dw r j ∧
        ∀ u : Vec d,
          eLpNorm (fun x => assemblyBlock m z w j (x + u) - assemblyBlock m z w j x)
            (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
              ENNReal.ofReal C₁ * ENNReal.ofReal (min 1 (euclidNorm u / auxSide (m + j))) *
                assemblyGradientTail m z Dw r j

/-- The concrete periodic smoothing converges in `L^r`.
This uses the assumed `L^r` function norm, with no gradient `L^r` premise. -/
def AssemblySmoothingConvergence (d : ℕ) (r : ℝ) : Prop :=
  ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ),
    IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume →
    MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) →
    Tendsto (fun n : ℕ =>
      eLpNorm (fun x => smoothAverage m (auxSide (m + n)) z w x - reflectedScalar m z w x)
        (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) atTop (𝓝 0)

/-- The Step 3 reflection factor in the exact notation consumed by the assembly. -/
theorem assemblyAverageSize_eq {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    (Dw : Vec d → Vec d) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    assemblyAverageSize m z Dw r j = ((2 : ℝ≥0∞) ^ d) ^ (1 / r) *
      eLpNorm (fun x => CoarseDeGiorgi.euclidNorm
        (CoarseDeGiorgi.auxAverage m (m + j) z Dw x))
        (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) := by
  have he := eLpNorm_euclidNorm_reflectedAverage m j z Dw (ENNReal.ofReal r)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top
  have h_normAverage (x : Vec d) : euclidNorm (auxAverage m (m + j) z Dw x) =
      CoarseDeGiorgi.euclidNorm (CoarseDeGiorgi.auxAverage m (m + j) z Dw x) := rfl
  simpa only [assemblyAverageSize, ENNReal.toReal_ofReal hr.le,
    auxCube_eq_statement, h_normAverage] using he

end
end CoarseDeGiorgi.Foundations.Reconstruction
