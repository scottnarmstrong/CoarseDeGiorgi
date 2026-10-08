module

public import CoarseDeGiorgi.Statements.EuclidDist
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Basic.NNReal.Defs

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `Lip(f)` on `S` for the Euclidean distance (Section `s.whitney.extension`: "Lip refers to Euclidean
distance"): the smallest Lipschitz constant, `⊤` if `f` is not Lipschitz on `S`. -/
noncomputable def euclidLipConst {d : ℕ} (S : Set (Vec d)) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨅ (K : ℝ≥0) (_ : ∀ x ∈ S, ∀ y ∈ S,
      ENNReal.ofReal |f x - f y| ≤ (K : ℝ≥0∞) * ENNReal.ofReal (euclidDist x y)),
    (K : ℝ≥0∞)

end CoarseDeGiorgi
