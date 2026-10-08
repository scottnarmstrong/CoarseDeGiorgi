module

public import Mathlib
public import CoarseDeGiorgiAudit.Defs
public import CoarseDeGiorgiAudit.DefsCells
public import CoarseDeGiorgiAudit.Solution.HarnackUniform
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessUniform

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit

namespace HarnackUniform

theorem vec_type_eq (d : ℕ) : Vec d = CoarseDeGiorgiAudit.Vec d := rfl
theorem mat_type_eq (d : ℕ) : Mat d = CoarseDeGiorgiAudit.Mat d := rfl
theorem coeffField_type_eq (d : ℕ) :
    CoeffField d = CoarseDeGiorgiAudit.CoeffField d := rfl
theorem cube_eq {d : ℕ} (ρ : ℝ) :
    cube (d := d) ρ = CoarseDeGiorgiAudit.originCube ρ := rfl
theorem weightedEnergy_eq {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) :
    weightedEnergy a U G = CoarseDeGiorgiAudit.weightedEnergy a U G := rfl
theorem averageOn_eq {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    averageOn U f = CoarseDeGiorgiAudit.volumeAverage U f := rfl
theorem smoothGrad_eq {d : ℕ} (φ : Vec d → ℝ) :
    smoothGrad φ = CoarseDeGiorgiAudit.smoothGrad φ := rfl
theorem isSmoothCore_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) :
    IsSmoothCore a V φ ↔ CoarseDeGiorgiAudit.IsSmoothCore a V φ := Iff.rfl
theorem memH1a_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    MemH1a a V u G ↔ CoarseDeGiorgiAudit.MemH1a a V u G := Iff.rfl

theorem isWeightedSolution_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSolution a V u G ↔
      CoarseDeGiorgiAudit.IsWeightedSolution a V u G := Iff.rfl

theorem essInfNonneg_eq {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    essInfNonneg V u = CoarseDeGiorgiAudit.nonnegativeEssInf V u := rfl

theorem uniformlyElliptic_iff {d : ℕ} (lam Λ : ℝ)
    (a : CoeffField d) :
    UniformlyElliptic lam Λ a ↔
      ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgiAudit.originCube 1)),
        (a x).IsHermitian ∧ ∀ ξ : Vec d,
          lam * dotProduct ξ ξ ≤ dotProduct ξ ((a x).mulVec ξ) ∧
          dotProduct ξ ((a x).mulVec ξ) ≤ Λ * dotProduct ξ ξ := Iff.rfl

end HarnackUniform

namespace LocalBoundednessUniform

theorem vec_type_eq (d : ℕ) : Vec d = CoarseDeGiorgiAudit.Vec d := rfl
theorem mat_type_eq (d : ℕ) : Mat d = CoarseDeGiorgiAudit.Mat d := rfl
theorem coeffField_type_eq (d : ℕ) :
    CoeffField d = CoarseDeGiorgiAudit.CoeffField d := rfl
theorem cube_eq {d : ℕ} (ρ : ℝ) :
    cube (d := d) ρ = CoarseDeGiorgiAudit.originCube ρ := rfl
theorem weightedEnergy_eq {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) :
    weightedEnergy a U G = CoarseDeGiorgiAudit.weightedEnergy a U G := rfl
theorem averageOn_eq {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    averageOn U f = CoarseDeGiorgiAudit.volumeAverage U f := rfl
theorem smoothGrad_eq {d : ℕ} (φ : Vec d → ℝ) :
    smoothGrad φ = CoarseDeGiorgiAudit.smoothGrad φ := rfl
theorem isSmoothCore_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) :
    IsSmoothCore a V φ ↔ CoarseDeGiorgiAudit.IsSmoothCore a V φ := Iff.rfl
theorem memH1a_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    MemH1a a V u G ↔ CoarseDeGiorgiAudit.MemH1a a V u G := Iff.rfl

theorem isWeightedSubsolution_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSubsolution a V u G ↔
      CoarseDeGiorgiAudit.IsWeightedSubsolution a V u G := Iff.rfl

theorem locallyBoundedAbove_iff {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) :
    LocallyBoundedAbove V u ↔
      CoarseDeGiorgiAudit.LocallyBoundedAbove V u := Iff.rfl

theorem positivePart_eq {d : ℕ} (u : Vec d → ℝ) :
    positivePart u = CoarseDeGiorgiAudit.positivePart u := rfl

theorem uniformlyElliptic_iff {d : ℕ} (lam Λ : ℝ)
    (a : CoeffField d) :
    UniformlyElliptic lam Λ a ↔
      ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgiAudit.originCube 1)),
        (a x).IsHermitian ∧ ∀ ξ : Vec d,
          lam * dotProduct ξ ξ ≤ dotProduct ξ ((a x).mulVec ξ) ∧
          dotProduct ξ ((a x).mulVec ξ) ≤ Λ * dotProduct ξ ξ := Iff.rfl

end LocalBoundednessUniform

end CoarseDeGiorgiAudit
