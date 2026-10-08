module

public import Mathlib
public import CoarseDeGiorgiAudit.Defs
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsSmoothCore
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.HarnackEtaParam

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgiAudit

theorem vec_type_eq (d : ℕ) : Vec d = Homogenization.Vec d := rfl

theorem mat_type_eq (d : ℕ) : Mat d = Homogenization.Mat d := rfl

theorem coeffField_type_eq (d : ℕ) : CoeffField d = Homogenization.CoeffField d := rfl

theorem vecDot_eq {d : ℕ} (x y : Vec d) :
    vecDot x y = Homogenization.vecDot x y := rfl

theorem matVecMul_eq {d : ℕ} (A : Mat d) (x : Vec d) :
    matVecMul A x = Homogenization.matVecMul A x := rfl

theorem basisVec_eq {d : ℕ} (i : Fin d) :
    basisVec i = Homogenization.basisVec i := rfl

theorem smoothGrad_eq {d : ℕ} (φ : Vec d → ℝ) :
    smoothGrad φ = CoarseDeGiorgi.smoothGrad φ := rfl

theorem weightedEnergy_eq {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) :
    weightedEnergy a U G = CoarseDeGiorgi.weightedEnergy a U G := rfl

theorem volumeAverage_eq {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage U f = Homogenization.volumeAverage U f := rfl

theorem originCube_eq {d : ℕ} (ρ : ℝ) :
    originCube (d := d) ρ = CoarseDeGiorgi.originCube (d := d) ρ := rfl

theorem isWeightedCoeffOn_iff {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) :
    IsWeightedCoeffOn V a ↔ CoarseDeGiorgi.IsWeightedCoeffOn V a := Iff.rfl

theorem isSmoothCore_iff {d : ℕ} (a : CoeffField d) (V : Set (Vec d)) (φ : Vec d → ℝ) :
    IsSmoothCore a V φ ↔ CoarseDeGiorgi.IsSmoothCore a V φ := Iff.rfl

theorem memH1a_iff {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) :
    MemH1a a V u G ↔ CoarseDeGiorgi.MemH1a a V u G := Iff.rfl

theorem isWeightedSubsolution_iff {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSubsolution a V u G ↔ CoarseDeGiorgi.IsWeightedSubsolution a V u G := Iff.rfl

theorem isWeightedSupersolution_iff {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSupersolution a V u G ↔ CoarseDeGiorgi.IsWeightedSupersolution a V u G := Iff.rfl

theorem isWeightedSolution_iff {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSolution a V u G ↔ CoarseDeGiorgi.IsWeightedSolution a V u G := Iff.rfl

theorem locallyBoundedAbove_iff {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    LocallyBoundedAbove V u ↔ CoarseDeGiorgi.LocallyBoundedAbove V u := Iff.rfl

theorem positivePart_eq {d : ℕ} (u : Vec d → ℝ) :
    positivePart u = CoarseDeGiorgi.positivePart u := rfl

theorem nonnegativeEssInf_eq {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    nonnegativeEssInf V u = CoarseDeGiorgi.nonnegativeEssInf V u := rfl

theorem normalizedLpMoment_eq {d : ℕ} (b : ℝ) (hb : 0 < b)
    (V : Set (Vec d)) (u : Vec d → ℝ) :
    normalizedLpMoment b hb V u = CoarseDeGiorgi.normalizedLpMoment b hb V u := rfl

theorem paramR_eq (q : ℝ) : paramR q = CoarseDeGiorgi.paramR q := rfl

theorem harnackEtaParam_eq (q : ℝ) :
    harnackEtaParam q = CoarseDeGiorgi.harnackEtaParam q := rfl

end CoarseDeGiorgiAudit
