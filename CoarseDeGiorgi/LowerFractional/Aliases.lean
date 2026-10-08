module

public import CoarseDeGiorgi.Statements.LowerResponseExistsUnique
public import CoarseDeGiorgi.Statements.UpperResponseExistsUnique
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.AuxCube
public import CoarseDeGiorgi.Statements.AuxAverage
public import CoarseDeGiorgi.Assembly.ParameterDefs
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Statements.GridOffset
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.LowerCellAverage
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.LowerResponseInv
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.RBoundaryParam
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.Simplex
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.TriangulationCard
public import CoarseDeGiorgi.Statements.UpperCellAverage
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.UpperResponse
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
public import CoarseDeGiorgi.Moments.Cells
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.LowerFractional.Aliases

/-! Compatibility aliases for the `Statements/` definitions. The response
uniqueness and geometric facts below are direct exports of the stated theorems. -/




noncomputable abbrev lowerResponseInv {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d := CoarseDeGiorgi.lowerResponseInv a V hV hV₀ ha

abbrev simplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Set (Vec d) :=
  CoarseDeGiorgi.simplex n π z



abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

abbrev SimplexIndex (d k : ℕ) := CoarseDeGiorgi.SimplexIndex d k

abbrev simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  CoarseDeGiorgi.simplexCell k η


theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) :=
  CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain k η

theorem simplexCell_nonempty {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (simplexCell k η).Nonempty := CoarseDeGiorgi.simplexCell_nonempty k η














end CoarseDeGiorgi.LowerFractional.Aliases
