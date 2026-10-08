module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.AuxAverage
public import CoarseDeGiorgi.Statements.AuxCube
public import CoarseDeGiorgi.Assembly.ParameterDefs
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Statements.GridOffset
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.LowerCellAverage
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.LowerResponseInv
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.PositiveTruncationGradient
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
public import CoarseDeGiorgi.Statements.TwoLevelQuantity
public import CoarseDeGiorgi.Statements.UpperCellAverage
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.UpperResponse
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.UpperResponseExistsUnique
public import CoarseDeGiorgi.Statements.LowerResponseExistsUnique
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Assembly.Aliases

/-! Compatibility aliases for `Statements/` definitions. -/

abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

end CoarseDeGiorgi.Assembly.Aliases
