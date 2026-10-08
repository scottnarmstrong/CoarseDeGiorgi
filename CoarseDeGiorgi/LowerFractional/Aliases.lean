import CoarseDeGiorgi.Statements.LowerResponseExistsUnique
import CoarseDeGiorgi.Statements.UpperResponseExistsUnique
import CoarseDeGiorgi.Statements.SimplexIndex
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.AuxCube
import CoarseDeGiorgi.Statements.AuxAverage
import CoarseDeGiorgi.Assembly.ParameterDefs
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.GridOffset
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.LowerResponseInv
import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.RBoundaryParam
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.Simplex
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
import CoarseDeGiorgi.Statements.SimplexCellNonempty
import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Triangulation
import CoarseDeGiorgi.Statements.TriangulationCard
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.UpperResponse
import CoarseDeGiorgi.Statements.UpperResponseOnCell
import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
import CoarseDeGiorgi.Moments.Cells
import Mathlib.Analysis.CStarAlgebra.Matrix

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
