import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
import CoarseDeGiorgi.Statements.TriangulationCard
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.UpperResponseOnCell
import CoarseDeGiorgi.LowerFractional.CompactCover
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import CoarseDeGiorgi.Weighted.ResponseBoundsLower
import CoarseDeGiorgi.Weighted.UpperSpecHarmonic
import CoarseDeGiorgi.Weighted.UpperSpecNorm
import CoarseDeGiorgi.Weighted.ZeroBoundary
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem halfPower_sq (x : ENNReal) : (x.rpow (1 / 2)) ^ 2 = x := by
  simpa using Assembly.ClassicalMomentsImpl.half_power_sq x (p := 1) (by norm_num)

end CoarseDeGiorgi.Harnack.Moments
