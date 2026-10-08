module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
public import CoarseDeGiorgi.Statements.LowerCellAverage
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import CoarseDeGiorgi.Statements.TriangulationCard
public import CoarseDeGiorgi.Statements.UpperCellAverage
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.LowerFractional.CompactCover
public import CoarseDeGiorgi.Weighted.LowerSpecNorm
public import CoarseDeGiorgi.Weighted.ResponseBoundsLower
public import CoarseDeGiorgi.Weighted.UpperSpecHarmonic
public import CoarseDeGiorgi.Weighted.UpperSpecNorm
public import CoarseDeGiorgi.Weighted.ZeroBoundary
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem halfPower_sq (x : ENNReal) : (x.rpow (1 / 2)) ^ 2 = x := by
  simpa using Assembly.ClassicalMomentsImpl.half_power_sq x (p := 1) (by norm_num)

end CoarseDeGiorgi.Harnack.Moments
