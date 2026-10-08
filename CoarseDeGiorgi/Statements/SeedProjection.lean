import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def seedProjection {d : ℕ} (τ : ℝ) (x : Vec d) : Vec d :=
  fun i => max (-τ / 2) (min (x i) (τ / 2))

end CoarseDeGiorgi
