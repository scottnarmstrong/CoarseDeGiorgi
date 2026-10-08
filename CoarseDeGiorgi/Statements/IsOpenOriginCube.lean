import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.NegSobolev.SobolevNormFacts
open Homogenization MeasureTheory

namespace CoarseDeGiorgi

/-- The cubes `ρ □₀` are open ("Cubes and simplices are open"). -/
theorem isOpen_originCube {d : ℕ} (ρ : ℝ) : IsOpen (originCube (d := d) ρ)
:=
  by exact CoarseDeGiorgi.NegSobolev.isOpen_originCube ρ

end CoarseDeGiorgi
