module

public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory

namespace CoarseDeGiorgi

theorem originCube_one_eq_cg (d : ℕ) :
    originCube (d := d) 1 = Homogenization.openCubeSet (Homogenization.originCube d 0) :=
  by
  ext x
  simp [originCube, Homogenization.openCubeSet, Homogenization.originCube,
    Homogenization.cubeScaleFactor]

end CoarseDeGiorgi
