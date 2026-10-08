module

public import CoarseDeGiorgi.Statements.IsWeakDerivArray

public import CoarseDeGiorgi.NegSobolev.SobolevNormFacts

@[expose] public section

open Homogenization MeasureTheory

namespace CoarseDeGiorgi

/-- On an open set, weak derivative arrays of a given order are unique almost everywhere. -/
theorem isWeakDerivArray_ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {j : ℕ}
    {w : Vec d → ℝ} {D D' : (Fin j → Fin d) → Vec d → ℝ}
    (hD : IsWeakDerivArray U j w D) (hD' : IsWeakDerivArray U j w D')
    (ι : Fin j → Fin d) : D ι =ᵐ[volume.restrict U] D' ι
:=
  by exact CoarseDeGiorgi.NegSobolev.isWeakDerivArray_ae_eq hU hD hD' ι

end CoarseDeGiorgi
