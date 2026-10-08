module

public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.Triangulation

@[expose] public section

open Homogenization MeasureTheory

namespace CoarseDeGiorgi

/-- `𝒯_k(U) := {△ ∈ 𝒯_k : △ ⊂ U}`: the simplices of the `k`-th triadic triangulation of `□₀`
contained in `U`. -/
noncomputable def triangulationIn {d : ℕ} (k : ℕ) (U : Set (Vec d)) : Finset (SimplexIndex d k) := by
  classical
  exact (triangulation (d := d) k).attach.filter (fun η => simplexCell k η ⊆ U)

end CoarseDeGiorgi
