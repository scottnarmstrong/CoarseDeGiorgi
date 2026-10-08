module

public import CoarseDeGiorgi.LowerFractional.CubeDomain
public import CoarseDeGiorgi.Localization.Geometry

/-! The unit cube `□₀` as the auxiliary cube `auxCube 1 0`, with its domain facts. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set Aliases
open scoped BigOperators ENNReal

lemma lower_unitCube_eq_auxCube {d : ℕ} :
    Aliases.originCube (d := d) 1 = auxCube 1 (fun _ => 0) := by
  ext x
  simp [Aliases.originCube, CoarseDeGiorgi.originCube, auxCube, abs_lt]

lemma lower_unitCube_domain {d : ℕ} : IsOpenBoundedConvexDomain (Aliases.originCube (d := d) 1) := by
  rw [lower_unitCube_eq_auxCube]
  exact auxCube_isOpenBoundedConvexDomain _ _

lemma lower_unitCube_nonempty {d : ℕ} : (Aliases.originCube (d := d) 1).Nonempty := by
  rw [lower_unitCube_eq_auxCube]
  exact auxCube_nonempty _ _


end CoarseDeGiorgi.LowerFractional
