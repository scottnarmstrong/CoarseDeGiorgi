import CoarseDeGiorgi.Statements.WhitneyCubes
import CoarseDeGiorgi.Statements.InfSupDist
import CoarseDeGiorgi.Statements.PointSupDist
import CoarseDeGiorgi.Foundations.Triadic.LocalFiniteness

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

variable {d : ℕ}

/-- The `Statements/` closed cube is the closed cube used by the triadic infrastructure. -/
theorem closedTriadicCube_eq_closedCube (D : TriadicCube d) :
    closedTriadicCube D = closedCube D := rfl

/-- The two ways of writing the fivefold radius agree. -/
theorem fivefoldClosedTriadicCube_eq_fivefoldCube (D : TriadicCube d) :
    fivefoldClosedTriadicCube D = fivefoldCube D := by
  have hrad : (5 / 2 : ℝ) * cubeScaleFactor D = 5 * cubeScaleFactor D / 2 := by ring
  ext x
  simp only [fivefoldClosedTriadicCube, fivefoldCube, Set.mem_ofPred_eq,
    triadicCenter, center, hrad]

/-- The `Statements/` reference cube is the reference cube used by the infrastructure. -/
theorem closedReferenceCube_eq_referenceCube (τ : ℝ) :
    closedReferenceCube (d := d) τ = referenceCube τ := rfl

/-- `whitneyAdmissible` is exactly fivefold disjointness in the local API. -/
theorem whitneyAdmissible_iff_admissible (τ : ℝ) (D : TriadicCube d) :
    whitneyAdmissible τ D ↔ Admissible τ D := by
  rw [whitneyAdmissible, Admissible, fivefoldClosedTriadicCube_eq_fivefoldCube,
    closedReferenceCube_eq_referenceCube]

/-- Membership in `whitneyCubes` agrees with maximal admissibility under closed-cube inclusion. -/
theorem mem_whitneyCubes_iff_maximalAdmissible (τ : ℝ) (D : TriadicCube d) :
    D ∈ whitneyCubes τ ↔ MaximalAdmissible τ D := by
  simp only [whitneyCubes, Set.mem_ofPred_eq, MaximalAdmissible,
    whitneyAdmissible_iff_admissible, closedTriadicCube_eq_closedCube]

/-- The cubes of `whitneyCubes` are the parent-detected selected cubes. -/
theorem mem_whitneyCubes_iff_selected {τ : ℝ} (hτ : 0 ≤ τ) (D : TriadicCube d) :
    D ∈ whitneyCubes τ ↔ Selected τ D :=
  (mem_whitneyCubes_iff_maximalAdmissible τ D).trans
    (selected_iff_maximalAdmissible hτ D).symm

/-- The point-to-set sup distance `pointSupDist` uses the ambient sup metric. -/
theorem pointSupDist_eq_infDist (x : Vec d) (S : Set (Vec d)) :
    pointSupDist x S = Metric.infDist x S := by
  simp only [pointSupDist, Metric.infDist_eq_iInf, sInf_image']

/-- Infimizing all pair distances agrees with infimizing point-to-set distances. -/
theorem infSupDist_eq_infDist_image {A B : Set (Vec d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    infSupDist A B = sInf ((fun x => Metric.infDist x B) '' A) := by
  have hpair : BddBelow ((fun p : Vec d × Vec d => dist p.1 p.2) '' (A ×ˢ B)) :=
    ⟨0, by rintro r ⟨p, _, rfl⟩; exact dist_nonneg⟩
  have hpoint : BddBelow ((fun x => Metric.infDist x B) '' A) :=
    ⟨0, by rintro r ⟨x, _, rfl⟩; exact Metric.infDist_nonneg⟩
  apply le_antisymm
  · apply le_csInf (hA.image _)
    rintro r ⟨x, hx, rfl⟩
    apply (Metric.le_infDist hB).mpr
    intro y hy
    exact csInf_le hpair ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · apply le_csInf ((hA.prod hB).image _)
    rintro r ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact (csInf_le hpoint ⟨x, hx, rfl⟩).trans (Metric.infDist_le_dist_of_mem hy)

/-- The `Statements/` cube distance is the cube distance used in the proved distance chain. -/
theorem infSupDist_closedCube_eq_cubeInfDist {τ : ℝ} (hτ : 0 ≤ τ) (D : TriadicCube d) :
    infSupDist (closedTriadicCube D) (closedReferenceCube τ) = cubeInfDist τ D := by
  rw [closedTriadicCube_eq_closedCube, closedReferenceCube_eq_referenceCube]
  exact infSupDist_eq_infDist_image ⟨center D, center_mem_closedCube D⟩
    (referenceCube_nonempty hτ)

/-- In dimension zero the reference cube is all of the ambient space. -/
theorem closedReferenceCube_zero_dim (τ : ℝ) :
    closedReferenceCube (d := 0) τ = Set.univ := by
  ext x
  simp [closedReferenceCube]

/-- There are no admissible Whitney cubes in dimension zero. -/
theorem not_mem_whitneyCubes_zero_dim (τ : ℝ) (D : TriadicCube 0) :
    D ∉ whitneyCubes τ := by
  intro hD
  have hdis := hD.1
  have hx : (0 : Vec 0) ∈ fivefoldClosedTriadicCube D := by
    simp [fivefoldClosedTriadicCube]
  exact Set.disjoint_left.mp hdis hx (by simp [closedReferenceCube_zero_dim])

end CoarseDeGiorgi.Foundations.Triadic
