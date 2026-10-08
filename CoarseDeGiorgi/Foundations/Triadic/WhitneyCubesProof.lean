import CoarseDeGiorgi.Foundations.Triadic.WhitneyCubesDefs

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization MeasureTheory

/-- The Whitney-cubes statement `whitney_cubes`, proved using the triadic selection API. -/
theorem whitney_cubes_proved {d : ℕ} {τ : ℝ}
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) :
    (∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      ∀ E : TriadicCube d, E ∈ whitneyCubes (d := d) τ → D ≠ E →
      Disjoint (openCubeSet D) (openCubeSet E)) ∧
    (∀ x : Vec d, x ∉ closedReferenceCube (d := d) τ →
      ∃ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ ∧
        x ∈ closedTriadicCube (d := d) D) ∧
    (∀ K : Set (Vec d), IsCompact K → K ⊆ (closedReferenceCube τ)ᶜ →
      {D : TriadicCube d | D ∈ whitneyCubes τ ∧
        (closedTriadicCube (d := d) D ∩ K).Nonempty}.Finite) ∧
    (∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      ∀ x : Vec d, x ∈ closedTriadicCube (d := d) D →
        2 * cubeScaleFactor D <
            infSupDist (d := d) (closedTriadicCube (d := d) D)
              (closedReferenceCube (d := d) τ) ∧
          infSupDist (d := d) (closedTriadicCube (d := d) D)
              (closedReferenceCube (d := d) τ) ≤
            pointSupDist (d := d) x (closedReferenceCube (d := d) τ) ∧
          pointSupDist (d := d) x (closedReferenceCube (d := d) τ) ≤
            9 * cubeScaleFactor D) := by
  have hτbounds : 0 ≤ τ ∧ τ < 1 :=
    ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hτ0, hτ1⟩
  have hτ := hτbounds.1
  by_cases hd : d = 0
  · subst d
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro D hD
      exact False.elim (not_mem_whitneyCubes_zero_dim τ D hD)
    · intro x hx
      exact False.elim (hx (by simp [closedReferenceCube_zero_dim]))
    · intro K _ _
      have heq : {D : TriadicCube 0 | D ∈ whitneyCubes τ ∧
          (closedTriadicCube D ∩ K).Nonempty} = ∅ := by
        ext D
        simp only [Set.mem_ofPred_eq, not_mem_whitneyCubes_zero_dim, false_and,
          Set.mem_empty_iff_false]
      rw [heq]
      exact Set.finite_empty
    · intro D hD
      exact False.elim (not_mem_whitneyCubes_zero_dim τ D hD)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro D hD E hE hne
      exact Selected.openCubeSet_disjoint hτ
        ((mem_whitneyCubes_iff_selected hτ D).mp hD)
        ((mem_whitneyCubes_iff_selected hτ E).mp hE) hne
    · intro x hx
      rw [closedReferenceCube_eq_referenceCube] at hx
      obtain ⟨D, hD, hxD⟩ := exists_selected_closedCube hτ hx
      exact ⟨D, (mem_whitneyCubes_iff_selected hτ D).mpr hD,
        by simpa only [closedTriadicCube_eq_closedCube] using hxD⟩
    · intro K hK hsub
      have hdis : Disjoint K (referenceCube τ) := by
        apply Set.disjoint_left.mpr
        intro x hxK hxR
        exact hsub hxK (by simpa only [closedReferenceCube_eq_referenceCube] using hxR)
      simpa only [mem_whitneyCubes_iff_selected hτ, closedTriadicCube_eq_closedCube] using
        finite_selected_meeting_compact hτ hK hdis
    · intro D hD x hx
      have hsel := (mem_whitneyCubes_iff_selected hτ D).mp hD
      rw [closedTriadicCube_eq_closedCube] at hx
      simp only [infSupDist_closedCube_eq_cubeInfDist hτ]
      simpa only [pointSupDist_eq_infDist, closedReferenceCube_eq_referenceCube] using
        hsel.distance_chain hτ hx

end CoarseDeGiorgi.Foundations.Triadic
