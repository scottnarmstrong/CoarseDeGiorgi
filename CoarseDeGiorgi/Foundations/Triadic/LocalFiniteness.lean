module

public import CoarseDeGiorgi.Foundations.Triadic.Selection
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

theorem isClosed_referenceCube (τ : ℝ) : IsClosed (referenceCube (d := d) τ) := by
  have heq : referenceCube (d := d) τ =
      ⋂ i : Fin d, {x : Vec d | |x i| ≤ τ / 2} := by
    ext x
    simp only [referenceCube, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const

/-- A bounded size range and a bounded meeting point bound both scale and index. -/
theorem finite_cubes_of_size_and_point_bounds {a b R : ℝ} (ha : 0 < a) :
    {D : TriadicCube d | a ≤ cubeScaleFactor D ∧ cubeScaleFactor D ≤ b ∧
      ∃ x : Vec d, x ∈ closedCube D ∧ ‖x‖ ≤ R}.Finite := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha (by norm_num : (1 / 3 : ℝ) < 1)
  have hl : (3 : ℝ) ^ (-(n : ℤ)) < a := by
    simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using hn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt b (by norm_num : (1 : ℝ) < 3)
  have hu : b < (3 : ℝ) ^ (m : ℤ) := by simpa only [zpow_natCast] using hm
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + b / 2) / a)
  let S : Set (TriadicCube d) := {D | a ≤ cubeScaleFactor D ∧ cubeScaleFactor D ≤ b ∧
    ∃ x : Vec d, x ∈ closedCube D ∧ ‖x‖ ≤ R}
  let f : TriadicCube d → ℤ × (Fin d → ℤ) := fun D => (D.scale, D.index)
  have hfinite :
      (Set.Icc (-(n : ℤ)) (m : ℤ) ×ˢ
        {z : Fin d → ℤ | ∀ i, z i ∈ Set.Icc (-(N : ℤ)) (N : ℤ)}).Finite :=
    (Set.finite_Icc _ _).prod (Set.Finite.pi' fun _ => Set.finite_Icc _ _)
  have himage : (f '' S).Finite := hfinite.subset (by
    rintro _ ⟨D, ⟨haD, hbD, x, hxD, hxR⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp
        (hl.le.trans haD)
    · exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp
        (hbD.trans hu.le)
    · intro i
      have hi : |(D.index i : ℝ)| * cubeScaleFactor D ≤ R + cubeScaleFactor D / 2 := by
        have htri := abs_sub_le (center D i) (x i) 0
        rw [sub_zero, sub_zero, abs_sub_comm (center D i)] at htri
        have hnorm : |x i| ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
        have hc : |center D i| = |(D.index i : ℝ)| * cubeScaleFactor D := by
          rw [center, abs_mul, abs_of_pos (scaleFactor_pos D)]
        rw [hc] at htri
        linarith only [htri, hxD i, hnorm, hxR]
      have hmul := mul_le_mul_of_nonneg_left haD (abs_nonneg (D.index i : ℝ))
      have hbnd : |(D.index i : ℝ)| ≤ (R + b / 2) / a := by
        apply (le_div_iff₀ ha).mpr
        linarith only [hi, hmul, hbD]
      obtain ⟨hlN, huN⟩ := abs_le.mp (hbnd.trans hN.le)
      change -(N : ℤ) ≤ D.index i ∧ D.index i ≤ (N : ℤ)
      constructor
      · exact_mod_cast hlN
      · exact_mod_cast huN)
  exact himage.of_finite_image (by
    intro D _ E _ heq
    have hs : D.scale = E.scale := congrArg Prod.fst heq
    have hi : D.index = E.index := congrArg Prod.snd heq
    cases D
    cases E
    exact congrArg₂ TriadicCube.mk hs hi)

/-- Only finitely many selected closed cubes meet a compact exterior set. -/
theorem finite_selected_meeting_compact {τ : ℝ} (hτ : 0 ≤ τ) {K : Set (Vec d)}
    (hK : IsCompact K) (hdis : Disjoint K (referenceCube τ)) :
    {D : TriadicCube d | Selected τ D ∧ (closedCube D ∩ K).Nonempty}.Finite := by
  obtain ⟨δ, hδ, hgap⟩ := hK.exists_forall_le'
    (Metric.continuous_infDist_pt (referenceCube τ)).continuousOn (a := 0) (by
      intro x hx
      exact ((isClosed_referenceCube τ).notMem_iff_infDist_pos
        (referenceCube_nonempty hτ)).mp (fun hy => Set.disjoint_left.mp hdis hx hy))
  obtain ⟨R, hR⟩ := hK.bddAbove_image continuous_norm.continuousOn
  have ha : 0 < δ / 9 := by linarith only [hδ]
  apply (finite_cubes_of_size_and_point_bounds (d := d) (b := R + 1) (R := R) ha).subset
  rintro D ⟨hD, x, hxD, hxK⟩
  have hn : ‖x‖ ≤ R := hR ⟨x, hxK, rfl⟩
  have hc := hD.distance_chain hτ hxD
  refine ⟨?_, ?_, x, hxD, hn⟩
  · linarith only [hgap x hxK, hc.2.2]
  · by_contra h
    have hsize : ‖x‖ + 1 < cubeScaleFactor D := by
      linarith only [hn, not_le.mp h]
    exact large_cube_not_admissible hτ D hxD hsize hD.1

end

end CoarseDeGiorgi.Foundations.Triadic
