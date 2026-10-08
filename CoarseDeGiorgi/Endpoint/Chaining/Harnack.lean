import CoarseDeGiorgi.Endpoint.Chaining.Restriction
import CoarseDeGiorgi.Endpoint.Chaining.Norms
import CoarseDeGiorgi.Endpoint.Chaining.Algebra

/-! The interior Harnack estimate, conditional on the rescaled cube estimates. -/
namespace CoarseDeGiorgi.Endpoint
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- Chaining the rescaled estimates proves the exact conclusion of `e.interior.harnack`. -/
theorem interior_harnack_of_cubes (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (hcubes : LocalHarnackCubes d p q s t hp hq hs ht) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube (3 / 4))), 0 ≤ u x) →
          IsWeightedSolution a (originCube (3 / 4)) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (5 / 8))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  obtain ⟨C, hC, hlocal⟩ := hcubes
  refine ⟨(53 : ℝ) * C, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) hC
  · intro a ha hU hL u G hu0 hu
    let : NeZero d := ⟨by omega⟩
    let A := ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal))
    let Q : (Fin d → Fin 53) → Set (Vec d) := fun m => gridCube d (chainingCenter 26 m) (1 / 2)
    let I : (Fin d → Fin 53) → ℝ≥0∞ := fun m => nonnegativeEssInf (Q m) u
    have hsub (m : Fin d → Fin 53) :
        gridCube d (chainingCenter 26 m) 1 ⊆ originCube (3 / 4) :=
      chainingCube_subset (N := 26) m (by norm_num)
    have h31 : originCube (d := d) (3 / 4) ⊆ originCube 1 :=
      originCube_mono' (by norm_num) one_pos (by norm_num)
    have hhalf (m : Fin d → Fin 53) : Q m ⊆ originCube (3 / 4) :=
      (gridCube_mono _ (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (hsub m)
    have hmeas (m : Fin d → Fin 53) : AEStronglyMeasurable u (volume.restrict (Q m)) :=
      hu.1.1.mono_set (hhalf m)
    have hloc (m : Fin d → Fin 53) : eLpNorm u ⊤ (volume.restrict (Q m)) ≤ A * I m := by
      apply hlocal a ha hU hL (chainingCenter 26 m) (chainingCenter_grid (N := 26) m)
        ((hsub m).trans h31) u G
      · exact ae_restrict_of_ae_restrict_of_subset (hsub m) hu0
      · exact weighted_solution_restrict (originCube_domain (by norm_num))
          (originCube_nonempty (by norm_num)) (LowerFractional.weightedCoeffOn_mono ha h31)
          (gridCube_domain _ one_pos) (hsub m) hu
    have hstep (m n : Fin d → Fin 53)
        (h : ∀ i, |chainingCenter 26 m i - chainingCenter 26 n i| ≤ 1 / 81) :
        I n ≤ A * I m := by
      let E := gridCube d (fun i => (chainingCenter 26 m i + chainingCenter 26 n i) / 2) (1 / 6)
      have he := overlap_cube_subset _ _ h
      have hE0 : volume E ≠ 0 := by
        dsimp only [E]
        rw [gridCube_volume _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
        positivity
      exact (inf_le_sup_of_overlap E (Q m) (Q n) u
        (fun _ hx => (he hx).1) (fun _ hx => (he hx).2) hE0 (hmeas m)).trans (hloc m)
    have hcoverW : originCube (d := d) (1 / 2) ⊆ ⋃ m, Q m :=
      chaining_halves_cover (N := 26) (by norm_num)
    obtain ⟨m, hm⟩ := exists_cover_inf_le (originCube (1 / 2)) Q u hcoverW
    have hchain (n : Fin d → Fin 53) : I n ≤ A ^ 52 * nonnegativeEssInf (originCube (1 / 2)) u :=
      (chaining_inf_le (N := 26) I A hstep m n).trans (mul_le_mul_of_nonneg_left hm zero_le)
    have hcoverV : originCube (d := d) (5 / 8) ⊆ ⋃ m, Q m :=
      chaining_halves_cover (N := 26) (by norm_num)
    have hVsub : originCube (d := d) (5 / 8) ⊆ originCube (3 / 4) :=
      originCube_mono' (by norm_num) (by norm_num) (by norm_num)
    have hbound := eLpNorm_top_cover_le (originCube (5 / 8)) Q u
      (hu.1.1.mono_set hVsub) hmeas hcoverV
      (A ^ 53 * nonnegativeEssInf (originCube (1 / 2)) u) (fun n => calc
        _ ≤ A * I n := hloc n
        _ ≤ A * (A ^ 52 * nonnegativeEssInf (originCube (1 / 2)) u) :=
          mul_le_mul_of_nonneg_left (hchain n) zero_le
        _ = _ := by rw [show A ^ 53 = A ^ 52 * A from pow_succ A 52]; ac_rfl)
    have hApow : A ^ 53 = ENNReal.ofReal
        (Real.exp ((53 * C) * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) :=
      chaining_exp_pow C _ 53
    rw [hApow] at hbound
    exact hbound
  
end CoarseDeGiorgi.Endpoint
