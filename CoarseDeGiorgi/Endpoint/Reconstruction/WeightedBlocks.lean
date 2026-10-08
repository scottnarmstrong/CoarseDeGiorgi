module

public import CoarseDeGiorgi.Endpoint.Reconstruction.BlockEstimates

/-! # Same-index weighted estimates for the Dirichlet blocks -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem eLpNorm_field_le_euclidNorm {d : ℕ} {μ : Measure (Vec d)}
    {F : Vec d → Vec d} {p : ℝ≥0∞} (hF : AEStronglyMeasurable F μ) :
    eLpNorm F p μ ≤ eLpNorm (fun x => euclidNorm (F x)) p μ := by
  apply eLpNorm_mono_ae hF
  filter_upwards [] with x
  change ‖F x‖ ≤ ‖Foundations.Euclid.eNorm2 (F x)‖
  rw [Real.norm_of_nonneg (Foundations.Euclid.eNorm2_nonneg _)]
  exact Foundations.Euclid.norm_le_eNorm2 (F x)

/-- One dimension/exponent constant controls every weighted zero-trace pair.
No coefficient moment is shifted from block index `k` to `k-1`. -/
theorem exists_weighted_dirichlet_blocks {d : ℕ} (hd : 3 ≤ d)
    {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : CoeffField d)
      (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
      (v : Vec d → ℝ) (G : Vec d → Vec d),
      MemH1a0 a (CoarseDeGiorgi.originCube 1) v G →
      ∃ w : ℕ → H10Function (openCubeSet (Homogenization.originCube d 0)),
        w 0 = 0 ∧ ∀ k : ℕ, 1 ≤ k →
          IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d))
            (openCubeSet (Homogenization.originCube d 0)) (w k) (fineIncrement (k - 1) G) ∧
          eLpNorm (w k).toH1Function.toFun (ENNReal.ofReal (paramR q))
              (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
            ENNReal.ofReal C * ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ))) *
              (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q)) *
              (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ) ∧
          eLpNorm (w k).toH1Function.toFun ⊤
              (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
            ENNReal.ofReal C *
              ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) * ((d : ℝ) / paramR q - 1))) *
              (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q)) *
              (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ) := by
  have hr1 := LowerFractional.lower_paramR_gt_one hq
  have hr2 : paramR q < 2 := by
    unfold paramR
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hrs : (paramR q).HolderConjugate (paramR q / (paramR q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hr1).mpr rfl
  obtain ⟨CL, CS, hCL, hCS, hblocks⟩ := exists_fineIncrement_dirichlet_estimates hd hrs hr2
  let C := 2 * max CL CS
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a ha v G hv
  let : NeZero d := ⟨by omega⟩
  have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) := by
    rw [originCube_one_eq_openCubeSet]
    exact isOpenBoundedConvexDomain_openCubeSet _
  have hne := LowerFractional.lower_unitCube_nonempty (d := d)
  have hW := Weighted.memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hv)
  have hG : IntegrableOn G (CoarseDeGiorgi.originCube 1) := Integrable.of_eval hW.2.1
  choose W hWweak hWL hWS using fun n => hblocks n G hG
  let w : ℕ → H10Function (openCubeSet (Homogenization.originCube d 0)) :=
    fun k => match k with | 0 => 0 | n + 1 => W n
  refine ⟨w, rfl, ?_⟩
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hμ : normalizedCubeMeasure (Homogenization.originCube d 0) =
      volume.restrict (CoarseDeGiorgi.originCube (d := d) 1) := by
    rw [normalizedCubeMeasure_unit_eq, originCube_one_eq_openCubeSet]
  have hnorm : eLpNorm (fineIncrement n G) (ENNReal.ofReal (paramR q))
      (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
      2 * (ENNReal.ofReal (lowerCellAverage a ha (n + 1) q)) ^ (1 / (2 * q)) *
        (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ) := by
    rw [hμ]
    apply (eLpNorm_field_le_euclidNorm
      (memLp_fineIncrement n G (ENNReal.ofReal (paramR q))).aestronglyMeasurable.restrict).trans
    convert fine_increment_weighted_norm_le n a ha hv hq using 1
    simp only [mul_assoc, ENNReal.rpow_eq_pow]
  have hCL2 : ENNReal.ofReal CL * 2 ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hCL]
    exact ENNReal.ofReal_le_ofReal (by dsimp [C]; nlinarith [le_max_left CL CS])
  have hCS2 : ENNReal.ofReal CS * 2 ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hCS]
    exact ENNReal.ofReal_le_ofReal (by dsimp [C]; nlinarith [le_max_right CL CS])
  refine ⟨by simpa only [Nat.succ_sub_one, w] using hWweak n, ?_, ?_⟩
  · have h : eLpNorm (W n).toH1Function.toFun (ENNReal.ofReal (paramR q))
        (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
        ENNReal.ofReal CL * ENNReal.ofReal ((3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) *
          (2 * (ENNReal.ofReal (lowerCellAverage a ha (n + 1) q)) ^ (1 / (2 * q)) *
            (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ)) :=
      (hWL n).trans (by gcongr)
    rw [hμ] at h
    refine h.trans ?_
    calc
      _ = (ENNReal.ofReal CL * 2) * ENNReal.ofReal ((3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) *
          (ENNReal.ofReal (lowerCellAverage a ha (n + 1) q)) ^ (1 / (2 * q)) *
          (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := by gcongr
  · have h : eLpNorm (W n).toH1Function.toFun ⊤
        (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
        ENNReal.ofReal CS *
          ENNReal.ofReal ((3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * ((d : ℝ) / paramR q - 1))) *
          (2 * (ENNReal.ofReal (lowerCellAverage a ha (n + 1) q)) ^ (1 / (2 * q)) *
            (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ)) :=
      (hWS n).trans (by gcongr)
    rw [hμ] at h
    refine h.trans ?_
    calc
      _ = (ENNReal.ofReal CS * 2) *
          ENNReal.ofReal ((3 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * ((d : ℝ) / paramR q - 1))) *
          (ENNReal.ofReal (lowerCellAverage a ha (n + 1) q)) ^ (1 / (2 * q)) *
          (weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := by gcongr

end

end CoarseDeGiorgi.Endpoint.Reconstruction
