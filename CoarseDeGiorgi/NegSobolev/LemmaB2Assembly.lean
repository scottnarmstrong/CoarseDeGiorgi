module

public import CoarseDeGiorgi.NegSobolev.LemmaB2Heat
public import CoarseDeGiorgi.NegSobolev.LemmaB2Series
public import CoarseDeGiorgi.Statements.IsOpenOriginCube
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.SimplexCell

/-! `l.negative.sobolev` assembled from `p.besov.averages` and the Gaussian Sobolev test estimate.
The first input is the heat-average comparison `p.besov.averages`.
The second states the Gaussian test estimate uniformly in time and the test function.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- `l.negative.sobolev` conditional on the heat-average comparison and Gaussian Sobolev test estimate. -/
theorem negative_sobolev_bound_of_inputs
    (haverages : ∀ (d : ℕ),
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p →
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        (∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))) →
        let heat : ℕ → ℝ≥0∞ := fun k =>
          eLpNorm
            (fun x => ‖Matrix.of fun i j =>
              ∫ y, gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) *
                (originCube 1).indicator b y i j ∂volume‖)
            (ENNReal.ofReal p) volume
        let simplexMean : ℕ → ℝ := fun k =>
          ((triangulation (d := d) k).attach.sum fun η =>
              Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) /
            ((triangulation (d := d) k).card : ℝ)
        let cubeMean : ℕ → ℝ := fun k =>
          (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (simplexMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (simplexMean k)).rpow (1 / p)) ∧
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (cubeMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (cubeMean k)).rpow (1 / p)) ∧
        ∀ s : ℝ, 0 < s →
          let heatSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)
          let simplexSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (simplexMean k)).rpow (1 / (2 * p))
          let cubeSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (cubeMean k)).rpow (1 / (2 * p))
          (simplexSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * simplexSum) ∧
          (cubeSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * cubeSum)
    )
    (htest : ∀ (d : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (hr : 1 < r),
      ∃ H : ℝ, 0 < H ∧ ∀ (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
          MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ⊤
            (volume.restrict (originCube 1)) ∧
          sobolevNorm (originCube 1) (isOpen_originCube 1) β r hβ hr.le
            (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ≤
              ENNReal.ofReal H * ENNReal.ofReal (Real.rpow t (-β / 2)) *
                eLpNorm g (ENNReal.ofReal r) volume)
    (d : ℕ) (p s ε : ℝ)
    (hp : 1 < p) (hs : 0 < s) (_hε : 0 < ε) (hεs : ε ≤ 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        ∀ (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))),
          besovCubeNorm b hb s p hs hp.le ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) b hb (2 * s - ε) p (sub_nonneg.mpr hεs) hp := by
  obtain ⟨B, hB, hav⟩ := haverages d
  have hr : 1 < p / (p - 1) := by
    apply (lt_div_iff₀ (sub_pos.mpr hp)).mpr
    linarith
  obtain ⟨H, hH, htestH⟩ := htest d (2 * s - ε) (p / (p - 1)) (sub_nonneg.mpr hεs) hr
  let G : ℝ := (1 - Real.rpow 3 (-ε / 2))⁻¹
  have hG : 0 ≤ G := inv_nonneg.mpr (sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith : -ε / 2 < 0)).le)
  let C : ℝ := B * G ^ 2 * ((d : ℝ) * H)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hB.le (sq_nonneg G))
    (mul_nonneg (Nat.cast_nonneg d) hH.le)
  refine ⟨C, hC, ?_⟩
  intro b hpos hb
  let heat : ℕ → ℝ≥0∞ := fun k => eLpNorm
    (fun x => ‖Matrix.of fun i j =>
      ∫ y, gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) *
        (originCube 1).indicator b y i j ∂volume‖) (ENNReal.ofReal p) volume
  let cubeSum : ℝ≥0∞ := ∑' k : ℕ,
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
      (ENNReal.ofReal
        ((∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
          ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ))).rpow (1 / (2 * p))
  have hcomp := ((hav p hp.le b hpos hb).2.2 s hs).2.1
  change cubeSum ≤ ENNReal.ofReal (Real.sqrt B) *
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)) at hcomp
  have hcomp' : cubeSum ≤ (ENNReal.ofReal B).rpow (1 / 2) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)) := by
    simpa only [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hB, Real.sqrt_eq_rpow] using hcomp
  have hbext : ∀ i j, Integrable (fun y => (originCube 1).indicator b y i j) volume := by
    intro i j
    have hi := (integrable_indicator_iff (isOpen_originCube (d := d) 1).measurableSet).mpr (hb i j)
    convert hi using 1
    ext y
    by_cases hy : y ∈ originCube 1
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, Matrix.zero_apply]
  have hposext := indicator_matrix_posSemidef (isOpen_originCube (d := d) 1).measurableSet b hpos
  have htrace : (fun y => ((originCube 1).indicator b y).trace) =
      (originCube 1).indicator (fun y => (b y).trace) := by
    ext y
    by_cases hy : y ∈ originCube 1
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, Matrix.trace_zero]
  have hh : ∀ k : ℕ, heat k ≤ ENNReal.ofReal ((d : ℝ) * H) *
      ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) *
        negSobolevNorm (originCube 1) (isOpen_originCube 1) b hb (2 * s - ε) p
          (sub_nonneg.mpr hεs) hp := by
    intro k
    let t : ℝ := (3 : ℝ) ^ (-(2 * (k : ℤ)))
    have ht : 0 < t := zpow_pos (by norm_num) _
    have ht1 : t ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    let M : ℝ := H * Real.rpow t (-(2 * s - ε) / 2)
    have hM : 0 < M := mul_pos hH (Real.rpow_pos_of_pos ht _)
    have htestM : ∀ g : Vec d → ℝ, MemLp g (ENNReal.ofReal (p / (p - 1))) volume →
        MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ⊤
          (volume.restrict (originCube 1)) ∧
        sobolevNorm (originCube 1) (isOpen_originCube 1) (2 * s - ε) (p / (p - 1))
          (sub_nonneg.mpr hεs) ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith))
          (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ≤
          ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume := by
      intro g hg
      obtain ⟨hbound, hnorm⟩ := htestH g hg t ht ht1
      refine ⟨hbound, ?_⟩
      simpa only [M, ENNReal.ofReal_mul hH.le] using hnorm
    have hscalar := lemmaB2_trace_heat_bound (isOpen_originCube 1) t ht (2 * s - ε) p
      (sub_nonneg.mpr hεs) hp b hb hpos M hM htestM
    have hmatrix := lemmaB2_matrix_heat_le_trace t ht ((originCube 1).indicator b) hbext hposext p hp
    have htrace_apply (y : Vec d) := congrFun htrace y
    simp_rw [htrace_apply] at hmatrix
    change heat k ≤ _ at hmatrix
    refine (hmatrix.trans hscalar).trans_eq ?_
    rw [show ENNReal.ofReal M = ENNReal.ofReal H *
      ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) by
        dsimp only [M, t]
        rw [ENNReal.ofReal_mul hH.le, lemmaB2_triadic_scale],
      ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    ac_rfl
  have hfinal := lemmaB2_series_square_le s ε _hε heat cubeSum (ENNReal.ofReal B)
    (ENNReal.ofReal ((d : ℝ) * H))
    (negSobolevNorm (originCube 1) (isOpen_originCube 1) b hb (2 * s - ε) p
      (sub_nonneg.mpr hεs) hp) hcomp' hh
  rw [lemmaB2_besovCubeNorm_eq]
  change cubeSum ^ 2 ≤ _
  refine hfinal.trans_eq ?_
  congr 1
  dsimp only [C, G]
  rw [ENNReal.ofReal_mul (mul_nonneg hB.le (sq_nonneg _)),
    ENNReal.ofReal_mul hB.le]
  rw [ENNReal.ofReal_pow hG 2]

end CoarseDeGiorgi.NegSobolev
