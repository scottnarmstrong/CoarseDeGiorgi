import CoarseDeGiorgi.SharpnessExamples.ScalarCoefficient
import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesGeometry
import CoarseDeGiorgi.Foundations.FracGeometry.FlatCoordinates

open Homogenization MeasureTheory
open CoarseDeGiorgi.Sharpness
open CoarseDeGiorgi.Foundations.FracGeometry

namespace CoarseDeGiorgi.SharpnessExamples

/-- The transverse center in the coordinates used by the average lemmas. -/
noncomputable def scalarTailCenter (m k : ℕ) : Vec m :=
  fun i => if i.val = 0 then cylinderB k else 0

theorem cylinderB_le_eighth (k : ℕ) : cylinderB k ≤ 1 / 8 := by
  have hmono := cylinderB_le_of_le (i := 0) (j := k) (Nat.zero_le k)
  norm_num [cylinderB] at hmono ⊢
  exact hmono

theorem scalarTailCenter_coord_bound {m k : ℕ} (i : Fin m) :
    |scalarTailCenter m k i| ≤ 1 / 4 := by
  by_cases hi : i.val = 0
  · simpa [scalarTailCenter, hi, abs_of_nonneg (cylinderB_pos k).le] using
      (cylinderB_le_eighth k).trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
  · simp [scalarTailCenter, hi]

theorem scalarCylinderCenter_eq_flatJoin {m k : ℕ} :
    cylinderCenter (d := m + 1) (cylinderB k) =
      flatJoin 0 (scalarTailCenter m k) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [cylinderCenter, flatJoin]
  · by_cases hj : j.val = 0
    · simp [cylinderCenter, scalarTailCenter, flatJoin, hj]
    · simp [cylinderCenter, scalarTailCenter, flatJoin, hj]

theorem scalarShiftedTransverseNorm_eq {m k : ℕ} (x : Vec (m + 1)) :
    transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB k)) =
      transverseNorm (flatJoin 0 (scalarTailCenter m k) - x) := by
  have hv : x - cylinderCenter (d := m + 1) (cylinderB k) =
      -(flatJoin 0 (scalarTailCenter m k) - x) := by
    rw [scalarCylinderCenter_eq_flatJoin]
    abel
  rw [hv]
  rw [Sharpness.transverseNorm, Sharpness.transverseNorm]
  have hpart : Sharpness.transversePart
      (-(flatJoin 0 (scalarTailCenter m k) - x)) =
      -Sharpness.transversePart (flatJoin 0 (scalarTailCenter m k) - x) := by
    ext i
    by_cases hi : i.val = 0
    · simp [Sharpness.transversePart, hi]
    · simp [Sharpness.transversePart, hi]
  rw [hpart]
  simp

theorem scalarCoreBand_inter_cube_eq_averageCylinder {m k : ℕ}
    (ζ κ : ℝ) :
    scalarCoreBand (d := m + 1) k ζ κ ∩ originCube 1 =
      averagesCylinder (cylinderRadius (m + 1) k ζ κ) (scalarTailCenter m k) := by
  ext x
  constructor
  · rintro ⟨hband, hcube⟩
    refine ⟨hcube, ?_⟩
    change transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB k)) < _ at hband
    rw [scalarShiftedTransverseNorm_eq] at hband
    exact hband
  · rintro ⟨hcube, hband⟩
    refine ⟨?_, hcube⟩
    change transverseNorm (flatJoin 0 (scalarTailCenter m k) - x) < _ at hband
    change transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB k)) < _
    rw [scalarShiftedTransverseNorm_eq]
    exact hband

theorem scalarTubeBand_inter_cube_eq_averageCylinder {m k : ℕ}
    (ζ κ : ℝ) :
    {x : Vec (m + 1) | transverseNorm
        (x - cylinderCenter (d := m + 1) (cylinderB k)) <
          2 * cylinderRadius (m + 1) k ζ κ} ∩ originCube 1 =
      averagesCylinder (2 * cylinderRadius (m + 1) k ζ κ)
        (scalarTailCenter m k) := by
  ext x
  constructor
  · rintro ⟨hband, hx⟩
    refine ⟨hx, ?_⟩
    change transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB k)) < _ at hband
    rw [scalarShiftedTransverseNorm_eq] at hband
    exact hband
  · rintro ⟨hx, hband⟩
    refine ⟨?_, hx⟩
    change transverseNorm (flatJoin 0 (scalarTailCenter m k) - x) < _ at hband
    change transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB k)) < _
    rw [scalarShiftedTransverseNorm_eq]
    exact hband

theorem scalarRadius_small {m k : ℕ} {ζ κ : ℝ}
    (hd : 3 ≤ m + 1) (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    0 < cylinderRadius (m + 1) k ζ κ ∧
      2 * cylinderRadius (m + 1) k ζ κ < 1 / 4 := by
  have hdata := cylinderRadius_data (d := m + 1) (n := k) hd hζ0 hζ2 hκ
  have hb : cylinderB k ≤ 1 / 8 := cylinderB_le_eighth k
  have hden : 16 ≤ 16 * (1 + Real.sqrt κ) := by
    have hs := Real.sqrt_nonneg κ
    nlinarith
  have hscale : cylinderB k / (16 * (1 + Real.sqrt κ)) ≤ 1 / 128 := by
    rw [div_le_iff₀ (by positivity : 0 < 16 * (1 + Real.sqrt κ))]
    nlinarith [cylinderB_le_eighth k, Real.sqrt_nonneg κ]
  refine ⟨hdata.1, ?_⟩
  have hε : cylinderRadius (m + 1) k ζ κ < 1 / 128 := hdata.2.1.trans_le hscale
  linarith

theorem scalarCoreBand_volume_bound {m k : ℕ} (hm : 2 ≤ m)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    (volume (scalarCoreBand (d := m + 1) k ζ κ ∩ originCube 1)).toReal ≤
      (2 * cylinderRadius (m + 1) k ζ κ) ^ m := by
  have hrad := cylinderRadius_data (d := m + 1) (n := k) (by omega) hζ0 hζ2 hκ
  have hsmall := scalarRadius_small (m := m) (k := k) (by omega) hζ0 hζ2 hκ
  have hvol := averagesCylinder_volume_bounds
    (cylinderRadius (m + 1) k ζ κ) (scalarTailCenter m k)
    hrad.1 (by linarith [hsmall.2]) (scalarTailCenter_coord_bound)
  rw [scalarCoreBand_inter_cube_eq_averageCylinder]
  exact hvol.2

theorem scalarTubeBand_volume_bound {m k : ℕ} (hm : 2 ≤ m)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    (volume ({x : Vec (m + 1) | transverseNorm
        (x - cylinderCenter (d := m + 1) (cylinderB k)) <
          2 * cylinderRadius (m + 1) k ζ κ} ∩ originCube 1)).toReal ≤
      (4 * cylinderRadius (m + 1) k ζ κ) ^ m := by
  have hrad := cylinderRadius_data (d := m + 1) (n := k) (by omega) hζ0 hζ2 hκ
  have hsmall := scalarRadius_small (m := m) (k := k) (by omega) hζ0 hζ2 hκ
  have hvol := averagesCylinder_volume_bounds
    (2 * cylinderRadius (m + 1) k ζ κ) (scalarTailCenter m k)
    (mul_pos (by norm_num) hrad.1) (by linarith [hsmall.2]) scalarTailCenter_coord_bound
  rw [scalarTubeBand_inter_cube_eq_averageCylinder]
  simpa only [show 2 * (2 * cylinderRadius (m + 1) k ζ κ) =
    4 * cylinderRadius (m + 1) k ζ κ by ring] using hvol.2

theorem scalarAnnulusBand_volume_bound {m k : ℕ} (hm : 2 ≤ m)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    (volume (scalarAnnulusBand (d := m + 1) k ζ κ ∩ originCube 1)).toReal ≤
      (4 * cylinderRadius (m + 1) k ζ κ) ^ m := by
  have hsubset : scalarAnnulusBand (d := m + 1) k ζ κ ∩ originCube 1 ⊆
      {x : Vec (m + 1) | transverseNorm
        (x - cylinderCenter (d := m + 1) (cylinderB k)) <
          2 * cylinderRadius (m + 1) k ζ κ} ∩ originCube 1 := by
    rintro x ⟨hx, hcube⟩
    exact ⟨hx.2, hcube⟩
  have hcubeTop : volume (originCube (d := m + 1) 1) ≠ ⊤ := by
    rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one (m + 1)]
    simp
  have htop : volume ({x : Vec (m + 1) | transverseNorm
        (x - cylinderCenter (d := m + 1) (cylinderB k)) <
        2 * cylinderRadius (m + 1) k ζ κ} ∩ originCube 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hcubeTop
    exact measure_mono Set.inter_subset_right
  have hmeas : volume (scalarAnnulusBand (d := m + 1) k ζ κ ∩ originCube 1) ≤
      volume ({x : Vec (m + 1) | transverseNorm
        (x - cylinderCenter (d := m + 1) (cylinderB k)) <
          2 * cylinderRadius (m + 1) k ζ κ} ∩ originCube 1) :=
    measure_mono hsubset
  apply (ENNReal.toReal_mono htop hmeas).trans
  exact scalarTubeBand_volume_bound hm hζ0 hζ2 hκ

end CoarseDeGiorgi.SharpnessExamples
