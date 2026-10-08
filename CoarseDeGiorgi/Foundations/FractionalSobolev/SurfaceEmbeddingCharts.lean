import CoarseDeGiorgi.Foundations.FractionalSobolev.UnitCube
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceVolume
import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import CoarseDeGiorgi.Statements.FracNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

/-- Tangential coordinates on a coordinate face, normalized to the unit cube. -/
def embeddingFaceChart {n : ℕ} (τ : ℝ) (i : Fin (n + 1)) (pos : Bool)
    (y : Vec n) : Vec (n + 1) :=
  i.insertNth (if pos then τ / 2 else -τ / 2) (τ • y)

def embeddingSideCube (n : ℕ) (τ : ℝ) : Set (Vec n) :=
  Set.pi Set.univ (fun _ => Ioo (-τ / 2) (τ / 2))

lemma embeddingFaceChart_measurable {n : ℕ} (τ : ℝ) (i : Fin (n + 1)) (pos : Bool) :
    Measurable (embeddingFaceChart τ i pos) :=
  (FracGeometry.isometry_insertNth i _).continuous.measurable.comp (measurable_const_smul τ)

lemma embeddingFace_map {n : ℕ} (τ : ℝ) (i : Fin (n + 1)) (pos : Bool) :
    Measure.map (fun y : Vec n => i.insertNth (if pos then τ / 2 else -τ / 2) y)
      (volume.restrict (embeddingSideCube n τ)) = cubeFaceMeasure τ i pos := by
  classical
  let c := if pos then τ / 2 else -τ / 2
  let S : Fin (n + 1) → Set ℝ := fun j => if j = i then univ else Ioo (-τ/2) (τ/2)
  have he : cubeFaceMeasure τ i pos =
      (Measure.pi (FracGeometry.fullFaceCoordinates i c)).restrict (Set.pi univ S) := by
    rw [cubeFaceMeasure, Measure.restrict_pi_pi]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [faceCoordinateMeasures, FracGeometry.fullFaceCoordinates, c, hji]
  have hpre : (fun y : Vec n => i.insertNth c y) ⁻¹' Set.pi univ S = embeddingSideCube n τ := by
    ext y
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, embeddingSideCube]
    rw [Fin.forall_iff_succAbove i]
    simp [S]
  rw [he, FracGeometry.pi_fullFaceCoordinates,
    Measure.restrict_map (FracGeometry.isometry_insertNth i c).continuous.measurable
      (MeasurableSet.pi (Set.to_countable _) (fun j _ => by dsimp [S]; split_ifs <;> measurability)), hpre]

lemma embeddingSideCube_preimage {n : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (fun y : Vec n => τ • y) ⁻¹' embeddingSideCube n τ = dnpvUnitCube n := by
  ext y
  simp only [mem_preimage, embeddingSideCube, mem_pi, mem_univ, true_implies,
    Pi.smul_apply, smul_eq_mul, dnpvUnitCube, mem_ofPred_eq]
  apply forall_congr'
  intro j
  change ( -τ / 2 < τ * y j ∧ τ * y j < τ / 2) ↔ _
  constructor
  · intro h; constructor <;> nlinarith only [h.1, h.2, hτ]
  · intro h; constructor <;> nlinarith only [h.1, h.2, hτ]

/-- Exact pushforward identity, including the tangential dilation density. -/
lemma embeddingFaceChart_map {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (i : Fin (n + 1)) (pos : Bool) :
    Measure.map (embeddingFaceChart τ i pos) (volume.restrict (dnpvUnitCube n)) =
      ENNReal.ofReal ((τ ^ n)⁻¹) • cubeFaceMeasure τ i pos := by
  have hs : Measure.map (fun y : Vec n => τ • y) (volume.restrict (dnpvUnitCube n)) =
      ENNReal.ofReal ((τ ^ n)⁻¹) • volume.restrict (embeddingSideCube n τ) := by
    rw [← embeddingSideCube_preimage hτ,
      ← Measure.restrict_map (measurable_const_smul τ)
        (show MeasurableSet (embeddingSideCube n τ) from
          MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioo)), Measure.map_addHaar_smul volume hτ.ne']
    simp only [Module.finrank_pi, Fintype.card_fin, abs_of_pos (inv_pos.mpr (pow_pos hτ n)), Measure.restrict_smul]
  change Measure.map ((fun y : Vec n => i.insertNth (α := fun _ => ℝ) (if pos then τ / 2 else -τ / 2) y) ∘
    (fun y : Vec n => τ • y)) _ = _
  rw [← Measure.map_map (FracGeometry.isometry_insertNth i _).continuous.measurable
      (measurable_const_smul τ), hs,
    Measure.map_smul _ (FracGeometry.isometry_insertNth i _).continuous.measurable.aemeasurable, embeddingFace_map]

lemma embeddingFaceChart_measure_bounds {n : ℕ} {τ : ℝ}
    (hτ : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ ≤ 1) (i : Fin (n + 1)) (pos : Bool) :
    cubeFaceMeasure τ i pos ≤ Measure.map (embeddingFaceChart τ i pos) (volume.restrict (dnpvUnitCube n)) ∧
    Measure.map (embeddingFaceChart τ i pos) (volume.restrict (dnpvUnitCube n)) ≤
      (2 ^ n : ℝ≥0∞) • cubeFaceMeasure τ i pos := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  rw [embeddingFaceChart_map hτ0]
  have hlow : (1 : ℝ) ≤ (τ ^ n)⁻¹ := (one_le_inv₀ (pow_pos hτ0 n)).mpr (pow_le_one₀ hτ0.le hτ1)
  have hupp : (τ ^ n)⁻¹ ≤ (2 : ℝ) ^ n := by
    rw [← inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hτ0.le)
    exact (inv_le_comm₀ hτ0 (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num; exact hτ)
  constructor
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul]
    have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((τ ^ n)⁻¹) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlow
    simpa only [one_mul] using mul_le_mul' hc le_rfl
  · have hc : ENNReal.ofReal ((τ ^ n)⁻¹) ≤ (2 ^ n : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal hupp
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hc le_rfl

lemma embeddingFaceChart_distance {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (i : Fin (n + 1)) (pos : Bool) (x y : Vec n) :
    euclidDist (embeddingFaceChart τ i pos x) (embeddingFaceChart τ i pos y) = τ * euclidDist x y := by
  unfold euclidDist vecNormSq vecDot
  have he : (∑ j : Fin (n + 1),
      (embeddingFaceChart τ i pos x - embeddingFaceChart τ i pos y) j *
        (embeddingFaceChart τ i pos x - embeddingFaceChart τ i pos y) j) =
      τ ^ 2 * ∑ j : Fin n, (x - y) j * (x - y) j := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [embeddingFaceChart, Pi.sub_apply, Fin.insertNth_apply_same, sub_self,
      mul_zero, Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
