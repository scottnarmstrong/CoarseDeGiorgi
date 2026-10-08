import CoarseDeGiorgi.NegSobolev.GaussianBasic
import CoarseDeGiorgi.Statements.CubeCell
import CoarseDeGiorgi.Statements.SimplexCell

/-! # Gaussian estimates on the two triadic cell families -/

open Homogenization MeasureTheory
open scoped BigOperators

namespace CoarseDeGiorgi.NegSobolev

/-- Coordinate diameter bounds imply the Euclidean squared diameter bound. -/
theorem vecNormSq_sub_le_of_coordinate_diameter {d : ℕ} (x y : Vec d)
    (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hxy : ∀ i, |x i - y i| ≤ ℓ) :
    vecNormSq (x - y) ≤ (d : ℝ) * ℓ ^ 2 := by
  unfold vecNormSq vecDot
  calc
    ∑ i, (x - y) i * (x - y) i ≤ ∑ _ : Fin d, ℓ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Pi.sub_apply, ← pow_two]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hℓ).mpr (hxy i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

/-- The heat time in `p.besov.averages` is the square of the cell side length. -/
theorem triadic_time_eq_side_sq (k : ℕ) :
    (3 : ℝ) ^ (-(2 * (k : ℤ))) = ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- The squared Euclidean diameter of every triadic cube is at most `d 3⁻²ᵏ`. -/
theorem cubeCell_sq_diameter {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    {x y : Vec d} (hx : x ∈ cubeCell k j) (hy : y ∈ cubeCell k j) :
    vecNormSq (x - y) ≤ (d : ℝ) * (3 : ℝ) ^ (-(2 * (k : ℤ))) := by
  rw [triadic_time_eq_side_sq]
  apply vecNormSq_sub_le_of_coordinate_diameter _ _ _ (le_of_lt (zpow_pos (by norm_num) _))
  intro i
  have hxi := hx i
  have hyi := hy i
  simp only [Pi.sub_apply] at hxi hyi
  apply abs_le.mpr
  constructor <;> linarith only [hxi.1, hxi.2, hyi.1, hyi.2]

/-- Every simplex has the same diameter bound, obtained from its defining box. -/
theorem simplexCell_sq_diameter {d : ℕ} (k : ℕ) (η : SimplexIndex d k)
    {x y : Vec d} (hx : x ∈ simplexCell k η) (hy : y ∈ simplexCell k η) :
    vecNormSq (x - y) ≤ (d : ℝ) * (3 : ℝ) ^ (-(2 * (k : ℤ))) := by
  obtain ⟨u, rfl, hu, _⟩ := hx
  obtain ⟨v, rfl, hv, _⟩ := hy
  rw [triadic_time_eq_side_sq]
  have hℓ : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  apply vecNormSq_sub_le_of_coordinate_diameter _ _ _ hℓ.le
  intro i
  simp only [Pi.add_apply]
  apply abs_le.mpr
  have hlo := mul_lt_mul_of_pos_left (show -(1 : ℝ) < u i - v i by
    linarith only [(hu i).1, (hv i).2]) hℓ
  have hhi := mul_lt_mul_of_pos_left (show u i - v i < (1 : ℝ) by
    linarith only [(hu i).2, (hv i).1]) hℓ
  constructor <;> nlinarith only [hlo, hhi]

/-- The lower Gaussian estimate on a cube, at the time specified in `p.besov.averages`. -/
theorem gaussianKernel_cubeCell_lower {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    {x y : Vec d} (hx : x ∈ cubeCell k j) (hy : y ∈ cubeCell k j) :
    (4 * Real.pi * (3 : ℝ) ^ (-(2 * (k : ℤ)))) ^ (-((d : ℝ) / 2)) *
        Real.exp (-((d : ℝ) / 4)) ≤
      gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) :=
  gaussianKernel_lower_of_sq_le _ _ _ (cubeCell_sq_diameter k j hx hy)

/-- The lower Gaussian estimate on a simplex, at the time specified in `p.besov.averages`. -/
theorem gaussianKernel_simplexCell_lower {d : ℕ} (k : ℕ) (η : SimplexIndex d k)
    {x y : Vec d} (hx : x ∈ simplexCell k η) (hy : y ∈ simplexCell k η) :
    (4 * Real.pi * (3 : ℝ) ^ (-(2 * (k : ℤ)))) ^ (-((d : ℝ) / 2)) *
        Real.exp (-((d : ℝ) / 4)) ≤
      gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) :=
  gaussianKernel_lower_of_sq_le _ _ _ (simplexCell_sq_diameter k η hx hy)

/-- The upper Gaussian comparison for two points in a cube. -/
theorem gaussianKernel_cubeCell_compare {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    (x : Vec d) {y z : Vec d} (hy : y ∈ cubeCell k j) (hz : z ∈ cubeCell k j) :
    gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * (3 : ℝ) ^ (-(2 * (k : ℤ)))) (by positivity) (x - z) :=
  gaussianKernel_compare_of_sq_sub_le _ _ _ _ _ (cubeCell_sq_diameter k j hy hz)

/-- The upper Gaussian comparison for two points in a simplex. -/
theorem gaussianKernel_simplexCell_compare {d : ℕ} (k : ℕ) (η : SimplexIndex d k)
    (x : Vec d) {y z : Vec d} (hy : y ∈ simplexCell k η) (hz : z ∈ simplexCell k η) :
    gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * (3 : ℝ) ^ (-(2 * (k : ℤ)))) (by positivity) (x - z) :=
  gaussianKernel_compare_of_sq_sub_le _ _ _ _ _ (simplexCell_sq_diameter k η hy hz)

end CoarseDeGiorgi.NegSobolev
