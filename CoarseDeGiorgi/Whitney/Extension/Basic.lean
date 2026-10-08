module

public import CoarseDeGiorgi.Whitney.Extension.SurfaceArea
public import CoarseDeGiorgi.Statements.SeedCutoff
public import CoarseDeGiorgi.Statements.SeedProjection
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.PointSupDist
public import CoarseDeGiorgi.Foundations.Triadic.WhitneyCubesProof

/-!
# Basic facts for the piecewise affine extension

The coordinate projection, the cutoff, Euclidean versus maximum distance, and integrability on the
cube surface.
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ### Euclidean distance -/

theorem norm_sub_le_euclidDist (x y : Vec d) : ‖x - y‖ ≤ euclidDist x y :=
  Foundations.Euclid.norm_le_eNorm2 (x - y)

theorem euclidDist_le_sqrt_mul (x y : Vec d) :
    euclidDist x y ≤ Real.sqrt (d : ℝ) * ‖x - y‖ :=
  Foundations.Euclid.eNorm2_le_sqrt_mul_norm (x - y)

theorem euclidDist_nonneg (x y : Vec d) : 0 ≤ euclidDist x y := Real.sqrt_nonneg _

theorem euclidDist_triangle (x y z : Vec d) :
    euclidDist x z ≤ euclidDist x y + euclidDist y z :=
  Foundations.Euclid.eDist2_triangle x y z

theorem euclidDist_comm (x y : Vec d) : euclidDist x y = euclidDist y x := by
  unfold euclidDist
  congr 1
  simp only [vecNormSq, vecDot, Pi.sub_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ### Cutoff -/

theorem seedCutoff_nonneg (u : ℝ) : 0 ≤ seedCutoff u :=
  le_min (by norm_num) (le_max_left _ _)

theorem seedCutoff_le_one (u : ℝ) : seedCutoff u ≤ 1 := min_le_left _ _

theorem seedCutoff_eq_one {u : ℝ} (hu : u ≤ 1 / 2) : seedCutoff u = 1 := by
  apply min_eq_left
  apply (show (1 : ℝ) ≤ 2 - 2 * u by linarith only [hu]).trans
  exact le_max_right _ _

theorem seedCutoff_eq_zero {u : ℝ} (hu : 1 ≤ u) : seedCutoff u = 0 := by
  have h : 2 - 2 * u ≤ 0 := by linarith only [hu]
  rw [seedCutoff, max_eq_left h, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem seedCutoff_abs_sub_le (u v : ℝ) : |seedCutoff u - seedCutoff v| ≤ 2 * |u - v| := by
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - 2 * u)) 1 (max 0 (2 - 2 * v))
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (2 - 2 * u) 0 (2 - 2 * v)
  have hmin' : |seedCutoff u - seedCutoff v| ≤
      |max 0 (2 - 2 * u) - max 0 (2 - 2 * v)| := by
    calc
      _ ≤ _ := hmin
      _ = _ := by rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
  have hmax' : |max 0 (2 - 2 * u) - max 0 (2 - 2 * v)| ≤
      |2 - 2 * u - (2 - 2 * v)| := by
    calc
      _ ≤ _ := hmax
      _ = _ := by rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
  have heq : 2 - 2 * u - (2 - 2 * v) = -2 * (u - v) := by ring
  rw [heq, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg] at hmax'
  exact hmin'.trans hmax'

/-! ### Coordinate projection -/

theorem seedProjection_coordinate_bound {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) (i : Fin d) :
    |seedProjection τ x i| ≤ τ / 2 := by
  change |max (-τ / 2) (min (x i) (τ / 2))| ≤ τ / 2
  apply abs_le.mpr
  constructor
  · simpa only [neg_div] using le_max_left (-τ / 2) (min (x i) (τ / 2))
  · exact max_le (by linarith only [hτ]) (min_le_right _ _)

theorem norm_seedProjection_le {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) :
    ‖seedProjection τ x‖ ≤ τ / 2 := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hτ (by norm_num))).mpr
  intro i
  simpa only [Real.norm_eq_abs] using seedProjection_coordinate_bound hτ x i

theorem seedProjection_coordinate_sub_le (τ : ℝ) (x y : Vec d) (i : Fin d) :
    |seedProjection τ x i - seedProjection τ y i| ≤ |x i - y i| := by
  have hmin := abs_min_sub_min_le_max (x i) (τ / 2) (y i) (τ / 2)
  have hmax := abs_max_sub_max_le_max (-τ / 2) (min (x i) (τ / 2))
    (-τ / 2) (min (y i) (τ / 2))
  calc
    _ ≤ _ := hmax
    _ = |min (x i) (τ / 2) - min (y i) (τ / 2)| := by
      rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
    _ ≤ _ := hmin
    _ = _ := by rw [sub_self, abs_zero]; exact max_eq_left (abs_nonneg _)

theorem seedProjection_euclidDist_le (τ : ℝ) (x y : Vec d) :
    euclidDist (seedProjection τ x) (seedProjection τ y) ≤ euclidDist x y := by
  apply Real.sqrt_le_sqrt
  simp only [vecNormSq, vecDot, Pi.sub_apply, ← pow_two]
  apply Finset.sum_le_sum
  intro i _
  exact sq_le_sq.mpr (seedProjection_coordinate_sub_le τ x y i)

theorem seedProjection_eq_self {τ : ℝ} {x : Vec d} (hx : ‖x‖ ≤ τ / 2) :
    seedProjection τ x = x := by
  funext i
  have hi : |x i| ≤ τ / 2 := by
    have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hn.trans hx
  obtain ⟨hl, hu⟩ := abs_le.mp hi
  have hl' : -τ / 2 ≤ x i := by simpa only [neg_div] using hl
  simp only [seedProjection, min_eq_left hu, max_eq_right hl']

theorem seedProjection_mem_surface {τ : ℝ} (hτ : 0 < τ) {x : Vec d}
    (hx : τ / 2 ≤ ‖x‖) : seedProjection τ x ∈ cubeSurface τ := by
  change ‖seedProjection τ x‖ = τ / 2
  apply le_antisymm (norm_seedProjection_le hτ.le x)
  by_contra hn
  have hp : ‖seedProjection τ x‖ < τ / 2 := lt_of_not_ge hn
  have hi (i : Fin d) : |x i| < τ / 2 := by
    have hpi : |seedProjection τ x i| < τ / 2 := by
      have hn : |seedProjection τ x i| ≤ ‖seedProjection τ x‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (seedProjection τ x) i
      exact hn.trans_lt hp
    have hpib := abs_lt.mp hpi
    have hl : -τ / 2 < x i := by
      by_contra hn
      have hm : min (x i) (τ / 2) ≤ -τ / 2 := (min_le_left _ _).trans (le_of_not_gt hn)
      have he : seedProjection τ x i = -τ / 2 := max_eq_left hm
      rw [he] at hpib
      linarith only [hpib.1]
    have hu : x i < τ / 2 := by
      by_contra hn
      have he : seedProjection τ x i = τ / 2 := by
        rw [seedProjection, min_eq_right (le_of_not_gt hn), max_eq_right (by linarith only [hτ])]
      rw [he] at hpib
      exact (lt_irrefl _) hpib.2
    exact abs_lt.mpr ⟨by simpa only [neg_div] using hl, hu⟩
  have : ‖x‖ < τ / 2 := (pi_norm_lt_iff (by linarith only [hτ])).mpr
    (fun i => by simpa only [Real.norm_eq_abs] using hi i)
  exact (not_lt_of_ge hx) this

theorem norm_sub_seedProjection_le {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) :
    ‖x - seedProjection τ x‖ ≤ max 0 (‖x‖ - τ / 2) := by
  apply (pi_norm_le_iff_of_nonneg (le_max_left _ _)).mpr
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  change |x i - max (-τ / 2) (min (x i) (τ / 2))| ≤ max 0 (‖x‖ - τ / 2)
  by_cases hl : x i ≤ -τ / 2
  · have hu : x i ≤ τ / 2 := by linarith only [hl, hτ]
    rw [min_eq_left hu, max_eq_left hl, abs_of_nonpos (by linarith only [hl])]
    have hn := (abs_le.mp hi).1
    have hm : ‖x‖ - τ / 2 ≤ max 0 (‖x‖ - τ / 2) := le_max_right _ _
    linarith only [hn, hm]
  · by_cases hu : τ / 2 ≤ x i
    · rw [min_eq_right hu, max_eq_right (by linarith only [hτ]),
        abs_of_nonneg (by linarith only [hu])]
      have hn := (abs_le.mp hi).2
      exact (sub_le_sub_right hn _).trans (le_max_right _ _)
    · rw [min_eq_left (le_of_not_ge hu), max_eq_right (le_of_not_ge hl), sub_self, abs_zero]
      exact le_max_left _ _

theorem seedPointDistance_eq {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) :
    pointSupDist x (closedReferenceCube τ) = max 0 (‖x‖ - τ / 2) := by
  rw [Foundations.Triadic.pointSupDist_eq_infDist]
  have hproj : seedProjection τ x ∈ closedReferenceCube τ :=
    seedProjection_coordinate_bound hτ x
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem hproj).trans
      (by simpa only [dist_eq_norm] using norm_sub_seedProjection_le hτ x)
  · apply max_le Metric.infDist_nonneg
    apply (Metric.le_infDist ⟨seedProjection τ x, hproj⟩).mpr
    intro y hy
    have hny : ‖y‖ ≤ τ / 2 := (pi_norm_le_iff_of_nonneg
      (div_nonneg hτ (by norm_num))).mpr (fun i => by
        simpa only [Real.norm_eq_abs] using hy i)
    have hn := norm_add_le (x - y) y
    rw [sub_add_cancel] at hn
    rw [dist_eq_norm]
    linarith only [hn, hny]


end

end CoarseDeGiorgi.WhitneyExt
