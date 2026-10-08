import CoarseDeGiorgi.Harnack.Log.FiniteCover
import CoarseDeGiorgi.Harnack.LogLimit.OverlapHolder
import CoarseDeGiorgi.Localization.Geometry
import CoarseDeGiorgi.Foundations.Reconstruction.Geometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CoarseDeGiorgi.Harnack.Log

open scoped BigOperators
open scoped ENNReal

noncomputable section

open Homogenization MeasureTheory

/-- Adjacent fixed-grid auxiliary cubes have an overlap of positive volume.
The smaller auxiliary cube at scale five centered one fine-grid step from
the first center lies inside their intersection. -/
theorem fixedLogGrid_positive_neighbor_overlap {d : ℕ}
    (z : Fin d → ℤ) (i : Fin d) :
    0 < volume (auxCube 4 z ∩ auxCube 4 (Function.update z i (z i + 1))) := by
  let z' := Function.update z i (z i + 1)
  let y : Fin d → ℤ := fun j => 3 * z j + if j = i then 1 else 0
  have hs4 : Localization.gridSpacing 4 = (1 / 81 : ℝ) := by
    norm_num [Localization.gridSpacing]
  have hs5 : Localization.gridSpacing 5 = (1 / 243 : ℝ) := by
    norm_num [Localization.gridSpacing]
  have hrad : 3 * ((3 : ℝ) ^ 4)⁻¹ / 2 = ((3 : ℝ) ^ 3)⁻¹ / 2 := by
    norm_num
  have hy0 (j : Fin d) : Localization.gridCenter 5 y j -
      Localization.gridCenter 4 z j = if j = i then (1 / 243 : ℝ) else 0 := by
    by_cases hji : j = i
    · subst j
      simp [y, Localization.gridCenter, hs4, hs5]
      ring
    · simp [y, Localization.gridCenter, hs4, hs5, hji]
      ring
  have hy1 (j : Fin d) : Localization.gridCenter 5 y j -
      Localization.gridCenter 4 z' j = if j = i then -(2 / 243 : ℝ) else 0 := by
    by_cases hji : j = i
    · subst j
      simp [z', y, Localization.gridCenter, hs4, hs5]
      ring
    · simp [z', y, Localization.gridCenter, hs4, hs5, hji]
      ring
  have hsub : auxCube 5 y ⊆ auxCube 4 z ∩ auxCube 4 z' := by
    intro x hx
    rw [Localization.auxCube_eq_coordinates] at hx ⊢
    constructor
    · intro j
      have hdist := abs_sub_le (x j) (Localization.gridCenter 5 y j)
        (Localization.gridCenter 4 z j)
      have hshift : |Localization.gridCenter 5 y j - Localization.gridCenter 4 z j| ≤
          (1 / 243 : ℝ) := by rw [hy0]; split_ifs <;> norm_num
      have hxi := hx j
      rw [hs5] at hxi
      have hineq : |x j - Localization.gridCenter 4 z j| <
          3 * Localization.gridSpacing 4 / 2 := by
        rw [hs4]
        nlinarith
      simpa [Localization.gridCenter, Localization.gridSpacing, hrad] using hineq
    · intro j
      have hdist := abs_sub_le (x j) (Localization.gridCenter 5 y j)
        (Localization.gridCenter 4 z' j)
      have hshift : |Localization.gridCenter 5 y j - Localization.gridCenter 4 z' j| ≤
          (2 / 243 : ℝ) := by rw [hy1]; split_ifs <;> norm_num
      have hxi := hx j
      rw [hs5] at hxi
      have hineq : |x j - Localization.gridCenter 4 z' j| <
          3 * Localization.gridSpacing 4 / 2 := by
        rw [hs4]
        nlinarith
      simpa [Localization.gridCenter, Localization.gridSpacing, hrad] using hineq
  have hvol : volume (auxCube 5 y) > 0 := by
    by_contra hnot
    have hle : volume (auxCube 5 y) ≤ 0 := le_of_not_gt hnot
    have hz : volume (auxCube 5 y) = 0 := le_antisymm hle bot_le
    exact Foundations.Reconstruction.volume_auxCube_ne_zero 5 y hz
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-- If overlap averaging bounds the integral of the constant difference, divide
by the positive overlap volume to obtain a bound on the two means.
-/
theorem mean_difference_of_overlap_integral_bound {d : ℕ} (O : Set (Vec d))
    (c c' A : ℝ) (hvol : 0 < (volume O).toReal)
    (hbound : |∫ x in O, (fun _ : Vec d => c - c') x| ≤ A) :
    |c - c'| ≤ A / (volume O).toReal := by
  have hconst : (∫ x in O, (fun _ : Vec d => c - c') x) =
      (volume O).toReal * (c - c') := by
    rw [integral_const]
    simp [Measure.real, smul_eq_mul]
  have hscaled : (volume O).toReal * |c - c'| ≤ A := by
    rw [hconst, abs_mul, abs_of_pos hvol] at hbound
    exact hbound
  apply (le_div_iff₀ hvol).2
  nlinarith [hscaled]

/-- Holder's overlap estimates transfer to the difference of the two centers.
The L¹ deviation bounds are the form obtained from the local Lʳ bounds by
Holder on the overlap.
-/
theorem means_close_of_overlap_deviation {d : ℕ} (O : Set (Vec d))
    (w : Vec d → ℝ) (c c' A A' : ℝ)
    (hvol : 0 < (volume O).toReal)
    (h1 : IntegrableOn (fun x => w x - c) O)
    (h2 : IntegrableOn (fun x => w x - c') O)
    (h1bound : ∫ x in O, |w x - c| ≤ A)
    (h2bound : ∫ x in O, |w x - c'| ≤ A') :
    |c - c'| ≤ (A + A') / (volume O).toReal := by
  have hleft : IntegrableOn (fun x => c - w x) O := by
    convert h1.neg using 1
    funext x
    simp
  have hsumInt : (∫ x in O, (fun x => (c - w x) + (w x - c')) x) =
      (∫ x in O, (fun x => c - w x) x) +
        (∫ x in O, (fun x => w x - c') x) := integral_add hleft h2
  have hnormLeft : |∫ x in O, (fun x => c - w x) x| ≤ A := by
    calc
      |∫ x in O, (fun x => c - w x) x| ≤ ∫ x in O, |c - w x| :=
        norm_integral_le_integral_norm (fun x => c - w x)
      _ = ∫ x in O, |w x - c| := by congr 1; funext x; rw [abs_sub_comm]
      _ ≤ A := h1bound
  have hnormRight : |∫ x in O, (fun x => w x - c') x| ≤ A' := by
    calc
      |∫ x in O, (fun x => w x - c') x| ≤ ∫ x in O, |w x - c'| :=
        norm_integral_le_integral_norm (fun x => w x - c')
      _ ≤ A' := h2bound
  have hsumBound : |∫ x in O,
      (fun x => (c - w x) + (w x - c')) x| ≤ A + A' := by
    rw [hsumInt]
    calc
      |(∫ x in O, (fun x => c - w x) x) +
          (∫ x in O, (fun x => w x - c') x)| ≤
          |∫ x in O, (fun x => c - w x) x| +
            |∫ x in O, (fun x => w x - c') x| := abs_add_le _ _
      _ ≤ A + A' := add_le_add hnormLeft hnormRight
  have hconstBound : |∫ x in O, (fun _ : Vec d => c - c') x| ≤ A + A' := by
    calc
      |∫ x in O, (fun _ : Vec d => c - c') x| =
          |∫ x in O, (fun x => (c - w x) + (w x - c')) x| := by
            congr 1
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ ≤ A + A' := hsumBound
  exact mean_difference_of_overlap_integral_bound O c c' (A + A') hvol hconstBound

/-- Local oscillation bounds on two adjacent covering cubes control their
auxiliary means through the finite-overlap Holder estimate. -/
theorem adjacentLogGrid_means_close_of_holder {d : ℕ}
    (r B : ℝ) (hr : 1 < r) (hB : 0 ≤ B) (w : Vec d → ℝ)
    (z : Fin d → ℤ) (hz : z ∈ fixedLogGrid (d := d)) (i : Fin d)
    (hz' : Function.update z i (z i + 1) ∈ fixedLogGrid)
    (hLocal : ∀ z ∈ fixedLogGrid,
      eLpNorm (fun x => w x - volumeAverage (auxCube 4 z) w)
        (ENNReal.ofReal r) (volume.restrict (auxCube 4 z)) ≤ ENNReal.ofReal B) :
    |volumeAverage (auxCube 4 z) w -
      volumeAverage (auxCube 4 (Function.update z i (z i + 1))) w| ≤
      2 * B *
        (volume (auxCube 4 z ∩ auxCube 4 (Function.update z i (z i + 1)))).toReal ^
          (1 - 1 / r) /
        (volume (auxCube 4 z ∩ auxCube 4 (Function.update z i (z i + 1)))).toReal := by
  let z' := Function.update z i (z i + 1)
  let Q := auxCube 4 z
  let Q' := auxCube 4 z'
  let O := Q ∩ Q'
  let μ := (volume.restrict Q).restrict O
  have hQmeas : MeasurableSet Q := Foundations.Reconstruction.measurableSet_auxCube 4 z
  have hQ'meas : MeasurableSet Q' := Foundations.Reconstruction.measurableSet_auxCube 4 z'
  have hOmeas : MeasurableSet O := hQmeas.inter hQ'meas
  have hQtop : volume Q ≠ ⊤ := Foundations.Reconstruction.volume_auxCube_ne_top 4 z
  let : IsFiniteMeasure (volume.restrict Q) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, hQmeas, Set.univ_inter] using hQtop.lt_top
  have hμle : μ ≤ volume.restrict Q := Measure.restrict_le_self
  have hμeq : μ = volume.restrict O := by
    dsimp [μ]
    rw [Measure.restrict_restrict hOmeas]
    congr 1
    ext x
    change (x ∈ O ∧ x ∈ Q) ↔ x ∈ O
    constructor
    · rintro ⟨hx, _⟩
      exact hx
    · intro hx
      have hxQ : x ∈ Q := by
        change x ∈ Q ∩ Q' at hx
        exact hx.1
      exact ⟨hx, hxQ⟩
  have hvol : 0 < (volume O).toReal := by
    have hvolpos : 0 < volume O := by
      dsimp [O, Q, Q']
      exact fixedLogGrid_positive_neighbor_overlap z i
    have hvoltop : volume O ≠ ⊤ := by
      intro htop
      apply hQtop
      apply top_unique
      rw [← htop]
      exact measure_mono Set.inter_subset_left
    exact ENNReal.toReal_pos hvolpos.ne' hvoltop
  have hlocalLeft := hLocal z hz
  have hlocalRight := hLocal z' hz'
  have hleftBound : eLpNorm (fun x => w x - volumeAverage Q w)
      (ENNReal.ofReal r) μ ≤ ENNReal.ofReal B := by
    exact (eLpNorm_mono_measure (p := ENNReal.ofReal r)
      (fun x => w x - volumeAverage Q w) hμle).trans hlocalLeft
  have hrightMeasure : volume.restrict O ≤ volume.restrict Q' := by
    dsimp [O, Q']
    exact volume.restrict_mono_set Set.inter_subset_right
  have hrightBound : eLpNorm (fun x => w x - volumeAverage Q' w)
      (ENNReal.ofReal r) μ ≤ ENNReal.ofReal B := by
    rw [hμeq]
    exact (eLpNorm_mono_measure (p := ENNReal.ofReal r)
      (fun x => w x - volumeAverage Q' w) hrightMeasure).trans hlocalRight
  obtain ⟨hleftInt, hleftIntegral⟩ :=
    CoarseDeGiorgi.Harnack.LogLimit.integral_abs_le_of_eLpNorm_le hr hB hleftBound
  obtain ⟨hrightInt, hrightIntegral⟩ :=
    CoarseDeGiorgi.Harnack.LogLimit.integral_abs_le_of_eLpNorm_le hr hB hrightBound
  have hmass : (volume.restrict O) Set.univ = volume O := by
    simp [Measure.restrict_apply]
  have hleftIntOn : IntegrableOn (fun x => w x - volumeAverage Q w) O := by
    change Integrable (fun x => w x - volumeAverage Q w) (volume.restrict O)
    rw [← hμeq]
    exact hleftInt
  have hrightIntOn : IntegrableOn (fun x => w x - volumeAverage Q' w) O := by
    change Integrable (fun x => w x - volumeAverage Q' w) (volume.restrict O)
    rw [← hμeq]
    exact hrightInt
  have hleftIntegral' : ∫ x in O, |w x - volumeAverage Q w| ≤
      B * (volume O).toReal ^ (1 - 1 / r) := by
    rw [hμeq] at hleftIntegral
    rw [hmass] at hleftIntegral
    simpa only [Real.norm_eq_abs] using hleftIntegral
  have hrightIntegral' : ∫ x in O, |w x - volumeAverage Q' w| ≤
      B * (volume O).toReal ^ (1 - 1 / r) := by
    rw [hμeq] at hrightIntegral
    rw [hmass] at hrightIntegral
    simpa only [Real.norm_eq_abs] using hrightIntegral
  have hclose := means_close_of_overlap_deviation O w (volumeAverage Q w)
    (volumeAverage Q' w) (B * (volume O).toReal ^ (1 - 1 / r))
    (B * (volume O).toReal ^ (1 - 1 / r)) hvol hleftIntOn hrightIntOn
    hleftIntegral' hrightIntegral'
  have hclose' : |volumeAverage Q w - volumeAverage Q' w| ≤
      2 * B * (volume O).toReal ^ (1 - 1 / r) / (volume O).toReal := by
    calc
      |volumeAverage Q w - volumeAverage Q' w| ≤
        (B * (volume O).toReal ^ (1 - 1 / r) +
          B * (volume O).toReal ^ (1 - 1 / r)) / (volume O).toReal := hclose
      _ = 2 * B * (volume O).toReal ^ (1 - 1 / r) / (volume O).toReal := by ring
  simpa [z', Q, Q', O] using hclose'

private noncomputable def fixedLogGrid_edgeFactor {d : ℕ} (r : ℝ)
    (e : (Fin d → ℤ) × Fin d) : ℝ :=
  let O := auxCube 4 e.1 ∩ auxCube 4 (Function.update e.1 e.2 (e.1 e.2 + 1))
  2 * (volume O).toReal ^ (1 - 1 / r) / (volume O).toReal

private theorem fixedLogGrid_edgeFactor_nonneg {d : ℕ} (r : ℝ)
    (e : (Fin d → ℤ) × Fin d) : 0 ≤ fixedLogGrid_edgeFactor r e := by
  let O := auxCube 4 e.1 ∩ auxCube 4 (Function.update e.1 e.2 (e.1 e.2 + 1))
  have hvolpos : 0 < volume O := by
    dsimp [O]
    exact fixedLogGrid_positive_neighbor_overlap e.1 e.2
  have hvoltop : volume O ≠ ⊤ := by
    have hQtop : volume (auxCube 4 e.1) ≠ ⊤ :=
      Foundations.Reconstruction.volume_auxCube_ne_top 4 e.1
    intro htop
    apply hQtop
    apply top_unique
    rw [← htop]
    exact measure_mono Set.inter_subset_left
  have hvol : 0 < (volume O).toReal := ENNReal.toReal_pos hvolpos.ne' hvoltop
  dsimp [fixedLogGrid_edgeFactor, O]
  positivity

/-- A dimension and exponent dependent sum of all neighboring-edge factors in
the fixed lattice cover. -/
noncomputable def fixedLogGrid_pathConstant {d : ℕ} (r : ℝ) : ℝ :=
  let edges : Finset ((Fin d → ℤ) × Fin d) := fixedLogGrid.product Finset.univ
  ∑ e ∈ edges, fixedLogGrid_edgeFactor r e

theorem fixedLogGrid_pathConstant_nonneg {d : ℕ} (r : ℝ) :
    0 ≤ fixedLogGrid_pathConstant (d := d) r := by
  classical
  dsimp [fixedLogGrid_pathConstant]
  exact Finset.sum_nonneg fun e he => fixedLogGrid_edgeFactor_nonneg r e

/-- Uniform neighboring-mean control follows from the local bounds and the
finite family of positive-volume grid overlaps. -/
theorem fixedLogGrid_neighbor_steps_of_local_bounds {d : ℕ}
    (r B : ℝ) (hr : 1 < r) (hB : 0 ≤ B)
    (w : Vec d → ℝ) (hLocal : ∀ z ∈ fixedLogGrid,
      eLpNorm (fun x => w x - volumeAverage (auxCube 4 z) w)
        (ENNReal.ofReal r) (volume.restrict (auxCube 4 z)) ≤ ENNReal.ofReal B) :
    ∀ z ∈ fixedLogGrid, ∀ i : Fin d,
      Function.update z i (z i + 1) ∈ fixedLogGrid →
        |volumeAverage (auxCube 4 z) w -
          volumeAverage (auxCube 4 (Function.update z i (z i + 1))) w| ≤
            fixedLogGrid_pathConstant (d := d) r * B := by
  classical
  let edges : Finset ((Fin d → ℤ) × Fin d) := fixedLogGrid.product Finset.univ
  let K : ℝ := fixedLogGrid_pathConstant (d := d) r
  have hK : 0 ≤ K := fixedLogGrid_pathConstant_nonneg (d := d) r
  intro z hz i hz'
  have hedge : (z, i) ∈ edges := Finset.mem_product.mpr ⟨hz, Finset.mem_univ i⟩
  have hfactor : fixedLogGrid_edgeFactor r (z, i) ≤ K := by
    dsimp [K]
    exact Finset.single_le_sum
      (fun e he => fixedLogGrid_edgeFactor_nonneg r e) hedge
  have hclose := adjacentLogGrid_means_close_of_holder r B hr hB w z hz i hz' hLocal
  have hscaled :
      2 * B * (volume (auxCube 4 z ∩
        auxCube 4 (Function.update z i (z i + 1)))).toReal ^ (1 - 1 / r) /
        (volume (auxCube 4 z ∩
          auxCube 4 (Function.update z i (z i + 1)))).toReal ≤ K * B := by
    have heq :
        2 * B * (volume (auxCube 4 z ∩
          auxCube 4 (Function.update z i (z i + 1)))).toReal ^ (1 - 1 / r) /
          (volume (auxCube 4 z ∩
            auxCube 4 (Function.update z i (z i + 1)))).toReal =
          fixedLogGrid_edgeFactor r (z, i) * B := by
      dsimp [fixedLogGrid_edgeFactor]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hfactor hB
  simpa [K] using hclose.trans hscaled

/-- The fixed lattice box is coordinatewise bounded by `35`. -/
private theorem fixedLogGrid_coordinate_bounds {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid (d := d)) (i : Fin d) :
    -35 ≤ z i ∧ z i ≤ 35 := by
  have h := Fintype.mem_piFinset.mp hz i
  exact Finset.mem_Icc.mp h

/-- Replacing one coordinate by another point of the same integer interval
preserves membership in the fixed grid. -/
private theorem fixedLogGrid_update_mem {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid (d := d)) (i : Fin d) (k : ℤ)
    (hk : -35 ≤ k ∧ k ≤ 35) :
    Function.update z i k ∈ fixedLogGrid := by
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  by_cases hji : j = i
  · subst j
    simpa using hk
  · simpa [Function.update_of_ne hji] using fixedLogGrid_coordinate_bounds hz j

/-- Manhattan distance from the zero lattice point. -/
private def fixedLogGridDistance {d : ℕ} (z : Fin d → ℤ) : ℕ :=
  ∑ i : Fin d, (z i).natAbs

private theorem fixedLogGridDistance_pos_decrease {d : ℕ}
    (z : Fin d → ℤ) (i : Fin d) (hi : 0 < z i) :
    fixedLogGridDistance (Function.update z i (z i - 1)) + 1 =
      fixedLogGridDistance z := by
  classical
  let y := Function.update z i (z i - 1)
  let f := fun j : Fin d => (y j).natAbs
  let g := fun j : Fin d => (z j).natAbs
  have hsame : ∑ j ∈ Finset.univ.erase i, f j =
      ∑ j ∈ Finset.univ.erase i, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [f, g, y, Function.update_of_ne hji]
  have hnat : (z i - 1).natAbs + 1 = (z i).natAbs := by
    have hcast : ((z i - 1).natAbs : ℤ) + 1 = ((z i).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (by omega : 0 ≤ z i - 1),
        Int.natAbs_of_nonneg (by omega : 0 ≤ z i)]
      omega
    exact_mod_cast hcast
  have hfi : f i = (z i - 1).natAbs := by simp [f, y]
  have hgi : g i = (z i).natAbs := by simp [g]
  have hsumY := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hsumZ := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
  unfold fixedLogGridDistance
  change (∑ j ∈ Finset.univ, f j) + 1 = ∑ j ∈ Finset.univ, g j
  rw [← hsumY, ← hsumZ, hsame, hfi, hgi]
  omega

private theorem fixedLogGridDistance_neg_decrease {d : ℕ}
    (z : Fin d → ℤ) (i : Fin d) (hi : z i < 0) :
    fixedLogGridDistance (Function.update z i (z i + 1)) + 1 =
      fixedLogGridDistance z := by
  classical
  let y := Function.update z i (z i + 1)
  let f := fun j : Fin d => (y j).natAbs
  let g := fun j : Fin d => (z j).natAbs
  have hsame : ∑ j ∈ Finset.univ.erase i, f j =
      ∑ j ∈ Finset.univ.erase i, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [f, g, y, Function.update_of_ne hji]
  have hnat : (z i + 1).natAbs + 1 = (z i).natAbs := by
    have hcast : ((z i + 1).natAbs : ℤ) + 1 = ((z i).natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (by omega : z i + 1 ≤ 0),
        Int.ofNat_natAbs_of_nonpos (by omega : z i ≤ 0)]
      omega
    exact_mod_cast hcast
  have hfi : f i = (z i + 1).natAbs := by simp [f, y]
  have hgi : g i = (z i).natAbs := by simp [g]
  have hsumY := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hsumZ := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
  unfold fixedLogGridDistance
  change (∑ j ∈ Finset.univ, f j) + 1 = ∑ j ∈ Finset.univ, g j
  rw [← hsumY, ← hsumZ, hsame, hfi, hgi]
  omega

/-- Any point of the fixed grid is joined to zero by coordinate-neighbor
steps. The induction follows the Manhattan distance, so it gives a path of at
most `35*d` edges without assuming a dimension-dependent path as input. -/
theorem fixedLogGrid_mean_bound_of_neighbor_steps {d : ℕ}
    (f : (Fin d → ℤ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ z ∈ fixedLogGrid (d := d), ∀ i : Fin d,
      Function.update z i (z i + 1) ∈ fixedLogGrid →
      |f z - f (Function.update z i (z i + 1))| ≤ B)
    {z : Fin d → ℤ} (hz : z ∈ fixedLogGrid (d := d)) :
    |f z - f (fun _ => 0)| ≤ (35 * (d : ℝ)) * B := by
  classical
  let zero : Fin d → ℤ := fun _ => 0
  have hzero : zero ∈ fixedLogGrid := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (by norm_num)
  have hmain : ∀ n : ℕ, ∀ z : Fin d → ℤ,
      z ∈ fixedLogGrid → fixedLogGridDistance z = n →
      |f z - f zero| ≤ (n : ℝ) * B := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz hdist
      by_cases hz0 : z = zero
      · subst z
        simp only [sub_self, abs_zero]
        exact mul_nonneg (by positivity) hB
      · have hcoord : ∃ i : Fin d, z i ≠ 0 := by
          by_contra h
          push Not at h
          apply hz0
          funext i
          exact h i
        obtain ⟨i, hzi⟩ := hcoord
        rcases lt_or_gt_of_ne hzi with hneg | hpos
        · let y := Function.update z i (z i + 1)
          have hycoord : -35 ≤ z i + 1 ∧ z i + 1 ≤ 35 := by
            have hc := fixedLogGrid_coordinate_bounds hz i
            omega
          have hy : y ∈ fixedLogGrid := by
            simpa [y] using fixedLogGrid_update_mem hz i (z i + 1) hycoord
          have hdec := fixedLogGridDistance_neg_decrease z i hneg
          have hdecY : fixedLogGridDistance y + 1 = fixedLogGridDistance z := by
            simpa [y] using hdec
          have hlt : fixedLogGridDistance y < n := by
            rw [← hdist, ← hdecY]
            omega
          have hrec := ih (fixedLogGridDistance y) hlt y hy rfl
          have hstepz : |f z - f y| ≤ B := by
            exact hstep z hz i (by simpa [y] using hy)
          have htri : |f z - f zero| ≤ |f z - f y| + |f y - f zero| :=
            abs_sub_le _ _ _
          have hnatcast : (fixedLogGridDistance y : ℝ) + 1 = n := by
            exact_mod_cast (by rw [← hdist, hdecY])
          calc
            |f z - f zero| ≤ |f z - f y| + |f y - f zero| := htri
            _ ≤ B + (fixedLogGridDistance y : ℝ) * B := add_le_add hstepz hrec
            _ = (n : ℝ) * B := by rw [← hnatcast]; ring
        · let y := Function.update z i (z i - 1)
          have hycoord : -35 ≤ z i - 1 ∧ z i - 1 ≤ 35 := by
            have hc := fixedLogGrid_coordinate_bounds hz i
            omega
          have hy : y ∈ fixedLogGrid := by
            simpa [y] using fixedLogGrid_update_mem hz i (z i - 1) hycoord
          have hdec := fixedLogGridDistance_pos_decrease z i hpos
          have hdecY : fixedLogGridDistance y + 1 = fixedLogGridDistance z := by
            simpa [y] using hdec
          have hlt : fixedLogGridDistance y < n := by
            rw [← hdist, ← hdecY]
            omega
          have hrec := ih (fixedLogGridDistance y) hlt y hy rfl
          have hnext : Function.update y i (y i + 1) = z := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [y]
            · simp [y, Function.update_of_ne hji]
          have hstepy : |f y - f z| ≤ B := by
            have hh := hstep y hy i (by simpa [hnext] using hz)
            simpa [hnext] using hh
          have hstepz : |f z - f y| ≤ B := by
            simpa [abs_sub_comm] using hstepy
          have hnatcast : (fixedLogGridDistance y : ℝ) + 1 = n := by
            exact_mod_cast (by rw [← hdist, hdecY])
          have htri : |f z - f zero| ≤ |f z - f y| + |f y - f zero| :=
            abs_sub_le _ _ _
          calc
            |f z - f zero| ≤ |f z - f y| + |f y - f zero| := htri
            _ ≤ B + (fixedLogGridDistance y : ℝ) * B := add_le_add hstepz hrec
            _ = (n : ℝ) * B := by rw [← hnatcast]; ring
  have hdistance := hmain (fixedLogGridDistance z) z hz rfl
  have hcoord (i : Fin d) : (z i).natAbs ≤ 35 := by
    have hb := fixedLogGrid_coordinate_bounds hz i
    rcases le_total 0 (z i) with hpos | hneg
    · have hc : ((z i).natAbs : ℤ) = z i := Int.natAbs_of_nonneg hpos
      have : ((z i).natAbs : ℤ) ≤ 35 := by rw [hc]; exact hb.2
      exact_mod_cast this
    · have hc : ((z i).natAbs : ℤ) = -(z i) := Int.ofNat_natAbs_of_nonpos hneg
      have : ((z i).natAbs : ℤ) ≤ 35 := by rw [hc]; omega
      exact_mod_cast this
  have hdistBound : fixedLogGridDistance z ≤ 35 * d := by
    unfold fixedLogGridDistance
    calc
      (∑ i : Fin d, (z i).natAbs) ≤ ∑ _i : Fin d, 35 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = 35 * d := by simp [Nat.mul_comm]
  have hrealBound : (fixedLogGridDistance z : ℝ) * B ≤
      (35 * (d : ℝ)) * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast hdistBound
  exact hdistance.trans hrealBound

/-- Uniform form of the fixed-grid path bound, with the zero lattice point as
reference center. -/
theorem fixedLogGrid_all_mean_bounds {d : ℕ}
    (f : (Fin d → ℤ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ z ∈ fixedLogGrid (d := d), ∀ i : Fin d,
      Function.update z i (z i + 1) ∈ fixedLogGrid →
      |f z - f (Function.update z i (z i + 1))| ≤ B) :
    ∀ z ∈ fixedLogGrid,
      |f z - f (fun _ => 0)| ≤ (35 * (d : ℝ)) * B := by
  intro z hz
  exact fixedLogGrid_mean_bound_of_neighbor_steps f B hB hstep hz

end

end CoarseDeGiorgi.Harnack.Log
