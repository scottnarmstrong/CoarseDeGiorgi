import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Statements.EuclidDist
import CoarseDeGiorgi.Foundations.Euclid.Basic
import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSupport
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceVolume

/-!
# Surface patch area

Upper and lower area bounds for Euclidean balls on the cube surface, for the summed-face
measure `surfaceMeasure`.
-/

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}


variable {d : ℕ}

private theorem prod_except_coordinate (i : Fin d) (a : ℝ≥0∞) :
    (∏ j : Fin d, if j = i then 1 else a) = a ^ (d - 1) := by
  classical
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  calc
    _ = ∏ _j ∈ Finset.univ.erase i, a := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    _ = _ := by simp

theorem seedSurfaceMeasure_finite (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := by
  change IsFiniteMeasure (Foundations.FracGeometry.surfaceMeasure (d := d) τ)
  infer_instance

/-- A tangential interval directed into the face, including when the center is
on an edge. Its endpoints have zero Lebesgue measure. -/
def seedInwardInterval (a δ : ℝ) : Set ℝ :=
  if 0 ≤ a then Ioo (a - δ) a else Ioo a (a + δ)

private theorem seedInwardInterval_volume (a δ : ℝ) :
    volume (seedInwardInterval a δ) = ENNReal.ofReal δ := by
  unfold seedInwardInterval
  split_ifs <;> rw [Real.volume_Ioo] <;> congr 1 <;> ring

private theorem seedInwardInterval_subset {τ a δ : ℝ} (ha : |a| ≤ τ / 2)
    (hδ : δ < τ / 2) : seedInwardInterval a δ ⊆ Ioo (-τ / 2) (τ / 2) := by
  intro b hb
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  unfold seedInwardInterval at hb
  split_ifs at hb with hn
  · constructor <;> linarith only [hb.1, hb.2, hn, hau, hδ]
  · constructor <;> linarith only [hb.1, hb.2, hn, hal, hδ]

private theorem seedInwardInterval_abs_sub_le {a δ b : ℝ}
    (hb : b ∈ seedInwardInterval a δ) : |b - a| ≤ δ := by
  apply abs_le.mpr
  unfold seedInwardInterval at hb
  split_ifs at hb <;> constructor <;> linarith only [hb.1, hb.2]

theorem seedFaceMeasure_euclidBall_lower {τ u : ℝ} (hu : 0 < u) (hut : u < τ / 2)
    (i : Fin d) (pos : Bool) (y : Vec d) (hy : ‖y‖ ≤ τ / 2)
    (hyi : y i = if pos then τ / 2 else -τ / 2) :
    ENNReal.ofReal (u / (2 * (d : ℝ))) ^ (d - 1) ≤
      cubeFaceMeasure τ i pos {x | euclidDist x y < u} := by
  classical
  have hd : 1 ≤ d := by have := i.isLt; omega
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdr
  let δ := u / (2 * (d : ℝ))
  have hδ : 0 < δ := div_pos hu (mul_pos (by norm_num) hdp)
  have hδu : δ ≤ u / 2 := by
    dsimp only [δ]
    apply div_le_div_of_nonneg_left hu.le (by norm_num)
    linarith only [hdr]
  have hδt : δ < τ / 2 := hδu.trans_lt ((half_lt_self hu).trans hut)
  let box : Fin d → Set ℝ := fun j =>
    if j = i then {y i} else seedInwardInterval (y j) δ
  let (j : Fin d) : IsFiniteMeasure (faceCoordinateMeasures τ i pos j) := by
    unfold faceCoordinateMeasures
    split_ifs <;> infer_instance
  have hvol : cubeFaceMeasure τ i pos (Set.pi univ box) = ENNReal.ofReal δ ^ (d - 1) := by
    rw [cubeFaceMeasure, Measure.pi_pi]
    calc
      _ = ∏ j : Fin d, if j = i then 1 else ENNReal.ofReal δ := by
        apply Finset.prod_congr rfl
        intro j _
        dsimp only [box, faceCoordinateMeasures]
        by_cases hji : j = i
        · simp only [hji, ite_true]
          rw [hyi]
          simp
        · simp only [hji, ite_false]
          have hm : MeasurableSet (seedInwardInterval (y j) δ) := by
            unfold seedInwardInterval; split_ifs <;> exact measurableSet_Ioo
          have hyj : |y j| ≤ τ / 2 := by
            have hn : |y j| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j
            exact hn.trans hy
          rw [Measure.restrict_apply hm, inter_eq_left.mpr
            (seedInwardInterval_subset hyj hδt)]
          exact seedInwardInterval_volume _ _
      _ = _ := prod_except_coordinate i _
  have hb : Set.pi univ box ⊆ {x : Vec d | euclidDist x y < u} := by
    intro x hx
    have hxy : ‖x - y‖ ≤ δ := by
      apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
      intro j
      have hj := hx j (mem_univ j)
      dsimp only [box] at hj
      by_cases hji : j = i
      · simp only [hji, ite_true, mem_singleton_iff] at hj
        simp only [Pi.sub_apply, hji, hj, sub_self, norm_zero]
        exact hδ.le
      · rw [ite_eq_right hji] at hj
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using seedInwardInterval_abs_sub_le hj
    have hsqrt : Real.sqrt (d : ℝ) ≤ d := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · exact hdp.le
      · nlinarith only [hdr]
    calc
      euclidDist x y ≤ Real.sqrt (d : ℝ) * ‖x - y‖ :=
        Foundations.Euclid.eNorm2_le_sqrt_mul_norm _
      _ ≤ (d : ℝ) * δ := mul_le_mul hsqrt hxy (norm_nonneg _) hdp.le
      _ = u / 2 := by dsimp only [δ]; field_simp
      _ < u := half_lt_self hu
  exact hvol.symm.le.trans (measure_mono hb)

theorem seedSurfaceMeasure_euclidPatch_lower {τ u : ℝ} (hu : 0 < u) (hut : u < τ / 2)
    {y : Vec d} (hy : y ∈ cubeSurface τ) :
    ENNReal.ofReal (u / (2 * (d : ℝ))) ^ (d - 1) ≤
      surfaceMeasure τ (cubeSurface τ ∩ {x | euclidDist x y < u}) := by
  classical
  have hτ : 0 < τ := by linarith only [hu, hut]
  change ‖y‖ = τ / 2 at hy
  have hex : ∃ i : Fin d, τ / 2 ≤ |y i| := by
    by_contra hn
    push Not at hn
    have hnorm : ‖y‖ < τ / 2 := (pi_norm_lt_iff (by linarith only [hτ])).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using hn i)
    rw [hy] at hnorm
    exact (lt_irrefl _) hnorm
  obtain ⟨i, hi⟩ := hex
  have hie : |y i| = τ / 2 := by
    have hn : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
    exact le_antisymm (hn.trans hy.le) hi
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, y i = if pos then τ / 2 else -τ / 2 := by
    by_cases hn : 0 ≤ y i
    · exact ⟨true, by simpa [abs_of_nonneg hn] using hie⟩
    · refine ⟨false, ?_⟩
      rw [abs_of_neg (lt_of_not_ge hn)] at hie
      simpa only [Bool.false_eq_true, ite_false, neg_div] using (neg_eq_iff_eq_neg.mp hie)
  have hl := seedFaceMeasure_euclidBall_lower hu hut i pos y hy.le hpos
  have hs : cubeFaceMeasure τ i pos {x | euclidDist x y < u} ≤
      surfaceMeasure τ {x | euclidDist x y < u} := by
    rw [surfaceMeasure]
    simp only [Measure.finsetSum_apply]
    calc
      _ ≤ ∑ b : Bool, cubeFaceMeasure τ i b {x | euclidDist x y < u} :=
        Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ pos)
      _ ≤ _ := Finset.single_le_sum
        (f := fun j : Fin d => ∑ b : Bool, cubeFaceMeasure τ j b {x | euclidDist x y < u})
        (fun _ _ => bot_le) (Finset.mem_univ i)
  have hae : ∀ᵐ x ∂surfaceMeasure (d := d) τ, x ∈ cubeSurface τ :=
    Foundations.FracGeometry.surfaceMeasure_ae_surface hτ.le
  rw [Measure.measure_inter_eq_of_ae hae]
  exact hl.trans hs


end

end CoarseDeGiorgi.WhitneyExt
