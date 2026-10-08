import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import Mathlib.MeasureTheory.Integral.Prod

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The free coordinates of an open face. -/
def faceBox (n : ℕ) (τ : ℝ) : Set (Vec n) :=
  Set.pi univ (fun _ => Ioo (-τ / 2) (τ / 2))

theorem measurableSet_faceBox (n : ℕ) (τ : ℝ) : MeasurableSet (faceBox n τ) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

variable {n : ℕ}

theorem measurable_insertNth (i : Fin (n + 1)) :
    Measurable (fun p : ℝ × Vec n => i.insertNth (α := fun _ => ℝ) p.1 p.2) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable

/-- Radius read from an oriented coordinate face. -/
def faceRadius {d : ℕ} (i : Fin d) (pos : Bool) (x : Vec d) : ℝ :=
  if pos then 2 * x i else -2 * x i

/-- An open sector with a unique largest signed coordinate. -/
def faceSector {d : ℕ} (ρ R : ℝ) (i : Fin d) (pos : Bool) : Set (Vec d) :=
  {x | faceRadius i pos x ∈ Ioo ρ R ∧
    ∀ j, j ≠ i → x j ∈ Ioo (-faceRadius i pos x / 2) (faceRadius i pos x / 2)}

theorem measurable_faceRadius {d : ℕ} (i : Fin d) (pos : Bool) :
    Measurable (faceRadius i pos) := by
  unfold faceRadius
  cases pos <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem measurableSet_faceSector {d : ℕ} (ρ R : ℝ) (i : Fin d) (pos : Bool) :
    MeasurableSet (faceSector ρ R i pos) := by
  unfold faceSector
  apply MeasurableSet.inter
  · exact measurableSet_Ioo.preimage (measurable_faceRadius i pos)
  · change MeasurableSet {x | ∀ j, j ≠ i →
      x j ∈ Ioo (-faceRadius i pos x / 2) (faceRadius i pos x / 2)}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _hj
    exact (measurableSet_lt ((measurable_faceRadius i pos).neg.div_const 2)
      (measurable_pi_apply j)).inter
      (measurableSet_lt (measurable_pi_apply j) ((measurable_faceRadius i pos).div_const 2))

/-- Dilation of the radius has the Jacobian two used in cubical coarea. -/
theorem lintegral_half {f : ℝ → ℝ≥0∞} (hf : Measurable f) (pos : Bool) :
    (∫⁻ τ, f (if pos then τ / 2 else -τ / 2)) = 2 * ∫⁻ l, f l := by
  cases pos
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true]
  · have h := lintegral_map hf (measurable_const_mul (-(1 : ℝ) / 2)) (μ := volume)
    rw [Real.map_volume_mul_left (by norm_num), lintegral_smul_measure] at h
    norm_num at h
    convert h.symm using 1
    congr 1; funext τ; congr 1; ring
  · have h := lintegral_map hf (measurable_const_mul ((1 : ℝ) / 2)) (μ := volume)
    rw [Real.map_volume_mul_left (by norm_num), lintegral_smul_measure] at h
    norm_num at h
    convert h.symm using 1
    congr 1; funext τ; congr 1; ring

/-- The face measure `cubeFaceMeasure` is exactly a restricted parameter-volume pushforward. -/
theorem cubeFaceMeasure_eq_map (τ : ℝ) (i : Fin (n + 1)) (pos : Bool) :
    CoarseDeGiorgi.cubeFaceMeasure τ i pos =
      Measure.map (fun u : Vec n => i.insertNth (if pos then τ / 2 else -τ / 2) u)
        (volume.restrict (faceBox n τ)) := by
  classical
  let μ := CoarseDeGiorgi.faceCoordinateMeasures (d := n + 1) τ i pos
  have : ∀ j, SigmaFinite (μ j) := fun j => by
    dsimp [μ, CoarseDeGiorgi.faceCoordinateMeasures]
    split_ifs <;> infer_instance
  have hp := (measurePreserving_piFinSuccAbove μ i).symm.map_eq
  have hc : (fun j : Fin n => μ (i.succAbove j)) =
      fun _ => volume.restrict (Ioo (-τ / 2) (τ / 2)) := by
    funext j
    simp [μ, CoarseDeGiorgi.faceCoordinateMeasures]
  rw [hc] at hp
  have hi : μ i = Measure.dirac (if pos then τ / 2 else -τ / 2) := by
    simp [μ, CoarseDeGiorgi.faceCoordinateMeasures]
  rw [hi, Measure.dirac_prod, Measure.map_map] at hp
  · rw [CoarseDeGiorgi.cubeFaceMeasure, ← hp]
    congr 1
    change _ = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.pi univ (fun _ => Ioo (-τ / 2) (τ / 2)))
    rw [Measure.restrict_pi_pi]
  · exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable
  · exact measurable_prodMk_left

/-- Fubini on a single face, with the open-face convention retained. -/
theorem lintegral_cubeFaceMeasure (τ : ℝ) (i : Fin (n + 1)) (pos : Bool)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, g x ∂CoarseDeGiorgi.cubeFaceMeasure τ i pos) =
      ∫⁻ u in faceBox n τ, g (i.insertNth (if pos then τ / 2 else -τ / 2) u) := by
  rw [cubeFaceMeasure_eq_map, lintegral_map hg]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable.comp
    measurable_prodMk_left

theorem faceSector_insertNth_iff (ρ R l : ℝ) (u : Vec n) (i : Fin (n + 1))
    (pos : Bool) :
    i.insertNth (α := fun _ => ℝ) l u ∈ faceSector ρ R i pos ↔
      (if pos then 2 * l else -2 * l) ∈ Ioo ρ R ∧
        u ∈ faceBox n (if pos then 2 * l else -2 * l) := by
  classical
  simp only [faceSector, mem_ofPred_eq, faceRadius, Fin.insertNth_apply_same,
    faceBox, mem_pi, mem_univ, forall_const]
  constructor
  · rintro ⟨hr, hu⟩
    exact ⟨hr, fun j => by simpa using hu (i.succAbove j) (Fin.succAbove_ne i j)⟩
  · rintro ⟨hr, hu⟩
    refine ⟨hr, ?_⟩
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simpa using hu k

/-- Exact coarea on one largest-coordinate sector. -/
theorem cubical_coarea_face (ρ R : ℝ) (i : Fin (n + 1)) (pos : Bool)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ τ in Ioo ρ R, ∫⁻ x, g x ∂CoarseDeGiorgi.cubeFaceMeasure τ i pos) =
      2 * ∫⁻ x in faceSector ρ R i pos, g x := by
  let f := (faceSector ρ R i pos).indicator g
  have hf : Measurable f := hg.indicator (measurableSet_faceSector ρ R i pos)
  have hsplit : (∫⁻ x, f x) =
      ∫⁻ l, ∫⁻ u : Vec n, f (i.insertNth (α := fun _ => ℝ) l u) := by
    rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.lintegral_comp hf]
    change (∫⁻ p : ℝ × Vec n, f (i.insertNth (α := fun _ => ℝ) p.1 p.2)
      ∂(volume.prod volume)) = _
    exact lintegral_prod _ (hf.comp (measurable_insertNth i)).aemeasurable
  have hm : Measurable (fun l : ℝ => ∫⁻ u : Vec n, f (i.insertNth (α := fun _ => ℝ) l u)) :=
    (hf.comp (measurable_insertNth i)).lintegral_prod_right'
  rw [← lintegral_indicator (measurableSet_faceSector ρ R i pos) g, hsplit,
    ← lintegral_half hm pos]
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro τ
  by_cases hτ : τ ∈ Ioo ρ R
  · simp only [indicator_of_mem hτ]
    rw [lintegral_cubeFaceMeasure τ i pos hg, ← lintegral_indicator (measurableSet_faceBox n τ)]
    apply lintegral_congr
    intro u
    have he : (if pos then 2 * (if pos then τ / 2 else -τ / 2)
        else -2 * (if pos then τ / 2 else -τ / 2)) = τ := by cases pos <;> simp <;> ring
    have hm := faceSector_insertNth_iff ρ R (if pos then τ / 2 else -τ / 2) u i pos
    rw [he] at hm
    by_cases hu : u ∈ faceBox n τ <;> simp [f, hm, hτ, hu]
  · simp only [indicator_of_notMem hτ]
    symm
    rw [← lintegral_zero (μ := (volume : Measure (Vec n)))]
    apply lintegral_congr
    intro u
    have he : (if pos then 2 * (if pos then τ / 2 else -τ / 2)
        else -2 * (if pos then τ / 2 else -τ / 2)) = τ := by cases pos <;> simp <;> ring
    have hm := faceSector_insertNth_iff ρ R (if pos then τ / 2 else -τ / 2) u i pos
    rw [he] at hm
    simp [f, hm, hτ]

/-- Integration against a moving cube face is measurable in the radius. -/
theorem measurable_cubeFaceIntegral (i : Fin (n + 1)) (pos : Bool)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun τ : ℝ => ∫⁻ x, g x ∂CoarseDeGiorgi.cubeFaceMeasure τ i pos) := by
  simp_rw [lintegral_cubeFaceMeasure _ i pos hg, ← lintegral_indicator (measurableSet_faceBox n _)]
  apply Measurable.lintegral_prod_right (f := fun τ u =>
    (faceBox n τ).indicator (fun u => g (i.insertNth (if pos then τ / 2 else -τ / 2) u)) u)
  change Measurable ({p : ℝ × Vec n | p.2 ∈ faceBox n p.1}.indicator
    (fun p => g (i.insertNth (if pos then p.1 / 2 else -p.1 / 2) p.2)))
  apply Measurable.indicator
  · have hm : Measurable (fun p : ℝ × Vec n =>
        (if pos then p.1 / 2 else -p.1 / 2, p.2)) := by
      cases pos <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
    exact hg.comp ((measurable_insertNth i).comp hm)
  · simp only [faceBox, mem_pi, mem_univ, forall_const]
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_lt (f := fun p : ℝ × Vec n => -p.1 / 2)
      (g := fun p => p.2 j) (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : ℝ × Vec n => p.2 j)
        (g := fun p => p.1 / 2) (by fun_prop) (by fun_prop))

/-- Integration against the surface measure `surfaceMeasure τ` is measurable in the radius. -/
theorem measurable_surfaceIntegral {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun τ : ℝ => ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ) := by
  unfold CoarseDeGiorgi.surfaceMeasure
  simp_rw [lintegral_finsetSum_measure]
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
    (fun pos _ => measurable_cubeFaceIntegral i pos hg))


end

end CoarseDeGiorgi.Selection
