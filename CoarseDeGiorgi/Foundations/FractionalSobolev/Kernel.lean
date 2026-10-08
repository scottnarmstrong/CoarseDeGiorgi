import CoarseDeGiorgi.Foundations.FractionalSobolev.Levels
import CoarseDeGiorgi.Foundations.FractionalSobolev.SetEstimate

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

lemma euclidDist_continuous {n : ℕ} : Continuous (fun xy : Vec n × Vec n => euclidDist xy.1 xy.2) := by
  unfold euclidDist vecNormSq vecDot
  fun_prop

lemma fracKernel_measurable {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f) (s p : ℝ) :
    Measurable (fracKernel s p f) := by
  unfold fracKernel fracKernelWithDimension
  apply Measurable.ennreal_ofReal
  apply Measurable.div
  · exact ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).norm.pow_const _
  · exact euclidDist_continuous.measurable.pow_const _

lemma euclidDist_symm {n : ℕ} (x y : Vec n) : euclidDist x y = euclidDist y x := by
  unfold euclidDist vecNormSq vecDot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

lemma fracKernel_symm {n : ℕ} (f : Vec n → ℝ) (s p : ℝ) (xy : Vec n × Vec n) :
    fracKernel s p f xy.swap = fracKernel s p f xy := by
  unfold fracKernel fracKernelWithDimension
  change ENNReal.ofReal (|f xy.2 - f xy.1| ^ p / euclidDist xy.2 xy.1 ^ _) = _
  rw [abs_sub_comm, euclidDist_symm]

/-- The repaired selected rectangle uses the full lower complement. -/
def selectedPairs {X : Type*} (f : X → ℝ) (i : ℤ) : Set (X × X) :=
  dyadicBand f i ×ˢ (dyadicLevel f (i - 1))ᶜ

lemma selectedPairs_measurable {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f) (i : ℤ) :
    MeasurableSet (selectedPairs f i) :=
  (dyadicBand_measurable hf i).prod (dyadicLevel_measurable hf (i - 1)).compl

lemma selectedPairs_disjoint {X : Type*} (f : X → ℝ) :
    Pairwise (fun i j => Disjoint (selectedPairs f i) (selectedPairs f j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro xy hi hj
  exact Set.disjoint_left.mp (dyadicBand_disjoint f hij) hi.1 hj.1

lemma selectedPairs_ordered {X : Type*} {f : X → ℝ} {i : ℤ} {xy : X × X}
    (hxy : xy ∈ selectedPairs f i) : |f xy.2| < |f xy.1| := by
  have hy : |f xy.2| ≤ dyadicHeight (i - 1) := le_of_not_gt hxy.2
  exact (hy.trans (dyadicHeight_mono (by omega))).trans_lt (mem_dyadicBand.mp hxy.1).1

/-- Disjointness in the first coordinate and symmetry retain the factor two. -/
lemma selectedPairs_energy {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f) (s p : ℝ) :
    2 * (∑' i : ℤ, ∫⁻ xy in selectedPairs f i, fracKernel s p f xy ∂(volume.prod volume)) ≤
      ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) := by
  let U := ⋃ i : ℤ, selectedPairs f i
  have hU : MeasurableSet U := MeasurableSet.iUnion (selectedPairs_measurable hf)
  have hswap : (∫⁻ xy in Prod.swap ⁻¹' U, fracKernel s p f xy ∂(volume.prod volume)) =
      ∫⁻ xy in U, fracKernel s p f xy ∂(volume.prod volume) := by
    rw [← lintegral_indicator (hU.preimage measurable_swap), ← lintegral_indicator hU]
    have heq : (fun xy : Vec n × Vec n => U.indicator (fracKernel s p f) xy.swap) =
        (Prod.swap ⁻¹' U).indicator (fracKernel s p f) := by
      funext xy
      by_cases hx : xy.swap ∈ U
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show xy ∈ Prod.swap ⁻¹' U from hx), fracKernel_symm]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show xy ∉ Prod.swap ⁻¹' U from hx)]
    rw [← heq]
    exact lintegral_prod_swap _
  have hdisj : Disjoint U (Prod.swap ⁻¹' U) := by
    apply Set.disjoint_left.mpr
    intro xy hx hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact (selectedPairs_ordered hi).asymm (selectedPairs_ordered hj)
  have hbound := lintegral_mono_set (μ := volume.prod volume)
    (f := fracKernel s p f) (Set.subset_univ (U ∪ Prod.swap ⁻¹' U))
  rw [lintegral_union (hU.preimage measurable_swap) hdisj, hswap,
    Measure.restrict_univ] at hbound
  rw [two_mul, ← lintegral_iUnion (selectedPairs_measurable hf) (selectedPairs_disjoint f)]
  exact hbound

lemma selectedPairs_gap {X : Type*} {f : X → ℝ} {i : ℤ} {x y : X}
    (hx : x ∈ dyadicBand f i) (hy : y ∈ (dyadicLevel f (i - 1))ᶜ) :
    dyadicHeight (i - 1) ≤ |f x - f y| := by
  have hx' := (mem_dyadicBand.mp hx).1
  have hy' : |f y| ≤ dyadicHeight (i - 1) := le_of_not_gt hy
  have hh : dyadicHeight i = 2 * dyadicHeight (i - 1) := by
    simpa only [sub_add_cancel] using dyadicHeight_add_one (i - 1)
  have hab := abs_sub_abs_le_abs_sub (f x) (f y)
  linarith

lemma dyadicHeight_rpow (p : ℝ) (k : ℤ) :
    ENNReal.ofReal (dyadicHeight k ^ p) = sequenceWeight ((2 : ℝ) ^ p) k := by
  unfold dyadicHeight sequenceWeight
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]

/-- DNPV Lemma 6.1 applied to the full complement, retaining pairs in the zero set. -/
lemma selectedPairs_lower {n : ℕ} (hn : 0 < n) {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    {f : Vec n → ℝ} (hf : Measurable f) (hcompact : HasCompactSupport f) (i : ℤ) :
    ENNReal.ofReal (setEstimateConstant n (s * p)) *
      sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
      (volume (dyadicLevel f (i - 1))) ^ (-(s * p) / n) * volume (dyadicBand f i) ≤
      ∫⁻ xy in selectedPairs f i, fracKernel s p f xy ∂(volume.prod volume) := by
  obtain ⟨M, hM, hbound⟩ := dyadicLevel_measure_bound hcompact
  have hfin : volume (dyadicLevel f (i - 1)) < ⊤ :=
    lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hM (hbound _))
  rw [selectedPairs, setLIntegral_prod _ (fracKernel_measurable hf s p).aemeasurable.restrict]
  have hxbound : ∀ x ∈ dyadicBand f i,
      ENNReal.ofReal (setEstimateConstant n (s * p)) *
        sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
        (volume (dyadicLevel f (i - 1))) ^ (-(s * p) / n) ≤
      ∫⁻ y in (dyadicLevel f (i - 1))ᶜ, fracKernel s p f (x, y) := by
    intro x hx
    have hg := set_estimate hn hs hp (dyadicLevel_measurable hf (i - 1)) hfin x
    calc
      _ = sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
          (ENNReal.ofReal (setEstimateConstant n (s * p)) *
            (volume (dyadicLevel f (i - 1))) ^ (-(s * p) / n)) := by ac_rfl
      _ ≤ sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
          ∫⁻ y in (dyadicLevel f (i - 1))ᶜ,
            ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + s * p)) := mul_le_mul' le_rfl hg
      _ = ∫⁻ y in (dyadicLevel f (i - 1))ᶜ,
          sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
            ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + s * p)) :=
        (lintegral_const_mul' _ _ (sequenceWeight_ne_top _ _)).symm
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (dyadicLevel_measurable hf (i - 1)).compl] with y hy
        rw [← dyadicHeight_rpow p (i - 1), ← ENNReal.ofReal_mul
          (Real.rpow_nonneg (dyadicHeight_pos _).le _)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_one_div]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (euclidDist_nonneg _ _) _)
        exact Real.rpow_le_rpow (dyadicHeight_pos _).le (selectedPairs_gap hx hy) hp.le
  calc
    _ = ∫⁻ x in dyadicBand f i,
        ENNReal.ofReal (setEstimateConstant n (s * p)) *
          sequenceWeight ((2 : ℝ) ^ p) (i - 1) *
          (volume (dyadicLevel f (i - 1))) ^ (-(s * p) / n) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (dyadicBand_measurable hf i)] with x hx
      exact hxbound x hx

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
