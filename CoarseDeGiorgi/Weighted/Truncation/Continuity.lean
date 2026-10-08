
import CoarseDeGiorgi.Weighted.Truncation.Truncate

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Positive-part gradient continuity, with locality removing the exceptional level. -/
theorem tendsto_energy_positivePart (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    (hf : ∀ n, CoarseDeGiorgi.MemH1a a V (f n) (F n))
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : CoarseDeGiorgi.MemH1a a V u G)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n => weightedEnergy a V
      ({x | c < f n x}.indicator (F n) - {x | c < u x}.indicator G)) atTop (𝓝 0) := by
  let χ : (Vec d → ℝ) → Vec d → ℝ := fun v x => if c < v x then 1 else 0
  have hχ {v : Vec d → ℝ} (hv : AEStronglyMeasurable v (volume.restrict V)) :
      AEStronglyMeasurable (χ v) (volume.restrict V) :=
    aestronglyMeasurable_const.indicator₀
      (nullMeasurableSet_lt measurable_const.aemeasurable hv.aemeasurable)
  have hχG (v : Vec d → ℝ) (H : Vec d → Vec d) :
      (fun x => χ v x • H x) = {x | c < v x}.indicator H := by
    funext x
    by_cases hx : c < v x <;> simp [χ, hx]
  have hfirst := tendsto_energy_bounded_mul ha (F := fun n => F n - G)
    (b := fun n => χ (f n)) (M := 1)
    (fun n => Eventually.of_forall fun x => by dsimp [χ]; split_ifs <;> norm_num) hE
  have hzero := MemH1a.gradient_zero_on_level hV hne ha hu c
  have hs := hu.1.nullMeasurableSet_eq_fun (aestronglyMeasurable_const (b := c))
  have hsecond : Tendsto (fun n => weightedEnergy a V
      (fun x => (χ (f n) x - χ u x) • G x)) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (ht.comp hns)).exists_seq_tendsto_ae
    let b : ℕ → Vec d → ℝ := fun n => {x | u x = c}ᶜ.indicator
      (fun x => χ (f (ns (ms n))) x - χ u x)
    have hbM (n : ℕ) : AEStronglyMeasurable (b n) (volume.restrict V) :=
      ((hχ (hf (ns (ms n))).1).sub (hχ hu.1)).indicator₀ hs.compl
    have hbnd (n : ℕ) : ∀ᵐ x ∂volume.restrict V, |b n x| ≤ 2 := by
      filter_upwards with x
      simp only [b, Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, χ]
      split_ifs <;> norm_num
    have hbL : ∀ᵐ x ∂volume.restrict V, Tendsto (fun n => b n x) atTop (𝓝 0) := by
      filter_upwards [hae] with x hx
      by_cases heq : u x = c
      · simp [b, heq]
      · rcases lt_or_gt_of_ne heq with hlo | hhi
        · have hev := (tendsto_order.mp hx).2 c hlo
          have he : (fun n => b n x) =ᶠ[atTop] (fun _ => 0) := by
            filter_upwards [hev] with n hn
            simp [b, χ, heq, not_lt_of_ge hlo.le, not_lt_of_ge hn.le]
          exact (tendsto_congr' he).mpr tendsto_const_nhds
        · have hev := (tendsto_order.mp hx).1 c hhi
          have he : (fun n => b n x) =ᶠ[atTop] (fun _ => 0) := by
            filter_upwards [hev] with n hn
            simp [b, χ, heq, hhi, hn]
          exact (tendsto_congr' he).mpr tendsto_const_nhds

    have hlim := tendsto_energy_mul_zero ha hu.2.1
      (MemH1a.energy_lt_top hV.isOpen ha hu) hbM hbnd hbL
    refine ⟨ms, ?_⟩
    convert hlim using 1
    funext n
    apply energy_congr_ae
    filter_upwards [hzero] with x hx
    by_cases heq : u x = c
    · have hz : G x = 0 := by simpa [heq] using hx
      simp [b, heq, hz]
    · simp [b, heq]
  have hsum := tendsto_energy_add_zero ha
    (fun n => (hχ (hf n).1).smul ((hf n).2.1.sub hu.2.1)) hfirst hsecond
  convert hsum using 1
  funext n
  rw [← hχG (f n) (F n), ← hχG u G]
  congr 1
  funext x i
  change χ (f n) x * F n x i - χ u x * G x i =
    χ (f n) x * (F n x i - G x i) + (χ (f n) x - χ u x) * G x i
  ring



end CoarseDeGiorgi.Weighted
