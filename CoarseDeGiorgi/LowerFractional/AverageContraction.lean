module

public import CoarseDeGiorgi.LowerFractional.CellHolder
public import Mathlib.Analysis.Convex.Jensen

/-! Jensen contraction from a finite simplex tiling to its cube average. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

lemma lower_finite_euclid_jensen {d : ℕ} {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (v : ι → Vec d) (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1)
    {r : ℝ} (hr : 1 ≤ r) :
    euclidNorm (∑ i ∈ s, p i • v i) ^ r ≤ ∑ i ∈ s, p i * euclidNorm (v i) ^ r := by
  have hc : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) (fun x => ‖x‖ ^ r) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hn := (convexOn_norm (E := EuclideanSpace ℝ (Fin d)) convex_univ).2 hx hy ha hb hab
    have hh := (convexOn_rpow hr).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
    exact (Real.rpow_le_rpow (norm_nonneg _) hn (zero_le_one.trans hr)).trans hh
  have hj := hc.map_sum_le hp hp1 (fun i _ => Set.mem_univ (WithLp.toLp 2 (v i)))
  simpa only [show ∀ v : Vec d, euclidNorm v = ‖WithLp.toLp 2 v‖ from
    Foundations.Euclid.eNorm2_eq_norm_toLp, WithLp.toLp_sum, WithLp.toLp_smul,
    smul_eq_mul] using hj

lemma lower_averageVec_tiling {d : ℕ} {ι : Type*} (s : Finset ι) (cell : ι → Set (Vec d))
    {D : Set (Vec d)} {G : Vec d → Vec d} (hG : IntegrableOn G D)
    (hcell : ∀ i ∈ s, MeasurableSet (cell i)) (hsub : ∀ i ∈ s, cell i ⊆ D)
    (hvol : ∀ i ∈ s, (volume (cell i)).toReal ≠ 0)
    (hdisj : (s : Set ι).PairwiseDisjoint cell) (hcover : (⋃ i ∈ s, cell i) =ᵐ[volume] D) :
    volumeAverageVec D G = ∑ i ∈ s, ((volume (cell i)).toReal / (volume D).toReal) •
      volumeAverageVec (cell i) G := by
  funext j
  have hs : (∫ x in D, G x j) = ∑ i ∈ s, ∫ x in cell i, G x j := by
    rw [← setIntegral_congr_set hcover]
    exact integral_biUnion_finset s hcell hdisj (fun i hi =>
      (show IntegrableOn (fun x => G x j) D volume from hG.eval j).mono_set (hsub i hi))
  simp only [volumeAverageVec, volumeAverage, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hvol i hi]

/-- Real volume-weighted Jensen inequality for an actual simplex tiling. -/
lemma lower_simplex_tiling_mean_rpow {d : ℕ} (k : ℕ) (s : Finset (Aliases.SimplexIndex d k))
    {D : Set (Vec d)} {G : Vec d → Vec d} (hG : IntegrableOn G D)
    (hD0 : volume D ≠ 0) (hDtop : volume D ≠ ⊤)
    (hsub : ∀ η ∈ s, Aliases.simplexCell k η ⊆ D)
    (hdisj : (s : Set (Aliases.SimplexIndex d k)).PairwiseDisjoint (Aliases.simplexCell k))
    (hcover : (⋃ η ∈ s, Aliases.simplexCell k η) =ᵐ[volume] D)
    {r : ℝ} (hr : 1 ≤ r) :
    (volume D).toReal * euclidNorm (volumeAverageVec D G) ^ r ≤
      ∑ η ∈ s, (volume (Aliases.simplexCell k η)).toReal *
        euclidNorm (volumeAverageVec (Aliases.simplexCell k η) G) ^ r := by
  have hv : 0 < (volume D).toReal := ENNReal.toReal_pos hD0 hDtop
  have hc (η : Aliases.SimplexIndex d k) : MeasurableSet (Aliases.simplexCell k η) :=
    (Aliases.simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet
  have hctop (η : Aliases.SimplexIndex d k) : volume (Aliases.simplexCell k η) ≠ ⊤ :=
    (Aliases.simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hc0 (η : Aliases.SimplexIndex d k) : (volume (Aliases.simplexCell k η)).toReal ≠ 0 :=
    (ENNReal.toReal_pos ((Aliases.simplexCell_isOpenBoundedConvexDomain k η).isOpen.measure_pos
      volume (Aliases.simplexCell_nonempty k η)).ne' (hctop η)).ne'
  have hsvol : (∑ η ∈ s, (volume (Aliases.simplexCell k η)).toReal) = (volume D).toReal := by
    rw [← ENNReal.toReal_sum (fun η _ => hctop η), ← measure_biUnion_finset hdisj
      (fun η _ => hc η), measure_congr hcover]
  let p : Aliases.SimplexIndex d k → ℝ := fun η =>
    (volume (Aliases.simplexCell k η)).toReal / (volume D).toReal
  have hp1 : ∑ η ∈ s, p η = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div, hsvol, div_self hv.ne']
  rw [lower_averageVec_tiling s (Aliases.simplexCell k) hG (fun η _ => hc η) hsub
    (fun η _ => hc0 η) hdisj hcover]
  have hj := lower_finite_euclid_jensen s p (fun η => volumeAverageVec (Aliases.simplexCell k η) G)
    (fun η _ => div_nonneg ENNReal.toReal_nonneg hv.le) hp1 hr
  have hm := mul_le_mul_of_nonneg_left hj hv.le
  refine hm.trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  dsimp only [p]
  field_simp [hv.ne']


end CoarseDeGiorgi.LowerFractional
