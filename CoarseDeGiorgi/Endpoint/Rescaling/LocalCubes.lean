module

public import CoarseDeGiorgi.Endpoint.Rescaling.MomentTransport
public import CoarseDeGiorgi.Endpoint.Rescaling.GridGeometry
public import CoarseDeGiorgi.Endpoint.Rescaling.AffineNorms
public import CoarseDeGiorgi.Statements.WeakHarnack
public import CoarseDeGiorgi.Statements.Harnack

/-! The two rescaled Harnack estimates, with constants uniform over the interior grid. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint

open Rescaling

theorem localWeakHarnackCubes_holds (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) : LocalWeakHarnackCubes d p q s t hp hq hs ht := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hweak⟩ := weak_harnack d _hd p q s t hp hq hs ht _hθ
  refine ⟨C * Real.sqrt (contrastCost d s t p q).toReal, mul_nonneg hC (Real.sqrt_nonneg _), ?_⟩
  intro a ha hU hL y hy hsub u G hn hu
  obtain ⟨z, rfl, hz⟩ := gridPoint_bounds y hy hsub
  have hr : (0 : ℝ) < 1 / 27 := by norm_num
  have haV : IsWeightedCoeffOn (affineImage (latticeCenter z) (1 / 27) (originCube 1)) a := by
    rw [affineImage_originCube]
    exact LowerFractional.weightedCoeffOn_mono ha hsub
  let hb := weightedCoeffOn_affine (latticeCenter z) hr haV
  have hd := momentData_affine z hz a ha hb hs ht hp.le hq.le hU hL
  have hsu := supersolution_affine (latticeCenter z) hr LowerFractional.lower_unitCube_domain
    (affineImage_domain _ hr LowerFractional.lower_unitCube_domain)
    (affineImage_nonempty _ _ LowerFractional.lower_unitCube_nonempty) haV
    ((affineImage_originCube _ 1).symm ▸ hu)
  have hnon := nonnegative_affine (latticeCenter z) hr (originCube 1) u
    ((affineImage_originCube _ 1).symm ▸ hn)
  have he := hweak _ hb hd.1 hd.2.1 _ _ hnon hsu
  rw [normalizedLpMoment_affine (latticeCenter z) hr,
    nonnegativeEssInf_affine (latticeCenter z) hr,
    affineImage_originCube, affineImage_originCube] at he
  have hroot := sqrt_contrast_affine_le z hz a ha hb hs ht hp.le hq.le hU hL
  have hcost := mul_le_mul_of_nonneg_left hroot hC
  have hexp : ENNReal.ofReal (Real.exp (C *
      Real.sqrt (contrast (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s t p q hs ht hp.le hq.le).toReal)) ≤
      ENNReal.ofReal (Real.exp ((C * Real.sqrt (contrastCost d s t p q).toReal) *
        Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcost.trans_eq (by ring)))
  exact he.trans (mul_le_mul_left hexp _)

theorem localHarnackCubes_holds (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) : LocalHarnackCubes d p q s t hp hq hs ht := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hhar⟩ := harnack d _hd p q s t hp hq hs ht _hθ
  refine ⟨C * Real.sqrt (contrastCost d s t p q).toReal, mul_nonneg hC (Real.sqrt_nonneg _), ?_⟩
  intro a ha hU hL y hy hsub u G hn hu
  obtain ⟨z, rfl, hz⟩ := gridPoint_bounds y hy hsub
  have hr : (0 : ℝ) < 1 / 27 := by norm_num
  have haV : IsWeightedCoeffOn (affineImage (latticeCenter z) (1 / 27) (originCube 1)) a := by
    rw [affineImage_originCube]
    exact LowerFractional.weightedCoeffOn_mono ha hsub
  let hb := weightedCoeffOn_affine (latticeCenter z) hr haV
  have hd := momentData_affine z hz a ha hb hs ht hp.le hq.le hU hL
  have hsu := solution_affine (latticeCenter z) hr LowerFractional.lower_unitCube_domain
    (affineImage_domain _ hr LowerFractional.lower_unitCube_domain)
    (affineImage_nonempty _ _ LowerFractional.lower_unitCube_nonempty) haV
    ((affineImage_originCube _ 1).symm ▸ hu)
  have hnon := nonnegative_affine (latticeCenter z) hr (originCube 1) u
    ((affineImage_originCube _ 1).symm ▸ hn)
  have he := hhar _ hb hd.1 hd.2.1 _ _ hnon hsu
  rw [eLpNorm_top_affine (latticeCenter z) hr,
    nonnegativeEssInf_affine (latticeCenter z) hr,
    affineImage_originCube] at he
  have hroot := sqrt_contrast_affine_le z hz a ha hb hs ht hp.le hq.le hU hL
  have hcost := mul_le_mul_of_nonneg_left hroot hC
  have hexp : ENNReal.ofReal (Real.exp (C *
      Real.sqrt (contrast (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s t p q hs ht hp.le hq.le).toReal)) ≤
      ENNReal.ofReal (Real.exp ((C * Real.sqrt (contrastCost d s t p q).toReal) *
        Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcost.trans_eq (by ring)))
  exact he.trans (mul_le_mul_left hexp _)

end CoarseDeGiorgi.Endpoint
