module

public import CoarseDeGiorgi.Endpoint.Rescaling.LocalCubes
public import CoarseDeGiorgi.Endpoint.Rescaling.ExponentialAbsorption
public import CoarseDeGiorgi.Statements.LocalBoundedness
public import CoarseDeGiorgi.Harnack.ContrastBound.RootHypotheses

/-! Rescaled Corollary B on the fixed remote cube of the endpoint argument. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint

open Rescaling

private theorem remoteCube_subset_unit (d : ℕ) : remoteCube d 1 ⊆ originCube 1 := by
  intro x hx i
  have hi := hx i
  change -(1 * (3 : ℝ) ^ (-3 : ℤ) / 2) < x i - remoteCenter d i ∧
    x i - remoteCenter d i < 1 * (3 : ℝ) ^ (-3 : ℤ) / 2 at hi
  dsimp only [remoteCenter] at hi
  split_ifs at hi <;> norm_num at hi <;> constructor <;> linarith only [hi.1, hi.2]

private theorem positivePart_norm_eq {d : ℕ} {u : Vec d → ℝ} {U : Set (Vec d)}
    (hu : ∀ᵐ x ∂(volume.restrict U), 0 ≤ u x) (η : ℝ≥0∞) :
    eLpNorm (positivePart u) η (volume.restrict U) = eLpNorm u η (volume.restrict U) := by
  apply eLpNorm_congr_ae
  filter_upwards [hu] with x hx
  exact max_eq_left hx

theorem remoteLocalBoundedness_holds (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) : RemoteLocalBoundedness d p q s t hp hq hs ht := by
  have : NeZero d := ⟨by omega⟩
  let η := harnackEtaParam q
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hη : 0 < η := by dsimp [η, harnackEtaParam, paramR]; positivity
  have hη2 : η < 2 := by
    dsimp [η, harnackEtaParam, paramR]
    have hq1 : 0 < q + 1 := by linarith only [hq]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4), div_lt_iff₀ hq1]
    nlinarith only [hq]
  obtain ⟨γ, _hγ, _, hB⟩ := local_boundedness d _hd p q s t hp hq hs ht _hθ
  obtain ⟨Cη, _hCη, hCηbound⟩ := hB η hη hη2
  let β : ℝ := (d - 1 : ℝ) / (2 * η * paramTheta d p q s t)
  have hβ : 0 ≤ β := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    exact div_nonneg (sub_nonneg.mpr hdR) (by positivity)
  let K := contrastCost d s t p q
  have hK : K ≠ ⊤ := contrastCost_ne_top d s t p q (zero_lt_one.trans hp) hq0
  let J := ENNReal.ofReal (((1 / 27 : ℝ) ^ d)⁻¹)
  let F := ENNReal.ofReal Cη * (ENNReal.ofReal (1 / 2)).rpow (-(2 * γ / η)) *
    K.rpow β * J.rpow (1 / η)
  have hF : F ≠ ⊤ := by
    dsimp only [F, J]
    simp only [ENNReal.rpow_eq_pow]
    finiteness
  obtain ⟨C, hC, hExp⟩ := absorb_polynomial F hF β hβ
  refine ⟨C, hC, ?_⟩
  intro a ha hU hL V Gv hn hu
  let z : Fin d → ℤ := fun i => if i.val = 0 then 34 else 0
  have hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39 := by intro i; dsimp [z]; split_ifs <;> norm_num
  have hy : remoteCenter d = latticeCenter z := by
    funext i
    dsimp [remoteCenter, latticeCenter, z]
    split_ifs <;> norm_num
  have hset (ρ : ℝ) : affineImage (latticeCenter z) (1 / 27) (originCube ρ) = remoteCube d ρ := by
    rw [affineImage_originCube, ← hy]
    rfl
  have hr : (0 : ℝ) < 1 / 27 := by norm_num
  have haV : IsWeightedCoeffOn (affineImage (latticeCenter z) (1 / 27) (originCube 1)) a := by
    rw [hset]
    exact LowerFractional.weightedCoeffOn_mono ha (remoteCube_subset_unit d)
  let hb := weightedCoeffOn_affine (latticeCenter z) hr haV
  have hd := momentData_affine z hz a ha hb hs ht hp.le hq.le hU hL
  have hsu := solution_affine (latticeCenter z) hr LowerFractional.lower_unitCube_domain
    (affineImage_domain _ hr LowerFractional.lower_unitCube_domain)
    (affineImage_nonempty _ _ LowerFractional.lower_unitCube_nonempty) haV
    ((hset 1).symm ▸ hu)
  have hsubsol : IsWeightedSubsolution (a ∘ affineMap (latticeCenter z) (1 / 27)) (originCube 1)
      (V ∘ affineMap (latticeCenter z) (1 / 27)) ((1 / 27 : ℝ) • (Gv ∘ affineMap (latticeCenter z) (1 / 27))) := by
    refine ⟨hsu.1, ?_⟩
    intro φ hφ hc hsφ _
    exact ⟨(hsu.2 φ hφ hc hsφ).1, (hsu.2 φ hφ hc hsφ).2.le⟩
  have hnon := nonnegative_affine (latticeCenter z) hr (originCube 1) V ((hset 1).symm ▸ hn)
  have hhalf : (originCube (d := d) (1 / 2)) ⊆ originCube 1 := by
    intro x hx i
    obtain ⟨hl, hh⟩ := hx i
    constructor <;> linarith only [hl, hh]
  have hnonhalf := ae_restrict_of_ae_restrict_of_subset hhalf hnon
  have he := (hCηbound _ hb hd.1 hd.2.1 _ _ hsubsol (1 / 2) 1
    (by norm_num) (by norm_num) le_rfl).1
  rw [positivePart_norm_eq hnonhalf, positivePart_norm_eq hnon] at he
  rw [eLpNorm_top_affine (latticeCenter z) hr, eLpNorm_affine (latticeCenter z) hr,
    ENNReal.toReal_ofReal hη.le, hset, hset] at he
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at he
  have hpow : (contrast (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s t p q hs ht hp.le hq.le).rpow β ≤
      K.rpow β * (contrast a ha s t p q hs ht hp.le hq.le).rpow β := by
    have h := ENNReal.rpow_le_rpow hd.2.2 hβ
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ] at h
    simpa only [ENNReal.rpow_eq_pow, K] using h
  have hco : contrast a ha s t p q hs ht hp.le hq.le ≠ ⊤ := (ENNReal.div_lt_top hU.ne hL.ne').ne
  have hcone := Harnack.ContrastBound.contrast_ge_one_of_root_hypotheses _hd a ha hp hq hs ht hU hL
  have habs := hExp _ hco hcone
  calc
    _ ≤ _ := he
    _ ≤ (F * (contrast a ha s t p q hs ht hp.le hq.le).rpow β) *
        eLpNorm V (ENNReal.ofReal η) (volume.restrict (remoteCube d 1)) := by
      calc
        _ ≤ (ENNReal.ofReal Cη * (ENNReal.ofReal (1 / 2)).rpow (-(2 * γ / η)) *
            (K.rpow β * (contrast a ha s t p q hs ht hp.le hq.le).rpow β)) *
            (J.rpow (1 / η) * eLpNorm V (ENNReal.ofReal η) (volume.restrict (remoteCube d 1))) :=
          mul_le_mul_left (mul_le_mul_right hpow _) _
        _ = _ := by dsimp only [F]; ac_rfl
    _ ≤ _ := mul_le_mul_left habs _

end CoarseDeGiorgi.Endpoint
