module

public import CoarseDeGiorgi.Foundations.Reconstruction.AuxProjection
public import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicReflection

/-! # Reflected averages: exact volume factors and strong L¹ convergence -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section

variable {d : ℕ}

/-- The vector whose coordinates are the reflected weak partial derivatives. -/
def reflectedGradient (m : ℤ) (z : Fin d → ℤ) (f : Vec d → Vec d) (x : Vec d) : Vec d :=
  fun i => reflectedPartial m z f i x

/-- Reflection of the exact auxiliary average field at relative depth `j`. -/
def reflectedAverage (m : ℤ) (j : ℕ) (z : Fin d → ℤ) (f : Vec d → Vec d) : Vec d → Vec d :=
  reflectedGradient m z (auxAverage m (m + j) z f)

theorem norm_signLinear (s : Fin d → Bool) (v : Vec d) : ‖signLinear s v‖ = ‖v‖ := by
  have hle (w : Vec d) : ‖signLinear s w‖ ≤ ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro i
    rw [signLinear_apply, norm_mul]
    have hs : ‖reflectionSign (s i)‖ = 1 := by cases h : s i <;> norm_num [reflectionSign, h]
    rw [hs, one_mul]
    exact norm_le_pi_norm w i
  have hinv (x : Vec d) : signLinear s (signLinear s x) = x := signLinear_involutive s x
  exact le_antisymm (hle v) (by simpa only [hinv] using hle (signLinear s v))

theorem reflectedGradient_eq_signLinear (m : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (x : Vec d) :
    reflectedGradient m z f x = signLinear (fun i => decide (0 < x i))
      (f (auxLower m z + fun i => |x i|)) := rfl

theorem euclidNorm_reflectedGradient (m : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (x : Vec d) :
    euclidNorm (reflectedGradient m z f x) =
      reflectedScalar m z (fun y => euclidNorm (f y)) x := by
  rw [reflectedGradient_eq_signLinear, euclidNorm_signLinear]
  rfl

theorem reflectedGradient_sub (m : ℤ) (z : Fin d → ℤ)
    (f g : Vec d → Vec d) (x : Vec d) :
    reflectedGradient m z f x - reflectedGradient m z g x =
      reflectedGradient m z (fun y => f y - g y) x := by
  simp only [reflectedGradient_eq_signLinear, map_sub]

/-- Even reflection multiplies ordinary integrals by the number of orthants. -/
theorem integral_reflectedScalar {m : ℤ} {z : Fin d → ℤ} {w : Vec d → ℝ}
    (hw : IntegrableOn w (auxCube m z) volume) :
    ∫ x in reflectionBox m, reflectedScalar m z w x ∂volume =
      (2 : ℝ) ^ d * ∫ x in auxCube m z, w x ∂volume := by
  rw [setIntegral_reflectionBox_eq_sum m _
    ((integrableOn_reflectionBox_iff m _).mp (integrableOn_reflectedScalar hw))]
  have hcell (s : Fin d → Bool) :
      ∫ x in reflectionPositiveBox m, reflectedScalar m z w (signLinear s x) ∂volume =
        ∫ x in auxCube m z, w x ∂volume := by
    rw [setIntegral_congr_fun (isOpen_reflectionPositiveBox m).measurableSet
      (fun _ hx => reflectedScalar_signLinear m z w s hx)]
    exact (measurePreserving_auxLower_add m z).integral_comp
      (Homeomorph.addLeft (auxLower m z)).measurableEmbedding w
  simp only [hcell, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- The same exact reflection factor holds for nonnegative integrals, without
measurability of the original representative. -/
theorem lintegral_reflectedScalar (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ≥0∞) :
    ∫⁻ x in reflectionBox m, w (auxLower m z + fun i => |x i|) ∂volume =
      (2 : ℝ≥0∞) ^ d * ∫⁻ x in auxCube m z, w x ∂volume := by
  rw [setLIntegral_congr (reflectionBox_ae_eq_iUnion_orthant m),
    lintegral_iUnion (measurableSet_reflectionOrthant m) (pairwise_disjoint_reflectionOrthant m)]
  rw [tsum_fintype]
  have hcell (s : Fin d → Bool) :
      ∫⁻ x in reflectionOrthant m s, w (auxLower m z + fun i => |x i|) ∂volume =
        ∫⁻ x in auxCube m z, w x ∂volume := by
    have hs : (∫⁻ x in reflectionOrthant m s, w (auxLower m z + fun i => |x i|) ∂volume) =
        ∫⁻ x in reflectionPositiveBox m, w (auxLower m z + fun i => |signLinear s x i|) ∂volume := by
      have hinv (x : Vec d) : signLinear s (signLinear s x) = x := signLinear_involutive s x
      simpa only [hinv] using
        (measurePreserving_signLinear_restrict m s).lintegral_comp_emb
          (signHomeomorph s).measurableEmbedding
          (fun x => w (auxLower m z + fun i => |signLinear s x i|))
    rw [hs]
    rw [setLIntegral_congr_fun (isOpen_reflectionPositiveBox m).measurableSet
      (fun _ hx => by rw [abs_signLinear_of_mem_positive m s hx])]
    exact (measurePreserving_auxLower_add m z).lintegral_comp_emb
      (Homeomorph.addLeft (auxLower m z)).measurableEmbedding w
  simp only [hcell, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Reflection preserves the vector L¹ error up to exactly `2^d`. -/
theorem integral_norm_reflectedGradient_sub (m : ℤ) (z : Fin d → ℤ)
    (f g : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (hg : IntegrableOn g (auxCube m z) volume) :
    ∫ x in reflectionBox m, ‖reflectedGradient m z f x - reflectedGradient m z g x‖ ∂volume =
      (2 : ℝ) ^ d * ∫ x in auxCube m z, ‖f x - g x‖ ∂volume := by
  have heq : (fun x => ‖reflectedGradient m z f x - reflectedGradient m z g x‖) =
      reflectedScalar m z (fun y => ‖f y - g y‖) := by
    funext x
    rw [reflectedGradient_sub, reflectedGradient_eq_signLinear, norm_signLinear]
    rfl
  rw [heq]
  exact integral_reflectedScalar (hf.sub hg).norm

theorem tendsto_integral_norm_reflectedAverage_sub (m : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume) :
    Tendsto (fun j : ℕ => ∫ x in reflectionBox m,
      ‖reflectedAverage m j z f x - reflectedGradient m z f x‖ ∂volume) atTop (𝓝 0) := by
  have hlim := (tendsto_integral_norm_auxAverage_sub m z f hf).const_mul ((2 : ℝ) ^ d)
  have heq (j : ℕ) := integral_norm_reflectedGradient_sub m z (auxAverage m (m + j) z f) f
    (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + j) z f 1)) hf
  simpa only [reflectedAverage, ← heq, mul_zero] using hlim

/-- The exact Euclidean Lʳ norm factor for reflected gradient averages. -/
theorem eLpNorm_euclidNorm_reflectedAverage (m : ℤ) (j : ℕ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun x => euclidNorm (reflectedAverage m j z f x)) p
      (volume.restrict (reflectionBox m)) =
      ((2 : ℝ≥0∞) ^ d) ^ (1 / p.toReal) *
        eLpNorm (fun x => euclidNorm (auxAverage m (m + j) z f x)) p
          (volume.restrict (auxCube m z)) := by
  let a := auxAverage m (m + j) z f
  have hmem := memLp_euclidNorm_auxAverage m (m + j) z f p
  have hi := memLp_one_iff_integrable.mp (memLp_euclidNorm_auxAverage m (m + j) z f 1)
  have hr : AEStronglyMeasurable (fun x => euclidNorm (reflectedAverage m j z f x))
      (volume.restrict (reflectionBox m)) := by
    have heq : (fun x => euclidNorm (reflectedAverage m j z f x)) =
        reflectedScalar m z (fun y => euclidNorm (a y)) := by
      funext x
      exact euclidNorm_reflectedGradient m z a x
    rw [heq]
    exact (integrableOn_reflectedScalar hi).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hmem.aestronglyMeasurable]
  simp only [reflectedAverage, euclidNorm_reflectedGradient, reflectedScalar]
  rw [lintegral_reflectedScalar m z (fun y => ‖euclidNorm (a y)‖ₑ ^ p.toReal)]
  exact ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

end

end CoarseDeGiorgi.Foundations.Reconstruction
