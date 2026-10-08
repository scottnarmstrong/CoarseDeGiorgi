import CoarseDeGiorgi.Cubical.Counting
import CoarseDeGiorgi.Cubical.EnnrealSum

/-! # The second inequality of Lemma `l.cubical.simplicial.moments`: simplices are controlled by cubes -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

namespace RespData

variable (D : RespData d)

/-- Mean over `𝒯_k` of `|R(△)|^p`. -/
noncomputable def simplexAvg (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (p : ℝ) : ℝ :=
  ((triangulation (d := d) k).attach.sum fun η => Real.rpow ‖D.simplex a ha k η‖ p) /
    ((triangulation (d := d) k).card : ℝ)

/-- Mean over `𝒬_k` of `|R(Q)|^p`. -/
noncomputable def cubeAvg (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (p : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖D.cube a ha k j‖ p) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

theorem second (hd : 1 ≤ d) (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p : ℝ} (hp : 1 ≤ p) (k : ℕ) :
    (ENNReal.ofReal (D.simplexAvg a ha k p)).rpow (1 / p) ≤
      ENNReal.ofReal (10 * d * (d + 1)) *
        ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
          (ENNReal.ofReal (D.cubeAvg a ha (k + l) p)).rpow (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  set C₀ : ℝ := 10 * d * (d + 1) with hC₀
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hC₁ : 1 ≤ C₀ := by rw [hC₀]; nlinarith
  have hcard : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) := by
    rw [triangulation_card]; positivity
  have hfac : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  set γ : ℕ → ℝ := fun l => (Nat.factorial d : ℝ) * (((3 : ℝ) ^ l)⁻¹) ^ d with hγ
  have hvolS : ∀ η : SimplexIndex d k, 0 < (volume (simplexCell k η)).toReal := fun η => by
    rw [volume_simplexCell_toReal]; positivity
  have hX : ∀ η : SimplexIndex d k, ENNReal.ofReal ‖D.simplex a ha k η‖ ≤
      ∑' l, ∑ z ∈ Wl (simplexCell k η) k l,
        ENNReal.ofReal (γ l) * ENNReal.ofReal ‖D.cube a ha (k + l) z‖ := fun η => by
    have := simplex_whitney_bound D a ha k η
    simpa only [volume_ratio] using this
  have hsumγ : ∀ (l : ℕ) (η : SimplexIndex d k),
      ∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) ≤ ENNReal.ofReal (C₀ * ((3 : ℝ) ^ l)⁻¹) := by
    intro l η
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := simplex_layer_weight hd k l η
    have h2 : ∑ z ∈ Wl (simplexCell k η) k l, γ l =
        (∑ z ∈ Wl (simplexCell k η) k l, (volume (cubeCell (k + l) z)).toReal) /
          (volume (simplexCell k η)).toReal := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [volume_ratio]
    rw [h2, div_le_iff₀ (hvolS η)]
    exact h1
  have hA : ∀ (l : ℕ) (η : SimplexIndex d k),
      (∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) * ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p ≤
        (ENNReal.ofReal (C₀ * ((3 : ℝ) ^ l)⁻¹)) ^ (p - 1) *
          ∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) * (ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p := by
    intro l η
    refine (holder_weighted (Wl (simplexCell k η) k l) (fun _ => ENNReal.ofReal (γ l))
      (fun z => ENNReal.ofReal ‖D.cube a ha (k + l) z‖) hp).trans ?_
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hsumγ l η) (by linarith)) le_rfl
  have hB : ∀ l : ℕ, ∑ η ∈ (triangulation (d := d) k).attach,
      ∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) * (ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p ≤
        ENNReal.ofReal ((triangulation (d := d) k).card) * ENNReal.ofReal (D.cubeAvg a ha (k + l) p) := by
    intro l
    refine (sum_Wl_le k l (fun z => ENNReal.ofReal (γ l) * (ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p)).trans ?_
    rw [← Finset.mul_sum, ← ENNReal.ofReal_mul (by positivity)]
    have hM : ((Finset.univ : Finset (Fin d → Fin (3 ^ (k + l)))).card : ℝ) =
        ((3 : ℝ) ^ (k + l)) ^ d := by
      simp [Finset.card_univ]
    have hMpos : (0 : ℝ) < ((3 : ℝ) ^ (k + l)) ^ d := by positivity
    have hid : ((triangulation (d := d) k).card : ℝ) / ((3 : ℝ) ^ (k + l)) ^ d = γ l := by
      rw [triangulation_card]
      push_cast
      simp only [hγ, pow_add, mul_pow, inv_pow, ← pow_mul]
      field_simp
    have hsumr : ∑ z : Fin d → Fin (3 ^ (k + l)), (ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p =
        ENNReal.ofReal (∑ z : Fin d → Fin (3 ^ (k + l)), Real.rpow ‖D.cube a ha (k + l) z‖ p) := by
      change _ = ENNReal.ofReal (∑ z : Fin d → Fin (3 ^ (k + l)), ‖D.cube a ha (k + l) z‖ ^ p)
      rw [ENNReal.ofReal_sum_of_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    rw [hsumr, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq; congr 1
    unfold cubeAvg
    rw [hM, ← hid]; ring
  have key := moment_assembly (τ := SimplexIndex d k) (triangulation (d := d) k).attach hp
    (N := ENNReal.ofReal ((triangulation (d := d) k).card))
    (fun η => ENNReal.ofReal ‖D.simplex a ha k η‖)
    (fun l η => ∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) * ENNReal.ofReal ‖D.cube a ha (k + l) z‖)
    (fun l η => ∑ z ∈ Wl (simplexCell k η) k l, ENNReal.ofReal (γ l) * (ENNReal.ofReal ‖D.cube a ha (k + l) z‖) ^ p)
    (fun l => ENNReal.ofReal (C₀ * ((3 : ℝ) ^ l)⁻¹))
    (fun l => ENNReal.ofReal (D.cubeAvg a ha (k + l) p)) hX hA hB
    (ENNReal.ofReal_pos.mpr hcard).ne' ENNReal.ofReal_ne_top
  have hlhs : ENNReal.ofReal (D.simplexAvg a ha k p) =
      (∑ η ∈ (triangulation (d := d) k).attach, (ENNReal.ofReal ‖D.simplex a ha k η‖) ^ p) /
        ENNReal.ofReal ((triangulation (d := d) k).card) := by
    unfold simplexAvg
    rw [ENNReal.ofReal_div_of_pos hcard]
    change ENNReal.ofReal ((triangulation (d := d) k).attach.sum fun η => ‖D.simplex a ha k η‖ ^ p) / _ = _
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun η : ↥(triangulation (d := d) k) => ‖D.simplex a ha k η‖ ^ p)
      (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  rw [hlhs]
  refine key.trans ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun l => ?_
  have hθ0 : 0 ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp
    linarith
  have hθ1 : 1 - 1 / p ≤ 1 := by have : 0 < 1 / p := by positivity
                                 linarith
  have hx : (0 : ℝ) ≤ ((3 : ℝ) ^ l)⁻¹ := by positivity
  have hK : (ENNReal.ofReal (C₀ * ((3 : ℝ) ^ l)⁻¹)) ^ (1 - 1 / p) ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.mul_rpow (by positivity) hx]
    have h1 : C₀ ^ (1 - 1 / p) ≤ C₀ := by
      calc C₀ ^ (1 - 1 / p) ≤ C₀ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC₁ hθ1
        _ = C₀ := Real.rpow_one _
    have h2 : (((3 : ℝ) ^ l)⁻¹) ^ (1 - 1 / p) = Real.rpow 3 (-((l : ℝ) * (1 - 1 / p))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul (by norm_num), neg_mul]
      rfl
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by norm_num) _)
  calc _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
        (ENNReal.ofReal (D.cubeAvg a ha (k + l) p)) ^ (1 / p) := mul_le_mul' hK le_rfl
    _ = _ := by rw [mul_assoc]; rfl

end RespData

end CoarseDeGiorgi.Cubical
