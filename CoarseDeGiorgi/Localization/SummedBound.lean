module

public import CoarseDeGiorgi.Localization.SummedCore

/-! # The summed localization bound for a measurable representative -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Foundations
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem summed_localization_bound (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t) (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (δ R b : ℝ) (m : ℤ) (K : Set (Vec d)),
          0 < δ → δ ≤ 1 → R ≤ 1 → 1 ≤ m → gridSpacing m ≤ 1 → δ / 192 < gridSpacing m →
          LocalizationCover m K R δ →
          (∀ y ∈ K, ∀ i, |y i| ≤ b / 2) → b + 4 * gridSpacing m < R →
          ∀ (w : Vec d → ℝ) (G : Vec d → Vec d), MemH1a a (originCube 1) w G → Measurable w →
            fracNorm Set.univ (alphaParam t) (paramR q) (localizedFunction m (coverIndices m K) w) ≤
              C * ENNReal.ofReal (δ ^ (-alphaParam t)) *
                ((lowerMoment a ha t q ht (le_of_lt hq)) ^ (-(1 / 2) : ℝ) *
                    (weightedEnergy a (originCube R) G) ^ (1 / 2 : ℝ) +
                  eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hα, hα1, hr, hr2, -⟩ := Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  obtain ⟨A, hA0, hlocal⟩ := CoarseDeGiorgi.lower_fractional_scale_bound d hd q t hq ht
  obtain ⟨C₁, hC₁fin, -, hsum⟩ := exists_localization_sum_gap_constant (d := d) hα hα1 hr
  set r := paramR q with hrdef
  set α := alphaParam t with hαdef
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hrq : r = 2 * q / (q + 1) := rfl
  set M : ℝ≥0∞ := ((4 ^ d : ℕ) : ℝ≥0∞) with hM
  have hMfin : M ≠ ⊤ := by simp [hM]
  set Kc : ℝ≥0∞ := M ^ (1 / (2 * q)) * M ^ (1 / 2 : ℝ) with hKc
  set N : ℝ≥0∞ := ENNReal.ofReal ((1 - Real.rpow 3 (-t))⁻¹) with hN
  refine ⟨C₁ ^ (1 / r) * (ENNReal.ofReal A * Kc * N + M ^ (1 / r)), ?_, ?_⟩
  · have : Kc ≠ ⊤ := by
      rw [hKc]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hMfin)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin)
    refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hC₁fin) ?_
    refine ENNReal.add_lt_top.mpr ⟨?_, ENNReal.rpow_lt_top_of_nonneg (by positivity) hMfin⟩
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top this.lt_top)
      ENNReal.ofReal_lt_top
  intro a ha hrange δ R b m K hδ hδ1 hR hm1 hs1 hgap hcover hK hm w G hw hwm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) + 1 = m := ⟨(m - 1).toNat, by omega⟩
  have hunit := unitCube_domain (d := d)
  have henergy := Weighted.MemH1a.energy_lt_top hunit.1.isOpen ha hw
  have hsubR : radiusCube (d := d) R ⊆ originCube 1 := by
    rw [radiusCube_eq_originCube]; exact originCube_mono hR
  have hQ (z : Fin d → ℤ) (hz : z ∈ coverIndices ((n : ℤ) + 1) K) :
      closure (auxCube ((n : ℤ) + 1) z) ⊆ originCube 1 := ((hcover.1 z hz).2).trans hsubR
  have hmem (z : Fin d → ℤ) (hz : z ∈ coverIndices ((n : ℤ) + 1) K) :
      MemH1a a (auxCube ((n : ℤ) + 1) z) w G :=
    LowerFractional.memH1a_restrict hunit.1 hunit.2 ha
      (LowerFractional.auxCube_isOpenBoundedConvexDomain _ z)
      (subset_closure.trans (hQ z hz)) hw
  have hfin (z : Fin d → ℤ) (hz : z ∈ coverIndices ((n : ℤ) + 1) K) :
      fracNorm (auxCube ((n : ℤ) + 1) z) α r w < ⊤ := by
    obtain ⟨Cz, hCz, hbd⟩ := lower_fractional_embedding hd p q s t a ha hrange _ z (subset_closure.trans (hQ z hz))
    refine (hbd w G (hmem z hz)).trans_lt (ENNReal.mul_lt_top hCz ?_)
    unfold h1aWeightedNorm
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, (lintegral_mono_set (subset_closure.trans (hQ z hz))).trans_lt henergy⟩).ne
  -- the local bounds, summed
  have hloc : ∀ z ∈ coverIndices ((n : ℤ) + 1) K,
      fracSeminorm (auxCube ((n : ℤ) + 1) z) α r w ≤
        ENNReal.ofReal A * (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
            volume (simplexCell k η) *
              ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ^ (1 / (2 * q))) *
          (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G) ^ (1 / 2 : ℝ) := by
    intro z hz
    refine (hlocal p s hp hs a ha hrange n z w G (subset_closure.trans (hQ z hz)) (hmem z hz)).trans ?_
    rw [mul_right_comm]
    simp only [ENNReal.rpow_eq_pow]
    gcongr with k
    split_ifs <;> simp
  have hT : ∀ k : ℕ, (∑ z ∈ coverIndices ((n : ℤ) + 1) K,
      ∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
        volume (simplexCell k η) *
          ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ≤
      M * ENNReal.ofReal (lowerCellAverage a ha k q) := fun k =>
    sum_cells_overlap_le a ha _ _ k q
  have hE := sum_energy_overlap_le ha hw.2.1 (m := (n : ℤ) + 1) (K := K) hK hm
    (by rw [radiusCube_eq_originCube]; exact originCube_mono hR)
  rw [radiusCube_eq_originCube] at hE
  have hsl := summed_local_bound (coverIndices ((n : ℤ) + 1) K)
    (fun z => fracSeminorm (auxCube ((n : ℤ) + 1) z) α r w)
    (fun z => weightedEnergy a (auxCube ((n : ℤ) + 1) z) G)
    (fun k z => ∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
        volume (simplexCell k η) *
          ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q))
    (fun k => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))))
    (fun k => ENNReal.ofReal (lowerCellAverage a ha k q)) (ENNReal.ofReal A) M
    (weightedEnergy a (originCube R) G) hq hrq hloc hT hE
  rw [lowerMoment_series_eq a ha t q ht hq.le] at hsl
  have hmass := sum_local_eLpNorm_rpow_le hr0 hK hm hwm
  rw [radiusCube_eq_originCube] at hmass
  have hF := hsum δ hδ ((n : ℤ) + 1) hs1 hgap (coverIndices ((n : ℤ) + 1) K) w hwm hfin
  set X : ℝ≥0∞ := ∑ z ∈ coverIndices ((n : ℤ) + 1) K,
    fracSeminorm (auxCube ((n : ℤ) + 1) z) α r w ^ r with hX
  set Y : ℝ≥0∞ := eLpNorm w (ENNReal.ofReal r) (volume.restrict (originCube R)) with hY
  set D : ℝ≥0∞ := ENNReal.ofReal (δ ^ (-α * r)) with hD
  have h1 : fracNorm univ α r (localizedFunction ((n : ℤ) + 1) (coverIndices ((n : ℤ) + 1) K) w) ≤
      (C₁ * X + C₁ * D * (M * Y ^ r)) ^ (1 / r) := by
    have h := ENNReal.rpow_le_rpow
      (hF.trans (add_le_add le_rfl (mul_le_mul_right hmass _))) (one_div_nonneg.mpr hr0.le)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one] at h
    exact h
  refine h1.trans ((ENNReal.rpow_add_le_add_rpow _ _ (one_div_nonneg.mpr hr0.le)
    (by rw [div_le_one hr0]; exact hr.le)).trans ?_)
  have hδα : 1 ≤ ENNReal.ofReal (δ ^ (-α)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith))
  have hD' : D ^ (1 / r) = ENNReal.ofReal (δ ^ (-α)) := by
    rw [hD, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hδ.le _) (one_div_nonneg.mpr hr0.le),
      ← Real.rpow_mul hδ.le]
    congr 2
    field_simp
  have hY' : (Y ^ r) ^ (1 / r) = Y := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
  have t1 : (C₁ * X) ^ (1 / r) ≤ C₁ ^ (1 / r) * (ENNReal.ofReal A * Kc *
      ((N * (lowerMoment a ha t q ht hq.le) ^ (-(1 / 2) : ℝ)) *
        (weightedEnergy a (originCube R) G) ^ (1 / 2 : ℝ))) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le)]
    exact mul_le_mul_right hsl _
  have t2 : (C₁ * D * (M * Y ^ r)) ^ (1 / r) =
      ENNReal.ofReal (δ ^ (-α)) * (C₁ ^ (1 / r) * M ^ (1 / r) * Y) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le),
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le),
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le), hD', hY']
    ring
  refine add_le_add t1 t2.le |>.trans ?_
  set lam := (lowerMoment a ha t q ht hq.le) ^ (-(1 / 2) : ℝ)
  set Et := (weightedEnergy a (originCube R) G) ^ (1 / 2 : ℝ)
  set E1 := C₁ ^ (1 / r)
  have hA' : E1 * (ENNReal.ofReal A * Kc * N) ≤ E1 * (ENNReal.ofReal A * Kc * N + M ^ (1 / r)) :=
    mul_le_mul_right (le_self_add) _
  have hB' : E1 * M ^ (1 / r) ≤ E1 * (ENNReal.ofReal A * Kc * N + M ^ (1 / r)) :=
    mul_le_mul_right (le_add_self) _
  set Cf := E1 * (ENNReal.ofReal A * Kc * N + M ^ (1 / r))
  calc E1 * (ENNReal.ofReal A * Kc * (N * lam * Et)) + ENNReal.ofReal (δ ^ (-α)) * (E1 * M ^ (1 / r) * Y)
      = (E1 * (ENNReal.ofReal A * Kc * N)) * (lam * Et) +
        ENNReal.ofReal (δ ^ (-α)) * ((E1 * M ^ (1 / r)) * Y) := by ring
    _ ≤ (ENNReal.ofReal (δ ^ (-α)) * Cf) * (lam * Et) + ENNReal.ofReal (δ ^ (-α)) * (Cf * Y) :=
      add_le_add (mul_le_mul' (hA'.trans (le_mul_of_one_le_left' hδα)) le_rfl)
        (mul_le_mul' le_rfl (mul_le_mul' hB' le_rfl))
    _ = _ := by ring

end
end CoarseDeGiorgi.Localization
