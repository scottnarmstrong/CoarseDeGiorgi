module

public import CoarseDeGiorgi.Harnack.Iterations.ExponentialCost
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Harnack.Iterations.NestedMomentLimit
public import CoarseDeGiorgi.Harnack.Iterations.PositiveMomentStop

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Remove the finite-positive bound restriction from the nested moment limit.
-/
theorem eLpNormEssSup_le_of_nested_normalizedMoments {d : ℕ}
    (E : Set (Vec d)) (V : ℕ → Set (Vec d)) (f : Vec d → ℝ)
    {A D : ℝ≥0∞} (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hDpos : 0 < D) (hDtop : D ≠ ⊤)
    (hsubset : ∀ n, E ⊆ V n) (hvolume : ∀ n, volume (V n) ≤ D * volume E)
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hpTop : Tendsto p atTop atTop)
    (hmeas : ∀ n, AEStronglyMeasurable f (volume.restrict (V n)))
    (hbound : ∀ n, normalizedLpMoment (p n) (hp n) (V n) f ≤ A) :
    eLpNormEssSup f (volume.restrict E) ≤ A := by
  by_contra hnot
  have hlt : A < eLpNormEssSup f (volume.restrict E) := lt_of_not_ge hnot
  obtain ⟨B, hAB, hBs⟩ := exists_between hlt
  have hBpos : 0 < B := zero_le.trans_lt hAB
  have hBtop : B ≠ ⊤ := (hBs.trans_le le_top).ne
  have h := eLpNormEssSup_le_of_uniform_normalizedMoments_on_nested_sets E V f
    hEpos hEtop hBpos hBtop hDpos hDtop hsubset hvolume p hp hpTop hmeas
    (fun n => (hbound n).trans hAB.le)
  exact (not_le_of_gt hBs) h

/-- Rearrange the reciprocal bound with a finite positive iteration factor.
-/
theorem reciprocal_iteration_bound_rearrange {H M I : ℝ≥0∞}
    (hHpos : 0 < H) (hHtop : H ≠ ⊤) (h : (H * M)⁻¹ ≤ I) :
    M⁻¹ ≤ H * I := by
  rw [ENNReal.mul_inv (Or.inl hHpos.ne') (Or.inl hHtop)] at h
  have hdiv : M⁻¹ / H ≤ I := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hmul := (ENNReal.div_le_iff hHpos.ne' hHtop).mp hdiv
  simpa only [mul_comm] using hmul

/-- A geometric powered chain with a uniform logarithmic envelope bounds every
normalized moment by the same initial-moment multiple.
-/
theorem geometric_normalizedMoment_chain_bound {d : ℕ}
    (V : ℕ → Set (Vec d)) (f : Vec d → ℝ)
    {χ b B : ℝ} (hχ : 0 < χ) (hb : 0 < b)
    (L : ℕ → ℝ)
    (hstep : ∀ j, normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
      (V (j + 1)) f ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (L j)) *
          normalizedLpMoment (b * χ ^ j) (by positivity) (V j) f ^ (b * χ ^ j))
    (hcost : ∀ n, (∑ j ∈ Finset.range n, (χ⁻¹) ^ j * L j) ≤ B)
    (n : ℕ) :
    normalizedLpMoment (b * χ ^ n) (by positivity) (V n) f ≤
      ENNReal.ofReal (Real.exp (B / b)) * normalizedLpMoment b hb (V 0) f := by
  let M := fun j => normalizedLpMoment (b * χ ^ j) (by positivity) (V j) f
  let K := fun j => ENNReal.ofReal (Real.exp (L j))
  have hchain := finite_rpow_iteration_chain_product M K (fun j => b * χ ^ j) n
    (fun j _ => by positivity) (fun j _ => hstep j)
  have hprod := geometric_cost_product_le hχ hb L K n (fun _ _ => le_rfl) (hcost n)
  calc
    _ ≤ (∏ j ∈ Finset.range n, K j ^ (1 / (b * χ ^ j))) * M 0 := hchain
    _ ≤ ENNReal.ofReal (Real.exp (B / b)) * M 0 := mul_le_mul_of_nonneg_right hprod zero_le
    _ = _ := by simp only [M, pow_zero, mul_one]

/-- The infinite geometric reciprocal chain passes to the essential infimum on
the fixed inner set, using precisely its common logarithmic envelope.
-/
theorem geometric_reciprocal_chain_essential_bound {d : ℕ}
    (E : Set (Vec d)) (V : ℕ → Set (Vec d)) (u : Vec d → ℝ)
    {χ b B : ℝ} (hχ : 1 < χ) (hb : 0 < b) (L : ℕ → ℝ)
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    {D : ℝ≥0∞} (hDpos : 0 < D) (hDtop : D ≠ ⊤)
    (hsubset : ∀ n, E ⊆ V n) (hvolume : ∀ n, volume (V n) ≤ D * volume E)
    (hu : ∀ᵐ x ∂volume.restrict E, 0 < u x)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => (u x)⁻¹) (volume.restrict (V n)))
    (hstep : ∀ j, normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
      (V (j + 1)) (fun x => (u x)⁻¹) ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (L j)) *
          normalizedLpMoment (b * χ ^ j) (by positivity) (V j)
            (fun x => (u x)⁻¹) ^ (b * χ ^ j))
    (hcost : ∀ n, (∑ j ∈ Finset.range n, (χ⁻¹) ^ j * L j) ≤ B) :
    (ENNReal.ofReal (Real.exp (B / b)) *
      normalizedLpMoment b hb (V 0) (fun x => (u x)⁻¹))⁻¹ ≤
        nonnegativeEssInf E u := by
  let A := ENNReal.ofReal (Real.exp (B / b)) *
    normalizedLpMoment b hb (V 0) (fun x => (u x)⁻¹)
  have hpTop : Tendsto (fun n : ℕ => b * χ ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hχ).const_mul_atTop hb
  apply nonnegativeEssInf_ge_inv_of_reciprocal_essSup_bound E u A hu
  apply eLpNormEssSup_le_of_nested_normalizedMoments E V (fun x => (u x)⁻¹)
    hEpos hEtop hDpos hDtop hsubset hvolume (fun n => b * χ ^ n)
    (fun _ => by positivity) hpTop hmeas
  intro n
  exact geometric_normalizedMoment_chain_bound V (fun x => (u x)⁻¹)
    (zero_lt_one.trans hχ) hb L hstep hcost n

/-- A stopped geometric chain has the same logarithmic envelope, followed by the
explicit subset volume factor at its terminal exponent.
-/
theorem geometric_stopped_chain_subset_bound {d : ℕ}
    (E : Set (Vec d)) (V : ℕ → Set (Vec d)) (f : Vec d → ℝ)
    {χ b B η : ℝ} (hχ : 0 < χ) (hb : 0 < b) (hη : 0 < η)
    (L : ℕ → ℝ) (N : ℕ) (hηN : η ≤ b * χ ^ N)
    (hstep : ∀ j < N, normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
      (V (j + 1)) f ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (L j)) *
          normalizedLpMoment (b * χ ^ j) (by positivity) (V j) f ^ (b * χ ^ j))
    (hcost : (∑ j ∈ Finset.range N, (χ⁻¹) ^ j * L j) ≤ B)
    (hsubset : E ⊆ V N) (hf : AEStronglyMeasurable f (volume.restrict (V N)))
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hVpos : 0 < volume (V N)) (hVtop : volume (V N) ≠ ⊤) :
    normalizedLpMoment η hη E f ≤
      volume E ^ (-(1 / (b * χ ^ N))) * volume (V N) ^ (1 / (b * χ ^ N)) *
        ENNReal.ofReal (Real.exp (B / b)) * normalizedLpMoment b hb (V 0) f := by
  have hprod := geometric_cost_product_le hχ hb L
    (fun j => ENNReal.ofReal (Real.exp (L j))) N (fun _ _ => le_rfl) hcost
  have h := normalizedLpMoment_stopped_chain_subset_bound E V f
    (fun j => b * χ ^ j) (fun j => ENNReal.ofReal (Real.exp (L j))) N
    (fun _ => by positivity) hstep η hη hηN hsubset hf hEpos hEtop hVpos hVtop
    (ENNReal.ofReal (Real.exp (B / b))) hprod
  simpa only [pow_zero, mul_one] using h

end CoarseDeGiorgi.Harnack.Iterations
