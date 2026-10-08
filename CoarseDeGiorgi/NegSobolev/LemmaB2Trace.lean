module

public import CoarseDeGiorgi.Statements.NegSobolevNorm
public import CoarseDeGiorgi.NegSobolev.LemmaB2Scaling
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Matrix and normalized dual-testing estimates for `l.negative.sobolev`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Every entry is bounded by the Euclidean operator norm. -/
theorem lemmaB2_abs_entry_le_norm {d : ℕ} (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  have hcoord := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e) i
  have hop := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e]
  have hentry : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A e).ofLp i‖ = |A i j| := by
    simp [e, Real.norm_eq_abs, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec]
  rw [hentry] at hcoord
  exact hcoord.trans (by simpa only [he, mul_one, Matrix.l2_opNorm_toEuclideanCLM] using hop)

/-- The trace bound holds for arbitrary real matrices. -/
theorem lemmaB2_abs_trace_le {d : ℕ} (A : Mat d) :
    |A.trace| ≤ (d : ℝ) * ‖A‖ := by
  calc
    |A.trace| ≤ ∑ i : Fin d, |A i i| := by
      simpa only [Matrix.trace, Matrix.diag_apply, Real.norm_eq_abs] using
        norm_sum_le (Finset.univ : Finset (Fin d)) (fun i => A i i)
    _ ≤ ∑ _i : Fin d, ‖A‖ := Finset.sum_le_sum (fun i _ => lemmaB2_abs_entry_le_norm A i i)
    _ = (d : ℝ) * ‖A‖ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- For positive semidefinite matrices the operator norm is bounded by the trace. -/
theorem lemmaB2_norm_le_trace {d : ℕ} {A : Mat d} (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace := by
  have hn : ‖A‖ = ‖hA.isHermitian.eigenvalues‖ := by
    conv_lhs => rw [hA.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal, RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [hn, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i))).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A bounded test function can be paired with every integrable matrix entry. -/
theorem lemmaB2_test_integrable {d : ℕ} {U : Set (Vec d)} {b : Vec d → Mat d}
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    {g : Vec d → ℝ} (hg : MemLp g ⊤ (volume.restrict U)) (i j : Fin d) :
    Integrable (fun x => g x * b x i j) (volume.restrict U) :=
  hg.integrable_mul (memLp_one_iff_integrable.mpr (hb i j))

/-- Testing by any member of the defining unit ball bounds the matrix pairing. -/
theorem lemmaB2_pairing_le_unit {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p)
    (g : Vec d → ℝ) (hg : MemLp g ⊤ (volume.restrict U))
    (hgn : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g ≤ 1) :
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖ ≤
      negSobolevNorm U hU b hb β p hβ hp := by
  unfold negSobolevNorm
  exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgn le_rfl))

/-- The trace pairing agrees with the trace of the entrywise matrix integral. -/
theorem lemmaB2_integral_trace {d : ℕ} {U : Set (Vec d)} {b : Vec d → Mat d}
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    {g : Vec d → ℝ} (hg : MemLp g ⊤ (volume.restrict U)) :
    ∫ x in U, g x * (b x).trace ∂volume =
      (Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume).trace := by
  simp only [Matrix.trace, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => lemmaB2_test_integrable hb hg i i)

/-- The normalized scalar trace pairing is controlled by the negative norm. -/
theorem lemmaB2_trace_pairing_le_unit {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p)
    (g : Vec d → ℝ) (hg : MemLp g ⊤ (volume.restrict U))
    (hgn : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g ≤ 1) :
    ENNReal.ofReal |∫ x in U, g x * (b x).trace ∂volume| ≤
      ENNReal.ofReal (d : ℝ) * negSobolevNorm U hU b hb β p hβ hp := by
  rw [lemmaB2_integral_trace hb hg]
  calc
    _ ≤ ENNReal.ofReal ((d : ℝ) * ‖Matrix.of fun i j =>
        ∫ x in U, g x * b x i j ∂volume‖) := ENNReal.ofReal_le_ofReal (lemmaB2_abs_trace_le _)
    _ = _ := ENNReal.ofReal_mul (Nat.cast_nonneg d)
    _ ≤ _ := mul_le_mul_right (lemmaB2_pairing_le_unit hU b hb β p hβ hp g hg hgn) _

/-- A positive real bound for the Sobolev norm gives the corresponding dual estimate. -/
theorem lemmaB2_pairing_le_of_bound {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p)
    (g : Vec d → ℝ) (hg : MemLp g ⊤ (volume.restrict U))
    (A : ℝ) (hA : 0 < A)
    (hgn : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g ≤ ENNReal.ofReal A) :
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖ ≤
      ENNReal.ofReal A * negSobolevNorm U hU b hb β p hβ hp := by
  have hA0 : ENNReal.ofReal A ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hA)
  have hAi : ENNReal.ofReal A⁻¹ = (ENNReal.ofReal A)⁻¹ := ENNReal.ofReal_inv_of_pos hA
  have hunit : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) (fun x => A⁻¹ * g x) ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal A⁻¹ * sobolevNorm U hU β (p / (p - 1)) hβ
          ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g :=
        lemmaB2_sobolevNorm_const_mul_le hU _ _ hβ _ g A⁻¹ (inv_pos.mpr hA)
      _ ≤ ENNReal.ofReal A⁻¹ * ENNReal.ofReal A := mul_le_mul_right hgn _
      _ = 1 := by rw [hAi, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top]
  have hscaled := lemmaB2_pairing_le_unit hU b hb β p hβ hp
    (fun x => A⁻¹ * g x) (hg.const_smul A⁻¹) hunit
  have hmat : (Matrix.of fun i j => ∫ x in U, (A⁻¹ * g x) * b x i j ∂volume) =
      A⁻¹ • (Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume) := by
    ext i j
    change (∫ x in U, (A⁻¹ * g x) * b x i j ∂volume) =
      A⁻¹ * (∫ x in U, g x * b x i j ∂volume)
    simp only [mul_assoc, integral_const_mul]
  rw [hmat, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA),
    ENNReal.ofReal_mul (inv_nonneg.mpr hA.le), hAi] at hscaled
  calc
    _ = ENNReal.ofReal A * ((ENNReal.ofReal A)⁻¹ *
        ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul_right hscaled _

/-- The bounded-test trace estimate with a positive real upper bound on the Sobolev norm. -/
theorem lemmaB2_trace_pairing_le_of_bound {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p)
    (g : Vec d → ℝ) (hg : MemLp g ⊤ (volume.restrict U))
    (A : ℝ) (hA : 0 < A)
    (hgn : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g ≤ ENNReal.ofReal A) :
    ENNReal.ofReal |∫ x in U, g x * (b x).trace ∂volume| ≤
      ENNReal.ofReal (d : ℝ) * ENNReal.ofReal A * negSobolevNorm U hU b hb β p hβ hp := by
  rw [lemmaB2_integral_trace hb hg]
  calc
    _ ≤ ENNReal.ofReal ((d : ℝ) * ‖Matrix.of fun i j =>
        ∫ x in U, g x * b x i j ∂volume‖) := ENNReal.ofReal_le_ofReal (lemmaB2_abs_trace_le _)
    _ = _ := ENNReal.ofReal_mul (Nat.cast_nonneg d)
    _ ≤ ENNReal.ofReal (d : ℝ) * (ENNReal.ofReal A * negSobolevNorm U hU b hb β p hβ hp) :=
      mul_le_mul_right (lemmaB2_pairing_le_of_bound hU b hb β p hβ hp g hg A hA hgn) _
    _ = _ := (mul_assoc _ _ _).symm

end CoarseDeGiorgi.NegSobolev
