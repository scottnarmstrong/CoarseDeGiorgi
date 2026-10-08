module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialDefs

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomialCubeFiniteVolume {d : ℕ} :
    volume (originCube (d := d) 1) ≠ ⊤ := by
  have he : originCube (d := d) 1 =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [he, Real.volume_pi_Ioo]
  norm_num

private theorem polynomialIdentityCoefficient {d : ℕ} {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) : IsWeightedCoeffOn V (fun _ => (1 : Mat d)) := by
  refine ⟨aestronglyMeasurable_const, ?_, ?_, ?_⟩
  · filter_upwards with x
    exact Matrix.PosDef.one
  · exact integrableOn_const hV
  · simpa using (integrableOn_const hV : IntegrableOn
      (fun _ : Vec d => (1 : Mat d).trace) V)

private theorem polynomialParallel_pos {d : ℕ} {q t epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon) : 0 < polynomialParallel d q t epsilon := by
  unfold polynomialParallel
  apply mul_pos
  · have hdR : 0 < (d : ℝ) - 1 := by
      have hcast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    exact hdR
  · exact Real.rpow_pos_of_pos hepsilon _

theorem polynomialPerpendicular_pos {d : ℕ} {q t epsilon : ℝ}
    (hepsilon : 0 < epsilon) : 0 < polynomialPerpendicular d q t epsilon := by
  unfold polynomialPerpendicular
  exact Real.rpow_pos_of_pos hepsilon _

/-- The total field is weighted on the unit cube for every real parameter. -/
theorem polynomialCoefficientFamily_weightedCoeffOn {d : ℕ} (hd : 2 ≤ d)
    (q t epsilon : ℝ) :
    IsWeightedCoeffOn (originCube (d := d) 1)
      (polynomialCoefficientFamily d q t epsilon) := by
  classical
  unfold polynomialCoefficientFamily
  split_ifs with he
  · exact cylinderCoefficient_weightedCoeffOn polynomialCubeFiniteVolume epsilon
      (polynomialParallel_pos hd he.1) (polynomialPerpendicular_pos he.1)
  · exact polynomialIdentityCoefficient polynomialCubeFiniteVolume

/-- Decomposing the parameter in the polynomial construction isolates the
inverse-moment exponent. -/
theorem polynomialTheta_decomposition (d : ℕ) (p q s t : ℝ) :
    paramTheta d p q s t =
      1 - (s + ((d : ℝ) - 1) / (2 * p)) - polynomialHatT d q t := by
  rw [polynomialHatT]
  unfold paramTheta
  ring

theorem polynomialHatT_pos {d : ℕ} (hd : 2 ≤ d) {q t : ℝ}
    (hq : 1 < q) (ht : 0 < t) :
    0 < polynomialHatT d q t := by
  unfold polynomialHatT
  have hdR : 0 < (d : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact add_pos ht (div_pos hdR (by positivity))

theorem polynomialHatT_lt_one {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hs : 0 < s)
    (hθ : 0 < paramTheta d p q s t) : polynomialHatT d q t < 1 := by
  have hdecomp := polynomialTheta_decomposition d p q s t
  rw [hdecomp] at hθ
  have hp0 : 0 < p := by linarith
  have hdR : 0 < (d : ℝ) - 1 := by
    have h3 : (3 : ℝ) ≤ (d : ℝ) := by norm_cast
    linarith
  have hterm : 0 < s + ((d : ℝ) - 1) / (2 * p) := by positivity
  linarith

end

end CoarseDeGiorgi.SharpnessExamples
