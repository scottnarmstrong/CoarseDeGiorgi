import CoarseDeGiorgi.SharpnessExamples.Parameters
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
import Mathlib.Topology.Instances.Matrix

open Homogenization MeasureTheory
open CoarseDeGiorgi.Sharpness
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The core where the scalar conductivity takes its large value. -/
def scalarCoreBand {d : ℕ} (n : ℕ) (ζ κ : ℝ) : Set (Vec d) :=
  {x | transverseNorm (x - cylinderCenter (cylinderB n)) <
    cylinderRadius d n ζ κ}

/-- The open annulus where the scalar conductivity takes its small value. -/
def scalarAnnulusBand {d : ℕ} (n : ℕ) (ζ κ : ℝ) : Set (Vec d) :=
  {x | cylinderRadius d n ζ κ < transverseNorm (x - cylinderCenter (cylinderB n)) ∧
    transverseNorm (x - cylinderCenter (cylinderB n)) <
      2 * cylinderRadius d n ζ κ}

/-- Large core conductivity `b_n ε_n^(-ζ)`. -/
noncomputable def scalarCoreValue (d n : ℕ) (ζ κ : ℝ) : ℝ :=
  cylinderB n * Real.rpow (cylinderRadius d n ζ κ) (-ζ)

/-- Small annular conductivity `b_n^(-1) ε_n^(2-ζ)`. -/
noncomputable def scalarAnnulusValue (d n : ℕ) (ζ κ : ℝ) : ℝ :=
  (cylinderB n)⁻¹ * Real.rpow (cylinderRadius d n ζ κ) (2 - ζ)

/-- The signed deviation from the background conductivity contributed by one
cylinder. -/
noncomputable def scalarCylinderContribution {d : ℕ} (n : ℕ) (ζ κ : ℝ)
    (x : Vec d) : ℝ := by
  classical
  exact if x ∈ scalarCoreBand n ζ κ then scalarCoreValue d n ζ κ - 1
    else if x ∈ scalarAnnulusBand n ζ κ then scalarAnnulusValue d n ζ κ - 1
    else 0

/-- The scalar conductivity, written as a pointwise sum of the disjoint band
deviations. On both interfaces the value is exactly one. -/
noncomputable def scalarSharpnessWeight {d : ℕ} (ζ κ : ℝ) (x : Vec d) : ℝ :=
  1 + ∑' n : ℕ, scalarCylinderContribution n ζ κ x

/-- The scalar coefficient matrix associated with the weight. -/
noncomputable def scalarSharpnessCoefficient {d : ℕ} (ζ κ : ℝ) : CoeffField d :=
  fun x => scalarSharpnessWeight ζ κ x • (1 : Mat d)

theorem scalarCoreBand_measurable {d : ℕ} (n : ℕ) (ζ κ : ℝ) :
    MeasurableSet (scalarCoreBand (d := d) n ζ κ) := by
  exact (isOpen_lt
    (lineRadius_continuous.comp
      (continuous_id.sub continuous_const)) continuous_const).measurableSet

theorem scalarAnnulusBand_measurable {d : ℕ} (n : ℕ) (ζ κ : ℝ) :
    MeasurableSet (scalarAnnulusBand (d := d) n ζ κ) := by
  have hρ : Continuous (fun x : Vec d =>
      transverseNorm (x - cylinderCenter (cylinderB n))) :=
    lineRadius_continuous.comp (continuous_id.sub continuous_const)
  exact (isOpen_lt continuous_const hρ).inter
    (isOpen_lt hρ continuous_const) |>.measurableSet

theorem scalarCylinderContribution_measurable {d : ℕ} (n : ℕ) (ζ κ : ℝ) :
    Measurable (scalarCylinderContribution (d := d) n ζ κ) := by
  classical
  unfold scalarCylinderContribution
  exact Measurable.ite (scalarCoreBand_measurable n ζ κ) measurable_const
    (Measurable.ite (scalarAnnulusBand_measurable n ζ κ)
      measurable_const measurable_const)

private theorem scalarCylinderContribution_support_outer {d n : ℕ} {ζ κ : ℝ}
    (hd : 3 ≤ d) (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    {x : Vec d} (h : scalarCylinderContribution n ζ κ x ≠ 0) :
    x ∈ outerCylinder n ζ κ := by
  classical
  unfold scalarCylinderContribution at h
  by_cases hc : x ∈ scalarCoreBand n ζ κ
  · rw [ite_eq_left hc] at h
    change transverseNorm (x - cylinderCenter (cylinderB n)) ≤
      2 * cylinderRadius d n ζ κ
    dsimp [scalarCoreBand] at hc
    exact le_of_lt (hc.trans (by
      have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ).1
      linarith))
  · rw [ite_eq_right hc] at h
    by_cases ha : x ∈ scalarAnnulusBand n ζ κ
    · rw [ite_eq_left ha] at h
      change transverseNorm (x - cylinderCenter (cylinderB n)) ≤
        2 * cylinderRadius d n ζ κ
      exact (ha.2).le
    · rw [ite_eq_right ha] at h
      exact (h rfl).elim

private theorem scalarContribution_unique {d : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d)
    {i j : ℕ} (hi : scalarCylinderContribution i ζ κ x ≠ 0)
    (hj : scalarCylinderContribution j ζ κ x ≠ 0) : i = j := by
  classical
  have hxi := scalarCylinderContribution_support_outer hd hζ0 hζ2 hκ hi
  have hxj := scalarCylinderContribution_support_outer hd hζ0 hζ2 hκ hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij' | hji
  · exact (Set.disjoint_left.mp
      (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hij')) hxi hxj
  · exact (Set.disjoint_left.mp
      (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hji) hxj hxi)

private theorem scalarCylinderContribution_summable {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d) :
    Summable (fun n : ℕ => scalarCylinderContribution n ζ κ x) := by
  classical
  by_cases hex : ∃ n, scalarCylinderContribution n ζ κ x ≠ 0
  · obtain ⟨i, hi⟩ := hex
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton i).subset
    intro j hj
    exact Set.mem_singleton_iff.mpr
      (scalarContribution_unique (i := i) (j := j) hd hζ0 hζ2 hκ x hi hj).symm
  · apply summable_of_hasFiniteSupport
    apply Set.finite_empty.subset
    intro i hi
    exact (hex ⟨i, hi⟩).elim

theorem scalarSharpnessWeight_measurable {d : ℕ} (ζ κ : ℝ) :
    Measurable (scalarSharpnessWeight (d := d) ζ κ) := by
  classical
  apply Measurable.add measurable_const
  exact Measurable.tsum fun n => scalarCylinderContribution_measurable n ζ κ

theorem scalarSharpnessWeight_pos {d : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d) :
    0 < scalarSharpnessWeight ζ κ x := by
  classical
  have hsum := scalarCylinderContribution_summable hd hζ0 hζ2 hκ x
  by_cases hex : ∃ n, scalarCylinderContribution n ζ κ x ≠ 0
  · obtain ⟨n, hn⟩ := hex
    have htsum : (∑' j : ℕ, scalarCylinderContribution j ζ κ x) =
        scalarCylinderContribution n ζ κ x :=
      tsum_eq_single n (by
        intro j hji
        by_contra hj
        have heq := scalarContribution_unique hd hζ0 hζ2 hκ x hn hj
        exact hji heq.symm)
    rw [scalarSharpnessWeight, htsum]
    have hdata := cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ
    have hb : 0 < cylinderB n := cylinderB_pos n
    have hcore : 0 < scalarCoreValue d n ζ κ := by
      unfold scalarCoreValue
      exact mul_pos hb (Real.rpow_pos_of_pos hdata.1 _)
    have hann : 0 < scalarAnnulusValue d n ζ κ := by
      unfold scalarAnnulusValue
      exact mul_pos (inv_pos.mpr hb) (Real.rpow_pos_of_pos hdata.1 _)
    by_cases hc : x ∈ scalarCoreBand n ζ κ
    · simp only [scalarCylinderContribution, ite_eq_left hc]
      linarith
    · have ha : x ∈ scalarAnnulusBand n ζ κ := by
        by_contra hna
        have hz : scalarCylinderContribution n ζ κ x = 0 := by
          simp [scalarCylinderContribution, hc, hna]
        exact hn hz
      simp only [scalarCylinderContribution, ite_eq_right hc, ite_eq_left ha]
      linarith
  · have hzero : ∀ n, scalarCylinderContribution n ζ κ x = 0 := by
      intro n
      by_contra hn
      exact hex ⟨n, hn⟩
    simp [scalarSharpnessWeight, hzero]

theorem scalarSharpnessWeight_eq_core {d : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) {n : ℕ} {x : Vec d}
    (hx : x ∈ scalarCoreBand n ζ κ) :
    scalarSharpnessWeight ζ κ x = scalarCoreValue d n ζ κ := by
  classical
  have hrad := cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ
  have houter : x ∈ outerCylinder n ζ κ := by
    change transverseNorm (x - cylinderCenter (cylinderB n)) ≤
      2 * cylinderRadius d n ζ κ
    change transverseNorm (x - cylinderCenter (cylinderB n)) <
      cylinderRadius d n ζ κ at hx
    linarith [hx, hrad.1]
  have htsum : (∑' j : ℕ, scalarCylinderContribution j ζ κ x) =
      scalarCylinderContribution n ζ κ x :=
    tsum_eq_single n (by
      intro j hji
      by_contra hj
      have houterj := scalarCylinderContribution_support_outer
        hd hζ0 hζ2 hκ hj
      by_cases hlt : n < j
      · exact (Set.disjoint_left.mp
          (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hlt) houter houterj)
      · have hjlt : j < n := by omega
        exact (Set.disjoint_left.mp
          (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hjlt) houterj houter))
  rw [scalarSharpnessWeight, htsum]
  simp [scalarCylinderContribution, hx]

theorem scalarSharpnessWeight_eq_annulus {d : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) {n : ℕ} {x : Vec d}
    (hx : x ∈ scalarAnnulusBand n ζ κ) :
    scalarSharpnessWeight ζ κ x = scalarAnnulusValue d n ζ κ := by
  classical
  have houter : x ∈ outerCylinder n ζ κ := by
    change transverseNorm (x - cylinderCenter (cylinderB n)) ≤
      2 * cylinderRadius d n ζ κ
    exact hx.2.le
  have htsum : (∑' j : ℕ, scalarCylinderContribution j ζ κ x) =
      scalarCylinderContribution n ζ κ x :=
    tsum_eq_single n (by
      intro j hji
      by_contra hj
      have houterj := scalarCylinderContribution_support_outer
        hd hζ0 hζ2 hκ hj
      by_cases hlt : n < j
      · exact (Set.disjoint_left.mp
          (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hlt) houter houterj)
      · have hjlt : j < n := by omega
        exact (Set.disjoint_left.mp
          (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hjlt) houterj houter))
  rw [scalarSharpnessWeight, htsum]
  have hcore : x ∉ scalarCoreBand n ζ κ := by
    intro hcore
    change transverseNorm (x - cylinderCenter (cylinderB n)) <
      cylinderRadius d n ζ κ at hcore
    change cylinderRadius d n ζ κ <
        transverseNorm (x - cylinderCenter (cylinderB n)) ∧ _ at hx
    linarith
  simp [scalarCylinderContribution, hcore, hx]

theorem scalarSharpnessWeight_invariant {d : ℕ} {ζ κ : ℝ}
    {x x' : Vec d}
    (h : ∀ i : Fin d, (i : ℕ) ≠ 0 → x i = x' i) :
    scalarSharpnessWeight ζ κ x = scalarSharpnessWeight ζ κ x' := by
  classical
  have htrans (n : ℕ) :
      transverseNorm (x - cylinderCenter (cylinderB n)) =
        transverseNorm (x' - cylinderCenter (cylinderB n)) := by
    have hp : transversePart (x - cylinderCenter (cylinderB n)) =
        transversePart (x' - cylinderCenter (cylinderB n)) := by
      funext i
      by_cases hi : i.val = 0
      · simp [transversePart, hi]
      · have hx := h i hi
        simp [transversePart, hi, cylinderCenter, hx]
    exact congrArg euclideanNorm hp
  have hterm (n : ℕ) : scalarCylinderContribution n ζ κ x =
      scalarCylinderContribution n ζ κ x' := by
    classical
    have hcore : x ∈ scalarCoreBand n ζ κ ↔ x' ∈ scalarCoreBand n ζ κ := by
      change transverseNorm (x - cylinderCenter (cylinderB n)) <
          cylinderRadius d n ζ κ ↔
        transverseNorm (x' - cylinderCenter (cylinderB n)) < cylinderRadius d n ζ κ
      rw [htrans n]
    have hann : x ∈ scalarAnnulusBand n ζ κ ↔ x' ∈ scalarAnnulusBand n ζ κ := by
      change (cylinderRadius d n ζ κ <
          transverseNorm (x - cylinderCenter (cylinderB n)) ∧
        transverseNorm (x - cylinderCenter (cylinderB n)) <
          2 * cylinderRadius d n ζ κ) ↔
        (cylinderRadius d n ζ κ <
          transverseNorm (x' - cylinderCenter (cylinderB n)) ∧
        transverseNorm (x' - cylinderCenter (cylinderB n)) <
          2 * cylinderRadius d n ζ κ)
      rw [htrans n]
    unfold scalarCylinderContribution
    simp only [hcore, hann]
  unfold scalarSharpnessWeight
  rw [show (fun n : ℕ => scalarCylinderContribution n ζ κ x) =
      fun n => scalarCylinderContribution n ζ κ x' from funext hterm]

local instance matMeasurableSpace {d : ℕ} : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

local instance matBorelSpace {d : ℕ} : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

local instance matPseudoMetrizableSpace {d : ℕ} :
    TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))

local instance matSecondCountableTopology {d : ℕ} : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

theorem scalarSharpnessCoefficient_measurable {d : ℕ} (ζ κ : ℝ) :
    Measurable (scalarSharpnessCoefficient (d := d) ζ κ) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simp only [scalarSharpnessCoefficient, Matrix.smul_apply]
  exact (scalarSharpnessWeight_measurable ζ κ).mul measurable_const

theorem scalarSharpnessCoefficient_posDef {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d) :
    (scalarSharpnessCoefficient ζ κ x).PosDef := by
  have heq : scalarSharpnessCoefficient ζ κ x =
      Matrix.diagonal (fun _ : Fin d => scalarSharpnessWeight ζ κ x) := by
    ext i j
    simp [scalarSharpnessCoefficient, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  rw [heq, Matrix.posDef_diagonal_iff]
  intro i
  exact scalarSharpnessWeight_pos hd hζ0 hζ2 hκ x

theorem scalarSharpnessCoefficient_eq_diagonal {d : ℕ} (ζ κ : ℝ) (x : Vec d) :
    scalarSharpnessCoefficient ζ κ x =
      Matrix.diagonal (fun _ : Fin d => scalarSharpnessWeight ζ κ x) := by
  ext i j
  simp [scalarSharpnessCoefficient, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply]

theorem scalarSharpnessCoefficient_inv_diagonal {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d) :
    (scalarSharpnessCoefficient ζ κ x)⁻¹ =
      Matrix.diagonal (fun _ : Fin d => (scalarSharpnessWeight ζ κ x)⁻¹) := by
  let w := scalarSharpnessWeight ζ κ x
  let v : Fin d → ℝ := fun _ => w
  have hwpos : 0 < w := scalarSharpnessWeight_pos hd hζ0 hζ2 hκ x
  have hwne : w ≠ 0 := hwpos.ne'
  have hvunit : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (by simpa [v, w] using hwne)
  let : Invertible v := hvunit.invertible
  have hvInv : (⅟v : Fin d → ℝ) = fun _ => w⁻¹ := by
    apply invOf_eq_right_inv
    ext i
    simp [v, hwne]
  rw [scalarSharpnessCoefficient_eq_diagonal, Matrix.inv_diagonal]
  congr 1
  funext i
  change (Ring.inverse v) i = _
  rw [Ring.inverse_invertible v, hvInv]

theorem scalarSharpnessCoefficient_trace {d : ℕ} (ζ κ : ℝ) (x : Vec d) :
    (scalarSharpnessCoefficient ζ κ x).trace =
      (d : ℝ) * scalarSharpnessWeight ζ κ x := by
  rw [scalarSharpnessCoefficient_eq_diagonal]
  simp [Matrix.trace]

theorem scalarSharpnessCoefficient_inv_trace {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec d) :
    ((scalarSharpnessCoefficient ζ κ x)⁻¹).trace =
      (d : ℝ) * (scalarSharpnessWeight ζ κ x)⁻¹ := by
  rw [scalarSharpnessCoefficient_inv_diagonal hd hζ0 hζ2 hκ]
  simp [Matrix.trace]

theorem scalarSharpnessCoefficient_entrywise_integrable {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hω : IntegrableOn (scalarSharpnessWeight (d := d) ζ κ) (originCube 1) volume)
    (hωi : IntegrableOn (fun x => (scalarSharpnessWeight (d := d) ζ κ x)⁻¹)
      (originCube 1) volume) :
    (∀ i j : Fin d, Integrable (fun x => scalarSharpnessCoefficient ζ κ x i j)
        (volume.restrict (originCube (d := d) 1))) ∧
      (∀ i j : Fin d, Integrable
        (fun x => (scalarSharpnessCoefficient ζ κ x)⁻¹ i j)
        (volume.restrict (originCube (d := d) 1))) := by
  constructor
  · intro i j
    have heq : (fun x => scalarSharpnessCoefficient ζ κ x i j) =
        if i = j then scalarSharpnessWeight ζ κ else fun _ => 0 := by
      funext x
      simp [scalarSharpnessCoefficient_eq_diagonal, Matrix.diagonal_apply]
      split_ifs <;> rfl
    rw [heq]
    split_ifs with hij
    · exact hω
    · exact integrable_zero (Vec d) ℝ (volume.restrict (originCube 1))
  · intro i j
    have heq : (fun x => (scalarSharpnessCoefficient ζ κ x)⁻¹ i j) =
        if i = j then (fun x => (scalarSharpnessWeight ζ κ x)⁻¹) else fun _ => 0 := by
      funext x
      simp [scalarSharpnessCoefficient_inv_diagonal hd hζ0 hζ2 hκ,
        Matrix.diagonal_apply]
      split_ifs <;> rfl
    rw [heq]
    split_ifs with hij
    · exact hωi
    · exact integrable_zero (Vec d) ℝ (volume.restrict (originCube 1))

theorem scalarSharpnessCoefficient_weightedCoeffOn {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hω : IntegrableOn (scalarSharpnessWeight (d := d) ζ κ) (originCube 1) volume)
    (hωi : IntegrableOn (fun x => (scalarSharpnessWeight (d := d) ζ κ x)⁻¹)
      (originCube 1) volume) :
    IsWeightedCoeffOn (originCube (d := d) 1)
      (scalarSharpnessCoefficient (d := d) ζ κ) := by
  have hmeas : Measurable (scalarSharpnessCoefficient (d := d) ζ κ) :=
    scalarSharpnessCoefficient_measurable ζ κ
  refine ⟨hmeas.aestronglyMeasurable, ae_of_all _ (fun x => ?_), ?_, ?_⟩
  · exact scalarSharpnessCoefficient_posDef hd hζ0 hζ2 hκ x
  · have heq : (fun x : Vec d => (scalarSharpnessCoefficient ζ κ x).trace) =
      fun x : Vec d => (d : ℝ) * scalarSharpnessWeight ζ κ x := by
        funext x
        exact scalarSharpnessCoefficient_trace ζ κ x
    rw [heq]
    exact hω.const_mul _
  · have heq : (fun x : Vec d => ((scalarSharpnessCoefficient ζ κ x)⁻¹).trace) =
      fun x : Vec d => (d : ℝ) * (scalarSharpnessWeight ζ κ x)⁻¹ := by
        funext x
        exact scalarSharpnessCoefficient_inv_trace hd hζ0 hζ2 hκ x
    rw [heq]
    exact hωi.const_mul _

end

end CoarseDeGiorgi.SharpnessExamples
