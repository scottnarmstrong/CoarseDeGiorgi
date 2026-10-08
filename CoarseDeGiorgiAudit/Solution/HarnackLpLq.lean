import Mathlib
import CoarseDeGiorgi.Statements.Harnack
import CoarseDeGiorgi.Statements.MomentBoundsLebesgue
import CoarseDeGiorgiAudit.Defs
import CoarseDeGiorgiAudit.Solution.Bridge

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.HarnackLpLq

section ChallengeCopies

attribute [-instance] Homogenization.instMeasurableSpaceVec

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def cube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}


/-! ## Coefficient fields -/

/-- A coefficient field: a `d × d` matrix at each point (no regularity is assumed here). -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Coefficients are measurable and positive definite a.e.
Their trace and inverse trace are integrable on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)


/-! ## Averages and energies -/

/-- Weighted energy `∫_U G · aG` of a vector field `G` (for `G = ∇u`, the energy of `u`),
as an extended nonnegative real. -/
noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (G x ⬝ᵥ (a x *ᵥ G x))

/-- Normalized average `⨍_U f = |U|⁻¹ ∫_U f`. -/
noncomputable def averageOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume


/-! ## The weighted space `H¹ₐ` -/

/-- Coordinate gradient of a smooth function: `(∇φ x)ᵢ = Dφ(x)eᵢ`. -/
noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (Pi.single i (1 : ℝ))

/-- A smooth core function is `C^∞` on `V`, integrable on `V`, and has finite weighted energy. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy.
Approximants converge in `L¹` on compact subsets and gradients in weighted energy. -/
noncomputable def MemH1a {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  AEStronglyMeasurable u (volume.restrict V) ∧
  AEStronglyMeasurable G (volume.restrict V) ∧
  ∃ φ : ℕ → Vec d → ℝ,
    (∀ n, IsSmoothCore a V (φ n)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        ENNReal.ofReal ((averageOn V (fun x => φ n x - φ m x)) ^ 2) +
          weightedEnergy a V
            (fun x => smoothGrad (φ n) x - smoothGrad (φ m) x) <
          ENNReal.ofReal ε) ∧
    (∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      Filter.Tendsto
        (fun n => ∫⁻ x in K, ‖φ n x - u x‖ₑ)
        Filter.atTop (nhds (0 : ENNReal))) ∧
    Filter.Tendsto
      (fun n => weightedEnergy a V (fun x => smoothGrad (φ n) x - G x))
      Filter.atTop (nhds (0 : ENNReal))


/-! ## Subsolutions, supersolutions, and solutions -/

/-- A weighted solution has zero flux pairing with every smooth compactly
supported test: `∫_V ∇φ · a∇u = 0`. -/
noncomputable def IsWeightedSolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V,
        smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume = 0


/-! ## Norms, moments, and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

end ChallengeCopies

/-! ## The theorem -/

theorem vec_type_eq (d : ℕ) : Vec d = CoarseDeGiorgiAudit.Vec d := rfl
theorem mat_type_eq (d : ℕ) : Mat d = CoarseDeGiorgiAudit.Mat d := rfl
theorem coeffField_type_eq (d : ℕ) :
    CoeffField d = CoarseDeGiorgiAudit.CoeffField d := rfl
theorem cube_eq {d : ℕ} (ρ : ℝ) :
    cube (d := d) ρ = CoarseDeGiorgiAudit.originCube ρ := rfl
theorem weightedEnergy_eq {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) :
    weightedEnergy a U G = CoarseDeGiorgiAudit.weightedEnergy a U G := rfl
theorem averageOn_eq {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    averageOn U f = CoarseDeGiorgiAudit.volumeAverage U f := rfl
theorem smoothGrad_eq {d : ℕ} (φ : Vec d → ℝ) :
    smoothGrad φ = CoarseDeGiorgiAudit.smoothGrad φ := rfl
theorem isSmoothCore_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) :
    IsSmoothCore a V φ ↔ CoarseDeGiorgiAudit.IsSmoothCore a V φ := Iff.rfl
theorem memH1a_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    MemH1a a V u G ↔ CoarseDeGiorgiAudit.MemH1a a V u G := Iff.rfl
theorem isWeightedCoeffOn_iff {d : ℕ} (V : Set (Vec d))
    (a : CoeffField d) :
    IsWeightedCoeffOn V a ↔ CoarseDeGiorgiAudit.IsWeightedCoeffOn V a := Iff.rfl
theorem isWeightedSolution_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSolution a V u G ↔
      CoarseDeGiorgiAudit.IsWeightedSolution a V u G := Iff.rfl
theorem essInfNonneg_eq {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    essInfNonneg V u = CoarseDeGiorgiAudit.nonnegativeEssInf V u := rfl

theorem harnackLpLq
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hrange : 1 / p + 1 / q < 2 / ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- coefficient field and coefficient moments
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
          (volume.restrict (cube 1)) < ⊤ →
        eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
          (volume.restrict (cube 1)) < ⊤ →
        let M : ℝ≥0∞ :=
          eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
            (volume.restrict (cube 1)) *
          eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
            (volume.restrict (cube 1))
        ∀
          -- nonnegative weighted solution
        (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSolution a (cube 1) u G →
          -- conclusion
          eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt M.toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  let theta0 : ℝ := 1 - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)
  have hd1 : 0 < (d : ℝ) - 1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hfac : 0 < ((d : ℝ) - 1) / 2 := by positivity
  have htheta0 : 0 < theta0 := by
    dsimp [theta0]
    have hmul := mul_lt_mul_of_pos_left hrange hfac
    have hcancel : ((d : ℝ) - 1) / 2 * (2 / ((d : ℝ) - 1)) = 1 := by
      field_simp
    nlinarith
  let s0 : ℝ := theta0 / 4
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  have hparam_eq : CoarseDeGiorgi.paramTheta d p q s0 s0 = theta0 / 2 := by
    unfold CoarseDeGiorgi.paramTheta
    dsimp [s0, theta0]
    ring
  have hparam : 0 < CoarseDeGiorgi.paramTheta d p q s0 s0 := by
    rw [hparam_eq]
    positivity
  obtain ⟨C, hC, hroot⟩ :=
    CoarseDeGiorgi.harnack d hd p q s0 s0 hp hq hs0 hs0 hparam
  refine ⟨C, hC, ?_⟩
  intro a ha hLp hInv M u G hu hsol
  have haAudit : CoarseDeGiorgiAudit.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.originCube 1) a := by
    have h := (isWeightedCoeffOn_iff (cube 1) a).mp ha
    simpa only [cube_eq] using h
  have haRoot : CoarseDeGiorgi.IsWeightedCoeffOn
      (CoarseDeGiorgi.originCube 1) a := by
    have h := (CoarseDeGiorgiAudit.isWeightedCoeffOn_iff
      (CoarseDeGiorgiAudit.originCube 1) a).mp haAudit
    simpa only [CoarseDeGiorgiAudit.originCube_eq] using h
  have hLpRoot : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (CoarseDeGiorgi.originCube 1)) < ⊤ := by
    simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq] using hLp
  have hInvRoot : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (CoarseDeGiorgi.originCube 1)) < ⊤ := by
    simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq] using hInv
  let Mroot : ℝ≥0∞ :=
    eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (CoarseDeGiorgi.originCube 1)) *
    eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (CoarseDeGiorgi.originCube 1))
  have hMroot_top : Mroot < ⊤ := by
    dsimp [Mroot]
    exact ENNReal.mul_lt_top hLpRoot hInvRoot
  have hmom := CoarseDeGiorgi.moment_bounds_lebesgue d hd p q s0 s0 hp hq hs0 hs0
    a haRoot hLpRoot hInvRoot
  have hcontrast := hmom.2.2
  have hup : CoarseDeGiorgi.upperMoment a haRoot s0 p hs0 hp.le < ⊤ :=
    lt_of_le_of_lt hmom.1 hLpRoot
  have hlow : 0 < CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le := by
    have h : (CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le)⁻¹ < ⊤ :=
      lt_of_le_of_lt hmom.2.1 hInvRoot
    exact ENNReal.inv_lt_top.mp h
  have hcontrast_real :
      (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).toReal ≤
        Mroot.toReal := by
    apply ENNReal.toReal_mono hMroot_top.ne
    exact hcontrast
  have hsqrt := Real.sqrt_le_sqrt hcontrast_real
  have hexp : Real.exp (C * Real.sqrt
      (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).toReal) ≤
        Real.exp (C * Mroot.toReal.sqrt) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt hC
  have huRoot : ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube 1)), 0 ≤ u x := by
    simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq] using hu
  have hsolAudit : CoarseDeGiorgiAudit.IsWeightedSolution a
      (CoarseDeGiorgiAudit.originCube 1) u G := by
    have h := (isWeightedSolution_iff a (cube 1) u G).mp hsol
    simpa only [cube_eq] using h
  have hsolRoot : CoarseDeGiorgi.IsWeightedSolution a
      (CoarseDeGiorgi.originCube 1) u G :=
    (CoarseDeGiorgiAudit.isWeightedSolution_iff
      a (CoarseDeGiorgiAudit.originCube 1) u G).mp hsolAudit
  have hroot_bound := hroot a haRoot hup hlow u G huRoot hsolRoot
  have hessInf_nonneg : 0 ≤ essInfNonneg (cube (1 / 2)) u := by
    rw [essInfNonneg_eq, CoarseDeGiorgiAudit.nonnegativeEssInf_eq]
    exact bot_le
  have hfinal := mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal hexp) hessInf_nonneg
  have hroot_bound' :
      eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
        ENNReal.ofReal (Real.exp (C * Mroot.toReal.sqrt)) *
          essInfNonneg (cube (1 / 2)) u := by
    simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq,
      essInfNonneg_eq, CoarseDeGiorgiAudit.nonnegativeEssInf_eq] using
      (le_trans hroot_bound hfinal)
  have hM_eq : Mroot =
      eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (cube 1)) *
      eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (cube 1)) := by
    dsimp [Mroot]
    simp only [cube_eq, CoarseDeGiorgiAudit.originCube_eq]
  simpa only [hM_eq] using hroot_bound'

end CoarseDeGiorgiAudit.HarnackLpLq
