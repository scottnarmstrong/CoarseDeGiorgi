module

public import Mathlib
public import CoarseDeGiorgi.Statements.WeakHarnackRange
public import CoarseDeGiorgi.Statements.MomentBoundsLebesgue
public import CoarseDeGiorgiAudit.Defs
public import CoarseDeGiorgiAudit.Solution.Bridge

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.WeakHarnackLpLq

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

/-- A weighted subsolution has nonpositive flux pairing with every nonnegative
smooth compactly supported test: `∫_V ∇φ · a∇u ≤ 0`. -/
noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V,
        smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume ≤ 0

/-- `u` is a weighted supersolution when `-u` is a weighted subsolution. -/
noncomputable def IsWeightedSupersolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  IsWeightedSubsolution a V (fun x => -u x) (fun x => -G x)

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

/-- Normalized `Lᵇ` moment `(|V|⁻¹ ∫_V |u|ᵇ)^(1/b)`.
Used with `b = η > 0`. -/
noncomputable def normalizedLpMoment {d : ℕ} (b : ℝ)
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow b).rpow (1 / b)

/-! ## The theorem -/

end ChallengeCopies

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
theorem isWeightedSubsolution_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSubsolution a V u G ↔
      CoarseDeGiorgiAudit.IsWeightedSubsolution a V u G := Iff.rfl
theorem isWeightedSupersolution_iff {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) :
    IsWeightedSupersolution a V u G ↔
      CoarseDeGiorgiAudit.IsWeightedSupersolution a V u G := Iff.rfl
theorem essInfNonneg_eq {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    essInfNonneg V u = CoarseDeGiorgiAudit.nonnegativeEssInf V u := rfl
theorem normalizedLpMoment_eq {d : ℕ} (b : ℝ) (hb : 0 < b)
    (V : Set (Vec d)) (u : Vec d → ℝ) :
    normalizedLpMoment b V u =
      CoarseDeGiorgiAudit.normalizedLpMoment b hb V u := rfl
theorem weakHarnackLpLq
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hrange : 1 / p + 1 / q < 2 / ((d : ℝ) - 1)) :
    -- exponent: 0 < η < dq/(dq + d − 2q), the value of r*/2 at t = 0
    ∀ η : ℝ, 0 < η → η < (d : ℝ) * q / ((d : ℝ) * q + (d : ℝ) - 2 * q) →
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
          -- nonnegative weighted supersolution
          (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (cube 1) u G →
          -- conclusion
          normalizedLpMoment η (cube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt M.toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  intro η hη hηlt
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hfac : 0 < ((d : ℝ) - 1) / 2 := by positivity
  let theta0 : ℝ := 1 - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)
  have htheta0 : 0 < theta0 := by
    dsimp [theta0]
    have hmul := mul_lt_mul_of_pos_left hrange hfac
    have hcancel : ((d : ℝ) - 1) / 2 * (2 / ((d : ℝ) - 1)) = 1 := by
      field_simp
    nlinarith
  -- choose `t0 > 0` so small that `η ≤ r*(t0)/2` (Theorem D(i) allows every `t > 0`)
  have hq0 : 0 < q := by linarith
  have hden : 0 < (d : ℝ) * q + (d : ℝ) - 2 * q := by nlinarith
  let X : ℝ := (d : ℝ) * q - η * ((d : ℝ) * q + (d : ℝ) - 2 * q)
  have hX : 0 < X := by
    have h := (lt_div_iff₀ hden).mp hηlt
    dsimp [X]
    linarith
  let s0 : ℝ := theta0 / 4
  let t0 : ℝ := min (theta0 / 4) (X / (2 * η * q))
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  have ht0 : 0 < t0 := lt_min (by positivity) (by positivity)
  have ht0θ : t0 ≤ theta0 / 4 := min_le_left _ _
  have ht0X : t0 ≤ X / (2 * η * q) := min_le_right _ _
  have hparam : 0 < CoarseDeGiorgi.paramTheta d p q s0 t0 := by
    have hsplit : CoarseDeGiorgi.paramTheta d p q s0 t0 = theta0 - s0 - t0 := by
      unfold CoarseDeGiorgi.paramTheta
      dsimp [s0, theta0]
      ring
    rw [hsplit]
    dsimp [s0]
    linarith
  have hηr : η ≤ CoarseDeGiorgi.rStarParam (d := d) q t0 / 2 := by
    have hkey : 2 * η * q * t0 ≤ X := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * η * q)).mp ht0X
      linarith
    have hden' : 0 < (d : ℝ) * q + (d : ℝ) - 2 * q + 2 * q * t0 := by
      have := mul_pos hq0 ht0
      linarith
    have hq1 : q + 1 ≠ 0 := by linarith
    have hval : CoarseDeGiorgi.rStarParam (d := d) q t0 / 2 =
        (d : ℝ) * q / ((d : ℝ) * q + (d : ℝ) - 2 * q + 2 * q * t0) := by
      unfold CoarseDeGiorgi.rStarParam CoarseDeGiorgi.paramR CoarseDeGiorgi.alphaParam
      have hD : (d : ℝ) - (1 - t0) * (2 * q / (q + 1)) =
          ((d : ℝ) * q + (d : ℝ) - 2 * q + 2 * q * t0) / (q + 1) := by
        field_simp
        ring
      simp only [hD]
      field_simp
    rw [hval, le_div_iff₀ hden']
    dsimp [X] at hkey
    nlinarith [hkey]
  obtain ⟨Cw, hCw, hweak⟩ :=
    CoarseDeGiorgi.weak_harnack_range d hd p q s0 t0 hp hq hs0 ht0 hparam η hη hηr
  refine ⟨Cw, hCw, ?_⟩
  intro a ha hLp hInv M u G hu hsuper
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
  have hmom := CoarseDeGiorgi.moment_bounds_lebesgue d hd p q s0 t0 hp hq hs0 ht0
    a haRoot hLpRoot hInvRoot
  have hcontrast_le :
      (CoarseDeGiorgi.contrast a haRoot s0 t0 p q hs0 ht0 hp.le hq.le) ≤ Mroot := by
    simpa only [Mroot] using hmom.2.2
  have hup : CoarseDeGiorgi.upperMoment a haRoot s0 p hs0 hp.le < ⊤ :=
    lt_of_le_of_lt hmom.1 hLpRoot
  have hlow : 0 < CoarseDeGiorgi.lowerMoment a haRoot t0 q ht0 hq.le := by
    have h : (CoarseDeGiorgi.lowerMoment a haRoot t0 q ht0 hq.le)⁻¹ < ⊤ :=
      lt_of_le_of_lt hmom.2.1 hInvRoot
    exact ENNReal.inv_lt_top.mp h
  have hweakRoot := hweak a haRoot hup hlow u G
      (by simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq] using hu)
      ((CoarseDeGiorgiAudit.isWeightedSupersolution_iff
        a (CoarseDeGiorgiAudit.originCube 1) u G).mp
        (by
          have h := (isWeightedSupersolution_iff a (cube 1) u G).mp hsuper
          simpa only [cube_eq] using h))
  have hMomentEq : normalizedLpMoment η (cube (5 / 8)) u =
      CoarseDeGiorgi.normalizedLpMoment η hη (CoarseDeGiorgi.originCube (5 / 8)) u := by
    calc
      normalizedLpMoment η (cube (5 / 8)) u =
          CoarseDeGiorgiAudit.normalizedLpMoment η hη (cube (5 / 8)) u :=
        normalizedLpMoment_eq η hη (cube (5 / 8)) u
      _ = CoarseDeGiorgiAudit.normalizedLpMoment η hη
            (CoarseDeGiorgiAudit.originCube (5 / 8)) u := by
        rw [cube_eq]
      _ = CoarseDeGiorgi.normalizedLpMoment η hη
            (CoarseDeGiorgi.originCube (5 / 8)) u :=
        CoarseDeGiorgiAudit.normalizedLpMoment_eq η hη
          (CoarseDeGiorgiAudit.originCube (5 / 8)) u
  have hInfNonneg : 0 ≤ essInfNonneg (cube (1 / 2)) u := by
    rw [essInfNonneg_eq, CoarseDeGiorgiAudit.nonnegativeEssInf_eq]
    exact bot_le
  have hMroot_eq : Mroot = M := by
    dsimp [Mroot, M]
    simp only [cube_eq, CoarseDeGiorgiAudit.originCube_eq]
  have hcontrast_real :
      (CoarseDeGiorgi.contrast a haRoot s0 t0 p q hs0 ht0 hp.le hq.le).toReal ≤
        Mroot.toReal := by
    apply ENNReal.toReal_mono hMroot_top.ne
    exact hcontrast_le
  have hsqrt := Real.sqrt_le_sqrt hcontrast_real
  have hexp : Real.exp (Cw * Real.sqrt
      (CoarseDeGiorgi.contrast a haRoot s0 t0 p q hs0 ht0 hp.le hq.le).toReal) ≤
        Real.exp (Cw * Mroot.toReal.sqrt) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt hCw
  have hweakBoundLocal : normalizedLpMoment η (cube (5 / 8)) u ≤
      ENNReal.ofReal (Real.exp (Cw *
        Real.sqrt (CoarseDeGiorgi.contrast a haRoot s0 t0 p q hs0 ht0 hp.le hq.le).toReal)) *
        essInfNonneg (cube (1 / 2)) u := by
    rw [hMomentEq]
    simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq,
      essInfNonneg_eq, CoarseDeGiorgiAudit.nonnegativeEssInf_eq] using hweakRoot
  have hmult := mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal hexp) hInfNonneg
  have hweakBound' := le_trans hweakBoundLocal hmult
  simpa only [hMroot_eq] using hweakBound'

end CoarseDeGiorgiAudit.WeakHarnackLpLq
