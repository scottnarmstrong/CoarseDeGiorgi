module

public import Mathlib
public import CoarseDeGiorgi.Statements.LocalBoundedness
public import CoarseDeGiorgi.Statements.MomentBoundsLebesgue
public import CoarseDeGiorgiAudit.Defs
public import CoarseDeGiorgiAudit.DefsCells
public import CoarseDeGiorgiAudit.Solution.Bridge

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.LocalBoundednessLpLq

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

/-- `u` is essentially bounded above on every compact subset of `V`. -/
def LocallyBoundedAbove {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
    ∃ M : ℝ, ∀ᵐ x ∂(volume.restrict K), u x ≤ M

/-- Positive part `u₊ = max(u, 0)`. -/
def positivePart {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => max (u x) 0

/-! ## Integrability margin -/

/-- `θ₀ = 1 − (d−1)(1/p+1/q)/2`, the positive margin in the moment range. -/
noncomputable def theta0 (d : ℕ) (p q : ℝ) : ℝ :=
  1 - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

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

theorem locallyBoundedAbove_iff {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) :
    LocallyBoundedAbove V u ↔
      CoarseDeGiorgiAudit.LocallyBoundedAbove V u := Iff.rfl

theorem positivePart_eq {d : ℕ} (u : Vec d → ℝ) :
    positivePart u = CoarseDeGiorgiAudit.positivePart u := rfl

theorem theta0_eq (d : ℕ) (p q : ℝ) :
    theta0 d p q =
      CoarseDeGiorgiAudit.paramTheta d p q 0 0 := by
  dsimp [theta0, CoarseDeGiorgiAudit.paramTheta]
  ring

theorem localBoundednessLpLq
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hrange : 1 / p + 1 / q < 2 / ((d : ℝ) - 1))
    -- coefficient-growth exponent
    (κ : ℝ) (hκ : ((d : ℝ) - 1) / (4 * theta0 d p q) < κ) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
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
            -- weighted subsolution
            (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (cube 1) u G →
            -- conclusion
            LocallyBoundedAbove (cube 1) u ∧
            ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
              let rhs := ENNReal.ofReal C_A *
                (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                (1 + M).rpow κ *
                eLpNorm (positivePart u) 2 (volume.restrict (cube R))
              eLpNorm (positivePart u) ⊤
                  (volume.restrict (cube ρ)) ≤ rhs ∧
                (R < 1 →
                  eLpNorm (positivePart u) 2
                    (volume.restrict (cube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
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
              -- weighted subsolution
              (u : Vec d → ℝ) (G : Vec d → Vec d),
              IsWeightedSubsolution a (cube 1) u G →
              -- conclusion
              ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                let rhs := ENNReal.ofReal C_η *
                  (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
                  (1 + M).rpow (2 * κ / η) *
                  eLpNorm (positivePart u) (ENNReal.ofReal η)
                    (volume.restrict (cube R))
                eLpNorm (positivePart u) ⊤
                    (volume.restrict (cube ρ)) ≤ rhs ∧
                  (R < 1 →
                    eLpNorm (positivePart u) (ENNReal.ofReal η)
                      (volume.restrict (cube R)) < ⊤))) := by
  have hd1 : 0 < (d : ℝ) - 1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hfac : 0 < ((d : ℝ) - 1) / 2 := by positivity
  have hmul := mul_lt_mul_of_pos_left hrange hfac
  have hcancel : ((d : ℝ) - 1) / 2 * (2 / ((d : ℝ) - 1)) = 1 := by
    field_simp
  have hsum_lt : ((d : ℝ) - 1) / 2 * (1 / p + 1 / q) < 1 := by
    rw [hcancel] at hmul
    exact hmul
  have htheta0 : 0 < theta0 d p q := by
    dsimp [theta0]
    linarith
  have htheta0_root : theta0 d p q = CoarseDeGiorgi.paramTheta d p q 0 0 := by
    rw [theta0_eq]
    rfl
  have hquotient_pos : 0 < ((d : ℝ) - 1) / (4 * theta0 d p q) := by
    exact div_pos hd1 (by positivity)
  have hkappa_pos : 0 < κ := lt_trans hquotient_pos hκ
  let θ : ℝ := ((d : ℝ) - 1) / (4 * κ)
  have hθ : 0 < θ := by
    dsimp [θ]
    exact div_pos hd1 (by positivity)
  have hθ_lt : θ < theta0 d p q := by
    have hden0 : 0 < 4 * theta0 d p q := by positivity
    have hden : 0 < 4 * κ := by positivity
    have hnum : ((d : ℝ) - 1) < κ * (4 * theta0 d p q) :=
      (div_lt_iff₀ hden0).1 hκ
    apply (div_lt_iff₀ hden).2
    calc
      ((d : ℝ) - 1) < κ * (4 * theta0 d p q) := hnum
      _ = theta0 d p q * (4 * κ) := by ring
  let s0 : ℝ := (theta0 d p q - θ) / 2
  have hs0 : 0 < s0 := by
    dsimp [s0]
    exact div_pos (sub_pos.mpr hθ_lt) (by norm_num)
  have hparam_eq : CoarseDeGiorgi.paramTheta d p q s0 s0 = θ := by
    calc
      CoarseDeGiorgi.paramTheta d p q s0 s0 =
          CoarseDeGiorgi.paramTheta d p q 0 0 - 2 * s0 := by
        unfold CoarseDeGiorgi.paramTheta
        ring
      _ = θ := by
        rw [← htheta0_root]
        dsimp [s0]
        ring
  have hparam : 0 < CoarseDeGiorgi.paramTheta d p q s0 s0 := by
    rw [hparam_eq]
    exact hθ
  have hpower_eq :
      ((d : ℝ) - 1) / (4 * CoarseDeGiorgi.paramTheta d p q s0 s0) = κ := by
    rw [hparam_eq]
    dsimp [θ]
    field_simp [ne_of_gt hd1, ne_of_gt hkappa_pos]
  obtain ⟨γ, hγ, hrest⟩ :=
    CoarseDeGiorgi.local_boundedness d hd p q s0 s0 hp hq hs0 hs0 hparam
  obtain ⟨C_A, hC_A, hA⟩ := hrest.1
  refine ⟨γ, hγ, ⟨⟨C_A, hC_A, ?_⟩, ?_⟩⟩
  · intro a ha hLp hInv M u G hsub
    have haChallenge : CoarseDeGiorgiAudit.IsWeightedCoeffOn
        (CoarseDeGiorgiAudit.originCube 1) a := by
      have h := (isWeightedCoeffOn_iff (cube 1) a).mp ha
      simpa only [cube_eq] using h
    have haRoot : CoarseDeGiorgi.IsWeightedCoeffOn
        (CoarseDeGiorgi.originCube 1) a := by
      have h := (CoarseDeGiorgiAudit.isWeightedCoeffOn_iff
        (CoarseDeGiorgiAudit.originCube 1) a).mp haChallenge
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
    have hMroot_eq : Mroot = M := by
      dsimp [Mroot, M]
      simp only [cube_eq, CoarseDeGiorgiAudit.originCube_eq]
    have hmom := CoarseDeGiorgi.moment_bounds_lebesgue d hd p q s0 s0 hp hq hs0 hs0
      a haRoot hLpRoot hInvRoot
    have hup : CoarseDeGiorgi.upperMoment a haRoot s0 p hs0 hp.le < ⊤ :=
      lt_of_le_of_lt hmom.1 hLpRoot
    have hlow : 0 < CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le := by
      have h : (CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le)⁻¹ < ⊤ :=
        lt_of_le_of_lt hmom.2.1 hInvRoot
      exact ENNReal.inv_lt_top.mp h
    have hcontrast_le :
        CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le ≤ Mroot := by
      simpa only [Mroot] using hmom.2.2
    have hsubChallenge : CoarseDeGiorgiAudit.IsWeightedSubsolution
        a (CoarseDeGiorgiAudit.originCube 1) u G := by
      have h := (isWeightedSubsolution_iff a (cube 1) u G).mp hsub
      simpa only [cube_eq] using h
    have hsubRoot : CoarseDeGiorgi.IsWeightedSubsolution
        a (CoarseDeGiorgi.originCube 1) u G := by
      have h := (CoarseDeGiorgiAudit.isWeightedSubsolution_iff
        a (CoarseDeGiorgiAudit.originCube 1) u G).mp hsubChallenge
      simpa only [CoarseDeGiorgiAudit.originCube_eq] using h
    have hcore := hA a haRoot hup hlow u G hsubRoot
    have hlocalChallenge : LocallyBoundedAbove (cube 1) u := by
      apply (locallyBoundedAbove_iff (cube 1) u).2
      have hlocalAudit : CoarseDeGiorgiAudit.LocallyBoundedAbove
          (CoarseDeGiorgiAudit.originCube 1) u := by
        apply (CoarseDeGiorgiAudit.locallyBoundedAbove_iff
          (CoarseDeGiorgiAudit.originCube 1) u).mpr
        simpa only [CoarseDeGiorgiAudit.originCube_eq] using hcore.1
      simpa only [cube_eq] using hlocalAudit
    refine ⟨hlocalChallenge, ?_⟩
    intro ρ R hρ hρR hR
    have hbound0 := hcore.2 ρ R hρ hρR hR
    have hbound :
        eLpNorm (CoarseDeGiorgi.positivePart u) ⊤
            (volume.restrict (CoarseDeGiorgi.originCube ρ)) ≤
          ENNReal.ofReal C_A * (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).rpow κ *
            eLpNorm (CoarseDeGiorgi.positivePart u) 2
              (volume.restrict (CoarseDeGiorgi.originCube R)) := by
      simpa only [hpower_eq] using hbound0.1
    have hbase :
        CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le ≤
          1 + Mroot :=
      le_trans hcontrast_le le_add_self
    have hpow :
        (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).rpow κ ≤
          (1 + Mroot).rpow κ :=
      ENNReal.rpow_le_rpow hbase (le_of_lt hkappa_pos)
    have hfactor := mul_le_mul_of_nonneg_left hpow (by positivity :
      0 ≤ ENNReal.ofReal C_A * (ENNReal.ofReal (R - ρ)).rpow (-γ))
    have hfull := mul_le_mul_of_nonneg_right hfactor (by positivity :
      0 ≤ eLpNorm (CoarseDeGiorgi.positivePart u) 2
        (volume.restrict (CoarseDeGiorgi.originCube R)))
    have hboundFinal := le_trans hbound hfull
    have hfinite :
        R < 1 → eLpNorm (CoarseDeGiorgi.positivePart u) 2
          (volume.restrict (CoarseDeGiorgi.originCube R)) < ⊤ := hbound0.2
    constructor
    · simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq, positivePart_eq,
        CoarseDeGiorgiAudit.positivePart_eq, hMroot_eq] using hboundFinal
    · intro hRlt
      simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq, positivePart_eq,
        CoarseDeGiorgiAudit.positivePart_eq] using hfinite hRlt
  · intro η hη hη2
    obtain ⟨Cη, hCη, hEta⟩ := hrest.2 η hη hη2
    refine ⟨Cη, hCη, ?_⟩
    intro a ha hLp hInv M u G hsub ρ R hρ hρR hR
    have haChallenge : CoarseDeGiorgiAudit.IsWeightedCoeffOn
        (CoarseDeGiorgiAudit.originCube 1) a := by
      have h := (isWeightedCoeffOn_iff (cube 1) a).mp ha
      simpa only [cube_eq] using h
    have haRoot : CoarseDeGiorgi.IsWeightedCoeffOn
        (CoarseDeGiorgi.originCube 1) a := by
      have h := (CoarseDeGiorgiAudit.isWeightedCoeffOn_iff
        (CoarseDeGiorgiAudit.originCube 1) a).mp haChallenge
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
    have hMroot_eq : Mroot = M := by
      dsimp [Mroot, M]
      simp only [cube_eq, CoarseDeGiorgiAudit.originCube_eq]
    have hmom := CoarseDeGiorgi.moment_bounds_lebesgue d hd p q s0 s0 hp hq hs0 hs0
      a haRoot hLpRoot hInvRoot
    have hup : CoarseDeGiorgi.upperMoment a haRoot s0 p hs0 hp.le < ⊤ :=
      lt_of_le_of_lt hmom.1 hLpRoot
    have hlow : 0 < CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le := by
      have h : (CoarseDeGiorgi.lowerMoment a haRoot s0 q hs0 hq.le)⁻¹ < ⊤ :=
        lt_of_le_of_lt hmom.2.1 hInvRoot
      exact ENNReal.inv_lt_top.mp h
    have hcontrast_le :
        CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le ≤ Mroot := by
      simpa only [Mroot] using hmom.2.2
    have hsubChallenge : CoarseDeGiorgiAudit.IsWeightedSubsolution
        a (CoarseDeGiorgiAudit.originCube 1) u G := by
      have h := (isWeightedSubsolution_iff a (cube 1) u G).mp hsub
      simpa only [cube_eq] using h
    have hsubRoot : CoarseDeGiorgi.IsWeightedSubsolution
        a (CoarseDeGiorgi.originCube 1) u G := by
      have h := (CoarseDeGiorgiAudit.isWeightedSubsolution_iff
        a (CoarseDeGiorgiAudit.originCube 1) u G).mp hsubChallenge
      simpa only [CoarseDeGiorgiAudit.originCube_eq] using h
    have hEtaEq :
        ((d : ℝ) - 1) / (2 * η * CoarseDeGiorgi.paramTheta d p q s0 s0) =
          2 * κ / η := by
      rw [hparam_eq]
      dsimp [θ]
      field_simp [ne_of_gt hd1, ne_of_gt hkappa_pos, ne_of_gt hη]
      ring
    have hEtaData := hEta a haRoot hup hlow u G hsubRoot ρ R hρ hρR hR
    have hbound :
        eLpNorm (CoarseDeGiorgi.positivePart u) ⊤
            (volume.restrict (CoarseDeGiorgi.originCube ρ)) ≤
          ENNReal.ofReal Cη * (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
            (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).rpow
              (2 * κ / η) *
            eLpNorm (CoarseDeGiorgi.positivePart u) (ENNReal.ofReal η)
              (volume.restrict (CoarseDeGiorgi.originCube R)) := by
      simpa only [hEtaEq] using hEtaData.1
    have hbase :
        CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le ≤
          1 + Mroot :=
      le_trans hcontrast_le le_add_self
    have hexp : 0 ≤ 2 * κ / η := by positivity
    have hpow :
        (CoarseDeGiorgi.contrast a haRoot s0 s0 p q hs0 hs0 hp.le hq.le).rpow
            (2 * κ / η) ≤ (1 + Mroot).rpow (2 * κ / η) :=
      ENNReal.rpow_le_rpow hbase hexp
    have hfactor := mul_le_mul_of_nonneg_left hpow (by positivity :
      0 ≤ ENNReal.ofReal Cη * (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)))
    have hfull := mul_le_mul_of_nonneg_right hfactor (by positivity :
      0 ≤ eLpNorm (CoarseDeGiorgi.positivePart u) (ENNReal.ofReal η)
        (volume.restrict (CoarseDeGiorgi.originCube R)))
    have hboundFinal := le_trans hbound hfull
    have hfinite :
        R < 1 → eLpNorm (CoarseDeGiorgi.positivePart u) (ENNReal.ofReal η)
          (volume.restrict (CoarseDeGiorgi.originCube R)) < ⊤ := hEtaData.2
    constructor
    · simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq, positivePart_eq,
        CoarseDeGiorgiAudit.positivePart_eq, hMroot_eq] using hboundFinal
    · intro hRlt
      simpa only [cube_eq, CoarseDeGiorgiAudit.originCube_eq, positivePart_eq,
        CoarseDeGiorgiAudit.positivePart_eq] using hfinite hRlt

end CoarseDeGiorgiAudit.LocalBoundednessLpLq
