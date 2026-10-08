module

public import CoarseDeGiorgi.Harnack.Log.PowerInput
public import CoarseDeGiorgi.Harnack.Log.EnergyLimit
public import CoarseDeGiorgi.Harnack.Log.ContrastFinite
public import CoarseDeGiorgi.Weighted.Identification
public import CoarseDeGiorgi.LowerFractional.MeanCube
public import CoarseDeGiorgi.LowerFractional.CubeDomain
public import CoarseDeGiorgi.LowerFractional.Restriction

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

private theorem originCube_one_volume_eq_one {d : ℕ} :
    volume (originCube (d := d) 1) = 1 := by
  have he : originCube (d := d) 1 =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [he, Real.volume_pi_Ioo]
  norm_num

private theorem originCube_one_domain {d : ℕ} [NeZero d] :
    IsOpenBoundedConvexDomain (originCube (d := d) 1) ∧
      (originCube (d := d) 1).Nonempty := by
  let z : Fin d → ℤ := fun _ => 0
  have he : originCube (d := d) 1 = auxCube 1 z := by
    ext x
    simp [z, originCube, auxCube, sub_self, sub_zero, Int.cast_zero,
      zero_mul, abs_lt]
  constructor
  · rw [he]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain 1 z
  · rw [he]
    exact LowerFractional.auxCube_nonempty 1 z

/-- The source logarithmic energy estimate follows from the power
Caccioppoli contract and the shifted-energy, power-coefficient,
and probability-cube norm limits. -/
theorem log_energy_bound_of_power_input
    (hPower : powerCaccioppoliInputContract) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C_E : ℝ≥0∞, C_E < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              weightedEnergy a (originCube (15 / 16 : ℝ))
                (fun x => (u x + ε)⁻¹ • G x) ≤
                C_E * upperMoment a ha s p hs (le_of_lt hp) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hPowerBound⟩ := hPower d hd p q s t hp hq hs ht hθ
  let widthFactor :=
    (ENNReal.ofReal (1 / 16 : ℝ)).rpow
      (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
        paramTheta d p q s t)
  let C_E := C * widthFactor
  have hwidthTop : widthFactor < ⊤ := by
    dsimp [widthFactor]
    exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_nonneg'
      (by norm_num : 0 < ENNReal.ofReal (1 / 16 : ℝ)) ENNReal.ofReal_ne_top
  have hCE : C_E < ⊤ := by
    dsimp [C_E]
    exact ENNReal.mul_lt_top hC hwidthTop
  refine ⟨C_E, hCE, ?_⟩
  intro a ha hrange u G hnonneg hu ε hε
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hV, hVne⟩ := originCube_one_domain (d := d)
  have hsub : IsWeightedSubsolution a (originCube 1) (-u) (-G) := by
    change IsWeightedSubsolution a (originCube 1) (fun x => -u x) (fun x => -G x)
    exact hu
  have hmemU : MemH1a a (originCube 1) u G := by
    have hneg := Weighted.MemH1a.neg hV hVne ha hsub.1
    simpa only [Pi.neg_apply, neg_neg] using hneg
  have hGTopFull : weightedEnergy a (originCube 1) G < ⊤ :=
    Weighted.MemH1a.energy_lt_top hV.isOpen ha hmemU
  have hcontain : originCube (15 / 16 : ℝ) ⊆ originCube (d := d) 1 := by
    intro x hx i
    have hxi := hx i
    change -(15 / 16 / 2 : ℝ) < x i ∧ x i < 15 / 16 / 2 at hxi
    change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
    constructor <;> nlinarith
  have hGTopInner : weightedEnergy a (originCube (15 / 16 : ℝ)) G < ⊤ := by
    exact lt_of_le_of_lt (LowerFractional.weightedEnergy_mono hcontain G) hGTopFull
  let U : Vec d → ℝ := fun x => u x + ε
  let μ : Measure (Vec d) := volume.restrict (originCube (d := d) 1)
  have hUmeas : AEStronglyMeasurable U μ := by
    dsimp [U, μ]
    exact hmemU.1.add aestronglyMeasurable_const
  have hUlower : ∀ᵐ x ∂μ, ε ≤ U x := by
    filter_upwards [hnonneg] with x hx
    dsimp [U]
    linarith
  have hUnitVolume : volume (originCube (d := d) 1) = 1 :=
    originCube_one_volume_eq_one
  let : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Measure.restrict_apply, hUnitVolume]
  let delta : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let m : ℕ → ℝ := fun n => -delta n
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hm : Tendsto m atTop (𝓝 0) := by
    simpa [m] using hdelta.neg
  have hdeltaPos (n : ℕ) : 0 < delta n := by
    dsimp [delta]
    positivity
  have hdeltaLe (n : ℕ) : delta n ≤ 1 := by
    dsimp [delta]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 n
    exact (div_le_one (by positivity)).2 hn
  have hmlo (n : ℕ) : -1 ≤ m n := by
    dsimp [m]
    linarith [hdeltaLe n]
  have hmhi (n : ℕ) : m n ≤ 0 := by
    dsimp [m]
    linarith [hdeltaPos n]
  have hmne (n : ℕ) : m n ≠ 0 := by
    dsimp [m]
    exact neg_ne_zero.mpr (ne_of_gt (hdeltaPos n))
  have hmhalf (n : ℕ) : m n < 1 / 2 := by
    exact lt_of_le_of_lt (hmhi n) (by norm_num)
  have hp0 : 0 < paramR q := by
    dsimp [paramR]
    positivity
  have hLpLimit := log_shifted_power_norm_tendsto_one ε hε U hUmeas hUlower
    (paramR q) hp0 m hmlo hmhi hm
  have hcontrastTop :
      contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) < ⊤ := by
    exact contrast_lt_top_of_spatialMomentRange a ha p q s t hp hq hs ht hrange
  have hRatioLimit :=
    CoarseDeGiorgi.Harnack.LogLimit.tendsto_powerFactor_sq_div_sq
      m hmhi hmne hm
  have hmSq : Tendsto (fun n => ENNReal.ofReal (m n ^ 2)) atTop (𝓝 0) := by
    have hsquare : Tendsto (fun n => m n ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using hm.pow 2
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsquare
  have hfactorSq : Tendsto (fun n => ENNReal.ofReal (powerFactor (m n) ^ 2))
      atTop (𝓝 0) := by
    have hEq (n : ℕ) : ENNReal.ofReal (powerFactor (m n) ^ 2) =
        ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) *
          ENNReal.ofReal ((m n) ^ 2) := by
      have hratioNonneg : 0 ≤ powerFactor (m n) ^ 2 / (m n) ^ 2 := by positivity
      have hcancel : powerFactor (m n) ^ 2 / (m n) ^ 2 * (m n) ^ 2 =
          powerFactor (m n) ^ 2 :=
        div_mul_cancel₀ _ (pow_ne_zero 2 (hmne n))
      calc
        _ = ENNReal.ofReal
            ((powerFactor (m n) ^ 2 / (m n) ^ 2) * (m n) ^ 2) := by
              rw [hcancel]
        _ = ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) *
            ENNReal.ofReal ((m n) ^ 2) := ENNReal.ofReal_mul hratioNonneg
    have hmul := ENNReal.Tendsto.mul hRatioLimit (by simp) hmSq (by simp)
    have hseq : (fun n => ENNReal.ofReal (powerFactor (m n) ^ 2)) =
        (fun n => ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) *
          ENNReal.ofReal ((m n) ^ 2)) := funext hEq
    rw [hseq]
    simpa using hmul
  let contrastValue := contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)
  have hcontrastSmall : Tendsto
      (fun n => ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul hfactorSq (Or.inr hcontrastTop.ne)
      tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
  let thetaExponent := sigmaParam (d := d) p q s / paramTheta d p q s t
  have hbaseLimit : Tendsto
      (fun n => 1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hcontrastSmall
  have hcontrastFactorLimit : Tendsto
      (fun n => ENNReal.rpow
        (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue) thetaExponent)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.rpow_eq_pow, ENNReal.one_rpow] using
      (ENNReal.continuous_rpow_const (y := thetaExponent)).continuousAt.tendsto.comp
        hbaseLimit
  have hLpSqLimit : Tendsto
      (fun n => (eLpNorm (fun x => U x ^ (m n))
        (ENNReal.ofReal (paramR q)) μ).rpow 2) atTop (𝓝 1) := by
    simpa using hLpLimit.ennrpow_const 2
  let factor : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) *
      ENNReal.rpow (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue) thetaExponent *
      (eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal (paramR q)) μ).rpow 2
  have hFactorLimit : Tendsto factor atTop (𝓝 1) := by
    dsimp [factor]
    have h₁ := ENNReal.Tendsto.mul hRatioLimit (by simp)
      hcontrastFactorLimit (by simp)
    have h₂ := ENNReal.Tendsto.mul h₁ (by simp) hLpSqLimit (by simp)
    simpa using h₂
  let C₀ := C_E * upperMoment a ha s p hs (le_of_lt hp)
  have hRhsLimit : Tendsto (fun n => C₀ * factor n) atTop (𝓝 C₀) := by
    have h := ENNReal.Tendsto.const_mul (a := C₀) hFactorLimit
      (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
    simpa [C₀] using h
  have haInner : IsWeightedCoeffOn (originCube (15 / 16 : ℝ)) a :=
    LowerFractional.weightedCoeffOn_mono ha hcontain
  have hμInner : volume.restrict (originCube (15 / 16 : ℝ)) ≤ μ := by
    dsimp [μ]
    exact Measure.restrict_mono_set volume hcontain
  have hUInner : AEStronglyMeasurable U
      (volume.restrict (originCube (15 / 16 : ℝ))) := hUmeas.mono_measure hμInner
  have hGInner : AEStronglyMeasurable G
      (volume.restrict (originCube (15 / 16 : ℝ))) :=
    hmemU.2.1.mono_measure hμInner
  have hUlowerInner : ∀ᵐ x ∂(volume.restrict (originCube (15 / 16 : ℝ))), ε ≤ U x :=
    hUlower.filter_mono (ae_mono hμInner)
  have hEnergyLimit := log_shifted_power_energy_tendsto haInner U G ε hε
    hUInner hUlowerInner hGInner hGTopInner m hmlo hmhi hm
  let Ediv : ℕ → ℝ≥0∞ := fun n => weightedEnergy a (originCube (15 / 16 : ℝ))
    (fun x => U x ^ (m n - 1) • G x)
  have hBound (n : ℕ) : Ediv n ≤ C₀ * factor n := by
    have hpower := hPowerBound a ha hrange u G hnonneg hu ε hε
      (m n) (hmhalf n) (hmne n) (15 / 16 : ℝ) 1
      (by norm_num) (by norm_num) (by norm_num)
    have hscaledEq : weightedEnergy a (originCube (15 / 16 : ℝ))
        (fun x => (m n * U x ^ (m n - 1)) • G x) =
        ENNReal.ofReal (m n ^ 2) * Ediv n := by
      have hfun : (fun x => (m n * U x ^ (m n - 1)) • G x) =
          (fun x => m n • (U x ^ (m n - 1) • G x)) := by
        funext x
        simp [smul_smul]
      rw [hfun]
      exact CoarseDeGiorgi.Harnack.LogLimit.weightedEnergy_real_smul
        a (originCube (15 / 16 : ℝ))
        (fun x => U x ^ (m n - 1) • G x) (m n)
    have hmSqPos : 0 < (m n) ^ 2 := sq_pos_of_ne_zero (hmne n)
    let X := ENNReal.ofReal (m n ^ 2)
    have hXzero : X ≠ 0 := (ENNReal.ofReal_pos.mpr hmSqPos).ne'
    have hXtop : X ≠ ⊤ := ENNReal.ofReal_ne_top
    have hre : powerFactor (m n) ^ 2 =
        (m n) ^ 2 * (powerFactor (m n) ^ 2 / (m n) ^ 2) := by
      calc
        _ = (powerFactor (m n) ^ 2 / (m n) ^ 2) * (m n) ^ 2 :=
          (div_mul_cancel₀ _ (pow_ne_zero 2 (hmne n))).symm
        _ = _ := mul_comm _ _
    have hpfFactor : ENNReal.ofReal (powerFactor (m n) ^ 2) =
        X * ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) := by
      dsimp [X]
      calc
        _ = ENNReal.ofReal
            ((m n) ^ 2 * (powerFactor (m n) ^ 2 / (m n) ^ 2)) :=
              congrArg ENNReal.ofReal hre
        _ = ENNReal.ofReal ((m n) ^ 2) *
            ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2) :=
              ENNReal.ofReal_mul (sq_nonneg _)
    have hscaledBound : X * Ediv n ≤
        C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2) *
          ENNReal.rpow (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue) thetaExponent *
          (eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal (paramR q)) μ).rpow 2 := by
      rw [← hscaledEq]
      have hgap : (1 : ℝ) - (15 / 16 : ℝ) = 1 / 16 := by norm_num
      rw [hgap] at hpower
      simpa [C₀, C_E, widthFactor, U, μ, contrastValue, thetaExponent, mul_assoc] using hpower
    have hdiv := (ENNReal.div_le_div_right hscaledBound) X
    have hleftCancel : X * Ediv n / X = Ediv n := by
      calc
        X * Ediv n / X = Ediv n * X / X := by ac_rfl
        _ = Ediv n := ENNReal.mul_div_cancel_right hXzero hXtop
    have hrightEq :
        C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2) *
          ENNReal.rpow (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue) thetaExponent *
          (eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal (paramR q)) μ).rpow 2 =
        X * (C₀ * factor n) := by
      have houter : C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2) =
          X * (C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2)) := by
        rw [hpfFactor]
        ac_rfl
      calc
        _ = (C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2)) *
            ENNReal.rpow (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue)
              thetaExponent *
            (eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal (paramR q)) μ).rpow 2 := by
              ac_rfl
        _ = (X * (C₀ * ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2))) *
            ENNReal.rpow (1 + ENNReal.ofReal (powerFactor (m n) ^ 2) * contrastValue)
              thetaExponent *
            (eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal (paramR q)) μ).rpow 2 := by
              rw [houter]
        _ = X * (C₀ * factor n) := by
              dsimp [factor]
              ac_rfl
    have hrightCancel : X * (C₀ * factor n) / X = C₀ * factor n := by
      calc
        X * (C₀ * factor n) / X = (C₀ * factor n) * X / X := by ac_rfl
        _ = C₀ * factor n := ENNReal.mul_div_cancel_right hXzero hXtop
    rw [hleftCancel, hrightEq, hrightCancel] at hdiv
    exact hdiv
  have hlogEnergy : weightedEnergy a (originCube (15 / 16 : ℝ))
      (fun x => (u x + ε)⁻¹ • G x) ≤ C₀ := by
    have htarget : weightedEnergy a (originCube (15 / 16 : ℝ))
        (fun x => U x ^ (-1 : ℝ) • G x) =
        weightedEnergy a (originCube (15 / 16 : ℝ))
          (fun x => (u x + ε)⁻¹ • G x) := by
      congr 2
      funext x
      simp [U, Real.rpow_neg_one]
    rw [← htarget]
    exact le_of_tendsto_of_tendsto' hEnergyLimit hRhsLimit hBound
  simpa [C₀] using hlogEnergy

end

end CoarseDeGiorgi.Harnack.Log
