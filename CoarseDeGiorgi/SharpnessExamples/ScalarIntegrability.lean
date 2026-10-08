import CoarseDeGiorgi.SharpnessExamples.ScalarBandGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private def scalarBandsInCube {d : ℕ} (n : ℕ) (ζ κ : ℝ) : Set (Vec d) :=
  (scalarCoreBand n ζ κ ∩ originCube 1) ∪
    (scalarAnnulusBand n ζ κ ∩ originCube 1)

private theorem originCube_one_measurable {d : ℕ} :
    MeasurableSet (originCube (d := d) 1) := by
  have hcube : originCube (d := d) 1 =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [CoarseDeGiorgi.originCube]
  rw [hcube]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

private theorem scalarBandsInCube_measurable {d : ℕ} (n : ℕ) (ζ κ : ℝ) :
    MeasurableSet (scalarBandsInCube (d := d) n ζ κ) := by
  unfold scalarBandsInCube
  exact (scalarCoreBand_measurable n ζ κ).inter originCube_one_measurable |>.union
    ((scalarAnnulusBand_measurable n ζ κ).inter originCube_one_measurable)

private theorem scalarBandsInCube_subset_tube {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    scalarBandsInCube (d := d) n ζ κ ⊆
      {x | transverseNorm (x - cylinderCenter (cylinderB n)) <
        2 * cylinderRadius d n ζ κ} ∩ originCube 1 := by
  rintro x (⟨hcore, hcube⟩ | ⟨hann, hcube⟩)
  · have heps := (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1
    change transverseNorm (x - cylinderCenter (cylinderB n)) <
      cylinderRadius d n ζ κ at hcore
    exact ⟨hcore.trans (by nlinarith [heps]), hcube⟩
  · exact ⟨hann.2, hcube⟩

private theorem scalarBandsInCube_volume_toReal_bound {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    (volume (scalarBandsInCube (d := d) n ζ κ)).toReal ≤
      (4 * cylinderRadius d n ζ κ) ^ (d - 1) := by
  let m := d - 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmeasure : volume (scalarBandsInCube (d := d) n ζ κ) ≤
      volume ({x : Vec d | transverseNorm (x - cylinderCenter (cylinderB n)) <
        2 * cylinderRadius d n ζ κ} ∩ originCube 1) :=
    measure_mono (scalarBandsInCube_subset_tube hd hζ0 hζ2 hκ n)
  have hcubeTop : volume (originCube (d := d) 1) ≠ ⊤ := by
    rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one d]
    simp
  have htubeTop : volume ({x : Vec d | transverseNorm
      (x - cylinderCenter (cylinderB n)) < 2 * cylinderRadius d n ζ κ} ∩
      originCube 1) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hcubeTop (measure_mono Set.inter_subset_right)
  have hmono := ENNReal.toReal_mono htubeTop hmeasure
  have hbound := scalarTubeBand_volume_bound (m := m) (k := n) hm hζ0 hζ2 hκ
  have hbound' : (volume ({x : Vec d | transverseNorm
      (x - cylinderCenter (cylinderB n)) < 2 * cylinderRadius d n ζ κ} ∩
      originCube 1)).toReal ≤ (4 * cylinderRadius d n ζ κ) ^ m := by
    have hdim : d - 1 + 1 = d := Nat.sub_add_cancel (by omega : 1 ≤ d)
    rw [hdim] at hbound
    exact hbound
  exact hmono.trans hbound'

private theorem scalarBandsInCube_measure_lt_top {d : ℕ}
    (n : ℕ) (ζ κ : ℝ) : volume (scalarBandsInCube (d := d) n ζ κ) ≠ ⊤ := by
  have hcubeTop : volume (originCube (d := d) 1) ≠ ⊤ := by
    rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one d]
    simp
  apply ne_top_of_le_ne_top hcubeTop
  apply measure_mono
  intro x hx
  unfold scalarBandsInCube at hx
  rcases hx with ⟨_, hcube⟩ | ⟨_, hcube⟩
  · exact hcube
  · exact hcube

private theorem scalarBands_subset_iUnion {d : ℕ} (ζ κ : ℝ) :
    (⋃ n : ℕ, scalarBandsInCube (d := d) n ζ κ) ⊆ originCube 1 := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
  unfold scalarBandsInCube at hn
  rcases hn with ⟨_, hcube⟩ | ⟨_, hcube⟩
  · exact hcube
  · exact hcube

private theorem scalarWeight_bound_on_bands {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (n : ℕ) {x : Vec d} (hx : x ∈ scalarBandsInCube n ζ κ) :
    ‖scalarSharpnessWeight ζ κ x‖ ≤ scalarCoreValue d n ζ κ := by
  have hdata := cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)
  have hplus := hdata.2.2.1
  have hpluspos : 0 < scalarCoreValue d n ζ κ := by
    unfold scalarCoreValue
    exact mul_pos (cylinderB_pos n) (Real.rpow_pos_of_pos hdata.1 _)
  rcases hx with ⟨hcore, _⟩ | ⟨hann, _⟩
  · rw [scalarSharpnessWeight_eq_core hd hζ0 hζ2 hκ hcore]
    simp [Real.norm_eq_abs, abs_of_pos hpluspos]
  · rw [scalarSharpnessWeight_eq_annulus hd hζ0 hζ2 hκ hann]
    have hminuspos : 0 < scalarAnnulusValue d n ζ κ := by
      unfold scalarAnnulusValue
      exact mul_pos (inv_pos.mpr (cylinderB_pos n)) (Real.rpow_pos_of_pos hdata.1 _)
    have hminusle : scalarAnnulusValue d n ζ κ ≤ 1 := hdata.2.2.2.1
    simp [Real.norm_eq_abs, abs_of_pos hminuspos]
    exact hminusle.trans hplus

private theorem scalarInvWeight_bound_on_bands {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (n : ℕ) {x : Vec d} (hx : x ∈ scalarBandsInCube n ζ κ) :
    ‖(scalarSharpnessWeight ζ κ x)⁻¹‖ ≤
      (scalarAnnulusValue d n ζ κ)⁻¹ := by
  have hdata := cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)
  have hminuspos : 0 < scalarAnnulusValue d n ζ κ := by
    unfold scalarAnnulusValue
    exact mul_pos (inv_pos.mpr (cylinderB_pos n)) (Real.rpow_pos_of_pos hdata.1 _)
  rcases hx with ⟨hcore, _⟩ | ⟨hann, _⟩
  · rw [scalarSharpnessWeight_eq_core hd hζ0 hζ2 hκ hcore]
    have hpluspos : 0 < scalarCoreValue d n ζ κ := by
      unfold scalarCoreValue
      exact mul_pos (cylinderB_pos n) (Real.rpow_pos_of_pos hdata.1 _)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpluspos)]
    exact ((inv_le_one₀ hpluspos).2 hdata.2.2.1).trans
      ((one_le_inv₀ hminuspos).2 hdata.2.2.2.1)
  · rw [scalarSharpnessWeight_eq_annulus hd hζ0 hζ2 hκ hann]
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr hminuspos)]

private theorem scalarWeight_integrableOn_bands {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    IntegrableOn (scalarSharpnessWeight (d := d) ζ κ) (scalarBandsInCube n ζ κ) volume := by
  have htop := scalarBandsInCube_measure_lt_top (d := d) n ζ κ
  have hconst : IntegrableOn (fun _ : Vec d => scalarCoreValue d n ζ κ)
      (scalarBandsInCube n ζ κ) volume := integrableOn_const htop
  refine hconst.mono' (scalarSharpnessWeight_measurable ζ κ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (scalarBandsInCube_measurable n ζ κ)] with x hx
  have hpluspos : 0 < scalarCoreValue d n ζ κ := by
    unfold scalarCoreValue
    exact mul_pos (cylinderB_pos n)
      (Real.rpow_pos_of_pos (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1 _)
  simpa [Real.norm_eq_abs, abs_of_pos hpluspos] using
    scalarWeight_bound_on_bands hd hζ0 hζ2 hκ n hx

private theorem scalarInvWeight_integrableOn_bands {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    IntegrableOn (fun x => (scalarSharpnessWeight (d := d) ζ κ x)⁻¹)
      (scalarBandsInCube n ζ κ) volume := by
  have htop := scalarBandsInCube_measure_lt_top (d := d) n ζ κ
  have hconst : IntegrableOn (fun _ : Vec d => (scalarAnnulusValue d n ζ κ)⁻¹)
      (scalarBandsInCube n ζ κ) volume := integrableOn_const htop
  have hmeas : Measurable (fun x : Vec d => (scalarSharpnessWeight ζ κ x)⁻¹) :=
    (scalarSharpnessWeight_measurable ζ κ).inv
  have hminuspos : 0 < scalarAnnulusValue d n ζ κ := by
    unfold scalarAnnulusValue
    exact mul_pos (inv_pos.mpr (cylinderB_pos n))
      (Real.rpow_pos_of_pos (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1 _)
  refine hconst.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (scalarBandsInCube_measurable n ζ κ)] with x hx
  have hbound := scalarInvWeight_bound_on_bands hd hζ0 hζ2 hκ n hx
  simpa [Real.norm_eq_abs, abs_of_pos hminuspos]
    using hbound

private theorem scalarBands_integral_norm_bound {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    (∫ x in scalarBandsInCube (d := d) n ζ κ,
      ‖scalarSharpnessWeight ζ κ x‖ ∂volume) ≤
        scalarCoreValue d n ζ κ *
          (4 * cylinderRadius d n ζ κ) ^ (d - 1) := by
  have hfn := scalarWeight_integrableOn_bands hd hζ0 hζ2 hκ n
  have htop := scalarBandsInCube_measure_lt_top (d := d) n ζ κ
  have hconst : IntegrableOn (fun _ : Vec d => scalarCoreValue d n ζ κ)
      (scalarBandsInCube n ζ κ) volume := integrableOn_const htop
  have hpluspos : 0 < scalarCoreValue d n ζ κ := by
    unfold scalarCoreValue
    exact mul_pos (cylinderB_pos n)
      (Real.rpow_pos_of_pos (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1 _)
  have hbound : ∀ᵐ x ∂volume.restrict (scalarBandsInCube n ζ κ),
      ‖scalarSharpnessWeight ζ κ x‖ ≤
        ‖(fun _ : Vec d => scalarCoreValue d n ζ κ) x‖ := by
    filter_upwards [ae_restrict_mem (scalarBandsInCube_measurable n ζ κ)] with x hx
    simpa [Real.norm_eq_abs, abs_of_pos hpluspos] using
      scalarWeight_bound_on_bands hd hζ0 hζ2 hκ n hx
  have hmono := integral_mono_ae hfn.norm hconst.norm hbound
  have hconstEval : (∫ x in scalarBandsInCube (d := d) n ζ κ,
      ‖scalarCoreValue d n ζ κ‖ ∂volume) =
      scalarCoreValue d n ζ κ *
        (volume (scalarBandsInCube (d := d) n ζ κ)).toReal := by
    simp [integral_const, measureReal_def, smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos hpluspos]
    ring
  have hvol := scalarBandsInCube_volume_toReal_bound hd hζ0 hζ2 hκ n
  have hpluspos : 0 ≤ scalarCoreValue d n ζ κ := by
    exact le_of_lt (by
      unfold scalarCoreValue
      exact mul_pos (cylinderB_pos n)
        (Real.rpow_pos_of_pos (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1 _))
  rw [hconstEval] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hvol hpluspos)

private theorem scalarInvBands_integral_norm_bound {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    (∫ x in scalarBandsInCube (d := d) n ζ κ,
      ‖(scalarSharpnessWeight ζ κ x)⁻¹‖ ∂volume) ≤
        (scalarAnnulusValue d n ζ κ)⁻¹ *
          (4 * cylinderRadius d n ζ κ) ^ (d - 1) := by
  have hf := scalarInvWeight_integrableOn_bands hd hζ0 hζ2 hκ n
  have htop := scalarBandsInCube_measure_lt_top (d := d) n ζ κ
  have hconst : IntegrableOn (fun _ : Vec d => (scalarAnnulusValue d n ζ κ)⁻¹)
      (scalarBandsInCube n ζ κ) volume := integrableOn_const htop
  have hvol := scalarBandsInCube_volume_toReal_bound hd hζ0 hζ2 hκ n
  have hminuspos : 0 < scalarAnnulusValue d n ζ κ := by
    unfold scalarAnnulusValue
    exact mul_pos (inv_pos.mpr (cylinderB_pos n))
      (Real.rpow_pos_of_pos (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1 _)
  have hbound : ∀ᵐ x ∂volume.restrict (scalarBandsInCube n ζ κ),
      ‖(scalarSharpnessWeight ζ κ x)⁻¹‖ ≤
        ‖(fun _ : Vec d => (scalarAnnulusValue d n ζ κ)⁻¹) x‖ := by
    filter_upwards [ae_restrict_mem (scalarBandsInCube_measurable n ζ κ)] with x hx
    simpa [Real.norm_eq_abs, abs_of_pos hminuspos] using
      scalarInvWeight_bound_on_bands hd hζ0 hζ2 hκ n hx
  have hconstEval : (∫ x in scalarBandsInCube (d := d) n ζ κ,
      ‖(scalarAnnulusValue d n ζ κ)⁻¹‖ ∂volume) =
      (scalarAnnulusValue d n ζ κ)⁻¹ *
        (volume (scalarBandsInCube (d := d) n ζ κ)).toReal := by
    simp [integral_const, measureReal_def, smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos hminuspos]
    ring
  have hpos : 0 ≤ (scalarAnnulusValue d n ζ κ)⁻¹ := inv_nonneg.mpr hminuspos.le
  have hmono := integral_mono_ae hf.norm hconst.norm hbound
  rw [hconstEval] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hvol hpos)

private theorem scalarCoreIntegral_bound {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    scalarCoreValue d n ζ κ *
      (4 * cylinderRadius d n ζ κ) ^ (d - 1) ≤
        (4 : ℝ) ^ (d - 1) * (1 / 2 : ℝ) ^ (n + 1) := by
  let ε := cylinderRadius d n ζ κ
  let b := cylinderB n
  let ν := cylinderNu d ζ
  have hdR : 0 < (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdata := cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)
  have hb : 0 < b := cylinderB_pos n
  have heps : 0 < ε := hdata.1
  have hnu : 0 < ν := cylinderNu_pos hd hζ2
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have hn : d - 1 + 1 = d := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hcast' : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hn
    linarith
  have hfactorSchedule :
      1 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (cylinderRate d n κ)) := by
    have hj : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hrate : 0 ≤ cylinderRate d n κ := by
      dsimp [cylinderRate]
      positivity
    have hexp : 1 ≤ Real.exp (cylinderRate d n κ) := Real.one_le_exp hrate
    nlinarith
  have hraw := hdata.2.2.2.2
  have hbase : 0 ≤ b⁻¹ * Real.rpow ε ν :=
    mul_nonneg (inv_nonneg.mpr hb.le) (Real.rpow_nonneg heps.le ν)
  have hraw' : b⁻¹ * Real.rpow ε ν ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    calc
      _ = 1 * (b⁻¹ * Real.rpow ε ν) := by ring
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (cylinderRate d n κ)) *
          (b⁻¹ * Real.rpow ε ν) :=
        mul_le_mul_of_nonneg_right hfactorSchedule hbase
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
        nlinarith [hraw]
  have htail : b * Real.rpow ε ν ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    have hb1 : b ^ 2 ≤ 1 := by
      have hbsmall : b ≤ 1 := by
        dsimp [b, cylinderB]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    calc
      b * Real.rpow ε ν = b ^ 2 * (b⁻¹ * Real.rpow ε ν) := by
        field_simp [hb.ne']
      _ ≤ 1 * (1 / 2 : ℝ) ^ (n + 1) :=
        mul_le_mul hb1 hraw' hbase (by positivity)
      _ = _ := by ring
  have hfactor : scalarCoreValue d n ζ κ * (4 * ε) ^ (d - 1) =
      (4 : ℝ) ^ (d - 1) * (b * Real.rpow ε ν) := by
    have hcomb : Real.rpow ε (-ζ) * Real.rpow ε ((d - 1 : ℕ) : ℝ) =
        Real.rpow ε ν := by
      calc
        _ = Real.rpow ε (-ζ + ((d - 1 : ℕ) : ℝ)) :=
          (Real.rpow_add heps (-ζ) ((d - 1 : ℕ) : ℝ)).symm
        _ = Real.rpow ε ν := by
          congr 1
          dsimp [ν, cylinderNu]
          rw [hcast]
          ring
    calc
      _ = (4 : ℝ) ^ (d - 1) *
          (cylinderB n * (Real.rpow ε (-ζ) * Real.rpow ε ((d - 1 : ℕ) : ℝ))) := by
        unfold scalarCoreValue
        dsimp [ε]
        rw [mul_pow, (Real.rpow_natCast (cylinderRadius d n ζ κ) (d - 1)).symm]
        ring
      _ = (4 : ℝ) ^ (d - 1) * (b * Real.rpow ε ν) := by
        rw [hcomb]
  calc
    _ = (4 : ℝ) ^ (d - 1) * (b * Real.rpow ε ν) := hfactor
    _ ≤ (4 : ℝ) ^ (d - 1) * (1 / 2 : ℝ) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left htail (by positivity)

private theorem scalarInvIntegral_bound {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (n : ℕ) :
    (scalarAnnulusValue d n ζ κ)⁻¹ *
      (4 * cylinderRadius d n ζ κ) ^ (d - 1) ≤
        (4 : ℝ) ^ (d - 1) * cylinderB n := by
  let ε := cylinderRadius d n ζ κ
  let b := cylinderB n
  let μ := (d : ℝ) - 3 + ζ
  have hdR : 0 < (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdata := cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)
  have hb : 0 < b := cylinderB_pos n
  have heps : 0 < ε := hdata.1
  have hmu : 0 < μ := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    dsimp [μ]
    linarith
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have hn : d - 1 + 1 = d := Nat.sub_add_cancel (by omega : 1 ≤ d)
    have hcast' : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hn
    linarith
  have hepsle1 : ε ≤ 1 := by
    have hsep := hdata.2.1
    have hsqrt := Real.sqrt_nonneg κ
    have hbsmall : cylinderB n ≤ 1 := by
      dsimp [cylinderB]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hden : 1 ≤ 16 * (1 + Real.sqrt κ) := by nlinarith
    have hratio : cylinderB n / (16 * (1 + Real.sqrt κ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 16 * (1 + Real.sqrt κ))).2
      nlinarith
    dsimp [ε] at hsep ⊢
    exact hsep.le.trans hratio
  have hpowle : Real.rpow ε μ ≤ 1 := by
    exact Real.rpow_le_one (le_of_lt heps) hepsle1 hmu.le
  have hfactor : (scalarAnnulusValue d n ζ κ)⁻¹ * (4 * ε) ^ (d - 1) =
      (4 : ℝ) ^ (d - 1) * (b * Real.rpow ε μ) := by
    have hcomb : Real.rpow ε (-(2 - ζ)) * Real.rpow ε ((d - 1 : ℕ) : ℝ) =
        Real.rpow ε μ := by
      calc
        _ = Real.rpow ε (-(2 - ζ) + ((d - 1 : ℕ) : ℝ)) :=
          (Real.rpow_add heps (-(2 - ζ)) ((d - 1 : ℕ) : ℝ)).symm
        _ = Real.rpow ε μ := by
          congr 1
          dsimp [μ]
          rw [hcast]
          ring
    have hvalue : (scalarAnnulusValue d n ζ κ)⁻¹ =
        b * Real.rpow ε (-(2 - ζ)) := by
      unfold scalarAnnulusValue
      simp only [Real.rpow_eq_pow]
      rw [mul_inv, inv_inv, ← Real.rpow_neg hdata.1.le]
    calc
      _ = b * ((4 : ℝ) ^ (d - 1) *
          (Real.rpow ε (-(2 - ζ)) * Real.rpow ε ((d - 1 : ℕ) : ℝ))) := by
        simp only [Real.rpow_eq_pow]
        rw [hvalue, mul_pow]
        change b * Real.rpow ε (-(2 - ζ)) * ((4 : ℝ) ^ (d - 1) * ε ^ (d - 1)) = _
        simp only [Real.rpow_eq_pow, Real.rpow_natCast]
        ring
      _ = (4 : ℝ) ^ (d - 1) * (b * Real.rpow ε μ) := by
        rw [hcomb]
        ring
  rw [hfactor]
  have hbr : b * Real.rpow ε μ ≤ b := by
    calc
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hpowle (le_of_lt hb)
      _ = b := by ring
  exact mul_le_mul_of_nonneg_left hbr (by positivity)

private theorem scalarWeight_eq_one_off_bands {d : ℕ} {ζ κ : ℝ} {x : Vec d}
    (hx : x ∈ originCube 1 \ ⋃ n : ℕ, scalarBandsInCube n ζ κ) :
    scalarSharpnessWeight ζ κ x = 1 := by
  classical
  have hc (n : ℕ) : x ∉ scalarCoreBand n ζ κ := by
    intro h
    exact hx.2 (Set.mem_iUnion.mpr ⟨n, Or.inl ⟨h, hx.1⟩⟩)
  have ha (n : ℕ) : x ∉ scalarAnnulusBand n ζ κ := by
    intro h
    exact hx.2 (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨h, hx.1⟩⟩)
  simp [scalarSharpnessWeight, scalarCylinderContribution, hc, ha]

private theorem scalar_integrableOn_of_bands {d : ℕ} {ζ κ : ℝ}
    {f : Vec d → ℝ}
    (hi : ∀ n, IntegrableOn f (scalarBandsInCube n ζ κ) volume)
    (hs : Summable (fun n => ∫ x in scalarBandsInCube n ζ κ, ‖f x‖ ∂volume))
    (hone : ∀ x ∈ originCube 1 \ ⋃ n : ℕ, scalarBandsInCube n ζ κ, f x = 1) :
    IntegrableOn f (originCube 1) volume := by
  let S := ⋃ n : ℕ, scalarBandsInCube (d := d) n ζ κ
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun n => scalarBandsInCube_measurable n ζ κ)
  have hI : IntegrableOn f S volume := integrableOn_iUnion_of_summable_integral_norm hi hs
  have htop : volume (originCube (d := d) 1 \ S) ≠ ⊤ := by
    have hcube : volume (originCube (d := d) 1) ≠ ⊤ := by
      rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one d]
      simp
    exact ne_top_of_le_ne_top hcube (measure_mono Set.sdiff_subset)
  have hC : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (originCube 1 \ S) volume :=
    integrableOn_const htop
  have hJ : IntegrableOn f (originCube 1 \ S) volume :=
    hC.congr_fun (fun x hx => (hone x hx).symm) (originCube_one_measurable.diff hS)
  have hUnion : S ∪ (originCube 1 \ S) = originCube 1 := by
    exact Set.union_sdiff_cancel (scalarBands_subset_iUnion ζ κ)
  rw [← hUnion]
  exact hI.union hJ

/-- Both the scalar conductivity and its reciprocal are integrable on the unit
cube, including the interfaces and the accumulating line. -/
theorem scalarSharpnessWeight_integrable {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    IntegrableOn (scalarSharpnessWeight (d := d) ζ κ) (originCube 1) volume ∧
      IntegrableOn (fun x => (scalarSharpnessWeight (d := d) ζ κ x)⁻¹)
        (originCube 1) volume := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using summable_geometric_two.mul_right (1 / 2 : ℝ)
  have hb : Summable cylinderB := by
    change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3))
    simpa only [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ 3)
  constructor
  · apply scalar_integrableOn_of_bands (scalarWeight_integrableOn_bands hd hζ0 hζ2 hκ)
    · apply Summable.of_nonneg_of_le
        (fun n => integral_nonneg (fun x => norm_nonneg _))
        (fun n => (scalarBands_integral_norm_bound hd hζ0 hζ2 hκ n).trans
          (scalarCoreIntegral_bound hd hζ0 hζ2 hκ n))
      exact hgeom.mul_left ((4 : ℝ) ^ (d - 1))
    · intro x hx
      exact scalarWeight_eq_one_off_bands hx
  · apply scalar_integrableOn_of_bands (scalarInvWeight_integrableOn_bands hd hζ0 hζ2 hκ)
    · apply Summable.of_nonneg_of_le
        (fun n => integral_nonneg (fun x => norm_nonneg _))
        (fun n => (scalarInvBands_integral_norm_bound hd hζ0 hζ2 hκ n).trans
          (scalarInvIntegral_bound hd hζ0 hζ2 hκ n))
      exact hb.mul_left ((4 : ℝ) ^ (d - 1))
    · intro x hx
      rw [scalarWeight_eq_one_off_bands hx, inv_one]

/-- The source's disjoint-cylinder field satisfies the weighted-coefficient
hypothesis without any unproved integrability premises. -/
theorem scalarSharpnessCoefficient_isWeightedCoeffOn {d : ℕ} (hd : 3 ≤ d)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    IsWeightedCoeffOn (originCube 1) (scalarSharpnessCoefficient (d := d) ζ κ) := by
  obtain ⟨hω, hinv⟩ := scalarSharpnessWeight_integrable hd hζ0 hζ2 hκ
  exact scalarSharpnessCoefficient_weightedCoeffOn hd hζ0 hζ2 hκ hω hinv

end

end CoarseDeGiorgi.SharpnessExamples
