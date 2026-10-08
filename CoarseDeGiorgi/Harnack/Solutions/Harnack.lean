import CoarseDeGiorgi.Harnack.Solutions.Solutions
import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
import CoarseDeGiorgi.Harnack.ContrastBound.RootHypotheses
import CoarseDeGiorgi.Statements.HarnackEtaParam
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Harnack.Solutions

private lemma originCube_subset_local {d : ℕ} {ρ R : ℝ} (hρR : ρ ≤ R) :
    originCube (d := d) ρ ⊆ originCube R := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

private lemma originCube_local_volume_pos {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    0 < volume (originCube (d := d) ρ) :=
  CoarseDeGiorgi.Harnack.Scalar.volume_originCube_pos hρ

private lemma originCube_one_domain_local {d : ℕ} :
    IsOpenBoundedConvexDomain (originCube (d := d) 1) ∧
      (originCube (d := d) 1).Nonempty := by
  have hcube : originCube (d := d) 1 = auxCube 1 (fun _ : Fin d => 0) := by
    ext x
    simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]
  rw [hcube]
  exact ⟨LowerFractional.auxCube_isOpenBoundedConvexDomain 1 (fun _ => 0),
    LowerFractional.auxCube_nonempty 1 (fun _ => 0)⟩

private lemma normalized_moment_ge_eLpNorm_local {d : ℕ} {η : ℝ} (hη : 0 < η)
    {V : Set (Vec d)} (hVpos : 0 < volume V) (hVvol : volume V ≤ 1) {u : Vec d → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict V)) :
    eLpNorm u (ENNReal.ofReal η) (volume.restrict V) ≤ normalizedLpMoment η hη V u := by
  have hη0 : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.mpr hη).ne'
  have hηtop : ENNReal.ofReal η ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvoltop : volume V ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hVvol ENNReal.one_lt_top)
  have hinv : 1 ≤ (volume V)⁻¹ := by
    calc
      1 = volume V * (volume V)⁻¹ := by
        symm
        exact ENNReal.mul_inv_cancel hVpos.ne' hvoltop
      _ ≤ 1 * (volume V)⁻¹ := mul_le_mul_of_nonneg_right hVvol (by positivity)
      _ = (volume V)⁻¹ := by rw [one_mul]
  have hnorm : ∀ x, ‖u x‖ₑ ^ η = (ENNReal.ofReal |u x|).rpow η := by
    intro x
    simp [Real.enorm_eq_ofReal_abs]
  have hnorm' : eLpNorm u (ENNReal.ofReal η) (volume.restrict V) =
      (∫⁻ x in V, (ENNReal.ofReal |u x|).rpow η).rpow (1 / η) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hη0 hηtop hu]
    simp only [ENNReal.toReal_ofReal hη.le]
    congr 1
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall hnorm
  rw [hnorm']
  unfold normalizedLpMoment
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hη.le)
  calc
    (∫⁻ x in V, (ENNReal.ofReal |u x|).rpow η) =
        1 * (∫⁻ x in V, (ENNReal.ofReal |u x|).rpow η) := by simp
    _ ≤ (volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow η := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv
        (by positivity : 0 ≤ ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow η)

private lemma nonnegativeEssInf_add_const_local {d : ℕ} {V : Set (Vec d)}
    {u : Vec d → ℝ} {ε : ℝ} (hμ : volume.restrict V ≠ 0) (hε : 0 ≤ ε)
    (hu : 0 ≤ᵐ[volume.restrict V] u) :
    nonnegativeEssInf V (fun x => u x + ε) =
      nonnegativeEssInf V u + ENNReal.ofReal ε := by
  have hshift : (fun x => ENNReal.ofReal (u x + ε)) =ᵐ[volume.restrict V]
      fun x => ENNReal.ofReal (u x) + ENNReal.ofReal ε := by
    filter_upwards [hu] with x hx
    rw [ENNReal.ofReal_add hx hε]
  unfold nonnegativeEssInf
  rw [essInf_congr_ae hshift, essInf, essInf]
  let : NeZero (volume.restrict V) := ⟨hμ⟩
  exact liminf_add_const (ae (volume.restrict V))
    (fun x => ENNReal.ofReal (u x)) (ENNReal.ofReal ε)
    (by isBoundedDefault) (by isBoundedDefault)

private lemma one_add_le_exp_two_sqrt_local {x : ℝ} (hx : 1 ≤ x) :
    1 + x ≤ Real.exp (2 * Real.sqrt x) := by
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsquares : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith : 0 ≤ x)
  have hsquare : 1 + x ≤ (1 + Real.sqrt x) ^ 2 := by nlinarith [hsquares]
  have hlinear : 1 + Real.sqrt x ≤ Real.exp (Real.sqrt x) :=
    by simpa [add_comm] using Real.add_one_le_exp (Real.sqrt x)
  calc
    1 + x ≤ (1 + Real.sqrt x) ^ 2 := hsquare
    _ ≤ Real.exp (Real.sqrt x) ^ 2 := by
      nlinarith [sq_nonneg (Real.exp (Real.sqrt x) - (1 + Real.sqrt x))]
    _ = Real.exp (2 * Real.sqrt x) := by
      rw [pow_two, ← Real.exp_add, show Real.sqrt x + Real.sqrt x = 2 * Real.sqrt x by ring]

private lemma polynomial_exp_absorption_local {x β K c : ℝ} (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hK : 1 ≤ K) :
    K * Real.exp (c * Real.sqrt x) * (1 + x) ^ β ≤
      Real.exp ((Real.log K + c + 2 * β) * Real.sqrt x) := by
  have hsqrt : 1 ≤ Real.sqrt x := by
    have hsquares : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith : 0 ≤ x)
    nlinarith [hsquares, Real.sqrt_nonneg x]
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKexp : K ≤ Real.exp (Real.log K * Real.sqrt x) := by
    calc
      K = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
      _ ≤ Real.exp (Real.log K * Real.sqrt x) := Real.exp_le_exp.mpr (by nlinarith)
  calc
    K * Real.exp (c * Real.sqrt x) * (1 + x) ^ β ≤
        Real.exp (Real.log K * Real.sqrt x) * Real.exp (c * Real.sqrt x) *
          (1 + x) ^ β := by gcongr
    _ ≤ Real.exp (Real.log K * Real.sqrt x) * Real.exp (c * Real.sqrt x) *
          Real.exp (2 * Real.sqrt x) ^ β := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (one_add_le_exp_two_sqrt_local hx) hβ)
      positivity
    _ = Real.exp ((Real.log K + c + 2 * β) * Real.sqrt x) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private lemma ennnreal_polynomial_exp_absorption_local {X : ℝ≥0∞} {β K c : ℝ}
    (hXtop : X < ⊤) (hX : 1 ≤ X) (hβ : 0 ≤ β) (hK : 1 ≤ K) :
    ENNReal.ofReal K * ENNReal.ofReal (Real.exp (c * Real.sqrt X.toReal)) *
        (1 + X).rpow β ≤
      ENNReal.ofReal (Real.exp ((Real.log K + c + 2 * β) * Real.sqrt X.toReal)) := by
  have hXreal : 1 ≤ X.toReal := by
    simpa using ENNReal.toReal_mono (b := X) hXtop.ne hX
  have hsum : 1 + X = ENNReal.ofReal (1 + X.toReal) := by
    rw [ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg]
    simp [ENNReal.ofReal_toReal hXtop.ne]
  have hreal := polynomial_exp_absorption_local (c := c) hXreal hβ hK
  rw [hsum, ENNReal.rpow_eq_pow,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hβ]
  have hKnonneg : 0 ≤ K := by linarith
  have hKexpnonneg : 0 ≤ K * Real.exp (c * Real.sqrt X.toReal) := by positivity
  calc
    _ = ENNReal.ofReal (K * Real.exp (c * Real.sqrt X.toReal)) *
          ENNReal.ofReal ((1 + X.toReal) ^ β) := by
      rw [← ENNReal.ofReal_mul hKnonneg]
    _ = ENNReal.ofReal (K * Real.exp (c * Real.sqrt X.toReal) * (1 + X.toReal) ^ β) := by
      rw [← ENNReal.ofReal_mul hKexpnonneg]
    _ ≤ ENNReal.ofReal (Real.exp ((Real.log K + c + 2 * β) * Real.sqrt X.toReal)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The coefficient lower bound here is the exact moment-comparison output from
the Moments area. The weak-Harnack input is written out at the type of the
`weak_harnack` statement, so this helper consumes the exact statement directly. -/
theorem harnack_of_weak_harnack {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (hweak : ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment (harnackEtaParam q) (by
              have _hq0 : 0 < q := lt_trans (by norm_num) hq
              dsimp [harnackEtaParam, paramR]
              positivity)
            (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (Cw * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u)
    (hcontrast : ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      upperMoment a ha s p hs hp.le < ⊤ →
      0 < lowerMoment a ha t q ht hq.le →
      1 ≤ contrast a ha s t p q hs ht hp.le hq.le) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSolution a (originCube 1) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  obtain ⟨Cw, hCw, hweak⟩ := hweak
  obtain ⟨γ, hγ, Cη, hCη, hB⟩ :=
    solution_local_upper_eta0 d hd p q s t hp hq hs ht hθ
  have hηfacts := harnack_eta_parameter_facts hq
  let η : ℝ := harnackEtaParam q
  have hη : 0 < η := by simpa [η, harnackEtaParam, paramR] using hηfacts.1
  have hη2 : η < 2 := by simpa [η, harnackEtaParam, paramR] using hηfacts.2
  let β : ℝ := ((d : ℝ) - 1) / (2 * η * paramTheta d p q s t)
  have hβ : 0 ≤ β := by
    dsimp [β]
    apply div_nonneg
    · have hd' : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
      linarith
    · exact (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hη) hθ).le
  let gapReal : ℝ := (1 / 8 : ℝ) ^ (-2 * γ / η)
  have hgapRealPos : 0 < gapReal := by
    dsimp [gapReal]
    exact Real.rpow_pos_of_pos (by norm_num) (-2 * γ / η)
  have hgapEq : (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) =
      ENNReal.ofReal gapReal := by
    dsimp [gapReal]
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
  let K : ℝ := max 1 (Cη.toReal * gapReal)
  have hK : 1 ≤ K := le_max_left _ _
  have hCηGap : Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) ≤
      ENNReal.ofReal K := by
    rw [hgapEq, ← ENNReal.ofReal_toReal hCη.ne]
    calc
      ENNReal.ofReal Cη.toReal * ENNReal.ofReal gapReal =
          ENNReal.ofReal (Cη.toReal * gapReal) := by
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  let C : ℝ := Real.log K + Cw + 2 * β
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  let : NeZero d := ⟨by omega⟩
  have hgeomPair := originCube_one_domain_local (d := d)
  have hhalfpos : 0 < volume (originCube (d := d) (1 / 2)) :=
    originCube_local_volume_pos (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro a ha hupper hlower u G hu_nonneg hu
  have hcontrast_one := hcontrast a ha hupper hlower
  let X : ℝ≥0∞ := contrast a ha s t p q hs ht hp.le hq.le
  have hXtop : X < ⊤ := by
    dsimp [X, contrast]
    exact ENNReal.div_lt_top hupper.ne hlower.ne'
  have hX : 1 ≤ X := by simpa [X] using hcontrast_one
  have hpoly := ennnreal_polynomial_exp_absorption_local (c := Cw) hXtop hX hβ hK
  have hcubeHalf : originCube (d := d) (1 / 2) ⊆ originCube 1 :=
    originCube_subset_local (by norm_num)
  let m : ℝ≥0∞ := nonnegativeEssInf (originCube (1 / 2)) u
  have hεbound : ∀ ε : ℝ, 0 < ε →
      eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
          (m + ENNReal.ofReal ε) := by
    intro ε hε
    let U : Vec d → ℝ := fun x => u x + ε
    have hshift := Harnack.Calculus.shiftedSolution_isNonnegativeSupersolution
      hgeomPair.1 hgeomPair.2 ha hu hu_nonneg hε
    have houterSubset : originCube (d := d) (5 / 8) ⊆ originCube 1 :=
      originCube_subset_local (by norm_num)
    have hUouter : ∀ᵐ x ∂volume.restrict (originCube (5 / 8)), 0 ≤ U x :=
      ae_restrict_of_ae_restrict_of_subset houterSubset hshift.1
    have hUmeas : AEStronglyMeasurable U
        (volume.restrict (originCube (5 / 8))) := by
      exact hshift.2.1.1.1.mono_measure
        (Measure.restrict_mono houterSubset le_rfl)
    have hηnorm := normalized_moment_ge_eLpNorm_local hη
      (originCube_local_volume_pos (by norm_num))
      (CoarseDeGiorgi.Harnack.Scalar.volume_originCube_le_one (by norm_num)) hUmeas
    have hweakU := hweak a ha hupper hlower U G hshift.1
      (by exact hshift.2.2)
    have hBε := hB a ha hupper hlower u G hu_nonneg hu ε hε
    let poly : ℝ≥0∞ :=
      (1 + X).rpow (((d : ℝ) - 1) / (2 * η * paramTheta d p q s t))
    have hpolyEq : poly = (1 + X).rpow β := by
      simp [poly, β]
    have hcoeff : Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) *
        poly * ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal)) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) := by
      rw [hpolyEq]
      have hbase := hpoly
      dsimp [C] at hbase ⊢
      calc
        _ = (Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η)) *
              (ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal)) *
                (1 + X).rpow β) := by ac_rfl
        _ ≤ ENNReal.ofReal K *
              (ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal)) *
                (1 + X).rpow β) :=
          mul_le_mul_of_nonneg_right hCηGap (by positivity)
        _ = ENNReal.ofReal K * ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal)) *
              (1 + X).rpow β := by ac_rfl
        _ ≤ ENNReal.ofReal (Real.exp ((Real.log K + Cw + 2 * β) * Real.sqrt X.toReal)) :=
          hbase
    calc
      eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
          eLpNorm U ⊤ (volume.restrict (originCube (1 / 2))) := by
        apply eLpNorm_mono_ae_real
          ((hu.1.1).mono_measure (Measure.restrict_mono hcubeHalf le_rfl))
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hcubeHalf hu_nonneg]
          with x hx
        dsimp [U]
        rw [abs_of_nonneg hx]
        linarith
      _ ≤ Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) * poly *
          eLpNorm U (ENNReal.ofReal η) (volume.restrict (originCube (5 / 8))) := by
        simpa [U, η, poly, β, harnackEtaParam, paramR] using hBε.1
      _ ≤ Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) * poly *
          normalizedLpMoment (harnackEtaParam q)
            (by
              have _hq0 : 0 < q := lt_trans (by norm_num) hq
              dsimp [harnackEtaParam, paramR]
              positivity)
            (originCube (5 / 8)) U := by
        exact mul_le_mul_of_nonneg_left hηnorm (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
          nonnegativeEssInf (originCube (1 / 2)) U := by
        have hweakmul := mul_le_mul_of_nonneg_left hweakU
          (by positivity : 0 ≤ Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) * poly)
        calc
          _ ≤ Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) * poly *
              (ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) U) := by
                simpa [mul_assoc] using hweakmul
          _ = (Cη * (ENNReal.ofReal (1 / 8 : ℝ)).rpow (-2 * γ / η) * poly *
                ENNReal.ofReal (Real.exp (Cw * Real.sqrt X.toReal))) *
                nonnegativeEssInf (originCube (1 / 2)) U := by ac_rfl
          _ ≤ ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) U :=
              mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
          (m + ENNReal.ofReal ε) := by
        have hμ : volume.restrict (originCube (d := d) (1 / 2)) ≠
            (0 : Measure (Vec d)) := by
          intro hz
          exact hhalfpos.ne' (Measure.restrict_eq_zero.mp hz)
        have hessInf := nonnegativeEssInf_add_const_local (V := originCube (d := d) (1 / 2))
          (u := u) hμ hε.le (ae_restrict_of_ae_restrict_of_subset hcubeHalf hu_nonneg)
        have hessInfU : nonnegativeEssInf (originCube (1 / 2)) U =
            m + ENNReal.ofReal ε := by simpa [U, m] using hessInf
        rw [hessInfU]

  by_cases hm : m = ⊤
  · have hm' : nonnegativeEssInf (originCube (1 / 2)) u = ⊤ := by
      simpa [m] using hm
    rw [hm']
    have hfactor : ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    rw [ENNReal.mul_eq_top.mpr (Or.inl ⟨hfactor, rfl⟩)]
    exact le_top
  · let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hεseq (n : ℕ) : 0 < εseq n := by
      dsimp [εseq]
      positivity
    have hεtendsto : Tendsto εseq atTop (𝓝 (0 : ℝ)) := by
      simpa [εseq] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hrealTendsto : Tendsto (fun n => m.toReal + εseq n) atTop
        (𝓝 m.toReal) := by
      simpa using tendsto_const_nhds.add hεtendsto
    have hsumEq (n : ℕ) : m + ENNReal.ofReal (εseq n) =
        ENNReal.ofReal (m.toReal + εseq n) := by
      calc
        m + ENNReal.ofReal (εseq n) =
            ENNReal.ofReal m.toReal + ENNReal.ofReal (εseq n) := by
          conv_lhs => rw [← ENNReal.ofReal_toReal hm]
        _ = ENNReal.ofReal (m.toReal + εseq n) :=
          (ENNReal.ofReal_add ENNReal.toReal_nonneg (le_of_lt (hεseq n))).symm
    have hsumTendsto : Tendsto
        (fun n => m + ENNReal.ofReal (εseq n)) atTop (𝓝 m) := by
      have heq : (fun n => m + ENNReal.ofReal (εseq n)) =
          fun n => ENNReal.ofReal (m.toReal + εseq n) := by
        funext n
        exact hsumEq n
      rw [heq]
      simpa [ENNReal.ofReal_toReal hm] using ENNReal.tendsto_ofReal hrealTendsto
    have hconst : Tendsto
        (fun n => ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
          (m + ENNReal.ofReal (εseq n))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) * m)) :=
      ENNReal.Tendsto.const_mul hsumTendsto (Or.inr ENNReal.ofReal_ne_top)
    have hbound : ∀ᶠ n : ℕ in atTop,
        eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt X.toReal)) *
            (m + ENNReal.ofReal (εseq n)) := by
      filter_upwards with n
      exact hεbound (εseq n) (hεseq n)
    simpa [X, m] using le_of_tendsto_of_tendsto tendsto_const_nhds hconst hbound

/-- The only theorem input is the exact fixed-parameter statement of
`weak_harnack`; the contrast bound follows from the root coefficient hypotheses. -/
theorem harnack_of_weak_harnack_root {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (hweak : ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            normalizedLpMoment (harnackEtaParam q) (by
              have _hq0 : 0 < q := lt_trans (by norm_num) hq
              dsimp [harnackEtaParam, paramR]
              positivity)
            (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (Cw * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSolution a (originCube 1) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  apply harnack_of_weak_harnack (d := d) hd p q s t hp hq hs ht hθ hweak
  intro a ha hupper hlower
  exact Harnack.ContrastBound.contrast_ge_one_of_root_hypotheses
    hd a ha hp hq hs ht hupper hlower

end CoarseDeGiorgi.Harnack.Solutions
