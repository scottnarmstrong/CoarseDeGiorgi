import CoarseDeGiorgi.SharpnessExamples.PolynomialPositivePart
import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
import CoarseDeGiorgi.Foundations.Euclid.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private def polynomialNormBox {d : ℕ} (epsilon : ℝ) : Set (Vec d) :=
  Set.pi Set.univ (fun i : Fin d =>
    Set.Ioo (if i.val = 0 then -(1 / 4 : ℝ) else -(epsilon / (2 * d)))
      (if i.val = 0 then 1 / 4 else epsilon / (2 * d)))

private lemma polynomialNormBox_measurable {d : ℕ} (epsilon : ℝ) :
    MeasurableSet (polynomialNormBox (d := d) epsilon) := by
  exact MeasurableSet.univ_pi (fun i => by split_ifs <;> exact measurableSet_Ioo)

private lemma polynomialNormBox_volume {d : ℕ} [NeZero d] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    (volume (polynomialNormBox (d := d) epsilon)).toReal =
      (1 / 2) * (epsilon / d) ^ (d - 1) := by
  rw [polynomialNormBox, Real.volume_pi_Ioo_toReal]
  · have hwidth :
        (fun i : Fin d =>
          (if i.val = 0 then (1 / 4 : ℝ) else epsilon / (2 * d)) -
            (if i.val = 0 then -(1 / 4 : ℝ) else -(epsilon / (2 * d)))) =
        (fun i => if i.val = 0 then (1 / 2 : ℝ) else epsilon / d) := by
      funext i
      by_cases hi : i.val = 0 <;> simp [hi] <;> ring
    rw [hwidth, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin d))]
    have hprod :
        (∏ i ∈ Finset.univ.erase (0 : Fin d),
          if i.val = 0 then (1 / 2 : ℝ) else epsilon / d) =
          (epsilon / d) ^ (d - 1) := by
      calc
        _ = ∏ _i ∈ Finset.univ.erase (0 : Fin d), epsilon / d := by
          apply Finset.prod_congr rfl
          intro i hi
          simp only [Finset.mem_erase, Finset.mem_univ] at hi
          simp [hi]
        _ = _ := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin d)),
            Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    simp
  · intro i
    dsimp
    split_ifs
    · norm_num
    · have hdpos : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      have hden : 0 < (2 : ℝ) * d := by positivity
      have hratio : 0 ≤ epsilon / (2 * d) := div_nonneg hepsilon hden.le
      nlinarith

private lemma polynomialNormBox_subset_cube {d : ℕ} {epsilon R : ℝ}
    (hd : 3 ≤ d) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hR : 1 / 2 < R)
    (x : Vec d) (hx : x ∈ polynomialNormBox (d := d) epsilon) :
    x ∈ originCube R := by
  intro i
  have hi := hx i (Set.mem_univ i)
  by_cases haxis : i.val = 0
  · simpa [polynomialNormBox, haxis] using
      (show -(R / 2) < x i ∧ x i < R / 2 by
        have hx' : -(1 / 4 : ℝ) < x i ∧ x i < 1 / 4 := by
          simpa [polynomialNormBox, haxis] using hi
        constructor <;> linarith)
  · have hsmall : epsilon / (2 * d) < R / 2 := by
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have hq : epsilon / (2 * d) < 1 / 32 := by
        rw [div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * d)]
        nlinarith
      linarith
    have hx' : -(epsilon / (2 * d)) < x i ∧ x i < epsilon / (2 * d) := by
      simpa [haxis] using hi
    constructor <;> linarith

private lemma polynomialNormBox_transverse_sq {d : ℕ} [NeZero d] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {x : Vec d}
    (hx : x ∈ polynomialNormBox (d := d) epsilon) :
    Sharpness.transverseNorm x ^ 2 ≤ epsilon ^ 2 / (4 * d) := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hcap : 0 ≤ epsilon / (2 * d) := by positivity
  have hcoord (i : Fin d) :
      |Sharpness.transversePart x i| ≤ epsilon / (2 * d) := by
    by_cases hi : i.val = 0
    · simp [Sharpness.transversePart, hi]
      exact hcap
    · have hxi : |x i| < epsilon / (2 * d) := by
        have hbox := hx i (Set.mem_univ i)
        simpa [hi] using (abs_lt.mpr (by
          simpa [hi] using hbox))
      simpa [Sharpness.transversePart, hi] using hxi.le
  have hsquare (i : Fin d) :
      (Sharpness.transversePart x i) ^ 2 ≤ (epsilon / (2 * d)) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hcap).2 (hcoord i)
    simpa [sq_abs] using h
  have hsum :
      (∑ i : Fin d, (Sharpness.transversePart x i) ^ 2) ≤
        ∑ _i : Fin d, (epsilon / (2 * d)) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hsquare i)
  have hnorm : Sharpness.transverseNorm x ^ 2 =
      ∑ i : Fin d, (Sharpness.transversePart x i) ^ 2 := by
    rw [Sharpness.transverseNorm, euclideanNorm_sq]
    simp [vecNormSq, vecDot, pow_two]
  rw [hnorm]
  calc
    _ ≤ ∑ _i : Fin d, (epsilon / (2 * d)) ^ 2 := hsum
    _ = (d : ℝ) * (epsilon / (2 * d)) ^ 2 := by simp
    _ = epsilon ^ 2 / (4 * d) := by field_simp; ring

private lemma polynomialNormBox_positivePart_lower {d : ℕ} [NeZero d]
    {q t epsilon R : ℝ} (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon8 : epsilon < 1 / 8) (hR : 1 / 2 < R) (hR1 : R ≤ 1)
    {x : Vec d} (hx : x ∈ polynomialNormBox (d := d) epsilon) :
    3 / 4 ≤ positivePart (polynomialSolution d q t epsilon) x := by
  have hxR := polynomialNormBox_subset_cube hd hepsilon hepsilon8 hR x hx
  have hx1 : x ∈ originCube (d := d) 1 := by
    intro i
    rcases hxR i with ⟨hlo, hhi⟩
    exact ⟨by linarith, by linarith⟩
  rw [polynomialPositivePart_eq_inner hd hepsilon hx1]
  have htrans := polynomialNormBox_transverse_sq (le_of_lt hepsilon) hx
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpen : Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 ≤ 1 / 12 := by
    have he2 : 0 < epsilon ^ 2 := by positivity
    have hdim : 1 / (4 * d) ≤ (1 / 12 : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < (4 : ℝ) * d)]
      nlinarith
    have hmul : epsilon ^ 2 / (4 * d) ≤ (1 / 12 : ℝ) * epsilon ^ 2 := by
      rw [div_le_iff₀ (by positivity : 0 < (4 : ℝ) * d)]
      nlinarith
    have hnum : Sharpness.transverseNorm x ^ 2 ≤ (1 / 12 : ℝ) * epsilon ^ 2 :=
      htrans.trans hmul
    have hquot := (div_le_iff₀ he2).2 hnum
    exact hquot
  have hinner :
      3 / 4 ≤ 1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 := by
    have hsquare : 0 ≤ (x 0) ^ 2 := sq_nonneg _
    nlinarith
  exact hinner.trans (le_max_left _ _)

private lemma originCube_isOpen {d : ℕ} (R : ℝ) :
    IsOpen (originCube (d := d) R) := by
  have hset : originCube (d := d) R =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(R / 2)) (R / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [hset]
  exact isOpen_set_pi Set.finite_univ (by intro i hi; exact isOpen_Ioo)

private lemma originCube_subset_of_le {d : ℕ} {R S : ℝ} (h : R ≤ S) :
    originCube (d := d) R ⊆ originCube S := by
  intro x hx i
  rcases hx i with ⟨hlo, hhi⟩
  exact ⟨by linarith, by linarith⟩

private lemma polynomialHeight_sublevel_positive_measure {d : ℕ} [NeZero d]
    {epsilon rho c q t : ℝ} (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hc : 0 ≤ c)
    (hcH : c < 1 + rho ^ 2 / 4) :
    ∃ U : Set (Vec d), IsOpen U ∧ U ⊆ originCube rho ∧
      0 < volume U ∧ ∀ x ∈ U,
        c < positivePart (polynomialSolution d q t epsilon) x := by
  let H : ℝ := 1 + rho ^ 2 / 4
  let gap : ℝ := H - c
  let delta : ℝ := gap / (2 * (H + 1))
  let axial : ℝ := rho / 2 * (1 - delta)
  have hH : H = 1 + rho ^ 2 / 4 := rfl
  have hgap : 0 < gap := by dsimp [gap, H]; linarith
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hdelta : 0 < delta ∧ delta < 1 := by
    dsimp [delta]
    constructor
    · positivity
    · have : 0 < H + 1 := by linarith
      rw [div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * (H + 1))]
      dsimp [gap]
      nlinarith [hc, hHpos]
  have haxial : 0 < axial ∧ axial < rho / 2 := by
    dsimp [axial]
    constructor <;> nlinarith [hrho, hdelta.1, hdelta.2]
  let x0 : Vec d := fun i => if i = 0 then axial else 0
  have hx0 : x0 ∈ originCube (d := d) rho := by
    intro i
    by_cases hi : i = 0
    · subst i
      change -(rho / 2) < axial ∧ axial < rho / 2
      exact ⟨by linarith [haxial.1, hrho], haxial.2⟩
    · change -(rho / 2) < x0 i ∧ x0 i < rho / 2
      have hxi : x0 i = 0 := by simp [x0, hi]
      rw [hxi]
      constructor <;> linarith
  have htrans0 : Sharpness.transverseNorm x0 = 0 := by
    have hpart : Sharpness.transversePart x0 = 0 := by
      funext i
      by_cases hi : i = 0
      · subst i
        simp [Sharpness.transversePart, x0]
      · have hiv : i.val ≠ 0 := by
          intro hval
          exact hi (Fin.ext hval)
        simp [Sharpness.transversePart, x0, hi, hiv]
    simp [Sharpness.transverseNorm, hpart]
  let g : Vec d → ℝ := fun x =>
    1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2
  have hgcont : Continuous g := by
    have hcoord : Continuous (fun x : Vec d => x 0) := continuous_apply 0
    have hrad : Continuous (Sharpness.transverseNorm (d := d)) :=
      Sharpness.lineRadius_continuous
    dsimp [g]
    fun_prop
  have hgx : c < g x0 := by
    have hx0val : x0 0 = axial := by simp [x0]
    have hgxval : g x0 = 1 + axial ^ 2 := by simp [g, hx0val, htrans0]
    have hval : c < 1 + axial ^ 2 := by
      let B : ℝ := rho ^ 2 / 4
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hBpos : 0 < B := by dsimp [B]; positivity
      have hBlt : B < H + 1 := by dsimp [B, H]; nlinarith [hrho]
      have hδeq : 2 * (H + 1) * delta = gap := by
        dsimp [delta]
        field_simp
      have hBδ : B * delta < gap / 2 := by
        calc
          B * delta < (H + 1) * delta := mul_lt_mul_of_pos_right hBlt hdelta.1
          _ = gap / 2 := by nlinarith [hδeq]
      have hloss : B * (2 * delta - delta ^ 2) < gap := by
        have hprodpos : 0 < B * delta ^ 2 := mul_pos hBpos (sq_pos_of_pos hdelta.1)
        calc
          B * (2 * delta - delta ^ 2) < 2 * B * delta := by nlinarith [hprodpos]
          _ < gap := by nlinarith [hBδ]
      have hvalue : 1 + axial ^ 2 = H - B * (2 * delta - delta ^ 2) := by
        dsimp [axial, H, B]
        ring
      rw [hvalue]
      dsimp [gap] at hloss
      linarith
    rw [hgxval]
    exact hval
  let U : Set (Vec d) := {x | c < g x} ∩ originCube rho
  have hUopen : IsOpen U := (isOpen_lt continuous_const hgcont).inter (originCube_isOpen rho)
  have hUnonempty : U.Nonempty := ⟨x0, ⟨hgx, hx0⟩⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUnonempty
  refine ⟨U, hUopen, ?_, hUpos, ?_⟩
  · intro x hx
    exact hx.2
  · intro x hx
    have hxρ := hx.2
    have hx1 : x ∈ originCube (d := d) 1 := originCube_subset_of_le hrho1 hxρ
    rw [polynomialPositivePart_eq_inner hd hepsilon hx1]
    exact lt_of_lt_of_le hx.1 (le_max_left _ _)

private lemma polynomialPositivePart_essSup_lower {d : ℕ} [NeZero d]
    {q t epsilon rho : ℝ} (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    (hrho : 1 / 2 ≤ rho) (hrho1 : rho < 1) {c : ℝ}
    (hc : 0 ≤ c) (hcH : c < 1 + rho ^ 2 / 4) :
    ENNReal.ofReal c ≤ eLpNormEssSup (positivePart (polynomialSolution d q t epsilon))
      (volume.restrict (originCube rho)) := by
  obtain ⟨U, hUopen, hUcube, hUpos, hUlower⟩ :=
    polynomialHeight_sublevel_positive_measure hd hepsilon (by linarith [hrho])
      (by linarith [hrho1]) hc hcH
  have hμU : (volume.restrict (originCube (d := d) rho)) U = volume U := by
    rw [Measure.restrict_apply hUopen.measurableSet]
    rw [Set.inter_eq_left.mpr hUcube]
  have hμUpos : (volume.restrict (originCube (d := d) rho)) U ≠ 0 := by
    rw [hμU]
    exact (ne_of_gt hUpos)
  have hmono :
      eLpNormEssSup (U.indicator fun _ : Vec d => c)
          (volume.restrict (originCube (d := d) rho)) ≤
        eLpNormEssSup (positivePart (polynomialSolution d q t epsilon))
          (volume.restrict (originCube (d := d) rho)) := by
    apply eLpNormEssSup_mono_enorm_ae
    filter_upwards [ae_restrict_mem (originCube_isOpen (d := d) rho).measurableSet] with x hxρ
    by_cases hxU : x ∈ U
    · have hfx := hUlower x hxU
      have hfx0 : 0 ≤ positivePart (polynomialSolution d q t epsilon) x := by
        simp [positivePart]
      rw [Set.indicator_of_mem hxU, Real.enorm_eq_ofReal hc, Real.enorm_eq_ofReal hfx0]
      exact ENNReal.ofReal_le_ofReal hfx.le
    · rw [Set.indicator_of_notMem hxU]
      simp
  rw [eLpNormEssSup_indicator_const_eq U c hμUpos] at hmono
  simpa [Real.enorm_eq_ofReal hc] using hmono

theorem polynomialPositivePart_height {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {q t epsilon : ℝ} (hepsilon : 0 < epsilon) (_hepsilon8 : epsilon < 1 / 8)
    (hmeas : AEStronglyMeasurable (positivePart (polynomialSolution d q t epsilon))
      (volume.restrict (originCube 1)))
    {rho : ℝ} (hrho : 1 / 2 ≤ rho) (hrho1 : rho < 1) :
    eLpNorm (positivePart (polynomialSolution d q t epsilon)) ⊤
      (volume.restrict (originCube rho)) = ENNReal.ofReal (1 + rho ^ 2 / 4) := by
  let f := positivePart (polynomialSolution d q t epsilon)
  let μ := volume.restrict (originCube (d := d) rho)
  have hsubset : originCube (d := d) rho ⊆ originCube 1 :=
    originCube_subset_of_le (by linarith)
  have hμle : μ ≤ volume.restrict (originCube (d := d) 1) :=
    Measure.restrict_mono hsubset le_rfl
  have hmeasρ : AEStronglyMeasurable f μ := by
    exact hmeas.mono_measure hμle
  have hupper : eLpNormEssSup f μ ≤ ENNReal.ofReal (1 + rho ^ 2 / 4) := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [ae_restrict_mem (originCube_isOpen (d := d) rho).measurableSet] with x hx
    have hx1 : x ∈ originCube (d := d) 1 := hsubset hx
    change ‖positivePart (polynomialSolution d q t epsilon) x‖ ≤ _
    rw [polynomialPositivePart_eq_inner hd hepsilon hx1]
    have hx0 : |x 0| < rho / 2 := by
      rw [abs_lt]
      exact hx 0
    have hx0sq : (x 0) ^ 2 ≤ rho ^ 2 / 4 := by
      have := (sq_lt_sq₀ (abs_nonneg (x 0)) (by positivity)).2 hx0
      rw [sq_abs] at this
      nlinarith
    have hsub : 0 ≤ Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 := by positivity
    have hf : 0 ≤ max (1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2) 0 :=
      le_max_right _ _
    have hfle : max (1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2) 0 ≤
        1 + rho ^ 2 / 4 := by
      apply max_le
      · nlinarith
      · positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf]
    exact hfle
  have hlower : ENNReal.ofReal (1 + rho ^ 2 / 4) ≤ eLpNormEssSup f μ := by
    by_contra! hnot
    have htop : eLpNormEssSup f μ < ⊤ := hupper.trans_lt ENNReal.ofReal_lt_top
    have hreal : (eLpNormEssSup f μ).toReal < 1 + rho ^ 2 / 4 :=
      (ENNReal.lt_ofReal_iff_toReal_lt htop.ne).mp hnot
    let c : ℝ := ((eLpNormEssSup f μ).toReal + (1 + rho ^ 2 / 4)) / 2
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hcH : c < 1 + rho ^ 2 / 4 := by dsimp [c]; linarith
    have hess : eLpNormEssSup f μ < ENNReal.ofReal c :=
      (ENNReal.lt_ofReal_iff_toReal_lt htop.ne).2 (by dsimp [c]; linarith)
    exact (not_le_of_gt hess) (polynomialPositivePart_essSup_lower hd hepsilon hrho hrho1 hc hcH)
  simpa [f, μ, eLpNorm_exponent_top hmeasρ] using le_antisymm hupper hlower

theorem polynomialPositivePart_Lp_asymptotic {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {q t eta : ℝ} (heta : 0 < eta)
    (hmeas : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      AEStronglyMeasurable (positivePart (polynomialSolution d q t epsilon))
        (volume.restrict (originCube 1))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∀ R : ℝ, 1 / 2 < R → R ≤ 1 →
        ENNReal.ofReal (C⁻¹ * epsilon ^ (((d : ℝ) - 1) / eta)) ≤
          eLpNorm (positivePart (polynomialSolution d q t epsilon)) (ENNReal.ofReal eta)
            (volume.restrict (originCube R)) ∧
        eLpNorm (positivePart (polynomialSolution d q t epsilon)) (ENNReal.ofReal eta)
            (volume.restrict (originCube R)) ≤
          ENNReal.ofReal (C * epsilon ^ (((d : ℝ) - 1) / eta)) := by
  let n : ℝ := (d : ℝ) - 1
  let lowerBase : ℝ := (1 / 2) * (1 / d) ^ (d - 1)
  let upperBase : ℝ := 2 * 4 ^ (d - 1)
  let A : ℝ := (3 / 4) * lowerBase ^ (1 / eta)
  let B : ℝ := (5 / 4) * upperBase ^ (1 / eta)
  let C : ℝ := max 1 (max B A⁻¹)
  have hn : n = (d - 1 : ℕ) := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hlowerBase : 0 < lowerBase := by
    dsimp [lowerBase]
    positivity
  have hupperBase : 0 < upperBase := by
    dsimp [upperBase]
    positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilon8 R hR hR1
  let f := positivePart (polynomialSolution d q t epsilon)
  let μ := volume.restrict (originCube (d := d) R)
  let p := ENNReal.ofReal eta
  let T := responseCylinder (d := d) epsilon
  have hsubset : originCube (d := d) R ⊆ originCube 1 :=
    originCube_subset_of_le hR1
  have hmeasR : AEStronglyMeasurable f μ := by
    exact (hmeas epsilon hepsilon hepsilon8).mono_measure
      (Measure.restrict_mono hsubset le_rfl)
  have hp0 : p ≠ 0 := by
    dsimp [p]
    exact ENNReal.ofReal_ne_zero_iff.mpr heta
  have hptop : p ≠ ⊤ := by simp [p]
  have hpToReal : p.toReal = eta := by simp [p, heta.le]
  have hTmeas : MeasurableSet T := responseCylinder_measurable epsilon
  have hdom : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖T.indicator (fun _ : Vec d => (5 / 4 : ℝ)) x‖ₑ := by
    filter_upwards [ae_restrict_mem (originCube_isOpen (d := d) R).measurableSet] with x hxR
    have hx1 : x ∈ originCube (d := d) 1 := hsubset hxR
    have hf0 : 0 ≤ f x := by simp [f, positivePart]
    by_cases hxT : x ∈ T
    · have hbound : f x ≤ 5 / 4 :=
        polynomialPositivePart_le_five_quarters hd hepsilon hx1
      rw [Set.indicator_of_mem hxT, Real.enorm_eq_ofReal hf0,
        Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      exact ENNReal.ofReal_le_ofReal hbound
    · have hfnot : ¬ 0 < f x := by
        intro hfpos
        have hmem := polynomialPositivePart_pos_mem_responseCylinder hd hepsilon hx1 hfpos
        exact hxT hmem
      have hfzero : f x = 0 := le_antisymm (le_of_not_gt hfnot) hf0
      rw [Set.indicator_of_notMem hxT, hfzero]
  have hmono : eLpNorm f p μ ≤
      eLpNorm (T.indicator (fun _ : Vec d => (5 / 4 : ℝ))) p μ :=
    eLpNorm_mono_enorm_ae hmeasR hdom
  have hformula :
      eLpNorm (T.indicator (fun _ : Vec d => (5 / 4 : ℝ))) p μ =
        ENNReal.ofReal (5 / 4) * (μ T) ^ (1 / eta) := by
    rw [eLpNorm_indicator_const hTmeas.nullMeasurableSet hp0 hptop]
    simp [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4), hpToReal]
  have hboxmeas : MeasurableSet (Sharpness.lineAnnulusBox (d := d) epsilon) :=
    Sharpness.lineAnnulusBox_measurable epsilon
  have hboxfinite : volume (Sharpness.lineAnnulusBox (d := d) epsilon) < ⊤ :=
    Sharpness.lineAnnulusBox_volume_lt_top epsilon
  have hmeasure : μ T ≤ ENNReal.ofReal (2 * (4 * epsilon) ^ (d - 1)) := by
    rw [Measure.restrict_apply hTmeas]
    have hset : T ∩ originCube (d := d) R ⊆
        Sharpness.lineAnnulusBox (d := d) epsilon := by
      intro x hx
      have hxR : x ∈ originCube (d := d) R := hx.2
      have hxT : x ∈ T := hx.1
      exact Sharpness.mem_lineAnnulusBox (hsubset hxR) (lt_of_lt_of_eq
        (show Sharpness.transverseNorm x < 2 * epsilon from hxT) rfl).le
    have hvol : volume (T ∩ originCube (d := d) R) ≤
        volume (Sharpness.lineAnnulusBox (d := d) epsilon) := measure_mono hset
    have hboxeq : volume (Sharpness.lineAnnulusBox (d := d) epsilon) =
        ENNReal.ofReal (2 * (4 * epsilon) ^ (d - 1)) := by
      calc
        _ = ENNReal.ofReal (volume (Sharpness.lineAnnulusBox (d := d) epsilon)).toReal :=
          (ENNReal.ofReal_toReal hboxfinite.ne).symm
        _ = _ := by rw [Sharpness.lineAnnulusBox_volume (le_of_lt hepsilon)]
    exact hvol.trans_eq hboxeq
  have hupperPower :
      (μ T) ^ (1 / eta) ≤ ENNReal.ofReal
        ((2 * (4 * epsilon) ^ (d - 1)) ^ (1 / eta)) := by
    calc
      _ ≤ (ENNReal.ofReal (2 * (4 * epsilon) ^ (d - 1))) ^ (1 / eta) :=
        ENNReal.rpow_le_rpow hmeasure (by positivity)
      _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
  have hupperNorm :
      eLpNorm f p μ ≤ ENNReal.ofReal
        ((5 / 4) * (2 * (4 * epsilon) ^ (d - 1)) ^ (1 / eta)) := by
    calc
      _ ≤ eLpNorm (T.indicator (fun _ : Vec d => (5 / 4 : ℝ))) p μ := hmono
      _ = ENNReal.ofReal (5 / 4) * (μ T) ^ (1 / eta) := hformula
      _ ≤ ENNReal.ofReal (5 / 4) * ENNReal.ofReal
          ((2 * (4 * epsilon) ^ (d - 1)) ^ (1 / eta)) := by
        gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  have hupperId :
      (5 / 4) * (2 * (4 * epsilon) ^ (d - 1)) ^ (1 / eta) =
        B * epsilon ^ (n / eta) := by
    rw [show 2 * (4 * epsilon) ^ (d - 1) =
        upperBase * epsilon ^ (d - 1) by
          dsimp [upperBase]
          rw [mul_pow]
          ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hexp : ((d - 1 : ℕ) : ℝ) * (1 / eta) = n / eta := by rw [hn]; ring
    rw [← Real.rpow_natCast epsilon (d - 1), ← Real.rpow_mul (le_of_lt hepsilon), hexp]
    dsimp [B]
    ring
  have hlowerBox :
      eLpNorm f p μ ≥ ENNReal.ofReal
        ((3 / 4) * ((1 / 2) * (epsilon / d) ^ (d - 1)) ^ (1 / eta)) := by
    let S := polynomialNormBox (d := d) epsilon
    have hSmeas : MeasurableSet S := polynomialNormBox_measurable epsilon
    have hScube : S ⊆ originCube (d := d) R := by
      intro x hx
      exact polynomialNormBox_subset_cube hd hepsilon hepsilon8 hR x hx
    have hSline : S ⊆ Sharpness.lineAnnulusBox (d := d) epsilon := by
      intro x hx
      have hxR := hScube hx
      have hx1 : x ∈ originCube (d := d) 1 := hsubset hxR
      have htrsq := polynomialNormBox_transverse_sq (le_of_lt hepsilon) hx
      have htr : Sharpness.transverseNorm x ≤ 2 * epsilon := by
        apply (sq_le_sq₀ (Sharpness.lineRadius_nonneg x) (by positivity)).1
        calc
          Sharpness.transverseNorm x ^ 2 ≤ epsilon ^ 2 / (4 * d) := htrsq
          _ ≤ (2 * epsilon) ^ 2 := by
            rw [div_le_iff₀ (by positivity : 0 < (4 : ℝ) * d)]
            have hdpos : (1 : ℝ) ≤ 4 * d := by
              have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
              nlinarith
            nlinarith [sq_nonneg epsilon, mul_le_mul_of_nonneg_left hdpos (sq_nonneg epsilon)]
      exact Sharpness.mem_lineAnnulusBox hx1 htr
    have hSfinite : volume S < ⊤ :=
      (measure_mono hSline).trans_lt hboxfinite
    have hSvol : (μ S) = ENNReal.ofReal ((1 / 2) * (epsilon / d) ^ (d - 1)) := by
      rw [Measure.restrict_apply hSmeas]
      rw [Set.inter_eq_left.mpr hScube]
      calc
        volume S = ENNReal.ofReal (volume S).toReal :=
          (ENNReal.ofReal_toReal hSfinite.ne).symm
        _ = _ := by rw [polynomialNormBox_volume (le_of_lt hepsilon)]
    have hSpositive : ∀ x ∈ S, 3 / 4 ≤ f x := by
      intro x hx
      exact polynomialNormBox_positivePart_lower hd hepsilon hepsilon8 hR hR1 hx
    have hSdom :
        ∀ᵐ x ∂μ, ‖S.indicator (fun _ : Vec d => (3 / 4 : ℝ)) x‖ₑ ≤ ‖f x‖ₑ := by
      filter_upwards [ae_restrict_mem (originCube_isOpen (d := d) R).measurableSet] with x hxR
      by_cases hxS : x ∈ S
      · have hfx0 : 0 ≤ f x := by simp [f, positivePart]
        have hfx := hSpositive x hxS
        rw [Set.indicator_of_mem hxS,
          Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4),
          Real.enorm_eq_ofReal hfx0]
        exact ENNReal.ofReal_le_ofReal hfx
      · rw [Set.indicator_of_notMem hxS]
        simp
    have hSmeasFunc :
        AEStronglyMeasurable (S.indicator (fun _ : Vec d => (3 / 4 : ℝ))) μ :=
      AEStronglyMeasurable.indicator₀ (by fun_prop) hSmeas.nullMeasurableSet
    have hSmono :
        eLpNorm (S.indicator (fun _ : Vec d => (3 / 4 : ℝ))) p μ ≤ eLpNorm f p μ :=
      eLpNorm_mono_enorm_ae hSmeasFunc hSdom
    have hSformula :
        eLpNorm (S.indicator (fun _ : Vec d => (3 / 4 : ℝ))) p μ =
          ENNReal.ofReal (3 / 4) * (μ S) ^ (1 / eta) := by
      rw [eLpNorm_indicator_const hSmeas.nullMeasurableSet hp0 hptop]
      simp [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4), hpToReal]
    calc
      eLpNorm f p μ ≥ eLpNorm (S.indicator (fun _ : Vec d => (3 / 4 : ℝ))) p μ := hSmono
      _ = ENNReal.ofReal (3 / 4) * (μ S) ^ (1 / eta) := hSformula
      _ = ENNReal.ofReal
          ((3 / 4) * ((1 / 2) * (epsilon / d) ^ (d - 1)) ^ (1 / eta)) := by
        rw [hSvol, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  have hlowerId :
      (3 / 4) * ((1 / 2) * (epsilon / d) ^ (d - 1)) ^ (1 / eta) =
        A * epsilon ^ (n / eta) := by
    rw [show (1 / 2) * (epsilon / d) ^ (d - 1) = lowerBase * epsilon ^ (d - 1) by
      dsimp [lowerBase]
      rw [div_pow]
      ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hexp : ((d - 1 : ℕ) : ℝ) * (1 / eta) = n / eta := by rw [hn]; ring
    rw [← Real.rpow_natCast epsilon (d - 1), ← Real.rpow_mul (le_of_lt hepsilon), hexp]
    dsimp [A]
    ring
  constructor
  · calc
      ENNReal.ofReal (C⁻¹ * epsilon ^ (n / eta)) ≤
          ENNReal.ofReal (A * epsilon ^ (n / eta)) := by
            apply ENNReal.ofReal_le_ofReal
            have hcinv : C⁻¹ ≤ A := by
              have hCA : A⁻¹ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
              have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
              have hAinvpos : 0 < A⁻¹ := inv_pos.mpr hA
              rw [← inv_inv A]
              exact (inv_le_inv₀ hCpos hAinvpos).2 hCA
            exact mul_le_mul_of_nonneg_right hcinv (Real.rpow_nonneg (le_of_lt hepsilon) _)
      _ ≤ eLpNorm f p μ := by rw [← hlowerId]; exact hlowerBox
  · calc
      eLpNorm f p μ ≤ ENNReal.ofReal (B * epsilon ^ (n / eta)) := by
        rw [← hupperId]
        exact hupperNorm
      _ ≤ ENNReal.ofReal (C * epsilon ^ (n / eta)) := by
        apply ENNReal.ofReal_le_ofReal
        have hBC : B ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
        exact mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg (le_of_lt hepsilon) _)

end

end CoarseDeGiorgi.SharpnessExamples
