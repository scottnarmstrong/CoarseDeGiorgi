module

public import CoarseDeGiorgi.Endpoint.Capacitary.Bounds
public import CoarseDeGiorgi.Endpoint.Source.Main

/-! Combining the remote local bound with the interior weak Harnack estimate. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set
open scoped ENNReal

variable {d : ℕ}

/-- The nonnegative essential infimum of a real function is finite on a nonempty open domain. -/
theorem capacitary_essInf_ne_top {U : Set (Vec d)} (hU : IsOpen U) (hne : U.Nonempty)
    (u : Vec d → ℝ) : nonnegativeEssInf U u ≠ ⊤ := by
  have hμ : volume.restrict U ≠ 0 := by
    intro h
    have hvol := congrArg (fun μ : Measure (Vec d) => μ univ) h
    rw [Measure.restrict_apply_univ] at hvol
    have hvol' : volume U = 0 := by simpa using hvol
    exact (hU.measure_pos volume hne).ne' hvol'
  have : NeBot (ae (volume.restrict U)) := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ := (ae_essInf_le (f := fun x => ENNReal.ofReal (u x))
    (μ := volume.restrict U)).exists
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx

/-- Step 3: the two interior estimates control the potential on the remote obstacle. -/
theorem capacitary_remote_bound (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {u V : Vec d → ℝ} {Gv : Vec d → Vec d}
    (hV : MemH1a0 a (originCube 1) V Gv)
    (hu0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (hV0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ V x)
    (hVu : ∀ᵐ x ∂volume.restrict (originCube 1), V x ≤ u x)
    (η X Y : ℝ)
    (hweak : eLpNorm u (ENNReal.ofReal η) (volume.restrict (originCube (15 / 16))) ≤
      ENNReal.ofReal (Real.exp X) * nonnegativeEssInf (originCube (15 / 16)) u)
    (hremote : eLpNorm V ⊤ (volume.restrict (remoteCube d (1 / 2))) ≤
      ENNReal.ofReal (Real.exp Y) * eLpNorm V (ENNReal.ofReal η)
        (volume.restrict (remoteCube d 1))) :
    eLpNorm V ⊤ (volume.restrict (remoteCube d (1 / 2))) ≤
      ENNReal.ofReal (Real.exp (X + Y)) * nonnegativeEssInf (originCube (1 / 2)) u := by
  have hRI : remoteCube d 1 ⊆ originCube (15 / 16) :=
    fun x hx => closure_remoteCube_subset_interior (subset_closure hx)
  have hRU := hRI.trans (originCube_mono' (by norm_num) one_pos (by norm_num))
  have hVmem := Weighted.MemH1a0.memH1a ha hV
  have hm := hVmem.1.mono_measure (Measure.restrict_mono hRU le_rfl)
  have hnorm : eLpNorm V (ENNReal.ofReal η) (volume.restrict (remoteCube d 1)) ≤
      eLpNorm u (ENNReal.ofReal η) (volume.restrict (originCube (15 / 16))) := by
    apply (eLpNorm_mono_ae hm ?_).trans
      (eLpNorm_mono_measure u (Measure.restrict_mono hRI le_rfl))
    filter_upwards [ae_mono (Measure.restrict_mono hRU le_rfl) hu0,
      ae_mono (Measure.restrict_mono hRU le_rfl) hV0,
      ae_mono (Measure.restrict_mono hRU le_rfl) hVu] with x hxu hxV hxVu
    simpa only [Real.norm_eq_abs, abs_of_nonneg hxu, abs_of_nonneg hxV] using hxVu
  calc
    _ ≤ ENNReal.ofReal (Real.exp Y) * eLpNorm V (ENNReal.ofReal η)
        (volume.restrict (remoteCube d 1)) := hremote
    _ ≤ ENNReal.ofReal (Real.exp Y) *
        (ENNReal.ofReal (Real.exp X) * nonnegativeEssInf (originCube (15 / 16)) u) :=
      mul_le_mul_right (hnorm.trans hweak) _
    _ ≤ ENNReal.ofReal (Real.exp Y) *
        (ENNReal.ofReal (Real.exp X) * nonnegativeEssInf (originCube (1 / 2)) u) := by
      apply mul_le_mul_right
      exact mul_le_mul_right (capacitary_essInf_mono
        (originCube_mono' (by norm_num) (by norm_num) (by norm_num)) u) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, add_comm Y X]

/-- An `L∞` bound gives the literal obstacle bound needed by the capacitary test. -/
theorem capacitary_ae_le_of_norm_top {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) {L : ℝ} (hL : 0 ≤ L)
    (hnorm : eLpNorm f ⊤ (volume.restrict U) ≤ ENNReal.ofReal L) :
    ∀ᵐ x ∂volume.restrict U, f x ≤ L := by
  rw [eLpNorm_exponent_top hf] at hnorm
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume.restrict U)] with x hx
  have h := hx.trans hnorm
  rw [Real.enorm_eq_ofReal_abs] at h
  exact (le_abs_self (f x)).trans ((ENNReal.ofReal_le_ofReal_iff hL).mp h)

end CoarseDeGiorgi.Endpoint
