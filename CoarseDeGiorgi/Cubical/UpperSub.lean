module

public import CoarseDeGiorgi.Cubical.Glue
public import CoarseDeGiorgi.Cubical.PsdSum
public import CoarseDeGiorgi.Weighted.UpperSpecMinimum
public import CoarseDeGiorgi.Statements.UpperResponse

/-! # Countable upper subadditivity (quadratic form version) -/

@[expose] public section

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory CoarseDeGiorgi.Whitney
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

/-- A set of full measure inside `U` has the same integrals as `U`. -/
lemma ae_eq_of_cover {U : Set (Vec d)} {W : Set (Vec d)} (hWU : W ⊆ U)
    (hcover : volume (U \ W) = 0) : U =ᵐ[volume] W := by
  rw [ae_eq_set]
  refine ⟨hcover, ?_⟩
  rw [Set.sdiff_eq_empty.mpr hWU]; simp

theorem upper_quadratic_countable [NeZero d] {a : CoeffField d} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (hVU : ∀ i, V i ⊆ U) (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : volume (U \ ⋃ i, V i) = 0) (e : Vec d) :
    ∃ S : ℝ, HasSum (fun i => (volume (V i)).toReal *
        qf (upperResponse a (V i) (hV i) (hV₀ i) (haV i)) e) S ∧
      (volume U).toReal * qf (upperResponse a U hU hU₀ ha) e ≤ S := by
  classical
  have hbaseline : MemH1a a U (Weighted.responseAffine e) (fun _ => e) :=
    Weighted.responseAffine_memH1a hU ha e
  have hfin : weightedEnergy a U (fun _ => e) < ⊤ := Weighted.MemH1a.energy_lt_top hU.isOpen ha hbaseline
  obtain ⟨ξ, H, hξ, hH⟩ := glue_exists hU hU₀ ha V hV hV₀ hVU hdisj (fun _ => e) (fun _ => e)
    (fun _ _ _ => rfl) hfin
  let cellPair (i : ι) := liftCellPair (hV i) (hV₀ i) (lift_coeff_mono ha (hVU i)) e
  have hcellPair (i : ι) := liftCellPair_spec (hV i) (hV₀ i) (lift_coeff_mono ha (hVU i)) e
  let valWhole : Vec d → ℝ := Weighted.responseAffine e + ξ
  let gradWhole : Vec d → Vec d := (fun _ => e) + H
  have hwhole : MemH1a a U valWhole gradWhole :=
    Weighted.MemH1a.add hU hU₀ ha hbaseline (Weighted.MemH1a0.memH1a ha hξ)
  have hboundary : MemH1a0 a U (fun x => valWhole x - Weighted.responseAffine e x)
      (fun x => gradWhole x - e) := by
    convert hξ using 1 <;> funext x <;> simp only [valWhole, gradWhole, Pi.add_apply] <;> abel
  let energyWhole : Vec d → ℝ := fun x => vecDot (gradWhole x) (matVecMul (a x) (gradWhole x))
  have hEnergyInt : IntegrableOn energyWhole U :=
    Weighted.quadratic_integrable ha hwhole.2.1 (Weighted.MemH1a.energy_lt_top hU.isOpen ha hwhole)
  have hmin := Weighted.UpperResponseImpl.upper_affine_minimum hU hU₀ ha e
  have hleast := hmin.2 ⟨valWhole, gradWhole, hwhole, hboundary, rfl⟩
  have hvolU : 0 < (volume U).toReal :=
    ENNReal.toReal_pos (hU.isOpen.measure_pos volume hU₀).ne'
      hU.isBoundedDomain.isBounded.measure_lt_top.ne
  have hmeas : ∀ i, MeasurableSet (V i) := fun i => (hV i).isOpen.measurableSet
  have hUnion : (⋃ i, V i) ⊆ U := Set.iUnion_subset hVU
  have hint : ∫ x in U, energyWhole x = ∫ x in ⋃ i, V i, energyWhole x :=
    setIntegral_congr_set (ae_eq_of_cover hUnion hcover)
  have hsum := hasSum_integral_iUnion hmeas hdisj (hEnergyInt.mono_set hUnion)
  refine ⟨∫ x in ⋃ i, V i, energyWhole x, ?_, ?_⟩
  · convert hsum using 1
    funext i
    have hvolV : 0 < (volume (V i)).toReal :=
      ENNReal.toReal_pos ((hV i).isOpen.measure_pos volume (hV₀ i)).ne'
        (hV i).isBoundedDomain.isBounded.measure_lt_top.ne
    have hb : MemH1a0 a (V i) (fun x => (cellPair i).1 x - (vecDot e x + 0))
        (fun x => (cellPair i).2 x - e) := by
      convert (hcellPair i).2 using 1
      funext x; simp [Weighted.responseAffine]; rfl
    have hq := Weighted.UpperResponseImpl.upper_affine_energy (hV i) (hV₀ i) (haV i) e 0
      (hcellPair i).1 hb
    have hcongr : ∫ x in V i, energyWhole x =
        ∫ x in V i, vecDot ((cellPair i).2 x) (matVecMul (a x) ((cellPair i).2 x)) := by
      apply integral_congr_ae
      filter_upwards [hH i, ae_restrict_mem (hmeas i)] with x hx _
      simp only [energyWhole, gradWhole, Pi.add_apply, hx]
      simp only [Pi.sub_apply, add_sub_cancel, cellPair]
    rw [hcongr]
    change _ = ∫ x in V i, _
    have hq' : qf (upperResponse a (V i) (hV i) (hV₀ i) (haV i)) e =
        (volume (V i)).toReal⁻¹ * ∫ x in V i,
          vecDot ((cellPair i).2 x) (matVecMul (a x) ((cellPair i).2 x)) := hq
    rw [hq', ← mul_assoc, mul_inv_cancel₀ hvolV.ne', one_mul]
  · rw [← hint]
    have := hleast
    change qf (upperResponse a U hU hU₀ ha) e ≤ (volume U).toReal⁻¹ * ∫ x in U, energyWhole x at this
    calc _ ≤ (volume U).toReal * ((volume U).toReal⁻¹ * ∫ x in U, energyWhole x) :=
          mul_le_mul_of_nonneg_left this hvolU.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hvolU.ne', one_mul]

end CoarseDeGiorgi.Cubical
