import CoarseDeGiorgi.Cubical.Interface
import CoarseDeGiorgi.Cubical.WhitneyLayer
import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube

/-! # Whitney bound for the response of one simplex -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

theorem simplex_whitney_bound (D : RespData d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (η : SimplexIndex d k) :
    ENNReal.ofReal ‖D.simplex a ha k η‖ ≤
      ∑' l, ∑ z ∈ Wl (simplexCell k η) k l,
        ENNReal.ofReal ((volume (cubeCell (k + l) z)).toReal / (volume (simplexCell k η)).toReal) *
          ENNReal.ofReal ‖D.cube a ha (k + l) z‖ := by
  classical
  set S := simplexCell k η with hSdef
  have hS := simplexCell_isOpenBoundedConvexDomain k η
  have hSO : S ⊆ originCube 1 := simplexCell_subset_originCube k η
  let V : (Σ l, ↥(Wl S k l)) → Set (Vec d) := fun p => cubeCell (k + p.1) p.2.1
  have hV : ∀ p, IsOpenBoundedConvexDomain (V p) := fun p =>
    cubeCell_isOpenBoundedConvexDomain _ _
  have hV₀ : ∀ p, (V p).Nonempty := fun p => cubeCell_nonempty _ _
  have haV : ∀ p, IsWeightedCoeffOn (V p) a := fun p => weightedCoeffOn_cubeCell _ a ha _
  have hbox : ∀ p, V p = box (k + p.1) (fun i => (p.2.1 i : ℕ)) := fun p => cubeCell_eq_box _ _
  have hVU : ∀ p, V p ⊆ S := fun p => by
    rw [hbox]; exact box_subset_of_mem_Wl p.2.2
  have hdisj : Pairwise (Function.onFun Disjoint V) := by
    intro p q hpq
    obtain ⟨l, z, hz⟩ := p
    obtain ⟨l', z', hz'⟩ := q
    simp only [Function.onFun, hbox]
    exact Wl_disjoint hz hz' (fun h => hpq (by
      obtain ⟨rfl, hh⟩ := Sigma.mk.inj h
      have e := eq_of_heq hh
      subst e
      rfl))
  have hcover : volume (S \ ⋃ p, V p) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (volume_gridNull (d := d))
    by_contra hng
    obtain ⟨j, z, hz, hmax, hxz⟩ := exists_maxGood hS.isOpen hSO k hx.1 hng
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmax.1
    apply hx.2
    refine Set.mem_iUnion.mpr ⟨⟨l, ⟨fun a => ⟨z a, hz a⟩, mem_Wl.mpr hmax⟩⟩, ?_⟩
    simp only [V, hbox]
    exact hxz
  obtain ⟨hsum, hle⟩ := D.norm_le_tsum a S hS (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η) V hV hV₀ haV hVU hdisj hcover
  have hnn : ∀ p, 0 ≤ (volume (V p)).toReal / (volume S).toReal *
      ‖D.R a (V p) (hV p) (hV₀ p) (haV p)‖ := fun p =>
    mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (norm_nonneg _)
  calc ENNReal.ofReal ‖D.simplex a ha k η‖
      ≤ ENNReal.ofReal (∑' p, (volume (V p)).toReal / (volume S).toReal *
        ‖D.R a (V p) (hV p) (hV₀ p) (haV p)‖) := ENNReal.ofReal_le_ofReal hle
    _ = ∑' p, ENNReal.ofReal ((volume (V p)).toReal / (volume S).toReal *
        ‖D.R a (V p) (hV p) (hV₀ p) (haV p)‖) := ENNReal.ofReal_tsum_of_nonneg hnn hsum
    _ = ∑' l, ∑ z ∈ Wl S k l, ENNReal.ofReal ((volume (cubeCell (k + l) z)).toReal /
          (volume S).toReal) * ENNReal.ofReal ‖D.cube a ha (k + l) z‖ := by
      rw [ENNReal.tsum_sigma']
      refine tsum_congr fun l => ?_
      refine (tsum_congr fun b => ?_).trans (Finset.tsum_subtype (Wl S k l) (fun z =>
        ENNReal.ofReal ((volume (cubeCell (k + l) z)).toReal / (volume S).toReal) *
          ENNReal.ofReal ‖D.cube a ha (k + l) z‖))
      exact ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end CoarseDeGiorgi.Cubical
