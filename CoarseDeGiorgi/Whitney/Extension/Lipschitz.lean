import CoarseDeGiorgi.Whitney.Extension.CellLipschitz
import CoarseDeGiorgi.Whitney.Extension.LipschitzGlue

/-!
# Lipschitz extension of the boundary data

The last paragraph of the proof of Proposition `p.affine.extension`.
-/

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem one_le_sqrt_of_one_le (hd : 1 ≤ d) : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hdr

/-- near the surface the extension is close to the data -/
theorem boundary_bound (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    {a b : Vec d} (ha : a ∈ cubeSurface τ) (hb1 : τ / 2 < ‖b‖) (hb2 : ‖b‖ < τ / 2 + h / 4) :
    |whitneyAffineExtension τ h f hτ0 hτ1 b - f a| ≤
      (Real.sqrt (d : ℝ) + 2) * K * euclidDist b a := by
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 := one_le_sqrt_of_one_le hd
  set s := Real.sqrt (d : ℝ) with hs
  have hbext : b ∈ (closedReferenceCube (d := d) τ)ᶜ := fun hb =>
    absurd (norm_le_of_mem_ref hτ hb) (not_le.mpr hb1)
  obtain ⟨D, hD, hbD⟩ := (whitney_cubes hτ0 hτ1).2.1 b hbext
  set ℓ := cubeScaleFactor D with hℓ
  have hp : 0 < ℓ := cubeScaleFactor_pos D
  set gb := ‖b‖ - τ / 2 with hgb
  have hgl : 2 * ℓ < gb := gap_lower hτ0 hτ1 hD hbD
  have hna : ‖a‖ = τ / 2 := ha
  set E := euclidDist b a with hE
  have hE0 : 0 ≤ E := euclidDist_nonneg _ _
  have hgE : gb ≤ E := by
    have h1 : ‖b‖ ≤ ‖a‖ + ‖b - a‖ := by
      have := norm_add_le a (b - a); simpa [add_comm] using this
    have h2 := norm_sub_le_euclidDist b a
    linarith only [h1, h2, hna, hgb, hE]
  have hM : 0 ≤ (s + 2) * K * E := by positivity
  -- the value at every point of the cube
  have key : ∀ w : Vec d, w ∈ closedTriadicCube D →
      |seedCutoff ((‖w‖ - τ / 2) / h) * patchAvg τ f w - f a| ≤ (s + 2) * K * E := by
    intro w hw
    have hwb : ‖w - b‖ ≤ ℓ := norm_sub_le_of_mem_cube hw hbD
    have hnw : ‖w‖ ≤ ‖b‖ + ‖w - b‖ := by
      have := norm_add_le b (w - b); simpa using this
    have hcut : seedCutoff ((‖w‖ - τ / 2) / h) = 1 := by
      apply seedCutoff_eq_one
      rw [div_le_iff₀ hh]
      linarith only [hnw, hwb, hgl, hb2, hh1, hh, hgb]
    rw [hcut, one_mul]
    have hl1 : ℓ < 1 := by linarith only [hgl, hb2, hh1, hh, hgb]
    apply abs_average_sub_le hτ (measurableSet_whitneyPatch τ w) (whitneyPatch_subset_surface τ w)
      (whitneyPatch_measure_pos hd hτ0 hτ1 hD hw hl1) hf
    intro y hy
    have hysurf := whitneyPatch_subset_surface τ w hy
    refine (hLip y hysurf a ha).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left (?_ : euclidDist y a ≤ (s + 2) * E) hK)
      (le_of_eq (by ring))
    have hy2 := hy.2
    simp only [mem_ofPred_eq] at hy2
    have hwgap : ‖w‖ - τ / 2 < 3 * gb / 2 := by linarith only [hnw, hwb, hgl, hgb]
    have hy3 : euclidDist y (seedProjection τ w) ≤ gb := by
      have : (‖w‖ - τ / 2) / (100 * (d : ℝ)) ≤ gb := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 < gb := by linarith only [hgl, hp]
        nlinarith only [hwgap, hdr, this]
      linarith only [hy2, this]
    have hpa : seedProjection τ a = a := seedProjection_eq_self hna.le
    have hy4 : euclidDist (seedProjection τ w) a ≤ euclidDist w a := by
      have := seedProjection_euclidDist_le τ w a
      rwa [hpa] at this
    have hy5 : euclidDist w a ≤ euclidDist w b + euclidDist b a := euclidDist_triangle _ _ _
    have hy6 : euclidDist w b ≤ s * ℓ :=
      (euclidDist_le_sqrt_mul w b).trans (mul_le_mul_of_nonneg_left hwb (Real.sqrt_nonneg _))
    have hy7 := euclidDist_triangle y (seedProjection τ w) a
    have hsl : s * ℓ ≤ s * (E / 2) := mul_le_mul_of_nonneg_left (by linarith only [hgl, hgE]) (by positivity)
    nlinarith only [hy3, hy4, hy5, hy6, hy7, hsl, hgE, hE0, hs1]
  obtain ⟨z, z', hz, hz', h1, h2⟩ := range_bound_ext (h := h) hτ0 hτ1 f hD hbD
  have e1 := key z.1 hz
  have e2 := key z'.1 hz'
  rw [← whitneyFreeValue_eq] at e1 e2
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith only [e1.1, e1.2, e2.1, e2.2, h1, h2]

/-- local Lipschitz bound at points of the open exterior -/
theorem local_lipschitz_exterior (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K B : ℝ} (hK : 0 ≤ K)
    (hB : 0 ≤ B)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    (hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B) {a : Vec d} (ha : τ / 2 < ‖a‖) :
    ∀ᶠ b in 𝓝 a, |whitneyAffineExtension τ h f hτ0 hτ1 b - whitneyAffineExtension τ h f hτ0 hτ1 a| ≤
      C32 d * (2 * B / h + 2 * Real.sqrt (d : ℝ) * K) * euclidDist b a := by
  classical
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  set r := (‖a‖ - τ / 2) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith only [ha]
  have hext : ∀ y ∈ Metric.closedBall a r, y ∈ (closedReferenceCube (d := d) τ)ᶜ := by
    intro y hy hyr
    have h1 := norm_le_of_mem_ref hτ hyr
    have h2 : ‖a‖ ≤ ‖y‖ + ‖a - y‖ := by
      have := norm_add_le y (a - y); simpa using this
    have h3 : ‖a - y‖ ≤ r := by
      rw [← dist_eq_norm, dist_comm]; exact Metric.mem_closedBall.mp hy
    linarith only [h1, h2, h3, hr, ha]
  have hT := (whitney_cubes hτ0 hτ1).2.2.1 (Metric.closedBall a r) (isCompact_closedBall a r) hext
  set S := {D : TriadicCube d | D ∈ whitneyCubes τ ∧
        (closedTriadicCube (d := d) D ∩ Metric.closedBall a r).Nonempty} with hS
  have hSf : {D : {D : TriadicCube d // D ∈ whitneyCubes τ} | D.1 ∈ S}.Finite :=
    hT.preimage Subtype.val_injective.injOn
  have hcellf : {cell : ExteriorCell d τ | cell.1.1 ∈ S}.Finite := by
    have : {cell : ExteriorCell d τ | cell.1.1 ∈ S} =
        {D : {D : TriadicCube d // D ∈ whitneyCubes τ} | D.1 ∈ S} ×ˢ
          (univ : Set ((Fin d → Fin 3) × Equiv.Perm (Fin d))) := by
      ext cell; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [this]
    exact hSf.prod Set.finite_univ
  have hloc := glueFiniteClosedCover_local_bound hcellf.toFinset
    (fun cell : ExteriorCell d τ => closure (exteriorCellSet cell)) (Metric.ball a r)
    (whitneyAffineExtension τ h f hτ0 hτ1)
    (C32 d * (2 * B / h + 2 * Real.sqrt (d : ℝ) * K)) (fun y x => euclidDist y x)
    (fun _ _ => isClosed_closure)
    (by
      intro y hy
      have hyc : y ∈ Metric.closedBall a r := Metric.ball_subset_closedBall hy
      obtain ⟨D, hD, hyD⟩ := (whitney_cubes hτ0 hτ1).2.1 y (hext y hyc)
      obtain ⟨cell, hcD, hycl⟩ := WhitneyInterp.exists_cell_of_mem_cube hD hyD
      refine ⟨cell, ?_, hycl⟩
      rw [Set.Finite.mem_toFinset]
      show cell.1.1 ∈ S
      rw [hcD]
      exact ⟨hD, y, hyD, hyc⟩)
    (fun cell _ x hx y hy => closure_cell_lipschitz hd hτ0 hτ1 hh hh1 hf hK hB hLip hbd cell hy hx)
    a
  rwa [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds a hr0)] at hloc

/-- The constant of the Lipschitz extension. -/
noncomputable def LipConst (d : ℕ) : ℝ := 10 * (C32 d + 1) * d

/-- the Lipschitz extension to the closed exterior with boundary values `f` -/
theorem exists_lipschitz_extension (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hh : 0 < h) (hh1 : h ≤ 1) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    (hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B) :
    ∃ F : Vec d → ℝ,
      (∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ, F x = whitneyAffineExtension τ h f hτ0 hτ1 x) ∧
      (∀ y ∈ cubeSurface τ, F y = f y) ∧
      ∀ x y : Vec d, τ / 2 ≤ ‖x‖ → τ / 2 ≤ ‖y‖ →
        |F x - F y| ≤ LipConst d * (K + B / h) * euclidDist x y := by
  classical
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 := one_le_sqrt_of_one_le hd
  set s := Real.sqrt (d : ℝ) with hs
  have hss : s * s = d := Real.mul_self_sqrt (by positivity)
  have hsd : s ≤ d := by nlinarith only [hss, hs1]
  have hC := C32_nonneg d
  set C := C32 d
  set Λ := LipConst d * (K + B / h) with hΛ
  set gx := whitneyAffineExtension τ h f hτ0 hτ1
  have hBh : 0 ≤ B / h := by positivity
  have hLd : LipConst d = 10 * (C + 1) * d := rfl
  have hΛ0 : 0 ≤ Λ := by rw [hΛ, hLd]; positivity
  -- constants
  have c1 : C * (2 * B / h + 2 * s * K) * s ≤ Λ := by
    rw [hΛ, hLd, mul_div_assoc]
    have e : C * (2 * (B / h) + 2 * s * K) * s = C * (2 * s * (B / h) + 2 * d * K) := by
      rw [← hss]; ring
    rw [e]
    have : s * (B / h) ≤ d * (B / h) := mul_le_mul_of_nonneg_right hsd hBh
    have h1 : 0 ≤ C * d * (B / h + K) := by positivity
    have h2 : 0 ≤ d * (B / h + K) := by positivity
    nlinarith only [this, h1, h2, hC, hdr, hK, hBh]
  have c2 : (s + 2) * K * s ≤ Λ := by
    rw [hΛ, hLd]
    have e : (s + 2) * K * s = (d + 2 * s) * K := by rw [← hss]; ring
    rw [e]
    have : (d + 2 * s) * K ≤ 3 * d * K := mul_le_mul_of_nonneg_right (by linarith only [hsd]) hK
    have h1 : 0 ≤ (C + 1) * d * (K + B / h) := by positivity
    have h2 : 0 ≤ C * d * K := by positivity
    have h3 : 0 ≤ d * (B / h) := by positivity
    nlinarith only [this, h1, h2, h3, hdr, hK, hC]
  have c3 : K * s ≤ (s + 2) * K * s := by
    have : 0 ≤ K * s := by positivity
    nlinarith only [this, hK, hs1]
  -- extension of the data
  have hfl : LipschitzOnWith ⟨K * s, by positivity⟩ f (cubeSurface τ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.dist_eq, dist_eq_norm]
    refine (hLip a ha b hb).trans ?_
    have he := mul_le_mul_of_nonneg_left (euclidDist_le_sqrt_mul a b) hK
    change K * euclidDist a b ≤ (K * s) * ‖a - b‖
    exact he.trans_eq (by ring)
  obtain ⟨gext, hg, hfg⟩ := hfl.extend_real
  let G : Vec d → ℝ := fun z => if τ / 2 < ‖z‖ then gx z else gext z
  have hgB (a b : Vec d) : |gext a - gext b| ≤ K * s * ‖a - b‖ := by
    have hb := hg.dist_le_mul a b
    rw [Real.dist_eq, dist_eq_norm] at hb
    exact hb
  have hgB' (a b : Vec d) : |gext b - gext a| ≤ Λ * ‖b - a‖ := by
    refine (hgB b a).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact c3.trans c2
  have hlocal : ∀ a : Vec d, ∀ᶠ b in 𝓝 a, |G b - G a| ≤ Λ * ‖b - a‖ := by
    intro a
    rcases lt_trichotomy ‖a‖ (τ / 2) with hin | hz | hout
    · have hn := continuous_norm.continuousAt.eventually (gt_mem_nhds hin)
      filter_upwards [hn] with b hb
      simp only [G, ite_eq_right (not_lt.mpr hin.le), ite_eq_right (not_lt.mpr hb.le)]
      exact hgB' a b
    · have hs' : a ∈ cubeSurface τ := hz
      have hGa : G a = f a := by
        simp only [G, hz, lt_self_iff_false, ite_false, ← hfg hs']
      have hn : ∀ᶠ b in 𝓝 a, ‖b‖ < τ / 2 + h / 4 :=
        continuous_norm.continuousAt.eventually (gt_mem_nhds (by show ‖a‖ < τ / 2 + h / 4; rw [hz]; linarith only [hh]))
      filter_upwards [hn] with b hb
      by_cases hbpos : τ / 2 < ‖b‖
      · rw [hGa]
        have he : G b = gx b := by simp only [G, ite_eq_left hbpos]
        rw [he]
        refine (boundary_bound hd hτ0 hτ1 hh hh1 hf hK hLip hs' hbpos hb).trans ?_
        have h1 := mul_le_mul_of_nonneg_left (euclidDist_le_sqrt_mul b a) (by positivity : 0 ≤ (s + 2) * K)
        have h2 := mul_le_mul_of_nonneg_right c2 (norm_nonneg (b - a))
        refine h1.trans ?_
        calc _ = (s + 2) * K * s * ‖b - a‖ := by ring
          _ ≤ _ := h2
      · simp only [G, hz, lt_self_iff_false, ite_false, ite_eq_right hbpos]
        exact hgB' a b
    · have hn := continuous_norm.continuousAt.eventually (lt_mem_nhds hout)
      filter_upwards [hn, local_lipschitz_exterior hd hτ0 hτ1 hh hh1 hf hK hB hLip hbd hout] with
        b hb hbl
      simp only [G, ite_eq_left hb, ite_eq_left hout]
      have he := mul_le_mul_of_nonneg_left (euclidDist_le_sqrt_mul b a)
        (by positivity : 0 ≤ C * (2 * B / h + 2 * s * K))
      have hm := mul_le_mul_of_nonneg_right c1 (norm_nonneg (b - a))
      exact (hbl.trans he).trans (by simpa only [mul_assoc] using hm)
  have hext : ∀ x : Vec d, x ∈ (closedReferenceCube (d := d) τ)ᶜ ↔ τ / 2 < ‖x‖ := by
    intro x
    constructor
    · intro hx
      by_contra hn
      exact hx (fun i => (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i :
        |x i| ≤ ‖x‖).trans (not_lt.mp hn))
    · intro hx hxr
      exact absurd (norm_le_of_mem_ref hτ hxr) (not_le.mpr hx)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x hx
    simp only [G, ite_eq_left ((hext x).mp hx)]
  · intro y hy
    have hy' : ‖y‖ = τ / 2 := hy
    simp only [G, hy', lt_self_iff_false, ite_false, ← hfg hy]
  · intro x y _ _
    have := glueGlobal_bound_of_local G Λ hlocal y x
    exact this.trans (mul_le_mul_of_nonneg_left (norm_sub_le_euclidDist x y) hΛ0)

end

end CoarseDeGiorgi.WhitneyExt
