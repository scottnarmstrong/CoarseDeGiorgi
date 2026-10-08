import CoarseDeGiorgi.Weighted.PairOperations
import CoarseDeGiorgi.Weighted.LowerSpecMean
import CoarseDeGiorgi.Weighted.HarmonicProperties
import CoarseDeGiorgi.Weighted.Truncation.Closure
import CoarseDeGiorgi.Statements.IsWeightedSolution

/-! Linear structure of zero-boundary pairs and weighted solutions. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Zero-boundary pairs are closed under scalar multiplication. -/
theorem memH1a0_smul [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (c : ℝ) : MemH1a0 a V (c • u) (c • G) := by
  obtain ⟨f, htf, hLf⟩ := Weighted.MemH1a0.supportedGraph_tendsto hV hne ha hu
  have hiu := (memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hu)).1
  let F := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hu)
  have hLs : Tendsto (fun n => eLpNorm ((c • f n).val - c • u) 1
      (volume.restrict V)) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul hLf (Or.inr (by simp : ‖c‖ₑ ≠ ⊤))
    simpa only [mul_zero, Submodule.coe_smul_of_tower, ← smul_sub,
      eLpNorm_const_smul] using hh
  have hts : Tendsto (fun n => supportedGraphMap hV.isOpen ha (c • f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (c • u),
        ((c • F : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_smul, ← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, F,
      volumeAverage_smul, UniformSpace.Completion.coe_smul] using htf.const_smul c
  have hout := memH1a0_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => c • f n) (G := c • F) (hiu.smul c) hLs hts
  simpa only [show (c • F).field = c • F.field from rfl,
    F, memH1aEnergyField_field] using hout

/-- Weighted solutions are closed under scalar multiples. -/
theorem solution_smul [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a V u G) (c : ℝ) : IsWeightedSolution a V (c • u) (c • G) := by
  refine ⟨LowerResponseImpl.lower_memH1a_smul hV hne ha hu.1 c, ?_⟩
  intro φ hφ hc hs
  obtain ⟨hi, h0⟩ := hu.2 φ hφ hc hs
  have e : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) ((c • G) x))) =
      fun x => c * vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
    funext x
    simp only [Pi.smul_apply, matVecMul_smul, vecDot_smul_right]
  rw [e]
  exact ⟨hi.const_mul c, by rw [integral_const_mul, h0, mul_zero]⟩

/-- Weighted solutions are closed under addition. -/
theorem solution_add [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u v : Vec d → ℝ} {G K : Vec d → Vec d}
    (hu : IsWeightedSolution a V u G) (hv : IsWeightedSolution a V v K) :
    IsWeightedSolution a V (u + v) (G + K) := by
  refine ⟨MemH1a.add hV hne ha hu.1 hv.1, ?_⟩
  intro φ hφ hc hs
  obtain ⟨hi, h0⟩ := hu.2 φ hφ hc hs
  obtain ⟨hj, k0⟩ := hv.2 φ hφ hc hs
  have e : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) ((G + K) x))) =
      fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) +
        vecDot (smoothGrad φ x) (matVecMul (a x) (K x)) := by
    funext x
    simp only [Pi.add_apply, matVecMul_add, vecDot_add_right]
  rw [e]
  exact ⟨hi.add hj, by rw [integral_add hi hj, h0, k0, add_zero]⟩

/-- `MemH1a0` is invariant under a.e. changes. -/
theorem memH1a0_congr_ae {a : CoeffField d}
    {V : Set (Vec d)} {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a0 a V u G)
    (huv : u =ᵐ[volume.restrict V] v)
    (hGH : G =ᵐ[volume.restrict V] H) :
    MemH1a0 a V v H := by
  obtain ⟨huM, hGM, f, hf, hc, ht, hE⟩ := hu
  refine ⟨huM.congr huv, hGM.congr hGH, f, hf, hc, ?_, ?_⟩
  · intro K hK hKV
    have heq := ae_mono (Measure.restrict_mono hKV le_rfl) huv
    convert ht K hK hKV using 1
    funext n
    apply lintegral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · convert hE using 1
    funext n
    exact Weighted.energy_congr_ae (EventuallyEq.rfl.sub hGH.symm)

theorem weightedSolution_congr_ae [NeZero d]
    {a : CoeffField d} {V : Set (Vec d)}
    {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : IsWeightedSolution a V u G)
    (huv : u =ᵐ[volume.restrict V] v)
    (hGH : G =ᵐ[volume.restrict V] H) :
    IsWeightedSolution a V v H := by
  refine ⟨Weighted.MemH1a.congr_ae hu.1 huv hGH, ?_⟩
  intro φ hφ hcompact hsupp
  have htest := hu.2 φ hφ hcompact hsupp
  have hpair :
      (fun x => vecDot (smoothGrad φ x)
        (Homogenization.matVecMul (a x) (G x))) =ᵐ[volume.restrict V]
      (fun x => vecDot (smoothGrad φ x)
        (Homogenization.matVecMul (a x) (H x))) := by
    filter_upwards [hGH] with x hx
    rw [hx]
  refine ⟨htest.1.congr hpair, ?_⟩
  rw [← integral_congr_ae hpair]
  exact htest.2


/-- Linearity of the harmonic replacement on one cell. -/
theorem replacement_linear [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (c₁ c₂ : ℝ)
    {L L₁ L₂ H H₁ H₂ : Vec d → ℝ} {G G₁ G₂ GH GH₁ GH₂ : Vec d → Vec d}
    (hL : L =ᵐ[volume.restrict V] fun x => c₁ * L₁ x + c₂ * L₂ x)
    (hG : G =ᵐ[volume.restrict V] fun x => c₁ • G₁ x + c₂ • G₂ x)
    (hs : IsWeightedSolution a V H GH) (hs₁ : IsWeightedSolution a V H₁ GH₁)
    (hs₂ : IsWeightedSolution a V H₂ GH₂)
    (h0 : MemH1a0 a V (fun x => H x - L x) (fun x => GH x - G x))
    (h₁ : MemH1a0 a V (fun x => H₁ x - L₁ x) (fun x => GH₁ x - G₁ x))
    (h₂ : MemH1a0 a V (fun x => H₂ x - L₂ x) (fun x => GH₂ x - G₂ x)) :
    (H =ᵐ[volume.restrict V] fun x => c₁ * H₁ x + c₂ * H₂ x) ∧
      (GH =ᵐ[volume.restrict V] fun x => c₁ • GH₁ x + c₂ • GH₂ x) := by
  have hK : IsWeightedSolution a V (c₁ • H₁ + c₂ • H₂) (c₁ • GH₁ + c₂ • GH₂) :=
    solution_add hV hne ha (solution_smul hV hne ha hs₁ c₁) (solution_smul hV hne ha hs₂ c₂)
  have hk0 : MemH1a0 a V (fun x => (c₁ • H₁ + c₂ • H₂) x - L x)
      (fun x => (c₁ • GH₁ + c₂ • GH₂) x - G x) := by
    have := Weighted.MemH1a0.add hV hne ha (memH1a0_smul hV hne ha h₁ c₁)
      (memH1a0_smul hV hne ha h₂ c₂)
    refine memH1a0_congr_ae this ?_ ?_
    · filter_upwards [hL] with x hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx]
      ring
    · filter_upwards [hG] with x hx
      simp only [Pi.add_apply, Pi.smul_apply, hx]
      rw [smul_sub, smul_sub]
      abel
  have := Weighted.harmonic_replacement_unique hV hne ha hs hK h0 hk0
  exact this

end CoarseDeGiorgi.Whitney.Harmonic
