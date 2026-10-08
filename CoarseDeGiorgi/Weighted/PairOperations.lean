import CoarseDeGiorgi.Weighted.ZeroSpace

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Negation commutes with the literal source mean. -/
theorem volumeAverage_neg (u : Vec d → ℝ) : volumeAverage V (-u) = -volumeAverage V u := by
  unfold volumeAverage
  rw [show (fun x => (-u) x) = fun x => -u x by rfl, integral_neg]
  ring

/-- Addition preserves scalar L¹ convergence. -/
theorem tendsto_l1_add {f g : ℕ → Vec d → ℝ} {u v : Vec d → ℝ}
    (hfu : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hgv : Tendsto (fun n => eLpNorm (g n - v) 1 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((f n + g n) - (u + v)) 1 (volume.restrict V)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V) +
      eLpNorm (g n - v) 1 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [add_zero] using hfu.add hgv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro n
  dsimp only
  rw [show (f n + g n) - (u + v) = (f n - u) + (g n - v) by abel]
  exact eLpNorm_add_le (by simp)

/-- Negation preserves scalar L¹ convergence. -/
theorem tendsto_l1_neg {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ}
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (-f n - -u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  simpa only [show ∀ n, -f n - -u = -(f n - u) by intro n; abel, eLpNorm_neg] using ht

/-- Full weighted pairs are closed under addition. -/
theorem MemH1a.add [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a a V u G) (hv : MemH1a a V v H) : MemH1a a V (u + v) (G + H) := by
  obtain ⟨f, htf, hLf⟩ := hu.smoothGraph_tendsto hV hne ha
  obtain ⟨g, htg, hLg⟩ := hv.smoothGraph_tendsto hV hne ha
  have hiu := (memH1a_memW11 hV hne ha hu).1
  have hiv := (memH1a_memW11 hV hne ha hv).1
  have ht := htf.add htg
  have hL := tendsto_l1_add hLf hLg
  let F := memH1aEnergyField hV.isOpen ha hu
  let K := memH1aEnergyField hV.isOpen ha hv
  have hts : Tendsto (fun n => smoothGraphMap hV.isOpen ha (f n + g n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (u + v), ((F + K : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_add, ← WithLp.toLp_add, Prod.mk_add_mk, F, K,
      volumeAverage_add hiu hiv, UniformSpace.Completion.coe_add] using ht
  have hout := memH1a_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => f n + g n) (G := F + K) (hiu.add hiv) hL hts
  simpa only [show (F + K).field = F.field + K.field from rfl,
    F, K, memH1aEnergyField_field] using hout

/-- Full weighted pairs are closed under negation. -/
theorem MemH1a.neg [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) : MemH1a a V (-u) (-G) := by
  obtain ⟨f, htf, hLf⟩ := hu.smoothGraph_tendsto hV hne ha
  have hiu := (memH1a_memW11 hV hne ha hu).1
  let F := memH1aEnergyField hV.isOpen ha hu
  have hts : Tendsto (fun n => smoothGraphMap hV.isOpen ha (-f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (-u), ((-F : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_neg, ← WithLp.toLp_neg, Prod.neg_mk, F,
      volumeAverage_neg, UniformSpace.Completion.coe_neg] using htf.neg
  have hout := memH1a_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => -f n) (G := -F) hiu.neg (tendsto_l1_neg hLf) hts
  simpa only [show (-F).field = -F.field by rfl, F, memH1aEnergyField_field] using hout

/-- Full weighted pairs are closed under subtraction. -/
theorem MemH1a.sub [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a a V u G) (hv : MemH1a a V v H) : MemH1a a V (u - v) (G - H) := by
  simpa only [sub_eq_add_neg] using hu.add hV hne ha (hv.neg hV hne ha)

/-- Prescribed graph/value limits with supported smooth approximants give zero-boundary pairs. -/
theorem memH1a0_of_graph_tendsto_and_l1 (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : ℕ → supportedCoreSubmodule V} {u : Vec d → ℝ} {G : GradientCore ha}
    (hi : IntegrableOn u V)
    (hL : Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (ht : Tendsto (fun n => supportedGraphMap hV ha (f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V u, (G : GradientHilbert ha))))) :
    MemH1a0 a V u G.field := by
  let s : ℕ → smoothCoreSubmodule hV ha := fun n => supportedToSmooth hV ha (f n)
  have hu := memH1a_of_graph_tendsto_and_l1 hV ha (f := s) hi hL ht
  have htc : Tendsto (fun n => (smoothEnergyField hV ha (s n).property : GradientHilbert ha))
      atTop (𝓝 (G : GradientHilbert ha)) :=
    (WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
  have hE := GradientCore.tendsto_energy_of_coe ha htc
  refine ⟨hu.1, hu.2.1, fun n => (f n).val, fun n => (f n).property, ?_, ?_, ?_⟩
  · exact smoothGraph_cauchy hV ha (f := s) ht.cauchySeq
  · intro K _ hKV
    exact local_l1_of_global (fun n => (s n).property.2.1) hi hL hKV
  · change Tendsto (fun n => weightedEnergy a V (smoothGrad (s n).val - G.field)) atTop (𝓝 0)
    simpa only [smoothEnergyField_field] using hE

/-- Zero-boundary pairs are closed under addition. -/
theorem MemH1a0.add [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (hv : MemH1a0 a V v H) : MemH1a0 a V (u + v) (G + H) := by
  obtain ⟨f, htf, hLf⟩ := hu.supportedGraph_tendsto hV hne ha
  obtain ⟨g, htg, hLg⟩ := hv.supportedGraph_tendsto hV hne ha
  have hiu := (memH1a_memW11 hV hne ha (hu.memH1a ha)).1
  have hiv := (memH1a_memW11 hV hne ha (hv.memH1a ha)).1
  have hL' := tendsto_l1_add hLf hLg
  let F := memH1aEnergyField hV.isOpen ha (hu.memH1a ha)
  let K := memH1aEnergyField hV.isOpen ha (hv.memH1a ha)
  have hts : Tendsto (fun n => supportedGraphMap hV.isOpen ha (f n + g n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (u + v), ((F + K : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_add, ← WithLp.toLp_add, Prod.mk_add_mk, F, K,
      volumeAverage_add hiu hiv, UniformSpace.Completion.coe_add] using htf.add htg
  have hout := memH1a0_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => f n + g n) (G := F + K) (hiu.add hiv) hL' hts
  simpa only [show (F + K).field = F.field + K.field from rfl,
    F, K, memH1aEnergyField_field] using hout

/-- Zero-boundary pairs are closed under negation. -/
theorem MemH1a0.neg [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) : MemH1a0 a V (-u) (-G) := by
  obtain ⟨f, htf, hLf⟩ := hu.supportedGraph_tendsto hV hne ha
  have hiu := (memH1a_memW11 hV hne ha (hu.memH1a ha)).1
  let F := memH1aEnergyField hV.isOpen ha (hu.memH1a ha)
  have hts : Tendsto (fun n => supportedGraphMap hV.isOpen ha (-f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (-u), ((-F : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_neg, ← WithLp.toLp_neg, Prod.neg_mk, F,
      volumeAverage_neg, UniformSpace.Completion.coe_neg] using htf.neg
  have hout := memH1a0_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => -f n) (G := -F) hiu.neg (tendsto_l1_neg hLf) hts
  simpa only [show (-F).field = -F.field by rfl, F, memH1aEnergyField_field] using hout

/-- Zero-boundary pairs are closed under subtraction. -/
theorem MemH1a0.sub [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (hv : MemH1a0 a V v H) : MemH1a0 a V (u - v) (G - H) := by
  simpa only [sub_eq_add_neg] using hu.add hV hne ha (hv.neg hV hne ha)

end CoarseDeGiorgi.Weighted
