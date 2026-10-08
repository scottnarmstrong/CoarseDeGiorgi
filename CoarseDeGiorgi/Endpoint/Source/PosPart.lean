module

public import CoarseDeGiorgi.Weighted.TestingApproximation
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Weighted.Truncation.Continuity
public import CoarseDeGiorgi.Weighted.UpperResponseAffine

/-! Positive parts `(w - s)_+` of zero-boundary pairs minus nonnegative pairs stay in `H¹_{a,0}`. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

theorem memH1a0_posPart_sub [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w s : Vec d → ℝ} {W S : Vec d → Vec d}
    (hw : MemH1a0 a V w W) (hs : MemH1a a V s S) (hs0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ s x) :
    MemH1a0 a V (fun x => max (w x - s x) 0) ({x | 0 < w x - s x}.indicator (W - S)) := by
  have hwH := Weighted.MemH1a0.memH1a ha hw
  have hdiff : CoarseDeGiorgi.MemH1a a V (w - s) (W - S) := hwH.sub hV hne ha hs
  have hpos := MemH1a.posPart hV hne ha hdiff
  obtain ⟨f, hf, -, hL0, hE0⟩ := Weighted.MemH1a0.comp_approximation hV hne ha hw
    (Φ := id) contDiff_id rfl (L := 1) (by intro t; simp)
  have hL : Tendsto (fun n => eLpNorm (f n - w) 1 (volume.restrict V)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hL0
  have hE : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - W)) atTop (𝓝 0) := by
    simpa using hE0
  have hfH : ∀ n, CoarseDeGiorgi.MemH1a a V (f n) (smoothGrad (f n)) := fun n =>
    memH1a_of_isSmoothCore hV.isOpen ha (isSmoothCore_of_supported ha (hf n).1 (hf n).2.1)
  have hfs : ∀ n, CoarseDeGiorgi.MemH1a a V (fun x => f n x - s x) (smoothGrad (f n) - S) :=
    fun n => Weighted.MemH1a.sub hV hne ha (hfH n) hs
  have hpn := fun n => MemH1a.posPart hV hne ha (hfs n)
  have h0 : ∀ n, MemH1a0 a V (fun x => max (f n x - s x) 0)
      ({x | 0 < f n x - s x}.indicator (smoothGrad (f n) - S)) := by
    intro n
    refine MemH1a.memH1a0_of_compact_support hV hne ha (hpn n) (hf n).2.1 (hf n).2.2 ?_
    filter_upwards [hs0] with x hx hxK
    rw [image_eq_zero_of_notMem_tsupport hxK]
    simpa using hx
  have hwi := (memH1a_memW11 hV hne ha hwH).1
  have hsi := (memH1a_memW11 hV hne ha hs).1
  have hint : IntegrableOn (fun x => max (w x - s x) 0) V := (hwi.sub hsi).pos_part
  have ht : Tendsto (fun n => eLpNorm ((fun x => max (f n x - s x) 0) -
      fun x => max (w x - s x) 0) 1 (volume.restrict V)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun _ => bot_le) (fun n => eLpNorm_mono_ae ((hpn n).1.sub hpos.1) (ae_of_all _ fun x => ?_))
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    congr 1
    ring
  have hE' := tendsto_energy_positivePart hV hne ha (f := fun n x => f n x - s x)
    (F := fun n => smoothGrad (f n) - S) hfs hdiff
    (hL.congr fun n => by congr 1; funext x; simp) (by simpa only [sub_sub_sub_cancel_right] using hE) 0
  exact memH1a0_of_tendsto hV hne ha h0 hint hpos.2.1 ht hE'

end CoarseDeGiorgi.Endpoint
