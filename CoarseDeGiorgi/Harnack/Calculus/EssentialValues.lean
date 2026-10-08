import CoarseDeGiorgi.Statements.NonnegativeEssInf
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace CoarseDeGiorgi.Harnack.Calculus

open Homogenization MeasureTheory Filter
open scoped ENNReal

/-- Translation by a real constant, as an order isomorphism of `EReal`. -/
private noncomputable def eRealAddOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun x := x + c
  invFun x := x - c
  left_inv x := EReal.add_sub_cancel_right
  right_inv x := EReal.sub_add_cancel
  map_rel_iff' := by
    intro a b
    change a + c ≤ b + c ↔ a ≤ b
    exact (EReal.addLECancellable_coe c).add_le_add_iff_right

private theorem essInf_bdd_below {X β : Type*} [MeasurableSpace X] [Preorder β] [OrderBot β]
    {μ : Measure X} (f : X → β) : IsBoundedUnder (· ≥ ·) (ae μ) f := by
  exact ⟨⊥, Filter.Eventually.of_forall (fun y => bot_le)⟩

private theorem essInf_cobdd_below {X β : Type*} [MeasurableSpace X] [Preorder β] [OrderTop β]
    {μ : Measure X} (f : X → β) : IsCoboundedUnder (· ≥ ·) (ae μ) f := by
  exact ⟨⊤, fun _ _ => le_top⟩

private theorem essSup_bdd_above {X β : Type*} [MeasurableSpace X] [Preorder β] [OrderTop β]
    {μ : Measure X} (f : X → β) : IsBoundedUnder (· ≤ ·) (ae μ) f := by
  exact ⟨⊤, Filter.Eventually.of_forall (fun y => le_top)⟩

private theorem essSup_cobdd_above {X β : Type*} [MeasurableSpace X] [Preorder β] [OrderBot β]
    {μ : Measure X} (f : X → β) : IsCoboundedUnder (· ≤ ·) (ae μ) f := by
  exact ⟨⊥, fun _ _ => bot_le⟩

/-- The essential infimum commutes with adding a real constant (in `EReal`). -/
theorem eRealEssInf_add_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ) (c : ℝ) :
    essInf (fun x => ((u x + c : ℝ) : EReal)) μ =
      essInf (fun x => (u x : EReal)) μ + c := by
  have h := OrderIso.essInf_apply (fun x => (u x : EReal)) μ (eRealAddOrderIso c)
    (essInf_bdd_below (μ := μ) _) (essInf_cobdd_below (μ := μ) _)
    (essInf_bdd_below (μ := μ) _) (essInf_cobdd_below (μ := μ) _)
  simpa [eRealAddOrderIso, EReal.coe_add] using h.symm

/-- For an a.e. nonnegative function, the `ENNReal` essential infimum of `ofReal ∘ u` is the
`EReal` essential infimum of `u`, truncated to `ENNReal`. -/
theorem nonnegativeEssInf_eq_toENNReal_erealEssInf {X : Type*}
    [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u x) :
    essInf (fun x => ENNReal.ofReal (u x)) μ =
      (essInf (fun x => (u x : EReal)) μ).toENNReal := by
  let e := essInf (fun x => (u x : EReal)) μ
  let n := essInf (fun x => ENNReal.ofReal (u x)) μ
  have he_nonneg : 0 ≤ e := by
    apply le_essInf_of_ae_le (f := fun x => (u x : EReal)) 0 ?_
      (essInf_cobdd_below (μ := μ) _)
    filter_upwards [hu] with x hx
    exact_mod_cast hx
  have hne : ((n : ENNReal) : EReal) ≤ e := by
    apply le_essInf_of_ae_le (f := fun x => (u x : EReal)) (n : EReal) ?_
      (essInf_cobdd_below (μ := μ) _)
    filter_upwards [ae_essInf_le (f := fun x => ENNReal.ofReal (u x))
        (essInf_bdd_below (μ := μ) _), hu]
      with x hn hx
    have hn' : ((n : ENNReal) : EReal) ≤
        ((ENNReal.ofReal (u x) : ENNReal) : EReal) := by exact_mod_cast hn
    simpa [EReal.coe_ennreal_ofReal, max_eq_left hx] using hn'
  have hen : e.toENNReal ≤ n := by
    apply le_essInf_of_ae_le (f := fun x => ENNReal.ofReal (u x))
      e.toENNReal ?_ (essInf_cobdd_below (μ := μ) _)
    filter_upwards [ae_essInf_le (f := fun x => (u x : EReal))
        (essInf_bdd_below (μ := μ) _), hu]
      with x he hx
    have ht := EReal.toENNReal_le_toENNReal he
    simpa using ht
  have hne' : n ≤ e.toENNReal := by
    have ht := EReal.toENNReal_le_toENNReal hne
    simpa using ht
  change n = e.toENNReal
  exact le_antisymm hne' hen

/-- `nonnegativeEssInf` commutes with adding a nonnegative constant. -/
theorem nonnegativeEssInf_add_const {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) (hu : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (c : ℝ) (hc : 0 ≤ c) :
    CoarseDeGiorgi.nonnegativeEssInf V (fun x => u x + c) =
      CoarseDeGiorgi.nonnegativeEssInf V u + ENNReal.ofReal c := by
  have huc : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x + c :=
    hu.mono fun x hx => add_nonneg hx hc
  rw [show CoarseDeGiorgi.nonnegativeEssInf V (fun x => u x + c) =
      essInf (fun x => ENNReal.ofReal (u x + c)) (volume.restrict V) by rfl,
    nonnegativeEssInf_eq_toENNReal_erealEssInf (volume.restrict V) (fun x => u x + c) huc,
    show CoarseDeGiorgi.nonnegativeEssInf V u =
      essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V) by rfl,
    nonnegativeEssInf_eq_toENNReal_erealEssInf (volume.restrict V) u hu,
    eRealEssInf_add_const]
  have he_nonneg : 0 ≤ essInf (fun x => (u x : EReal)) (volume.restrict V) := by
    apply le_essInf_of_ae_le (f := fun x => (u x : EReal)) 0 ?_
      (essInf_cobdd_below (μ := volume.restrict V) _)
    filter_upwards [hu] with x hx
    exact_mod_cast hx
  rw [EReal.toENNReal_add he_nonneg (show 0 ≤ (c : EReal) by exact_mod_cast hc)]
  simp

/-- The essential supremum of `f⁻¹` is the inverse of the essential infimum of `f`. -/
theorem essSup_inv_eq_inv_essInf {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) :
    essSup (fun x => (f x)⁻¹) μ = (essInf f μ)⁻¹ := by
  change (limsup (fun x => (f x)⁻¹) (ae μ)) =
    (liminf f (ae μ))⁻¹
  exact (ENNReal.inv_liminf).symm

/-- `c` is below the essential supremum of `f` iff `{c < f}` has positive measure. -/
theorem ennreal_lt_essSup_iff_measure_pos {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (c : ℝ≥0∞) :
    c < essSup f μ ↔ 0 < μ {x | c < f x} := by
  constructor
  · intro hc
    by_contra hpos
    have hzero : μ {x | c < f x} = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    have hae : ∀ᵐ x ∂μ, x ∉ {x | c < f x} :=
      (measure_eq_zero_iff_ae_notMem).mp hzero
    have hle : f ≤ᵐ[μ] fun _ => c := hae.mono fun x hx => le_of_not_gt hx
    exact (not_le_of_gt hc) (essSup_le_of_ae_le c hle (essSup_cobdd_above (μ := μ) _))
  · intro hpos
    by_contra hc
    have hle : essSup f μ ≤ c := le_of_not_gt hc
    have hae : f ≤ᵐ[μ] fun _ => c :=
      (ae_le_essSup (f := f) (essSup_bdd_above (μ := μ) _)).mono fun _ hx => hx.trans hle
    have hzero : μ {x | c < f x} = 0 :=
      (measure_eq_zero_iff_ae_notMem).mpr (hae.mono fun _ hx => not_lt_of_ge hx)
    exact (ne_of_gt hpos) hzero

end CoarseDeGiorgi.Harnack.Calculus
