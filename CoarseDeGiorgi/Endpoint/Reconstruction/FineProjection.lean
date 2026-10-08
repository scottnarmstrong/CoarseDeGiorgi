import CoarseDeGiorgi.Endpoint.Reconstruction.FineAverages
import CoarseDeGiorgi.Endpoint.Reconstruction.DirichletBlock
import CoarseDeGiorgi.Foundations.Reconstruction.AuxIncrementLp

/-! # Nesting and cancellation for the fine projection -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

def fineOffsetEmbedding (k : ℕ) : (Fin d → Fin (3 ^ k)) ↪ (Fin d → ℤ) where
  toFun := gridOffset k
  inj' := Moments.gridOffset_injective k

theorem fine_offsets_eq_auxDescendantIndices (k : ℕ) :
    Finset.univ.map (fineOffsetEmbedding (d := d) k) =
      auxDescendantIndices 1 (1 + (k : ℤ)) := by
  classical
  ext n
  change n ∈ Finset.univ.map (fineOffsetEmbedding k) ↔
    n ∈ Foundations.Reconstruction.auxDescendantIndices 1 (1 + (k : ℤ))
  rw [Finset.mem_map, Foundations.Reconstruction.mem_auxDescendantIndices_iff
    1 (1 + (k : ℤ)) (by omega)]
  simp only [add_sub_cancel_left, Int.toNat_natCast]
  constructor
  · rintro ⟨j, _, rfl⟩
    have hj := (fineSimplexEmbedding k j (Equiv.refl _)).property
    exact (LowerFractional.lower_mem_triangulation_iff k (gridOffset k j)
      (Equiv.refl _)).mp hj
  · intro hn
    have hmem := (LowerFractional.lower_mem_triangulation_iff k n (Equiv.refl _)).mpr hn
    obtain ⟨⟨j, π⟩, _, heq⟩ := Finset.mem_image.mp hmem
    exact ⟨j, Finset.mem_univ _, congrArg Prod.fst heq⟩

theorem fineCube_eq_auxDescendantCube (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    fineCube k j = auxDescendantCube 1 (1 + (k : ℤ)) (fun _ => 0) (gridOffset k j) := by
  ext x
  simp only [fineCube, Foundations.Simplex.simplexCube, auxDescendantCube,
    Set.mem_ofPred_eq, Int.cast_zero, zero_mul, zero_add,
    show 1 - (1 + (k : ℤ)) = -(k : ℤ) by omega, abs_lt, mul_comm, neg_div]

/-- This is the established auxiliary projection at depth `k`, with no shift
of the coefficient moment's index. -/
theorem fineAverage_eq_auxAverage (k : ℕ) (G : Vec d → Vec d) :
    fineAverage k G = auxAverage 1 (1 + (k : ℤ)) (fun _ => 0) G := by
  classical
  funext x
  simp only [fineAverage, Finset.sum_apply, auxAverage,
    ← fine_offsets_eq_auxDescendantIndices, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  simp only [fineOffsetEmbedding, Function.Embedding.coeFn_mk,
    Set.indicator_apply, fineCube_eq_auxDescendantCube,
    LowerFractional.lower_descendant_average_eq]

theorem fineAverage_eq_cubeProjectionVec_ae (k : ℕ) (G : Vec d → Vec d) :
    fineAverage k G =ᵐ[volume]
      Foundations.Reconstruction.cubeProjectionVec (Homogenization.originCube d 0) k G := by
  rw [fineAverage_eq_auxAverage]
  have hb : Foundations.Reconstruction.auxAverage 1 (1 + (k : ℤ)) (fun _ => 0) G =
      CoarseDeGiorgi.auxAverage 1 (1 + (k : ℤ)) (fun _ => 0) G := rfl
  rw [← hb]
  have hz : Foundations.Reconstruction.auxCenter 1 (fun _ : Fin d => 0) = 0 := by
    funext i
    simp [Foundations.Reconstruction.auxCenter]
  simpa only [hz, add_zero, sub_self] using
    (Foundations.Reconstruction.auxAverage_add_eq_cubeProjectionVec_ae
      1 k (fun _ => 0) G)

theorem fine_average_norm_mono (k : ℕ) (G : Vec d → Vec d)
    (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (fun x => euclidNorm (fineAverage k G x)) p
        (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      eLpNorm (fun x => euclidNorm (fineAverage (k + 1) G x)) p
        (volume.restrict (CoarseDeGiorgi.originCube 1)) := by
  have hU : CoarseDeGiorgi.originCube (d := d) 1 = auxCube 1 (fun _ => 0) :=
    LowerFractional.lower_unitCube_eq_auxCube
  rw [fineAverage_eq_auxAverage, fineAverage_eq_auxAverage, hU]
  have hGa : IntegrableOn G (Foundations.Reconstruction.auxCube 1 (fun _ => 0)) := by
    rw [Foundations.Reconstruction.auxCube_eq_statement, ← hU]
    exact hG
  exact Foundations.Reconstruction.eLpNorm_euclidNorm_auxAverage_mono
    1 k (fun _ => 0) G hGa p hp hpTop

def fineIncrement (k : ℕ) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x => fineAverage (k + 1) G x - fineAverage k G x

theorem memLp_fineIncrement (k : ℕ) (G : Vec d → Vec d) (p : ℝ≥0∞) :
    MemLp (fineIncrement k G) p volume :=
  (memLp_fineAverage (k + 1) G p).sub (memLp_fineAverage k G p)

theorem fine_increment_norm_le (k : ℕ) (G : Vec d → Vec d)
    (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (fun x => euclidNorm (fineIncrement k G x)) p
        (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      2 * eLpNorm (fun x => euclidNorm (fineAverage (k + 1) G x)) p
        (volume.restrict (CoarseDeGiorgi.originCube 1)) := by
  have ht := Foundations.Reconstruction.eLpNorm_euclidNorm_sub_le
    (μ := volume.restrict (CoarseDeGiorgi.originCube 1))
    (fineAverage (k + 1) G) (fineAverage k G)
    (measurable_fineAverage (k + 1) G).aestronglyMeasurable
    (measurable_fineAverage k G).aestronglyMeasurable p hp
  exact ht.trans ((add_le_add le_rfl (fine_average_norm_mono k G hG p hp hpTop)).trans_eq
    (two_mul _).symm)

theorem fine_increment_weighted_norm_le [NeZero d] (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a0 a (CoarseDeGiorgi.originCube 1) v G) {q : ℝ} (hq : 1 < q) :
    eLpNorm (fun x => euclidNorm (fineIncrement k G x)) (ENNReal.ofReal (paramR q))
        (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      2 * ((ENNReal.ofReal (lowerCellAverage a ha (k + 1) q)).rpow (1 / (2 * q)) *
        (weightedEnergy a (CoarseDeGiorgi.originCube 1) G).rpow (1 / 2)) := by
  have hW := Weighted.memH1a_memW11 LowerFractional.lower_unitCube_domain
    LowerFractional.lower_unitCube_nonempty ha (Weighted.MemH1a0.memH1a ha hv)
  have hG : IntegrableOn G (CoarseDeGiorgi.originCube 1) := Integrable.of_eval hW.2.1
  exact (fine_increment_norm_le k G hG (ENNReal.ofReal (paramR q))
    (by rw [ENNReal.one_le_ofReal]; exact (LowerFractional.lower_paramR_gt_one hq).le)
    ENNReal.ofReal_ne_top).trans (mul_le_mul le_rfl
      (fine_average_norm_le_zeroTrace (k + 1) a ha hv hq) bot_le bot_le)

/-- Each increment has zero mean on every parent cell of side `3^(-k)`. -/
theorem integral_fineIncrement_coordinate_eq_zero (k : ℕ) (G : Vec d → Vec d)
    (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1))
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (Homogenization.originCube d 0) k)
    (i : Fin d) :
    ∫ x in openCubeSet R, fineIncrement k G x i = 0 := by
  have heq : (fun x => fineIncrement k G x i) =ᵐ[volume.restrict (openCubeSet R)]
      fun x => Foundations.Reconstruction.cubeProjectionVec (Homogenization.originCube d 0)
        (k + 1) G x i - Foundations.Reconstruction.cubeProjectionVec
        (Homogenization.originCube d 0) k G x i := by
    filter_upwards [(fineAverage_eq_cubeProjectionVec_ae (k + 1) G).restrict,
      (fineAverage_eq_cubeProjectionVec_ae k G).restrict] with x hn hp
    simp only [fineIncrement, hn, hp, Pi.sub_apply]
  rw [integral_congr_ae heq, ← setIntegral_congr_set (cubeSet_ae_eq_openCubeSet R)]
  apply Foundations.Reconstruction.integral_cubeProjectionVec_increment_coordinate_eq_zero
    G hR
  change Integrable G (volume.restrict (cubeSet (Homogenization.originCube d 0)))
  rwa [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _),
    ← originCube_one_eq_openCubeSet] 

end

end CoarseDeGiorgi.Endpoint.Reconstruction
