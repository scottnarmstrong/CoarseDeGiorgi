module

public import CoarseDeGiorgi.Endpoint.Reconstruction.DirichletDualBound
public import CoarseDeGiorgi.Endpoint.Reconstruction.MorreyLocalToGlobal
public import CoarseDeGiorgi.Endpoint.Reconstruction.BlockScales

/-! # Simultaneous Lr and L-infinity estimates for Dirichlet increments -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem eLpNorm_le_of_cubeLpNorm_le {d : ℕ} {Q : TriadicCube d}
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : Vec d → E} {g : Vec d → F} {p : ℝ≥0∞} {C : ℝ}
    (hC : 0 ≤ C) (hf : MemLp f p (normalizedCubeMeasure Q))
    (hg : MemLp g p (normalizedCubeMeasure Q))
    (h : cubeLpNorm Q p f ≤ C * cubeLpNorm Q p g) :
    eLpNorm f p (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal C * eLpNorm g p (normalizedCubeMeasure Q) := by
  have hh := ENNReal.ofReal_le_ofReal h
  dsimp [cubeLpNorm] at hh
  rwa [ENNReal.ofReal_toReal hf.eLpNorm_ne_top, ENNReal.ofReal_mul hC,
    ENNReal.ofReal_toReal hg.eLpNorm_ne_top] at hh

/-- Both constants depend only on dimension and the real exponent. The
increment numbered `k` here contributes to target block `k+1`. -/
theorem exists_fineIncrement_dirichlet_estimates {d : ℕ} (hd : 3 ≤ d)
    {r s : ℝ} (hrs : r.HolderConjugate s) (hr2 : r < 2) :
    ∃ CL Csup : ℝ, 0 ≤ CL ∧ 0 ≤ Csup ∧
      ∀ (k : ℕ) (G : Vec d → Vec d),
        IntegrableOn G (CoarseDeGiorgi.originCube 1) →
        ∃ w : H10Function (openCubeSet (Homogenization.originCube d 0)),
          IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d))
            (openCubeSet (Homogenization.originCube d 0)) w (fineIncrement k G) ∧
          eLpNorm w.toH1Function.toFun (ENNReal.ofReal r)
              (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
            ENNReal.ofReal CL * ENNReal.ofReal ((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) *
              eLpNorm (fineIncrement k G) (ENNReal.ofReal r)
                (normalizedCubeMeasure (Homogenization.originCube d 0)) ∧
          eLpNorm w.toH1Function.toFun ⊤
              (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
            ENNReal.ofReal Csup *
              ENNReal.ofReal ((3 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * ((d : ℝ) / r - 1))) *
              eLpNorm (fineIncrement k G) (ENNReal.ofReal r)
                (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  have hd1 : 1 ≤ d := by omega
  let : NeZero d := ⟨by omega⟩
  obtain ⟨CL, hCL, hL⟩ := exists_unitCube_dirichlet_cancellation_bound (d := d) hrs hr2
  obtain ⟨M, hM, hMorrey⟩ := exists_unitCube_cell_morrey_bound (d := d)
  have hp1 : 1 < ENNReal.ofReal (2 * (d : ℝ)) := ENNReal.one_lt_ofReal.mpr (by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  obtain ⟨CG, hCG, hGrad⟩ := exists_unitCube_dirichlet_gradient_bound (d := d)
    (by omega) (ENNReal.ofReal (2 * d)) hp1 ENNReal.ofReal_lt_top
  refine ⟨3 * CL, 3 * CL + M * CG, by positivity, by positivity, ?_⟩
  intro k G hG
  let Q := Homogenization.originCube d 0
  let μ := normalizedCubeMeasure Q
  let F := fineIncrement k G
  have hFp (p : ℝ≥0∞) : MemLp F p μ := by
    dsimp [μ, Q]
    rw [normalizedCubeMeasure_unit_eq]
    exact (memLp_fineIncrement k G p).mono_measure Measure.restrict_le_self
  have hF2 : MemVectorL2 (openCubeSet Q) F := by
    simpa only [μ, Q, normalizedCubeMeasure_unit_eq] using hFp 2
  obtain ⟨w, hw⟩ := exists_unitCube_dirichlet_block F hF2
  have hmean : ∀ R ∈ descendantsAtDepth Q k, ∀ i, ∫ x in openCubeSet R, F x i = 0 :=
    fun _ hR i => integral_fineIncrement_coordinate_eq_zero k G hG hR i
  have hLw := hL k F (hFp _) hmean w hw
  obtain ⟨hgrad, hgradReal⟩ := hGrad F (hFp _) w hw
  have hgradEN := eLpNorm_le_of_cubeLpNorm_le hCG.le hgrad (hFp _) hgradReal
  have hSup := hMorrey (k + 1) w.toH1Function r hrs.lt.le hgrad
  have hinverse := fineIncrement_inverse_bound (d := d) k G hrs.pos (by positivity)
    (by
      have hdReal : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith : r ≤ 2 * d)
  have hLchild : ENNReal.ofReal (CL * (3 : ℝ) ^ (-(k : ℤ))) =
      ENNReal.ofReal (3 * CL) * ENNReal.ofReal ((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) := by
    rw [parent_scale_eq_three_mul_child, show CL * (3 * (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) =
      (3 * CL) * (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) by ring, ENNReal.ofReal_mul (by positivity)]
  refine ⟨w, hw, hLw.trans_eq (by rw [hLchild]), ?_⟩
  calc
    _ ≤ (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (-(1 / r)) *
        (ENNReal.ofReal (CL * (3 : ℝ) ^ (-(k : ℤ))) * eLpNorm F (ENNReal.ofReal r) μ) +
        ENNReal.ofReal M * ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal CG *
            ((ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (1 / (2 * d) - 1 / r) *
              eLpNorm F (ENNReal.ofReal r) μ)) := by
      apply hSup.trans
      gcongr
      apply hgradEN.trans
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul hCL]
      have hmeanScale := mean_parent_cell_scale (d := d) k r
      have hmorreyScale := morrey_cell_scale hd1 (k + 1) r
      calc
        _ = (ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal CL +
            ENNReal.ofReal M * ENNReal.ofReal CG) *
            ENNReal.ofReal ((3 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * ((d : ℝ) / r - 1))) *
            eLpNorm F (ENNReal.ofReal r) μ := by
          calc
            _ = ENNReal.ofReal CL *
                ((ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (-(1 / r)) *
                  ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ)))) * eLpNorm F (ENNReal.ofReal r) μ +
                (ENNReal.ofReal M * ENNReal.ofReal CG) *
                  (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ (1 / 2 : ℝ)) *
                    (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (1 / (2 * d) - 1 / r)) *
                  eLpNorm F (ENNReal.ofReal r) μ := by ring
            _ = _ := by rw [hmeanScale, hmorreyScale]; ring
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
