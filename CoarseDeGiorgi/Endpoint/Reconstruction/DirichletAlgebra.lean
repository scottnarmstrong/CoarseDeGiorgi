module

public import CoarseDeGiorgi.Endpoint.Reconstruction.WeightedBlocks

/-! # Finite sums and differences of Dirichlet blocks -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

abbrev UnitH10 (d : ℕ) := H10Function (openCubeSet (Homogenization.originCube d 0))

abbrev UnitDirichletEquation {d : ℕ} (w : UnitH10 d) (F : Vec d → Vec d) :=
  IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d))
    (openCubeSet (Homogenization.originCube d 0)) w F

theorem matVecMul_one {d : ℕ} (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem h10_add_grad {d : ℕ} {U : Set (Vec d)} (u v : H10Function U) :
    (u + v).toH1Function.grad = fun x => u.toH1Function.grad x + v.toH1Function.grad x :=
  H1Function.add_grad _ _

theorem h10_sub_grad {d : ℕ} {U : Set (Vec d)} (u v : H10Function U) :
    (u - v).toH1Function.grad = fun x => u.toH1Function.grad x - v.toH1Function.grad x :=
  H1Function.sub_grad _ _

theorem h10_add_toFun {d : ℕ} {U : Set (Vec d)} (u v : H10Function U) :
    (u + v).toH1Function.toFun = fun x => u.toH1Function.toFun x + v.toH1Function.toFun x :=
  H1Function.add_toFun _ _

theorem h10_sub_toFun {d : ℕ} {U : Set (Vec d)} (u v : H10Function U) :
    (u - v).toH1Function.toFun = fun x => u.toH1Function.toFun x - v.toH1Function.toFun x :=
  H1Function.sub_toFun _ _

theorem UnitDirichletEquation.add {d : ℕ} {u v : UnitH10 d} {F G : Vec d → Vec d}
    (hu : UnitDirichletEquation u F) (hv : UnitDirichletEquation v G)
    (hF : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) F)
    (hG : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) G) :
    UnitDirichletEquation (u + v) (fun x => F x + G x) := by
  intro ψ
  have huψ := hu ψ
  have hvψ := hv ψ
  simp only [matVecMul_one] at huψ hvψ ⊢
  rw [h10_add_grad]
  simp only [vecDot_add_left]
  rw [integral_add (integrableOn_vecDot_of_memVectorL2 u.toH1Function.grad_memVectorL2
      ψ.toH1Function.grad_memVectorL2)
    (integrableOn_vecDot_of_memVectorL2 v.toH1Function.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2),
    integral_add (integrableOn_vecDot_of_memVectorL2 hF ψ.toH1Function.grad_memVectorL2)
      (integrableOn_vecDot_of_memVectorL2 hG ψ.toH1Function.grad_memVectorL2), huψ, hvψ]

theorem UnitDirichletEquation.sub {d : ℕ} {u v : UnitH10 d} {F G : Vec d → Vec d}
    (hu : UnitDirichletEquation u F) (hv : UnitDirichletEquation v G)
    (hF : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) F)
    (hG : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) G) :
    UnitDirichletEquation (u - v) (fun x => F x - G x) := by
  intro ψ
  have huψ := hu ψ
  have hvψ := hv ψ
  simp only [matVecMul_one] at huψ hvψ ⊢
  rw [h10_sub_grad]
  have hsub (a b c : Vec d) : vecDot (a - b) c = vecDot a c - vecDot b c := by
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [hsub]
  rw [integral_sub (integrableOn_vecDot_of_memVectorL2 u.toH1Function.grad_memVectorL2
      ψ.toH1Function.grad_memVectorL2)
    (integrableOn_vecDot_of_memVectorL2 v.toH1Function.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2),
    integral_sub (integrableOn_vecDot_of_memVectorL2 hF ψ.toH1Function.grad_memVectorL2)
      (integrableOn_vecDot_of_memVectorL2 hG ψ.toH1Function.grad_memVectorL2), huψ, hvψ]

theorem UnitDirichletEquation.congr_forcing {d : ℕ} {u : UnitH10 d}
    {F G : Vec d → Vec d} (hu : UnitDirichletEquation u F)
    (hFG : F =ᵐ[volume.restrict (openCubeSet (Homogenization.originCube d 0))] G) :
    UnitDirichletEquation u G := by
  intro ψ
  refine (hu ψ).trans ?_
  apply integral_congr_ae
  exact hFG.mono fun _ hx => by dsimp only; rw [hx]

def blockPartialSum {d : ℕ} (w : ℕ → UnitH10 d) : ℕ → UnitH10 d
  | 0 => 0
  | n + 1 => blockPartialSum w n + w (n + 1)

theorem blockPartialSum_toFun {d : ℕ} (w : ℕ → UnitH10 d) (N : ℕ) :
    (blockPartialSum w N).toH1Function.toFun =
      fun x => ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x := by
  induction N with
  | zero =>
    simp only [blockPartialSum, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1),
      Finset.sum_empty]
    rfl
  | succ n ih =>
    rw [blockPartialSum, h10_add_toFun, ih]
    funext x
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
