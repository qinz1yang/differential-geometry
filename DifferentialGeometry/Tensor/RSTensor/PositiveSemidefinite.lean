import DifferentialGeometry.Tensor.RSTensor.Evaluation
import Mathlib.Tactic.FinCases
import DifferentialGeometry.Tensor.Multilinear.Curry.FiniteNorm
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_left
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0 := by
  let C := (Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)).symm
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x A)
  let B : LinearMap.BilinForm ℝ (TangentSpace I x) := C.toBilinForm
  have hB (u w : TangentSpace I x) : B u w = eval02 (I := I) A u w := by
    change (Tensor.Multilinear.biForm₂ToModel (TangentSpace I x)).symm
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x A) u w = _
    rw [Tensor.Multilinear.biForm₂ToModel_symm_apply]
    change A ![u, w] = A (fun i : Fin 2 => if i = 0 then u else w)
    congr 1
    funext i
    fin_cases i <;> rfl
  have hnonneg : ∀ u, 0 ≤ B u u := by
    intro u
    simpa only [hB, eval02_self] using hpsd u
  have hsymm : B.IsSymm := by
    refine ⟨?_⟩
    intro u w
    rw [hB, hB]
    exact hsym u w
  have hv : v ∈ LinearMap.ker B :=
    (B.apply_apply_same_eq_zero_iff hnonneg hsymm).mp (by
      simpa only [hB, eval02_self] using hnull)
  have hzero : B v = 0 := LinearMap.mem_ker.mp hv
  intro w
  rw [← hB v w]
  simpa only [LinearMap.zero_apply] using
    congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L w) hzero

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_right
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A w v = 0 := by
  intro w
  rw [← hsym v w]
  exact psd_null_left (I := I) (M := M) A hsym hpsd hnull w

end DifferentialGeometry
