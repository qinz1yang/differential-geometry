import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import DifferentialGeometry.Tensor.RSTensor.PositiveSemidefinite
import Mathlib.Tactic.FinCases

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [IsManifold I 1 M]

noncomputable def twoTensorLeftKernel
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Submodule Real (TangentSpace I x) :=
  LinearMap.ker ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
theorem mem_twoTensorLeftKernel_iff
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) :
    v ∈ twoTensorLeftKernel (I := I) (M := M) A ↔
      ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0 := by
  change (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A) v = 0 ↔ _
  have h_eval (w : TangentSpace I x) :
      ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A) v)
          (fun _ : Fin 1 => w) = eval02 (I := I) (M := M) A v w := by
    change
      (((continuousMultilinearCurryLeftEquiv Real
          (fun _ : Fin (1 + 1) => TangentSpace I x) Real)
          ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
          v)
          (fun _ : Fin 1 => w)) =
        ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
          (fun i : Fin 2 => if i = 0 then v else w)
    rw [continuousMultilinearCurryLeftEquiv_apply]
    congr 1
    funext i
    fin_cases i <;> simp [Fin.cons_zero]
  constructor
  · intro hv w
    have h := congrArg
      (fun B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 x ↦ B (fun _ : Fin 1 ↦ w)) hv
    change
      ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x A) v)
          (fun _ : Fin 1 ↦ w) = 0 at h
    rw [h_eval] at h
    simpa [eval02] using h
  · intro hv
    apply tensor0SSpace_ext 1 x
    intro m
    have hm : m = fun _ : Fin 1 ↦ m 0 := by
      funext i
      fin_cases i
      rfl
    rw [hm, h_eval]
    simpa [eval02] using hv (m 0)

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
theorem quad02_eq_zero_iff_mem_twoTensorLeftKernel
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u) :
    quad02 (I := I) (M := M) A v = 0 ↔
      v ∈ twoTensorLeftKernel (I := I) (M := M) A := by
  constructor
  · intro hv
    rw [mem_twoTensorLeftKernel_iff]
    exact psd_null_left (I := I) (M := M) A hsym hpsd hv
  · intro hv
    have h := (mem_twoTensorLeftKernel_iff (I := I) (M := M) A v).mp hv v
    simpa [eval02_self] using h

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
theorem twoTensorLeftKernel_eq_bot_iff_positive_definite
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u) :
    twoTensorLeftKernel (I := I) (M := M) A = ⊥ ↔
      ∀ v : TangentSpace I x, v ≠ 0 → 0 < quad02 (I := I) (M := M) A v := by
  constructor
  · intro hker v hv
    have hnonnegative := hpsd v
    have hnonzero : quad02 (I := I) (M := M) A v ≠ 0 := by
      intro hzero
      have hmem :=
        (quad02_eq_zero_iff_mem_twoTensorLeftKernel
          (I := I) (M := M) A hsym hpsd).mp hzero
      rw [hker] at hmem
      have : v = 0 := by simpa using hmem
      exact hv this
    exact lt_of_le_of_ne hnonnegative (Ne.symm hnonzero)
  · intro hpositive
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_bot]
      by_contra hne
      have hpos := hpositive v hne
      have hzero :=
        (quad02_eq_zero_iff_mem_twoTensorLeftKernel
          (I := I) (M := M) A hsym hpsd).mpr hv
      exact ne_of_gt hpos hzero
    · exact bot_le

end DifferentialGeometry

end

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Tensor0SBundle

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable local instance contractionKernelTopology :
    TopologicalSpace (TotalSpace (E →L[Real] Tensor0SModel 1 Real E)
      (fun x : M => TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id Real)
    E (TangentSpace I) (Tensor0SModel 1 Real E)
      (fun x : M => Tensor0SSpace (I := I) (M := M) 1 x)

noncomputable local instance contractionKernelFiber :
    FiberBundle (E →L[Real] Tensor0SModel 1 Real E)
      (fun x : M => TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id Real)
    E (TangentSpace I) (Tensor0SModel 1 Real E)
      (fun x : M => Tensor0SSpace (I := I) (M := M) 1 x)

theorem exists_smooth_twoTensorLeftKernel {k : ℕ}
    (A : ∀ x : M, Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x)
    (hA : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Tensor0SModel 1 Real E)) ∞
      (fun x => TotalSpace.mk' (E →L[Real] Tensor0SModel 1 Real E) x
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x))))
    (hker : ∀ x : M, Module.finrank Real
      (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x)).toLinearMap.ker = k) :
    ∃ S : ContMDiffVectorSubbundle (I := I) (F := E) (V := TangentSpace I)
      (n := (∞ : WithTop ℕ∞)),
      S.rank = k ∧ ∀ x, S.fiber x = twoTensorLeftKernel (I := I) (M := M) (A x) := by
  let B : ∀ x : M, TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x :=
    fun x => tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x)
  have hB : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Tensor0SModel 1 Real E)) ∞
      (fun x => TotalSpace.mk' (E →L[Real] Tensor0SModel 1 Real E) x (B x)) := by
    simpa [B] using hA
  have hker' : ∀ x : M, Module.finrank Real (B x).ker = k := by
    intro x
    simpa [B, twoTensorLeftKernel] using hker x
  obtain ⟨S, hSrank, hSf⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel
    (I := I) (M := M) B hB k hker'
  refine ⟨S, hSrank, ?_⟩
  intro x
  simpa [B, twoTensorLeftKernel] using hSf x

end Tensor0SBundle
end DifferentialGeometry

end
