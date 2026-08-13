import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry

open Bundle Tensor0SBundle
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
  LinearMap.ker ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
theorem mem_twoTensorLeftKernel_iff
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) :
    v ∈ twoTensorLeftKernel (I := I) (M := M) A ↔
      ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0 := by
  change (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) v = 0 ↔ _
  constructor
  · intro hv w
    have h := congrArg
      (fun B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 x ↦ B (fun _ : Fin 1 ↦ w)) hv
    change
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) v)
          (fun _ : Fin 1 ↦ w) = 0 at h
    rw [Tensor0SBundle.tensor0S_curry_one_apply] at h
    simpa [eval02] using h
  · intro hv
    apply tensor0SSpace_ext 1 x
    intro m
    have hm : m = fun _ : Fin 1 ↦ m 0 := by
      funext i
      fin_cases i
      rfl
    rw [hm, Tensor0SBundle.tensor0S_curry_one_apply]
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
