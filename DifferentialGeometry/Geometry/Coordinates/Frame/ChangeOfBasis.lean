import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section ChangeOfBasis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem localFrame_eq_sum_repr
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (j : κ) :
    e.localFrame c j = ∑ a, b.repr (c j) a • e.localFrame b a := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  by_cases hx : x ∈ e.baseSet
  · simp only [e.localFrame_apply_of_mem_baseSet _ hx,
      Trivialization.basisAt, Module.Basis.map_apply]
    simpa only [map_sum, map_smul] using
      congrArg (e.linearEquivAt ℝ x hx).symm (b.sum_repr (c j)).symm
  · simp only [e.localFrame_apply_of_notMem _ hx, smul_zero, Finset.sum_const_zero]

omit [Fintype ι] [Fintype κ] in
theorem localFrame_coeff_localFrame
    (e : Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) (k : κ) :
    e.localFrameCoeff I c k x (e.localFrame b i x) = c.repr (b i) k := by
  rw [e.localFrameCoeff_apply_of_mem_baseSet c hx,
    e.localFrame_apply_of_mem_baseSet b hx]
  simp only [Trivialization.basisAt, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

end ChangeOfBasis

variable [Module.Finite ℝ E]

theorem chartBasisVecFiber_eq_localFrame (α : M) :
    chartBasisVecFiber (I := I) α =
      (trivializationAt E (TangentSpace I) α).localFrame (chartModelBasis E) := by
  funext i x
  by_cases hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet
  · rw [Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
    rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
    rfl
  · rw [Trivialization.localFrame_apply_of_notMem _ _ hx]
    exact Trivialization.symmL_apply_of_notMem _ hx _

theorem chartBasisVecFiber_isLocalFrame (α : M) :
    IsLocalFrameOn I E 1 (chartBasisVecFiber (I := I) α)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [chartBasisVecFiber_eq_localFrame]
  exact (trivializationAt E (TangentSpace I) α).isLocalFrameOn_localFrame_baseSet
    I 1 (chartModelBasis E)

end DifferentialGeometry.Tensor.Coordinates
