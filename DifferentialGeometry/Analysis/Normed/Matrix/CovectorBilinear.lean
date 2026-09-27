import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace Matrix

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinearNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private def covectorBilinEntry (b : ι → E) (i j : ι) :
    Matrix ι ι 𝕜 →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.proj j : (ι → 𝕜) →L[𝕜] 𝕜).comp
    (ContinuousLinearMap.proj i : Matrix ι ι 𝕜 →L[𝕜] (ι → 𝕜))).smulRight
      ((ContinuousLinearMap.apply 𝕜 𝕜 (b j)).smulRight
        (ContinuousLinearMap.apply 𝕜 𝕜 (b i)))

def covectorBilin (b : ι → E) :
    Matrix ι ι 𝕜 →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, ∑ j, covectorBilinEntry b i j

@[simp] theorem covectorBilin_apply (b : ι → E) (A : Matrix ι ι 𝕜)
    (u v : E →L[𝕜] 𝕜) :
    covectorBilin b A u v = ∑ i, ∑ j, A i j * u (b j) * v (b i) := by
  unfold covectorBilin
  rw [_root_.sum_apply, _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.sum_apply, _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change A i j * (u (b j) * v (b i)) = _
  exact (mul_assoc _ _ _).symm

end Matrix
