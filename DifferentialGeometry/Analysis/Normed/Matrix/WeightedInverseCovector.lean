import DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import DifferentialGeometry.Topology.UniformConvergence.Composition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace Matrix

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def weightedInvCovectorBilin (b : ι → E) (p : ℝ × Matrix ι ι ℝ) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (p.1 * Real.sqrt p.2.det) • covectorBilin b p.2⁻¹

@[simp] theorem weightedInvCovectorBilin_apply (b : ι → E)
    (p : ℝ × Matrix ι ι ℝ) (u v : E →L[ℝ] ℝ) :
    weightedInvCovectorBilin b p u v =
      (p.1 * Real.sqrt p.2.det) * (∑ i, ∑ j, p.2⁻¹ i j * u (b j) * v (b i)) := by
  simp [weightedInvCovectorBilin]

theorem continuousAt_weightedInvCovectorBilin (b : ι → E)
    {p : ℝ × Matrix ι ι ℝ} (hp : p.2.det ≠ 0) :
    ContinuousAt (weightedInvCovectorBilin b) p := by
  have hinv : ContinuousAt (fun A : Matrix ι ι ℝ => A⁻¹) p.2 := by
    apply continuousAt_matrix_inv _
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ hp
  have hbilin : ContinuousAt
      (fun q : ℝ × Matrix ι ι ℝ => covectorBilin b q.2⁻¹) p :=
    (covectorBilin b).continuous.continuousAt.comp
      (hinv.comp continuous_snd.continuousAt)
  exact (continuous_fst.continuousAt.mul
    (Real.continuous_sqrt.comp continuous_snd.matrix_det).continuousAt).smul hbilin

end Matrix

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem TendstoUniformlyOn.weightedInvCovectorBilin
    {ι P N : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → E) {X : N → P → ℝ × Matrix ι ι ℝ}
    {v : P → ℝ × Matrix ι ι ℝ} {l : Filter N} {K : Set P}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    (hdet : ∀ z ∈ K, (v z).2.det ≠ 0) :
    TendstoUniformlyOn (fun n z => Matrix.weightedInvCovectorBilin b (X n z))
      (fun z => Matrix.weightedInvCovectorBilin b (v z)) l K := by
  apply hX.comp_continuousAt_of_isCompact_image hK
  rintro p ⟨z, hz, rfl⟩
  exact Matrix.continuousAt_weightedInvCovectorBilin b (hdet z hz)

end
