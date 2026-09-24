import DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import DifferentialGeometry.Topology.UniformConvergence.Composition
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace Matrix

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

theorem continuousAt_smul_covectorBilin_inv (b : ι → E)
    {p : 𝕜 × Matrix ι ι 𝕜} (hp : p.2.det ≠ 0) :
    ContinuousAt (fun q : 𝕜 × Matrix ι ι 𝕜 => q.1 • covectorBilin b q.2⁻¹) p := by
  have hinv : ContinuousAt (fun A : Matrix ι ι 𝕜 => A⁻¹) p.2 := by
    apply continuousAt_matrix_inv _
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ hp
  have hbilin : ContinuousAt
      (fun q : 𝕜 × Matrix ι ι 𝕜 => covectorBilin b q.2⁻¹) p :=
    (covectorBilin b).continuous.continuousAt.comp
      (hinv.comp continuous_snd.continuousAt)
  exact continuous_fst.continuousAt.smul hbilin

end Matrix

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace 𝕜 (E →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  ContinuousLinearMap.toNormedSpace

theorem TendstoUniformlyOn.smul_covectorBilin_inv
    {ι P N : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → E) {X : N → P → 𝕜 × Matrix ι ι 𝕜}
    {v : P → 𝕜 × Matrix ι ι 𝕜} {l : Filter N} {K : Set P}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    (hdet : ∀ z ∈ K, (v z).2.det ≠ 0) :
    TendstoUniformlyOn (fun n z => (X n z).1 • Matrix.covectorBilin b (X n z).2⁻¹)
      (fun z => (v z).1 • Matrix.covectorBilin b (v z).2⁻¹) l K := by
  apply hX.comp_continuousAt_of_isCompact_image
    (g := fun p : 𝕜 × Matrix ι ι 𝕜 => p.1 • Matrix.covectorBilin b p.2⁻¹) hK
  rintro p ⟨z, hz, rfl⟩
  exact Matrix.continuousAt_smul_covectorBilin_inv b (hdet z hz)

end
