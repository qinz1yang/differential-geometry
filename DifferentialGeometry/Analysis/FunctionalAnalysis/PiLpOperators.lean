import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {E F : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, SeminormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

def piLpMapL (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (∀ i, E i →L[𝕜] F i) →L[𝕜] (PiLp p E →L[𝕜] PiLp p F) :=
  let L : (∀ i, E i →L[𝕜] F i) →ₗ[𝕜] (PiLp p E →L[𝕜] PiLp p F) :=
    { toFun := piLpMap p
      map_add' := by
        intro f g
        ext x i
        rfl
      map_smul' := by
        intro c f
        ext x i
        rfl }
  { toLinearMap := L
    cont := continuous_of_continuous_uncurry L (by
      change Continuous (fun z : (∀ i, E i →L[𝕜] F i) × PiLp p E =>
        WithLp.toLp p (fun i => z.1 i (z.2 i)))
      apply (PiLp.continuous_toLp p F).comp
      apply continuous_pi
      intro i
      exact ((continuous_apply i).comp continuous_fst).clm_apply
        ((PiLp.continuous_apply p E i).comp continuous_snd)) }

@[simp] theorem piLpMapL_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (L : ∀ i, E i →L[𝕜] F i) (x : PiLp p E) (i : ι) :
    piLpMapL p L x i = L i (x i) := rfl

theorem norm_piLpMapL_le : ‖piLpMapL (𝕜 := 𝕜) (E := E) (F := F) 2‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro L
  change ‖piLpMap 2 L‖ ≤ 1 * ‖L‖
  rw [one_mul]
  exact norm_piLpMap_le L (norm_nonneg L) (fun i => norm_le_pi_norm L i)

end ContinuousLinearMap
