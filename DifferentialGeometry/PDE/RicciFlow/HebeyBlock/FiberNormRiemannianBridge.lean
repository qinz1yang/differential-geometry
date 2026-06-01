import DifferentialGeometry.Integral.Connection.TensorRSChartFiberToModelOpNormUnconditional
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberFromModelOpNormUnconditional
import DifferentialGeometry.Tensor.RSTensor.TensorRSBundleLocalityIdentities

/-!
# Uniform comparability of model-fiber norm and Riemannian fiber norm

On a compact Riemannian manifold `(M, g)`, the model-fiber norm
`‖TensorRSSpace.toModel T‖` and the g-induced Riemannian bundle norm `‖T‖_g`
(from `tensorRS_riemannianBundle g r s`) are uniformly comparable.

## Strategy

At each point `x₀ ∈ M`, the forward-trivialization locality identity
(`tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality`) shows
that the trivialization CLM at chart `x₀` evaluated at `x₀` itself
agrees pointwise with `TensorRSSpace.toModel`:

  `triv_{x₀}.CLM_{x₀}(T) = toModel(T)`

Combining with the unconditional forward triv op-norm bound
(`tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional`)
applied to the compact singleton `K = {x₀}`, we obtain:

  `‖toModel(T)‖ ≤ C_{x₀} * ‖T‖_g`

at the single point `x₀`. For the reverse direction, the inverse locality
identity (`tensorRS_trivAt_symmL_apply_eq_self_on_locality`) gives:

  `triv_{x₀}.symmL_{x₀}(toModel(T)) = T`

and the unconditional inverse triv bound gives:

  `‖T‖_g ≤ D_{x₀} * ‖toModel(T)‖`

## Main results

* `triv_eq_toModel_at_chartCenter` — the trivialization at chart center
  equals `TensorRSSpace.toModel`.
* `symmL_toModel_eq_self_at_chartCenter` — the inverse trivialization
  applied to `toModel(T)` recovers `T` at the chart center.
* `modelNorm_le_gNorm_pointwise` — per-point forward bound.
* `gNorm_le_modelNorm_pointwise` — per-point reverse bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- At the chart center `b₀`, the forward trivialization of the `(r,s)`-tensor
bundle equals `TensorRSSpace.toModel` as CLMs. This follows from the locality
identity with `b = b₀`, since `chartAt H b₀ = chartAt H b₀` trivially. -/
theorem triv_eq_toModel_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b₀ T =
      TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T := by
  ext D_α
  have h_loc :=
    tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
      (I := I) (M := M) r s b₀
      (h_chart := rfl) (h_src := mem_chart_source H b₀) T D_α
  simp only [TensorRSSpace.toModel, tensorRSSpace_continuousLinearEquiv]
  rw [h_loc]
  rfl

set_option linter.unusedSectionVars false in
/-- At the chart center `b₀`, the inverse trivialization applied to
`TensorRSSpace.toModel T` recovers `T`. -/
theorem symmL_toModel_eq_self_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).symmL ℝ b₀
          (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T) = T := by
  have h_mem : b₀ ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet :=
    ⟨mem_baseSet_trivializationAt _ _ b₀, mem_baseSet_trivializationAt _ _ b₀⟩
  rw [← triv_eq_toModel_at_chartCenter (I := I) r s b₀ T]
  exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀) h_mem T

set_option linter.unusedSectionVars false in
set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-point forward bound.** At each point `x₀ ∈ M`, there exists `C > 0`
such that `‖toModel(T)‖ ≤ C * ‖T‖_g` for all `T` in the fiber at `x₀`. -/
theorem modelNorm_le_gNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ ≤ C * ‖T‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨C₀, hC₀_pos, fun T => ?_⟩
  have h_triv := hC₀_bound x₀ (Set.mem_singleton x₀) T
  rw [triv_eq_toModel_at_chartCenter (I := I) r s x₀ T] at h_triv
  exact h_triv

set_option linter.unusedSectionVars false in
set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-point reverse bound.** At each point `x₀ ∈ M`, there exists `D > 0`
such that `‖T‖_g ≤ D * ‖toModel(T)‖` for all `T` in the fiber at `x₀`. -/
theorem gNorm_le_modelNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨D₀, hD₀_pos, hD₀_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨D₀, hD₀_pos, fun T => ?_⟩
  have h_inv := hD₀_bound x₀ (Set.mem_singleton x₀)
    (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T)
  rw [symmL_toModel_eq_self_at_chartCenter (I := I) r s x₀ T] at h_inv
  exact h_inv

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
