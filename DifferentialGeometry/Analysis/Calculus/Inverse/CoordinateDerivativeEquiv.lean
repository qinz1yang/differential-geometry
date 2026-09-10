import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section
open Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem bijective_fderiv_of_partialDiffeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) {x : E} (hx : x ∈ c.source) :
    Function.Bijective (fderiv ℝ c x) := by
  let L := (c.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv
    (by simp)
  have hL := L.bijective
  change Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) c x) at hL
  rw [mfderiv_eq_fderiv] at hL
  exact hL

theorem fderiv_symm_comp_fderiv_of_partialDiffeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) {x : E} (hx : x ∈ c.source) :
    (fderiv ℝ c.symm (c x)).comp (fderiv ℝ c x) = ContinuousLinearMap.id ℝ E := by
  have hA := ((c.contMDiffOn.contDiffOn.contDiffAt
    (c.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hB := ((c.symm.contMDiffOn.contDiffOn.contDiffAt
    (c.open_target.mem_nhds (c.map_source hx))).differentiableAt (by simp)).hasFDerivAt
  have heq : (c.symm ∘ c) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    exact c.left_inv hy
  exact ((hB.comp x hA).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id x)

end DifferentialGeometry.Analysis
