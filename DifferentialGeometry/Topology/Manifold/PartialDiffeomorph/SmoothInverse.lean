import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.PartialDiffeomorph

theorem contDiffOn_symm_of_partialDiffeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1) {k : ℕ∞ω}
    (he : ContDiffOn ℝ k e e.source) : ContDiffOn ℝ k e.symm e.target := by
  intro y hy
  have hx : e.symm y ∈ e.source := e.toPartialEquiv.map_target hy
  let A : E ≃L[ℝ] F := (e.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 hx).mfderivToContinuousLinearEquiv (by norm_num)
  have hA : A.toContinuousLinearMap = fderiv ℝ e (e.symm y) := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e (e.symm y) = fderiv ℝ e (e.symm y)
    exact mfderiv_eq_fderiv
  have hd : HasFDerivAt e A.toContinuousLinearMap (e.symm y) := by
    rw [hA]
    exact ((contMDiffAt_iff_contDiffAt.mp
      (e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx))).differentiableAt
        (by norm_num)).hasFDerivAt
  exact (e.toOpenPartialHomeomorph.contDiffAt_symm hy hd
    (he.contDiffAt (e.open_source.mem_nhds hx))).contDiffWithinAt

end DifferentialGeometry.Manifold.PartialDiffeomorph
