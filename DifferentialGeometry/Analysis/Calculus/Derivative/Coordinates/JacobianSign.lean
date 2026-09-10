import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem det_fderiv_ne_zero_of_partialDiffeomorph
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {x : E} (hx : x ∈ e.source) :
    (fderiv ℝ e x).toLinearMap.det ≠ 0 := by
  let A := fderiv ℝ e x
  let B := fderiv ℝ e.symm (e x)
  have hA : HasFDerivAt e A x :=
    ((e.contMDiffOn.contDiffOn.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  have hB : HasFDerivAt e.symm B (e x) :=
    ((e.symm.contMDiffOn.contDiffOn.contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)).hasFDerivAt
  have heq : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E :=
    ((hB.comp x hA).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id x)
  have hprod : B.toLinearMap.det * A.toLinearMap.det = 1 := by
    rw [← LinearMap.det_comp]
    change (B.comp A).toLinearMap.det = 1
    rw [hBA]
    simp
  intro h
  change A.toLinearMap.det = 0 at h
  rw [h, mul_zero] at hprod
  exact zero_ne_one hprod

theorem det_fderiv_pos_iff_of_preconnected
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hconn : IsPreconnected e.source) {x y : E} (hx : x ∈ e.source) (hy : y ∈ e.source) :
    0 < (fderiv ℝ e x).toLinearMap.det ↔ 0 < (fderiv ℝ e y).toLinearMap.det := by
  have hc : ContinuousOn (fun z ↦ (fderiv ℝ e z).toLinearMap.det) e.source :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (e.contMDiffOn.contDiffOn.continuousOn_fderiv_of_isOpen e.open_source (by simp))
  have hprop (a b : E) (ha : a ∈ e.source) (hb : b ∈ e.source)
      (hpos : 0 < (fderiv ℝ e a).toLinearMap.det) :
      0 < (fderiv ℝ e b).toLinearMap.det := by
    by_contra hn
    obtain ⟨z, hz, hzero⟩ := hconn.intermediate_value hb ha hc
      (show (0 : ℝ) ∈ Icc (fderiv ℝ e b).toLinearMap.det (fderiv ℝ e a).toLinearMap.det from
        ⟨le_of_not_gt hn, hpos.le⟩)
    exact det_fderiv_ne_zero_of_partialDiffeomorph e hz hzero
  exact ⟨hprop x y hx hy, hprop y x hy hx⟩

end Poincare.Analysis
