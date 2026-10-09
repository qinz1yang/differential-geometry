import DifferentialGeometry.Topology.Manifold.HalfLine
import Mathlib.Geometry.Manifold.Immersion

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem isImmersionOfComplement_scaledHalfSpaceOneCoordinate {σ : ℝ} (hσ : σ ≠ 0) :
    IsImmersionOfComplement PUnit.{1} (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : EuclideanHalfSpace 1 ↦ σ * t.val 0) := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let L := T.trans (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 σ hσ))
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    (f := fun t : EuclideanHalfSpace 1 ↦ σ * t.val 0) (x := x)
    ((continuous_const.mul ((EuclideanSpace.proj 0).continuous.comp
      continuous_subtype_val)).continuousAt)
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) PUnit.{1}).trans L)
  intro u hu
  have he := (extChartAt (𝓡∂ 1) x).right_inv hu
  rw [extChartAt_self_apply] at he
  have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) he
  change ((extChartAt (𝓡∂ 1) x).symm u).val 0 = u 0 at hc
  change σ * ((extChartAt (𝓡∂ 1) x).symm u).val 0 = u 0 * σ
  rw [hc, mul_comm]

end DifferentialGeometry.Topology.Manifold
