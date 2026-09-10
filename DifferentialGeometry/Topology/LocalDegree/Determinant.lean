import DifferentialGeometry.Topology.LocalDegree.EuclideanLinearization
import DifferentialGeometry.Topology.LocalDegree.LinearDegree

set_option autoImplicit false
open Metric Set
open scoped Topology
noncomputable section
namespace Poincare.LocalDegree

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))}

theorem isolatedZero_of_det_fderiv_ne_zero
    {s : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hd : DifferentiableAt ℝ f x) (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    isolatedZero f x := by
  let A := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  exact isolatedZero_of_hasFDerivAt_equiv A hs hc hz hd.hasFDerivAt

theorem euclideanLocalDegree_eq_sign_det_fderiv
    (h : isolatedZero f x) (hd : DifferentiableAt ℝ f x)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    euclideanLocalDegree f x h = (SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : ℤ) := by
  let A := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hR := h.choose_spec
  rw [euclideanLocalDegree_eq_linear_of_hasFDerivAt A
    (closedBall_mem_nhds _ hR.pos) hR.continuousOn hR.zero hd.hasFDerivAt h,
    euclideanSphereDegree_linearEquiv]
  rfl

end Poincare.LocalDegree
