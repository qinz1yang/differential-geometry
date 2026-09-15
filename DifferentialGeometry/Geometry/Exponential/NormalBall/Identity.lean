import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

noncomputable section
open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

def identity {r : ℝ} (hr : 0 < r) : NormalBallChart (I := 𝓘(ℝ, E)) (0 : E) where
  radius := r
  radius_pos := hr
  hom :=
    { toPartialEquiv := PartialEquiv.refl E
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := contMDiffOn_id
      contMDiffOn_invFun := contMDiffOn_id }
  ball_subset := subset_univ _
  map_zero := rfl
  smooth_to := contMDiffOn_id
  smooth_inv := contMDiffOn_id

@[simp] theorem identity_radius {r : ℝ} (hr : 0 < r) :
    (identity (E := E) hr).radius = r := rfl

@[simp] theorem identity_apply {r : ℝ} (hr : 0 < r) (z : E) :
    (identity (E := E) hr).hom z = z := rfl

@[simp] theorem identity_inv {r : ℝ} (hr : 0 < r) (z : E) :
    (identity (E := E) hr).inv z = z := rfl

@[simp] theorem metric_identity (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {r : ℝ} (hr : 0 < r) :
    (identity (E := E) hr).metric g = fun z => g.inner z := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [metric_apply]
  change g.inner z (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w) = g.inner z v w
  rw [mfderiv_id]
  rfl


end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
