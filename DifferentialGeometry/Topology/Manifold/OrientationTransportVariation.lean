import DifferentialGeometry.Topology.Manifold.OrientationTransport
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology
namespace DifferentialGeometry.Topology.Manifold
variable {X E F : Type*} [TopologicalSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tangentOrientationEquiv_eventually_eq (e : X → E ≃L[ℝ] F) (x : X)
    (he : ContinuousAt (fun y => (e y : E →L[ℝ] F)) x)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    ∀ᶠ y in 𝓝 x, tangentOrientationEquiv (e y).toLinearEquiv o =
      tangentOrientationEquiv (e x).toLinearEquiv o := by
  let c : X → E ≃L[ℝ] E := fun y => (e y).trans (e x).symm
  have hc : ContinuousAt (fun y => (c y : E →L[ℝ] E)) x := by
    change ContinuousAt (fun y => ((e x).symm : F →L[ℝ] E).comp (e y : E →L[ℝ] F)) x
    exact continuousAt_const.clm_comp he
  have h := orientation_map_eventually_eq c x hc o
  filter_upwards [h] with y hy
  have h' : tangentOrientationEquiv (c y).toLinearEquiv o =
      tangentOrientationEquiv (c x).toLinearEquiv o := by
    simpa only [tangentOrientationEquiv_self] using hy
  have h'' := congrArg (tangentOrientationEquiv (e x).toLinearEquiv) h'
  have hcancel : ∀ z : X, (c z).toLinearEquiv.trans (e x).toLinearEquiv = (e z).toLinearEquiv := by
    intro z
    apply LinearEquiv.ext
    intro v
    exact (e x).apply_symm_apply ((e z) v)
  rw [← tangentOrientationEquiv_trans, ← tangentOrientationEquiv_trans,
    hcancel y, hcancel x] at h''
  exact h''

theorem tangentOrientationEquiv_symm_eventually_eq (e : X → E ≃L[ℝ] F) (x : X)
    (he : ContinuousAt (fun y => (e y : E →L[ℝ] F)) x)
    (o : Orientation ℝ F (Fin (Module.finrank ℝ F))) :
    ∀ᶠ y in 𝓝 x, tangentOrientationEquiv (e y).symm.toLinearEquiv o =
      tangentOrientationEquiv (e x).symm.toLinearEquiv o := by
  have h := tangentOrientationEquiv_eventually_eq e x he
    (tangentOrientationEquiv (e x).symm.toLinearEquiv o)
  filter_upwards [h] with y hy
  have hx : tangentOrientationEquiv (e x).toLinearEquiv
      (tangentOrientationEquiv (e x).symm.toLinearEquiv o) = o :=
    tangentOrientationEquiv_symm (e x).symm.toLinearEquiv o
  rw [hx] at hy
  have h' := congrArg (tangentOrientationEquiv (e y).symm.toLinearEquiv) hy
  have hc := tangentOrientationEquiv_symm (e y).toLinearEquiv
    (tangentOrientationEquiv (e x).symm.toLinearEquiv o)
  exact (h'.symm.trans hc)

theorem tangentOrientationEquiv_symm_locallyConstant_field (e : X → E ≃L[ℝ] F)
    (he : Continuous (fun y => (e y : E →L[ℝ] F)))
    (o : X → Orientation ℝ F (Fin (Module.finrank ℝ F))) (ho : IsLocallyConstant o) :
    IsLocallyConstant (fun y => tangentOrientationEquiv (e y).symm.toLinearEquiv (o y)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  filter_upwards [ho.eventually_eq x,
    tangentOrientationEquiv_symm_eventually_eq e x he.continuousAt (o x)] with y hy heq
  rw [hy]
  exact heq
end DifferentialGeometry.Topology.Manifold
