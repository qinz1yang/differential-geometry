import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology
namespace DifferentialGeometry.Topology.Manifold
variable {X E : Type*} [TopologicalSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem orientation_map_eventually_eq (e : X → E ≃L[ℝ] E) (x : X)
    (he : ContinuousAt (fun y => (e y : E →L[ℝ] E)) x)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    ∀ᶠ y in 𝓝 x, Orientation.map _ (e y).toLinearEquiv o =
      Orientation.map _ (e x).toLinearEquiv o := by
  let d : X → ℝ := fun y => (e y : E →L[ℝ] E).det
  have hd : ContinuousAt d x := ContinuousLinearMap.continuous_det.continuousAt.comp he
  have hn : d x ≠ 0 := (e x).toLinearEquiv.isUnit_det'.ne_zero
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hx := (Orientation.map_eq_neg_iff_det_neg o (e x).toLinearEquiv (by simp)).2 hneg
    filter_upwards [hd.eventually (gt_mem_nhds hneg)] with y hy
    exact ((Orientation.map_eq_neg_iff_det_neg o (e y).toLinearEquiv (by simp)).2 hy).trans hx.symm
  · have hx := (Orientation.map_eq_iff_det_pos o (e x).toLinearEquiv (by simp)).2 hpos
    filter_upwards [hd.eventually (lt_mem_nhds hpos)] with y hy
    exact ((Orientation.map_eq_iff_det_pos o (e y).toLinearEquiv (by simp)).2 hy).trans hx.symm

theorem orientation_map_isLocallyConstant (e : X → E ≃L[ℝ] E)
    (he : Continuous (fun y => (e y : E →L[ℝ] E)))
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    IsLocallyConstant (fun y => Orientation.map _ (e y).toLinearEquiv o) :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    orientation_map_eventually_eq e x he.continuousAt o

theorem orientation_map_locallyConstant_field (e : X → E ≃L[ℝ] E)
    (he : Continuous (fun y => (e y : E →L[ℝ] E)))
    (o : X → Orientation ℝ E (Fin (Module.finrank ℝ E))) (ho : IsLocallyConstant o) :
    IsLocallyConstant (fun y => Orientation.map _ (e y).toLinearEquiv (o y)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  filter_upwards [ho.eventually_eq x,
    orientation_map_eventually_eq e x he.continuousAt (o x)] with y hy heq
  rw [hy]
  exact heq
end DifferentialGeometry.Topology.Manifold
