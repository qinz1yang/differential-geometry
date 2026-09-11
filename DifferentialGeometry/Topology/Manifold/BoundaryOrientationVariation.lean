import DifferentialGeometry.Topology.Manifold.BoundaryOrientationFrameChange
import DifferentialGeometry.Topology.Manifold.OrientationTransportVariation

set_option autoImplicit false
noncomputable section
open Function Module Filter
open scoped Topology
namespace DifferentialGeometry.Topology.Manifold
variable {X E F : Type*} [TopologicalSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalFirstOrientation_eventually_eq (e : X → (ℝ × F) ≃L[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (x : X)
    (he : ContinuousAt (fun y => (e y : (ℝ × F) →L[ℝ] E)) x)
    (o : Orientation ℝ E (Fin 3)) :
    ∀ᶠ y in 𝓝 x, normalFirstOrientation (e y).toLinearEquiv b o =
      normalFirstOrientation (e x).toLinearEquiv b o := by
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.of_injective (e x).symm.toLinearMap (e x).symm.injective
  let c : X → E ≃L[ℝ] E := fun y => (e x).symm.trans (e y)
  have hc : ContinuousAt (fun y => (c y : E →L[ℝ] E)) x := by
    change ContinuousAt (fun y => (e y : (ℝ × F) →L[ℝ] E).comp ((e x).symm : E →L[ℝ] (ℝ × F))) x
    exact he.clm_comp continuousAt_const
  have hcx : c x = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact (e x).apply_symm_apply v
  have hpos : 0 < (c x : E →L[ℝ] E).det := by
    rw [hcx]
    change 0 < LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)
    rw [LinearMap.det_id]
    exact zero_lt_one
  have hd := ContinuousLinearMap.continuous_det.continuousAt.comp hc
  have hdim : Fintype.card (Fin 3) = Module.finrank ℝ E := by
    rw [← (e x).toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_eq_card_basis b]
    simp
  filter_upwards [hd.eventually (lt_mem_nhds hpos)] with y hy
  have ho : Orientation.map (Fin 3) (c y).toLinearEquiv o = o :=
    (Orientation.map_eq_iff_det_pos o (c y).toLinearEquiv hdim).mpr hy
  have h := normalFirstOrientation_map (e x).toLinearEquiv (c y).toLinearEquiv b o
  rw [ho] at h
  have heq : (e x).toLinearEquiv.trans (c y).toLinearEquiv = (e y).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change e y ((e x).symm ((e x) v)) = e y v
    rw [(e x).symm_apply_apply]
  rw [heq] at h
  exact h

theorem normalFirstOrientation_isLocallyConstant (e : X → (ℝ × F) ≃L[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (he : Continuous (fun y => (e y : (ℝ × F) →L[ℝ] E)))
    (o : Orientation ℝ E (Fin 3)) :
    IsLocallyConstant (fun y => normalFirstOrientation (e y).toLinearEquiv b o) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr fun x =>
    normalFirstOrientation_eventually_eq e b x he.continuousAt o

theorem normalFirstOrientation_locallyConstant_field (e : X → (ℝ × F) ≃L[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (he : Continuous (fun y => (e y : (ℝ × F) →L[ℝ] E)))
    (o : X → Orientation ℝ E (Fin 3)) (ho : IsLocallyConstant o) :
    IsLocallyConstant (fun y => normalFirstOrientation (e y).toLinearEquiv b (o y)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [ho.eventually_eq x, normalFirstOrientation_eventually_eq e b x he.continuousAt (o x)] with y hy heq
  rw [hy]
  exact heq
end DifferentialGeometry.Topology.Manifold
