import DifferentialGeometry.Topology.Engulfing.Local.Charts.ChartSourceNeighborhood
import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology
open scoped ContinuousMap

variable {Z M F : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [MetricSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_chart_preimage_tolerance (f : C(Z, M))
    (e : OpenPartialHomeomorph M F) (c : F) {r R : ℝ} (hrR : r < R)
    (hR : closedBall c R ⊆ e.target) {A : Set Z}
    (hA : f ⁻¹' (e.symm '' closedBall c R) ⊆ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : C(Z, M), (∀ x, dist (g x) (f x) < δ) →
      g ⁻¹' (e.symm '' closedBall c r) ⊆ A := by
  let V := f ⁻¹' (e.source ∩ e ⁻¹' ball c R)
  have hV : IsOpen V := (e.isOpen_inter_preimage isOpen_ball).preimage f.continuous
  have hVA : V ⊆ A := by
    intro x hx
    exact hA ⟨e (f x), ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  have hr : closedBall c r ⊆ e.target := (closedBall_subset_closedBall hrR.le).trans hR
  let S := e.symm '' closedBall c r
  have hS : IsClosed S := ((isCompact_closedBall c r).image_of_continuousOn
    (e.continuousOn_symm.mono hr)).isClosed
  have havoid : Disjoint (f '' Vᶜ) S := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    apply hx
    change f x ∈ e.source ∩ e ⁻¹' ball c R
    rw [← he]
    exact ⟨e.map_target (hr hz), by
      change e (e.symm z) ∈ ball c R
      rw [e.right_inv (hr hz)]
      exact closedBall_subset_ball hrR hz⟩
  obtain ⟨δ, hδ, hcontrol⟩ := exists_perturbation_control f hV.isClosed_compl.isCompact
    isOpen_univ hS (subset_univ _) havoid
  refine ⟨δ, hδ, fun g hg x hx => ?_⟩
  have hd := (hcontrol g (fun x _ => hg x)).2
  by_contra hn
  exact disjoint_left.mp hd (mem_image_of_mem g (fun hxV => hn (hVA hxV))) hx

end DifferentialGeometry.Topology.Engulfing
