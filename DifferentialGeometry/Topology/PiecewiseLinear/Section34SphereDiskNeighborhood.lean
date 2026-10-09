import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedSphereAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_interior_point_outside_closed_disk_subset
    {Γ D : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ) (hD : IsClosed D)
    (hDΓ : D ⊆ r '' openSimplex (stdVertices 1)) :
    ∃ p ∈ Γ \ r '' stdSimplexBoundary 2, p ∉ D := by
  obtain ⟨z, hz⟩ := hr.isPLSphere_image_stdSimplexBoundary.nonempty
  have hzΓ : z ∈ Γ := hr.image_eq ▸ image_mono (fun _ hx => hx.1) hz
  have hzD : z ∉ D := by
    intro hx
    have h := hDΓ hx
    rw [hr.image_openSimplex_stdVertices] at h
    exact h.2 hz
  have hzcl : z ∈ closure (Γ \ r '' stdSimplexBoundary 2) := by
    rwa [hr.closure_sdiff_image_stdSimplexBoundary]
  obtain ⟨p, hpD, hpΓ⟩ := mem_closure_iff_nhds.mp hzcl _ (hD.isOpen_compl.mem_nhds hzD)
  exact ⟨p, hpΓ, hpD⟩

theorem IsPLSphere.exists_disk_chart_around_disk
    {S D : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S)
    (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    ∃ (Γ : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ ∧ Γ ⊆ S ∧
      D ⊆ r '' openSimplex (stdVertices 1) ∧
      p ∈ Γ \ r '' stdSimplexBoundary 2 ∧ p ∉ D ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ Γ ↔ y ∈ S := by
  obtain ⟨q, hqS, hqD⟩ := (hS.isConnected_sdiff_of_isPLBall_two hD hDS).nonempty
  obtain ⟨Q, v, hv, hQS, hQD, -, -⟩ :=
    hS.exists_disk_neighborhood_avoiding_closed hD.isPolyhedron.isClosed hqS hqD
  have hQ : IsPLBall 2 Q := ⟨v, hv⟩
  obtain ⟨r, hr⟩ := hS.isPLBall_closure_sdiff hQ hQS
  have hΓS : closure (S \ Q) ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  have hbdQ : r '' stdSimplexBoundary 2 ⊆ Q :=
    (hS.image_stdSimplexBoundary_complement hQ hQS hr).subset.trans inter_subset_right
  have hDΓ : D ⊆ closure (S \ Q) \ r '' stdSimplexBoundary 2 := by
    intro x hx
    exact ⟨subset_closure ⟨hDS hx, fun hxQ => disjoint_left.mp hQD hxQ hx⟩,
      fun hxBd => disjoint_left.mp hQD (hbdQ hxBd) hx⟩
  obtain ⟨z, hz⟩ := hr.isPLSphere_image_stdSimplexBoundary.nonempty
  have hzD : z ∉ D := fun hzD => (hDΓ hzD).2 hz
  have hzΓ : z ∈ closure (S \ Q) := hr.image_eq ▸ image_mono (fun _ hx => hx.1) hz
  have hzcl : z ∈ closure (closure (S \ Q) \ r '' stdSimplexBoundary 2) := by
    rwa [hr.closure_sdiff_image_stdSimplexBoundary]
  obtain ⟨p, hpD, hpΓ⟩ := mem_closure_iff_nhds.mp hzcl _
    (hD.isPolyhedron.isClosed.isOpen_compl.mem_nhds hzD)
  refine ⟨closure (S \ Q), r, p, hr, hΓS, ?_, hpΓ, hpD, ?_⟩
  · rwa [hr.image_openSimplex_stdVertices]
  · intro x hx
    filter_upwards [hQ.isPolyhedron.isClosed.isOpen_compl.mem_nhds
      (fun hxQ => disjoint_left.mp hQD hxQ hx)] with y hyQ
    exact ⟨fun hy => hΓS hy, fun hy => subset_closure ⟨hy, hyQ⟩⟩

theorem IsPLSphere.exists_disk_neighborhood_of_disk_subset
    {S D Ω : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S)
    (hD : IsPLBall 2 D) (hDS : D ⊆ S) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ (M : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M ∧ M ⊆ S ∩ Ω ∧
      D ⊆ r '' openSimplex (stdVertices 1) ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ M ↔ y ∈ S := by
  obtain ⟨Γ, q, p, hq, hΓS, hDΓ, hpΓ, hpD, hag⟩ := hS.exists_disk_chart_around_disk hD hDS
  have hpc := hq.isPseudoCell_of_mem_interior hpΓ
  have hDE : D ⊆ (Γ \ q '' stdSimplexBoundary 2) \ {p} := by
    intro x hx
    refine ⟨?_, fun hxp => hpD (hxp ▸ hx)⟩
    exact hq.image_openSimplex_stdVertices ▸ hDΓ hx
  obtain ⟨M, r, hr, hMΓ, hMΩ, hDM, hMgerm⟩ := hpc.exists_disk_neighborhood hD hDE hΩ hDΩ
  refine ⟨M, r, hr, fun x hx => ⟨hΓS (hMΓ hx).1.1, hMΩ hx⟩, hDM, ?_⟩
  intro x hx
  filter_upwards [hMgerm x hx, hag x hx] with y h₁ h₂
  exact h₁.trans h₂

end DifferentialGeometry.Topology.PiecewiseLinear
