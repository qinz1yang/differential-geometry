import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientSphericalCover
import DifferentialGeometry.Topology.Covering.SphericalBall
import DifferentialGeometry.Topology.ProjectiveSpace.SmoothNonembedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapExterior
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

section
set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem eq_of_connected_open_of_frontier_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hcA : IsPreconnected A) (hcB : IsPreconnected B)
    (hF : frontier A = frontier B) (hAB : (A ∩ B).Nonempty) : A = B := by
  have hdis : Disjoint A (frontier B) := by
    rw [← hF]
    simpa only [hA.interior_eq] using (disjoint_interior_frontier (s := A))
  have hdis' : Disjoint B (frontier A) := by
    rw [hF]
    simpa only [hB.interior_eq] using (disjoint_interior_frontier (s := B))
  exact ((DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
    hcA hAB hdis).trans interior_subset).antisymm
      ((DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        hcB (by simpa only [inter_comm] using hAB) hdis').trans interior_subset)

theorem LocalCap.exists_exterior_ball_of_compact_ancientKappa_of_projective_slice
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    {eps t : ℝ} {x : F.M} {U : Set F.M} (cap : LocalCap F.S eps x t U)
    (rp : SphereAntipodalQuotient → F.M)
    (hrp : Manifold.IsSmoothEmbedding I2 I3 ∞ rp) (hrpU : range rp ⊆ U) :
    ∃ G : PartialDiffeomorph I3 I3 ThreeSpace F.M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
      G '' Metric.ball (0 : ThreeSpace) 1 = Uᶜ ∧
      G '' Metric.closedBall (0 : ThreeSpace) 1 = closure Uᶜ ∧
      G '' Metric.sphere (0 : ThreeSpace) 1 = frontier U := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨⟨p, hp, honto, hlocal⟩, _hpi⟩ := exists_spherical_cover_of_compact_ancientKappa F hF
  have hxU : x ∈ interior U := cap.core_inside (interior_subset cap.center_inside)
  have hxout : x ∉ range (fun z : Sphere 2 => cap.tubeMap (z, 1)) := by
    rw [cap.range_outer_boundary_eq]
    exact fun h => disjoint_interior_frontier.le_bot ⟨hxU, h⟩
  obtain ⟨G, hG, hGs⟩ := DifferentialGeometry.Topology.exists_ball_chart_of_spherical_cover
    hp honto hlocal (fun z : Sphere 2 => cap.tubeMap (z, 1)) cap.outer_boundary_isSmoothEmbedding hxout
  rw [cap.range_outer_boundary_eq] at hGs
  let B := G '' Metric.ball (0 : ThreeSpace) 1
  have hbs : Metric.ball (0 : ThreeSpace) 1 ⊆ G.source := Metric.ball_subset_closedBall.trans hG
  have hBo : IsOpen B := DifferentialGeometry.image_opens_isOpen G (U := ⟨_, Metric.isOpen_ball⟩) hbs
  have hBc : IsConnected B := ((convex_ball (0 : ThreeSpace) (1 : ℝ)).isConnected
    ⟨0, Metric.mem_ball_self zero_lt_one⟩).image G (G.contMDiffOn_toFun.continuousOn.mono hbs)
  have hKc : IsCompact (G '' Metric.closedBall (0 : ThreeSpace) 1) :=
    (isCompact_closedBall (0 : ThreeSpace) 1).image_of_continuousOn
      (G.contMDiffOn_toFun.continuousOn.mono hG)
  have hBcl : closure B = G '' Metric.closedBall (0 : ThreeSpace) 1 := by
    apply subset_antisymm
    · exact closure_minimal (image_mono Metric.ball_subset_closedBall) hKc.isClosed
    · have hc : ContinuousOn G (closure (Metric.ball (0 : ThreeSpace) 1)) := by
        rw [closure_ball _ one_ne_zero]
        exact G.contMDiffOn_toFun.continuousOn.mono hG
      simpa only [closure_ball _ one_ne_zero] using hc.image_closure
  have hBfr : frontier B = frontier U := by
    rw [frontier, hBcl, hBo.interior_eq, ← hGs]
    apply subset_antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hnot⟩
      have hznot : z ∉ Metric.ball (0 : ThreeSpace) 1 := fun h => hnot (mem_image_of_mem _ h)
      refine ⟨z, ?_, rfl⟩
      rw [Metric.mem_sphere]
      exact le_antisymm hz (not_lt.mp hznot)
    · rintro y ⟨z, hz, rfl⟩
      have hzc : z ∈ Metric.closedBall (0 : ThreeSpace) 1 := hz.le
      refine ⟨mem_image_of_mem _ hzc, ?_⟩
      rintro ⟨w, hw, heq⟩
      have hwz : w = z := G.toPartialEquiv.injOn (hbs hw) (hG hzc) heq
      subst w
      exact (ne_of_lt hw) hz
  have hc : IsClosed U := cap.isCompact_carrier.isClosed
  have hUi := cap.isConnected_interior_and_compl
  have hfrontUi : frontier (interior U) = frontier U := by
    obtain ⟨K, hK, _hx⟩ := cap.exists_compactDomain
    have hreg : closure (interior U) = U := by simpa only [hK] using K.regular_closed
    rw [frontier, hreg, interior_interior, hc.frontier_eq]
  have hBside : B = interior U ∨ B = Uᶜ := by
    obtain ⟨y, hy⟩ := hBc.nonempty
    have hyF : y ∉ frontier U := by
      rw [← hBfr]
      exact fun h => disjoint_interior_frontier.le_bot ⟨hBo.interior_eq.symm ▸ hy, h⟩
    have hycases : y ∈ interior U ∪ Uᶜ := by
      rw [← hc.isOpen_compl.interior_eq, ← compl_frontier_eq_union_interior]
      exact hyF
    rcases hycases with hyU | hyU
    · exact Or.inl (eq_of_connected_open_of_frontier_eq hBo isOpen_interior
        hBc.isPreconnected hUi.1.isPreconnected (hBfr.trans hfrontUi.symm) ⟨y, hy, hyU⟩)
    · exact Or.inr (eq_of_connected_open_of_frontier_eq hBo hc.isOpen_compl
        hBc.isPreconnected hUi.2.isPreconnected (hBfr.trans (frontier_compl U).symm) ⟨y, hy, hyU⟩)
  have hBext : B = Uᶜ := by
    rcases hBside with hinside | hout
    · have hUimage : U = G '' Metric.closedBall (0 : ThreeSpace) 1 := by
        obtain ⟨K, hK, _hx⟩ := cap.exists_compactDomain
        have hreg : closure (interior U) = U := by simpa only [hK] using K.regular_closed
        rw [← hBcl, hinside, hreg]
      apply False.elim
      apply SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target rp hrp G
      apply hrpU.trans
      rw [hUimage]
      rintro y ⟨z, hz, rfl⟩
      exact G.map_source' (hG hz)
    · exact hout
  exact ⟨G, hG, hBext, hBcl.symm.trans (congrArg closure hBext), hGs⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
