import DifferentialGeometry.Topology.Manifold.SphereBoundarySimplyConnected
import DifferentialGeometry.Topology.VanKampen.BallChartEmbeddedCellCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]

theorem ProjectivePresentation.not_simplyConnectedSpace_ball_complement
    (pr : ProjectivePresentation Z)
    (ball : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (hball : Metric.closedBall (0 : ThreeSpace) 2 ⊆ ball.source) :
    ¬ SimplyConnectedSpace ((ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ : Set Z) := by
  intro h
  obtain ⟨d, _⟩ := pr.exists_realProjectiveThree_diffeomorph
  let _ : T2Space Z := d.toHomeomorph.t2Space
  let c : BallChart 3 I3 Z := ⟨ball, hball⟩
  let _ : SimplyConnectedSpace Z := c.simplyConnectedSpace_iff_punctured.mpr h
  let _ : SimplyConnectedSpace RealProjectiveThreeSpace :=
    d.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact not_simplyConnectedSpace_realProjectiveSpace (E := EuclideanSpace ℝ (Fin 4))
    (n := 3) (by decide) inferInstance

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

private theorem exists_ball_of_simplyConnected_capCore [SimplyConnectedSpace M] {K : Set M} (cap : CapCore K) :
    ∃ F : PartialDiffeomorph I3 I3 ThreeSpace M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source ∧
      F '' Metric.closedBall (0 : ThreeSpace) 1 = K := by
  cases cap with
  | ball F hF hK => exact ⟨F, hF, hK⟩
  | projective Z pr b hb F hF hK =>
    have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hb
    exact (pr.not_simplyConnectedSpace_ball_complement b hb
      (DifferentialGeometry.Topology.Manifold.simplyConnectedSpace_ball_complement_of_closed_image
        b F hb1 hF
        (CapCore.isCompact_carrier (CapCore.projective Z pr b hb F hF rfl)).isClosed)).elim

theorem CapCore.exists_ball_of_componentwiseSimplyConnected
    (hsc : ∀ x : M, SimplyConnectedSpace (connectedComponent x))
    {K : Set M} (cap : CapCore K) :
    ∃ F : PartialDiffeomorph I3 I3 ThreeSpace M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source ∧
      F '' Metric.closedBall (0 : ThreeSpace) 1 = K := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace ThreeSpace M
  obtain ⟨x, hx⟩ := cap.nonempty_carrier
  let U : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : SimplyConnectedSpace U := hsc x
  have hKU : K ⊆ (U : Set M) :=
    cap.isConnected_carrier.isPreconnected.subset_connectedComponent hx
  obtain ⟨capU⟩ := cap.nonempty_preimage_open U hKU
  obtain ⟨F, hF, hFK⟩ := exists_ball_of_simplyConnected_capCore capU
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U
    ⟨⟨x, hKU hx⟩⟩
  refine ⟨F.trans inc, (fun z hz => ⟨hF hz, mem_univ _⟩), ?_⟩
  change (inc ∘ F) '' Metric.closedBall (0 : ThreeSpace) 1 = K
  calc
    (inc ∘ F) '' Metric.closedBall (0 : ThreeSpace) 1 =
        inc '' (F '' Metric.closedBall (0 : ThreeSpace) 1) := by rw [Function.comp_def, image_image]
    _ = inc '' (Subtype.val ⁻¹' K : Set U) := by rw [hFK]
    _ = K := ?_
  change Subtype.val '' (Subtype.val ⁻¹' K : Set U) = K
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · intro y hy
    exact ⟨⟨y, hKU hy⟩, hy, rfl⟩

theorem CapCore.exists_ball_of_simplyConnected [SimplyConnectedSpace M]
    {K : Set M} (cap : CapCore K) :
    ∃ F : PartialDiffeomorph I3 I3 ThreeSpace M ∞,
      Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source ∧
      F '' Metric.closedBall (0 : ThreeSpace) 1 = K := by
  apply cap.exists_ball_of_componentwiseSimplyConnected
  intro x
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact (Homeomorph.Set.univ M).toHomotopyEquiv.simplyConnectedSpace

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
