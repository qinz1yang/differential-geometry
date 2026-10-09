import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket
import DifferentialGeometry.Geometry.Collapse.EdgeRowSequenceApplications

/-!
# Consumers of the LC84 edge disk packet

* `EdgeDiskPacket.fibre_homeomorph_closedCell`: the ENTIRE zero fibre
  `{y ∈ B(center, 100Δ) : η_p y = 0, H y ≤ 4Δ}` of a packet, as a subspace of `M`, is homeomorphic
  to `ClosedCell 2` (through `diskModel` and `slabFibreHomeomorph`), compact and connected.
* `EdgeDiskPacket.tsupport_cutoff_subset_ball`: the margin in the form consumed by LC87 / FC12:
  the edge cutoff is supported in the open ball `B(center, 13Δ)`, while the coordinate domain
  contains `B̄(center, 100Δ)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_packetapp_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

/-- **Consumer.** The whole zero fibre of a packet is a closed disk, compact and connected. -/
theorem EdgeDiskPacket.fibre_homeomorph_closedCell
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) (hΔ : 0 < Δ) :
    Nonempty ({y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ∧
      ConnectedSpace {y : M // y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let T := slabFibreHomeomorph P.slabOpen (B := ball P.center (100 * Δ)) (f := P.coord)
    (H := edgeRowHeight Δ F ρ) (c := 4 * Δ)
    (fun y hy => ball_subset_ball (by linarith) (P.slabOpen_subset hy))
    (fun y hy hf hH => P.slab_subset y hy (by rw [hf, abs_zero]; positivity) hH)
  let φ := (Diffeomorph.toHomeomorph P.diskModel).trans T
  have hconn : ConnectedSpace (ClosedCell 2) := by
    have heq : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    have hc : IsConnected {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} := by
      rw [heq]
      exact (Metric.isPathConnected_closedBall zero_le_one).isConnected
    exact isConnected_iff_connectedSpace.mp hc
  exact ⟨⟨φ.symm⟩, φ.compactSpace, φ.connectedSpace_iff.mp hconn⟩

/-- **Consumer (LC87 / FC12 margin).** The edge cutoff is supported in `B(center, 13Δ)`. -/
theorem EdgeDiskPacket.tsupport_cutoff_subset_ball
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) (hΔ : 0 < Δ) :
    tsupport ((Subtype.val : ball P.center (100 * Δ) → M).extend
      (fun x => edgeCoordinateProfile (P.coord x.val / Δ) *
        edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0) ⊆ ball P.center (13 * Δ) :=
  P.tsupport_cutoff_subset.trans (closedBall_subset_ball (by linarith))

end DifferentialGeometry.Geometry.Collapse
