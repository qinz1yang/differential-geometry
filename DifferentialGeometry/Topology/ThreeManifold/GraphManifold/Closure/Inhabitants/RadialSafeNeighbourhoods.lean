import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialPreparedRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

instance radialRowsEndEmpty : IsEmpty radialRows.edge.EdgeEnd := by
  change IsEmpty radialEdgeBundle.EdgeEnd
  exact radialEdgeEndEmpty

theorem radial_shared_unique (σ : radialRows.SharedFace) :
    σ.val = radialSharedEnd := by
  apply Subtype.ext
  apply Prod.ext
  · exact @Subsingleton.elim (Fin 1) inferInstance _ _
  · exact radial_shared_false σ

theorem radial_shared_indices_unique (σ τ : radialRows.SharedFace) : σ = τ := by
  apply Subtype.ext
  exact (radial_shared_unique σ).trans (radial_shared_unique τ).symm

theorem radial_shared_level (σ : radialRows.SharedFace) : radialRows.sharedSet σ =
    {p | height p = -(1 / 4 : ℝ)} := by
  change radialSlims.endSet σ.val = _
  let τ : ActualSharedFace radialSlims := σ
  have he := radial_end_height τ.val
  rw [radial_shared_false τ] at he
  exact he

theorem radial_shared_closure_band : closure (cuspNear : Set carrier.Carrier) ⊆
    {p | -(3 / 8 : ℝ) ≤ height p ∧ height p ≤ -(1 / 8 : ℝ)} := by
  apply closure_minimal
  · intro p hp
    exact ⟨hp.1.le, hp.2.le⟩
  · exact (isClosed_le continuous_const height_continuous).inter
      (isClosed_le height_continuous continuous_const)

theorem radialSharedSafe : SharedSafe radialRows (fun _ => cuspNear) where
  face_subset σ := by
    rw [radial_shared_level]
    intro p hp
    change height p = -(1 / 4 : ℝ) at hp
    change -(3 / 8 : ℝ) < height p ∧ height p < -(1 / 8 : ℝ)
    rw [hp]
    norm_num
  closure_disjoint σ τ hn := (hn (radial_shared_indices_unique σ τ)).elim
  off_edge σ := by
    change Disjoint (closure (cuspNear : Set carrier.Carrier)) radialEdgeBundle.edgePiece
    rw [radial_edge_height, disjoint_left]
    intro p hp hq
    have hband := radial_shared_closure_band hp
    change height p ≤ -(3 / 4 : ℝ) at hq
    linarith [hband.1]
  off_region σ := by
    change Disjoint (closure (cuspNear : Set carrier.Carrier)) radialCircleBundle.region
    rw [radialCircleBundle_region, disjoint_left]
    intro p hp hq
    have hband := radial_shared_closure_band hp
    change -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ) at hq
    linarith [hband.1, hq.2]
  off_external σ i := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [disjoint_left]
    intro p hp hq
    have hband := radial_shared_closure_band hp
    have hc := collar_target_height hq
    linarith [hband.2]

def radialSafe : ProducerSafeNeighbourhoods radialRows where
  shared _ := cuspNear
  shared_safe := radialSharedSafe
  cornerBase e := isEmptyElim e
  cornerBase_sub e := isEmptyElim e
  rimBase_mem e := isEmptyElim e
  corner_closure_disjoint e := isEmptyElim e
  corner_off_external e := isEmptyElim e
  corner_off_shared e := isEmptyElim e

end GC.GraphManifold.Assembly.FC39P0.X135Radial
