import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapRestrictedNeighborhood
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentSelection
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev LabelE3 := EuclideanSpace ℝ (Fin 3)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "LabelQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem finiteCapComponentLabel_neighborhood (b : ι × Bool) (q : LabelQ)
    (hq : q ∈ finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b) :
    finiteCapComponentLabel hL hδ f hf hdisj q = cuttingSphereComponent hδ f hf hdisj b := by
  let N := finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b
  let B := {x : LabelE3 | ‖x‖ < L + cuttingCollarWidth (precision b.1)}
  have hB : IsConnected B := by
    simpa only [Metric.ball, dist_zero_right] using
      (Metric.isConnected_ball (x := (0 : LabelE3)) (add_pos hL (cuttingCollarWidth_pos (hδ b.1))))
  let : ConnectedSpace N := (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hB)
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  let p : N := ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
    ⟨b, ⟨0, by simpa using hL.le⟩⟩, Or.inl ⟨⟨0, by simpa using hL.le⟩, rfl⟩⟩
  have hc : Continuous (fun x : N => finiteCapComponentLabel hL hδ f hf hdisj x.val) :=
    (continuous_finiteCapComponentLabel hL hδ f hf hdisj).comp continuous_subtype_val
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace N) hc (x := ⟨q, hq⟩) (y := p)

theorem finiteCapNeighborhood_retained_iff (R : Set (ConnectedComponents (cutCore f)))
    (b : ι × Bool) (q : LabelQ)
    (hq : q ∈ finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b) :
    q ∈ finiteCapRetained hL hδ f hf hdisj R ↔ cuttingSphereComponent hδ f hf hdisj b ∈ R := by
  change finiteCapComponentLabel hL hδ f hf hdisj q ∈ R ↔ _
  rw [finiteCapComponentLabel_neighborhood hL hδ f hf hdisj b q hq]

theorem finiteCapRestrictedNeighborhood_subset_retained (R : Set (ConnectedComponents (cutCore f)))
    (b : ι × Bool) (hb : cuttingSphereComponent hδ f hf hdisj b ∈ R) (r : ℝ) :
    (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r : Set LabelQ) ⊆
      finiteCapRetained hL hδ f hf hdisj R := by
  intro q hq
  exact (finiteCapNeighborhood_retained_iff hL hδ f hf hdisj R b q
    ((mem_finiteCapRestrictedNeighborhood_iff hL hδ f hf hdisj b r q).mp hq).1).mpr hb

theorem finiteCapRetained_restricted_cover (R : Set (ConnectedComponents (cutCore f)))
    (r : ι × Bool → ℝ) (hr : ∀ b, 0 < r b) :
    ((finiteCapRetained hL hδ f hf hdisj R : Set LabelQ) ∩
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) ∪
      (⋃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b.val (r b.val) : Set LabelQ)) =
          (finiteCapRetained hL hδ f hf hdisj R : Set LabelQ) := by
  ext q
  constructor
  · rintro (hq | hq)
    · exact hq.1
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hq
      exact finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property (r b.val) hb
  · intro hq
    have hc := eq_univ_iff_forall.mp (finiteCapRestrictedNeighborhood_cover hL hδ f hf hdisj r hr) q
    rcases hc with hi | hb
    · exact Or.inl ⟨hq, hi⟩
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hb
      have hbr := (finiteCapNeighborhood_retained_iff hL hδ f hf hdisj R b q
        ((mem_finiteCapRestrictedNeighborhood_iff hL hδ f hf hdisj b (r b) q).mp hb).1).mp hq
      exact Or.inr (mem_iUnion.mpr ⟨⟨b, hbr⟩, hb⟩)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
