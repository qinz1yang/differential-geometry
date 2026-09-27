import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "LabelQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

private def componentOnSum : IndexedCaps ι L ⊕ cutCore f → ConnectedComponents (cutCore f) :=
  Sum.elim (fun p => cuttingSphereComponent hδ f hf hdisj p.1) ConnectedComponents.mk

private theorem componentOnSum_rel (a b : IndexedCaps ι L ⊕ cutCore f)
    (h : adjunctionRel (indexedCapBoundary (ι := ι) hL)
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) a b) :
    componentOnSum hδ f hf hdisj a = componentOnSum hδ f hf hdisj b := by
  rcases h with ⟨s, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact (cuttingSphere_component_eq hδ f hf hdisj s.1 s.2).symm
  · exact cuttingSphere_component_eq hδ f hf hdisj s.1 s.2

def finiteCapComponentLabel : LabelQ → ConnectedComponents (cutCore f) :=
  Quot.lift (componentOnSum hδ f hf hdisj) (componentOnSum_rel hL hδ f hf hdisj)

theorem finiteCapComponentLabel_core (x : cutCore f) :
    finiteCapComponentLabel hL hδ f hf hdisj
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj x) = ConnectedComponents.mk x := rfl

theorem finiteCapComponentLabel_cap (p : IndexedCaps ι L) :
    finiteCapComponentLabel hL hδ f hf hdisj
      (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj p) =
        cuttingSphereComponent hδ f hf hdisj p.1 := rfl

theorem continuous_finiteCapComponentLabel : Continuous (finiteCapComponentLabel hL hδ f hf hdisj) := by
  apply continuous_quot_lift
  apply continuous_sumElim.mpr
  refine ⟨continuous_sigma (fun b => ?_), ConnectedComponents.continuous_coe⟩
  change Continuous (fun _ : {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ ≤ L} => cuttingSphereComponent hδ f hf hdisj b)
  exact continuous_const

theorem finiteCapComponentLabel_surjective : Surjective (finiteCapComponentLabel hL hδ f hf hdisj) := by
  intro c
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p, rfl⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
