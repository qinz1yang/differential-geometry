import DifferentialGeometry.Topology.Manifold.SigmaComponent
import DifferentialGeometry.Topology.Manifold.DisjointUnion

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u
variable {ι : Type u} [Fintype ι] (M : ι → ClosedOrientedManifold.{u} 3)

def closedOrientedUnionComponent (i : ι) (x : (M i).Carrier) :
    ClosedOrientedManifold.OrientedDiffeomorph
      ((M i).component (ConnectedComponents.mk x)).toClosedOrientedManifold
      ((closedOrientedUnion M).component
        (ConnectedComponents.mk (⟨i, x⟩ : (closedOrientedUnion
            M).Carrier))).toClosedOrientedManifold := by
  let U := closedOrientedUnion M
  let A := (M i).componentOpen (ConnectedComponents.mk x)
  let B := U.componentOpen (ConnectedComponents.mk (⟨i, x⟩ : U.Carrier))
  have hA : A = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3) x := by
    apply TopologicalSpace.Opens.ext
    exact (M i).componentSet_mk x
  have hB : B = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3)
      (⟨i, x⟩ : U.Carrier) := by
    apply TopologicalSpace.Opens.ext
    exact U.componentSet_mk _
  let F₀ := sigmaComponentDiffeomorph (I := 𝓡 3) (fun j => (M j).Carrier) i x
  let F : Diffeomorph (𝓡 3) (𝓡 3) A B ∞ := hA.symm ▸ (hB.symm ▸ F₀)
  refine ⟨F, ?_⟩
  have hsrc : (M i).componentOrientation (ConnectedComponents.mk x) =
      (M i).orientation.restrictOpen A := by
    apply ManifoldOrientation.ext
    intro y
    exact (M i).componentTangentOrientation_apply (ConnectedComponents.mk x) y
  have htgt : U.componentOrientation (ConnectedComponents.mk (⟨i, x⟩ : U.Carrier)) =
      U.orientation.restrictOpen B := by
    apply ManifoldOrientation.ext
    intro y
    exact U.componentTangentOrientation_apply (ConnectedComponents.mk (⟨i, x⟩ : U.Carrier)) y
  change F.preservesOrientation ((M i).componentOrientation (ConnectedComponents.mk x))
    (U.componentOrientation (ConnectedComponents.mk (⟨i, x⟩ : U.Carrier)))
  rw [hsrc, htgt]
  have hF₀ := sigmaComponentDiffeomorph_preservesOrientation
    (I := 𝓡 3) (fun j => (M j).Carrier) (by simp)
    (fun j => (M j).orientation) i x
  have htransport : ∀ (A' : TopologicalSpace.Opens (M i).Carrier)
      (B' : TopologicalSpace.Opens U.Carrier)
      (ha : A' = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3) x)
      (hb : B' = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3)
        (⟨i, x⟩ : U.Carrier)),
      (ha.symm ▸ (hb.symm ▸ F₀) : Diffeomorph (𝓡 3) (𝓡 3) A' B' ∞).preservesOrientation
        ((M i).orientation.restrictOpen A') (U.orientation.restrictOpen B') := by
    intro A' B' ha hb
    subst A'
    subst B'
    exact hF₀
  exact htransport A B hA hB

theorem closedOrientedUnionComponent_apply (i : ι) (x : (M i).Carrier)
    (y : ((M i).component (ConnectedComponents.mk x)).Carrier) :
    ((closedOrientedUnionComponent M i x).val y).val =
      (⟨i, y.val⟩ : (closedOrientedUnion M).Carrier) := by
  unfold closedOrientedUnionComponent
  dsimp only
  have htransport : ∀ (A : TopologicalSpace.Opens (M i).Carrier)
      (B : TopologicalSpace.Opens (closedOrientedUnion M).Carrier)
      (ha : A = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3) x)
      (hb : B = DifferentialGeometry.connectedComponentOpen (I := 𝓡 3)
        (⟨i, x⟩ : (closedOrientedUnion M).Carrier)) (y : A),
      ((ha.symm ▸ (hb.symm ▸ sigmaComponentDiffeomorph (I := 𝓡 3)
        (fun j => (M j).Carrier) i x) : Diffeomorph (𝓡 3) (𝓡 3) A B ∞) y).val =
          (⟨i, y.val⟩ : (closedOrientedUnion M).Carrier) := by
    intro A B ha hb y
    subst A
    subst B
    rfl
  exact htransport _ _
    (TopologicalSpace.Opens.ext ((M i).componentSet_mk x))
    (TopologicalSpace.Opens.ext ((closedOrientedUnion M).componentSet_mk
      (⟨i, x⟩ : (closedOrientedUnion M).Carrier))) y

end DifferentialGeometry.Topology
