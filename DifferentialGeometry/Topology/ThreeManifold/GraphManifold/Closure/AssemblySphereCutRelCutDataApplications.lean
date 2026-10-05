import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelCutDataLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelCutDataBoundary

/-!
# Consumer of the shared cut data: the shrunk ports of `W` inside a drilled piece

`SphereCutCapped.exists_shrinkPortLifts`: for a sphere-cut-capped carrier `X` of `W`, a recorded
shrink `E.shrink δ` of its ports exhausts `∂W` (`boundary_eq_image`, `BoundaryTori.shrink_image`),
and if the shrunk collar targets lie in the range of an injective piece, every shrunk port lifts to
a half collar of that piece over it (`PieceFold.exists_halfCollarLift_of_injective`). These are the
`external_exhausted`, `externalLift`, `externalLift_source` and `externalLift_eq` fields of a
`RegularCutData W (E.shrink δ)` whose ports are all owned by one piece.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}

/-- **The shrunk ports of `W` and their lifts into one injective piece.** -/
theorem exists_shrinkPortLifts (X : SphereCutCapped W S E) (P : PieceFold W)
    (hinj : Injective P.map) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrange : ∀ i, ((E.shrink hδ hδ1).collar i).target ⊆ range P.map) :
    W.model.boundary W.Carrier = (E.shrink hδ hδ1).image ∧
      ∃ ℓ : Fin n → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
        (Torus × EuclideanHalfSpace 1) P.Piece ∞,
        (∀ i, (ℓ i).source = halfCollarSource) ∧
        ∀ i p, p ∈ halfCollarSource → P.map (ℓ i p) = (E.shrink hδ hδ1).collar i p := by
  refine ⟨by rw [BoundaryTori.shrink_image]; exact X.boundary_eq_image, ?_⟩
  have h := fun i => P.exists_halfCollarLift_of_injective hinj ((E.shrink hδ hδ1).collar i)
    ((E.shrink hδ hδ1).source_eq i) (hrange i)
  choose ℓ hs _ hv using h
  exact ⟨ℓ, hs, hv⟩

end SphereCutCapped

end GC.GraphManifold.Assembly
