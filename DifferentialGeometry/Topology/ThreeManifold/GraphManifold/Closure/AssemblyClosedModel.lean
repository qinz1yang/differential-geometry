import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

/-!
# Chapter-14 assembly, bridge B0: a carrier with empty boundary is a closed oriented manifold

For a connected carrier `W` (either model kind) with `W.model.boundary W.Carrier = ∅`, the identity
rechart `interiorChartedSpace W.model ∞` on the same underlying space is a closed smooth `𝓡 3`
manifold, the identity is a diffeomorphism `W.model → 𝓡 3` (`interiorAtlasDiffeomorph`), and the
orientation of `W` pulled back along its inverse makes it orientation preserving. This is the
pattern of `Closure/SphereCapClosed.lean:78–165`, for an arbitrary carrier. It is not a proof that
`W.kind = closed`.

* `boundaryEmptyClosedModel`, `boundaryEmptyDiffeomorph`: the closed model and the diffeomorphism;
* `exists_closedModel_of_boundary_eq_empty`: B0, the frozen statement of the assembly design
  (`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §4 row §2).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable (W : CompactCarrier.{u}) (h : W.model.boundary W.Carrier = ∅)

/-- The identity rechart of a carrier with empty boundary onto the boundaryless model `𝓡 3`. -/
@[reducible]
def boundaryEmptyChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) W.Carrier :=
  haveI : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty h
  DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞

theorem boundaryEmptyIsManifold :
    letI := boundaryEmptyChartedSpace W h
    IsManifold (𝓡 3) ∞ W.Carrier := by
  have : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty h
  exact DifferentialGeometry.Manifold.interiorIsManifold W.model ∞

/-- The identity map, from the carrier structure to the boundaryless rechart. -/
def boundaryEmptyDiffeomorph :
    letI := boundaryEmptyChartedSpace W h
    W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ W.Carrier := by
  haveI : BoundarylessManifold W.model W.Carrier :=
    ModelWithCorners.Boundaryless.of_boundary_eq_empty h
  exact DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞

theorem boundaryEmptyDiffeomorph_apply (x : W.Carrier) :
    boundaryEmptyDiffeomorph W h x = x := rfl

theorem boundaryEmptyDiffeomorph_symm_apply (x : W.Carrier) :
    letI := boundaryEmptyChartedSpace W h
    (boundaryEmptyDiffeomorph W h).symm x = x := rfl

/-- The orientation of `W`, pulled back to the boundaryless rechart along the identity. -/
def boundaryEmptyOrientation :
    letI := boundaryEmptyChartedSpace W h
    haveI := boundaryEmptyIsManifold W h
    ManifoldOrientation (𝓡 3) W.Carrier 3 :=
  letI := boundaryEmptyChartedSpace W h
  haveI := boundaryEmptyIsManifold W h
  DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback (𝓡 3) W.model
    finrank_euclideanSpace_fin (boundaryEmptyDiffeomorph W h).symm
    (boundaryEmptyDiffeomorph W h).symm.contMDiff
    (fun x => ((boundaryEmptyDiffeomorph W h).symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective) W.orientation

theorem boundaryEmptyDiffeomorph_symm_preservesOrientation :
    letI := boundaryEmptyChartedSpace W h
    haveI := boundaryEmptyIsManifold W h
    (boundaryEmptyDiffeomorph W h).symm.preservesOrientation (boundaryEmptyOrientation W h)
      W.orientation := by
  let _ := boundaryEmptyChartedSpace W h
  have _ := boundaryEmptyIsManifold W h
  intro x
  have hx := DifferentialGeometry.Topology.Manifold.orientation_map_manifoldOrientationPullback
    (𝓡 3) W.model finrank_euclideanSpace_fin (boundaryEmptyDiffeomorph W h).symm
    (boundaryEmptyDiffeomorph W h).symm.contMDiff
    (fun x => ((boundaryEmptyDiffeomorph W h).symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective) W.orientation x
  refine Eq.trans ?_ hx
  exact congrArg (fun L => Orientation.map (Fin 3) L ((boundaryEmptyOrientation W h).orientation x))
    (LinearEquiv.ext fun v => rfl)

/-- The closed oriented model of a connected carrier with empty boundary: the same space with the
identity rechart and the pulled-back orientation. -/
def boundaryEmptyClosedModel [ConnectedSpace W.Carrier] : ConnectedClosedOrientedManifold.{u} 3 :=
  letI := boundaryEmptyChartedSpace W h
  { Carrier := W.Carrier
    smooth := boundaryEmptyIsManifold W h
    orientation := boundaryEmptyOrientation W h }

/-- The identity diffeomorphism onto the closed model. -/
def boundaryEmptyClosedDiffeomorph [ConnectedSpace W.Carrier] :
    W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ (boundaryEmptyClosedModel W h).Carrier :=
  boundaryEmptyDiffeomorph W h

theorem boundaryEmptyClosedDiffeomorph_apply [ConnectedSpace W.Carrier] (x : W.Carrier) :
    boundaryEmptyClosedDiffeomorph W h x = x := rfl

theorem boundaryEmptyClosedDiffeomorph_preservesOrientation [ConnectedSpace W.Carrier] :
    (boundaryEmptyClosedDiffeomorph W h).preservesOrientation W.orientation
      (boundaryEmptyClosedModel W h).orientation := by
  let _ := boundaryEmptyChartedSpace W h
  have _ := boundaryEmptyIsManifold W h
  change (boundaryEmptyDiffeomorph W h).preservesOrientation W.orientation
    (boundaryEmptyOrientation W h)
  have h' := Diffeomorph.preservesOrientation_symm
    (boundaryEmptyDiffeomorph_symm_preservesOrientation W h)
  have he : (boundaryEmptyDiffeomorph W h).symm.symm = boundaryEmptyDiffeomorph W h := by
    ext x
    rfl
  rw [he] at h'
  exact h'

/-- **B0 (empty-boundary model change).** Pattern: `Closure/SphereCapClosed.lean:77–165`. -/
theorem exists_closedModel_of_boundary_eq_empty (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (h : W.model.boundary W.Carrier = ∅) :
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3) (e : W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ Q.Carrier),
      e.preservesOrientation W.orientation Q.orientation :=
  ⟨boundaryEmptyClosedModel W h, boundaryEmptyClosedDiffeomorph W h,
    boundaryEmptyClosedDiffeomorph_preservesOrientation W h⟩

end GC.GraphManifold.Assembly
