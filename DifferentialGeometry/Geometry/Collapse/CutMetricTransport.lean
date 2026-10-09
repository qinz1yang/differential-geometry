import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem contMDiff_cutPieceMap {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    ContMDiff (D.component i).model (𝓡 3) ∞ (cutPieceMap D i) := by
  let := D.reconstructionAtlas.charts
  let := D.reconstructionAtlas.smooth
  have hsub : ContMDiff D.carrier.model D.carrier.model ∞
      (Subtype.val : D.components.piece i → D.carrier.Carrier) :=
    contMDiff_subtype_val
  exact D.reconstruction.val.contMDiff.comp
    (D.reconstructionAtlas.quotient_smooth.comp hsub)

theorem injOn_cutPieceMap_interior {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    Set.InjOn (cutPieceMap D i) ((D.component i).interior : Set (D.component i).Carrier) := by
  intro x hx y hy hxy
  apply Subtype.ext
  exact D.boundary.interior_fiber_singleton
    (D.carrier.model.isInteriorPoint_iff_isInteriorPoint_val.mp hx)
    (D.reconstruction.val.injective hxy)

theorem isLocalDiffeomorph_cutPieceMap_interior
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    IsLocalDiffeomorph (D.component i).model (𝓡 3) ∞
      (fun x : (D.component i).interior => cutPieceMap D i x.val) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) D.boundary.Assembled :=
    D.reconstructionAtlas.charts
  let : IsManifold (𝓡 3) ∞ D.boundary.Assembled := D.reconstructionAtlas.smooth
  let U : TopologicalSpace.Opens (D.components.piece i) := (D.component i).interior
  have hmem (x : U) : x.val.val ∈ D.carrier.interior :=
    D.carrier.model.isInteriorPoint_iff_isInteriorPoint_val.mp x.property
  let f : U → D.carrier.interior := fun x => ⟨x.val.val, hmem x⟩
  have hval : IsLocalDiffeomorph D.carrier.model D.carrier.model ∞
      (fun x : U => x.val.val) :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_subtype_val (I := D.carrier.model) (D.components.piece i))
      (isLocalDiffeomorph_subtype_val (I := D.carrier.model) U)
  have hf : IsLocalDiffeomorph D.carrier.model D.carrier.model ∞ f :=
    fun x => isLocalDiffeomorphAt_subtypeCodRestrict hmem (hval x)
  have htargetVal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : D.reconstructionAtlas.interiorImage → D.boundary.Assembled) :=
    isLocalDiffeomorph_subtype_val (I := 𝓡 3) D.reconstructionAtlas.interiorImage
  have hinterior : IsLocalDiffeomorph D.carrier.model (𝓡 3) ∞
      (fun x : U => (D.reconstructionAtlas.interiorDiffeomorph (f x)).val) :=
    isLocalDiffeomorph_comp htargetVal
      (isLocalDiffeomorph_comp D.reconstructionAtlas.interiorDiffeomorph.isLocalDiffeomorph hf)
  have hmap : IsLocalDiffeomorph D.carrier.model (𝓡 3) ∞
      (fun x : U => D.reconstruction.val
        (D.reconstructionAtlas.interiorDiffeomorph (f x)).val) := by
    have hreconstruction : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (D.reconstruction.val : D.boundary.Assembled → M.Carrier) :=
      D.reconstruction.val.isLocalDiffeomorph
    exact isLocalDiffeomorph_comp (I := D.carrier.model) (J := 𝓡 3) (K := 𝓡 3)
      (M := U) (N := D.boundary.Assembled) (P := M.Carrier) hreconstruction hinterior
  have heq : (fun x : U => D.reconstruction.val
      (D.reconstructionAtlas.interiorDiffeomorph (f x)).val) =
      fun x : U => cutPieceMap D i x.val := by
    funext x
    rw [D.reconstructionAtlas.interior_map]
    rfl
  rw [heq] at hmap
  exact hmap

theorem curvatureDerivativeNorm_cutPieceMap
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (k : ℕ) (x : (D.component i).Carrier)
    (hx : (D.component i).model.IsInteriorPoint x) :
    curvatureDerivativeNorm h k x =
      curvatureDerivativeNorm g k (cutPieceMap D i x) := by
  let U := (D.component i).interior
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (D.component i).model U.isOpen)
  have hinj : Function.Injective (fun y : U => cutPieceMap D i y.val) := by
    intro y z hyz
    exact Subtype.ext (injOn_cutPieceMap_interior D i y.property z.property hyz)
  have hmetric (y : U) (v w : TangentSpace (D.component i).model y) :
      (h.restrictOpen U).inner y v w = g.inner (cutPieceMap D i y.val)
        (mfderiv (D.component i).model (𝓡 3) (fun z : U => cutPieceMap D i z.val) y v)
        (mfderiv (D.component i).model (𝓡 3) (fun z : U => cutPieceMap D i z.val) y w) := by
    rw [mfderiv_restrict_open, SmoothRiemannianMetric.restrictOpen_inner]
    exact hinduced y.val v w
  have hnorm := curvatureDerivativeNorm_of_injective_local_isometry
    (h.restrictOpen U) g (fun y : U => cutPieceMap D i y.val)
    (isLocalDiffeomorph_cutPieceMap_interior D i) hinj hmetric k ⟨x, hx⟩
  exact (curvatureDerivativeNorm_restrictOpen h U k ⟨x, hx⟩).symm.trans hnorm

end DifferentialGeometry.Geometry.Collapse
