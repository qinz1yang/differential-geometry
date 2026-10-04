import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryCoordinates

/-!
Genuine local model coordinates for spherical half collars, signed collars and all source points.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private abbrev SphereCapE2 := EuclideanSpace ℝ (Fin 2)
private abbrev SphereCapE3 := EuclideanSpace ℝ (Fin 3)

private def sphereCapSignedLinear : (SphereCapE2 × ℝ) ≃L[ℝ] SphereCapE3 :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofFinrankEq _ _ (by simp))

private def sphereCapHalfProductDiffeomorph :
    (SphereCapE2 × EuclideanHalfSpace 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯
      EuclideanHalfSpace 3 := by
  let e := DifferentialGeometry.Manifold.modelLinearHomeomorphDiffeomorph
    ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
  refine { e.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [chartedSpaceSelf_prod]
    exact e.contMDiff
  · rw [chartedSpaceSelf_prod]
    exact e.symm.contMDiff

theorem exists_sphereCapSignedCoordinates (p : ClosureSphere.{u} × ℝ) :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel (𝓡∂ 3)
      (ClosureSphere.{u} × ℝ) (EuclideanHalfSpace 3) ∞, p ∈ d.source := by
  let a := PartialDiffeomorph.extendedChart (I := sphereSignedCollarModel) p
  let d := a.trans sphereCapSignedLinear.toDiffeomorph.toPartialDiffeomorph
  exact exists_surgeryHalfCoordinates_of_euclidean d ⟨mem_extChartAt_source p, mem_univ _⟩

theorem exists_sphereCapHalfCoordinates (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    ∃ d : PartialDiffeomorph sphereHalfCollarModel (𝓡∂ 3)
      (ClosureSphere.{u} × EuclideanHalfSpace 1) (EuclideanHalfSpace 3) ∞,
        p ∈ d.source := by
  let a := PartialDiffeomorph.extendedChart (I := 𝓡 2) p.1
  let d := (DifferentialGeometry.Topology.PartialDiffeomorph.prod a
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞).toPartialDiffeomorph).trans
      sphereCapHalfProductDiffeomorph.toPartialDiffeomorph
  exact ⟨d, ⟨mem_extChartAt_source p.1, mem_univ _⟩, mem_univ _⟩

private def sphereCapHalfChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] (x : M) :
    PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) M (EuclideanHalfSpace 3) ∞ where
  __ := chartAt (EuclideanHalfSpace 3) x
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

private theorem exists_sphereCapModelCoordinates (k : CarrierModel) {M : Type u}
    [TopologicalSpace M] [ChartedSpace k.Space M] [IsManifold k.model ∞ M] (x : M) :
    ∃ d : PartialDiffeomorph k.model (𝓡∂ 3) M (EuclideanHalfSpace 3) ∞,
      x ∈ d.source := by
  cases k with
  | closed =>
    exact exists_surgeryHalfCoordinates_of_euclidean
      (PartialDiffeomorph.extendedChart (I := 𝓡 3) x) (mem_extChartAt_source x)
  | withBoundary =>
    exact ⟨sphereCapHalfChart x, mem_chart_source (EuclideanHalfSpace 3) x⟩

theorem exists_sphereCapCarrierCoordinates (C : CompactCarrier.{u}) (x : C.Carrier) :
    ∃ d : PartialDiffeomorph C.model (𝓡∂ 3) C.Carrier (EuclideanHalfSpace 3) ∞,
      x ∈ d.source :=
  exists_sphereCapModelCoordinates C.kind x

end GC.GraphManifold
