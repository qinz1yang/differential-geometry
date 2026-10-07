/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.BoundaryFromCover

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold (halfSpaceOneLift)
open scoped Manifold

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

theorem continuousCuspMap_fundamentalGroup_injective {H : FiniteVolumeHyperbolicModel}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (p : CuspHalfSpace) :
    Function.Injective (FundamentalGroup.map (Tr.continuousCuspMap i) p) := by
  rcases p with ⟨x, r⟩
  have hsec (y : H.Carrier) (v w : TangentSpace (𝓡 3) y) :
      Geometry.Curvature.metricRm04StandardAt H.metric y v w w v =
        -(1 / 4 : ℝ) * (H.metric.inner y v v * H.metric.inner y w w -
          H.metric.inner y v w * H.metric.inner y v w) :=
    Geometry.Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) y (H.curvature y) v w
  obtain ⟨q, P, hq, hqs, hP, hcomm⟩ :=
    exists_native_cover_square_of_curvature_identity Tr i hsec 1 (by norm_num)
  have hone := Tr.slice_injective_of_covering_square i (halfSpaceOneLift 1)
    q P (modelSlice 1 1) hq hqs hP (hcomm 1 (by norm_num))
    (modelSlice_injective 1 1) x
  have hr := Tr.slice_injective_of_depth i (halfSpaceOneLift 1) r x hone
  intro a b hab
  obtain ⟨a, rfl⟩ := (cuspSlice_fundamentalGroup_bijective r x).surjective a
  obtain ⟨b, rfl⟩ := (cuspSlice_fundamentalGroup_bijective r x).surjective b
  apply congrArg (FundamentalGroup.map (cuspSlice r) x)
  apply hr
  simp only [GC.Topology.fundamentalGroup_map_comp, ContinuousMap.comp_apply,
    cuspSlice_apply]
  change FundamentalGroup.map (Tr.continuousCuspMap i) (x, r)
      (FundamentalGroup.map (cuspSlice r) x a) =
    FundamentalGroup.map (Tr.continuousCuspMap i) (x, r)
      (FundamentalGroup.map (cuspSlice r) x b)
  exact hab

theorem slice_injective {H : FiniteVolumeHyperbolicModel}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (r : EuclideanHalfSpace 1) (x : GC.Endpoint.Torus) :
    Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice r)) x) := by
  rw [GC.Topology.fundamentalGroup_map_comp]
  exact (Tr.continuousCuspMap_fundamentalGroup_injective i (x, r)).comp
    (cuspSlice_fundamentalGroup_bijective r x).injective

theorem boundary_incompressible {H : FiniteVolumeHyperbolicModel}
    (Tr : HyperbolicTruncation H) : Tr.boundary.incompressible :=
  Tr.boundary_incompressible_of_slice_injective (fun _ => GC.Endpoint.halfZero)
    (fun i x => Tr.slice_injective i GC.Endpoint.halfZero x)

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
