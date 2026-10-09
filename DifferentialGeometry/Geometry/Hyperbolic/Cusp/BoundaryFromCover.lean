/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.CoverAssembly
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

variable {H : FiniteVolumeHyperbolicModel}

theorem boundary_incompressible_of_curvature_identity (Tr : HyperbolicTruncation H)
    (hsec : ∀ (x : H.Carrier) (X Y : TangentSpace (𝓡 3) x),
      Geometry.Curvature.metricRm04StandardAt H.metric x X Y Y X =
        -(1 / 4 : ℝ) * (H.metric.inner x X X * H.metric.inner x Y Y -
          H.metric.inner x X Y * H.metric.inner x X Y)) :
    Tr.boundary.incompressible := by
  apply Tr.boundary_incompressible_of_slice_injective (fun _ => halfSpaceOneLift 1)
  intro i x
  obtain ⟨q, P, hq, hqs, hP, hcomm⟩ :=
    exists_native_cover_square_of_curvature_identity Tr i hsec 1 (by norm_num)
  exact Tr.slice_injective_of_covering_square i (halfSpaceOneLift 1)
    q P (modelSlice 1 1) hq hqs hP (hcomm 1 (by norm_num))
    (modelSlice_injective 1 1) x

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
