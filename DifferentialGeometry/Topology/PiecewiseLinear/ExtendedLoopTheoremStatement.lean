/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Contractible

/-!
# The orientable extended loop theorem

`Moise264Orientable` is the orientable case of the extended loop theorem for finite
triangulated three-manifolds. Two-sidedness is measured in the ambient manifold subtype,
as in Moise Section 26.4, rather than in its auxiliary vector space realization. The older
`Moise264` uses vector-space two-sidedness and has no orientability hypothesis; that named
input remains open. No implication between these two formulations is asserted here.

The existing essential-disk theorem for surfaces in open subsets of three-dimensional
Euclidean space is a separate local result. This statement neither replaces it nor supplies
the triangulation and ambient-neighborhood bridges needed by particular applications.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
def Moise264Orientable : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (_ : Finite K.faces),
    IsCombinatorialManifoldWithBoundary 3 K → IsOrientable 3 K →
    ∀ (L : Geometry.SimplicialComplex ℝ E) (_ : Finite L.faces),
      IsCombinatorialManifold 2 L →
    ∀ hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space,
      IsTwoSided (((↑) : K.space → E) ⁻¹' L.space) →
    ∀ (x : L.space) (g : FundamentalGroup L.space x),
      g ≠ 1 →
      FundamentalGroup.map
        (⟨Set.inclusion (hLK.trans sdiff_subset), continuous_inclusion _⟩ :
          C(L.space, K.space)) x g = 1 →
      ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
        Δ ∩ L.space = r '' stdSimplexBoundary 2 ∧
        ∃ hb : r '' stdSimplexBoundary 2 ⊆ L.space,
          ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
            C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic

end DifferentialGeometry.Topology.PiecewiseLinear
