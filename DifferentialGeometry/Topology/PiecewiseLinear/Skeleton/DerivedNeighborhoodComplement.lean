/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.CompactEmbeddingComplement
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRay
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

/-!
# A producer skeleton for the interior complement of a derived neighborhood

The frozen endpoint is `section33_tube_product`. Its image transport is proved by
`nonempty_homeomorph_interior_sdiff_image_of_isCompact`; only continuity and injectivity on
the compact tube are used. The ambient function need not be continuous outside the tube.

The two leaves concern the same explicit map `derivedNeighborhoodRay A K`: a frontier point
`b` at time `t` is sent to `(1 - t) * b + t * p(b)`, where `p` is the existing normalized
subcomplex barycentric projection on the first barycentric subdivision. Both leaves are
owned by the regular-neighborhood lane:
* `isEmbedding_derivedNeighborhoodRay`: unique boundary rays and continuity of their inverse;
  UNREVIEWED.
* `range_derivedNeighborhoodRay`: the image is exactly the interior with the core removed;
  UNREVIEWED.

The map and its continuity are proved in `DerivedNeighborhoodRay.lean`. The existing strong
deformation retract proves preservation of the closed derived neighborhood; it does not prove
either open ray leaf. Fundamental-group equivalences do not supply a product homeomorphism.
`NeighborhoodCylinder` only handles a connected one-dimensional manifold, not an arbitrary
graph, and does not pin its coordinates to this specified core.

The finite-simplex geometry is the maximum-weight condition in
`mem_faceNeighborhood_space_iff`, not a constant total-core-mass level. On a first-derived
simplex write `m` for total core weight and `a`, `b` for maximal core and noncore weights.
For an interior point outside the core the proposed ray parameter is `t = m * (1 - b / a)`;
its boundary point is `(x - t * p(x)) / (1 - t)`. The open obligations must justify strict
versus non-strict weight inequalities using the ambient frontier, and glue these inverses
across faces. The formula is a proof route, not a proved global coordinate theorem.

The core must lie in the ambient interior. In the assembly this follows from the frozen
`IsTube.isNeighborhood`, the equality with the derived neighborhood supplied by the very same
`derivedModel`, and `derivedNeighborhood_space_subset`. No connectedness, purity or absence of
endpoints is added. The leaves allow arbitrary subcomplexes, hence isolated vertices and
nonpure graphs as well. A boundary vertex in a tetrahedron is a geometric warning against
dropping the interior hypothesis: its derived neighborhood has the core on its frontier.
This boundary example has not been formalized and is not a counterexample to `IsTube`.

Joint fixture: UNTESTED. An interior triangular polygon together with an isolated interior
vertex in a sufficiently subdivided three-ball is a proposed instance covering a nonpure,
disconnected graph. The simultaneous triangulation, derived neighborhood, and full `IsTube`
witness have not been formalized. No joint satisfiability certificate is claimed.

The endpoint assembly has no direct `sorry`; its transitive closure contains the two open
leaves. These leaves need external review and real proofs before the frozen input can close.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance euclideanDecidableEq : DecidableEq E3 :=
  fun a b => Classical.propDecidable (a = b)

open Classical in
theorem isEmbedding_derivedNeighborhoodRay (A K : Geometry.SimplicialComplex ℝ E3)
    [Finite A.faces] (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hKA : K.faces ⊆ A.faces) (hKint : K.space ⊆ interior A.space) :
    _root_.Topology.IsEmbedding (derivedNeighborhoodRay A K) := by
  sorry

open Classical in
theorem range_derivedNeighborhoodRay (A K : Geometry.SimplicialComplex ℝ E3)
    [Finite A.faces] (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hKA : K.faces ⊆ A.faces) (hKint : K.space ⊆ interior A.space) :
    Set.range (derivedNeighborhoodRay A K) =
      interior (derivedNeighborhood A K).space \ K.space := by
  sorry

open Classical in
theorem nonempty_homeomorph_derivedNeighborhood_interior_sdiff
    (A K : Geometry.SimplicialComplex ℝ E3) [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hKA : K.faces ⊆ A.faces) (hKint : K.space ⊆ interior A.space) :
    Nonempty ((frontier (derivedNeighborhood A K).space × Set.Ioo (0 : ℝ) 1) ≃ₜ
      ↥(interior (derivedNeighborhood A K).space \ K.space)) := by
  have hemb := isEmbedding_derivedNeighborhoodRay A K hA hKA hKint
  have hrange := range_derivedNeighborhoodRay A K hA hKA hKint
  let e := hemb.toHomeomorph
  let e' := Homeomorph.setCongr hrange
  exact ⟨e.trans e'⟩

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem section33_tube_product (ht : IsTube K N C D Dbd h N') :
    Nonempty ((frontier N × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N' \ h '' K.space)) := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, hA, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  have hKN : K.space ⊆ interior N := subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood
  have hNA : N ⊆ A.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset A K
  have hKint : K.space ⊆ interior A.space := hKN.trans (interior_mono hNA)
  have hprod : Nonempty ((frontier N × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N \ K.space)) := by
    rw [hN]
    exact nonempty_homeomorph_derivedNeighborhood_interior_sdiff A K hA hKA hKint
  have hcompact : IsCompact N := by
    rw [hN]
    let _ : Finite (derivedNeighborhood A K).faces :=
      (derivedNeighborhood_faces_finite A K).to_subtype
    exact SimplicialComplex.isCompact_geometricSpace (derivedNeighborhood A K)
  obtain ⟨e⟩ := hprod
  obtain ⟨e'⟩ := nonempty_homeomorph_interior_sdiff_image_of_isCompact hcompact
    (hKN.trans interior_subset)
    (continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous)
    (injOn_iff_injective.mpr ht.isEmbedding.injective)
  rw [ht.imageEq]
  exact ⟨e.trans e'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
