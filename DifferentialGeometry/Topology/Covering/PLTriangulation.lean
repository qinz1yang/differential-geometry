/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringTriangulation
import Mathlib.Data.Set.Card

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type u} [TopologicalSpace X]
  (K : Geometry.SimplicialComplex ℝ E) (p : X → K.space)
  [Finite (coveringVertex K p)]

open Classical in
theorem coveringBaseMap_mapsTo :
    MapsTo (coveringBaseMap K p) (coveringComplex K p).space K.space := by
  apply simplicialMap_mapsTo
  intro q hq
  obtain ⟨s, hs, rfl⟩ := (mem_coveringComplex_faces_iff K p).mp hq
  rw [coveringBaseVertex_image]
  exact (Classical.choice hs).face

open Classical in
theorem isPiecewiseAffineOn_coveringBaseMap :
    IsPiecewiseAffineOn (coveringBaseMap K p) (coveringComplex K p).space := by
  let _ : Finite (coveringComplex K p).faces :=
    (coveringComplex_faces_finite K p).to_subtype
  exact isPiecewiseAffineOn_simplicialMap (coveringComplex K p) (coveringBaseVertex K p)

variable [FiniteDimensional ℝ E]

open Classical in
theorem coveringBaseMap_restrict_eq (hp : IsCoveringMap p) :
    (coveringBaseMap_mapsTo K p).restrict (coveringBaseMap K p)
        (coveringComplex K p).space K.space =
      p ∘ coveringSpaceHomeomorph K p hp := by
  funext x
  apply Subtype.ext
  exact (coveringSpaceMap_projection K p x).symm

open Classical in
theorem isCoveringMap_coveringBaseMap_restrict (hp : IsCoveringMap p) :
    IsCoveringMap ((coveringBaseMap_mapsTo K p).restrict (coveringBaseMap K p)
      (coveringComplex K p).space K.space) := by
  rw [coveringBaseMap_restrict_eq K p hp]
  exact hp.comp_homeomorph (coveringSpaceHomeomorph K p hp)

open Classical in
theorem encard_preimage_coveringBaseMap_restrict (hp : IsCoveringMap p) (y : K.space) :
    (((coveringBaseMap_mapsTo K p).restrict (coveringBaseMap K p)
      (coveringComplex K p).space K.space) ⁻¹' {y}).encard = (p ⁻¹' {y}).encard := by
  rw [coveringBaseMap_restrict_eq K p hp, preimage_comp]
  exact encard_preimage_of_bijective (coveringSpaceHomeomorph K p hp).bijective _

open Classical in
theorem isPreconnected_coveringComplex_space [PreconnectedSpace X] (hp : IsCoveringMap p) :
    IsPreconnected (coveringComplex K p).space := by
  let e := coveringSpaceHomeomorph K p hp
  exact isPreconnected_iff_preconnectedSpace.mpr
    (e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous)

omit [Finite (coveringVertex K p)] in
open Classical in
theorem exists_isPiecewiseAffineOn_coveringMap [Finite K.faces]
    (hp : IsCoveringMap p) (hfin : ∀ y, (p ⁻¹' {y}).Finite) :
    ∃ (N : ℕ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (e : L.space ≃ₜ X) (q : EuclideanSpace ℝ (Fin N) → E)
      (hmap : MapsTo q L.space K.space),
      L.faces.Finite ∧ IsPiecewiseAffineOn q L.space ∧
      IsCoveringMap (hmap.restrict q L.space K.space) ∧
      (∀ x, hmap.restrict q L.space K.space x = p (e x)) ∧
      (∀ y, ((hmap.restrict q L.space K.space) ⁻¹' {y}).encard = (p ⁻¹' {y}).encard) ∧
      (PreconnectedSpace X → IsPreconnected L.space) ∧
      (∀ n, IsCombinatorialManifoldWithBoundary n K →
        IsCombinatorialManifoldWithBoundary n L) := by
  let _ : Finite (coveringVertex K p) := coveringVertex.finite K hfin
  refine ⟨Nat.card (coveringVertex K p), coveringComplex K p,
    coveringSpaceHomeomorph K p hp, coveringBaseMap K p, coveringBaseMap_mapsTo K p,
    coveringComplex_faces_finite K p, isPiecewiseAffineOn_coveringBaseMap K p,
    isCoveringMap_coveringBaseMap_restrict K p hp, ?_,
    encard_preimage_coveringBaseMap_restrict K p hp, ?_, ?_⟩
  · intro x
    exact congrFun (coveringBaseMap_restrict_eq K p hp) x
  · intro hconn
    let _ : PreconnectedSpace X := hconn
    exact isPreconnected_coveringComplex_space K p hp
  · intro n hK
    exact isCombinatorialManifoldWithBoundary_coveringComplex K p hp hK

end DifferentialGeometry.Topology.PiecewiseLinear
