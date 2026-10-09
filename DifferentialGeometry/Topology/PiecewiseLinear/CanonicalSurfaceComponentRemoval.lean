/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalSurface.of_component_complement [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (hX : IsCanonicalSurface X S' T I P' a b)
    (i : ℤ) (c : ConnectedComponents (X i).space)
    (R : Geometry.SimplicialComplex ℝ E3) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRo : IsOrientable 2 R)
    (hRspace : R.space = (X i).space \ (connectedComponentComplex (X i) c).space)
    (hRb : (boundaryComplex 2 R).space =
      (boundaryComplex 2 (X i)).space \ (connectedComponentComplex (X i) c).space)
    (hsep : IsSeparatorIn I (towerSurface T (fun j => (Function.update X i R j).space) P')
      {a} {b}) : IsCanonicalSurface (Function.update X i R) S' T I P' a b := by
  classical
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let _ : Finite (connectedComponentComplex (X i) c).faces :=
    (connectedComponentComplex_faces_finite (X i) c).to_subtype
  let Y := Function.update X i R
  let Z := (connectedComponentComplex (X i) c).space
  have hZX : Z ⊆ (X i).space :=
    (subset_iUnion (fun q => (connectedComponentComplex (X i) q).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hcover : R.space ∪ Z = (X i).space := by
    rw [hRspace]
    exact sdiff_union_of_subset hZX
  have hdis : Disjoint R.space Z := by
    rw [hRspace]
    exact disjoint_sdiff_left
  have htrace (V : Set E3) (hk : HasFiniteCollaredTrace (X i).space V) :
      HasFiniteCollaredTrace R.space V :=
    (hcover.symm ▸ hk).of_disjoint_union_left (isPolyhedron_space R)
      (isPolyhedron_space (connectedComponentComplex (X i) c)).isClosed hdis
  have htraceSub (V : Set E3) (hk : HasFiniteCollaredTrace (X i).space V) :
      traceCircles R.space V ⊆ traceCircles (X i).space V :=
    traceCircles_subset_of_inter_subset hk.traceCover
      (inter_subset_inter_left V (hRspace.subset.trans sdiff_subset))
  have hbasic : ∀ j, ∃ hf : (Y j).faces.Finite,
      IsCombinatorialManifoldWithBoundary 2 (Y j) ∧
        letI := hf.to_subtype; IsOrientable 2 (Y j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Y, Function.update_self]
      exact ⟨Set.toFinite _, hR, hRo⟩
    · simp only [Y, Function.update_of_ne hji]
      exact ⟨hX.finiteFaces j, hX.manifold j, hX.orientable j⟩
  have hsub : ∀ j, (Y j).space ⊆ (X j).space := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using hRspace.subset.trans sdiff_subset
    · simpa only [Y, Function.update_of_ne hji] using
        (Subset.rfl : (X j).space ⊆ (X j).space)
  have hboundary : (boundaryComplex 2 R).space =
      R.space ∩ (T (2 * i) ∪ T (2 * (i + 1))) := by
    rw [hRb, hRspace, hX.boundary i]
    ext x
    exact ⟨fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩,
      fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩⟩
  refine
    { finiteFaces := fun j => (hbasic j).choose
      manifold := fun j => (hbasic j).choose_spec.1
      orientable := fun j => (hbasic j).choose_spec.2
      interiorCarrier := fun j => (hsub j).trans (hX.interiorCarrier j)
      piecesDisjoint := fun j k hjk => (hX.piecesDisjoint hjk).mono (hsub j) (hsub k)
      boundary := ?_
      lowerTrace := ?_
      upperTrace := ?_
      lowerOrigin := ?_
      upperOrigin := ?_
      centerNotMem := fun j hx => hX.centerNotMem j (hsub j hx)
      subsetInterior := ?_
      separator := hsep }
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using hboundary
    · simpa only [Y, Function.update_of_ne hji] using hX.boundary j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using htrace (T (2 * i)) (hX.lowerTrace i)
    · simpa only [Y, Function.update_of_ne hji] using hX.lowerTrace j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using htrace (T (2 * (i + 1))) (hX.upperTrace i)
    · simpa only [Y, Function.update_of_ne hji] using hX.upperTrace j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using
        (htraceSub (T (2 * i)) (hX.lowerTrace i)).trans (hX.lowerOrigin i)
    · simpa only [Y, Function.update_of_ne hji] using hX.lowerOrigin j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using
        (htraceSub (T (2 * (i + 1))) (hX.upperTrace i)).trans (hX.upperOrigin i)
    · simpa only [Y, Function.update_of_ne hji] using hX.upperOrigin j
  · intro x hx
    apply hX.subsetInterior
    rcases hx with hx | hxP
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Or.inl (mem_iUnion.mpr ⟨j, hj.imp id (fun hy => hsub j hy)⟩)
    · exact Or.inr hxP

end DifferentialGeometry.Topology.PiecewiseLinear
