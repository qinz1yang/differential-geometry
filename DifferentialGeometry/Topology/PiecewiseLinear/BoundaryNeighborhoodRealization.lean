/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem NormalSystem.exists_boundaryNeighborhood_realization
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 S.manifoldComplex)
      (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    let ι := simplicialMap S.manifoldComplex
      (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 S.manifoldComplex) id)
    let B := ((↑) : (double 3 S.manifoldComplex).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∀ {D : SingularTwoCell (double 3 S.manifoldComplex).space},
      Set.range D.boundary ⊆ B →
      ∃ (ρ : S.boundaryNeighborhoodSpace → (double 3 S.manifoldComplex).space)
        (f : frontier D.domain → S.boundaryNeighborhoodSpace),
        IsEmbedding ρ ∧ B ⊆ Set.range ρ ∧ Continuous f ∧
          (∀ y : S.boundaryNeighborhoodSpace,
            ((ρ y : (double 3 S.manifoldComplex).space) : E × E × ℝ) = ι (y : E)) ∧
          ∀ z : frontier D.domain, ρ (f z) = D z := by
  intro ι B D hD
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (double 3 K).space :=
    combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let Bc := normalSystemBoundaryComplex S.neighborhood
  let A := glued₂ K Bc id
  let L := double 3 K
  have hBK_faces : Bc.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hBK_space : Bc.space ⊆ K.space := space_mono_of_faces_subset hBK_faces
  have hNK_space : S.boundaryNeighborhood.space ⊆ K.space :=
    (derivedNeighborhood_space_subset Bc S.loopComplex).trans hBK_space
  have hι : IsPLHomeomorphOn ι K.space A.space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ Bc id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hAL : A.space ⊆ L.space := by
    dsimp only [L, double]
    rw [gluedComplex_space]
    exact subset_union_right
  have hρ_maps : ∀ y : S.boundaryNeighborhoodSpace, ι (y : E) ∈ L.space :=
    fun y => hAL (hι.1.mapsTo (hNK_space y.2))
  let ρ : S.boundaryNeighborhoodSpace → L.space := fun y => ⟨ι (y : E), hρ_maps y⟩
  have hι_cont : Continuous (fun y : S.boundaryNeighborhoodSpace => ι (y : E)) :=
    hι.2.1.continuousOn.comp_continuous continuous_subtype_val (fun y => hNK_space y.2)
  have hρ_cont : Continuous ρ := hι_cont.codRestrict (fun y => hρ_maps y)
  have hρ_inj : Function.Injective ρ := by
    intro y₁ y₂ h
    have hval : ι (y₁ : E) = ι (y₂ : E) := congrArg Subtype.val h
    exact Subtype.ext (hι.1.injOn (hNK_space y₁.2) (hNK_space y₂.2) hval)
  have hBfaces : Bc.faces.Finite := S.manifoldComplex_faces_finite.subset hBK_faces
  have _ : Finite Bc.faces := hBfaces.to_subtype
  have hNfaces : S.boundaryNeighborhood.faces.Finite :=
    derivedNeighborhood_faces_finite Bc S.loopComplex
  have _ : Finite S.boundaryNeighborhood.faces := hNfaces.to_subtype
  have hNpoly : IsPolyhedron S.boundaryNeighborhood.space :=
    isPolyhedron_space S.boundaryNeighborhood
  have _ : CompactSpace S.boundaryNeighborhoodSpace :=
    isCompact_iff_compactSpace.mp hNpoly.isCompact
  have hclosed : IsClosedEmbedding ρ := hρ_cont.isClosedEmbedding hρ_inj
  have hemb : IsEmbedding ρ := hclosed.isEmbedding
  have hB_sub : B ⊆ Set.range ρ := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := hp
    refine ⟨⟨x, hx⟩, Subtype.ext hpx⟩
  let f : frontier D.domain → S.boundaryNeighborhoodSpace := fun z =>
    Classical.choose (Set.mem_range.mp (hB_sub (hD ⟨z, rfl⟩)))
  have hfz : ∀ z : frontier D.domain, ρ (f z) = D z := fun z =>
    (Classical.choose_spec (Set.mem_range.mp (hB_sub (hD ⟨z, rfl⟩)))).trans (D.boundary_apply z)
  have hf_cont : Continuous f := by
    rw [hemb.isInducing.continuous_iff]
    rw [show ρ ∘ f = ⇑D.boundary from
      funext fun z => Classical.choose_spec (Set.mem_range.mp (hB_sub (hD ⟨z, rfl⟩)))]
    exact D.boundary.continuous
  refine ⟨ρ, f, hemb, hB_sub, hf_cont, fun _ => rfl, hfz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
