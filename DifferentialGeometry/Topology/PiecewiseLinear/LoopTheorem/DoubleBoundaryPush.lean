/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskPush
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.PolyhedralCell
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_nonsingular_two_cell_of_boundary_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hD : D ⊆ (boundaryComplex 3 K).space) :
    letI := combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    ∃ A : SingularTwoCell (double 3 K).space, A.IsNonsingular ∧
      Subtype.val '' (A '' A.domain) ⊆ ι '' K.space ∧
      Set.range (fun x => (A.boundary x : E × E × ℝ)) = ι '' (r '' stdSimplexBoundary 2) ∧
      Subtype.val '' (A '' A.domain) ∩ ι '' (boundaryComplex 3 K).space =
        ι '' (r '' stdSimplexBoundary 2) := by
  classical
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L := isCombinatorialManifold_double_succ_succ K hK
  let _ := combinatorialChartedSpace L hL
  let B := boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hcopy : ι '' K.space ⊆ L.space := by
    rw [hι.image_eq]
    change (glued₂ K B id).space ⊆ (double 3 K).space
    rw [double, gluedComplex_space]
    exact subset_union_right
  obtain ⟨Q, q, hq, hQK, hboundary, hinter⟩ :=
    hK.exists_isPLHomeomorphOn_push_boundary_disk hr hD
  have hqcopy := hq.trans (hι.restrict (show IsPLBall 2 Q from ⟨q, hq⟩).isPolyhedron hQK)
  obtain ⟨A, hA, hAQ, hAboundary⟩ :=
    exists_nonsingular_two_cell_of_isPLBall_in_combinatorial_manifold L hL hqcopy
      ((image_mono hQK).trans hcopy)
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · rw [hAQ]
    exact image_mono hQK
  · rw [hAboundary, image_comp, hboundary]
  · rw [hAQ, ← hι.bijOn.injOn.image_inter hQK (boundaryComplex_space_subset 3 K), hinter]

open Classical in
theorem exists_nonsingular_two_cell_of_disk_in_double_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    ∀ {D : Set (E × E × ℝ)} {r : (Fin 3 → ℝ) → E × E × ℝ},
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ ι '' (boundaryComplex 3 K).space →
      ∃ A : SingularTwoCell (double 3 K).space, A.IsNonsingular ∧
        Subtype.val '' (A '' A.domain) ⊆ ι '' K.space ∧
        Set.range (fun x => (A.boundary x : E × E × ℝ)) = r '' stdSimplexBoundary 2 ∧
        Subtype.val '' (A '' A.domain) ∩ ι '' (boundaryComplex 3 K).space =
          r '' stdSimplexBoundary 2 := by
  classical
  let _ := combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)
  let B := boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  dsimp only
  intro D r hr hD
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hDM : D ⊆ (glued₂ K B id).space :=
    hD.trans ((image_mono (boundaryComplex_space_subset 3 K)).trans hι.image_eq.subset)
  let g := Function.invFunOn ι K.space
  have hr₀ := hr.trans (hι.symm.restrict (show IsPLBall 2 D from ⟨r, hr⟩).isPolyhedron hDM)
  have hD₀ : g '' D ⊆ B.space := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hD hy
    rw [← hxy]
    change Function.invFunOn ι K.space (ι x) ∈ B.space
    rw [hι.bijOn.invOn_invFunOn.1 (boundaryComplex_space_subset 3 K hx)]
    exact hx
  obtain ⟨A, hA, hAM, hboundary, hinter⟩ :=
    exists_nonsingular_two_cell_of_boundary_disk K hK hr₀ hD₀
  have hboundary_eq : ι '' ((g ∘ r) '' stdSimplexBoundary 2) = r '' stdSimplexBoundary 2 := by
    rw [image_image]
    apply Set.EqOn.image_eq
    intro x hx
    exact hι.bijOn.invOn_invFunOn.2 (hDM (hr.bijOn.mapsTo hx.1))
  exact ⟨A, hA, hAM, hboundary.trans hboundary_eq, hinter.trans hboundary_eq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
