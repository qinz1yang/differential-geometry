/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwo

/-!
# The actual carrier of a normal system in its double
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem NormalSystem.exists_singular_two_cell_in_double_with_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∃ D : SingularTwoCell (double 3 K).space,
      D.domain = S.sourceComplex.space ∧
      EqOn (fun x => (D x : E × E × ℝ)) (ι ∘ S.singularMap) S.sourceComplex.space ∧
      Subtype.val '' (D '' D.domain) = ι '' S.imageComplex.space ∧
      Set.range (fun x => (D.boundary x : E × E × ℝ)) = ι '' S.loopComplex.space ∧
      Subtype.val '' (D '' D.domain) ∩ ι '' (PiecewiseLinear.boundaryComplex 3 K).space =
        ι '' S.loopComplex.space ∧
      (∀ θ, (D (S.boundaryParam θ) : E × E × ℝ) = ι (S.boundaryLoop θ)) ∧
      (D.IsNonsingular ↔ S.IsNonsingular) ∧
      (∀ x ∈ S.sourceComplex.space, D.domain ∩ D ⁻¹' {D x} =
        S.sourceComplex.space ∩ S.singularMap ⁻¹' {S.singularMap x}) ∧
      MapsTo D D.domain C ∧ frontier C = Bd ∧
      D '' D.domain ∩ frontier C = Set.range D.boundary ∧
      ∀ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (y : (double 3 K).space), y ∈ e.source →
        ∀ᶠ z in 𝓝 (e y), z ∈ frontier (e '' (e.source ∩ C)) ↔
          z ∈ e '' (e.source ∩ Bd) := by
  classical
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
    (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
  obtain ⟨D, hdom, hDeq, himage, hboundary, hinter, hparam, hnonsingular⟩ :=
    S.exists_singular_two_cell_in_double
  have hι : IsPLHomeomorphOn ι K.space
      (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
      (glueSnd E E) (fun _ _ _ _ => rfl)
  have hfiber (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ S.sourceComplex.space) :
      D.domain ∩ D ⁻¹' {D x} =
        S.sourceComplex.space ∩ S.singularMap ⁻¹' {S.singularMap x} := by
    rw [hdom]
    ext z
    apply and_congr_right
    intro hz
    change D z = D x ↔ S.singularMap z = S.singularMap x
    constructor
    · intro hzx
      apply hι.bijOn.injOn (S.singularMap_mapsTo_manifoldComplex hz)
        (S.singularMap_mapsTo_manifoldComplex hx)
      exact (hDeq hz).symm.trans ((congrArg Subtype.val hzx).trans (hDeq hx))
    · intro hzx
      apply Subtype.ext
      exact (hDeq hz).trans ((congrArg ι hzx).trans (hDeq hx).symm)
  have hC : C = ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space := by
    rw [glued₂_space]
  have hfront : frontier C = Bd := by
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K S.isManifold
  have hmap : MapsTo D D.domain C := by
    intro x hx
    have hDx : (D x : E × E × ℝ) ∈ ι '' S.imageComplex.space :=
      himage ▸ mem_image_of_mem Subtype.val (mem_image_of_mem D hx)
    exact image_mono S.image_space_subset_manifoldComplex hDx
  have hinter' : D '' D.domain ∩ frontier C = Set.range D.boundary := by
    rw [hfront]
    apply Subtype.val_injective.image_injective
    rw [image_inter_preimage, ← range_comp, hinter]
    exact hboundary.symm
  refine ⟨D, hdom, hDeq, himage, hboundary, hinter, hparam, hnonsingular,
    hfiber, hmap, hfront, hinter', ?_⟩
  intro e y hy
  change ∀ᶠ z in 𝓝 (e y), z ∈ frontier (e '' (e.source ∩ C)) ↔
    z ∈ e '' (e.source ∩ Bd)
  rw [hC]
  exact eventually_mem_frontier_image_glued₂_iff K S.isManifold e hy

end DifferentialGeometry.Topology.PiecewiseLinear
