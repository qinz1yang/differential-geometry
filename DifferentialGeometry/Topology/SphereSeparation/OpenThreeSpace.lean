import DifferentialGeometry.Topology.SphereSeparation.EuclideanComponents
import DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import DifferentialGeometry.Topology.SphereSeparation.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.Transport

set_option autoImplicit false

open Function Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem range_equiv_comp
    {X Y Z : Type*} (h : Y ≃ Z) (f : X → Y) :
    Set.range (h ∘ f) = h '' Set.range f := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

noncomputable def topologicalSphereSidesOpenThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (happroach :
      let p := complementPairOfComponentCount
        ((isCompact_range
          (ψ.continuous.comp he.contMDiff.continuous)).isClosed.isOpen_compl)
        hcount
      Set.range (ψ ∘ e) ⊆ closure p.left ∧
        Set.range (ψ ∘ e) ⊆ closure p.right) :
    SphereSides (Set.range e) := by
  have hcompact : IsCompact (Set.range (ψ ∘ e)) :=
    isCompact_range (ψ.continuous.comp he.contMDiff.continuous)
  let p : ComplementPair (Set.range (ψ ∘ e)) :=
    complementPairOfComponentCount hcompact.isClosed.isOpen_compl hcount
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    sphereSidesOfComplementPair hcompact p happroach.1 happroach.2
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange]
    rw [Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

noncomputable def topologicalSphereSidesOpenThreeSpaceOfLocallyTwoSided
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (𝓘(ℝ, EuclideanThree)) ∞ EuclideanThree]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (hlocal : LocallyTwoSided (Set.range (ψ ∘ e))) :
    SphereSides (Set.range e) := by
  have heℝ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞
      (ψ ∘ e) :=
    he.postcomp_diffeomorph ψ
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    topologicalSphereSidesOfComponentCountOfLocallyTwoSided
      (ψ ∘ e) heℝ hcount hlocal
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

noncomputable def topologicalSphereSidesOpenThreeSpaceOfAlexanderDualityCertificate
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate (ψ ∘ e)) :
    SphereSides (Set.range e) := by
  have heℝ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞
      (ψ ∘ e) :=
    he.postcomp_diffeomorph ψ
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    topologicalSphereSidesOfAlexanderDuality (ψ ∘ e) heℝ hAD
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

theorem topologicalSphereSidesOpenThreeSpace_unique
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (happroach :
      let p := complementPairOfComponentCount
        ((isCompact_range
          (ψ.continuous.comp he.contMDiff.continuous)).isClosed.isOpen_compl)
        hcount
      Set.range (ψ ∘ e) ⊆ closure p.left ∧
        Set.range (ψ ∘ e) ⊆ closure p.right)
    (d : SphereSides (Set.range e)) :
    d = topologicalSphereSidesOpenThreeSpace e he ψ hcount happroach :=
  SphereSides.unique _ _

end DifferentialGeometry.Topology.SphereSeparation
