import DifferentialGeometry.Topology.SphereSeparation.BicollarCertificates
import DifferentialGeometry.Topology.SphereSeparation.SeparationAssembly

set_option autoImplicit false

open Function Set Topology
open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = ψ (e p))
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
      ha (ψ ∘ e) Φ hΦ hzero hSphere)

noncomputable def smoothSphereSidesOpenThreeSpace_of_openBicollar
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = ψ (e p))
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (hasAlexanderDualityH0Certificate_of_openBicollar
      ha (ψ ∘ e) Φ hΦ hzero comparison)

theorem bicollar_sides_openThreeSpace_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    let hAD :=
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere (axialZero ha)
    let d :=
      topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  exact bicollar_sides_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ
      (hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere (axialZero ha))

theorem bicollar_sides_openThreeSpace_of_cellularComparison
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    let hAD :=
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison (axialZero ha)
    let d :=
      topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  exact bicollar_sides_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ
      (hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison (axialZero ha))

theorem bicollar_order_openThreeSpace_of_sphereH1
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1))
    (o₀ :
      let hAD := fun c ↦
        hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
          (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
      IsAxiallyOrientedAtZero ha Φ
        (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
    let hAD := fun c ↦
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
    let d := bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  let _ : T2Space N := ψ.symm.toHomeomorph.t2Space
  let hAD := fun c ↦
    hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
      (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
  exact bicollar_order_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ hAD o₀ hst

theorem bicollar_order_openThreeSpace_of_cellularComparison
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex)
    (o₀ :
      let hAD := fun c ↦
        hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
          (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
      IsAxiallyOrientedAtZero ha Φ
        (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
    let hAD := fun c ↦
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
    let d := bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  let _ : T2Space N := ψ.symm.toHomeomorph.t2Space
  let hAD := fun c ↦
    hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
      (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
  exact bicollar_order_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ hAD o₀ hst

end DifferentialGeometry.Topology.SphereSeparation
