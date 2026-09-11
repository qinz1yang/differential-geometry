import DifferentialGeometry.Topology.SphereSeparation.BicollarSeparationAssembly
import DifferentialGeometry.Topology.SphereSeparation.NestingSeparation
import DifferentialGeometry.Topology.SphereSeparation.TubularBicollar

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Function Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

def axialIntervalHomeomorphIoo (a : ℝ) :
    AxialInterval a ≃ₜ (Ioo (-a) a : Set ℝ) where
  toFun t := ⟨t, t.2⟩
  invFun t := ⟨t, t.2⟩
  left_inv _t := Subtype.ext rfl
  right_inv _t := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _


noncomputable def normalFieldBicollar
    (e ν : SphereTwo → EuclideanThree) (a : ℝ) :
    SphereTwo × AxialInterval a → EuclideanThree :=
  fun z ↦ e z.1 + (z.2 : ℝ) • ν z.1

@[simp]
theorem normalFieldBicollar_zeroSlice
    (e ν : SphereTwo → EuclideanThree) {a : ℝ} (ha : 0 < a)
    (p : SphereTwo) :
    normalFieldBicollar e ν a (p, axialZero ha) = e p := by
  simp [normalFieldBicollar, axialZero]

theorem exists_openBicollar_of_smooth_normalField
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ IsOpenEmbedding (normalFieldBicollar e ν a) := by
  obtain ⟨a, ha, hΦ⟩ :=
    exists_uniform_normal_bicollar_product he hν hνnormal hνne
  refine ⟨a, ha, ?_⟩
  let sourceEquiv :
      SphereTwo × AxialInterval a ≃ₜ
        SphereTwo × (Ioo (-a) a : Set ℝ) :=
    (Homeomorph.refl SphereTwo).prodCongr (axialIntervalHomeomorphIoo a)
  have hcomp := hΦ.comp sourceEquiv.isOpenEmbedding
  convert hcomp using 1
  funext z
  rfl

theorem hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
    {e ν : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine e p)
    (hνne : ∀ p, ν p ≠ 0)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    HasAlexanderDualityH0Certificate e := by
  obtain ⟨a, ha, hΦ⟩ :=
    exists_openBicollar_of_smooth_normalField he hν hνnormal hνne
  exact hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    ha e (normalFieldBicollar e ν a) hΦ
      (normalFieldBicollar_zeroSlice e ν ha) hSphere

noncomputable def smoothSphereSidesOpenThreeSpace_of_smooth_normalField_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (ν : SphereTwo → EuclideanThree)
    (hν : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν)
    (hνnormal : ∀ p, ν p ∈ embeddedSphereNormalLine (ψ ∘ e) p)
    (hνne : ∀ p, ν p ≠ 0)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
      (he.postcomp_diffeomorph ψ) hν hνnormal hνne hSphere)

theorem disjoint_spheres_nested_openThreeSpace_of_smooth_normalFields_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e₁ e₂ : SphereTwo → N)
    (he₁ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₂)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (ν₁ ν₂ : SphereTwo → EuclideanThree)
    (hν₁ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν₁)
    (hν₂ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ ν₂)
    (hν₁normal : ∀ p, ν₁ p ∈ embeddedSphereNormalLine (ψ ∘ e₁) p)
    (hν₂normal : ∀ p, ν₂ p ∈ embeddedSphereNormalLine (ψ ∘ e₂) p)
    (hν₁ne : ∀ p, ν₁ p ≠ 0)
    (hν₂ne : ∀ p, ν₂ p ≠ 0)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1))
    (hdisjoint : Disjoint (Set.range e₁) (Set.range e₂))
    (hmeet :
      let hAD₁ :=
        hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
          (he₁.postcomp_diffeomorph ψ) hν₁ hν₁normal hν₁ne hSphere
      let hAD₂ :=
        hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
          (he₂.postcomp_diffeomorph ψ) hν₂ hν₂normal hν₂ne hSphere
      let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₁ he₁ ψ hAD₁
      let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₂ he₂ ψ hAD₂
      (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    let hAD₁ :=
      hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
        (he₁.postcomp_diffeomorph ψ) hν₁ hν₁normal hν₁ne hSphere
    let hAD₂ :=
      hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
        (he₂.postcomp_diffeomorph ψ) hν₂ hν₂normal hν₂ne hSphere
    let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₁ he₁ ψ hAD₁
    let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₂ he₂ ψ hAD₂
    Xor
      (closure d₁.compactSide ⊂ d₂.compactSide ∧
        d₂.compactSide = interior (closure d₂.compactSide) ∧
        closure d₁.compactSide ⊂ closure d₂.compactSide)
      (closure d₂.compactSide ⊂ d₁.compactSide ∧
        d₁.compactSide = interior (closure d₁.compactSide) ∧
        closure d₂.compactSide ⊂ closure d₁.compactSide) := by
  let hAD₁ :=
    hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
      (he₁.postcomp_diffeomorph ψ) hν₁ hν₁normal hν₁ne hSphere
  let hAD₂ :=
    hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
      (he₂.postcomp_diffeomorph ψ) hν₂ hν₂normal hν₂ne hSphere
  exact disjoint_spheres_nested_openThreeSpace_of_alexanderDuality
    e₁ e₂ he₁ he₂ ψ hAD₁ hAD₂ hdisjoint hmeet

end DifferentialGeometry.Topology.SphereSeparation
