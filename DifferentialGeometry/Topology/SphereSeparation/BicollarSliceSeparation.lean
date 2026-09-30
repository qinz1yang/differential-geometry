import DifferentialGeometry.Topology.SphereSeparation.BicollarLocalTwoSided
import DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import DifferentialGeometry.Topology.SphereSeparation.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.Transport

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation


def bicollarSliceMap {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    SphereTwo → N :=
  fun x => Φ (x, c)

theorem range_bicollarSliceMap {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    Set.range (bicollarSliceMap Φ c) = sliceImage Φ c := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x, c), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hpEq : p = (p.1, c) := by
      apply Prod.ext
      · rfl
      · exact hp.2
    exact ⟨p.1, by rw [bicollarSliceMap, ← hpEq]⟩

noncomputable def bicollarSliceSidesOfAlexanderDualityCertificate
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (c : AxialInterval a)
    (hAD : HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c)) :
    SphereSides (sliceImage Φ c) := by
  have hcont : Continuous (bicollarSliceMap Φ c) := by
    exact hΦ.contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcompact : IsCompact (Set.range (bicollarSliceMap Φ c)) :=
    isCompact_range hcont
  have hconnected : IsConnected (Set.range (bicollarSliceMap Φ c)) := by
    simpa only [image_univ] using
      isConnected_sphereTwo.image (bicollarSliceMap Φ c)
        hcont.continuousOn
  rw [← range_bicollarSliceMap Φ c]
  exact topologicalSphereSidesOfAlexanderDualityData
    (bicollarSliceMap Φ c) hcompact hconnected
    (by
      rw [range_bicollarSliceMap Φ c]
      exact locallyTwoSided_sliceImage Φ hΦ c)
    hAD

theorem sliceImage_equiv_comp
    {N M : Type*} {a : ℝ} (ψ : N ≃ M)
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    sliceImage (ψ ∘ Φ) c = ψ '' sliceImage Φ c := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Φ p, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

noncomputable def bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificate
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (c : AxialInterval a)
    (hAD : HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c)) :
    SphereSides (sliceImage Φ c) := by
  have hΦℝ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ (ψ ∘ Φ) :=
    hΦ.postcomp_diffeomorph ψ
  let dℝ : SphereSides (sliceImage (ψ ∘ Φ) c) :=
    bicollarSliceSidesOfAlexanderDualityCertificate
      (ψ ∘ Φ) hΦℝ c hAD
  have himage :
      sliceImage (ψ ∘ Φ) c = ψ '' sliceImage Φ c :=
    sliceImage_equiv_comp ψ.toEquiv Φ c
  have hback : ψ.symm '' sliceImage (ψ ∘ Φ) c = sliceImage Φ c := by
    rw [himage, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

noncomputable def bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificates
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : ∀ c, HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c))
    (c : AxialInterval a) :
    SphereSides (sliceImage Φ c) :=
  bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificate
    Φ hΦ ψ c (hAD c)

theorem bicollar_sides_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) (axialZero ha))) :
    let d :=
      bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificate
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  let d :=
    bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificate
      Φ hΦ ψ (axialZero ha) hAD
  change Xor
    (negativeHalfImage Φ ha ⊆ d.compactSide ∧
      positiveHalfImage Φ ha ⊆ d.endSide)
    (negativeHalfImage Φ ha ⊆ d.endSide ∧
      positiveHalfImage Φ ha ⊆ d.compactSide)
  change SphereSides (zeroSliceImage Φ ha) at d
  exact bicollar_halves_opposite ha Φ hΦ d

theorem bicollar_order_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : ∀ c, HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ
      (bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificates Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
    let d := bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificates Φ hΦ ψ hAD
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  exact bicollar_order_of_atZero ha Φ hΦ
    (bicollarSliceSidesOpenThreeSpaceOfAlexanderDualityCertificates Φ hΦ ψ hAD)
    o₀ hst

end DifferentialGeometry.Topology.SphereSeparation
