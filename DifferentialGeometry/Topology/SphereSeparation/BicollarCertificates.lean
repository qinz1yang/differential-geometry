import DifferentialGeometry.Topology.SphereSeparation.BicollarSliceSeparation
import DifferentialGeometry.Topology.SphereSeparation.TubularExcision

set_option autoImplicit false

open Function Set Topology
open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation


noncomputable def axialRecenterRadius {a : ℝ} (c : AxialInterval a) : ℝ :=
  min ((c : ℝ) + a) (a - (c : ℝ)) / 2

theorem axialRecenterRadius_pos {a : ℝ} (c : AxialInterval a) :
    0 < axialRecenterRadius c := by
  apply div_pos
  · exact lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  · norm_num

private theorem axialRecenterRadius_lt_leftMargin
    {a : ℝ} (c : AxialInterval a) :
    axialRecenterRadius c < (c : ℝ) + a := by
  have hm : 0 < min ((c : ℝ) + a) (a - (c : ℝ)) :=
    lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  have hh : min ((c : ℝ) + a) (a - (c : ℝ)) / 2 <
      min ((c : ℝ) + a) (a - (c : ℝ)) := by linarith
  exact lt_of_lt_of_le hh (min_le_left _ _)

private theorem axialRecenterRadius_lt_rightMargin
    {a : ℝ} (c : AxialInterval a) :
    axialRecenterRadius c < a - (c : ℝ) := by
  have hm : 0 < min ((c : ℝ) + a) (a - (c : ℝ)) :=
    lt_min (by linarith [c.2.1]) (by linarith [c.2.2])
  have hh : min ((c : ℝ) + a) (a - (c : ℝ)) / 2 <
      min ((c : ℝ) + a) (a - (c : ℝ)) := by linarith
  exact lt_of_lt_of_le hh (min_le_right _ _)

def axialRecenter {a : ℝ} (c : AxialInterval a) :
    AxialInterval (axialRecenterRadius c) → AxialInterval a :=
  fun t ↦ ⟨(c : ℝ) + (t : ℝ),
    by
      have ht := t.2.1
      have hb := axialRecenterRadius_lt_leftMargin c
      linarith,
    by
      have ht := t.2.2
      have hb := axialRecenterRadius_lt_rightMargin c
      linarith⟩

@[simp]
theorem axialRecenter_coe {a : ℝ} (c : AxialInterval a)
    (t : AxialInterval (axialRecenterRadius c)) :
    (axialRecenter c t : ℝ) = (c : ℝ) + (t : ℝ) :=
  rfl


theorem axialRecenter_isOpenEmbedding {a : ℝ} (c : AxialInterval a) :
    IsOpenEmbedding (axialRecenter c) := by
  let g : AxialInterval (axialRecenterRadius c) → ℝ :=
    fun t ↦ (c : ℝ) + (t : ℝ)
  have hg : IsOpenEmbedding g := by
    exact (Homeomorph.addLeft (c : ℝ)).isOpenEmbedding.comp
      isOpen_Ioo.isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp (axialRecenter c)
    (AxialInterval a).2.isOpenEmbedding_subtypeVal
  convert hg using 1
  funext t
  rfl


def recenteredBicollar
    {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    SphereTwo × AxialInterval (axialRecenterRadius c) → N :=
  fun x ↦ Φ (x.1, axialRecenter c x.2)


theorem recenteredBicollar_isOpenEmbedding
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a)
    (hΦ : IsOpenEmbedding Φ) :
    IsOpenEmbedding (recenteredBicollar Φ c) := by
  have hsource : IsOpenEmbedding
      (Prod.map (id : SphereTwo → SphereTwo) (axialRecenter c)) :=
    IsOpenEmbedding.id.prodMap (axialRecenter_isOpenEmbedding c)
  convert hΦ.comp hsource using 1
  funext x
  rfl

@[simp]
theorem recenteredBicollar_zeroSlice
    {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a)
    (p : SphereTwo) :
    recenteredBicollar Φ c
        (p, axialZero (axialRecenterRadius_pos c)) = Φ (p, c) := by
  apply congrArg Φ
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [axialRecenter, axialZero]

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ) (c : AxialInterval a)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) := by
  apply hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    (axialRecenterRadius_pos c) (bicollarSliceMap Φ c)
    (recenteredBicollar Φ c)
    (recenteredBicollar_isOpenEmbedding Φ c hΦ)
  · intro p
    exact recenteredBicollar_zeroSlice Φ c p
  · exact hSphere

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ) (c : AxialInterval a)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    Φ hΦ c
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

theorem smoothBicollar_isOpenEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ) :
    IsOpenEmbedding Φ := by
  refine ⟨hΦ.isEmbedding, ?_⟩
  have hrank :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
        Module.finrank ℝ EuclideanThree := by
    norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
  exact Manifold.isOpen_range_of_isSmoothEmbedding
    (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
    (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1))
    (c : AxialInterval a) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_openEmbedding_of_sphereH1
    Φ (smoothBicollar_isOpenEmbedding Φ hΦ) c hSphere

theorem hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex)
    (c : AxialInterval a) :
    HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c) :=
  hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
    Φ hΦ
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)
    c

end Poincare.Topology.SphereSeparation
