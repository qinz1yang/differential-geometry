import DifferentialGeometry.Topology.SphereSeparation.BicollarRelativeHomology
import DifferentialGeometry.Topology.SphereSeparation.TopologicalRelativeUnion

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Set
open Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def openBicollarExcisionAmbientHomeomorph
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ) :
    SphereTwo × AxialInterval a ≃ₜ
      (((Set.range Φ)ᶜ)ᶜ : Set EuclideanThree) :=
  hΦ.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by simp))

@[simp]
theorem openBicollarExcisionAmbientHomeomorph_coe
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ) (x : SphereTwo × AxialInterval a) :
    ((openBicollarExcisionAmbientHomeomorph Φ hΦ x :
      (((Set.range Φ)ᶜ)ᶜ : Set EuclideanThree)) : EuclideanThree) = Φ x :=
  by
    simp only [openBicollarExcisionAmbientHomeomorph,
      Homeomorph.trans_apply]
    exact hΦ.isEmbedding.toHomeomorph_apply_coe x

noncomputable def openBicollarExcisionSubspaceHomeomorph
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a)) ≃ₜ
      subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ := by
  let h := openBicollarExcisionAmbientHomeomorph Φ hΦ
  apply h.subtype
  intro x
  change x ∉ zeroSliceDomain ha ↔ (h x).1 ∉ Set.range e
  rw [show (h x).1 = Φ x by
    exact openBicollarExcisionAmbientHomeomorph_coe Φ hΦ x]
  constructor
  · intro hx hxe
    rcases hxe with ⟨p, hp⟩
    have hp' : Φ x = Φ (p, axialZero ha) := by
      rw [hzero p]
      exact hp.symm
    have : x = (p, axialZero ha) := hΦ.injective hp'
    apply hx
    rw [this]
    exact ⟨Set.mem_univ _, rfl⟩
  · intro hx hxslice
    apply hx
    rcases hxslice with ⟨-, haxial⟩
    refine ⟨x.1, ?_⟩
    rw [← hzero x.1]
    congr
    exact haxial.symm


theorem range_subset_openBicollar_range
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    Set.range e ⊆ Set.range Φ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p, axialZero ha), hzero p⟩

theorem openBicollar_excision_condition
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p) :
    closure (Set.range Φ)ᶜ ⊆ interior (Set.range e)ᶜ := by
  have hecont : Continuous e := by
    have hsection : Continuous
        (fun p : SphereTwo ↦ (p, axialZero ha)) := by fun_prop
    have hcomp : Continuous (fun p : SphereTwo ↦ Φ (p, axialZero ha)) :=
      hΦ.continuous.comp hsection
    simpa only [hzero] using hcomp
  have heclosed : IsClosed (Set.range e) :=
    (isCompact_range hecont).isClosed
  rw [hΦ.isOpen_range.isClosed_compl.closure_eq,
    heclosed.isOpen_compl.interior_eq]
  exact compl_subset_compl.mpr
    (range_subset_openBicollar_range ha e Φ hzero)

theorem isIso_openBicollar_relativeSingularHomologyMap
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (n : ℕ) :
    IsIso
      (relativeSingularHomologyMapOfSubspaces
        ⟨openBicollarExcisionAmbientHomeomorph Φ hΦ,
          (openBicollarExcisionAmbientHomeomorph Φ hΦ).continuous⟩
        ((zeroSliceDomain ha)ᶜ :
          Set (SphereTwo × AxialInterval a))
        (subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ)
        (fun x hx ↦
          (openBicollarExcisionSubspaceHomeomorph
            ha e Φ hΦ hzero ⟨x, hx⟩).2)
        n) := by
  apply isIso_relativeSingularHomologyMapOfSubspaces
  · exact (openBicollarExcisionAmbientHomeomorph Φ hΦ).isHomeomorph
  · let g := openBicollarExcisionSubspaceHomeomorph
      ha e Φ hΦ hzero
    convert g.isHomeomorph using 1
    funext x
    apply Subtype.ext
    rfl

theorem embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    Nonempty
      (relativeSingularHomologyOfSubspace (Set.range e)ᶜ 1 ≅
        ModuleCat.of ℤ ℤ) := by
  let pairMap := relativeSingularHomologyMapOfSubspaces
    ⟨openBicollarExcisionAmbientHomeomorph Φ hΦ,
      (openBicollarExcisionAmbientHomeomorph Φ hΦ).continuous⟩
    ((zeroSliceDomain ha)ᶜ : Set (SphereTwo × AxialInterval a))
    (subspaceOutside (Set.range e)ᶜ (Set.range Φ)ᶜ)
    (fun x hx ↦
      (openBicollarExcisionSubspaceHomeomorph
        ha e Φ hΦ hzero ⟨x, hx⟩).2)
    1
  let _ : IsIso pairMap :=
    isIso_openBicollar_relativeSingularHomologyMap
      ha e Φ hΦ hzero 1
  let excisionMap := excisionRelativeSingularHomologyMap
    (Set.range e)ᶜ (Set.range Φ)ᶜ 1
  let _ : IsIso excisionMap :=
    singularExcisionFor (Set.range e)ᶜ (Set.range Φ)ᶜ
      (openBicollar_excision_condition ha e Φ hΦ hzero) 1
  exact ⟨(asIso excisionMap).symm ≪≫ (asIso pairMap).symm ≪≫
    Classical.choice
      (centralSliceComplement_relativeH1_iso_int_of_sphere ha hSphere)⟩

theorem embeddedSphere_relativeH1_iso_int_of_openBicollar
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    Nonempty
      (relativeSingularHomologyOfSubspace (Set.range e)ᶜ 1 ≅
        ModuleCat.of ℤ ℤ) :=
  embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
    ha e Φ hΦ hzero
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

theorem hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (hSphere : IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_relativeH1 e
    (embeddedSphere_relativeH1_iso_int_of_openBicollar_of_sphereH1
      ha e Φ hΦ hzero hSphere)

theorem hasAlexanderDualityH0Certificate_of_openBicollar
    {a : ℝ} (ha : 0 < a)
    (e : SphereTwo → EuclideanThree)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = e p)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
    ha e Φ hΦ hzero
      (isZero_integerSingularHomology_sphereTwo_one_of_cellularComparison
        comparison)

end DifferentialGeometry.Topology.SphereSeparation
