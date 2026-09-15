import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Cap

open Set TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

theorem integralCompactlySupportedCohomology_cap_bijective_iff_of_absolute
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (k m : ℕ) (a : integralSingularHomology (k + m) X)
    (D : integralCompactlySupportedCohomology k X →ₗ[ℤ] integralSingularHomology m X)
    (hD : ∀ (K : Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
      D (integralRelativeToCompactlySupportedCohomology k K α) =
        integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α
          (integralAbsoluteToRelative (k + m) (K : Set X)ᶜ a)) :
    Function.Bijective D ↔ Function.Bijective (fun α : integralSingularCohomology k X => integralSingularCohomologyCapProduct k m α a) := by
  obtain ⟨D', ⟨hD', hcomp⟩, _⟩ :=
    exists_unique_integralCompactlySupportedCohomology_cap_of_absolute k m a
  have hDD' : D = D' := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hD K α).trans (hD' K α).symm)
  have heq : (D : integralCompactlySupportedCohomology k X → integralSingularHomology m X) =
      (fun α : integralSingularCohomology k X => integralSingularCohomologyCapProduct k m α a) ∘
        integralCompactlySupportedToSingularCohomology k X := by
    funext α
    rw [hDD']
    exact hcomp α
  rw [heq]
  exact Function.Bijective.of_comp_iff _
    (integralCompactlySupportedToSingularCohomology_bijective (X := X) k)

end DifferentialGeometry.Topology
