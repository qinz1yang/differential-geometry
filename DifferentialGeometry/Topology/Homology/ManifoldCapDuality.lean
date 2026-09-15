import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold
import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CompactCap

noncomputable section

open Set TopologicalSpace

namespace DifferentialGeometry.Topology

theorem integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    {E X : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace E X]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E)
    (a : integralSingularHomology (k + m) X)
    (ha : ∀ p : X, Function.Bijective (fun z : ℤ =>
      z • integralAbsoluteToRelative (k + m) ({p}ᶜ : Set X) a)) :
    Function.Bijective (fun α : integralSingularCohomology k X =>
      integralSingularCohomologyCapProduct k m α a) := by
  let cX (K : Compacts X) : integralRelativeHomology (k + m) (K : Set X)ᶜ :=
    integralAbsoluteToRelative (k + m) (K : Set X)ᶜ a
  have hcX (K L : Compacts X) (h : K ≤ L) :
      integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
        (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (cX L) = cX K := by
    have hn := LinearMap.congr_fun (integralAbsoluteToRelative_natural (k + m)
      (ContinuousMap.id X)
      (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h)) a
    simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id,
      LinearMap.id_apply] using hn.symm
  obtain ⟨D, ⟨hD, _⟩, _⟩ := exists_unique_integralCompactlySupportedCohomology_cap_of_absolute k m a
  apply (integralCompactlySupportedCohomology_cap_bijective_iff_of_absolute k m a D hD).mp
  exact integralCompactlySupportedCohomology_cap_bijective_of_chartedSpace
    k m hkm cX hcX ha D hD

end DifferentialGeometry.Topology

end
