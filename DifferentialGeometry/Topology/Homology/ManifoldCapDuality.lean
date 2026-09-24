import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold
import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.CompactCap
import DifferentialGeometry.Topology.Homology.ManifoldHomologyGenerator

noncomputable section

open CategoryTheory Set TopologicalSpace
open scoped Manifold

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

private theorem integralAbsoluteToRelative_generator_of_degree_eq
    {X : Type} [TopologicalSpace X] (n d : ℕ) (h : n = d)
    (a : integralSingularHomology d X)
    (ha : ∀ p : X, Function.Bijective (fun z : ℤ =>
      z • integralAbsoluteToRelative d ({p}ᶜ : Set X) a)) :
    ∀ p : X, Function.Bijective (fun z : ℤ => z • integralAbsoluteToRelative n ({p}ᶜ : Set X)
      ((eqToHom (congrArg (fun j => integralSingularHomology j X) h.symm)) a)) := by
  subst d
  exact ha

theorem exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ a : integralSingularHomology (Module.finrank ℝ E) M,
      Function.Bijective (fun z : ℤ => z • a) ∧
      (∀ p : M, Function.Bijective (fun z : ℤ =>
        z • integralAbsoluteToRelative (Module.finrank ℝ E) ({p}ᶜ : Set M) a)) ∧
      ∀ (k m : ℕ) (hkm : k + m = Module.finrank ℝ E),
        Function.Bijective (fun α : integralSingularCohomology k M =>
          integralSingularCohomologyCapProduct k m α
            ((eqToHom (congrArg (fun j => integralSingularHomology j M) hkm.symm)) a)) := by
  obtain ⟨a, hgen, hpoints⟩ :=
    exists_integralSingularHomology_generator_of_simplyConnected (E := E) (M := M)
  refine ⟨a, hgen, hpoints, ?_⟩
  intro k m hkm
  apply integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    (E := E) (X := M) k m hkm
  exact integralAbsoluteToRelative_generator_of_degree_eq (k + m) (Module.finrank ℝ E)
    hkm a hpoints

theorem exists_integralSingularHomology_cap_bijective_of_simplyConnected
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E) :
    ∃ a : integralSingularHomology (k + m) M,
      Function.Bijective (fun α : integralSingularCohomology k M =>
        integralSingularCohomologyCapProduct k m α a) := by
  obtain ⟨a, _, _, ha⟩ :=
    exists_integralSingularHomology_generator_with_cap_bijections_of_simplyConnected
      (E := E) (M := M)
  exact ⟨(eqToHom (congrArg (fun j => integralSingularHomology j M) hkm.symm)) a,
    ha k m hkm⟩


end DifferentialGeometry.Topology

end
