import DifferentialGeometry.Topology.Homology.CarrierRestriction
import DifferentialGeometry.Topology.Homology.RelativeMaps



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]



theorem integralSingularChainsIn_map (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    (integralSingularChainMap f).f n c ∈ integralSingularChainsIn n B := by
  have h : integralSingularChainsIn n A ≤
      Submodule.comap ((integralSingularChainMap f).f n).hom (integralSingularChainsIn n B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change (integralSingularChainMap f).f n (integralSimplexChain n σ) ∈ integralSingularChainsIn n B
    rw [integralSimplexChain_map]
    apply Submodule.subset_span
    refine ⟨integralSingularSimplexMap n f σ, ?_, rfl⟩
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    exact hf (hσ ⟨t, rfl⟩)
  exact h hc


def singularCarrierMap (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    integralSingularChainsIn n A →ₗ[ℤ] integralSingularChainsIn n B :=
  ((integralSingularChainMap f).f n).hom.restrict (fun _ hc => integralSingularChainsIn_map n f hf hc)


theorem integralSingularChainRestriction_map (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (c : integralSingularChainsIn n A) :
    integralSingularChainRestriction n B (singularCarrierMap n f hf c) =
      (integralSingularChainMap (singularPairRestriction f hf)).f n (integralSingularChainRestriction n A c) := by
  apply integralSingularChainInclusion_injective n B
  rw [integralSingularChainRestriction_inclusion]
  have h := congrArg (fun h : integralSingularChains A ⟶ integralSingularChains Y =>
    h.f n (integralSingularChainRestriction n A c)) (integralSingularChainMap_pair_square f hf)
  change (integralSingularChainMap f).f n ((integralSingularChainMap (singularSubspaceInclusion A)).f n
    (integralSingularChainRestriction n A c)) =
      (integralSingularChainMap (singularSubspaceInclusion B)).f n
        ((integralSingularChainMap (singularPairRestriction f hf)).f n
          (integralSingularChainRestriction n A c)) at h
  rw [integralSingularChainRestriction_inclusion] at h
  exact h

end DifferentialGeometry.Topology
