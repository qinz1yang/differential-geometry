import Poincare.Topology.Homology.ChainSupport
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Poincare.Topology.Homology.ChainCokernelElements
import Poincare.Topology.Homology.ModuleHomologyMaps
import Poincare.Topology.Homology.RelativeFunctoriality


section

open Set

universe u

namespace Poincare.Topology

theorem exists_compact_carrier_integral_singular_chain
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X n) (hc : c ∈ integralSingularChainsIn n A) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ c ∈ integralSingularChainsIn n K := by
  classical
  let S := (integralSingularChainRepr n X c).support
  refine ⟨⋃ σ ∈ S, range (integralSingularSimplexEquiv n X σ), ?_, ?_, ?_⟩
  · exact S.isCompact_biUnion fun σ _ =>
      isCompact_range (integralSingularSimplexEquiv n X σ).continuous
  · intro x hx
    rcases mem_iUnion₂.mp hx with ⟨σ, hσ, hx⟩
    exact (integralSingularChainsIn_mem_iff n A c).mp hc σ
      (Finsupp.mem_support_iff.mp hσ) hx
  · apply (integralSingularChainsIn_mem_iff n _ c).mpr
    intro σ hσ x hx
    exact mem_iUnion₂.mpr ⟨σ, Finsupp.mem_support_iff.mpr hσ, hx⟩

end Poincare.Topology

end


section

open Set

namespace Poincare.Topology

private theorem exists_compact_neighborhood_avoiding_integral_chain
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (c : (integralSingularChains X).X n) (hc : c ∈ integralSingularChainsIn n Kᶜ) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      c ∈ integralSingularChainsIn n Lᶜ := by
  obtain ⟨F, hF, hFK, hcF⟩ := exists_compact_carrier_integral_singular_chain n Kᶜ c hc
  have hKF : K ⊆ Fᶜ := by
    intro x hx hxF
    exact hFK hxF hx
  obtain ⟨L, hL, hKL, hLUF⟩ := exists_compact_between hK
    (hU.inter hF.isClosed.isOpen_compl) (subset_inter hKU hKF)
  refine ⟨L, hL, hKL, hLUF.trans inter_subset_left, ?_⟩
  apply integralSingularChainsIn_mono n (show F ⊆ Lᶜ from ?_) hcF
  intro x hxF hxL
  exact (hLUF hxL).2 hxF

end Poincare.Topology

end


section

open CategoryTheory CategoryTheory.Limits Set

universe v

namespace Poincare.Topology

theorem exists_relative_homology_class_on_compact_neighborhood
    {X : Type v} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (a : integralRelativeHomology n Kᶜ) :
    ∃ (L : Set X) (hKL : K ⊆ interior L), IsCompact L ∧ L ⊆ U ∧
      ∃ b : integralRelativeHomology n Lᶜ,
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
            fun _ hx hxK => hx (interior_subset (hKL hxK))) b = a := by
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective ((integralRelativeChains Kᶜ).sc n) a
  let πK : integralSingularChains X ⟶ integralRelativeChains Kᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion Kᶜ))
  obtain ⟨c, hc⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion Kᶜ)) n z.val
  let m := (ComplexShape.down ℕ).next n
  have hdcK : πK.f m ((integralSingularChains X).d n m c) = 0 := by
    have h := congrArg (fun f : (integralSingularChains X).X n ⟶
      (integralRelativeChains Kᶜ).X m => f c) (πK.comm n m)
    change (integralRelativeChains Kᶜ).d n m (πK.f n c) =
      πK.f m ((integralSingularChains X).d n m c) at h
    rw [← h]
    change (integralRelativeChains Kᶜ).d n m
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion Kᶜ))).f n c) = 0
    rw [hc]
    exact z.property
  have hdc : (integralSingularChains X).d n m c ∈ integralSingularChainsIn m Kᶜ := by
    rw [integralSingularChainsIn_eq_range]
    exact (chainCokernelπ_eq_zero_iff _ m _).mp hdcK
  obtain ⟨L, hL, hKL, hLU, hdcL⟩ := exists_compact_neighborhood_avoiding_integral_chain
    m K U hK hU hKU ((integralSingularChains X).d n m c) hdc
  let πL : integralSingularChains X ⟶ integralRelativeChains Lᶜ :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion Lᶜ))
  have hdcLzero : πL.f m ((integralSingularChains X).d n m c) = 0 := by
    apply (chainCokernelπ_eq_zero_iff _ m _).mpr
    rw [integralSingularChainsIn_eq_range] at hdcL
    obtain ⟨d, hd⟩ := hdcL
    exact ⟨d, hd⟩
  let w : LinearMap.ker ((integralRelativeChains Lᶜ).sc n).g.hom :=
    ⟨πL.f n c, by
      change (integralRelativeChains Lᶜ).d n m (πL.f n c) = 0
      have h := congrArg (fun f : (integralSingularChains X).X n ⟶
        (integralRelativeChains Lᶜ).X m => f c) (πL.comm n m)
      exact h.trans hdcLzero⟩
  let hLK : MapsTo (ContinuousMap.id X) Lᶜ Kᶜ :=
    fun _ hx hxK => hx (interior_subset (hKL hxK))
  let ρ := integralRelativeChainMap (ContinuousMap.id X) hLK
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} ℤ)
    (ComplexShape.down ℕ) n).map ρ
  refine ⟨L, hKL, hL, hLU, moduleHomologyClass ((integralRelativeChains Lᶜ).sc n) w, ?_⟩
  change ShortComplex.homologyMap φ
    (moduleHomologyClass ((integralRelativeChains Lᶜ).sc n) w) = a
  rw [moduleHomologyClass_map]
  have hwz : moduleCycleMap φ w = z := by
    apply Subtype.ext
    change ρ.f n (πL.f n c) = z.val
    have h := integralRelativeChainMap_π (ContinuousMap.id X) hLK
    rw [integralSingularChainMap_id, Category.id_comp] at h
    exact (congrArg (fun f : integralSingularChains X ⟶ integralRelativeChains Kᶜ =>
      f.f n c) h).trans hc
  rw [hwz]
  exact hz

end Poincare.Topology

end
