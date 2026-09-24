import DifferentialGeometry.Topology.Homology.RadialCohomology
import DifferentialGeometry.Topology.Homology.TwoPointCapDuality
import DifferentialGeometry.Topology.Homology.ContractiblePairOne

universe v

namespace DifferentialGeometry.Topology

open Set Metric

theorem exists_unique_real_local_cap_bijective :
    ∃! c : integralRelativeHomology 1 ({0}ᶜ : Set ℝ),
      integralRelativeConnecting 0 ({0}ᶜ : Set ℝ) c =
        integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : ({0}ᶜ : Set ℝ))) -
          integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : ({0}ᶜ : Set ℝ))) ∧
      Function.Bijective (fun α : integralRelativeCohomology 1 ({0}ᶜ : Set ℝ) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set ℝ) 1 0 α c) := by
  have hS : sphere (0 : ℝ) 1 = ({-1, 1} : Set ℝ) := by
    simpa only [zero_sub, zero_add] using Real.sphere_eq_pair 0 (by norm_num : (0 : ℝ) ≤ 1)
  have hcomparison := exists_integralRelativeCohomologyMap_sphere_puncture_bijective ℝ 1
  rw [hS] at hcomparison
  obtain ⟨h, hcoh⟩ := hcomparison
  obtain ⟨c, ⟨hc, hcap⟩, _⟩ :=
    exists_unique_relative_pair_cap_bijective (-1 : ℝ) 1 (by norm_num)
  let d := integralRelativeHomologyMap 1 (ContinuousMap.id ℝ) h c
  have hd : integralRelativeConnecting 0 ({0}ᶜ : Set ℝ) d =
      integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : ({0}ᶜ : Set ℝ))) -
        integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : ({0}ᶜ : Set ℝ))) := by
    have hn := LinearMap.congr_fun (integralRelativeConnecting_natural 0 (ContinuousMap.id ℝ) h) c
    change integralSingularHomologyMap 0 (singularPairRestriction (ContinuousMap.id ℝ) h)
      (integralRelativeConnecting 0 ({-1, 1} : Set ℝ) c) =
        integralRelativeConnecting 0 ({0}ᶜ : Set ℝ) d at hn
    rw [hc, map_sub, integralZeroChainClass_map, integralZeroChainClass_map,
      integralVertexChain_map, integralVertexChain_map] at hn
    exact hn.symm
  refine ⟨d, ⟨hd, ?_⟩, ?_⟩
  · exact integralRelativeCohomologyCapToAbsolute_bijective_map 1 0 (ContinuousMap.id ℝ) h
      (by rw [integralSingularHomologyMap_id]; exact Function.bijective_id) hcoh c hcap
  · intro e he
    exact integralRelativeConnecting_zero_injective ({0}ᶜ : Set ℝ) (he.1.trans hd.symm)

end DifferentialGeometry.Topology
