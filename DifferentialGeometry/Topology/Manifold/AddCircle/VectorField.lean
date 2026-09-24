import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent

noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace AddCircle

theorem contMDiff_periodic_lift_family {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hper : ∀ t, Function.Periodic (fun x => β (t, x)) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => (hper p.1).lift p.2) := by
  rw [← contMDiffOn_univ, ← Set.univ_prod_univ]
  apply contMDiffOn_of_comp_coe
  change ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ β (univ ×ˢ univ)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact hβ.contMDiff.contMDiffOn

theorem contMDiff_parameterTangent_smul {β : ℝ × AddCircle (1 : ℝ) → ℝ}
    (hβ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun p : ℝ × AddCircle (1 : ℝ) =>
        (⟨p.2, β p • parameterTangent p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) := by
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun p : ℝ × AddCircle (1 : ℝ) =>
        (⟨p.2, parameterTangent p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) :=
    contMDiff_parameterTangent.comp contMDiff_snd
  intro p₀
  have hVat := hV p₀
  rw [Bundle.contMDiffAt_totalSpace] at hVat ⊢
  refine ⟨hVat.1, ?_⟩
  let e := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) : AddCircle (1 : ℝ) → Type) p₀.2
  have hfib := (hβ p₀).smul hVat.2
  have hmem : e.baseSet ∈ 𝓝 p₀.2 :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p₀.2)
  refine hfib.congr_of_eventuallyEq ?_
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hmem] with p hp
  exact (e.linear ℝ hp).2 (β p) (parameterTangent p.2)

end AddCircle
