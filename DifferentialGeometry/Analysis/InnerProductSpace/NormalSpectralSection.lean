import DifferentialGeometry.Tensor.LinearAlgebra.Eigenspace.FixedSubspace
import DifferentialGeometry.Analysis.InnerProductSpace.NormalProjectionSpan

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H]

theorem starProjection_eigenspace_iSup_of_fixed
    (V : Submodule 𝕜 H) (O : H →L[𝕜] H) (s : Set 𝕜) (hs : 1 ∈ s)
    (hfix : ∀ v ∈ V, O v = v) :
    V.starProjection.comp (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection =
      V.starProjection :=
  starProjection_comp_starProjection_of_le (le_iSup_eigenspace_of_fixed V O.toLinearMap s hs hfix)

theorem eigenspace_iSup_starProjection_comp_of_fixed
    (V : Submodule 𝕜 H) (O : H →L[𝕜] H) (s : Set 𝕜) (hs : 1 ∈ s)
    (hfix : ∀ v ∈ V, O v = v) :
    (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection.comp V.starProjection =
      V.starProjection := by
  ext v
  exact starProjection_eq_self_iff.mpr
    (le_iSup_eigenspace_of_fixed V O.toLinearMap s hs hfix (V.starProjection_apply_mem v))

theorem starProjection_weighted_normal_section
    {A : Type*} (V : Submodule 𝕜 H) (S : Finset A)
    (L : A → Submodule 𝕜 H) (x : A → H) (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1)
    (hL : ∀ i ∈ S, w i ≠ 0 → L i ≤ Vᗮ)
    (hx : ∀ i ∈ S, w i ≠ 0 → x i ∈ Vᗮ)
    (s : Set 𝕜) (hs : 1 ∈ s) (z : H) :
    let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
    V.starProjection (∑ i ∈ S, w i • Q (z - x i)) = V.starProjection z := by
  classical
  let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
  let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
  have hfix (v : H) (hv : v ∈ V) : O v = v :=
    sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal Vᗮ S L w hw hL
      (le_orthogonal_orthogonal V hv)
  have hQ := starProjection_eigenspace_iSup_of_fixed V O s hs hfix
  have hQv (v : H) : V.starProjection (Q v) = V.starProjection v :=
    congrArg (fun A : H →L[𝕜] H => A v) hQ
  change V.starProjection (∑ i ∈ S, w i • Q (z - x i)) = V.starProjection z
  rw [map_sum]
  calc
    ∑ i ∈ S, V.starProjection (w i • Q (z - x i)) = ∑ i ∈ S, w i • V.starProjection z := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, zero_smul, map_zero]
      · have hz : V.starProjection (x i) = 0 :=
          (V.starProjection_apply_eq_zero_iff).mpr (hx i hi hwi)
        rw [map_smul, hQv, map_sub, hz, sub_zero]
    _ = V.starProjection z := by rw [← Finset.sum_smul, hw, one_smul]

end Submodule
