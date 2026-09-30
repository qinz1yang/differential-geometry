import DifferentialGeometry.Tensor.LinearAlgebra.Dimension.FiniteSup
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ContinuousLinearMap

variable {𝕜 H A : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem range_id_sub_sum_smul_starProjection_orthogonal_le
    (S : Finset A) (L : A → Submodule 𝕜 H)
    [∀ i, FiniteDimensional 𝕜 (L i)] (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1) :
    (ContinuousLinearMap.id 𝕜 H - ∑ i ∈ S, w i • (L i)ᗮ.starProjection).range ≤ S.sup L := by
  classical
  rintro _ ⟨v, rfl⟩
  have hid : (ContinuousLinearMap.id 𝕜 H - ∑ i ∈ S, w i • (L i)ᗮ.starProjection) v =
      ∑ i ∈ S, w i • (L i).starProjection v := by
    simp only [sub_apply, id_apply, sum_apply, smul_apply, Submodule.starProjection_orthogonal_val,
      smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul, sub_sub_cancel]
  simp only [ContinuousLinearMap.coe_coe, hid]
  apply Submodule.sum_mem
  intro i hi
  exact (S.sup L).smul_mem (w i) ((Finset.le_sup (f := L) hi : L i ≤ S.sup L) ((L i).starProjection_apply_mem v))

theorem finrank_range_id_sub_sum_smul_starProjection_orthogonal_le
    (S : Finset A) (L : A → Submodule 𝕜 H)
    [∀ i, FiniteDimensional 𝕜 (L i)] (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1) :
    Module.finrank 𝕜
      (ContinuousLinearMap.id 𝕜 H - ∑ i ∈ S, w i • (L i)ᗮ.starProjection).range ≤
        ∑ i ∈ S, Module.finrank 𝕜 (L i) := by
  exact (Submodule.finrank_mono (range_id_sub_sum_smul_starProjection_orthogonal_le S L w hw)).trans
    (Submodule.finrank_finset_sup_le_sum S L)

end ContinuousLinearMap

namespace Submodule

variable {𝕜 H A : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem sum_smul_starProjection_orthogonal_mapsTo
    (V : Submodule 𝕜 H) (S : Finset A) (L : A → Submodule 𝕜 H)
    [∀ i, FiniteDimensional 𝕜 (L i)] (w : A → 𝕜)
    (hL : ∀ i ∈ S, w i ≠ 0 → L i ≤ V) :
    Set.MapsTo (∑ i ∈ S, w i • (L i)ᗮ.starProjection : H →L[𝕜] H) V V := by
  intro v hv
  simp only [sum_apply, smul_apply, starProjection_orthogonal_val]
  apply V.sum_mem
  intro i hi
  by_cases hwi : w i = 0
  · simp only [hwi, zero_smul]
    exact V.zero_mem
  · exact V.smul_mem _ (V.sub_mem hv (hL i hi hwi ((L i).starProjection_apply_mem v)))

theorem sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal
    (V : Submodule 𝕜 H) (S : Finset A) (L : A → Submodule 𝕜 H)
    [∀ i, FiniteDimensional 𝕜 (L i)] (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1) (hL : ∀ i ∈ S, w i ≠ 0 → L i ≤ V)
    {v : H} (hv : v ∈ Vᗮ) :
    (∑ i ∈ S, w i • (L i)ᗮ.starProjection : H →L[𝕜] H) v = v := by
  classical
  simp only [sum_apply, smul_apply]
  calc
    ∑ i ∈ S, w i • (L i)ᗮ.starProjection v = ∑ i ∈ S, w i • v := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, zero_smul]
      · rw [starProjection_eq_self_iff.mpr (orthogonal_le (hL i hi hwi) hv)]
    _ = v := by rw [← Finset.sum_smul, hw, one_smul]

end Submodule
