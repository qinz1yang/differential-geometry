import DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Submodule

variable {𝕜 H A : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H]

theorem finite_affine_family_normal_reduction
    (S : Finset A) (L : A → Submodule 𝕜 H) (x : A → H) (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1) {k : ℕ} (hdim : ∀ i ∈ S, Module.finrank 𝕜 (L i) ≤ k)
    (s : Set 𝕜) (hs : 1 ∈ s) (z : H) :
    let V := S.sup (fun i => 𝕜 ∙ x i ⊔ L i)
    let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
    Module.finrank 𝕜 V ≤ S.card * (k + 1) ∧
      Module.finrank 𝕜 (ContinuousLinearMap.id 𝕜 H - O).range ≤ S.card * k ∧
      Set.MapsTo O V V ∧ (∀ v ∈ Vᗮ, O v = v) ∧ (∀ v ∈ Vᗮ, Q v = v) ∧
      Vᗮ.starProjection (∑ i ∈ S, w i • Q (z - x i)) = Vᗮ.starProjection z := by
  classical
  let V := S.sup (fun i => 𝕜 ∙ x i ⊔ L i)
  let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
  have hL (i : A) (hi : i ∈ S) : L i ≤ V :=
    le_sup_right.trans (Finset.le_sup (f := fun i => 𝕜 ∙ x i ⊔ L i) hi)
  have hx (i : A) (hi : i ∈ S) : x i ∈ V :=
    (le_sup_left.trans (Finset.le_sup (f := fun i => 𝕜 ∙ x i ⊔ L i) hi) : 𝕜 ∙ x i ≤ V)
      (mem_span_singleton_self (x i))
  have hfix (v : H) (hv : v ∈ Vᗮ) : O v = v :=
    sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal V S L w hw
      (fun i hi _ => hL i hi) hv
  refine ⟨?_, ?_, sum_smul_starProjection_orthogonal_mapsTo V S L w (fun i hi _ => hL i hi),
    hfix, ?_, ?_⟩
  · apply (finrank_finset_sup_span_singleton_sup_le S L x).trans
    calc
      ∑ i ∈ S, (Module.finrank 𝕜 (L i) + 1) ≤ ∑ _i ∈ S, (k + 1) :=
        Finset.sum_le_sum (fun i hi => Nat.add_le_add_right (hdim i hi) 1)
      _ = S.card * (k + 1) := by simp
  · apply (ContinuousLinearMap.finrank_range_id_sub_sum_smul_starProjection_orthogonal_le S L w hw).trans
    calc
      ∑ i ∈ S, Module.finrank 𝕜 (L i) ≤ ∑ _i ∈ S, k := Finset.sum_le_sum hdim
      _ = S.card * k := by simp
  · intro v hv
    exact starProjection_eq_self_iff.mpr (le_iSup_eigenspace_of_fixed Vᗮ O.toLinearMap s hs hfix hv)
  · exact starProjection_weighted_normal_section Vᗮ S L x w hw
      (fun i hi _ => (hL i hi).trans V.le_orthogonal_orthogonal)
      (fun i hi _ => V.le_orthogonal_orthogonal (hx i hi)) s hs z

end Submodule
