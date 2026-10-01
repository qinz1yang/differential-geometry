import DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Metric

namespace Submodule

open Classical in
theorem localized_weighted_normal_spectral_section
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (S : Finset ι) (U : Set H) (w : ι → H → ℝ)
    (hw : ∀ z ∈ U, ∑ i ∈ S, w i z = 1)
    (L : ι → Submodule ℝ H) (c : ι → H) (o : H) :
    let J : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
    let V : Submodule ℝ H := J.sup (fun i => (ℝ ∙ (c i - o)) ⊔ L i)
    let Q : H → H →L[ℝ] H := fun z =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i z • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
    Module.finrank ℝ V ≤ ∑ i ∈ J, (Module.finrank ℝ (L i) + 1) ∧
      ∀ z ∈ U,
        (∀ v ∈ Vᗮ, Q z v = v) ∧
        Vᗮ.starProjection (Q z (z - ∑ i ∈ S, w i z • c i)) =
          Vᗮ.starProjection (z - o) := by
  dsimp only
  let J : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
  let V : Submodule ℝ H := J.sup (fun i => (ℝ ∙ (c i - o)) ⊔ L i)
  let O : H → H →L[ℝ] H := fun z => ∑ i ∈ S, w i z • (L i)ᗮ.starProjection
  let Q : H → H →L[ℝ] H := fun z =>
    (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace (O z).toLinearMap μ).starProjection
  have hdim : Module.finrank ℝ V ≤ ∑ i ∈ J, (Module.finrank ℝ (L i) + 1) :=
    finrank_finset_sup_span_singleton_sup_le J L (fun i => c i - o)
  refine ⟨hdim, ?_⟩
  have hL (i : ι) (hi : i ∈ J) : L i ≤ V :=
    le_sup_right.trans (Finset.le_sup (f := fun j => (ℝ ∙ (c j - o)) ⊔ L j) hi)
  have hc (i : ι) (hi : i ∈ J) : c i - o ∈ V := by
    have hspan : (ℝ ∙ (c i - o)) ≤ V :=
      le_sup_left.trans (Finset.le_sup (f := fun j => (ℝ ∙ (c j - o)) ⊔ L j) hi)
    exact hspan (mem_span_singleton_self _)
  intro z hz
  have hactive (i : ι) (hi : i ∈ S) (hne : w i z ≠ 0) : i ∈ J :=
    Finset.mem_filter.mpr ⟨hi, z, hz, hne⟩
  have hfix (v : H) (hv : v ∈ Vᗮ) : O z v = v :=
    sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal V S L (fun i => w i z)
      (hw z hz) (fun i hi hne => hL i (hactive i hi hne)) hv
  have hone : (1 : ℝ) ∈ ball (1 : ℝ) (1 / 2) := by
    rw [mem_ball, dist_self]
    norm_num
  have hQfix (v : H) (hv : v ∈ Vᗮ) : Q z v = v := by
    apply starProjection_eq_self_iff.mpr
    exact le_iSup_eigenspace_of_fixed Vᗮ (O z).toLinearMap
      (ball (1 : ℝ) (1 / 2)) hone hfix hv
  refine ⟨hQfix, ?_⟩
  have hcomp : Vᗮ.starProjection.comp (Q z) = Vᗮ.starProjection :=
    starProjection_eigenspace_iSup_of_fixed Vᗮ (O z)
      (ball (1 : ℝ) (1 / 2)) hone hfix
  have hQproject (v : H) : Vᗮ.starProjection (Q z v) = Vᗮ.starProjection v :=
    congrArg (fun A : H →L[ℝ] H => A v) hcomp
  have hrelative : (∑ i ∈ S, w i z • (c i - o)) =
      (∑ i ∈ S, w i z • c i) - o := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw z hz, one_smul]
  have hrelative_mem : (∑ i ∈ S, w i z • (c i - o)) ∈ V := by
    apply V.sum_mem
    intro i hi
    by_cases hzero : w i z = 0
    · rw [hzero, zero_smul]
      exact V.zero_mem
    · exact V.smul_mem _ (hc i (hactive i hi hzero))
  have hproject_zero : Vᗮ.starProjection (∑ i ∈ S, w i z • (c i - o)) = 0 :=
    (Vᗮ.starProjection_apply_eq_zero_iff).mpr (V.le_orthogonal_orthogonal hrelative_mem)
  have hargs : z - (∑ i ∈ S, w i z • c i) =
      (z - o) - ∑ i ∈ S, w i z • (c i - o) := by
    rw [hrelative]
    abel
  change Vᗮ.starProjection (Q z (z - ∑ i ∈ S, w i z • c i)) = _
  rw [hQproject, hargs, map_sub, hproject_zero, sub_zero]

end Submodule
