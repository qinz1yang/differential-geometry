import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold Topology

namespace Poincare.Geometry.VectorBundle

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

omit [CompleteSpace G] in
theorem contMDiffOn_clm_apply_iff [FiniteDimensional ℝ F]
    {A : M → F →L[ℝ] G} {U : Set M} :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] G) n A U ↔
      ∀ v, ContMDiffOn I 𝓘(ℝ, G) n (fun x ↦ A x v) U := by
  refine ⟨fun h v ↦ h.clm_apply contMDiffOn_const, fun h ↦ ?_⟩
  let d := Module.finrank ℝ F
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  have he : ContMDiffOn I 𝓘(ℝ, Fin d → G) n (fun x ↦ e₂ (A x)) U :=
    contMDiffOn_pi_space.mpr (fun i ↦ h (e₁.symm (Pi.single i 1)))
  exact (e₂.symm.contDiff.contMDiff.comp_contMDiffOn he).congr (fun x _ ↦ by simp)

theorem exists_contMDiffOn_rightInverse
    {A : M → F →L[ℝ] G} {U : Set M} {x₀ : M}
    (hA : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] G) n A U)
    (hU : U ∈ 𝓝 x₀) (hsplit : (A x₀).HasRightInverse) :
    ∃ V ∈ 𝓝 x₀, V ⊆ U ∧ ∃ R : M → G →L[ℝ] F,
      ContMDiffOn I 𝓘(ℝ, G →L[ℝ] F) n R V ∧
      ∀ x ∈ V, Function.RightInverse (R x) (A x) := by
  let R₀ := hsplit.rightInverse
  let B : M → G →L[ℝ] G := fun x ↦ (A x).comp R₀
  have hB : ContMDiffOn I 𝓘(ℝ, G →L[ℝ] G) n B U :=
    hA.clm_comp contMDiffOn_const
  have hB₀ : B x₀ = ContinuousLinearMap.id ℝ G := by
    ext v
    exact hsplit.rightInverse_rightInverse v
  have hopen : IsOpen {L : G →L[ℝ] G | L.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  have hnear : {x | (B x).IsInvertible} ∈ 𝓝 x₀ := by
    change B ⁻¹' {L : G →L[ℝ] G | L.IsInvertible} ∈ 𝓝 x₀
    apply (hB.continuousOn.continuousAt hU).preimage_mem_nhds
    apply hopen.mem_nhds
    rw [hB₀]
    exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
  refine ⟨U ∩ {x | (B x).IsInvertible}, Filter.inter_mem hU hnear,
    Set.inter_subset_left, (fun x ↦ R₀.comp (B x).inverse), ?_, ?_⟩
  · intro x hx
    exact contMDiffWithinAt_const.clm_comp
      (hx.2.contDiffAt_map_inverse.comp_contMDiffWithinAt
        ((hB x hx.1).mono Set.inter_subset_left))
  · intro x hx v
    exact hx.2.self_apply_inverse v

end Poincare.Geometry.VectorBundle
