import DifferentialGeometry.Analysis.InnerProductSpace.RealSpectralProjectionPerturbation
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionRankStability

set_option autoImplicit false
noncomputable section
open scoped TensorProduct Topology ContDiff
open Metric ContinuousLinearMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem ContDiffOn.real_starProjection_eigenspace_ball_of_norm_sub_le
    {f : E → H →L[ℝ] H} {s : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n f s) (hself : ∀ x ∈ s, (f x).toLinearMap.IsSymmetric)
    (P : Submodule ℝ H) (hclose : ∀ x ∈ s, ‖f x - P.starProjection‖ ≤ 1 / 4) :
    ContDiffOn ℝ n (fun x =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace (f x).toLinearMap μ).starProjection) s := by
  let F := (complexifyₗᵢ (H := H) (K := H)).toContinuousLinearMap
  let G := realPartOperator H H
  let fC : E → (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] H) := fun x => F (f x)
  have hfC : ContDiffOn ℝ n fC s := F.contDiff.comp_contDiffOn hf
  have hselfC (x : E) (hx : x ∈ s) : (fC x).toLinearMap.IsSymmetric :=
    (hself x hx).complexify
  have hc (x : E) (hx : x ∈ s) : sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ (fC x) := by
    intro z hz
    have hgap : 1 / 2 ≤ min ‖z‖ ‖z - 1‖ := by
      rw [mem_sphere, dist_eq_norm] at hz
      have hn := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one, norm_sub_rev, hz] at hn
      exact le_min (by linarith) hz.ge
    apply mem_resolventSet_of_norm_sub_starProjection_lt (fC x) (P.baseChange ℂ)
    have he : fC x - (P.baseChange ℂ).starProjection = F (f x - P.starProjection) := by
      rw [map_sub]
      exact congrArg (fun T => F (f x) - T) P.complexify_starProjection.symm
    rw [he]
    change ‖(f x - P.starProjection).complexify‖ < _
    rw [norm_complexify]
    exact (hclose x hx).trans_lt (lt_of_lt_of_le (by norm_num) hgap)
  have hq := hfC.starProjection_eigenspace_ball hselfC (by norm_num : (0 : ℝ) ≤ 1 / 2) hc
  apply (G.contDiff.comp_contDiffOn hq).congr
  intro x hx
  symm
  have hproj := (hself x hx).starProjection_eigenspace_ball_complexify 1 (1 / 2)
  simp only [Complex.ofReal_one] at hproj
  change realPartOperator H H
    (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (f x).complexify.toLinearMap μ).starProjection = _
  rw [← hproj, realPartOperator_complexify]

theorem norm_real_starProjection_eigenspace_ball_sub_le (A : H →L[ℝ] H)
    (hA : A.toLinearMap.IsSymmetric) (P : Submodule ℝ H)
    (hclose : ‖A - P.starProjection‖ ≤ 1 / 4) :
    ‖(⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace A.toLinearMap μ).starProjection -
      P.starProjection‖ ≤ 4 * ‖A - P.starProjection‖ := by
  have h := (contDiffOn_const : ContDiffOn ℝ (0 : ℕ) (fun _ : ℝ => A) Set.univ).norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sub_le isOpen_univ
      (fun _ _ => hA) P (norm_nonneg _) hclose (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ _ => le_rfl) (Set.mem_univ (0 : ℝ)) 0
      (fun j hj hj0 => by omega) 0 le_rfl
  simpa [norm_iteratedFDeriv_zero, resolventDerivativeBound] using h

theorem finrank_real_eigenspace_ball_eq_of_norm_sub_starProjection_lt (A : H →L[ℝ] H)
    (hA : A.toLinearMap.IsSymmetric) (P : Submodule ℝ H)
    (hclose : ‖A - P.starProjection‖ < 1 / 4) :
    Module.finrank ℝ (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace A.toLinearMap μ : Submodule ℝ H) =
      Module.finrank ℝ P := by
  apply Submodule.finrank_eq_of_norm_starProjection_sub_lt_one
  have h := norm_real_starProjection_eigenspace_ball_sub_le A hA P hclose.le
  linarith
