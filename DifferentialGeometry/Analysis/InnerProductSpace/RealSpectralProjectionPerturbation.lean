import DifferentialGeometry.Analysis.InnerProductSpace.ComplexificationRealPart
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralComplexification
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionPerturbation

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

open Metric ContinuousLinearMap
open scoped NNReal Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem ContDiffOn.norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sub_le
    {U : Set E} (hU : IsOpen U) {f : E → H →L[ℝ] H} {m : ℕ}
    (hf : ContDiffOn ℝ m f U) (hself : ∀ y ∈ U, (f y).toLinearMap.IsSymmetric)
    (P : Submodule ℝ H) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4) (hσ : 0 ≤ σ)
    (hclose : ∀ y ∈ U, ‖f y - P.starProjection‖ ≤ δ) {x : E} (hx : x ∈ U)
    (B : ℝ≥0) (hD : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ δ * B * σ ^ j) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace (f y).toLinearMap μ).starProjection -
          P.starProjection) x‖ ≤
        max 4 ((resolventDerivativeBound 4 B n : ℝ) / 2) * δ * σ ^ n := by
  let F := (complexifyₗᵢ (H := H) (K := H)).toContinuousLinearMap
  let G := realPartOperator H H
  let fC : E → (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] H) := fun y => F (f y)
  have hF : ‖F‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  have hG : ‖G‖ ≤ 1 := norm_realPartOperator_le H H
  have hfC : ContDiffOn ℝ m fC U := F.contDiff.comp_contDiffOn hf
  have hselfC (y : E) (hy : y ∈ U) : (fC y).toLinearMap.IsSymmetric :=
    (hself y hy).complexify
  have hcloseC (y : E) (hy : y ∈ U) :
      ‖fC y - (P.baseChange ℂ).starProjection‖ ≤ δ := by
    have he : fC y - (P.baseChange ℂ).starProjection = F (f y - P.starProjection) := by
      rw [map_sub]
      exact congrArg (fun T => F (f y) - T) P.complexify_starProjection.symm
    rw [he]
    change ‖(f y - P.starProjection).complexify‖ ≤ δ
    rw [norm_complexify]
    exact hclose y hy
  have hDC (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j fC x‖ ≤ δ * B * σ ^ j := by
    have hh := F.norm_iteratedFDeriv_comp_left
      ((hf x hx).contDiffAt (hU.mem_nhds hx)) (by exact_mod_cast hjm)
    apply hh.trans
    exact ((mul_le_mul_of_nonneg_right hF (norm_nonneg _)).trans_eq (one_mul _)).trans
      (hD j hj hjm)
  have hc (y : E) (hy : y ∈ U) :
      sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ (fC y) := by
    intro z hz
    have hgap : 1 / 2 ≤ min ‖z‖ ‖z - 1‖ := by
      rw [mem_sphere, dist_eq_norm] at hz
      have hn := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one, norm_sub_rev, hz] at hn
      exact le_min (by linarith) hz.ge
    exact mem_resolventSet_of_norm_sub_starProjection_lt (fC y) (P.baseChange ℂ)
      ((hcloseC y hy).trans_lt (hδsmall.trans_lt (lt_of_lt_of_le (by norm_num) hgap)))
  let qC : E → (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] H) := fun y =>
    (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (fC y).toLinearMap μ).starProjection -
      (P.baseChange ℂ).starProjection
  have hqC : ContDiffOn ℝ m qC U :=
    (hfC.starProjection_eigenspace_ball hselfC (by norm_num) hc).sub contDiffOn_const
  have heq : (fun y =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace (f y).toLinearMap μ).starProjection -
        P.starProjection) =ᶠ[𝓝 x] G ∘ qC := by
    filter_upwards [hU.mem_nhds hx] with y hy
    dsimp only [Function.comp_def, G, qC]
    rw [map_sub]
    change _ = realPartOperator H H
      (⨆ μ ∈ ball (1 : ℂ) (1 / 2),
        Module.End.eigenspace (f y).complexify.toLinearMap μ).starProjection -
          realPartOperator H H (P.baseChange ℂ).starProjection
    have hproj := (hself y hy).starProjection_eigenspace_ball_complexify 1 (1 / 2)
    simp only [Complex.ofReal_one] at hproj
    rw [← hproj, ← P.complexify_starProjection, realPartOperator_complexify,
      realPartOperator_complexify]
  intro n hnm
  rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
  have hh := G.norm_iteratedFDeriv_comp_left
    ((hqC x hx).contDiffAt (hU.mem_nhds hx)) (by exact_mod_cast hnm)
  apply hh.trans
  apply ((mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans_eq (one_mul _)).trans
  exact hfC.norm_iteratedFDeriv_starProjection_eigenspace_ball_sub_le
    hU hselfC (P.baseChange ℂ) hδ hδsmall hσ hcloseC hx B hDC n hnm

theorem norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le
    {ι : Type*} (S : Finset ι) {U : Set E} (hU : IsOpen U) {w : ι → E → ℝ} {m : ℕ}
    (hw : ∀ i ∈ S, ContDiffOn ℝ m (w i) U)
    (hw0 : ∀ y ∈ U, ∀ i ∈ S, 0 ≤ w i y) (hw1 : ∀ y ∈ U, ∑ i ∈ S, w i y = 1)
    (A : ι → H →L[ℝ] H) (hA : ∀ i ∈ S, (A i).toLinearMap.IsSymmetric)
    (P : Submodule ℝ H) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4) (hσ : 0 ≤ σ)
    (hclose : ∀ i ∈ S, ‖A i - P.starProjection‖ ≤ δ) {x : E} (hx : x ∈ U) (B : ℝ≥0)
    (hD : ∀ j, 1 ≤ j → j ≤ m → (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * σ ^ j) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
          Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ).starProjection -
            P.starProjection) x‖ ≤
        max 4 ((resolventDerivativeBound 4 B n : ℝ) / 2) * δ * σ ^ n := by
  classical
  let f : E → H →L[ℝ] H := fun y => ∑ i ∈ S, w i y • A i
  have hf : ContDiffOn ℝ m f U := ContDiffOn.sum (fun i hi => (hw i hi).smul_const (A i))
  have hself (y : E) (_hy : y ∈ U) : (f y).toLinearMap.IsSymmetric := by
    intro u v
    change inner ℝ (f y u) v = inner ℝ u (f y v)
    simp only [f, sum_apply, smul_apply, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, real_inner_smul_right, (hA i hi).apply_clm]
  have hdiff (y : E) (hy : y ∈ U) : f y - P.starProjection =
      ∑ i ∈ S, w i y • (A i - P.starProjection) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1 y hy, one_smul, f]
  have hfc (y : E) (hy : y ∈ U) : ‖f y - P.starProjection‖ ≤ δ := by
    rw [hdiff y hy]
    exact norm_sum_smul_le (hw0 y hy) (hw1 y hy) hclose
  have hfd (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ δ * B * σ ^ j := by
    have hfx : ContDiffAt ℝ j f x :=
      ((hf x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm)
    have heq : iteratedFDeriv ℝ j (fun y => f y - P.starProjection) x =
        iteratedFDeriv ℝ j f x := by
      rw [fun_iteratedFDeriv_sub_apply hfx contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    rw [← heq]
    have h := norm_iteratedFDeriv_sum_smul_sub_le (𝕜 := ℝ) (w := w) (n := j) (x := x) S A P.starProjection
      (fun i hi => (((hw i hi) x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm))
      (Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hw1 y hy))
    apply h.trans
    calc
      _ ≤ ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hclose i hi) (norm_nonneg _)
      _ = (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) * δ := (Finset.sum_mul _ _ _).symm
      _ ≤ (B * σ ^ j) * δ := mul_le_mul_of_nonneg_right (hD j hj hjm) hδ
      _ = δ * B * σ ^ j := by ring
  exact hf.norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sub_le
    hU hself P hδ hδsmall hσ hfc hx B hfd
