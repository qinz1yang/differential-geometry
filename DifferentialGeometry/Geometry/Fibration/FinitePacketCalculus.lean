import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockDerivatives
import Mathlib.Analysis.Calculus.MeanValue

import DifferentialGeometry.Analysis.Calculus.ScaledCutoffBlock
import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockBounds
import DifferentialGeometry.Analysis.Calculus.FixedJointCutoffNetwork
import DifferentialGeometry.Analysis.Calculus.FreezeScale
import Mathlib.Analysis.Calculus.FDeriv.WithLp

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.Fibration

open DifferentialGeometry.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Orthogonal actual scaled blocks share a positive lower scale, without a large-scale loss. -/
theorem finite_scaled_packet_c1 {ι : Type*} [Fintype ι]
    (φ : ι → E → ℝ) (s : ι → ℝ) {s₀ C L₁ L₂ ε L : ℝ}
    (hs₀ : 0 < s₀) (hs : ∀ j, s₀ ≤ s j) (hC : 0 ≤ C)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hφ : ∀ j, ContDiff ℝ 2 (φ j)) (hvalue : ∀ j y, φ j y ∈ Icc 0 1)
    (hsupport : ∀ j, tsupport (φ j) ⊆ closedBall 0 C)
    (hfirst : ∀ j y, ‖fderiv ℝ (φ j) y‖ ≤ L₁)
    (hsecond : ∀ j y, ‖fderiv ℝ (fderiv ℝ (φ j)) y‖ ≤ L₂)
    (U V₀ : ι → V → E) (x : V)
    (hU : ∀ j, DifferentiableAt ℝ (U j) x)
    (hV : ∀ j, DifferentiableAt ℝ (V₀ j) x)
    (hclose : ∀ j, ‖U j x - V₀ j x‖ ≤ ε)
    (hDclose : ∀ j, ‖fderiv ℝ (U j) x - fderiv ℝ (V₀ j) x‖ ≤ ε)
    (hDV : ∀ j, ‖fderiv ℝ (V₀ j) x‖ ≤ L) :
    let F : V → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun y => WithLp.toLp 2 (fun j => scaledCutoffBlock (s j) (φ j) (U j y))
    let G : V → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun y => WithLp.toLp 2 (fun j => scaledCutoffBlock (s j) (φ j) (V₀ j y))
    max ‖F x - G x‖ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤
      Real.sqrt (Fintype.card ι) *
        ((1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s₀ * L) * ε) := by
  dsimp only
  let c := (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s₀ * L) * ε
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hblock (j : ι) := scaledCutoffBlock_c1_comp_sub_le (hφ j)
    (hs₀.trans_le (hs j)) hC hL₁ hL₂ (hvalue j) (hsupport j) (hfirst j) (hsecond j)
    (hU j) (hV j) hε hL (hclose j) (hDclose j) (hDV j)
  have hbound (j : ι) :
      (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s j * L) * ε ≤ c := by
    apply mul_le_mul_of_nonneg_right _ hε
    apply add_le_add_right _ _
    apply mul_le_mul_of_nonneg_right _ hL
    exact div_le_div_of_nonneg_left (by positivity) hs₀ (hs j)
  have hdiff (U₀ : ι → V → E) (hU₀ : ∀ j, DifferentiableAt ℝ (U₀ j) x) :
      DifferentiableAt ℝ (fun y => WithLp.toLp 2
        (fun j => scaledCutoffBlock (s j) (φ j) (U₀ j y))) x := by
    apply (differentiableAt_piLp 2).mpr
    intro j
    exact ((contDiff_scaledCutoffBlock (hφ j) (s j)).differentiable (by norm_num))
      |>.differentiableAt.comp x (hU₀ j)
  have h := c1_dist_le_of_blocks _ _ (hdiff U hU) (hdiff V₀ hV) hc
    (fun j => (le_max_left _ _).trans ((hblock j).trans (hbound j)))
    (fun j => (le_max_right _ _).trans ((hblock j).trans (hbound j)))
  exact max_le h.1 h.2

/-- Actual fixed KL profiles and the SAME coordinate maps on an entire tested source set. -/
theorem finite_joint_packet_c1_on {ι : Type*} [Fintype ι] {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (s : ι → ℝ) (hs : ∀ j, s j ∈ Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (U V₀ : V → E) (D : Set V) {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V₀ x)
    (hclose : ∀ x ∈ D, ‖U x - V₀ x‖ ≤ ε)
    (hDclose : ∀ x ∈ D, ‖fderiv ℝ U x - fderiv ℝ V₀ x‖ ≤ ε)
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V₀ x‖ ≤ L) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * edgeProfileDerivativeBound ^ 3
    let W := fixedJointCutoffNetwork Δ s u v
    ContDiff ℝ ∞ W ∧ ∀ x ∈ D,
      max ‖W (U x) - W (V₀ x)‖ ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V₀) x‖ ≤
        (Real.sqrt N * (2 + 20 * K) + (24 * Real.sqrt N * K / Δ) * L) * ε := by
  refine ⟨contDiff_fixedJointCutoffNetwork Δ s u v, ?_⟩
  intro x hx
  exact fixedJointCutoffNetwork_c1_comp_sub_le hΔ s hs u v hu hv (hU x hx) (hV x hx)
    hε hL (hclose x hx) (hDclose x hx) (hDV x hx)

/-- A normalized actual Lipschitz scale supplies both variable-scale error terms. -/
theorem finite_packet_freeze_actual_scale (ρ : V → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p x : V} (hp : ρ p = 1)
    {L Δ A C D₁ B : ℝ} (hx : x ∈ ball p L) (hsmall : L * Λ ≤ 1 / 2)
    (F : V → E) (u : V → ℝ) (hρd : DifferentiableAt ℝ ρ x)
    (hF : DifferentiableAt ℝ F x) (hu : DifferentiableAt ℝ u x)
    (hvalue : ‖F x‖ ≤ B * Δ) (hDF : ‖fderiv ℝ F x‖ ≤ A)
    (huvalue : |u x| ≤ C * Δ) (hDu : ‖fderiv ℝ u x‖ ≤ D₁) :
    |ρ x - 1| ≤ L * Λ ∧ ρ x ∈ Icc (1 / 2) (3 / 2) ∧
      max ‖ρ x • F x - F x‖ ‖fderiv ℝ (fun y => ρ y • F y) x - fderiv ℝ F x‖ ≤
        Λ * ((L + 1) * B * Δ + L * A) ∧
      max |u x / ρ x - u x| ‖fderiv ℝ (fun y => u y / ρ y) x - fderiv ℝ u x‖ ≤
        Λ * ((2 * L + 4) * C * Δ + 2 * L * D₁) := by
  have hclose : |ρ x - 1| ≤ L * Λ := by
    have hh := hρ.dist_le_mul x p
    rw [Real.dist_eq, hp] at hh
    exact hh.trans (by nlinarith [NNReal.coe_nonneg Λ, mem_ball.mp hx])
  have hd := norm_fderiv_le_of_lipschitz ℝ hρ (x₀ := x)
  refine ⟨hclose, ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [(abs_le.mp hclose).1]
  · linarith [(abs_le.mp hclose).2]
  · exact freeze_scale_product_c1_le hρd hF hclose hd hvalue hDF
  · exact freeze_scale_quotient_c1_le hρd hu hsmall hclose hd huvalue hDu

end DifferentialGeometry.Geometry.Fibration

namespace DifferentialGeometry.Geometry.Fibration

open DifferentialGeometry.Analysis
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

private theorem finite_packet_active_derivative_bounds {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) (s : Finset ι) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ i ∈ s, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ i ∈ s, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hfirstzero : ∀ i ∉ s, fderiv ℝ (f i) x = 0)
    (hsecondzero : ∀ i ∉ s, fderiv ℝ (fderiv ℝ (f i)) x = 0) :
    ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (s.card : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (s.card : ℝ) * B := by
  let W := orthogonalBlocks f
  have hW := contDiff_orthogonalBlocks hf
  have hWd := hW.differentiable (by norm_num)
  have hWdd : Differentiable ℝ (fderiv ℝ W) :=
    (hW.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  let P (i : ι) : PiLp 2 F →L[ℝ] F i :=
    (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ F).toContinuousLinearMap
  have hD (i : ι) : fderiv ℝ (f i) =
      (ContinuousLinearMap.compL ℝ E (PiLp 2 F) (F i) (P i)) ∘ fderiv ℝ W := by
    funext y
    exact ((P i).hasFDerivAt.comp y (hWd y).hasFDerivAt).fderiv
  have hfirsteq (i : ι) (v : E) : (fderiv ℝ W x v) i = fderiv ℝ (f i) x v := by
    rw [hD]
    rfl
  have hsecondeq (i : ι) (v w : E) :
      (fderiv ℝ (fderiv ℝ W) x v w) i = fderiv ℝ (fderiv ℝ (f i)) x v w := by
    rw [hD, fderiv_comp x (ContinuousLinearMap.compL ℝ E (PiLp 2 F) (F i) (P i)).differentiableAt
      (hWdd x), ContinuousLinearMap.fderiv]
    rfl
  constructor
  · apply (fderiv ℝ W x).norm_le_sqrt_active_blocks s hA
    · intro v i hi
      rw [hfirsteq]
      exact ((fderiv ℝ (f i) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hfirst i hi) (norm_nonneg v))
    · intro v i hi
      rw [hfirsteq, hfirstzero i hi]
      rfl
  · apply (fderiv ℝ (fderiv ℝ W) x).opNorm_le_bound (by positivity)
    intro v
    have h := (fderiv ℝ (fderiv ℝ W) x v).norm_le_sqrt_active_blocks s
      (B := B * ‖v‖) (by positivity)
      (fun w i hi => by
        rw [hsecondeq]
        exact ((fderiv ℝ (fderiv ℝ (f i)) x).le_opNorm₂ v w).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hsecond i hi) (norm_nonneg v)) (norm_nonneg w)))
      (fun w i hi => by rw [hsecondeq, hsecondzero i hi]; rfl)
    simpa only [mul_assoc] using h

private theorem finite_packet_active_derivative_modulus {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (D : Set E) (hD : Convex ℝ D)
    (active : E → Finset ι) {N : ℕ} (hcard : ∀ x ∈ D, (active x).card ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hfirstzero : ∀ x ∈ D, ∀ i ∉ active x, fderiv ℝ (f i) x = 0)
    (hsecondzero : ∀ x ∈ D, ∀ i ∉ active x, fderiv ℝ (fderiv ℝ (f i)) x = 0) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks f) y - fderiv ℝ (orthogonalBlocks f) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  have hb (x : E) (hx : x ∈ D) :
      ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B := by
    have h := finite_packet_active_derivative_bounds hf x (active x) hA hB
      (hfirst x hx) (hsecond x hx) (hfirstzero x hx) (hsecondzero x hx)
    have hr := Real.sqrt_le_sqrt (show ((active x).card : ℝ) ≤ N by exact_mod_cast hcard x hx)
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hr hA),
      h.2.trans (mul_le_mul_of_nonneg_right hr hB)⟩
  refine ⟨hb, ?_⟩
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((contDiff_orthogonalBlocks hf).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num) z)
    (fun z hz => (hb z hz).2) hD hx hy



/-- Actual locally zero blocks supply the sparse derivative and Hessian modulus. -/
theorem finite_packet_sparse_actual_modulus {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (D : Set E) (hD : Convex ℝ D)
    (active : E → Finset ι) {N : ℕ} (hcard : ∀ x ∈ D, (active x).card ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hzero : ∀ x ∈ D, ∀ i ∉ active x, f i =ᶠ[𝓝 x] 0) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks f) y - fderiv ℝ (orthogonalBlocks f) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  have hz₁ (x : E) (hx : x ∈ D) (i : ι) (hi : i ∉ active x) : fderiv ℝ (f i) x = 0 := by
    simpa using (hzero x hx i hi).fderiv_eq (𝕜 := ℝ)
  have hz₂ (x : E) (hx : x ∈ D) (i : ι) (hi : i ∉ active x) :
      fderiv ℝ (fderiv ℝ (f i)) x = 0 := by
    have h := ((hzero x hx i hi).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    simpa using h
  exact finite_packet_active_derivative_modulus hf D hD active hcard hA hB hfirst hsecond hz₁ hz₂

end DifferentialGeometry.Geometry.Fibration
