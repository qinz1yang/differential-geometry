import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockBounds
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import DifferentialGeometry.Analysis.Calculus.ScaledCutoffBlock
import DifferentialGeometry.Analysis.Calculus.FixedJointCutoffNetwork
import DifferentialGeometry.Analysis.Calculus.NormalizedScale
import DifferentialGeometry.Analysis.Calculus.FreezeScale

set_option autoImplicit false
open Set Metric

namespace DifferentialGeometry.Analysis.X81Sol

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem normalized_scale_freeze_product {ρ : E → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (p : E) (hp : 0 < ρ p) {L : ℝ}
    (hsmall : L * Λ ≤ 1 / 2) {F : E → H} {x : E}
    (hx : x ∈ closedBall (0 : E) L)
    (hσ : DifferentiableAt ℝ (fun y => ρ (p + ρ p • y) / ρ p) x)
    (hF : DifferentiableAt ℝ F x) {V Δ A : ℝ}
    (hvalue : ‖F x‖ ≤ V * Δ) (hDF : ‖fderiv ℝ F x‖ ≤ A) :
    let σ : E → ℝ := fun y => ρ (p + ρ p • y) / ρ p
    σ x ∈ Icc (1 / 2) (3 / 2) ∧
      max ‖σ x • F x - F x‖ ‖fderiv ℝ (fun y => σ y • F y) x - fderiv ℝ F x‖ ≤
        Λ * ((L + 1) * V * Δ + L * A) := by
  have h := (normalized_scale_in_affine_coordinates hρ p hp hsmall).2.2 x hx
  exact ⟨h.2.2, freeze_scale_product_c1_le hσ hF h.1 h.2.1 hvalue hDF⟩

theorem normalized_scale_freeze_quotient {ρ : E → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (p : E) (hp : 0 < ρ p) {L : ℝ}
    (hsmall : L * Λ ≤ 1 / 2) {u : E → ℝ} {x : E}
    (hx : x ∈ closedBall (0 : E) L)
    (hσ : DifferentiableAt ℝ (fun y => ρ (p + ρ p • y) / ρ p) x)
    (hu : DifferentiableAt ℝ u x) {C Δ D : ℝ}
    (hvalue : |u x| ≤ C * Δ) (hDu : ‖fderiv ℝ u x‖ ≤ D) :
    let σ : E → ℝ := fun y => ρ (p + ρ p • y) / ρ p
    max |u x / σ x - u x| ‖fderiv ℝ (fun y => u y / σ y) x - fderiv ℝ u x‖ ≤
      Λ * ((2 * L + 4) * C * Δ + 2 * L * D) := by
  have h := (normalized_scale_in_affine_coordinates hρ p hp hsmall).2.2 x hx
  exact freeze_scale_quotient_c1_le hσ hu hsmall h.1 h.2.1 hvalue hDu

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem scaledCutoffBlock_domain_c1_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {s C L₁ L₂ : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hvalue : ∀ y, φ y ∈ Icc 0 1) (hsupport : tsupport φ ⊆ closedBall 0 C)
    (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ L₁)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ L₂)
    (D : Set X) {U V : X → E} (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V x) {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hclose : ∀ x ∈ D, ‖U x - V x‖ ≤ ε)
    (hDclose : ∀ x ∈ D, ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V x‖ ≤ L) :
    ∀ x ∈ D, max ‖scaledCutoffBlock s φ (U x) - scaledCutoffBlock s φ (V x)‖
      ‖fderiv ℝ (scaledCutoffBlock s φ ∘ U) x - fderiv ℝ (scaledCutoffBlock s φ ∘ V) x‖ ≤
        (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε := by
  intro x hx
  exact scaledCutoffBlock_c1_comp_sub_le hφ hs hC hL₁ hL₂ hvalue hsupport hfirst hsecond
    (hU x hx) (hV x hx) hε hL (hclose x hx) (hDclose x hx) (hDV x hx)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem fixedJointCutoffNetwork_domain_c1_le {ι : Type*} [Fintype ι] {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (s : ι → ℝ) (hs : ∀ i, s i ∈ Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V : X → E} (D : Set X)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x) (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    {ε L₀ : ℝ} (hε : 0 ≤ ε) (hL₀ : 0 ≤ L₀)
    (hclose : ∀ x ∈ D, ‖U x - V x‖ ≤ ε) (hDclose : ∀ x ∈ D, ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V x‖ ≤ L₀) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * edgeProfileDerivativeBound ^ 3
    let W := fixedJointCutoffNetwork Δ s u v
    ∀ x ∈ D, max ‖W (U x) - W (V x)‖ ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤
      (Real.sqrt N * (2 + 20 * K) + (24 * Real.sqrt N * K / Δ) * L₀) * ε := by
  dsimp only
  intro x hx
  exact fixedJointCutoffNetwork_c1_comp_sub_le hΔ s hs u v hu hv
    (hU x hx) (hV x hx) hε hL₀ (hclose x hx) (hDclose x hx) (hDV x hx)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem finite_scaledCutoffBlock_domain_c1_le {ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {s C L₁ L₂ : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hvalue : ∀ y, φ y ∈ Icc 0 1) (hsupport : tsupport φ ⊆ closedBall 0 C)
    (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ L₁)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ L₂)
    (D : Set X) (U V : ι → X → E) (hU : ∀ i x, x ∈ D → DifferentiableAt ℝ (U i) x)
    (hV : ∀ i x, x ∈ D → DifferentiableAt ℝ (V i) x)
    {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hclose : ∀ i x, x ∈ D → ‖U i x - V i x‖ ≤ ε)
    (hDclose : ∀ i x, x ∈ D → ‖fderiv ℝ (U i) x - fderiv ℝ (V i) x‖ ≤ ε)
    (hDV : ∀ i x, x ∈ D → ‖fderiv ℝ (V i) x‖ ≤ L) :
    let F : X → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun x => WithLp.toLp 2 (fun i => scaledCutoffBlock s φ (U i x))
    let G : X → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun x => WithLp.toLp 2 (fun i => scaledCutoffBlock s φ (V i x))
    ∀ x ∈ D, max ‖F x - G x‖ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤
      Real.sqrt (Fintype.card ι : ℝ) *
        ((1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε) := by
  dsimp only
  intro x hx
  have hc : 0 ≤ (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε := by positivity
  have hblock i := scaledCutoffBlock_domain_c1_le hφ hs hC hL₁ hL₂ hvalue hsupport hfirst hsecond D
    (hU i) (hV i) hε hL (hclose i) (hDclose i) (hDV i) x hx
  have hFu : DifferentiableAt ℝ
      (fun y : X => (WithLp.toLp 2 (fun i => scaledCutoffBlock s φ (U i y)) :
        PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)))) x := (differentiableAt_piLp 2).mpr (fun i =>
    ((contDiff_scaledCutoffBlock hφ s).differentiable (by norm_num)).differentiableAt.comp x (hU i x hx))
  have hGv : DifferentiableAt ℝ
      (fun y : X => (WithLp.toLp 2 (fun i => scaledCutoffBlock s φ (V i y)) :
        PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)))) x := (differentiableAt_piLp 2).mpr (fun i =>
    ((contDiff_scaledCutoffBlock hφ s).differentiable (by norm_num)).differentiableAt.comp x (hV i x hx))
  have h := c1_dist_le_of_blocks _ _ hFu hGv hc
    (fun i => (le_max_left _ _).trans (hblock i))
    (fun i => (le_max_right _ _).trans (hblock i))
  exact max_le h.1 h.2

end DifferentialGeometry.Analysis.X81Sol
