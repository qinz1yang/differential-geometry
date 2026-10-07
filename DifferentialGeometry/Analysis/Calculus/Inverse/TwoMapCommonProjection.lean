import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

-- Same range/projection argument as CommonProjection; the two source maps
-- below remain distinct throughout the construction.
private theorem invertible_comp_of_range_le
    (P : E →L[ℝ] V) (L₁ L₂ : V →L[ℝ] E)
    (h₁ : (P.comp L₁).IsInvertible) (h₂ : Function.Injective L₂)
    (hrange : LinearMap.range L₂.toLinearMap ≤ LinearMap.range L₁.toLinearMap) :
    (P.comp L₂).IsInvertible := by
  have hinj : Function.Injective (P.comp L₂) := by
    intro u v huv
    obtain ⟨u', hu'⟩ := hrange (LinearMap.mem_range_self L₂.toLinearMap u)
    obtain ⟨v', hv'⟩ := hrange (LinearMap.mem_range_self L₂.toLinearMap v)
    change L₁ u' = L₂ u at hu'
    change L₁ v' = L₂ v at hv'
    have heq : u' = v' := h₁.injective (by
      change P (L₁ u') = P (L₁ v')
      rw [hu', hv']
      exact huv)
    apply h₂
    rw [← hu', ← hv', heq]
  have hbij : Function.Bijective (P.comp L₂) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  let D : V ≃L[ℝ] V :=
    (LinearEquiv.ofBijective (P.comp L₂).toLinearMap hbij).toContinuousLinearEquiv
  refine ⟨D, ?_⟩
  ext z
  rfl

/-- Two distinct maps with the same tangent plane admit inverse graph germs
for the same prescribed projection. Each inverse is tied to its own original
map and open source domain. The two marked parameters may coincide. -/
theorem exists_two_map_common_projection_inverse_germs
    {X₁ X₂ : V → E} {s₁ s₂ : Set V}
    (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂)
    (hX₁ : ContDiffOn ℝ ∞ X₁ s₁) (hX₂ : ContDiffOn ℝ ∞ X₂ s₂)
    (P : E →L[ℝ] V) {a b : V} (ha : a ∈ s₁) (hb : b ∈ s₂)
    (hvalue : X₁ a = X₂ b)
    (hPa : (P.comp (fderiv ℝ X₁ a)).IsInvertible)
    (hDb : Function.Injective (fderiv ℝ X₂ b))
    (hrange : LinearMap.range (fderiv ℝ X₂ b).toLinearMap ≤
      LinearMap.range (fderiv ℝ X₁ a).toLinearMap) :
    ∃ e₁ e₂ : OpenPartialHomeomorph V V,
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s₁ ∧ e₂.source ⊆ s₂ ∧
      (e₁ : V → V) = P ∘ X₁ ∧ (e₂ : V → V) = P ∘ X₂ ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      P (X₁ a) ∈ e₁.target ∩ e₂.target := by
  have hPb := invertible_comp_of_range_le P _ _ hPa hDb hrange
  let F₁ : V → V := P ∘ X₁
  let F₂ : V → V := P ∘ X₂
  have hF₁ : ContDiffOn ℝ ∞ F₁ s₁ := P.contDiff.comp_contDiffOn hX₁
  have hF₂ : ContDiffOn ℝ ∞ F₂ s₂ := P.contDiff.comp_contDiffOn hX₂
  have hd₁ : HasFDerivAt F₁ (P.comp (fderiv ℝ X₁ a)) a :=
    P.hasFDerivAt.comp a ((hX₁.contDiffAt (hs₁.mem_nhds ha)).differentiableAt
      (by simp)).hasFDerivAt
  have hd₂ : HasFDerivAt F₂ (P.comp (fderiv ℝ X₂ b)) b :=
    P.hasFDerivAt.comp b ((hX₂.contDiffAt (hs₂.mem_nhds hb)).differentiableAt
      (by simp)).hasFDerivAt
  obtain ⟨D₁, hD₁⟩ := hPa
  obtain ⟨D₂, hD₂⟩ := hPb
  obtain ⟨e₁, hae₁, he₁s, he₁, he₁i⟩ :=
    exists_smooth_localInverse hs₁ hF₁ ha D₁ (by rw [hD₁]; exact hd₁)
  obtain ⟨e₂, hbe₂, he₂s, he₂, he₂i⟩ :=
    exists_smooth_localInverse hs₂ hF₂ hb D₂ (by rw [hD₂]; exact hd₂)
  refine ⟨e₁, e₂, hae₁, hbe₂, he₁s, he₂s, he₁, he₂, he₁i, he₂i, ?_, ?_⟩
  · change F₁ a ∈ e₁.target
    rw [← he₁]
    exact e₁.map_source hae₁
  · rw [hvalue]
    change F₂ b ∈ e₂.target
    rw [← he₂]
    exact e₂.map_source hbe₂

end DifferentialGeometry.Analysis
