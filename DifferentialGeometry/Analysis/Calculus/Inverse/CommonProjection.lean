import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

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

/-- The same prescribed projection gives disjoint smooth inverse germs at two
regular preimages with the same tangent plane. The ambient map and projection
in the conclusion are exactly those in the hypotheses. -/
theorem exists_disjoint_common_projection_inverse_germs
    {X : V → E} {s : Set V} (hs : IsOpen s)
    (hX : ContDiffOn ℝ ∞ X s) (P : E →L[ℝ] V)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hvalue : X a = X b)
    (hPa : (P.comp (fderiv ℝ X a)).IsInvertible)
    (hDb : Function.Injective (fderiv ℝ X b))
    (hrange : LinearMap.range (fderiv ℝ X b).toLinearMap ≤
      LinearMap.range (fderiv ℝ X a).toLinearMap) :
    ∃ e₁ e₂ : OpenPartialHomeomorph V V,
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s ∧ e₂.source ⊆ s ∧ Disjoint e₁.source e₂.source ∧
      (e₁ : V → V) = P ∘ X ∧ (e₂ : V → V) = P ∘ X ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      P (X a) ∈ e₁.target ∩ e₂.target := by
  have hPb := invertible_comp_of_range_le P _ _ hPa hDb hrange
  obtain ⟨A, B, hAo, hBo, haA, hbB, hAB⟩ := t2_separation hab
  let F : V → V := P ∘ X
  have hF : ContDiffOn ℝ ∞ F s := P.contDiff.comp_contDiffOn hX
  have hd (z : V) (hz : z ∈ s) :
      HasFDerivAt F (P.comp (fderiv ℝ X z)) z :=
    P.hasFDerivAt.comp z ((hX.contDiffAt (hs.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt
  obtain ⟨D₁, hD₁⟩ := hPa
  obtain ⟨D₂, hD₂⟩ := hPb
  obtain ⟨e₁, hae₁, he₁s, he₁, he₁i⟩ :=
    exists_smooth_localInverse (hs.inter hAo) (hF.mono inter_subset_left)
      ⟨ha, haA⟩ D₁ (by rw [hD₁]; exact hd a ha)
  obtain ⟨e₂, hbe₂, he₂s, he₂, he₂i⟩ :=
    exists_smooth_localInverse (hs.inter hBo) (hF.mono inter_subset_left)
      ⟨hb, hbB⟩ D₂ (by rw [hD₂]; exact hd b hb)
  refine ⟨e₁, e₂, hae₁, hbe₂,
    he₁s.trans inter_subset_left, he₂s.trans inter_subset_left,
    hAB.mono (he₁s.trans inter_subset_right) (he₂s.trans inter_subset_right),
    he₁, he₂, he₁i, he₂i, ?_, ?_⟩
  · change F a ∈ e₁.target
    rw [← he₁]
    exact e₁.map_source hae₁
  · rw [hvalue]
    change F b ∈ e₂.target
    rw [← he₂]
    exact e₂.map_source hbe₂

end DifferentialGeometry.Analysis
