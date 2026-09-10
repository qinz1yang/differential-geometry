import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientGlobalSection
import DifferentialGeometry.Geometry.Metric.Basic

noncomputable section
open scoped ContDiff Manifold
open Bundle
open DifferentialGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

namespace Poincare.Geometry.Gradient

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

def normalizedGradient (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : M) : TangentSpace I x :=
  (g.inner x (gradFun g f x) (gradFun g f x))⁻¹ • gradFun g f x

private theorem grad_ne_zero (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    {x : M} (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) : gradFun g f x ≠ 0 := by
  intro hzero
  apply hreg
  ext v
  rw [← inner_gradFun g f x v, hzero]
  simp only [map_zero, zero_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_normalizedGradient (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : M) (hreg : mfderiv I 𝓘(ℝ) f x ≠ 0) :
    mfderiv I 𝓘(ℝ) f x (normalizedGradient g f x) = (1 : ℝ) := by
  have hpos := g.pos x _ (grad_ne_zero g f hreg)
  rw [normalizedGradient, map_smul, ← inner_gradFun]
  exact inv_mul_cancel₀ hpos.ne'

theorem contMDiff_normalizedGradient (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : ∀ x, mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, normalizedGradient g f x⟩ : TangentBundle I M)) := by
  have hgrad := WithBoundary.gradFun_contMDiff_total g hf
  have h1 := ContMDiff.clm_bundle_apply (b := id)
    (E₁ := TangentSpace I) (E₂ := fun x ↦ TangentSpace I x →L[ℝ] ℝ)
    (ϕ := g.inner) (v := gradFun g f) g.contMDiff hgrad
  have h2 := ContMDiff.clm_bundle_apply (b := id)
    (E₁ := TangentSpace I) (E₂ := fun _ : M ↦ ℝ)
    (ϕ := fun x ↦ g.inner x (gradFun g f x)) (v := gradFun g f) h1 hgrad
  have hn : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ g.inner x (gradFun g f x) (gradFun g f x)) := by
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (h2 x)
  exact (hn.inv₀ (fun x ↦ (g.pos x _ (grad_ne_zero g f (hreg x))).ne')).smul_section hgrad

end Poincare.Geometry.Gradient
