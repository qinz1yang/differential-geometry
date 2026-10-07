import DifferentialGeometry.Analysis.Calculus.LineDeriv
import DifferentialGeometry.Topology.Algebra.Module.AffineLimit
import DifferentialGeometry.Geometry.Affine.PlaneRigidity

open scoped Topology

namespace DifferentialGeometry.Geometry.Affine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactPair E F]

theorem exists_affineEquiv_of_homothety_limits
    (hF : Module.finrank ℝ F = 2)
    (h₀ : E → F) (h₁ h₂ h₃ h₄ : C(E, F))
    (z₁ w₁ z₂ w₂ : E)
    (s₁ s₂ s₃ s₄ : ℕ → ℝ)
    (f₁ f₂ f₃ f₄ : ℕ → C(E, F))
    (hs₁ : Filter.Tendsto s₁ Filter.atTop Filter.atTop)
    (hs₂ : Filter.Tendsto s₂ Filter.atTop Filter.atTop)
    (hs₃ : Filter.Tendsto s₃ Filter.atTop Filter.atTop)
    (hs₄ : Filter.Tendsto s₄ Filter.atTop Filter.atTop)
    (hdense₁ : Dense {v : E | LineDifferentiableAt ℝ h₀ z₁ v})
    (hdense₃ : Dense {v : E | LineDifferentiableAt ℝ (h₂ : E → F) z₂ v})
    (hzoom₁ : ∀ (n : ℕ) (x : E),
      f₁ n x = h₀ z₁ + s₁ n • (h₀ (z₁ + (s₁ n)⁻¹ • (x - z₁)) - h₀ z₁))
    (hzoom₂ : ∀ (n : ℕ) (x : E),
      f₂ n x = h₁ w₁ + s₂ n • (h₁ (w₁ + (s₂ n)⁻¹ • (x - w₁)) - h₁ w₁))
    (hzoom₃ : ∀ (n : ℕ) (x : E),
      f₃ n x = h₂ z₂ + s₃ n • (h₂ (z₂ + (s₃ n)⁻¹ • (x - z₂)) - h₂ z₂))
    (hzoom₄ : ∀ (n : ℕ) (x : E),
      f₄ n x = h₃ w₂ + s₄ n • (h₃ (w₂ + (s₄ n)⁻¹ • (x - w₂)) - h₃ w₂))
    (hlim₁ : Filter.Tendsto f₁ Filter.atTop (𝓝 h₁))
    (hlim₂ : Filter.Tendsto f₂ Filter.atTop (𝓝 h₂))
    (hlim₃ : Filter.Tendsto f₃ Filter.atTop (𝓝 h₃))
    (hlim₄ : Filter.Tendsto f₄ Filter.atTop (𝓝 h₄))
    (hind : LinearIndependent ℝ ![w₁ - z₁, w₂ - z₂])
    (hinj : Function.Injective h₄) :
    ∃ A : E ≃ᵃ[ℝ] F, ∀ x, A x = h₄ x := by
  have hpoint₁ (x : E) : Filter.Tendsto
      (fun n => h₀ z₁ + s₁ n • (h₀ (z₁ + (s₁ n)⁻¹ • (x - z₁)) - h₀ z₁))
      Filter.atTop (𝓝 (h₁ x)) :=
    (hlim₁.eval_const x).congr' (Filter.Eventually.of_forall (fun n => hzoom₁ n x))
  have hradial₁ := h₁.continuous.homothety_limit_eq_add_smul
    (h := h₀) (z := z₁) s₁ hs₁ hdense₁ hpoint₁
  have hcenter₁ : h₁ z₁ = h₀ z₁ := by
    simpa only [zero_smul, add_zero] using hradial₁ (0 : E) 0
  have hpencil₁ (v : E) (t : ℝ) :
      h₁ (z₁ + t • v) = h₁ z₁ + t • (h₁ (z₁ + v) - h₁ z₁) := by
    rw [hcenter₁]
    exact hradial₁ v t
  have hparallel₂ := ContinuousMap.map_add_smul_eq_of_tendsto_homothety
    h₁ z₁ w₁ s₂ hpencil₁ hs₂ hzoom₂ hlim₂
  have hparallel₃ := ContinuousMap.affine_direction_of_tendsto_homothety
    (h₂ : E → F) z₂ (w₁ - z₁) s₃ hparallel₂ hzoom₃ hlim₃
  have hpoint₃ (x : E) : Filter.Tendsto
      (fun n => h₂ z₂ + s₃ n • (h₂ (z₂ + (s₃ n)⁻¹ • (x - z₂)) - h₂ z₂))
      Filter.atTop (𝓝 (h₃ x)) :=
    (hlim₃.eval_const x).congr' (Filter.Eventually.of_forall (fun n => hzoom₃ n x))
  have hradial₃ := h₃.continuous.homothety_limit_eq_add_smul
    (h := (h₂ : E → F)) (z := z₂) s₃ hs₃ hdense₃ hpoint₃
  have hcenter₃ : h₃ z₂ = h₂ z₂ := by
    simpa only [zero_smul, add_zero] using hradial₃ (0 : E) 0
  have hpencil₃ (v : E) (t : ℝ) :
      h₃ (z₂ + t • v) = h₃ z₂ + t • (h₃ (z₂ + v) - h₃ z₂) := by
    rw [hcenter₃]
    exact hradial₃ v t
  have hparallel₄_first := ContinuousMap.affine_direction_of_tendsto_homothety
    (h₃ : E → F) w₂ (w₁ - z₁) s₄ hparallel₃ hzoom₄ hlim₄
  have hparallel₄_second := ContinuousMap.map_add_smul_eq_of_tendsto_homothety
    h₃ z₂ w₂ s₄ hpencil₃ hs₄ hzoom₄ hlim₄
  exact exists_affineEquiv_of_injective_of_two_directions hF
    (h₄ : E → F) hinj (w₁ - z₁) (w₂ - z₂) hind
    hparallel₄_first hparallel₄_second

end DifferentialGeometry.Geometry.Affine
