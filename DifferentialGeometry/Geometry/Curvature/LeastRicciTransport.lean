import DifferentialGeometry.Geometry.Curvature.RicciPullback
import DifferentialGeometry.Geometry.Curvature.RicciSharpScaling
import Mathlib.LinearAlgebra.Eigenspace.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

theorem least_ricci_eigenpair_pullback
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (μ : ℝ) (w : TangentSpace I x)
    (hunit : (Diffeomorph.pullbackMetricCross g Φ).inner x w w = 1)
    (heigen : ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x w = μ • w)
    (hmin : ∀ z, (Diffeomorph.pullbackMetricCross g Φ).inner x z z = 1 →
      μ ≤ ricciTensor (Diffeomorph.pullbackMetricCross g Φ) x z z)
    (hsimple : Module.End.eigenspace
      (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x).toLinearMap μ =
        Submodule.span ℝ {w}) :
    let u := mfderiv I J Φ x w
    g.inner (Φ x) u u = 1 ∧ ricciSharp g (Φ x) u = μ • u ∧
      (∀ z, g.inner (Φ x) z z = 1 → μ ≤ ricciTensor g (Φ x) z z) ∧
      Module.End.eigenspace (ricciSharp g (Φ x)).toLinearMap μ = Submodule.span ℝ {u} := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  have hi (z : TangentSpace I x) :
      e (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x z) = ricciSharp g (Φ x) (e z) := by
    simpa only [he] using ricciSharp_pullbackMetricCross g Φ x z
  have heu : ricciSharp g (Φ x) (e w) = μ • e w := by rw [← hi, heigen, map_smul]
  change g.inner (Φ x) (mfderiv I J Φ x w) (mfderiv I J Φ x w) = 1 ∧ _
  refine ⟨by rwa [← Diffeomorph.pullbackMetricCross_inner], ?_, ?_, ?_⟩
  · simpa only [he] using heu
  · intro z hz
    obtain ⟨v, rfl⟩ := e.surjective z
    have hv : (Diffeomorph.pullbackMetricCross g Φ).inner x v v = 1 := by
      rwa [Diffeomorph.pullbackMetricCross_inner, ← he]
    simpa only [ricciTensor_pullbackMetricCross, ← he] using hmin v hv
  · apply le_antisymm
    · intro z hz
      obtain ⟨v, rfl⟩ := e.surjective z
      have hv : v ∈ Module.End.eigenspace
          (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x).toLinearMap μ := by
        apply Module.End.mem_eigenspace_iff.mpr
        change ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x v = μ • v
        apply e.injective
        rw [hi, map_smul]
        exact Module.End.mem_eigenspace_iff.mp hz
      rw [hsimple] at hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      apply Submodule.mem_span_singleton.mpr
      exact ⟨c, by simpa only [map_smul, he] using congrArg e hc⟩
    · apply Submodule.span_le.mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      apply Module.End.mem_eigenspace_iff.mpr
      change ricciSharp g (Φ x) (mfderiv I J Φ x w) = μ • mfderiv I J Φ x w
      simpa only [he] using heu

end Poincare.Geometry.Curvature
