import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]


theorem ricci_trace_pinching_scaleMetric_iff
    (g : SmoothRiemannianMetric I M) (s : ℝ) (hs : 0 < s) (c : ℝ) :
    (∀ x : M, ∀ v : TangentSpace I x,
      c * metricScalarAt (scaleMetric s hs g) x * (scaleMetric s hs g).inner x v v ≤
        ricciTensor (scaleMetric s hs g) x v v) ↔
    ∀ x : M, ∀ v : TangentSpace I x,
      c * metricScalarAt g x * g.inner x v v ≤ ricciTensor g x v v := by
  have hRic (x : M) (v w : TangentSpace I x) :
      ricciTensor (scaleMetric s hs g) x v w = ricciTensor g x v w := by
    rw [ricciTensor_apply, ricciTensor_apply]
    congr 1
    ext z
    simp only [ricciEndo_apply, LeviCivita, lcConn_scaleMetric]
  have hweight (x : M) (v : TangentSpace I x) :
      c * (s⁻¹ * metricScalarAt g x) * (s * g.inner x v v) =
        c * metricScalarAt g x * g.inner x v v := by
    calc
      _ = (s⁻¹ * s) * (c * metricScalarAt g x * g.inner x v v) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hs.ne', one_mul]
  constructor
  · intro h x v
    have hx := h x v
    rw [metricScalarAt_scaleMetric, scaleMetric_inner, hRic, hweight] at hx
    exact hx
  · intro h x v
    rw [metricScalarAt_scaleMetric, scaleMetric_inner, hRic, hweight]
    exact h x v

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [BoundarylessManifold I N]


theorem ricci_trace_pinching_pullback_iff
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) (c : ℝ) :
    (∀ x : M, ∀ v : TangentSpace I x,
      c * metricScalarAt (Diffeomorph.pullbackMetric g Phi) x *
          (Diffeomorph.pullbackMetric g Phi).inner x v v ≤
        ricciTensor (Diffeomorph.pullbackMetric g Phi) x v v) ↔
    ∀ y : N, ∀ v : TangentSpace I y,
      c * metricScalarAt g y * g.inner y v v ≤ ricciTensor g y v v := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := Phi.surjective y
    intro v
    let L := Diffeomorph.mfderivToContinuousLinearEquiv Phi (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
    have hL : mfderiv I I (Phi : M → N) x (L.symm v) = v := by
      have hcoe := Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi) (x := x) (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      have heval := congrArg
        (fun f : TangentSpace I x →L[ℝ] TangentSpace I (Phi x) => f (L.symm v)) hcoe
      exact heval.symm.trans (L.apply_symm_apply v)
    have hx := h x (L.symm v)
    rw [metricScalarAt_pullback, Diffeomorph.pullbackMetric_inner,
      DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback, hL] at hx
    exact hx
  · intro h x v
    rw [metricScalarAt_pullback, Diffeomorph.pullbackMetric_inner,
      DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback]
    exact h (Phi x) (mfderiv I I (Phi : M → N) x v)


theorem scalar_positive_of_pullback_scaleMetric
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (s : ℝ) (hs : 0 < s)
    (h : ∀ x : M, 0 < metricScalarAt (Diffeomorph.pullbackMetric (scaleMetric s hs g) Phi) x) :
    ∀ y : N, 0 < metricScalarAt g y := by
  intro y
  obtain ⟨x, rfl⟩ := Phi.surjective y
  have hx := h x
  rw [metricScalarAt_pullback, metricScalarAt_scaleMetric] at hx
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hs)).mp hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
