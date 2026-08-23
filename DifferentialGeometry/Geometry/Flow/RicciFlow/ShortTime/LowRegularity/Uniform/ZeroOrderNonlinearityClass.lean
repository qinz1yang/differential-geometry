import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ZeroOrderNonlinearityBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.DeTurckRHSFirstDerivative

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

structure ZeroOrderNonlinearityParameters where
  zeroBd : ℝ

structure HasUniformZeroOrderNonlinearityBound
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (Z : ZeroOrderNonlinearityParameters) : Prop where
  zero_nonneg : 0 ≤ Z.zeroBd
  zero : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∀ {R δ : ℝ} (hR : 0 < R) (hδ : δ < 1)
      (hreal : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
      (_hcore : Continuous
        (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ hreal)),
      ‖deTurckRemainderOnLowerState (I := I) (M := M) g gBase hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hR.le⟩‖ ≤ Z.zeroBd

noncomputable def zeroOrderNonlinearityParameters
    (gBase : SmoothRiemannianMetric I M) (Λ Ksup : ℝ) : ZeroOrderNonlinearityParameters where
  zeroBd := zeroStateRemainderBound Ksup Λ
    ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
    (Module.finrank ℝ E)

theorem has_uniform_zero_order_nonlinearity_bound
    (gBase : SmoothRiemannianMetric I M) {Λ Ksup : ℝ}
    (hKsup : 0 ≤ Ksup)
    (hsup : ∀ g : SmoothRiemannianMetric I M,
      (∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v) →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g gBase Λ →
      ∀ j : ℕ, j ≤ 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((iteratedCovGrad (I := I) g 0 2 j
            (deTurckRHSSection (I := I) gBase g)).toSection x) ≤ Ksup ^ 2) :
    HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ
      (zeroOrderNonlinearityParameters (I := I) (M := M) gBase Λ Ksup) := by
  refine ⟨?_, ?_⟩
  · exact nZeroC_nonneg hKsup Λ
      ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
      (Module.finrank ℝ E)
  · intro g hEq hjet R δ hR hδ hreal hcore
    have hcomp : ∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v :=
      fun x v => hEq.2 x (Set.mem_univ x) v
    have hsupg := hsup g hcomp
      (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) (hjet 3 (by norm_num))
    simpa only [zeroOrderNonlinearityParameters] using
      zero_state_remainder_uniform_bound (I := I) (M := M) gBase g hR hδ hreal hcore hKsup hEq hsupg

theorem exists_uniform_zero_order_nonlinearity_parameters
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ Z : ZeroOrderNonlinearityParameters,
      HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ Z := by
  obtain ⟨Ksup, hKsup, hsup⟩ :=
    uniformKsupLeOne (I := I) (M := M) gBase hΛ
  exact ⟨zeroOrderNonlinearityParameters (I := I) (M := M) gBase Λ Ksup,
    has_uniform_zero_order_nonlinearity_bound (I := I) (M := M) gBase hKsup hsup⟩

theorem zero_order_nonlinearity_bound_of_uniform_parameters
    {gBase : SmoothRiemannianMetric I M} {Λ : ℝ} {Z : ZeroOrderNonlinearityParameters}
    (hZ : HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ Z)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ
      (lowRegularityMetricRealization (I := I) (M := M) g
        (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal))) :
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ Z.zeroBd := by
  simpa only [boundedDeTurckRemainderOnLowerState] using hZ.zero g hEq hjet
    (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ
    (lowRegularityMetricRealization (I := I) (M := M) g
      (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal) hcore

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
