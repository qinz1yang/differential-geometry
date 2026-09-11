import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.MetricPerturbationRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Remainder.ZeroOrderClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Remainder.DenseTameBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.AllTimes

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

structure HasUniformLowRegularityBounds
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (K : LowRegularityBoundParameters) : Prop where
  bounds : ∀ g : SmoothRiemannianMetric I M,
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    HasLowRegularityBoundsAt (I := I) (M := M) g gBase K

structure HasUniformLowRegularityBoundCaps
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (U : LowRegularityHorizonParameters) : Prop where
  bounds : ∀ g : SmoothRiemannianMetric I M,
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∃ K : LowRegularityBoundParameters,
      HasLowRegularityBoundsAt (I := I) (M := M) g gBase K ∧ IsLowRegularityBoundCap K U

theorem HasUniformLowRegularityBounds.to_caps
    {gBase : SmoothRiemannianMetric I M} {Λ : ℝ} {K : LowRegularityBoundParameters}
    (hK : HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K) :
    HasUniformLowRegularityBoundCaps (I := I) (M := M) gBase Λ K.toHorizon where
  bounds g hEq hjet :=
    ⟨K, hK.bounds g hEq hjet, boundCap_refl K⟩

theorem exists_uniform_low_regularity_bound_parameters
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : LowRegularityBoundParameters,
      HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K := by
  obtain ⟨RD, hRD⟩ :=
    exists_uniform_metric_perturbation_realization_parameters (I := I) (M := M) hDim gBase hΛ
  obtain ⟨ZD, hZD⟩ := exists_uniform_zero_order_nonlinearity_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, houter⟩ :=
    deTurckRemainderOnLowerState_outer_uniform_bound (I := I) (M := M) hDim gBase hΛ
      hRD.threshold_nonneg hRD.threshold_lt
  let Q : ℝ := lowRegularityOuterRadius Ctop ρ RD.radius
  have hQpos : 0 < Q := by
    simpa only [Q] using lowRegularityOuterRadius_pos hCtop hρ hRD.radius_pos
  have hB1Q : 0 ≤ B1 Q := hB1 Q hQpos.le
  have hSpos : 0 < lowRegularityStateRadius Ctop (B1 Q) ρ RD.radius :=
    lowRegularityStateRadius_pos hCtop hB1Q hρ hRD.radius_pos
  have hQρ : Q ≤ ρ := by
    have hhalf := lowRegularityOuterRadius_le_rho
      (Ctop := Ctop) (ρ := ρ) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hQP : Q ≤ RD.radius := by
    have hhalf := lowRegularityOuterRadius_le_P
      (Ctop := Ctop) (ρ := ρ) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hSQ : lowRegularityStateRadius Ctop (B1 Q) ρ RD.radius ≤ Q := by
    have hhalf := lowRegularityStateRadius_le_Q
      (Ctop := Ctop) (B1 := B1 Q) (ρ := ρ) (P := RD.radius)
    linarith
  let K : LowRegularityBoundParameters := {
    threshold := RD.threshold
    top := Ctop
    base := B0 Q
    slope := B1 Q
    zeroBd := ZD.zeroBd
    outer := ρ
    realize := RD.radius
    threshold_lt := hRD.threshold_lt
    top_nonneg := hCtop
    base_nonneg := hB0 Q hQpos.le
    slope_nonneg := hB1Q
    zero_nonneg := hZD.zero_nonneg
    outer_pos := hρ
    realize_pos := hRD.radius_pos
  }
  refine ⟨K, { bounds := ?_ }⟩
  intro g hEq hjet
  have hreal := hRD.realize g hEq hjet
  have hrealQ : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) RD.threshold :=
    realizeOfLE (I := I) (M := M) g hQP hreal
  obtain ⟨hcont0, hcore0, htame0⟩ :=
    houter g hEq hjet hQpos.le hQρ hSpos hSQ hrealQ
  have hcore' : Continuous
      (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hRD.threshold_lt
        (lowRegularityMetricRealization (I := I) (M := M) g
          (Ctop := Ctop) (B1 := B1 Q) (ρ := ρ)
          hRD.radius_pos.le hreal)) := by
    simpa only using hcore0
  have hzero0 := zero_order_nonlinearity_bound_of_uniform_parameters (I := I) (M := M) hZD g hEq hjet
    hRD.threshold_lt hCtop hB1Q hρ hRD.radius_pos hreal hcore'
  have hrealK : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ K.realize →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) K.threshold := by
    simpa only [K] using hreal
  refine {
    threshold_nonneg := by simpa only [K] using hRD.threshold_nonneg
    threshold_le_third := by simpa only [K] using hRD.threshold_le_third
    metric_realization := hrealK
    remainder_continuous := ?_
    remainder_lipschitz := ?_
    remainder_zero_bound := ?_
    smoothCore_continuous := ?_ }
  · simpa only [K, Q, boundedDeTurckRemainderOnLowerState] using hcont0
  · simpa only [K, Q, boundedDeTurckRemainderOnLowerState] using htame0
  · simpa only [K, Q] using hzero0
  · simpa only [K, Q] using hcore'

theorem exists_uniform_low_regularity_horizon_parameters
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ U : LowRegularityHorizonParameters,
      HasUniformLowRegularityBoundCaps (I := I) (M := M) gBase Λ U := by
  obtain ⟨K, hK⟩ := exists_uniform_low_regularity_bound_parameters (I := I) (M := M) hDim gBase hΛ
  exact ⟨K.toHorizon, HasUniformLowRegularityBounds.to_caps (I := I) (M := M) hK⟩

theorem exists_low_regularity_solution_of_uniform_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (K : LowRegularityBoundParameters)
    (hK : HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K) :
    0 < lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
        (hjet : ∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
        ∀ {T : ℝ} (hT : 0 < T)
          (_ : T ≤ lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize)
          (hT1 : T ≤ 1),
          ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
            (gforce : timeL2
              (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
            IsBackgroundLowRegularitySolution (I := I) (M := M) g gBase K
              (hK.bounds g hEq hjet) hT hT1 u gforce := by
  refine ⟨lowRegularityTimeHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
    K.zero_nonneg K.outer_pos K.realize_pos, ?_⟩
  intro g hEq hjet T hT hTτ hT1
  exact exists_background_lowRegularity_solution (I := I) (M := M) g gBase K
    (hK.bounds g hEq hjet) hT hTτ hT1

theorem exists_low_regularity_solution_of_uniform_caps
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (U : LowRegularityHorizonParameters)
    (hU : HasUniformLowRegularityBoundCaps (I := I) (M := M) gBase Λ U) :
    0 < lowRegularityTimeHorizon U.top U.base U.slope U.zeroBd U.outer U.realize ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (_hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
        (_hjet : ∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
        ∀ {T : ℝ} (hT : 0 < T)
          (_ : T ≤ lowRegularityTimeHorizon U.top U.base U.slope U.zeroBd U.outer U.realize)
          (hT1 : T ≤ 1),
          ∃ (K : LowRegularityBoundParameters)
            (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gBase K)
            (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
            (gforce : timeL2
              (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
            IsLowRegularityBoundCap K U ∧
              IsBackgroundLowRegularitySolution (I := I) (M := M) g gBase K hK hT hT1 u gforce := by
  refine ⟨lowRegularityTimeHorizon_pos U.top_nonneg U.base_nonneg U.slope_nonneg
    U.zero_nonneg U.outer_pos U.realize_pos, ?_⟩
  intro g hEq hjet T hT hTτ hT1
  obtain ⟨K, hK, hcap⟩ := hU.bounds g hEq hjet
  obtain ⟨u, gforce, hsol⟩ := exists_background_lowRegularity_solution (I := I) (M := M) g gBase K hK
    hT (hTτ.trans (horizon_le_of_cap hcap)) hT1
  exact ⟨K, hK, u, gforce, hcap, hsol⟩

theorem exists_uniform_low_regularity_solution
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ U : LowRegularityHorizonParameters,
      0 < lowRegularityTimeHorizon U.top U.base U.slope U.zeroBd U.outer U.realize ∧
        ∀ (g : SmoothRiemannianMetric I M)
          (_hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
          (_hjet : ∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
          ∀ {T : ℝ} (hT : 0 < T)
            (_ : T ≤ lowRegularityTimeHorizon U.top U.base U.slope U.zeroBd U.outer U.realize)
            (hT1 : T ≤ 1),
            ∃ (K : LowRegularityBoundParameters)
              (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gBase K)
              (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
              (gforce : timeL2
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
              IsLowRegularityBoundCap K U ∧
                IsBackgroundLowRegularitySolution (I := I) (M := M) g gBase K hK hT hT1 u gforce := by
  obtain ⟨U, hU⟩ := exists_uniform_low_regularity_horizon_parameters (I := I) (M := M) hDim gBase hΛ
  obtain ⟨hpos, hsolve⟩ := exists_low_regularity_solution_of_uniform_caps (I := I) (M := M) gBase U hU
  exact ⟨U, hpos, hsolve⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
