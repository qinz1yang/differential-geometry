import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ClassBounds

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

structure IsBackgroundLowRegularitySolutionAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap : ℝ) : Prop where

  bounds : HasLowRegularityBoundsAt (I := I) (M := M) g₀ g_bg K

  solve : IsBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K bounds hT hT1 u gforce

  hTτ : T ≤ lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize

  hcap : lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ Rcap

namespace IsBackgroundLowRegularitySolutionAt

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
  {T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T}
  {gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
  {Rcap : ℝ}

theorem hδ (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    K.threshold < 1 :=
  K.threshold_lt

theorem hCtop
    (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.top :=
  K.top_nonneg

theorem hB1
    (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.slope :=
  K.slope_nonneg

theorem hρ (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 < K.outer :=
  K.outer_pos

theorem hP (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 < K.realize :=
  K.realize_pos

theorem hreal
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤
          K.realize →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) K.threshold :=
  h.bounds.hreal

theorem hδ0
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.threshold :=
  h.bounds.threshold_nonneg

theorem hδ3
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    K.threshold ≤ 1 / 3 :=
  h.bounds.threshold_le_third

theorem hcore
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg K.threshold_lt
      (lowRegularityMetricRealization (I := I) (M := M) g₀
        (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
        K.realize_pos.le h.hreal)) :=
  h.bounds.core_cont

theorem hB0
    (_h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.base :=
  K.base_nonneg

theorem hcont
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt
      K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.hreal) :=
  h.bounds.hcont

theorem htame
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ v w : lowerState (I := I) (M := M) g₀ 1
      (lowRegularityStateRadius K.top K.slope K.outer K.realize),
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.hreal v -
        boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.hreal w‖ ≤
      K.top * lowRegularityOuterRadius K.top K.outer K.realize *
          ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) - w.1‖ +
        K.base *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ +
        K.slope *
            (‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(w.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ :=
  h.bounds.htame

theorem hzero
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
        K.slope_nonneg K.outer_pos K.realize_pos h.hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
            K.realize_pos).le⟩‖ ≤ K.zeroBd :=
  h.bounds.hzero

theorem hball
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖gforce‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 :=
  h.solve.force_bound

theorem hforce
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    gforce =ᵐ[timeMeasure T]
      (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt
        K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
              K.realize_pos).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce) t)) :=
  h.solve.force_eq

end IsBackgroundLowRegularitySolutionAt

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
