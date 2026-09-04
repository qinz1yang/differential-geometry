import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.SmallTimeBounds

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

structure BackgroundLiftParameters (K : LowRegularityBoundParameters) where
  coeffRadius : ℝ
  contract : ℝ
  zero : ℝ
  slope : ℝ
  forceCap : ℝ
  coeffRadius_pos : 0 < coeffRadius
  contract_nonneg : 0 ≤ contract
  contract_lt_one : contract < 1
  zero_nonneg : 0 ≤ zero
  slope_nonneg : 0 ≤ slope
  forceCap_nonneg : 0 ≤ forceCap
  forceCap_eq :
    forceCap = lowRegularityStateRadius K.top K.slope K.outer K.realize / 4
  state_le_radius :
    lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ coeffRadius
  coeffRadius_le_realize : coeffRadius ≤ K.realize
  force_margin :
    6 * (2 * slope * forceCap) ≤ (1 - contract) / 2

namespace BackgroundLiftParameters

def horizon {K : LowRegularityBoundParameters} (D : BackgroundLiftParameters K) : ℝ :=
  affineLiftTimeHorizon D.contract D.zero

theorem horizon_pos {K : LowRegularityBoundParameters} (D : BackgroundLiftParameters K) :
    0 < D.horizon :=
  affineLiftTimeHorizon_pos D.contract_nonneg D.contract_lt_one D.zero_nonneg

theorem horizon_le_one {K : LowRegularityBoundParameters} (D : BackgroundLiftParameters K) :
    D.horizon ≤ 1 :=
  affineLiftTimeHorizon_le_one

def commonHorizon (K : LowRegularityBoundParameters) (D : BackgroundLiftParameters K) : ℝ :=
  min (lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize) D.horizon

theorem commonHorizon_pos (K : LowRegularityBoundParameters) (D : BackgroundLiftParameters K) :
    0 < D.commonHorizon K := by
  exact lt_min
    (lowRegularityTimeHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
      K.zero_nonneg K.outer_pos K.realize_pos)
    D.horizon_pos

theorem commonHorizon_le_one (K : LowRegularityBoundParameters) (D : BackgroundLiftParameters K) :
    D.commonHorizon K ≤ 1 :=
  (min_le_left _ _).trans lowRegularityTimeHorizon_le_one

theorem commonHorizon_le_low (K : LowRegularityBoundParameters) (D : BackgroundLiftParameters K) :
    D.commonHorizon K ≤
      lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize :=
  min_le_left _ _

theorem commonHorizon_le_lift (K : LowRegularityBoundParameters) (D : BackgroundLiftParameters K) :
    D.commonHorizon K ≤ D.horizon :=
  min_le_right _ _

end BackgroundLiftParameters

theorem IsBackgroundLowRegularitySolution.force_le_cap
    {g₀ g_bg : SmoothRiemannianMetric I M}
    {K : LowRegularityBoundParameters} {hK : HasLowRegularityBoundsAt (I := I) (M := M) g₀ g_bg K}
    {T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T}
    {gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hsol : IsBackgroundLowRegularitySolution (I := I) (M := M)
      g₀ g_bg K hK hT hT1 u gforce)
    (D : BackgroundLiftParameters K) :
    ‖gforce‖ ≤ D.forceCap := by
  rw [D.forceCap_eq]
  exact hsol.force_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
