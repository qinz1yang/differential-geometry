import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.PointwiseSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.EnergyLadderGate

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

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

def IsAdaptedBackgroundLowRegularitySolution (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ) : Prop :=
  IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap ∧
    HasGalerkinEnergyThreeBoundBackground (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap ∧
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1

namespace IsAdaptedBackgroundLowRegularitySolution

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
  {T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    ((1 : ℕ) : ℝ) T}
  {gforce : timeL2
    (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}

theorem toIsBackgroundLowRegularitySolutionAt
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap :=
  h.1

theorem toIsBackgroundLowRegularitySolution
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K
      h.toIsBackgroundLowRegularitySolutionAt.bounds hT hT1 u gforce :=
  h.toIsBackgroundLowRegularitySolutionAt.solve

theorem toHasGalerkinEnergyThreeBoundBackground
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    HasGalerkinEnergyThreeBoundBackground (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap :=
  h.2.1

theorem exists_absorption_constants_and_margin
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ A B : ℝ, HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1 :=
  h.2.2

theorem absorb
    (h : IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ ε : ℝ, 0 < ε ∧
      Ctop₂ * (Kcap * (K.threshold / (1 - K.threshold) ^ 2)) +
          Kr2 * lowRegularityStateRadius K.top K.slope K.outer K.realize +
          Kr1 * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1 := by
  obtain ⟨A, B, _hgate, hA, hB, ε, hε, hbudget⟩ := h.exists_absorption_constants_and_margin
  have hR : 0 ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize :=
    (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
      K.outer_pos K.realize_pos).le
  have hdom := energyLadder_absorption_coefficient_le hA hB h.1.hδ0 hR
  exact ⟨ε, hε, by linarith only [hdom, hbudget]⟩

end IsAdaptedBackgroundLowRegularitySolution

theorem adaptedBackground_of_given
    {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
    {T Rcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T}
    {gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hsolve : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap)
    {A B : ℝ} (hgate : HasEnergyLadderAbsorptionConstantsBackground (I := I) (M := M) g₀ g_bg A B)
    (hbudget : ∃ ε : ℝ, 0 < ε ∧
      A * (K.threshold / (1 - K.threshold) ^ 2) +
        B * lowRegularityStateRadius K.top K.slope K.outer K.realize + ε < 1) :
    ∃ Ctop₂ Kr2 Kr1 Kcap : ℝ,
      IsAdaptedBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hT hT1
        u gforce Rcap Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hrung, hA, hB⟩ := hgate.2.2.1
  exact ⟨Ctop₂, Kr2, Kr1, Kcap, hsolve, hrung,
    A, B, hgate, hA, hB, hbudget⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
