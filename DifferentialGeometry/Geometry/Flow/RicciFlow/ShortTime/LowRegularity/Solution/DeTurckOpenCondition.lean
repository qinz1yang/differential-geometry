import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Regularity.AllOrders
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.RemainderRepresentation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral (tensorResolventL2_isCompactOperator)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_jointly_smooth_ricci_deTurck_solution_for_short_time (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ {T : ℝ} (_hT : 0 < T) (_ : T ≤ T₀) (_hT1 : T ≤ 1),
        ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
            (g := g) (r := 0) (s := 2) (2 : ℝ) T)
            (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
            (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g (F t)) δ'),
          F 0 = 0 ∧
          (∀ t ∈ Set.Icc (0 : ℝ) T,
            SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
              tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
            HasDerivWithinAt
              (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
              (deTurckRicciRHS (I := I) g
                (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t))
                  x v w)
              (Set.Ici 0) t) ∧
          JointChartGramSmooth (I := I) T
            (fun t : ℝ =>
              tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  refine exists_jointly_smooth_metric_solution_for_short_time (I := I) (M := M) hDim g
    (deTurckRicciRHS (I := I) g) ?_
  intro S δ hδ_lt hδ x v w
  simpa only [deTurckRemainderSection] using
    deTurck_rem_repr (I := I) (M := M) g g S hδ_lt hδ x v w

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
