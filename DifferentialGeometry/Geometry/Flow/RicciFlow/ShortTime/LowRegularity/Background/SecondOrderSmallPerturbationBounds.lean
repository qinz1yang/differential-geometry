import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientJetBounds

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_lowerScaleSecondOrderCoefficient_background_smallPerturbation_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      let A := lowerScaleActionCoefficients (I := I) (M := M) g gB T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      (∀ x : M,
        DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq
            (I := I) (M := M) g 4 2 x
            (A.secondOrderCoefficient.toSection x) ≤ (C * R) ^ 2) ∧
        covariantJetNormSq (I := I) (M := M) g 2
          A.secondOrderCoefficient ≤ (C * R) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hdiag⟩ :=
    exists_lowerScaleSecondOrderCoefficient_smallPerturbation_secondOrder_bound
      (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R hR0 hRρ hTHs
  have hcoeff :
      (lowerScaleActionCoefficients (I := I) (M := M) g gB T
          (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).secondOrderCoefficient =
        (lowerScaleActionCoefficients (I := I) (M := M) g g T
          (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).secondOrderCoefficient := by
    rw [RicciDeTurckLowOrder.secondOrderCoefficient_eq,
      RicciDeTurckLowOrder.secondOrderCoefficient_eq]
  dsimp only
  rw [hcoeff]
  exact hdiag T hT hδ_le hδ0 hδ hδZ hR0 hRρ hTHs

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
