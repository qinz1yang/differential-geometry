import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScaleSobolevExtensions
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_ricciDeTurckRemainder_lowOrder_spectralSobolev_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ K C : ℝ, 0 ≤ κ ∧ 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      ∃ A : LowerScaleActionCoefficients g,
        deTurckSmoothRemainder (I := I) g g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g g
              (0 : SmoothCcTensor g 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤
            (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
        ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6) ∧
        ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.firstOrderAction (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
          (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨κ, K, hκ, hK, hrem⟩ :=
    ricciDeTurckRemainder_lowOrder_split (I := I) (M := M) hDim g
  obtain ⟨C, hC, hextensions⟩ :=
    exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  refine ⟨κ, K, C, hκ, hK, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  obtain ⟨A, hsplit, hcap, hHi, hLo⟩ :=
    hrem T hT hδ_le hδ0 hδ hδZ
  let Q : ℝ :=
    K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6
  have hjet : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 T := by
    unfold covariantJetNormSq
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQ : 0 ≤ Q := by
    exact mul_nonneg hK (pow_nonneg (by linarith) 6)
  obtain ⟨hHiNorm, hLoNorm, hHiCore, hLoCore, hcompat⟩ :=
    hextensions A Q hQ
      (by simpa only [Q] using hHi)
      (by simpa only [Q] using hLo)
  refine ⟨A, hsplit, hcap, ?_, ?_, hHiCore, hLoCore, hcompat⟩
  · simpa only [Q] using hHiNorm
  · simpa only [Q] using hLoNorm

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
