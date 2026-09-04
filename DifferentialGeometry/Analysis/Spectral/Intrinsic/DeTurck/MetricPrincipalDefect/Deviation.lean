import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Defs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.InverseMetricDifferenceCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_deviation_riemannianFiberNormSq_le_inverseMetricDifferenceSlotCoefficient
    (g₀ g₁ : SmoothRiemannianMetric I M) (CTH CR : ℝ) (x : M)
    (hTH : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CTH * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x))
    (hR : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁
          - ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀).toSection x) ≤
      CR * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₁
          - deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀).toSection x) ≤
      (8 * CTH + 8 * CR) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection x) := by
  set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA
  set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT
  set DTHs : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ g₁
      - traceHessianCoeff (I := I) (M := M) g₀ g₀
  set DRs : SmoothCcTensor g₀ 4 2 :=
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁
      - ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀
  have hdev : deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₁
        - deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT
        - (DRs + DRs) := by
    rw [deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g₀ g₁,
      deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g₀ g₀,
      reindexCoefficientInputSlots_sub (I := I) (M := M) g₀ _ _ ρA,
      reindexCoefficientInputSlots_sub (I := I) (M := M) g₀ _ _ ρAT]
    dsimp [ρA, ρAT, DTHs, DRs]
    abel
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₁
          - deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀).toSection x) ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x)
        + 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
        + 8 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) := by
    have hsection :
        ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA
            + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT
            - (DRs + DRs)).toSection x) =
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA
              + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x
            - (DRs + DRs).toSection x := by
      rw [SmoothCcTensor.toSection_sub]
      rfl
    rw [hdev, hsection]
    have h1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
      ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
      ((DRs + DRs).toSection x)
    have h2 := lieCorrectionZero_riemannianFiberNormSq_toSection_add_le
      (I := I) (M := M) g₀ 4 2
      (reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA)
      (reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT) x
    have h3 := lieCorrectionZero_riemannianFiberNormSq_toSection_add_le
      (I := I) (M := M) g₀ 4 2 DRs DRs x
    linarith
  have hAr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
    rw [reindexCoefficientInputSlots_toSection]
    exact
      Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
      (I := I) (M := M) g₀ 4 2 x ρA
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        DTHs.toSection x)
  have hATr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
    rw [reindexCoefficientInputSlots_toSection]
    exact
      Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
      (I := I) (M := M) g₀ 4 2 x ρAT
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        DTHs.toSection x)
  rw [hAr, hATr] at h0
  change riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) ≤ _ at hTH
  change riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) ≤ _ at hR
  linarith

end DifferentialGeometry.Analysis.Spectral
