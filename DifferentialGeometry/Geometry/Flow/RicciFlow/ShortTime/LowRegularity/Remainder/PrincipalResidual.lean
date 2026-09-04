import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.CoreIdentification

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

noncomputable def principalResidual
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
    deTurckSmoothRemainder (I := I) g g
      (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
    deTurckPrincipalCometricTerm (I := I) (M := M) g
      (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ) T

noncomputable def principalResidualSobolev
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ) -
    lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)
      (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T)

noncomputable def lowerScaleResidual
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
    deTurckSmoothRemainder (I := I) g g
      (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
    (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderAction
      (I := I) (M := M) T

noncomputable def lowerScaleResidualSobolev
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
    (lowerScaleResidual (I := I) (M := M) g T hδ_lt hδ hδZ)

theorem principalResidualSobolev_eq
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (hsmall : ‖metricPerturbationOperatorH2 (I := I) (M := M) g
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)‖ < 1) :
    principalResidualSobolev (I := I) (M := M) g T hδ_lt hδ hδZ =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (principalResidual (I := I) (M := M) g T hδ_lt hδ hδZ) := by
  let gm : SmoothRiemannianMetric I M :=
    tensorSectionRealizeMetric (I := I) g T hδ_lt hδ
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w := by
    intro y v w
    exact tensorSectionRealizeMetric_inner
      (I := I) g T hδ_lt hδ y v w
  have hprincipal :
      lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (deTurckPrincipalCometricTerm (I := I) (M := M) g gm T) := by
    rw [lowRegularityPrincipalOperatorH2_apply_smoothCore (I := I) (M := M)
      hDim g gm T htie hsmall]
    exact principalCometricOperatorH2_apply_smoothCore (I := I) (M := M) hDim g gm T
  have hsub (S U : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - U) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
    simpa only [ccToHsLin_apply] using
      map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S U
  simp only [principalResidualSobolev, principalResidual]
  rw [hsub, hsub, hprincipal]
  rw [hsub]

theorem exists_principalResidual_decomposition_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, ∃ D : ℝ → ℝ,
      0 ≤ κ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      let hδ_lt : δ < 1 :=
        lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
      let L : LowerScaleActionCoefficients g :=
        lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ
      principalResidual (I := I) (M := M) g T hδ_lt hδ hδZ =
          (L.secondOrderAction (I := I) (M := M) T -
            deTurckPrincipalCometricTerm (I := I) (M := M) g
              (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ) T) +
            L.firstOrderAction (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (L.secondOrderCoefficient.toSection x) ≤
            (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
        covariantJetNormSq (I := I) (M := M) g 2
            (L.firstOrderAction (I := I) (M := M) T) ≤
          (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨κ, D, hκ, hD, hsplit⟩ :=
    exists_ricciDeTurckRemainder_diagonal_secondOrder_bound (I := I) (M := M) hDim g
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hmain :=
    hsplit T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  dsimp only at hmain ⊢
  refine ⟨?_, hmain.2.1, hmain.2.2⟩
  simp only [principalResidual]
  rw [hmain.1]
  abel

theorem exists_lowerScaleResidual_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      let hδ_lt : δ < 1 :=
        lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
      let L : LowerScaleActionCoefficients g :=
        lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ
      lowerScaleResidual (I := I) (M := M) g T hδ_lt hδ hδZ =
          L.firstOrderAction (I := I) (M := M) T ∧
        covariantJetNormSq (I := I) (M := M) g 2
            (lowerScaleResidual (I := I) (M := M)
              g T hδ_lt hδ hδZ) ≤
          (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨_, D, _, hD, hsplit⟩ :=
    exists_ricciDeTurckRemainder_diagonal_secondOrder_bound (I := I) (M := M) hDim g
  refine ⟨D, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hmain :=
    hsplit T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  dsimp only at hmain ⊢
  have heq :
      lowerScaleResidual (I := I) (M := M) g T
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          hδ hδZ =
        (lowerScaleActionCoefficients (I := I) (M := M) g g T
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          hδ hδZ).firstOrderAction (I := I) (M := M) T := by
    simp only [lowerScaleResidual]
    rw [hmain.1]
    abel
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hmain.2.2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
