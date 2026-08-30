import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderLowerScalePairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LiftAffine

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccToHsLin ccToHsLin_dense)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem lowerScaleFirstOrderAction_core_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        LowA1CorePair (I := I) (M := M) g hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, hρ₀, hpair⟩ :=
    radialFirstOrderActionSecondToFirstOrder_pairing_bound (I := I) (M := M) hDim g
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρ_le hδ0 hδ_le hreal
  exact hpair hρ hρ_le hδ0 hδ_le hreal


theorem lowerScaleFirstOrderActionSecondToFirstOrder_ball_bound
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : LowA1CorePair (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ), ‖v‖ ≤ R →
        ‖lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ C := by
  let j : SmoothCcTensor g 0 2 →ₗ[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) :=
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
  let F : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
    lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
  obtain ⟨K, hK⟩ := hpair (R + 1)
  let K₀ : ℝ := max K 0
  let C : ℝ := K₀ * R + ‖F 0‖
  have hK₀ : 0 ≤ K₀ := le_max_right K 0
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hK₀ hR) (norm_nonneg (F 0))
  refine ⟨C, hC, ?_⟩
  intro v hv
  have hF : Continuous F :=
    lowerScaleFirstOrderActionSecondToFirstOrder_continuous (I := I) (M := M) hpair
  have hright : Continuous
      (fun w : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
        K₀ * ‖w‖ + ‖F 0‖) :=
    (continuous_const.mul continuous_norm).add continuous_const
  have hFnorm : Continuous
      (fun w : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
        ‖show
          TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
            TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)
          from F w‖) :=
    Continuous.comp
      (continuous_norm (E :=
        TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
          TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))) hF
  have hclosed :
      IsClosed {w : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) |
        R + 1 ≤ ‖w‖ ∨ ‖F w‖ ≤ K₀ * ‖w‖ + ‖F 0‖} := by
    simpa only [Set.ofPred_or] using
      (isClosed_le continuous_const continuous_norm).union
        (isClosed_le hFnorm hright)
  have hall :
      R + 1 ≤ ‖v‖ ∨ ‖F v‖ ≤ K₀ * ‖v‖ + ‖F 0‖ := by
    refine (ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)).induction_on
      v hclosed ?_
    intro S
    by_cases hlarge : R + 1 ≤ ‖j S‖
    · exact Or.inl hlarge
    · right
      have hsmall : ‖j S‖ ≤ R + 1 := (lt_of_not_ge hlarge).le
      have hzero : ‖j (0 : SmoothCcTensor g 0 2)‖ ≤ R + 1 := by
        simp only [map_zero, norm_zero]
        linarith
      have hdiff := hK S (0 : SmoothCcTensor g 0 2) hsmall hzero
      have hcoreS :
          F (j S) =
            (lowCoreActionCoefficients (I := I) (M := M) g
              hρ hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
        exact lowerScaleFirstOrderActionSecondToFirstOrder_core (I := I) (M := M) hpair S
      have hcore0 :
          F 0 =
            (lowCoreActionCoefficients (I := I) (M := M) g
              hρ hδ0 hδ_le hreal
              (0 : SmoothCcTensor g 0 2)).firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
        simpa only [map_zero] using
          (lowerScaleFirstOrderActionSecondToFirstOrder_core (I := I) (M := M) hpair
            (0 : SmoothCcTensor g 0 2))
      rw [← hcoreS, ← hcore0] at hdiff
      have hdiff0 :
          ‖F (j S) - F 0‖ ≤ K * ‖j S‖ := by
        simpa only [map_zero, sub_zero] using hdiff
      have hdiff' :
          ‖F (j S) - F 0‖ ≤ K₀ * ‖j S‖ := by
        refine hdiff0.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _)
      calc
        ‖F (j S)‖ = ‖(F (j S) - F 0) + F 0‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖F (j S) - F 0‖ + ‖F 0‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
        _ ≤ K₀ * ‖j S‖ + ‖F 0‖ := add_le_add hdiff' le_rfl
  rcases hall with hlarge | hbound
  · exact (not_le_of_gt (hv.trans_lt (lt_add_one R)) hlarge).elim
  · refine hbound.trans ?_
    simpa only [C] using
      add_le_add (mul_le_mul_of_nonneg_left hv hK₀) (le_refl ‖F 0‖)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
