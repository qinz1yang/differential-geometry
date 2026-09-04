import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.GalerkinForcingTerms

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem galN_evalBackground (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (ccTensor02Symm (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
        (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) := by
  have hsub :
      (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ :
          lowerState (I := I) (M := M) g₀ 1 R) =
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
            (galCoreRep (I := I) (M := M) g₀ R S c),
          galCoreRep_ball (I := I) (M := M) g₀ hR.le S c⟩ :=
    Subtype.ext (galCoreRep_eq (I := I) (M := M) g₀ R S c).symm
  rw [hsub]
  exact deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR.le S c)

theorem galTermIdBackground (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)).secondOrderAction
            (I := I) (M := M)
            (ccTensor02Symm (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) +
          (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)).firstOrderAction
            (I := I) (M := M)
            (ccTensor02Symm (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c))) := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  set W := ccTensor02Symm (I := I) (M := M) g₀
    (galCoreRep (I := I) (M := M) g₀ R S c) with hW
  set U : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
      galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ with hU
  set Z : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ with hZ
  let P := galRepFib (I := I) (M := M) g₀ hR.le hreal S c
  let P₀ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal
  let N := deTurckSmoothN (I := I) (M := M) g₀ g_bg 1 W hδ P
  let N₀ := deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
    (0 : SmoothCcTensor g₀ 0 2) hδ P₀
  let Rm := deTurckSmoothRemainder (I := I) g₀ g_bg W hδ P
  let Rm₀ := deTurckSmoothRemainder (I := I) g₀ g_bg
    (0 : SmoothCcTensor g₀ 0 2) hδ P₀
  set A :=
    (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg W hδ P P₀).secondOrderAction
        (I := I) (M := M) W +
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg W hδ P P₀).firstOrderAction
        (I := I) (M := M) W with hA
  have h₁ :
      deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal U -
          deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal Z =
        N - N₀ := by
    dsimp only [N, N₀, P, P₀, W]
    rw [hU, hZ]
    rw [galN_evalBackground (I := I) (M := M) g₀ g_bg hR hδ hreal hcore S c,
      deTurckRemainderOnLowerState_zero_eq_deTurckRHS (I := I) (M := M) g₀ g_bg hR hδ hreal hcore,
      ← deTurckSmoothN_zero (I := I) (M := M) g₀ g_bg 1 hδ
        (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)]
  have h₂ : N - N₀ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) (Rm - Rm₀) := by
    dsimp only [N, N₀, Rm, Rm₀, P, P₀]
    exact deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub (I := I) (M := M)
      g₀ g_bg 1 _ _ hδ _ hδ _
  have hsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g₀ W x u v = ccTensorBilin (I := I) g₀ W x v u := by
    rw [hW]
    exact smoothCcTensorBilinForm_ccTensor02Symm_symm
      (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R S c)
  have h₃ : Rm - Rm₀ = A := by
    rw [hA]
    dsimp only [Rm, Rm₀]
    exact (hsplit W hsymm hδ3 hδ0 P P₀).1
  exact h₁.trans (h₂.trans
    (congrArg (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)) h₃))

theorem galTermCapBackground (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderCoefficient.toSection x) ≤
          Cδ ^ 2 := by
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  refine ⟨K * (δ / (1 - δ) ^ 2),
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro S c x
  exact (hsplit _
    (smoothCcTensorBilinForm_ccTensor02Symm_symm (I := I) (M := M)
      g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
    hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR hreal S c)
      (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).2 x

def galerkinActionVectorBackground (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
    ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderAction
        (I := I) (M := M)
        (ccTensor02Symm (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c)) +
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).firstOrderAction
        (I := I) (M := M)
        (ccTensor02Symm (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c)))

open scoped Classical in
theorem galForceTermBackground (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        S c i =
      if i ∈ S then
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩).coeff i +
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).secondOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)) +
              (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).firstOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)))).coeff i
      else 0 := by
  have harm := galTermIdBackground (I := I) (M := M) g₀ g_bg
    (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ hδ0 hδ3
    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal) hcore S c
  have hval :
      boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius Ctop B1 ρ P) S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le S c⟩ =
        boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩ +
          smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).secondOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)) +
              (lowerScaleActionCoefficients (I := I) (M := M) g₀ g_bg
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).firstOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c))) :=
    sub_eq_iff_eq_add'.mp harm
  rw [galTameForce_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, hval, TensorHs.add_coeff]
  · rw [if_neg hi, if_neg hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
