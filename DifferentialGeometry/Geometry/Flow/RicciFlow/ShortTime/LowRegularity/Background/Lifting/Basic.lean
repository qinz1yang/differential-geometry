import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Lifting.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Time.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FirstOrder.Decomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Time.SecondOrderAffineRegularity

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccToHsLin smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

structure BackgroundLiftOps (g : SmoothRiemannianMetric I M) where
  firstOrderActionThirdToSecondOrder : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
  firstOrderActionSecondToFirstOrder : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))

theorem HasLowRegularityBoundsAt.realizeCc
    {g gB : SmoothRiemannianMetric I M}
    {K : LowRegularityBoundParameters}
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K)
    (S : SmoothCcTensor g 0 2)
    (hS : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ K.realize) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) K.threshold := by
  apply hK.metric_realization S
  rw [show (((1 : ℕ) : ℝ) + 1) = 2 by norm_num]
  have heq :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S =
        smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S :=
    TensorHs.ext (funext fun _ => rfl)
  rw [← heq]
  exact hS

namespace BackgroundLiftParameters

theorem realize
    {g gB : SmoothRiemannianMetric I M}
    {K : LowRegularityBoundParameters} (D : BackgroundLiftParameters K)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K)
    (S : SmoothCcTensor g 0 2)
    (hS : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤
      D.coeffRadius) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) K.threshold :=
  hK.realizeCc S (hS.trans D.coeffRadius_le_realize)

end BackgroundLiftParameters

structure IsBackgroundSecondOrderActionAt
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K)
    (D : BackgroundLiftParameters K) : Prop where
  secondOrderActionFourthToSecondOrder_continuous : Continuous
    (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  secondOrderActionThirdToFirstOrder_continuous : Continuous
    (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  secondOrderActionFourthToSecondOrder_norm_le : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  secondOrderActionThirdToFirstOrder_norm_le : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  secondOrderActionFourthToSecondOrder_ccTensorToHs : ∀ S : SmoothCcTensor g 0 2,
    lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreActionCoefficientsBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).secondOrderActionFourthToSecondOrder
          (I := I) (M := M)
  secondOrderActionThirdToFirstOrder_ccTensorToHs : ∀ S : SmoothCcTensor g 0 2,
    lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreActionCoefficientsBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).secondOrderActionThirdToFirstOrder
          (I := I) (M := M)
  secondOrderAction_extensions_commute : ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
          hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v) =
      (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num))

structure IsBackgroundFirstOrderActionAt
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K)
    (D : BackgroundLiftParameters K) (F : BackgroundLiftOps (I := I) (M := M) g) : Prop where
  firstOrderActionThirdToSecondOrder_continuous : Continuous F.firstOrderActionThirdToSecondOrder
  firstOrderActionSecondToFirstOrder_continuous : Continuous F.firstOrderActionSecondToFirstOrder
  firstOrderActionThirdToSecondOrder_norm_le : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.firstOrderActionThirdToSecondOrder x‖ ≤ D.zero + D.slope * ‖x‖
  firstOrderActionSecondToFirstOrder_norm_le : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.firstOrderActionSecondToFirstOrder x‖ ≤ D.zero + D.slope * ‖x‖
  firstOrderActionThirdToSecondOrder_ccTensorToHs : ∀ S : SmoothCcTensor g 0 2,
    F.firstOrderActionThirdToSecondOrder (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).firstOrderActionThirdToSecondOrder
          (I := I) (M := M)
  firstOrderActionSecondToFirstOrder_ccTensorToHs : ∀ S : SmoothCcTensor g 0 2,
    F.firstOrderActionSecondToFirstOrder (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).firstOrderActionSecondToFirstOrder
          (I := I) (M := M)
  firstOrderAction_extensions_commute : ∀ x : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp (F.firstOrderActionThirdToSecondOrder x) =
      (F.firstOrderActionSecondToFirstOrder x).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num))

structure IsBackgroundLiftAt
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K)
    (D : BackgroundLiftParameters K) (F : BackgroundLiftOps (I := I) (M := M) g) : Prop extends
  IsBackgroundSecondOrderActionAt (I := I) (M := M) g gB K hK D,
  IsBackgroundFirstOrderActionAt (I := I) (M := M) g gB K hK D F

theorem background_first_order_operator_of_decomposition
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegularityBoundParameters}
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ D : BackgroundLiftParameters K, D.coeffRadius ≤ ρ0 →
        ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
          (Z ≤ D.zero → L ≤ D.slope →
            ∃ F : BackgroundLiftOps (I := I) (M := M) g,
              IsBackgroundFirstOrderActionAt (I := I) (M := M) g gB K hK D F) := by
  obtain ⟨ρ1, hρ1, hpack⟩ := exists_background_first_order_continuous_operator_extensions (I := I) (M := M) hDim g gB
  obtain ⟨ρ2, hρ2, hdel⟩ := hasBackgroundDifferenceContinuousOperatorExtensions (I := I) (M := M) hDim g gB
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, ?_⟩
  intro D hD
  obtain ⟨Z1, L1, hZ1, hL1, FHi, FLo, hFHi, hFLo, hHiCore, hLoCore,
      hHiBd, hLoBd, hcomm⟩ :=
    hpack D.coeffRadius_pos (hD.trans (min_le_left _ _))
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
  obtain ⟨Z0, L0, hZ0, hL0, GHi, GLo, hGHi, hGLo, hGHiCore, hGLoCore,
      hGHiBd, hGLoBd, hGcomm⟩ :=
    hdel D.coeffRadius_pos (hD.trans (min_le_right _ _))
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
  refine ⟨Z1 + Z0, L1 + L0, add_nonneg hZ1 hZ0, add_nonneg hL1 hL0,
    fun hZD hLD => ⟨⟨fun x => FHi x + GHi x, fun x => FLo x + GLo x⟩, ?_⟩⟩
  refine
    { firstOrderActionThirdToSecondOrder_continuous := hFHi.add hGHi
      firstOrderActionSecondToFirstOrder_continuous := hFLo.add hGLo
      firstOrderActionThirdToSecondOrder_norm_le := ?_
      firstOrderActionSecondToFirstOrder_norm_le := ?_
      firstOrderActionThirdToSecondOrder_ccTensorToHs := ?_
      firstOrderActionSecondToFirstOrder_ccTensorToHs := ?_
      firstOrderAction_extensions_commute := ?_ }
  · intro x
    have hsum := norm_add_le (FHi x) (GHi x)
    have hx : ‖FHi x‖ + ‖GHi x‖ ≤ D.zero + D.slope * ‖x‖ := by
      calc
        ‖FHi x‖ + ‖GHi x‖ ≤ (Z1 + L1 * ‖x‖) + (Z0 + L0 * ‖x‖) :=
          add_le_add (hHiBd x) (hGHiBd x)
        _ = (Z1 + Z0) + (L1 + L0) * ‖x‖ := by ring
        _ ≤ D.zero + D.slope * ‖x‖ :=
          add_le_add hZD (mul_le_mul_of_nonneg_right hLD (norm_nonneg x))
    exact hsum.trans hx
  · intro x
    have hsum := norm_add_le (FLo x) (GLo x)
    have hx : ‖FLo x‖ + ‖GLo x‖ ≤ D.zero + D.slope * ‖x‖ := by
      calc
        ‖FLo x‖ + ‖GLo x‖ ≤ (Z1 + L1 * ‖x‖) + (Z0 + L0 * ‖x‖) :=
          add_le_add (hLoBd x) (hGLoBd x)
        _ = (Z1 + Z0) + (L1 + L0) * ‖x‖ := by ring
        _ ≤ D.zero + D.slope * ‖x‖ :=
          add_le_add hZD (mul_le_mul_of_nonneg_right hLD (norm_nonneg x))
    exact hsum.trans hx
  · intro S
    change FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
        GHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) = _
    rw [hHiCore S, hGHiCore S]
    exact (combinedLowerScaleActionCoefficientsBackground_firstOrderActionThirdToSecondOrder_decomposition (I := I) (M := M) hDim g gB
      D.coeffRadius_pos.le hK.threshold_nonneg hK.threshold_le_third
      (D.realize hK) S).symm
  · intro S
    change FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
        GLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) = _
    rw [hLoCore S, hGLoCore S]
    exact (combinedLowerScaleActionCoefficientsBackground_firstOrderActionSecondToFirstOrder_decomposition (I := I) (M := M) hDim g gB
      D.coeffRadius_pos.le hK.threshold_nonneg hK.threshold_le_third
      (D.realize hK) S).symm
  · intro x
    apply ContinuousLinearMap.ext
    intro v
    have h1 := DFunLike.congr_fun (hcomm x) v
    have h2 := DFunLike.congr_fun (hGcomm x) v
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    change tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num) ((FHi x + GHi x) v) =
      (FLo x + GLo x)
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num) v)
    simp only [add_apply, map_add, h1, h2]

theorem isBackgroundSecondOrderActionAt_of_radial
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegularityBoundParameters}
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 ≤ C ∧
      ∀ D : BackgroundLiftParameters K, D.coeffRadius ≤ ρ0 →
        (C * D.coeffRadius ≤ D.contract →
          IsBackgroundSecondOrderActionAt (I := I) (M := M) g gB K hK D) := by
  obtain ⟨ρL, _CL, hρL, _hρL_le, hlip⟩ :=
    radialSecondOrderActionBackground_lipschitz (I := I) (M := M) hDim g gB K.realize_pos
      hK.threshold_nonneg hK.threshold_le_third hK.realizeCc
  obtain ⟨ρS, C, hρS, _hρS_le, hC, hsmall⟩ :=
    lowerScaleSecondOrderActionBackground_small (I := I) (M := M) hDim g gB K.realize_pos
      hK.threshold_nonneg hK.threshold_le_third hK.realizeCc
  refine ⟨min ρL ρS, C, lt_min hρL hρS, hC, ?_⟩
  intro D hD hdom
  have hr0 : (0 : ℝ) ≤ D.coeffRadius := D.coeffRadius_pos.le
  have hrL : D.coeffRadius ≤ ρL := hD.trans (min_le_left _ _)
  have hrS : D.coeffRadius ≤ ρS := hD.trans (min_le_right _ _)
  obtain ⟨-, -, hcoreHi, hcoreLo, -⟩ := hlip hr0 hrL
  obtain ⟨hcontHi, hcontLo, hbdHi, hbdLo, hsq⟩ := hsmall hr0 hrS
  exact
    { secondOrderActionFourthToSecondOrder_continuous := hcontHi
      secondOrderActionThirdToFirstOrder_continuous := hcontLo
      secondOrderActionFourthToSecondOrder_norm_le := fun v => (hbdHi v).trans hdom
      secondOrderActionThirdToFirstOrder_norm_le := fun v => (hbdLo v).trans hdom
      secondOrderActionFourthToSecondOrder_ccTensorToHs := hcoreHi
      secondOrderActionThirdToFirstOrder_ccTensorToHs := hcoreLo
      secondOrderAction_extensions_commute := hsq }

theorem bgLift_of_radial
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegularityBoundParameters}
    (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 ≤ C ∧
      ∀ D : BackgroundLiftParameters K, D.coeffRadius ≤ ρ0 →
        ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
          (Z ≤ D.zero → L ≤ D.slope → C * D.coeffRadius ≤ D.contract →
            ∃ F : BackgroundLiftOps (I := I) (M := M) g,
              IsBackgroundLiftAt (I := I) (M := M) g gB K hK D F) := by
  obtain ⟨ρ1, hρ1, hA1⟩ := background_first_order_operator_of_decomposition (I := I) (M := M) hDim g gB hK
  obtain ⟨ρ2, C, hρ2, hC, hA2⟩ :=
    isBackgroundSecondOrderActionAt_of_radial (I := I) (M := M) hDim g gB hK
  refine ⟨min ρ1 ρ2, C, lt_min hρ1 hρ2, hC, ?_⟩
  intro D hD
  obtain ⟨Z, L, hZ, hL, hF⟩ := hA1 D (hD.trans (min_le_left _ _))
  refine ⟨Z, L, hZ, hL, fun hZD hLD hdom => ?_⟩
  obtain ⟨F, hF1⟩ := hF hZD hLD
  exact ⟨F,
    { toIsBackgroundSecondOrderActionAt := hA2 D (hD.trans (min_le_right _ _)) hdom
      toIsBackgroundFirstOrderActionAt := hF1 }⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
