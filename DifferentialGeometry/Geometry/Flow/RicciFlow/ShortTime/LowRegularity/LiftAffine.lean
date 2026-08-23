import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.StaticForcingLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FirstOrderDecomposition
import DifferentialGeometry.Analysis.DenseExtension

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic (lowerState)
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensorToHs_add ccTensorToHs_coeff ccToHsLin ccToHsLin_apply
    ccToHsLin_dense deTurckSmoothN deTurckSmoothRemainder
    deTurckSmoothRemainderTensorHs norm_smoothCcToTensorHs_symmS_le smoothCcToTensorHs
    tensorHsInclusion_smoothCcToTensorHs)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem smoothCcToTensorHs_eq_ccToHs (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g σ S =
      ccTensorToHs (I := I) (M := M) g 2 σ S :=
  tensorHs.ext (funext fun _ => rfl)

theorem tensorHsCongr_smoothCc (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (S : SmoothCcTensor g 0 2) :
    tensorHsCongr (I := I) (M := M) g 0 2 hab
        (smoothCcToTensorHs (I := I) (M := M) g a S) =
      smoothCcToTensorHs (I := I) (M := M) g b S := by
  cases hab
  rfl

theorem tensorHsInclusion_ccToHs (g : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (S : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (ccTensorToHs (I := I) (M := M) g 2 σ S) =
      ccTensorToHs (I := I) (M := M) g 2 τ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff, ccTensorToHs_coeff]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem tensorHsCongr_symm_self (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (u : tensorHs (I := I) (M := M) g 0 2 a) :
    tensorHsCongr (I := I) (M := M) g 0 2 hab.symm
        (tensorHsCongr (I := I) (M := M) g 0 2 hab u) = u := by
  cases hab
  rfl

theorem norm_smoothCc_congr (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (S : SmoothCcTensor g 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g a S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g b S‖ := by
  cases hab
  rfl

theorem deTurckSmoothN_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) :=
  rfl

omit [SigmaCompactSpace M] in
theorem deTurckSmoothRem_congr (g₀ g_bg : SmoothRiemannianMetric I M)
    {S U : SmoothCcTensor g₀ 0 2} (h : S = U) {δ : ℝ} (hδ_lt : δ < 1)
    (hS : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hU : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ U) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg S hδ_lt hS =
      deTurckSmoothRemainder (I := I) g₀ g_bg U hδ_lt hU := by
  subst h
  rfl

section A1

variable (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}

abbrev LowA1CorePair (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ S U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
              (I := I) (M := M) -
            (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
              (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

variable {g}


theorem lowerScaleFirstOrderActionSecondToFirstOrder_core {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : LowA1CorePair (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (S : SmoothCcTensor g 0 2) :
    lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
        (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (fun U => (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
      (I := I) (M := M))
    (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore_value (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    hpair S


theorem lowerScaleFirstOrderActionSecondToFirstOrder_continuous {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : LowA1CorePair (I := I) (M := M) g hρ hδ0 hδ_le hreal) :
    Continuous (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (fun U => (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal U).firstOrderActionSecondToFirstOrder
      (I := I) (M := M))
    (LowerScaleTimeInternal.firstOrderActionSecondToFirstOrderCore_value (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    hpair

end A1

noncomputable def lowerScaleNonlinearityWithFirstOrderOperator
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  lowerScaleForce (I := I) (M := M) g +
    lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    FLo u
      (lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u))

theorem lowerScaleN_cont
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hA2 : Continuous (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal))
    (hA1 : Continuous (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal)) :
    Continuous (lowerScaleN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) := by
  have hincl : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)).continuous
  have h2 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((hA2.comp hincl).prodMk (lowRadialH3_cont (I := I) (M := M) g hρ))
  have h1 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hA1.prodMk
        ((lowRadialHs_cont (I := I) (M := M) g hρ.le).comp hincl))
  exact (continuous_const.add h2).add h1

theorem lowerScaleNonlinearityWithFirstOrderOperator_continuous
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hA2 : Continuous (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal))
    (hFLo : Continuous FLo) :
    Continuous (lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal FLo) := by
  have hincl : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)).continuous
  have h2 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((hA2.comp hincl).prodMk (lowRadialH3_cont (I := I) (M := M) g hρ))
  have h1 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      FLo u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hFLo.prodMk ((lowRadialHs_cont (I := I) (M := M) g hρ.le).comp hincl))
  exact (continuous_const.add h2).add h1

theorem deTurckRemainderOnLowerState_affine
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hreal' : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hNcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ hreal))
    (hA2cont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g₀ 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder
          (I := I) (M := M))
    (FLo : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFcore : ∀ S : SmoothCcTensor g₀ 0 2,
      FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
          (firstOrderCoreActionCoefficients (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (w : lowerState (I := I) (M := M) g₀ 1 R) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal w) =
      lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
        (tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) w.1) := by
  classical
  have hzeroNorm : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
      (0 : SmoothCcTensor g₀ 0 2)‖ ≤ ρ := by
    rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2) = 0 by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ))]
    simpa only [norm_zero] using hρ.le
  have hΦcont : Continuous fun v : lowerState (I := I) (M := M) g₀ 1 R =>
      tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal v) :=
    (tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).continuous.comp hNcont
  have hΨcont : Continuous fun v : lowerState (I := I) (M := M) g₀ 1 R =>
      lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
        (tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1) :=
    (lowerScaleNonlinearityWithFirstOrderOperator_continuous (I := I) (M := M) g₀ hρ hδ0 hδ_le hreal'
        FLo hA2cont hFLo).comp
      ((tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)).continuous.comp
          continuous_subtype_val)
  have hclosed : IsClosed {v : lowerState (I := I) (M := M) g₀ 1 R |
      tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
        lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
          (tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    isClosed_eq hΦcont hΨcont
  have hsub : smoothCore (I := I) (M := M) g₀ R ⊆
      {v : lowerState (I := I) (M := M) g₀ 1 R |
        tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
          lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} := by
    intro v hv
    obtain ⟨S, hS⟩ := hv
    have hball : ‖tensorHsInclusion (I := I) (M := M) (g := g₀)
        (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R := by
      rw [hS]
      exact v.2
    have hnorm : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R := by
      rwa [tensorHsInclusion_smoothCcToTensorHs] at hball
    have hnorm2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S‖ ≤ R := by
      rw [← smoothCcToTensorHs_eq_ccToHs,
        ← norm_smoothCc_congr (I := I) (M := M) g₀
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S]
      exact hnorm
    have hsymm2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (symmS (I := I) (M := M) g₀ S)‖ ≤ ρ := by
      refine le_trans ?_ (le_trans hnorm2 hRρ)
      rw [← smoothCcToTensorHs_eq_ccToHs, ← smoothCcToTensorHs_eq_ccToHs]
      exact norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (2 : ℝ) S
    have hrad : lowRadial (I := I) (M := M) g₀ ρ S =
        symmS (I := I) (M := M) g₀ S :=
      lowRadial_eq_self (I := I) (M := M) g₀ S hsymm2
    have hveq : v = ⟨smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S, hball⟩ := Subtype.ext hS.symm
    set F := combinedLowerScaleActionCoefficients (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S with hF
    set S' := lowRadial (I := I) (M := M) g₀ ρ S with hS'
    have hsmoothN :
        deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g₀ 1
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball)) =
          smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g₀
              (symmS (I := I) (M := M) g₀ S) hδ
              (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))) := by
      exact deTurckSmoothN_eq (I := I) (M := M) g₀ g₀ 1
        (symmS (I := I) (M := M) g₀ S) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))
    have hLHS : tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))) := by
      rw [hveq,
        deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g₀ hR hδ hreal hcore S hball,
        hsmoothN, tensorHsCongr_smoothCc,
        smoothCcToTensorHs_eq_ccToHs]
    have hu : tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          (v.1 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) =
        ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S := by
      rw [hveq, tensorHsCongr_smoothCc, ccToHsLin_apply,
        smoothCcToTensorHs_eq_ccToHs]
    have hsplit :
        deTurckSmoothRemainder (I := I) g₀ g₀ S' hδ
              (hreal' _ (lowRadial_norm (I := I) (M := M) g₀ hρ.le S)) -
            deTurckSmoothRemainder (I := I) g₀ g₀
              (0 : SmoothCcTensor g₀ 0 2) hδ (hreal' _ hzeroNorm) =
          F.secondOrderAction (I := I) (M := M) S' + F.firstOrderAction (I := I) (M := M) S' :=
      deTurckSmoothRemainder_sub_eq_combined_actions (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S
    have e1 : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S := by
      rw [ccToHsLin_apply, ccToHsLin_apply]
      exact tensorHsInclusion_ccToHs (I := I) (M := M) g₀ _ S
    have e6 : F.secondOrderActionThirdToFirstOrder (I := I) (M := M)
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (F.secondOrderAction (I := I) (M := M) S') := by
      rw [ccToHsLin_apply]
      exact secondOrderActionThirdToFirstOrder_ccTensorToHs (I := I) (M := M) hDim g₀ F S'
    have e7 : FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)
          (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (F.firstOrderAction (I := I) (M := M) S') := by
      rw [hFcore S, ccToHsLin_apply]
      simpa only [F] using
        (combinedLowerScaleActionCoefficients_firstOrderActionSecondToFirstOrder (I := I) (M := M) hDim g₀
          hρ.le hδ0 hδ_le hreal' S S')
    have hRHS : lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M)
          g₀ hρ.le hδ0 hδ_le hreal' FLo
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))) := by
      rw [show lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' FLo
            (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
          lowerScaleForce (I := I) (M := M) g₀ +
            lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'
              (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
                (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S))
              (lowRadialH3 (I := I) (M := M) g₀ ρ
                (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)) +
            FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)
              (lowRadialHs (I := I) (M := M) g₀ ρ
                (tensorHsInclusion (I := I) (M := M) (g := g₀)
                  (r := 0) (s := 2)
                  (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
                  (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S))) from rfl,
        e1,
        lowRadialH3_core (I := I) (M := M) g₀ hρ S,
        lowRadialHs_core (I := I) (M := M) g₀ hρ.le S,
        hA2core S, ← hF, ← hS', e6, e7,
        lowerScaleForce_core (I := I) (M := M) g₀,
        ← ccTensorToHs_add, ← ccTensorToHs_add]
      refine congrArg (ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)) ?_
      have hz0 := deTurckRem_zero (I := I) (M := M) g₀ g₀
        (show (0 : ℝ) < 1 by norm_num)
        (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀)
      have hz1 := deTurckRem_zero (I := I) (M := M) g₀ g₀ hδ
        (hreal' (0 : SmoothCcTensor g₀ 0 2) hzeroNorm)
      have hrem : deTurckSmoothRemainder (I := I) g₀ g₀ S' hδ
            (hreal' _ (lowRadial_norm (I := I) (M := M) g₀ hρ.le S)) =
          deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball)) :=
        deTurckSmoothRem_congr (I := I) (M := M) g₀ g₀ hrad hδ _ _
      rw [← hrem, add_assoc, ← hsplit, hz0, ← hz1]
      abel
    rw [Set.mem_setOf_eq, hLHS, hu, hRHS]
  have hclos : closure (smoothCore (I := I) (M := M) g₀ R) ⊆
      {v : lowerState (I := I) (M := M) g₀ 1 R |
        tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
          lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    hclosed.closure_subset_iff.mpr hsub
  have hw : w ∈ closure (smoothCore (I := I) (M := M) g₀ R) := by
    rw [(smoothCore_dense (I := I) (M := M) g₀ hR).closure_eq]
    trivial
  exact hclos hw

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
