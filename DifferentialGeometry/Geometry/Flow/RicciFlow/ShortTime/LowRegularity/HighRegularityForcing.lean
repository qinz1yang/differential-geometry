import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.CrossScaleCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LiftAffine

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic (lowerState zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccToHsLin deTurckSmoothN smoothCcToTensorHs)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem force_hi_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t))
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂timeMeasure T,
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := by
  have hlo := deTurck_remainder_forcing_eq_smooth_remainder_ae (I := I) (M := M) g₀ g_bg hR hδ
    hreal hcore field fLo hstate hforce F hpin hball
  filter_upwards [hincl, hlo] with t hi hlow
  apply tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
  calc
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t := hi
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := hlow
    _ = tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
          (symmS (I := I) (M := M) g₀ (F t)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) :=
      (deTurckSmoothN_incl (I := I) (M := M) g₀ g_bg
        (a := 1) (b := 2) (by norm_num)
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))).symm

noncomputable def liftHiN
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  staticForce (I := I) (M := M) g g (2 : ℝ) +
    lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v) v) +
    FHi (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (lowRadialH3 (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v))

theorem hiN_incl
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FHi v) =
      lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FLo
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v) := by
  set u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v with hudef
  set w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v with hwdef
  have hwu : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u = w := by
    rw [hudef, hwdef]
    exact (tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v).symm
  have hstat : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (staticForce (I := I) (M := M) g g (2 : ℝ)) =
      lowerScaleForce (I := I) (M := M) g := by
    rw [staticForce_incl (I := I) (M := M) g g
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num),
      lowerScaleForce_eq_static (I := I) (M := M) g]
  have hrad4 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)
      (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
        w v) =
      radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ
        w u := by
    have h := DFunLike.congr_fun
      (radialCLM_incl (I := I) (M := M) g
        (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w) v
    simpa only [ContinuousLinearMap.comp_apply, hudef] using h
  have hrad3 : radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ w u =
      lowRadialH3 (I := I) (M := M) g ρ u := by
    rw [← hwu]
    exact radialCLM_h3 (I := I) (M := M) g hρ u
  have hradlo : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (lowRadialH3 (I := I) (M := M) g ρ u) =
      lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u) :=
    lowRadialH3_incl (I := I) (M := M) g hρ u
  have hA2 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)) =
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) := by
    have h := DFunLike.congr_fun (hA2sq w)
      (radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hrad4, hrad3, hwu]
  have hA1 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (FHi u (lowRadialH3 (I := I) (M := M) g ρ u)) =
      FLo u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) := by
    have h := DFunLike.congr_fun (hFComm u)
      (lowRadialH3 (I := I) (M := M) g ρ u)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hradlo]
  rw [show lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FLo u =
      lowerScaleForce (I := I) (M := M) g +
        lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
          (lowRadialH3 (I := I) (M := M) g ρ u) +
        FLo u
          (lowRadialHs (I := I) (M := M) g ρ
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) from rfl,
    show liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FHi v =
      staticForce (I := I) (M := M) g g (2 : ℝ) +
        lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w
          (radialCLM (I := I) (M := M) g
            (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v) +
        FHi u (lowRadialH3 (I := I) (M := M) g ρ u) from rfl,
    map_add, map_add, hstat, hA2, hA1]

theorem deTurck_remainder_lower_scale_eq_included_higher_order_forcing
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
    (FHi : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)))
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
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (w : lowerState (I := I) (M := M) g₀ 1 R)
    (v : tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ))
    (hv : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v =
      tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) w.1) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal w) =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FHi v) := by
  rw [hiN_incl (I := I) (M := M) g₀ hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm v, hv]
  exact deTurckRemainderOnLowerState_affine (I := I) (M := M) hDim g₀ hR hρ hRρ hδ0 hδ_le hδ
    hreal hreal' hNcont hcore hA2cont hA2core FLo hFLo hFcore w

theorem force_hi_id
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {R ρ δ T : ℝ}
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
    (FHi : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)))
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
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hi : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ))
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hpin : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) (hi t) =
        tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) (state t).1)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal (state t)) :
    (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FHi
        (hi t) := by
  filter_upwards [included_high_order_forcing_eq_deTurck_remainder_ae (I := I) (M := M) g₀ g₀ hR hδ hreal
    (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) state fHi fLo hincl hforce,
    hpin] with t ht hp
  have hcongr := congrArg
    (fun z => tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) z) ht
  simp only at hcongr
  rw [tensorHsCongr_incl (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
      (show (2 : ℝ) = (2 : ℝ) from rfl)
      (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t),
    tensorHsCongr_refl,
    deTurck_remainder_lower_scale_eq_included_higher_order_forcing (I := I) (M := M) hDim g₀ hR hρ hRρ hδ0 hδ_le hδ
      hreal hreal' hNcont hcore hA2cont hA2core FHi FLo hFLo hFcore
      hA2sq hFComm (state t) (hi t) hp] at hcongr
  exact tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) hcongr

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
