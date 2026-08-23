import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.HighRegularityForcing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Affine

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem lowerScaleForceBackground_eq
    (g gB : SmoothRiemannianMetric I M) :
    lowerScaleForceBackground (I := I) (M := M) g gB =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)
        (staticForce (I := I) (M := M) g gB (2 : ℝ)) := by
  change
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)
        (zeroStateDeTurckRemainderH2 (I := I) (M := M) g gB) = _
  rw [staticForcing_eq_zeroStateDeTurckRemainderH2]

noncomputable def liftHiNBackground
    (g gB : SmoothRiemannianMetric I M)
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
  staticForce (I := I) (M := M) g gB (2 : ℝ) +
    lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
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

noncomputable def lowerScaleNBackgroundWith
    (g gB : SmoothRiemannianMetric I M)
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
  lowerScaleForceBackground (I := I) (M := M) g gB +
    lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    FLo u
      (lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u))

theorem hiNBackground_incl
    (g gB : SmoothRiemannianMetric I M)
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
          (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w) =
        (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiNBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal FHi v) =
      lowerScaleNBackgroundWith (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FLo
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
      (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)) =
      lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal
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
  rw [show liftHiNBackground (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FHi v =
      staticForce (I := I) (M := M) g gB (2 : ℝ) +
        lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w
          (radialCLM (I := I) (M := M) g
            (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v) +
        FHi u (lowRadialH3 (I := I) (M := M) g ρ u) from rfl,
    show lowerScaleNBackgroundWith (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FLo u =
      lowerScaleForceBackground (I := I) (M := M) g gB +
        lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
          (lowRadialH3 (I := I) (M := M) g ρ u) +
        FLo u
          (lowRadialHs (I := I) (M := M) g ρ
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) from rfl,
    map_add, map_add, (lowerScaleForceBackground_eq (I := I) (M := M) g gB).symm,
    hA2, hA1, hudef]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
