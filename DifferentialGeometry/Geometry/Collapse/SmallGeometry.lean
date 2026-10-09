import DifferentialGeometry.Topology.Manifold.SmallTransport
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Sectional
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback

/-!
The outer small smooth model preserves the original volume scales and curvature data.
All identities use its actual diffeomorphism and genuine Riemannian metric pullback.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

variable {M : Type u} [i1 : MetricSpace M] [i2 : ChartedSpace E3 M] [i3 : IsManifold I3 ∞ M]
  [i4 : SigmaCompactSpace M] (S : SmallManifoldModel (I := I3) M)

instance smallModelSigmaCompact : SigmaCompactSpace S.Carrier :=
  S.diffeo.toHomeomorph.isClosedEmbedding.sigmaCompactSpace

private local instance measurableSource : MeasurableSpace M := borel M
private local instance borelSource : BorelSpace M := ⟨rfl⟩
private local instance measurableSmall : MeasurableSpace S.Carrier := borel S.Carrier
private local instance borelSmall : BorelSpace S.Carrier := ⟨rfl⟩

omit [SigmaCompactSpace M] in
theorem smallModel_ball_preimage (g : SmoothRiemannianMetric I3 M)
    (p : S.Carrier) (r : ℝ) :
    riemannianBallOf (S.metric g) p r = S.diffeo ⁻¹' riemannianBallOf g (S.diffeo p) r := by
  ext x
  change riemannianEDistOf (S.metric g) p x < ENNReal.ofReal r ↔
    riemannianEDistOf g (S.diffeo p) (S.diffeo x) < ENNReal.ofReal r
  rw [S.metric_edist]

theorem smallModel_ballVolume (g : SmoothRiemannianMetric I3 M)
    (p : S.Carrier) (r : ℝ) :
    ballVolume (S.metric g) p r = ballVolume g (S.diffeo p) r := by
  rw [ballVolume, SmallManifoldModel.metric, riemannianVolumeMeasure_pullback_cross]
  rw [Measure.map_apply S.diffeo.symm.continuous.measurable]
  · congr 1
    ext x
    change riemannianEDistOf (S.metric g) p (S.diffeo.symm x) < ENNReal.ofReal r ↔
      riemannianEDistOf g (S.diffeo p) x < ENNReal.ofReal r
    rw [S.metric_edist, S.diffeo.apply_symm_apply]
  · exact (isOpen_lt (Riemannian.continuous_riemannianEDist (S.metric g) p)
      continuous_const).measurableSet

theorem smallModel_firstVolumeScale (g : SmoothRiemannianMetric I3 M)
    (p : S.Carrier) (w : ℝ) :
    firstVolumeScale (S.metric g) p w = firstVolumeScale g (S.diffeo p) w := by
  unfold firstVolumeScale
  simp only [smallModel_ballVolume]

omit [SigmaCompactSpace M] in
theorem smallModel_curvatureRadius (g : SmoothRiemannianMetric I3 M) (p : S.Carrier) :
    curvatureRadius (S.metric g) p = curvatureRadius g (S.diffeo p) := by
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf g (S.diffeo p) r,
        SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹) := by
      intro y hy
      have hyS : S.diffeo.symm y ∈ riemannianBallOf (S.metric g) p r := by
        rw [smallModel_ball_preimage]
        simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using hy
      have hbS := hb (S.diffeo.symm y) hyS
      have heq : Diffeomorph.pullbackMetricCross (S.metric g) S.diffeo.symm = g := by
        rw [SmallManifoldModel.metric, Diffeomorph.pullbackMetricCross_trans,
          Diffeomorph.symm_trans_self, Diffeomorph.pullbackMetricCross_refl]
      simpa only [heq] using
        sectionalBoundedBelowAt_pullbackMetricCross (S.metric g) S.diffeo.symm y hbS
    exact le_iSup_of_le hbd le_rfl
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf (S.metric g) p r,
        SectionalBoundedBelowAt (S.metric g) y (-(r ^ 2)⁻¹) := by
      intro y hy
      apply sectionalBoundedBelowAt_pullbackMetricCross g S.diffeo y
      exact hb (S.diffeo y) ((smallModel_ball_preimage S g p r).le hy)
    exact le_iSup_of_le hbd le_rfl

theorem smallModel_curvatureDerivativeNorm (g : SmoothRiemannianMetric I3 M)
    (k : ℕ) (p : S.Carrier) :
    curvatureDerivativeNorm (S.metric g) k p = curvatureDerivativeNorm g k (S.diffeo p) :=
  curvatureDerivativeNorm_of_injective_local_isometry (S.metric g) g S.diffeo
    S.diffeo.isLocalDiffeomorph S.diffeo.injective (S.metric_inner g) k p

omit [SigmaCompactSpace M] in
theorem smallModel_curvDerivNorm (g : SmoothRiemannianMetric I3 M)
    (k : ℕ) (p : S.Carrier) :
    CheegerGromovCompactness.curvDerivNorm k (S.metric g) p =
      CheegerGromovCompactness.curvDerivNorm k g (S.diffeo p) :=
  PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross g S.diffeo k p

end DifferentialGeometry.Geometry.Collapse
