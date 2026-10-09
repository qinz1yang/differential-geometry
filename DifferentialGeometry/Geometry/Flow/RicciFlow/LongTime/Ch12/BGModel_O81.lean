import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceRadius_S26

set_option autoImplicit false

/-! # CH12-O81 G3 (part A): relative Bishop–Gromov on a finite-volume hyperbolic model.

`sec_model_O81`: the model metric has `sec ≥ -1/4` everywhere (`metricRm_eq_neg_quarter_S26`).
`bishopGromov_model_O81`: `vol B(p, R) · V(s) ≤ V(R) · vol B(p, s)` for `0 < s ≤ R`,
`V = modelVolume (-1/4) 3` — the final step of `localBishopGromov_cross_of_isometricOn`
(BishopGromovBoundaryBuffer.lean l.323-337) run directly on the complete connected model. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Hyperbolic
open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal NNReal Manifold Topology
universe u
namespace GC.LongTime.Ch12

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem sec_model_O81 (H : FiniteVolumeHyperbolicModel.{u}) (q : H.Carrier) :
    SectionalBoundedBelowAt H.metric q (-(1 / 4 : ℝ)) := by
  intro v w
  rw [metricRm_eq_neg_quarter_S26 H q v w]
  apply le_of_eq
  ring

theorem bishopGromov_model_O81 (H : FiniteVolumeHyperbolicModel.{u}) (p : H.Carrier) {s R : ℝ}
    (hs : 0 < s) (hsR : s ≤ R) :
    ballVolume H.metric p R * ENNReal.ofReal (modelVolume (-(1 / 4 : ℝ)) 3 s) ≤
      ENNReal.ofReal (modelVolume (-(1 / 4 : ℝ)) 3 R) * ballVolume H.metric p s := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  let : IsManifold (𝓡 3) 1 H.Carrier := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.inner, H.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace H.Carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) H.Carrier
  have : CompleteSpace H.Carrier := H.complete.complete
  have : IsRiemannianManifold (𝓡 3) H.Carrier := ⟨fun _ _ => rfl⟩
  have : T2Space (TangentBundle (𝓡 3) H.Carrier) := inferInstance
  have hEnorm : IsMetricNorm (I := 𝓡 3) H.metric :=
    isMetricNorm_of_riemannianBundle (I := 𝓡 3) H.metric
  have hcross := localBishopGromov_cross_endpoint_sectional_three H.metric hEnorm (by simp) p
    (κ := 1 / 4) (by norm_num) hs hsR (fun q _ => sec_model_O81 H q)
  rwa [← collapseBallVolume_eq_comparison H.metric hEnorm,
    ← collapseBallVolume_eq_comparison H.metric hEnorm] at hcross

end GC.LongTime.Ch12
