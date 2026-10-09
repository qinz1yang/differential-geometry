import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardSpatialNeck
import DifferentialGeometry.Geometry.Comparison.Toponogov.RemoteTriangleDistortion

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_far_spatialNeck_of_backwardExtension
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ {eps sigma : ℝ} {Phi : ℝ → ℝ}, eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
          ¬ CompactSpace L.space.M → ∀ (D : ℝ), 0 ≤ D → ∀ p : L.space.M,
          ∃ D0 : ℝ, 0 < D0 ∧ ∀ (J : RealTimeInterval) (B : BackwardExtension L J),
            ∀ s ∈ J.carrier,
              (∀ x z : L.space.M, |metricDistance (B.solution.base.metric s) x z -
                metricDistance L.space.metric x z| ≤ D) →
              ∀ y : L.space.M, D0 < metricDistance L.space.metric p y →
                4 < B.solution.scalar s y →
                Nonempty (SpatialNeck (B.solution.base.metric s) (2 * alpha) y) := by
  obtain ⟨epsStar, R, hepsStar, hR, hneck⟩ :=
    exists_spatialNeck_of_backwardExtension_comparisonAngle.{u} kappa ha hsmall
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps sigma pinching heps X L hnoncompact D hD p
  let _ : ConnectedSpace L.space.M := L.connected
  have hcomplete0 : RiemannianMetricComplete L.space.metric := ⟨L.complete.complete⟩
  have hsec0 : SectionalBoundedBelow L.space.metric 0 := by
    intro x v w
    have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [metricRm04StandardAt_apply, hvec] using L.nonnegative x (mem_univ x) v w
  obtain ⟨R0, hR0, htri⟩ := exists_remote_triangle_of_additive_distortion
    L.space.metric hnoncompact hcomplete0 hsec0 p hD
  refine ⟨max R0 (2 * R) + 1, by positivity, ?_⟩
  intro J B s hs hdist y hy hq
  have hyR0 : R0 < metricDistance L.space.metric p y := by
    have hh := le_max_left R0 (2 * R)
    linarith
  have hyR : 2 * R < metricDistance L.space.metric p y := by
    have hh := le_max_right R0 (2 * R)
    linarith
  obtain ⟨z, _hfar, hpy, hyz, hangle⟩ := htri (B.solution.base.metric s) hdist y hyR0
  have hroot : 1 ≤ Real.sqrt (B.solution.scalar s y) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hpnonneg : 0 ≤ metricDistance (B.solution.base.metric s) y p := ENNReal.toReal_nonneg
  have hznonneg : 0 ≤ metricDistance (B.solution.base.metric s) y z := ENNReal.toReal_nonneg
  have hlongp : R < Real.sqrt (B.solution.scalar s y) *
      metricDistance (B.solution.base.metric s) y p := by
    have hmul := mul_le_mul_of_nonneg_right hroot hpnonneg
    change metricDistance L.space.metric p y / 2 < metricDistance (B.solution.base.metric s) y p at hpy
    nlinarith
  have hlongz : R < Real.sqrt (B.solution.scalar s y) *
      metricDistance (B.solution.base.metric s) y z := by
    have hmul := mul_le_mul_of_nonneg_right hroot hznonneg
    change metricDistance L.space.metric p y / 2 < metricDistance (B.solution.base.metric s) y z at hyz
    nlinarith
  exact hneck heps X L J B s hs y p z hq hlongp hlongz hangle

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
