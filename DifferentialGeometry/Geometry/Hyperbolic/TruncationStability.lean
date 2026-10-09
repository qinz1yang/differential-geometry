import DifferentialGeometry.Geometry.Hyperbolic.Stability
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel

universe u v

private theorem curvature_identity (H : FiniteVolumeHyperbolicModel)
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isometry_close_of_truncation_count_le
    (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) {η : ℝ} (hη : 0 < η) :
    letI : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
    letI : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
    letI : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{v})
        (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H'),
        Tr.count ≤ Tr'.count →
        ∀ (Ω : Set H.Carrier) (f : Ω → H'.Carrier),
          isMetricApproximationOnBall f H.metric H'.metric o ξ⁻¹ (n + 1) ξ →
          letI : TopologicalSpace.MetrizableSpace H'.Carrier :=
            Manifold.metrizableSpace (𝓡 3) H'.Carrier
          letI : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
          letI : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
          ∃ e : H.Carrier ≃ᵢ H'.Carrier,
            sSup ((fun p : Ω => dist (e p) (f p)) ''
              (Subtype.val ⁻¹' Metric.closedBall o η⁻¹)) < η := by
  let _ : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  let _ : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
  obtain ⟨ξ, hξ, n, hn, hr, hclose⟩ :=
    hyperbolic_stability_of_cusp_count_le.{u, v} H.metric H.complete H.finite_volume
      (curvature_identity H) o hη
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro H' Tr Tr' hcount Ω f hf
  have hends : Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier := by
    rw [Tr.endCount_eq_count, Tr'.endCount_eq_count]
    exact ENat.natCast_le_natCast.mpr hcount
  exact hclose H'.Carrier H'.metric H'.complete H'.finite_volume
    (curvature_identity H') hends Ω f hf

end DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel
