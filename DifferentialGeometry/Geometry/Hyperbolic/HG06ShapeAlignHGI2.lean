import DifferentialGeometry.Geometry.Hyperbolic.TruncationStability

/-!
# HG06 in the ch12 D-R3-19 minimal-binder form (S-HG-INTAKE-2, suffix `_HGI2`)

ch12 D-R3-19 keeps the donor's single pair `∃ ξ n` as the minimal binder:
`ξ = 1 / (n + 1)`, `η⁻¹ < ξ⁻¹`, and for every competitor `H'` (second universe `v`) with at least
as many ends, every `isMetricApproximationOnBall … ξ⁻¹ (n + 1) ξ` is `η`-close (in `sSup` of the
distance on the ball of radius `η⁻¹`) to a distance isometry `e : H.Carrier ≃ᵢ H'.Carrier`.

Here the full shape is written out explicitly, three ways:

* `hg06_truncation_form_HGI2`: with `Tr.count ≤ Tr'.count` (donor `TruncationStability.lean:25–42`);
* `hg06_endCount_form_HGI2`: with `endCount H.Carrier ≤ endCount H'.Carrier` and **no** truncation
  (donor `Stability.lean:230`, applied to `H.metric`);
* `hg06_count_le_iff_endCount_le_HGI2`: the two hypotheses agree once truncations are given
  (`TruncationEnds.endCount_eq_count`).

So the ends-count hypothesis of D-R3-19 needs HG03 only if it is stated in terms of `Tr.count`.
-/

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel

universe u v

private theorem curvature_identity_HGI2 (H : FiniteVolumeHyperbolicModel)
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

/-- the ends-count hypothesis in terms of truncations: `Tr.count ≤ Tr'.count` is the same as
`endCount H.Carrier ≤ endCount H'.Carrier` -/
theorem hg06_count_le_iff_endCount_le_HGI2 {H : FiniteVolumeHyperbolicModel.{u}}
    {H' : FiniteVolumeHyperbolicModel.{v}} (Tr : HyperbolicTruncation H)
    (Tr' : HyperbolicTruncation H') :
    Tr.count ≤ Tr'.count ↔
      Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier := by
  rw [Tr.endCount_eq_count, Tr'.endCount_eq_count]
  exact ENat.natCast_le_natCast.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- HG06, truncation form (D-R3-19 shape with `Tr.count ≤ Tr'.count`) -/
theorem hg06_truncation_form_HGI2
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
              (Subtype.val ⁻¹' Metric.closedBall o η⁻¹)) < η :=
  exists_isometry_close_of_truncation_count_le.{u, v} H o hη

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- HG06, ends-count form (D-R3-19 shape with `endCount ≤ endCount`, no truncation / HG03) -/
theorem hg06_endCount_form_HGI2
    (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) {η : ℝ} (hη : 0 < η) :
    letI : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
    letI : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
    letI : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{v}),
        Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier →
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
      (curvature_identity_HGI2 H) o hη
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro H' hends Ω f hf
  exact hclose H'.Carrier H'.metric H'.complete H'.finite_volume
    (curvature_identity_HGI2 H') hends Ω f hf

end DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeHyperbolicModel
