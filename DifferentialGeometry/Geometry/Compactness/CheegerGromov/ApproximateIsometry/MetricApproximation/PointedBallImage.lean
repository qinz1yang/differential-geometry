import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
universe u uE uH

section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PartialDiffeomorphMetricApproximation.mapsTo_riemannianBallOf
    {P Q : PointedRiemannianManifold.{u, uE, uH} I}
    {Φ : PartialDiffeomorph I I P.M Q.M ∞} {r r₂ R ε : ℝ} {p : ℕ}
    (D : PartialDiffeomorphMetricApproximation
      (riemannianClosedBallOf P.metric P.basepoint r₂) ε p Φ P.metric Q.metric)
    (hr : 0 < r) (hrr₂ : r ≤ r₂)
    (hR : Real.sqrt (1 + ε) * r < R) (hbase : Φ P.basepoint = Q.basepoint) :
    Set.MapsTo Φ (riemannianBallOf P.metric P.basepoint r)
      (riemannianBallOf Q.metric Q.basepoint R) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : Bundle.RiemannianBundle (fun x : P.M => TangentSpace I x) := P.riemBundle
  let : Bundle.RiemannianBundle (fun x : Q.M => TangentSpace I x) := Q.riemBundle
  let : (x : P.M) → InnerProductSpace ℝ (TangentSpace I x) := P.riemInner
  let : (x : Q.M) → InnerProductSpace ℝ (TangentSpace I x) := Q.riemInner
  let : EMetricSpace P.M := P.emetricSpace
  let : EMetricSpace Q.M := Q.emetricSpace
  let : IsRiemannianManifold I P.M := ⟨fun _ _ => rfl⟩
  let : IsRiemannianManifold I Q.M := ⟨fun _ _ => rfl⟩
  have hPnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm P.metric x v
  have hQnorm : ∀ (x : Q.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Q.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm Q.metric x v
  have hclosed : Metric.closedEBall P.basepoint (ENNReal.ofReal r₂) =
      riemannianClosedBallOf P.metric P.basepoint r₂ := by
    ext x
    change edist x P.basepoint ≤ ENNReal.ofReal r₂ ↔ _
    rw [edist_comm]
    rfl
  have hdata : MapMetricApproximationOn
      (Metric.closedEBall P.basepoint (ENNReal.ofReal r₂)) ε p Φ P.metric Q.metric := by
    rw [hclosed]
    exact D.forward
  have hsource : Metric.closedEBall P.basepoint (ENNReal.ofReal r₂) ⊆ Φ.source := by
    rw [hclosed]
    exact D.source_sub
  have himage := hdata.image_eball_subset_closedEBall Φ hPnorm hQnorm hrr₂
    D.forward.eps_pos.le hsource
  intro x hx
  have hx' : x ∈ Metric.eball P.basepoint (ENNReal.ofReal r) := by
    change edist x P.basepoint < ENNReal.ofReal r
    rw [edist_comm]
    exact hx
  have hdist := himage ⟨x, hx', rfl⟩
  rw [Metric.mem_closedEBall, hbase, edist_comm] at hdist
  have hRpos : 0 < R := (mul_nonneg (Real.sqrt_nonneg _) hr.le).trans_lt hR
  exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hR)

end DifferentialGeometry.CheegerGromovCompactness

end
