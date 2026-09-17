import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimMetricTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedTimeTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance pointedTimeCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance pointedTimeSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance pointedTimeC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance pointedTimeT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

private local instance pointedTimeMetricTopology
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace F.M := F.topology
private local instance pointedTimeMetricCharted
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H F.M := F.charted
private local instance pointedTimeMetricSmooth
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ F.M := F.smooth
private local instance pointedTimeMetricC1
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance pointedTimeMetricT2
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space F.M := F.t2

theorem exists_pointed_metric_time_modulus_on_compact
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (C : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) k)
    (K : Set L.M) (hK : IsCompact K) (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ i in atTop, K ⊆ Phi.source i ∧
      ∀ s ∈ Icc a 0, ∀ t ∈ Icc a 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
        |((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) -
          ((X.term (phi i)).S.base.metric s).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v)| ≤
          B * (L.S.base.metric 0).inner x v v * |t - s| := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hdim := (hsource 0).dimension_ge_two
    omega⟩
  obtain ⟨C0, hC0, hscalar⟩ := exists_pointed_scalar_bound_on_compact C hcanonical K hK
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C href K hK 1 zero_lt_one
  refine ⟨2 * C0 * Real.exp (C0 * (-a)), by positivity, ?_⟩
  filter_upwards [hscalar, Filter.eventually_ge_atTop k0] with i hi hik
  refine ⟨hi.1, fun s hs t ht x hx v => ?_⟩
  have hquad := (hk0 i hik).2 x hx v
  have hterminal : ((X.term (phi i)).S.base.metric 0).inner (Phi.map i x)
      (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) ≤
        2 * (L.S.base.metric 0).inner x v v := by
    have hupper := (abs_le.mp hquad).2
    change ((X.term (phi i)).S.base.metric 0).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) -
      (L.S.base.metric 0).inner x v v ≤ (1 : ℝ) * (L.S.base.metric 0).inner x v v at hupper
    linarith
  have hscalarSource : (X.term (phi i)).S.scalar 0 (Phi.map i x) ≤ C0 :=
    (le_abs_self _).trans (hi.2 x hx)
  have htime := (hsource (phi i)).metric_inner_time_difference_le
    hs ht (Phi.map i x) hscalarSource (mfderiv I I (Phi.map i) x v)
  apply htime.trans
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hterminal
      (by positivity : 0 ≤ C0 * Real.exp (C0 * (-a)))) (abs_nonneg (t - s))
  convert hmul using 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
