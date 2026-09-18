import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowConvergence

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

omit [I.Boundaryless] in
theorem eventually_pointed_pullback_lower_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData (I := I) F)
    (hreference : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    {times : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ᶠ i in atTop, ∀ t ∈ times,
      ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
        c * ((X.term i).S.base.metric 0).inner x v v ≤
          ((X.term i).S.base.metric t).inner x v v) :
    ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      K ⊆ F.source i ∧ ∀ t ∈ times, ∀ x ∈ K, ∀ v : TangentSpace I x,
        (c / 2) * P.metric.inner x v v ≤
          ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro K hK
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control
    C hreference K hK (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop N, hphi.eventually hlower] with i hi hlow
  refine ⟨(hN i hi).1, ?_⟩
  intro t ht x hx v
  have hclose := (abs_le.mp ((hN i hi).2 x hx v)).1
  change -(1 / 2 * P.metric.inner x v v) ≤
    ((X.term (phi i)).S.base.metric 0).inner (F.map i x)
      (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) -
    P.metric.inner x v v at hclose
  have hhalf : (1 / 2) * P.metric.inner x v v ≤
      ((X.term (phi i)).S.base.metric 0).inner (F.map i x)
        (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hhalf hc
  have htime := hlow t ht (F.map i x) (mfderiv I I (F.map i) x v)
  nlinarith

omit [I.Boundaryless] in
theorem exists_eventually_pointed_pullback_lower_bound_on_window
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData (I := I) F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0,
        ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
        K ⊆ F.source i ∧ ∀ t ∈ Icc (-T) 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
          c * P.metric.inner x v v ≤
            ((X.term (phi i)).S.base.metric t).inner (F.map i x)
              (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v) := by
  intro T hT
  obtain ⟨c, hc, hlow⟩ := hlower T hT
  refine ⟨c / 2, div_pos hc (by norm_num),
    eventually_pointed_pullback_lower_bound X hphi F C ?_ hc.le hlow⟩
  intro i
  rw [hcanonical i]
  exact canonicalSourceData_referenceMetric_eq_limitMetric F i

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_pointed_metric_extension_lower_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (bf : BumpFamily (pointedCGHMapsOfManifold X P phi F))
    (hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold X P phi F))
    (htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold X P phi F))
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
        ∀ t ∈ Icc (-T) 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
          c * P.metric.inner x v v ≤
            (gSeqExt (pointedCGHMapsOfManifold X P phi F)
              P.metric bf hsrc htgt i t).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro T hT
  obtain ⟨c, hc, hlow⟩ := exists_eventually_pointed_pullback_lower_bound_on_window
    X hphi F C hcanonical hlower T hT
  refine ⟨c, hc, fun K hK => ?_⟩
  have heq := eventually_gSeqExt_eq_pullback
    (pointedCGHMapsOfManifold X P phi F) P.metric bf hsrc htgt K hK
  filter_upwards [hlow K hK, heq] with i hi hGi
  obtain ⟨U, _hU, hKU, _hUsrc, hG⟩ := hGi
  intro t ht x hx v
  rw [hG t x (hKU hx) v v]
  exact hi.2 t ht x hx v

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
