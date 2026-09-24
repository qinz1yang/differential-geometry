import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
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

theorem metric_lower_on_window_of_pointed_convergence
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I)) P phi)
    (C0 : MetricConvergenceData F)
    (hcanonical : ∀ i, C0.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v)
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (pointedCGHMapsOfManifold X P phi F)}
    {hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold X P phi F)}
    {htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold X P phi F)}
    (co : HalfLineMetricConvergenceData
      (pointedCGHMapsOfManifold X P phi F) R bf hsrc htgt) :
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ t ∈ Icc (-T) 0, ∀ x : P.M, ∀ v : TangentSpace I x,
        c * P.metric.inner x v v ≤ (co.gInf t).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro T hT
  obtain ⟨c, hc, hlowerPull⟩ :=
    exists_eventually_pointed_pullback_lower_bound_on_window X hphi F C0 hcanonical hlower T hT
  refine ⟨c, hc, ?_⟩
  intro t ht x v
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htn : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht.2⟩
  have hconv := FlowMetricConvergenceData.metric_convergence_at
    (pointedCGHMapsOfManifold X P phi F) R bf hsrc htgt (-(n : ℝ)) 0
    (co.atWindow (pointedCGHMapsOfManifold X P phi F) n) htn x v v
  apply ge_of_tendsto hconv
  filter_upwards [co.strictMono.tendsto_atTop.eventually
    (hlowerPull {x} isCompact_singleton)] with i hi
  exact hi.2 t ht x (mem_singleton x) v

theorem metric_complete_of_pointed_convergence
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I)) P phi)
    (C0 : MetricConvergenceData F)
    (hcanonical : ∀ i, C0.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hcompleteP : MetricComplete P)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v)
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (pointedCGHMapsOfManifold X P phi F)}
    {hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold X P phi F)}
    {htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold X P phi F)}
    (co : HalfLineMetricConvergenceData
      (pointedCGHMapsOfManifold X P phi F) R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0) :
    MetricComplete ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  obtain ⟨c, hc, hlowerLimit⟩ := metric_lower_on_window_of_pointed_convergence
    X hphi F C0 hcanonical hlower co (1 - t) (by linarith)
  exact MetricComplete.complete_of_lower P hcompleteP (co.gInf t) c hc
    (hlowerLimit t ⟨by linarith, ht⟩)

end DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData
