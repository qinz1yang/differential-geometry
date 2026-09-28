import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

set_option autoImplicit false

noncomputable section

open Set Filter Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvDerivNormSq_restrictOpen (g : SmoothRiemannianMetric I M) (U : Opens M) (k : ℕ)
    (x : U) : curvDerivNormSq k (g.restrictOpen U) x = curvDerivNormSq k g (x : M) := by
  have h : curvCovDeriv (g.restrictOpen U) k x = curvCovDeriv g k (x : M) := by
    ext slots
    exact curvCovDeriv_restrictOpen g U k x slots
  unfold curvDerivNormSq
  rw [Tensor0SBundle.normSq0S_restrictOpen_apply, h]

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.tendsto_curvDerivNormSq (L : G.TerminalLimitMetric) (k : ℕ)
    (x : G.terminalRegularOpen) :
    Tendsto (fun t => curvDerivNormSq k (G.flow.base.metric t) x.val) (𝓝[<] s)
      (𝓝 (curvDerivNormSq k L.metric x)) := by
  have hgram := chartGramMatrix_joint_contMDiffOn L.extendedMetric (Icc a s)
    (L.extendedMetric_jointContMDiffOn le_rfl G.lt)
  have h := normSq0S_jointContMDiffOn L.extendedMetric
    (fun t z => nablaKRm04Field
      (solutionOfMetric (D := RealTimeInterval.univ 0) L.extendedMetric) t k z)
    hgram (fun x₀ K _ ht => nablaKRmChartJoint L.extendedMetric x₀ (hgram x₀) k K ht)
  have hc : ContinuousOn (fun z : ℝ × G.terminalRegularOpen =>
      curvDerivNormSq k (L.extendedMetric z.1) z.2) (Icc a s ×ˢ univ) :=
    h.continuousOn.congr fun z _ =>
      curvNormSq_eq (solutionOfMetric (D := RealTimeInterval.univ 0) L.extendedMetric) k z.1 z.2
  have hpath : ContinuousWithinAt (fun t : ℝ => (t, x)) (Icc a s) s :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  have hlim : Tendsto (fun t => curvDerivNormSq k (L.extendedMetric t) x) (𝓝[<] s)
      (𝓝 (curvDerivNormSq k (L.extendedMetric s) x)) :=
    (ContinuousWithinAt.comp (f := fun t : ℝ => (t, x)) (hc (s, x) ⟨⟨G.lt.le, le_rfl⟩,
      mem_univ x⟩) hpath fun t ht => ⟨ht, mem_univ x⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT G.lt) Ioo_subset_Icc_self)
  rw [L.extendedMetric_terminal] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t < s)
  rw [L.extendedMetric_before ht, curvDerivNormSq_restrictOpen]

theorem TerminalLimitMetric.tendsto_scalar (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) :
    Tendsto (fun t => G.flow.scalar t x.val) (𝓝[<] s) (𝓝 (metricScalarAt L.metric x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [L.eventually_scalar_close_on_compact isCompact_singleton hε] with t ht
  rw [Real.dist_eq]
  exact ht x rfl

theorem TerminalLimitMetric.curvDerivNormSq_le_of_eventually (L : G.TerminalLimitMetric)
    {K q : ℝ} {k : ℕ} (x : G.terminalRegularOpen) (hx : q < metricScalarAt L.metric x)
    (hold : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val →
      curvDerivNormSq k (G.flow.base.metric t) x.val ≤ K * G.flow.scalar t x.val ^ (k + 2)) :
    curvDerivNormSq k L.metric x ≤ K * metricScalarAt L.metric x ^ (k + 2) := by
  have hR := L.tendsto_scalar x
  refine le_of_tendsto_of_tendsto (L.tendsto_curvDerivNormSq k x)
    ((hR.pow (k + 2)).const_mul K) ?_
  filter_upwards [hold, hR.eventually (lt_mem_nhds hx)] with t ht hq
  exact ht hq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem RegularCrossing.curvDerivNormSq_eq
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier}
    (h : E.RegularCrossing p.val q) (k : ℕ) :
    curvDerivNormSq k E.terminal.metric p = curvDerivNormSq k E.outputMetric q := by
  obtain ⟨F, _, hp, heq, _, _, hmetric⟩ := h.exists_survivor_partialDiffeomorph E
  let U : Opens E.incoming.terminalRegularOpen := ⟨F.source, F.open_source⟩
  let V : Opens Q.Carrier :=
    ⟨(F : E.incoming.terminalRegularOpen → Q.Carrier) ''
      (U : Set E.incoming.terminalRegularOpen),
      DifferentialGeometry.image_opens_isOpen F Subset.rfl⟩
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo F Subset.rfl
  have hiso : ∀ (x : U) (v w : TangentSpace ThreeModel x),
      (E.terminal.metric.restrictOpen U).inner x v w =
        1 * (E.outputMetric.restrictOpen V).inner (e x)
          (mfderiv ThreeModel ThreeModel e x v) (mfderiv ThreeModel ThreeModel e x w) := by
    intro x v w
    rw [one_mul, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    have hd := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      F (show (U : Set E.incoming.terminalRegularOpen) ⊆ F.source from Subset.rfl) x
    change _ = E.outputMetric.inner (F x.val) (mfderiv ThreeModel ThreeModel e x v)
      (mfderiv ThreeModel ThreeModel e x w)
    rw [hd v, hd w]
    exact (hmetric x.val x.property v w).symm
  have hk := curvDerivNormSq_eq_of_scaled_local_isometry _ _ e e.isLocalDiffeomorph one_pos
    hiso k ⟨p, hp⟩
  rw [one_pow, one_mul, curvDerivNormSq_restrictOpen, curvDerivNormSq_restrictOpen] at hk
  change curvDerivNormSq k E.outputMetric (F p) = curvDerivNormSq k E.terminal.metric p at hk
  rw [← heq, hk]

theorem curvDerivNormSq_output_le_of_regularCrossing {K q : ℝ} {k : ℕ}
    {p : E.incoming.terminalRegularOpen} {y : Q.Carrier} (h : E.RegularCrossing p.val y)
    (hy : q < metricScalarAt E.outputMetric y)
    (hold : ∀ᶠ t in 𝓝[<] s, q < E.incoming.flow.scalar t p.val →
      curvDerivNormSq k (E.incoming.flow.base.metric t) p.val ≤
        K * E.incoming.flow.scalar t p.val ^ (k + 2)) :
    curvDerivNormSq k E.outputMetric y ≤ K * metricScalarAt E.outputMetric y ^ (k + 2) := by
  rw [← h.curvDerivNormSq_eq E k, ← h.scalar_eq E] at *
  exact E.terminal.curvDerivNormSq_le_of_eventually p hy hold

theorem curvDerivNormSq_le_at_slab_start_of_regularCrossing {s' K q : ℝ} {k : ℕ}
    (G : Q.IncomingSlab s s') (hG : G.flow.base.metric s = E.outputMetric)
    {p : E.incoming.terminalRegularOpen} {y : Q.Carrier} (h : E.RegularCrossing p.val y)
    (hy : q < G.flow.scalar s y)
    (hold : ∀ᶠ t in 𝓝[<] s, q < E.incoming.flow.scalar t p.val →
      curvDerivNormSq k (E.incoming.flow.base.metric t) p.val ≤
        K * E.incoming.flow.scalar t p.val ^ (k + 2)) :
    curvDerivNormSq k (G.flow.base.metric s) y ≤ K * G.flow.scalar s y ^ (k + 2) := by
  change q < metricScalarAt (G.flow.base.metric s) y at hy
  change _ ≤ K * metricScalarAt (G.flow.base.metric s) y ^ (k + 2)
  rw [hG] at hy ⊢
  exact E.curvDerivNormSq_output_le_of_regularCrossing h hy hold

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
