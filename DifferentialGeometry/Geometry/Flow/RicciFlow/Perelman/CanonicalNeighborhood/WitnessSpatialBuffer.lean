import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity


set_option autoImplicit false

noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

omit [CompleteSpace E] in
theorem exists_larger_riemannianClosedBall_subset
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 ≤ R) {U : Set M} (hU : IsOpen U)
    (hsub : riemannianClosedBallOf g p R ⊆ U) :
    ∃ delta : ℝ, 0 < delta ∧ riemannianClosedBallOf g p (R + delta) ⊆ U := by
  classical
  let K := riemannianClosedBallOf g p (R + 1) \ U
  have hK : IsCompact K :=
    (RiemannianMetricComplete.closedEBall_isCompact hcomplete p (R + 1)).inter_right
      hU.isClosed_compl
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne
      (continuous_riemannianEDist g p).continuousOn
    have hfinite : riemannianEDistOf g p z ≠ ⊤ :=
      ne_of_lt (hz.1.trans_lt ENNReal.ofReal_lt_top)
    have hlarge : ENNReal.ofReal R < riemannianEDistOf g p z := by
      by_contra hnot
      exact hz.2 (hsub (le_of_not_gt hnot))
    have hlargeReal : R < (riemannianEDistOf g p z).toReal := by
      by_contra hnot
      have hle := ENNReal.ofReal_le_ofReal (le_of_not_gt hnot)
      rw [ENNReal.ofReal_toReal hfinite] at hle
      exact not_le_of_gt hlarge hle
    let delta := min 1 (((riemannianEDistOf g p z).toReal - R) / 2)
    have hdelta : 0 < delta := lt_min zero_lt_one (by linarith)
    refine ⟨delta, hdelta, ?_⟩
    intro y hy
    by_contra hnot
    have hdelta_le : delta ≤ 1 := min_le_left _ _
    have hyK : y ∈ K := ⟨(riemannianClosedBallOf_mono g p
      (show R + delta ≤ R + 1 by linarith)) hy, hnot⟩
    have hd : (riemannianEDistOf g p z).toReal ≤ R + delta := by
      calc
        _ ≤ (ENNReal.ofReal (R + delta)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((hmin hyK).trans hy)
        _ = R + delta := ENNReal.toReal_ofReal (by linarith)
    have hsmall : delta ≤ ((riemannianEDistOf g p z).toReal - R) / 2 := min_le_right _ _
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    by_contra hnot
    exact hne ⟨y, hy, hnot⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_moving_riemannianClosedBall_subset
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 ≤ R) {U : Set M} (hU : IsOpen U)
    (hsub : riemannianClosedBallOf g p R ⊆ U) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ z ∈ riemannianBallOf g p eta,
      ∀ r : ℝ, r ≤ R + eta → riemannianClosedBallOf g z r ⊆ U := by
  obtain ⟨delta, hdelta, hroom⟩ :=
    exists_larger_riemannianClosedBall_subset g hcomplete p hR hU hsub
  let eta := delta / 3
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, fun z hz r hr y hy => hroom ?_⟩
  have htriangle : riemannianEDistOf g p y ≤
      riemannianEDistOf g p z + riemannianEDistOf g z y := by
    let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_triangle (I := I) (x := p) (y := z) (z := y)
  have hsum : ENNReal.ofReal eta + ENNReal.ofReal (R + eta) =
      ENNReal.ofReal (R + 2 * eta) := by
    rw [← ENNReal.ofReal_add heta.le (add_nonneg hR heta.le)]
    congr 1
    ring
  exact (htriangle.trans (add_le_add hz.le (hy.trans (ENNReal.ofReal_le_ofReal hr)))).trans
    (hsum.le.trans (ENNReal.ofReal_le_ofReal (by dsimp only [eta]; linarith)))

end Metric

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [T2Space M] in
theorem WindowedModelWitness.exists_extra_spatial_buffer
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t) :
    ∃ delta : ℝ, 0 < delta ∧
      riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius eps + 1 + delta) ⊆ W.embedding.source := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  apply exists_larger_riemannianClosedBall_subset _ hcomplete W.model.basepoint
    (by unfold modelRadius; positivity) W.embedding.open_source W.buffered_ball

omit [T2Space M] in
theorem WindowedModelWitness.exists_moving_spatial_buffer
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ z ∈ riemannianBallOf (I := I3) (W.model.S.base.metric 0) W.model.basepoint eta,
        ∀ r : ℝ, r ≤ modelRadius eps + 1 + eta →
          riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0) z r ⊆
            W.embedding.source := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  exact exists_moving_riemannianClosedBall_subset _ hcomplete W.model.basepoint
    (by unfold modelRadius; positivity) W.embedding.open_source W.buffered_ball

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
