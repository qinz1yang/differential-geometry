import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackMetricEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.CompactEquivalence
import DifferentialGeometry.Geometry.Metric.Comparison.BallImage
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance distanceModelComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.sigmaCompact PointedFlowData.t2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem FlowMetricConvergenceData.exists_eventually_edist_map_le_on_ball
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b r : ℝ} (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (hG : tensor0SFamilyContinuousOnSet (I := I) 2 (Icc a b)
      (fun t x ↦ Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x))
    (hK : IsCompact {x : P.M | riemannianEDistOf R P.basepoint x ≤ ENNReal.ofReal r}) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x : P.M,
      riemannianEDistOf R P.basepoint x < ENNReal.ofReal r →
      riemannianEDistOf ((X.term (subseq (co.φ k))).S.base.metric t)
        (X.term (subseq (co.φ k))).basepoint (Φ.map (co.φ k) x) ≤ ENNReal.ofReal B := by
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let : T3Space P.M := inferInstance
  let K : Set P.M := {x | riemannianEDistOf R P.basepoint x ≤ ENNReal.ofReal r}
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact
      co.gInf R isCompact_Icc hK hG
  obtain ⟨N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Φ R bf hsrc htgt co hK hL hlimit
  have hevent := co.strictMono.tendsto_atTop.eventually
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
      Φ R bf hsrc htgt K hK)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hevent
  have hLpos : 0 < 2 * L := by linarith
  refine ⟨max 1 (Real.sqrt (2 * L) * r), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    max N₁ N₂, ?_⟩
  intro k hk t ht x hx
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨U, _hU, hKU, hUsrc, hmetric⟩ := hN₂ k hk₂
  let : TopologicalSpace.MetrizableSpace (X.term (subseq (co.φ k))).M :=
    Manifold.metrizableSpace I (X.term (subseq (co.φ k))).M
  let : T3Space (X.term (subseq (co.φ k))).M := inferInstance
  let g := (X.term (subseq (co.φ k))).S.base.metric t
  let : RiemannianBundle (fun y : P.M ↦ TangentSpace I y) := ⟨R.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : P.M ↦ TangentSpace I y) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I P.M
  let : RiemannianBundle
      (fun y : (X.term (subseq (co.φ k))).M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun y : (X.term (subseq (co.φ k))).M ↦ TangentSpace I y) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace (X.term (subseq (co.φ k))).M :=
    EMetricSpace.ofRiemannianMetric I (X.term (subseq (co.φ k))).M
  have hsrcBall : Metric.closedEBall P.basepoint (ENNReal.ofReal r) ⊆
      (Φ.partialDiffeomorph (co.φ k)).source := by
    intro y hy
    apply hUsrc (hKU ?_)
    rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I)] at hy
    exact hy
  have hquad : ∀ y ∈ Metric.closedEBall P.basepoint (ENNReal.ofReal r),
      ∀ v : TangentSpace I y,
        g.inner (Φ.map (co.φ k) y)
          (mfderiv I I (Φ.map (co.φ k)) y v) (mfderiv I I (Φ.map (co.φ k)) y v) ≤
          (2 * L) * R.inner y v v := by
    intro y hy v
    have hyK : y ∈ K := by
      rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I)] at hy
      exact hy
    rw [← hmetric t y (hKU hyK)]
    exact (hN₁ k hk₁ t ht).2 y hyK v |>.2
  have himage := DifferentialGeometry.PartialDiffeomorph.image_eball_subset_closedEBall_of_quad_le
    (Φ.partialDiffeomorph (co.φ k)) (by exact_mod_cast le_top)
    (g := R) (h := g) (O := P.basepoint) (r := r) (r₂ := r)
    (fun y v ↦ by rw [← ofReal_norm, norm_eq_sqrt_real_inner]; rfl)
    (fun y v ↦ by rw [← ofReal_norm, norm_eq_sqrt_real_inner]; rfl)
    le_rfl hLpos.le hsrcBall hquad
  have hxBall : x ∈ Metric.eball P.basepoint (ENNReal.ofReal r) := by
    rw [Metric.mem_eball', IsRiemannianManifold.out (I := I)]
    exact hx
  have hmem := himage (mem_image_of_mem (Φ.partialDiffeomorph (co.φ k)) hxBall)
  change edist (Φ.map (co.φ k) x) (Φ.map (co.φ k) P.basepoint) ≤ _ at hmem
  have hbase : Φ.map (co.φ k) P.basepoint = (X.term (subseq (co.φ k))).basepoint :=
    Φ.basepoint_map (co.φ k)
  rw [hbase, edist_comm, IsRiemannianManifold.out (I := I)] at hmem
  exact hmem.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))


theorem FlowMetricConvergenceData.exists_eventually_edist_map_le_on_ball_of_metricFamilySmoothOn
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b r : ℝ} (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (hG : MetricFamilySmoothOn X.D co.gInf) (hcarrier : Icc a b ⊆ X.D.carrier)
    (hK : IsCompact {x : P.M | riemannianEDistOf R P.basepoint x ≤ ENNReal.ofReal r}) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x : P.M,
      riemannianEDistOf R P.basepoint x < ENNReal.ofReal r →
      riemannianEDistOf ((X.term (subseq (co.φ k))).S.base.metric t)
        (X.term (subseq (co.φ k))).basepoint (Φ.map (co.φ k) x) ≤ ENNReal.ofReal B :=
  co.exists_eventually_edist_map_le_on_ball Φ R bf hsrc htgt
    (metricTensor_cont_restrict_of_metricFamilySmoothOn co.gInf hG hcarrier) hK


theorem FlowMetricConvergenceData.exists_eventually_edist_map_map_le_on_ball
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b r : ℝ} (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (hG : tensor0SFamilyContinuousOnSet (I := I) 2 (Icc a b)
      (fun t x ↦ Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x))
    (hK : IsCompact {x : P.M | riemannianEDistOf R P.basepoint x ≤ ENNReal.ofReal r}) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x y : P.M,
      riemannianEDistOf R P.basepoint x < ENNReal.ofReal r →
      riemannianEDistOf R P.basepoint y < ENNReal.ofReal r →
      riemannianEDistOf ((X.term (subseq (co.φ k))).S.base.metric t)
        (Φ.map (co.φ k) x) (Φ.map (co.φ k) y) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hB, N, hN⟩ :=
    co.exists_eventually_edist_map_le_on_ball Φ R bf hsrc htgt hG hK
  refine ⟨2 * B, mul_pos (by norm_num) hB, N, ?_⟩
  intro k hk t ht x y hx hy
  let g := (X.term (subseq (co.φ k))).S.base.metric t
  let O := (X.term (subseq (co.φ k))).basepoint
  have hxB : riemannianEDistOf g O (Φ.map (co.φ k) x) ≤ ENNReal.ofReal B :=
    hN k hk t ht x hx
  have hyB : riemannianEDistOf g O (Φ.map (co.φ k) y) ≤ ENNReal.ofReal B :=
    hN k hk t ht y hy
  calc
    riemannianEDistOf g (Φ.map (co.φ k) x) (Φ.map (co.φ k) y)
        ≤ riemannianEDistOf g (Φ.map (co.φ k) x) O +
            riemannianEDistOf g O (Φ.map (co.φ k) y) :=
      riemannianEDistOf_triangle g _ O _
    _ = riemannianEDistOf g O (Φ.map (co.φ k) x) +
        riemannianEDistOf g O (Φ.map (co.φ k) y) := by
      rw [riemannianEDistOf_comm g (Φ.map (co.φ k) x) O]
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hxB hyB
    _ = ENNReal.ofReal (2 * B) := by
      rw [← ENNReal.ofReal_add hB.le hB.le, two_mul]


attribute [local instance] PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem FlowMetricConvergenceData.exists_eventually_edist_map_le_on_compact
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace P.M]
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (hG : tensor0SFamilyContinuousOnSet (I := I) 2 (Icc a b)
      (fun t x ↦ Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x))
    {K : Set P.M} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x ∈ K,
      riemannianEDistOf ((X.term (subseq (co.φ k))).S.base.metric t)
        (X.term (subseq (co.φ k))).basepoint (Φ.map (co.φ k) x) ≤ ENNReal.ofReal B := by
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let : T3Space P.M := inferInstance
  let : RiemannianBundle (fun x : P.M ↦ TangentSpace I x) := ⟨R.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : P.M ↦ TangentSpace I x) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : MetricSpace P.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := P.M)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball P.basepoint).mp hK.isBounded
  obtain ⟨B, hB, N, hN⟩ := co.exists_eventually_edist_map_le_on_ball Φ R bf hsrc htgt hG
    (hR.closedEBall_isCompact P.basepoint r)
  refine ⟨B, hB, N, ?_⟩
  intro k hk t ht x hx
  apply hN k hk t ht x
  have hdist : dist P.basepoint x < r := by
    simpa only [Metric.mem_ball, dist_comm] using hr hx
  have hrpos : 0 < r := dist_nonneg.trans_lt hdist
  have hed : edist P.basepoint x < ENNReal.ofReal r := by
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hrpos]
    exact hdist
  rw [IsRiemannianManifold.out (I := I)] at hed
  exact hed

end DifferentialGeometry.CheegerGromovCompactness

end
