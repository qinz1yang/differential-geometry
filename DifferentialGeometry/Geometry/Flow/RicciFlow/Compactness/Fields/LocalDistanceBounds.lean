import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedDistanceBounds
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphLocalDistance

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

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.sigmaCompact PointedFlowData.t2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem FlowMetricConvergenceData.exists_eventually_local_edist_map_map_le_on_compact
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace P.M]
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {a b : ℝ} (co : FlowMetricConvergenceData Phi R bf hsrc htgt a b)
    (hG : tensor0SFamilyContinuousOnSet (I := I) 2 (Icc a b)
      (fun t x ↦ Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x))
    {J : Set P.M} (hJ : IsCompact J) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ t ∈ Icc a b, ∀ x ∈ J, ∀ y : P.M,
      riemannianEDistOf R x y < ENNReal.ofReal 1 →
      riemannianEDistOf ((X.term (subseq (co.φ k))).S.base.metric t)
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) ≤
          ENNReal.ofReal B * riemannianEDistOf R x y := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let : T3Space P.M := inferInstance
  let : RiemannianBundle (fun x : P.M ↦ TangentSpace I x) := ⟨R.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : P.M ↦ TangentSpace I x) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : MetricSpace P.M := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := P.M)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball P.basepoint).mp hJ.isBounded
  let K : Set P.M := {x | riemannianEDistOf R P.basepoint x ≤ ENNReal.ofReal (r + 1)}
  have hK : IsCompact K := hR.closedEBall_isCompact P.basepoint (r + 1)
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact co.gInf R isCompact_Icc hK hG
  obtain ⟨N, hN⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Phi R bf hsrc htgt co hK hL hlimit
  have hevent := co.strictMono.tendsto_atTop.eventually
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
      Phi R bf hsrc htgt K hK)
  refine ⟨Real.sqrt (2 * L), Real.sqrt_nonneg _, ?_⟩
  filter_upwards [eventually_ge_atTop N, hevent] with k hk hmetric
  intro t ht x hx y hxy
  obtain ⟨U, _hU, hKU, hUsrc, hmetric⟩ := hmetric
  let g := (X.term (subseq (co.φ k))).S.base.metric t
  let : TopologicalSpace.MetrizableSpace (X.term (subseq (co.φ k))).M :=
    Manifold.metrizableSpace I (X.term (subseq (co.φ k))).M
  let : T3Space (X.term (subseq (co.φ k))).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.term (subseq (co.φ k))).M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : (X.term (subseq (co.φ k))).M ↦ TangentSpace I z) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace (X.term (subseq (co.φ k))).M :=
    EMetricSpace.ofRiemannianMetric I (X.term (subseq (co.φ k))).M
  have hxball : dist P.basepoint x < r := by
    simpa only [Metric.mem_ball, dist_comm] using hr hx
  have hxK : Metric.closedEBall x (ENNReal.ofReal 1) ⊆ K := by
    intro z hz
    have hzx : dist x z ≤ 1 := by
      rw [Metric.mem_closedEBall', edist_dist] at hz
      exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp hz
    have hzdist : dist P.basepoint z ≤ r + 1 :=
      (dist_triangle _ _ _).trans (add_le_add hxball.le hzx)
    change riemannianEDistOf R P.basepoint z ≤ ENNReal.ofReal (r + 1)
    have hed : edist P.basepoint z ≤ ENNReal.ofReal (r + 1) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hzdist
    rw [IsRiemannianManifold.out (I := I)] at hed
    exact hed
  have hsource : Metric.closedEBall x (ENNReal.ofReal 1) ⊆
      (Phi.partialDiffeomorph (co.φ k)).source := fun z hz ↦ hUsrc (hKU (hxK hz))
  have hquad : ∀ z ∈ Metric.closedEBall x (ENNReal.ofReal 1), ∀ v : TangentSpace I z,
      g.inner (Phi.map (co.φ k) z)
        (mfderiv I I (Phi.map (co.φ k)) z v)
        (mfderiv I I (Phi.map (co.φ k)) z v) ≤ (2 * L) * R.inner z v v := by
    intro z hz v
    rw [← hmetric t z (hKU (hxK hz))]
    exact ((hN k hk t ht).2 z (hxK hz) v).2
  have hlocal := DifferentialGeometry.PartialDiffeomorph.edist_map_le_mul_of_quad_le_on_closedEBall
    (Phi.partialDiffeomorph (co.φ k)) (by exact_mod_cast le_top)
    (g := R) (h := g) (x := x) (y := y) (rho := 1) (C := 2 * L)
    (fun z v ↦ by rw [← ofReal_norm, norm_eq_sqrt_real_inner]; rfl)
    (fun z v ↦ by rw [← ofReal_norm, norm_eq_sqrt_real_inner]; rfl)
    (by linarith) hsource hquad (by
      rw [IsRiemannianManifold.out (I := I)]
      exact hxy)
  rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I)] at hlocal
  exact hlocal

end DifferentialGeometry.CheegerGromovCompactness
