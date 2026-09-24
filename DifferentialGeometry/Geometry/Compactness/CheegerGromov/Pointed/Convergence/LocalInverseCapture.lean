import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section
open Filter Set Bundle TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem exists_isCompact_riemannianClosedBall
    (P : PointedRiemannianManifold.{u, uE, uH} I) (p : P.M) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (riemannianClosedBallOf P.metric p R) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let _ : MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : RegularSpace P.M := inferInstance
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) := P.riemBundle
  let _ : IsContinuousRiemannianBundle E (fun x : P.M => TangentSpace I x) := P.riemBundle_cont
  obtain ⟨K, hK, hpK⟩ := exists_compact_mem_nhds p
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hpK
  have hcR : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨(c : ℝ) / 2, half_pos hcR, hK.of_isClosed_subset ?_ ?_⟩
  · exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist P.metric p) continuous_const
  · intro y hy
    apply hball
    change riemannianEDistOf P.metric p y < (c : ℝ≥0∞)
    exact hy.trans_lt (by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 (by linarith))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianConvergenceMaps.exists_local_inverse_compact_capture
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P subseq) (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) (p : P.M) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : Set P.M, IsCompact K ∧
      ∀ᶠ i in atTop, K ⊆ F.source i ∧
        ∀ y ∈ riemannianClosedBallOf (X.obj (subseq i)).metric (F.map i p) r,
          y ∈ (F.partialDiffeomorph i).target ∧
          (F.partialDiffeomorph i).symm y ∈ K ∧
          F.map i ((F.partialDiffeomorph i).symm y) = y := by
  obtain ⟨R, hR, hK⟩ := exists_isCompact_riemannianClosedBall P p
  let K := riemannianClosedBallOf P.metric p R
  obtain ⟨N, hN⟩ :=
    PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control C href K hK
    (1 / 2) (by norm_num)
  refine ⟨R / 4, by positivity, K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop N] with i hi
  have hsource := (hN i hi).1
  have hcapture :=
    DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower
      P.metric (X.obj (subseq i)).metric (F.partialDiffeomorph i) p
      (R := R) (L := 2) (r := R / 4) hR (by norm_num) (by linarith) hK hsource ?_
  · refine ⟨hsource, ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hcapture hy
    have hxsrc : x ∈ (F.partialDiffeomorph i).source := hsource hx
    have hytarget : y ∈ (F.partialDiffeomorph i).target :=
      hxy ▸ (F.partialDiffeomorph i).map_source hxsrc
    have hinv : (F.partialDiffeomorph i).symm y = x := by
      rw [← hxy]
      exact (F.partialDiffeomorph i).left_inv hxsrc
    exact ⟨hytarget, hinv ▸ hx, (F.partialDiffeomorph i).right_inv hytarget⟩
  · intro x hx v
    change P.metric.inner x v v ≤ (2 : ℝ) ^ 2 *
      (X.obj (subseq i)).metric.inner (F.map i x)
        (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x v)
    have h := (abs_le.mp ((hN i hi).2 x hx v)).1
    have hnonneg := metric_inner_self_nonneg P.metric x v
    nlinarith

end DifferentialGeometry.CheegerGromovCompactness
