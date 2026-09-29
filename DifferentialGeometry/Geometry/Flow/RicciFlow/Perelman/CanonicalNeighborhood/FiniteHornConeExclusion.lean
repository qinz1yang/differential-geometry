import DifferentialGeometry.Geometry.Metric.ConeChart.Construction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalConeHomeomorphism
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceConeEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceNormalizedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AnnularRepresentatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact EndAngles.metric

theorem RealizedFiniteHorn.exists_original_source_local_coneChart
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (angles : EndAngles H.horn) [CompactSpace (UniformSpace.Completion angles.quotient)]
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (C : AnnularConvergence H.horn angles ray d)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi) (hnseq : StrictMono nseq)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {a b lambda R : ℝ} (ha : 0 < a) (hlambda : 0 < lambda)
    (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hscale : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k))))
 :
    ∃ W : Set V, IsOpen W ∧ (⟨q, hq⟩ : V) ∈ W ∧ Nonempty (ConeChart (g.restrictOpen V) W) := by
  obtain ⟨e, he, _, hpos, hdist⟩ :=
    H.exists_marked_original_source_local_distance_cone X angles ray d N C hd j psi nseq
      hpsi hnseq hQ ha hlambda ha1 h1b hR hscale hcompact hdiagonal
      g V U hVU q hq f G hG hsource hmetric hbase
  let : SecondCountableTopology Q := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace Q
  let : LocallyCompactSpace Q := Manifold.locallyCompact_of_finiteDimensional (M := Q) I3
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let : SigmaCompactSpace V := inferInstance
  obtain ⟨W, hW, hqW, _, hcone⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_cone_chart_of_riemannianEDistOf_cone
      (g.restrictOpen V) e hpos hdist (m := 2) (by simp [ThreeSpace]) he
  exact ⟨W, hW, hqW, hcone⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact EndAngles.metric

theorem RealizedFiniteHorn.false_of_original_source_nonnegative_local_flow_limit
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (H : RealizedFiniteHorn X.toFlowSequence)
    (angles : EndAngles H.horn) [CompactSpace (UniformSpace.Completion angles.quotient)]
    (ray : EndRay H.horn.endpoint) (d : ℕ → ℝ) (N : ℕ)
    (C : AnnularConvergence H.horn angles ray d)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (j psi nseq : ℕ → ℕ) (hpsi : StrictMono psi) (hnseq : StrictMono nseq)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (ray.point (d (N + n))))
    {a b lambda R : ℝ} (ha : 0 < a) (hlambda : 0 < lambda)
    (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hscale : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric)
      (ray.point (d (N + n))) R))
    (hdiagonal : ∀ i n : ℕ, n ≤ i →
      let scaled := scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n) H.metric
      let ball := riemannianClosedBallOf scaled (ray.point (d (N + n))) R
      ball ⊆ (H.maps (j i)).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled)
        (fun _ => scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hQ n)
          ((X.term (H.subseq (j i))).S.base.metric 0)) (H.maps (j i)) ball {0} i
            (1 / ((i : ℝ) + 2))))
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
    [T2Space Q] [SigmaCompactSpace Q]
    (g : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ k, PartialDiffeomorph I3 I3 Q (X.term (H.subseq (j (psi (nseq k))))).M ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set Q) ⊆ (f k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G k).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k)))) (hQ (nseq k))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f k x)
            (mfderiv I3 I3 (f k) x v) (mfderiv I3 I3 (f k) x w))
    (hbase : ∀ k, f k q = H.maps (j (psi (nseq k))) (ray.point (d (N + nseq k))))
    {delta : ℝ} (hdelta : 0 < delta)
    (S : SolutionOn (I := I3) (M := V)
      (RealTimeInterval.closed (-delta) 0 (by linarith)))
    (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = g.restrictOpen V)
    (hnonnegative : ∀ t ∈ Icc (-delta) 0, SecLower (S.base.metric t) 0 univ)
    (hnormalized : metricScalarAt (S.base.metric 0) (⟨q, hq⟩ : V) = 1) : False := by
  obtain ⟨W, _, hqW, ⟨cone⟩⟩ :=
    H.exists_original_source_local_coneChart X angles ray d N C hd j psi nseq hpsi hnseq
      hQ ha hlambda ha1 h1b hR hscale hcompact hdiagonal
      g V U hVU q hq f G hG hsource hmetric hbase
  let : SecondCountableTopology Q := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace Q
  let : LocallyCompactSpace Q := Manifold.locallyCompact_of_finiteDimensional (M := Q) I3
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let : SigmaCompactSpace V := inferInstance
  have cone' : ConeChart (S.base.metric 0) W := hterminal.symm ▸ cone
  exact solution_cone_terminal_exclusion S hS (neg_lt_zero.mpr hdelta)
    (fun _ ht => ht) (fun _ ht => ht) W cone'
    (fun t ht x _ => hnonnegative t ht x (mem_univ x))
    ⟨⟨q, hq⟩, hqW, by rw [hnormalized]; norm_num⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact
    EndAngles.metric
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_pos_not_nonempty_realizedFiniteHorn
    {kappa : ℝ} (hkappa : 0 < kappa) (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ¬ Nonempty (RealizedFiniteHorn X.toFlowSequence) := by
  obtain ⟨epsStar, c, Cbound, hc, hepsStar, _, hlimits⟩ :=
    RealizedFiniteHorn.exists_original_source_normalized_nonnegative_local_ricci_flow_limit hkappa
      hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi X hH
  obtain ⟨H⟩ := hH
  obtain ⟨B, eta, _, _, hlimits'⟩ := hlimits eps heps hepsStar' sigma hsigma Phi hPhi
  obtain ⟨endData⟩ := H.end_rays
  obtain ⟨angles⟩ := H.end_angle endData
  have : CompactSpace (UniformSpace.Completion angles.quotient) :=
    (H.direction_compactness endData angles).2.1
  let ray := H.horn.axial
  obtain ⟨upper, _, hupper⟩ := H.curvatureUpper.upper
  obtain ⟨tau, lambda, htau, hlambda, _, hscale0⟩ :=
    exists_tendsto_curvature_radial_scale H.horn ray H.radii H.radii_mem H.radii_zero hupper
  have hd0 : ∀ i, H.radii (tau i) ∈ Ioc 0 ray.length := fun i => H.radii_mem _
  have hzero0 : Tendsto (fun i => H.radii (tau i)) atTop (𝓝 0) :=
    H.radii_zero.comp htau.tendsto_atTop
  have hscalar := ray.metricScalarAt_tendsto_atTop H.horn (Eventually.of_forall hd0) hzero0
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hscalar.eventually_ge_atTop 1)
  let d : ℕ → ℝ := fun i => H.radii (tau (N0 + i))
  have hshift : StrictMono (fun i => N0 + i) := fun _ _ h => Nat.add_lt_add_left h N0
  have hd : ∀ i, d i ∈ Ioc 0 ray.length := fun _ => H.radii_mem _
  have hzero : Tendsto d atTop (𝓝 0) := hzero0.comp hshift.tendsto_atTop
  have hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt H.metric (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda) :=
    hscale0.comp hshift.tendsto_atTop
  have hQall : ∀ i, 1 ≤ metricScalarAt H.metric (ray.point (d i)) :=
    fun i => hN0 (N0 + i) (Nat.le_add_right N0 i)
  obtain ⟨annuli⟩ := H.cone_convergence endData angles ray d hd hzero
  obtain ⟨N, R, j, hR, hj, _, _, hq, hcompact, hdiagonal⟩ :=
    H.exists_original_source_rescaled_diagonal angles ray d hd hzero annuli (fun _ => 0)
  let hQ : ∀ n, 1 ≤ metricScalarAt H.metric (ray.point (d (N + n))) := fun _ => hQall _
  obtain ⟨psi, hpsi, _, S, _, _, _, _, _, _, _, _, phi, hphi, _, Q,
    top, charts, hman, hT2, hsecond, gQ, V, U, q, F, G, _, _, hqV, hG, hGconv,
    offset, f, hf, hVU, T, _, _, _, rho, hrho, _, g, hg0, hflow, hnormalized, hnonnegative, _⟩ :=
    hlimits' X H ray d N hQ j hj
  let := top
  let := charts
  let := hman
  let := hT2
  let := hsecond
  let : LocallyCompactSpace Q := Manifold.locallyCompact_of_finiteDimensional (M := Q) I3
  let : SigmaCompactSpace Q := inferInstance
  let nseq : ℕ → ℕ := fun k => phi (rho k + offset)
  have hindex : StrictMono (fun k => rho k + offset) :=
    fun _ _ h => Nat.add_lt_add_right (hrho h) offset
  have hnseq : StrictMono nseq := hphi.comp hindex
  have hfullindex : StrictMono (fun k => N + nseq k) :=
    fun _ _ h => Nat.add_lt_add_left (hnseq h) N
  have hscale' : Tendsto (fun k => Real.sqrt
      (metricScalarAt H.metric (ray.point (d (N + nseq k))) * d (N + nseq k) ^ 2))
      atTop (𝓝 lambda) := hscale.comp hfullindex.tendsto_atTop
  have hfsource : ∀ k, (U : Set Q) ⊆ (f (rho k)).source :=
    fun k _ hx => (hf (rho k)).1 (subset_closure hx)
  have hpull : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G (rho k + offset)).inner x v w =
        (scaleMetric (metricScalarAt H.metric (ray.point (d (N + nseq k))))
          (zero_lt_one.trans_le (hQ (nseq k)))
          ((X.term (H.subseq (j (psi (nseq k))))).S.base.metric 0)).inner (f (rho k) x)
            (mfderiv I3 I3 (f (rho k)) x v) (mfderiv I3 I3 (f (rho k)) x w) := by
    filter_upwards [hindex.tendsto_atTop.eventually hG] with k hk
    intro x v w
    have hnear : (f (rho k) : Q → _) =ᶠ[𝓝 (x : Q)] F (rho k + offset) :=
      Filter.eventuallyEq_of_mem ((f (rho k)).open_source.mem_nhds (hfsource k x.property))
        (fun y hy => (hf (rho k)).2.1 hy)
    rw [hnear.eq_of_nhds, hnear.mfderiv_eq]
    exact hk x v w
  exact H.false_of_original_source_nonnegative_local_flow_limit X angles ray d N annuli hd
    j psi nseq hpsi hnseq (fun n => zero_lt_one.trans_le (hQ n))
    (a := 1 / 2) (b := 3 / 2) (by norm_num) hlambda (by norm_num) (by norm_num)
    hR hscale' hcompact (fun i n hn => ⟨(hdiagonal i n hn).1, (hdiagonal i n hn).2.1⟩)
    gQ V U hVU q hqV (fun k => f (rho k)) (fun k => G (rho k + offset))
    (hGconv.comp_subseq hindex) (Eventually.of_forall hfsource) hpull
    (fun k => (hf (rho k)).2.2.1) (delta := c / 24) (by positivity)
    ({ base.metric := g } : SolutionOn (I := I3) (M := V)
      (RealTimeInterval.closed (-(c / 24)) 0 (by linarith)))
    hflow hg0 hnonnegative (hnormalized hqV)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
