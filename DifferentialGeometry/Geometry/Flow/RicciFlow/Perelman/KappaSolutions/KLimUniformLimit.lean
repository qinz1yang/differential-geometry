import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section MetricImages

variable [NeZero (Module.finrank ℝ E)]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps (I := I) X L phi}

local instance klimUniformImageTopology : TopologicalSpace L.M := L.topology
local instance klimUniformImageCharted : ChartedSpace H L.M := L.charted
local instance klimUniformImageSmooth : IsManifold I ∞ L.M := L.smooth
local instance klimUniformImageT2 : T2Space L.M := L.t2
local instance klimUniformImageSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance klimUniformImageApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance klimUniformImageApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance klimUniformImageApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

private theorem klimUniform_pointed_image_bounded
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M)
    (y : L.M) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k in atTop,
      (riemannianEDistOf (I := I) (X.obj (phi k)).metric
        (X.obj (phi k)).basepoint (Phi.map k y)).toReal ≤ A := by
  let _ : ConnectedSpace L.M := hconnected
  let _ : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : RiemannianBundle (fun z : L.M => TangentSpace I z) :=
    ⟨L.metric.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun z : L.M => TangentSpace I z) :=
    ⟨⟨L.metric.inner, L.metric.contMDiff.continuous, by intro z v w; rfl⟩⟩
  have hfinite : riemannianEDistOf (I := I) L.metric L.basepoint y ≠ ⊤ := by
    change riemannianEDist I L.basepoint y ≠ ⊤
    exact DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
      (I := I) L.basepoint y
  let d : ℝ := (riemannianEDistOf (I := I) L.metric L.basepoint y).toReal
  let R : ℝ := d + 1
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hR : 0 < R := by dsimp only [R]; linarith
  have hy : riemannianEDistOf (I := I) L.metric L.basepoint y < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 (by change d < d + 1; linarith)
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := by
    refine ⟨?_⟩
    exact MetricComplete.complete (I := I) L hcomplete
  have hcompact : IsCompact (riemannianClosedBallOf (I := I) L.metric L.basepoint R) :=
    RiemannianMetricComplete.closedEBall_isCompact hmetricComplete L.basepoint R
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control C hreference
    (riemannianClosedBallOf (I := I) L.metric L.basepoint R) hcompact 1 zero_lt_one
  refine ⟨2 * R, mul_pos (by norm_num) hR, ?_⟩
  filter_upwards [eventually_ge_atTop k0] with k hk
  let f := Phi.partialDiffeomorph k
  have hupper : ∀ z ∈ riemannianClosedBallOf (I := I) L.metric L.basepoint R,
      ∀ v : TangentSpace I z,
      (X.obj (phi k)).metric.inner (f z)
          (mfderiv I I (f : L.M → (X.obj (phi k)).M) z v)
          (mfderiv I I (f : L.M → (X.obj (phi k)).M) z v) ≤
        (2 : ℝ) ^ 2 * L.metric.inner z v v := by
    intro z hz v
    have herror := (abs_le.mp ((hk0 k hk).2 z hz v)).2
    change (X.obj (phi k)).metric.inner (f z)
        (mfderiv I I (f : L.M → (X.obj (phi k)).M) z v)
        (mfderiv I I (f : L.M → (X.obj (phi k)).M) z v) -
      L.metric.inner z v v ≤ 1 * L.metric.inner z v v at herror
    have hnonneg : 0 ≤ L.metric.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (L.metric.pos z v hv).le
    nlinarith
  have hmap := edistOf_map_le_of_metric_upper_on_ball L.metric (X.obj (phi k)).metric
    f L.basepoint y hR (by norm_num : (0 : ℝ) < 2) (hk0 k hk).1 hupper hy
  have hbase : f L.basepoint = (X.obj (phi k)).basepoint := Phi.basepoint_map k
  rw [hbase] at hmap
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hmap
  have hbound : (riemannianEDistOf (I := I) (X.obj (phi k)).metric
      (X.obj (phi k)).basepoint (Phi.map k y)).toReal ≤ 2 * d := by
    simpa only [f, d, PointedRiemannianConvergenceMaps.map,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      using hreal
  exact hbound.trans (by dsimp only [R]; linarith)

end MetricImages

section AncientLimit

variable (X : PointedFlowSeq.{u, uE, uH} (I := I))
  (L : PointedFlowData.{u, uE, uH} (I := I) X.D) {phi : ℕ → ℕ}
  (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)

local instance klimUniformLimitTopology : TopologicalSpace L.M := L.topology
local instance klimUniformLimitCharted : ChartedSpace H L.M := L.charted
local instance klimUniformLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance klimUniformLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
local instance klimUniformLimitT2 : T2Space L.M := L.t2
local instance klimUniformLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance klimUniformLimitTermTopology (i : ℕ) :
    TopologicalSpace (X.term i).M := (X.term i).topology
local instance klimUniformLimitTermCharted (i : ℕ) :
    ChartedSpace H (X.term i).M := (X.term i).charted
local instance klimUniformLimitTermSmooth (i : ℕ) :
    IsManifold I ∞ (X.term i).M := (X.term i).smooth
local instance klimUniformLimitTermC1 (i : ℕ) : IsManifold I 1 (X.term i).M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance klimUniformLimitTermT2 (i : ℕ) : T2Space (X.term i).M := (X.term i).t2
local instance klimUniformLimitTermSigma (i : ℕ) :
    SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact

theorem ancientKappaThree_of_uniformly_bounded_KLim_limit
    {kappa : ℝ} (hdim : Module.finrank ℝ E = 3) (hD : X.D = ancientTimeInterval)
    (B : ℝ) (hB : 1 ≤ B)
    (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I) (X.term i) 1)
    (hphi : StrictMono phi)
    (hlocal : ∀ A : ℝ, ∀ᶠ i in atTop, ∀ t ∈ X.D.carrier, ∀ z : (X.term i).M,
      (riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z).toReal ≤ A →
        0 ≤ (X.term i).S.scalar t z ∧ (X.term i).S.scalar t z ≤ B)
    (hconnected : ConnectedSpace L.M)
    (hcomplete : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := X) (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k) :
    IsAncientKappaSolution (I := I) kappa L ∧
      PointedFlowScalarAtBase (I := I) L 1 ∧
      PointedFlowScalarBounded (I := I) L B ∧
      PointedFlowRmNormSqBounded (I := I) L (3 * B ^ 2) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have ht0 : (0 : ℝ) ∈ X.D.carrier := by simp [hD]
  obtain ⟨C0, hc0⟩ := hconv 0 ht0
  have hscalarBase : PointedFlowScalarAtBase (I := I) L 1 := by
    apply pointedScalar_base_eq_of_metricCG_canonical_domains C0 hc0
    intro k
    exact hbase (phi k)
  have hscalar : PointedFlowScalarBounded (I := I) L B := by
    intro t ht y
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hlim := pointedScalar_tendsto_of_metricCG_canonical_domains Ct hct y
    change Tendsto (fun k => (X.term (phi k)).S.scalar t (Phi.map k y)) atTop
      (𝓝 (L.S.scalar t y)) at hlim
    obtain ⟨A, _hA, hA⟩ := klimUniform_pointed_image_bounded C0 hc0
      (hcomplete 0 ht0) hconnected y
    have htail := hphi.tendsto_atTop.eventually (hlocal A)
    have hbounds : ∀ᶠ k in atTop,
        0 ≤ (X.term (phi k)).S.scalar t (Phi.map k y) ∧
          (X.term (phi k)).S.scalar t (Phi.map k y) ≤ B := by
      filter_upwards [hA, htail] with k hk hkt
      exact hkt t ht (Phi.map k y) hk
    exact ⟨ge_of_tendsto hlim (hbounds.mono fun _ h => h.1),
      le_of_tendsto hlim (hbounds.mono fun _ h => h.2)⟩
  have hoperator : ∀ t ∈ X.D.carrier,
      PointedFlowNonnegativeCurvatureOperator (I := I) L t := by
    intro t ht
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hcone : ∀ y : L.M,
        metricAlgebraicCurvatureTensorAt (I := I) (L.S.base.metric t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence Ct hct
      intro K _hK
      refine Filter.Eventually.of_forall ?_
      intro k y _hy _hs
      change metricAlgebraicCurvatureTensorAt (I := I)
          ((X.term (phi k)).S.base.metric t) (Phi.map k y) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I)
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have h := (hsource (phi k)).nonnegativeCurvatureOperator t ht
        (Phi.map k y) n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval,
        metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
        metricRm04_apply] using h
    intro y n c v w
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone y)) n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  have hnoncollapsed : PointedFlowNoncollapsedAllScales (I := I) L kappa := by
    intro time ball hcurvature
    obtain ⟨Ct, hct⟩ := hconv time time.property
    have hnc := tensor_noncollapsed_of_pointed_canonical_convergence Ct hct
      (hcomplete time time.property) kappa (fun i p r hr hcurv => by
        let b : FlowMetricBall (X.term i).S time := ⟨p, r, hr⟩
        have hb : b.IsSpatiallyRmControlled := by
          intro z hz
          exact hcurv z hz
        exact ((hsource i).noncollapsed time b hb).2)
    refine ⟨(hsource 0).kappa_pos, ?_⟩
    exact hnc ball.center ball.radius ball.radius_pos hcurvature
  have hL : IsAncientKappaSolution (I := I) kappa L :=
    { kappa_pos := (hsource 0).kappa_pos
      carrier_eq := by rw [hD]; rfl
      regular_eq := by rw [hD]; rfl
      connected := hconnected
      complete := hcomplete
      nonnegativeCurvatureOperator := hoperator
      globalScalarBound := ⟨B, hscalar⟩
      noncollapsed := hnoncollapsed
      notFlat := pointedFlowNotFlat_of_scalar_ne_zero L ht0 L.basepoint
        (by change L.S.scalar 0 L.basepoint ≠ 0; rw [hscalarBase]; norm_num) }
  have hRm : PointedFlowRmNormSqBounded (I := I) L (3 * B ^ 2) := by
    intro t ht y
    have hnorm := ancientKappa_rmNormLeScalar L hdim hL t ht y
    have hupper : Real.sqrt (L.rmNormSq (I := I) t y) ≤ Real.sqrt 3 * B :=
      hnorm.trans (mul_le_mul_of_nonneg_left (hscalar t ht y).2 (Real.sqrt_nonneg 3))
    have hright : 0 ≤ Real.sqrt 3 * B :=
      mul_nonneg (Real.sqrt_nonneg 3) (zero_le_one.trans hB)
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hright).2 hupper
    rw [Real.sq_sqrt (pointedFlow_rmNormSq_nonneg (I := I) L t y),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsquare
    exact hsquare
  exact ⟨hL, hscalarBase, hscalar, hRm⟩

end AncientLimit

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
