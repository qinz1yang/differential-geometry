import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

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

local instance ascrImageTopology : TopologicalSpace L.M := L.topology
local instance ascrImageCharted : ChartedSpace H L.M := L.charted
local instance ascrImageSmooth : IsManifold I ∞ L.M := L.smooth
local instance ascrImageT2 : T2Space L.M := L.t2
local instance ascrImageSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance ascrImageApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance ascrImageApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance ascrImageApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

private theorem ascr_pointed_image_bounded
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

local instance ascrLimitTopology : TopologicalSpace L.M := L.topology
local instance ascrLimitCharted : ChartedSpace H L.M := L.charted
local instance ascrLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance ascrLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
local instance ascrLimitT2 : T2Space L.M := L.t2
local instance ascrLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance ascrLimitTermTopology (i : ℕ) :
    TopologicalSpace (X.term i).M := (X.term i).topology
local instance ascrLimitTermCharted (i : ℕ) :
    ChartedSpace H (X.term i).M := (X.term i).charted
local instance ascrLimitTermSmooth (i : ℕ) :
    IsManifold I ∞ (X.term i).M := (X.term i).smooth
local instance ascrLimitTermC1 (i : ℕ) : IsManifold I 1 (X.term i).M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance ascrLimitTermT2 (i : ℕ) : T2Space (X.term i).M := (X.term i).t2
local instance ascrLimitTermSigma (i : ℕ) :
    SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact

theorem ancientKappaThree_of_selected_pointed_ancient_limit
    {kappa : ℝ} (hdim : Module.finrank ℝ E = 3) (hD : X.D = ancientTimeInterval)
    (hsource : ∀ i, IsAncientKappaSolution (I := I) kappa (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I) (X.term i) 1)
    (hphi : StrictMono phi)
    (hlocal : ∀ A : ℝ, ∀ᶠ i in atTop, ∀ t ∈ X.D.carrier, ∀ z : (X.term i).M,
      (riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z).toReal ≤ A →
        0 ≤ (X.term i).S.scalar t z ∧ (X.term i).S.scalar t z ≤ 4)
    (hconnected : ConnectedSpace L.M)
    (hcomplete : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) :
    IsAncientKappaSolution (I := I) kappa L ∧
      PointedFlowScalarAtBase (I := I) L 1 ∧
      PointedFlowScalarBounded (I := I) L 4 ∧
      PointedFlowRmNormSqBounded (I := I) L 48 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have ht0 : (0 : ℝ) ∈ X.D.carrier := by simp [hD]
  obtain ⟨C0, hc0⟩ := hconv 0 ht0
  have hscalarBase : PointedFlowScalarAtBase (I := I) L 1 := by
    apply pointedScalar_base_eq_of_metricCG_canonical_domains C0 hc0
    intro k
    exact hbase (phi k)
  have hscalar : PointedFlowScalarBounded (I := I) L 4 := by
    intro t ht y
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hlim := pointedScalar_tendsto_of_metricCG_canonical_domains Ct hct y
    change Tendsto (fun k => (X.term (phi k)).S.scalar t (Phi.map k y)) atTop
      (𝓝 (L.S.scalar t y)) at hlim
    obtain ⟨A, _hA, hA⟩ := ascr_pointed_image_bounded C0 hc0
      (hcomplete 0 ht0) hconnected y
    have htail := hphi.tendsto_atTop.eventually (hlocal A)
    have hbounds : ∀ᶠ k in atTop,
        0 ≤ (X.term (phi k)).S.scalar t (Phi.map k y) ∧
          (X.term (phi k)).S.scalar t (Phi.map k y) ≤ 4 := by
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
    intro time B hcurvature
    obtain ⟨Ct, hct⟩ := hconv time time.property
    have hnc := tensor_noncollapsed_of_pointed_canonical_convergence Ct hct
      (hcomplete time time.property) kappa (fun i p r hr hcurv => by
        let b : FlowMetricBall (X.term i).S time := ⟨p, r, hr⟩
        have hb : b.IsSpatiallyRmControlled := by
          intro z hz
          exact hcurv z hz
        exact ((hsource i).noncollapsed time b hb).2)
    refine ⟨(hsource 0).kappa_pos, ?_⟩
    exact hnc B.center B.radius B.radius_pos hcurvature
  have hL : IsAncientKappaSolution (I := I) kappa L :=
    { kappa_pos := (hsource 0).kappa_pos
      carrier_eq := by rw [hD]; rfl
      regular_eq := by rw [hD]; rfl
      connected := hconnected
      complete := hcomplete
      nonnegativeCurvatureOperator := hoperator
      globalScalarBound := ⟨4, hscalar⟩
      noncollapsed := hnoncollapsed
      notFlat := pointedFlowNotFlat_of_scalar_ne_zero L ht0 L.basepoint
        (by change L.S.scalar 0 L.basepoint ≠ 0; rw [hscalarBase]; norm_num) }
  have hRm := pointedFlowRmNormSqBounded_of_scalarBounded (I := I) L
    (Real.sqrt_nonneg 3) hscalar (ancientKappa_rmNormLeScalar L hdim hL)
  have hconstant : (Real.sqrt 3 * 4) ^ 2 = (48 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hconstant] at hRm
  exact ⟨hL, hscalarBase, hscalar, hRm⟩

end AncientLimit

section NormalizedSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ascrLimitSourceTopology : TopologicalSpace F.M := F.topology
local instance ascrLimitSourceCharted : ChartedSpace H F.M := F.charted
local instance ascrLimitSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance ascrLimitSourceT2 : T2Space F.M := F.t2
local instance ascrLimitSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem terminalCurvatureNormalizedFlowSeq_ancient_limit_geometry
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F) (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3) (x : ℕ → F.M) (r : ℕ → ℝ)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z, (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal <
      r i → F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (Phi : PointedCGHMaps (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ)
      (L.atTime (I := I) 0) phi)
    (hconnected : @ConnectedSpace L.M L.topology)
    (hcomplete : ∀ t ≤ 0, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ≤ 0,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t) k) :
    IsAncientKappaSolution (I := I) kappa L ∧
      PointedFlowScalarAtBase (I := I) L 1 ∧
      PointedFlowScalarBounded (I := I) L 4 ∧
      PointedFlowRmNormSqBounded (I := I) L 48 := by
  let X := terminalCurvatureNormalizedFlowSeq F hK x hQ
  have htime : X.D.carrier = Set.Iic (0 : ℝ) := by
    change ancientTimeInterval.carrier = Set.Iic (0 : ℝ)
    simp
  have hsource (i : ℕ) : IsAncientKappaSolution (I := I) kappa (X.term i) :=
    isAncientKappaSolution_curvatureNormalizedFlow F hF
      0 (F.S.scalar 0 (x i)) (hQ i)
      (by simpa only [hF.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
      (x i) rfl
  apply ancientKappaThree_of_selected_pointed_ancient_limit X L Phi hdim rfl hsource
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ) hphi
    _ hconnected
    (fun t ht => hcomplete t (by simpa only [htime, Set.mem_Iic] using ht))
    (fun t ht => hconv t (by simpa only [htime, Set.mem_Iic] using ht))
  intro A
  filter_upwards [hexpand (eventually_gt_atTop A)] with i hi
  intro t ht z hz
  change F.M at z
  let g : SmoothRiemannianMetric I F.M := ((X.atZero (I := I)).obj i).metric
  have hcomm : riemannianEDistOf (I := I) g z (x i) =
      riemannianEDistOf (I := I) g (x i) z := by
    let _ : RiemannianBundle (fun y : F.M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist I z (x i) = Manifold.riemannianEDist I (x i) z
    exact Manifold.riemannianEDist_comm (I := I) (x := z) (y := x i)
  have hz' : (riemannianEDistOf (I := I) g z (x i)).toReal ≤ A := by
    rw [hcomm]
    exact hz
  exact terminalCurvatureNormalizedFlowSeq_scalar_bound F hK x hQ i (r i)
    (hlocal i) (by simpa only [htime, Set.mem_Iic] using ht) z (hz'.trans_lt hi)

end NormalizedSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
