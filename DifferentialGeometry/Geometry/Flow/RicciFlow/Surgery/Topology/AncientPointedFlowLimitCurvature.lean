import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalScalarAncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ParabolicOfSpatialAncient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false

noncomputable section
open Set Filter TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

open CanonicalNeighborhood.FiniteHorn
  (curvatureOperator_nonnegative_of_metricCInf_admissible_pinching) in
theorem curvatureOperator_nonnegative_of_local_pinching_limit
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M} {h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n)}
    {f : ℕ → ℕ} (hf : StrictMono f) {V : ℕ → Opens P.M} (hV : Monotone V)
    (hcover : ∀ x : P.M, ∃ k, x ∈ V k) {N : ℕ → ℕ}
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I I ∞ (φ k j hj)}
    {G : ℝ → SmoothRiemannianMetric I P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) :
    ∀ t ≤ 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro t ht x
  obtain ⟨k, hxk⟩ := hcover x
  obtain ⟨l, hl⟩ := exists_nat_ge (-t)
  set n := max k l
  have hxn : x ∈ V n := hV (le_max_left k l) hxk
  have htn : t ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
    refine ⟨?_, ht⟩
    have hh : (l : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right k l)
    push_cast
    linarith
  let _ : SigmaCompactSpace (V n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (V n).isOpen)
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N n))).and
      ((hQ.comp hfψ).eventually (eventually_gt_atTop (0 : ℝ))))
  let seq : ℕ → SmoothRiemannianMetric I (V n) := fun i =>
    localPullMetric (h n (f (ψ (i + i0))) t) (φ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
  have hconvU : MetricCInfConvergenceOnCompacts seq ((G t).restrictOpen (V n))
      (P.metric.restrictOpen (V n)) := by
    intro K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconv n K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ (i + i0) (by omega)
    exact hb t htn
  have hpinchU : ∀ᶠ i in atTop, ∀ y : V n,
      curvatureOperatorLowerBoundAt (seq i) y (metricAlgebraicCurvatureTensorAt (seq i) y)
        (rescalePinchingFunction (Q (f (ψ (i + i0)))) Phi (metricScalarAt (seq i) y)) := by
    filter_upwards [(hfψ.comp (tendsto_add_atTop_nat i0)).eventually (hpinch n)] with i hi y
    have h1 := hi t htn (φ n (ψ (i + i0)) (hi0 (i + i0) (by omega)).1 y)
    rw [curvatureOperatorLowerBoundAt_localPullMetric_iff, metricScalarAt_localPull]
    exact h1
  have hnonneg := curvatureOperator_nonnegative_of_metricCInf_admissible_pinching seq
    ((G t).restrictOpen (V n)) (P.metric.restrictOpen (V n)) hconvU hPhi
    (fun i => Q (f (ψ (i + i0)))) (fun i => (hi0 (i + i0) (by omega)).2)
    ((hQ.comp hfψ).comp (tendsto_add_atTop_nat i0)) hpinchU ⟨x, hxn⟩
  exact (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    (G t) (V n) ⟨x, hxn⟩).mp hnonneg

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem riemannianMetricComplete_of_ancient_curvatureOperator_nonnegative
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] {G : ℝ → SmoothRiemannianMetric I M}
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    (hcone : ∀ t ≤ 0, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    (h0 : RiemannianMetricComplete (G 0)) :
    ∀ t ≤ 0, RiemannianMetricComplete (G t) := by
  intro t ht
  exact complete_at_earlier_time_of_ricci_nonnegative
    ({ base.metric := G } : SolutionOn (I := I) (M := M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) hG
    (a := t) (b := 0) (fun _ hs => hs.2) (fun _ hs => hs.2)
    (fun r hr x v => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (G r) x (hcone r hr.2.le x) v) h0 ⟨le_rfl, ht⟩

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

universe w wE wH
variable {E : Type wE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type wH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    {X : PointedRiemannianSeq.{w, wE, wH} I} {P : PointedRiemannianManifold.{w, wE, wH} I}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M} {h : ∀ k n, ℝ → SmoothRiemannianMetric I (W k n)}
    {f : ℕ → ℕ} (hf : StrictMono f) (hcomplete : MetricComplete P) (hconn : ConnectedSpace P.M)
    {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I I ∞ (φ k j hj)}
    {G : ℝ → SmoothRiemannianMetric I P.M} (hG0 : G 0 = P.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := P.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop) {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
      curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) :
    (∀ t ≤ 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone) ∧
    ∀ t ≤ 0, RiemannianMetricComplete (G t) := by
  have hmono : Monotone V := by
    intro k l hkl z hz
    change z ∈ (V l : Set P.M)
    have hz' : z ∈ (V k : Set P.M) := hz
    rw [hV] at hz' ⊢
    refine riemannianBallOf_mono _ _ ?_ hz'
    have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hkl 1
    linarith
  have hcover : ∀ x : P.M, ∃ k, x ∈ V k := by
    intro x
    have hne := riemannianEDistOf_ne_top P.metric P.basepoint x
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf P.metric P.basepoint x).toReal)
    refine ⟨k, ?_⟩
    change x ∈ (V k : Set P.M)
    rw [hV]
    refine (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr ?_
    push_cast
    linarith
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit hf hmono hcover hψ hconv
    hQ hPhi hpinch
  refine ⟨hcone, riemannianMetricComplete_of_ancient_curvatureOperator_nonnegative hGsol hcone ?_⟩
  rw [hG0]
  exact ⟨hcomplete⟩

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth PointedFlowData.t2
  PointedFlowData.sigmaCompact

theorem isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative
    (P : PointedRiemannianManifold.{v, 0, 0} I3) {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      ancientTimeInterval))
    (hG0 : G 0 = P.metric) (hconn : ConnectedSpace P.M)
    (hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ≤ 0, ∀ x : P.M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    {C : ℝ} (hbound : ∀ t ≤ 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C)
    {kappa : ℝ} (hkappa0 : 0 < kappa)
    (hkappa : ∀ rho : ℝ, 0 < rho → ParabolicallyKappaNoncollapsedBelowScale
      ({ base.metric := G } : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) kappa rho)
    (hbase : metricScalarAt P.metric P.basepoint = 1) :
    IsAncientKappaSolution (kappa / 30 ^ 3) (flowOfMetric ancientTimeInterval P G hsol) ∧
      PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hsol) 1 := by
  let F := flowOfMetric ancientTimeInterval P G hsol
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr le_rfl
  have hcompl : ∀ t ∈ ancientTimeInterval.carrier, MetricComplete (F.atTime t) :=
    fun t ht => (hcomplete t ht).complete
  have hnonneg :
      ∀ t ∈ ancientTimeInterval.carrier, PointedFlowNonnegativeCurvatureOperator F t := by
    intro t ht x n c v w
    have hh := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone t ht x)) n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] at hh ⊢
    exact hh
  have hscalar : PointedFlowScalarBounded F C := by
    intro t ht x
    exact ⟨metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G t) x (hcone t ht x),
      hbound t ht x⟩
  have hbase' : PointedFlowScalarAtBase F 1 := by
    change metricScalarAt (G 0) P.basepoint = 1
    rw [hG0]
    exact hbase
  refine ⟨{ kappa_pos := by positivity
            carrier_eq := rfl
            regular_eq := rfl
            connected := hconn
            complete := hcompl
            nonnegativeCurvatureOperator := hnonneg
            globalScalarBound := ⟨C, hscalar⟩
            noncollapsed :=
              pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative F hdim
                rfl rfl hcompl hnonneg ⟨C, hscalar⟩ hkappa
            notFlat := pointedFlowNotFlat_of_scalar_ne_zero F hzero P.basepoint (by
              have h1 : F.S.scalar 0 P.basepoint = 1 := hbase'
              rw [h1]
              norm_num) }, hbase'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
