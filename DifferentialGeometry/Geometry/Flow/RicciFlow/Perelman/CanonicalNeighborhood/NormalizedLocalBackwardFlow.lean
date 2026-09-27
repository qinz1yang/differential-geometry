import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLocalCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.MetricConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem secLower_zero_of_local_normalized_metric_convergence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hPhi : AdmissiblePinchingFunction Phi)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (L : PointedRiemannianManifold.{0, 0, 0} I3)
    (V : TopologicalSpace.Opens L.M) (hp : L.basepoint ∈ V)
    (F : ∀ i, PartialDiffeomorph I3 I3 L.M (X.term (f i)).M ∞)
    (hsource : ∀ i, (V : Set L.M) ⊆ (F i).source)
    (hbase : ∀ i, F i L.basepoint = (X.term (f i)).basepoint)
    (t : ℝ) (ht : t ≤ 0)
    (G : ℕ → SmoothRiemannianMetric I3 V) (g r : SmoothRiemannianMetric I3 V)
    (hmetric : ∀ i (x : V) (v w : TangentSpace I3 x),
      (G i).inner x v w = ((X.term (f i)).S.base.metric t).inner (F i x)
        (mfderiv I3 I3 (F i) x v) (mfderiv I3 I3 (F i) x w))
    (hconv : MetricCInfConvergenceOnCompacts G g r) :
    SecLower g 0 univ ∧ (t = 0 → metricScalarAt g ⟨L.basepoint, hp⟩ = 1) := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P : PointedRiemannianManifold I3 := {L.restrictOpen V hp with metric := g}
  let Y : PointedRiemannianSeq I3 := {obj := fun i => {P with metric := G i}}
  let maps : PointedRiemannianConvergenceMaps Y P id := {
    partialDiffeomorph := fun _ => PartialDiffeomorph.refl (I := I3) V
    source_exhausts := ⟨fun _ => isOpen_univ, fun _ => subset_univ _,
      fun _ _ => ⟨0, fun _ _ => subset_univ _⟩⟩
    base_mem := fun _ => mem_univ _
    basepoint_map := fun _ => rfl }
  obtain ⟨C, hcanonical, _⟩ := exists_canonicalMetricConvergenceData_of_metric_extension
    maps G (hconv.change_reference g) (by
      intro K _
      exact Eventually.of_forall fun i => ⟨univ, isOpen_univ, subset_univ _, subset_univ _,
        fun x _ v w => by
          change (G i).inner x v w = (G i).inner x
            (mfderiv I3 I3 id x v) (mfderiv I3 I3 id x w)
          rw [mfderiv_id]
          rfl⟩)
  have hlocal (i : ℕ) : IsLocalDiffeomorph I3 I3 ∞ (fun x : V => F i x) :=
    isLocalDiffeomorph_restrict_open V (fun x => ⟨F i, hsource i x.property, fun _ _ => rfl⟩)
  have hg (i : ℕ) : G i = localPullMetric ((X.term (f i)).S.base.metric t)
      (fun x : V => F i x) (hlocal i) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hd (z : TangentSpace I3 x) : mfderiv I3 I3 (fun x : V => F i x) x z =
        mfderiv I3 I3 (F i) (x : L.M) z := by
      change mfderiv I3 I3 ((F i : L.M → (X.term (f i)).M) ∘ Subtype.val) x z = _
      rw [mfderiv_comp x
        (((F i).contMDiffOn_toFun.contMDiffAt
          ((F i).open_source.mem_nhds (hsource i x.property))).mdifferentiableAt (by simp))
          ((contMDiff_subtype_val (I := I3) (U := V) (n := ∞)).mdifferentiableAt (by simp)),
        ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    rw [localPullMetric_inner, hd, hd]
    exact hmetric i x v w
  have hscalar (i : ℕ) (x : V) : metricScalarAt (G i) x =
      metricScalarAt ((X.term (f i)).S.base.metric t) (F i x) := by
    rw [hg, metricScalarAt_localPull]
  have htime : ∀ᶠ i in atTop, t ∈ (X.interval (f i)).carrier := by
    filter_upwards [(X.depth_tendsto.comp hf.tendsto_atTop).eventually_ge_atTop (-t)] with i hi
    change -t ≤ X.depth (f i) at hi
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], ht⟩
  have hpin : ∀ᶠ i in atTop, ∀ x : V, curvatureOperatorLowerBoundAt (G i) x
      (metricAlgebraicCurvatureTensorAt (G i) x)
      (rescalePinchingFunction (X.scale (f i)) Phi (metricScalarAt (G i) x)) := by
    filter_upwards [htime] with i hi
    intro x
    rw [hscalar, hg, curvatureOperatorLowerBoundAt_localPullMetric_iff]
    have hh := X.pinching (f i) t hi (F i x)
    simpa only [PhiAlmostNonnegative, SolutionFamily.rm04, metricRm04_apply,
      SolutionOn.scalar, SolutionFamily.scalar, metricAlgebraicCurvatureTensorAt] using hh
  have hsec := sectional_nonnegative_of_pointed_admissible_pinching_eventually
    C hcanonical hPhi (fun i => X.scale (f i)) (fun i => X.scale_pos (f i))
    (X.scale_tendsto.comp hf.tendsto_atTop) hpin
  refine ⟨?_, ?_⟩
  · intro x _ v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> rfl
    have hh : 0 ≤ metricRm04StandardAt g x v w w v := hsec x v w
    simpa only [SecLower, zero_mul, metricRm04StandardAt_apply, hslots] using hh
  · intro ht0
    apply KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
    intro i
    change metricScalarAt (G i) ⟨L.basepoint, hp⟩ = 1
    rw [hscalar, hbase, ht0]
    exact X.base_one (f i)

theorem exists_nonnegative_local_backward_limit {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar tau r : ℝ, 0 < epsStar ∧ 0 < tau ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∃ f : ℕ → ℕ, StrictMono f ∧
            ∃ L : PointedRiemannianManifold.{0, 0, 0} I3,
            ∃ V : TopologicalSpace.Opens L.M, ∃ hp : L.basepoint ∈ V,
            ∃ F : ∀ i, PartialDiffeomorph I3 I3 L.M (X.term (f i)).M ∞,
            ∃ htau : -tau ≤ 0,
            ∃ S : ℕ → SolutionOn (I := I3) (M := V) (RealTimeInterval.closed (-tau) 0 htau),
            IsCompact (closure (V : Set L.M)) ∧
            (∀ i, closure (V : Set L.M) ⊆ (F i).source) ∧
            (∀ i, F i L.basepoint = (X.term (f i)).basepoint) ∧
            (∀ i, riemannianClosedBallOf ((X.term (f i)).S.base.metric 0)
                (X.term (f i)).basepoint (r / 2) ⊆ (F i) '' (V : Set L.M)) ∧
            (∀ i, (F i) '' closure (V : Set L.M) ⊆
              riemannianBallOf ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint r) ∧
            (∀ i, IsSolutionOn (S i)) ∧
            (∀ i t (x : V) (v w : TangentSpace I3 x),
              ((S i).base.metric t).inner x v w =
                ((X.term (f i)).S.base.metric t).inner (F i x)
                  (mfderiv I3 I3 (F i) x v) (mfderiv I3 I3 (F i) x w)) ∧
            MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
              (L.metric.restrictOpen V) (L.metric.restrictOpen V) ∧
            (∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ ∀ i m t, t ∈ Icc (-tau) 0 →
              ∀ x : V, curvDerivNorm m ((S i).base.metric t) x ≤ B m) ∧
            ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I3 V,
              g 0 = L.metric.restrictOpen V ∧
              IsSolutionOn ({base.metric := g} : SolutionOn (I := I3) (M := V)
                (RealTimeInterval.closed (-tau / 2) 0 (by linarith))) ∧
              (∀ t ∈ Icc (-tau / 2) 0, SecLower (g t) 0 univ) ∧
              metricScalarAt (g 0) ⟨L.basepoint, hp⟩ = 1 ∧
              ∀ K : Set V, IsCompact K → ∀ p : ℕ, ∀ eta : ℝ, 0 < eta →
                ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc (-tau / 2) 0,
                  metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t)
                    (L.metric.restrictOpen V) < eta := by
  obtain ⟨epsCyl, tau, r, hepsCyl, htau, hr, B, hB, hprop⟩ :=
    exists_curvDerivNorm_bound_on_terminal_cylinder.{u} hkappa
  obtain ⟨epsNC, hepsNC, hnc⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  refine ⟨min epsCyl epsNC, tau, r, lt_min hepsCyl hepsNC, htau, hr, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hb := hprop eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X
  obtain ⟨kappa', -, hncX⟩ := hnc Phi hPhi
  have hncX := hncX eps heps (hle.trans (min_le_right _ _)) sigma X
  have hcomplete : SeqMetricComplete (X.toFlowSequence.atTime 0) := by
    constructor
    intro i
    apply X.complete i 0
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hbound : ∀ᶠ i in atTop, ∀ y, metricDistance ((X.term i).S.base.metric 0)
      (X.term i).basepoint y < r → curvDerivNorm 0 ((X.term i).S.base.metric 0) y ≤ B 0 := by
    filter_upwards [hb] with i hi y hy
    apply hi.2.2 0 0 ⟨by linarith, le_rfl⟩ y
    let _ := X.connected i
    have hfinite := riemannianEDistOf_ne_top ((X.term i).S.base.metric 0)
      (X.term i).basepoint y
    exact (ENNReal.le_ofReal_iff_toReal_le hfinite hr.le).mpr hy.le
  obtain ⟨eta, heta, hinj⟩ := X.eventually_hasInjRadiusAt_on_closed_ball_of_curvature_bound
    hncX (r := r / 2) (by positivity) (by linarith) hbound
  obtain ⟨phi, hphi, Q, top, chart, hman, hT2, hsecond, gQ, V, U, q, F, G,
    hV, hVU, hq, hG, hconv, hF⟩ :=
    exists_finite_pointed_metric_comparison_of_local_curvature_injectivity
      (X.toFlowSequence.atTime 0) hcomplete X.connected (r := r / 2) (R := r)
      (by positivity) (by linarith) heta (by
        intro m
        refine ⟨B m, hB m, ?_⟩
        filter_upwards [hb] with i hi y hy
        exact hi.2.2 m 0 ⟨by linarith, le_rfl⟩ y hy) hinj
  let _ := top
  let _ := chart
  let _ := hman
  let _ := hT2
  let _ := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace ThreeSpace Q
  let _ : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  let L : PointedRiemannianManifold.{0, 0, 0} I3 := {
    M := Q
    topology := top
    charted := chart
    smooth := hman
    t2 := hT2
    sigmaCompact := inferInstance
    t2TangentBundle := inferInstance
    basepoint := q
    metric := gQ }
  have hVU' : V ≤ U := subset_closure.trans hVU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hF.and hG).and (hphi.tendsto_atTop hb))
  let f : ℕ → ℕ := fun i => phi (i + N)
  have hf : StrictMono f := hphi.comp (show StrictMono (fun i : ℕ => i + N) from fun _ _ h => Nat.add_lt_add_right h N)
  choose Psi hsource hEq hbase hcapture hupper using fun i => (hN (i + N) (by omega)).1.1
  have hsrc (i : ℕ) : (V : Set Q) ⊆ (Psi i).source :=
    fun x hx => hsource i (subset_closure (hVU' hx))
  let D := RealTimeInterval.closed (-tau) 0 (neg_nonpos.mpr htau.le)
  have hpull (i : ℕ) : ∃ S : SolutionOn (I := I3) (M := V) D, IsSolutionOn S ∧
      ∀ t (x : V) (v w : TangentSpace I3 x), (S.base.metric t).inner x v w =
        ((X.term (f i)).S.base.metric t).inner (Psi i x)
          (mfderiv I3 I3 (Psi i) x v) (mfderiv I3 I3 (Psi i) x w) := by
    obtain ⟨S, hS, hmetric⟩ := KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (X.term (f i)).S (X.term (f i)).isSolution (Psi i) V (hsrc i)
    refine ⟨S.timeRestrict D, isSolutionOn_timeRestrict hS ?_ ?_, hmetric⟩
    · exact (Icc_subset_Icc (by linarith) le_rfl).trans (hN (i + N) (by omega)).2.1
    · exact (Ioo_subset_Ico_self.trans (Ico_subset_Ico (by linarith) le_rfl)).trans
        (hN (i + N) (by omega)).2.2.1
  choose S hS hmetric using hpull
  have hterminal : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
      (L.metric.restrictOpen V) (L.metric.restrictOpen V) := by
    have hc := (hconv.comp_subseq (show StrictMono (fun i : ℕ => i + N) from fun _ _ h => Nat.add_lt_add_right h N)).restrictOpenOfSubset hVU'
    have he : (gQ.restrictOpen U).restrictOpenOfSubset hVU' = gQ.restrictOpen V := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rfl
    rw [he] at hc
    apply hc.congr (Eventually.of_forall fun i => ?_)
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hnear : (Psi i : Q → (X.term (f i)).M) =ᶠ[𝓝 (x : Q)] F (i + N) :=
      Filter.eventuallyEq_of_mem ((Psi i).open_source.mem_nhds (hsrc i x.property)) (hEq i)
    have hv := hnear.mfderiv_eq (I := I3) (I' := I3)
    change (G (i + N)).inner ⟨x, hVU' x.property⟩ v w = _
    erw [(hN (i + N) (by omega)).1.2, hmetric, hnear.self_of_nhds, hv]
    rfl
  have hjets (i m : ℕ) (t : ℝ) (ht : t ∈ Icc (-tau) 0) (x : V) :
      curvDerivNorm m ((S i).base.metric t) x ≤ B m := by
    rw [curvDerivNorm_eq_of_partialDiffeomorph_restriction (Psi i) V (hsrc i)
      ((S i).base.metric t) ((X.term (f i)).S.base.metric t) (hmetric i t)]
    have hx : riemannianEDistOf ((X.term (f i)).S.base.metric 0)
        (X.term (f i)).basepoint (Psi i x) < ENNReal.ofReal r :=
      hupper i ⟨x, subset_closure x.property, rfl⟩
    exact (hN (i + N) (by omega)).2.2.2 m t ht (Psi i x) hx.le
  have hslab : Icc (-tau / 2) 0 ⊆ D.carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-tau / 2) 0 ⊆ D.regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨rho, hrho, g, hg0, hg⟩ :=
    exists_metric_subsequence_on_closed_interval_of_terminal_convergence S hS
      (L.metric.restrictOpen V) (show -tau / 2 < 0 by linarith) hslab hreg hterminal (by
        intro K _ m
        exact ⟨B m, hB m, Eventually.of_forall fun i t ht x _ =>
          hjets i m t ⟨by linarith [ht.1], ht.2⟩ x⟩)
  let P := L.restrictOpen V hq
  have hsol := isSolutionOn_of_fixed_domain_metric_convergence P S hS
    (show -tau / 2 < 0 by linarith) hslab (Ioo_subset_Ico_self.trans hreg)
    rho hrho g hg (by
      intro K hK m
      exact Eventually.of_forall fun i => by
        obtain ⟨C, _, hc⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S i) (hS i) (show -tau / 2 < 0 by linarith) hslab hreg P.metric hK m
        exact ⟨C, fun s hs t ht p hp x hx => hc p hp s hs t ht x hx⟩)
  have hgeometry (t : ℝ) (ht : t ∈ Icc (-tau / 2) 0) :=
    secLower_zero_of_local_normalized_metric_convergence X hPhi (f ∘ rho) (hf.comp hrho)
      L V hq (fun i => Psi (rho i)) (fun i => hsrc (rho i)) (fun i => hbase (rho i))
      t ht.2 (fun i => (S (rho i)).base.metric t) (g t) (L.metric.restrictOpen V)
      (fun i => hmetric (rho i) t) (by
        intro K hK m epsilon hepsilon
        obtain ⟨N, hN⟩ := hg K hK m epsilon hepsilon
        exact ⟨N, fun i hi => hN i hi t ht⟩)
  exact ⟨f, hf, L, V, hq, Psi, (neg_nonpos.mpr htau.le), S, hV,
    fun i => hVU.trans (subset_closure.trans (hsource i)), hbase, hcapture, hupper,
    hS, hmetric, hterminal, ⟨B, hB, hjets⟩, rho, hrho, g, hg0, hsol,
    fun t ht => (hgeometry t ht).1, (hgeometry 0 ⟨by linarith, le_rfl⟩).2 rfl, hg⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
