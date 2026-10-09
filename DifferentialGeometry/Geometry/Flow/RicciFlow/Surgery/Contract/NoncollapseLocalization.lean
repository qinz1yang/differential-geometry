import DifferentialGeometry.Geometry.Curvature.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Family.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceInputs

set_option autoImplicit false

noncomputable section

open Bundle Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

theorem MetricFiberData.hom_inner_congr_of_inner_eq {V W : Type*}
    [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV DV' : MetricFiberData V) (DW DW' : MetricFiberData W)
    (hV : ∀ v w : V, DV.inner v w = DV'.inner v w)
    (hW : ∀ v w : W, DW.inner v w = DW'.inner v w) (A B : V →ₗ[Real] W) :
    (MetricFiberData.hom DV DW).inner A B = (MetricFiberData.hom DV' DW').inner A B := by
  simpa using MetricFiberData.hom_inner_congr DV' DW' DV DW
    (LinearEquiv.refl Real V) (LinearEquiv.refl Real W)
    (fun v w => by simpa using hV v w) (fun v w => by simpa using hW v w) A B

theorem MetricFiberData.homCLM_inner_congr_of_inner_eq {V W : Type*}
    [AddCommGroup V] [Module Real V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul Real V] [T2Space V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul Real W] [FiniteDimensional Real W]
    (DV DV' : MetricFiberData V) (DW DW' : MetricFiberData W)
    (hV : ∀ v w : V, DV.inner v w = DV'.inner v w)
    (hW : ∀ v w : W, DW.inner v w = DW'.inner v w) (A B : V →L[Real] W) :
    (MetricFiberData.homCLM DV DW).inner A B =
      (MetricFiberData.homCLM DV' DW').inner A B := by
  rw [MetricFiberData.homCLM, MetricFiberData.homCLM, MetricFiberData.pullback_inner,
    MetricFiberData.pullback_inner]
  exact MetricFiberData.hom_inner_congr_of_inner_eq DV DV' DW DW' hV hW _ _

end DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

omit [T2Space M] in
theorem inner0S_eq_of_inner_eq (g h : SmoothRiemannianMetric I M) (x : M)
    (hgh : ∀ v w : TangentSpace I x, g.inner x v w = h.inner x v w) :
    ∀ (s : Nat) (A B : Tensor0SSpace s I x), inner0S (I := I) g x s A B =
      inner0S (I := I) h x s A B := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A B
    rcases s with _ | _ | s
    · exact rfl
    · change cotangentInner (I := I) g x A B = cotangentInner (I := I) h x A B
      have hsharp : (tangentMetricData (I := I) g x).metric.sharp =
          (tangentMetricData (I := I) h x).metric.sharp := by
        have hflat : (tangentMetricData (I := I) g x).metric.flat =
            (tangentMetricData (I := I) h x).metric.flat := by
          refine LinearEquiv.ext fun v => LinearMap.ext fun w => ?_
          rw [← MetricFiberData.inner_apply, ← MetricFiberData.inner_apply,
            TangentMetricData.inner_eq (tangentMetricData (I := I) g x) v w,
            TangentMetricData.inner_eq (tangentMetricData (I := I) h x) v w]
          exact hgh v w
        rw [MetricFiberData.sharp, MetricFiberData.sharp, hflat]
      rw [cotangentInner, cotangentInner, cotangentSharpLinear, cotangentSharpLinear, hsharp]
      exact hgh _ _
    · have hD : ∀ (P Q : Tensor0SSpace (s + 1) I x),
          (tensor0SMetricData (I := I) g x (s + 1)).inner P Q =
            (tensor0SMetricData (I := I) h x (s + 1)).inner P Q :=
        ih (s + 1) (by omega)
      have hDt : ∀ (P Q : TangentSpace I x),
          (tangentMetricData (I := I) g x).metric.inner P Q =
            (tangentMetricData (I := I) h x).metric.inner P Q := by
        intro P Q
        rw [TangentMetricData.inner_eq (tangentMetricData (I := I) g x) P Q,
          TangentMetricData.inner_eq (tangentMetricData (I := I) h x) P Q]
        exact hgh P Q
      simp only [inner0S, tensor0SMetricData, tensor0SMetricStep, MetricFiberData.pullback_inner]
      exact MetricFiberData.homCLM_inner_congr_of_inner_eq _ _ _ _ hDt hD _ _

variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem rmNormSq_eq_of_metric_eventuallyEq (S S' : SolutionOn (I := I) (M := M) D)
    {s : Real} {x : M}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      (S.base.metric s).inner y v w = (S'.base.metric s).inner y v w) :
    FlowMetricBall.rmNormSq S' s x = FlowMetricBall.rmNormSq S s x := by
  have hx : ∀ v w : TangentSpace I x,
      (S.base.metric s).inner x v w = (S'.base.metric s).inner x v w := hmetric.self_of_nhds
  have hrm : S.base.rm04 s x = S'.base.rm04 s x := by
    simpa only [SolutionFamily.rm04, Geometry.Curvature.metricRm04_apply] using
      Geometry.Curvature.metricRm04At_eq_of_metric_eventuallyEq (S.base.metric s)
        (S'.base.metric s) x hmetric
  simp only [FlowMetricBall.rmNormSq, Tensor0SBundle.normSq0S_eq_inner, ← hrm]
  exact inner0S_eq_of_inner_eq (S'.base.metric s) (S.base.metric s) x
    (fun v w => (hx v w).symm) 4 _ _

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_eq_of_eqOn_closedBall (g g' : SmoothRiemannianMetric I M)
    {W : Set M} {p : M} {R : Real}
    (hW : riemannianClosedBallOf (I := I) g p R ⊆ W)
    (heq : ∀ z ∈ W, ∀ v w : TangentSpace I z, g'.inner z v w = g.inner z v w)
    (hle : ∀ (z : M) (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) :
    riemannianBallOf (I := I) g' p R = riemannianBallOf (I := I) g p R := by
  have heq' : ∀ z ∈ W, g'.inner z = g.inner z := fun z hz => by
    ext v w
    exact heq z hz v w
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    exact lt_of_le_of_lt (edistOf_mono (I := I) g g' (fun z v => hle z v) p y) hy
  · intro y hy
    have hy' : riemannianEDistOf (I := I) g p y < ENNReal.ofReal R := hy
    have h := riemannianEDistOf_eq_of_eqOn_ball (I := I) g g' hW heq' hle hy'
    simpa [riemannianBallOf, h] using hy

theorem riemannianVolumeMeasure_congr_of_inner_eqOn (g g' : SmoothRiemannianMetric I M)
    {K : Set M} (hK : MeasurableSet K)
    (heq : ∀ x ∈ K, ∀ v w : TangentSpace I x, g'.inner x v w = g.inner x v w) :
    riemannianVolumeMeasure (I := I) (M := M) g' K =
      riemannianVolumeMeasure (I := I) (M := M) g K := by
  refine le_antisymm ?_ ?_
  · have h := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
      (I := I) (M := M) g g' (C := 1) one_pos hK fun x hx v => by
        rw [heq x hx v v, one_mul]
    simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h
  · have h := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
      (I := I) (M := M) g' g (C := 1) one_pos hK fun x hx v => by
        rw [← heq x hx v v, one_mul]
    simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isOpen_riemannianBallOf (g : SmoothRiemannianMetric I M) (p : M) (r : Real) :
    IsOpen (riemannianBallOf (I := I) g p r) := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : Continuous (fun y : M => riemannianEDistOf (I := I) g p y) :=
    continuous_const.edist continuous_id
  exact isOpen_lt hcont continuous_const

omit [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_subset_of_inner_le (g g' : SmoothRiemannianMetric I M)
    (hle : ∀ (z : M) (v : TangentSpace I z), g'.inner z v v ≤ g.inner z v v)
    (p : M) (r : Real) :
    riemannianBallOf (I := I) g p r ⊆ riemannianBallOf (I := I) g' p r :=
  fun y hy =>
    lt_of_le_of_lt (edistOf_mono (I := I) g' g (fun z v => hle z v) p y) hy

end DifferentialGeometry

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Surgery

open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem FlowMetricBall.setAt_eq_of_eqOn_closedBall (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) {s : Real} {W : Set M}
    (hW : riemannianClosedBallOf (I := I) (S.base.metric s) B.center B.radius ⊆ W)
    (heq : ∀ z ∈ W, ∀ v w : TangentSpace I z,
      (S'.base.metric s).inner z v w = (S.base.metric s).inner z v w)
    (hle : ∀ (z : M) (v : TangentSpace I z),
      (S.base.metric s).inner z v v ≤ (S'.base.metric s).inner z v v) :
    B'.setAt s = B.setAt s := by
  simpa only [FlowMetricBall.setAt, riemannianBallOf, hcenter, hradius] using
    riemannianBallOf_eq_of_eqOn_closedBall (I := I) (S.base.metric s) (S'.base.metric s)
      hW heq hle

theorem FlowMetricBall.volume_eq_of_inner_eqOn (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hset : B'.set = B.set) (hmeas : MeasurableSet B.set)
    (heq : ∀ x ∈ B.set, ∀ v w : TangentSpace I x,
      (S'.base.metric (t : Real)).inner x v w = (S.base.metric (t : Real)).inner x v w) :
    B'.volume = B.volume := by
  unfold FlowMetricBall.volume
  rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric, hset]
  exact riemannianVolumeMeasure_congr_of_inner_eqOn (I := I) (M := M)
    (S.base.metric (t : Real)) (S'.base.metric (t : Real)) hmeas heq

theorem FlowMetricBall.volume_le_of_metric_agreesOn (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hsubset : B.set ⊆ B'.set)
    (heq : ∀ x ∈ B.set, ∀ v w : TangentSpace I x,
      (S'.base.metric (t : Real)).inner x v w = (S.base.metric (t : Real)).inner x v w) :
    B.volume ≤ B'.volume := by
  have hmeas : MeasurableSet B.set := by
    have hopen : IsOpen (riemannianBallOf (I := I) (S.base.metric (t : Real)) B.center
        B.radius) := isOpen_riemannianBallOf (I := I) (S.base.metric (t : Real)) B.center
      B.radius
    simpa only [FlowMetricBall.set, FlowMetricBall.setAt, riemannianBallOf] using
      hopen.measurableSet
  have hvol_eq : riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (t : Real)) B.set =
      riemannianVolumeMeasure (I := I) (M := M) (S'.base.metric (t : Real)) B.set := by
    rw [← riemannianVolumeMeasure_congr_of_inner_eqOn (I := I) (M := M)
      (S.base.metric (t : Real)) (S'.base.metric (t : Real)) hmeas heq]
  have hmono : riemannianVolumeMeasure (I := I) (M := M) (S'.base.metric (t : Real)) B.set ≤
      riemannianVolumeMeasure (I := I) (M := M) (S'.base.metric (t : Real)) B'.set :=
    MeasureTheory.measure_mono (by simpa only [FlowMetricBall.set] using hsubset)
  unfold FlowMetricBall.volume
  rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric]
  exact hvol_eq.le.trans hmono

omit [SigmaCompactSpace M] in
theorem isRmControlled_of_setAt_subset_of_rmNormSq_eq
    (S S' : SolutionOn (I := I) (M := M) D) {t : D.FlowTime}
    (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hradius : B'.radius = B.radius) (hB : B.IsRmControlled)
    (hset : ∀ s ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real), B'.setAt s ⊆ B.setAt s)
    (hnorm : ∀ s ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real), ∀ x ∈ B'.setAt s,
      FlowMetricBall.rmNormSq S' s x = FlowMetricBall.rmNormSq S s x) :
    B'.IsRmControlled := by
  refine ⟨?_, ?_⟩
  · simpa only [hradius] using hB.1
  · intro s hs x hx
    have hs' : s ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
      simpa only [hradius] using hs
    rw [hradius, hnorm s hs' x hx]
    exact hB.2 s hs' x (hset s hs' hx)

theorem isKappaNoncollapsed_of_volume_le (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t) {kappa : Real}
    (hradius : B'.radius = B.radius) (hvol : B.volume ≤ B'.volume)
    (h : B.IsKappaNoncollapsed kappa) : B'.IsKappaNoncollapsed kappa := by
  obtain ⟨hk, hle⟩ := h
  refine ⟨hk, ?_⟩
  rw [hradius]
  exact hle.trans hvol

def surgeryRegionAgreesOnParabolicBalls (S S' : SolutionOn (I := I) (M := M) D)
    (rho : Real) : Prop :=
  ∀ (t : D.FlowTime) (B' : FlowMetricBall S' t), B'.radius ≤ rho →
    ∀ s ∈ Set.Icc ((t : Real) - B'.radius ^ 2) (t : Real),
      ∃ U : Set M, IsOpen U ∧ B'.setAt s ⊆ U ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (S'.base.metric s).inner x v w = (S.base.metric s).inner x v w

def metricDomination (S S' : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
    ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real), ∀ x (v : TangentSpace I x),
      (S'.base.metric s).inner x v v ≤ (S.base.metric s).inner x v v

def isSurgeryNoncollapsingStep (S S' : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  metricDomination S S' rho ∧ surgeryRegionAgreesOnParabolicBalls S S' rho

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem isSurgeryNoncollapsingStep.metricDomination {S S' : SolutionOn (I := I) (M := M) D}
    {rho : Real} (h : isSurgeryNoncollapsingStep S S' rho) : metricDomination S S' rho :=
  h.1

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem isSurgeryNoncollapsingStep.agrees {S S' : SolutionOn (I := I) (M := M) D}
    {rho : Real} (h : isSurgeryNoncollapsingStep S S' rho) :
    surgeryRegionAgreesOnParabolicBalls S S' rho :=
  h.2

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem isSurgeryNoncollapsingStep_mono {S S' : SolutionOn (I := I) (M := M) D} {rho rho' : Real}
    (h : rho ≤ rho') (hstep : isSurgeryNoncollapsingStep S S' rho') :
    isSurgeryNoncollapsingStep S S' rho :=
  ⟨fun t r hr hrle => hstep.1 t r hr (le_trans hrle h),
    fun t B' hr => hstep.2 t B' (le_trans hr h)⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem surgeryRegionAgreesOnParabolicBalls_self (S : SolutionOn (I := I) (M := M) D)
    (rho : Real) : surgeryRegionAgreesOnParabolicBalls S S rho :=
  fun _ _ _ _ _ => ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ _ _ _ => rfl⟩

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem metricDomination_self (S : SolutionOn (I := I) (M := M) D) (rho : Real) :
    metricDomination S S rho :=
  fun _ _ _ _ _ _ _ _ => le_rfl

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem isSurgeryNoncollapsingStep_self (S : SolutionOn (I := I) (M := M) D) (rho : Real) :
    isSurgeryNoncollapsingStep S S rho :=
  ⟨metricDomination_self S rho, surgeryRegionAgreesOnParabolicBalls_self S rho⟩

theorem kappaNoncollapsedBelowScale_of_surgeryRegionAgreesOnParabolicBalls
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : KappaNoncollapsedBelowScale S kappa rho)
    (hle : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real), ∀ x (v : TangentSpace I x),
        (S'.base.metric s).inner x v v ≤ (S.base.metric s).inner x v v)
    (havoid : surgeryRegionAgreesOnParabolicBalls S S' rho) :
    KappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hB' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hradius : B'.radius = B.radius := rfl
  have hsubset : ∀ s ∈ Set.Icc ((t : Real) - B'.radius ^ 2) (t : Real),
      B.setAt s ⊆ B'.setAt s := by
    intro s hs x hx
    have hmono : riemannianEDistOf (I := I) (S'.base.metric s) B.center x ≤
        riemannianEDistOf (I := I) (S.base.metric s) B.center x :=
      edistOf_mono (I := I) (S'.base.metric s) (S.base.metric s)
        (fun z v => hle t B'.radius B'.radius_pos hr s hs z v) B.center x
    exact lt_of_le_of_lt hmono hx
  have hnorm : ∀ s ∈ Set.Icc ((t : Real) - B'.radius ^ 2) (t : Real),
      ∀ x ∈ B.setAt s, FlowMetricBall.rmNormSq S s x = FlowMetricBall.rmNormSq S' s x := by
    intro s hs x hx
    obtain ⟨U, hUopen, hball, hagree⟩ := havoid t B' hr s hs
    have hxU : x ∈ U := hball (hsubset s hs hx)
    have hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
        (S.base.metric s).inner y v w = (S'.base.metric s).inner y v w := by
      filter_upwards [hUopen.mem_nhds hxU] with y hy v w
      exact (hagree y hy v w).symm
    exact (rmNormSq_eq_of_metric_eventuallyEq (S := S) (S' := S') hmetric).symm
  have hB : B.IsRmControlled :=
    isRmControlled_of_setAt_subset_of_rmNormSq_eq (S := S') (S' := S) B' B hradius hB'
      hsubset hnorm
  have hvol : B.volume ≤ B'.volume := by
    have hagree : ∀ x ∈ B.set, ∀ v w : TangentSpace I x,
        (S'.base.metric (t : Real)).inner x v w = (S.base.metric (t : Real)).inner x v w := by
      intro x hx v w
      obtain ⟨U, _hUopen, hball, hagree⟩ := havoid t B' hr (t : Real)
        ⟨by linarith [sq_nonneg B.radius], le_rfl⟩
      exact hagree x (hball (by
        simpa only [hradius] using hsubset (t : Real)
          ⟨by linarith [sq_nonneg B.radius], le_rfl⟩ hx)) v w
    exact FlowMetricBall.volume_le_of_metric_agreesOn (S := S) (S' := S') B B'
      (hsubset (t : Real) ⟨by linarith [sq_nonneg B.radius], le_rfl⟩) hagree
  exact isKappaNoncollapsed_of_volume_le (S := S) (S' := S') B B' hradius hvol
    (h.2 t B hr hB)

theorem kappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : KappaNoncollapsedBelowScale S kappa rho)
    (hstep : isSurgeryNoncollapsingStep S S' rho) :
    KappaNoncollapsedBelowScale S' kappa rho :=
  kappaNoncollapsedBelowScale_of_surgeryRegionAgreesOnParabolicBalls S S' kappa rho h
    hstep.1 hstep.2

theorem spatiallyKappaNoncollapsedBelowScale_of_surgeryRegionAgreesOnParabolicBalls
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hle : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real), ∀ x (v : TangentSpace I x),
        (S'.base.metric s).inner x v v ≤ (S.base.metric s).inner x v v)
    (havoid : surgeryRegionAgreesOnParabolicBalls S S' rho) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hspat' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hradius : B'.radius = B.radius := rfl
  have htime : (t : Real) ∈ Set.Icc ((t : Real) - B'.radius ^ 2) (t : Real) :=
    ⟨by linarith [sq_nonneg B'.radius], le_rfl⟩
  have hsubset : B.set ⊆ B'.set := by
    intro x hx
    have hmono : riemannianEDistOf (I := I) (S'.base.metric (t : Real)) B.center x ≤
        riemannianEDistOf (I := I) (S.base.metric (t : Real)) B.center x :=
      edistOf_mono (I := I) (S'.base.metric (t : Real)) (S.base.metric (t : Real))
        (fun z v => hle t B'.radius B'.radius_pos hr (t : Real) htime z v) B.center x
    exact lt_of_le_of_lt hmono hx
  have hagree : ∀ x ∈ B.set, ∀ v w : TangentSpace I x,
      (S'.base.metric (t : Real)).inner x v w = (S.base.metric (t : Real)).inner x v w := by
    intro x hx v w
    obtain ⟨U, _hUopen, hball, hagree⟩ := havoid t B' hr (t : Real) htime
    exact hagree x (hball (hsubset hx)) v w
  have hspat : B.IsSpatiallyRmControlled := by
    intro x hx
    obtain ⟨U, hUopen, hball, hagreeU⟩ := havoid t B' hr (t : Real) htime
    have hxU : x ∈ U := hball (hsubset hx)
    have hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
        (S.base.metric (t : Real)).inner y v w = (S'.base.metric (t : Real)).inner y v w := by
      filter_upwards [hUopen.mem_nhds hxU] with y hy v w
      exact (hagreeU y hy v w).symm
    have hnorm : FlowMetricBall.rmNormSq S' (t : Real) x = FlowMetricBall.rmNormSq S (t : Real) x :=
      rmNormSq_eq_of_metric_eventuallyEq (S := S) (S' := S') hmetric
    have hb := hspat' x (hsubset hx)
    rw [← hradius, ← hnorm]
    exact hb
  exact isKappaNoncollapsed_of_volume_le (S := S) (S' := S') B B' hradius
    (FlowMetricBall.volume_le_of_metric_agreesOn (S := S) (S' := S') B B' hsubset hagree)
    (h.2 t B hr hspat)

theorem spatiallyKappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep
    (S S' : SolutionOn (I := I) (M := M) D) (kappa rho : Real)
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hstep : isSurgeryNoncollapsingStep S S' rho) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa rho :=
  spatiallyKappaNoncollapsedBelowScale_of_surgeryRegionAgreesOnParabolicBalls S S' kappa rho h
    hstep.1 hstep.2

theorem noLocalCollapsing_of_isSurgeryNoncollapsingStep
    (S S' : SolutionOn (I := I) (M := M) D) (rho : Real)
    (h : NoLocalCollapsing S rho) (hstep : isSurgeryNoncollapsingStep S S' rho) :
    NoLocalCollapsing S' rho := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa, hkappa,
    kappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep S S' kappa rho hbelow hstep⟩

theorem spatialNoLocalCollapsing_of_isSurgeryNoncollapsingStep
    (S S' : SolutionOn (I := I) (M := M) D) (rho : Real)
    (h : SpatialNoLocalCollapsing S rho) (hstep : isSurgeryNoncollapsingStep S S' rho) :
    SpatialNoLocalCollapsing S' rho := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa, hkappa,
    spatiallyKappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep S S' kappa rho hbelow hstep⟩

end Surgery
end RicciFlow
end PDE
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.PDE.RicciFlow.Surgery

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem recenteredSource_inputs_of_isSurgeryNoncollapsingStep
    (S S' : SolutionOn (I := I) (M := M) D)
    {Hd s B eps kappa rho : Real} (hB : 2 < B)
    (hs : s ∈ Set.Icc (-Hd) 0)
    (hwindow : Set.Icc (-Hd) 0 ⊆ D.carrier)
    {Phi : Real → Real}
    (hpinch : DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative
      (I := I) (M := M) S' (Set.Icc (-Hd) 0) Phi)
    (hnc : DifferentialGeometry.PDE.RicciFlow.Perelman.SpatiallyKappaNoncollapsedBelowScale
      (I := I) S kappa rho)
    (hstep : isSurgeryNoncollapsingStep S S' rho)
    (hgood : ∀ (x : M) (t : Real), t ∈ Set.Icc (-Hd) 0 →
      2 ≤ S'.scalar t x → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S' x t)
    {w : M} (hw : S'.scalar s w = B) :
    let hBpos : 0 < B := lt_trans (by norm_num : (0 : Real) < 2) hB
    let SR := DifferentialGeometry.PDE.RicciFlow.parabolicSolution S' s B hBpos (hwindow hs)
    SR.scalar 0 w = 1 ∧
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa SR w 0 ∧
      Set.Icc (-(B * (Hd + s))) 0 ⊆
        (DifferentialGeometry.PDE.RicciFlow.parabolicInterval D s B (hwindow hs)).carrier ∧
      (∀ (x : M) (u : Real), u ∈ Set.Icc (-(B * (Hd + s))) 0 →
        2 ≤ SR.scalar u x → IsGoodPoint.{u, uE, uH} (I := I) eps kappa SR x u) ∧
      DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative (I := I) (M := M) SR
        (Set.Icc (-(B * (Hd + s))) 0)
        (DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction B Phi) ∧
      DifferentialGeometry.PDE.RicciFlow.Perelman.SpatiallyKappaNoncollapsedBelowScale
        (I := I) SR kappa (Real.sqrt B * rho) :=
  recenteredSource_inputs S' hB hs hwindow hpinch
    (spatiallyKappaNoncollapsedBelowScale_of_isSurgeryNoncollapsingStep S S' kappa rho hnc hstep)
    hgood hw

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
