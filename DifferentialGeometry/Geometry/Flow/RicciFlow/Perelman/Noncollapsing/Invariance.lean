import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.AllScales
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Family.Metric
import DifferentialGeometry.Geometry.Metric.Distance.Ball

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

private theorem sub_mem_Icc {a r x τ : Real} (h : x ∈ Set.Icc (a - r ^ 2) a) :
    x - τ ∈ Set.Icc ((a - τ) - r ^ 2) (a - τ) := by
  constructor <;> linarith [h.1, h.2]

private theorem add_mem_Icc {a r x τ : Real}
    (h : x ∈ Set.Icc ((a - τ) - r ^ 2) (a - τ)) :
    x + τ ∈ Set.Icc (a - r ^ 2) a := by
  constructor <;> linarith [h.1, h.2]

noncomputable section

open Bundle MeasureTheory DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem setAt_timeShift (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) (s : Real) :
    B'.setAt s = B.setAt (s + τ) := by
  simp only [setAt, hcenter, hradius, SolutionOn.timeShift_base_metric]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem set_timeShift (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime} (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.set = B.set := by
  change B'.setAt (t' : Real) = B.setAt (t : Real)
  rw [setAt_timeShift (S := S) τ B B' hcenter hradius, ht]

omit [SigmaCompactSpace M] in
theorem rmNormSq_timeShift (S : SolutionOn (I := I) (M := M) D) (τ s : Real) (x : M) :
    rmNormSq (S.timeShift τ) s x = rmNormSq S (s + τ) x :=
  rfl

omit [SigmaCompactSpace M] in
theorem isRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D) (τ : Real)
    {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime} (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsRmControlled ↔ B.IsRmControlled := by
  have ht' : (t' : Real) = (t : Real) - τ := by linarith [ht]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hcar := h.1 hs'
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq] at hcar
      simpa only [sub_add_cancel] using hcar
    · intro s hs x hx
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hx' : x ∈ B'.setAt (s - τ) := by
        rw [setAt_timeShift (S := S) τ B B' hcenter hradius, sub_add_cancel]
        exact hx
      have hk := h.2 (s - τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift, sub_add_cancel] using hk
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq]
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      exact h.1 hs'
    · intro s hs x hx
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      have hx' : x ∈ B.setAt (s + τ) := by
        rw [← setAt_timeShift (S := S) τ B B' hcenter hradius s]
        exact hx
      have hk := h.2 (s + τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift] using hk

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsSpatiallyRmControlled ↔ B.IsSpatiallyRmControlled := by
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h x hx
    have hx' : x ∈ B'.set := by rwa [hset]
    have hk := h x hx'
    simpa only [hradius, rmNormSq_timeShift, ht] using hk
  · intro h x hx
    have hx' : x ∈ B.set := by rwa [← hset]
    have hk := h x hx'
    simpa only [hradius, rmNormSq_timeShift, ht] using hk

omit [SigmaCompactSpace M] in
theorem isParabolicallyRmControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsParabolicallyRmControlled ↔ B.IsParabolicallyRmControlled := by
  have ht' : (t' : Real) = (t : Real) - τ := by linarith [ht]
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hcar := h.1 hs'
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq] at hcar
      simpa only [sub_add_cancel] using hcar
    · intro s hs x hx
      have hs' : s - τ ∈ Set.Icc ((t' : Real) - B'.radius ^ 2) (t' : Real) := by
        rw [ht', hradius]
        exact sub_mem_Icc hs
      have hx' : x ∈ B'.set := by rwa [hset]
      have hk := h.2 (s - τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift, sub_add_cancel] using hk
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq]
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      exact h.1 hs'
    · intro s hs x hx
      have hs' : s + τ ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real) := by
        rw [ht', hradius] at hs
        exact add_mem_Icc hs
      have hx' : x ∈ B.set := by rwa [← hset]
      have hk := h.2 (s + τ) hs' x hx'
      simpa only [hradius, rmNormSq_timeShift] using hk

omit [T2Space M] [SigmaCompactSpace M] in
theorem isScalarControlled_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) :
    B'.IsScalarControlled ↔ B.IsScalarControlled := by
  have hset : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
  constructor
  · intro h x hx
    have hx' : x ∈ B'.set := by rwa [hset]
    have hk := h x hx'
    simpa only [hradius, SolutionOn.timeShift_scalar, ht] using hk
  · intro h x hx
    have hx' : x ∈ B.set := by rwa [← hset]
    have hk := h x hx'
    simpa only [hradius, SolutionOn.timeShift_scalar, ht] using hk

theorem isKappaNoncollapsed_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ : Real) {t : D.FlowTime} {t' : (D.timeShift τ).FlowTime}
    (ht : (t' : Real) + τ = (t : Real))
    (B : FlowMetricBall S t) (B' : FlowMetricBall (S.timeShift τ) t')
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius) (kappa : Real) :
    B'.IsKappaNoncollapsed kappa ↔ B.IsKappaNoncollapsed kappa := by
  have hvol : B'.volume = B.volume := by
    unfold volume
    have hm : (S.timeShift τ).family.metric (t' : Real) = S.family.metric (t : Real) := by
      rw [SolutionOn.timeShift_family_metric, ht]
    have hs : B'.set = B.set := set_timeShift (S := S) τ ht B B' hcenter hradius
    rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric, hm, hs]
  simp only [IsKappaNoncollapsed, hradius, hvol]

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem setAt_metric_eq (S S' : SolutionOn (I := I) (M := M) D) {t : D.FlowTime}
    (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (s : Real) (hmetric : S'.base.metric s = S.base.metric s) :
    B'.setAt s = B.setAt s := by
  simp only [setAt, hcenter, hradius, hmetric]

omit [SigmaCompactSpace M] in
theorem isRmControlled_of_metric_eqOn (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : ∀ s ∈ Set.Icc ((t : Real) - B.radius ^ 2) (t : Real),
      S'.base.metric s = S.base.metric s)
    (hB : B.IsRmControlled) : B'.IsRmControlled := by
  refine ⟨?_, ?_⟩
  · intro s hs
    exact hB.1 (by simpa only [hradius] using hs)
  · intro s hs x hx
    have hx' : x ∈ B.setAt s := by
      rw [← setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius s
        (hmetric s (by simpa only [hradius] using hs))]
      exact hx
    have hk := hB.2 s (by simpa only [hradius] using hs) x hx'
    simpa only [hradius, rmNormSq, SolutionFamily.rm04,
      hmetric s (by simpa only [hradius] using hs)] using hk

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_of_metric_eq (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : S'.base.metric (t : Real) = S.base.metric (t : Real))
    (hB : B.IsSpatiallyRmControlled) : B'.IsSpatiallyRmControlled := by
  intro x hx
  have hx' : x ∈ B.set := by
    change x ∈ B.setAt (t : Real)
    rw [← setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius (t : Real) hmetric]
    exact hx
  have hk := hB x hx'
  simpa only [hradius, rmNormSq, SolutionFamily.rm04, hmetric] using hk

theorem isKappaNoncollapsed_of_metric_eq (S S' : SolutionOn (I := I) (M := M) D)
    {t : D.FlowTime} (B : FlowMetricBall S t) (B' : FlowMetricBall S' t)
    (hcenter : B'.center = B.center) (hradius : B'.radius = B.radius)
    (hmetric : S'.base.metric (t : Real) = S.base.metric (t : Real))
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) : B'.IsKappaNoncollapsed kappa := by
  have hvol : B'.volume = B.volume := by
    unfold volume
    have hs : B'.set = B.set := by
      change B'.setAt (t : Real) = B.setAt (t : Real)
      rw [setAt_metric_eq (S := S) (S' := S') B B' hcenter hradius (t : Real) hmetric]
    rw [volumeMeasureOn_eq_metric, volumeMeasureOn_eq_metric, SolutionOn.family_metric,
      SolutionOn.family_metric, hmetric, hs]
  simp only [IsKappaNoncollapsed, hradius, hvol]
  exact hB

omit [FiniteDimensional Real E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem set_eq_riemannianBallOf (S : SolutionOn (I := I) (M := M) D) {time : D.FlowTime}
    (B : FlowMetricBall S time) :
    B.set = riemannianBallOf (I := I) (S.base.metric (time : Real)) B.center B.radius :=
  rfl

theorem volume_eq_riemannianVolumeMeasure (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) :
    B.volume = riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real))
      B.set := by
  unfold volume
  rw [volumeMeasureOn_eq_metric, SolutionOn.family_metric]

theorem isKappaNoncollapsed_iff_volumeMeasure (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) (kappa : Real) :
    B.IsKappaNoncollapsed kappa ↔
      0 < kappa ∧ ENNReal.ofReal (kappa * B.radius ^ Module.finrank Real E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real)) B.set := by
  have hvol := volume_eq_riemannianVolumeMeasure (S := S) B
  constructor
  · rintro ⟨hkappa, hle⟩
    refine ⟨hkappa, ?_⟩
    rw [← hvol, ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow B.radius_pos.le]
    exact hle
  · rintro ⟨hkappa, hle⟩
    refine ⟨hkappa, ?_⟩
    rw [hvol, ← ENNReal.ofReal_pow B.radius_pos.le, ← ENNReal.ofReal_mul hkappa.le]
    exact hle

theorem isKappaNoncollapsed_iff_riemannianBallOf (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) (kappa : Real) :
    B.IsKappaNoncollapsed kappa ↔
      0 < kappa ∧ ENNReal.ofReal (kappa * B.radius ^ Module.finrank Real E) ≤
        riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : Real))
          (riemannianBallOf (I := I) (S.base.metric (time : Real)) B.center B.radius) := by
  rw [isKappaNoncollapsed_iff_volumeMeasure, set_eq_riemannianBallOf]

end FlowMetricBall

theorem kappaNoncollapsedBelowScale_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ kappa rho : Real) :
    KappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      KappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

theorem noLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    NoLocalCollapsing (S.timeShift τ) rho ↔ NoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (kappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (kappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

theorem kappaNoncollapsedOnAllScales_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ kappa : Real) :
    KappaNoncollapsedOnAllScales (S.timeShift τ) kappa ↔
      KappaNoncollapsedOnAllScales S kappa := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsRmControlled :=
      (FlowMetricBall.isRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

theorem spatiallyKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    SpatiallyKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      SpatiallyKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsSpatiallyRmControlled :=
      (FlowMetricBall.isSpatiallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B)
        (B' := B') (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsSpatiallyRmControlled :=
      (FlowMetricBall.isSpatiallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B')
        (B' := B) (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

theorem spatialNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    SpatialNoLocalCollapsing (S.timeShift τ) rho ↔ SpatialNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (spatiallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (spatiallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

theorem parabolicallyKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    ParabolicallyKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      ParabolicallyKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsParabolicallyRmControlled :=
      (FlowMetricBall.isParabolicallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B)
        (B' := B') (hcenter := rfl) (hradius := rfl)).2 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B)
      (B' := B') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hB => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    have hB' : B'.IsParabolicallyRmControlled :=
      (FlowMetricBall.isParabolicallyRmControlled_timeShift_iff (S := S) τ (ht := ht) (B := B')
        (B' := B) (hcenter := rfl) (hradius := rfl)).1 hB
    have hk := h.2 t' B' hr hB'
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B')
      (B' := B) (hcenter := rfl) (hradius := rfl) kappa).2 hk

theorem parabolicNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    ParabolicNoLocalCollapsing (S.timeShift τ) rho ↔ ParabolicNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (parabolicallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (parabolicallyKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

theorem stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff
    (S : SolutionOn (I := I) (M := M) D) (τ kappa rho : Real) :
    StronglyScalarKappaNoncollapsedBelowScale (S.timeShift τ) kappa rho ↔
      StronglyScalarKappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · intro h
    refine ⟨h.1, fun t B hr hsc B₂ hc₂ hr₂ => ?_⟩
    let t' : (D.timeShift τ).FlowTime := ⟨(t : Real) - τ, by
      change (t : Real) - τ + τ ∈ D.carrier
      rw [sub_add_cancel]
      exact t.2⟩
    have ht : (t' : Real) + τ = (t : Real) := by dsimp only [t']; ring
    let B' : FlowMetricBall (S.timeShift τ) t' := ⟨B.center, B.radius, B.radius_pos⟩
    let B₂' : FlowMetricBall (S.timeShift τ) t' := ⟨B₂.center, B₂.radius, B₂.radius_pos⟩
    have hsc' : B'.IsScalarControlled :=
      (FlowMetricBall.isScalarControlled_timeShift_iff (S := S) τ (ht := ht) (B := B) (B' := B')
        (hcenter := rfl) (hradius := rfl)).2 hsc
    have hk := h.2 t' B' hr hsc' B₂' hc₂ hr₂
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B₂)
      (B' := B₂') (hcenter := rfl) (hradius := rfl) kappa).1 hk
  · intro h
    refine ⟨h.1, fun t B hr hsc B₂ hc₂ hr₂ => ?_⟩
    let t' : D.FlowTime := ⟨(t : Real) + τ, t.2⟩
    have ht : (t : Real) + τ = (t' : Real) := rfl
    let B' : FlowMetricBall S t' := ⟨B.center, B.radius, B.radius_pos⟩
    let B₂' : FlowMetricBall S t' := ⟨B₂.center, B₂.radius, B₂.radius_pos⟩
    have hsc' : B'.IsScalarControlled :=
      (FlowMetricBall.isScalarControlled_timeShift_iff (S := S) τ (ht := ht) (B := B') (B' := B)
        (hcenter := rfl) (hradius := rfl)).1 hsc
    have hk := h.2 t' B' hr hsc' B₂' hc₂ hr₂
    exact (FlowMetricBall.isKappaNoncollapsed_timeShift_iff (S := S) τ (ht := ht) (B := B₂')
      (B' := B₂) (hcenter := rfl) (hradius := rfl) kappa).2 hk

theorem strongScalarNoLocalCollapsing_timeShift_iff (S : SolutionOn (I := I) (M := M) D)
    (τ rho : Real) :
    StrongScalarNoLocalCollapsing (S.timeShift τ) rho ↔
      StrongScalarNoLocalCollapsing S rho := by
  constructor
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).1 hbelow⟩
  · rintro ⟨kappa, hkappa, hbelow⟩
    exact ⟨kappa, hkappa,
      (stronglyScalarKappaNoncollapsedBelowScale_timeShift_iff (S := S) τ kappa rho).2 hbelow⟩

theorem kappaNoncollapsedBelowScale_of_metric_eqOn (S S' : SolutionOn (I := I) (M := M) D)
    (kappa rho : Real) (h : KappaNoncollapsedBelowScale S kappa rho)
    (hm : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      ∀ s ∈ Set.Icc ((t : Real) - r ^ 2) (t : Real),
        S'.base.metric s = S.base.metric s) :
    KappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hB' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hB : B.IsRmControlled :=
    FlowMetricBall.isRmControlled_of_metric_eqOn (S := S') (S' := S) B' B rfl rfl
      (fun s hs => (hm t B'.radius B'.radius_pos hr s hs).symm) hB'
  have hk := h.2 t B hr hB
  exact FlowMetricBall.isKappaNoncollapsed_of_metric_eq (S := S) (S' := S') B B' rfl rfl
    (hm t B'.radius B'.radius_pos hr (t : Real)
      ⟨by linarith [sq_nonneg B'.radius], le_rfl⟩) kappa hk

theorem spatiallyKappaNoncollapsedBelowScale_of_metric_eqOn
    (S S' : SolutionOn (I := I) (M := M) D)
    (kappa rho : Real) (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho)
    (hm : ∀ (t : D.FlowTime) (r : Real), 0 < r → r ≤ rho →
      S'.base.metric (t : Real) = S.base.metric (t : Real)) :
    SpatiallyKappaNoncollapsedBelowScale S' kappa rho := by
  refine ⟨h.1, fun t B' hr hB' => ?_⟩
  let B : FlowMetricBall S t := ⟨B'.center, B'.radius, B'.radius_pos⟩
  have hB : B.IsSpatiallyRmControlled :=
    FlowMetricBall.isSpatiallyRmControlled_of_metric_eq (S := S') (S' := S) B' B rfl rfl
      (hm t B'.radius B'.radius_pos hr).symm hB'
  have hk := h.2 t B hr hB
  exact FlowMetricBall.isKappaNoncollapsed_of_metric_eq (S := S) (S' := S') B B' rfl rfl
    (hm t B'.radius B'.radius_pos hr) kappa hk

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
