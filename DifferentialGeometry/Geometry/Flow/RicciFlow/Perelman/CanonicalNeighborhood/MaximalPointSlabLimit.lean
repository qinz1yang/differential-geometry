import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientCanonicalNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

noncomputable def PointedRiemannianConvergenceMaps.atTimeSlice
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) D} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) 0)
      (L.atTime (I := I) 0) phi) (t : ℝ) :
    PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) t)
      (L.atTime (I := I) t) phi :=
  { partialDiffeomorph := F.partialDiffeomorph
    source_exhausts := F.source_exhausts
    base_mem := F.base_mem
    basepoint_map := F.basepoint_map }

omit [I.Boundaryless] in
@[simp] theorem PointedRiemannianConvergenceMaps.atTimeSlice_source
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) D} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I) (X.atTime (I := I) 0)
      (L.atTime (I := I) 0) phi) (t : ℝ) (k : ℕ) :
    (F.atTimeSlice (I := I) t).source k = F.source k :=
  rfl

omit [I.Boundaryless] in
theorem eventually_subset_source_of_metricSourceConvergesOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (I := I) X L phi}
    {Dm : ∀ k : ℕ, MetricSourceData (I := I) F k} {K : Set L.M} {p : ℕ}
    (h : metricSourceConvergesOn (I := I) F Dm K p) :
    ∀ᶠ k : ℕ in Filter.atTop, K ⊆ F.source k := by
  obtain ⟨k0, hk0⟩ := h 1 zero_lt_one
  exact Filter.eventually_atTop.2 ⟨k0, fun k hk => (hk0 k hk).1⟩

theorem ExhaustsByOpen.univ (M : Type u) [TopologicalSpace M] :
    ExhaustsByOpen (fun _ : ℕ => (Set.univ : Set M)) where
  isOpen := fun _ => isOpen_univ
  mono_step := fun _ => Set.subset_univ _
  subset := fun _K _ => ⟨0, fun _ _ => Set.subset_univ _⟩

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

section Capture

variable {X : PointedRiemannianSeq.{u, 0, 0} (I := I3)}
variable {Lp : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}

theorem metricSourceCapture_of_metricComparisonOn
    (F : PointedRiemannianConvergenceMaps (I := I3) X Lp phi)
    (hcomplete : RiemannianMetricComplete (I := I3) Lp.metric)
    (h : ℝ → SmoothRiemannianMetric I3 Lp.M) (hzero : h 0 = Lp.metric)
    (g : ∀ i : ℕ, ℝ → SmoothRiemannianMetric I3 (X.obj (phi i)).M)
    (gzero : ∀ i : ℕ, g i 0 = (X.obj (phi i)).metric)
    (hcmp : ∀ K : Set Lp.M, IsCompact K → ∀ A : ℝ, 0 < A →
      ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
        K ⊆ (F.partialDiffeomorph i).source ∧
        Nonempty (MetricComparisonOn h (g i) (F.partialDiffeomorph i) K
          (Set.Icc (-A) 0) order eta)) :
    MetricSourceCapture F := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  intro r hr
  set R : ℝ := 2 * r + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hK : IsCompact (riemannianClosedBallOf (I := I3) (h 0) Lp.basepoint R) := by
    rw [hzero]
    exact RiemannianMetricComplete.closedEBall_isCompact (I := I3) hcomplete Lp.basepoint R
  have hev := hcmp (riemannianClosedBallOf (I := I3) (h 0) Lp.basepoint R) hK 1
    (by norm_num) 0 (1 / 2) (by norm_num)
  filter_upwards [hev] with i hi
  obtain ⟨hsrc, ⟨C⟩⟩ := hi
  have hlower : ∀ y ∈ riemannianClosedBallOf (I := I3) (h 0) Lp.basepoint R,
      ∀ v : TangentSpace I3 y,
        (h 0).inner y v v ≤ Real.sqrt 2 ^ 2 *
          (g i 0).inner (F.partialDiffeomorph i y)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v) := by
    intro y hy v
    have hh := (C.equivalence 0 ⟨by norm_num, le_rfl⟩ y hy v).1
    rw [C.pullback_eq 0 y hy (fun _ => v)] at hh
    have hh' : (1 - 1 / 2) * (h 0).inner y v v ≤
        (g i 0).inner (F.partialDiffeomorph i y)
          (mfderiv I3 I3 (F.partialDiffeomorph i) y v)
          (mfderiv I3 I3 (F.partialDiffeomorph i) y v) := hh
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hcap := ball_subset_image_of_metric_lower_crossModel (h 0) (g i 0)
    (F.partialDiffeomorph i) Lp.basepoint hR hsqrt hK hsrc hlower
  have hr' : r ≤ R / Real.sqrt 2 := by
    rw [le_div_iff₀ hsqrt, hRdef]
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    nlinarith [hr.le, h2]
  intro y hy
  have hy' : y ∈ riemannianBallOf (I := I3) (g i 0)
      (F.partialDiffeomorph i Lp.basepoint) (R / Real.sqrt 2) := by
    rw [gzero i, F.basepoint_map i]
    exact riemannianBallOf_mono _ _ hr' hy
  obtain ⟨z, hz, hzy⟩ := hcap hy'
  exact ⟨z, hsrc hz, hzy⟩

end Capture

noncomputable def pointedRiemannianConvergenceMapsSelf
    (P : PointedRiemannianManifold.{u, 0, 0} (I := I3)) :
    PointedRiemannianConvergenceMaps (I := I3)
      (⟨fun _ : ℕ => P⟩ : PointedRiemannianSeq.{u, 0, 0} (I := I3)) P id where
  partialDiffeomorph _ := PartialDiffeomorph.refl (I := I3) P.M
  source_exhausts := by
    have hfun : (fun _ : ℕ => (PartialDiffeomorph.refl (I := I3) P.M).source) =
        (fun _ : ℕ => (Set.univ : Set P.M)) := by
      funext _
      rfl
    rw [hfun]
    exact ExhaustsByOpen.univ P.M
  base_mem _ := Set.mem_univ _
  basepoint_map _ := rfl

theorem metricSourceCapture_self (P : PointedRiemannianManifold.{u, 0, 0} (I := I3))
    (hcomplete : RiemannianMetricComplete (I := I3) P.metric) :
    MetricSourceCapture (pointedRiemannianConvergenceMapsSelf P) := by
  refine metricSourceCapture_of_metricComparisonOn (pointedRiemannianConvergenceMapsSelf P)
    hcomplete (fun _ => P.metric) rfl (fun _ _ => P.metric) (fun _ => rfl) ?_
  intro K _ A hA order eta heta
  filter_upwards with i
  exact ⟨Set.subset_univ K,
    ⟨metricComparisonOnRefl (fun _ => P.metric) K (Set.Icc (-A) 0) order heta⟩⟩

theorem orientedConvergenceMaps_self (P : PointedRiemannianManifold.{u, 0, 0} (I := I3))
    (o : TangentOrientationSection P.M) :
    ∃ ori : TangentOrientationSection P.M, ∀ i y, y ∈
        ((pointedRiemannianConvergenceMapsSelf P).partialDiffeomorph i).source →
      ∃ hf : Function.Bijective (mfderiv I3 I3
          ((pointedRiemannianConvergenceMapsSelf P).partialDiffeomorph i) y),
        PreservesTangentOrientationAt ori o
          ((pointedRiemannianConvergenceMapsSelf P).partialDiffeomorph i) y hf := by
  refine ⟨o, fun i y _ => ⟨?_, ?_⟩⟩
  · have hd : mfderiv I3 I3 ((PartialDiffeomorph.refl (I := I3) P.M) : P.M → P.M) y =
        ContinuousLinearMap.id ℝ (TangentSpace I3 y) := mfderiv_id
    change Function.Bijective
      (mfderiv I3 I3 ((PartialDiffeomorph.refl (I := I3) P.M) : P.M → P.M) y)
    rw [hd]
    exact Function.bijective_id
  · exact preservesTangentOrientationAt_refl o y _

theorem slabSourceBallCapture_of_canonicalMetricComparison {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
    (F : PointedRiemannianConvergenceMaps (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
      (L.atTime (I := I3) 0) phi)
    (hcomplete : RiemannianMetricComplete (I := I3) (L.S.base.metric 0))
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A →
      ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
        K ⊆ (F.partialDiffeomorph i).source ∧
        Nonempty (MetricComparisonOn (fun s => L.S.base.metric s)
          (fun s => ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term
            (phi i)).S.base.metric s)
          (F.partialDiffeomorph i) K (Set.Icc (-A) 0) order eta)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
      riemannianBallOf (I := I3)
          (rescaledMetric S (t (phi i)) (S.scalar (t (phi i)) (x (phi i)))
            (hpos (phi i)) 0) (x (phi i)) r ⊆
        (fun a => F.partialDiffeomorph i a) '' (F.partialDiffeomorph i).source := by
  have hmain : MetricSourceCapture F :=
    metricSourceCapture_of_metricComparisonOn
      (X := (highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
      (Lp := L.atTime (I := I3) 0) F hcomplete (fun s => L.S.base.metric s) rfl
      (fun i s => ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term
        (phi i)).S.base.metric s) (fun _ => rfl) hcmp
  intro r hr
  filter_upwards [hmain r hr] with i hi
  exact hi

def MaximalPointSlabLimitSelection {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (kappa : ℝ) : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      (∀ i, theta ≤ t i) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
        S.scalar s y ≤ S.scalar (t i) (x i)) →
      ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
        (F : PointedRiemannianConvergenceMaps (I := I3)
          ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
          (L.atTime (I := I3) 0) phi),
        StrictMono phi ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        (∀ t' : ℝ, t' ≤ 0 →
          ∃ Ft : PointedRiemannianConvergenceMaps (I := I3)
            ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime t')
            (L.atTime (I := I3) t') phi,
            ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) Ft
              (CanonicalMetricCompactness.canonicalSourceData (I := I3) Ft) K 2) ∧
        (∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A →
          ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
            K ⊆ (F.partialDiffeomorph i).source ∧
            Nonempty (MetricComparisonOn (fun s => L.S.base.metric s)
              (fun s =>
                ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term
                  (phi i)).S.base.metric s)
              (F.partialDiffeomorph i) K (Set.Icc (-A) 0) order eta)) ∧
        (∃ ori : TangentOrientationSection L.M, ∀ i y,
          y ∈ (F.partialDiffeomorph i).source →
          ∃ hf : Function.Bijective (mfderiv I3 I3 (F.partialDiffeomorph i) y),
            PreservesTangentOrientationAt ori o (F.partialDiffeomorph i) y hf)

theorem maximalPointSlabLimitSelection_of_maximalPointSlabCompactnessAtPastMaximum {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ MaximalPointSlabLimitSelection.{u} hT S hS o kappa := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  refine ⟨kappa, hkpos, fun theta htheta x t htpos htmem0 hpos htlower hscalar hmax => ?_⟩
  obtain ⟨L, phi, F, hphi, hanc, _hbase, hconvT, hcmp, _hcap, ori, hor⟩ :=
    hmain theta htheta x t htpos htmem0 hpos htlower hscalar hmax
  exact ⟨L, phi, F, hphi, hanc, hconvT, hcmp, ori, hor⟩

theorem maximalPointSlabCompactnessAtPastMaximum_of_maximalPointSlabLimitSelection {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) {kappa : ℝ} (hkappa : 0 < kappa)
    (h : MaximalPointSlabLimitSelection.{u} hT S hS o kappa) :
    MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o := by
  refine ⟨kappa, hkappa, fun theta htheta x t htpos htmem0 hpos htlower hscalar hmax => ?_⟩
  obtain ⟨L, phi, F, hphi, hanc, hconvT, hcmp, ori, hor⟩ :=
    h theta htheta x t htpos htmem0 hpos htlower hscalar hmax
  obtain ⟨F0, hF0⟩ := hconvT 0 le_rfl
  have hbase : PointedFlowScalarAtBase (I := I3) L 1 :=
    pointedFlowScalarAtBase_of_metricConvergence_at_zero hT S hS x t htmem0 htpos hpos L phi F0 hF0
  have hzero_mem : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr le_rfl
  have hcomplete : RiemannianMetricComplete (I := I3) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete _ (hanc.complete 0 hzero_mem)⟩
  have hcap := slabSourceBallCapture_of_canonicalMetricComparison hT S hS x t htmem0 htpos hpos
    L phi F hcomplete hcmp
  exact ⟨L, phi, F, hphi, hanc, hbase, hconvT, hcmp, hcap, ori, hor⟩

theorem maximalPointSlabCompactnessAtPastMaximum_iff_exists_maximalPointSlabLimitSelection
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o ↔
      ∃ kappa : ℝ, 0 < kappa ∧ MaximalPointSlabLimitSelection.{u} hT S hS o kappa := by
  constructor
  · exact maximalPointSlabLimitSelection_of_maximalPointSlabCompactnessAtPastMaximum hT S hS o
  · rintro ⟨kappa, hkpos, h⟩
    exact maximalPointSlabCompactnessAtPastMaximum_of_maximalPointSlabLimitSelection hT S hS o
      hkpos h

theorem maximalPointSlabLimitSelection_of_forall_scalar_eq_zero {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) {kappa : ℝ}
    (hscalar : ∀ (t : ℝ) (x : M), S.scalar t x = 0) :
    MaximalPointSlabLimitSelection.{u} hT S hS o kappa := by
  intro theta htheta x t htpos htmem0 hpos
  exact absurd (hpos 0) (by rw [hscalar (t 0) (x 0)]; exact lt_irrefl 0)

theorem maximalPointSlabCompactnessAtPastMaximum_of_forall_scalar_eq_zero {T : ℝ}
    (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (hscalar : ∀ (t : ℝ) (x : M), S.scalar t x = 0) :
    MaximalPointSlabCompactnessAtPastMaximum.{u} hT S hS o :=
  maximalPointSlabCompactnessAtPastMaximum_of_maximalPointSlabLimitSelection hT S hS o
    one_pos (maximalPointSlabLimitSelection_of_forall_scalar_eq_zero hT S hS o hscalar)

theorem maximalPointSlabLimitSelection_euclidean {T : ℝ} (hT : 0 < T)
    (o : TangentOrientationSection ThreeSpace) {kappa : ℝ} :
    MaximalPointSlabLimitSelection (M := ThreeSpace) hT
      (SolutionOn.const (euclideanMetric (E := ThreeSpace))
        (RealTimeInterval.closedOpen 0 T hT))
      (isSolutionOn_const_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace))
        (fun x v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)
        (RealTimeInterval.closedOpen 0 T hT)) o kappa := by
  refine maximalPointSlabLimitSelection_of_forall_scalar_eq_zero hT _ _ o ?_
  intro t x
  simp only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.const_metric]
  exact metricScalarAt_eq_zero_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace)) x
    (fun v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)

theorem maximalPointSlabCompactnessAtPastMaximum_euclidean {T : ℝ} (hT : 0 < T)
    (o : TangentOrientationSection ThreeSpace) :
    MaximalPointSlabCompactnessAtPastMaximum (M := ThreeSpace) hT
      (SolutionOn.const (euclideanMetric (E := ThreeSpace))
        (RealTimeInterval.closedOpen 0 T hT))
      (isSolutionOn_const_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace))
        (fun x v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)
        (RealTimeInterval.closedOpen 0 T hT)) o := by
  refine maximalPointSlabCompactnessAtPastMaximum_of_forall_scalar_eq_zero hT _ _ o ?_
  intro t x
  simp only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.const_metric]
  exact metricScalarAt_eq_zero_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace)) x
    (fun v w => DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
