import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckEscapingContradiction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricSeparatedSubsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialPointSelection
import DifferentialGeometry.Geometry.Comparison.Soul.SoulRetraction
import DifferentialGeometry.Geometry.Comparison.Splitting.TwoEndsScalarBound
import DifferentialGeometry.Geometry.Curvature.CurvatureRicciContraction
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance highCurvatureNeckC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem not_tendsto_scalar_spatialNeck_centers_of_nonnegative
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h) :
    ¬ Tendsto (fun i => metricScalarAt (I := I) h (centers i)) atTop atTop := by
  classical
  intro hscalar
  have hcont := (metricScalar_smooth (I := I) h).continuous
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [(W 0).dimension_three]; norm_num⟩
  let _ : ProperSpace N := completeMetric_compatible_properSpace h hEnorm (W 0).complete
  let _ : NoncompactSpace N := ⟨by
    intro hcompact
    have hbounded : BddAbove (range (fun q : N => metricScalarAt (I := I) h q)) := by
      simpa only [image_univ] using (hcompact.image hcont).bddAbove
    apply not_bddAbove_of_tendsto_atTop hscalar
    apply hbounded.mono
    rintro _ ⟨i, rfl⟩
    exact ⟨centers i, rfl⟩⟩
  let _ : CompleteSpace N := completeMetric_compatible_completeSpace h hEnorm (W 0).complete
  let _ : LocallyPathConnectedSpace N :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  have hends : ¬ HasAtLeastEnds N 2 := by
    intro htwo
    obtain ⟨C, hC⟩ := exists_metricScalarAt_le_of_nonnegative_ricci_of_two_ends h (W 0).complete
      (fun x v => ricciTensor_nonneg_of_sectionalNonnegative h x (hsec x) v) htwo
    apply not_bddAbove_of_tendsto_atTop hscalar
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC (centers i)⟩
  obtain ⟨S, _hSne, hScompact, _hconv, _hboundary, r, hrange, hr, _hfix⟩ :=
    exists_soul_homotopic_retraction h hEnorm hsec
  have hrad := tendsto_dist_atTop_of_continuous_values_atTop hcont hscalar (centers 0)
  obtain ⟨R, hSR⟩ := hScompact.isBounded.subset_closedBall (centers 0)
  have hevent : ∀ᶠ i in atTop,
      (W i).core ⊆ Metric.ball (centers i) 1 ∧ Disjoint S (W i).core := by
    filter_upwards [eventually_spatialNeck_core_subset_ball W hEnorm hsmall hscalar 1
      (by norm_num), hrad.eventually_gt_atTop (R + 1)] with i hcore hfar
    refine ⟨hcore, Set.disjoint_left.mpr ?_⟩
    intro q hqS hqcore
    have hqR : dist (centers 0) q ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hSR hqS
    have hqi : dist q (centers i) < 1 := hcore hqcore
    have htriangle := dist_triangle (centers 0) q (centers i)
    linarith
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp hevent
  have hshift : Tendsto (fun n : ℕ => i0 + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat i0
  have htail : Tendsto (fun n => dist (centers 0) (centers (i0 + n))) atTop atTop :=
    hrad.comp hshift
  obtain ⟨phi, hphi, hballs⟩ :=
    exists_disjoint_closedBall_subsequence (centers 0) htail 1 (by norm_num)
  let psi : ℕ → ℕ := fun n => i0 + phi n
  have hpsi : StrictMono psi := fun i j hij => Nat.add_lt_add_left (hphi hij) i0
  have hcores (n : ℕ) : (W (psi n)).core ⊆ Metric.closedBall (centers (psi n)) 1 :=
    (hi0 (psi n) (Nat.le_add_right i0 (phi n))).1.trans Metric.ball_subset_closedBall
  have hdisjoint : Pairwise (fun i j : ℕ => Disjoint (W (psi i)).core (W (psi j)).core) := by
    intro i j hij
    exact (hballs hij).mono (hcores i) (hcores j)
  have hescape : Tendsto (fun n => centers (psi n)) atTop (cocompact N) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (centers 0)
    simpa only [Function.comp_def, dist_comm] using hrad.comp hpsi.tendsto_atTop
  have havoid (n : ℕ) : Disjoint (range r) (W (psi n)).centralSphere := by
    rw [hrange]
    exact ((hi0 (psi n) (Nat.le_add_right i0 (phi n))).2).mono_right
      (W (psi n)).centralSphere_subset_core
  choose W' _hchoice _hsphere hcore _himage hside using fun n : ℕ =>
    (W (psi n)).exists_ordered_compact_end_sides_of_homotopic_disjoint r hr (havoid n) hends
  let D : ∀ n : ℕ, SpatialNeckSideData (W' n) := fun n => Classical.choice (hside n)
  have hcores' : Pairwise (fun i j : ℕ => Disjoint (W' i).core (W' j).core) := by
    intro i j hij
    simpa only [hcore i, hcore j] using hdisjoint hij
  obtain ⟨theta, htheta, hbound⟩ :=
    SpatialNeckSideData.exists_scalar_bounded_subsequence W' D hEnorm hsmall hsec hcores' hescape
  apply not_bddAbove_of_tendsto_atTop
    (hscalar.comp (hpsi.comp htheta).tendsto_atTop)
  refine ⟨144 * metricScalarAt (I := I) h (centers (psi (theta 0))), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hbound n

theorem not_tendsto_scalar_spatialNeck_centers
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ¬ Tendsto (fun i => metricScalarAt (I := I) h (centers i)) atTop atTop := by
  exact not_tendsto_scalar_spatialNeck_centers_of_nonnegative W hEnorm hsmall hsec.toNonnegative

theorem bddAbove_scalar_spatialNeck_centers_of_nonnegative
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h) :
    BddAbove (range (fun i => metricScalarAt (I := I) h (centers i))) := by
  classical
  by_contra hunbounded
  have hlarge (n : ℕ) : ∃ i : ℕ, (n : ℝ) < metricScalarAt (I := I) h (centers i) := by
    obtain ⟨a, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hunbounded (n : ℝ)
    exact ⟨i, hi⟩
  choose idx hidx using hlarge
  have hdiverges : Tendsto (fun n => metricScalarAt (I := I) h (centers (idx n))) atTop atTop :=
    tendsto_atTop_mono (fun n => (hidx n).le) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact not_tendsto_scalar_spatialNeck_centers_of_nonnegative
    (fun n => W (idx n)) hEnorm hsmall hsec hdiverges


theorem bddAbove_scalar_spatialNeck_centers
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    BddAbove (range (fun i => metricScalarAt (I := I) h (centers i))) := by
  exact bddAbove_scalar_spatialNeck_centers_of_nonnegative W hEnorm hsmall hsec.toNonnegative

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
