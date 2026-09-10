import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckEscapingContradiction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricSeparatedSubsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialPointSelection

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

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

theorem not_tendsto_scalar_spatialNeck_centers
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ¬ Tendsto (fun i => metricScalarAt (I := I) h (centers i)) atTop atTop := by
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
  have hrad := tendsto_dist_atTop_of_continuous_values_atTop hcont hscalar (centers 0)
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    (eventually_spatialNeck_core_subset_ball W hEnorm hsmall hscalar 1 (by norm_num))
  have hshift : Tendsto (fun n : ℕ => i0 + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat i0
  have htail : Tendsto (fun n => dist (centers 0) (centers (i0 + n))) atTop atTop := hrad.comp hshift
  obtain ⟨phi, hphi, hballs⟩ := exists_disjoint_closedBall_subsequence (centers 0) htail 1 (by norm_num)
  let psi : ℕ → ℕ := fun n => i0 + phi n
  have hpsi : StrictMono psi := fun i j hij => Nat.add_lt_add_left (hphi hij) i0
  have hcores (n : ℕ) : (W (psi n)).core ⊆ Metric.closedBall (centers (psi n)) 1 :=
    (hi0 (psi n) (Nat.le_add_right i0 (phi n))).trans Metric.ball_subset_closedBall
  have hdisjoint : Pairwise (fun i j : ℕ => Disjoint (W (psi i)).core (W (psi j)).core) := by
    intro i j hij
    exact (hballs hij).mono (hcores i) (hcores j)
  have hescape : Tendsto (fun n => centers (psi n)) atTop (cocompact N) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (centers 0)
    simpa only [Function.comp_def, dist_comm] using hrad.comp hpsi.tendsto_atTop
  exact not_tendsto_scalar_of_disjoint_escaping_necks (fun n => W (psi n))
    hEnorm hsmall hsec hdisjoint hescape (hscalar.comp hpsi.tendsto_atTop)

theorem bddAbove_scalar_spatialNeck_centers
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    BddAbove (range (fun i => metricScalarAt (I := I) h (centers i))) := by
  classical
  by_contra hunbounded
  have hlarge (n : ℕ) : ∃ i : ℕ, (n : ℝ) < metricScalarAt (I := I) h (centers i) := by
    obtain ⟨a, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hunbounded (n : ℝ)
    exact ⟨i, hi⟩
  choose idx hidx using hlarge
  have hdiverges : Tendsto (fun n => metricScalarAt (I := I) h (centers (idx n))) atTop atTop :=
    tendsto_atTop_mono (fun n => (hidx n).le) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact not_tendsto_scalar_spatialNeck_centers (fun n => W (idx n)) hEnorm hsmall hsec hdiverges

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
