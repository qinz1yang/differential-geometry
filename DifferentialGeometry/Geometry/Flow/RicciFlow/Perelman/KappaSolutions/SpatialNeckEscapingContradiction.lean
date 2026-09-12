import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardSubsequence

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] [NoncompactSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance escapingNeckC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem exists_scalarBounded_spatialNeck_subsequence
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (W i).core (W j).core))
    (hescape : Tendsto centers atTop (cocompact N)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ n : ℕ,
      metricScalarAt (I := I) h (centers (phi n)) ≤
        144 * metricScalarAt (I := I) h (centers (phi 0)) := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [(W 0).dimension_three]; norm_num⟩
  let _ : CompleteSpace N := completeMetric_compatible_completeSpace h hEnorm (W 0).complete
  choose W' _hchoice _hsphere hcore _himage hside using
    fun i : ℕ => (W i).exists_ordered_compact_end_sides hsec
  let D : ∀ i : ℕ, SpatialNeckSideData (W' i) := fun i => Classical.choice (hside i)
  have hcores' : Pairwise (fun i j : ℕ => Disjoint (W' i).core (W' j).core) := by
    intro i j hij
    simpa only [hcore i, hcore j] using hcores hij
  have hray : ∃ c : ℝ≥0 → N, Isometry c := by
    by_contra! hno
    have hcompact := isCompact_rayBusemannSublevel h hEnorm hsec.toNonnegative
      (centers 0) (k := 0)
    have heq : rayBusemannSublevel (centers 0) 0 = univ := by
      apply eq_univ_of_forall
      intro q c hc _hc0
      exact False.elim (hno c hc)
    rw [heq] at hcompact
    exact noncompact_univ N hcompact
  obtain ⟨c, hc⟩ := hray
  obtain ⟨q, _hvalue, hmin⟩ := (D 0).exists_busemann_minimum hEnorm hsmall hsec.toNonnegative hc
  obtain ⟨phi, hphi, _havoid, hnested⟩ := exists_outward_spatialNeck_subsequence W' D
    hEnorm hsmall hsec.toNonnegative hc q hmin hcores' hescape
  have horder (n : ℕ) :
      closure ((D (phi 0)).lower 0) ⊆ (D (phi (n + 1))).lower 0 := by
    induction n with
    | zero => exact hnested 0
    | succ n ih =>
      intro x hx
      exact hnested (n + 1) (subset_closure (ih hx))
  refine ⟨phi, hphi, ?_⟩
  intro n
  cases n with
  | zero =>
    have hpos := (W (phi 0)).scalar_pos
    linarith
  | succ n =>
    exact (D (phi 0)).outward_scalar_le (D (phi (n + 1))) hEnorm hsmall hsec.toNonnegative
      (hcores' (hphi (Nat.succ_pos n)).ne) (horder n)

theorem not_tendsto_scalar_of_disjoint_escaping_necks
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (W i).core (W j).core))
    (hescape : Tendsto centers atTop (cocompact N)) :
    ¬ Tendsto (fun i => metricScalarAt (I := I) h (centers i)) atTop atTop := by
  obtain ⟨phi, hphi, hbound⟩ :=
    exists_scalarBounded_spatialNeck_subsequence W hEnorm hsmall hsec hcores hescape
  intro hdiverges
  apply (not_bddAbove_of_tendsto_atTop (hdiverges.comp hphi.tendsto_atTop))
  refine ⟨144 * metricScalarAt (I := I) h (centers (phi 0)), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hbound n

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
