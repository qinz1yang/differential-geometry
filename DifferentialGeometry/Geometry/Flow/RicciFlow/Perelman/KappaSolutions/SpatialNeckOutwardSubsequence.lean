import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannProper
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
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
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance outwardSubsequenceC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem exists_outward_spatialNeck_subsequence
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (D : ∀ i : ℕ, SpatialNeckSideData (W i))
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) (q : N)
    (hmin : ∀ x : N, busemann c q ≤ busemann c x)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (W i).core (W j).core))
    (hescape : Tendsto centers atTop (cocompact N)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ n : ℕ, q ∉ (W (phi n)).core) ∧
      ∀ n : ℕ, closure ((D (phi n)).lower 0) ⊆ (D (phi (n + 1))).lower 0 := by
  classical
  let good : ℕ → Prop := fun i => q ∉ (W i).core
  have hgood : ∀ᶠ i in atTop, good i := by
    by_cases hex : ∃ i : ℕ, q ∈ (W i).core
    · obtain ⟨i, hi⟩ := hex
      filter_upwards [eventually_gt_atTop i] with j hij
      exact fun hj => Set.disjoint_left.mp (hcores (ne_of_lt hij)) hi hj
    · exact Eventually.of_forall (fun i hi => hex ⟨i, hi⟩)
  have hepsilon := (W 0).epsilon_pos
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by rw [abs_zero]; positivity
  have hstep (i : {i : ℕ // good i}) :
      ∃ j : {j : ℕ // good j}, i.val < j.val ∧
        closure ((D i.val).lower 0) ⊆ (D j.val).lower 0 := by
    have hKi : IsCompact (closure ((D i.val).lower 0)) :=
      ((D i.val).slice_spec 0 hzero).2.2.2.2.2.2.1
    have hex : ∀ᶠ j in atTop, i.val < j ∧ centers j ∉ closure ((D i.val).lower 0) ∧ good j := by
      filter_upwards [eventually_gt_atTop i.val, hescape.eventually hKi.compl_mem_cocompact,
        hgood] with j hj havoid hgoodj
      exact ⟨hj, havoid, hgoodj⟩
    obtain ⟨j, hij, havoid, hgoodj⟩ := hex.exists
    have hqi : q ∈ (D i.val).lower 0 :=
      (D i.val).minimum_mem_lower_zero hEnorm hsmall hsec hc hmin i.property
    have hqj : q ∈ (D j).lower 0 :=
      (D j).minimum_mem_lower_zero hEnorm hsmall hsec hc hmin hgoodj
    have hnested := (D i.val).compact_sides_nested (D j)
      (hcores (ne_of_lt hij)) ⟨q, hqi, hqj⟩
    refine ⟨⟨j, hgoodj⟩, hij, ?_⟩
    rcases hnested with hout | hin
    · exact hout
    · have hpj : centers j ∈ closure ((D j).lower 0) := by
        rw [((D j).slice_spec 0 hzero).2.2.2.2.2.2.2.2.1]
        exact Or.inr (W j).marked_mem_centralSphere
      exact False.elim (havoid (subset_closure (hin hpj)))
  obtain ⟨i0, hi0⟩ := hgood.exists
  let next : {i : ℕ // good i} → {i : ℕ // good i} := fun i => Classical.choose (hstep i)
  have hnext (i : {i : ℕ // good i}) : i.val < (next i).val ∧
      closure ((D i.val).lower 0) ⊆ (D (next i).val).lower 0 := Classical.choose_spec (hstep i)
  let seq : ℕ → {i : ℕ // good i} := fun n => (next^[n]) ⟨i0, hi0⟩
  have hsucc (n : ℕ) : seq (n + 1) = next (seq n) :=
    Function.iterate_succ_apply' next n ⟨i0, hi0⟩
  let phi : ℕ → ℕ := fun n => (seq n).val
  have hmono : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    change (seq n).val < (seq (n + 1)).val
    rw [hsucc]
    exact (hnext (seq n)).1
  refine ⟨phi, hmono, fun n => (seq n).property, ?_⟩
  intro n
  change closure ((D (seq n).val).lower 0) ⊆ (D (seq (n + 1)).val).lower 0
  rw [hsucc]
  exact (hnext (seq n)).2

theorem eventually_mem_spatialNeck_lower
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (D : ∀ i : ℕ, SpatialNeckSideData (W i))
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) (q : N)
    (havoid : ∀ᶠ i in atTop, q ∉ (W i).core)
    (hescape : Tendsto centers atTop (cocompact N)) :
    ∀ᶠ i in atTop, q ∈ (D i).lower 0 := by
  have hK : IsCompact {x : N | busemann c x ≤ busemann c q} :=
    (D 0).busemann_sublevel_isCompact hEnorm hsmall hsec hc _
  filter_upwards [hescape.eventually hK.compl_mem_cocompact, havoid] with i hi hnot
  exact (D i).mem_lower_zero_of_busemann_le hEnorm hsmall hsec hc
    (not_le.mp hi).le hnot

theorem eventually_mem_spatialNeck_lower_of_pairwise_disjoint
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (D : ∀ i : ℕ, SpatialNeckSideData (W i))
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) (q : N)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (W i).core (W j).core))
    (hescape : Tendsto centers atTop (cocompact N)) :
    ∀ᶠ i in atTop, q ∈ (D i).lower 0 := by
  apply eventually_mem_spatialNeck_lower W D hEnorm hsmall hsec hc q _ hescape
  by_cases hex : ∃ i : ℕ, q ∈ (W i).core
  · obtain ⟨i, hi⟩ := hex
    filter_upwards [eventually_gt_atTop i] with j hij
    exact fun hj => Set.disjoint_left.mp (hcores (ne_of_lt hij)) hi hj
  · exact Eventually.of_forall (fun i hi => hex ⟨i, hi⟩)

theorem exists_outward_spatialNeck_exhaustion
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (D : ∀ i : ℕ, SpatialNeckSideData (W i))
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c)
    (hcores : Pairwise (fun i j : ℕ => Disjoint (W i).core (W j).core))
    (hescape : Tendsto centers atTop (cocompact N)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ n : ℕ, closure ((D (phi n)).lower 0) ⊆ (D (phi (n + 1))).lower 0) ∧
      ∀ K : Set N, IsCompact K → ∀ᶠ n in atTop, K ⊆ (D (phi n)).lower 0 := by
  obtain ⟨q, _, hmin⟩ := (D 0).exists_busemann_minimum hEnorm hsmall hsec hc
  obtain ⟨phi, hphi, _, hnested⟩ :=
    exists_outward_spatialNeck_subsequence W D hEnorm hsmall hsec hc q hmin hcores hescape
  refine ⟨phi, hphi, hnested, ?_⟩
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    rw [abs_zero]
    have hepsilon := (W 0).epsilon_pos
    positivity
  have hmono : Monotone (fun n => (D (phi n)).lower 0) := by
    apply monotone_nat_of_le_succ
    intro n
    exact subset_closure.trans (hnested n)
  intro K hK
  have hcover : K ⊆ ⋃ n, (D (phi n)).lower 0 := by
    intro x _
    have hevent := hphi.tendsto_atTop.eventually
      (eventually_mem_spatialNeck_lower_of_pairwise_disjoint
        W D hEnorm hsmall hsec hc x hcores hescape)
    obtain ⟨n, hn⟩ := hevent.exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (D (phi n)).lower 0)
    (fun n => ((D (phi n)).slice_spec 0 hzero).2.2.1) hcover hmono.directed_le
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hn.trans (hmono hm)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
