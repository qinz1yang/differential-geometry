import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckNesting
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology NNReal

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
    (hsec : Poincare.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
