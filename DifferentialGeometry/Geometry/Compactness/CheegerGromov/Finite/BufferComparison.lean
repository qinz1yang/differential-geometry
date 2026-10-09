import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing

/-!
# Fixed-tolerance comparison on a compact buffer (LFR14 data, LFR20 last paragraph)

Blueprint LFR20 (master207A:26404–26406, proof step 5 at A:26516–26525): "the model embedding can
additionally meet any prescribed positive finite-buffer `C^{K-1}` metric and pointed-distance
comparison tolerance". The finite Cheeger–Gromov limits of the tree (LFR14/LFR16) deliver the
metric convergence chart by chart: for every chart centre `x` of the limit `N` and every compact
`L' ⊆ (extChartAt x).target`, `MapCPConvergenceOn L' m` of the pulled-back coefficients
`pullbackMetricCoefficients gᵢ (jᵢ ∘ (extChartAt x)⁻¹)` to `chartCoeff G x`. This file turns that
predicate, at a FIXED tolerance `ε`, into one tail on a compact buffer:

* `exists_finite_chart_patches`: a compact set `B` of a boundaryless finite-dimensional charted
  space is covered by the interiors of finitely many compact chart patches `L x ⊆ target`;
* `eventually_buffer_chart_comparison`: with the exhaustion and chart convergence of LFR14, for
  every compact `B` and `ε > 0` there is such a finite family (chosen before the tail) and one tail
  on which `B` and all the patches lie in the sources and every coefficient difference of order
  `≤ m` is at most `ε` on every patch;
* `eventually_abs_dist_sub_lt_of_isBounded`: the pointed distance comparison on a bounded buffer.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing

section Patches

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- **A finite atlas of compact chart patches over a compact set.** -/
theorem exists_finite_chart_patches {B : Set N} (hB : IsCompact B) :
    ∃ (S : Finset N) (L : N → Set E),
      (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt I x).target) ∧
      ∀ x ∈ B, ∃ x' ∈ S, x ∈ (extChartAt I x').source ∧
        extChartAt I x' x ∈ interior (L x') := by
  have hr : ∀ x : N, ∃ r > 0, closedBall (extChartAt I x x) r ⊆ (extChartAt I x).target := by
    intro x
    obtain ⟨r, hr, hsub⟩ :=
      Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x) _ (mem_extChartAt_target x)
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hsub⟩
  choose r hr hsub using hr
  let U : N → Set N := fun x =>
    (extChartAt I x).source ∩ extChartAt I x ⁻¹' ball (extChartAt I x x) (r x)
  have hU : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_preimage' x isOpen_ball
  have hxU : ∀ x, x ∈ U x := fun x => ⟨mem_extChartAt_source x, mem_ball_self (hr x)⟩
  obtain ⟨S, hS⟩ := hB.elim_finite_subcover U hU (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨S, fun x => closedBall (extChartAt I x x) (r x),
    fun x _ => ⟨isCompact_closedBall _ _, hsub x⟩, fun x hx => ?_⟩
  obtain ⟨x', hx'S, hxU'⟩ := mem_iUnion₂.mp (hS hx)
  refine ⟨x', hx'S, hxU'.1, ?_⟩
  have hball : ball (extChartAt I x' x') (r x') ⊆ interior (closedBall (extChartAt I x' x') (r x')) :=
    interior_maximal ball_subset_closedBall isOpen_ball
  exact hball hxU'.2

end Patches

section Eventual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)]

/-- **LFR14's chart convergence at a fixed tolerance on a compact buffer.** The finite family of
patches depends only on `N` and `B`; the tail is chosen after it. -/
theorem eventually_buffer_chart_comparison (g : ∀ i, SmoothRiemannianMetric I (X i)) {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) {K : ℕ}
    (j : ∀ i, PartialDiffeomorph I I N (X i) K) {m : ℕ}
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L' : Set E), IsCompact L' → L' ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L' m
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {B : Set N} (hB : IsCompact B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset N) (L : N → Set E),
      (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt I x).target) ∧
      (∀ x ∈ B, ∃ x' ∈ S, x ∈ (extChartAt I x').source ∧
        extChartAt I x' x ∈ interior (L x')) ∧
      ∀ᶠ i in atTop, B ⊆ (j i).source ∧ ∀ x ∈ S,
        (extChartAt I x).symm '' L x ⊆ (j i).source ∧
        ∀ k ≤ m, ∀ y ∈ L x, mapDerivNorm k
          (pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ (extChartAt I x).symm))
          (chartCoeff G x) y ≤ ε := by
  obtain ⟨S, L, hL, hcov⟩ := exists_finite_chart_patches (I := I) hB
  refine ⟨S, L, hL, hcov, (hexh B hB).and ((S.eventually_all).mpr fun x hx => ?_)⟩
  have himg : IsCompact ((extChartAt I x).symm '' L x) :=
    (hL x hx).1.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono (hL x hx).2)
  obtain ⟨k₀, hk₀⟩ := hconv x (L x) (hL x hx).1 (hL x hx).2 ε hε
  filter_upwards [hexh _ himg, eventually_ge_atTop k₀] with i hi hik
  exact ⟨hi, fun k hk y hy => hk₀ i hik k hk y hy⟩

end Eventual

/-- **Pointed distance comparison on a bounded buffer.** -/
theorem eventually_abs_dist_sub_lt_of_isBounded {N : Type*} [PseudoMetricSpace N]
    {X : ℕ → Type*} [∀ i, PseudoMetricSpace (X i)] (f : ∀ i, N → X i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (f i x) (f i y) - dist x y| < ε)
    {B : Set N} (hB : Bornology.IsBounded B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ B, ∀ y ∈ B, |dist (f i x) (f i y) - dist x y| < ε := by
  obtain ⟨R, hR⟩ := hB.subset_ball q
  filter_upwards [hdist R ε hε] with i hi x hx y hy
  exact hi x (hR hx) y (hR hy)

end DifferentialGeometry.CheegerGromovCompactness
