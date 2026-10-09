import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction.FiniteCurvature

/-!
# LFR16, first clause: eventual ballwise curvature bounds are uniform for a modified bound

Blueprint 207A, LFR16 (`lem:collapse-finite-compact-factor`, A:26159–26203) replaces LFR14's
hypothesis `|∇^q Rm| ≤ A(R)` on `B(p i, R)` for ALL `i` by the eventual version: for every `R`
there is `i_R` with the bounds for `i ≥ i_R`. The blueprint re-runs LFR14's proof on tails.

Here is a shorter route that makes LFR14 (and every other consumer of the uniform hypothesis)
applicable verbatim: each member is a complete smooth manifold, so each of the finitely many early
members `i < i_R` has bounded curvature derivatives on the compact closed ball of radius `R`
(Hopf–Rinow, continuity of `curvDerivNorm`). Hence a modified positive bound function `A' ≥ A`
bounds the WHOLE sequence (`exists_uniform_curvature_bound_of_eventual`). LFR14's hypothesis
asks only for some positive bound function, not a monotone one, so no member is changed and no
subsequence is taken.

Consumer: LFR14 step 1's metric limit (`exists_pointed_limit_of_original_finite_curvature_bounds`)
under the eventual hypotheses (`exists_pointed_limit_of_eventual_finite_curvature_bounds`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

namespace GC.MetricGeometry

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- One complete smooth member has bounded curvature derivatives on every ball. -/
theorem exists_curvDerivNorm_bound_on_riemannianBallOf {M : Type*} [MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M) (j : ℕ)
    (R : ℝ) : ∃ C : ℝ, ∀ y ∈ riemannianBallOf g p R, curvDerivNorm j g y ≤ C := by
  have hg : RiemannianMetricComplete (I := I) g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  have hfun : (fun y => curvDerivNorm j g y) = curvatureDerivativeNorm g j :=
    funext fun y => (curvatureDerivativeNorm_eq_curvDerivNorm g j y).symm
  have hcont : Continuous (fun y => curvDerivNorm j g y) := by
    rw [hfun]
    exact continuous_curvatureDerivativeNorm g j
  obtain ⟨C, hC⟩ := (isCompact_riemannianClosedBallOf hg p R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, fun y hy => ?_⟩
  have hy' : y ∈ riemannianClosedBallOf g p R := by
    change riemannianEDistOf g p y < ENNReal.ofReal R at hy
    exact le_of_lt hy
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC y hy')

variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

omit [∀ i, T2Space (TangentBundle I (X i))] in
/-- **LFR16, eventual bounds (kernel).** Eventual ballwise bounds through order `K` on complete
smooth members give a positive bound function `A' ≥ A` valid for every member on every ball. -/
theorem exists_uniform_curvature_bound_of_eventual (K : ℕ)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (A : ℝ → ℝ)
    (hev : ∀ R > 0, ∀ᶠ i in atTop, ∀ j ≤ K,
      ∀ y ∈ riemannianBallOf (g i) (p i) R, curvDerivNorm j (g i) y ≤ A R) :
    ∃ A' : ℝ → ℝ, (∀ R, 0 < A' R) ∧ (∀ R, A R ≤ A' R) ∧ ∀ R > 0, ∀ i, ∀ j ≤ K,
      ∀ y ∈ riemannianBallOf (g i) (p i) R, curvDerivNorm j (g i) y ≤ A' R := by
  classical
  have hC : ∀ i j (R : ℝ), ∃ C : ℝ, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm j (g i) y ≤ C := fun i j R =>
    exists_curvDerivNorm_bound_on_riemannianBallOf (g i) (hmetric i) (p i) j R
  choose C hC using hC
  have hN : ∀ R : ℝ, ∃ N : ℕ, 0 < R → ∀ i, N ≤ i → ∀ j ≤ K,
      ∀ y ∈ riemannianBallOf (g i) (p i) R, curvDerivNorm j (g i) y ≤ A R := by
    intro R
    by_cases hR : 0 < R
    · obtain ⟨N, hN⟩ := eventually_atTop.1 (hev R hR)
      exact ⟨N, fun _ i hi => hN i hi⟩
    · exact ⟨0, fun h => absurd h hR⟩
  choose N hN using hN
  let S : ℝ → ℝ := fun R =>
    ∑ i ∈ Finset.range (N R), ∑ j ∈ Finset.range (K + 1), max (C i j R) 0
  have hS0 : ∀ R, 0 ≤ S R := fun R =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨fun R => max (A R) 0 + 1 + S R, fun R => by positivity, fun R => ?_, ?_⟩
  · linarith [le_max_left (A R) 0, hS0 R]
  intro R hR i j hj y hy
  by_cases hi : N R ≤ i
  · linarith [hN R hR i hi j hj y hy, le_max_left (A R) 0, hS0 R]
  · have hiN : i ∈ Finset.range (N R) := Finset.mem_range.2 (not_le.1 hi)
    have hjK : j ∈ Finset.range (K + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hj)
    have h1 : max (C i j R) 0 ≤ ∑ j' ∈ Finset.range (K + 1), max (C i j' R) 0 :=
      Finset.single_le_sum (f := fun j' => max (C i j' R) 0)
        (fun _ _ => le_max_right _ _) hjK
    have h2 : ∑ j' ∈ Finset.range (K + 1), max (C i j' R) 0 ≤ S R :=
      Finset.single_le_sum (f := fun i' => ∑ j' ∈ Finset.range (K + 1), max (C i' j' R) 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) hiN
    linarith [hC i j R y hy, le_max_left (C i j R) 0, le_max_right (A R) 0]

/-- **Consumer: LFR14 step 1 under LFR16's eventual hypotheses.** The pointed metric limit of the
original sequence exists when the finite-order curvature bounds hold only eventually on each
ball. -/
theorem exists_pointed_limit_of_eventual_finite_curvature_bounds (K : ℕ)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (A : ℝ → ℝ)
    (hev : ∀ R > 0, ∀ᶠ i in atTop, ∀ j ≤ K,
      ∀ y ∈ riemannianBallOf (g i) (p i) R, curvDerivNorm j (g i) y ≤ A R) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ a b : Y, Metric.intrinsicEDist a b = edist a b) ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  obtain ⟨A', -, -, hA'⟩ := exists_uniform_curvature_bound_of_eventual K g hmetric p A hev
  exact exists_pointed_limit_of_original_finite_curvature_bounds K g hmetric p A' hA'

end GC.MetricGeometry
