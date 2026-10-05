import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.SigmaCompact
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPointApproximants

/-!
A single smooth approximation sequence and a single increasing subsequence control curvature
on a fixed compact buffer inside the original local curvature ball. The buffer is chosen
before the common tail, and the chart convergence and global metric bounds retain that sequence.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.FiniteComparison

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [groupE : NormedAddCommGroup E] [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E] [rankE : NeZero (Module.finrank ℝ E)]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [sigmaM : SigmaCompactSpace M] [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M] {n : ℕ∞ω}

theorem exists_buffered_local_hinge_approximants
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) {A R : ℝ} (hA : 0 < A) (hR : 2 * A < R)
    (hsec : ∀ y ∈ Metric.ball o R, ∀ v w : TangentSpace I y,
      0 ≤ g.sectionalCurvature y v w) :
    ∃ ρ : ℝ, ∃ gSeq : ℕ → SmoothRiemannianMetric I M, ∃ φ : ℕ → ℕ,
      0 < ρ ∧ 2 * A < ρ ∧ ρ < R ∧ StrictMono φ ∧ (∀ j, 2 ≤ φ j) ∧
      (∀ (k : ℕ) (x : M) (w : TangentSpace I x),
        (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
          (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w) ∧
      (∀ (q : M) (L : Set E), IsCompact L → L ⊆ (extChartAt I q).target →
        MapCPConvergenceOn L 2 (fun k => chartCoeff (gSeq k) q) (chartCoeff g q)) ∧
      ∀ j, ∀ y ∈ Metric.closedBall o ρ,
        SectionalBoundedBelowAt (gSeq (φ j)) y (-1 / ((j : ℝ) + 1)) := by
  obtain ⟨ρ, hρA, hρR⟩ := exists_between hR
  have hρ : 0 < ρ := lt_trans (by linarith) hρA
  obtain ⟨gSeq, hbil, hconv⟩ := exists_smooth_approximants_sigmaCompact_chart g hn
  have hlow (x : M) (w : TangentSpace I x) :
      (1 - 1 / ((0 : ℕ) + 2 : ℝ)) ^ 2 * g.inner x w w ≤ (gSeq 0).inner x w w :=
    (hbil 0 x w).1
  have hup (x : M) (w : TangentSpace I x) :
      (gSeq 0).inner x w w ≤ (1 + 1 / ((0 : ℕ) + 2 : ℝ)) ^ 2 * g.inner x w w :=
    (hbil 0 x w).2
  have properM : ProperSpace M :=
    properSpace_of_bilipschitz_smooth g hnorm (gSeq 0)
      (by norm_num) (by norm_num) hlow hup
  have hcompact : IsCompact (Metric.closedBall o ρ) := isCompact_closedBall o ρ
  have hsecC : ∀ y ∈ Metric.closedBall o ρ, ∀ v w : TangentSpace I y,
      0 ≤ g.sectionalCurvature y v w := fun y hy =>
    hsec y (Metric.closedBall_subset_ball hρR hy)
  have hev : ∀ j : ℕ, ∀ᶠ k in atTop, 2 ≤ k ∧
      ∀ y ∈ Metric.closedBall o ρ,
        SectionalBoundedBelowAt (gSeq k) y (-1 / ((j : ℝ) + 1)) := by
    intro j
    have hcurv := eventually_sectionalBoundedBelowAt_of_chartCoeff_tendsto g hn gSeq
      hconv hcompact (κ := 0) (ε := 1 / ((j : ℝ) + 1)) (by positivity) hsecC
    exact (eventually_ge_atTop 2).and (by simpa only [zero_sub, neg_div] using hcurv)
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually hev
  exact ⟨ρ, gSeq, φ, hρ, hρA, hρR, hφ, fun j => (hφP j).1,
    hbil, hconv, fun j => (hφP j).2⟩

end DifferentialGeometry.Geometry.FiniteComparison
