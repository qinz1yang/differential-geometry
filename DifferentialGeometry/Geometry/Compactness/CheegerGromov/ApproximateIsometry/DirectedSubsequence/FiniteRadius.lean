import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.ChainEstimates
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.FiniteRadiusBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.PrescribedRadii
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.Tail
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Balls

set_option autoImplicit false

noncomputable section

universe u uE uH

section

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold ContDiff _root_.Topology BigOperators ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chain_metric_approximation_on_finite_radii
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ)
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
    ∀ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M ∞,
    (∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint) →
    (∀ j, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j)) (δ j) j
      (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall ((X.obj (σ j)).basepoint) (finiteStageRadius L j)) ε p
        (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ j l)
        (X.obj (σ j)).metric (X.obj (σ (j + l))).metric) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  intro Ψ hΨbase hΨdata
  obtain ⟨N, hN⟩ := exists_half_pow_le_three_quarter_pow 2 (by norm_num)
  have heta : ∀ s, N ≤ s → 2 * (1 / 2 : ℝ) ^ s < 1 := by
    intro s hs
    have hz : (3 / 4 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h := hN s hs
    linarith
  have hbudget : ∀ s, N ≤ s →
      (2 * (1 / 2 : ℝ) ^ s) * L ≤ finiteRadiusBuffer L s / 4 :=
    fun s hs => mul_le_finiteRadiusBuffer_quarter hL.le s (hN s hs)
  apply chain_metric_approximation_on_buffered_radii P σ
    (finiteStageRadius L) (finiteComparisonRadius L)
    (finiteOpenRadius L) (finiteMidRadius L) N
    (finiteComparisonRadius_pos hL) (finiteOpenRadius_pos hL) (finiteMidRadius_pos hL)
    (finiteStageRadius_lt_openRadius hL) (finiteOpenRadius_succ_lt_midRadius hL)
    (finiteMidRadius_lt_openRadius hL)
    (fun s l => (finiteMidRadius_lt_comparisonRadius hL s l).le) heta
    (fun s hs l => sqrt_one_add_mul_finiteMidRadius_lt_comparisonRadius hL s l
      (by positivity) (hbudget s hs))
    (fun s hs l => sqrt_one_add_mul_finiteMidRadius_lt_next_openRadius hL s l
      (by positivity : 0 ≤ 2 * (1 / 2 : ℝ) ^ s)
      (by rw [pow_succ]; nlinarith [show 0 < (1 / 2 : ℝ) ^ s by positivity])
      (hbudget s hs)) Ψ hΨbase
  intro j
  obtain ⟨D⟩ := hΨdata j
  exact ⟨D.mono (Set.Subset.refl _) (hδ j)
    (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))⟩

end CheegerGromovCompactness
end DifferentialGeometry

end

section

set_option autoImplicit false
open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_directed_metric_approximation_below_radius
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {L : ℝ} (hL : 0 < L) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint (finiteOuterRadius L n) p C)
    (hinj : ∀ n, ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal (finiteComparisonRadius L n) → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℕ → ℝ,
      (∀ n, 0 < δ n ∧ δ n ≤ ε n ∧ δ n ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      ∃ Ψ : ∀ n, PartialDiffeomorph I I (X.obj (σ n)).M (X.obj (σ (n + 1))).M ∞,
        (∀ n, Ψ n (X.obj (σ n)).basepoint = (X.obj (σ (n + 1))).basepoint) ∧
        (∀ n, Nonempty (PartialDiffeomorphMetricApproximation
          (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (finiteComparisonRadius L n))
          (δ n) n (Ψ n) (X.obj (σ n)).metric (X.obj (σ (n + 1))).metric)) ∧
        (∀ n, Set.MapsTo (Ψ n)
          (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (finiteStageRadius L n))
          (riemannianBallOf (X.obj (σ (n + 1))).metric
            (X.obj (σ (n + 1))).basepoint (finiteStageRadius L (n + 1)))) ∧
        (∀ j k, riemannianClosedBallOf (X.obj (σ j)).metric
            (X.obj (σ j)).basepoint (finiteStageRadius L j) ⊆ (chainComp Ψ j k).source) ∧
        ∀ η : ℝ, 0 < η → η < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximation
            (riemannianClosedBallOf (X.obj (σ j)).metric (X.obj (σ j)).basepoint
              (finiteStageRadius L j)) η p (chainComp Ψ j l)
            (X.obj (σ j)).metric (X.obj (σ (j + l))).metric) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨σ, hσ, δ, hδ, Ψ, hbase, hdata, hmap, hsource⟩ :=
    exists_subsequence_metric_approximation_chain_on_radii X hcomplete hconn
      (finiteStageRadius L) (finiteComparisonRadius L) (finiteOuterRadius L) ε
      (finiteStageRadius_pos hL) (finiteStageRadius_strictMono hL)
      (finiteStageRadius_lt_comparisonRadius hL) (finiteComparisonRadius_lt_outerRadius hL)
      hε hjets hinj
  refine ⟨σ, hσ, δ, hδ, Ψ, hbase, hdata, hmap, hsource, ?_⟩
  let P : ∀ k, ProperMetricOn (I := I) (X.obj k) := fun k =>
    Classical.choice (exists_proper_metric_on (X.obj k) (hcomplete.complete k) (hconn k))
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  have hstep : ∀ j, Nonempty (PartialDiffeomorphMetricApproximation
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j))
      (δ j) j (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric) := by
    intro j
    rw [← ProperMetricOn.riemannianClosedBallOf_eq_closedBall (P (σ j))
      (X.obj (σ j)).basepoint (finiteComparisonRadius_pos hL j).le]
    exact hdata j
  have hacc := chain_metric_approximation_on_finite_radii P σ hL δ
    (fun j => (hδ j).2.2) Ψ hbase hstep
  intro η hη hη1 p
  obtain ⟨N, hN⟩ := hacc η hη hη1 p
  refine ⟨N, fun j hj l => ?_⟩
  have h := hN j hj l
  rwa [← ProperMetricOn.riemannianClosedBallOf_eq_closedBall (P (σ j))
    (X.obj (σ j)).basepoint (finiteStageRadius_pos hL j).le] at h

end DifferentialGeometry.CheegerGromovCompactness

end

section

set_option autoImplicit false
open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_chain_metric_bounds_below_radius
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {L : ℝ} (hL : 0 < L) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint (finiteOuterRadius L n) p C)
    (hinj : ∀ n, ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal (finiteComparisonRadius L n) → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℕ → ℝ,
      (∀ n, 0 < δ n ∧ δ n ≤ ε n ∧ δ n ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      Summable δ ∧
      ∃ Ψ : ∀ n, PartialDiffeomorph I I (X.obj (σ n)).M (X.obj (σ (n + 1))).M ∞,
        (∀ n, Ψ n (X.obj (σ n)).basepoint = (X.obj (σ (n + 1))).basepoint) ∧
        (∀ n, Nonempty (PartialDiffeomorphMetricApproximation
          (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint
            (finiteComparisonRadius L n)) (δ n) n (Ψ n)
          (X.obj (σ n)).metric (X.obj (σ (n + 1))).metric)) ∧
        let M := fun n => (X.obj (σ n)).M
        let g : ∀ n, SmoothRiemannianMetric I (M n) := fun n => (X.obj (σ n)).metric
        let K : ∀ n, Set (M n) := fun n =>
          riemannianClosedBallOf (g n) (X.obj (σ n)).basepoint (finiteStageRadius L n)
        let U : ∀ n, Set (M n) := fun n =>
          riemannianBallOf (g n) (X.obj (σ n)).basepoint (finiteStageRadius L n)
        ∃ N : ℕ,
          let Ψ' : ∀ j, PartialDiffeomorph I I (M (N + j)) (M (N + (j + 1)))
              (∞ : WithTop ℕ∞) := fun j => Ψ (N + j)
          ∃ _ : ∀ j k : ℕ, PartialDiffeomorphMetricApproximation (I := I)
              (K (N + j)) (1 / 2) 0
              (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
              (g (N + j)) (g (N + (j + k))),
            (∀ j k, U (N + j) ⊆
              (chainComp (Mf := fun n => M (N + n)) Ψ' j k).source) ∧
            (∀ j k, MapsTo (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
              (U (N + j)) (U (N + (j + k)))) ∧
            ∀ j p : ℕ, ∃ a : ℕ,
              (chainComp (Mf := fun n => M (N + n)) Ψ' j a :
                M (N + j) → M (N + (j + a))) '' U (N + j) ⊆ K (N + (j + a)) ∧
              ∀ c : ℕ, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
                (K (N + (j + a))) (1 / 2) p
                (chainComp (Mf := fun n => M (N + n)) Ψ' (j + a) c)
                (g (N + (j + a))) (g (N + ((j + a) + c)))) := by
  classical
  obtain ⟨σ, hσ, δ, hδ, Ψ, hbase, hstep, hmap, _, hdata⟩ :=
    exists_subsequence_directed_metric_approximation_below_radius
      X hcomplete hconn hL ε hε hjets hinj
  have hsum : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2 : ℝ)
  have hsumδ : Summable δ := Summable.of_nonneg_of_le
    (fun n => (hδ n).1.le) (fun n => (hδ n).2.2) hsum
  refine ⟨σ, hσ, δ, hδ, hsumδ, Ψ, hbase, hstep, ?_⟩
  let K : ∀ n, Set (X.obj (σ n)).M := fun n =>
    riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (finiteStageRadius L n)
  let U : ∀ n, Set (X.obj (σ n)).M := fun n =>
    riemannianBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (finiteStageRadius L n)
  have hUK : ∀ n, U n ⊆ K n := by
    intro n x hx
    change riemannianEDistOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint x <
      ENNReal.ofReal (finiteStageRadius L n) at hx
    exact hx.le
  exact exists_tail_chain_metric_approximations Ψ (fun n => (X.obj (σ n)).metric)
    K U hUK (fun n x hx => hmap n (hUK n hx))
    (hdata (1 / 2) (by norm_num) (by norm_num))

end DifferentialGeometry.CheegerGromovCompactness

end
