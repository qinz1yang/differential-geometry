import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def metricApproximationBallSystem
    (b : ∀ j, M j) (r ε : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hε : ∀ j, 0 ≤ ε j)
    (p : ℕ → ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ∀ j, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) (r j)) (ε j) (p j) (Ψ j) (g j) (g (j + 1)))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hgrow : ∀ j, Real.sqrt (1 + ε j) * r j < r (j + 1)) :
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ball_open_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ball_open_nonempty b r j (hr j)
  have hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source := by
    intro j x hx
    apply (D j).source_sub
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  have hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1))) := by
    intro j
    have hdata : MapMetricApproximationOn (I := I)
        (Metric.closedEBall (b j) (ENNReal.ofReal (r j))) (ε j) (p j)
        (Ψ j : M j → M (j + 1)) (g j) (g (j + 1)) := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).forward
    have hsource : Metric.closedEBall (b j) (ENNReal.ofReal (r j)) ⊆ (Ψ j).source := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).source_sub
    simpa only [ballOpen, Opens.coe_mk, hbase j] using
      (data_image_metric_ball (I := I) (Ψ j) (hnorm j) (hnorm (j + 1))
        (hr j) le_rfl (hε j) (hgrow j) hdata hsource)
  exact ballSystem b r hr Ψ hsrc hmap

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def directedBallSystem
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
        (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    Σ j₀ : ℕ,
      let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
      let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
      letI : ∀ n, Nonempty (ballOpen b' r' n) :=
        fun n => ball_open_nonempty b' r' n (by positivity)
      SmoothSeqSystem I (fun n => ballOpen b' r' n) := by
  classical
  let hex := hdata (1 / 2) (by norm_num) (by norm_num) 0
  let j₀ := Classical.choose hex
  have hj₀ := Classical.choose_spec hex
  refine ⟨j₀, ?_⟩
  let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
  let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
  let Ψ' : ∀ n, PartialDiffeomorph I I (M (j₀ + n)) (M (j₀ + (n + 1)))
      (∞ : WithTop ℕ∞) := fun n =>
    chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1
  let g' : ∀ n, SmoothRiemannianMetric I (M (j₀ + n)) := fun n => g (j₀ + n)
  letI : ∀ n, Nonempty (ballOpen b' r' n) :=
    fun n => ball_open_nonempty b' r' n (by dsimp [r']; positivity)
  have hD : ∀ n, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1))) := by
    intro n
    exact hj₀ (j₀ + n) (Nat.le_add_right j₀ n) 1
  let D : ∀ n, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1)) :=
    fun n => Classical.choice (hD n)
  have hbase' : ∀ n, (Ψ' n : M (j₀ + n) → M (j₀ + (n + 1))) (b' n) = b' (n + 1) := by
    intro n
    exact chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1
  have hnorm' : ∀ n (x : M (j₀ + n)) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g' n).inner x v v)) := by
    intro n
    exact hnorm (j₀ + n)
  have hgrow : ∀ n, Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < r' (n + 1) := by
    intro n
    have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < 2 * r' n :=
        mul_lt_mul_of_pos_right hsqrt (by dsimp [r']; positivity)
      _ = r' (n + 1) := by
        dsimp [r']
        rw [show j₀ + (n + 1) = (j₀ + n) + 1 by omega]
        rw [pow_succ]
        ring
  exact metricApproximationBallSystem b' r' (fun _ => 1 / 2) (fun n => by dsimp [r']; positivity)
    (fun _ => by norm_num) (fun _ => 0) Ψ' hbase' g' D hnorm' hgrow

end ApproxData

end HCGCompactness
end DifferentialGeometry
