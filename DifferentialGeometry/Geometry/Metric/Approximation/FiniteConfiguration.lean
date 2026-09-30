import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace GC.MetricGeometry

open Filter

universe u v w

variable {X : Type u} {Y : Type v} {ι : Type w}
variable [MetricSpace X] [MetricSpace Y]

theorem PointedBallApprox.exists_lift_configuration
    {p : X} {q : Y} {M ε : ℝ}
    (f : PointedBallApprox p q (M + 2) ε) (_hM : 1 ≤ M)
    (hε : ε < 1 / 4) (y : ι → Y) (hy : ∀ a, dist (y a) q ≤ M) :
    ∃ z : ι → BallCarrier p (M + 2),
      (∀ a, dist (f.toFun (z a)) (y a) < ε) ∧
      (∀ a, dist (z a).val p < dist (y a) q + 2 * ε) ∧
      (∀ a, dist (y a) q + 2 * ε < M + 2) ∧
      (∀ a b, |dist (z a).val (z b).val - dist (y a) (y b)| < 3 * ε) := by
  have hMR : M + ε ≤ M + 2 := by linarith
  let z (a : ι) := f.inverseLift hMR ⟨y a, hy a⟩
  have hspec (a : ι) : dist (y a) (f.toFun (z a)) < ε :=
    f.inverseLift_spec hMR ⟨y a, hy a⟩
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro a
    simpa only [dist_comm] using hspec a
  · intro a
    have hr := f.radial_lower (z a)
    have ht := dist_triangle (f.toFun (z a)) (y a) q
    rw [dist_comm (f.toFun (z a)) (y a)] at ht
    linarith [hspec a]
  · intro a
    linarith [hy a]
  · intro a b
    exact f.inverseLift_distortion hMR ⟨y a, hy a⟩ ⟨y b, hy b⟩

theorem PointedBallApprox.exists_injective_lift_configuration
    {p : X} {q : Y} {M ε : ℝ}
    (f : PointedBallApprox p q (M + 2) ε) (hM : 1 ≤ M)
    (hε : ε < 1 / 4) (y : ι → Y) (hy : ∀ a, dist (y a) q ≤ M)
    (hsep : ∀ a b, a ≠ b → 3 * ε < dist (y a) (y b)) :
    ∃ z : ι → BallCarrier p (M + 2), Function.Injective z ∧
      (∀ a, dist (f.toFun (z a)) (y a) < ε) ∧
      (∀ a, dist (z a).val p < dist (y a) q + 2 * ε) ∧
      (∀ a, dist (y a) q + 2 * ε < M + 2) ∧
      (∀ a b, |dist (z a).val (z b).val - dist (y a) (y b)| < 3 * ε) := by
  obtain ⟨z, hi, hr, hR, hd⟩ := f.exists_lift_configuration hM hε y hy
  refine ⟨z, ?_, hi, hr, hR, hd⟩
  intro a b hab
  by_contra hne
  have hdist := hd a b
  rw [hab, dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at hdist
  exact (not_lt_of_gt (hsep a b hne)) hdist

theorem PointedGHConverges.exists_subsequence_lift_configuration
    {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] {p : ∀ n, Z n} {q : Y}
    (h : PointedGHConverges p q) {M : ℝ} (hM : 1 ≤ M)
    (y : ι → Y) (hy : ∀ a, dist (y a) q ≤ M)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεsmall : ∀ j, ε j < 1 / 4)
    (hεzero : Tendsto ε atTop (nhds 0))
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, P j (φ j)) ∧
      ∃ z : ∀ j, ι → BallCarrier (p (φ j)) (M + 2),
        (∀ j a, dist (z j a).val (p (φ j)) < dist (y a) q + 2 * ε j) ∧
        (∀ j a, dist (z j a).val (p (φ j)) < M + 2) ∧
        (∀ j a b, |dist (z j a).val (z j b).val - dist (y a) (y b)| < 3 * ε j) ∧
        (∀ a b, Tendsto (fun j => dist (z j a).val (z j b).val) atTop
          (nhds (dist (y a) (y b)))) := by
  classical
  have hchoose (j : ℕ) : ∀ᶠ n in atTop,
      P j n ∧ Nonempty (PointedBallApprox (p n) q (M + 2) (ε j)) :=
    (hP j).and (h.eventually_approx (hεpos j) (by linarith [hεsmall j]))
  obtain ⟨φ, hφ, hsel⟩ := extraction_forall_of_eventually hchoose
  let f (j : ℕ) := Classical.choice (hsel j).2
  have hlift (j : ℕ) := (f j).exists_lift_configuration hM (hεsmall j) y hy
  choose z hi hr hR hd using hlift
  refine ⟨φ, hφ, fun j => (hsel j).1, z, hr, ?_, hd, ?_⟩
  · intro j a
    exact (hr j a).trans (hR j a)
  · intro a b
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hbound (j : ℕ) : dist (dist (z j a).val (z j b).val) (dist (y a) (y b)) ≤
        3 * ε j := by
      simpa only [Real.dist_eq] using le_of_lt (hd j a b)
    exact squeeze_zero (fun j => dist_nonneg) hbound
      (by simpa using hεzero.const_mul 3)

end GC.MetricGeometry
