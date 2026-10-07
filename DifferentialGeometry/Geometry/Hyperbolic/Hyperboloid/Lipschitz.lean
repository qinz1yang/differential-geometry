import DifferentialGeometry.Topology.MetricSpace.CoveringLipschitz
import DifferentialGeometry.Topology.MetricSpace.LocalLipschitzComposition
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Geodesic
import Mathlib.Algebra.Order.Floor.Ring

open scoped Topology NNReal

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lipschitzWith_of_locally_lipschitzOnWith
    {Y : Type*} [PseudoEMetricSpace Y] {f : Hyperboloid E → Y} {L : ℝ≥0}
    (hf : ∀ x, ∃ U ∈ 𝓝 x, LipschitzOnWith L f U) :
    LipschitzWith L f := by
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  obtain ⟨c, hc, hc0, hc1⟩ := exists_isometry_through hxy
  have hcomp := DifferentialGeometry.Topology.lipschitzOnWith_comp_of_locally_lipschitzOn
    (a := 0) (b := dist x y) hc.lipschitzWith.lipschitzOnWith
    (fun z _ => hf z)
  have hbound := hcomp (show (0 : ℝ) ∈ Set.Icc 0 (dist x y) from ⟨le_rfl, dist_nonneg⟩)
    (show dist x y ∈ Set.Icc 0 (dist x y) from ⟨dist_nonneg, le_rfl⟩)
  simpa only [Function.comp_apply, ← hc.edist_eq, hc0, hc1, mul_one] using hbound

theorem lipschitzWith_of_lift
    {Y B : Type*} [PseudoEMetricSpace Y] [PseudoEMetricSpace B]
    {f : Hyperboloid E → Y} {p : Y → B} {L : ℝ≥0}
    (hf : Continuous f)
    (hp : ∀ y, ∃ V ∈ 𝓝 y, ∀ u ∈ V, ∀ v ∈ V, edist u v ≤ edist (p u) (p v))
    (hcomp : LipschitzWith L (p ∘ f)) : LipschitzWith L f :=
  lipschitzWith_of_locally_lipschitzOnWith
    (Metric.exists_lipschitzOnWith_nhds_of_comp hf hp hcomp)

theorem lipschitzWith_lift_of_image_ball
    {A B Y : Type*} [PseudoEMetricSpace A] [PseudoEMetricSpace B] [PseudoMetricSpace Y]
    {f : A → B} {q : Hyperboloid E → A} {p : Y → B} {F : Hyperboloid E → Y}
    {L : ℝ≥0} (hF : Continuous F) (hp : IsLocallyInjective p)
    (hball : ∀ y r, 0 < r → p '' Metric.ball y r = Metric.eball (p y) (ENNReal.ofReal r))
    (hcomm : ∀ x, p (F x) = f (q x)) (hq : LipschitzWith 1 q)
    (hf : LipschitzWith L f) : LipschitzWith L F := by
  apply lipschitzWith_of_lift hF (Metric.exists_nhds_edist_le_of_image_ball hp hball)
  have heq : p ∘ F = f ∘ q := funext hcomm
  rw [heq]
  simpa only [mul_one] using hf.comp hq

theorem dist_le_mul_add_of_dist_le_one
    {Y : Type*} [PseudoMetricSpace Y] {f : Hyperboloid E → Y} {B : ℝ}
    (hf : ∀ x y, dist x y ≤ 1 → dist (f x) (f y) ≤ B)
    (x y : Hyperboloid E) : dist (f x) (f y) ≤ B * dist x y + B := by
  have hB : 0 ≤ B := by
    simpa only [dist_self] using hf origin origin (by simp)
  by_cases hxy : x = y
  · simp [hxy, hB]
  obtain ⟨c, hc, hc0, hc1⟩ := exists_isometry_through hxy
  let n : ℕ := ⌈dist x y⌉₊
  have hn : 0 < n := Nat.ceil_pos.mpr (dist_pos.mpr hxy)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdn : dist x y ≤ (n : ℝ) := Nat.le_ceil _
  let t : ℕ → ℝ := fun i => (i : ℝ) * (dist x y / n)
  have ht0 : t 0 = 0 := by simp [t]
  have htn : t n = dist x y := by
    dsimp [t]
    field_simp [ne_of_gt hnpos]
  have hstep (i : ℕ) : dist (c (t i)) (c (t (i + 1))) ≤ 1 := by
    rw [hc.dist_eq, Real.dist_eq]
    have heq : t i - t (i + 1) = -(dist x y / n) := by
      simp only [t, Nat.cast_add, Nat.cast_one]
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg dist_nonneg hnpos.le)]
    exact (div_le_one hnpos).mpr hdn
  have hsum : dist (f (c (t 0))) (f (c (t n))) ≤ (n : ℝ) * B := by
    have h := dist_le_range_sum_of_dist_le (f := fun i => f (c (t i)))
      n (d := fun _ => B) (fun {i} _ => hf _ _ (hstep i))
    simpa using h
  rw [ht0, htn, hc0, hc1] at hsum
  have hceil : (n : ℝ) ≤ dist x y + 1 := (Nat.ceil_lt_add_one dist_nonneg).le
  nlinarith

end DifferentialGeometry.Hyperboloid
