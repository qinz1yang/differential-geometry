import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

namespace Metric

theorem dist_le_mul_add_of_coarse_left_inverse
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {g : Y → X} {L C A : ℝ}
    (hg : ∀ u v, dist (g u) (g v) ≤ L * dist u v + C)
    (hgf : ∀ x, dist (g (f x)) x ≤ A) (x y : X) :
    dist x y ≤ L * dist (f x) (f y) + C + 2 * A := by
  have htri := dist_triangle4 x (g (f x)) (g (f y)) y
  have hx := hgf x
  have hy := hgf y
  have h := hg (f x) (f y)
  rw [dist_comm x (g (f x))] at htri
  linarith

theorem exists_quasi_isometry_bounds_of_coarse_left_inverse
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {g : Y → X} {Lf Cf Lg Cg A : ℝ}
    (hf : ∀ x y, dist (f x) (f y) ≤ Lf * dist x y + Cf)
    (hg : ∀ u v, dist (g u) (g v) ≤ Lg * dist u v + Cg)
    (hgf : ∀ x, dist (g (f x)) x ≤ A) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ L * dist x y + C := by
  let L := max 1 (max Lf Lg)
  let C := max 0 (max Cf (Cg + 2 * A))
  have hL : 1 ≤ L := le_max_left _ _
  have hLf : Lf ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLg : Lg ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 ≤ C := le_max_left _ _
  have hCf : Cf ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCg : Cg + 2 * A ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  refine ⟨L, C, hL, hC, fun x y => ⟨?_, ?_⟩⟩
  · have h := dist_le_mul_add_of_coarse_left_inverse hg hgf x y
    have hgL := mul_le_mul_of_nonneg_right hLg (dist_nonneg (x := f x) (y := f y))
    have hLC : C ≤ L * C := by nlinarith
    have hmain : dist x y ≤ L * (dist (f x) (f y) + C) := by nlinarith
    have hdiv : dist x y / L ≤ dist (f x) (f y) + C :=
      (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm L] using hmain)
    rw [div_eq_mul_inv, mul_comm] at hdiv
    linarith
  · exact (hf x y).trans (add_le_add
      (mul_le_mul_of_nonneg_right hLf dist_nonneg) hCf)

end Metric
