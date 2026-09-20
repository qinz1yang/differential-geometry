import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

theorem lipschitzOnWith_affine_interpolation
    {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set X} {t : X → ℝ} {a b : X → F} {Lt La Lb δ : ℝ≥0}
    (ht : LipschitzOnWith Lt t s) (ha : LipschitzOnWith La a s)
    (hb : LipschitzOnWith Lb b s) (ht01 : ∀ x ∈ s, t x ∈ Icc (0 : ℝ) 1)
    (hgap : ∀ x ∈ s, ‖b x - a x‖ ≤ (δ : ℝ)) :
    LipschitzOnWith (max La Lb + Lt * δ)
      (fun x => (1 - t x) • a x + t x • b x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have htx : 0 ≤ t x := (ht01 x hx).1
  have htx' : 0 ≤ 1 - t x := sub_nonneg.mpr (ht01 x hx).2
  have ha' : ‖a x - a y‖ ≤ (max La Lb : ℝ≥0) * dist x y := by
    simpa only [dist_eq_norm] using
      (ha.weaken (le_max_left La Lb)).dist_le_mul x hx y hy
  have hb' : ‖b x - b y‖ ≤ (max La Lb : ℝ≥0) * dist x y := by
    simpa only [dist_eq_norm] using
      (hb.weaken (le_max_right La Lb)).dist_le_mul x hx y hy
  have ht' : |t x - t y| ≤ (Lt : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using ht.dist_le_mul x hx y hy
  have hdiff :
      ((1 - t x) • a x + t x • b x) - ((1 - t y) • a y + t y • b y) =
        (1 - t x) • (a x - a y) + t x • (b x - b y) +
          (t x - t y) • (b y - a y) := by
    module
  calc
    dist ((1 - t x) • a x + t x • b x) ((1 - t y) • a y + t y • b y) =
        ‖(1 - t x) • (a x - a y) + t x • (b x - b y) +
          (t x - t y) • (b y - a y)‖ := by
      rw [dist_eq_norm, hdiff]
    _ ≤ (‖(1 - t x) • (a x - a y)‖ + ‖t x • (b x - b y)‖) +
        ‖(t x - t y) • (b y - a y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1 - t x) * ‖a x - a y‖ + t x * ‖b x - b y‖ +
        |t x - t y| * ‖b y - a y‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg htx', abs_of_nonneg htx]
    _ ≤ (1 - t x) * ((max La Lb : ℝ≥0) * dist x y) +
        t x * ((max La Lb : ℝ≥0) * dist x y) +
        ((Lt : ℝ) * dist x y) * (δ : ℝ) :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left ha' htx')
          (mul_le_mul_of_nonneg_left hb' htx))
        (mul_le_mul ht' (hgap y hy) (norm_nonneg _)
          (mul_nonneg Lt.coe_nonneg dist_nonneg))
    _ = ((max La Lb + Lt * δ : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

end DifferentialGeometry.Analysis
