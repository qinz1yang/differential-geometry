import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

section

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem isCompact_coordinate_box {ι : Type*} [Finite ι] (C : ι → ℝ) :
    IsCompact {y : EuclideanSpace ℝ ι | ∀ i, |y i| ≤ C i} := by
  classical
  let _ := Fintype.ofFinite ι
  apply Metric.isCompact_of_isClosed_isBounded
  · have heq : {y : EuclideanSpace ℝ ι | ∀ i, |y i| ≤ C i} =
        ⋂ i : ι, {y : EuclideanSpace ℝ ι | |y i| ≤ C i} := by ext; simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).abs continuous_const
  · apply (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ ι)) (r := ∑ i, |C i|)).subset
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have heq : (∑ i : ι, EuclideanSpace.single i (y i)) = y := by ext; simp
    calc
      ‖y‖ = ‖∑ i : ι, EuclideanSpace.single i (y i)‖ := by rw [heq]
      _ ≤ ∑ i : ι, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : ι, |C i| := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [PiLp.norm_single, Real.norm_eq_abs] using (hy i).trans (le_abs_self _)

end DifferentialGeometry.Analysis

end

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem convex_coordinate_box {ι : Type*} (C : ι → ℝ) :
    Convex ℝ {y : EuclideanSpace ℝ ι | ∀ i, |y i| ≤ C i} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab i
  change |a * x i + b * y i| ≤ C i
  calc
    |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * C i + b * C i := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = C i := by rw [← add_mul, hab, one_mul]

end DifferentialGeometry.Analysis

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Finite ι]
local notation "F" => EuclideanSpace ℝ ι

theorem exists_pos_coordinate_box_subset_of_mem_nhds_zero
    {U : Set F} (hU : U ∈ 𝓝 (0 : F)) :
    ∃ τ : ℝ, 0 < τ ∧ {y : F | ∀ i, |y i| ≤ τ} ⊆ U := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  let τ := ε / (Fintype.card ι + 1)
  have hτ : 0 < τ := div_pos hε (by positivity)
  refine ⟨τ, hτ, ?_⟩
  intro y hy
  apply hεU
  apply mem_ball_zero_iff.mpr
  have heq : (∑ i, EuclideanSpace.single i (y i)) = y := by ext; simp
  have hnorm : ‖y‖ ≤ Fintype.card ι * τ := by
    calc
      ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := by rw [heq]
      _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, τ := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [PiLp.norm_single, Real.norm_eq_abs] using hy i
      _ = _ := by simp
  have he : (Fintype.card ι + 1 : ℝ) * τ = ε := by
    dsimp only [τ]
    field_simp
  linarith

theorem exists_source_ball_mapsTo_coordinate_box
    {V : Type*} [PseudoMetricSpace V] {z : V → F} {b : V}
    (hz : ContinuousAt z b) (hzb : z b = 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ closedBall b r, ∀ i, |z x i| ≤ τ := by
  classical
  let _ := Fintype.ofFinite ι
  have hnear : z ⁻¹' ball (0 : F) τ ∈ 𝓝 b :=
    hz.preimage_mem_nhds (hzb ▸ ball_mem_nhds _ hτ)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨r, hr, ?_⟩
  intro x hx i
  have hi : |z x i| ≤ ‖z x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (z x) i
  exact hi.trans (mem_ball_zero_iff.mp (hball hx)).le

end DifferentialGeometry.Analysis

end

end
