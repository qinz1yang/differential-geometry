import DifferentialGeometry.Geometry.Metric.CloudCoverBindings
import Mathlib.Tactic

/-!
# A dyadic cloud with unbounded full-radius overlap

The actual truncated affine-plane tests have zero error. Full-radius balls are disjoint,
while every centre lies in the five-radius ball at one and every cutoff at zero is active.
This disproves the unshrunk packing inference, without asserting failure of smoothing.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

open Classical in
def dyadicCloudCenters (n : ℕ) : Finset ℝ :=
  insert 0 ((Finset.range n).image (fun i : ℕ => (1 / 2 : ℝ) ^ i))

def dyadicCloudFloor (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / 100

def dyadicCloudRadius (n : ℕ) (x : ℝ) : ℝ := max (dyadicCloudFloor n) (|x| / 4)

def dyadicCloudTestSet (δ : ℝ) : Set ℝ := Icc (-(2 + δ⁻¹)) (2 + δ⁻¹)

theorem dyadicCloud_halfPower (i : ℕ) : (1 / 2 : ℝ) ^ i = (2 : ℝ) ^ (-(i : ℤ)) := by
  classical
  simp [zpow_neg, inv_pow, one_div]

theorem dyadicCloud_floor_pos (n : ℕ) : 0 < dyadicCloudFloor n := by
  classical
  unfold dyadicCloudFloor
  positivity

private theorem dyadicCloud_power_le_one (i : ℕ) : (1 / 2 : ℝ) ^ i ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

private theorem dyadicCloud_power_anti : Antitone (fun i : ℕ => (1 / 2 : ℝ) ^ i) :=
  pow_right_anti₀ (by norm_num) (by norm_num)

theorem dyadicCloud_radius_pos (n : ℕ) (x : ℝ) : 0 < dyadicCloudRadius n x :=
  (dyadicCloud_floor_pos n).trans_le (le_max_left _ _)

theorem dyadicCloud_radius_zero (n : ℕ) : dyadicCloudRadius n 0 = dyadicCloudFloor n := by
  classical
  simp [dyadicCloudRadius, (dyadicCloud_floor_pos n).le]

theorem dyadicCloud_radius_power {n i : ℕ} (hi : i ≤ n) :
    dyadicCloudRadius n ((1 / 2 : ℝ) ^ i) = (1 / 2 : ℝ) ^ i / 4 := by
  classical
  have hp : 0 < (1 / 2 : ℝ) ^ i := by positivity
  have hle := dyadicCloud_power_anti hi
  rw [dyadicCloudRadius, abs_of_pos hp, max_eq_right]
  unfold dyadicCloudFloor
  nlinarith

theorem dyadicCloud_radius_one (n : ℕ) : dyadicCloudRadius n 1 = 1 / 4 := by
  classical
  simpa using dyadicCloud_radius_power (Nat.zero_le n)

theorem dyadicCloud_card (n : ℕ) : (dyadicCloudCenters n).card = n + 1 := by
  classical
  have hzero : (0 : ℝ) ∉ (Finset.range n).image (fun i : ℕ => (1 / 2 : ℝ) ^ i) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i hi
    exact (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) i).ne'
  rw [dyadicCloudCenters, Finset.card_insert_of_notMem hzero,
    Finset.card_image_of_injective (Finset.range n)
      (pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)),
    Finset.card_range]

theorem dyadicCloud_center_bounds {n : ℕ} {x : ℝ} (hx : x ∈ dyadicCloudCenters n) :
    0 ≤ x ∧ x ≤ 1 := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(pow_pos (by norm_num : (0 : ℝ) < 1 / 2) i).le,
      dyadicCloud_power_le_one i⟩

theorem dyadicCloud_radius_bounds {n : ℕ} {x : ℝ} (hx : x ∈ dyadicCloudCenters n) :
    dyadicCloudFloor n ≤ dyadicCloudRadius n x ∧ dyadicCloudRadius n x ≤ 1 / 4 := by
  classical
  have hfloor : dyadicCloudFloor n ≤ 1 / 100 := by
    unfold dyadicCloudFloor
    linarith [dyadicCloud_power_le_one n]
  obtain ⟨hx0, hx1⟩ := dyadicCloud_center_bounds hx
  refine ⟨le_max_left _ _, max_le (by linarith) ?_⟩
  rw [abs_of_nonneg hx0]
  linarith

theorem dyadicCloud_radius_lipschitz (n : ℕ) (x y : ℝ) :
    |dyadicCloudRadius n y - dyadicCloudRadius n x| ≤ |y - x| / 4 := by
  classical
  have hmax := abs_max_sub_max_le_abs (|y| / 4) (|x| / 4) (dyadicCloudFloor n)
  have habs := abs_abs_sub_abs_le_abs_sub y x
  have hdiv : |(|y| / 4) - (|x| / 4)| = |(|y| - |x|)| / 4 := by
    rw [← sub_div, abs_div]
    norm_num
  simpa only [dyadicCloudRadius, max_comm, hdiv] using
    hmax.trans (by rw [hdiv]; linarith)

theorem dyadicCloud_radius_inequality (n : ℕ) (x y : ℝ) :
    |dyadicCloudRadius n y - dyadicCloudRadius n x| ≤ dist x y + dyadicCloudRadius n x := by
  classical
  have hlip := dyadicCloud_radius_lipschitz n x y
  rw [Real.dist_eq, abs_sub_comm x y]
  linarith [abs_nonneg (y - x), dyadicCloud_radius_pos n x]

theorem dyadicCloud_exact_test {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x : ℝ} (hx : x ∈ dyadicCloudCenters n) :
    dyadicCloudTestSet δ ∩ ball x (dyadicCloudRadius n x / δ) =
      (AffineSubspace.mk' x (⊤ : Submodule ℝ ℝ) : Set ℝ) ∩
        ball x (dyadicCloudRadius n x / δ) := by
  classical
  simp only [AffineSubspace.mk'_top, AffineSubspace.top_coe, univ_inter]
  apply inter_eq_right.mpr
  intro y hy
  obtain ⟨hx0, hx1⟩ := dyadicCloud_center_bounds hx
  have hr := (dyadicCloud_radius_bounds hx).2
  have hd : |y - x| < dyadicCloudRadius n x / δ := hy
  have htest : dyadicCloudRadius n x / δ ≤ δ⁻¹ := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hδ]
  obtain ⟨hlo, hup⟩ := abs_lt.mp (hd.trans_le htest)
  change -(2 + δ⁻¹) ≤ y ∧ y ≤ 2 + δ⁻¹
  constructor <;> linarith

private theorem dyadicCloud_power_separation {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i < j) :
    dyadicCloudRadius n ((1 / 2 : ℝ) ^ i) +
      dyadicCloudRadius n ((1 / 2 : ℝ) ^ j) <
        dist ((1 / 2 : ℝ) ^ i) ((1 / 2 : ℝ) ^ j) := by
  classical
  have hp : 0 < (1 / 2 : ℝ) ^ i := by positivity
  have hsmall : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i / 2 := by
    have hh := dyadicCloud_power_anti (Nat.succ_le_of_lt hij)
    change (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (i + 1) at hh
    rw [pow_succ] at hh
    nlinarith
  rw [dyadicCloud_radius_power hi.le, dyadicCloud_radius_power hj.le,
    Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ (1 / 2 : ℝ) ^ i - (1 / 2) ^ j)]
  linarith

private theorem dyadicCloud_zero_separation {n i : ℕ} (hi : i < n) :
    dyadicCloudRadius n 0 + dyadicCloudRadius n ((1 / 2 : ℝ) ^ i) <
      dist (0 : ℝ) ((1 / 2 : ℝ) ^ i) := by
  classical
  have hp : 0 < (1 / 2 : ℝ) ^ i := by positivity
  have hh := dyadicCloud_power_anti hi.le
  rw [dyadicCloud_radius_zero, dyadicCloud_radius_power hi.le, Real.dist_eq,
    zero_sub, abs_neg, abs_of_pos hp]
  unfold dyadicCloudFloor
  nlinarith

theorem dyadicCloud_disjoint (n : ℕ) :
    (dyadicCloudCenters n : Set ℝ).PairwiseDisjoint
      (fun x => ball x (dyadicCloudRadius n x)) := by
  classical
  intro x hx y hy hxy
  apply disjoint_ball_ball_iff (dyadicCloud_radius_pos n x)
    (dyadicCloud_radius_pos n y) |>.mpr
  change x ∈ dyadicCloudCenters n at hx
  change y ∈ dyadicCloudCenters n at hy
  rcases Finset.mem_insert.mp hx with rfl | hx
  · obtain ⟨i, hi, rfl⟩ :=
      Finset.mem_image.mp ((Finset.mem_insert.mp hy).resolve_left hxy.symm)
    exact (dyadicCloud_zero_separation (Finset.mem_range.mp hi)).le
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [add_comm, dist_comm] using
        (dyadicCloud_zero_separation (Finset.mem_range.mp hi)).le
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hij : i ≠ j := fun heq => hxy (congrArg (fun k : ℕ => (1 / 2 : ℝ) ^ k) heq)
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (dyadicCloud_power_separation (Finset.mem_range.mp hi)
          (Finset.mem_range.mp hj) hij).le
      · simpa only [add_comm, dist_comm] using
          (dyadicCloud_power_separation (Finset.mem_range.mp hj)
            (Finset.mem_range.mp hi) hji).le

theorem dyadicCloud_centers_in_fiveBall {n : ℕ} {x : ℝ} (hx : x ∈ dyadicCloudCenters n) :
    x ∈ ball (1 : ℝ) (5 * dyadicCloudRadius n 1) := by
  classical
  obtain ⟨hx0, hx1⟩ := dyadicCloud_center_bounds hx
  rw [dyadicCloud_radius_one]
  change |x - 1| < 5 * (1 / 4 : ℝ)
  rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
  linarith

theorem dyadicCloud_cutoff_argument {n : ℕ} {x : ℝ} (hx : x ∈ dyadicCloudCenters n) :
    |(0 : ℝ) - x| / (10 * dyadicCloudRadius n x) ≤ 2 / 5 := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hp : 0 < (1 / 2 : ℝ) ^ i := by positivity
    rw [zero_sub, abs_neg, abs_of_pos hp,
      dyadicCloud_radius_power (Finset.mem_range.mp hi).le]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith

theorem dyadicCloud_cutoff_sum (n : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ t ∈ Icc (0 : ℝ) (1 / 2), χ t = 1) :
    ∑ x ∈ dyadicCloudCenters n, χ (|(0 : ℝ) - x| / (10 * dyadicCloudRadius n x)) =
      (n + 1 : ℕ) := by
  classical
  calc
    _ = ∑ x ∈ dyadicCloudCenters n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply hχ
      refine ⟨div_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num) (dyadicCloud_radius_pos n x).le), ?_⟩
      have hh := dyadicCloud_cutoff_argument hx
      linarith
    _ = (n + 1 : ℕ) := by simp [dyadicCloud_card]


theorem dyadicCloud_packet (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (dyadicCloudCenters n : Set ℝ) ⊆ dyadicCloudTestSet δ ∧
    Bornology.IsBounded (dyadicCloudCenters n : Set ℝ) ∧
    0 < dyadicCloudFloor n ∧
    (∀ x ∈ dyadicCloudCenters n, dyadicCloudFloor n ≤ dyadicCloudRadius n x ∧
      dyadicCloudRadius n x ≤ 1 / 4) ∧
    (∀ x : (dyadicCloudCenters n : Set ℝ),
      Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 ∧
      hausdorffEDist (dyadicCloudTestSet δ ∩ ball (x : ℝ) (dyadicCloudRadius n x / δ))
        ((AffineSubspace.mk' (x : ℝ) (⊤ : Submodule ℝ ℝ) : Set ℝ) ∩
          ball (x : ℝ) (dyadicCloudRadius n x / δ)) = 0) := by
  classical
  refine ⟨?_, (dyadicCloudCenters n).finite_toSet.isBounded, dyadicCloud_floor_pos n,
    fun x hx => dyadicCloud_radius_bounds hx, ?_⟩
  · intro x hx
    obtain ⟨hx0, hx1⟩ := dyadicCloud_center_bounds hx
    change -(2 + δ⁻¹) ≤ x ∧ x ≤ 2 + δ⁻¹
    constructor <;> linarith [inv_pos.mpr hδ]
  · intro x
    refine ⟨by simp, ?_⟩
    rw [dyadicCloud_exact_test hδ x.property]
    exact hausdorffEDist_self

theorem dyadicCloud_radius_test_bound {n : ℕ} {δ x : ℝ} (hδ : 0 < δ)
    (hx : x ∈ dyadicCloudTestSet δ) : dyadicCloudRadius n x ≤ (2 + δ⁻¹) / 4 := by
  classical
  have ha : |x| ≤ 2 + δ⁻¹ := abs_le.mpr hx
  have hf : dyadicCloudFloor n ≤ 1 / 100 := by
    unfold dyadicCloudFloor
    linarith [dyadicCloud_power_le_one n]
  apply max_le
  · linarith [inv_pos.mpr hδ]
  · linarith

theorem dyadicCloud_counterexample (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hn : 1 ≤ n) :
    (1 : ℝ) ∈ dyadicCloudCenters n ∧
    (dyadicCloudCenters n).card = n + 1 ∧
    (dyadicCloudCenters n : Set ℝ).PairwiseDisjoint
      (fun x => ball x (dyadicCloudRadius n x)) ∧
    (∀ x ∈ dyadicCloudCenters n, x ∈ ball (1 : ℝ) (5 * dyadicCloudRadius n 1)) ∧
    (∀ x ∈ dyadicCloudCenters n,
      |(0 : ℝ) - x| / (10 * dyadicCloudRadius n x) ≤ 2 / 5) ∧
    (dyadicCloudCenters n : Set ℝ) ⊆ dyadicCloudTestSet δ ∧
    (∀ x : (dyadicCloudCenters n : Set ℝ),
      hausdorffEDist (dyadicCloudTestSet δ ∩ ball (x : ℝ) (dyadicCloudRadius n x / δ))
        ((AffineSubspace.mk' (x : ℝ) (⊤ : Submodule ℝ ℝ) : Set ℝ) ∩
          ball (x : ℝ) (dyadicCloudRadius n x / δ)) = 0) := by
  classical
  refine ⟨?_, dyadicCloud_card n, dyadicCloud_disjoint n,
    fun x hx => dyadicCloud_centers_in_fiveBall hx,
    fun x hx => dyadicCloud_cutoff_argument hx, (dyadicCloud_packet n δ hδ).1,
    fun x => (dyadicCloud_packet n δ hδ).2.2.2.2 x |>.2⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩

open Classical in
theorem dyadicCloud_unbounded_local_count (B : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      B < ((dyadicCloudCenters n).filter
        (fun x => x ∈ ball (1 : ℝ) (5 * dyadicCloudRadius n 1))).card := by
  classical
  refine ⟨B + 1, by omega, ?_⟩
  have heq : (dyadicCloudCenters (B + 1)).filter
      (fun x => x ∈ ball (1 : ℝ) (5 * dyadicCloudRadius (B + 1) 1)) =
        dyadicCloudCenters (B + 1) :=
    Finset.filter_eq_self.mpr (fun x hx => dyadicCloud_centers_in_fiveBall hx)
  rw [heq, dyadicCloud_card]
  omega

end GC.MetricGeometry
