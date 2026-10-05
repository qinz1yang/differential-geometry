import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# Slack-aware restriction toward an affine plane (uncoded lemma, `master207B.tex` B:10923)

Blueprint `lem:fibration-cloud-quality-weakening` (lines 10923–10950) and the paragraph after it
(open balls, lines 10952–10960; the cloud-quality weakening, lines 10968–10978).

* `exists_mem_affineSubspace_dist_le_trunc`: radial truncation inside an affine subspace through
  `x`: a point `a ∈ A` can be moved toward `x` to radius `≤ ρ`, by at most `max 0 (|a − x| − ρ)`.
* `affine_restriction_closedBall`: if `S ∩ B̄(x, R)` and `A ∩ B̄(x, R)` have Hausdorff distance at
  most `e` (two distance-to-set bounds; no closedness, no attained nearest point), then for every
  `0 < r ≤ R` the restrictions to `B̄(x, r)` have Hausdorff distance at most `6e`;
  `affine_restriction_ball`: the same with open balls throughout.
* `cloud_test_weakening`: a truncated-set test of quality `Γ` at radius `ρ(x)` (open balls of radius
  `ρ/Γ`, error `Γ ρ`) with `0 < Γ < δ / 8` implies the test of quality `δ` (radius `ρ/δ`, error
  `δ ρ`), for the same centre, radius and affine plane — the form of the cloud test (CS).
-/

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial truncation of a point of an affine subspace through `x`. -/
theorem exists_mem_affineSubspace_dist_le_trunc {A : AffineSubspace ℝ E} {x a : E} (hxA : x ∈ A)
    (ha : a ∈ A) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ a' ∈ A, dist a' x ≤ ρ ∧ dist a a' ≤ max 0 (dist a x - ρ) := by
  by_cases h : dist a x ≤ ρ
  · exact ⟨a, ha, h, by simp⟩
  rw [not_le] at h
  have hd : 0 < dist a x := hρ.trans_lt h
  set t : ℝ := ρ / dist a x with ht
  have ht0 : 0 ≤ t := div_nonneg hρ hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr h.le
  refine ⟨t • (a -ᵥ x) +ᵥ x, A.smul_vsub_vadd_mem t ha hxA hxA, ?_, ?_⟩
  · rw [vsub_eq_sub, vadd_eq_add, dist_eq_norm, add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg ht0, ← dist_eq_norm, ht, div_mul_cancel₀ _ hd.ne']
  · have hx : a - (t • (a - x) + x) = (1 - t) • (a - x) := by
      rw [sub_smul, one_smul]
      abel
    rw [vsub_eq_sub, vadd_eq_add, dist_eq_norm, hx, norm_smul, Real.norm_of_nonneg (by linarith),
      ← dist_eq_norm, sub_mul, one_mul, ht, div_mul_cancel₀ _ hd.ne']
    exact le_max_right _ _

/-- Witness form of a Hausdorff bound with slack: `hausdorffEDist ≤ e` and `e > 0` give witnesses
at distance `< 2e`. -/
theorem exists_dist_lt_two_mul_of_hausdorffEDist_le {M : Type*} [PseudoMetricSpace M]
    {X Y : Set M} {e : ℝ} (he : 0 < e)
    (h : hausdorffEDist X Y ≤ ENNReal.ofReal e) {z : M} (hz : z ∈ X) :
    ∃ y ∈ Y, dist z y < 2 * e := by
  have h2e : (0 : ℝ) < 2 * e := by linarith
  have hlt : ENNReal.ofReal e < ENNReal.ofReal (2 * e) :=
    (ENNReal.ofReal_lt_ofReal_iff h2e).mpr (by linarith)
  obtain ⟨y, hy, hzy⟩ := exists_edist_lt_of_hausdorffEDist_lt hz (h.trans_lt hlt)
  refine ⟨y, hy, ?_⟩
  rw [edist_dist] at hzy
  exact (ENNReal.ofReal_lt_ofReal_iff h2e).mp hzy

/-- The lemma with closed balls: the restriction to `B̄(x, r)`, `0 < r ≤ R`, has Hausdorff
distance at most `6e`. -/
theorem affine_restriction_closedBall {S : Set E} {A : AffineSubspace ℝ E} {x : E} (hxS : x ∈ S)
    (hxA : x ∈ A) {R e r : ℝ} (he : 0 < e) (hr : 0 < r) (hrR : r ≤ R)
    (h : hausdorffEDist (S ∩ closedBall x R) ((A : Set E) ∩ closedBall x R) ≤ ENNReal.ofReal e) :
    hausdorffEDist (S ∩ closedBall x r) ((A : Set E) ∩ closedBall x r) ≤
      ENNReal.ofReal (6 * e) := by
  have h' : hausdorffEDist ((A : Set E) ∩ closedBall x R) (S ∩ closedBall x R) ≤
      ENNReal.ofReal e := by rwa [hausdorffEDist_comm]
  apply hausdorffEDist_le_of_mem_edist
  · rintro z ⟨hzS, hzr⟩
    rw [mem_closedBall] at hzr
    obtain ⟨a, ⟨haA, -⟩, hza⟩ := exists_dist_lt_two_mul_of_hausdorffEDist_le he h
      ⟨hzS, mem_closedBall.mpr (hzr.trans hrR)⟩
    obtain ⟨a', ha'A, ha'x, haa'⟩ := exists_mem_affineSubspace_dist_le_trunc hxA haA hr.le
    refine ⟨a', ⟨ha'A, mem_closedBall.mpr ha'x⟩, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hax : dist a x ≤ dist a z + dist z x := dist_triangle a z x
    have := dist_triangle z a a'
    rw [dist_comm a z] at hax
    have hm : max 0 (dist a x - r) < 2 * e := max_lt (by linarith) (by linarith)
    linarith
  · rintro a ⟨haA, har⟩
    rw [mem_closedBall] at har
    by_cases hr4 : r ≤ 4 * e
    · refine ⟨x, ⟨hxS, mem_closedBall_self hr.le⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [not_le] at hr4
    obtain ⟨a', ha'A, ha'x, haa'⟩ := exists_mem_affineSubspace_dist_le_trunc hxA haA
      (ρ := r - 4 * e) (by linarith)
    obtain ⟨z, ⟨hzS, -⟩, ha'z⟩ := exists_dist_lt_two_mul_of_hausdorffEDist_le he h'
      ⟨ha'A, mem_closedBall.mpr (by linarith)⟩
    have hzx : dist z x < r := by
      have := dist_triangle z a' x
      rw [dist_comm z a'] at this
      linarith
    refine ⟨z, ⟨hzS, mem_closedBall.mpr hzx.le⟩, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hm : max 0 (dist a x - (r - 4 * e)) ≤ 4 * e := max_le (by linarith) (by linarith)
    have := dist_triangle a a' z
    linarith

/-- The lemma with open balls throughout. -/
theorem affine_restriction_ball {S : Set E} {A : AffineSubspace ℝ E} {x : E} (hxS : x ∈ S)
    (hxA : x ∈ A) {R e r : ℝ} (he : 0 < e) (hr : 0 < r) (hrR : r ≤ R)
    (h : hausdorffEDist (S ∩ ball x R) ((A : Set E) ∩ ball x R) ≤ ENNReal.ofReal e) :
    hausdorffEDist (S ∩ ball x r) ((A : Set E) ∩ ball x r) ≤ ENNReal.ofReal (6 * e) := by
  have h' : hausdorffEDist ((A : Set E) ∩ ball x R) (S ∩ ball x R) ≤ ENNReal.ofReal e := by
    rwa [hausdorffEDist_comm]
  apply hausdorffEDist_le_of_mem_edist
  · rintro z ⟨hzS, hzr⟩
    rw [mem_ball] at hzr
    by_cases hr4 : r ≤ 4 * e
    · refine ⟨x, ⟨hxA, mem_ball_self hr⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [not_le] at hr4
    obtain ⟨a, ⟨haA, -⟩, hza⟩ := exists_dist_lt_two_mul_of_hausdorffEDist_le he h
      ⟨hzS, mem_ball.mpr (hzr.trans_le hrR)⟩
    obtain ⟨a', ha'A, ha'x, haa'⟩ := exists_mem_affineSubspace_dist_le_trunc hxA haA
      (ρ := r - 2 * e) (by linarith)
    refine ⟨a', ⟨ha'A, mem_ball.mpr (by linarith)⟩, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hax : dist a x ≤ dist a z + dist z x := dist_triangle a z x
    rw [dist_comm a z] at hax
    have hm : max 0 (dist a x - (r - 2 * e)) < 4 * e := max_lt (by linarith) (by linarith)
    have := dist_triangle z a a'
    linarith
  · rintro a ⟨haA, har⟩
    rw [mem_ball] at har
    by_cases hr4 : r ≤ 4 * e
    · refine ⟨x, ⟨hxS, mem_ball_self hr⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [not_le] at hr4
    obtain ⟨a', ha'A, ha'x, haa'⟩ := exists_mem_affineSubspace_dist_le_trunc hxA haA
      (ρ := r - 4 * e) (by linarith)
    obtain ⟨z, ⟨hzS, -⟩, ha'z⟩ := exists_dist_lt_two_mul_of_hausdorffEDist_le he h'
      ⟨ha'A, mem_ball.mpr (by linarith)⟩
    have hzx : dist z x < r := by
      have := dist_triangle z a' x
      rw [dist_comm z a'] at this
      linarith
    refine ⟨z, ⟨hzS, mem_ball.mpr hzx⟩, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hm : max 0 (dist a x - (r - 4 * e)) ≤ 4 * e := max_le (by linarith) (by linarith)
    have := dist_triangle a a' z
    linarith

/-- Cloud-quality weakening (B:10968–10978): a truncated-set test of quality `Γ` at the radius
`ρ` with `0 < Γ < δ / 8` implies the test of quality `δ` for the same centre, radius and plane. -/
theorem cloud_test_weakening {S : Set E} {A : AffineSubspace ℝ E} {x : E} (hxS : x ∈ S)
    (hxA : x ∈ A) {ρ Γ δ : ℝ} (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΓδ : Γ < δ / 8)
    (h : hausdorffEDist (S ∩ ball x (ρ / Γ)) ((A : Set E) ∩ ball x (ρ / Γ)) ≤
      ENNReal.ofReal (Γ * ρ)) :
    hausdorffEDist (S ∩ ball x (ρ / δ)) ((A : Set E) ∩ ball x (ρ / δ)) ≤
      ENNReal.ofReal (δ * ρ) := by
  have hδ : 0 < δ := by linarith
  have hle : ρ / δ ≤ ρ / Γ := div_le_div_of_nonneg_left hρ.le hΓ (by linarith)
  refine (affine_restriction_ball hxS hxA (mul_pos hΓ hρ) (div_pos hρ hδ) hle h).trans
    (ENNReal.ofReal_le_ofReal ?_)
  nlinarith

end GC.MetricGeometry
