import DifferentialGeometry.Geometry.Comparison.PairedPacket
import DifferentialGeometry.Geometry.Comparison.ModelAngleStability

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v

variable {Y : Type u} {ι : Type*} [MetricSpace Y] [Finite ι]

theorem PairedComparisonPacket.exists_metric_perturbation_bounds
    {δ : ℝ} {q : Y} (c : ι × Bool → Y)
    (hpacket : PairedComparisonPacket (δ / 2) {q}
      (fun j => c (j, true)) (fun j => c (j, false)))
    (hδ : 0 < δ) (hne : ∀ j, q ≠ c j) :
    ∃ a A ξ : ℝ, 0 < a ∧ a ≤ A ∧ 0 < ξ ∧
      ∀ {Z : Type v} [MetricSpace Z] (z : Z) (d : ι × Bool → Z),
        (∀ j, |dist z (d j) - dist q (c j)| < ξ) →
        (∀ j k, |dist (d j) (d k) - dist (c j) (c k)| < ξ) →
        PairedComparisonPacket δ {z} (fun j => d (j, true)) (fun j => d (j, false)) ∧
        ∀ j, dist z (d j) ∈ Icc a A := by
  have hfinite : (range c).Finite := finite_range c
  have hq : q ∈ (range c)ᶜ := by
    rintro ⟨j, hj⟩
    exact hne j hj.symm
  obtain ⟨a₀, ha₀, hball⟩ := Metric.isOpen_iff.mp hfinite.isClosed.isOpen_compl q hq
  obtain ⟨A₀, hA₀⟩ := (hfinite.image (fun y => dist q y)).bddAbove
  have hlo (j) : a₀ ≤ dist q (c j) := by
    by_contra hh
    exact hball (by rw [mem_ball, dist_comm]; exact lt_of_not_ge hh) ⟨j, rfl⟩
  have hhi (j) : dist q (c j) ≤ A₀ := hA₀ ⟨c j, ⟨j, rfl⟩, rfl⟩
  let a := a₀ / 2
  let A := max a (A₀ + 1)
  have ha : 0 < a := half_pos ha₀
  obtain ⟨η, hη, hstab⟩ := comparisonAngleNegCurvature_uniform_stability_on_side_window
    (κ := 1) (Lmax := A) (by norm_num) ha (half_pos hδ)
  let ξ := min η (min a 1)
  have hξ : 0 < ξ := lt_min hη (lt_min ha zero_lt_one)
  have hξη : ξ ≤ η := min_le_left _ _
  have hξa : ξ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hξ1 : ξ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have horig (j) : dist q (c j) ∈ Icc a A :=
    ⟨by dsimp [a]; linarith [hlo j], (hhi j).trans (by dsimp [A]; exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))⟩
  refine ⟨a, A, ξ, ha, le_max_left _ _, hξ, ?_⟩
  intro Z _ z d hd hdd
  have hnew (j) : dist z (d j) ∈ Icc a A := by
    have hj := abs_lt.mp (hd j)
    constructor
    · have := hlo j
      dsimp [a] at *
      linarith
    · have := hhi j
      have hAA : A₀ + 1 ≤ A := le_max_right _ _
      linarith
  have hangle (j k) : |comparisonAngleNegCurvature 1 (dist z (d j)) (dist z (d k))
      (dist (d j) (d k)) - comparisonAngleNegCurvature 1 (dist q (c j)) (dist q (c k))
      (dist (c j) (c k))| < δ / 2 := by
    apply hstab _ _ _ _ _ _ (hnew j) (hnew k) ?_ (horig j) (horig k) ?_
      ((hd j).trans_le hξη) ((hd k).trans_le hξη) ((hdd j k).trans_le hξη)
    · constructor
      · exact dist_nonneg
      · have ht := dist_triangle (d j) z (d k)
        rw [dist_comm (d j) z] at ht
        linarith [(hnew j).2, (hnew k).2]
    · constructor
      · exact dist_nonneg
      · have ht := dist_triangle (c j) q (c k)
        rw [dist_comm (c j) q] at ht
        linarith [(horig j).2, (horig k).2]
  refine ⟨?_, hnew⟩
  constructor
  · intro w hw j
    have hwz : w = z := mem_singleton_iff.mp hw
    subst w
    have hp := hpacket.opposite q (by simp) j
    have hh := (abs_lt.mp (hangle (j, true) (j, false))).1
    linarith
  · intro w hw j k hjk u hu v hv
    have hwz : w = z := mem_singleton_iff.mp hw
    subst w
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hu :
      u = d (j, true) ∨ u = d (j, false)) with rfl | rfl <;>
      rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hv :
        v = d (k, true) ∨ v = d (k, false)) with rfl | rfl
    all_goals
      have hp := hpacket.cross q (by simp) j k hjk
      first
      | have hp' := hp (c (j, true)) (by simp) (c (k, true)) (by simp)
        have hh := (abs_lt.mp (hangle (j, true) (k, true))).1
        linarith
      | have hp' := hp (c (j, true)) (by simp) (c (k, false)) (by simp)
        have hh := (abs_lt.mp (hangle (j, true) (k, false))).1
        linarith
      | have hp' := hp (c (j, false)) (by simp) (c (k, true)) (by simp)
        have hh := (abs_lt.mp (hangle (j, false) (k, true))).1
        linarith
      | have hp' := hp (c (j, false)) (by simp) (c (k, false)) (by simp)
        have hh := (abs_lt.mp (hangle (j, false) (k, false))).1
        linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
