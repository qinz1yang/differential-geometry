import DifferentialGeometry.Topology.MetricSpace.CompactBaseIsometry
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Metric

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_isometric_line_of_compact_centers {K : Set X} (hK : IsCompact K)
    (hsegments : ∀ (R : ℝ) (hR : 0 < R), ∃ f : Icc (-R) R → X,
      Isometry f ∧ f ⟨0, neg_nonpos.mpr hR.le, hR.le⟩ ∈ K) :
    ∃ f : ℝ → X, Isometry f ∧ f 0 ∈ K := by
  classical
  have hs (n : ℕ) := hsegments (n + 1) (by positivity)
  choose f hf hbase using hs
  let c (n : ℕ) (t : ℝ) : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
    ⟨max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) t), le_max_left _ _,
      max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩
  let g (n : ℕ) (t : ℝ) := f n (c n t)
  have hgbase (n : ℕ) : g n 0 ∈ K := by
    simpa only [g, c, min_eq_right (by positivity : (0 : ℝ) ≤ n + 1),
      max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n] : -((n : ℝ) + 1) ≤ 0)] using hbase n
  apply exists_isometry_of_local_distortion 0 hK g hgbase
    (ε := fun _ => 0) tendsto_const_nhds
  intro S
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop S)] with n hn
  intro s t hs ht
  have hclip (u : ℝ) (hu : dist u 0 ≤ S) : (c n u : ℝ) = u := by
    have hu' := abs_le.mp (show |u| ≤ S by simpa [Real.dist_eq] using hu)
    simp only [c, min_eq_right (show u ≤ (n : ℝ) + 1 by linarith),
      max_eq_right (show -((n : ℝ) + 1) ≤ u by linarith)]
  change |dist (f n (c n s)) (f n (c n t)) - dist s t| ≤ 0
  rw [(hf n).dist_eq, Subtype.dist_eq, hclip s hs, hclip t ht, sub_self, abs_zero]

theorem exists_isometric_line_of_unbounded_components
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {K : Set X} (hK : IsCompact K) {a b : X}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    ∃ f : ℝ → X, Isometry f ∧ f 0 ∈ K := by
  classical
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall a
  have hfar (z : X) (hz : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z))
      (R : ℝ) : ∃ x ∈ connectedComponentIn Kᶜ z, R < dist x a := by
    by_contra! h
    exact hz (isBounded_closedBall.subset h)
  apply exists_isometric_line_of_compact_centers hK
  intro R hR
  obtain ⟨x, hx, hxR⟩ := hfar a ha (B + R)
  obtain ⟨y, hy, hyR⟩ := hfar b hb (B + R)
  obtain ⟨g, _, hg0, hg1, hgd⟩ := hsegments x y
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_isometric_segment_of_dist_eq_mul hg0 hg1 hgd
  have hmeet : ∃ t, σ t ∈ K := by
    by_contra! havoid
    let : PreconnectedSpace (Icc (0 : ℝ) (dist x y)) := Subtype.preconnectedSpace isPreconnected_Icc
    have hc := (isPreconnected_range hσ.continuous).subset_connectedComponentIn
      (show x ∈ range σ from ⟨_, hσ0⟩)
      (show range σ ⊆ Kᶜ from by rintro _ ⟨t, rfl⟩; exact havoid t)
    have hyx := hc (show y ∈ range σ from ⟨_, hσ1⟩)
    exact hab ((connectedComponentIn_eq hx).trans
      ((connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hy).symm))
  obtain ⟨t, htK⟩ := hmeet
  have htB : dist (σ t) a ≤ B := hB htK
  have hxdist : dist x (σ t) = (t : ℝ) := by
    conv_lhs => rw [← hσ0, hσ.dist_eq]
    simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg t.property.1]
  have hydist : dist y (σ t) = dist x y - (t : ℝ) := by
    conv_lhs => rw [← hσ1, hσ.dist_eq]
    exact abs_of_nonneg (sub_nonneg.mpr t.property.2)
  have hleft : R ≤ (t : ℝ) := by
    have hh := dist_triangle x (σ t) a
    rw [hxdist] at hh
    linarith
  have hright : (t : ℝ) + R ≤ dist x y := by
    have hh := dist_triangle y (σ t) a
    rw [hydist] at hh
    linarith
  let shift (s : Icc (-R) R) : Icc (0 : ℝ) (dist x y) :=
    ⟨(t : ℝ) + s, by linarith [s.property.1], by linarith [s.property.2]⟩
  refine ⟨σ ∘ shift, Isometry.of_dist_eq (fun s u => ?_), ?_⟩
  · change dist (σ (shift s)) (σ (shift u)) = dist s u
    rw [hσ.dist_eq]
    change |(t : ℝ) + s - ((t : ℝ) + u)| = |(s : ℝ) - u|
    congr 1
    ring
  · simpa [Function.comp_def, shift] using htK

end Metric
