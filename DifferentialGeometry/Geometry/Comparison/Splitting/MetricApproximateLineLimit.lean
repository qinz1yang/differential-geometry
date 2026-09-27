import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X]

theorem exists_isometry_of_pointwise_compact_distance_limits
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → ℝ → X)
    (B : ℝ → Set X) (hB : ∀ t, IsCompact (B t))
    (hbound : ∀ i t, f i t ∈ B t) {K : Set X} (hK : IsCompact K)
    (hcenter : ∀ i, f i 0 ∈ K)
    (hdist : ∀ s t, Tendsto (fun i => dist (f i s) (f i t)) l (𝓝 |s - t|)) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ gamma 0 ∈ K := by
  have hcompact : IsCompact (Set.pi univ B) := isCompact_univ_pi hB
  obtain ⟨gamma, _, hcluster⟩ := hcompact.exists_mapClusterPt (f := l) (u := f) (by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ i in l, f i ∈ Set.pi univ B
    exact Filter.Eventually.of_forall fun i t _ => hbound i t)
  have hgamma0 : gamma 0 ∈ K := by
    have h := hcluster.continuousAt_comp (continuous_apply 0).continuousAt
    exact hK.isClosed.mem_of_mapClusterPt h (Filter.Eventually.of_forall hcenter)
  refine ⟨gamma, ?_, hgamma0⟩
  apply Isometry.of_dist_eq
  intro s t
  have h := hcluster.continuousAt_comp
    ((continuous_apply s).dist (continuous_apply t)).continuousAt
  have heq : dist (gamma s) (gamma t) = |s - t| :=
    eq_of_nhds_neBot (h.clusterPt.mono (hdist s t))
  simpa only [Real.dist_eq] using heq

theorem exists_isometry_of_approximate_distance_limits [ProperSpace X]
    (f : ℕ → ℝ → X) {K : Set X} (hK : IsCompact K)
    (hcenter : ∀ n, f n 0 ∈ K)
    (hdist : ∀ s t, Tendsto (fun n => dist (f n s) (f n t)) atTop (𝓝 |s - t|)) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ gamma 0 ∈ K := by
  let p : X := f 0 0
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
  have hnear : ∀ t, ∃ C : ℝ, ∀ n, dist (f n t) (f n 0) ≤ C := by
    intro t
    have hbounded := Metric.isBounded_range_of_tendsto _ (hdist t 0)
    obtain ⟨C, hC⟩ := hbounded.subset_closedBall 0
    refine ⟨C, ?_⟩
    intro n
    have h := hC (Set.mem_range_self n)
    change dist (dist (f n t) (f n 0)) 0 ≤ C at h
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h
  choose C hC using hnear
  let B : ℝ → Set X := fun t => closedBall p (C t + R)
  apply exists_isometry_of_pointwise_compact_distance_limits f B
    (fun t => isCompact_closedBall p (C t + R)) _ hK hcenter hdist
  intro n t
  have hzero : dist (f n 0) p ≤ R := hR (hcenter n)
  exact (dist_triangle (f n t) (f n 0) p).trans (add_le_add (hC t n) hzero)

theorem tendsto_cross_distance_of_approximate_opposite_rays
    {ι : Type*} {l : Filter ι} {alpha beta : ι → ℝ → X}
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t →
      Tendsto (fun i => dist (alpha i s) (alpha i t)) l (𝓝 |s - t|))
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t →
      Tendsto (fun i => dist (beta i s) (beta i t)) l (𝓝 |s - t|))
    (hcenter : ∀ i, alpha i 0 = beta i 0)
    (hopposite : ∀ r, 0 ≤ r →
      Tendsto (fun i => dist (alpha i r) (beta i r)) l (𝓝 (2 * r)))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Tendsto (fun i => dist (alpha i s) (beta i t)) l (𝓝 (s + t)) := by
  have hR : 0 ≤ s + t := add_nonneg hs ht
  have hst : |s + t - s| = t := by
    have heq : s + t - s = t := by ring
    rw [heq, abs_of_nonneg ht]
  have hts : |t - (s + t)| = s := by
    have heq : t - (s + t) = -s := by ring
    rw [heq, abs_neg, abs_of_nonneg hs]
  have heq : 2 * (s + t) - t - s = s + t := by ring
  have hlow : Tendsto (fun i => dist (alpha i (s + t)) (beta i (s + t)) -
      dist (alpha i (s + t)) (alpha i s) - dist (beta i t) (beta i (s + t)))
      l (𝓝 (s + t)) := by
    simpa only [hst, hts, heq] using
      ((hopposite (s + t) hR).sub (halpha (s + t) s hR hs)).sub
        (hbeta t (s + t) ht hR)
  have hupp : Tendsto (fun i => dist (alpha i s) (alpha i 0) +
      dist (beta i 0) (beta i t)) l (𝓝 (s + t)) := by
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hs, abs_of_nonneg ht] using
      (halpha s 0 hs le_rfl).add (hbeta 0 t le_rfl ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro i
    have hchain :=
      (dist_triangle (alpha i (s + t)) (alpha i s) (beta i (s + t))).trans
        (add_le_add_right (dist_triangle (alpha i s) (beta i t) (beta i (s + t)))
          (dist (alpha i (s + t)) (alpha i s)))
    linarith
  · intro i
    calc
      dist (alpha i s) (beta i t) ≤
          dist (alpha i s) (alpha i 0) + dist (alpha i 0) (beta i t) :=
        dist_triangle (alpha i s) (alpha i 0) (beta i t)
      _ = dist (alpha i s) (alpha i 0) + dist (beta i 0) (beta i t) := by
        rw [hcenter i]

theorem exists_isometry_of_approximate_opposite_rays [ProperSpace X]
    (alpha beta : ℕ → ℝ → X) {K : Set X} (hK : IsCompact K)
    (hcenter : ∀ n, alpha n 0 = beta n 0) (hcenterK : ∀ n, alpha n 0 ∈ K)
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t →
      Tendsto (fun n => dist (alpha n s) (alpha n t)) atTop (𝓝 |s - t|))
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t →
      Tendsto (fun n => dist (beta n s) (beta n t)) atTop (𝓝 |s - t|))
    (hopposite : ∀ r, 0 ≤ r →
      Tendsto (fun n => dist (alpha n r) (beta n r)) atTop (𝓝 (2 * r))) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ gamma 0 ∈ K := by
  let f : ℕ → ℝ → X := fun n t => if 0 ≤ t then alpha n t else beta n (-t)
  have hcross (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      Tendsto (fun n => dist (alpha n s) (beta n t)) atTop (𝓝 (s + t)) :=
    tendsto_cross_distance_of_approximate_opposite_rays halpha hbeta hcenter hopposite hs ht
  apply exists_isometry_of_approximate_distance_limits f hK
  · intro n
    simpa only [f, le_refl, ite_true] using hcenterK n
  · intro s t
    by_cases hs : 0 ≤ s
    · by_cases ht : 0 ≤ t
      · simpa only [f, if_pos hs, if_pos ht] using halpha s t hs ht
      · have hnt : 0 ≤ -t := by linarith
        have hst : 0 ≤ s - t := by linarith
        have hval : |s - t| = s + -t := by
          rw [abs_of_nonneg hst, sub_eq_add_neg]
        simpa only [f, if_pos hs, if_neg ht, hval] using hcross s (-t) hs hnt
    · have hns : 0 ≤ -s := by linarith
      by_cases ht : 0 ≤ t
      · have hst : s - t ≤ 0 := by linarith
        have hval : |s - t| = t + -s := by
          rw [abs_of_nonpos hst, neg_sub, sub_eq_add_neg]
        simpa only [f, if_neg hs, if_pos ht, dist_comm, hval] using hcross t (-s) ht hns
      · have hnt : 0 ≤ -t := by linarith
        simpa only [f, if_neg hs, if_neg ht, neg_sub_neg, abs_sub_comm] using
          hbeta (-s) (-t) hns hnt

end DifferentialGeometry.Geometry.Topology
