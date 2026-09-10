import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X]

theorem dist_eq_sub_of_lipschitzWith_one_of_endpoints {f : ℝ → X}
    (hf : LipschitzWith 1 f) {a s t b : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hend : dist (f a) (f b) = b - a) : dist (f s) (f t) = t - s := by
  have hbound (u v : ℝ) (huv : u ≤ v) : dist (f u) (f v) ≤ v - u := by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv),
      neg_sub] using hf.dist_le_mul u v
  have htri := (dist_triangle (f a) (f s) (f b)).trans
    (add_le_add (le_refl (dist (f a) (f s))) (dist_triangle (f s) (f t) (f b)))
  have hleft := hbound a s has
  have hright := hbound t b htb
  have hmiddle := hbound s t hst
  rw [hend] at htri
  linarith

theorem exists_isometry_of_two_sided_minimizing_segments [ProperSpace X]
    (f : ℕ → ℝ → X) (hLip : ∀ n, LipschitzWith 1 (f n))
    {K : Set X} (hK : IsCompact K) (hcenter : ∀ n, f n 0 ∈ K)
    (a b : ℕ → ℝ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hend : ∀ n, dist (f n (-a n)) (f n (b n)) = a n + b n) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ gamma 0 ∈ K := by
  let p : X := f 0 0
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
  let B : ℝ → Set X := fun t => closedBall p (|t| + R)
  have hbound (n : ℕ) : f n ∈ Set.pi univ B := by
    intro t _
    have hzero : dist (f n 0) p ≤ R := hR (hcenter n)
    have hnear : dist (f n t) (f n 0) ≤ |t| := by
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_zero] using (hLip n).dist_le_mul t 0
    exact (dist_triangle (f n t) (f n 0) p).trans (add_le_add hnear hzero)
  have hcompact : IsCompact (Set.pi univ B) :=
    isCompact_univ_pi fun t => isCompact_closedBall p (|t| + R)
  obtain ⟨gamma, _, hcluster⟩ := hcompact.exists_mapClusterPt (f := atTop) (u := f) (by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ n in atTop, f n ∈ Set.pi univ B
    exact Filter.Eventually.of_forall hbound)
  have hgamma0 : gamma 0 ∈ K := by
    have h := hcluster.continuousAt_comp (continuous_apply 0).continuousAt
    exact hK.isClosed.mem_of_mapClusterPt h (Filter.Eventually.of_forall hcenter)
  have hdist (s t : ℝ) (hst : s ≤ t) : dist (gamma s) (gamma t) = t - s := by
    have hevent : ∀ᶠ n in atTop, dist (f n s) (f n t) = t - s := by
      filter_upwards [ha (eventually_ge_atTop (-s)), hb (eventually_ge_atTop t)] with n hna hnb
      change -s ≤ a n at hna
      change t ≤ b n at hnb
      apply dist_eq_sub_of_lipschitzWith_one_of_endpoints (hLip n)
        (a := -a n) (b := b n) (by linarith) hst hnb
      simpa only [sub_neg_eq_add, add_comm] using hend n
    have h := hcluster.continuousAt_comp
      ((continuous_apply s).dist (continuous_apply t)).continuousAt
    exact isClosed_singleton.mem_of_mapClusterPt h hevent
  refine ⟨gamma, ?_, hgamma0⟩
  apply Isometry.of_dist_eq
  intro s t
  rcases le_total s t with hst | hts
  · rw [hdist s t hst, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  · rw [dist_comm (gamma s) (gamma t), hdist t s hts, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts)]

end DifferentialGeometry.Geometry.Topology
