import Mathlib.Topology.EMetricSpace.BoundedVariation



noncomputable section

open Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {f : ℝ → X} {ν : ℝ → Y} {s : Set ℝ}


theorem eVariationOn_le_of_dist_le
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist (ν x) (ν y)) :
    eVariationOn f s ≤ eVariationOn ν s := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans (eVariationOn.sum_le hu hs)
  simp only [edist_dist]
  exact ENNReal.ofReal_le_ofReal (h _ (hs _) _ (hs _))



theorem eVariationOn_Icc_le_of_dist_le_sub {v : ℝ → ℝ} (hv : Monotone v)
    (h : ∀ x y, x ≤ y → dist (f x) (f y) ≤ v y - v x) (a b : ℝ) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (v b - v a) := by
  have hb : eVariationOn f (Icc a b) ≤ eVariationOn v (Icc a b) := by
    apply eVariationOn_le_of_dist_le
    intro x _ y _
    rcases le_total x y with hxy | hyx
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hv hxy)), neg_sub]
      exact h x y hxy
    · rw [dist_comm (f x) (f y), dist_comm (v x) (v y)]
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hv hyx)), neg_sub]
      exact h y x hyx
  exact hb.trans_eq (by simpa only [univ_inter] using
    (hv.monotoneOn univ).eVariationOn_eq (mem_univ a) (mem_univ b))

end DifferentialGeometry.Analysis
