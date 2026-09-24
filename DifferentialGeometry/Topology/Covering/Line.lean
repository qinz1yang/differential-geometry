import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

private theorem not_bddBelow_range_of_abs_sub_le_abs_sub_add
    (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ)
    (hd : ∀ s t : ℝ, |s - t| ≤ |f s - f t| + C) : ¬ BddBelow (range f) := by
  intro hbelow
  obtain ⟨B, hB⟩ := hbelow
  have hlow (t : ℝ) : B ≤ f t := hB (mem_range_self t)
  have hC : 0 ≤ C := by simpa using hd 0 0
  let T := max (f 0 - B + C) C + 1
  have hTC : C < T := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hTB : f 0 - B + C < T := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hT : 0 < T := hC.trans_lt hTC
  have hneg : f 0 < f (-T) := by
    by_contra hnot
    have hb := hd (-T) 0
    rw [sub_zero, abs_neg, abs_of_pos hT, abs_of_nonpos (sub_nonpos.mpr (not_lt.mp hnot))] at hb
    linarith [hlow (-T)]
  let U := max (f 0 - B + C) (f (-T) - f 0 + C) + 1
  have hUB : f 0 - B + C < U := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hUF : f (-T) - f 0 + C < U := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hU : 0 < U := by linarith
  have hpos : f (-T) < f U := by
    by_contra hnot
    have hb := hd U 0
    rw [sub_zero, abs_of_pos hU] at hb
    rcases le_total (f U) (f 0) with hle | hge
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hb
      linarith [hlow U]
    · rw [abs_of_nonneg (sub_nonneg.mpr hge)] at hb
      linarith [not_lt.mp hnot]
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hU.le hf.continuousOn ⟨hneg.le, hpos.le⟩
  have hb := hd (-T) s
  rw [heq, sub_self, abs_zero, zero_add] at hb
  rw [abs_of_nonpos (by linarith [hs.1] : -T - s ≤ 0)] at hb
  linarith [hs.1]


variable {S X : Type*} [TopologicalSpace S] [PseudoMetricSpace X]

theorem not_isometry_of_covering_reflection
    (proj : S × ℝ → X) (hproj : IsCoveringMap proj) (hsurj : Function.Surjective proj)
    (τ : S → S) (hreflection : ∀ p : S × ℝ, proj (τ p.1, -p.2) = proj p)
    (C : ℝ) (hbound : ∀ p q : S × ℝ, dist (proj p) (proj q) ≤ |p.2 - q.2| + C)
    (γ : ℝ → X) : ¬ Isometry γ := by
  intro hγ
  obtain ⟨p, hp⟩ := hsurj (γ 0)
  obtain ⟨G, ⟨_, hG⟩, _⟩ := hproj.existsUnique_continuousMap_lifts ⟨γ, hγ.continuous⟩ 0 p hp
  have hproj (t : ℝ) : proj (G t) = γ t := congrFun hG t
  have hrad (p q : S × ℝ) : dist (proj p) (proj q) ≤ |abs p.2 - abs q.2| + C := by
    have hb := hbound p q
    have hr := hbound p (τ q.1, -q.2)
    rw [hreflection q] at hr
    dsimp only at hr
    rcases le_total 0 p.2 with hp | hp <;> rcases le_total 0 q.2 with hq | hq
    · simpa only [abs_of_nonneg hp, abs_of_nonneg hq] using hb
    · simpa only [abs_of_nonneg hp, abs_of_nonpos hq] using hr
    · rw [abs_of_nonpos hp, abs_of_nonneg hq]
      have heq : -p.2 - q.2 = -(p.2 - -q.2) := by ring
      rw [heq, abs_neg]
      exact hr
    · rw [abs_of_nonpos hp, abs_of_nonpos hq]
      have heq : -p.2 - -q.2 = -(p.2 - q.2) := by ring
      rw [heq, abs_neg]
      exact hb
  apply not_bddBelow_range_of_abs_sub_le_abs_sub_add (fun t => |(G t).2|)
    (continuous_snd.comp G.continuous).abs C ?_ ⟨0, ?_⟩
  · intro s t
    have hb := hrad (G s) (G t)
    rw [hproj, hproj, hγ.dist_eq, Real.dist_eq] at hb
    exact hb
  · rintro _ ⟨t, rfl⟩
    exact abs_nonneg _

end DifferentialGeometry.Topology
