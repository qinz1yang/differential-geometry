import DifferentialGeometry.Geometry.Comparison.ArbitraryQualityPairedPackets
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_rank_three_packet_near_of_dimH_gt_two
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdimlo : 2 < dimH (univ : Set X)) (hdimhi : dimH (univ : Set X) ≤ 3)
    (x : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ q ∈ ball x r, ∃ a b : Fin 3 → X, PairedComparisonPacket ε {q} a b := by
  classical
  have : Nontrivial X := by
    by_contra h
    have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    have hz : dimH (univ : Set X) = 0 := (Set.subsingleton_univ).dimH_zero
    rw [hz] at hdimlo
    exact (not_lt_of_ge (by norm_num)) hdimlo
  have hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω :=
    fun _ => ⟨univ, isOpen_univ, hcomp.of_zero (by norm_num), mem_univ _⟩
  obtain ⟨m, hm, hd, _, hp⟩ :=
    exists_global_rank_paired_packets_of_local_comparison_and_dimH
      hcurves (n := 3) (by simpa using hdimhi) hlocal
  have hmlo : 2 < m := by
    rw [hd] at hdimlo
    exact_mod_cast hdimlo
  have hmeq : m = 3 := by omega
  subst m
  obtain ⟨q, hq, Ω, _, _, _, a, b, _, hab⟩ :=
    hp ε hε (ball x r) isOpen_ball ⟨x, mem_ball_self hr⟩
  exact ⟨q, hq, a, b, hab⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
