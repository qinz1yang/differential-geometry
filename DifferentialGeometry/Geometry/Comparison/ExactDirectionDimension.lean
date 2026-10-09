import DifferentialGeometry.Geometry.Comparison.GlobalTangentDimension
import DifferentialGeometry.Geometry.Metric.ConeHausdorffDimension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_global_exact_tangent_direction_dimH_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∀ q : X,
        letI : HasAnglesAt q := by
          obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
          exact hasAnglesAt_of_local_fourPointComparison
            (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
        dimH (univ : Set (TangentCone q)) = m ∧
          dimH (univ : Set (SpaceOfDirections q)) = (m - 1 : ℕ) ∧
          (1 < m → ∀ a b : SpaceOfDirections q,
            ∃ f : Icc (0 : ℝ) 1 → SpaceOfDirections q,
              Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) := by
  obtain ⟨m, hmn, hglobal, hopen, hpoint⟩ :=
    exists_global_tangent_dimH_and_directions_of_local_comparison_and_dimH hcurves hdim hlocal
  refine ⟨m, hmn, hglobal, hopen, ?_⟩
  intro q
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨hT, hdir, hgeo⟩ := hpoint q
  refine ⟨hT, le_antisymm hdir ?_, hgeo⟩
  cases m with
  | zero => simp only [Nat.zero_sub, Nat.cast_zero]; exact zero_le
  | succ k =>
      have hcone := EuclideanCone.dimH_univ_le_dimH_base_add_one
        (Y := SpaceOfDirections q)
      change dimH (univ : Set (TangentCone q)) ≤
        dimH (univ : Set (SpaceOfDirections q)) + 1 at hcone
      rw [hT] at hcone
      have hsum : (k : ENNReal) + 1 ≤ dimH (univ : Set (SpaceOfDirections q)) + 1 := by
        simpa only [Nat.cast_succ] using hcone
      have hlow : (k : ENNReal) ≤ dimH (univ : Set (SpaceOfDirections q)) :=
        (ENNReal.add_le_add_iff_right (by simp : (1 : ENNReal) ≠ ⊤)).mp hsum
      simpa only [Nat.succ_sub_one] using hlow

end DifferentialGeometry.Geometry.Comparison.Toponogov
