import DifferentialGeometry.Geometry.Metric.Approximation.RayConeLimitProperties
import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinityApplications
import DifferentialGeometry.Geometry.Collapse.RankStrataApplications

/-!
# Consumers of the full LC21 package (tier T4)

* `exists_cone_at_infinity_of_cone_at_infinity`: the cone at infinity again satisfies every
  hypothesis of (F) (proper, geodesic, nonnegative four-point comparison), so it has its own cone
  at infinity with Kleiner–Lott maps from all its large blow-downs.
* `exists_cone_at_infinity_package_of_innerProductSpace`: the package for a finite-dimensional real
  inner product space, with `dimH C ≤ finrank V`.
* `exists_eventually_scaledSplittingRank_le_two_of_dimH_le_two`: the package feeds the
  existing model bound `exists_uniform_scaled_rank_bound_of_model`
  (`Geometry/Collapse/RankStrataApplications.lean`), whose cone hypotheses are exactly the new
  properties (complete, geodesic, `dimH ≤ 2`, four-point comparison `0`): a proper geodesic space with
  nonnegative four-point comparison and `dimH ≤ 2` has splitting rank at most `2` at every large
  constant scale.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

/-- The cone at infinity of `Y` has itself a cone at infinity: the package's cone satisfies the
hypotheses of (F). -/
theorem exists_cone_at_infinity_of_cone_at_infinity
    {Y : Type u} [mY : MetricSpace Y] [ProperSpace Y]
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C),
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) mC q o ε)) ∧
      ∃ (C' : Type u) (mC' : MetricSpace C') (o' : C'), Nonempty (RadialConeData o') ∧
        ProperSpace C' ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
          Nonempty (@KleinerLottApprox C C' (mC.rescale R⁻¹ (inv_pos.mpr hR)) mC' o o' ε) := by
  obtain ⟨C, mC, o, -, hCp, -, hCseg, hCcomp, -, hK⟩ :=
    exists_cone_at_infinity_package_of_fourPointComparison_zero hcomp hsegments q
  exact ⟨C, mC, o, hK, exists_cone_at_infinity_of_fourPointComparison_zero hCcomp hCseg o⟩

/-- The full package for a finite-dimensional real inner product space: the cone has dimension at
most `finrank ℝ V`. -/
theorem exists_cone_at_infinity_package_of_innerProductSpace {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (q : V) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ Module.finrank ℝ V ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox V C ((inferInstance : MetricSpace V).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o ε) := by
  obtain ⟨C, mC, o, hH, hp, hc, hseg, hcompC, hdim, hK⟩ :=
    exists_cone_at_infinity_package_of_fourPointComparison_zero
      fourPointComparison_zero_of_innerProductSpace exists_affine_segment q
  exact ⟨C, mC, o, hH, hp, hc, hseg, hcompC, hdim.trans (Real.dimH_univ_eq_finrank V).le, hK⟩

/-- A proper geodesic space with nonnegative four-point comparison and `dimH ≤ 2` has splitting
rank at most `2` at every large constant scale: the LC21 package supplies the cone hypotheses of
`exists_uniform_scaled_rank_bound_of_model`. -/
theorem exists_eventually_scaledSplittingRank_le_two_of_dimH_le_two :
    ∃ η : ℝ, 0 < η ∧ ∀ (Y : Type u) [mY : MetricSpace Y] [ProperSpace Y],
      fourPointComparison 0 (univ : Set Y) →
      (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) →
      dimH (univ : Set Y) ≤ 2 → ∀ (q : Y) (β : ℕ → ℝ), β 3 ≤ η →
        ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
          @scaledSplittingRank.{u, u} Y mY (fun _ => R)
            (fun _ => hR) β q ≤ 2 := by
  obtain ⟨η, hη, hη10, hex⟩ :=
    DifferentialGeometry.Geometry.Collapse.exists_uniform_scaled_rank_bound_of_model.{u, u}
  refine ⟨η, hη, fun Y mY _ hcomp hseg hdim q β hβ => ?_⟩
  obtain ⟨C, mC, o, -, -, hCc, hCseg, hCcomp, hCdim, hK⟩ :=
    exists_cone_at_infinity_package_of_fourPointComparison_zero hcomp hseg q
  obtain ⟨R₀, hR₀⟩ := hK η hη (by linarith)
  refine ⟨R₀, fun R hR hRR => ?_⟩
  obtain ⟨f⟩ := hR₀ R hR hRR
  exact @hex Y mY (fun _ => R) (fun _ => hR) q C mC hCc o hCseg (hCdim.trans hdim) hCcomp η β
    le_rfl hβ f

end GC.MetricGeometry
