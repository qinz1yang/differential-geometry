import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.RadialConeIdentities
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

/-!
# Producers of LC21 cone-at-infinity packages

Blueprint 207A, LC21 (`def:collapse-cone-at-infinity`): a cone-at-infinity package of a pointed
metric space `(N, n)` is a pointed cone `(C, o)` with AC82 radial maps and, for every `0 < ε < 1`,
a threshold `R₀` such that every rescaling `(R⁻¹ N, n)` with `R ≥ R₀` has an actual pointed
Kleiner–Lott `ε`-approximation to the fixed `(C, o)`. The package is used inline (as the
hypothesis `hlimit` of `exists_uniform_bounded_rescaling`); no named predicate is introduced.

This file produces the approximation clause of such packages in the two cases the blueprint
singles out:

* a cone is its own cone at infinity: the radial map `H_{1/R}` is an onto isometry
  `R⁻¹ C → C` (`RadialConeData.nonempty_kleinerLottApprox_rescale_self`);
* a bounded (in particular compact) space has the one-point cone (A:20893–20895,
  `exists_kleinerLottApprox_rescale_point_of_isBounded`).

The Tits-cone existence theorem for nonnegatively curved spaces (KL Section 3.3) is not proved
here; the blueprint keeps it as a source-qualified input.
-/

set_option autoImplicit false

noncomputable section
open Set Metric
open scoped NNReal

namespace GC.MetricGeometry

/-- LC21 for a cone: for every `R > 0` the radial map `H_{1/R}` is an actual pointed
Kleiner–Lott `ε`-approximation `(R⁻¹ C, o) → (C, o)` (it is an onto isometry). -/
theorem RadialConeData.nonempty_kleinerLottApprox_rescale_self {C : Type*} [mC : MetricSpace C]
    {o : C} (H : RadialConeData o) (R : ℝ) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Nonempty (@KleinerLottApprox C C (mC.rescale R⁻¹ (inv_pos.mpr hR)) mC o o ε) := by
  let t : ℝ≥0 := ⟨R⁻¹, (inv_pos.mpr hR).le⟩
  have ht : t ≠ 0 := by
    intro h
    have h' := congrArg (fun s : ℝ≥0 => (s : ℝ)) h
    simp only [NNReal.coe_zero, t] at h'
    exact (inv_pos.mpr hR).ne' h'
  have hdist (x y : C) : dist (H.map t x) (H.map t y) =
      @dist C (mC.rescale R⁻¹ (inv_pos.mpr hR)).toDist x y := by
    rw [MetricSpace.rescale_dist, H.similarity]
    rfl
  refine ⟨@KleinerLottApprox.mk C C (mC.rescale R⁻¹ (inv_pos.mpr hR)) mC o o ε hε hε1
    (H.map t) (H.map_apex t) ?_ ?_⟩
  · intro x _ x' _
    rw [hdist, sub_self, abs_zero]
    exact hε.le
  · intro y hy
    have hmem : y ∈ H.map t '' @Metric.ball C (mC.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace
        o ε⁻¹ := by
      refine ⟨H.map t⁻¹ y, ?_, H.map_map_inv ht y⟩
      change @dist C (mC.rescale R⁻¹ (inv_pos.mpr hR)).toDist (H.map t⁻¹ y) o < ε⁻¹
      rw [← hdist, H.map_map_inv ht, H.map_apex]
      linarith
    rw [infDist_zero_of_mem hmem]
    exact hε.le

/-- LC21 for a bounded space (in particular a compact one): the one-point cone is a cone at
infinity, with threshold `R₀ = diam N / ε`. -/
theorem exists_kleinerLottApprox_rescale_point_of_isBounded {N : Type*} [mN : MetricSpace N]
    (n : N) (hb : Bornology.IsBounded (univ : Set N)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N PUnit (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit ε) := by
  refine ⟨Metric.diam (univ : Set N) / ε, fun R hR hR₀ => ?_⟩
  refine ⟨@KleinerLottApprox.mk N PUnit (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit ε hε hε1
    (fun _ => PUnit.unit) rfl ?_ ?_⟩
  · intro x _ x' _
    rw [dist_self, zero_sub, abs_neg, MetricSpace.rescale_dist,
      abs_of_nonneg (mul_nonneg (inv_pos.mpr hR).le dist_nonneg)]
    have hd : dist x x' ≤ Metric.diam (univ : Set N) :=
      Metric.dist_le_diam_of_mem hb (mem_univ x) (mem_univ x')
    have hdR : Metric.diam (univ : Set N) ≤ ε * R := by
      rw [div_le_iff₀ hε] at hR₀
      linarith
    rw [inv_mul_le_iff₀ hR]
    linarith
  · intro y _
    have hmem : y ∈ (fun _ : N => PUnit.unit) ''
        @Metric.ball N (mN.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace n ε⁻¹ :=
      ⟨n, @Metric.mem_ball_self N (mN.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace _ _
        (inv_pos.mpr hε), Subsingleton.elim _ _⟩
    rw [infDist_zero_of_mem hmem]
    exact hε.le

/-- LC21 for a compact space: the one-point cone. -/
theorem exists_kleinerLottApprox_rescale_point_of_compactSpace {N : Type*} [mN : MetricSpace N]
    [CompactSpace N] (n : N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N PUnit (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit ε) :=
  exists_kleinerLottApprox_rescale_point_of_isBounded n isCompact_univ.isBounded hε hε1

/-- The one-point cone carries AC82 radial data. -/
def RadialConeData.punit : RadialConeData PUnit.unit where
  map _ _ := PUnit.unit
  map_zero _ := rfl
  map_one _ := Subsingleton.elim _ _
  dist_sq _ _ _ _ := by simp [radialConeKernel]

end GC.MetricGeometry
