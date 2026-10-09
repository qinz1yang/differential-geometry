import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinity
import DifferentialGeometry.Geometry.Comparison.RayChordInnerProduct

/-!
# Consumers of the cone-at-infinity producer (F)

* `exists_kleinerLottApprox_rescale_ge_of_fourPointComparison_zero`: the one-scale form W1 of the
  design (`docs/geometrization/chapter13/design-tits-cone-20261004.md` §1.3), the weakest form
  LC23's proof consumes: above every threshold there is a scale with a Kleiner–Lott map to an AC82
  cone.
* `exists_affine_segment`: segments of a real normed space in the form (F) takes.
* `exists_cone_at_infinity_of_innerProductSpace`: (F) for every finite-dimensional real inner product
  space (four-point comparison from tier T1's `fourPointComparison_zero_of_innerProductSpace`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

/-- W1 (design §1.3): for every `0 < ε < 1` and every threshold `T` there are a scale `R ≥ T` and
an AC82 cone with a Kleiner–Lott `ε`-map from `(R⁻¹ Y, q)`. -/
theorem exists_kleinerLottApprox_rescale_ge_of_fourPointComparison_zero
    {Y : Type u} [mY : MetricSpace Y] [ProperSpace Y]
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℝ) :
    ∃ R : ℝ, ∃ hR : 0 < R, T ≤ R ∧
      ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
        Nonempty (@KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) mC q o ε) := by
  obtain ⟨C, mC, o, hH, -, hK⟩ :=
    exists_cone_at_infinity_of_fourPointComparison_zero hcomp hsegments q
  obtain ⟨R₀, hR₀⟩ := hK ε hε hε1
  have hpos : 0 < max (max R₀ T) 1 := lt_max_of_lt_right one_pos
  exact ⟨max (max R₀ T) 1, hpos, le_max_of_le_left (le_max_right _ _), C, mC, o, hH,
    hR₀ _ hpos (le_max_of_le_left (le_max_left _ _))⟩

/-- Segments of a real normed space: the affine parametrization `t ↦ a + t (b - a)`. -/
theorem exists_affine_segment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : V) :
    ∃ f : Icc (0 : ℝ) 1 → V, Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧
      f ⟨1, by norm_num⟩ = b ∧ ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  refine ⟨fun t => AffineMap.lineMap a b (t : ℝ),
    (AffineMap.lineMap_continuous).comp continuous_subtype_val, AffineMap.lineMap_apply_zero a b,
    AffineMap.lineMap_apply_one a b, fun s t => ?_⟩
  rw [dist_lineMap_lineMap, mul_comm, Subtype.dist_eq]

/-- (F) for a finite-dimensional real inner product space: it has a proper AC82 cone at infinity
with Kleiner–Lott maps from all large blow-downs. -/
theorem exists_cone_at_infinity_of_innerProductSpace {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (q : V) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
      @ProperSpace C mC.toPseudoMetricSpace ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox V C ((inferInstance : MetricSpace V).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o ε) :=
  exists_cone_at_infinity_of_fourPointComparison_zero fourPointComparison_zero_of_innerProductSpace
    exists_affine_segment q

end GC.MetricGeometry
