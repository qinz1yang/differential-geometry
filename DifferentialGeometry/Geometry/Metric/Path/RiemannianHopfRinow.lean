import DifferentialGeometry.Geometry.Metric.Path.Variation
import DifferentialGeometry.Topology.MetricSpace.HopfRinow

/-!
# Metric Hopf–Rinow on a Riemannian manifold of any regularity

If the distance of `M` is the Riemannian distance of a bundle metric (`IsRiemannianManifold I M`),
the tree's metric Hopf–Rinow (`Metric.properSpace_of_arbitrarily_short_curves`,
`Metric.exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves`,
Topology/MetricSpace/HopfRinow.lean) applies, because `Manifold.exists_path_eVariationOn_lt_of_riemannianEDist_lt`
(Geometry/Metric/Path/Variation.lean) supplies arbitrarily short curves. No smoothness of the bundle
metric is used: this is the metric part of Hopf–Rinow for finite-regularity metrics (CM2.b).
Lane CM-H, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)] [IsRiemannianManifold I M]

variable (I) in
include I in
/-- On a Riemannian manifold (distance = Riemannian distance of a bundle metric), any two points
are joined by curves of length arbitrarily close to their distance. -/
theorem exists_short_curve_of_isRiemannianManifold (a b : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : unitInterval → M, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) := by
  have hlt : riemannianEDist I a b < ENNReal.ofReal (dist a b + ε) := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := a) (y := b)])).mpr
      (by linarith)
  obtain ⟨p, hp⟩ := exists_path_eVariationOn_lt_of_riemannianEDist_lt (I := I) hlt
  exact ⟨p, p.continuous, p.source, p.target, hp⟩

variable (I) in
include I in
/-- **Hopf–Rinow, metric part.** A complete finite-dimensional Riemannian manifold is proper
(closed bounded sets are compact). No regularity of the metric is used. -/
theorem properSpace_of_isRiemannianManifold [FiniteDimensional ℝ E] [CompleteSpace M] :
    ProperSpace M := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  exact Metric.properSpace_of_arbitrarily_short_curves
    (fun a b ε hε => exists_short_curve_of_isRiemannianManifold I a b hε)

variable (I) in
include I in
/-- On a complete finite-dimensional Riemannian manifold any two points are joined by a
unit-speed segment. -/
theorem exists_unit_speed_segment_of_isRiemannianManifold [FiniteDimensional ℝ E]
    [CompleteSpace M] (x y : M) :
    ∃ c : ℝ → M, c 0 = x ∧ c (dist x y) = y ∧
      ∀ s ∈ Icc 0 (dist x y), ∀ t ∈ Icc 0 (dist x y), dist (c s) (c t) = |s - t| := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨f, -, hf0, hf1, hf⟩ :=
    Metric.exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves
      (fun a b ε hε => exists_short_curve_of_isRiemannianManifold I a b hε) x y
  rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with hd | hd
  · have hxy : x = y := dist_eq_zero.mp hd.symm
    subst hxy
    refine ⟨fun _ => x, rfl, rfl, fun s hs t ht => ?_⟩
    rw [dist_self] at hs ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    simp [hs0, ht0]
  · refine ⟨fun t => f (projIcc 0 1 zero_le_one (t / dist x y)), ?_, ?_, fun s hs t ht => ?_⟩
    · simp only [zero_div, projIcc_left]
      exact hf0
    · simp only [div_self hd.ne', projIcc_right]
      exact hf1
    · have hs' : s / dist x y ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hs.1 hd.le, (div_le_one hd).mpr hs.2⟩
      have ht' : t / dist x y ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hd.le, (div_le_one hd).mpr ht.2⟩
      simp only
      rw [hf, projIcc_of_mem _ hs', projIcc_of_mem _ ht', Subtype.dist_eq, Real.dist_eq,
        ← sub_div, abs_div, abs_of_pos hd]
      field_simp

end Manifold
