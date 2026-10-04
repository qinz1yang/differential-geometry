import DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinity
import DifferentialGeometry.Geometry.Collapse.OriginalRadialSplitting

/-!
# The cone at infinity of a manifold with `sec ≥ 0` has dimension at most `n`

The finite-dimensional form of the Riemannian LC21 package (LFR59, A:29862: "Hausdorff dimension
at most `n`"). `exists_cone_at_infinity_package_of_sectional_nonneg` gives `dimH C ≤ dimH M`; the
σ-compact dimension bridge `dimH_univ_le_finrank_of_riemannian_distance` (Codex X82,
`Geometry/Collapse/OriginalRadialSplitting.lean`: finite Riemannian volume on a compact exhaustion,
no compactness of `M`) gives `dimH M ≤ finrank ℝ E`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The full LC21 package for a complete Riemannian manifold with `sec ≥ 0`, with the dimension
bound `dimH C ≤ finrank ℝ E` of LFR59. -/
theorem exists_cone_at_infinity_package_of_sectional_nonneg_finrank {M : Type u}
    [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [CompleteSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y 0) (p : M) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ Module.finrank ℝ E ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox M C (mM.rescale R⁻¹ (inv_pos.mpr hR)) mC p o ε) := by
  obtain ⟨C, mC, o, hH, hp, hc, hseg, hcompC, hdim, hK⟩ :=
    exists_cone_at_infinity_package_of_sectional_nonneg g hmetric hsec p
  exact ⟨C, mC, o, hH, hp, hc, hseg, hcompC,
    hdim.trans (dimH_univ_le_finrank_of_riemannian_distance g hmetric), hK⟩

/-- The brief's form (complete, connected, NONcompact `M` with `sec ≥ 0`): the extra hypotheses are
not used, so the theorem above is a strengthening. -/
example {M : Type u} [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M] [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y 0) (p : M) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ Module.finrank ℝ E ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox M C (mM.rescale R⁻¹ (inv_pos.mpr hR)) mC p o ε) :=
  exists_cone_at_infinity_package_of_sectional_nonneg_finrank g hmetric hsec p

end DifferentialGeometry.Geometry.Collapse
