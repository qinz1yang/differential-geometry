import DifferentialGeometry.Geometry.Operator.DivergenceNaturality
import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open Bundle Geometry.Curvature Geometry.Connection Geometry.Operator
open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem divergence_g_with_boundary_eq_divergence_metricCov [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceGWithBoundary g X x = divergence (metricCov g) X x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hleft := (divergence_g_with_boundary_contMDiff g X).continuous.continuousAt (x := x)
  have hright := (leviCivita_divergence_contMDiff g X).continuous.continuousAt (x := x)
  by_contra hne
  have hev := (hleft.sub hright).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hyint⟩ := mem_closure_iff_nhds.mp (I.dense_interior (M := M) x) _ hev
  apply hy
  apply sub_eq_zero.mpr
  exact (divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint g X hyint).trans
    (divergence_g_eq_leviCivita_divergence_of_isInteriorPoint g X hyint)

theorem divergence_g_with_boundary_pullbackCross [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceGWithBoundary (Diffeomorph.pullbackMetricCross g Φ) X x =
      divergenceGWithBoundary g (pushFwdSectionCross Φ X) (Φ x) := by
  rw [divergence_g_with_boundary_eq_divergence_metricCov, divergence_g_with_boundary_eq_divergence_metricCov]
  exact divergence_metricCov_pullbackCross g Φ X x

theorem divergence_g_with_boundary_restrictOpen [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : U) :
    divergenceGWithBoundary (g.restrictOpen U) (restrictOpenTangentSection U X) x =
      divergenceGWithBoundary g X x.1 := by
  rw [divergence_g_with_boundary_eq_divergence_metricCov, divergence_g_with_boundary_eq_divergence_metricCov]
  exact divergence_metricCov_restrictOpen g U X x


end

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
