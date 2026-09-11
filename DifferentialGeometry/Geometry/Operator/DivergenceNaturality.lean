import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Operator.Divergence

namespace DifferentialGeometry.Geometry.Operator

open Bundle Curvature Connection
open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem divergence_metricCov_pullbackCross [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence (metricCov (Diffeomorph.pullbackMetricCross g Φ)) X x =
      divergence (metricCov g) (pushFwdSectionCross Φ X) (Φ x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e := Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  let A := (metricCov (Diffeomorph.pullbackMetricCross g Φ) X x).toLinearMap
  let B := (metricCov g (pushFwdSectionCross Φ X) (Φ x)).toLinearMap
  have he : B = e.toLinearEquiv.conj A := by
    ext v
    have h := metricCov_pullbackCross g Φ X x (e.symm v)
    change e (A (e.symm v)) = B (e (e.symm v)) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  change LinearMap.trace ℝ (TangentSpace I x) A = LinearMap.trace ℝ (TangentSpace J (Φ x)) B
  rw [he, LinearMap.trace_conj']

theorem divergence_metricCov_restrictOpen [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : U) :
    divergence (metricCov (g.restrictOpen U)) (restrictOpenTangentSection U X) x =
      divergence (metricCov g) X x.1 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have he : metricCov (g.restrictOpen U) (restrictOpenTangentSection U X) x = metricCov g X x.1 := by
    ext v
    exact metricCov_restrictOpen_globalSection g U X x v
  change LinearMap.trace ℝ E _ = LinearMap.trace ℝ E _
  rw [he]

end

end DifferentialGeometry.Geometry.Operator
