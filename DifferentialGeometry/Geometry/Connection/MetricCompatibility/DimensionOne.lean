import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem IsMetricCompatibleOn.covariantDerivative_eq_smul_of_finrank_eq_one
    {cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    {g : SmoothRiemannianMetric I M} {s : Set M}
    (hcov : IsMetricCompatibleOn cov g s) {x : M} (hx : x ∈ s)
    (hdim : Module.finrank ℝ E = 1) {e : ∀ x : M, TangentSpace I x}
    (he : MDiffAt (T% e) x) (hne : e x ≠ 0) (v : TangentSpace I x) :
    cov e x v =
      ((show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => g.inner y (e y) (e y)) x v) /
        (2 * g.inner x (e x) (e x))) • e x := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank ℝ (TangentSpace I x) = 1 from hdim) hne (cov e x v)
  have hmetric := hcov.apply he he hx v
  rw [← hc, g.symm x (e x) (c • e x)] at hmetric
  simp only [map_smul, smul_apply, smul_eq_mul] at hmetric
  have hmetric' :
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => g.inner y (e y) (e y)) x v) =
        c * g.inner x (e x) (e x) + c * g.inner x (e x) (e x) := hmetric
  have hq : g.inner x (e x) (e x) ≠ 0 := (g.pos x (e x) hne).ne'
  rw [← hc]
  congr 1
  apply (eq_div_iff (mul_ne_zero (by norm_num) hq)).2
  rw [hmetric']
  ring

theorem IsMetricCompatible.covariantDerivative_eq_smul_of_finrank_eq_one
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : SmoothRiemannianMetric I M} (hcov : IsMetricCompatible cov g)
    (hdim : Module.finrank ℝ E = 1) {e : ∀ x : M, TangentSpace I x} {x : M}
    (he : MDiffAt (T% e) x) (hne : e x ≠ 0) (v : TangentSpace I x) :
    cov e x v =
      ((show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => g.inner y (e y) (e y)) x v) /
        (2 * g.inner x (e x) (e x))) • e x := by
  exact IsMetricCompatibleOn.covariantDerivative_eq_smul_of_finrank_eq_one
    hcov.toIsMetricCompatibleOn (s := Set.univ) (by trivial) hdim he hne v

end DifferentialGeometry.Geometry.Connection
