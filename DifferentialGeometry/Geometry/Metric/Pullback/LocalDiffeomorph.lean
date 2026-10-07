import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem exists_partialDiffeomorph_of_injOn_of_metric_lower [Nonempty M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I J ∞ f U)
    (hinj : Set.InjOn f U) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {c : M → ℝ} (hc : ∀ x ∈ U, 0 < c x)
    (hlower : ∀ x ∈ U, ∀ v : TangentSpace I x,
      c x * g.inner x v v ≤ h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) :
    ∃ Φ : PartialDiffeomorph I J M N ∞,
      Φ.source = U ∧ Φ.target = f '' U ∧ (Φ : M → N) = f := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn hU _ hinj
  apply hf.isLocalDiffeomorphOn_of_isInvertible_mfderiv hU (by simp)
  intro x hx
  have hi : Function.Injective (mfderiv I J f x) := by
    apply (injective_iff_map_eq_zero (mfderiv I J f x)).mpr
    intro v hv
    by_contra hne
    have hp := mul_pos (hc x hx) (g.pos x v hne)
    have hb := hlower x hx v
    rw [hv] at hb
    simp only [map_zero] at hb
    exact (not_le_of_gt hp) hb
  let A : E ≃L[ℝ] F :=
    ((mfderiv I J f x).toLinearMap.linearEquivOfInjective hi hdim).toContinuousLinearEquiv
  exact ⟨A, rfl⟩

end DifferentialGeometry.Geometry.Metric
