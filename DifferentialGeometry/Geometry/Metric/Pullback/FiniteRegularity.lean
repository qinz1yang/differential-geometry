import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem exists_pullback_metric_of_finite_diffeomorph
    (K s r : ℕ) (hrK : r ≤ K) (hrs : r + 1 ≤ s)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N (s : WithTop ℕ∞)) :
    ∃ h : ContMDiffRiemannianMetric I (r : WithTop ℕ∞)
        E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  exact exists_pullback_metric_of_finite_diffeomorph_proved K s r hrK hrs g f

theorem exists_pullback_metric_of_diffeomorph_one_order_higher
    (K : ℕ)
    (g : ContMDiffRiemannianMetric J (K : WithTop ℕ∞) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N ((K + 1 : ℕ) : WithTop ℕ∞)) :
    ∃ h : ContMDiffRiemannianMetric I (K : WithTop ℕ∞) E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  exact exists_pullback_metric_of_finite_diffeomorph K (K + 1) K le_rfl le_rfl g f

theorem exists_pullback_metric_of_diffeomorph_three_orders_lower
    (m : ℕ) (hm : 4 ≤ m)
    (g : ContMDiffRiemannianMetric J (m : WithTop ℕ∞)
      F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N ((m - 3 : ℕ) : WithTop ℕ∞)) :
    ∃ h : ContMDiffRiemannianMetric I ((m - 4 : ℕ) : WithTop ℕ∞)
        E (TangentSpace I : M → Type _),
      ∀ (x : M) (v w : TangentSpace I x),
        h.inner x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  exact exists_pullback_metric_of_finite_diffeomorph m (m - 3) (m - 4)
    (by omega) (by omega) g f

end DifferentialGeometry.Geometry
