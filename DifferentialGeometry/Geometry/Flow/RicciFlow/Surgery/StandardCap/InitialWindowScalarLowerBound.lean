import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLowerBound
set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff

open Manifold DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
open private window_scalar_eq_of_scaled_inner from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
theorem exists_uniform_window_scalar_lower_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ ε₀ → 2 ≤ m → ∀ x : standardCapWindow D, ‖x.val‖ < D →
          1 / 2 ≤ metricScalarAt w.windowMetric x := by
  obtain ⟨ε₀, hε₀, hbound⟩ :=
    exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens 0 le_rfl (by norm_num)
  obtain ⟨Q⟩ := standard_solution_nonempty
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ε w hε hm x hx
  apply hbound (standardCapWindow D) w.windowMetric Q 0 ⟨le_rfl, le_rfl⟩ x
  intro j hj
  rw [Q.val.initial]
  have he := w.properties.window_close
  change metricDerivENormSupOn
    {y : standardCapWindow D | (riemannianEDistOf metric 0 y.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at he
  simp only [distance_zero] at he
  exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ he (hj.trans hm) hx).le.trans hε

theorem exists_uniform_window_image_scalar_lower_bound_of_scaled_pullback :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ ε₀ → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          q / 2 ≤ metricScalarAt h (J x) := by
  obtain ⟨ε₀, hε₀, hbound⟩ := exists_uniform_window_scalar_lower_bound
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H M N _ _ _ _ _ I _ _ _ _ _ _ _ _ _ g x₀ δ k d A hA D m ε w hε hm
    h J hJ q hq hinner x hx
  have hb := hbound w hε hm x hx
  rw [window_scalar_eq_of_scaled_inner w.windowMetric h J hJ hq hinner x] at hb
  have hh := (le_div_iff₀ hq).mp hb
  linarith

theorem exists_uniform_window_scale_bound_of_rm_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ ε₀ → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ (x : standardCapWindow D), ‖x.val‖ < D → ∀ r : ℝ,
          r ^ 4 * normSq0S h (J x) 4 (metricRm04At h (J x)) ≤ 1 →
          q * r ^ 2 ≤ 18 := by
  obtain ⟨ε₀, hε₀, hfloor⟩ :=
    exists_uniform_window_image_scalar_lower_bound_of_scaled_pullback
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H M N _ _ _ _ _ I _ _ _ _ _ _ _ _ _ g x₀ δ k d A hA D m ε w hε hm
    h J hJ q hq hinner x hx r hrm
  have hscalar := (hfloor w hε hm h J hJ q hq hinner x hx).trans (le_abs_self _)
  have hsq := sq_mul_scalar_abs_le_of_rm_bound h (J x) hrm
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hsq
  have hscaled := mul_le_mul_of_nonneg_right hscalar (sq_nonneg r)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at hsq
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
