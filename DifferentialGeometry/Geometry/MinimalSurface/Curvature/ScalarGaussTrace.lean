import DifferentialGeometry.Geometry.Submanifold.Gauss
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold BigOperators

namespace DifferentialGeometry.Geometry

open Curvature

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The ambient Ricci trace on a minimal tangent plane, with every curvature and
second fundamental form computed from the given isometric immersion. -/
theorem ricci_tangent_trace_eq_scalar_gauss_of_zero_mean_curvature
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {f : N → M}
    (hf : ContMDiff IN I ∞ f)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (f x) (mfderiv IN I f x u) (mfderiv IN I f x v) = gN.inner x u v)
    (x : N) (hdim : Module.finrank ℝ (TangentSpace I (f x)) = 3)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace IN x))
    (hb : ∀ i j, gN.inner x (b i) (b j) = if i = j then 1 else 0)
    (hmean : ∑ i : Fin 2, secondFundamentalFormAmbientAt gN gM f x (b i) (b i) = 0) :
    (∑ i : Fin 2, metricRicciAt gM (f x)
      (vec2 (mfderiv IN I f x (b i)) (mfderiv IN I f x (b i)))) =
      metricScalarAt gM (f x) / 2 +
        metricRm04StandardAt gN x (b 0) (b 1) (b 1) (b 0) +
        (∑ i : Fin 2, ∑ j : Fin 2,
          gM.inner (f x) (secondFundamentalFormAmbientAt gN gM f x (b i) (b j))
            (secondFundamentalFormAmbientAt gN gM f x (b i) (b j))) / 2 := by
  have hgauss := gauss_equation_of_inner_map hf hmetric x (b 0) (b 1) (b 1) (b 0)
  have hric := metricRm04StdAt_eq_ricci3 gM (f x) hdim
    (mfderiv IN I f x (b 0)) (mfderiv IN I f x (b 1))
    (mfderiv IN I f x (b 1)) (mfderiv IN I f x (b 0))
  simp [hmetric, hb] at hric
  have hsym := secondFundamentalFormAmbientAt_symmetric gN gM
    (hf.contMDiffAt.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)) (b 1) (b 0)
  have hdiag : secondFundamentalFormAmbientAt gN gM f x (b 1) (b 1) =
      -secondFundamentalFormAmbientAt gN gM f x (b 0) (b 0) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Fin.sum_univ_two, add_comm] using hmean
  simp only [Fin.sum_univ_two, hsym, hdiag, map_neg, neg_apply, neg_neg] at hgauss ⊢
  simp only [metricRm04StandardAt_apply] at hgauss ⊢
  linarith

/-- Dropping the nonnegative squared second fundamental form gives the pointwise
curvature estimate used in the Ricci-flow area inequality. -/
theorem scalar_gauss_le_ricci_tangent_trace_of_zero_mean_curvature
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {f : N → M}
    (hf : ContMDiff IN I ∞ f)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (f x) (mfderiv IN I f x u) (mfderiv IN I f x v) = gN.inner x u v)
    (x : N) (hdim : Module.finrank ℝ (TangentSpace I (f x)) = 3)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace IN x))
    (hb : ∀ i j, gN.inner x (b i) (b j) = if i = j then 1 else 0)
    (hmean : ∑ i : Fin 2, secondFundamentalFormAmbientAt gN gM f x (b i) (b i) = 0) :
    metricScalarAt gM (f x) / 2 + metricRm04StandardAt gN x (b 0) (b 1) (b 1) (b 0) ≤
      ∑ i : Fin 2, metricRicciAt gM (f x)
        (vec2 (mfderiv IN I f x (b i)) (mfderiv IN I f x (b i))) := by
  rw [ricci_tangent_trace_eq_scalar_gauss_of_zero_mean_curvature hf hmetric x hdim b hb hmean]
  have hnonneg : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      gM.inner (f x) (secondFundamentalFormAmbientAt gN gM f x (b i) (b j))
        (secondFundamentalFormAmbientAt gN gM f x (b i) (b j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      metric_inner_self_nonneg gM (f x) _
  linarith

end DifferentialGeometry.Geometry
