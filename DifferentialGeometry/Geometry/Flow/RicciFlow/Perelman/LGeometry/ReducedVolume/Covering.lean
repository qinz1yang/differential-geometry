import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Covering
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Covering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measurability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem exists_redVolume_covering_lower_bound_of_compact
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (k : ℕ) (hcard : ∀ y : N, {x : M | p x = y}.encard = (k : ℕ∞))
    (T : ℝ) (hregular : Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : ℝ, 1 < tau →
      ENNReal.ofReal (Real.exp (-C / (2 * Real.sqrt tau))) *
          ((k : ℝ≥0∞) * redVolume S T (p x) tau) ≤
        redVolume (S.localPullback p hp) T x tau := by
  obtain ⟨C, hC, hbound⟩ := exists_lCost_covering_sub_le_of_compact
    S hS p hp hcover T hregular hscalar x
  refine ⟨C, hC, ?_⟩
  intro tau htau
  have htau0 : 0 < tau := zero_lt_one.trans htau
  have hden : 0 < 2 * Real.sqrt tau := mul_pos (by norm_num) (Real.sqrt_pos.mpr htau0)
  have hpoint (y : M) :
      Real.exp (-C / (2 * Real.sqrt tau)) * redDensity S T (p x) (p y) tau ≤
        redDensity (S.localPullback p hp) T x y tau := by
    have hcost := (hbound y tau htau).2
    have hred : redLength (S.localPullback p hp) T x y tau ≤
        redLength S T (p x) (p y) tau + C / (2 * Real.sqrt tau) := by
      unfold redLength
      rw [← add_div]
      exact (div_le_div_iff_of_pos_right hden).mpr (by linarith)
    unfold redDensity
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hmeas : Measurable (fun y : N => ENNReal.ofReal (redDensity S T (p x) y tau)) :=
    ENNReal.measurable_ofReal.comp (measurable_redDensity_of_compact S hS T (p x) tau
      htau0 (fun _ ht => hregular ht.2))
  have hmap := riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    (localPullMetric (S.base.metric (T - tau)) p hp) (S.base.metric (T - tau)) hp rfl k hcard
  have hintegral : (∫⁻ y : M, ENNReal.ofReal (redDensity S T (p x) (p y) tau)
      ∂riemannianVolumeMeasure I M ((S.localPullback p hp).base.metric (T - tau))) =
      (k : ℝ≥0∞) * redVolume S T (p x) tau := by
    rw [SolutionOn.localPullback_metric,
      ← lintegral_map hmeas hp.contMDiff.continuous.measurable, hmap,
      lintegral_smul_measure]
    rfl
  rw [← hintegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  dsimp only
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hpoint y)

end DifferentialGeometry.PDE.RicciFlow.Perelman
