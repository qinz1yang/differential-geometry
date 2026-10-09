import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeGrowth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

namespace SolutionOn

/-- The power-normalized total volume has the exact integrated scalar-deficit
derivative on each regular time of the original compact Ricci flow. -/
theorem hasDerivAt_rpow_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (α c : ℝ) {t : ℝ} (ht : t ∈ D.regular)
    (hpos : 0 < t + c) :
    HasDerivAt
      (fun s : ℝ => (s + c) ^ (-α) *
        (riemannianVolumeMeasure I M (S.family.metric s) univ).toReal)
      (-(t + c) ^ (-α) *
        ∫ x, (S.scalar t x + α / (t + c))
          ∂riemannianVolumeMeasure I M (S.family.metric t)) t := by
  let μ := riemannianVolumeMeasure I M (S.family.metric t)
  let : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (S.family.metric t)
  have hscalar : Integrable (S.scalar t) μ :=
    (metricScalar_smooth (S.family.metric t)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpower : HasDerivAt (fun s : ℝ => (s + c) ^ (-α))
      ((-α) * (t + c) ^ (-α - 1)) t := by
    simpa only [one_mul] using
      ((hasDerivAt_id' t).add_const c).rpow_const (p := -α) (Or.inl hpos.ne')
  have hproduct := hpower.mul (S.hasDerivAt_volume hS ht)
  refine hproduct.congr_deriv ?_
  change (-α) * (t + c) ^ (-α - 1) * (μ univ).toReal +
      (t + c) ^ (-α) * (-(∫ x, S.scalar t x ∂μ)) =
    -(t + c) ^ (-α) * ∫ x, (S.scalar t x + α / (t + c)) ∂μ
  rw [integral_add hscalar (integrable_const _), integral_const]
  simp only [smul_eq_mul, Measure.real_def, Real.rpow_sub_one hpos.ne']
  ring

/-- A scalar lower bound makes power-normalized total volume nonincreasing.
The scalar bound and evolution equation are needed only in the interval's
interior; actual volume continuity retains its closed endpoints. -/
theorem antitoneOn_rpow_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (α c : ℝ) {J : Set ℝ} (hJ : Convex ℝ J)
    (hcarrier : J ⊆ D.carrier) (hregular : interior J ⊆ D.regular)
    (hpos : ∀ t ∈ J, 0 < t + c)
    (hscalar : ∀ t ∈ interior J, ∀ x : M, -α / (t + c) ≤ S.scalar t x) :
    AntitoneOn
      (fun t : ℝ => (t + c) ^ (-α) *
        (riemannianVolumeMeasure I M (S.family.metric t) univ).toReal) J := by
  have hweight : ContinuousOn (fun t : ℝ => (t + c) ^ (-α)) J :=
    (continuous_id.add continuous_const).continuousOn.rpow_const
      (fun t ht => Or.inl (hpos t ht).ne')
  apply antitoneOn_of_hasDerivWithinAt_nonpos hJ
    (hweight.mul ((S.continuousOn_volume hS).mono hcarrier))
  · intro t ht
    exact (S.hasDerivAt_rpow_mul_volume hS α c (hregular ht)
      (hpos t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (Real.rpow_nonneg (hpos t (interior_subset ht)).le _)
    · apply integral_nonneg
      intro x
      change (0 : ℝ) ≤ S.scalar t x + α / (t + c)
      have hx := hscalar t ht x
      rw [neg_div] at hx
      linarith

end SolutionOn

end DifferentialGeometry.PDE.RicciFlow
