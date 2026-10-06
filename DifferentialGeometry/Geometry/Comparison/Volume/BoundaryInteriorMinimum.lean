import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorCurveLength
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

/-!
Actual original endpoint distance and unit speed imply minimum against every native competitor.
True-interior inclusion preserves the competitors' lengths; no native minimum is assumed.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorMinimum_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInterior_curve_minimizing (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorMinimum_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → U) (a b : ℝ), a ≤ b →
      (∀ t ∈ Ioo a b, k.inner (γ t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) = 1) →
      DifferentialGeometry.riemannianEDistOf g (γ a : M) (γ b : M) =
        ENNReal.ofReal (b - a) →
      ∀ η : ℝ → U, ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc a b) →
        η a = γ a → η b = γ b → arcLength k γ a b ≤ arcLength k η a b := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorMinimum_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ a b hab hunit hdist η hη hηa hηb
  have hlength : arcLength k γ a b = b - a := by
    unfold arcLength
    calc
      _ = ∫ _t in a..b, (1 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => by
          rw [hunit t ht, Real.sqrt_one])
      _ = b - a := by simp
  have hbound := (boundaryInterior_curve_length g η a b hab hη).2
  rw [hηa, hηb, hdist] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (DifferentialGeometry.Geometry.Riemannian.arcLength_nonneg k hab)).mp hbound
  exact hlength.le.trans hreal

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
