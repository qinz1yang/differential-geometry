import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

/-!
Actual true-interior curves preserve arc length under their original-manifold inclusion.
Original metric distance bounds every native competitor, using only genuine curve smoothness.
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

private theorem interiorCurveLength_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInterior_curve_length (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorCurveLength_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (η : ℝ → U) (a b : ℝ), a ≤ b →
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc a b) →
      arcLength k η a b = arcLength g (fun t => (η t : M)) a b ∧
        DifferentialGeometry.riemannianEDistOf g (η a : M) (η b : M) ≤
          ENNReal.ofReal (arcLength k η a b) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorCurveLength_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro η a b hab hη
  have hval : ContMDiff 𝓘(ℝ, E) I 1 (Subtype.val : U → M) :=
    (DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
      I ∞ interiorCurveLength_infty_ne_zero (M := M)).of_le (by simp)
  have hlength : arcLength k η a b = arcLength g (fun t => (η t : M)) a b := by
    unfold arcLength
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    have hηAt := hη.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hc := mfderiv_comp t
      ((hval.contMDiffAt (x := η t)).mdifferentiableAt (by norm_num))
      (hηAt.mdifferentiableAt (by norm_num))
    have hvelocity := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hc
    have hm := boundaryInteriorAtlasMetric_inner g (η t)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η t (1 : ℝ))
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η t (1 : ℝ))
    have hp := congrArg₂ (fun w z : E => g.inner (η t : M) w z) hvelocity hvelocity
    exact congrArg Real.sqrt (hm.trans hp.symm)
  refine ⟨hlength, ?_⟩
  have hdist := DifferentialGeometry.riemannianEDistOf_le_arcLength g hab
    (hval.comp_contMDiffOn hη)
  exact hdist.trans_eq (congrArg ENNReal.ofReal hlength.symm)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
