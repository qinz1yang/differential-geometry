import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CoefficientChart

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.Analysis (coefficientGram coefficientGram_apply coefficientRm04
  coefficientSectional coefficientSectional_def contDiffOn_coefficientGram jet2 jetRm04
  jet2_congr_of_eventuallyEq)
open DifferentialGeometry.Geometry.Curvature (chartGramPi chartGramPi_apply
  sectionalCurvatureNumerator_eq_jetRm04)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis chartBasisVecFiber
  chartGramMatrix_apply)
open DifferentialGeometry.Geometry.Operator (chartGramOnE_def)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartGramPi_eq_coefficientGram_of_mem
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ (extChartAt I p).target) :
    chartGramPi g p y = coefficientGram
      (DifferentialGeometry.Geometry.pullbackMetricCoefficients g (extChartAt I p).symm) y := by
  have hx : (extChartAt I p).symm y ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hy
  have ht : (trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm y := by
    rw [TangentBundle.symmL_trivializationAt hx]
    rw [(extChartAt I p).right_inv hy, I.range_eq_univ, mfderivWithin_univ]
  funext i j
  rw [chartGramPi_apply, chartGramOnE_def, chartGramMatrix_apply, coefficientGram_apply]
  change (g.inner ((extChartAt I p).symm y) : E →L[ℝ] E →L[ℝ] ℝ)
      ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y)
        (chartModelBasis E i))
      ((trivializationAt E (TangentSpace I) p).symmL ℝ ((extChartAt I p).symm y)
        (chartModelBasis E j)) = _
  rw [ht]
  rfl

theorem sectionalCurvature_eq_smooth
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    g.sectionalCurvature p v w =
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature g p v w := by
  let φ := DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ p
  let b := DifferentialGeometry.Geometry.pullbackMetricCoefficients g (extChartAt I p).symm
  let z := extChartAt I p p
  have hz : z ∈ φ.target := φ.map_source (mem_extChartAt_source p)
  have hreg : ContDiffOn ℝ 2 b φ.target :=
    (DifferentialGeometry.Geometry.contDiffOn_pullback_metric_coefficients g
      φ.open_target φ.contMDiffOn_invFun).of_le (by simp)
  have hcgU : ContDiffOn ℝ 2 (coefficientGram b) φ.target := contDiffOn_coefficientGram hreg
  have hcg : ContDiffAt ℝ 2 (coefficientGram b) z :=
    hcgU.contDiffAt (φ.open_target.mem_nhds hz)
  have heq : chartGramPi g p =ᶠ[𝓝 z] coefficientGram b := by
    filter_upwards [φ.open_target.mem_nhds hz] with y hy
    exact chartGramPi_eq_coefficientGram_of_mem g p hy
  have hG : DifferentiableAt ℝ (chartGramPi g p) z :=
    (hcg.differentiableAt (by norm_num)).congr_of_eventuallyEq heq
  have hG1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (chartGramPi g p) y := by
    filter_upwards [heq.eventuallyEq_nhds, φ.open_target.mem_nhds hz] with y hy hys
    exact ((hcgU.contDiffAt (φ.open_target.mem_nhds hys)).differentiableAt
      (by norm_num)).congr_of_eventuallyEq hy
  have heq1 : (fun y => fderiv ℝ (chartGramPi g p) y) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (coefficientGram b) y) :=
    heq.eventuallyEq_nhds.mono fun _ hy => hy.fderiv_eq
  have hG2 : DifferentiableAt ℝ (fun y => fderiv ℝ (chartGramPi g p) y) z :=
    ((hcg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).congr_of_eventuallyEq heq1
  have hint : z ∈ interior (extChartAt I p).target :=
    mem_interior_iff_mem_nhds.mpr (φ.open_target.mem_nhds hz)
  have hj : jet2 (chartGramPi g p) z = jet2 (coefficientGram b) z :=
    jet2_congr_of_eventuallyEq heq
  let v₀ : E := v
  let w₀ : E := w
  have hnum : DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator g p v w =
      coefficientRm04 b z v₀ w₀ w₀ v₀ := by
    exact (sectionalCurvatureNumerator_eq_jetRm04 g p v w hint hG hG1 hG2).trans
      (congrArg (fun q => jetRm04 q v₀ w₀ w₀ v₀) hj)
  have hid (a : E) : (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z : E →L[ℝ] E) a = a := by
    have h := mfderivWithin_range_extChartAt_symm (I := I) (x := p)
    rw [I.range_eq_univ, mfderivWithin_univ] at h
    exact congrArg (fun L => L a) h
  have hread (a c : E) : b z a c = g.inner p a c := by
    calc
      b z a c = (g.inner ((extChartAt I p).symm z) : E →L[ℝ] E →L[ℝ] ℝ) a c :=
        congrArg₂ (fun u t : E =>
          (g.inner ((extChartAt I p).symm z) : E →L[ℝ] E →L[ℝ] ℝ) u t) (hid a) (hid c)
      _ = g.inner p a c := congrArg
        (fun q : M => (g.inner q : E →L[ℝ] E →L[ℝ] ℝ) a c)
        ((extChartAt I p).left_inv (mem_extChartAt_source p))
  have hden : b z v₀ v₀ * b z w₀ w₀ - (b z v₀ w₀) ^ 2 =
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator g p v w := by
    exact congrArg₂ (fun a c : ℝ => a - c ^ 2)
      (congrArg₂ (fun a c : ℝ => a * c) (hread v₀ v₀) (hread w₀ w₀)) (hread v₀ w₀)
  unfold sectionalCurvature
  simp only [mfderiv_extChartAt_self]
  change coefficientRm04 b z v₀ w₀ w₀ v₀ /
      (b z v₀ v₀ * b z w₀ w₀ - (b z v₀ w₀) ^ 2) =
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator g p v w /
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator g p v w
  exact congrArg₂ (fun a c : ℝ => a / c) hnum.symm hden

end Bundle.ContMDiffRiemannianMetric
