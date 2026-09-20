import DifferentialGeometry.Geometry.Operator.Gradient.QuadraticForm
import DifferentialGeometry.Analysis.Normed.Matrix.WeightedInverseCovector
import DifferentialGeometry.Analysis.Normed.Matrix.InverseCovector
import DifferentialGeometry.Geometry.Measure.Chart.GramOperator

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Curvature

open Geometry.Operator Integral.Measure Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private def gramMatrixCLM : (E →L[ℝ] E) →L[ℝ]
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (innerSLFlip ℝ (chartModelBasis E j)).comp
      (ContinuousLinearMap.apply ℝ E (chartModelBasis E i))

private theorem gramMatrixCLM_chartGramOp {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M) (p : ℝ × E) :
    gramMatrixCLM (chartGramOp G alpha p) =
      chartGramMatrix (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) := by
  ext i j
  change inner ℝ (chartGramOp G alpha p (chartModelBasis E i)) (chartModelBasis E j) = _
  rw [chartGramOp_inner]
  exact (Tensor.Tensor0SRiemannian.chartGramMatrix_eq_innerJinv
    (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) i j).symm

private theorem weightedInvCovectorBilin_chartGramOp {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (alpha : M) (p : ℝ × E) (a : ℝ) :
    Matrix.weightedInvCovectorBilin (chartModelBasis E)
        (a, gramMatrixCLM (chartGramOp G alpha p)) =
      (a * chartDensity (G.metric p.1) alpha ((extChartAt I alpha).symm p.2)) •
        chartGradientBilin (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) := by
  rw [gramMatrixCLM_chartGramOp]
  rfl

theorem continuousOn_chartDensity_smul_chartGradientBilin {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    {S : Set (ℝ × E)}
    (hchart : ∀ p ∈ S, p.2 ∈ (extChartAt I alpha).target)
    (hG : ContinuousOn (chartGramOp G alpha) S)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w S) :
    ContinuousOn
      (fun p => (w p * chartDensity (G.metric p.1) alpha
        ((extChartAt I alpha).symm p.2)) •
        chartGradientBilin (G.metric p.1) alpha ((extChartAt I alpha).symm p.2)) S := by
  have hpair : ContinuousOn
      (fun p => (w p, gramMatrixCLM (chartGramOp G alpha p))) S :=
    hw.prodMk (gramMatrixCLM.continuous.comp_continuousOn hG)
  intro p hp
  have hdet : (gramMatrixCLM (chartGramOp G alpha p)).det ≠ 0 := by
    rw [gramMatrixCLM_chartGramOp]
    exact (chartGramMatrix_det_pos (G.metric p.1) alpha
      (extChartAt_symm_mem_trivializationAt_baseSet alpha (hchart p hp))).ne'
  have h := (Matrix.continuousAt_weightedInvCovectorBilin
    (chartModelBasis E) hdet).comp_continuousWithinAt (hpair p hp)
  simpa only [Function.comp_def, weightedInvCovectorBilin_chartGramOp] using h

theorem tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
    {ι : Type*} {l : Filter ι} {D D' : RealTimeInterval}
    (G : ι → MetricConnectionFamilyOn (I := I) (M := M) D)
    (G₀ : MetricConnectionFamilyOn (I := I) (M := M) D') (alpha : M)
    {S : Set (ℝ × E)} (hS : IsCompact S)
    (hchart : ∀ p ∈ S, p.2 ∈ (extChartAt I alpha).target)
    (hG₀ : ContinuousOn (chartGramOp G₀ alpha) S)
    (hG : TendstoUniformlyOn (fun k => chartGramOp (G k) alpha)
      (chartGramOp G₀ alpha) l S)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w S) :
    TendstoUniformlyOn
      (fun k p => (w p * chartDensity ((G k).metric p.1) alpha
        ((extChartAt I alpha).symm p.2)) •
        chartGradientBilin ((G k).metric p.1) alpha ((extChartAt I alpha).symm p.2))
      (fun p => (w p * chartDensity (G₀.metric p.1) alpha
        ((extChartAt I alpha).symm p.2)) •
        chartGradientBilin (G₀.metric p.1) alpha ((extChartAt I alpha).symm p.2)) l S := by
  have hA : TendstoUniformlyOn
      (fun k p => gramMatrixCLM (chartGramOp (G k) alpha p))
      (fun p => gramMatrixCLM (chartGramOp G₀ alpha p)) l S :=
    (gramMatrixCLM (E := E)).uniformContinuous.comp_tendstoUniformlyOn hG
  have hAc : ContinuousOn (fun p => gramMatrixCLM (chartGramOp G₀ alpha p)) S :=
    gramMatrixCLM.continuous.comp_continuousOn hG₀
  have hwlim : TendstoUniformlyOn (fun _ : ι => w) w l S := by
    intro V hV
    exact Eventually.of_forall fun _ p _ => refl_mem_uniformity hV
  have hpair : TendstoUniformlyOn
      (fun k p => (w p, gramMatrixCLM (chartGramOp (G k) alpha p)))
      (fun p => (w p, gramMatrixCLM (chartGramOp G₀ alpha p))) l S :=
    fun V hV => ((hwlim.prodMk hA) V hV).diag_of_prod
  have hQ := hpair.comp_continuousAt_of_isCompact_image
    (hS.image_of_continuousOn (hw.prodMk hAc))
    (g := Matrix.weightedInvCovectorBilin (chartModelBasis E)) ?_
  · simpa only [weightedInvCovectorBilin_chartGramOp] using hQ
  · rintro _ ⟨p, hp, rfl⟩
    apply Matrix.continuousAt_weightedInvCovectorBilin
    change (gramMatrixCLM (chartGramOp G₀ alpha p)).det ≠ 0
    rw [gramMatrixCLM_chartGramOp]
    exact (chartGramMatrix_det_pos (G₀.metric p.1) alpha
      (extChartAt_symm_mem_trivializationAt_baseSet alpha (hchart p hp))).ne'

private theorem smul_covectorBilin_inv_chartGramOp {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (alpha : M) (p : ℝ × E) (a : ℝ) :
    a • Matrix.covectorBilin (chartModelBasis E) (gramMatrixCLM (chartGramOp G alpha p))⁻¹ =
      a • chartGradientBilin (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) := by
  rw [gramMatrixCLM_chartGramOp]
  rfl

theorem continuousOn_smul_chartGradientBilin {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    {S : Set (ℝ × E)}
    (hchart : ∀ p ∈ S, p.2 ∈ (extChartAt I alpha).target)
    (hG : ContinuousOn (chartGramOp G alpha) S)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w S) :
    ContinuousOn
      (fun p => w p •
        chartGradientBilin (G.metric p.1) alpha ((extChartAt I alpha).symm p.2)) S := by
  have hpair : ContinuousOn
      (fun p => (w p, gramMatrixCLM (chartGramOp G alpha p))) S :=
    hw.prodMk (gramMatrixCLM.continuous.comp_continuousOn hG)
  intro p hp
  have hdet : (gramMatrixCLM (chartGramOp G alpha p)).det ≠ 0 := by
    rw [gramMatrixCLM_chartGramOp]
    exact (chartGramMatrix_det_pos (G.metric p.1) alpha
      (extChartAt_symm_mem_trivializationAt_baseSet alpha (hchart p hp))).ne'
  have h := (Matrix.continuousAt_smul_covectorBilin_inv
    (chartModelBasis E) hdet).comp_continuousWithinAt (hpair p hp)
  simpa only [Function.comp_def, smul_covectorBilin_inv_chartGramOp] using h

theorem tendstoUniformlyOn_smul_chartGradientBilin
    {ι : Type*} {l : Filter ι} {D D' : RealTimeInterval}
    (G : ι → MetricConnectionFamilyOn (I := I) (M := M) D)
    (G₀ : MetricConnectionFamilyOn (I := I) (M := M) D') (alpha : M)
    {S : Set (ℝ × E)} (hS : IsCompact S)
    (hchart : ∀ p ∈ S, p.2 ∈ (extChartAt I alpha).target)
    (hG₀ : ContinuousOn (chartGramOp G₀ alpha) S)
    (hG : TendstoUniformlyOn (fun k => chartGramOp (G k) alpha)
      (chartGramOp G₀ alpha) l S)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w S) :
    TendstoUniformlyOn
      (fun k p => w p •
        chartGradientBilin ((G k).metric p.1) alpha ((extChartAt I alpha).symm p.2))
      (fun p => w p •
        chartGradientBilin (G₀.metric p.1) alpha ((extChartAt I alpha).symm p.2)) l S := by
  have hA : TendstoUniformlyOn
      (fun k p => gramMatrixCLM (chartGramOp (G k) alpha p))
      (fun p => gramMatrixCLM (chartGramOp G₀ alpha p)) l S :=
    (gramMatrixCLM (E := E)).uniformContinuous.comp_tendstoUniformlyOn hG
  have hAc : ContinuousOn (fun p => gramMatrixCLM (chartGramOp G₀ alpha p)) S :=
    gramMatrixCLM.continuous.comp_continuousOn hG₀
  have hwlim : TendstoUniformlyOn (fun _ : ι => w) w l S := by
    intro V hV
    exact Eventually.of_forall fun _ p _ => refl_mem_uniformity hV
  have hpair : TendstoUniformlyOn
      (fun k p => (w p, gramMatrixCLM (chartGramOp (G k) alpha p)))
      (fun p => (w p, gramMatrixCLM (chartGramOp G₀ alpha p))) l S :=
    fun V hV => ((hwlim.prodMk hA) V hV).diag_of_prod
  have hQ := hpair.smul_covectorBilin_inv (chartModelBasis E)
    (hS.image_of_continuousOn (hw.prodMk hAc)) ?_
  · simpa only [smul_covectorBilin_inv_chartGramOp] using hQ
  · intro p hp
    change (gramMatrixCLM (chartGramOp G₀ alpha p)).det ≠ 0
    rw [gramMatrixCLM_chartGramOp]
    exact (chartGramMatrix_det_pos (G₀.metric p.1) alpha
      (extChartAt_symm_mem_trivializationAt_baseSet alpha (hchart p hp))).ne'

end DifferentialGeometry.Geometry.Curvature
