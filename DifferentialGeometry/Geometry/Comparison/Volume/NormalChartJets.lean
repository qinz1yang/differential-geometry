import DifferentialGeometry.Analysis.Calculus.Matrix.Determinant
import DifferentialGeometry.Geometry.Comparison.Volume.NormalGramJets
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion

noncomputable section

open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open NormalCoordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)] [T2Space M]

omit [T2Space M] in
private theorem normalGram_det_pos_zero (g : SmoothRiemannianMetric I M) (p : M) :
    0 < (normalGramMatrix g p 0).det :=
  paramGramMatrix_det_pos g (expMapDiffeo g p) (zero_mem_expMapDiffeo_source g p)

theorem fderiv_normalChartDensity_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    fderiv ℝ (normalChartDensity g p) 0 = 0 := by
  have hG := (contDiffAt_normalGramMatrix_zero g p).differentiableAt (by simp)
  have houter := (Matrix.contDiff_det (𝕜 := ℝ) (n := 1)).contDiffAt.sqrt
    (normalGram_det_pos_zero g p).ne'
  have hchain := houter.differentiableAt (by simp) |>.hasFDerivAt.comp 0 hG.hasFDerivAt
  refine hchain.fderiv.trans ?_
  let D := fderiv ℝ (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
    Real.sqrt A.det) (normalGramMatrix g p 0)
  exact (congrArg D.comp (fderiv_normalGram_zero g p)).trans (ContinuousLinearMap.comp_zero D)

omit [T2Space M] in
private theorem normalGram_inverse_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    Tensor0SBundle.MetricInverseInBasis g p (chartModelBasis E)
      (fun i j => (normalGramMatrix g p 0)⁻¹ i j) := by
  have hunit := (normalGram_det_pos_zero g p).ne'.isUnit
  intro i j
  constructor
  · have h := congrArg (fun A => A i j) (Matrix.nonsing_inv_mul (normalGramMatrix g p 0) hunit)
    simp only [Matrix.mul_apply, Matrix.one_apply, normalGram_zero] at h
    exact h
  · have h := congrArg (fun A => A i j) (Matrix.mul_nonsing_inv (normalGramMatrix g p 0) hunit)
    simp only [Matrix.mul_apply, Matrix.one_apply, normalGram_zero] at h
    exact h

omit [T2Space M] in
private theorem contDiffAt_normalGram_radial
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    ContDiffAt ℝ 2 (fun t : ℝ => normalGramMatrix g p (t • x)) 0 := by
  have hG : ContDiffAt ℝ 2 (normalGramMatrix g p) ((0 : ℝ) • x) := by
    rw [zero_smul]
    exact (contDiffAt_normalGramMatrix_zero g p).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact hG.comp 0 (contDiffAt_id.smul contDiffAt_const)

private theorem iteratedDeriv_two_normalGram_radial_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x)) 0 i j =
      -(2 / 3 : ℝ) * g.inner p
        (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x)
        (chartModelBasis E j) := by
  let P : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →L[ℝ]
      (Fin (Module.finrank ℝ E) → ℝ) := ContinuousLinearMap.proj i
  let Q : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let A := Q.comp P
  have hA := A.iteratedFDeriv_comp_left (contDiffAt_normalGram_radial g p x) (i := 2) le_rfl
  have h := congrArg (fun B => B (fun _ : Fin 2 => (1 : ℝ))) hA
  have heq : iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x) i j) 0 =
      iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x)) 0 i j := by
    exact h
  exact heq.symm.trans (second_derivative_normalGram_radial_zero g p x i j)

private theorem trace_inv_normalGram_mul_second_derivative
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    Matrix.trace ((normalGramMatrix g p 0)⁻¹ *
      iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x)) 0) =
      -(2 / 3 : ℝ) * Curvature.ricciTensor g p x x := by
  have htrace := Tensor0SBundle.linearMap_trace_eq_sum_inv_inner_apply g p (chartModelBasis E)
    (fun i j => (normalGramMatrix g p 0)⁻¹ i j) (normalGram_inverse_zero g p)
    (Curvature.ricciEndo g p x x)
  have hricci : Curvature.ricciTensor g p x x =
      ∑ i, ∑ j, (normalGramMatrix g p 0)⁻¹ i j *
        g.inner p (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x)
          (chartModelBasis E j) := by
    exact (Curvature.ricciTensor_apply g p x x).trans htrace
  rw [hricci, Matrix.trace, Finset.mul_sum]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_two_normalGram_radial_apply]
  have hsymm := (Curvature.riemannOp_diag_symm g p x (chartModelBasis E j)
    (chartModelBasis E i)).trans
    (g.symm p (chartModelBasis E j)
      (Curvature.riemannOp (Connection.LeviCivita g) p (chartModelBasis E i) x x))
  rw [hsymm]
  ring

theorem second_derivative_normalChartDensity_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    iteratedDeriv 2 (fun t : ℝ => normalChartDensity g p (t • x)) 0 =
      -(normalChartDensity g p 0 / 3) * Curvature.ricciTensor g p x x := by
  have hG := (contDiffAt_normalGramMatrix_zero g p).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => t • x) x 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const x).congr_deriv (one_smul ℝ x)
  have hcurve := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hzero : deriv (fun t : ℝ => normalGramMatrix g p (t • x)) 0 = 0 :=
    hcurve.deriv.trans (congrArg (fun L => L x) (fderiv_normalGram_zero g p))
  have hpos : 0 < (normalGramMatrix g p ((0 : ℝ) • x)).det := by
    rw [zero_smul]
    exact normalGram_det_pos_zero g p
  have h := Matrix.iteratedDeriv_two_sqrt_det_of_deriv_eq_zero
    (contDiffAt_normalGram_radial g p x) hzero hpos
  refine h.trans ?_
  have hbase := congrArg (fun y : E => (1 / 2 : ℝ) *
    Matrix.trace ((normalGramMatrix g p y)⁻¹ *
      iteratedDeriv 2 (fun t : ℝ => normalGramMatrix g p (t • x)) 0) *
      Real.sqrt (normalGramMatrix g p y).det) (zero_smul ℝ x)
  refine hbase.trans ?_
  rw [trace_inv_normalGram_mul_second_derivative]
  change (1 / 2 : ℝ) * (-(2 / 3 : ℝ) * Curvature.ricciTensor g p x x) *
    normalChartDensity g p 0 = _
  ring

theorem iteratedFDeriv_two_normalChartDensity_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    iteratedFDeriv ℝ 2 (normalChartDensity g p) 0 (fun _ => x) =
      -(normalChartDensity g p 0 / 3) * Curvature.ricciTensor g p x x := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  let U := Metric.ball (0 : E) (expMapC2Radius g p)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzero : L 0 ∈ U := by simpa [L, U] using expMapC2Radius_pos g p
  have hcomp := L.iteratedFDerivWithin_comp_right (contDiffOn_normalChartDensity g p)
    hU.uniqueDiffOn (hU.preimage L.continuous).uniqueDiffOn hzero (i := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [iteratedFDerivWithin_of_isOpen 2 (hU.preimage L.continuous) hzero,
    iteratedFDerivWithin_of_isOpen 2 hU hzero] at hcomp
  have h := congrArg (fun B => B (fun _ : Fin 2 => (1 : ℝ))) hcomp
  have heq : iteratedDeriv 2 (fun t : ℝ => normalChartDensity g p (t • x)) 0 =
      iteratedFDeriv ℝ 2 (normalChartDensity g p) 0 (fun _ => x) := by
    simpa only [iteratedDeriv_eq_iteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, zero_smul, one_smul,
      Function.comp_def, L] using h
  exact heq.symm.trans (second_derivative_normalChartDensity_radial_zero g p x)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
