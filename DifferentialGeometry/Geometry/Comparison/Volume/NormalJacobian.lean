import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartJets

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

def normalJacobian (g : SmoothRiemannianMetric I M) (p : M) (v : E) : ℝ :=
  normalChartDensity g p v / normalChartDensity g p 0

private theorem normalChartDensity_pos_zero (g : SmoothRiemannianMetric I M) (p : M) :
    0 < normalChartDensity g p 0 :=
  paramDensity_pos g (expMapDiffeo g p) (zero_mem_expMapDiffeo_source g p)

theorem normalJacobian_zero (g : SmoothRiemannianMetric I M) (p : M) :
    normalJacobian g p 0 = 1 :=
  div_self (normalChartDensity_pos_zero g p).ne'

theorem normalJacobian_pos (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ (expMapDiffeo g p).source) : 0 < normalJacobian g p v :=
  div_pos (paramDensity_pos g (expMapDiffeo g p) hv) (normalChartDensity_pos_zero g p)

theorem contDiffOn_normalJacobian (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffOn ℝ ∞ (normalJacobian g p) (Metric.ball 0 (expMapC2Radius g p)) :=
  (contDiffOn_normalChartDensity g p).div_const (normalChartDensity g p 0)

theorem contDiffAt_normalJacobian_zero (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ ∞ (normalJacobian g p) 0 :=
  (contDiffAt_normalChartDensity_zero g p).div_const (normalChartDensity g p 0)

theorem normalJacobian_inv_sqrt_zero (g : SmoothRiemannianMetric I M) (p : M) :
    (Real.sqrt (normalJacobian g p 0))⁻¹ = 1 := by
  rw [normalJacobian_zero, Real.sqrt_one, inv_one]

theorem contDiffOn_normalJacobian_inv_sqrt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffOn ℝ ∞ (fun v => (Real.sqrt (normalJacobian g p v))⁻¹)
      (Metric.ball 0 (expMapC2Radius g p)) := by
  have hpos : ∀ v ∈ Metric.ball (0 : E) (expMapC2Radius g p), 0 < normalJacobian g p v :=
    fun v hv => normalJacobian_pos g p
      (mem_expMapDiffeo_source_of_norm_lt_radius g p (by simpa using hv))
  exact ((contDiffOn_normalJacobian g p).sqrt (fun v hv => (hpos v hv).ne')).inv
    (fun v hv => Real.sqrt_ne_zero'.mpr (hpos v hv))

theorem contDiffAt_normalJacobian_inv_sqrt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ ∞ (fun v => (Real.sqrt (normalJacobian g p v))⁻¹) 0 :=
  (contDiffOn_normalJacobian_inv_sqrt g p).contDiffAt
    (Metric.ball_mem_nhds 0 (expMapC2Radius_pos g p))

variable [T2Space M]

theorem fderiv_normalJacobian_zero (g : SmoothRiemannianMetric I M) (p : M) :
    fderiv ℝ (normalJacobian g p) 0 = 0 := by
  have hd := (contDiffAt_normalChartDensity_zero g p).differentiableAt (by simp)
  have h := hd.hasFDerivAt.mul_const (normalChartDensity g p 0)⁻¹
  change fderiv ℝ (fun v => normalChartDensity g p v * (normalChartDensity g p 0)⁻¹) 0 = 0
  refine h.fderiv.trans ?_
  rw [fderiv_normalChartDensity_zero]
  exact smul_zero _

theorem second_derivative_normalJacobian_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    iteratedDeriv 2 (fun t : ℝ => normalJacobian g p (t • x)) 0 =
      -(1 / 3 : ℝ) * Curvature.ricciTensor g p x x := by
  have h := iteratedDeriv_div_const (n := 2) (x := 0)
    (fun t : ℝ => normalChartDensity g p (t • x)) (normalChartDensity g p 0)
  refine h.trans ?_
  rw [second_derivative_normalChartDensity_radial_zero]
  let d : ℝ := normalChartDensity g p 0
  let r : ℝ := Curvature.ricciTensor g p x x
  change -(d / 3) * r / d = -(1 / 3 : ℝ) * r
  have hd : d ≠ 0 := (normalChartDensity_pos_zero g p).ne'
  field_simp

theorem fderiv_normalJacobian_inv_sqrt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    fderiv ℝ (fun v => (Real.sqrt (normalJacobian g p v))⁻¹) 0 = 0 := by
  have hj := (contDiffAt_normalJacobian_zero g p).differentiableAt (by simp)
  have houter : ContDiffAt ℝ 1 (fun z : ℝ => (Real.sqrt z)⁻¹) (normalJacobian g p 0) := by
    rw [normalJacobian_zero]
    exact (Real.contDiffAt_sqrt one_ne_zero).inv (by norm_num)
  have hchain := houter.differentiableAt (by simp) |>.hasFDerivAt.comp 0 hj.hasFDerivAt
  refine hchain.fderiv.trans ?_
  let D := fderiv ℝ (fun z : ℝ => (Real.sqrt z)⁻¹) (normalJacobian g p 0)
  exact (congrArg D.comp (fderiv_normalJacobian_zero g p)).trans (ContinuousLinearMap.comp_zero D)

private theorem deriv_normalJacobian_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    deriv (fun t : ℝ => normalJacobian g p (t • x)) 0 = 0 := by
  have hj := (contDiffAt_normalJacobian_zero g p).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => t • x) x 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const x).congr_deriv (one_smul ℝ x)
  have h := hj.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact h.deriv.trans (congrArg (fun L => L x) (fderiv_normalJacobian_zero g p))

theorem second_derivative_normalJacobian_inv_sqrt_radial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    iteratedDeriv 2 (fun t : ℝ => (Real.sqrt (normalJacobian g p (t • x)))⁻¹) 0 =
      (1 / 6 : ℝ) * Curvature.ricciTensor g p x x := by
  have hj : ContDiffAt ℝ 2 (normalJacobian g p) ((0 : ℝ) • x) := by
    rw [zero_smul]
    exact (contDiffAt_normalJacobian_zero g p).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hline := hj.comp 0 (show ContDiffAt ℝ 2 (fun t : ℝ => t • x) 0 from
    contDiffAt_id.smul contDiffAt_const)
  have houter : ContDiffAt ℝ 2 (fun z : ℝ => (Real.sqrt z)⁻¹)
      (normalJacobian g p ((0 : ℝ) • x)) := by
    rw [zero_smul, normalJacobian_zero]
    exact (Real.contDiffAt_sqrt one_ne_zero).inv (by norm_num)
  have hderiv : HasDerivAt (fun z : ℝ => (Real.sqrt z)⁻¹) (-(1 / 2 : ℝ)) 1 := by
    exact ((Real.hasDerivAt_sqrt (x := 1) one_ne_zero).inv (by norm_num)).congr_deriv (by norm_num)
  have h := iteratedDeriv_comp_two (f := fun t : ℝ => normalJacobian g p (t • x))
    (x := 0) houter hline
  rw [deriv_normalJacobian_radial_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
    zero_smul, normalJacobian_zero, hderiv.deriv, second_derivative_normalJacobian_radial_zero] at h
  exact h.trans (by ring)

theorem iteratedFDeriv_two_normalJacobian_inv_sqrt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    iteratedFDeriv ℝ 2 (fun v => (Real.sqrt (normalJacobian g p v))⁻¹) 0 (fun _ => x) =
      (1 / 6 : ℝ) * Curvature.ricciTensor g p x x := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  let U := Metric.ball (0 : E) (expMapC2Radius g p)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzero : L 0 ∈ U := by simpa [L, U] using expMapC2Radius_pos g p
  have hcomp := L.iteratedFDerivWithin_comp_right (contDiffOn_normalJacobian_inv_sqrt g p)
    hU.uniqueDiffOn (hU.preimage L.continuous).uniqueDiffOn hzero (i := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [iteratedFDerivWithin_of_isOpen 2 (hU.preimage L.continuous) hzero,
    iteratedFDerivWithin_of_isOpen 2 hU hzero] at hcomp
  have h := congrArg (fun B => B (fun _ : Fin 2 => (1 : ℝ))) hcomp
  have heq : iteratedDeriv 2 (fun t : ℝ => (Real.sqrt (normalJacobian g p (t • x)))⁻¹) 0 =
      iteratedFDeriv ℝ 2 (fun v => (Real.sqrt (normalJacobian g p v))⁻¹) 0 (fun _ => x) := by
    simpa only [iteratedDeriv_eq_iteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, zero_smul, one_smul,
      Function.comp_def, L] using h
  exact heq.symm.trans (second_derivative_normalJacobian_inv_sqrt_radial_zero g p x)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
