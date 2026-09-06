import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobian
import DifferentialGeometry.Geometry.Comparison.Volume.RadialTransport
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentGauss
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Intrinsic

noncomputable section

open scoped Manifold ContDiff Topology Matrix

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Bundle Filter Set
open NormalCoordinates Exponential Variation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem normalChartDensity_eq_curveDensity_intrinsicJacobi_at_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) :
    normalChartDensity g p x =
      curveDensity g (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x))
        (fun i : Fin (Module.finrank ℝ E) =>
          intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
            (show TangentSpace I p from chartModelBasis E i)) 1 := by
  have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p hx
  have hD := (expDiffeo_mfderiv g p hsrc).trans (exp_germ_eq_intr g hEnorm p hx).mfderiv_eq
  have hp : expMapDiffeo g p x =
      intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) 1 :=
    (expMapDiffeo_apply_eq g p hsrc).trans
      ((exp_eq_intr_of_c2 g hEnorm p hx).trans (expMapIntrinsic_def g hEnorm p _))
  rw [normalDensity_det, curveDensity]
  apply congrArg (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
    Real.sqrt A.det)
  ext i j
  rw [normalGram_apply]
  have hcol (k : Fin (Module.finrank ℝ E)) :
      (mfderiv 𝓘(ℝ, E) I (expMapDiffeo g p) x (chartModelBasis E k) : E) =
        intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
          (show TangentSpace I p from chartModelBasis E k) 1 := by
    exact (congrArg (fun L => (L (chartModelBasis E k) : E)) hD).trans
      (intrinsic_jacobi_one g hEnorm p x (chartModelBasis E k)).symm
  simp only [curveGram, Matrix.of_apply]
  rw [hcol i, hcol j, hp]

theorem curveDensity_intrinsicJacobi_eq_normalChartDensity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) (x : E)
    {t : ℝ} (htx : ‖t • x‖ < expMapC2Radius g p) :
    curveDensity g (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x))
        (fun i : Fin (Module.finrank ℝ E) =>
          intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
            (show TangentSpace I p from chartModelBasis E i)) t =
      |t| ^ Module.finrank ℝ E * normalChartDensity g p (t • x) := by
  rw [transDens_scale g hEnorm p (show TangentSpace I p from x)
    (fun i => (show TangentSpace I p from chartModelBasis E i)) t]
  rw [normalChartDensity_eq_curveDensity_intrinsicJacobi_at_one g hEnorm p htx]
  rfl

theorem normalChartDensity_eq_curveDensity_intrinsicJacobi
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) :
    normalChartDensity g p x =
      curveDensity g (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x))
        (fun i : Fin (Module.finrank ℝ E) =>
          intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
            (show TangentSpace I p from chartModelBasis E i)) 1 := by
  have h := curveDensity_intrinsicJacobi_eq_normalChartDensity g hEnorm p x
    (t := 1) (by simpa only [one_smul] using hx)
  simpa only [abs_one, one_pow, one_smul, one_mul] using h.symm

theorem hasDerivAt_normalChartDensity_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => normalChartDensity g p (t • x))
      ((laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) * normalChartDensity g p x) 1 := by
  let d := fun t : ℝ => normalChartDensity g p (t • x)
  let V := fun i : Fin (Module.finrank ℝ E) =>
    intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
      (show TangentSpace I p from chartModelBasis E i)
  let γ := intrinsicGeodesic g hEnorm p (show TangentSpace I p from x)
  have hball : x ∈ Metric.ball (0 : E) (expMapC2Radius g p) := by simpa using hx
  have hd : DifferentiableAt ℝ d 1 := by
    have hs := (contDiffOn_normalChartDensity g p).contDiffAt (Metric.isOpen_ball.mem_nhds hball)
    have hline : ContDiffAt ℝ ∞ (fun t : ℝ => t • x) 1 :=
      contDiffAt_id.smul contDiffAt_const
    have hs' : ContDiffAt ℝ ∞ (normalChartDensity g p) ((1 : ℝ) • x) := by
      simpa only [one_smul] using hs
    exact (hs'.comp 1 hline).differentiableAt (by simp)
  have hd1 : d 1 = normalChartDensity g p x := by simp only [d, one_smul]
  have hprod : HasDerivAt (fun t : ℝ => t ^ Module.finrank ℝ E * d t)
      (Module.finrank ℝ E * d 1 + deriv d 1) 1 := by
    have hp := (hasDerivAt_pow (Module.finrank ℝ E) (1 : ℝ)).mul hd.hasDerivAt
    change HasDerivAt (fun t : ℝ => t ^ Module.finrank ℝ E * d t)
      ((Module.finrank ℝ E * 1 ^ (Module.finrank ℝ E - 1)) * d 1 +
        1 ^ Module.finrank ℝ E * deriv d 1) 1 at hp
    simpa only [one_pow, mul_one, one_mul] using hp
  have hev : ∀ᶠ t : ℝ in 𝓝 1, ‖t • x‖ < expMapC2Radius g p :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by
      change ‖(1 : ℝ) • x‖ < expMapC2Radius g p
      simpa only [one_smul] using hx)
  have heq : curveDensity g γ V =ᶠ[𝓝 1] fun t : ℝ => t ^ Module.finrank ℝ E * d t := by
    filter_upwards [hev, isOpen_Ioi.mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht hpos
    rw [curveDensity_intrinsicJacobi_eq_normalChartDensity g hEnorm p x ht, abs_of_pos hpos]
  have hc := hasDerivAt_curveDensity_intrinsicJacobi B
    (u := (show TangentSpace I p from x)) hB
    (show Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) from chartModelBasis E)
  have hval := (hprod.congr_of_eventuallyEq heq).unique hc
  have hden : curveDensity g γ V 1 = d 1 := by
    simpa only [one_pow, one_mul] using heq.self_of_nhds
  change Module.finrank ℝ E * d 1 + deriv d 1 =
    laplacian (LeviCivita g) g (branchEnergy g B)
      (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) *
      curveDensity g γ V 1 at hval
  rw [hden, hd1] at hval
  apply hd.hasDerivAt.congr_deriv
  linarith

theorem hasDerivAt_normalJacobian_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => normalJacobian g p (t • x))
      ((laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) * normalJacobian g p x) 1 := by
  have hd := (hasDerivAt_normalChartDensity_radial_one B hx hB).div_const (normalChartDensity g p 0)
  exact hd.congr_deriv (by rw [normalJacobian, mul_div_assoc])

theorem hasDerivAt_normalJacobian_inv_sqrt_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => (Real.sqrt (normalJacobian g p (t • x)))⁻¹)
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        (Real.sqrt (normalJacobian g p x))⁻¹) 1 := by
  have hj := hasDerivAt_normalJacobian_radial_one B hx hB
  have hjpos := normalJacobian_pos g p (mem_expMapDiffeo_source_of_norm_lt_radius g p hx)
  have hjs : normalJacobian g p ((1 : ℝ) • x) ≠ 0 := by
    simpa only [one_smul] using hjpos.ne'
  have hr : Real.sqrt (normalJacobian g p ((1 : ℝ) • x)) ≠ 0 := by
    rw [one_smul]
    exact Real.sqrt_ne_zero'.mpr hjpos
  have hd := ((Real.hasDerivAt_sqrt hjs).comp 1 hj).inv hr
  apply hd.congr_deriv
  simp only [Function.comp_apply, one_smul]
  have hr' : Real.sqrt (normalJacobian g p x) ≠ 0 := Real.sqrt_ne_zero'.mpr hjpos
  have hs : (Real.sqrt (normalJacobian g p x)) ^ 2 = normalJacobian g p x :=
    Real.sq_sqrt hjpos.le
  rw [hs]
  field_simp
  ring

theorem hasDerivAt_normalJacobian_inv_sqrt_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => (Real.sqrt (normalJacobian g p
        (normalChartAt g p
          (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))))⁻¹)
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        (Real.sqrt (normalJacobian g p x))⁻¹) 1 := by
  apply (hasDerivAt_normalJacobian_inv_sqrt_radial_one B hx hB).congr_of_eventuallyEq
  have heq := normalChartAt_intrinsicGeodesic_eventuallyEq g hEnorm p x
    (t := 1) (by simpa only [one_smul] using hx)
  filter_upwards [heq] with t ht
  rw [ht]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
