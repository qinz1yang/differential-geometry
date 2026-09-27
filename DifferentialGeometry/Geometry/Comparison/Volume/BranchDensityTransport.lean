import DifferentialGeometry.Geometry.Comparison.Volume.RadialTransport
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Gauss
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensitySmoothness

noncomputable section

open scoped Manifold ContDiff Topology Matrix

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Bundle Filter Set
open NormalCoordinates Exponential Variation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

lemma paramDensity_pos_branch
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    0 < paramDensity g B.hom x := by
  let D1 : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := B.hom.toPartialEquiv, open_source := B.hom.open_source,
      open_target := B.hom.open_target, contMDiffOn_toFun := B.hom.contMDiffOn.of_le (by simp),
      contMDiffOn_invFun := B.hom.contMDiffOn_invFun.of_le (by simp) }
  exact paramDensity_pos g D1 hx

theorem paramDensity_eq_curveDensity_intrinsicJacobi
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    paramDensity g B.hom x =
      curveDensity g (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x))
        (fun i : Fin (Module.finrank ℝ E) =>
          intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
            (show TangentSpace I p from chartModelBasis E i)) 1 := by
  have hgerm : (B.hom : E → M) =ᶠ[𝓝 x]
      fun v : E => expMapIntrinsic g hEnorm p (show TangentSpace I p from v) := by
    filter_upwards [B.hom.open_source.mem_nhds hx] with v hv
    exact (B.hom_eq hv).symm
  have hD := hgerm.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I)
  have hp : B.hom x = intrinsicGeodesic g hEnorm p
      (show TangentSpace I p from x) 1 :=
    hgerm.eq_of_nhds.trans (expMapIntrinsic_def g hEnorm p _)
  rw [paramDensity, curveDensity]
  apply congrArg (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
    Real.sqrt A.det)
  ext i j
  rw [paramGramMatrix_apply]
  have hcol (k : Fin (Module.finrank ℝ E)) :
      (mfderiv 𝓘(ℝ, E) I (B.hom : E → M) x (chartModelBasis E k) : E) =
        intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
          (show TangentSpace I p from chartModelBasis E k) 1 := by
    exact (congrArg (fun L => (L (chartModelBasis E k) : E)) hD).trans
      (intrinsic_jacobi_one g hEnorm p x (chartModelBasis E k)).symm
  simp only [curveGram, Matrix.of_apply]
  rw [hcol i, hcol j, hp]

theorem curveDensity_intrinsicJacobi_eq_paramDensity
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (x : E) {t : ℝ}
    (htx : t • x ∈ B.hom.source) :
    curveDensity g (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x))
        (fun i : Fin (Module.finrank ℝ E) =>
          intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
            (show TangentSpace I p from chartModelBasis E i)) t =
      |t| ^ Module.finrank ℝ E * paramDensity g B.hom (t • x) := by
  rw [transDens_scale g hEnorm p (show TangentSpace I p from x)
    (fun i => (show TangentSpace I p from chartModelBasis E i)) t]
  rw [paramDensity_eq_curveDensity_intrinsicJacobi B htx]
  rfl

theorem hasDerivAt_paramDensity_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => paramDensity g B.hom (t • x))
      ((laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) * paramDensity g B.hom x) 1 := by
  let V := fun i : Fin (Module.finrank ℝ E) =>
    intrinsicJacobi g hEnorm p (show TangentSpace I p from x)
      (show TangentSpace I p from chartModelBasis E i)
  let γ := intrinsicGeodesic g hEnorm p (show TangentSpace I p from x)
  have hc := hasDerivAt_curveDensity_intrinsicJacobi B
    (u := (show TangentSpace I p from x)) hx
    (show Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) from chartModelBasis E)
  have hden : (1 : ℝ) ^ Module.finrank ℝ E ≠ 0 := by simp
  have hd := hc.div (hasDerivAt_pow (Module.finrank ℝ E) (1 : ℝ)) hden
  have hval : curveDensity g γ V 1 = paramDensity g B.hom x :=
    (paramDensity_eq_curveDensity_intrinsicJacobi B hx).symm
  have hd' : HasDerivAt (fun t : ℝ => curveDensity g γ V t / t ^ Module.finrank ℝ E)
      ((laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) * paramDensity g B.hom x) 1 := by
    apply hd.congr_deriv
    simp only [one_pow, mul_one, div_one]
    change _ * curveDensity g γ V 1 - curveDensity g γ V 1 * _ = _
    rw [hval]
    ring
  apply hd'.congr_of_eventuallyEq
  have hev : ∀ᶠ t : ℝ in 𝓝 1, t • x ∈ B.hom.source :=
    (B.hom.open_source.preimage (by fun_prop)).mem_nhds (by
      simpa only [mem_preimage, one_smul] using hx)
  filter_upwards [hev, isOpen_Ioi.mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht hpos
  rw [curveDensity_intrinsicJacobi_eq_paramDensity B x ht, abs_of_pos hpos]
  exact (mul_div_cancel_left₀ (paramDensity g B.hom (t • x)) (pow_ne_zero _ hpos.ne')).symm

theorem hasDerivAt_paramDensity_ratio_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => paramDensity g B.hom (t • x) / paramDensity g B.hom 0)
      ((laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) * (paramDensity g B.hom x / paramDensity g B.hom 0)) 1 := by
  have hd := (hasDerivAt_paramDensity_radial_one B hx).div_const (paramDensity g B.hom 0)
  exact hd.congr_deriv (by rw [mul_div_assoc])


theorem hasDerivAt_paramDensity_inv_sqrt_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => (Real.sqrt (paramDensity g B.hom (t • x)))⁻¹)
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        (Real.sqrt (paramDensity g B.hom x))⁻¹) 1 := by
  have hd := hasDerivAt_paramDensity_radial_one B hx
  have hpos : 0 < paramDensity g B.hom x := paramDensity_pos_branch B hx
  have hjs : paramDensity g B.hom ((1 : ℝ) • x) ≠ 0 := by
    simpa only [one_smul] using hpos.ne'
  have hr : Real.sqrt (paramDensity g B.hom ((1 : ℝ) • x)) ≠ 0 := by
    rw [one_smul]
    exact Real.sqrt_ne_zero'.mpr hpos
  have hsqrt := ((Real.hasDerivAt_sqrt hjs).comp 1 hd).inv hr
  apply hsqrt.congr_deriv
  simp only [Function.comp_apply, one_smul]
  have hr' : Real.sqrt (paramDensity g B.hom x) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hs : (Real.sqrt (paramDensity g B.hom x)) ^ 2 = paramDensity g B.hom x :=
    Real.sq_sqrt hpos.le
  rw [hs]
  field_simp
  ring


theorem hasDerivAt_paramDensity_ratio_inv_sqrt_radial_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {x : E} (hx : x ∈ B.hom.source)
    (h0 : (0 : E) ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ =>
        (Real.sqrt (paramDensity g B.hom (t • x) / paramDensity g B.hom 0))⁻¹)
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        (Real.sqrt (paramDensity g B.hom x / paramDensity g B.hom 0))⁻¹) 1 := by
  have hdenpos : 0 < paramDensity g B.hom 0 := paramDensity_pos_branch B (x := (0 : E)) h0
  have hpos : 0 < paramDensity g B.hom x / paramDensity g B.hom 0 :=
    div_pos (paramDensity_pos_branch B hx) hdenpos
  have hd := hasDerivAt_paramDensity_ratio_radial_one B hx
  have hjs : paramDensity g B.hom ((1 : ℝ) • x) /
      paramDensity g B.hom 0 ≠ 0 := by
    simpa only [one_smul] using ne_of_gt hpos
  have hr : Real.sqrt (paramDensity g B.hom ((1 : ℝ) • x) /
      paramDensity g B.hom 0) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (by simpa only [one_smul] using hpos)
  have hsqrt := ((Real.hasDerivAt_sqrt hjs).comp 1 hd).inv hr
  apply hsqrt.congr_deriv
  simp only [Function.comp_apply, one_smul]
  have hr' : Real.sqrt (paramDensity g B.hom x / paramDensity g B.hom 0) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  have hs : (Real.sqrt (paramDensity g B.hom x / paramDensity g B.hom 0)) ^ 2 =
      paramDensity g B.hom x / paramDensity g B.hom 0 := Real.sq_sqrt hpos.le
  rw [hs]
  have hxne : paramDensity g B.hom x ≠ 0 := ne_of_gt (paramDensity_pos_branch B hx)
  field_simp [hxne, ne_of_gt hdenpos]
  ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
