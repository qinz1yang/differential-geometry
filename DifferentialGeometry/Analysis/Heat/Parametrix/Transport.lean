import DifferentialGeometry.Analysis.Heat.Parametrix.Coefficient
import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobianTransport

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius expMapC2Radius_pos
  expMap_contMDiffAt_infty_of_norm_lt_radius mem_expMapDiffeo_source_of_norm_lt_radius)
open Geometry.Riemannian.VolumeComparison Geometry.Riemannian.NormalCoordinates
open Geometry.Riemannian.Exponential Geometry.Connection Geometry.Operator
open DifferentialGeometry.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)] [T2Space M]

private theorem continuousOn_heatParametrixCoefficient_source
    (g : SmoothRiemannianMetric I M) (p : M) (k : ℕ) :
    ContinuousOn (fun v : E => Real.sqrt (normalJacobian g p v) *
      laplacian (LeviCivita g) g (heatParametrixCoefficient g p k)
        (expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)))
      (Metric.ball (0 : E) (expMapC2Radius g p)) := by
  let U := Metric.ball (0 : E) (expMapC2Radius g p)
  let V := (normalChartAt g p).source ∩ (normalChartAt g p) ⁻¹' U
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hΔ := (contMDiffOn_laplacian_leviCivita g hV
    (contMDiffOn_heatParametrixCoefficient g p k)).continuousOn
  apply (contDiffOn_normalJacobian g p).continuousOn.sqrt.mul
  apply hΔ.comp
  · intro v hv
    exact (expMap_contMDiffAt_infty_of_norm_lt_radius g p (by simpa using hv)).continuousAt.continuousWithinAt
  · intro v hv
    have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p (by simpa using hv)
    have heq : expMapDiffeo g p v =
        expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) :=
      expMapDiffeo_apply_eq g p hsrc
    change expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) ∈ V
    rw [← heq]
    refine ⟨(expMapDiffeo g p).map_source hsrc, ?_⟩
    have hinv : normalChartAt g p (expMapDiffeo g p v) = v :=
      (expMapDiffeo g p).left_inv hsrc
    change normalChartAt g p (expMapDiffeo g p v) ∈ U
    rw [hinv]
    exact hv

variable [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem hasDerivAt_heatParametrixCoefficient_zero_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => heatParametrixCoefficient g p 0
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))
      ((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 *
        heatParametrixCoefficient g p 0
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) 1 := by
  have hc := normalChartAt_intrinsicGeodesic g hEnorm p x
    (t := 1) (by simpa only [one_smul] using hx)
  rw [one_smul] at hc
  have hq : normalChartAt g p (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) = x := by
    rw [expMapIntrinsic_def]
    exact hc
  have hd := hasDerivAt_normalJacobian_inv_sqrt_intrinsicGeodesic B hx hB
  simpa only [heatParametrixCoefficient, hq] using hd

theorem hasDerivAt_heatParametrixCoefficient_succ_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (k : ℕ) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    HasDerivAt (fun t : ℝ => heatParametrixCoefficient g p (k + 1)
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t))
      (((Module.finrank ℝ E - laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) / 2 - (k + 1 : ℝ)) *
        heatParametrixCoefficient g p (k + 1)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) +
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p k)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))) 1 := by
  let Q := fun v : E => Real.sqrt (normalJacobian g p v) *
    laplacian (LeviCivita g) g (heatParametrixCoefficient g p k)
      (expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
  have hstar : StarConvex ℝ (0 : E) (Metric.ball 0 (expMapC2Radius g p)) :=
    (convex_ball (0 : E) (expMapC2Radius g p)).starConvex
      (Metric.mem_ball_self (expMapC2Radius_pos g p))
  have hI := hasDerivAt_radialIntegral_smul k Metric.isOpen_ball hstar
    (continuousOn_heatParametrixCoefficient_source g p k) (by simpa using hx)
  have h0 := hasDerivAt_normalJacobian_inv_sqrt_radial_one B hx hB
  have hd := h0.mul hI
  have hechart := normalChartAt_intrinsicGeodesic_eventuallyEq g hEnorm p x
    (t := 1) (by simpa only [one_smul] using hx)
  have heq : (fun t : ℝ => heatParametrixCoefficient g p (k + 1)
      (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t)) =ᶠ[𝓝 1]
      fun t : ℝ => (Real.sqrt (normalJacobian g p (t • x)))⁻¹ * radialIntegral k Q (t • x) := by
    filter_upwards [hechart] with t ht
    rw [heatParametrixCoefficient, ht]
  have hq : normalChartAt g p (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) = x := by
    rw [expMapIntrinsic_def]
    simpa only [one_smul] using hechart.eq_of_nhds
  have ha : heatParametrixCoefficient g p (k + 1)
      (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) =
      (Real.sqrt (normalJacobian g p x))⁻¹ * radialIntegral k Q x := by
    rw [heatParametrixCoefficient, hq]
  have hxexp : expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm x) =
      expMapIntrinsic g hEnorm p (show TangentSpace I p from x) := exp_eq_intr_of_c2 g hEnorm p hx
  have hpos := normalJacobian_pos g p (mem_expMapDiffeo_source_of_norm_lt_radius g p hx)
  have hs : Real.sqrt (normalJacobian g p x) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  simp only [one_smul, Q, smul_eq_mul, hxexp, ha]
  field_simp
  ring

theorem heatParametrixCoefficient_transport
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (k : ℕ) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    deriv (fun t : ℝ => heatParametrixCoefficient g p k
        (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t)) 1 +
      ((k : ℝ) + (laplacian (LeviCivita g) g (branchEnergy g B)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) -
        Module.finrank ℝ E) / 2) *
        heatParametrixCoefficient g p k
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) =
      match k with
      | 0 => 0
      | j + 1 => laplacian (LeviCivita g) g (heatParametrixCoefficient g p j)
          (expMapIntrinsic g hEnorm p (show TangentSpace I p from x)) := by
  cases k with
  | zero =>
    rw [(hasDerivAt_heatParametrixCoefficient_zero_intrinsicGeodesic B hx hB).deriv]
    simp only [Nat.cast_zero, zero_add]
    ring
  | succ k =>
    rw [(hasDerivAt_heatParametrixCoefficient_succ_intrinsicGeodesic B k hx hB).deriv]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

end DifferentialGeometry.Analysis.HeatEquation
