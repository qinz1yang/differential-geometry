import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem covDerivAlong_diskMapPartial
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {c v : ℝ → ℂ} {t : ℝ} (hc : DifferentiableAt ℝ c t)
    (hv : DifferentiableAt ℝ v t) (hz : c t ∈ s) :
    covDerivAlong g (U ∘ c) (fun r => diskMapPartial U (c r) (v r)) t =
      diskMapCovariantPartial g U (c t) (deriv c t) (v t) +
        diskMapPartial U (c t) (deriv v t) := by
  let F := (extChartAt 𝓘(ℝ, E) (U (c t))) ∘ U
  have hUz := (hU (c t) hz).contMDiffAt (hs.mem_nhds hz)
  have hF : ContDiffAt ℝ 2 F (c t) :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := U (c t))).comp (c t) hUz).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hrepnear : (fun q =>
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U (c t))).continuousLinearMapAt ℝ (U q) ∘L
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q) =ᶠ[𝓝 (c t)] fderiv ℝ F := by
    filter_upwards [hs.mem_nhds hz, hUz.continuousAt
      ((chartAt E (U (c t))).open_source.mem_nhds (mem_chart_source E (U (c t))))] with q hq hchart
    exact chartCoord_source_mfderiv
      (((hU q hq).contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)) (U (c t)) hchart
  have hrep : chartRepAt (U ∘ c) (fun r => diskMapPartial U (c r) (v r)) t =ᶠ[𝓝 t]
      (fun r => fderiv ℝ F (c r) (v r)) := by
    filter_upwards [hc.continuousAt.eventually hrepnear] with r hr
    exact congrArg (fun L => L (v r)) hr
  have hd := (hDF.hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt).clm_apply hv.hasDerivAt
  have hdrep := hd.congr_of_eventuallyEq hrep
  have hcurve := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt
  have hcov := covDerivAlong_chartCoord g (U ∘ c)
    (fun r => diskMapPartial U (c r) (v r)) t
  have hself (X : TangentSpace 𝓘(ℝ, E) (U (c t))) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U (c t))).continuousLinearMapAt ℝ (U (c t)) X = X :=
    (trivToE_basepoint (U (c t)) X).trans
      (tangentSpaceModelContinuousLinearEquiv_apply (U (c t)) X)
  erw [hself] at hcov
  have hsecond := diskMapCovariantPartial_chart g hs hU hz (deriv c t) (v t)
  rw [hself] at hsecond
  have hpartial : diskMapPartial U (c t) (deriv v t) = fderiv ℝ F (c t) (deriv v t) := by
    have hp := congrArg (fun L => L (deriv v t)) hrepnear.eq_of_nhds
    erw [hself] at hp
    exact hp
  have hsecondD : fderiv ℝ (fun q => fderiv ℝ F q (v t)) (c t) (deriv c t) =
      fderiv ℝ (fderiv ℝ F) (c t) (deriv c t) (v t) := by
    rw [fderiv_clm_apply hDF (differentiableAt_const (v t))]
    simp
  rw [hcov, hsecond, hpartial]
  rw [chartCovDerivAlong_def, hdrep.deriv, hrep.eq_of_nhds]
  change _ + _ = (fderiv ℝ (fun q => fderiv ℝ F q (v t)) (c t) (deriv c t) + _) + _
  rw [hsecondD]
  have hchart : deriv (chartCurve (I := 𝓘(ℝ, E)) (U (c t)) (U ∘ c)) t =
      fderiv ℝ F (c t) (deriv c t) := hcurve.deriv
  erw [hchart]
  exact add_right_comm _ _ _




theorem covDerivAlong_diskMapVelocity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) {t : ℝ} (hz : c t ∈ s) :
    covDerivAlong g (U ∘ c)
      (fun r => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) r (1 : ℝ)) t =
      diskMapCovariantPartial g U (c t) (deriv c t) (deriv c t) +
        diskMapPartial U (c t) (deriv (deriv c) t) := by
  have heq : ∀ᶠ r in 𝓝 t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) r (1 : ℝ) =
      diskMapPartial U (c r) (deriv c r) := by
    filter_upwards [hc.continuous.continuousAt (hs.mem_nhds hz)] with r hr
    exact congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E))
      (tangent_velocity_comp (((hU _ hr).contMDiffAt (hs.mem_nhds hr)).mdifferentiableAt (by simp))
        (hc.differentiable (by simp) r))
  rw [DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq g (U ∘ c) heq]
  exact covDerivAlong_diskMapPartial g hs hU (hc.differentiable (by simp) t)
    ((contDiff_infty_iff_deriv.mp hc).2.differentiable (by simp) t) hz

end DifferentialGeometry.Geometry
