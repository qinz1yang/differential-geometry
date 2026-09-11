import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Distribution



noncomputable section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis



theorem integral_complexDivergence_closedBall {F G : ℂ → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) {R : ℝ} (hR : 0 < R) :
    (∫ z in Metric.closedBall (0 : ℂ) R, complexDivergence F G z) =
      ∫ θ in -Real.pi..Real.pi, R *
        (F (Complex.polarCoord.symm (R, θ)) * Real.cos θ +
          G (Complex.polarCoord.symm (R, θ)) * Real.sin θ) := by
  let B : ℝ → ℝ := fun r => ∫ θ in -Real.pi..Real.pi,
    F (Complex.polarCoord.symm (r, θ)) * Real.cos θ +
      G (Complex.polarCoord.symm (r, θ)) * Real.sin θ
  have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hjoint : Continuous (fun p : ℝ × ℝ =>
      F (Complex.polarCoord.symm p) * Real.cos p.2 +
      G (Complex.polarCoord.symm p) * Real.sin p.2) :=
    ((hF.continuous.comp hp).mul (Real.continuous_cos.comp continuous_snd)).add
      ((hG.continuous.comp hp).mul (Real.continuous_sin.comp continuous_snd))
  have hB : Continuous B := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    convert! hjoint
  have hsmall : Tendsto (fun r : ℝ => r * B r) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.mul (hB.tendsto 0))
  have hdiv : Continuous (complexDivergence F G) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hset : {z : ℂ | ‖z‖ ≤ R} = Metric.closedBall (0 : ℂ) R := by
    ext z
    simp
  have hi : IntegrableOn (complexDivergence F G) {z : ℂ | ‖z‖ ≤ R} := by
    rw [hset]
    exact hdiv.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hlim := (tendsto_integral_annulus_zero hi).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hout := ((tendsto_const_nhds (x := R * B R)).sub hsmall).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hgreen : Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      complexDivergence F G z) (𝓝[>] 0) (𝓝 (R * B R)) := by
    apply (show Tendsto (fun r => R * B R - r * B r) (𝓝[>] 0) (𝓝 (R * B R)) by
      simpa using hout).congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono inf_le_left] with r hr hrR
    rw [integral_complexDivergence_annulus hr hrR.le (fun _ _ => hF.contDiffAt)
      (fun _ _ => hG.contDiffAt), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have he := tendsto_nhds_unique hlim hgreen
  rw [hset] at he
  simpa only [B, intervalIntegral.integral_const_mul] using he


theorem integral_laplacian_closedBall {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    {R : ℝ} (hR : 0 < R) :
    (∫ z in Metric.closedBall (0 : ℂ) R, Laplacian.laplacian f z) =
      ∫ θ in -Real.pi..Real.pi, R *
        fderiv ℝ f (Complex.polarCoord.symm (R, θ)) (Complex.polarCoord.symm (1, θ)) := by
  have hd := hf.fderiv_right (m := 1) (by norm_num)
  have h := integral_complexDivergence_closedBall
    (F := fun q => fderiv ℝ f q 1) (G := fun q => fderiv ℝ f q Complex.I)
    (hd.clm_apply contDiff_const) (hd.clm_apply contDiff_const) hR
  simp only [complexDivergence_gradient hf.contDiffAt] at h
  rw [h]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  erw [apply_polar_unit]
  ring

end DifferentialGeometry.Analysis
