import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopShellRound

/-!
Both actual boundary levels of the concrete shell rounding are regular.
The true radial curve gives a nonzero derivative at every inner or outer zero point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

private theorem radialNorm_deriv (z : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun s : ℝ => ‖s • z‖ ^ 2) (2 * ‖z‖ ^ 2) 1 := by
  convert (hasDerivAt_pow 2 (1 : ℝ)).mul_const (‖z‖ ^ 2) using 1
  · ext s
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · norm_num

private theorem radialRadius_deriv {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    HasDerivAt (fun s : ℝ => loopModelRadius (s • z))
      (-2 * ‖z‖ ^ 2 / loopModelRadius z) 1 := by
  have hp : 0 < 2 * (1 - ‖z‖ ^ 2) := by nlinarith [norm_nonneg z]
  have ha : HasDerivAt (fun s : ℝ => 2 * (1 - ‖s • z‖ ^ 2)) (-4 * ‖z‖ ^ 2) 1 := by
    convert ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (radialNorm_deriv z)).const_mul 2
      using 1
    ring
  have hd := ha.sqrt (by simpa only [one_smul] using hp.ne')
  convert hd using 1
  · ext s
    rw [loopModelRadius_eq_sqrt]
  · simp only [one_smul]
    rw [loopModelRadius_eq_sqrt]
    ring

theorem loopShellRounding_regular {z : EuclideanSpace ℝ (Fin 2)}
    (hz : loopShellRounding z = 0) : fderiv ℝ loopShellRounding z ≠ 0 := by
  have hsrc := loopShellRounding_source hz.le
  have hopen : IsOpen {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  have hat := loopShellRounding_smooth.contDiffAt (hopen.mem_nhds hsrc)
  have hRadius := radialRadius_deriv hsrc
  intro hzero
  have hdiff : DifferentiableAt ℝ loopShellRounding z := hat.differentiableAt (by simp)
  have hfd : HasFDerivAt loopShellRounding
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) z := by
    simpa only [hzero] using hdiff.hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => s • z) z 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const z
  have hcomp0 : HasDerivAt (fun s : ℝ => loopShellRounding (s • z)) 0 1 := by
    simpa only [Function.comp_def, zero_apply] using
      hfd.comp_hasDerivAt_of_eq 1 hγ (by simp)
  rcases loopShellRounding_zero_iff.mp hz with hi | ho
  · have hr : loopModelRadius z = 1 := by
      rw [loopModelRadius_eq_sqrt]
      have ha : (2 : ℝ) * (1 - ‖z‖ ^ 2) = 1 := by rw [hi]; norm_num
      rw [ha, Real.sqrt_one]
    have hd : HasDerivAt (fun s : ℝ => loopModelRadius (s • z)) (-1) 1 := by
      convert hRadius using 1
      norm_num [hi, hr]
    have hpoly : HasDerivAt (fun s : ℝ => 16 * (1 - loopModelRadius (s • z))) 16 1 := by
      convert ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hd).const_mul 16 using 1
      norm_num
    have hnear : ∀ᶠ s in 𝓝 (1 : ℝ), loopModelRadius (s • z) < 5 / 4 :=
      hd.continuousAt.eventually (Iio_mem_nhds (by
        change loopModelRadius ((1 : ℝ) • z) < 5 / 4
        rw [one_smul, hr]
        norm_num))
    have hphi : HasDerivAt (fun s : ℝ => loopShellRounding (s • z)) 16 1 :=
      hpoly.congr_of_eventuallyEq (by
        filter_upwards [hnear] with s hs
        exact loopShellRounding_inner (s • z) hs.le)
    have he := hcomp0.unique hphi
    norm_num at he
  · have hsq := loopModelRadius_sq hsrc
    rw [ho] at hsq
    have hn : 0 ≤ loopModelRadius z := by
      rw [loopModelRadius_eq_sqrt]
      exact Real.sqrt_nonneg _
    have hgt : 21 / 16 < loopModelRadius z := by nlinarith
    have hpos : 0 < loopModelRadius z := by linarith
    have hr : loopModelRadius z = Real.sqrt (7 / 4) := by
      rw [loopModelRadius_eq_sqrt, ho]
      congr 1
      norm_num
    have hpoly : HasDerivAt
        (fun s : ℝ => 16 * (1 - loopModelRadius (s • z)) *
          (Real.sqrt (7 / 4) - loopModelRadius (s • z)))
        (16 * (1 - loopModelRadius z) * (2 * ‖z‖ ^ 2 / loopModelRadius z)) 1 := by
      convert (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hRadius).const_mul 16).mul
        ((hasDerivAt_const (1 : ℝ) (Real.sqrt (7 / 4))).sub hRadius) using 1
      simp only [Pi.sub_apply, one_smul, ← hr]
      ring
    have hnear : ∀ᶠ s in 𝓝 (1 : ℝ), 21 / 16 < loopModelRadius (s • z) :=
      hRadius.continuousAt.eventually (Ioi_mem_nhds (by
        change 21 / 16 < loopModelRadius ((1 : ℝ) • z)
        rwa [one_smul]))
    have hphi : HasDerivAt (fun s : ℝ => loopShellRounding (s • z))
        (16 * (1 - loopModelRadius z) * (2 * ‖z‖ ^ 2 / loopModelRadius z)) 1 :=
      hpoly.congr_of_eventuallyEq (by
        filter_upwards [hnear] with s hs
        exact loopShellRounding_outer (s • z) hs.le)
    have hdne : 16 * (1 - loopModelRadius z) *
        (2 * ‖z‖ ^ 2 / loopModelRadius z) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by linarith))
        (ne_of_gt (div_pos (by rw [ho]; norm_num) hpos))
    exact hdne (hcomp0.unique hphi).symm

end GC.GraphManifold.Assembly
