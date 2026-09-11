import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.SupportMargin
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LogKernelBoundary
import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportDerivative



noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis




theorem contDiffOn_weighted_diskNeumannLogKernel_radial {κ : ℂ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : ‖z‖ = 1) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × ℂ => κ q.2 * diskNeumannLogKernel q.2 (q.1 • z))
      (Ioo ρ R ×ˢ univ) := by
  intro q hq
  by_cases hw : q.2 ∈ tsupport κ
  · have hrpos : 0 < q.1 := hρ.trans hq.1.1
    have hrnorm : ‖q.1 • z‖ = q.1 := by
      rw [norm_smul, hz, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
    have hfirst_ne : q.1 • z - q.2 ≠ 0 := by
      intro he
      have heq := congrArg norm (sub_eq_zero.mp he)
      rw [hrnorm] at heq
      have hlt : ρ < ‖q.2‖ := by
        rw [← heq]
        exact hq.1.1
      exact (not_le_of_gt hlt) (hs q.2 hw)
    have hlinear : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => p.1 • z - p.2) q :=
      (contDiffAt_fst.smul_const z).sub contDiffAt_snd
    have hfirst : ContDiffAt ℝ ∞
        (fun p : ℝ × ℂ => Real.log ‖p.1 • z - p.2‖) q :=
      (hlinear.norm ℝ hfirst_ne).log (norm_ne_zero_iff.mpr hfirst_ne)
    have hp : ‖q.2‖ * ‖q.1 • z‖ < 1 := by
      rw [hrnorm]
      exact (mul_le_mul_of_nonneg_right (hs q.2 hw) hrpos.le).trans_lt
        ((mul_lt_mul_of_pos_left hq.1.2 hρ).trans hρR)
    have ho : IsOpen {p : ℂ × ℂ | ‖p.1‖ * ‖p.2‖ < 1} :=
      isOpen_lt (continuous_fst.norm.mul continuous_snd.norm) continuous_const
    have hi := (contDiffOn_diskImageLogKernel (q.2, q.1 • z) hp).contDiffAt
      (ho.mem_nhds hp)
    have hparam : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => (p.2, p.1 • z)) q :=
      contDiffAt_snd.prodMk (contDiffAt_fst.smul_const z)
    have himage_comp := hi.comp q hparam
    have himage : ContDiffAt ℝ ∞
        (fun p : ℝ × ℂ => diskImageLogKernel p.2 (p.1 • z)) q := by
      simpa only [Function.comp_apply] using! himage_comp
    exact ((hκ.contDiffAt.comp q contDiffAt_snd).mul
      (hfirst.add himage)).contDiffWithinAt
  · have he : (fun p : ℝ × ℂ => κ p.2 * diskNeumannLogKernel p.2 (p.1 • z)) =ᶠ[𝓝 q] 0 := by
      have hn : ∀ᶠ p : ℝ × ℂ in 𝓝 q, p.2 ∉ tsupport κ :=
        ((isClosed_tsupport κ).isOpen_compl.preimage continuous_snd).mem_nhds hw
      filter_upwards [hn] with p hp
      have hk : κ p.2 = 0 := by
        by_contra hne
        exact hp (subset_closure hne)
      simp only [hk, zero_mul, Pi.zero_apply]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt



theorem diskRegularizerPotential_eq_kernel_integral {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    diskRegularizerPotential κ z =
      -(1 / (2 * Real.pi)) * ∫ w : ℂ, κ w * diskNeumannLogKernel w z := by
  have hsing : Integrable (fun w : ℂ => κ w * Real.log ‖z - w‖) :=
    (hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hκ.continuous
      locallyIntegrable_log_norm_complex z).integrable
  have hjoint := contDiffOn_weighted_diskImageLogKernel hκ hρ hρR hs
  have himage_cont : Continuous (fun w : ℂ => κ w * diskImageLogKernel w z) := by
    rw [← continuousOn_univ]
    exact hjoint.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun w _ => ⟨hz, mem_univ w⟩)
  have himage_support : HasCompactSupport (fun w : ℂ => κ w * diskImageLogKernel w z) := by
    refine hc.mono ?_
    intro w
    contrapose!
    intro hw
    simp [hw]
  have himage : Integrable (fun w : ℂ => κ w * diskImageLogKernel w z) :=
    himage_cont.integrable_of_hasCompactSupport himage_support
  rw [diskRegularizerPotential, logarithmicPotential, diskImagePotential]
  simp_rw [diskNeumannLogKernel, mul_add]
  rw [integral_add hsing himage]
  ring



theorem hasDerivAt_diskRegularizerPotential_radial {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1) {z : ℂ} (hz : ‖z‖ = 1) :
    HasDerivAt (fun r : ℝ => diskRegularizerPotential κ (r • z))
      (-(1 / (2 * Real.pi)) * ∫ w : ℂ, κ w) 1 := by
  obtain ⟨ρ, R, hρ, hρ1, hR, hρR, hsρ⟩ := exists_disk_support_radii hc hs
  have hjoint := contDiffOn_weighted_diskNeumannLogKernel_radial hκ hρ hρR hsρ hz
  have hint := hasDerivAt_planeIntegral_of_compact_support
    (f := fun r w => κ w * diskNeumannLogKernel w (r • z))
    isOpen_Ioo hc
    (fun _ w _ hw => by
      have hk : κ w = 0 := by
        by_contra hne
        exact hw (subset_closure hne)
      simp only [hk, zero_mul])
    (hjoint.of_le (by norm_num))
    (show (1 : ℝ) ∈ Ioo ρ R from ⟨hρ1, hR⟩)
  have hderiv : (∫ w : ℂ,
      deriv (fun r : ℝ => κ w * diskNeumannLogKernel w (r • z)) 1) =
      ∫ w : ℂ, κ w := by
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      by_cases hw : w ∈ tsupport κ
      · have hw1 : ‖w‖ < 1 := by
          simpa only [mem_ball_zero_iff] using hs hw
        simpa using (HasDerivAt.const_mul (κ w)
          (hasDerivAt_diskNeumannLogKernel_radial hw1 hz)).deriv
      · have hk : κ w = 0 := by
          by_contra hne
          exact hw (subset_closure hne)
        simp [hk]
  rw [hderiv] at hint
  have hscaled := HasDerivAt.const_mul (-(1 / (2 * Real.pi))) hint
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hρ1, hR⟩] with r hr
  have hrpos : 0 < r := hρ.trans hr.1
  have hrball : r • z ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_smul, hz, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
    exact hr.2
  exact diskRegularizerPotential_eq_kernel_integral hc hκ hρ hρR hsρ hrball



theorem hasDerivAt_diskRegularizerPotential_radial_eq_neg_one {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1)
    (hmass : ∫ w : ℂ, κ w = 2 * Real.pi) {z : ℂ} (hz : ‖z‖ = 1) :
    HasDerivAt (fun r : ℝ => diskRegularizerPotential κ (r • z)) (-1) 1 := by
  convert hasDerivAt_diskRegularizerPotential_radial hc hκ hs hz using 1
  rw [hmass]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

end DifferentialGeometry.Analysis
