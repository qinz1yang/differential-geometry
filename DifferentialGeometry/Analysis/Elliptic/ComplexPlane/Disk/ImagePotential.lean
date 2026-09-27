import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportParametric
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LogKernel
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Basic



noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis


def diskImagePotential (κ : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(1 / (2 * Real.pi)) * ∫ w : ℂ, κ w * diskImageLogKernel w z



def diskRegularizerPotential (κ : ℂ → ℝ) (z : ℂ) : ℝ :=
  logarithmicPotential κ z + diskImagePotential κ z



theorem contDiffOn_weighted_diskImageLogKernel {κ : ℂ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℂ => κ q.2 * diskImageLogKernel q.2 q.1)
      (Metric.ball (0 : ℂ) R ×ˢ univ) := by
  intro q hq
  by_cases hw : q.2 ∈ tsupport κ
  · have hp : ‖q.2‖ * ‖q.1‖ < 1 :=
      (mul_le_mul_of_nonneg_right (hs q.2 hw) (norm_nonneg q.1)).trans_lt
        ((mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hq.1) hρ).trans hρR)
    have ho : IsOpen {p : ℂ × ℂ | ‖p.1‖ * ‖p.2‖ < 1} :=
      isOpen_lt (continuous_fst.norm.mul continuous_snd.norm) continuous_const
    have hi := (contDiffOn_diskImageLogKernel (q.2, q.1) hp).contDiffAt (ho.mem_nhds hp)
    have hswap : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => (p.2, p.1)) q :=
      contDiffAt_snd.prodMk contDiffAt_fst
    exact ((hκ.contDiffAt.comp q contDiffAt_snd).mul (hi.comp q hswap)).contDiffWithinAt
  · have he : (fun p : ℂ × ℂ => κ p.2 * diskImageLogKernel p.2 p.1) =ᶠ[𝓝 q] 0 := by
      have hn : ∀ᶠ p : ℂ × ℂ in 𝓝 q, p.2 ∉ tsupport κ :=
        ((isClosed_tsupport κ).isOpen_compl.preimage continuous_snd).mem_nhds hw
      filter_upwards [hn] with p hp
      have hk : κ p.2 = 0 := by
        by_contra hne
        exact hp (subset_closure hne)
      simp only [hk, zero_mul, Pi.zero_apply]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt



theorem contDiffOn_diskImagePotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * R < 1) (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    ContDiffOn ℝ ∞ (diskImagePotential κ) (Metric.ball (0 : ℂ) R) := by
  have hi := contDiffOn_planeIntegral_of_compact_support (K := tsupport κ)
    isOpen_ball hc (f := fun z w => κ w * diskImageLogKernel w z)
    (fun _ w _ hw => by
      have hk : κ w = 0 := by
        by_contra hne
        exact hw (subset_closure hne)
      simp only [hk, zero_mul])
    (contDiffOn_weighted_diskImageLogKernel hκ hρ hρR hs)
  exact contDiffOn_const.mul hi



theorem contDiffOn_diskRegularizerPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ * R < 1) (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) :
    ContDiffOn ℝ ∞ (diskRegularizerPotential κ) (Metric.ball (0 : ℂ) R) :=
  (contDiff_logarithmicPotential hc hκ).contDiffOn.add
    (contDiffOn_diskImagePotential hc hκ hρ hρR hs)

end DifferentialGeometry.Analysis
