import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.ClosedStart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.StageMonotonicity

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature

open private mem_Ioo_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.IndexForm.WindowChain

universe u

variable {H : ObservedHistory.{u}} {first last k : Fin (H.eventCount + 1)} {T B : ℝ}
  {p : (H.stage last).Carrier}

private theorem eventually_sub_sq_not_mem_range {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y in 𝓝[<] x, T - y ^ 2 ∉ range H.time := by
  have hall : ∀ j : Fin (H.eventCount + 1), ∀ᶠ y in 𝓝[<] x, T - y ^ 2 ≠ H.time j := by
    intro j
    rcases eq_or_ne (T - x ^ 2) (H.time j) with h | h
    · filter_upwards [Ioo_mem_nhdsLT hx] with y hy
      have : y ^ 2 < x ^ 2 := pow_lt_pow_left₀ hy.2 hy.1.le two_ne_zero
      intro hy'
      linarith
    · have hc : ContinuousAt (fun y : ℝ => T - y ^ 2) x := by fun_prop
      exact nhdsWithin_le_nhds (hc.eventually_ne h)
  filter_upwards [(Filter.eventually_all.2 hall)] with y hy
  rintro ⟨j, hj⟩
  exact hy j hj.symm

private theorem historyReducedJacobianAlong_congr {first' : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {hle' : first' ≤ last} {w w' : ℝ}
    (Z : H.historyLExpDomain hle T w p) (Z' : H.historyLExpDomain hle' T w' p) (hZ : Z'.1 = Z.1)
    {v : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hvw' : v ≤ w') :
    H.historyReducedJacobianAlong Z' v = H.historyReducedJacobianAlong Z v := by
  unfold historyReducedJacobianAlong
  rw [dite_eq_left ⟨hv, hvw'⟩, dite_eq_left ⟨hv, hvw⟩]
  exact historyReducedJacobian_congr rfl _ _ _ _ hZ

variable (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

private theorem historyReducedJacobianAlong_le_of_not_mem_range {hle : first ≤ last} {w : ℝ}
    (Z : H.historyLExpDomain hle T w p) (hZ : Z.1 ∈ H.historyMinDomain hle T B w p)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbw : b ≤ w) (haF : T - a ^ 2 ∉ range H.time)
    (hbF : T - b ^ 2 ∉ range H.time) :
    H.historyReducedJacobianAlong Z b ≤ H.historyReducedJacobianAlong Z a := by
  have hb : 0 < b := ha.trans_le hab
  have hbd := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z hb hbw)
  have hkl := historyStage_le_last Z hb hbw
  have hT := stageDomain_last_of_historyLExpDomain Z
  have hTh : T - b ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
    nlinarith [pow_pos hb 2]
  let Zb : H.historyLExpDomain hkl T b p := ⟨Z.1, mem_historyLExpDomain_historyStage Z hb hbw⟩
  have hZb : Zb.1 ∈ H.historyMinDomain hkl T B b p :=
    mem_historyMinDomain_of_le hfloor hkl hb hbw hbd hZ
  have h := historyReducedJacobianAlong_le hfloor hb (mem_Ioo_of_mem_stageDomain hbd hbF hTh) Zb
    hZb ha hab le_rfl haF hbF
  rwa [historyReducedJacobianAlong_congr Z Zb rfl hb hbw le_rfl,
    historyReducedJacobianAlong_congr Z Zb rfl ha (hab.trans hbw) hab] at h

private theorem tendsto_historyReducedJacobianAlong_nhdsLT {hle : first ≤ last} {w : ℝ}
    (Z : H.historyLExpDomain hle T w p) (hZ : Z.1 ∈ H.historyMinDomain hle T B w p) {b : ℝ}
    (hb : 0 < b) (hbw : b ≤ w) :
    Tendsto (H.historyReducedJacobianAlong Z) (𝓝[<] b)
      (𝓝 (H.historyReducedJacobianAlong Z b)) := by
  have hbd := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z hb hbw)
  have hkl := historyStage_le_last Z hb hbw
  let Zb : H.historyLExpDomain hkl T b p := ⟨Z.1, mem_historyLExpDomain_historyStage Z hb hbw⟩
  have hZb : Zb.1 ∈ H.historyMinDomain hkl T B b p :=
    mem_historyMinDomain_of_le hfloor hkl hb hbw hbd hZ
  have hc := (continuousWithinAt_historyReducedJacobianAlong_of_mem_historyMinDomain hfloor hb Zb
    hZb).mono (Iio_subset_Iic_self (a := b))
  have heq : H.historyReducedJacobianAlong Zb b = H.historyReducedJacobianAlong Z b :=
    historyReducedJacobianAlong_congr Z Zb rfl hb hbw le_rfl
  rw [← heq]
  refine hc.tendsto.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hb] with y hy
  exact historyReducedJacobianAlong_congr Z Zb rfl hy.1 (hy.2.le.trans hbw) hy.2.le

theorem historyReducedJacobianAlong_antitoneOn {hle : first ≤ last} {w : ℝ}
    (Z : H.historyLExpDomain hle T w p) (hZ : Z.1 ∈ H.historyMinDomain hle T B w p) :
    AntitoneOn (H.historyReducedJacobianAlong Z) (Ioc 0 w) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hstep : ∀ a' ∈ Ioo 0 a, T - a' ^ 2 ∉ range H.time →
      H.historyReducedJacobianAlong Z b ≤ H.historyReducedJacobianAlong Z a' := by
    intro a' ha' ha'F
    refine le_of_tendsto (tendsto_historyReducedJacobianAlong_nhdsLT hfloor Z hZ hb.1 hb.2) ?_
    filter_upwards [Ioo_mem_nhdsLT hlt, eventually_sub_sq_not_mem_range hb.1] with b' hb' hb'F
    exact historyReducedJacobianAlong_le_of_not_mem_range hfloor Z hZ ha'.1
      (ha'.2.trans hb'.1).le (hb'.2.le.trans hb.2) ha'F hb'F
  refine ge_of_tendsto (tendsto_historyReducedJacobianAlong_nhdsLT hfloor Z hZ ha.1 ha.2) ?_
  filter_upwards [Ioo_mem_nhdsLT ha.1, eventually_sub_sq_not_mem_range ha.1] with a' ha' ha'F
  exact hstep a' ha' ha'F

theorem historyReducedJacobian_le_of_le {hle : first ≤ last} (hfk : first ≤ k) (hkl : k ≤ last)
    {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    (Z : H.historyLExpDomain hle T v₂ p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v₂ p) :
    H.historyReducedJacobian hle T v₂ p Z ≤
      H.historyReducedJacobian hkl T v₁ p
        ⟨Z.1, mem_historyLExpDomain_of_le hfk hkl hv₁ h12 hk Z.2⟩ := by
  have hv₂ : 0 < v₂ := hv₁.trans_le h12
  rw [← historyReducedJacobianAlong_eq Z hv₂ le_rfl hle (isHistoryLGeodesicOn_historyLCurve Z).1 Z
    rfl, ← historyReducedJacobianAlong_eq Z hv₁ h12 hkl hk _ rfl]
  exact historyReducedJacobianAlong_antitoneOn hfloor Z hZ ⟨hv₁, h12⟩ ⟨hv₂, le_rfl⟩ h12

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
