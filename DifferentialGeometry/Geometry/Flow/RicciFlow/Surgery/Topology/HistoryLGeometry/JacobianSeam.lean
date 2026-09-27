import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.AntitoneOffFinite

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

open private mem_regularizedStage_Icc from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private LWindowChain.exists_contMDiff_eqOn from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w B₀ : ℝ} {p : (H.stage last).Carrier}

theorem time_lt_stageEndTime_or_eq_last (j : Fin (H.eventCount + 1)) :
    H.time j < H.stageEndTime j ∨ j = Fin.last H.eventCount := by
  cases j using Fin.lastCases with
  | last => exact Or.inr rfl
  | cast i =>
    left
    rw [stageEndTime_castSucc]
    exact H.time_strictMono i.castSucc_lt_succ

theorem historyReducedJacobianAlong_eq_split
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) (γ : ℝ → W.X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    {v₀ v' : ℝ} (hv₀ : 0 < v₀) (hlt : v₀ < v') (hv₀W : v₀ ∈ Ioo W.a W.b)
    (hv'W : v' ∈ Ioo W.a W.b) (hv'w : v' ≤ w)
    (hrepcl : ∀ j : H.StageInterval lo hi, ∀ r ∈ Icc v₀ v',
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
        W.f j (γ r))
    {κ₀ κ' : Fin (H.eventCount + 1)} (hκ₀l : κ₀ ≤ last) (hfκ' : first ≤ κ') (hκ'l : κ' ≤ last)
    (hκ₀ : T - v₀ ^ 2 ∈ H.stageDomain κ₀) (hκ' : T - v' ^ 2 ∈ H.stageDomain κ')
    (Zv₀ : H.historyLExpDomain hκ₀l T v₀ p) (hZv₀ : Zv₀.1 = Z₀.1) :
    H.historyReducedJacobianAlong Z₀ v' =
      H.historyLJacobianDensity hle T w p Z₀ ⟨κ', hfκ', hκ'l⟩ v' / H.historyLSourceDensity T p *
        Real.exp (-(H.historyLAction hκ₀l T v₀ p Zv₀ + lRegularizedAction W.S T γ v₀ v') /
          (2 * v') - (3 / 2 : ℝ) * Real.log (v' ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
  have hv' : 0 < v' := hv₀.trans hlt
  have hmem' := mem_historyLExpDomain_of_le hfκ' hκ'l hv' hv'w hκ' Z₀.2
  rw [historyReducedJacobianAlong_eq Z₀ hv' hv'w hκ'l hκ' ⟨Z₀.1, hmem'⟩ rfl]
  unfold historyReducedJacobian
  rw [historyLJacobianDensity_domain hw Z₀ hZo hfκ' hκ'l hv' hv'w hκ' ⟨Z₀.1, hmem'⟩ rfl,
    historyLAction_split_of_eqOn hfloor hw Z₀ hZmin hlo hhi W γ hγ hv₀ hlt hv₀W hv'W hv'w hrepcl
      hκ₀l hκ'l hκ₀ hκ' Zv₀ ⟨Z₀.1, hmem'⟩ hZv₀ rfl]

theorem exists_tendsto_seam_historyReducedJacobianAlong
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    (hwk : T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) {v : ℝ} (hv : 0 < v)
    (hvw : v < w) (hvS : T - v ^ 2 ∈ range H.time) :
    ∃ L, Tendsto (H.historyReducedJacobianAlong Z₀) (𝓝[<] v) (𝓝 L) ∧
      Tendsto (H.historyReducedJacobianAlong Z₀) (𝓝[>] v) (𝓝 L) := by
  classical
  have hZo := historyMinDomain_subset_historyLExpOpenDomain hw hwk hfloor hZmin
  have hT := stageDomain_last_of_historyLExpDomain Z₀
  obtain ⟨j, hj⟩ := hvS
  have hvw2 : v ^ 2 < w ^ 2 := pow_lt_pow_left₀ hvw hv.le two_ne_zero
  have hfirst := H.time_le_of_mem_stageDomain (H.mem_stageDomain_of_mem_Ioo hwk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [H.time_zero] at hj
    linarith [H.time_nonneg first]
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj0
  have hlt : first < i.succ := by
    by_contra h
    have := H.time_strictMono.monotone (not_lt.1 h)
    linarith
  have hlo : first ≤ i.castSucc := Fin.le_castSucc_iff.2 hlt
  have hhi : i.succ ≤ last := by
    by_contra h
    have h1 := H.stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 := H.le_stageEndTime_of_mem_stageDomain hT
    have : 0 < v ^ 2 := pow_pos hv 2
    linarith
  have hsv : Real.sqrt (T - H.time i.succ) = v := by
    rw [hj, sub_sub_cancel, Real.sqrt_sq hv.le]
  obtain ⟨V, hV, hZ₀V, -, hVdom, W, K, hK, hwK, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_seam_window_family_historyLCurve hw hZo i hlo hhi
      (by rw [hsv]; exact ⟨hv, hvw⟩)
  have hlims := tendsto_historyLJacobianDensity_seam (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V
    hVdom hK hKW hβ hgeo hrep hwK
  rw [hsv] at hwK hlims
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK v hwK
  set δ := min ε (min v (w - v)) with hδ
  have hδ0 : 0 < δ := lt_min hε (lt_min hv (by linarith))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδv : δ ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hδw : δ ≤ w - v := (min_le_right _ _).trans (min_le_right _ _)
  have hK' : Ioo (v - 3 * δ / 4) (v + 3 * δ / 4) ⊆ K := fun r hr => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  have hβZ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => β (Z₀.1, s)) K :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hZ₀V, hs⟩
  have hβc : ∀ r ∈ K, ContinuousAt (fun s => β (Z₀.1, s)) r := fun r hr =>
    (hβZ r hr).continuousWithinAt.continuousAt (hK.mem_nhds hr)
  obtain ⟨γ, hγ, hγeq⟩ := LWindowChain.exists_contMDiff_eqOn (a := v - δ / 2) (b := v + δ / 2)
    (by linarith) (show 0 < δ / 4 by positivity) (hβZ.mono (fun r hr => hK' ⟨by linarith [hr.1],
      by linarith [hr.2]⟩))
  set v₀ := v - δ / 2 with hv₀def
  have hv₀ : 0 < v₀ := by linarith
  have hv₀w : v₀ ≤ w := by linarith
  have hmem₀ := mem_historyLExpDomain_historyStage Z₀ hv₀ hv₀w
  have hκ₀ := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv₀ hv₀w)
  have hinK : ∀ r ∈ Icc v₀ (v + δ / 2), r ∈ K ∧ γ r = β (Z₀.1, r) := fun r hr =>
    ⟨hK' ⟨by linarith [hr.1], by linarith [hr.2]⟩, hγeq ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  have hsplit : ∀ v' ∈ Ioo v₀ (v + δ / 2), ∀ {κ' : Fin (H.eventCount + 1)} (hfκ' : first ≤ κ')
      (hκ'l : κ' ≤ last), T - v' ^ 2 ∈ H.stageDomain κ' →
      H.historyReducedJacobianAlong Z₀ v' =
        H.historyLJacobianDensity hle T w p Z₀ ⟨κ', hfκ', hκ'l⟩ v' / H.historyLSourceDensity T p *
          Real.exp (-(H.historyLAction (historyStage_le_last Z₀ hv₀ hv₀w) T v₀ p ⟨Z₀.1, hmem₀⟩ +
            lRegularizedAction W.S T γ v₀ v') / (2 * v') - (3 / 2 : ℝ) * Real.log (v' ^ 2) -
            (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
    intro v' hv' κ' hfκ' hκ'l hκ'
    have hv'w : v' ≤ w := by linarith [hv'.2, hδw]
    refine historyReducedJacobianAlong_eq_split hfloor hw Z₀ hZmin hZo hlo hhi W γ hγ hv₀ hv'.1
      (hKW (hinK v₀ ⟨le_rfl, by linarith⟩).1) (hKW (hinK v' ⟨hv'.1.le, hv'.2.le⟩).1) hv'w
      (fun j r hr ht => ?_) (historyStage_le_last Z₀ hv₀ hv₀w) hfκ' hκ'l hκ₀ hκ' ⟨Z₀.1, hmem₀⟩ rfl
    have hr' := hinK r ⟨hr.1, hr.2.trans hv'.2.le⟩
    rw [hr'.2]
    have hrW := hKW hr'.1
    exact historyLCurve_eq_of_family Z₀ hlo hhi W hK hβc (hrep Z₀.1 hZ₀V) j hr'.1 hrW
      (by linarith [hr.2, hv'.2, hδw]) (mem_regularizedStage_Icc W.nonneg ⟨hrW.1.le, hrW.2.le⟩ ht)
  have hU : IsOpen {s : ℝ | T - s ^ 2 ∈ W.D.regular} := W.D.regular_isOpen.preimage (by fun_prop)
  have hLcont : ContinuousOn (lRegularizedLagrangian W.S T γ)
      {s : ℝ | T - s ^ 2 ∈ W.D.regular} := by
    have hc := lRegularizedLagrangian_continuousOn_carrier W.S W.solution γ (hγ.of_le (by decide))
    have hh := hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s (hs : s ∈ {s : ℝ | T - s ^ 2 ∈ W.D.regular}) =>
        (W.D.regular_subset hs : (T, s).1 - (T, s).2 ^ 2 ∈ W.D.carrier))
    exact hh
  have hreg : ∀ r ∈ Icc v₀ (v + δ / 2), r ∈ {s : ℝ | T - s ^ 2 ∈ W.D.regular} := fun r hr =>
    W.regular r ⟨(hKW (hinK r hr).1).1.le, (hKW (hinK r hr).1).2.le⟩
  have hvreg : v ∈ {s : ℝ | T - s ^ 2 ∈ W.D.regular} := hreg v ⟨by linarith, by linarith⟩
  have hIc : ContinuousAt (fun v' => lRegularizedAction W.S T γ v₀ v') v :=
    (intervalIntegral.integral_hasDerivAt_right
      ((hLcont.mono fun r hr => hreg r ⟨hr.1, hr.2.trans (by linarith)⟩).intervalIntegrable_of_Icc
        (by linarith))
      (hLcont.stronglyMeasurableAtFilter hU v hvreg)
      (hLcont.continuousAt (hU.mem_nhds hvreg))).continuousAt
  have hgc : ContinuousAt (fun v' => Real.exp (-(H.historyLAction (historyStage_le_last Z₀ hv₀ hv₀w)
      T v₀ p ⟨Z₀.1, hmem₀⟩ + lRegularizedAction W.S T γ v₀ v') / (2 * v') -
      (3 / 2 : ℝ) * Real.log (v' ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))) v := by
    refine Real.continuous_exp.continuousAt.comp ?_
    refine ((((continuousAt_const.add hIc).neg).div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero two_ne_zero hv.ne')).sub (continuousAt_const.mul ?_)).sub continuousAt_const
    exact ((continuous_pow 2).continuousAt).log (pow_ne_zero 2 hv.ne')
  refine ⟨_, ((hlims.1.div_const (H.historyLSourceDensity T p)).mul
    (hgc.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_, ((hlims.2.div_const
      (H.historyLSourceDensity T p)).mul (hgc.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_⟩
  · have hcont : Continuous fun s : ℝ => T - s ^ 2 := by fun_prop
    have hlt' : T - v ^ 2 < H.stageEndTime i.succ := by
      rcases time_lt_stageEndTime_or_eq_last (H := H) i.succ with h | h
      · rw [← hj]; exact h
      · rw [h, stageEndTime_last]
        have := (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
        have : 0 < v ^ 2 := pow_pos hv 2
        linarith
    filter_upwards [Ioo_mem_nhdsLT (show v₀ < v by linarith), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hcont.continuousAt.eventually_lt continuousAt_const hlt')]
      with v' hv' hv'v hv'e
    refine (hsplit v' ⟨hv'.1, hv'.2.trans (by linarith)⟩ (hlo.trans i.castSucc_lt_succ.le) hhi
      (H.mem_stageDomain_of_mem_Ioo ⟨?_, hv'e⟩)).symm
    rw [hj]
    have : v' ^ 2 < v ^ 2 := pow_lt_pow_left₀ hv'v (by linarith [hv'.1]) two_ne_zero
    linarith
  · have hcont : Continuous fun s : ℝ => T - s ^ 2 := by fun_prop
    have hlt' : H.time i.castSucc < T - v ^ 2 := by
      rw [← hj]
      exact H.time_strictMono i.castSucc_lt_succ
    filter_upwards [Ioo_mem_nhdsGT (show v < v + δ / 2 by linarith), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (continuousAt_const.eventually_lt hcont.continuousAt hlt')]
      with v' hv' hv'v hv'e
    refine (hsplit v' ⟨by linarith [hv'.1], hv'.2⟩ hlo (i.castSucc_lt_succ.le.trans hhi)
      (H.mem_stageDomain_of_mem_Ioo ⟨hv'e, ?_⟩)).symm
    rw [stageEndTime_castSucc, hj]
    have : v ^ 2 < v' ^ 2 := pow_lt_pow_left₀ hv'v hv.le two_ne_zero
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
