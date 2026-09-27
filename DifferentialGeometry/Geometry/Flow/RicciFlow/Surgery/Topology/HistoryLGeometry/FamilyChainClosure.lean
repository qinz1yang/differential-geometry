import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.FamilyChainGram

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Icc mem_regularizedStage_Ioo LWindow.mem_range_of_mem_Icc from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w : ℝ} {p : (H.stage last).Carrier}

theorem historyLCurve_eq_of_family (Z₀ : H.historyLExpDomain hle T w p)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last) (W : H.LWindow lo hi T)
    {K : Set ℝ} (hK : IsOpen K) {β : ThreeSpace × ℝ → W.X}
    (hβc : ∀ r ∈ K, ContinuousAt (fun s => β (Z₀.1, s)) r)
    (hrep : ∀ j : H.StageInterval lo hi, ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val)
      (H.regularizedStageEnd T W.b j.val),
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
        W.f j (β (Z₀.1, r)))
    (j : H.StageInterval lo hi) {r : ℝ} (hrK : r ∈ K) (hrW : r ∈ Ioo W.a W.b) (hrw : r < w)
    (hr : r ∈ Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
      W.f j (β (Z₀.1, r)) := by
  have ht : T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) := W.mem_Icc_of_mem_piece j hr
  have hr0 : 0 < r := W.nonneg.trans_lt hrW.1
  obtain ⟨lo'', hi'', hlo'', hhi'', W'', hrW'', -, γ'', hγ'', heq''⟩ :=
    (isHistoryLGeodesicOn_historyLCurve Z₀).2.2.1 r ⟨hr0, hrw⟩
  have hj'' := LWindow.mem_range_of_mem_Icc W'' hrW'' ht
  have hQ : ∀ s ∈ Ioo W''.a W''.b, T - s ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ s =
        W''.f ⟨j.val, hj''⟩ (γ'' s) := fun s hs hts =>
    (heq'' ⟨j.val, hj''⟩ (mem_regularizedStage_Icc W''.nonneg ⟨hs.1.le, hs.2.le⟩ hts)).symm
  have key : ∀ (l : Filter ℝ) [l.NeBot], l ≤ 𝓝 r →
      (∀ᶠ s in l, T - s ^ 2 ∈ Ioo (H.time j.val) (H.stageEndTime j.val)) →
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
        W.f j (β (Z₀.1, r)) := by
    intro l _ hl hstage
    have hc1 : Tendsto (fun s => W.f j (β (Z₀.1, s))) l (𝓝 (W.f j (β (Z₀.1, r)))) :=
      (((W.localDiffeomorph j).contMDiff.continuous.continuousAt.comp
        (hβc r hrK)).tendsto).mono_left hl
    have hc2 : Tendsto (fun s => W''.f ⟨j.val, hj''⟩ (γ'' s)) l
        (𝓝 (W''.f ⟨j.val, hj''⟩ (γ'' r))) :=
      (((W''.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
        (hγ'' r hrW'').2.1.continuousAt).tendsto).mono_left hl
    have hev : (fun s => W''.f ⟨j.val, hj''⟩ (γ'' s)) =ᶠ[l] fun s => W.f j (β (Z₀.1, s)) := by
      filter_upwards [hl (isOpen_Ioo.mem_nhds hrW''), hl (isOpen_Ioo.mem_nhds hrW),
        hl (hK.mem_nhds hrK), hstage] with s h1 h2 h3 h4
      rw [← hQ s h1 ⟨h4.1.le, h4.2.le⟩]
      exact hrep j s ⟨h3, mem_regularizedStage_Ioo W.nonneg h2 h4⟩
    rw [hQ r hrW'' ht]
    exact tendsto_nhds_unique (hc2.congr' hev) hc1
  have hcont : Continuous fun s : ℝ => T - s ^ 2 := by fun_prop
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · refine key (𝓝[<] r) nhdsWithin_le_nhds ?_
    filter_upwards [nhdsWithin_le_nhds (hcont.continuousAt.eventually_lt continuousAt_const hlt),
      Ioo_mem_nhdsLT hr0] with s h1 h2
    refine ⟨?_, h1⟩
    have : s ^ 2 < r ^ 2 := pow_lt_pow_left₀ h2.2 h2.1.le two_ne_zero
    linarith [ht.1]
  · have hlt : H.time j.val < T - r ^ 2 := by
      rw [heq]
      rcases j with ⟨j, h1, h2⟩
      cases j using Fin.lastCases with
      | last =>
        exfalso
        have hup := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
          (H.stageEndTime_le_horizon hi)
        have h2' : W.a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hrW.1 W.nonneg two_ne_zero
        simp only [stageEndTime_last] at heq
        linarith
      | cast i =>
        simp only [stageEndTime_castSucc]
        exact H.time_strictMono i.castSucc_lt_succ
    refine key (𝓝[>] r) nhdsWithin_le_nhds ?_
    filter_upwards [nhdsWithin_le_nhds (continuousAt_const.eventually_lt hcont.continuousAt hlt),
      Ioo_mem_nhdsGT (show r < r + 1 by linarith)] with s h1 h2
    refine ⟨?_, ?_⟩
    · linarith
    · have : r ^ 2 < s ^ 2 := pow_lt_pow_left₀ h2.1 hr0.le two_ne_zero
      linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
