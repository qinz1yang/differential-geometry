import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.FamilyChainConjugate

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Icc LWindow.mem_range_of_mem_Icc from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private le_of_mem_stageDomain bounds_of_action_eq_cost absolutelyContinuous_truncate from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Truncation

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w B₀ : ℝ} {p : (H.stage last).Carrier}

theorem historyLAction_split_of_eqOn
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) (γ : ℝ → W.X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ)
    {v v' : ℝ} (hv : 0 < v) (hvv' : v < v') (hvW : v ∈ Ioo W.a W.b) (hv'W : v' ∈ Ioo W.a W.b)
    (hv'w : v' ≤ w)
    (hrepcl : ∀ j : H.StageInterval lo hi, ∀ r ∈ Icc v v',
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) →
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
        W.f j (γ r))
    {κ κ' : Fin (H.eventCount + 1)} (hκl : κ ≤ last) (hκ'l : κ' ≤ last)
    (hκ : T - v ^ 2 ∈ H.stageDomain κ) (hκ' : T - v' ^ 2 ∈ H.stageDomain κ')
    (Zv : H.historyLExpDomain hκl T v p) (Zv' : H.historyLExpDomain hκ'l T v' p)
    (hZv : Zv.1 = Z₀.1) (hZv' : Zv'.1 = Z₀.1) :
    H.historyLAction hκ'l T v' p Zv' =
      H.historyLAction hκl T v p Zv + lRegularizedAction W.S T γ v v' := by
  obtain ⟨α, hgeo, hinit, hac, hp, hmin₀, hfin⟩ := hZmin
  have hmin : H.regularizedExtendedAction first last T B₀ 0 w α =
      H.regularizedCost first last hle T B₀ 0 w (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ w) := by rw [hp]; exact hmin₀
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have hv' : 0 < v' := hv.trans hvv'
  have hfκ' : first ≤ κ' := first_le_of_mem_stageDomain hv'.le hv'w hlower hκ'
  have hfκ : first ≤ κ := first_le_of_mem_stageDomain hv.le (hvv'.le.trans hv'w) hlower hκ
  have hκ'κ : κ' ≤ κ := le_of_mem_stageDomain hκ' hκ (by nlinarith)
  have hZmin' : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p := ⟨α, hgeo, hinit, hac, hp, hmin₀, hfin⟩
  have hminv' : Zv'.1 ∈ H.historyMinDomain hκ'l T B₀ v' p := by
    rw [hZv']; exact mem_historyMinDomain_of_le hfloor hκ'l hv' hv'w hκ' hZmin'
  have hminv : Zv.1 ∈ H.historyMinDomain hκl T B₀ v p := by
    rw [hZv]; exact mem_historyMinDomain_of_le hfloor hκl hv (hvv'.le.trans hv'w) hκ hZmin'
  have e1' := regularizedExtendedAction_historyLCurve_eq_historyLAction hfloor hv' Zv' hminv'
  have e1 := regularizedExtendedAction_historyLCurve_eq_historyLAction hfloor hv Zv hminv
  have hgeo' := isHistoryLGeodesicOn_truncate hfloor hfκ' hκ'l hv' hv'w hκ' hgeo hac hmin hfin
  have hgeoκ := isHistoryLGeodesicOn_truncate hfloor hfκ hκl hv (hvv'.le.trans hv'w) hκ hgeo hac
    hmin hfin
  have hinit' := hinit.truncate hv' hfκ' hκ'
  have hinitκ := hinit.truncate hv hfκ hκ
  rw [← hZv'] at hinit'
  rw [← hZv] at hinitκ
  have e2' := regularizedExtendedAction_historyLCurve_eq (B := B₀) hv' Zv' hgeo' hinit'
  have e2 := regularizedExtendedAction_historyLCurve_eq (B := B₀) hv Zv hgeoκ hinitκ
  have hac' := absolutelyContinuous_truncate hfκ' hv'.le hv'w hupper hlower hκ' hac
  have hsplit := H.regularizedExtendedAction_eq_add_at_parameter κ hκ'κ hκl le_rfl hv.le hvv'.le hκ
    (fun t ht x => hfloor κ _ (H.mapsTo_regularizedStage_Ioo T 0 v' κ ht) x)
    (fun j : H.StageInterval κ' last => α ⟨j.val, hfκ'.trans j.property.1, j.property.2⟩)
    (B := B₀) hac'
  have hrκ := LWindow.mem_range_of_mem_Icc W hvW
    ⟨H.time_le_of_mem_stageDomain hκ, H.le_stageEndTime_of_mem_stageDomain hκ⟩
  have hrκ' := LWindow.mem_range_of_mem_Icc W hv'W
    ⟨H.time_le_of_mem_stageDomain hκ', H.le_stageEndTime_of_mem_stageDomain hκ'⟩
  let W' := W.restrict hrκ'.1 hrκ.2 hκ'κ hvW.1.le hvv' hv'W.2.le hκ hκ'
  have hγ1 : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ := hγ.of_le (by decide)
  have hint : IntervalIntegrable (lRegularizedLagrangian W.S T γ) MeasureTheory.volume v v' := by
    have hc := lRegularizedLagrangian_continuousOn_carrier W.S W.solution γ hγ1
    have hh := hc.comp (s := Icc v v') (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => W'.mem_carrier ht)
    exact hh.intervalIntegrable_of_Icc hvv'.le
  have hW' := W'.regularizedExtendedAction_eq_coe (B := B₀)
    (fun j t ht x => hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T v v' j.val ht) x)
    (fun j : H.StageInterval κ' κ => α ⟨j.val, hfκ'.trans j.property.1,
      j.property.2.trans hκl⟩) γ
    (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hγ1.contMDiffOn) ?_ hint
  · have hA : (H.historyLAction hκ'l T v' p Zv' : WithTop ℝ) =
        (H.historyLAction hκl T v p Zv : WithTop ℝ) +
          (lRegularizedAction W.S T γ v v' : WithTop ℝ) := by
      rw [← e1', e2', hsplit, ← e1, e2]
      exact congrArg _ hW'
    rw [← WithTop.coe_add] at hA
    exact WithTop.coe_inj.1 hA
  · intro j r hr
    have hrI : r ∈ Icc v v' := W'.piece_subset j hr
    change W.f ⟨j.val, hrκ'.1.trans j.property.1, j.property.2.trans hrκ.2⟩ (γ r) = _
    have hJ : r ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val) :=
      ⟨(regularizedStageStart_le_of_le le_rfl hv.le j.val).trans hr.1,
        hr.2.trans (regularizedStageEnd_le_of_le hv'.le hv'w j.val)⟩
    refine (hrepcl ⟨j.val, hrκ'.1.trans j.property.1, j.property.2.trans hrκ.2⟩ r hrI
      (W'.mem_Icc_of_mem_piece j hr)).symm.trans ?_
    exact eqOn_historyLCurve hw Z₀ hgeo hinit _ hJ

theorem historyLAction_split
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) {K : Set ℝ} (hK : IsOpen K) (hKW : K ⊆ Ioo W.a W.b)
    {β : ThreeSpace × ℝ → W.X} (hβc : ∀ r ∈ K, ContinuousAt (fun s => β (Z₀.1, s)) r)
    (hrep : ∀ j : H.StageInterval lo hi, ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val)
      (H.regularizedStageEnd T W.b j.val),
      H.historyLCurve hle T w p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r =
        W.f j (β (Z₀.1, r)))
    (γ : ℝ → W.X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ) (hγβ : ∀ r ∈ K, γ r = β (Z₀.1, r))
    {v v' : ℝ} (hv : 0 < v) (hvv' : v < v') (hsub : Icc v v' ⊆ K) (hv'w : v' < w)
    {κ κ' : Fin (H.eventCount + 1)} (hκl : κ ≤ last) (hκ'l : κ' ≤ last)
    (hκ : T - v ^ 2 ∈ H.stageDomain κ) (hκ' : T - v' ^ 2 ∈ H.stageDomain κ')
    (Zv : H.historyLExpDomain hκl T v p) (Zv' : H.historyLExpDomain hκ'l T v' p)
    (hZv : Zv.1 = Z₀.1) (hZv' : Zv'.1 = Z₀.1) :
    H.historyLAction hκ'l T v' p Zv' =
      H.historyLAction hκl T v p Zv + lRegularizedAction W.S T γ v v' := by
  have hvW := hKW (hsub (left_mem_Icc.2 hvv'.le))
  have hv'W := hKW (hsub (right_mem_Icc.2 hvv'.le))
  refine historyLAction_split_of_eqOn hfloor hw Z₀ hZmin hlo hhi W γ hγ hv hvv' hvW hv'W hv'w.le
    (fun j r hr ht => ?_) hκl hκ'l hκ hκ' Zv Zv' hZv hZv'
  rw [hγβ r (hsub hr)]
  have hrW := hKW (hsub hr)
  exact historyLCurve_eq_of_family Z₀ hlo hhi W hK hβc hrep j (hsub hr) hrW
    (hr.2.trans_lt hv'w) (mem_regularizedStage_Icc W.nonneg ⟨hrW.1.le, hrW.2.le⟩ ht)

theorem historyLJacobianDensity_domain (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) {κ : Fin (H.eventCount + 1)}
    (hfκ : first ≤ κ) (hκl : κ ≤ last) {v : ℝ} (hv : 0 < v) (hvw : v ≤ w)
    (hκ : T - v ^ 2 ∈ H.stageDomain κ) (Zv : H.historyLExpDomain hκl T v p) (hZv : Zv.1 = Z₀.1) :
    H.historyLJacobianDensity hκl T v p Zv ⟨κ, le_rfl, hκl⟩ v =
      H.historyLJacobianDensity hle T w p Z₀ ⟨κ, hfκ, hκl⟩ v := by
  have hf : H.historyLCurveMap hκl T v p Zv ⟨κ, le_rfl, hκl⟩ v =ᶠ[𝓝 Z₀.1]
      H.historyLCurveMap hle T w p Z₀ ⟨κ, hfκ, hκl⟩ v := by
    filter_upwards [(isOpen_historyLExpOpenDomain hw).mem_nhds hZo] with Z hZ
    have hZd := historyLExpOpenDomain_subset_historyLExpDomain hZ
    have hZv' := mem_historyLExpDomain_of_le hfκ hκl hv hvw hκ hZd
    rw [historyLCurveMap_of_mem _ _ hZv', historyLCurveMap_of_mem _ _ hZd]
    exact historyLExp_eq_historyLCurve_of_mem_historyLExpDomain hfκ hκl hv hvw hκ ⟨Z, hZd⟩
  have h := paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := Z₀)
    ⟨κ, hfκ, hκl⟩ v hf
  obtain ⟨zv, hzv⟩ := Zv
  change zv = Z₀.1 at hZv
  subst hZv
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
