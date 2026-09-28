import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Splitting

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

open private bounds_of_action_eq_cost le_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Truncation
open private exists_mem_Ioo_not_mem_range eq_of_mem_Ioo_of_mem_Icc mem_regularizedStage_Ioo
  not_mem_range_of_mem_Ioo from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity
open private mem_Ioo_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.IndexForm.WindowChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w B₀ : ℝ} {p : (H.stage last).Carrier}

theorem historyLCurve_minimizer (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p) :
    (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (H.historyLCurve hle T w p Z₀ j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) ∧
    H.regularizedExtendedAction first last T B₀ 0 w (H.historyLCurve hle T w p Z₀) =
      H.regularizedCost first last hle T B₀ 0 w (H.historyLCurve hle T w p Z₀ ⟨last, hle, le_rfl⟩ 0)
        (H.historyLCurve hle T w p Z₀ ⟨first, le_rfl, hle⟩ w) ∧
    H.regularizedExtendedAction first last T B₀ 0 w (H.historyLCurve hle T w p Z₀) ≠ ⊤ := by
  obtain ⟨α, hgeo, hinit, hac, hp, hmin₀, hfin⟩ := hZmin
  have hmin : H.regularizedExtendedAction first last T B₀ 0 w α =
      H.regularizedCost first last hle T B₀ 0 w (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ w) := by rw [hp]; exact hmin₀
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have heq := eqOn_historyLCurve hw Z₀ hgeo hinit
  have hb := fun j : H.StageInterval first last =>
    H.regularizedStage_bounds le_rfl hw.le hupper hlower j
  have hext := regularizedExtendedAction_historyLCurve_eq (B := B₀) hw Z₀ hgeo hinit
  have h0 : H.historyLCurve hle T w p Z₀ ⟨last, hle, le_rfl⟩ 0 = α ⟨last, hle, le_rfl⟩ 0 := by
    refine heq _ ⟨?_, ?_⟩
    · rw [H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper]
    · exact (Real.sqrt_nonneg _)
  have hwv : H.historyLCurve hle T w p Z₀ ⟨first, le_rfl, hle⟩ w = α ⟨first, le_rfl, hle⟩ w := by
    refine heq _ ⟨(hb _).2.1.trans_eq ?_, ?_⟩
    · exact H.regularizedStageEnd_eq_of_mem_stageDomain hw.le hlower
    · exact (H.regularizedStageEnd_eq_of_mem_stageDomain hw.le hlower).symm.le
  refine ⟨fun j => Manifold.absolutelyContinuousOnInterval_congr (hac j) ?_, ?_, ?_⟩
  · rw [uIcc_of_le (hb j).2.1]
    exact fun r hr => (heq j hr).symm
  · rw [hext, h0, hwv]
    exact hmin
  · rw [hext]
    exact hfin

variable (H) in
def historyStage (T v : ℝ) : Fin (H.eventCount + 1) :=
  H.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))

theorem mem_stageDomain_historyStage {v : ℝ} (h : T - v ^ 2 ∈ Icc 0 H.horizon) :
    T - v ^ 2 ∈ H.stageDomain (H.historyStage T v) := by
  unfold historyStage
  rw [projIcc_of_mem _ h]
  exact H.activeStage_mem _

theorem historyStage_eq {v : ℝ} {k : Fin (H.eventCount + 1)} (hk : T - v ^ 2 ∈ H.stageDomain k) :
    H.historyStage T v = k := by
  have hI : T - v ^ 2 ∈ Icc 0 H.horizon :=
    ⟨(H.time_nonneg k).trans (H.time_le_of_mem_stageDomain hk),
      (H.le_stageEndTime_of_mem_stageDomain hk).trans (H.stageEndTime_le_horizon k)⟩
  have h := mem_stageDomain_historyStage hI
  exact le_antisymm (le_of_mem_stageDomain h hk le_rfl) (le_of_mem_stageDomain hk h le_rfl)

theorem mem_Icc_of_historyLExpDomain (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ} (hv : 0 < v)
    (hvw : v ≤ w) : T - v ^ 2 ∈ Icc 0 H.horizon := by
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z₀
  obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hasHistoryLInitialVector_historyLCurve Z₀
  have hT : T ∈ H.stageDomain last := by simpa [ha₀] using W₀.upper
  have h1 := H.time_le_of_mem_stageDomain hgeo.1
  have h2 := (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
  have h3 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hv.le hvw 2
  constructor <;> nlinarith [H.time_nonneg first, sq_nonneg v]

theorem stageDomain_last_of_historyLExpDomain (Z₀ : H.historyLExpDomain hle T w p) :
    T ∈ H.stageDomain last := by
  obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hasHistoryLInitialVector_historyLCurve Z₀
  simpa [ha₀] using W₀.upper

theorem historyStage_le_last (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ} (hv : 0 < v)
    (hvw : v ≤ w) : H.historyStage T v ≤ last :=
  le_of_mem_stageDomain (mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv hvw))
    (stageDomain_last_of_historyLExpDomain Z₀) (by nlinarith)

theorem le_historyStage (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ} (hv : 0 < v)
    (hvw : v ≤ w) : first ≤ H.historyStage T v :=
  first_le_of_mem_stageDomain hv.le hvw (isHistoryLGeodesicOn_historyLCurve Z₀).1
    (mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv hvw))

theorem mem_historyLExpDomain_historyStage (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ}
    (hv : 0 < v) (hvw : v ≤ w) :
    (Z₀.1 : TangentSpace ThreeModel p) ∈
      H.historyLExpDomain (historyStage_le_last Z₀ hv hvw) T v p :=
  mem_historyLExpDomain_of_le (le_historyStage Z₀ hv hvw) (historyStage_le_last Z₀ hv hvw) hv hvw
    (mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv hvw)) Z₀.2

variable (H) in
def historyReducedJacobianAlong (Z₀ : H.historyLExpDomain hle T w p) (v : ℝ) : ℝ :=
  if h : 0 < v ∧ v ≤ w then
    H.historyReducedJacobian (historyStage_le_last Z₀ h.1 h.2) T v p
      ⟨Z₀.1, mem_historyLExpDomain_historyStage Z₀ h.1 h.2⟩
  else 0

theorem historyReducedJacobian_congr {v : ℝ} {k k' : Fin (H.eventCount + 1)} (h : k = k')
    (hkl : k ≤ last) (hk'l : k' ≤ last) (Z : H.historyLExpDomain hkl T v p)
    (Z' : H.historyLExpDomain hk'l T v p) (hZ : Z.1 = Z'.1) :
    H.historyReducedJacobian hkl T v p Z = H.historyReducedJacobian hk'l T v p Z' := by
  subst h
  obtain ⟨z, hz⟩ := Z
  obtain ⟨z', hz'⟩ := Z'
  change z = z' at hZ
  subst hZ
  rfl

theorem historyReducedJacobianAlong_eq (Z₀ : H.historyLExpDomain hle T w p) {v : ℝ} (hv : 0 < v)
    (hvw : v ≤ w) {k : Fin (H.eventCount + 1)} (hkl : k ≤ last) (hk : T - v ^ 2 ∈ H.stageDomain k)
    (Zv : H.historyLExpDomain hkl T v p) (hZ : Zv.1 = Z₀.1) :
    H.historyReducedJacobianAlong Z₀ v = H.historyReducedJacobian hkl T v p Zv := by
  unfold historyReducedJacobianAlong
  rw [dite_eq_left ⟨hv, hvw⟩]
  exact historyReducedJacobian_congr (historyStage_eq hk) _ _ _ _ hZ.symm

theorem linearIndependent_historyLJacobiField_congr {Z₀ : H.historyLExpDomain hle T w p}
    (J J' : H.StageInterval first last) (hJ : J.val = J'.val) {r r' : ℝ} (hr : r = r')
    (h : LinearIndependent ℝ fun i => (H.historyLJacobiField hle T w p Z₀ J i r : ThreeSpace)) :
    LinearIndependent ℝ fun i => (H.historyLJacobiField hle T w p Z₀ J' i r' : ThreeSpace) := by
  obtain rfl : J = J' := Subtype.ext hJ
  subst hr
  exact h

theorem exists_family_chain_linearIndependent {B₀ : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    (hZo : Z₀.1 ∈ H.historyLExpOpenDomain hle T w p) {v : ℝ} (hv : 0 < v) (hvw : v < w)
    {κ : Fin (H.eventCount + 1)} (hfκ : first ≤ κ) (hκl : κ ≤ last)
    (hvk : T - v ^ 2 ∈ Ioo (H.time κ) (H.stageEndTime κ)) :
    ∃ ch : H.LFamilyChain hle hfκ T w v p Z₀, 0 < ch.n ∧
      LinearIndependent ℝ fun i => ch.jacobiField i (ch.n - 1) v := by
  classical
  have hT := stageDomain_last_of_historyLExpDomain Z₀
  obtain ⟨hac, hmin, hfin⟩ := historyLCurve_minimizer hw Z₀ hZmin
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z₀
  obtain ⟨w', hw'I, hw'F⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) hv le_rfl
  obtain ⟨ch, -⟩ := exists_lFamilyChain hw Z₀ hZo hT hv hvw hfκ hvk hw'I.1 hw'I.2 hw'F
  have hn : 0 < ch.n := Nat.pos_of_ne_zero fun h => by
    have := ch.c_n
    rw [h, ch.c_zero] at this
    linarith
  obtain ⟨v', hv'I, hv'F⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) hvw hv.le
  have hv'0 : 0 < v' := hv.trans hv'I.1
  have hv'd := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv'0 hv'I.2.le)
  have hTh : T - v' ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
    nlinarith
  have hv'k := mem_Ioo_of_mem_stageDomain hv'd hv'F hTh
  obtain ⟨ch', m, hm0, hmn, hcm⟩ := exists_lFamilyChain hw Z₀ hZo hT hv'0 hv'I.2
    (le_historyStage Z₀ hv'0 hv'I.2.le) hv'k hv hv'I.1 (not_mem_range_of_mem_Ioo hvk)
  obtain ⟨k₀, rfl⟩ : ∃ k₀, m = k₀ + 1 := ⟨m - 1, by omega⟩
  have hli' := ch'.linearIndependent_historyLJacobiField hfloor hgeo hac hmin hfin hv'0 hv'I.2.le
    (historyStage_le_last Z₀ hv'0 hv'I.2.le) hv'd hmn
  have hst : ch'.stage (k₀ + 1) = κ := by
    have h := ch'.mem_stageDomain (k₀ + 1) hmn.le
    rw [hcm] at h
    exact eq_of_mem_Ioo_of_mem_Icc hvk
      ⟨H.time_le_of_mem_stageDomain h, H.le_stageEndTime_of_mem_stageDomain h⟩
  have hu := linearIndependent_historyLJacobiField_congr (J' := ⟨κ, hfκ, hκl⟩) _ hst hcm hli'
  refine ⟨ch, hn, ?_⟩
  have hk : ch.n - 1 < ch.n := Nat.sub_lt hn one_pos
  have hvK := ch.mem_K_last hn
  have hone := (ch.bump_last hn).self_of_nhds
  have hvW : v ∈ Ioo (ch.W (ch.n - 1)).a (ch.W (ch.n - 1)).b := ch.K_W _ ⟨hvK, hv⟩
  have hstage : ch.stage (ch.n - 1 + 1) = κ := by rw [Nat.sub_add_cancel hn, ch.stage_n]
  have hvpiece : v ∈ Ioo (H.regularizedStageStart T (ch.W (ch.n - 1)).a (ch.bottom hk).val)
      (H.regularizedStageEnd T (ch.W (ch.n - 1)).b (ch.bottom hk).val) := by
    refine mem_regularizedStage_Ioo (ch.W _).nonneg hvW ?_
    change T - v ^ 2 ∈ Ioo (H.time (ch.stage (ch.n - 1 + 1)))
      (H.stageEndTime (ch.stage (ch.n - 1 + 1)))
    rw [hstage]
    exact hvk
  have hpush := fun i => ch.mfderiv_jacobiField_eq (ch.bottom hk) i hvK hv hvpiece hone
  have hu'' := linearIndependent_historyLJacobiField_congr _
    ⟨(ch.bottom hk).val, (hfκ.trans (ch.first_le (ch.n - 1))).trans (ch.bottom hk).property.1,
      (ch.bottom hk).property.2.trans (ch.le_last _)⟩ hstage.symm rfl hu
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : ∑ i, g i • (mfderiv ThreeModel ThreeModel ((ch.W (ch.n - 1)).f (ch.bottom hk))
      (ch.γ (ch.n - 1) v) (ch.jacobiField i (ch.n - 1) v) : ThreeSpace) = 0 := by
    refine (mfderiv_sum_smul ((ch.W (ch.n - 1)).f (ch.bottom hk)) (ch.γ (ch.n - 1) v)
      Finset.univ g (fun i => (ch.jacobiField i (ch.n - 1) v : ThreeSpace))).symm.trans ?_
    exact (congrArg (fun y : ThreeSpace => (mfderiv ThreeModel ThreeModel
      ((ch.W (ch.n - 1)).f (ch.bottom hk)) (ch.γ (ch.n - 1) v) y : ThreeSpace)) hg).trans
      (map_zero _)
  simp only [hpush] at h0
  exact Fintype.linearIndependent_iff.1 hu'' g h0

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
