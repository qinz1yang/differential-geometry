import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.ClosedStart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.UpperSemicontinuity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Icc mem_regularizedStage_Ioo eq_of_mem_Ioo_of_mem_Icc
  LWindow.mem_range_of_mem_Icc from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity

open private isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.ClosedStart
open private exists_lRegularizedSpeedSq_le_of_closedStart from
DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedStartVelocity

universe u

variable {H : ObservedHistory.{u}}

private theorem stageRegularizedLagrangian_congr_of_eventuallyEq (j : Fin (H.eventCount + 1))
    (T : ℝ) {α β : ℝ → (H.stage j).Carrier} {s : ℝ} (h : α =ᶠ[𝓝 s] β) :
    H.stageRegularizedLagrangian j T α s = H.stageRegularizedLagrangian j T β s := by
  have hval : α s = β s := h.self_of_nhds
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) h
  have hvel : lVelocity (I := ThreeModel) α s = lVelocity (I := ThreeModel) β s := by
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

private theorem mem_Ioo_of_mem_regularizedStage_Ioo {j : Fin (H.eventCount + 1)} {T u v r : ℝ}
    (hr : r ∈ Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)) :
    T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) := by
  have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.1
  have h1 := (Real.sqrt_lt' hr0).1 hr.1
  have h2 := (Real.lt_sqrt hr0.le).1 hr.2
  constructor
  · have := le_max_right (T - v ^ 2) (H.time j)
    linarith
  · have := min_le_right (T - u ^ 2) (H.stageEndTime j)
    linarith

private theorem continuousOn_lRegularizedLagrangian_of_window {lo hi : Fin (H.eventCount + 1)}
    {T : ℝ} (W : H.LWindow lo hi T) {γ : ℝ → W.X} {K J : Set ℝ} (hK : IsOpen K)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ K) (hJK : J ⊆ K)
    (hcar : ∀ s ∈ J, T - s ^ 2 ∈ W.D.carrier) :
    ContinuousOn (lRegularizedLagrangian W.S T γ) J := by
  have hsnd : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1
      (Prod.snd : ThreeSpace × ℝ → ℝ) (univ ×ˢ K) := contMDiff_snd.contMDiffOn
  have hfam : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel 1
      (γ ∘ (Prod.snd : ThreeSpace × ℝ → ℝ)) (univ ×ˢ K) :=
    ContMDiffOn.comp (t := K) hγ hsnd fun q hq => hq.2
  have h := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one W.S W.solution T
    isOpen_univ hK hfam hJK hcar
  have hs : ContinuousOn (fun s : ℝ => ((0 : ThreeSpace), s)) J := by fun_prop
  have hmaps : MapsTo (fun s : ℝ => ((0 : ThreeSpace), s)) J (univ ×ˢ J) :=
    fun s hs => ⟨trivial, hs⟩
  have hγeq : (fun r => (γ ∘ (Prod.snd : ThreeSpace × ℝ → ℝ)) ((0 : ThreeSpace), r)) = γ := rfl
  refine (h.comp hs hmaps).congr fun s _ => ?_
  exact congrArg (fun β => lRegularizedLagrangian W.S T β s) hγeq.symm

private theorem local_of_window {j lo hi : Fin (H.eventCount + 1)} {T : ℝ}
    (W : H.LWindow lo hi T) (hj : lo ≤ j ∧ j ≤ hi) {β : ℝ → (H.stage j).Carrier}
    {a b s₀ ε : ℝ} (hε : 0 < ε) {γ : ℝ → W.X}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Ioo (s₀ - 2 * ε) (s₀ + 2 * ε)))
    (hcar : ∀ r ∈ Icc (s₀ - ε) (s₀ + ε), T - r ^ 2 ∈ W.D.carrier)
    (heq : ∀ r ∈ Icc a b ∩ Icc (s₀ - ε) (s₀ + ε), β r = W.f ⟨j, hj⟩ (γ r))
    (hmet : ∀ r ∈ Ioo a b ∩ Ioo (s₀ - ε) (s₀ + ε),
      r ∈ Ioo (H.regularizedStageStart T W.a j) (H.regularizedStageEnd T W.b j)) :
    (∀ x y, x ≤ y → Icc x y ⊆ Icc a b ∩ Icc (s₀ - ε) (s₀ + ε) →
      Manifold.absolutelyContinuousOnInterval ThreeModel β x y) ∧
    ∃ C, ∀ r ∈ Ioo a b ∩ Ioo (s₀ - ε) (s₀ + ε), |H.stageRegularizedLagrangian j T β r| ≤ C := by
  have hsub : Icc (s₀ - ε) (s₀ + ε) ⊆ Ioo (s₀ - 2 * ε) (s₀ + 2 * ε) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (W.f ⟨j, hj⟩ ∘ γ)
      (Ioo (s₀ - 2 * ε) (s₀ + 2 * ε)) :=
    ((W.localDiffeomorph _).contMDiff.of_le (by decide)).comp_contMDiffOn hγ
  refine ⟨fun x y hxy hxyS => ?_, ?_⟩
  · have hac := Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (a := x) (b := y)
      (hfγ.mono (by rw [uIcc_of_le hxy]; exact fun r hr => hsub (hxyS hr).2))
    refine Manifold.absolutelyContinuousOnInterval_congr hac fun r hr => ?_
    rw [uIcc_of_le hxy] at hr
    exact (heq r (hxyS hr)).symm
  · have hcont := continuousOn_lRegularizedLagrangian_of_window W isOpen_Ioo hγ hsub hcar
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨C, fun r hr => ?_⟩
    have hrI : r ∈ Icc (s₀ - ε) (s₀ + ε) := Ioo_subset_Icc_self hr.2
    have hO : IsOpen (Ioo a b ∩ Ioo (s₀ - ε) (s₀ + ε)) := isOpen_Ioo.inter isOpen_Ioo
    have hev : β =ᶠ[𝓝 r] W.f ⟨j, hj⟩ ∘ γ := Filter.eventuallyEq_of_mem (hO.mem_nhds hr)
      fun r' hr' => heq r' ⟨Ioo_subset_Icc_self hr'.1, Ioo_subset_Icc_self hr'.2⟩
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel γ r :=
      ((hγ r (hsub hrI)).contMDiffAt (isOpen_Ioo.mem_nhds (hsub hrI))).mdifferentiableAt
        one_ne_zero
    rw [stageRegularizedLagrangian_congr_of_eventuallyEq j T hev,
      H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j W.S (W.f ⟨j, hj⟩)
        (W.localDiffeomorph _) T hmd (W.metric ⟨j, hj⟩ r (hmet r hr))]
    have h := hC r hrI
    rwa [Real.norm_eq_abs] at h

private theorem exists_bound_of_forall_local {a b : ℝ} {f : ℝ → ℝ}
    (h : ∀ t ∈ Icc a b, ∃ ε > 0, ∃ C, ∀ r ∈ Ioo a b ∩ Ioo (t - ε) (t + ε), |f r| ≤ C) :
    ∃ C, ∀ r ∈ Ioo a b, |f r| ≤ C := by
  classical
  choose! ε hε C hC using h
  obtain ⟨s, hsI, hcover⟩ := isCompact_Icc.elim_nhds_subcover
    (fun t => Ioo (t - ε t) (t + ε t))
    (fun t ht => Ioo_mem_nhds (by linarith [hε t ht]) (by linarith [hε t ht]))
  refine ⟨∑ t ∈ s, |C t|, fun r hr => ?_⟩
  obtain ⟨t, hts, hrt⟩ := mem_iUnion₂.1 (hcover (Ioo_subset_Icc_self hr))
  exact (hC t (hsI t hts) r ⟨hr, hrt⟩).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun t _ => abs_nonneg (C t)) hts))

private def LocalGood (T : ℝ) {j : Fin (H.eventCount + 1)} (β : ℝ → (H.stage j).Carrier)
    (a b s₀ : ℝ) : Prop :=
  ∃ ε > 0, (∀ x y, x ≤ y → Icc x y ⊆ Icc a b ∩ Icc (s₀ - ε) (s₀ + ε) →
      Manifold.absolutelyContinuousOnInterval ThreeModel β x y) ∧
    ∃ C, ∀ r ∈ Ioo a b ∩ Ioo (s₀ - ε) (s₀ + ε), |H.stageRegularizedLagrangian j T β r| ≤ C

private theorem localGood_of_window {j lo hi : Fin (H.eventCount + 1)} {T : ℝ}
    (W : H.LWindow lo hi T) (hj : lo ≤ j ∧ j ≤ hi) {β : ℝ → (H.stage j).Carrier}
    {a b s₀ ε : ℝ} (hε : 0 < ε) {γ : ℝ → W.X}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Ioo (s₀ - 2 * ε) (s₀ + 2 * ε)))
    (hcar : ∀ r ∈ Icc (s₀ - ε) (s₀ + ε), T - r ^ 2 ∈ W.D.carrier)
    (heq : ∀ r ∈ Icc a b ∩ Icc (s₀ - ε) (s₀ + ε), β r = W.f ⟨j, hj⟩ (γ r))
    (hmet : ∀ r ∈ Ioo a b ∩ Ioo (s₀ - ε) (s₀ + ε),
      r ∈ Ioo (H.regularizedStageStart T W.a j) (H.regularizedStageEnd T W.b j)) :
    LocalGood (H := H) T β a b s₀ :=
  ⟨ε, hε, local_of_window W hj hε hγ hcar heq hmet⟩

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

private theorem localGood_of_interior (hv : 0 < v)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hgeo : H.IsHistoryLGeodesicOn hle T v α)
    (hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last)) (j : H.StageInterval first last)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hpos : 0 < s₀) (hlt : s₀ < v) :
    LocalGood (H := H) T (α j) (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val) s₀ := by
  obtain ⟨lo, hi, hlo, hhi, W, hsW, -, γ, hγ, heqW⟩ := hgeo.2.2.1 s₀ ⟨hpos, hlt⟩
  have hts := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hgeo.1 j hs₀
  have hjW : lo ≤ j.val ∧ j.val ≤ hi := LWindow.mem_range_of_mem_Icc W hsW hts
  set ε := min (s₀ - W.a) (W.b - s₀) / 4 with hεdef
  have hε : 0 < ε := by
    have := lt_min (sub_pos.2 hsW.1) (sub_pos.2 hsW.2)
    positivity
  have hε1 : ε ≤ (s₀ - W.a) / 4 := by
    rw [hεdef]; gcongr; exact min_le_left _ _
  have hε2 : ε ≤ (W.b - s₀) / 4 := by
    rw [hεdef]; gcongr; exact min_le_right _ _
  have hsub : Ioo (s₀ - 2 * ε) (s₀ + 2 * ε) ⊆ Ioo W.a W.b := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hγs : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ _ :=
    ((hγ.contMDiffOn W.solution isOpen_Ioo).of_le (by decide)).mono hsub
  refine localGood_of_window W hjW hε hγs (fun r hr => W.mem_carrier ⟨by linarith [hr.1],
    by linarith [hr.2]⟩) (fun r hr => ?_) (fun r hr => ?_)
  · have hrp := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hgeo.1 j hr.1
    have hrW := mem_regularizedStage_Icc W.nonneg
      (show r ∈ Icc W.a W.b from ⟨by linarith [hr.2.1], by linarith [hr.2.2]⟩) hrp
    exact (heqW ⟨j.val, hjW⟩ hrW).symm
  · exact mem_regularizedStage_Ioo W.nonneg
      (show r ∈ Ioo W.a W.b from ⟨by linarith [hr.2.1], by linarith [hr.2.2]⟩)
      (mem_Ioo_of_mem_regularizedStage_Ioo hr.1)

private theorem localGood_of_base (hv : 0 < v)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    {Z : TangentSpace ThreeModel p} (hinit : H.HasHistoryLInitialVector T α p Z)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last)) (j : H.StageInterval first last)
    (hs₀ : 0 ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    LocalGood (H := H) T (α j) (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val) 0 := by
  obtain ⟨lo, hlo, W, x, Zx, ha0, -, -, hdom, heqB⟩ := hinit
  obtain ⟨α₁, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  have hb : 0 < W.b := ha0 ▸ W.lt
  have hts := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower j hs₀
  have hjW : lo ≤ j.val ∧ j.val ≤ last := by
    refine ⟨?_, j.property.2⟩
    by_contra h
    have h1 := H.stageEndTime_le_time_of_lt (not_le.1 h)
    have h2 := H.time_le_of_mem_stageDomain W.lower
    have h3 : 0 < W.b ^ 2 := pow_pos hb 2
    have h4 := hts.2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h4
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hJo 0 h0J
  set ε := min δ W.b / 4 with hεdef
  have hε : 0 < ε := by
    have := lt_min hδ hb
    positivity
  have hεδ : ε ≤ δ / 4 := by rw [hεdef]; gcongr; exact min_le_left _ _
  have hεb : ε ≤ W.b / 4 := by rw [hεdef]; gcongr; exact min_le_right _ _
  have hsub : Ioo (0 - 2 * ε) (0 + 2 * ε) ⊆ J := fun r hr => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  have hγs : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 α₁ (Ioo (0 - 2 * ε) (0 + 2 * ε)) :=
    (ContMDiffOn.of_le (hcurve.2.2.contMDiffOn W.solution hJo) (by decide)).mono hsub
  have heqJ := lRegularizedCurve_eqOn W.S W.solution T hJo hJc h0J hcurve
  refine localGood_of_window W hjW hε hγs (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)
  · have h := W.mem_carrier (s := |r|) ⟨by rw [ha0]; exact abs_nonneg r, by
      rw [abs_le]; constructor <;> linarith [hr.1, hr.2]⟩
    rwa [sq_abs] at h
  · have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr.1.1
    have hrp := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower j hr.1
    have hrW := mem_regularizedStage_Icc le_rfl
      (show r ∈ Icc 0 W.b from ⟨hr0, by linarith [hr.2.2]⟩) hrp
    have e := heqB ⟨j.val, hjW⟩ hrW
    have hrJ : r ∈ J := hsub ⟨by linarith [hr.2.1], by linarith [hr.2.2]⟩
    simp only [Function.comp_apply] at e
    rw [heqJ hrJ] at e
    exact e.symm
  · have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.1.1
    rw [ha0]
    exact mem_regularizedStage_Ioo le_rfl
      (show r ∈ Ioo 0 W.b from ⟨hr0, by linarith [hr.2.2]⟩)
      (mem_Ioo_of_mem_regularizedStage_Ioo hr.1)

private theorem upper_of_mem_historyLExpDomain (Z : H.historyLExpDomain hle T v p) :
    T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
  obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hasHistoryLInitialVector_historyLCurve Z
  have h := W₀.upper_mem_Icc
  rwa [ha₀] at h

private theorem localGood_of_end (hv : 0 < v) (Z : H.historyLExpDomain hle T v p)
    (j : H.StageInterval first last)
    (hs₀ : v ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    LocalGood (H := H) T (H.historyLCurve hle T v p Z j) (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val) v := by
  have hupper := upper_of_mem_historyLExpDomain Z
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z
  have hlower := hgeo.1
  have hts := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower j hs₀
  have hTh : T ≤ H.horizon := by
    have h := hupper.2.trans (H.stageEndTime_le_horizon last)
    simpa using h
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hend : T - v ^ 2 < H.stageEndTime first := by
    cases hf : first using Fin.lastCases with
    | last => rw [stageEndTime_last]; linarith
    | cast i =>
      rw [hf] at hlower
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hlower
      rw [stageEndTime_castSucc]
      exact hlower.2
  have hjf : j = ⟨first, le_rfl, hle⟩ := by
    refine Subtype.ext (le_antisymm ?_ j.property.1)
    by_contra h
    have h1 := H.stageEndTime_le_time_of_lt (not_le.1 h)
    linarith [hts.1]
  subst hjf
  have htf : H.time first < H.stageEndTime first :=
    (H.time_le_of_mem_stageDomain hlower).trans_lt hend
  obtain ⟨G, -, hGm⟩ := exists_incomingSlab_stageMetric first htf
  have hmetric := G.smoothUpTo.jointContMDiffOn
  set γ₀ := H.historyLCurve hle T v p Z ⟨first, le_rfl, hle⟩ with hγ₀
  have hsq : Real.sqrt (T - H.stageEndTime first) < v := (Real.sqrt_lt' hv).2 (by linarith)
  set s₁ := max (v / 2) (Real.sqrt (T - H.stageEndTime first)) with hs₁def
  have hs₁pos : 0 < s₁ := lt_max_of_lt_left (by linarith)
  have hs₁v : s₁ < v := max_lt (by linarith) hsq
  have hin : ∀ s ∈ Ioo s₁ v, T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    intro s hs
    have hspos : 0 < s := hs₁pos.trans hs.1
    have h1 := (Real.sqrt_lt' hspos).1 ((le_max_right _ _).trans_lt hs.1)
    have h2 : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hs.2 hspos.le two_ne_zero
    exact ⟨(H.time_le_of_mem_stageDomain hlower).trans_lt (by linarith), by linarith⟩
  have hSm : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      G.flow.base.metric t = H.stageMetric first t := fun t ht => (hGm t ht).symm
  have hgeo₀ := isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn hgeo G.flow hSm
    (fun t ht => ht) hs₁pos le_rfl hin
  set b₀ := (T - v ^ 2 + H.stageEndTime first) / 2 with hb₀
  have hsq₀ : Real.sqrt (T - b₀) < v := (Real.sqrt_lt' hv).2 (by linarith)
  set s₂ := (max s₁ (Real.sqrt (T - b₀)) + v) / 2 with hs₂def
  have hs₁₂ : s₁ < s₂ := by linarith [le_max_left s₁ (Real.sqrt (T - b₀)), max_lt hs₁v hsq₀]
  have hs₂v : s₂ < v := by linarith [max_lt hs₁v hsq₀]
  have hs₂b : T - s₂ ^ 2 ≤ b₀ := by
    have h := (Real.sqrt_lt' (hs₁pos.trans hs₁₂)).1
      ((le_max_right _ _).trans_lt (show max s₁ (Real.sqrt (T - b₀)) < s₂ by
        linarith [max_lt hs₁v hsq₀]))
    linarith
  have hmet' := hmetric.mono (prod_mono (fun t (ht : t ∈ Icc (T - v ^ 2) b₀) =>
    (⟨(H.time_le_of_mem_stageDomain hlower).trans ht.1, ht.2.trans_lt (by linarith)⟩ :
      t ∈ Ico (H.time first) (H.stageEndTime first))) subset_rfl)
  obtain ⟨Q, hQ⟩ := exists_lRegularizedSpeedSq_le_of_closedStart G.flow G.equation hmet' hs₁pos
    hs₁₂ hs₂v rfl hs₂b hgeo₀
  have hγs : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ₀ (Ioo s₂ v) :=
    (ContMDiffOn.of_le (hgeo₀.contMDiffOn G.equation isOpen_Ioo) (by decide)).mono
      (Ioo_subset_Ioo_left hs₁₂.le)
  have hcar : ∀ s ∈ Ioc s₂ v, T - s ^ 2 ∈
      (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first) G.lt).carrier := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨H.time_le_of_mem_stageDomain hlower, hend⟩
    · have h := hin s ⟨hs₁₂.trans hs.1, hlt⟩
      exact ⟨h.1.le, h.2⟩
  obtain ⟨c, hc, hAC, C, hC⟩ := exists_absolutelyContinuousOnInterval_of_lRegularizedSpeedSq_le
    G.flow G.equation T hs₂v hγs hgeo.2.2.2 hcar fun s hs => hQ s ⟨hs.1.le, hs.2⟩
  have hbv : H.regularizedStageEnd T v first ≤ v :=
    (H.regularizedStage_bounds le_rfl hv.le hupper hlower ⟨first, le_rfl, hle⟩).2.2
  refine ⟨(v - c) / 2, by linarith [hc.2], fun x y hxy hxyS => ?_, C, fun r hr => ?_⟩
  · refine Manifold.absolutelyContinuousOnInterval_mono hAC ?_
    rw [uIcc_of_le hxy, uIcc_of_le (hc.2.le)]
    exact Icc_subset_Icc (by linarith [(hxyS (left_mem_Icc.2 hxy)).2.1, hc.2])
      ((hxyS (right_mem_Icc.2 hxy)).1.2.trans hbv)
  · have hrc : r ∈ Ioo c v := ⟨by linarith [hr.2.1, hc.2], hr.1.2.trans_le hbv⟩
    have hrin := hin r ⟨hs₁₂.trans (hc.1.trans hrc.1), hrc.2⟩
    have heqL : H.stageRegularizedLagrangian first T γ₀ r =
        lRegularizedLagrangian G.flow T γ₀ r := by
      simp only [stageRegularizedLagrangian, lRegularizedLagrangian, SolutionOn.scalar,
        SolutionFamily.scalar, hGm _ hrin]
    rw [heqL]
    exact hC r hrc

private theorem localGood_of_mem_historyLExpDomain (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    LocalGood (H := H) T (H.historyLCurve hle T v p Z j) (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val) s₀ := by
  have hupper := upper_of_mem_historyLExpDomain Z
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z
  have hb := H.regularizedStage_bounds le_rfl hv.le hupper hgeo.1 j
  have h0 : 0 ≤ s₀ := hb.1.trans hs₀.1
  have h1 : s₀ ≤ v := hs₀.2.trans hb.2.2
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · exact localGood_of_base hv (hasHistoryLInitialVector_historyLCurve Z) hgeo.1 hupper j hs₀
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · exact localGood_of_end hv Z j hs₀
  exact localGood_of_interior hv hgeo hupper j hs₀ hpos hlt

theorem absolutelyContinuousOnInterval_historyLCurve (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (H.historyLCurve hle T v p Z j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
  have hab := (H.regularizedStage_bounds le_rfl hv.le (upper_of_mem_historyLExpDomain Z)
    (isHistoryLGeodesicOn_historyLCurve Z).1 j).2.1
  apply Manifold.absolutelyContinuousOnInterval_of_forall_left_right hab
  · intro t ht
    obtain ⟨ε, hε, hAC, -⟩ := localGood_of_mem_historyLExpDomain hv Z j (Ioc_subset_Icc_self ht)
    refine ⟨max (H.regularizedStageStart T 0 j.val) (t - ε), max_lt ht.1 (by linarith),
      hAC _ _ (max_le ht.1.le (by linarith)) fun r hr => ⟨⟨(le_max_left _ _).trans hr.1,
        hr.2.trans ht.2⟩, (le_max_right _ _).trans hr.1, by linarith [hr.2]⟩⟩
  · intro t ht
    obtain ⟨ε, hε, hAC, -⟩ := localGood_of_mem_historyLExpDomain hv Z j (Ico_subset_Icc_self ht)
    refine ⟨min (H.regularizedStageEnd T v j.val) (t + ε), lt_min ht.2 (by linarith),
      hAC _ _ (le_min ht.2.le (by linarith)) fun r hr => ⟨⟨ht.1.trans hr.1,
        hr.2.trans (min_le_left _ _)⟩, by linarith [hr.1], hr.2.trans (min_le_right _ _)⟩⟩

theorem intervalIntegrable_stageRegularizedLagrangian_historyLCurve (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) :
    IntervalIntegrable (H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p Z j))
      volume (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
  have hab := (H.regularizedStage_bounds le_rfl hv.le (upper_of_mem_historyLExpDomain Z)
    (isHistoryLGeodesicOn_historyLCurve Z).1 j).2.1
  obtain ⟨C, hC⟩ := exists_bound_of_forall_local fun t ht => by
    obtain ⟨ε, hε, -, C, hC⟩ := localGood_of_mem_historyLExpDomain hv Z j ht
    exact ⟨ε, hε, C, hC⟩
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  have _ : IsFiniteMeasure (volume.restrict (Ioo (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val))) := ⟨by simp⟩
  refine Integrable.of_bound
    (H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval j.val T 0
      v _ (absolutelyContinuousOnInterval_historyLCurve hv Z j)) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [Real.norm_eq_abs]
  exact hC r hr

theorem regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem {B : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) :
    H.regularizedExtendedAction first last T B 0 v (H.historyLCurve hle T v p Z) =
      (H.historyLAction hle T v p Z : WithTop ℝ) := by
  rw [H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le
    (upper_of_mem_historyLExpDomain Z) (isHistoryLGeodesicOn_historyLCurve Z).1 _
    (intervalIntegrable_stageRegularizedLagrangian_historyLCurve hv Z) fun j => ?_]
  · rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T 0 v j.val ht) _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
