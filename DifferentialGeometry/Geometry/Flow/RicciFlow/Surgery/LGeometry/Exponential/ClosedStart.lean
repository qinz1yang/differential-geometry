import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.SmoothFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedStartVelocity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Connection (trivToE)

open private mem_regularizedStage_Ioo mem_regularizedStage_Icc LWindow.mem_range_of_mem_Icc
  eq_of_mem_Ioo_of_mem_Icc contDiffAt_familySeed exists_mem_Ioo_not_mem_range exists_stage_nhds
  hasPrefixFamily_end IsHistoryLGeodesicPrefix HasPrefixFamily from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity
open private lt_stageEndTime_of_mem_stageDomain from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Basic
open private exists_mem_stageDomain le_of_mem_stageDomain from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Truncation

universe u
variable {H : ObservedHistory.{u}}

section PieceAction

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

open Classical in
variable (H) in
private def pieceAction (hle : first ≤ last) (T v : ℝ) (p : (H.stage last).Carrier)
    (j : H.StageInterval first last) (r₁ r₂ : ℝ) (Z : ThreeSpace) : ℝ :=
  if h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
    ∫ r in r₁..r₂, H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, h⟩ j) r
  else 0

private theorem mem_Ioo_of_mem_regularizedStage_Ioo {T u w r : ℝ} {j : Fin (H.eventCount + 1)}
    (hr : r ∈ Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T w j)) :
    T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) ∧ T - r ^ 2 ∈ Ioo (T - w ^ 2) (T - u ^ 2) := by
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr.1.le
  have hrpos : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.1
  have h1 : T - min (T - u ^ 2) (H.stageEndTime j) < r ^ 2 := (Real.sqrt_lt' hrpos).1 hr.1
  have h2 : r ^ 2 < T - max (T - w ^ 2) (H.time j) := (Real.lt_sqrt hr0).1 hr.2
  have h3 := min_le_left (T - u ^ 2) (H.stageEndTime j)
  have h4 := min_le_right (T - u ^ 2) (H.stageEndTime j)
  have h5 := le_max_left (T - w ^ 2) (H.time j)
  have h6 := le_max_right (T - w ^ 2) (H.time j)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem regularizedStageEnd_le_self {T v : ℝ} (hv : 0 ≤ v) (j : Fin (H.eventCount + 1)) :
    H.regularizedStageEnd T v j ≤ v := by
  unfold regularizedStageEnd
  calc Real.sqrt (T - max (T - v ^ 2) (H.time j)) ≤ Real.sqrt (v ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [le_max_left (T - v ^ 2) (H.time j)])
    _ = v := Real.sqrt_sq hv

private theorem stageRegularizedLagrangian_congr_nhds (j : Fin (H.eventCount + 1)) (T : ℝ)
    {α β : ℝ → (H.stage j).Carrier} {r : ℝ} (h : α =ᶠ[𝓝 r] β) :
    H.stageRegularizedLagrangian j T α r = H.stageRegularizedLagrangian j T β r := by
  have hvel : lVelocity (I := ThreeModel) α r = lVelocity (I := ThreeModel) β r := by
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) h
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  have hval : α r = β r := h.self_of_nhds
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

private theorem continuousOn_pieceAction_of_local (j : H.StageInterval first last)
    {Z₀ : ThreeSpace} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ s₀ ∈ Icc a b, ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ ∃ K : Set ℝ, IsOpen K ∧
      s₀ ∈ K ∧ ∀ r₁ r₂, r₁ < r₂ → Icc r₁ r₂ ⊆ K ∩ Icc a b →
        ContinuousOn (H.pieceAction hle T v p j r₁ r₂) V ∧
        ∀ Z ∈ V, ∀ h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
          IntervalIntegrable
            (H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, h⟩ j))
            volume r₁ r₂) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ ContinuousOn (H.pieceAction hle T v p j a b) V := by
  classical
  rcases hab.eq_or_lt with rfl | hlt
  · refine ⟨univ, isOpen_univ, mem_univ _, (continuousOn_const (c := (0 : ℝ))).congr fun Z _ => ?_⟩
    change H.pieceAction hle T v p j a a Z = 0
    unfold pieceAction
    split_ifs <;> simp
  choose! V hV hZV K hK hsK hgood using hloc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun i : Icc a b => K i)
    isCompact_Icc (fun i => hK i i.2) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hsK x hx⟩)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (div_pos (sub_pos.2 hlt) hδ).trans hN
    exact_mod_cast this
  set h : ℝ := (b - a) / N with hhdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hh : 0 < h := div_pos (sub_pos.2 hlt) hNr
  have hhδ : h < δ := by
    rw [hhdef, div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  let pt : ℕ → ℝ := fun i => a + i * h
  have hpt0 : pt 0 = a := by simp [pt]
  have hptN : pt N = b := by
    simp only [pt, hhdef]
    field_simp
    ring
  have hptI : ∀ i ≤ N, pt i ∈ Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
    refine ⟨by simp only [pt]; nlinarith, ?_⟩
    have : (i : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right hi' hh.le
    have hNh : (N : ℝ) * h = b - a := by
      simp only [hhdef]
      field_simp
    simp only [pt]
    linarith
  have hsel : ∀ i : ℕ, ∃ s : ℝ, i < N → s ∈ Icc a b ∧ Metric.ball (pt i) δ ⊆ K s := by
    intro i
    by_cases hi : i < N
    · obtain ⟨s, hs⟩ := hball (pt i) (hptI i hi.le)
      exact ⟨s, fun _ => ⟨s.2, hs⟩⟩
    · exact ⟨a, fun h' => absurd h' hi⟩
  choose s hs using hsel
  have hsub : ∀ i < N, Icc (pt i) (pt (i + 1)) ⊆ K (s i) ∩ Icc a b := by
    intro i hi r hr
    refine ⟨(hs i hi).2 ?_, (hptI i hi.le).1.trans hr.1, hr.2.trans (hptI (i + 1) hi).2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : pt (i + 1) = pt i + h := by
      simp only [pt]
      push_cast
      ring
    constructor <;> linarith [hr.1, hr.2]
  have hlt' : ∀ i, pt i < pt (i + 1) := fun i => by
    simp only [pt]
    push_cast
    nlinarith
  refine ⟨⋂ i ∈ Finset.range N, V (s i), ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset fun i hi => hV (s i) (hs i (Finset.mem_range.1 hi)).1
  · exact mem_iInter₂.2 fun i hi => hZV (s i) (hs i (Finset.mem_range.1 hi)).1
  have hcont : ContinuousOn (fun Z => ∑ i ∈ Finset.range N, H.pieceAction hle T v p j (pt i)
      (pt (i + 1)) Z) (⋂ i ∈ Finset.range N, V (s i)) := by
    refine continuousOn_finsetSum _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    exact (hgood (s i) (hs i hi').1 (pt i) (pt (i + 1)) (hlt' i) (hsub i hi')).1.mono
      (biInter_subset_of_mem hi)
  refine hcont.congr fun Z hZ => ?_
  have hZ' : ∀ i < N, Z ∈ V (s i) := fun i hi =>
    mem_iInter₂.1 hZ i (Finset.mem_range.2 hi)
  change H.pieceAction hle T v p j a b Z =
    ∑ i ∈ Finset.range N, H.pieceAction hle T v p j (pt i) (pt (i + 1)) Z
  by_cases hdom : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p
  · simp only [pieceAction, dite_eq_left hdom]
    rw [intervalIntegral.sum_integral_adjacent_intervals fun i hi =>
      (hgood (s i) (hs i hi).1 (pt i) (pt (i + 1)) (hlt' i) (hsub i hi)).2 Z (hZ' i hi) hdom,
      hpt0, hptN]
  · simp only [pieceAction, dite_eq_right hdom, Finset.sum_const_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem pieceAction_local_of_family {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (j : H.StageInterval first last) {V : Set ThreeSpace} {K : Set ℝ} (hV : IsOpen V)
    (hK : IsOpen K) {β : ThreeSpace × ℝ → X}
    (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
    (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p)
    {a b : ℝ} (hcar : ∀ r ∈ K ∩ Icc a b, T - r ^ 2 ∈ D.carrier)
    (hid : ∀ Z (hZ : Z ∈ V), ∀ r ∈ K ∩ Ioo a b,
      H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩ j) r =
        lRegularizedLagrangian S T (fun s => β (Z, s)) r)
    {r₁ r₂ : ℝ} (hr : r₁ < r₂) (hsub : Icc r₁ r₂ ⊆ K ∩ Icc a b) :
    ContinuousOn (H.pieceAction hle T v p j r₁ r₂) V ∧
      ∀ Z ∈ V, ∀ h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
        IntervalIntegrable
          (H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, h⟩ j))
          volume r₁ r₂ := by
  have hβ1 := hβ.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have hsubK : [[r₁, r₂]] ⊆ K := by
    rw [uIcc_of_le hr.le]
    exact fun r h => (hsub h).1
  have hcar' : ∀ r ∈ [[r₁, r₂]], T - r ^ 2 ∈ D.carrier := by
    rw [uIcc_of_le hr.le]
    exact fun r h => hcar r (hsub h)
  have hIoo : ∀ r ∈ Ioo r₁ r₂, r ∈ K ∩ Ioo a b := fun r h =>
    ⟨(hsub (Ioo_subset_Icc_self h)).1, (hsub ⟨le_rfl, hr.le⟩).2.1.trans_lt h.1,
      h.2.trans_le (hsub ⟨hr.le, le_rfl⟩).2.2⟩
  have hlag := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one S hS T hV hK hβ1
    hsubK hcar'
  have hact := continuousOn_lRegularizedAction_family_of_contMDiffOn_one S hS T r₁ r₂ hV hK hβ1
    hcar' hsubK
  have hint : ∀ Z ∈ V,
      IntervalIntegrable (lRegularizedLagrangian S T (fun s => β (Z, s))) volume r₁ r₂ := by
    intro Z hZ
    have hc : ContinuousOn ((fun q : ThreeSpace × ℝ =>
        lRegularizedLagrangian S T (fun s => β (q.1, s)) q.2) ∘ fun r => (Z, r)) [[r₁, r₂]] :=
      ContinuousOn.comp hlag (continuous_const.prodMk continuous_id).continuousOn
        fun r hr => ⟨hZ, hr⟩
    exact hc.intervalIntegrable
  refine ⟨hact.congr fun Z hZ => ?_, fun Z hZ h => ?_⟩
  · simp only [pieceAction, dite_eq_left (hVdom Z hZ)]
    exact intervalIntegral.integral_congr_Ioo_of_le hr.le fun r h => hid Z hZ r (hIoo r h)
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le]
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).1 (hint Z hZ)).congr_fun
      (fun r h' => (hid Z hZ r (hIoo r h')).symm) measurableSet_Ioo

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem pieceAction_local_of_window {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo)
    (hhi : hi ≤ last) (W : H.LWindow lo hi T) {V : Set ThreeSpace} {K : Set ℝ} (hV : IsOpen V)
    (hK : IsOpen K) (hKW : K ⊆ Ioo W.a W.b) {β : ThreeSpace × ℝ → W.X}
    (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
    (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K)
    (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p)
    (hrep : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
      ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
        H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩
          ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)))
    (j : H.StageInterval first last) {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (hsub : Icc r₁ r₂ ⊆ K ∩ Icc (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val)) :
    ContinuousOn (H.pieceAction hle T v p j r₁ r₂) V ∧
      ∀ Z ∈ V, ∀ h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
        IntervalIntegrable
          (H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, h⟩ j))
          volume r₁ r₂ := by
  refine pieceAction_local_of_family W.S W.solution j hV hK hβ hVdom
    (fun r hr => W.mem_carrier (Ioo_subset_Icc_self (hKW hr.1))) (fun Z hZ r hr => ?_) hr hsub
  have ht := (mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2).1
  have hjW : lo ≤ j.val ∧ j.val ≤ hi :=
    LWindow.mem_range_of_mem_Icc W (hKW hr.1) ⟨ht.1.le, ht.2.le⟩
  have hrW : r ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) :=
    mem_regularizedStage_Ioo W.nonneg (hKW hr.1) ht
  have hO : IsOpen (K ∩ Ioo (H.regularizedStageStart T W.a j.val)
      (H.regularizedStageEnd T W.b j.val)) := hK.inter isOpen_Ioo
  have hev : H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩ j =ᶠ[𝓝 r]
      W.f ⟨j.val, hjW⟩ ∘ fun s => β (Z, s) := by
    filter_upwards [hO.mem_nhds ⟨hr.1, hrW⟩] with s hs
    exact hrep Z hZ ⟨j.val, hjW⟩ s hs
  rw [stageRegularizedLagrangian_congr_nhds j.val T hev]
  exact H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val W.S (W.f ⟨j.val, hjW⟩)
    (W.localDiffeomorph _) T (hgeo Z hZ r hr.1).2.1 (W.metric ⟨j.val, hjW⟩ r hrW)

variable (H) in
private def ActionGoodNear (hle : first ≤ last) (T v : ℝ) (p : (H.stage last).Carrier)
    (Z₀ : ThreeSpace) (s₀ : ℝ) : Prop :=
  ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ ∃ K : Set ℝ, IsOpen K ∧ s₀ ∈ K ∧
    ∀ (j : H.StageInterval first last) (r₁ r₂ : ℝ), r₁ < r₂ →
      Icc r₁ r₂ ⊆ K ∩ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
      ContinuousOn (H.pieceAction hle T v p j r₁ r₂) V ∧
      ∀ Z ∈ V, ∀ h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
        IntervalIntegrable
          (H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, h⟩ j))
          volume r₁ r₂

open Classical in
private theorem exists_continuousOn_historyLAction {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) (hv : 0 < v)
    (hgood : ∀ s₀ ∈ Icc 0 v, H.ActionGoodNear hle T v p Z₀ s₀) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      ContinuousOn (fun Z : ThreeSpace =>
        if h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
          H.historyLAction hle T v p ⟨Z, h⟩ else 0) V := by
  set Zd : H.historyLExpDomain hle T v p := ⟨Z₀, hZ₀⟩
  have hlower := (isHistoryLGeodesicOn_historyLCurve Zd).1
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    obtain ⟨lo, -, W, -, -, ha, -⟩ := hasHistoryLInitialVector_historyLCurve Zd
    have h := W.upper_mem_Icc
    rwa [ha] at h
  have hpiece : ∀ j : H.StageInterval first last,
      H.regularizedStageStart T 0 j.val ≤ H.regularizedStageEnd T v j.val ∧
        Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ⊆
          Icc 0 v := fun j => by
    have hb := H.regularizedStage_bounds le_rfl hv.le hupper hlower j
    exact ⟨hb.2.1, Icc_subset_Icc hb.1 hb.2.2⟩
  have hj : ∀ j : H.StageInterval first last, ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      ContinuousOn (H.pieceAction hle T v p j (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T v j.val)) V := fun j =>
    continuousOn_pieceAction_of_local j (hpiece j).1 fun s₀ hs₀ => by
      obtain ⟨V, hV, hZV, K, hK, hsK, hG⟩ := hgood s₀ ((hpiece j).2 hs₀)
      exact ⟨V, hV, hZV, K, hK, hsK, fun r₁ r₂ hr hsub => hG j r₁ r₂ hr hsub⟩
  choose V hV hZV hcont using hj
  refine ⟨⋂ j, V j, isOpen_iInter_of_finite hV, mem_iInter.2 hZV, ?_⟩
  have hsum : ContinuousOn (fun Z => ∑ j : H.StageInterval first last,
      H.pieceAction hle T v p j (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T v j.val) Z) (⋂ j, V j) :=
    continuousOn_finsetSum _ fun j _ => (hcont j).mono (iInter_subset _ j)
  refine hsum.congr fun Z _ => ?_
  by_cases h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p
  · simp only [dite_eq_left h, historyLAction, pieceAction, stageRegularizedAction]
  · simp only [dite_eq_right h, pieceAction, Finset.sum_const_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem actionGoodNear_zero (hv : 0 < v) {Z₀ : ThreeSpace} {V₃ : Set ThreeSpace}
    (hV₃ : IsOpen V₃) (hZ₀V₃ : Z₀ ∈ V₃)
    (hV₃dom : ∀ Z ∈ V₃, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) :
    H.ActionGoodNear hle T v p Z₀ 0 := by
  classical
  set Zd : H.historyLExpDomain hle T v p := ⟨Z₀, hV₃dom Z₀ hZ₀V₃⟩
  have hlower := (isHistoryLGeodesicOn_historyLCurve Zd).1
  obtain ⟨lo₀, -, W₀, x, Zx₀, ha₀, hx, hZx₀, hdom, -⟩ := hasHistoryLInitialVector_historyLCurve Zd
  have hb₀ : 0 < W₀.b := ha₀ ▸ W₀.lt
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V', hV', hZV', K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W₀.S W₀.solution T hJo hJc h0J hbJ hcurve
  have hIcc : Icc 0 W₀.b ⊆ K := hKc.Icc_subset h0K hbK
  obtain ⟨c₁, hc₁, hne⟩ := exists_mem_Ioo_not_mem_range (H := H) (T := T) (lt_min hb₀ hv) le_rfl
  have hc₁b : c₁ < W₀.b := hc₁.2.trans_le (min_le_left _ _)
  have hc₁v : c₁ < v := hc₁.2.trans_le (min_le_right _ _)
  have hTup : T - 0 ^ 2 ∈ H.stageDomain last := by
    have h := W₀.upper
    rwa [ha₀] at h
  have hT0 : T ∈ H.stageDomain last := by simpa using hTup
  have hc₁0 : 0 ≤ T - c₁ ^ 2 := by
    have := H.time_le_of_mem_stageDomain hlower
    have h2 : c₁ ^ 2 < v ^ 2 := pow_lt_pow_left₀ hc₁v hc₁.1.le two_ne_zero
    linarith [H.time_nonneg first]
  have hc₁h : T - c₁ ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT0).trans (H.stageEndTime_le_horizon last)
    have : 0 < c₁ ^ 2 := pow_pos hc₁.1 2
    linarith
  obtain ⟨k₀, η, hη, -, hηk⟩ := exists_stage_nhds hc₁.1 hc₁0 hc₁h hne
  have hkc := hηk c₁ ⟨by linarith, by linarith⟩
  have hc₁a : W₀.a < c₁ := by rw [ha₀]; exact hc₁.1
  have hk₀ : lo₀ ≤ k₀ ∧ k₀ ≤ last :=
    LWindow.mem_range_of_mem_Icc W₀ ⟨hc₁a, hc₁b⟩ ⟨hkc.1.le, hkc.2.le⟩
  have hdown : T - c₁ ^ 2 ∈ H.stageDomain k₀ := H.mem_stageDomain_of_mem_Ioo hkc
  have hfk₀ : first ≤ k₀ := first_le_of_mem_stageDomain hc₁.1.le hc₁v.le hlower hdown
  let e := (W₀.localDiffeomorph ⟨last, W₀.le, le_rfl⟩).mfderivToContinuousLinearEquiv
    (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩ x) →L[ℝ]
      TangentSpace ThreeModel x)
  have hLe : ∀ Z : ThreeSpace, mfderiv ThreeModel ThreeModel (W₀.f ⟨last, W₀.le, le_rfl⟩) x
      (L Z) = Z := fun Z => e.apply_symm_apply Z
  have hLZ₀ : L Z₀ = Zx₀ := by
    have h : e Zx₀ = Z₀ := hZx₀
    have h2 : e.symm (e Zx₀) = Zx₀ := e.symm_apply_apply Zx₀
    rw [h] at h2
    exact h2
  let V : Set ThreeSpace := L ⁻¹' V' ∩ V₃
  have hV : IsOpen V := (hV'.preimage L.continuous).inter hV₃
  have hZ₀V : Z₀ ∈ V := by
    refine ⟨?_, hZ₀V₃⟩
    change L Z₀ ∈ V'
    rw [hLZ₀]
    exact hZV'
  let β₀ : ThreeSpace × ℝ → W₀.X := fun q => fam (L q.1, q.2)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (V ×ˢ K) := by
    have hmap : ContMDiff (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ThreeSpace × ℝ => (L q.1, q.2)) :=
      (L.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact hfam.comp hmap.contMDiffOn fun q hq => ⟨hq.1.1, hq.2⟩
  have hcurveZ : ∀ Z ∈ V, IsLRegularizedCurveOn W₀.S T (fun s => β₀ (Z, s)) K x (L Z) :=
    fun Z hZ => hfamc (L Z) hZ.1
  let W'' := W₀.restrict hk₀.1 le_rfl hk₀.2 (by rw [ha₀]) hc₁.1 hc₁b.le hTup hdown
  let B : ThreeSpace → (j : H.StageInterval k₀ last) → ℝ → (H.stage j.val).Carrier :=
    fun Z j r => W₀.f ⟨j.val, hk₀.1.trans j.property.1, j.property.2⟩ (β₀ (Z, r))
  have hc₁K : c₁ ∈ K := hIcc ⟨hc₁.1.le, hc₁b.le⟩
  have hB : ∀ Z ∈ V, H.IsHistoryLGeodesicOn hk₀.2 T c₁ (B Z) ∧
      H.HasHistoryLInitialVector T (B Z) p Z := by
    intro Z hZ
    refine ⟨⟨hdown, fun i hf hl => W₀.crossing i (hk₀.1.trans hf) hl _, fun s hs => ?_, ?_⟩, ?_⟩
    · exact ⟨k₀, last, le_rfl, le_rfl, W'', hs, le_rfl, fun r => β₀ (Z, r),
        fun r hr => (hcurveZ Z hZ).2.2 r (hIcc ⟨hr.1.le, hr.2.le.trans hc₁b.le⟩),
        fun j r _ => rfl⟩
    · exact ((W₀.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
        ((hcurveZ Z hZ).2.2 c₁ hc₁K).2.1.continuousAt).continuousWithinAt
    · refine ⟨k₀, le_rfl, W'', x, L Z, rfl, hx, hLe Z,
        ⟨fun s => β₀ (Z, s), K, hK, hKc, h0K, hc₁K, hcurveZ Z hZ⟩, fun j r hr => ?_⟩
      have hrI : r ∈ Icc 0 c₁ := LWindow.piece_subset W'' j hr
      have hcur := lRegularizedCurve_eqOn W₀.S W₀.solution T hK hKc h0K (hcurveZ Z hZ)
        (hIcc ⟨hrI.1, hrI.2.trans hc₁b.le⟩)
      change W₀.f _ (lRegularizedCurve W₀.S T x (L Z) r) = W₀.f _ (β₀ (Z, r))
      rw [hcur]
  have hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => hV₃dom Z hZ.2
  refine ⟨V, hV, hZ₀V, K ∩ Ioo (-c₁) c₁, hK.inter isOpen_Ioo, ⟨h0K, by linarith, hc₁.1⟩,
    fun j r₁ r₂ hr hsub => ?_⟩
  refine pieceAction_local_of_family W₀.S W₀.solution j hV (hK.inter isOpen_Ioo)
    (hβ₀.mono (prod_mono subset_rfl inter_subset_left)) hVdom (fun r hr => ?_)
    (fun Z hZ r hr => ?_) hr hsub
  · refine W₀.mem_carrier ⟨?_, hr.1.2.2.le.trans hc₁b.le⟩
    rw [ha₀]
    exact (Real.sqrt_nonneg _).trans hr.2.1
  have ht := (mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2).1
  have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.2.1
  have hrc : r < c₁ := hr.1.2.2
  have hk₀j : k₀ ≤ j.val := by
    by_contra hlt
    have h1 := stageEndTime_le_time_of_lt (not_le.1 hlt)
    have h2 : r ^ 2 < c₁ ^ 2 := pow_lt_pow_left₀ hrc hr0.le two_ne_zero
    linarith [hkc.1, ht.2]
  have hrB : r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T c₁ j.val) :=
    mem_regularizedStage_Ioo le_rfl ⟨hr0, hrc⟩ ht
  set Zd' : H.historyLExpDomain hle T v p := ⟨Z, hVdom Z hZ⟩
  have hαZ := (isHistoryLGeodesicOn_historyLCurve Zd').truncate hfk₀ hk₀.2 hc₁.1 hc₁v.le hdown
  have hinitZ := (hasHistoryLInitialVector_historyLCurve Zd').truncate hc₁.1 hfk₀ hdown
  have heq := IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hc₁.1 (hB Z hZ).1 hαZ
    (hB Z hZ).2 hinitZ ⟨j.val, hk₀j, j.property.2⟩
  have hev : H.historyLCurve hle T v p Zd' j =ᶠ[𝓝 r]
      W₀.f ⟨j.val, hk₀.1.trans hk₀j, j.property.2⟩ ∘ fun s => β₀ (Z, s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hrB] with s hs
    exact (heq (Ioo_subset_Icc_self hs)).symm
  have hrW : r ∈ Ioo (H.regularizedStageStart T W₀.a j.val) (H.regularizedStageEnd T W₀.b j.val) :=
    mem_regularizedStage_Ioo W₀.nonneg ⟨by rw [ha₀]; exact hr0, hrc.trans hc₁b⟩ ht
  rw [stageRegularizedLagrangian_congr_nhds j.val T hev]
  exact H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val W₀.S
    (W₀.f ⟨j.val, hk₀.1.trans hk₀j, j.property.2⟩) (W₀.localDiffeomorph _) T
    ((hcurveZ Z hZ).2.2 r hr.1.1).2.1 (W₀.metric ⟨j.val, hk₀.1.trans hk₀j, j.property.2⟩ r hrW)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem actionGoodNear_end_of_mem_historyLExpOpenDomain (hv : 0 < v) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T v p) :
    H.ActionGoodNear hle T v p Z₀ v := by
  obtain ⟨α₀, hα₀, hinit, W, hvW, γ, hγ, hγα⟩ := hZ₀
  obtain ⟨V, hV, hZ₀V, A, hA, lo, hi, hlo, hhi, Wv, γv, -, -, -, k, hk, η, hη, hηW, hηk, β, hβ,
    hgeo, -, hAβ⟩ := hasPrefixFamily_end hv hα₀ hinit W hvW γ hγ hγα
  have hvk := hηk v ⟨by linarith, by linarith⟩
  have hfk : first = k := eq_of_mem_Ioo_of_mem_Icc hvk
    ⟨H.time_le_of_mem_stageDomain hα₀.1, H.le_stageEndTime_of_mem_stageDomain hα₀.1⟩
  subst hfk
  have hmem : ∀ Z ∈ V, H.IsHistoryLGeodesicOn hle T v (A Z) ∧
      H.HasHistoryLInitialVector T (A Z) p Z := by
    intro Z hZ
    obtain ⟨hcross, hwin, lo₀, hlo₀, W₀, x, Zx, ha₀, -, hx, hZx, hdom, hbase⟩ := hA Z hZ
    refine ⟨⟨hα₀.1, fun i hf hl => hcross i hf hl ?_, hwin, ?_⟩,
      ⟨lo₀, hlo₀, W₀, x, Zx, ha₀, hx, hZx, hdom, hbase⟩⟩
    · have h1 : H.stageEndTime first ≤ H.time i.succ := by
        rw [← stageEndTime_castSucc]
        exact H.stageEndTime_mono hf
      exact (Real.sqrt_lt' hv).2 (by linarith [hvk.2])
    · have hβv : ContinuousAt (fun r => β (Z, r)) v :=
        (((hβ (Z, v) ⟨hZ, by constructor <;> linarith⟩).contMDiffAt
          ((hV.prod isOpen_Ioo).mem_nhds ⟨hZ, by constructor <;> linarith⟩)).comp v
          (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
      have hg : ContinuousAt (fun r => Wv.f ⟨first, hk⟩ (β (Z, r))) v :=
        (Wv.localDiffeomorph _).contMDiff.continuous.continuousAt.comp hβv
      refine hg.continuousWithinAt.congr_of_eventuallyEq ?_ (hAβ Z hZ v ⟨by linarith, le_rfl⟩)
      filter_upwards [Ioo_mem_nhdsLT (show v - η < v by linarith)] with r hr
      exact hAβ Z hZ r ⟨hr.1, hr.2.le⟩
  have hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => ⟨A Z, hmem Z hZ⟩
  refine ⟨V, hV, hZ₀V, Ioo (v - η) (v + η), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun j r₁ r₂ hr hsub => ?_⟩
  refine pieceAction_local_of_family Wv.S Wv.solution j hV isOpen_Ioo hβ hVdom
    (fun r hr => Wv.mem_carrier (Ioo_subset_Icc_self (hηW hr.1))) (fun Z hZ r hr => ?_) hr hsub
  have ht := (mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2).1
  have hrv : r < v := by
    have h := (mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2).2
    have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.2.1
    nlinarith [h.1]
  have hjk : j.val = first := eq_of_mem_Ioo_of_mem_Icc (hηk r hr.1) ⟨ht.1.le, ht.2.le⟩
  obtain ⟨jv, hj1, hj2⟩ := j
  change jv = first at hjk
  subst hjk
  have hrW : r ∈ Ioo (H.regularizedStageStart T Wv.a jv) (H.regularizedStageEnd T Wv.b jv) :=
    mem_regularizedStage_Ioo Wv.nonneg (hηW hr.1) ht
  set Zd' : H.historyLExpDomain hle T v p := ⟨Z, hVdom Z hZ⟩
  have hev : H.historyLCurve hle T v p Zd' ⟨jv, hj1, hj2⟩ =ᶠ[𝓝 r]
      Wv.f ⟨jv, hk⟩ ∘ fun s => β (Z, s) := by
    have hO : IsOpen (Ioo (v - η) v ∩ Ioo (H.regularizedStageStart T 0 jv)
        (H.regularizedStageEnd T v jv)) := isOpen_Ioo.inter isOpen_Ioo
    filter_upwards [hO.mem_nhds ⟨⟨hr.1.1, hrv⟩, hr.2⟩] with s hs
    rw [eqOn_historyLCurve hv Zd' (hmem Z hZ).1 (hmem Z hZ).2 ⟨jv, hj1, hj2⟩
      (Ioo_subset_Icc_self hs.2)]
    exact hAβ Z hZ s ⟨hs.1.1, hs.1.2.le⟩
  rw [stageRegularizedLagrangian_congr_nhds jv T hev]
  exact H.stageRegularizedLagrangian_comp_eq_of_localPullMetric jv Wv.S (Wv.f ⟨jv, hk⟩)
    (Wv.localDiffeomorph _) T (hgeo Z hZ r hr.1).2.1 (Wv.metric ⟨jv, hk⟩ r hrW)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem actionGoodNear_of_mem_historyLExpOpenDomain (hv : 0 < v) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T v p) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo 0 v) : H.ActionGoodNear hle T v p Z₀ s₀ := by
  obtain ⟨V, hV, hZ₀V, -, hVdom, lo, hi, hlo, hhi, W, K, hK, hs₀K, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_window_family_historyLCurve hv hZ₀ hs₀
  exact ⟨V, hV, hZ₀V, K, hK, hs₀K, fun j r₁ r₂ hr hsub =>
    pieceAction_local_of_window hlo hhi W hV hK hKW hβ hgeo hVdom hrep j hr hsub⟩

private theorem exists_package_of_mem_historyLExpOpenDomain (hv : 0 < v) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T v p) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) ∧
      (∃ g : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ g V ∧
        ∀ Z ∈ V, ∀ hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
          H.historyLExp hle T v p ⟨Z, hZ⟩ = g Z) ∧
      ∀ s₀ ∈ Icc 0 v, H.ActionGoodNear hle T v p Z₀ s₀ := by
  obtain ⟨V, hV, hZ₀V, hVsub, g, hg, hgeq⟩ := exists_nhds_contMDiffOn_historyLExp hv hZ₀
  have hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => historyLExpOpenDomain_subset_historyLExpDomain (hVsub hZ)
  refine ⟨V, hV, hZ₀V, hVdom, ⟨g, hg, hgeq⟩, fun s₀ hs₀ => ?_⟩
  rcases hs₀.1.eq_or_lt with rfl | h0
  · exact actionGoodNear_zero hv hV hZ₀V hVdom
  rcases hs₀.2.eq_or_lt with rfl | hv'
  · exact actionGoodNear_end_of_mem_historyLExpOpenDomain hv hZ₀
  · exact actionGoodNear_of_mem_historyLExpOpenDomain hv hZ₀ ⟨h0, hv'⟩

end PieceAction

section Helpers

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hα : H.IsHistoryLGeodesicOn hle T v α) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D)
    (hSm : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      S.base.metric t = H.stageMetric first t)
    (hSreg : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first), t ∈ D.regular)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂v : s₂ ≤ v)
    (hin : ∀ s ∈ Ioo s₁ s₂, T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) :
    IsLRegularizedGeodesicOn S T (α ⟨first, le_rfl, hle⟩) (Ioo s₁ s₂) := by
  intro s hs
  obtain ⟨lo, hi, hlo, hhi, W, hsW, -, γ, hγ, heq⟩ :=
    hα.2.2.1 s ⟨hs₁.trans hs.1, hs.2.trans_le hs₂v⟩
  have ht := hin s hs
  have hj : lo ≤ first ∧ first ≤ hi := LWindow.mem_range_of_mem_Icc W hsW ⟨ht.1.le, ht.2.le⟩
  set O : Set ℝ := Ioo s₁ s₂ ∩
    Ioo (H.regularizedStageStart T W.a first) (H.regularizedStageEnd T W.b first)
  have hO : IsOpen O := isOpen_Ioo.inter isOpen_Ioo
  have hsO : s ∈ O := ⟨hs, mem_regularizedStage_Ioo W.nonneg hsW ht⟩
  have hOW : O ⊆ Ioo W.a W.b := fun r hr => by
    have h := (mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2).2
    have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.2.1
    constructor
    · by_contra hc
      have := pow_le_pow_left₀ hr0.le (not_lt.1 hc) 2
      linarith [h.2]
    · by_contra hc
      have := pow_le_pow_left₀ (W.nonneg.trans W.lt.le) (not_lt.1 hc) 2
      linarith [h.1]
  have hcomp := LWindow.isLRegularizedGeodesicOn_comp W ⟨first, hj⟩ S hO (fun r hr => hr.2)
    (fun r hr => hSm _ (hin r hr.1)) (fun r hr => hSreg _ (hin r hr.1))
    (fun r hr => hγ r (hOW hr))
  have heqO : ∀ r ∈ O, α ⟨first, le_rfl, hle⟩ =ᶠ[𝓝 r] W.f ⟨first, hj⟩ ∘ γ := fun r hr => by
    filter_upwards [hO.mem_nhds hr] with r' hr'
    exact (heq ⟨first, hj⟩ (Ioo_subset_Icc_self hr'.2)).symm
  exact (hcomp.congr_of_eventuallyEq heqO) s hsO

private theorem hasHistoryLInitialVector_of_eq_of_le {c : ℝ}
    {α α' : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    {Z : TangentSpace ThreeModel p} (hc : 0 < c) (hcdom : T - c ^ 2 ∈ H.stageDomain first)
    (h : H.HasHistoryLInitialVector T α p Z) (heq : ∀ j r, r ≤ c → α' j r = α j r) :
    H.HasHistoryLInitialVector T α' p Z := by
  obtain ⟨lo, hlo, W, x, Zx, ha, hx, hZ, hb, hW⟩ := h
  have hT : T ∈ H.stageDomain last := by simpa [ha] using W.upper
  set b' := min W.b c
  have hab : W.a < b' := lt_min W.lt (ha ▸ hc)
  have hb'0 : 0 ≤ b' := W.nonneg.trans hab.le
  have hb'b : b' ≤ W.b := min_le_left _ _
  have hb'c : b' ≤ c := min_le_right _ _
  have hlowb : T - W.b ^ 2 ≤ T - b' ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hb'0 hb'b 2) T
  have hbv : T - c ^ 2 ≤ T - b' ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hb'0 hb'c 2) T
  have hbT : T - b' ^ 2 ≤ T := by nlinarith
  have h0 : 0 ≤ T - b' ^ 2 :=
    (H.time_nonneg first).trans ((H.time_le_of_mem_stageDomain hcdom).trans hbv)
  have hH : T - b' ^ 2 ≤ H.horizon :=
    hbT.trans ((H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon _))
  obtain ⟨lo', hlo'⟩ := exists_mem_stageDomain (H := H) h0 hH
  have h1 : lo ≤ lo' := le_of_mem_stageDomain W.lower hlo' hlowb
  have h2 : first ≤ lo' := le_of_mem_stageDomain hcdom hlo' hbv
  have h3 : lo' ≤ last := le_of_mem_stageDomain hlo' hT hbT
  refine ⟨lo', h2, W.restrict h1 le_rfl h3 le_rfl hab hb'b W.upper hlo', x, Zx, ha, hx, hZ,
    ?_, fun j r hr => ?_⟩
  · obtain ⟨γ, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hb
    exact ⟨γ, J, hJo, hJc, h0J, hJc.Icc_subset h0J hbJ ⟨hb'0, hb'b⟩, hcurve⟩
  · have hend : H.regularizedStageEnd T b' j.val ≤ b' := by
      unfold regularizedStageEnd
      calc Real.sqrt (T - max (T - b' ^ 2) (H.time j.val)) ≤ Real.sqrt (b' ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [le_max_left (T - b' ^ 2) (H.time j.val)])
        _ = b' := Real.sqrt_sq hb'0
    change _ = α' ⟨j.val, h2.trans j.property.1, j.property.2⟩ r
    rw [heq _ r (hr.2.trans (hend.trans hb'c))]
    exact hW ⟨j.val, h1.trans j.property.1, j.property.2⟩
      ⟨hr.1, hr.2.trans (regularizedStageEnd_le_of_le hb'0 hb'b j.val)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_stage_window_lift {k : Fin (H.eventCount + 1)} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := (H.stage k).Carrier) D)
    (hSm : ∀ t ∈ Ioo (H.time k) (H.stageEndTime k), S.base.metric t = H.stageMetric k t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hstart : H.time k < T - b ^ 2)
    (hend : T - a ^ 2 < H.stageEndTime k) {δ : ℝ → (H.stage k).Carrier}
    (hδ : IsLRegularizedGeodesicOn S T δ (Ioo a b)) :
    ∃ W : H.LWindow k k T, W.a = a ∧ W.b = b ∧ ∃ γ : ℝ → W.X,
      IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
      ∀ r, W.f ⟨k, le_rfl, le_rfl⟩ (γ r) = δ r := by
  classical
  obtain ⟨W, hWa, hWb, hr⟩ := LWindow.exists_stage (T := T) k ha hab hstart hend
  have hrange := hr ⟨k, le_rfl, le_rfl⟩
  have hmem : ∀ y, y ∈ range (W.f ⟨k, le_rfl, le_rfl⟩) := fun y => by
    rw [hrange]
    exact mem_univ y
  have : Nonempty W.X := ⟨(hmem (δ a)).choose⟩
  let γ : ℝ → W.X := fun r => Function.invFun (W.f ⟨k, le_rfl, le_rfl⟩) (δ r)
  have hγf : ∀ r, W.f ⟨k, le_rfl, le_rfl⟩ (γ r) = δ r := fun r => Function.invFun_eq (hmem _)
  refine ⟨W, hWa, hWb, γ, ?_, hγf⟩
  have hin : ∀ s ∈ Ioo W.a W.b, T - s ^ 2 ∈ Ioo (H.time k) (H.stageEndTime k) := by
    intro s hs
    rw [hWa, hWb] at hs
    have h1 : a ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 ha two_ne_zero
    have h2 : s ^ 2 < b ^ 2 := pow_lt_pow_left₀ hs.2 (ha.trans hs.1.le) two_ne_zero
    exact ⟨by linarith, by linarith⟩
  have hδ' : IsLRegularizedGeodesicOn S T δ (Ioo W.a W.b) := by
    rw [hWa, hWb]
    exact hδ
  have hcomp : IsLRegularizedGeodesicOn S T (W.f ⟨k, le_rfl, le_rfl⟩ ∘ γ) (Ioo W.a W.b) :=
    hδ'.congr_of_eventuallyEq fun r _ => Eventually.of_forall fun r' => hγf r'
  have hinv := (W.contMDiffOn_invFun ⟨k, le_rfl, le_rfl⟩).continuousOn
  rw [hrange] at hinv
  refine hcomp.of_comp_localPullMetric (W.localDiffeomorph _) (fun s hs => ?_)
    (fun s hs _ => W.regular s (Ioo_subset_Icc_self hs)) (fun s hs => ?_) (fun s hs => ?_)
  · rw [W.metric ⟨k, le_rfl, le_rfl⟩ s (mem_regularizedStage_Ioo W.nonneg hs (hin s hs)),
      hSm _ (hin s hs)]
  · filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact (hinv.continuousAt (isOpen_univ.mem_nhds (mem_univ _))).comp (hδ' r hr).2.1.continuousAt
  · filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact (hcomp r hr).2.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem actionGoodNear_of_window_of_le {c : ℝ} (hc : 0 < c) (hcv : c ≤ v)
    (hcdom : T - c ^ 2 ∈ H.stageDomain first) {Z₀ : ThreeSpace} {s₀ : ℝ} (hs₀c : s₀ < c)
    {V : Set ThreeSpace} (hV : IsOpen V) (hZ₀V : Z₀ ∈ V)
    (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p)
    (hVdomc : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T c p)
    {lo hi : Fin (H.eventCount + 1)} (hlo : first ≤ lo) (hhi : hi ≤ last)
    (W : H.LWindow lo hi T) {K : Set ℝ} (hK : IsOpen K) (hs₀K : s₀ ∈ K) (hKW : K ⊆ Ioo W.a W.b)
    {β : ThreeSpace × ℝ → W.X}
    (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
    (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K)
    (hrep : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
      ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
        H.historyLCurve hle T c p ⟨Z, hVdomc Z hZ⟩
          ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r))) :
    H.ActionGoodNear hle T v p Z₀ s₀ := by
  refine ⟨V, hV, hZ₀V, K ∩ Iio c, hK.inter isOpen_Iio, ⟨hs₀K, hs₀c⟩,
    fun j r₁ r₂ hr hsub => pieceAction_local_of_window hlo hhi W hV (hK.inter isOpen_Iio)
      (fun r hr => hKW hr.1) (hβ.mono (prod_mono subset_rfl inter_subset_left))
      (fun Z hZ r hr => hgeo Z hZ r hr.1) hVdom (fun Z hZ j' r hr => ?_) j hr hsub⟩
  have ht := W.mem_Icc_of_mem_piece j' (Ioo_subset_Icc_self hr.2)
  have hr0 : 0 ≤ r := W.nonneg.trans (hKW hr.1.1).1.le
  have hrc : r ∈ Icc (H.regularizedStageStart T 0 j'.val) (H.regularizedStageEnd T c j'.val) :=
    mem_regularizedStage_Icc le_rfl ⟨hr0, hr.1.2.le⟩ ht
  set Zd : H.historyLExpDomain hle T v p := ⟨Z, hVdom Z hZ⟩
  have htr := eqOn_historyLCurve hc ⟨Z, hVdomc Z hZ⟩
    ((isHistoryLGeodesicOn_historyLCurve Zd).truncate le_rfl hle hc hcv hcdom)
    ((hasHistoryLInitialVector_historyLCurve Zd).truncate hc le_rfl hcdom)
    ⟨j'.val, hlo.trans j'.property.1, j'.property.2.trans hhi⟩ hrc
  rw [← hrep Z hZ j' r ⟨hr.1.1, hr.2⟩]
  exact htr.symm

end Helpers

section ClosedStart

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_package_of_closedStart (hv : 0 < v) (hstart : T - v ^ 2 = H.time first)
    (htf : H.time first < H.stageEndTime first) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) ∧
      (∃ g : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ g V ∧
        ∀ Z ∈ V, ∀ hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
          H.historyLExp hle T v p ⟨Z, hZ⟩ = g Z) ∧
      ∀ s₀ ∈ Icc 0 v, H.ActionGoodNear hle T v p Z₀ s₀ := by
  classical
  obtain ⟨G, -, hGm⟩ := exists_incomingSlab_stageMetric first htf
  have hmetric := G.smoothUpTo.jointContMDiffOn
  have hSm : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      G.flow.base.metric t = H.stageMetric first t := fun t ht => (hGm t ht).symm
  have hSreg : ∀ t ∈ Ioo (H.time first) (H.stageEndTime first),
      t ∈ (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first) G.lt).regular :=
    fun t ht => ht
  set fZ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  set Zd : H.historyLExpDomain hle T v p := ⟨Z₀, hZ₀⟩
  have hα₀ := isHistoryLGeodesicOn_historyLCurve Zd
  have hinit₀ := hasHistoryLInitialVector_historyLCurve Zd
  have hev1 : ∀ᶠ s in 𝓝[<] v, 0 < s ∧ T - s ^ 2 < H.stageEndTime first := by
    have hc : ContinuousAt (fun s : ℝ => T - s ^ 2) v := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const
      (by rw [hstart]; exact htf)), nhdsWithin_le_nhds (lt_mem_nhds hv)] with s h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨s₁, ⟨hs₁pos, hs₁b⟩, hs₁v⟩ := (hev1.and self_mem_nhdsWithin).exists
  have hs₁v' : s₁ < v := hs₁v
  have hin : ∀ s ∈ Ioo s₁ v, T - s ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    intro s hs
    have h1 : s₁ ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 hs₁pos.le two_ne_zero
    have h2 : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hs.2 (hs₁pos.trans hs.1).le two_ne_zero
    constructor <;> linarith
  have hgeo₀ := isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn hα₀ G.flow hSm hSreg
    hs₁pos le_rfl hin
  obtain ⟨ξ, hlim⟩ := exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart
    G.flow G.equation htf hmetric hs₁pos hs₁v' hstart (fun s hs => hSreg _ (hin s hs)) hgeo₀
  set γ₀ : ℝ → (H.stage first).Carrier := H.historyLCurve hle T v p Zd fZ
  set x0 := ξ.proj
  set e := trivializationAt ThreeSpace (TangentSpace ThreeModel) x0
  set zl : ThreeSpace × ThreeSpace := (extChartAt ThreeModel x0 x0, (e ξ).2)
  have hξ : ξ ∈ e.source := by
    rw [e.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x0
  have hzl : zl.1 ∈ interior (extChartAt ThreeModel x0).target := by
    rw [(isOpen_extChartAt_target (I := ThreeModel) x0).interior_eq]
    exact mem_extChartAt_target (I := ThreeModel) x0
  let st : ℝ → ThreeSpace × ThreeSpace := fun s =>
    (extChartAt ThreeModel x0 (γ₀ s),
      trivToE (I := ThreeModel) x0 (γ₀ s) (lVelocity (I := ThreeModel) γ₀ s))
  have hlim' := (e.tendsto_nhds_iff hξ).mp hlim
  have hproj : Tendsto γ₀ (𝓝[<] v) (𝓝 x0) := hlim'.1
  have hbase : ∀ᶠ s in 𝓝[<] v, γ₀ s ∈ (chartAt ThreeSpace x0).source :=
    hproj.eventually ((chartAt ThreeSpace x0).open_source.mem_nhds (mem_chart_source ThreeSpace x0))
  have hst : Tendsto st (𝓝[<] v) (𝓝 zl) := by
    refine ((continuousAt_extChartAt (I := ThreeModel) x0).tendsto.comp hproj).prodMk_nhds ?_
    refine hlim'.2.congr' ?_
    filter_upwards [hbase] with s hs
    have hsb : γ₀ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hs
    exact (e.continuousLinearMapAt_apply_of_mem (R := ℝ) hsb _).symm
  obtain ⟨ε, hε, W, hWo, hvW, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
    exists_lPhaseFlow_of_start G.flow htf hmetric hv hstart x0 zl hzl
  have hmax : max s₁ (v - ε) < v := max_lt hs₁v' (by linarith)
  have hpair : Tendsto (fun s => (s, st s)) (𝓝[<] v) (𝓝 (v, zl)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).prodMk_nhds hst
  obtain ⟨c₀, hc₀W, hc₀src, hc₀I⟩ := ((hpair.eventually (hWo.mem_nhds hvW)).and
    (hbase.and (Ioo_mem_nhdsLT hmax))).exists
  set c : ℝ := (c₀ + v) / 2 with hcdef
  have hc₀c : c₀ < c := by linarith [hc₀I.2]
  have hcv : c < v := by linarith [hc₀I.2]
  have hms : max s₁ (v - ε) < c₀ := hc₀I.1
  have hs₁c₀ : s₁ < c₀ := (le_max_left _ _).trans_lt hms
  have hc₀pos : 0 < c₀ := hs₁pos.trans hs₁c₀
  have hcpos : 0 < c := hc₀pos.trans hc₀c
  have hcin := hin c ⟨hs₁c₀.trans hc₀c, hcv⟩
  have hcdom : T - c ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hcin
  have hαc := hα₀.truncate le_rfl hle hcpos hcv.le hcdom
  have hinitc := hinit₀.truncate hcpos le_rfl hcdom
  obtain ⟨lo, hi, hlo, hhi, Wc, hcW, -, γc, hγc, heqc⟩ := hα₀.2.2.1 c ⟨hcpos, hcv⟩
  have hjc : lo ≤ first ∧ first ≤ hi :=
    LWindow.mem_range_of_mem_Icc Wc hcW ⟨hcin.1.le, hcin.2.le⟩
  set a' : ℝ := max Wc.a c₀
  set b' : ℝ := min Wc.b ((c + v) / 2)
  have ha'c : a' < c := max_lt hcW.1 hc₀c
  have hcb' : c < b' := lt_min hcW.2 (by linarith)
  have ha'I : a' ∈ Ioo s₁ v := ⟨hs₁c₀.trans_le (le_max_right _ _), ha'c.trans hcv⟩
  have hb'I : b' ∈ Ioo s₁ v :=
    ⟨(hs₁c₀.trans hc₀c).trans hcb', (min_le_right _ _).trans_lt (by linarith)⟩
  let W₁ := Wc.restrict hjc.1 hjc.2 le_rfl (le_max_left _ _) (ha'c.trans hcb') (min_le_left _ _)
    (H.mem_stageDomain_of_mem_Ioo (hin a' ha'I)) (H.mem_stageDomain_of_mem_Ioo (hin b' hb'I))
  have hZ₀c : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T c p := by
    refine ⟨_, hαc, hinitc, W₁, ⟨ha'c, hcb'⟩, γc,
      fun r hr => hγc r ⟨(le_max_left _ _).trans_lt hr.1, hr.2.trans_le (min_le_left _ _)⟩,
      fun r hr => ?_⟩
    have ht := hin r ⟨hs₁c₀.trans_le ((le_max_right _ _).trans hr.1.le), hr.2.trans_lt hcv⟩
    exact heqc ⟨first, hjc⟩ (mem_regularizedStage_Icc Wc.nonneg
      ⟨(le_max_left _ _).trans hr.1.le, hr.2.trans hcW.2.le⟩ ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨V₁, hV₁, hZ₀V₁, -, hV₁dom, lo₁, hi₁, hlo₁, hhi₁, W₂, K₁, hK₁, hc₀K₁, hK₁W, β₁, hβ₁,
    hgeo₁, hrep₁⟩ := exists_contMDiffOn_window_family_historyLCurve hcpos hZ₀c ⟨hc₀pos, hc₀c⟩
  have ht₀ := hin c₀ ⟨hs₁c₀, hc₀c.trans hcv⟩
  have hj₁ : lo₁ ≤ first ∧ first ≤ hi₁ :=
    LWindow.mem_range_of_mem_Icc W₂ (hK₁W hc₀K₁) ⟨ht₀.1.le, ht₀.2.le⟩
  let F₁ : ThreeSpace × ℝ → (H.stage first).Carrier := fun q => W₂.f ⟨first, hj₁⟩ (β₁ q)
  set O₁ : Set ℝ := K₁ ∩ Ioo (H.regularizedStageStart T W₂.a first)
    (H.regularizedStageEnd T W₂.b first) ∩ Ioo (max s₁ (v - ε)) c
  have hO₁ : IsOpen O₁ := (hK₁.inter isOpen_Ioo).inter isOpen_Ioo
  have hc₀O₁ : c₀ ∈ O₁ :=
    ⟨⟨hc₀K₁, mem_regularizedStage_Ioo W₂.nonneg (hK₁W hc₀K₁) ht₀⟩, hms, hc₀c⟩
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hO₁ c₀ hc₀O₁
  set J₁ : Set ℝ := Ioo (c₀ - δ₁) (c₀ + δ₁)
  have hJ₁ : J₁ ⊆ O₁ := fun r hr => hball₁ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  have hc₀J₁ : c₀ ∈ J₁ := ⟨by linarith, by linarith⟩
  have hJ₁in : ∀ r ∈ J₁, r ∈ Ioo s₁ v := fun r hr =>
    ⟨(le_max_left _ _).trans_lt (hJ₁ hr).2.1, (hJ₁ hr).2.2.trans hcv⟩
  have hJ₁L : J₁ ⊆ Ioo (max s₁ (v - ε)) v := fun r hr => ⟨(hJ₁ hr).2.1, (hJ₁ hr).2.2.trans hcv⟩
  have hF₁geo : ∀ Z ∈ V₁, IsLRegularizedGeodesicOn G.flow T (fun r => F₁ (Z, r)) J₁ :=
    fun Z hZ => LWindow.isLRegularizedGeodesicOn_comp W₂ ⟨first, hj₁⟩ G.flow isOpen_Ioo
      (fun r hr => (hJ₁ hr).1.2) (fun r hr => hSm _ (hin r (hJ₁in r hr)))
      (fun r hr => hSreg _ (hin r (hJ₁in r hr))) (fun r hr => hgeo₁ Z hZ r (hJ₁ hr).1.1)
  have hF₁rep : ∀ Z (hZ : Z ∈ V₁), ∀ r ∈ J₁,
      H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ⟩ fZ r = F₁ (Z, r) := fun Z hZ r hr =>
    hrep₁ Z hZ ⟨first, hj₁⟩ r (hJ₁ hr).1
  have hF₁at : ∀ Z ∈ V₁, ContMDiffAt (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ F₁ (Z, c₀) :=
    fun Z hZ => (W₂.localDiffeomorph _).contMDiff.contMDiffAt.comp (Z, c₀)
      ((hβ₁ (Z, c₀) ⟨hZ, hc₀K₁⟩).contMDiffAt ((hV₁.prod hK₁).mem_nhds ⟨hZ, hc₀K₁⟩))
  have hposC : ContinuousOn (fun Z => F₁ (Z, c₀)) V₁ := fun Z hZ =>
    (((hF₁at Z hZ).comp (f := fun Z' : ThreeSpace => (Z', c₀)) Z
      (contMDiffAt_id.prodMk contMDiffAt_const)).continuousAt).continuousWithinAt
  set V₁' : Set ThreeSpace := V₁ ∩ (fun Z => F₁ (Z, c₀)) ⁻¹' (chartAt ThreeSpace x0).source
  have hV₁' : IsOpen V₁' := hposC.isOpen_inter_preimage hV₁ (chartAt ThreeSpace x0).open_source
  let σ : ThreeSpace → ThreeSpace × ThreeSpace := fun Z =>
    (extChartAt ThreeModel x0 (F₁ (Z, c₀)),
      fderiv ℝ (fun s : ℝ => extChartAt ThreeModel x0 (F₁ (Z, s))) c₀ (1 : ℝ))
  have hσ : ContDiffOn ℝ ∞ σ V₁' := fun Z hZ =>
    (contDiffAt_familySeed x0 hZ.2 (hF₁at Z hZ.1)).contDiffWithinAt
  have hσv : ∀ Z ∈ V₁', σ Z = (extChartAt ThreeModel x0 (F₁ (Z, c₀)),
      trivToE (I := ThreeModel) x0 (F₁ (Z, c₀))
        (lVelocity (I := ThreeModel) (fun s => F₁ (Z, s)) c₀)) := fun Z hZ =>
    Prod.ext rfl (lPhaseSeed_velocity (I := ThreeModel) x0 ((hF₁geo Z hZ.1) c₀ hc₀J₁).2.1 hZ.2)
  set V₂ : Set ThreeSpace :=
    V₁' ∩ (fun Z => ((c₀, σ Z) : ℝ × (ThreeSpace × ThreeSpace))) ⁻¹' W
  have hV₂ : IsOpen V₂ :=
    (continuousOn_const.prodMk hσ.continuousOn).isOpen_inter_preimage hV₁' hWo
  have hγ₀F : ∀ r ∈ J₁, F₁ (Z₀, r) = γ₀ r := by
    intro r hr
    have ht := hin r (hJ₁in r hr)
    have hrc : r ∈ Icc (H.regularizedStageStart T 0 first) (H.regularizedStageEnd T c first) :=
      mem_regularizedStage_Icc le_rfl ⟨(hs₁pos.trans (hJ₁in r hr).1).le, (hJ₁ hr).2.2.le⟩
        ⟨ht.1.le, ht.2.le⟩
    rw [← hF₁rep Z₀ hZ₀V₁ r hr]
    exact eqOn_historyLCurve hcpos _ hαc hinitc fZ hrc
  have hγ₀germ : (fun r => F₁ (Z₀, r)) =ᶠ[𝓝 c₀] γ₀ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hc₀J₁) fun r hr => hγ₀F r hr
  have hvelF : lVelocity (I := ThreeModel) (fun r => F₁ (Z₀, r)) c₀ =
      lVelocity (I := ThreeModel) γ₀ c₀ := by
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hγ₀germ
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  have hZ₀V₁' : Z₀ ∈ V₁' := by
    refine ⟨hZ₀V₁, ?_⟩
    change F₁ (Z₀, c₀) ∈ (chartAt ThreeSpace x0).source
    rw [hγ₀F c₀ hc₀J₁]
    exact hc₀src
  have hσZ₀ : σ Z₀ = st c₀ := by
    simp only [hσv Z₀ hZ₀V₁', hvelF]
    rw [hγ₀F c₀ hc₀J₁]
  have hZ₀V₂ : Z₀ ∈ V₂ := by
    refine ⟨hZ₀V₁', ?_⟩
    change ((c₀, σ Z₀) : ℝ × (ThreeSpace × ThreeSpace)) ∈ W
    rw [hσZ₀]
    exact hc₀W
  let zZ : ThreeSpace → ℝ → ThreeSpace × ThreeSpace := fun Z r => Ψ ((c₀, σ Z), r)
  let βt : ThreeSpace → ℝ → (H.stage first).Carrier := fun Z =>
    lPhaseCurve (I := ThreeModel) x0 (zZ Z)
  have hLsub : ∀ r ∈ Ioo (max s₁ (v - ε)) v, r ∈ Ioc (v - ε) v ∧ r ∈ Ioo s₁ v := fun r hr =>
    ⟨⟨(le_max_right _ _).trans_lt hr.1, hr.2.le⟩, ⟨(le_max_left _ _).trans_lt hr.1, hr.2⟩⟩
  have hzd : ∀ Z ∈ V₂, ∀ r ∈ Ioo (max s₁ (v - ε)) v,
      HasDerivAt (zZ Z) (lPhaseField G.flow T x0 r (zZ Z r)) r ∧
        T - r ^ 2 ∈ (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first)
          G.lt).regular ∧
        (zZ Z r).1 ∈ interior (extChartAt ThreeModel x0).target := fun Z hZ r hr =>
    ⟨(hΨd _ hZ.2 r (hLsub r hr).1).1, hSreg _ (hin r (hLsub r hr).2),
      (hΨd _ hZ.2 r (hLsub r hr).1).2.2⟩
  have hβtgeo : ∀ Z ∈ V₂,
      IsLRegularizedGeodesicOn G.flow T (βt Z) (Ioo (max s₁ (v - ε)) v) :=
    fun Z hZ => isLRegularizedGeodesicOn_lPhaseCurve G.flow T x0 isOpen_Ioo (hzd Z hZ)
  have hagreeJ : ∀ Z ∈ V₂, ∀ r ∈ J₁, F₁ (Z, r) = βt Z r := fun Z hZ r hr =>
    eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn G.flow G.equation T x0 isOpen_Ioo
      isPreconnected_Ioo (hF₁geo Z hZ.1.1) isOpen_Ioo isPreconnected_Ioo (hzd Z hZ) hc₀J₁
      (hJ₁L hc₀J₁) hZ.1.2 ((hΨ0 _ hZ.2).trans (hσv Z hZ.1)) ⟨hr, hJ₁L hr⟩
  have hαcgeo : ∀ Z (hZ : Z ∈ V₁), IsLRegularizedGeodesicOn G.flow T
      (H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ⟩ fZ) (Ioo s₁ c) := fun Z hZ =>
    isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn (isHistoryLGeodesicOn_historyLCurve _)
      G.flow hSm hSreg hs₁pos le_rfl fun s hs => hin s ⟨hs.1, hs.2.trans hcv⟩
  have hmc : max s₁ (v - ε) < c := hms.trans hc₀c
  have hagree : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) c,
      H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ r = βt Z r := by
    intro Z hZ
    have hgerm : H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ =ᶠ[𝓝 c₀] βt Z :=
      eventually_of_mem (isOpen_Ioo.mem_nhds hc₀J₁) fun r hr =>
        (hF₁rep Z hZ.1.1 r hr).trans (hagreeJ Z hZ r hr)
    have hvel : lVelocity (I := ThreeModel) (H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ)
        c₀ = lVelocity (I := ThreeModel) (βt Z) c₀ := by
      have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hgerm
      with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
    have heq := lRegularizedSolution_eqOn G.flow G.equation T isOpen_Ioo isPreconnected_Ioo
      (⟨hs₁c₀, hc₀c⟩ : c₀ ∈ Ioo s₁ c) isOpen_Ioo isPreconnected_Ioo (hJ₁L hc₀J₁)
      (hαcgeo Z hZ.1.1) (hβtgeo Z hZ) hgerm.self_of_nhds hvel
    intro r hr
    rcases hr.2.lt_or_eq with hrc | hrc
    · exact heq ⟨⟨(le_max_left _ _).trans_lt hr.1, hrc⟩, hr.1, hrc.trans hcv⟩
    rw [hrc]
    have hcont1 := (isHistoryLGeodesicOn_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)).2.2.2
    have hcont2 : ContinuousWithinAt (βt Z) (Iio c) c :=
      ((hβtgeo Z hZ) c ⟨hmc, hcv⟩).2.1.continuousAt.continuousWithinAt
    have hev : H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ fZ =ᶠ[𝓝[<] c] βt Z := by
      filter_upwards [Ioo_mem_nhdsLT hmc] with r' hr'
      exact heq ⟨⟨(le_max_left _ _).trans_lt hr'.1, hr'.2⟩, hr'.1, hr'.2.trans hcv⟩
    exact tendsto_nhds_unique_of_eventuallyEq hcont1 hcont2 hev
  let A : ∀ Z ∈ V₂, (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun Z hZ j r => if h : j.val = first ∧ c < r then
      cast (congrArg (fun k => (H.stage k).Carrier) h.1.symm) (βt Z r)
    else H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ j r
  have hAle : ∀ Z (hZ : Z ∈ V₂) j r, r ≤ c →
      A Z hZ j r = H.historyLCurve hle T c p ⟨Z, hV₁dom Z hZ.1.1⟩ j r := fun Z hZ j r hr =>
    dite_eq_right fun h => (not_lt.2 hr) h.2
  have hAgt : ∀ Z (hZ : Z ∈ V₂) r, c < r → A Z hZ fZ r = βt Z r := fun Z hZ r hr => by
    simp only [A, dite_eq_left (show fZ.val = first ∧ c < r from ⟨rfl, hr⟩)]
    rfl
  have hAfirst : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) v, A Z hZ fZ r = βt Z r := by
    intro Z hZ r hr
    rcases le_or_gt r c with hrc | hrc
    · rw [hAle Z hZ fZ r hrc]
      exact hagree Z hZ r ⟨hr.1, hrc⟩
    · exact hAgt Z hZ r hrc
  have hvI : v ∈ Ioo (v - ε) (v + ε) := ⟨by linarith, by linarith⟩
  have hvI' : v ∈ Ioc (v - ε) v := ⟨by linarith, le_rfl⟩
  have hmem : ∀ Z (hZ : Z ∈ V₂), H.IsHistoryLGeodesicOn hle T v (A Z hZ) ∧
      H.HasHistoryLInitialVector T (A Z hZ) p Z := by
    intro Z hZ
    have hαcZ := isHistoryLGeodesicOn_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)
    have hinitcZ := hasHistoryLInitialVector_historyLCurve
      (⟨Z, hV₁dom Z hZ.1.1⟩ : H.historyLExpDomain hle T c p)
    refine ⟨⟨hα₀.1, fun i hf hl => ?_, fun s hs => ?_, ?_⟩,
      hasHistoryLInitialVector_of_eq_of_le hcpos hcdom hinitcZ fun j r hr => hAle Z hZ j r hr⟩
    · have h1 : H.stageEndTime first ≤ H.time i.succ := by
        rw [← stageEndTime_castSucc]
        exact H.stageEndTime_mono hf
      have hw : Real.sqrt (T - H.time i.succ) ≤ c :=
        ((Real.sqrt_lt' hcpos).2 (by linarith [hcin.2])).le
      rw [hAle Z hZ _ _ hw, hAle Z hZ _ _ hw]
      exact hαcZ.2.1 i hf hl
    · rcases lt_or_ge s c with hsc | hsc
      · obtain ⟨lo', hi', hlo', hhi', W', hsW', hbc, γ', hγ', heq'⟩ := hαcZ.2.2.1 s ⟨hs.1, hsc⟩
        refine ⟨lo', hi', hlo', hhi', W', hsW', hbc.trans hcv.le, γ', hγ', fun j r hr => ?_⟩
        rw [heq' j hr, hAle Z hZ _ r ((W'.piece_subset j hr).2.trans hbc)]
      · set a₂ : ℝ := (max s₁ (v - ε) + c) / 2 with ha₂def
        set b₂ : ℝ := (s + v) / 2 with hb₂def
        have ha₂c : a₂ < c := by linarith
        have hma₂ : max s₁ (v - ε) < a₂ := by linarith
        have hsb₂ : s < b₂ := by linarith [hs.2]
        have hb₂v : b₂ < v := by linarith [hs.2]
        have ha₂0 : 0 ≤ a₂ := (hs₁pos.le.trans (le_max_left _ _)).trans hma₂.le
        have htb₂ : H.time first < T - b₂ ^ 2 := by
          have : b₂ ^ 2 < v ^ 2 := pow_lt_pow_left₀ hb₂v (by linarith) two_ne_zero
          linarith
        have hta₂ : T - a₂ ^ 2 < H.stageEndTime first :=
          (hin a₂ ⟨(le_max_left _ _).trans_lt hma₂, ha₂c.trans hcv⟩).2
        obtain ⟨Wn, hWna, hWnb, γn, hγn, hγnf⟩ := exists_stage_window_lift G.flow hSm ha₂0
          ((ha₂c.trans_le hsc).trans hsb₂) htb₂ hta₂
          (fun r hr => hβtgeo Z hZ r ⟨hma₂.trans hr.1, hr.2.trans hb₂v⟩)
        refine ⟨first, first, le_rfl, hle, Wn, by rw [hWna, hWnb]; exact ⟨ha₂c.trans_le hsc, hsb₂⟩,
          by rw [hWnb]; exact hb₂v.le, γn, hγn, fun j r hr => ?_⟩
        obtain ⟨jv, hj1, hj2⟩ := j
        obtain rfl : first = jv := le_antisymm hj1 hj2
        have hrI : r ∈ Icc Wn.a Wn.b := Wn.piece_subset _ hr
        rw [hWna, hWnb] at hrI
        change Wn.f ⟨first, hj1, hj2⟩ (γn r) = A Z hZ fZ r
        rw [hγnf r]
        exact (hAfirst Z hZ r ⟨hma₂.trans_le hrI.1, hrI.2.trans hb₂v.le⟩).symm
    · have hint := (hΨd _ hZ.2 v hvI').2.2
      have hzc : ContinuousAt (zZ Z) v :=
        (hΨsm.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
          (fun r hr => ⟨hZ.2, hr⟩)).continuousAt (isOpen_Ioo.mem_nhds hvI)
      have hβc : ContinuousAt (βt Z) v :=
        (continuousAt_extChartAt_symm'' (interior_subset hint)).comp
          (f := fun r => (zZ Z r).1) hzc.fst
      refine hβc.continuousWithinAt.congr_of_eventuallyEq ?_ (hAgt Z hZ v hcv)
      filter_upwards [Ioo_mem_nhdsLT hcv] with r hr
      exact hAgt Z hZ r hr.1
  have hV₂dom : ∀ Z ∈ V₂, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p :=
    fun Z hZ => ⟨A Z hZ, hmem Z hZ⟩
  have hhist : ∀ Z (hZ : Z ∈ V₂), ∀ r ∈ Ioc (max s₁ (v - ε)) v,
      H.historyLCurve hle T v p ⟨Z, hV₂dom Z hZ⟩ fZ r = βt Z r := by
    intro Z hZ r hr
    have hr1 : s₁ < r := (le_max_left _ _).trans_lt hr.1
    have hr0 : 0 ≤ r := hs₁pos.le.trans hr1.le
    have ht : T - r ^ 2 ∈ Icc (H.time first) (H.stageEndTime first) := by
      have h1 : s₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr1 hs₁pos.le two_ne_zero
      have h2 : r ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
      constructor <;> linarith
    rw [eqOn_historyLCurve hv ⟨Z, hV₂dom Z hZ⟩ (hmem Z hZ).1 (hmem Z hZ).2 fZ
      (mem_regularizedStage_Icc le_rfl ⟨hr0, hr.2⟩ ht)]
    exact hAfirst Z hZ r hr
  have hΨsm' : ContDiffOn ℝ ∞ (fun q : ThreeSpace × ℝ => Ψ ((c₀, σ q.1), q.2))
      (V₂ ×ˢ Ioo (v - ε) (v + ε)) :=
    hΨsm.comp ((contDiffOn_const.prodMk ((hσ.mono inter_subset_left).comp contDiffOn_fst
      fun q hq => hq.1)).prodMk contDiffOn_snd) fun q hq => ⟨hq.1.2, hq.2⟩
  have hgsm : ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ (fun Z => βt Z v) V₂ := by
    have h1 : ContDiffOn ℝ ∞ (fun Z : ThreeSpace => Ψ ((c₀, σ Z), v)) V₂ :=
      hΨsm'.comp (contDiffOn_id.prodMk contDiffOn_const) fun Z hZ => ⟨hZ, hvI⟩
    refine (contMDiffOn_extChartAt_symm (I := ThreeModel) (n := ∞) x0).comp
      h1.fst.contMDiffOn fun Z hZ => ?_
    exact interior_subset (s := (extChartAt ThreeModel x0).target) (hΨd _ hZ.2 v hvI').2.2
  have hOΨ := hΨsm'.continuousOn.fst.isOpen_inter_preimage (hV₂.prod isOpen_Ioo)
    (isOpen_interior (s := (extChartAt ThreeModel x0).target))
  have hZ₀v : ((Z₀, v) : ThreeSpace × ℝ) ∈ (V₂ ×ˢ Ioo (v - ε) (v + ε)) ∩
      (fun q : ThreeSpace × ℝ => (Ψ ((c₀, σ q.1), q.2)).1) ⁻¹'
        interior (extChartAt ThreeModel x0).target :=
    ⟨⟨hZ₀V₂, hvI⟩, (hΨd _ hZ₀V₂.2 v hvI').2.2⟩
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 (hOΨ.mem_nhds hZ₀v)
  obtain ⟨V₄, hV₄u, hV₄, hZ₀V₄⟩ := mem_nhds_iff.1 hu
  obtain ⟨δ, hδ, hballδ⟩ := Metric.mem_nhds_iff.1 ht
  have hδ'pos : 0 < min δ ε := lt_min hδ hε
  have hK₂sub : Ioo (max s₁ (v - ε)) (v + min δ ε) ⊆ Ioo (v - ε) (v + ε) := fun r hr =>
    ⟨(le_max_right _ _).trans_lt hr.1, hr.2.trans_le (by linarith [min_le_right δ ε])⟩
  have hV₄' : IsOpen (V₄ ∩ V₂) := hV₄.inter hV₂
  have hint2 : ∀ q ∈ (V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε),
      (Ψ ((c₀, σ q.1), q.2)).1 ∈ interior (extChartAt ThreeModel x0).target := by
    rintro ⟨Z, r⟩ ⟨hZ, hr⟩
    rcases le_or_gt r v with hrv | hrv
    · exact (hΨd _ hZ.2.2 r ⟨(le_max_right _ _).trans_lt hr.1, hrv⟩).2.2
    · have hrt : r ∈ t := hballδ (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hr.2, min_le_left δ ε])
      exact (hut ⟨hV₄u hZ.1, hrt⟩).2
  have hBsm : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞
      (fun q : ThreeSpace × ℝ => βt q.1 q.2)
      ((V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε)) := by
    have hph : ContMDiffOn 𝓘(ℝ, ThreeSpace × ℝ) 𝓘(ℝ, ThreeSpace) ∞
        (fun q : ThreeSpace × ℝ => (Ψ ((c₀, σ q.1), q.2)).1)
        ((V₄ ∩ V₂) ×ˢ Ioo (max s₁ (v - ε)) (v + min δ ε)) :=
      (hΨsm'.fst.mono (prod_mono inter_subset_right hK₂sub)).contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hph
    exact (contMDiffOn_extChartAt_symm (I := ThreeModel) (n := ∞) x0).comp hph
      fun q hq => interior_subset (s := (extChartAt ThreeModel x0).target) (hint2 q hq)
  have hgoodEnd : ∀ s₀ ∈ Icc c v, H.ActionGoodNear hle T v p Z₀ s₀ := by
    intro s₀ hs₀
    refine ⟨V₄ ∩ V₂, hV₄', ⟨hZ₀V₄, hZ₀V₂⟩, Ioo (max s₁ (v - ε)) (v + min δ ε), isOpen_Ioo,
      ⟨hmc.trans_le hs₀.1, hs₀.2.trans_lt (by linarith)⟩, fun j r₁ r₂ hr hsub => ?_⟩
    refine pieceAction_local_of_family G.flow G.equation j hV₄' isOpen_Ioo hBsm
      (fun Z hZ => hV₂dom Z hZ.2) (fun r hr => ?_) (fun Z hZ r hr => ?_) hr hsub
    · have hrv : r ≤ v := hr.2.2.trans (regularizedStageEnd_le_self hv.le j.val)
      have hr1 : s₁ < r := (le_max_left _ _).trans_lt hr.1.1
      have h1 : s₁ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr1 hs₁pos.le two_ne_zero
      have h2 : r ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (hs₁pos.le.trans hr1.le) hrv 2
      change T - r ^ 2 ∈ Ico (H.time first) (H.stageEndTime first)
      exact ⟨by linarith, by linarith⟩
    · have hti := mem_Ioo_of_mem_regularizedStage_Ioo (H := H) hr.2
      have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.2.1
      have hrv : r < v := by nlinarith [hti.2.1]
      have hrin := hin r ⟨(le_max_left _ _).trans_lt hr.1.1, hrv⟩
      have hjk : j.val = first := eq_of_mem_Ioo_of_mem_Icc hrin ⟨hti.1.1.le, hti.1.2.le⟩
      obtain ⟨jv, hj1, hj2⟩ := j
      change jv = first at hjk
      obtain rfl : first = jv := hjk.symm
      have hev : H.historyLCurve hle T v p ⟨Z, hV₂dom Z hZ.2⟩ ⟨first, hj1, hj2⟩ =ᶠ[𝓝 r]
          βt Z := by
        filter_upwards [isOpen_Ioo.mem_nhds
          (⟨hr.1.1, hrv⟩ : r ∈ Ioo (max s₁ (v - ε)) v)] with r' hr'
        exact hhist Z hZ.2 r' ⟨hr'.1, hr'.2.le⟩
      rw [stageRegularizedLagrangian_congr_nhds first T hev]
      simp only [stageRegularizedLagrangian, lRegularizedLagrangian, SolutionOn.scalar,
        SolutionFamily.scalar, hSm _ hrin]
  have hgoodMid : ∀ s₀ ∈ Ioo 0 c, H.ActionGoodNear hle T v p Z₀ s₀ := by
    intro s₀ hs₀
    obtain ⟨V₅, hV₅, hZ₀V₅, -, hV₅dom, lo₅, hi₅, hlo₅, hhi₅, W₅, K₅, hK₅, hs₀K₅, hK₅W, β₅, hβ₅,
      hgeo₅, hrep₅⟩ := exists_contMDiffOn_window_family_historyLCurve hcpos hZ₀c hs₀
    exact actionGoodNear_of_window_of_le hcpos hcv.le hcdom hs₀.2 (hV₅.inter hV₂)
      ⟨hZ₀V₅, hZ₀V₂⟩ (fun Z hZ => hV₂dom Z hZ.2) (fun Z hZ => hV₅dom Z hZ.1) hlo₅ hhi₅ W₅ hK₅
      hs₀K₅ hK₅W (hβ₅.mono (prod_mono inter_subset_left subset_rfl))
      (fun Z hZ => hgeo₅ Z hZ.1) (fun Z hZ j r hr => hrep₅ Z hZ.1 j r hr)
  refine ⟨V₂, hV₂, hZ₀V₂, hV₂dom, ⟨fun Z => βt Z v, hgsm, fun Z hZ hZ' => ?_⟩, fun s₀ hs₀ => ?_⟩
  · rw [historyLExp_eq hv ⟨Z, hZ'⟩ (hmem Z hZ).1 (hmem Z hZ).2]
    exact hAgt Z hZ v hcv
  · rcases hs₀.1.eq_or_lt with h0 | h0
    · rw [← h0]
      exact actionGoodNear_zero hv hV₂ hZ₀V₂ hV₂dom
    rcases lt_or_ge s₀ c with hsc | hsc
    · exact hgoodMid s₀ ⟨h0, hsc⟩
    · exact hgoodEnd s₀ ⟨hsc, hs₀.2⟩

end ClosedStart

section OpenPackage

variable {first last : Fin (H.eventCount + 1)} {T B v : ℝ} {p : (H.stage last).Carrier}

theorem exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain
    {hle : first ≤ last} (hv : 0 < v) (hT : T ∈ Ico (H.time last) (H.stageEndTime last))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (q : (H.stage first).Carrier) :
    ∃ U : Set ThreeSpace, IsOpen U ∧ H.historyMinDomain hle T B v p ⊆ U ∧
      U ⊆ H.historyLExpDomain hle T v p ∧
      (∃ f : ThreeSpace → (H.stage first).Carrier,
        ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel 1 f U ∧
        ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), f Z = H.historyLExp hle T v p ⟨Z, hZ⟩) ∧
      ∃ L : ThreeSpace → ℝ, ContinuousOn L U ∧
        ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), L Z = H.historyLAction hle T v p ⟨Z, hZ⟩ :=
  by
  classical
  let f : ThreeSpace → (H.stage first).Carrier := fun Z =>
    if h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
      H.historyLExp hle T v p ⟨Z, h⟩ else q
  let L : ThreeSpace → ℝ := fun Z =>
    if h : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
      H.historyLAction hle T v p ⟨Z, h⟩ else 0
  have key : ∀ Z₀ ∈ H.historyMinDomain hle T B v p, ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
      V ⊆ H.historyLExpDomain hle T v p ∧ ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ f V ∧
      ContinuousOn L V := by
    intro Z₀ hZ₀
    have hZ₀d := historyMinDomain_subset_historyLExpDomain hZ₀
    have hlower := (isHistoryLGeodesicOn_historyLCurve
      (⟨Z₀, hZ₀d⟩ : H.historyLExpDomain hle T v p)).1
    have hlt : T - v ^ 2 < H.stageEndTime first := by
      refine lt_stageEndTime_of_mem_stageDomain hlower ?_
      have := hT.2.trans_le (H.stageEndTime_le_horizon last)
      nlinarith [pow_pos hv 2]
    obtain ⟨V, hV, hZ₀V, hVdom, ⟨g, hg, hgeq⟩, hgood⟩ :
        ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧
          (∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) ∧
          (∃ g : ThreeSpace → (H.stage first).Carrier,
            ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ g V ∧
            ∀ Z ∈ V, ∀ hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p,
              H.historyLExp hle T v p ⟨Z, hZ⟩ = g Z) ∧
          ∀ s₀ ∈ Icc 0 v, H.ActionGoodNear hle T v p Z₀ s₀ := by
      rcases (H.time_le_of_mem_stageDomain hlower).eq_or_lt with heq | hgt
      · exact exists_package_of_closedStart hv heq.symm (heq.trans_lt hlt) hZ₀d
      · exact exists_package_of_mem_historyLExpOpenDomain hv
          (historyMinDomain_subset_historyLExpOpenDomain hv ⟨hgt, hlt⟩ hfloor hZ₀)
    obtain ⟨V', hV', hZ₀V', hL⟩ := exists_continuousOn_historyLAction hZ₀d hv hgood
    refine ⟨V ∩ V', hV.inter hV', ⟨hZ₀V, hZ₀V'⟩, fun Z hZ => hVdom Z hZ.1, ?_,
      hL.mono inter_subset_right⟩
    refine (hg.mono inter_subset_left).congr fun Z hZ => ?_
    simp only [f, dite_eq_left (hVdom Z hZ.1)]
    exact hgeq Z hZ.1 _
  choose! V hV hZV hVdom hVf hVL using key
  refine ⟨⋃ Z₀ ∈ H.historyMinDomain hle T B v p, V Z₀, isOpen_biUnion fun Z₀ h => hV Z₀ h,
    fun Z hZ => mem_biUnion hZ (hZV Z hZ), iUnion₂_subset fun Z₀ h => hVdom Z₀ h,
    ⟨f, fun Z hZ => ?_, fun Z hZ => dite_eq_left hZ⟩, L, fun Z hZ => ?_, fun Z hZ => dite_eq_left hZ⟩
  · obtain ⟨Z₀, hZ₀, hZV'⟩ := mem_iUnion₂.1 hZ
    exact (((hVf Z₀ hZ₀ Z hZV').contMDiffAt ((hV Z₀ hZ₀).mem_nhds hZV')).of_le
      (by decide)).contMDiffWithinAt
  · obtain ⟨Z₀, hZ₀, hZV'⟩ := mem_iUnion₂.1 hZ
    exact ((hVL Z₀ hZ₀ Z hZV').continuousAt ((hV Z₀ hZ₀).mem_nhds hZV')).continuousWithinAt

end OpenPackage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
