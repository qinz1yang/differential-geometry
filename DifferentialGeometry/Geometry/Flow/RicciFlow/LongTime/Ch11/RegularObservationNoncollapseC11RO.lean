import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalProduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MarkedContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryNoncollapsePrefixC11RO

set_option autoImplicit false

/-!
# O-CH11-REPROVE-O (G3)：逐层 noncollapse 的核心上游——regular observation 的 noncollapse

S6 经 G2 归约到**逐层** noncollapse（`noncollapseSupply_iff_levels_C11RO`）。astra 里逐层 κ 的
核心上游是 `exists_regular_observation_noncollapsed`（`SN/RegularObservationNoncollapse.lean:178`，
reference-only，W8 树里没有）：有限 horizon `< B`、带 canonical cutoff record family（caps 只依赖
`B ε Λ`）的 retained-core history 在**整个** horizon 之前 κ-noncollapse，κ 只依赖 `(P₀, g₀, B, ε, Λ)`。
这里按其证明在树内重证（新名字，后缀 `_C11RO`）：

* `regularCanonical_of_leaves_C11RO`：W8 `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`
  （`CN/UniformEstimates.lean:249`）的 regular-terminal 版：末段 incoming slab `G` 不要求
  `SingularEndpoint`（W8 版的证明本来就不用它）。叶子 `PinchingThroughSurgery /
  NoncollapsingThroughSurgery / CanonicalNeighborhoodContinuation / SpatialCanonicalContinuation`
  作为显式参数。
* `exists_regular_observation_noncollapsed_C11RO`：把四个叶子换成 W8 的无条件定理
  （`pinchingThroughSurgery`、
  `general_noncollapsing_of_small_scale (general_small_scale_noncollapsing)`、
  `canonical_neighborhood_continuation`、`spatial_canonical_continuation`，均 0 sorry）；末段若是
  regular closed slab，用 `exists_closedSlab_or_singular_incomingSlab_from_time` 取一个延伸 slab、
  在 `extendHorizon` 上读 terminal noncollapse，再经 G1 的
  `noncollapsedBefore_iff_of_samePresentation_C11RO` 搬回。

astra 原文件唯一不在 W8 的依赖是 `ST/HistoryNoncollapsingPresentation`（由 G1 替代）；证明其余部分
逐行同 reference。没有新结构、没有额外前提；L-geometry（quarantine 的 FiniteJoint* /
LocalClockTransfer / PhysicalWeightedMinimum）**不在**这条链上。
-/

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- canonical neighborhoods through surgery 的 regular-terminal 版（末段 slab 不要求 singular
endpoint）：有限 induction 本来不需要它；model / cutoff 预算仍只依赖 `B` 与 κ。 -/
theorem regularCanonical_of_leaves_C11RO
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hpinch : PinchingThroughSurgery P₀ g₀) (hnon : NoncollapsingThroughSurgery P₀ g₀)
    (hcont : CanonicalNeighborhoodContinuation P₀ g₀)
    (hspat : SpatialCanonicalContinuation P₀ g₀) :
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε Λ : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
  ∃ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime Cgrad : ℝ≥0)
    (κ a₀ : ℝ),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧
    0 < εcap ∧ 0 < Dcap ∧ 0 < κ ∧ 0 < a₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant ≤ Λ →
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ hend : H.time (Fin.last H.eventCount) = H.horizon, H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)) ∧
      (∀ j : Fin H.eventCount,
        (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qcan
          (H.time j.succ)) ∧
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) ∧
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        ∀ hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount),
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) ∧
        G.GradientBoundBefore Cgrad qcan s ∧
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) ∧
        G.SpatiallyCanonicalBefore ε C1s C2s qcan s ∧
        ∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ε t₀ := by
  obtain ⟨εbar, hεbar, hcont⟩ := hcont
  obtain ⟨εs, hεs, hspat⟩ := hspat
  refine ⟨min εbar εs, lt_min hεbar hεs, ?_⟩
  intro B ε Λ hB hε hε' hεbar' hΛ
  obtain ⟨phi, δP, ρP, εP, hphi, hδP, hρP, hεP, hP⟩ := hpinch B hB
  obtain ⟨C1, C2, τmin, Ctime, Cgrad, hC1, hC2, hτ, hF⟩ :=
    hcont B ε hB hε hε' (hεbar'.trans (min_le_left _ _))
  obtain ⟨C1s, C2s, Cs, hC1s, hC2s, hCs, hS⟩ :=
    hspat B ε hB hε hε' (hεbar'.trans (min_le_right _ _)) C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  obtain ⟨κ, hκ, hN⟩ :=
    hnon B ε C1 C2 C1s C2s τmin Ctime Cgrad phi hB hε hε' hC1 hC2 hC1s hC2s hτ hphi
  obtain ⟨q₄, -, hS₄⟩ := hS κ phi hκ hphi
  obtain ⟨qcan, δF, ρF, εF, DF, mF, hq₄c, hqcan, hδF, hρF, hεF, hDF, hstep⟩ :=
    hF C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi q₄
  obtain ⟨qs, δS, ρS, εS, DS, mS, hqs, hqsC, hδS, hρS, hεS, -, hsp⟩ := hS₄ qcan hq₄c
  obtain ⟨δN, ρN, εN, DN, mN, hδN, hρN, hεN, -, hball⟩ := hN qcan qs hqcan hqs
  obtain ⟨a₀, ha₀, hfix⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  have hΛinv : 0 < (2 * Λ)⁻¹ := inv_pos.mpr (by positivity)
  refine ⟨C1, C2, C1s, C2s, qs, τmin, min δP (min δF (min δS (min δN (2 * Λ)⁻¹))),
    min ρP (min ρF (min ρS ρN)), min εP (min εF (min εS εN)), max DF (max DS DN),
    max mF (max mS mN), Ctime, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s, hqcan.trans_le hqs, hτ,
    lt_min hδP (lt_min hδF (lt_min hδS (lt_min hδN hΛinv))),
    lt_min hρP (lt_min hρF (lt_min hρS hρN)), lt_min hεP (lt_min hεF (lt_min hεS hεN)),
    lt_max_of_lt_left hDF, hκ, ha₀, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ hΛp H hinit htime hhor hclass
  simp only [le_min_iff, max_le_iff] at hacc hD hm hδ hρ
  have hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound := ⟨⟨hinit⟩, htime, hhor, hclass,
    CutoffParameters.recenterConstant_mul_le_half hΛ hΛp hδ.2.2.2.2⟩
  have hP' := hP p₀ δbound ρbound hacc.1 hδ.1 hρ.1 H hH
  have hpinched : H.EventSlabsPinched phi :=
    fun j => hP' j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
      (H.isContinuationSlab_event hhor j)
  have hF' := hstep qs hqs hqsC p₀ δbound ρbound hacc.2.1 hD.1 hm.1 hδ.2.1 hρ.2.1 H hH hpinched
  have hS' := hsp p₀ δbound ρbound hacc.2.2.1 hD.2.1 hm.2.1 hδ.2.2.1 hρ.2.2.1 H hH hpinched
  have hN' := hball p₀ δbound ρbound hacc.2.2.2 hD.2.2 hm.2.2 hδ.2.2.2.1 hρ.2.2.2 H hH hpinched
  have hstage : ∀ k : Fin (H.eventCount + 1),
      H.EventSlabsCanonical ε C1 C2 qcan τmin k ∧ H.EventSlabsDerivative Ctime qcan k ∧
        H.EventSlabsGradient Cgrad qcan k ∧ H.EventSlabsSpatiallyCanonical ε C1s C2s qs k ∧
        H.NoncollapsedBefore κ ε (H.time k) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      refine ⟨fun j hj => (Fin.not_lt_zero _ hj).elim, fun j hj => (Fin.not_lt_zero _ hj).elim,
        fun j hj => (Fin.not_lt_zero _ hj).elim, fun j hj => (Fin.not_lt_zero _ hj).elim, ?_⟩
      rw [H.time_zero]
      exact H.noncollapsedBefore_zero κ ε
    | succ j ih =>
      obtain ⟨hcanP, hderP, hgradP, hspatP, hncP⟩ := ih
      have hcl := (H.toHistory.event j).incoming.canonicalBefore_end_of_continuation_spatial
        (fun t₀ => H.NoncollapsedBefore κ ε t₀)
        (fun t₀ ht₀ hc hd hg hs =>
          hN'.1 j hcanP hderP hgradP hspatP t₀ ⟨ht₀.1, ht₀.2.le⟩ hc hd hg hs)
        hncP
        (fun t₀ ht₀ hc hd hg hs hn =>
          have hF₀ := hF'.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn
          (H.toHistory.event j).incoming.exists_boundsOn_spatiallyCanonicalOn hF₀
            (hS'.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hF₀))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hcanP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hderP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hgradP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.2.1
      · intro j' hj'
        rcases (Fin.castSucc_lt_succ_iff.mp hj').lt_or_eq with h | rfl
        · exact hspatP j' (Fin.castSucc_lt_castSucc_iff.mpr h)
        · exact hcl.2.2.2
      · exact hN'.1 j hcanP hderP hgradP hspatP (H.time j.succ)
          ⟨H.time_strictMono j.castSucc_lt_succ, le_rfl⟩ hcl.1 hcl.2.1 hcl.2.2.1 hcl.2.2.2
  obtain ⟨hcanL, hderL, hgradL, hspatL, hncL⟩ := hstage (Fin.last H.eventCount)
  refine ⟨fun j y t ht hR => hderL j (Fin.castSucc_lt_last j) y t ht (hqs.trans_lt hR),
    fun j => (H.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le hqs
      (hgradL j (Fin.castSucc_lt_last j)),
    fun j => (H.toHistory.event j).incoming.canonicalBefore_of_threshold_le hqs
      (hcanL j (Fin.castSucc_lt_last j)),
    fun j => hspatL j (Fin.castSucc_lt_last j), (hfix H.toHistory hinit).1, hncL, ?_⟩
  intro s G hs hinitG
  have hG : H.IsContinuationSlab B (Fin.last H.eventCount) G := ⟨hs, hinitG⟩
  have hpinchG := hP' (Fin.last H.eventCount) s G hG
  have hcl := G.canonicalBefore_end_of_continuation_spatial
    (fun t₀ => H.TerminalNoncollapsedBefore htime G hinitG κ ε t₀)
    (fun t₀ ht₀ hc hd hg hsp =>
      hN'.2 s G hG hpinchG hcanL hderL hgradL hspatL t₀ ht₀ hc hd hg hsp)
    (H.terminalNoncollapsedBefore_start htime G hinitG κ ε)
    (fun t₀ ht₀ hc hd hg hsp hn =>
      have hF₀ := hF'.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn
      G.exists_boundsOn_spatiallyCanonicalOn hF₀
        (hS'.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn hF₀))
  refine ⟨fun y t ht hR => hcl.2.1 y t ht (hqs.trans_lt hR),
    G.gradientBoundBefore_of_threshold_le hqs hcl.2.2.1,
    fun y t ht hR hτ => hcl.1 y t ht (hqs.trans_lt hR) hτ, hcl.2.2.2, ?_⟩
  intro t₀ ht₀
  exact hN'.2 s G hG hpinchG hcanL hderL hgradL hspatL t₀ ht₀
    (G.canonicalBefore_mono ht₀.2.le hcl.1) (G.derivativeBoundBefore_mono ht₀.2.le hcl.2.1)
    (G.gradientBoundBefore_mono ht₀.2.le hcl.2.2.1)
    (G.spatiallyCanonicalBefore_mono ht₀.2.le hcl.2.2.2)

/-- **regular observation noncollapse**：horizon `< B`、带 canonical cutoff record family 的
history 在整个 horizon 之前 κ-noncollapse（末段可以是 regular closed slab）；κ 与 caps 在 history
之前选定，只依赖 `(P₀, g₀, B, ε, Λ)`。 -/
theorem exists_regular_observation_noncollapsed_C11RO
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ B ε Λ : ℝ, 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    ∃ (δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (κ : ℝ),
      0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧ 0 < κ ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant ≤ Λ →
      ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ H.toHistory →
      ∀ (p : CutoffParameters)
        (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        H.NoncollapsedBefore κ ε H.horizon := by
  obtain ⟨εbar, hεbar, hcan⟩ := regularCanonical_of_leaves_C11RO P₀ g₀
    (pinchingThroughSurgery P₀ g₀)
    (general_noncollapsing_of_small_scale P₀ g₀ (general_small_scale_noncollapsing P₀ g₀))
    (canonical_neighborhood_continuation P₀ g₀) (spatial_canonical_continuation P₀ g₀)
  refine ⟨εbar, hεbar, ?_⟩
  intro B ε Λ hB hε hε' hεbar' hΛ
  obtain ⟨C1, C2, C1s, C2s, qcan, τmin, δmax, ρmax, εcap, Dcap, mcap,
    Ctime, Cgrad, κ, a₀, _, _, _, _, _, _, hδ, hρ, hεcap, hDcap, hκ, _, hcl⟩ :=
    hcan B ε Λ hB hε hε' hεbar' hΛ
  refine ⟨δmax, ρmax, εcap, Dcap, mcap, κ, hδ, hρ, hεcap, hDcap, hκ, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδb hρb hΛp H A p records hhor hfamily
  have hclass : H.hasCanonicalCutoffRecords p₀ δbound ρbound :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mpr
      ⟨p, records, hfamily⟩
  rcases H.time_le_horizon.lt_or_eq with hlast | hlast
  · let J := H.prefixAt (Fin.last H.eventCount)
    let initial : InitialIdentification P₀ g₀ J.toHistory := A.ofStageZero rfl HEq.rfl
    have hJclass : J.hasCanonicalCutoffRecords p₀ δbound ρbound :=
      (J.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mpr
        ⟨p, H.prefixRecords (Fin.last H.eventCount) records,
          H.isCanonicalCutoffRecordFamily_prefixAt (Fin.last H.eventCount) hfamily⟩
    obtain ⟨_, _, _, _, _, _, hterminal⟩ :=
      hcl p₀ δbound ρbound hacc hD hm hδb hρb hΛp J initial rfl
        (H.time_le_horizon.trans_lt hhor) hJclass
    have useIncoming (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hs : s ≤ B)
        (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (hHs : H.horizon < s) : H.NoncollapsedBefore κ ε H.horizon := by
      obtain ⟨t₀, ht₀, ht₀s⟩ := exists_between hHs
      have hn := (hterminal s G hs hinit).2.2.2.2 t₀ ⟨hlast.trans ht₀, ht₀s⟩
      let S := G.closedPrefix H.horizon hlast hHs
      let L := H.extendHorizon H.horizon le_rfl S hinit
      have hncL : L.NoncollapsedBefore κ ε H.horizon := by
        exact hn H.horizon hlast hHs ht₀.le
      have hp : H.toHistory.IsPrefixOf L.toHistory :=
        actual_closed_extension_preserves_prefix H le_rfl S hinit
      have hsame : L.toHistory.SamePresentation H.toHistory :=
        L.toHistory.restrict_self.symm.trans hp.presentation
      exact (RetainedCoreHistory.noncollapsedBefore_iff_of_samePresentation_C11RO hsame).mp hncL
    obtain ⟨S, hS⟩ | ⟨s, G, hs, hG, hsing⟩ :=
      (H.stage (Fin.last H.eventCount)).exists_closedSlab_or_singular_incomingSlab_from_time
        (H.initialMetric (Fin.last H.eventCount)) (H.time_le_horizon.trans_lt hhor)
    · exact useIncoming B (S.restrictIncoming le_rfl S.lt le_rfl) le_rfl hS hhor
    · exact useIncoming s G hs hG (singular_time_gt_closed_end (H.finalSlab hlast) G
        (hG.trans (H.final_initial hlast).symm) hsing)
  · obtain ⟨_, _, _, _, _, hnc, _⟩ :=
      hcl p₀ δbound ρbound hacc hD hm hδb hρb hΛp H A hlast hhor hclass
    simpa only [hlast] using hnc

end GC.GeneralFlow

end
