import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalSpatialCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinalSlabNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Pinching.ThroughSurgery

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open scoped Manifold NNReal

namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- Choose a sufficient finite analytic packet before any actual history or
record family. The same supplied history's noncollapse pays the finite-event
and actual final-open-interval continuation arguments. -/
theorem exists_uniform_observation_estimate_packet :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ (C1 C2 C1s C2s Cs τmin : ℝ) (Ctime Cgrad : ℝ≥0),
      1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧ 0 < τmin ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
    ∃ (qcan qs δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (K : RetainedCoreHistory.{u}) (I : InitialIdentification P g K.toHistory)
      (p : CutoffParameters)
      (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
      K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      K.NoncollapsedBefore κ ε K.horizon →
      (∀ j : Fin K.eventCount,
        (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan (K.time j.succ) ∧
        (K.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (K.time j.succ) ∧
        (K.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (K.time j.succ) ∧
        (K.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs (K.time j.succ)) ∧
      ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
        let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
        G.DerivativeBoundBefore Ctime qcan K.horizon ∧
        G.GradientBoundBefore Cgrad qcan K.horizon ∧
        G.CanonicalBefore ε C1 C2 qcan τmin K.horizon ∧
        G.SpatiallyCanonicalBefore ε C1s C2s qs K.horizon := by
  obtain ⟨εt, hεt, hT⟩ := exists_universal_canonicalNeighborhoodContinuation.{u}
  obtain ⟨εs, hεs, hS⟩ := exists_universal_spatialCanonicalContinuation.{u}
  refine ⟨min εt εs, lt_min hεt hεs, ?_⟩
  intro ε hε hε11 hεbar
  obtain ⟨C1, C2, τmin, Ctime, Cgrad, hC1, hC2, hτ, hT⟩ :=
    hT ε hε hε11 (hεbar.trans (min_le_left _ _))
  obtain ⟨C1s, C2s, Cs, hC1s, hC2s, hCs, hS⟩ :=
    hS ε hε hε11 (hεbar.trans (min_le_right _ _)) C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  refine ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτ, ?_⟩
  intro P g B κ hB hκ
  have hB1 : 0 < B + 1 := by linarith
  obtain ⟨phi, δP, ρP, εP, hphi, hδP, hρP, hεP, hP⟩ :=
    pinchingThroughSurgery P g (B + 1) hB1
  obtain ⟨q₄, _, hS⟩ := hS P g (B + 1) hB1 κ phi hκ hphi
  obtain ⟨qcan, δt, ρt, εt, Dt, mt, hq₄, hqcan, hδt, hρt, hεt, hDt, hT⟩ :=
    hT P g (B + 1) hB1 C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi q₄
  obtain ⟨qs, δs, ρs, εs, Ds, ms, hqs, hqsC, hδs, hρs, hεs, _, hS⟩ := hS qcan hq₄
  refine ⟨qcan, qs, min δP (min δt δs), min ρP (min ρt ρs),
    min εP (min εt εs), max Dt Ds, max mt ms,
    hqcan, hqs, hqsC, lt_min hδP (lt_min hδt hδs),
    lt_min hρP (lt_min hρt hρs), lt_min hεP (lt_min hεt hεs),
    lt_max_of_lt_left hDt, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδ hρ hrec K I p records hKB hfamily hnc
  simp only [le_min_iff, max_le_iff] at hacc hrad hord hδ hρ
  let J := K.prefixAt (Fin.last K.eventCount)
  have hfamilyJ : J.IsCanonicalCutoffRecordFamily p₀ δbound ρbound
      (K.prefixRecords (Fin.last K.eventCount) records) :=
    K.isCanonicalCutoffRecordFamily_prefixAt (Fin.last K.eventCount) hfamily
  have hInv : J.hasCanonicalCutoffRecords p₀ δbound ρbound :=
    (J.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
      p₀ δbound ρbound).mpr ⟨p, K.prefixRecords (Fin.last K.eventCount) records, hfamilyJ⟩
  have hJhor : J.horizon < B + 1 :=
    lt_of_le_of_lt (K.time_le_horizon.trans hKB) (by linarith)
  have hJ : J.InCutoffClass (P₀ := P) g (B + 1) p₀ δbound ρbound :=
    ⟨⟨I.ofStageZero rfl HEq.rfl⟩, rfl, hJhor, hInv, hrec⟩
  have hncJ : J.NoncollapsedBefore κ ε J.horizon :=
    K.noncollapsedBefore_prefixAt (Fin.last K.eventCount) hnc K.time_le_horizon
  have hncBefore (t : ℝ) (ht : t ≤ J.horizon) : J.NoncollapsedBefore κ ε t :=
    J.noncollapsedBefore_mono ht hncJ
  have hP' := hP p₀ δbound ρbound hacc.1 hδ.1 hρ.1 J hJ
  have hpinched : J.EventSlabsPinched phi :=
    fun j => hP' j.castSucc (J.time j.succ) (J.toHistory.event j).incoming
      (J.isContinuationSlab_event hJhor j)
  have hF := hT qs hqs hqsC p₀ δbound ρbound hacc.2.1 hrad.1 hord.1
    hδ.2.1 hρ.2.1 J hJ hpinched
  have hSp := hS p₀ δbound ρbound hacc.2.2 hrad.2 hord.2
    hδ.2.2 hρ.2.2 J hJ hpinched
  have hstage : ∀ k : Fin (J.eventCount + 1),
      J.EventSlabsCanonical ε C1 C2 qcan τmin k ∧ J.EventSlabsDerivative Ctime qcan k ∧
        J.EventSlabsGradient Cgrad qcan k ∧ J.EventSlabsSpatiallyCanonical ε C1s C2s qs k := by
    intro k
    induction k using Fin.induction with
    | zero =>
      exact ⟨fun j hj => (Fin.not_lt_zero _ hj).elim,
        fun j hj => (Fin.not_lt_zero _ hj).elim,
        fun j hj => (Fin.not_lt_zero _ hj).elim,
        fun j hj => (Fin.not_lt_zero _ hj).elim⟩
    | succ j ih =>
      obtain ⟨hcanP, hderP, hgradP, hspatP⟩ := ih
      have hcl := (J.toHistory.event j).incoming.canonicalBefore_end_of_continuation_spatial
        (fun t₀ => J.NoncollapsedBefore κ ε t₀)
        (fun t₀ ht₀ _ _ _ _ =>
          hncBefore t₀ (ht₀.2.le.trans (J.toHistory.time_le_horizon_at j.succ)))
        (hncBefore (J.time j.castSucc) (J.toHistory.time_le_horizon_at j.castSucc))
        (fun t₀ ht₀ hc hd hg hs hn =>
          have hF₀ := hF.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn
          (J.toHistory.event j).incoming.exists_boundsOn_spatiallyCanonicalOn hF₀
            (hSp.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hF₀))
      refine ⟨?_, ?_, ?_, ?_⟩
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
  obtain ⟨hcanL, hderL, hgradL, hspatL⟩ := hstage (Fin.last J.eventCount)
  refine ⟨?_, ?_⟩
  · intro j
    exact ⟨hderL j (Fin.castSucc_lt_last j), hgradL j (Fin.castSucc_lt_last j),
      hcanL j (Fin.castSucc_lt_last j), hspatL j (Fin.castSucc_lt_last j)⟩
  · intro hfinal
    let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
    change G.DerivativeBoundBefore Ctime qcan K.horizon ∧
      G.GradientBoundBefore Cgrad qcan K.horizon ∧
      G.CanonicalBefore ε C1 C2 qcan τmin K.horizon ∧
      G.SpatiallyCanonicalBefore ε C1s C2s qs K.horizon
    have hG : J.IsContinuationSlab (B + 1) (Fin.last J.eventCount) G :=
      ⟨by linarith, K.final_initial hfinal⟩
    have hpinchedG := hP' (Fin.last J.eventCount) K.horizon G hG
    have hncFinal : J.TerminalNoncollapsedBefore rfl G hG.2 κ ε K.horizon :=
      K.terminalNoncollapsedBefore_finalSlab hfinal hnc
    have hncTerminal (t : ℝ) (ht : t ≤ K.horizon) :
        J.TerminalNoncollapsedBefore rfl G hG.2 κ ε t :=
      fun T hT hTs hTt => hncFinal T hT hTs (hTt.trans ht)
    have hcl := G.canonicalBefore_end_of_continuation_spatial
      (fun t₀ => J.TerminalNoncollapsedBefore rfl G hG.2 κ ε t₀)
      (fun t₀ ht₀ _ _ _ _ => hncTerminal t₀ ht₀.2.le)
      (hncTerminal (J.time (Fin.last J.eventCount)) K.time_le_horizon)
      (fun t₀ ht₀ hc hd hg hs hn =>
        have hF₀ := hF.2 K.horizon G hG hpinchedG hcanL hderL hgradL hspatL
          hncJ t₀ ht₀ hc hd hg hs hn
        G.exists_boundsOn_spatiallyCanonicalOn hF₀
          (hSp.2 K.horizon G hG hpinchedG hcanL hderL hgradL hspatL
            hncJ t₀ ht₀ hc hd hg hs hn hF₀))
    exact ⟨hcl.2.1, hcl.2.2.1, hcl.1, hcl.2.2.2⟩

end GC.GeneralFlow
