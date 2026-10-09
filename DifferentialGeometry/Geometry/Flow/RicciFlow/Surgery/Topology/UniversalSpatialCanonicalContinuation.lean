import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformSpatialCrossingContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowSpatialCanonicalWitness

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The spatial canonical constants precede both the initial metric and horizon.
The finite packet is selected later and one actual record family is used in all branches. -/
theorem exists_universal_spatialCanonicalContinuation :
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∃ C1s C2s Cs : ℝ, 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
  ∀ B : ℝ, 0 < B →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∃ q₄ : ℝ, 0 < q₄ ∧
  ∀ qcan : ℝ, q₄ ≤ qcan →
  ∃ (qs δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    qcan ≤ qs ∧ qs ≤ Cs * qcan ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound),
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          (∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η ∧
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η ∧
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η) →
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.SpatiallyCanonicalOn ε C1s C2s qs t₀ η) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          (∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧
            G.GradientBoundOn Cgrad qcan t₀ η ∧ G.CanonicalOn ε C1 C2 qcan τmin t₀ η) →
          ∃ η : ℝ, 0 < η ∧ G.SpatiallyCanonicalOn ε C1s C2s qs t₀ η := by
  obtain ⟨εbar, hεbar, -, hX⟩ := exists_uniform_spatialCrossingContinuation.{u}
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε hε' hεb C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
  obtain ⟨Cx, -, hX⟩ := hX ε hε hε' hεb
  obtain ⟨Cw, -, hM5⟩ :=
    RetainedCoreHistory.exists_uniform_capWindowPoint_spatialCanonicalWitness.{u} hε hε'
  have hA1 : C1 ≤ max C1 (max Cw Cx) := le_max_left _ _
  have hA2 : C2 ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) := le_max_left _ _
  have hB1 : Cw ≤ max C1 (max Cw Cx) := (le_max_left _ _).trans (le_max_right _ _)
  have hB2 : max Cw (Cgrad : ℝ) ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX1 : Cx ≤ max C1 (max Cw Cx) := (le_max_right _ _).trans (le_max_right _ _)
  have hX2 : Cx ≤ max C2 (max (max Cw (Cgrad : ℝ)) Cx) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C1 (max Cw Cx), max C2 (max (max Cw (Cgrad : ℝ)) Cx), 1, hC1.trans hA1,
    hC2.trans hA2, le_rfl, ?_⟩
  intro P₀ g₀ B hB κ phi hκ hphi
  have hX := hX P₀ g₀
  have hM5 := hM5 P₀ g₀
  obtain ⟨Dx, θcap, qx, mx, hDx, hθcap, hqx, hXq⟩ :=
    hX B hB C1 C2 τmin Ctime Cgrad hC1 hC2 hτ _ _ 1 (hC1.trans hA1) (hC2.trans hA2) le_rfl
      κ phi τmin hκ hphi hτ
  obtain ⟨Rcap, mw, hRcap, hM5q⟩ := hM5 Ctime Cgrad Dx θcap hDx hθcap
  refine ⟨qx, hqx, fun qcan hqcan => ?_⟩
  obtain ⟨δx, ρx, εx, hδx, hρx, hεx, hXs⟩ := hXq qcan hqcan
  obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hM5s⟩ := hM5q qcan (hqx.trans_le hqcan)
  refine ⟨qcan, min δx δw, min ρx ρw, min εx εw, max Dx Rcap, max mx mw, le_rfl,
    (one_mul qcan).ge, lt_min hδx hδw, lt_min hρx hρw, lt_min hεx hεw, lt_max_of_lt_left hDx, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ H hH hpinch
  obtain ⟨p, records, hrec⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hH.2.2.2.1
  have hXH := hXs qcan le_rfl (one_mul qcan).ge p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hD) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH p records hrec hpinch
  have hW := hM5s p₀ δbound ρbound (hacc.trans (min_le_right _ _)) ((le_max_right _ _).trans hD)
    ((le_max_right _ _).trans hm) (hδ.trans (min_le_right _ _)) (hρ.trans (min_le_right _ _))
    H hH.1 hH.2.2.2.2 p records hrec
  refine ⟨fun j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hC3 => ?_,
    fun s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn hC3 => ?_⟩
  · obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
    obtain ⟨η, hη, hηη₃, -, hYoung⟩ :=
      hXH.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn η₃ hη₃ hdOn hgOn hcOn
    refine ⟨η, hη, fun y t hat ht₀' htη hts hR => ?_⟩
    have htη₃ : t < t₀ + η₃ := htη.trans_le (by linarith)
    rcases le_or_gt τmin
        ((H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc)) with
      hold | hyoung
    · exact (H.toHistory.event j).incoming.exists_spatialCanonicalWitness_of_canonicalOn hA1 hA2
        le_rfl hcOn hat ht₀' htη₃ hts hR hold
    by_cases hcw : H.CapWindowPoint records j.castSucc y t Dx θcap
    · obtain ⟨W, hW'⟩ := hW j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
        (H.event_initial j) hderP t hat hts
        ((H.toHistory.event j).incoming.derivativeBoundBefore_of_derivativeBoundOn hd hdOn
          htη₃.le hts.le) y hcw hR (hgOn y t hat ht₀' htη₃ hts hR)
      exact ⟨W.enlargeConstants hB1 hB2, hW'.enlarge_constants hB1 hB2⟩
    · obtain ⟨W, hW'⟩ := hYoung y t hat ht₀' htη hts hR hyoung hcw
      exact ⟨W.enlargeConstants hX1 hX2, hW'.enlarge_constants hX1 hX2⟩
  · obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
    obtain ⟨η, hη, hηη₃, -, hYoung⟩ :=
      hXH.2 s G hG hpinchG hcanL hderL hgradL hspatL hncL t₀ ht₀ hc hd hg hsp hn η₃ hη₃ hdOn hgOn
        hcOn
    refine ⟨η, hη, fun y t hat ht₀' htη hts hR => ?_⟩
    have htη₃ : t < t₀ + η₃ := htη.trans_le (by linarith)
    rcases le_or_gt τmin (G.flow.scalar t y * (t - H.time (Fin.last H.eventCount))) with
      hold | hyoung
    · exact G.exists_spatialCanonicalWitness_of_canonicalOn hA1 hA2 le_rfl hcOn hat ht₀' htη₃ hts
        hR hold
    by_cases hcw : H.CapWindowPoint records (Fin.last H.eventCount) y t Dx θcap
    · obtain ⟨W, hW'⟩ := hW (Fin.last H.eventCount) s G hG.2 hderL t hat hts
        (G.derivativeBoundBefore_of_derivativeBoundOn hd hdOn htη₃.le hts.le) y hcw hR
        (hgOn y t hat ht₀' htη₃ hts hR)
      exact ⟨W.enlargeConstants hB1 hB2, hW'.enlarge_constants hB1 hB2⟩
    · obtain ⟨W, hW'⟩ := hYoung y t hat ht₀' htη hts hR hyoung hcw
      exact ⟨W.enlargeConstants hX1 hX2, hW'.enlarge_constants hX1 hX2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
