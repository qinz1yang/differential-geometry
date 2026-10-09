import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem canonicalBefore_of_threshold_le {ε C1 C2 q q' τmin t₀ : ℝ} (hq : q ≤ q')
    (hG : G.CanonicalBefore ε C1 C2 q τmin t₀) : G.CanonicalBefore ε C1 C2 q' τmin t₀ :=
  fun y t ht hR hτ => hG y t ht (hq.trans_lt hR) hτ

theorem derivativeBoundBefore_of_threshold_le {Ctime : ℝ≥0} {q q' t₀ : ℝ} (hq : q ≤ q')
    (hG : G.DerivativeBoundBefore Ctime q t₀) : G.DerivativeBoundBefore Ctime q' t₀ :=
  fun y t ht hR => hG y t ht (hq.trans_lt hR)

theorem gradientBoundBefore_of_threshold_le {Cgrad : ℝ≥0} {q q' t₀ : ℝ} (hq : q ≤ q')
    (hG : G.GradientBoundBefore Cgrad q t₀) : G.GradientBoundBefore Cgrad q' t₀ :=
  fun y t ht hR => hG y t ht (hq.trans_lt hR)

theorem spatiallyCanonicalBefore_of_threshold_le {ε C1 C2 q q' t₀ : ℝ} (hq : q ≤ q')
    (hG : G.SpatiallyCanonicalBefore ε C1 C2 q t₀) : G.SpatiallyCanonicalBefore ε C1 C2 q' t₀ :=
  fun y t ht hR => hG y t ht (hq.trans_lt hR)

theorem derivativeBoundOn_mono {Ctime : ℝ≥0} {qcan t₀ η₁ η₂ : ℝ} (h : η₁ ≤ η₂)
    (hG : G.DerivativeBoundOn Ctime qcan t₀ η₂) : G.DerivativeBoundOn Ctime qcan t₀ η₁ :=
  fun y t hat ht₀ htη hts hR => hG y t hat ht₀ (htη.trans_le (by linarith)) hts hR

theorem gradientBoundOn_mono {Cgrad : ℝ≥0} {qcan t₀ η₁ η₂ : ℝ} (h : η₁ ≤ η₂)
    (hG : G.GradientBoundOn Cgrad qcan t₀ η₂) : G.GradientBoundOn Cgrad qcan t₀ η₁ :=
  fun y t hat ht₀ htη hts hR => hG y t hat ht₀ (htη.trans_le (by linarith)) hts hR

theorem canonicalOn_mono {ε C1 C2 qcan τmin t₀ η₁ η₂ : ℝ} (h : η₁ ≤ η₂)
    (hG : G.CanonicalOn ε C1 C2 qcan τmin t₀ η₂) : G.CanonicalOn ε C1 C2 qcan τmin t₀ η₁ :=
  fun y t hat ht₀ htη hts hR hτ => hG y t hat ht₀ (htη.trans_le (by linarith)) hts hR hτ

theorem spatiallyCanonicalOn_mono {ε C1 C2 qcan t₀ η₁ η₂ : ℝ} (h : η₁ ≤ η₂)
    (hG : G.SpatiallyCanonicalOn ε C1 C2 qcan t₀ η₂) :
    G.SpatiallyCanonicalOn ε C1 C2 qcan t₀ η₁ :=
  fun y t hat ht₀ htη hts hR => hG y t hat ht₀ (htη.trans_le (by linarith)) hts hR

theorem exists_boundsOn_spatiallyCanonicalOn {ε C1 C2 C1s C2s qcan qs τmin t₀ : ℝ}
    {Ctime Cgrad : ℝ≥0}
    (h₁ : ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧
      G.GradientBoundOn Cgrad qcan t₀ η ∧ G.CanonicalOn ε C1 C2 qcan τmin t₀ η)
    (h₂ : ∃ η : ℝ, 0 < η ∧ G.SpatiallyCanonicalOn ε C1s C2s qs t₀ η) :
    ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧ G.GradientBoundOn Cgrad qcan t₀ η ∧
      G.CanonicalOn ε C1 C2 qcan τmin t₀ η ∧ G.SpatiallyCanonicalOn ε C1s C2s qs t₀ η := by
  obtain ⟨η₁, hη₁, hd, hg, hc⟩ := h₁
  obtain ⟨η₂, hη₂, hs⟩ := h₂
  exact ⟨min η₁ η₂, lt_min hη₁ hη₂, G.derivativeBoundOn_mono (min_le_left _ _) hd,
    G.gradientBoundOn_mono (min_le_left _ _) hg, G.canonicalOn_mono (min_le_left _ _) hc,
    G.spatiallyCanonicalOn_mono (min_le_right _ _) hs⟩

theorem canonicalBefore_end_of_continuation_spatial {ε C1 C2 C1s C2s qcan qs τmin : ℝ}
    {Ctime Cgrad : ℝ≥0} (N : ℝ → Prop)
    (hN : ∀ t₀ ∈ Ioo a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ → N t₀)
    (hNa : N a)
    (hcont : ∀ t₀ ∈ Ico a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ →
      G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ → N t₀ →
      ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧ G.GradientBoundOn Cgrad qcan t₀ η ∧
        G.CanonicalOn ε C1 C2 qcan τmin t₀ η ∧ G.SpatiallyCanonicalOn ε C1s C2s qs t₀ η) :
    G.CanonicalBefore ε C1 C2 qcan τmin s ∧ G.DerivativeBoundBefore Ctime qcan s ∧
      G.GradientBoundBefore Cgrad qcan s ∧ G.SpatiallyCanonicalBefore ε C1s C2s qs s := by
  set A : Set ℝ := {τ | τ ∈ Icc a s ∧ G.CanonicalBefore ε C1 C2 qcan τmin τ ∧
    G.DerivativeBoundBefore Ctime qcan τ ∧ G.GradientBoundBefore Cgrad qcan τ ∧
    G.SpatiallyCanonicalBefore ε C1s C2s qs τ}
  have hmemA : a ∈ A :=
    ⟨⟨le_rfl, G.lt.le⟩, G.canonicalBefore_start ε C1 C2 qcan τmin,
      G.derivativeBoundBefore_start Ctime qcan, G.gradientBoundBefore_start Cgrad qcan,
      G.spatiallyCanonicalBefore_start ε C1s C2s qs⟩
  have hne : A.Nonempty := ⟨_, hmemA⟩
  have hbdd : BddAbove A := ⟨s, fun τ hτ => hτ.1.2⟩
  have hTa : a ≤ sSup A := le_csSup hbdd hmemA
  have hTs : sSup A ≤ s := csSup_le hne fun τ hτ => hτ.1.2
  have hcanT : G.CanonicalBefore ε C1 C2 qcan τmin (sSup A) := by
    intro y t ht hR hτ
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.1 y t ⟨ht.1, htτ⟩ hR hτ
  have hderT : G.DerivativeBoundBefore Ctime qcan (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.1 y t ⟨ht.1, htτ⟩ hR
  have hgradT : G.GradientBoundBefore Cgrad qcan (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.2.1 y t ⟨ht.1, htτ⟩ hR
  have hspatT : G.SpatiallyCanonicalBefore ε C1s C2s qs (sSup A) := by
    intro y t ht hR
    obtain ⟨τ, hτA, htτ⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hτA.2.2.2.2 y t ⟨ht.1, htτ⟩ hR
  rcases hTs.lt_or_eq with hlt | heq
  · exfalso
    have hNT : N (sSup A) := by
      rcases hTa.lt_or_eq with hlt' | heq'
      · exact hN (sSup A) ⟨hlt', hlt⟩ hcanT hderT hgradT hspatT
      · rw [← heq']
        exact hNa
    obtain ⟨η, hη, hder, hgrad, hcan, hspat⟩ :=
      hcont (sSup A) ⟨hTa, hlt⟩ hcanT hderT hgradT hspatT hNT
    have hmem : min (sSup A + η) s ∈ A := by
      refine ⟨⟨le_min (by linarith) G.lt.le, min_le_right _ _⟩, ?_, ?_, ?_, ?_⟩
      · intro y t ht hR hτ
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hcanT y t ⟨ht.1, htT⟩ hR hτ
        · exact hcan y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR hτ
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hderT y t ⟨ht.1, htT⟩ hR
        · exact hder y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hgradT y t ⟨ht.1, htT⟩ hR
        · exact hgrad y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
      · intro y t ht hR
        rcases lt_or_ge t (sSup A) with htT | hTt
        · exact hspatT y t ⟨ht.1, htT⟩ hR
        · exact hspat y t ht.1 hTt (lt_of_lt_of_le ht.2 (min_le_left _ _))
            (lt_of_lt_of_le ht.2 (min_le_right _ _)) hR
    have hle : min (sSup A + η) s ≤ sSup A := le_csSup hbdd hmem
    have hgt : sSup A < min (sSup A + η) s := lt_min (by linarith) hlt
    exact absurd hle (not_le.mpr hgt)
  · rw [heq] at hcanT hderT hgradT hspatT
    exact ⟨hcanT, hderT, hgradT, hspatT⟩

end OrientedThreeStage.IncomingSlab

def SpatialCanonicalContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∃ C1s C2s Cs : ℝ, 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧
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
          ∃ η : ℝ, 0 < η ∧ G.SpatiallyCanonicalOn ε C1s C2s qs t₀ η

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
