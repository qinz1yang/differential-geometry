import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.ExtinctionCriterion

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

def CanonicalBefore (ε C1 C2 qcan τmin t₀ : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a t₀ → qcan < G.flow.scalar t y →
    τmin ≤ G.flow.scalar t y * (t - a) →
    ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε

def DerivativeBoundBefore (Ctime : ℝ≥0) (qcan t₀ : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a t₀ → qcan < G.flow.scalar t y →
    |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2

def GradientBoundBefore (Cgrad : ℝ≥0) (qcan t₀ : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a t₀ → qcan < G.flow.scalar t y →
    ∀ v : TangentSpace I3 y, |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
      Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
        Real.sqrt ((G.flow.base.metric t).inner y v v)

def SpatiallyCanonicalBefore (ε C1 C2 qcan t₀ : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), t ∈ Ioo a t₀ → qcan < G.flow.scalar t y →
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε

def CanonicalOn (ε C1 C2 qcan τmin t₀ η : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    τmin ≤ G.flow.scalar t y * (t - a) →
    ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε

def DerivativeBoundOn (Ctime : ℝ≥0) (qcan t₀ η : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2

def GradientBoundOn (Cgrad : ℝ≥0) (qcan t₀ η : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    ∀ v : TangentSpace I3 y, |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
      Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
        Real.sqrt ((G.flow.base.metric t).inner y v v)

def SpatiallyCanonicalOn (ε C1 C2 qcan t₀ η : ℝ) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε

theorem canonicalBefore_mono {ε C1 C2 qcan τmin t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hG : G.CanonicalBefore ε C1 C2 qcan τmin t₁) : G.CanonicalBefore ε C1 C2 qcan τmin t₀ :=
  fun y t ht hR hτ => hG y t ⟨ht.1, ht.2.trans_le h⟩ hR hτ

theorem derivativeBoundBefore_mono {Ctime : ℝ≥0} {qcan t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hG : G.DerivativeBoundBefore Ctime qcan t₁) : G.DerivativeBoundBefore Ctime qcan t₀ :=
  fun y t ht hR => hG y t ⟨ht.1, ht.2.trans_le h⟩ hR

theorem gradientBoundBefore_mono {Cgrad : ℝ≥0} {qcan t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hG : G.GradientBoundBefore Cgrad qcan t₁) : G.GradientBoundBefore Cgrad qcan t₀ :=
  fun y t ht hR => hG y t ⟨ht.1, ht.2.trans_le h⟩ hR

theorem spatiallyCanonicalBefore_mono {ε C1 C2 qcan t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hG : G.SpatiallyCanonicalBefore ε C1 C2 qcan t₁) :
    G.SpatiallyCanonicalBefore ε C1 C2 qcan t₀ :=
  fun y t ht hR => hG y t ⟨ht.1, ht.2.trans_le h⟩ hR

theorem canonicalBefore_start (ε C1 C2 qcan τmin : ℝ) :
    G.CanonicalBefore ε C1 C2 qcan τmin a :=
  fun _ _ ht _ _ => absurd ht.1 (not_lt.mpr ht.2.le)

theorem derivativeBoundBefore_start (Ctime : ℝ≥0) (qcan : ℝ) :
    G.DerivativeBoundBefore Ctime qcan a :=
  fun _ _ ht _ => absurd ht.1 (not_lt.mpr ht.2.le)

theorem gradientBoundBefore_start (Cgrad : ℝ≥0) (qcan : ℝ) :
    G.GradientBoundBefore Cgrad qcan a :=
  fun _ _ ht _ => absurd ht.1 (not_lt.mpr ht.2.le)

theorem spatiallyCanonicalBefore_start (ε C1 C2 qcan : ℝ) :
    G.SpatiallyCanonicalBefore ε C1 C2 qcan a :=
  fun _ _ ht _ => absurd ht.1 (not_lt.mpr ht.2.le)

theorem canonicalBefore_end_of_continuation {ε C1 C2 qcan τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (N : ℝ → Prop)
    (hN : ∀ t₀ ∈ Ioo a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ → N t₀)
    (hNa : N a)
    (hcont : ∀ t₀ ∈ Ico a s, G.CanonicalBefore ε C1 C2 qcan τmin t₀ →
      G.DerivativeBoundBefore Ctime qcan t₀ → G.GradientBoundBefore Cgrad qcan t₀ → N t₀ →
      ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧ G.GradientBoundOn Cgrad qcan t₀ η ∧
        G.CanonicalOn ε C1 C2 qcan τmin t₀ η) :
    G.CanonicalBefore ε C1 C2 qcan τmin s ∧ G.DerivativeBoundBefore Ctime qcan s ∧
      G.GradientBoundBefore Cgrad qcan s := by
  set A : Set ℝ := {τ | τ ∈ Icc a s ∧ G.CanonicalBefore ε C1 C2 qcan τmin τ ∧
    G.DerivativeBoundBefore Ctime qcan τ ∧ G.GradientBoundBefore Cgrad qcan τ}
  have hmemA : a ∈ A :=
    ⟨⟨le_rfl, G.lt.le⟩, G.canonicalBefore_start ε C1 C2 qcan τmin,
      G.derivativeBoundBefore_start Ctime qcan, G.gradientBoundBefore_start Cgrad qcan⟩
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
    exact hτA.2.2.2 y t ⟨ht.1, htτ⟩ hR
  rcases hTs.lt_or_eq with hlt | heq
  · exfalso
    have hNT : N (sSup A) := by
      rcases hTa.lt_or_eq with hlt' | heq'
      · exact hN (sSup A) ⟨hlt', hlt⟩ hcanT hderT hgradT
      · rw [← heq']
        exact hNa
    obtain ⟨η, hη, hder, hgrad, hcan⟩ := hcont (sSup A) ⟨hTa, hlt⟩ hcanT hderT hgradT hNT
    have hmem : min (sSup A + η) s ∈ A := by
      refine ⟨⟨le_min (by linarith) G.lt.le, min_le_right _ _⟩, ?_, ?_, ?_⟩
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
    have hle : min (sSup A + η) s ≤ sSup A := le_csSup hbdd hmem
    have hgt : sSup A < min (sSup A + η) s := lt_min (by linarith) hlt
    exact absurd hle (not_le.mpr hgt)
  · rw [heq] at hcanT hderT hgradT
    exact ⟨hcanT, hderT, hgradT⟩

end OrientedThreeStage.IncomingSlab

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u})

def InCutoffClass (g₀ : P₀.Metric) (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ) : Prop :=
  Nonempty (InitialIdentification P₀ g₀ H.toHistory) ∧
    H.time (Fin.last H.eventCount) = H.horizon ∧ H.horizon < B ∧
    H.hasCanonicalCutoffRecords p₀ δbound ρbound ∧ p₀.recenterConstant * δbound ≤ 1 / 2

def IsContinuationSlab (B : ℝ) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) : Prop :=
  s ≤ B ∧ G.flow.base.metric (H.time k) = H.initialMetric k

def NoncollapsedBefore (κ ρ t₀ : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
    (t : ℝ) ≤ t₀ → r ≤ ρ → H.toHistory.isParabolicallyRmControlledBall t p r →
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)

theorem noncollapsedBefore_mono {κ ρ t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    (hH : H.NoncollapsedBefore κ ρ t₁) : H.NoncollapsedBefore κ ρ t₀ :=
  fun t p r ht hr hball => hH t p r (ht.trans h) hr hball

theorem noncollapsedBefore_zero (κ ρ : ℝ) : H.NoncollapsedBefore κ ρ 0 := by
  intro t p r ht _ hball
  exfalso
  have hr := hball.1
  have hsq := hball.radius_sq_le_time
  have h0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
  have ht0 : (t : ℝ) = 0 := le_antisymm ht h0
  rw [ht0] at hsq
  exact absurd hsq (not_le.mpr (pow_pos hr 2))

def TerminalNoncollapsedBefore (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (κ ρ t₀ : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t₀ →
    (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).NoncollapsedBefore κ ρ T

theorem terminalNoncollapsedBefore_start (hend : H.time (Fin.last H.eventCount) = H.horizon)
    {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (κ ρ : ℝ) :
    H.TerminalNoncollapsedBefore hend G hG κ ρ (H.time (Fin.last H.eventCount)) :=
  fun _ hT _ hTle => absurd (hT.trans_le hTle) (lt_irrefl _)

def EventSlabsPinched (phi : ℝ → ℝ) : Prop :=
  ∀ j : Fin H.eventCount,
    Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi

def EventSlabsCanonical (ε C1 C2 qcan τmin : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (H.time j.succ)

def EventSlabsDerivative (Ctime : ℝ≥0) (qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan (H.time j.succ)

def EventSlabsGradient (Cgrad : ℝ≥0) (qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)

def EventSlabsSpatiallyCanonical (ε C1 C2 qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1 C2 qcan (H.time j.succ)

theorem isContinuationSlab_event {B : ℝ} (hB : H.horizon < B) (j : Fin H.eventCount) :
    H.IsContinuationSlab B j.castSucc (H.toHistory.event j).incoming :=
  ⟨((H.time_strictMono.monotone (Fin.le_last _)).trans H.time_le_horizon).trans hB.le,
    H.event_initial j⟩

end RetainedCoreHistory

def PinchingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ B : ℝ, 0 < B →
  ∃ (phi : ℝ → ℝ) (δmax ρmax εcap : ℝ),
    Perelman.AdmissiblePinchingFunction phi ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (G : (H.stage k).IncomingSlab (H.time k) s),
      H.IsContinuationSlab B k G →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time k) s) phi

def NoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε C1 C2 C1s C2s τmin : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ),
    0 < B → 0 < ε → ε < 1 / 11 → 1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < τmin →
    Perelman.AdmissiblePinchingFunction phi →
  ∃ κ : ℝ, 0 < κ ∧
  ∀ qcan qs : ℝ, 0 < qcan → qcan ≤ qs →
  ∃ (δmax ρmax εcap Dcap : ℝ) (mcap : ℕ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
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
        ∀ t₀ : ℝ, t₀ ∈ Ioc (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        ∀ t₀ : ℝ, t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ → G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀

def CanonicalNeighborhoodContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < τmin ∧
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∀ qfloor : ℝ,
  ∃ (qcan δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    qfloor ≤ qcan ∧ 0 < qcan ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
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
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η ∧
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η ∧
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η) ∧
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
          G.GradientBoundBefore Cgrad qcan t₀ → G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.DerivativeBoundOn Ctime qcan t₀ η ∧
            G.GradientBoundOn Cgrad qcan t₀ η ∧ G.CanonicalOn ε C1 C2 qcan τmin t₀ η

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
