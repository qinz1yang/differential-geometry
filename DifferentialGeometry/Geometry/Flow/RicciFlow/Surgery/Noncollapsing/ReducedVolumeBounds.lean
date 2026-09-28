import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

namespace ObservedHistory

variable (H : ObservedHistory.{u})

def regularMinimizerEndpoints (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) : Set (H.stage first).Carrier :=
  {q | ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
    (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
    α ⟨last, hle, le_rfl⟩ 0 = p ∧ α ⟨first, le_rfl, hle⟩ v = q ∧
    (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))) ∧
    H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v p q}

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

def reducedVolume (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) (T v : ℝ) : ℝ≥0∞ :=
  let first := H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))
  if hle : first ≤ k then
    Filter.limsup (fun B : ℝ =>
      ∫⁻ q in H.toHistory.regularMinimizerEndpoints first k hle T B v p,
        H.toHistory.regularizedDensity first k hle T B v p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.toHistory.stageMetric first (T - v ^ 2))) Filter.atTop
  else 0

def NoncollapsedAboveBefore (κ r₀ ρ t₀ : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
    (t : ℝ) ≤ t₀ → r₀ ≤ r → r ≤ ρ → H.toHistory.isParabolicallyRmControlledBall t p r →
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)

def ReducedVolumeBoundedBelowBefore (c r₀ ρ t₀ : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
    (t : ℝ) ≤ t₀ → r₀ ≤ r → r ≤ ρ → H.toHistory.isParabolicallyRmControlledBall t p r →
    ENNReal.ofReal c ≤ H.reducedVolume (H.toHistory.activeStage t) p t (Real.sqrt t)

def TerminalNoncollapsedAboveBefore (hend : H.time (Fin.last H.eventCount) = H.horizon)
    {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (κ r₀ ρ t₀ : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t₀ →
    (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).NoncollapsedAboveBefore
      κ r₀ ρ T

def TerminalReducedVolumeBoundedBelowBefore
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (c r₀ ρ t₀ : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t₀ →
    (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).ReducedVolumeBoundedBelowBefore
      c r₀ ρ T

theorem noncollapsedBefore_min_of_noncollapsedAboveBefore {κ₁ κ₂ r₀ ρ t₀ : ℝ}
    (habove : H.NoncollapsedAboveBefore κ₁ r₀ ρ t₀) (hbelow : H.NoncollapsedBefore κ₂ r₀ t₀) :
    H.NoncollapsedBefore (min κ₁ κ₂) ρ t₀ := by
  intro t p r ht hr hball
  rcases le_or_gt r r₀ with hsmall | hlarge
  · exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_right κ₁ κ₂)) _).trans
      (hbelow t p r ht hsmall hball)
  · exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left κ₁ κ₂)) _).trans
      (habove t p r ht hlarge.le hr hball)

end RetainedCoreHistory

def HistoryReducedVolumeMonotone : Prop :=
  ∀ (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier)
    (T v₁ v₂ : ℝ), T ∈ H.toHistory.stageDomain k → 0 < v₁ → v₁ ≤ v₂ → v₂ ^ 2 ≤ T →
    H.reducedVolume k p T v₂ ≤ H.reducedVolume k p T v₁

def HistoryReducedVolumeLocalUpperBound : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧
    ∀ (H : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) H.toHistory.horizon)
      (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
      H.toHistory.isParabolicallyRmControlledBall t p r →
      H.reducedVolume (H.toHistory.activeStage t) p t (σ * r) ≤
        ENNReal.ofReal (C₀ / (σ * r) ^ 3) *
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) +
        ENNReal.ofReal η

def HistoryReducedVolumeInitialLowerBound (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∀ (B ε C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ),
    0 < B → 0 < ε → ε < 1 / 11 → 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
    Perelman.AdmissiblePinchingFunction phi →
  ∃ c : ℝ, 0 < c ∧
  ∀ qcan r₀ : ℝ, 0 < qcan → 0 < r₀ →
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
        ∀ t₀ : ℝ, t₀ ∈ Ioc (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          H.ReducedVolumeBoundedBelowBefore c r₀ ε t₀) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        ∀ t₀ : ℝ, t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          H.TerminalReducedVolumeBoundedBelowBefore hH.2.1 G hG.2 c r₀ ε t₀

def SmallScaleNoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∀ (B ε C1 C2 C1s C2s τmin : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ) (κ₁ : ℝ),
    0 < B → 0 < ε → ε < 1 / 11 → 1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < τmin →
    Perelman.AdmissiblePinchingFunction phi → 0 < κ₁ →
  ∃ κ : ℝ, 0 < κ ∧
  ∀ qcan qs : ℝ, 0 < qcan → qcan ≤ qs →
  ∃ (r₀ δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    0 < r₀ ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
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
          H.NoncollapsedAboveBefore κ₁ r₀ ε t₀ →
          H.NoncollapsedBefore κ r₀ t₀) ∧
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
          H.TerminalNoncollapsedAboveBefore hH.2.1 G hG.2 κ₁ r₀ ε t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ r₀ t₀

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem noncollapsedAboveBefore_of_reducedVolume_bounds {c C₀ σ r₀ ρ t₀ : ℝ}
    (hc : 0 < c) (hC₀ : 0 < C₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hmono : HistoryReducedVolumeMonotone.{u})
    (hupper : ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier)
      (r : ℝ), H.toHistory.isParabolicallyRmControlledBall t p r →
      H.reducedVolume (H.toHistory.activeStage t) p t (σ * r) ≤
        ENNReal.ofReal (C₀ / (σ * r) ^ 3) *
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) +
        ENNReal.ofReal (c / 2))
    (hlower : H.ReducedVolumeBoundedBelowBefore c r₀ ρ t₀) :
    H.NoncollapsedAboveBefore (c * σ ^ 3 / (2 * C₀)) r₀ ρ t₀ := by
  intro t p r ht hr₀ hr hball
  have hrpos : 0 < r := hball.1
  have hrt : r ^ 2 ≤ (t : ℝ) := hball.radius_sq_le_time
  have hsr : σ * r ≤ Real.sqrt t :=
    (mul_le_of_le_one_left hrpos.le hσ1).trans ((le_abs_self r).trans (Real.abs_le_sqrt hrt))
  have hmon := hmono H (H.toHistory.activeStage t) p t (σ * r) (Real.sqrt t)
    (H.toHistory.activeStage_mem t) (mul_pos hσ hrpos) hsr (Real.sq_sqrt t.property.1).le
  have hchain := ((hlower t p r ht hr₀ hr hball).trans hmon).trans (hupper t p r hball)
  set V := riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
    (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)
  have hsplit : ENNReal.ofReal c = ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) := by
    rw [← ENNReal.ofReal_add (half_pos hc).le (half_pos hc).le]
    congr 1
    ring
  rw [hsplit] at hchain
  have hhalf : ENNReal.ofReal (c / 2) ≤ ENNReal.ofReal (C₀ / (σ * r) ^ 3) * V :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have hC₀ne : C₀ ≠ 0 := hC₀.ne'
  have hsr3 : 0 < (σ * r) ^ 3 := pow_pos (mul_pos hσ hrpos) 3
  have hsr3ne : (σ * r) ^ 3 ≠ 0 := hsr3.ne'
  have hκ : 0 ≤ c * σ ^ 3 / (2 * C₀) := by positivity
  have hreal : c * σ ^ 3 / (2 * C₀) * r ^ 3 = c / 2 * ((σ * r) ^ 3 / C₀) := by
    field_simp
  have hone : C₀ / (σ * r) ^ 3 * ((σ * r) ^ 3 / C₀) = 1 := by
    field_simp
  calc ENNReal.ofReal (c * σ ^ 3 / (2 * C₀)) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal (c / 2) * ENNReal.ofReal ((σ * r) ^ 3 / C₀) := by
        rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul hκ, hreal,
          ENNReal.ofReal_mul (half_pos hc).le]
    _ ≤ ENNReal.ofReal (C₀ / (σ * r) ^ 3) * V * ENNReal.ofReal ((σ * r) ^ 3 / C₀) :=
        mul_le_mul_left hhalf _
    _ = V := by
        rw [mul_comm (ENNReal.ofReal (C₀ / (σ * r) ^ 3)) V, mul_assoc,
          ← ENNReal.ofReal_mul (div_pos hC₀ hsr3).le, hone, ENNReal.ofReal_one, mul_one]

end RetainedCoreHistory

theorem noncollapsingThroughSurgery_of_reducedVolume_of_smallScale
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hmono : HistoryReducedVolumeMonotone.{u})
    (hupper : HistoryReducedVolumeLocalUpperBound.{u})
    (hlower : HistoryReducedVolumeInitialLowerBound P₀ g₀)
    (hsmall : SmallScaleNoncollapsingThroughSurgery P₀ g₀) :
    NoncollapsingThroughSurgery P₀ g₀ := by
  intro B ε C1 C2 C1s C2s τmin Ctime Cgrad phi hB hε hε' hC1 hC2 hC1s hC2s hτ hphi
  obtain ⟨C₀, hC₀, hU⟩ := hupper
  obtain ⟨c, hc, hL⟩ := hlower B ε C1 C2 τmin Ctime Cgrad phi hB hε hε' hC1 hC2 hτ hphi
  obtain ⟨σ, hσ, hσ1, hUσ⟩ := hU (c / 2) (by positivity)
  have hκ₁ : 0 < c * σ ^ 3 / (2 * C₀) := by positivity
  obtain ⟨κ₂, hκ₂, hS⟩ :=
    hsmall B ε C1 C2 C1s C2s τmin Ctime Cgrad phi _ hB hε hε' hC1 hC2 hC1s hC2s hτ hphi hκ₁
  refine ⟨min (c * σ ^ 3 / (2 * C₀)) κ₂, lt_min hκ₁ hκ₂, ?_⟩
  intro qcan qs hqcan hqs
  obtain ⟨r₀, δS, ρS, εS, DS, mS, hr₀, hδS, hρS, hεS, hDS, hSstep⟩ := hS qcan qs hqcan hqs
  obtain ⟨δL, ρL, εL, DL, mL, hδL, hρL, hεL, hDL, hLstep⟩ := hL qcan r₀ hqcan hr₀
  refine ⟨min δS δL, min ρS ρL, min εS εL, max DS DL, max mS mL, lt_min hδS hδL,
    lt_min hρS hρL, lt_min hεS hεL, lt_max_of_lt_left hDS, ?_⟩
  intro p₀ δbound ρbound hacc hD hm hδ hρ H hH hpinch
  have hs := hSstep p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hD) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH hpinch
  have hl := hLstep p₀ δbound ρbound (hacc.trans (min_le_right _ _))
    ((le_max_right _ _).trans hD) ((le_max_right _ _).trans hm) (hδ.trans (min_le_right _ _))
    (hρ.trans (min_le_right _ _)) H hH hpinch
  refine ⟨?_, ?_⟩
  · intro j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb
    have habove := H.noncollapsedAboveBefore_of_reducedVolume_bounds hc hC₀ hσ hσ1 hmono
      (hUσ H) (hl.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb)
    exact H.noncollapsedBefore_min_of_noncollapsedAboveBefore habove
      (hs.1 j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb habove)
  · intro s G hG hpG hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb
    have habove : H.TerminalNoncollapsedAboveBefore hH.2.1 G hG.2
        (c * σ ^ 3 / (2 * C₀)) r₀ ε t₀ := fun T hT hTs hTt =>
      RetainedCoreHistory.noncollapsedAboveBefore_of_reducedVolume_bounds _ hc hC₀ hσ hσ1
        hmono (hUσ _) (hl.2 s G hG hpG hcan hder hgrad t₀ ht₀ hcb hdb hgb T hT hTs hTt)
    have hbelow := hs.2 s G hG hpG hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb habove
    exact fun T hT hTs hTt =>
      RetainedCoreHistory.noncollapsedBefore_min_of_noncollapsedAboveBefore _
        (habove T hT hTs hTt) (hbelow T hT hTs hTt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
