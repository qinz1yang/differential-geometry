import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

def CanonicalBoundsOn (ε C1 C2 qcan τmin : ℝ) (Ctime Cgrad : ℝ≥0) (t₀ η : ℝ)
    (S : P.Carrier → ℝ → Prop) : Prop :=
  ∀ (y : P.Carrier) (t : ℝ), a < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    S y t →
    (τmin ≤ G.flow.scalar t y * (t - a) →
      ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
    |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
    ∀ v : TangentSpace I3 y, |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
      Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
        Real.sqrt ((G.flow.base.metric t).inner y v v)

theorem canonicalBoundsOn_of_cover {ε C1 C2 qcan τmin : ℝ} {Ctime Cgrad : ℝ≥0} {t₀ η₁ η₂ η₃ : ℝ}
    {S₁ S₂ S₃ : P.Carrier → ℝ → Prop}
    (h₁ : G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η₁ S₁)
    (h₂ : G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η₂ S₂)
    (h₃ : G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η₃ S₃)
    (hcover : ∀ y t, S₁ y t ∨ S₂ y t ∨ S₃ y t) :
    G.DerivativeBoundOn Ctime qcan t₀ (min η₁ (min η₂ η₃)) ∧
      G.GradientBoundOn Cgrad qcan t₀ (min η₁ (min η₂ η₃)) ∧
      G.CanonicalOn ε C1 C2 qcan τmin t₀ (min η₁ (min η₂ η₃)) := by
  have hall : ∀ y t, a < t → t₀ ≤ t → t < t₀ + min η₁ (min η₂ η₃) → t < s →
      qcan < G.flow.scalar t y →
      (τmin ≤ G.flow.scalar t y * (t - a) →
        ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
          Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
            Real.sqrt ((G.flow.base.metric t).inner y v v) := by
    intro y t hat ht₀ htη hts hR
    have hη₁ : t < t₀ + η₁ := htη.trans_le (by linarith [min_le_left η₁ (min η₂ η₃)])
    have hη₂ : t < t₀ + η₂ := htη.trans_le (by
      linarith [min_le_right η₁ (min η₂ η₃), min_le_left η₂ η₃])
    have hη₃ : t < t₀ + η₃ := htη.trans_le (by
      linarith [min_le_right η₁ (min η₂ η₃), min_le_right η₂ η₃])
    rcases hcover y t with h | h | h
    · exact h₁ y t hat ht₀ hη₁ hts hR h
    · exact h₂ y t hat ht₀ hη₂ hts hR h
    · exact h₃ y t hat ht₀ hη₃ hts hR h
  exact ⟨fun y t hat ht₀ htη hts hR => (hall y t hat ht₀ htη hts hR).2.1,
    fun y t hat ht₀ htη hts hR => (hall y t hat ht₀ htη hts hR).2.2,
    fun y t hat ht₀ htη hts hR => (hall y t hat ht₀ htη hts hR).1⟩

end OrientedThreeStage.IncomingSlab

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

def IsCanonicalCutoffRecordFamily (p₀ : CutoffParameters) (δ₀ ρ₀ : ℝ) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) : Prop :=
  p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧ p.modelOrder = p₀.modelOrder ∧
    p.modelAccuracy = p₀.modelAccuracy ∧ p.recenterConstant = p₀.recenterConstant ∧
    (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
    (∀ i : Fin H.eventCount, p.delta (H.time i.succ) ≤ δ₀) ∧
    ∀ i : Fin H.eventCount, p.neckRadius (H.time i.succ) ≤ ρ₀

theorem hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily
    (p₀ : CutoffParameters) (δ₀ ρ₀ : ℝ) :
    H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ ↔
      ∃ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records := by
  constructor
  · rintro ⟨p, hf, hD, hm, hε, hc, records, hcan, hδ, hρ⟩
    exact ⟨p, records, hf, hD, hm, hε, hc, hcan, hδ, hρ⟩
  · rintro ⟨p, records, hf, hD, hm, hε, hc, hcan, hδ, hρ⟩
    exact ⟨p, hf, hD, hm, hε, hc, records, hcan, hδ, hρ⟩

theorem IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale {H : RetainedCoreHistory.{u}}
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    (2 * ρ₀ ^ 2)⁻¹ < ((records i).static b).neck.scale := by
  obtain ⟨-, -, -, -, hrc, -, hδ, hρ⟩ := hrec
  have ht : 0 ≤ H.time i.succ := H.toHistory.time_nonneg i.succ
  set α := b.1.1
  have hn := (records i).nominal_small ⟨α⟩
  have hnpos := (records i).nominal_pos ⟨α⟩
  have hdpos := p.delta_pos _ ht
  have hd1 := p.delta_lt_one _ ht
  have hρpos := p.neckRadius_pos _ ht
  have hcmp := (records i).recenter_scale_comparison b
  have hsc := (records i).scale_eq α
  have hdα := (records i).delta_le α
  have hdαpos := (records i).delta_pos α
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  rw [hrc] at hcmp hΛ
  set r := (records i).nominalRadius ⟨α⟩
  set N := ((records i).neck α).scale
  set S := ((records i).static b).neck.scale
  have hSpos : 0 < S := ((records i).static b).neck.scale_pos
  have hr : r < ρ₀ := by
    have h1 : p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤
        p.neckRadius (H.time i.succ) := by
      have : p.delta (H.time i.succ) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    exact hn.trans_le (h1.trans (hρ i))
  have hNlow : (ρ₀ ^ 2)⁻¹ < N := by
    rw [hsc]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (by nlinarith)
  have hNpos : 0 < N := (inv_pos.mpr (pow_pos (hnpos.trans hr) 2)).trans hNlow
  have hΛδα : p₀.recenterConstant * (records i).delta α ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hdα.trans (hδ i)) (by linarith)).trans hΛδ
  have hhalf : 1 / 2 ≤ S / N := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  have hS : N / 2 ≤ S := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * ρ₀ ^ 2)⁻¹ = (ρ₀ ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]; ring
  rw [h2]
  linarith

def CapWindowPoint {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (k : Fin (H.eventCount + 1)) (y : (H.stage k).Carrier) (t Dcap θcap : ℝ) : Prop :=
  ∃ (j : Fin H.eventCount) (hl : j.succ ≤ k) (A : BackwardPointTrace H.toHistory j.succ k hl y)
    (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
    A.point j.succ le_rfl hl = ((records j).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
      t - H.time j.succ ≤ θcap * (((records j).static b).neck.scale)⁻¹

end RetainedCoreHistory

def DeepContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →
  ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
    C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∃ (θ q₀ δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    0 < θ ∧ 0 < q₀ ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound),
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => θ ≤ (H.toHistory.event j).incoming.flow.scalar t y *
                (t - H.time j.castSucc)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
            fun y t => θ ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount))

def CapWindowContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →
  ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
    C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ Dcap θcap : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
    0 < θ → 0 < Dcap → θcap < 1 →
  ∃ (Rcap q₀ : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧
            (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => H.CapWindowPoint records j.castSucc y t Dcap θcap) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
            fun y t => H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap

def CrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →
  ∃ (C1₀ C2₀ τ₀ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 1 ≤ C1₀ ∧ 1 ≤ C2₀ ∧ 0 < τ₀ ∧
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0),
    C1₀ ≤ C1 → C2₀ ≤ C2 → τ₀ ≤ τmin → Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi → 0 < θ →
  ∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
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
            (H.toHistory.event j).incoming.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
              fun y t => (H.toHistory.event j).incoming.flow.scalar t y *
                  (t - H.time j.castSucc) < θ ∧
                ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap) ∧
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
          ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
            fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
              ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap

theorem canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hdeep : DeepContinuation P₀ g₀)
    (hcap : CapWindowContinuation P₀ g₀) (hcross : CrossingContinuation P₀ g₀) :
    CanonicalNeighborhoodContinuation P₀ g₀ := by
  obtain ⟨εbar, hεbar, hcross⟩ := hcross
  refine ⟨εbar, hεbar, ?_⟩
  intro B ε hB hε hε' hεbar'
  obtain ⟨C1d, C2d, τd, Ctd, Cgd, hC1d, hC2d, hτd, hD⟩ := hdeep B ε hB hε hε'
  obtain ⟨C1w, C2w, τw, Ctw, Cgw, -, -, -, hW⟩ := hcap B ε hB hε hε'
  obtain ⟨C1x, C2x, τx, Ctx, Cgx, -, -, -, hX⟩ := hcross B ε hB hε hε' hεbar'
  refine ⟨max C1d (max C1w C1x), max C2d (max C2w C2x), max τd (max τw τx),
    max Ctd (max Ctw Ctx), max Cgd (max Cgw Cgx), le_max_of_le_left hC1d,
    le_max_of_le_left hC2d, lt_max_of_lt_left hτd, ?_⟩
  intro C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi qfloor
  obtain ⟨θ, qd, δd, ρd, εd, Dd, md, hθ, hqd, hδd, hρd, hεd, hDd, hDstep⟩ :=
    hD _ _ _ _ _ (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) κ phi hκ hphi
  obtain ⟨Dx, θcap, qx, mx, hDx, hθcap, hqx, hXq⟩ :=
    hX _ _ _ _ _ ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
      C1s C2s Cs hC1s hC2s hCs κ phi θ hκ hphi hθ
  obtain ⟨Rw, qw, mw, hRw, hqw, hWq⟩ :=
    hW _ _ _ _ _ ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
      κ phi θ Dx θcap hκ hphi hθ hDx hθcap
  have hqdc : qd ≤ max qfloor (max qd (max qw qx)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hqwc : qw ≤ max qfloor (max qd (max qw qx)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hqxc : qx ≤ max qfloor (max qd (max qw qx)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hWstep⟩ := hWq _ hqwc
  obtain ⟨δx, ρx, εx, hδx, hρx, hεx, hXstep⟩ := hXq _ hqxc
  refine ⟨max qfloor (max qd (max qw qx)), min δd (min δw δx), min ρd (min ρw ρx),
    min εd (min εw εx), max Dd Rw, max md (max mw mx), le_max_left _ _, hqd.trans_le hqdc,
    lt_min hδd (lt_min hδw hδx), lt_min hρd (lt_min hρw hρx), lt_min hεd (lt_min hεw hεx),
    lt_max_of_lt_left hDd, ?_⟩
  intro qs hqs hqsC p₀ δbound ρbound hacc hDc hm hδ hρ H hH hpinch
  obtain ⟨p, records, hrec⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hH.2.2.2.1
  have hd := hDstep _ hqdc p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hDc) ((le_max_left _ _).trans hm) (hδ.trans (min_le_left _ _))
    (hρ.trans (min_le_left _ _)) H hH hpinch
  have hw := hWstep p₀ δbound ρbound
    (hacc.trans ((min_le_right _ _).trans (min_le_left _ _))) ((le_max_right _ _).trans hDc)
    (((le_max_left _ _).trans (le_max_right _ _)).trans hm)
    (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hρ.trans ((min_le_right _ _).trans (min_le_left _ _))) H hH p records hrec hpinch
  have hx := hXstep qs hqs hqsC p₀ δbound ρbound
    (hacc.trans ((min_le_right _ _).trans (min_le_right _ _)))
    ((by linarith : Dx ≤ Rw).trans ((le_max_right _ _).trans hDc))
    (((le_max_right _ _).trans (le_max_right _ _)).trans hm)
    (hδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hρ.trans ((min_le_right _ _).trans (min_le_right _ _))) H hH p records hrec hpinch
  refine ⟨?_, ?_⟩
  · intro j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
    obtain ⟨η₁, hη₁, h₁⟩ := hd.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₂, hη₂, h₂⟩ := hw.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₃, hη₃, h₃⟩ := hx.1 j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
    refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃),
      (H.toHistory.event j).incoming.canonicalBoundsOn_of_cover h₁ h₂ h₃ fun y t => ?_⟩
    rcases le_or_gt θ ((H.toHistory.event j).incoming.flow.scalar t y *
      (t - H.time j.castSucc)) with h | h
    · exact Or.inl h
    · by_cases hc : H.CapWindowPoint records j.castSucc y t Dx θcap
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨h, hc⟩)
  · intro s G hG hpG hcan hder hgrad hspat hncL t₀ ht₀ hcb hdb hgb hsb hnc
    obtain ⟨η₁, hη₁, h₁⟩ := hd.2 s G hG hpG hcan hder hgrad hncL t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₂, hη₂, h₂⟩ := hw.2 s G hG hpG hcan hder hgrad hncL t₀ ht₀ hcb hdb hgb hnc
    obtain ⟨η₃, hη₃, h₃⟩ :=
      hx.2 s G hG hpG hcan hder hgrad hspat hncL t₀ ht₀ hcb hdb hgb hsb hnc
    refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃),
      G.canonicalBoundsOn_of_cover h₁ h₂ h₃ fun y t => ?_⟩
    rcases le_or_gt θ (G.flow.scalar t y * (t - H.time (Fin.last H.eventCount))) with h | h
    · exact Or.inl h
    · by_cases hc : H.CapWindowPoint records (Fin.last H.eventCount) y t Dx θcap
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨h, hc⟩)
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
