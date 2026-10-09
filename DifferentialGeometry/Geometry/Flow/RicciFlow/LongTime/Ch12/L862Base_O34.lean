import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862MinimalBad_O34

/-!
# CH12-O34 G2: the BASE clause of the `[FROZEN v4] CH12-O34` contract from `hsub86N`

The base clause (balls at or below the neck scale are good) of the base+step contract `hBS` of
`hG2c_of_baseStep_O34`, at any common constants that dominate those of Sublemma 86.3 in its
restricted tower-history form (`[FROZEN v2] CH12-S63 hsub86N`, lane S74; inline binder,
verbatim): larger guard constant `C` and window `Λ`, later threshold `T`, larger curvature bound
`K`, smaller `τ₁ τ₂ κ`.  The halved Euclidean-subball premise of `hsub86N` follows from the full
one of the contract (`B(x, r/2) ⊆ B(x, r)`, `ρ ≤ r/2 ≤ r`); `b` is not used by the base clause.
-/
set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **BASE of `[FROZEN v4] CH12-O34` from `hsub86N` (`[FROZEN v2] CH12-S63`, restricted form).** -/
theorem base_of_hsub86N_O34 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {ε C₁' K' τ₁' τ₂' Λ' T' κ' C K τ₁ τ₂ κ Λ b T : ℝ} (hC : C₁' ≤ C) (hΛ : Λ' ≤ Λ) (hT : T' ≤ T)
    (hK' : 0 < K') (hK : K' ≤ K) (hτ₁ : 0 < τ₁) (hτ₁' : τ₁ ≤ τ₁') (hτ₂ : 0 < τ₂)
    (hτ₂' : τ₂ ≤ τ₂') (hκ : 0 < κ) (hκ' : κ ≤ κ')
    (hsub :
    ∀ s : RegularSlice F.observation, T' ≤ s.time →
    ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T' ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
    (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
    ∀ (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r0 : ℝ), 0 < r0 →
      r0 ≤ Hp.parameters.neckRadius u →
      (∀ m (i : Fin (F.tower.history m).eventCount),
        (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ' * r0 ^ 2) u →
        ∀ h, C₁' * (Hp.records m i).nominalRadius h ≤ r0) →
      (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) x0 r0,
        SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r0 ^ 2)⁻¹)) →
      (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) x0 (r0 / 2),
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 / 2 →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
            ballVolume ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
      ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hat : a ≤ u)
        (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
          ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
          ((sliceTowerHistory_CX2 s).activeStage_mono hat) x0),
        (a : ℝ) = (u : ℝ) - τ₁' * r0 ^ 2 ∧
        ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
          (sliceTowerHistory_CX2 s).isTracedRegion w
            (X.point ((sliceTowerHistory_CX2 s).activeStage w)
              ((sliceTowerHistory_CX2 s).activeStage_mono haw)
              ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
            (κ' * r0) (τ₂' * r0 ^ 2) (K' * (r0 ^ 2)⁻¹)) :
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ Hp.parameters.neckRadius (u : ℝ) →
        r ≤ b * Real.sqrt u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)) := by
  intro s hTs u hTu hus hreg x r hr hrn _ hgw hsec hvol
  exact good_mono_O34 hr hκ hκ' hτ₁ hτ₁' hτ₂ hτ₂' hK'.le hK
    (hsub s (le_trans hT hTs) u (le_trans hT hTu) hus hreg x r hr hrn
      (fun m i hi h => le_trans
        (mul_le_mul_of_nonneg_right hC ((Hp.records m i).nominal_pos h).le)
        (hgw m i ⟨by nlinarith [hi.1, mul_le_mul_of_nonneg_right hΛ (sq_nonneg r)], hi.2⟩ h))
      hsec
      (fun z hz ρ hρ hρr => hvol z (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal (by linarith)))
        ρ hρ (by linarith)))

end GC.LongTime.Ch12
