import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Base_O34

/-!
# CH12-O37 G3: the base+step contract `hBS` of `hG2c_of_baseStep_O34` from Sublemma 86.3 and a
uniform Sublemma 86.6

`hBS_O37 Hp hsub86N hSTEP` chooses the common constants of `[FROZEN v4] CH12-O34` in the lead's
order ε → θ → (C) → K → κ → τ₁, τ₂ → Λ → b → T: `ε` from `hsub86N` (= `hsub86N_S74_shape`,
`[FROZEN v2] CH12-S63`), then each constant of the uniform step `hSTEP` (`[FROZEN] CH12-O37`,
every later constant may depend on the earlier ones, monotone in the direction used here) is
combined with the matching constant of `hsub86N` by `max`/`min`; `b` also meets the O34 budget
`b ≤ 1/(2(Λ+τ₁+τ₂+1))` and `T ≥ 2Λ·neck(0)²`. BASE is `base_of_hsub86N_O34`, STEP is `hSTEP` at
these constants. `hG2c_O37` feeds the result to `hG2c_of_baseStep_O34`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

/-- The base+step contract `hBS` (`[FROZEN v4] CH12-O34`, verbatim) from Sublemma 86.3 in the
restricted tower form (`hsub86N`) and Sublemma 86.6 in uniform-constant form (`hSTEP`). -/
theorem hBS_O37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hsub86N :
    ∃ ε C₁ K τ₁ τ₂ Λ T κ₀ : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      τ₁ + τ₂ ≤ Λ ∧ 0 < T ∧ 0 < κ₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r0 ^ 2) u →
          ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0) →
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
          (a : ℝ) = (u : ℝ) - τ₁ * r0 ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w)
                ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹))
    (hSTEP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ θ C₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C₆ ∧ ∀ C : ℝ, C₆ ≤ C →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
      ∃ τ₆ : ℝ, 0 < τ₆ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ Λ₆ : ℝ, τ₁ + τ₂ ≤ Λ₆ ∧ ∀ Λ : ℝ, Λ₆ ≤ Λ →
      ∃ b₆ : ℝ, 0 < b₆ ∧ ∀ b : ℝ, 0 < b → b ≤ b₆ →
      ∃ T₆ : ℝ, ∀ T : ℝ, T₆ ≤ T →
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → Hp.parameters.neckRadius (u : ℝ) < r →
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
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
          (y : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r' : ℝ), v ≤ u →
          (u : ℝ) - Λ * r ^ 2 ≤ v - Λ * r' ^ 2 → θ * Hp.parameters.neckRadius (u : ℝ) ≤ r' →
          r' ≤ θ * r → (0 < (v : ℝ) ∧ (v : ℝ) ∉ F.observation.eventTimes) → r' ≤ b * Real.sqrt v →
          (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r' ^ 2)⁻¹)) →
          (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
              ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) z ρ) →
          (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ v)
            (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
              ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hau) y),
            (a : ℝ) = v - τ₁ * r' ^ 2 ∧
            ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ v),
              (sliceTowerHistory_CX2 s).isTracedRegion w
                (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹))) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)))) :
    ∃ ε θ C K τ₁ τ₂ κ Λ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C ∧ 0 < K ∧
      0 < τ₁ ∧ 0 < τ₂ ∧ 0 < κ ∧ τ₁ + τ₂ ≤ Λ ∧ 0 < b ∧ b ≤ 1 / (2 * (Λ + τ₁ + τ₂ + 1)) ∧ 0 < T ∧
      2 * Λ * Hp.parameters.neckRadius 0 ^ 2 ≤ T ∧
     (∀ s : RegularSlice F.observation, T ≤ s.time →
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
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) ∧
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → Hp.parameters.neckRadius (u : ℝ) < r →
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
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
          (y : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r' : ℝ), v ≤ u →
          (u : ℝ) - Λ * r ^ 2 ≤ v - Λ * r' ^ 2 → θ * Hp.parameters.neckRadius (u : ℝ) ≤ r' →
          r' ≤ θ * r → (0 < (v : ℝ) ∧ (v : ℝ) ∉ F.observation.eventTimes) → r' ≤ b * Real.sqrt v →
          (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r' ^ 2)⁻¹)) →
          (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
              ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) z ρ) →
          (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ v)
            (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
              ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hau) y),
            (a : ℝ) = v - τ₁ * r' ^ 2 ∧
            ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ v),
              (sliceTowerHistory_CX2 s).isTracedRegion w
                (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹))) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) := by
  obtain ⟨ε, C₁', K', τ₁', τ₂', Λ', T', κ', hε, hε2, hC₁', hK', hτ₁', hτ₂', hΛ', hT', hκ', hsub⟩ :=
    hsub86N
  obtain ⟨θ, C₆, hθ, hθ2, hC₆, hS⟩ := hSTEP ε hε hε2
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C₁' C₆ := ⟨_, rfl⟩
  have hCC₆ : C₆ ≤ C := hCdef ▸ le_max_right _ _
  have hCC₁ : C₁' ≤ C := hCdef ▸ le_max_left _ _
  obtain ⟨K₆, hK₆, hS⟩ := hS C hCC₆
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max K' K₆ := ⟨_, rfl⟩
  have hKK₆ : K₆ ≤ K := hKdef ▸ le_max_right _ _
  have hKK' : K' ≤ K := hKdef ▸ le_max_left _ _
  obtain ⟨κ₆, hκ₆, hS⟩ := hS K hKK₆
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min κ' κ₆ := ⟨_, rfl⟩
  have hκpos : 0 < κ := hκdef ▸ lt_min hκ' hκ₆
  have hκκ₆ : κ ≤ κ₆ := hκdef ▸ min_le_right _ _
  have hκκ' : κ ≤ κ' := hκdef ▸ min_le_left _ _
  obtain ⟨τ₆, hτ₆, hS⟩ := hS κ hκpos hκκ₆
  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ : ℝ, τ = min τ₁' τ₆ := ⟨_, rfl⟩
  obtain ⟨τ₂, hτ₂def⟩ : ∃ τ : ℝ, τ = min τ₂' τ₆ := ⟨_, rfl⟩
  have hτ₁pos : 0 < τ₁ := hτ₁def ▸ lt_min hτ₁' hτ₆
  have hτ₂pos : 0 < τ₂ := hτ₂def ▸ lt_min hτ₂' hτ₆
  have hτ₁₆ : τ₁ ≤ τ₆ := hτ₁def ▸ min_le_right _ _
  have hτ₂₆ : τ₂ ≤ τ₆ := hτ₂def ▸ min_le_right _ _
  have hτ₁' : τ₁ ≤ τ₁' := hτ₁def ▸ min_le_left _ _
  have hτ₂' : τ₂ ≤ τ₂' := hτ₂def ▸ min_le_left _ _
  obtain ⟨Λ₆, -, hS⟩ := hS τ₁ τ₂ hτ₁pos hτ₁₆ hτ₂pos hτ₂₆
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = max Λ' Λ₆ := ⟨_, rfl⟩
  have hΛΛ₆ : Λ₆ ≤ Λ := hΛdef ▸ le_max_right _ _
  have hΛΛ' : Λ' ≤ Λ := hΛdef ▸ le_max_left _ _
  have hτΛ : τ₁ + τ₂ ≤ Λ := by linarith
  obtain ⟨b₆, hb₆, hS⟩ := hS Λ hΛΛ₆
  have hden : 0 < 2 * (Λ + τ₁ + τ₂ + 1) := by linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = min b₆ (1 / (2 * (Λ + τ₁ + τ₂ + 1))) := ⟨_, rfl⟩
  have hbpos : 0 < b := hbdef ▸ lt_min hb₆ (by positivity)
  have hbb₆ : b ≤ b₆ := hbdef ▸ min_le_left _ _
  have hbL : b ≤ 1 / (2 * (Λ + τ₁ + τ₂ + 1)) := hbdef ▸ min_le_right _ _
  obtain ⟨T₆, hS⟩ := hS b hbpos hbb₆
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ,
      T = max (max T' T₆) (2 * Λ * Hp.parameters.neckRadius 0 ^ 2) := ⟨_, rfl⟩
  have hTT₆ : T₆ ≤ T := hTdef ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hTT' : T' ≤ T := hTdef ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hTn : 2 * Λ * Hp.parameters.neckRadius 0 ^ 2 ≤ T := hTdef ▸ le_max_right _ _
  have hC1 : 1 ≤ C := hC₁'.trans hCC₁
  have hKpos : 0 < K := hK'.trans_le hKK'
  exact ⟨ε, θ, C, K, τ₁, τ₂, κ, Λ, b, T, hε, hε2, hθ, hθ2, hC1, hKpos, hτ₁pos, hτ₂pos, hκpos,
    hτΛ, hbpos, hbL, hT'.trans_le hTT', hTn,
    base_of_hsub86N_O34 Hp (b := b) hCC₁ hΛΛ' hTT' hK' hKK' hτ₁pos hτ₁' hτ₂pos hτ₂' hκpos hκκ'
      hsub,
    hS T hTT₆⟩

/-- `hG2c` in κ-cert form (`[FROZEN v3] CH12-O28`, the `hG2c` binder of `A13_of_supplies_S78`)
from `hsub86N` and the uniform Sublemma 86.6 `hSTEP`. -/
theorem hG2c_O37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hsub86N :
    ∃ ε C₁ K τ₁ τ₂ Λ T κ₀ : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      τ₁ + τ₂ ≤ Λ ∧ 0 < T ∧ 0 < κ₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r0 ^ 2) u →
          ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0) →
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
          (a : ℝ) = (u : ℝ) - τ₁ * r0 ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w)
                ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹))
    (hSTEP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ θ C₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C₆ ∧ ∀ C : ℝ, C₆ ≤ C →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
      ∃ τ₆ : ℝ, 0 < τ₆ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ Λ₆ : ℝ, τ₁ + τ₂ ≤ Λ₆ ∧ ∀ Λ : ℝ, Λ₆ ≤ Λ →
      ∃ b₆ : ℝ, 0 < b₆ ∧ ∀ b : ℝ, 0 < b → b ≤ b₆ →
      ∃ T₆ : ℝ, ∀ T : ℝ, T₆ ≤ T →
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → Hp.parameters.neckRadius (u : ℝ) < r →
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
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
          (y : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r' : ℝ), v ≤ u →
          (u : ℝ) - Λ * r ^ 2 ≤ v - Λ * r' ^ 2 → θ * Hp.parameters.neckRadius (u : ℝ) ≤ r' →
          r' ≤ θ * r → (0 < (v : ℝ) ∧ (v : ℝ) ∉ F.observation.eventTimes) → r' ≤ b * Real.sqrt v →
          (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r' ^ 2)⁻¹)) →
          (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
              ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) z ρ) →
          (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ v)
            (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
              ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hau) y),
            (a : ℝ) = v - τ₁ * r' ^ 2 ∧
            ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ v),
              (sliceTowerHistory_CX2 s).isTracedRegion w
                (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹))) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)))) :
    ∃ ε C₁ K τ₁ τ₂ κ₀ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      0 < κ₀ ∧ 0 < b ∧ (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) :=
  hG2c_of_baseStep_O34 Hp (hBS_O37 Hp hsub86N hSTEP)

end GC.LongTime.Ch12
