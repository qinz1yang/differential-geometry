import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HbsPack_O49
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862EnlargeKL82_O42
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862UnscathedRegion_S111

/-!
# CH12-S111 G2: `step866_of_unscathed_S111` and `hG2c_S111`

`hUnscathed866` (`[FROZEN] CH12-S111`, an inline input, typechecked text:
`build-logs/ch12/scratch/FrozenS111.lean`) is the unscathedness of the parent ball `B_v(X(v), σ r)`
along a trace of `x` to the depth `τ₀ (σ r)²`, in the constant order of `hSTEP866 v2`.  From it,
`enlarged_rm_kl82_O42` at `A = 1`, `w = (1 − ε) ω₃` gives `|Rm| ≤ B/(σ r)²` on the moving balls
for `v ∈ [u − c (σ r)², u]`; with `τ₆ := min τ₆' (cσ²/4, σ²/(64 (B+16)))`, `K₆ := max K₆' (B/σ²)`,
`κ₆ := min κ₆' (σ/4)`, `b₆ := min b₆' (1/2, ρ/2)`, `T₆ := max T₆' (2 T₁)` the traced regions
of `hSTEP866 v2` follow from `traced_region_S111`.  The Child induction hypothesis and `θ` occur only
inside `hUnscathed866`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal

namespace GC.LongTime.Ch12

universe u

/-- **Sublemma 86.6 (v2) from the unscathedness input.** -/
theorem step866_of_unscathed_S111 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hU :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 →
      ∃ σ τ₆ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < τ₆ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ θ C₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C₆ ∧ ∀ C : ℝ, C₆ ≤ C →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
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
        ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₀ * (σ * r) ^ 2 ∧ ∃ K' : ℝ,
          (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v)
                (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (σ * r),
              ∃ A' : BackwardPointTrace (sliceTowerHistory_CX2 s)
                  ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav) q,
                A'.isRmBoundedBy (hat := hav) K') ∧
          (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v)
                (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (σ * r),
              SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q (-((σ * r) ^ 2)⁻¹)))) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ τ₆ : ℝ, 0 < τ₆ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ θ C₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C₆ ∧ ∀ C : ℝ, C₆ ≤ C →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
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
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) := by
  intro ε hε hε2
  have hω : 0 < euclideanUnitBallVolume 3 := euclideanUnitBallVolume_pos 3
  have hw : 0 < (1 - ε) * euclideanUnitBallVolume 3 := mul_pos (by linarith) hω
  obtain ⟨τ₀, c, T₁, ρ, B, hτ₀, hτ₀1, hc, hcτ, hT₁, hρ, hB, henl⟩ :=
    enlarged_rm_kl82_O42.{u} Hp 1 one_pos hw
  obtain ⟨σ, τ₆', hσ, hσ1, hτ₆', hU1⟩ := hU ε hε hε2 τ₀ hτ₀ hτ₀1
  have hBp : 0 < B + 16 := by linarith
  have hσ2 : 0 < σ ^ 2 := by positivity
  refine ⟨min τ₆' (min (c * σ ^ 2 / 4) (σ ^ 2 / (64 * (B + 16)))),
    lt_min hτ₆' (lt_min (by positivity) (by positivity)), ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₁6 hτ₂ hτ₂6
  obtain ⟨hτ₁a, hτ₁b, hτ₁c⟩ : τ₁ ≤ τ₆' ∧ τ₁ ≤ c * σ ^ 2 / 4 ∧
      τ₁ ≤ σ ^ 2 / (64 * (B + 16)) := by
    simp only [le_min_iff] at hτ₁6
    exact ⟨hτ₁6.1, hτ₁6.2.1, hτ₁6.2.2⟩
  obtain ⟨hτ₂a, hτ₂b, hτ₂c⟩ : τ₂ ≤ τ₆' ∧ τ₂ ≤ c * σ ^ 2 / 4 ∧
      τ₂ ≤ σ ^ 2 / (64 * (B + 16)) := by
    simp only [le_min_iff] at hτ₂6
    exact ⟨hτ₂6.1, hτ₂6.2.1, hτ₂6.2.2⟩
  obtain ⟨θ, C₆, hθ, hθ2, hC₆, hU2⟩ := hU1 τ₁ τ₂ hτ₁ hτ₁a hτ₂ hτ₂a
  refine ⟨θ, C₆, hθ, hθ2, hC₆, fun C hC => ?_⟩
  obtain ⟨K₆, hK₆, hU3⟩ := hU2 C hC
  refine ⟨max K₆ (B / σ ^ 2), lt_max_of_lt_left hK₆, fun K hK => ?_⟩
  obtain ⟨hK6, hKB⟩ := max_le_iff.mp hK
  obtain ⟨κ₆, hκ₆, hU4⟩ := hU3 K hK6
  refine ⟨min κ₆ (σ / 4), lt_min hκ₆ (by positivity), fun κ hκ hκ6 => ?_⟩
  obtain ⟨hκa, hκb⟩ := le_min_iff.mp hκ6
  obtain ⟨Λ₆, hΛ₆, hU5⟩ := hU4 κ hκ hκa
  refine ⟨Λ₆, hΛ₆, fun Λ hΛ => ?_⟩
  obtain ⟨b₆, hb₆, hU6⟩ := hU5 Λ hΛ
  refine ⟨min b₆ (min (1 / 2) (ρ / 2)),
    lt_min hb₆ (lt_min (by norm_num) (by positivity)), fun b hb hb6 => ?_⟩
  obtain ⟨hba, hbb, hbc⟩ : b ≤ b₆ ∧ b ≤ 1 / 2 ∧ b ≤ ρ / 2 := by
    simp only [le_min_iff] at hb6
    exact ⟨hb6.1, hb6.2.1, hb6.2.2⟩
  obtain ⟨T₆, hU7⟩ := hU6 b hb hba
  refine ⟨max T₆ (2 * T₁), fun T hT => ?_⟩
  obtain ⟨hT6, hT1⟩ := max_le_iff.mp hT
  have hdatum := hU7 T hT6
  intro s hTs u hTu hus hreg x r hr hneck hrb hguard hsec hvol hIH
  obtain ⟨a, hau, X, ha, K', hSF, hsecU⟩ :=
    hdatum s hTs u hTu hus hreg x r hr hneck hrb hguard hsec hvol hIH
  have hr0 : 0 < σ * r := mul_pos hσ hr
  have hσr : σ * r ≤ r := mul_le_of_le_one_left hr.le hσ1
  have hvol0 : ENNReal.ofReal (((1 - ε) * euclideanUnitBallVolume 3) * (σ * r) ^ 3) ≤
      ballVolume ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage u) u) x (σ * r) :=
    hvol x (mem_ball_self_O12 _ x hr) (σ * r) hr0 hσr
  have hu0 : 0 ≤ (u : ℝ) := u.2.1
  have hrm : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ u),
      (u : ℝ) - c * (σ * r) ^ 2 ≤ v →
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v)
          (X.point ((sliceTowerHistory_CX2 s).activeStage v)
            ((sliceTowerHistory_CX2 s).activeStage_mono hav)
            ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (20 * (1 * (σ * r))),
        Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
          (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ B / (σ * r) ^ 2 := by
    intro v hav hvt hv q hq
    obtain ⟨hTv, hrv⟩ := window_S111 hu0 hr hσ hσ1 hcτ hτ₀1 hb hbb hbc hρ hrb hT₁ hT1 hTu
      v.2.1 hv
    exact henl s u hus a hau x X (σ * r) K' hr0 ha hSF hsecU hvol0 v hav hvt hv hTv hrv q hq
  -- the new left end `a'` of the trace and the traced regions
  have hX0 : 0 ≤ (σ * r) ^ 2 := sq_nonneg _
  have hcX : c * (σ * r) ^ 2 ≤ τ₀ * (σ * r) ^ 2 := mul_le_mul_of_nonneg_right hcτ hX0
  have hcX0 : 0 ≤ c * (σ * r) ^ 2 := mul_nonneg hc.le hX0
  have h1 : τ₁ * r ^ 2 ≤ c * (σ * r) ^ 2 / 4 :=
    calc τ₁ * r ^ 2 ≤ c * σ ^ 2 / 4 * r ^ 2 := mul_le_mul_of_nonneg_right hτ₁b (sq_nonneg r)
      _ = c * (σ * r) ^ 2 / 4 := by ring
  have h2 : τ₂ * r ^ 2 ≤ c * (σ * r) ^ 2 / 4 :=
    calc τ₂ * r ^ 2 ≤ c * σ ^ 2 / 4 * r ^ 2 := mul_le_mul_of_nonneg_right hτ₂b (sq_nonneg r)
      _ = c * (σ * r) ^ 2 / 4 := by ring
  have ha'ge : (a : ℝ) ≤ (u : ℝ) - τ₁ * r ^ 2 := by rw [ha]; linarith
  let a' : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(u : ℝ) - τ₁ * r ^ 2, a.2.1.trans ha'ge,
      (sub_le_self _ (by positivity)).trans u.2.2⟩
  have haa' : a ≤ a' := ha'ge
  have ha'u : a' ≤ u := show (u : ℝ) - τ₁ * r ^ 2 ≤ u from sub_le_self _ (by positivity)
  refine ⟨a', ha'u, X.restrictFirst ((sliceTowerHistory_CX2 s).activeStage_mono haa')
    ((sliceTowerHistory_CX2 s).activeStage_mono ha'u), rfl, ?_⟩
  intro w haw hwu
  have hKb : B / (σ * r) ^ 2 ≤ K * (r ^ 2)⁻¹ := by
    have e : B / (σ * r) ^ 2 = B / σ ^ 2 * (r ^ 2)⁻¹ := by
      rw [mul_pow]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hKB (by positivity)
  have hδs : τ₂ * r ^ 2 ≤ (σ * r) ^ 2 / (64 * (B + 16)) :=
    calc τ₂ * r ^ 2 ≤ σ ^ 2 / (64 * (B + 16)) * r ^ 2 :=
          mul_le_mul_of_nonneg_right hτ₂c (sq_nonneg r)
      _ = (σ * r) ^ 2 / (64 * (B + 16)) := by rw [mul_pow]; ring
  have hac : (a : ℝ) ≤ (u : ℝ) - c * (σ * r) ^ 2 := by rw [ha]; linarith
  have hwcond : (u : ℝ) - c * (σ * r) ^ 2 + τ₂ * r ^ 2 ≤ w := by
    have hw' : (a' : ℝ) ≤ w := haw
    have h3 : (a' : ℝ) = (u : ℝ) - τ₁ * r ^ 2 := rfl
    linarith
  have hκr4 : κ * r ≤ σ * r / 4 :=
    calc κ * r ≤ σ / 4 * r := mul_le_mul_of_nonneg_right hκb hr.le
      _ = σ * r / 4 := by ring
  exact traced_region_S111 (sliceTowerHistory_CX2 s) hau X hr0 hB (by positivity)
    (mul_pos hκ hr) hκr4 hδs hKb hac hSF hrm w (haa'.trans haw) hwu hwcond

/-- `hG2c` in κ-cert form (`[FROZEN v3] CH12-O28`) from S94's Sublemma 86.3 inputs and the
unscathedness input `hUnscathed866` (`[FROZEN] CH12-S111`): `hG2c_O49` with `hSTEP` produced by
`step866_of_unscathed_S111`. -/
theorem hG2c_S111 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    (hU :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ 1 →
      ∃ σ τ₆ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < τ₆ ∧ ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ θ C₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C₆ ∧ ∀ C : ℝ, C₆ ≤ C →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
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
        ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₀ * (σ * r) ^ 2 ∧ ∃ K' : ℝ,
          (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v)
                (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (σ * r),
              ∃ A' : BackwardPointTrace (sliceTowerHistory_CX2 s)
                  ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav) q,
                A'.isRmBoundedBy (hat := hav) K') ∧
          (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v)
                (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (σ * r),
              SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q (-((σ * r) ^ 2)⁻¹)))) :
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
  hG2c_O49 Hp hdec hP2 hscale (step866_of_unscathed_S111 Hp hU)

end GC.LongTime.Ch12
