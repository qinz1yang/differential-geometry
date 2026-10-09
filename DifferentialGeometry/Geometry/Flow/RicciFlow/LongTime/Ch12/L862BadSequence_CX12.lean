import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TraceFamily_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Selection_CX12

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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)

/- This is the negation of the exact target, used only for contradiction
reductions. It is never presented as a supplier of the geometric result. -/
variable (hfail : ¬ (∃ ε C₁ K τ₁ τ₂ b T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < b ∧ 0 < T ∧
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
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)))

include hfail

/-- Negating the frozen existential statement produces a bad ball for
every positive normalized scale and every late-time threshold, in this
same fixed flow. -/
theorem bad_slice_of_not_hG2c_CX12 (ε C₁ K τ₁ τ₂ b T : ℝ)
    (hε : 0 < ε) (hC₁ : 1 ≤ C₁) (hK : 0 < K) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hb : 0 < b) (hT : 0 < T) :
    ∃ s : RegularSlice F.observation, T ≤ s.time ∧
      ∃ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 ∧
        r0 ≤ b * Real.sqrt s.time ∧
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) ∧
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) ∧
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) ∧
        ¬ (∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) := by
  classical
  push Not at hfail ⊢
  exact hfail ε C₁ K τ₁ τ₂ b T hε hC₁ hK hτ₁ hτ₂ hb hT

/-- The frozen Sublemma 86.3 removes the small-neck case from every
counterexample. The resulting balls occur at times at least n+1 and have
r0/sqrt(t) at most 1/(n+1), all in one fixed flow. -/
theorem bad_neck_scale_sequence_CX12
    (hsub86 : ∃ ε C₁ K τ₁ τ₂ T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius s.time →
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
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) :
    ∃ ε C₁ K τ₁ τ₂ T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < T ∧
      ∀ n : ℕ,
    ∃ s : RegularSlice F.observation, max T ((n : ℝ) + 1) ≤ s.time ∧
      ∃ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 ∧
        r0 ≤ ((n : ℝ) + 1)⁻¹ * Real.sqrt s.time ∧
        Hp.parameters.neckRadius s.time < r0 ∧
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) ∧
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) ∧
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) ∧
        ¬ (∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) := by
  obtain ⟨ε, C₁, K, τ₁, τ₂, T, hε, hC₁, hK, hτ₁, hτ₂, hT, hsub⟩ := hsub86
  refine ⟨ε, C₁, K, τ₁, τ₂, T, hε, hC₁, hK, hτ₁, hτ₂, hT, ?_⟩
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨s, hs, x0, r0, hr, hrb, hrec, hsec, hvol, hbad⟩ :=
    bad_slice_of_not_hG2c_CX12 Hp hfail ε C₁ K τ₁ τ₂ ((n : ℝ) + 1)⁻¹
      (max T ((n : ℝ) + 1)) hε hC₁ hK hτ₁ hτ₂ (inv_pos.mpr hn)
      (hT.trans_le (le_max_left _ _))
  refine ⟨s, hs, x0, r0, hr, hrb, ?_, hrec, hsec, hvol, hbad⟩
  apply lt_of_not_ge
  intro hneck
  exact hbad (hsub s ((le_max_left _ _).trans hs) x0 r0 hr hneck hrec hsec hvol)

end GC.LongTime.Ch12
