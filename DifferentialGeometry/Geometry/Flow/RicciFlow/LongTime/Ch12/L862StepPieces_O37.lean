import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862ChildBall_O34

/-!
# CH12-O37 G2a: two pieces of the STEP clause (KL Sublemma 86.6)

* `center_rm_of_tracedRegion_O37`: a traced region bounds the curvature at its own center (the
  trace of the center at its own time is the center). Applied along the trace of a child's
  `Good` family this is the a-priori curvature bound that feeds the trace hypothesis of `hKL82`.
* `children_at_parent_time_O37`: the restart at the parent's own time (`v = u`, `r' = θ r`): the
  Child induction hypothesis of the STEP clause of `[FROZEN v4] CH12-O34` (verbatim) gives a
  `Good` family at every `z ∈ B_u(x, r/2)` (`child_ball_O34` for sec/vol of the sub-ball).
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

/-- A traced region bounds `|Rm|² ≤ K²` at its center, at its own time. -/
theorem center_rm_of_tracedRegion_O37 {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) :
    normSq0S (H.stageMetric (H.activeStage t) t) p 4
      (metricRm04At (H.stageMetric (H.activeStage t) t) p) ≤ K ^ 2 := by
  obtain ⟨hρ, -, a, hat, -, hall⟩ := h
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  obtain ⟨A, hA⟩ := hall p hp
  have hb := hA.1 t hat le_rfl
  have he : A.point (H.activeStage t) (H.activeStage_mono hat) (H.activeStage_mono le_rfl) = p :=
    A.endpoint_eq
  rw [he] at hb
  exact hb

/-- STEP restart at the parent's time: every `z ∈ B_u(x, r/2)` carries a `Good` family at radius
`θ r` (Child premises at `v = u`, `y = z`, `r' = θ r`). -/
theorem children_at_parent_time_O37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
    (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) {ε θ K τ₁ τ₂ κ Λ b r : ℝ}
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (hneck : Hp.parameters.neckRadius (u : ℝ) < r) (hrb : r ≤ b * Real.sqrt u)
    (hreg : 0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes)
    (hsec :
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)))
    (hvol :
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ))
    (IH :
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
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹)))) :
    ∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x (r / 2),
      ∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
        (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
          ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
          ((sliceTowerHistory_CX2 s).activeStage_mono hau) z),
        (a : ℝ) = u - τ₁ * (θ * r) ^ 2 ∧
        ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
          (sliceTowerHistory_CX2 s).isTracedRegion w
            (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
              ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
            (κ * (θ * r)) (τ₂ * (θ * r) ^ 2) (K * ((θ * r) ^ 2)⁻¹) := by
  intro z hz
  obtain ⟨hsec', hvol'⟩ := child_ball_O34 s u x z hr hθ hθ2 hz hsec hvol
  have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
  have hsq : (θ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hθr 2
  have hwin : (u : ℝ) - Λ * r ^ 2 ≤ (u : ℝ) - Λ * (θ * r) ^ 2 := by nlinarith
  have hfloor : θ * Hp.parameters.neckRadius (u : ℝ) ≤ θ * r :=
    mul_le_mul_of_nonneg_left hneck.le hθ.le
  exact IH u z (θ * r) le_rfl hwin hfloor le_rfl hreg (hθr.trans hrb) hsec' hvol'

end GC.LongTime.Ch12
